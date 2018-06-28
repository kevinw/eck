extern crate failure;
extern crate cretonne;
extern crate cretonne_faerie;
extern crate cretonne_module;
extern crate cretonne_codegen;
extern crate cretonne_frontend;
#[macro_use] extern crate target_lexicon;

use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::io::Read;
use std::str::FromStr;
use failure::Error;

use cretonne_codegen::verifier::verify_function;
use cretonne_faerie::{FaerieBackend, FaerieBuilder, FaerieTrapCollection};
use cretonne_module::{DataContext, Linkage, Module, Writability};
use cretonne::prelude::{FunctionBuilder, Variable, InstBuilder, Value,
    AbiParam, settings, FunctionBuilderContext,
    Configurable, codegen, isa, EntityRef};

#[derive(Debug, Clone)]
pub enum Expr {
    IntegerLiteral(String),
    Ref(String),
    Block(Vec<Expr>),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    Assign(String, Box<Expr>),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),
    Func {
        params: Vec<String>,
        block: Box<Expr>, // block
    },
    Nil,
}

mod parser {
    include!(concat!(env!("OUT_DIR"), "/grammar.rs"));
}

fn make_builder(name: &str) -> FaerieBuilder {
    let mut flag_builder = settings::builder();
    flag_builder.enable("is_pic").unwrap();
    let isa_builder = isa::lookup(triple!("x86_64-unknown-unknown-macho")).unwrap();
    let isa = isa_builder.finish(settings::Flags::new(flag_builder));
    let builder = FaerieBuilder::new(
        isa,
        name.to_owned(),
        target_lexicon::BinaryFormat::Macho,
        FaerieTrapCollection::Disabled,
        FaerieBuilder::default_libcall_names(),
    ).unwrap();
    builder
}

struct Translator<'a> {
    builder: FunctionBuilder<'a, Variable>,
    module: &'a mut Module<FaerieBackend>,
    names: &'a mut HashMap<String, Variable>,
}

impl<'a> Translator<'a> {
    fn declare_variables(&mut self, exprs: &[Expr]) {
        let mut variable_names = HashSet::new();
        for expr in exprs {
            match *expr {
                Expr::Assign(ref name, _) => {
                    variable_names.insert(name);
                }
                _ => {}
            }
        }

        for (index, variable_name) in variable_names.iter().enumerate() {
            let x = Variable::new(index);
            self.builder.declare_var(x, self.module.pointer_type());
            self.names.insert(variable_name.to_string(), x);
        }
    }

    fn translate_expr(&mut self, expr: Expr) -> Value {
        match expr {
            Expr::Func { params: _, block } => {
                let b = *block;
                match &b {
                    Expr::Block(_statements) => self.translate_expr(b.clone()), // TODO: how to remove this clone?
                    _ => panic!("function block expected to be an Expr::Block")
                }
            },
            Expr::Nil => {
                let int_type = self.module.pointer_type();
                self.builder.ins().iconst(int_type, 0) // TODO: this isn't right
            }

            Expr::If(condition, then_block, else_block) => {
                let condition_value = self.translate_expr(*condition);
                
                let int_type = self.module.pointer_type();

                let else_ebb = self.builder.create_ebb();
                let merge_ebb = self.builder.create_ebb();
                self.builder.append_ebb_param(merge_ebb, int_type);

                self.builder.ins().brz(condition_value, else_ebb, &[]);

                let then_return = self.translate_expr(*then_block);
                self.builder.ins().jump(merge_ebb, &[then_return]);

                self.builder.switch_to_block(else_ebb);
                self.builder.seal_block(else_ebb);
                let else_return = self.translate_expr(*else_block);
                self.builder.ins().jump(merge_ebb, &[else_return]);

                self.builder.switch_to_block(merge_ebb);
                self.builder.seal_block(merge_ebb);
                let phi = self.builder.ebb_params(merge_ebb)[0];
                phi
            }
            Expr::Block(expressions) => {
                let mut val = self.builder.ins().iconst(self.module.pointer_type(), 0);
                for expr in expressions {
                    val = self.translate_expr(expr);
                }
                val
            }
            Expr::Assign(name, expr) => {
                let new_value = self.translate_expr(*expr);
                let variable = self.names.get(&name).expect(&format!("no var named '{}'", name));
                self.builder.def_var(*variable, new_value);
                new_value
            }
            Expr::Ref(name) => {
                let variable = self.names.get(&name).expect(&format!("no var named '{}'", name));
                self.builder.use_var(*variable)
            }
            Expr::Add(lhs, rhs) => {
                let lhs = self.translate_expr(*lhs);
                let rhs = self.translate_expr(*rhs);
                self.builder.ins().iadd(lhs, rhs)
            }
            Expr::Sub(lhs, rhs) => {
                let lhs = self.translate_expr(*lhs);
                let rhs = self.translate_expr(*rhs);
                self.builder.ins().isub(lhs, rhs)
            }
            Expr::Mul(lhs, rhs) => {
                let lhs = self.translate_expr(*lhs);
                let rhs = self.translate_expr(*rhs);
                self.builder.ins().imul(lhs, rhs)
            }
            Expr::Div(lhs, rhs) => {
                let lhs = self.translate_expr(*lhs);
                let rhs = self.translate_expr(*rhs);
                self.builder.ins().udiv(lhs, rhs)
            }
            Expr::IntegerLiteral(n) => {
                let integer_value:i32 = n.parse().unwrap();
                self.builder.ins().iconst(self.module.pointer_type(), i64::from(integer_value))
            }
        }
    }
}

fn main() -> Result<(), Error> {
    let mut input = String::new();
    File::open("hello.eck")?.read_to_string(&mut input)?;

    let mut module = Module::<FaerieBackend>::new(make_builder("test.o"));
    let int = module.pointer_type();

    let mut func_builder_ctx = FunctionBuilderContext::<Variable>::new();

    {
        let mut data_context = DataContext::new();
        let mut contents = Vec::<u8>::new();
        contents.push(0);
        contents.push(0);
        contents.push(0);
        contents.push(0);
        data_context.define(contents.into_boxed_slice(), Writability::Writable);
        let data_name = "foo";
        let data_id = module.declare_data(data_name, Linkage::Export, true)?;
        module.define_data(data_id, &data_context).unwrap();
        data_context.clear();
        module.finalize_data(data_id);
    }

    let mut context: codegen::Context = module.make_context();
    context.func.signature.params.push(AbiParam::new(int));
    context.func.signature.params.push(AbiParam::new(int));
    context.func.signature.returns.push(AbiParam::new(int));

    {
        let builder = FunctionBuilder::<Variable>::new(&mut context.func, &mut func_builder_ctx);
        let mut names = HashMap::new();
        let mut trans = Translator { module: &mut module, builder: builder, names: &mut names };
        let entry_ebb = trans.builder.create_ebb();
        trans.builder.append_ebb_params_for_function_params(entry_ebb);
        trans.builder.switch_to_block(entry_ebb);
        trans.builder.seal_block(entry_ebb);

        let items = parser::module(&input).unwrap_or_else(|e| {
            eprintln!("error parsing: {:?}", e);
            std::process::exit(1);
        });
        trans.declare_variables(&items);

        let return_value = {
            println!("parsed: {:?}", items);
            let mut last_value:Value = Value::with_number(0).unwrap(); // TODO: how to not have a value
            for item in items {
                last_value = trans.translate_expr(item);
            }
            last_value
        };

        trans.builder.ins().return_(&[return_value]);
        trans.builder.finalize();
    }

    {
        let flags = settings::Flags::new(settings::builder());
        verify_function(&context.func, &flags).unwrap_or_else(|e| {
            eprintln!("error verifying function: {:?}", e);
        });
        println!("{}", context.func.display(None));
    }

    let id = module.declare_function("main", Linkage::Export, &context.func.signature)?;
    module.define_function(id, &mut context).unwrap();
    module.clear_context(&mut context);
    
    module.finalize_function(id);

    let product = module.finish();
    let file = File::create(product.name()).expect("error opening file");
    product.write(file).expect("error writing to file");

    Ok(())
}


