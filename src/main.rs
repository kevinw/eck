extern crate failure;
extern crate cretonne;
extern crate cretonne_faerie;
extern crate cretonne_module;
extern crate cretonne_codegen;
extern crate cretonne_frontend;
#[macro_use] extern crate target_lexicon;

use std::fs::File;
use std::io::Read;
use cretonne_codegen::verifier::verify_function;
use cretonne_faerie::{FaerieBackend, FaerieBuilder, FaerieTrapCollection};
use cretonne_module::{DataContext, Linkage, Module, Writability};
use cretonne::prelude::{FunctionBuilder, Variable, InstBuilder, Value,
    AbiParam, settings, FunctionBuilderContext,
    Configurable, codegen, isa};
use std::str::FromStr;
use failure::Error;

#[derive(Debug)]
pub enum Expr {
    IntegerLiteral(String),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),
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
}

impl<'a> Translator<'a> {
    fn translate_expr(&mut self, expr: Expr) -> Value {
        match expr {
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
        let mut trans = Translator { module: &mut module, builder: builder };
        let entry_ebb = trans.builder.create_ebb();
        trans.builder.append_ebb_params_for_function_params(entry_ebb);
        trans.builder.switch_to_block(entry_ebb);

        let return_value = {
            match parser::module(&input) {
                Ok(items) => {
                    println!("parsed: {:?}", items);
                    let mut last_value:Value = Value::with_number(0).unwrap(); // TODO: how to not have a value
                    for item in items {
                        last_value = trans.translate_expr(item);
                    }
                    last_value
                },
                Err(e) => {
                    eprintln!("error parsing: {:?}", e);
                    std::process::exit(1);

                }
            }
        };

        trans.builder.seal_block(entry_ebb);

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


