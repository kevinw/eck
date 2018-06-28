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
        FaerieTrapCollection::Disabled,
        FaerieBuilder::default_libcall_names(),
    ).unwrap();
    builder
}

struct Scope {
    names: HashMap<String, Variable>,
}

impl Scope {
    fn new() -> Scope {
        Scope { names: HashMap::new() }
    }

}

struct Translator<'a> {
    builder: FunctionBuilder<'a, Variable>,
    module: &'a mut Module<FaerieBackend>,
    scopes: Vec<Scope>,
    //names: &'a mut HashMap<String, Variable>,
}

impl<'a> Translator<'a> {
    fn new(module: &'a mut Module<FaerieBackend>, builder: FunctionBuilder<'a, Variable>) -> Translator<'a> {
        let scopes = vec![Scope::new()];
        Translator { module, builder, scopes }
    }

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
            let scope = &mut self.scopes[0];
            scope.names.insert(variable_name.to_string(), x);
        }
    }

    fn new_scope(&mut self) {
        self.scopes.push(Scope::new());
    }

    fn end_scope(&mut self) {
        let length = self.scopes.len();
        self.scopes.remove(length - 1);
    }

    fn translate_block_expressions(&mut self, expressions: Vec<Expr>) -> Value {
        self.new_scope();
        self.declare_variables(&expressions);
        let mut val = self.builder.ins().iconst(self.module.pointer_type(), 0);
        for expr in expressions {
            val = self.translate_expr(expr);
        }
        self.end_scope();
        val
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
                self.builder.ins().iconst(self.module.pointer_type(), 0) // TODO: this isn't right
            }

            Expr::If(condition, then_block, else_block) => {
                let condition_value = self.translate_expr(*condition);
                
                let else_ebb = self.builder.create_ebb();
                let merge_ebb = self.builder.create_ebb();
                self.builder.append_ebb_param(merge_ebb, self.module.pointer_type());

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
                self.translate_block_expressions(expressions)
            }
            Expr::Assign(name, expr) => {
                let new_value = self.translate_expr(*expr);
                let scope = &mut self.scopes[0];
                let variable = scope.names.get(&name).expect(&format!("no var named '{}'", name));
                self.builder.def_var(*variable, new_value);
                new_value
            }
            Expr::Ref(name) => {
                let scope = &mut self.scopes[0];
                let variable = scope.names.get(&name).expect(&format!("no var named '{}'", name));
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

fn _define_data<T>(module: &mut Module<T>) -> Result<(), Error>
    where T: cretonne_module::Backend 
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
    Ok(())
}

fn main() -> Result<(), Error> {
    let mut input = String::new();
    File::open("hello.eck")?.read_to_string(&mut input)?;

    let mut module = Module::<FaerieBackend>::new(make_builder("test.o"));
    let int = module.pointer_type();

    let mut func_builder_ctx = FunctionBuilderContext::<Variable>::new();

    let mut context: codegen::Context = module.make_context();
    context.func.signature.params.push(AbiParam::new(int));
    context.func.signature.params.push(AbiParam::new(int));
    context.func.signature.returns.push(AbiParam::new(int));


    {
        let builder = FunctionBuilder::<Variable>::new(&mut context.func, &mut func_builder_ctx);
        let mut trans = Translator::new(&mut module, builder);
        let entry_ebb = trans.builder.create_ebb();
        trans.builder.append_ebb_params_for_function_params(entry_ebb);
        trans.builder.switch_to_block(entry_ebb);
        trans.builder.seal_block(entry_ebb);

        let items = parser::module(&input).unwrap_or_else(|e| {
            eprintln!("error parsing: {:?}", e);
            std::process::exit(1);
        });

        println!("parsed: {:?}", items);

        let return_value = trans.translate_block_expressions(items);
        trans.builder.ins().return_(&[return_value]);
        trans.builder.finalize();
    }

    {
        let flags = settings::Flags::new(settings::builder());
        verify_function(&context.func, &flags).unwrap_or_else(|e| {
            eprintln!("error verifying function: {:?}", e);
        });

        // show ir
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

#[cfg(test)]
mod test {
    use super::*;
    use cretonne::codegen::scoped_hash_map::Entry::*;
    use cretonne::codegen::scoped_hash_map::ScopedHashMap;

    type ScopeVars = ScopedHashMap<String, Variable>;

    fn ensure_vacant_and_insert(vals: &mut ScopeVars, key: &str, var: Variable) {
        let entry = vals.entry(key.into());

        match entry {
            Occupied(_) => {
                let msg = format!("shouldn't have an entry for {}", key);
                panic!(msg);
            },
            Vacant(entry) => {
                entry.insert(var);
            },
        };

        ()
    }

    fn ensure_vacant(vals: &mut ScopeVars, key: &str) {
        match vals.entry(key.into()) {
            Occupied(_) => { panic!("expected vacant"); }
            Vacant(_) => { }
        }
    }

    #[test]
    fn test_scoped_hashmap() {
        let mut vals: ScopedHashMap<String, Variable> = ScopedHashMap::new();

        vals.increment_depth();

        ensure_vacant_and_insert(&mut vals, "foo", Variable::with_u32(0));

        match vals.entry("foo".into()) {
            Vacant(_) => panic!(),
            Occupied(entry) => {
                assert!(entry.get().index() == 0);
            }
        }

        vals.decrement_depth();

        ensure_vacant(&mut vals, "foo");
    }
}


