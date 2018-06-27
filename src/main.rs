extern crate failure;
extern crate cretonne;
extern crate cretonne_faerie;
extern crate cretonne_module;
#[macro_use] extern crate target_lexicon;

use std::fs::File;
use std::io::Read;
use cretonne_faerie::{FaerieBackend, FaerieBuilder, FaerieTrapCollection};
use cretonne_module::{DataContext, Linkage, Module, Writability};
use cretonne::prelude::{FunctionBuilder, Variable, InstBuilder, Value, Ebb,
    AbiParam, types, IntCC, Signature, CallConv, settings, FunctionBuilderContext,
    Configurable, codegen, isa, EntityRef};
use std::str::FromStr;
use failure::Error;

#[derive(Debug)]
pub enum Expr {
    Literal(String),
    IntegerLiteral(String),
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

fn main() -> Result<(), Error> {
    let mut input = String::new();
    File::open("hello.eck")?.read_to_string(&mut input)?;

    let mut value_from_code: i32 = 999;

    match parser::module(&input) {
        Ok(items) => {
            match &items[0] {
                Expr::Literal(ref n) => { value_from_code = n.parse().unwrap(); }
                Expr::IntegerLiteral(ref n) => { value_from_code = n.parse().unwrap(); }
            }
            println!("parsed: {:?}", items);
        },
        Err(e) => {
            eprintln!("error parsing: {:?}", e);
        }
    }

    let mut module = Module::<FaerieBackend>::new(make_builder("test.o"));
    let int = module.pointer_type();

    let mut func_builder_ctx = FunctionBuilderContext::<Variable>::new();

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


    let mut context: codegen::Context = module.make_context();
    context.func.signature.params.push(AbiParam::new(int));
    context.func.signature.params.push(AbiParam::new(int));
    context.func.signature.returns.push(AbiParam::new(int));

    {
        let mut builder = FunctionBuilder::<Variable>::new(&mut context.func, &mut func_builder_ctx);
        let entry_ebb = builder.create_ebb();
        builder.append_ebb_params_for_function_params(entry_ebb);
        builder.switch_to_block(entry_ebb);

        let index:usize = 0;
        let var = Variable::new(index);
        builder.declare_var(var, int);
        let number_value = builder.ins().iconst(int, i64::from(value_from_code));
        builder.def_var(var, number_value);

        builder.seal_block(entry_ebb);

        let return_value = builder.use_var(var);
        builder.ins().return_(&[return_value]);
        builder.finalize();
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

