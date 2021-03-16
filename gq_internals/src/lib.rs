mod enum_value;
mod input_value;
mod write_idl;

pub struct ArgumentsConst<'a>(Vec<(&'a str, ConstInputValue<'a>)>);
pub struct DirectivesConst<'a>(Vec<(&'a str, ArgumentsConst<'a>)>);

pub use input_value::ConstInputValue;
pub use enum_value::EnumValue;
pub use write_idl::{IdlWriter, TypeIdl, ValueIdl};


impl ValueIdl for DirectivesConst<'_> {
    fn write_idl<W: IdlWriter>(&self, out: &mut W) -> Result<(), W::Error> {
        todo!()
    }
}