use crate::{DirectivesConst, write_idl::{IdlWriter, TypeIdl, ValueIdl}};

pub trait EnumValue: Sized + 'static {
    const NAME: &'static str;
    const VALUES: &'static [Self];

    const DESCRIPTION: Option<&'static str> = None;
    const DIRECTIVES: Option<DirectivesConst<'static>> = None;

    fn value(&self) -> &str;
    fn from_value(value: &str) -> Option<Self>;

    fn deprecated(&self) -> Option<&'static str>;
    fn description(&self) -> Option<&'static str> { None }
    fn directives(&self) -> Option<DirectivesConst<'_>> { None }
}

impl<T> TypeIdl for T where T: EnumValue {
    fn write_type_idl<W: IdlWriter>(output: &mut W) -> Result<(), W::Error> {
        if let Some(desc) = T::DESCRIPTION {
            output.write_multiline_string(desc)?;
        }
        
        output.write_all(format!( "enum {} ", T::NAME).as_bytes())?;

        if let Some(dir) = T::DIRECTIVES {
            dir.write_idl(output)?;
        }

        output.write_all(b"{")?;

        {
            let output = &mut output.indent(1);

            for value in T::VALUES {
                value.write_idl(output)?;
            }
        }

        output.write_all(b"\n}\n")?;

        Ok(())
    }
}

impl<T: EnumValue> ValueIdl for T {
    fn write_idl<W: IdlWriter>(&self, out: &mut W) -> Result<(), W::Error> {
        out.write_all(b"\n")?;

        if let Some(desc) = self.description() {
            out.write_multiline_string(desc)?;
        }

        out.write_all(self.value().as_bytes())?;

        if let Some(dir) = self.directives() {
            dir.write_idl(out)?;
        }

        Ok(())
    }
}