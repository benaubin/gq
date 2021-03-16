
pub trait IdlWriter: Sized {
    type Error;

    fn write_all(&mut self, buf: &[u8]) -> Result<(), Self::Error>;

    fn write_multiline_string(&mut self, str: &str) -> Result<(), Self::Error> {
        self.write_all(br#""""
"#)?;
        self.write_all(str.replace(r#"""""#, r#"\""""#).as_bytes())?;
        self.write_all(br#"
"""
"# )?;
        Ok(())
    }

    fn indent<'a>(&'a mut self, level: usize) -> Indented<'a, Self> {
        Indented {
            parent: self,
            level
        }
    }
}

impl<T: std::io::Write> IdlWriter for T {
    type Error = std::io::Error;
    
    #[inline(always)]
    fn write_all(&mut self, buf: &[u8]) -> Result<(), Self::Error> {
        self.write_all(buf)
    }
}

pub struct Indented<'a, T: IdlWriter> {
    parent: &'a mut T,
    level: usize
}

impl<'a, T: IdlWriter> IdlWriter for Indented<'a, T> {
    type Error = T::Error;

    fn write_all(&mut self, buf: &[u8]) -> Result<(), Self::Error> {
        let mut lines = buf.split(|i| i == &b"\n"[0]);

        let last = lines.next_back();

        for line in lines {
            self.parent.write_all(line)?;
            self.parent.write_all(b"\n")?;
            self.parent.write_all("  ".repeat(self.level).as_bytes())?;
        }

        if let Some(last) = last {
            self.parent.write_all(last)?;
        }

        Ok(())
    }
}


pub trait TypeIdl {
    fn write_type_idl<W: IdlWriter>(out: &mut W) -> Result<(), W::Error>;
}

pub trait ValueIdl {
    fn write_idl<W: IdlWriter>(&self, out: &mut W) -> Result<(), W::Error>;
}