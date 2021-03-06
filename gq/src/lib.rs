pub use gq_internals::EnumValue;
pub use gq_macros::EnumValue;


/// A test enum
#[derive(EnumValue, Debug, PartialEq)]
enum TestEnum {
    Foobar,
    ///  A test value
    TestValue,
    #[deprecated(since="old", note="Foobar")]
    OldValue
}


#[cfg(test)]
mod tests {
    use super::{*};
    use gq_internals::EnumValue;

    use gq_internals::TypeIdl;

    #[test]
    #[allow(deprecated)]
    fn it_works() {
        assert_eq!(TestEnum::NAME, "TestEnum");
        assert_eq!(TestEnum::DESCRIPTION, Some("A test enum"));
        assert_eq!(TestEnum::VALUES, &[ TestEnum::Foobar, TestEnum::TestValue, TestEnum::OldValue ]);
        assert_eq!(TestEnum::Foobar.value(), "FOOBAR");
        assert_eq!(TestEnum::Foobar.description(), None);
        assert_eq!(TestEnum::TestValue.value(), "TEST_VALUE");
        assert_eq!(TestEnum::TestValue.description(), Some(" A test value"));
        assert_eq!(TestEnum::TestValue.deprecated(), None);
        assert_eq!(TestEnum::OldValue.deprecated(), Some("Foobar"));
    }

    #[test]
    fn to_idl() {
        let mut idl = vec![];
        TestEnum::write_type_idl(&mut idl).unwrap();

        assert_eq!(idl, br#""""
A test enum
"""
enum TestEnum {
  FOOBAR
  """
   A test value
  """
  TEST_VALUE
  OLD_VALUE
}
"#);
    }
}
