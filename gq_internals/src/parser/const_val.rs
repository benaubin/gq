use std::{borrow::Cow};

use serde::forward_to_deserialize_any;

use super::{
    tokenizer::{TokenContent, Tokenizer},
    ParserError, ParserErrorKind, Token,
};

impl<'src> serde::Deserializer<'src> for &'_ mut Tokenizer<'src> {
    type Error = ParserError;

    fn deserialize_any<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'src>,
    {
        let Token { content, pos } = self
            .next()
            .ok_or(ParserErrorKind::Unexpected("EOF").at(self.pos()))??;

        match content {
            TokenContent::DollarSign => Err(ParserErrorKind::VariableInConstInput.at(pos)),
            TokenContent::Name("null") => visitor.visit_none(),
            TokenContent::Name("true") => visitor.visit_bool(true),
            TokenContent::Name("false") => visitor.visit_bool(false),
            TokenContent::Name(val) => {
                // technically, an enum
                visitor.visit_borrowed_str(val)
            }
            TokenContent::IntValue(val) => visitor.visit_i32(val),
            TokenContent::FloatValue(val) => visitor.visit_f32(val),
            TokenContent::StringValue(Cow::Borrowed(val)) => visitor.visit_borrowed_str(val),
            TokenContent::StringValue(Cow::Owned(val)) => visitor.visit_string(val),
            TokenContent::LeftBracket => {
                struct S<'t, 'src> {
                    tokenizer: &'t mut Tokenizer<'src>,
                }

                impl<'src> serde::de::SeqAccess<'src> for S<'_, 'src> {
                    type Error = ParserError;

                    fn next_element_seed<T>(
                        &mut self,
                        seed: T,
                    ) -> Result<Option<T::Value>, Self::Error>
                    where
                        T: serde::de::DeserializeSeed<'src>,
                    {
                        let token = self
                            .tokenizer
                            .peek_token()
                            .ok_or(ParserErrorKind::Unexpected("EOF").unknown_location())??;

                        if token.content == TokenContent::RightBracket {
                            return Ok(None);
                        }

                        seed.deserialize(&mut *self.tokenizer).map(Some)
                    }
                }

                let tokenizer = self;

                let seq = S { tokenizer };

                let val = visitor.visit_seq(seq)?;

                let Token { content, pos } = tokenizer
                    .next()
                    .ok_or(ParserErrorKind::Unexpected("EOF").at(tokenizer.pos()))??;

                if content != TokenContent::RightBracket {
                    return Err(ParserErrorKind::Expected("end of input list").at(pos));
                }

                Ok(val)
            }
            TokenContent::LeftCurlyBracket => {
                struct M<'t, 'src> {
                    tokenizer: &'t mut Tokenizer<'src>,
                }

                impl<'src> serde::de::MapAccess<'src> for M<'_, 'src> {
                    type Error = ParserError;

                    fn next_key_seed<K>(&mut self, seed: K) -> Result<Option<K::Value>, Self::Error>
                    where
                        K: serde::de::DeserializeSeed<'src>,
                    {
                        let Token { content, .. } = match self.tokenizer.peek_token() {
                            Some(val) => val?,
                            None => return Ok(None),
                        };

                        if matches!(content, TokenContent::RightCurlyBracket) { return Ok(None) }

                        let Token { content, pos } = match self.tokenizer.next() {
                            Some(val) => val?,
                            None => return Ok(None),
                        };

                        struct DeserializerBorrowedString<'de>(&'de str);
                        impl<'de> serde::Deserializer<'de> for DeserializerBorrowedString<'de> {
                            type Error = ParserError;

                            fn deserialize_any<V>(self, visitor: V) -> Result<V::Value, Self::Error>
                            where
                                V: serde::de::Visitor<'de>,
                            {
                                visitor.visit_str(self.0)
                            }

                            forward_to_deserialize_any! {
                                <W: Visitor<'de>>
                                bool i8 i16 i32 i64 i128 u8 u16 u32 u64 u128 f32 f64 char str string
                                bytes byte_buf option unit unit_struct newtype_struct seq tuple
                                tuple_struct map struct enum identifier ignored_any
                            }
                        }

                        match content {
                            TokenContent::Name(name) => {
                                Ok(Some(seed.deserialize(DeserializerBorrowedString(name))?))
                            }
                            _ => Err(ParserErrorKind::Unexpected("token for object key").at(pos)),
                        }
                    }

                    fn next_value_seed<V>(&mut self, seed: V) -> Result<V::Value, Self::Error>
                    where
                        V: serde::de::DeserializeSeed<'src>,
                    {
                        let Token { content, pos } = self
                            .tokenizer
                            .next()
                            .ok_or(ParserErrorKind::Unexpected("EOF").at(self.tokenizer.pos()))??;
                        if content != TokenContent::Colon {
                            return Err(ParserErrorKind::Expected(
                                "colon before input object value",
                            )
                            .at(pos));
                        }

                        seed.deserialize(&mut *self.tokenizer)
                    }
                }

                let val = visitor.visit_map(M { tokenizer: self })?;

                let Token { content, pos } = self
                    .next()
                    .ok_or(ParserErrorKind::Unexpected("EOF").at(self.pos()))??;

                if content != TokenContent::RightCurlyBracket {
                    return Err(ParserErrorKind::Expected("end of input object").at(pos));
                }

                Ok(val)
            }
            _ => Err(ParserErrorKind::Unexpected("token for input value").at(pos)),
        }
    }

    forward_to_deserialize_any! {
        <W: Visitor<'src>>
        bool i8 i16 i32 i64 i128 u8 u16 u32 u64 u128 f32 f64 char str string
        bytes byte_buf option unit unit_struct newtype_struct seq tuple
        tuple_struct map struct enum identifier ignored_any
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    use serde::Deserialize;

    #[test]
    fn test() {
        let mut tokenizer = Tokenizer::new(r#"
            {
                foobar: 5,
                aaaa: 7.0 list: [9]
                bbb: "foobar"
                nested: { val: ONE }
                block: """
                       hey!
                       """
            }

            after_object
        "#);

        #[derive(Deserialize, Debug, PartialEq)]
        struct Nested<'a> {
            val: Cow<'a, str>
        }

        #[derive(Deserialize, Debug, PartialEq)]
        struct Test<'a> {
            foobar: i32,
            aaaa: f32,
            bbb: Cow<'a, str>,
            block: Cow<'a, str>,
            list: Vec<i32>,
            nested: Nested<'a>
        }

        let test: Test = Deserialize::deserialize(&mut tokenizer).unwrap();

        assert_eq! ( test, Test {
            foobar: 5,
            aaaa: 7.0,
            bbb: Cow::Borrowed("foobar"),
            block: Cow::Owned("hey!".to_owned()),
            list: vec![9],
            nested: Nested {
                val: Cow::Borrowed("ONE")
            }
        } );

        let token = tokenizer.next().unwrap().unwrap();

        assert_eq!(token.content, TokenContent::Name("after_object"))
    }
}
