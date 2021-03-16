use std::{collections::BTreeMap, convert::TryInto, fmt::Debug};

use serde::de::{EnumAccess, value::MapDeserializer};
use serde::de::IntoDeserializer;

use thiserror::Error;


pub enum ConstInputValue<'de> {
    Null,
    Int(i32),
    Float(f32),
    String(&'de str),
    Boolean(bool),
    Enum(&'de str),
    List(Vec<ConstInputValue<'de>>),
    Object(Vec<(&'de str, ConstInputValue<'de>)>),
}

#[derive(Error, Debug)]
pub enum InputError {
    #[error("{0}")]
    Custom(String)
}

impl serde::de::Error for InputError {
    fn custom<T>(msg:T)-> Self where T:std::fmt::Display {
        InputError::Custom(msg.to_string())
    }
}

impl<'de> serde::de::IntoDeserializer<'de, InputError> for ConstInputValue<'de> {
    type Deserializer = ConstInputValue<'de>;

    #[inline]
    fn into_deserializer(self) -> Self::Deserializer { self }
}

impl<'de> serde::Deserializer<'de> for ConstInputValue<'de> {
    type Error = InputError;

    fn deserialize_any<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: serde::de::Visitor<'de> {
        match self {
            ConstInputValue::Null => visitor.visit_none(),
            ConstInputValue::Int(val) => visitor.visit_i32(val),
            ConstInputValue::Float(val) => visitor.visit_f32(val),
            ConstInputValue::String(val) => visitor.visit_borrowed_str(val),
            ConstInputValue::Boolean(val) => visitor.visit_bool(val),
            ConstInputValue::Enum(val) => visitor.visit_enum(val.into_deserializer()),
            ConstInputValue::List(val) => visitor.visit_seq(val.into_deserializer()),
            ConstInputValue::Object(val) => {
                visitor.visit_map(MapDeserializer::new(val.into_iter()))
            }
        }
    }

    serde::forward_to_deserialize_any! {
        bool i8 i16 i32 i64 i128 u8 u16 u32 u64 u128 f32 f64 char str string
        bytes byte_buf option unit unit_struct newtype_struct seq tuple
        tuple_struct map struct enum identifier ignored_any
    }
}

