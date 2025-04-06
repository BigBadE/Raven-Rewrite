use crate::util::path::FilePath;
use lazy_static::lazy_static;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

pub mod literal;
pub mod traits;
pub mod visitor;

lazy_static! {
    pub static ref MODIFIERS: HashMap<&'static str, Modifier> = HashMap::from([
        ("pub", Modifier::PUBLIC),
        ("operation", Modifier::OPERATION)
    ]);
}

#[derive(Serialize, Deserialize, Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Modifier {
    PUBLIC = 0b1,
    OPERATION = 0b10,
}

pub trait FileOwner {
    fn file(&self) -> &FilePath;

    fn set_file(&mut self, file: FilePath);
}
