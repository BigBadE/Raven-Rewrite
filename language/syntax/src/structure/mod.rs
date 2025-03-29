use lazy_static::lazy_static;
use std::collections::HashMap;
use serde::{Deserialize, Serialize};
use crate::util::path::FilePath;

pub mod literal;
pub mod visitor;
pub mod traits;

lazy_static! {
    pub static ref MODIFIERS: HashMap<&'static str, Modifier> =
        HashMap::from([("pub", Modifier::PUBLIC)]);
}

#[derive(Serialize, Deserialize, Copy, Clone, Debug)]
pub enum Modifier {
    PUBLIC = 0b1,
}

pub trait FileOwner {
    fn file(&self) -> &FilePath;

    fn set_file(&mut self, file: FilePath);
}