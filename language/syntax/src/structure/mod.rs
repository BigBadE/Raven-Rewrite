use lazy_static::lazy_static;
use std::collections::HashMap;

pub mod visitor;

lazy_static! {
    pub static ref MODIFIERS: HashMap<&'static str, Modifier> = HashMap::from([("pub", Modifier::PUBLIC)]);
}

#[derive(Copy, Clone, Debug)]
pub enum Modifier {
    PUBLIC = 0b1,

}