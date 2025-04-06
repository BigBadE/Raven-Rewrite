use crate::util::path::FilePath;
use serde::{Deserialize, Serialize};
use std::fmt::Debug;

pub trait Type: Serialize + for<'a> Deserialize<'a> + Debug {
    fn file(&self) -> &FilePath;
}

pub trait TypeReference: Serialize + for<'a> Deserialize<'a> + Debug {}

pub trait Function: Serialize + for<'a> Deserialize<'a> + Debug {
    fn file(&self) -> &FilePath;
}

pub trait FunctionReference: Serialize + for<'a> Deserialize<'a> + Debug {}

pub trait Terminator: Serialize + for<'a> Deserialize<'a> + Debug {}

pub trait Expression: Serialize + for<'a> Deserialize<'a> + Debug {}

pub trait Statement: Serialize + for<'a> Deserialize<'a> + Debug {}
