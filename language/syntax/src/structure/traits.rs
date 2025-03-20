use std::fmt::Debug;
use crate::util::path::FilePath;

pub trait Type: Debug {
    fn file(&self) -> &FilePath;
}

pub trait TypeReference: Debug {}

pub trait Function: Debug {
    fn file(&self) -> &FilePath;
}

pub trait FunctionReference: Debug {}

pub trait Terminator: Debug {}

pub trait Expression: Debug {}

pub trait Statement: Debug {}