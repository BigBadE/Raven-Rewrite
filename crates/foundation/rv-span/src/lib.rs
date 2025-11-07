//! Source file spans and locations

use serde::{Deserialize, Serialize};
use std::ops::Range;

/// A unique identifier for a source file
#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq, Serialize, Deserialize)]
pub struct FileId(pub u32);

impl FileId {
    pub fn new(id: u32) -> Self {
        Self(id)
    }
}

/// A byte offset span in a source file
#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq, Serialize, Deserialize)]
pub struct Span {
    pub start: u32,
    pub end: u32,
}

impl Span {
    pub fn new(start: u32, end: u32) -> Self {
        Self { start, end }
    }

    pub fn range(&self) -> Range<usize> {
        self.start as usize..self.end as usize
    }

    pub fn len(&self) -> u32 {
        self.end - self.start
    }

    pub fn is_empty(&self) -> bool {
        self.start == self.end
    }
}

/// A span with associated file
#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq, Serialize, Deserialize)]
pub struct FileSpan {
    pub file: FileId,
    pub span: Span,
}

impl FileSpan {
    pub fn new(file: FileId, span: Span) -> Self {
        Self { file, span }
    }

    pub fn range(&self) -> Range<usize> {
        self.span.range()
    }
}
