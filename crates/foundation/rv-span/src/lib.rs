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

/// A unique identifier for a lifetime variable.
///
/// Used during lifetime inference and borrow checking to track which
/// lifetime a reference type belongs to.
#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq, Serialize, Deserialize)]
pub struct LifetimeId(pub u32);

/// A unique identifier for a runtime lifetime region/scope.
///
/// Regions are the concrete representation of lifetimes. They correspond
/// to scopes in the program where values are live.
#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq, Serialize, Deserialize)]
pub struct RegionId(pub u32);

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

    /// Creates a synthetic span for compiler-generated nodes that have no
    /// corresponding source location. Uses `FileId(u32::MAX)` as a sentinel
    /// value that will never collide with a real file ID.
    pub fn synthetic() -> Self {
        Self {
            file: FileId(u32::MAX),
            span: Span::new(0, 0),
        }
    }

    pub fn range(&self) -> Range<usize> {
        self.span.range()
    }
}
