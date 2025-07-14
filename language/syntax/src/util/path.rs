use std::fmt;
use std::fmt::Write;
use lasso::{Spur, ThreadedRodeo};
use std::path::PathBuf;
use crate::util::pretty_print::{NestedWriter, PrettyPrint};

/// A path to a file, function, struct, etc.
/// Usually written in the style of foo::bar::Baz
pub type FilePath = Vec<Spur>;

impl<W: Write> PrettyPrint<W> for FilePath {
    fn format(&self, interner: &ThreadedRodeo, writer: &mut NestedWriter<W>) -> Result<(), fmt::Error> {
        write!(writer, "{}", self.iter()
            .map(|s| interner.resolve(s))
            .collect::<Vec<_>>()
            .join("::"))
    }
}

pub fn get_file_path(path: FilePath) -> FilePath {
    path[..path.len() - 1].to_vec()
}

/// Translates a file to its path representation.
pub fn get_path(interner: &ThreadedRodeo, file: &PathBuf, root: &PathBuf) -> FilePath {
    // Compute the relative path from root to file.
    let relative = file.strip_prefix(&root).unwrap_or(&file);

    let mut components = relative
        .components()
        .filter_map(|comp| comp.as_os_str().to_str())
        .map(|str| str.to_string())
        .collect::<Vec<_>>();

    // Remove the file extension
    let len = components.len() - 1;
    components[len] = components[len].replace(".rv", "");

    // Add the root directory
    components.insert(
        0,
        root.components()
            .last()
            .unwrap()
            .as_os_str()
            .to_str()
            .unwrap()
            .to_string(),
    );

    components
        .iter()
        .map(|s| interner.get_or_intern(s))
        .collect()
}