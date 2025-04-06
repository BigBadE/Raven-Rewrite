use lasso::{Spur, ThreadedRodeo};
use std::path::PathBuf;

/// A path to a file, function, struct, etc.
/// Usually written in the style of foo::bar::Baz
pub type FilePath = Vec<Spur>;

/// Converts the interned representation of a file path to a string.
pub fn path_to_str(path: &FilePath, interner: &ThreadedRodeo) -> String {
    path.iter()
        .map(|s| interner.resolve(s))
        .collect::<Vec<_>>()
        .join("::")
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
