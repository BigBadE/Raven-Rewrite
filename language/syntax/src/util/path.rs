use std::path::PathBuf;
use lasso::{Spur, ThreadedRodeo};

// A path to a file, function, struct, etc.
// Usually written in the style of foo::bar::Baz
pub type FilePath = Vec<Spur>;

pub fn get_path(interner: &ThreadedRodeo, file: &PathBuf, root: &PathBuf) -> FilePath {
    // Compute the relative path from root to file.
    let relative = file.strip_prefix(&root).unwrap_or(&file);
    
    // Convert each valid component to a Spur.
    let mut path: FilePath = relative
        .components()
        .filter_map(|comp| comp.as_os_str().to_str())
        .map(|s| interner.get_or_intern(s.replace(".rv", "")))
        .collect();
    
    // Add the root directory
    path.insert(0, interner.get_or_intern(root.components().last().unwrap().as_os_str().to_str().unwrap()));
    
    path
}