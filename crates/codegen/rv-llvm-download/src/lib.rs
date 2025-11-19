// This crate exists solely to download LLVM before llvm-sys tries to find it.
// Its build.rs downloads LLVM, then other crates can depend on it.
