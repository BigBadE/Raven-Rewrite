# Building on Linux

## Quick Start

```bash
cargo build
```

That's it! LLVM downloads automatically on the first build.

## Prerequisites

- Rust nightly toolchain
- clang and lld linker (usually installed by default)
- libzstd and libxml2 runtime libraries (usually installed by default)

If needed, install on Ubuntu/Debian:
```bash
sudo apt-get install clang lld
```

## How It Works

On the first build, `rv-llvm-backend/build.rs` automatically:
- Downloads pre-built LLVM 18 for Linux x86_64 to `target/llvm/`
- Creates library symlinks for libzstd and libxml2 in `target/llvm/target/lib/`
- Sets up everything for `llvm-sys` to find and link LLVM

The `.cargo/config.toml` tells llvm-sys where to find LLVM:
```toml
LLVM_SYS_180_PREFIX = { value = "target/llvm/target", relative = true }
```

After the first build, LLVM is cached and subsequent builds are fast.

## Troubleshooting

### Missing libzstd or libxml2

If you see linker errors about missing `-lzstd` or `-lxml2`:

1. Check that the symlinks exist in the LLVM lib directory:
   ```bash
   ls -la target/llvm/target/lib/
   ```

2. If not, clean and rebuild (build.rs will recreate them):
   ```bash
   cargo clean
   cargo build
   ```

3. Or create them manually:
   ```bash
   mkdir -p target/llvm/target/lib
   ln -sf /usr/lib/x86_64-linux-gnu/libzstd.so.1 target/llvm/target/lib/libzstd.so
   ln -sf /usr/lib/x86_64-linux-gnu/libxml2.so.2 target/llvm/target/lib/libxml2.so
   ```

### LLVM Not Found

If llvm-sys can't find LLVM:

1. Ensure you have internet access (for the first build)
2. Try cleaning and rebuilding:
   ```bash
   cargo clean
   cargo build
   ```

### How It Works (Technical Details)

The build.rs automatically downloads LLVM:

1. **rv-llvm-backend/build.rs** runs before compilation
2. Downloads LLVM 18 from GitHub releases if not already present
3. Extracts to `target/llvm/`
4. Creates library symlinks for libzstd and libxml2
5. **llvm-sys** finds LLVM via `LLVM_SYS_180_PREFIX` and handles all linking

This approach works without dev packages and requires zero manual setup.

## Differences from Windows Build

- Linux uses lld linker (Windows uses rust-lld.exe)
- Linux uses library symlinks for zstd/xml2 (dev packages not always installed)
- Both platforms use the same automatic LLVM download and linking system
