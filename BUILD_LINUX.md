# Building on Linux

## Quick Start

```bash
# One-time setup
./download-llvm.sh

# Build (works forever after this)
cargo build
```

That's it! The download script runs once, then all future builds just work with `cargo build`.

## Prerequisites

- Rust nightly toolchain
- clang and lld linker (usually installed by default)
- libzstd and libxml2 runtime libraries (usually installed by default)

If needed, install on Ubuntu/Debian:
```bash
sudo apt-get install clang lld
```

## How It Works

The `download-llvm.sh` script:
- Downloads pre-built LLVM 18 for Linux x86_64 to `target/llvm/`
- Creates library symlinks for libzstd and libxml2
- Runs once - subsequent builds don't need it

The `.cargo/config.toml` tells llvm-sys where to find LLVM:
```toml
LLVM_SYS_180_PREFIX = { value = "target/llvm/target", relative = true }
```

After the initial download, `cargo build` works automatically. The `llvm-sys` crate handles all linking.

## Troubleshooting

### Missing libzstd or libxml2

If you see linker errors about missing `-lzstd` or `-lxml2`:

1. Check that the symlinks exist in the LLVM lib directory:
   ```bash
   ls -la target/llvm/target/lib/
   ```

2. If not, run the download script again:
   ```bash
   ./download-llvm.sh
   ```

3. Or create them manually:
   ```bash
   mkdir -p target/llvm/target/lib
   ln -sf /usr/lib/x86_64-linux-gnu/libzstd.so.1 target/llvm/target/lib/libzstd.so
   ln -sf /usr/lib/x86_64-linux-gnu/libxml2.so.2 target/llvm/target/lib/libxml2.so
   ```

### LLVM Not Found

If llvm-sys can't find LLVM headers during build:

1. Ensure `target/llvm/target/` exists and contains LLVM files
2. Run the download script if missing:
   ```bash
   ./download-llvm.sh
   ```

### How It Works (Technical Details)

The build uses the `no-llvm-linking` feature:

1. **inkwell** uses feature `llvm18-0-no-llvm-linking`
2. This disables automatic LLVM linking by `llvm-sys`
3. **rv-llvm-backend/build.rs** handles all linking instead:
   - Downloads LLVM if not present
   - Queries `llvm-config` for library information
   - Emits correct `cargo:rustc-link-lib` directives
   - Links system libraries (zstd, xml2, stdc++, etc.)

This approach gives us full control over the linking process and works without dev packages.

## Differences from Windows Build

- Linux uses lld linker (Windows uses rust-lld.exe)
- Linux uses library symlinks for zstd/xml2 (dev packages not always installed)
- Both platforms use the same automatic LLVM download and linking system
