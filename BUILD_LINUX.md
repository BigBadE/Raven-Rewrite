# Building on Linux

## Prerequisites

- Rust nightly toolchain
- clang and lld linker
- System libraries: libzstd and libxml2 (runtime versions)

Install on Ubuntu/Debian:
```bash
sudo apt-get install clang lld
```

## Build Steps

### 1. Download LLVM

Run the download script to fetch LLVM and set up library symlinks:

```bash
./download-llvm.sh
```

This script:
- Downloads pre-built LLVM 18 for Linux x86_64
- Extracts it to `target/llvm/`
- Creates symlinks for libzstd and libxml2 in `target/lib/`

### 2. Update Config (if needed)

The `.cargo/config.toml` is pre-configured for the project directory. If you're building in a different location, update the paths:

```toml
[env]
LLVM_SYS_180_PREFIX = "/path/to/your/project/target/llvm/target"

[target.x86_64-unknown-linux-gnu]
rustflags = [
    "-Clink-arg=-L/path/to/your/project/target/lib",
    # ... other flags
]
```

### 3. Build

```bash
cargo build
```

## Troubleshooting

### Missing libzstd or libxml2

If you see linker errors about missing `-lzstd` or `-lxml2`:

1. Check that the symlinks exist:
   ```bash
   ls -la target/lib/
   ```

2. If not, the download script will create them, or manually:
   ```bash
   mkdir -p target/lib
   ln -sf /usr/lib/x86_64-linux-gnu/libzstd.so.1 target/lib/libzstd.so
   ln -sf /usr/lib/x86_64-linux-gnu/libxml2.so.2 target/lib/libxml2.so
   ```

### LLVM Not Found

If llvm-sys can't find LLVM, ensure:
1. `target/llvm/target/` exists
2. `LLVM_SYS_180_PREFIX` in `.cargo/config.toml` points to the correct path

## Differences from Windows Build

- Linux uses lld linker (Windows uses rust-lld.exe)
- Linux requires library symlinks for zstd/xml2 (dev packages not installed)
- Linux supports `-Cprefer-dynamic` (Windows does not for LLVM compatibility)
