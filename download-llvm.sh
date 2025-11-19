#!/bin/bash
# Download LLVM before building to avoid llvm-sys build issues

set -e

TARGET_DIR="$(pwd)/target"
LLVM_DIR="$TARGET_DIR/llvm"
LIB_DIR="$TARGET_DIR/lib"

if [ -d "$LLVM_DIR" ]; then
    echo "LLVM already downloaded at $LLVM_DIR"
else
    echo "Downloading LLVM for Linux x86_64..."
    mkdir -p "$TARGET_DIR"
    cd "$TARGET_DIR"

    # Download LLVM
    wget -q --show-progress \
        "https://github.com/BigBadE/LLVMBinaryBuilder/releases/download/release/Linux-x86_64.zip" \
        -O llvm-temp.zip

    echo "Extracting LLVM..."
    unzip -q llvm-temp.zip -d llvm

    echo "Cleaning up..."
    rm llvm-temp.zip

    echo "LLVM downloaded successfully to $LLVM_DIR"
fi

# Create library symlinks for LLVM dependencies (needed on Linux without dev packages)
echo "Setting up library symlinks..."
LLVM_LIB_DIR="$LLVM_DIR/target/lib"
mkdir -p "$LLVM_LIB_DIR"
ln -sf /usr/lib/x86_64-linux-gnu/libzstd.so.1 "$LLVM_LIB_DIR/libzstd.so" 2>/dev/null || true
ln -sf /usr/lib/x86_64-linux-gnu/libxml2.so.2 "$LLVM_LIB_DIR/libxml2.so" 2>/dev/null || true

echo "Setup complete!"
echo "LLVM_SYS_180_PREFIX=$LLVM_DIR/target"
echo "Library symlinks created in: $LLVM_LIB_DIR"
