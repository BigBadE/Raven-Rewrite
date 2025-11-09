#!/bin/bash
# Setup script to download LLVM before building
# Run this once before your first build: ./scripts/setup-llvm.sh

set -e

TARGET_DIR="target/llvm/target"

if [ -d "$TARGET_DIR" ]; then
    echo "LLVM already downloaded at $TARGET_DIR"
    exit 0
fi

echo "Downloading LLVM..."

ARCH=$(uname -m)
OS=$(uname -s | tr '[:upper:]' '[:lower:]')

# Determine URL based on platform
case "$ARCH" in
    x86_64)
        case "$OS" in
            linux)
                URL="https://github.com/BigBadE/LLVMBinaryBuilder/releases/download/release/Linux-x86_64.zip"
                ;;
            darwin)
                URL="https://github.com/BigBadE/LLVMBinaryBuilder/releases/download/release/MacOS-x86_64.zip"
                ;;
            mingw*|msys*|cygwin*)
                URL="https://github.com/BigBadE/LLVMBinaryBuilder/releases/download/release/Windows-x86_64.zip"
                ;;
            *)
                echo "Unsupported OS: $OS"
                exit 1
                ;;
        esac
        ;;
    aarch64|arm64)
        if [ "$OS" = "darwin" ]; then
            URL="https://github.com/BigBadE/LLVMBinaryBuilder/releases/download/release/MacOS-ARM.zip"
        else
            echo "Unsupported architecture: $ARCH on $OS"
            exit 1
        fi
        ;;
    *)
        echo "Unsupported architecture: $ARCH"
        exit 1
        ;;
esac

echo "Downloading from $URL..."

# Create target directory
mkdir -p target

# Download
curl -L -o target/llvm-temp.zip "$URL"

# Extract
echo "Extracting..."
mkdir -p target/llvm
unzip -q target/llvm-temp.zip -d target/llvm

# Cleanup
rm target/llvm-temp.zip

echo "LLVM downloaded successfully to $TARGET_DIR"
echo "You can now run: cargo build"
