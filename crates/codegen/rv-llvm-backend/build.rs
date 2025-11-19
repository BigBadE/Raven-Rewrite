use std::fs::File;
use std::path::PathBuf;
use std::time::Duration;
use std::{env, fs, io};

use reqwest::blocking::Client;
use zip::ZipArchive;

/// Automatically downloads LLVM from a separate repo and sets up library symlinks.
/// llvm-sys handles the actual linking once LLVM is found at LLVM_SYS_180_PREFIX.
fn main() {
    // Get the target directory (4 levels up from OUT_DIR)
    let target = PathBuf::from(env::var("OUT_DIR").unwrap())
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf();

    // Download LLVM based on platform
    match env::consts::ARCH {
            "x86_64" => match env::consts::OS {
                "windows" => setup_llvm(
                    target.clone(),
                    "https://github.com/BigBadE/LLVMBinaryBuilder/releases/download/release/Windows-x86_64.zip",
                ),
                "linux" => setup_llvm(
                    target.clone(),
                    "https://github.com/BigBadE/LLVMBinaryBuilder/releases/download/release/Linux-x86_64.zip",
                ),
                "macos" => setup_llvm(
                    target.clone(),
                    "https://github.com/BigBadE/LLVMBinaryBuilder/releases/download/release/MacOS-x86_64.zip",
                ),
                _ => panic!(
                    "Unsupported OS: {}. Make sure to download LLVM yourself and follow llvm-sys's instructions or make an issue on the github",
                    env::consts::OS
                ),
            },
            "aarch64" => match env::consts::OS {
                "macos" => setup_llvm(
                    target.clone(),
                    "https://github.com/BigBadE/LLVMBinaryBuilder/releases/download/release/MacOS-ARM.zip",
                ),
                _ => panic!(
                    "Unsupported architecture: {}. Make sure to download LLVM yourself and follow llvm-sys's instructions or make an issue on the github",
                    env::consts::ARCH
                ),
            },
            _ => panic!(
                "Unsupported architecture: {}. Make sure to download LLVM yourself and follow llvm-sys's instructions or make an issue on the github",
                env::consts::ARCH
            ),
        }

    // llvm-sys will automatically handle linking once it finds LLVM at LLVM_SYS_180_PREFIX
    // The environment variable is already set in .cargo/config.toml
}

fn setup_llvm(mut target: PathBuf, url: &'static str) {
    let llvm_path = target.join("llvm");
    if !llvm_path.exists() {
        let temp = target.join("llvm-temp.zip");
        if temp.exists() {
            fs::remove_file(temp.clone()).unwrap();
        }
        eprintln!("Downloading LLVM, this build may take a while...");
        let mut resp = Client::builder()
            .timeout(Duration::from_secs(60 * 60))
            .build()
            .unwrap()
            .get(url)
            .send()
            .expect("request failed");
        let temp = target.join("llvm-temp.zip");
        if temp.exists() {
            fs::remove_file(temp.clone()).unwrap();
        }
        let mut file = File::create(temp.clone()).expect("failed to create file");
        io::copy(&mut resp, &mut file).expect("failed to download llvm");
        let mut archive = ZipArchive::new(File::open(temp.clone()).unwrap()).unwrap();
        target = target.join("llvm");
        archive.extract(target.clone()).unwrap();
        fs::remove_file(temp.clone()).unwrap();
        eprintln!("LLVM downloaded successfully!");
    }

    // Create library symlinks for LLVM dependencies on Linux
    // This allows linking libzstd and libxml2 without dev packages installed
    if env::consts::OS == "linux" {
        let llvm_lib_dir = llvm_path.join("target").join("lib");
        fs::create_dir_all(&llvm_lib_dir).ok();

        // Create symlinks to system libraries
        let _ = std::os::unix::fs::symlink(
            "/usr/lib/x86_64-linux-gnu/libzstd.so.1",
            llvm_lib_dir.join("libzstd.so")
        );
        let _ = std::os::unix::fs::symlink(
            "/usr/lib/x86_64-linux-gnu/libxml2.so.2",
            llvm_lib_dir.join("libxml2.so")
        );
    }
}
