extern crate anyhow;
extern crate cc;
extern crate regex_lite;
extern crate semver;

use anyhow::Context as _;
use std::ffi::OsStr;
use std::fs::File;
use std::path::Path;
use std::path::PathBuf;
use std::process::{Command, Output};
use std::time::Duration;
use std::{env, fs, io};

use reqwest::blocking::Client;
use zip::ZipArchive;

static CFLAGS: &str = "CFLAGS";
static OUT_DIR: &str = "OUT_DIR";
static ZSTD_LIB_DIR: &str = "ZSTD_LIB_DIR";

/// To automatically keep up to date with LLVM, this will download and link a binary from a seperate repo.
/// Linking code is taken from llvm-sys.
fn main() {
    let mut target = PathBuf::from(env::var(OUT_DIR).unwrap())
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf();
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
                "Unsupported architecture: {}. Make sure to download LLVM yourself and follow llvm-sys's instructions or make an issue on the github",
                env::consts::ARCH
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
    target = target.join("llvm").join("target");
    build(target);
}

fn setup_llvm(mut target: PathBuf, url: &'static str) {
    let llvm_path = target.join("llvm");
    if !llvm_path.exists() {
        let temp = target.join("llvm-temp.zip");
        if temp.exists() {
            fs::remove_file(temp.clone()).unwrap();
        }
        eprintln!("Downloading LLVM, this build may fail while it downloads");
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
    }
}

fn target_env_is(name: &str) -> bool {
    match env::var_os("CARGO_CFG_TARGET_ENV") {
        Some(s) => s == name,
        None => false,
    }
}

fn target_os_is(name: &str) -> bool {
    match env::var_os("CARGO_CFG_TARGET_OS") {
        Some(s) => s == name,
        None => false,
    }
}

/// Try to find a version of llvm-config that is compatible with this crate.
///
/// If $LLVM_SYS_<VERSION>_PREFIX is set, look for llvm-config ONLY in there. The assumption is
/// that the user know best, and they want to link to a specific build or fork of LLVM.
///
/// If $LLVM_SYS_<VERSION>_PREFIX is NOT set, then look for llvm-config in $PATH.
///
/// Returns None on failure.
fn locate_llvm_config(prefix: &PathBuf) -> PathBuf {
    let binary_name = prefix
        .join("bin")
        .join(format!("llvm-config{}", env::consts::EXE_SUFFIX));
    llvm_config_ex(&*binary_name, ["--version"])
        .expect("llvm-config not found or downloaded incorrectly!");
    binary_name
}

/// Invoke the specified binary as llvm-config.
fn llvm_config<I, S>(binary: &Path, args: I) -> String
where
    I: IntoIterator<Item = S>,
    S: AsRef<OsStr>,
{
    llvm_config_ex(binary, args).expect("Surprising failure from llvm-config")
}

/// Invoke the specified binary as llvm-config.
///
/// Explicit version of the `llvm_config` function that bubbles errors
/// up.
fn llvm_config_ex<I, S>(binary: &Path, args: I) -> anyhow::Result<String>
where
    I: IntoIterator<Item = S>,
    S: AsRef<OsStr>,
{
    let mut cmd = Command::new(binary);
    (|| {
        let Output {
            status,
            stdout,
            stderr,
        } = cmd.args(args).output()?;
        let stdout = String::from_utf8(stdout).context("stdout")?;
        let stderr = String::from_utf8(stderr).context("stderr")?;
        if status.success() {
            Ok(stdout)
        } else {
            Err(anyhow::anyhow!(
                "status={status}\nstdout={}\nstderr={}",
                stdout.trim(),
                stderr.trim()
            ))
        }
    })()
    .with_context(|| format!("{cmd:?}"))
}

/// Get the names of the dylibs required by LLVM, including the C++ standard
/// library.
fn get_system_libraries(llvm_config_path: &Path, kind: LibraryKind) -> Vec<String> {
    let link_arg = match kind {
        LibraryKind::Static => "--link-static",
        LibraryKind::Dynamic => "--link-shared",
    };

    llvm_config(llvm_config_path, ["--system-libs", link_arg])
        .split(&[' ', '\n'] as &[char])
        .filter(|s| !s.is_empty())
        .map(handle_flag)
        .chain(get_system_libcpp())
        .map(str::to_owned)
        .collect()
}

fn handle_flag(flag: &str) -> &str {
    if target_env_is("msvc") {
        // Same as --libnames, foo.lib
        return flag.strip_suffix(".lib").unwrap_or_else(|| {
            panic!(
                "system library '{}' does not appear to be a MSVC library file",
                flag
            )
        });
    }

    if let Some(flag) = flag.strip_prefix("-l") {
        // Linker flags style, -lfoo
        if target_os_is("macos") {
            // .tdb libraries are "text-based stub" files that provide lists of symbols,
            // which refer to libraries shipped with a given system and aren't shipped
            // as part of the corresponding SDK. They're named like the underlying
            // library object, including the 'lib' prefix that we need to strip.
            if let Some(flag) = flag
                .strip_prefix("lib")
                .and_then(|flag| flag.strip_suffix(".tbd"))
            {
                return flag;
            }
        }

        // On some distributions (OpenBSD, perhaps others), we get sonames
        // like "-lz.so.7.0". Correct those by pruning the file extension
        // and library version.
        return flag.split(".so.").next().unwrap();
    }

    let maybe_lib = Path::new(flag);
    if !maybe_lib.is_file() {
        panic!(
            "Unable to parse result of llvm-config --system-libs: {}",
            flag
        );
    }

    // Library on disk, likely an absolute path to a .so. We'll add its location to
    // the library search path and specify the file as a link target.
    println!(
        "cargo:rustc-link-search={}",
        maybe_lib.parent().unwrap().display()
    );

    // Expect a file named something like libfoo.so, or with a version libfoo.so.1.
    // Trim everything after and including the last .so and remove the leading 'lib'
    let soname = maybe_lib
        .file_name()
        .unwrap()
        .to_str()
        .expect("Shared library path must be a valid string");
    let (stem, _rest) = soname
        .rsplit_once(target_dylib_extension())
        .expect("Shared library should be a .so file");

    stem.strip_prefix("lib")
        .unwrap_or_else(|| panic!("system library '{}' does not have a 'lib' prefix", soname))
}

/// Return additional linker search paths that should be used but that are not discovered
/// by other means.
///
/// In particular, this should include only directories that are known from platform-specific
/// knowledge that aren't otherwise discovered from either `llvm-config` or a linked library
/// that includes an absolute path.
fn get_system_library_dirs() -> impl IntoIterator<Item = &'static str> {
    if target_os_is("openbsd") {
        Some("/usr/local/lib")
    } else {
        None
    }
}

fn target_dylib_extension() -> &'static str {
    if target_os_is("macos") {
        ".dylib"
    } else {
        ".so"
    }
}

/// Get the library that must be linked for C++, if any.
fn get_system_libcpp() -> Option<&'static str> {
    if target_env_is("msvc") {
        Some("msvcprt")
    } else if target_os_is("macos") {
        // On OS X 10.9 and later, LLVM's libc++ is the default. On earlier
        // releases GCC's libstdc++ is default. Unfortunately we can't
        // reasonably detect which one we need (on older ones libc++ is
        // available and can be selected with -stdlib=lib++), so assume the
        // latest, at the cost of breaking the build on older OS releases
        // when LLVM was built against libstdc++.
        Some("c++")
    } else if target_os_is("freebsd") || target_os_is("openbsd") {
        Some("c++")
    } else if target_env_is("musl") {
        // The one built with musl.
        Some("c++")
    } else {
        // Otherwise assume GCC's libstdc++.
        // This assumption is probably wrong on some platforms, but would need
        // testing on them.
        Some("stdc++")
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum LibraryKind {
    Static,
    Dynamic,
}

impl LibraryKind {
    /// Stringifies the enum
    pub fn string(&self) -> &'static str {
        match self {
            LibraryKind::Static => "static",
            LibraryKind::Dynamic => "dylib",
        }
    }
}

/// Get the names of libraries to link against, along with whether it is static or shared library.
fn get_link_libraries(
    llvm_config_path: &Path,
    preferences: &LinkingPreferences,
) -> (LibraryKind, Vec<String>) {
    // Using --libnames in conjunction with --libdir is particularly important
    // for MSVC when LLVM is in a path with spaces, but it is generally less of
    // a hack than parsing linker flags output from --libs and --ldflags.

    fn get_link_libraries_impl(
        llvm_config_path: &Path,
        kind: LibraryKind,
    ) -> anyhow::Result<String> {
        // Windows targets don't get dynamic support.
        // See: https://gitlab.com/taricorp/llvm-sys.rs/-/merge_requests/31#note_1306397918
        if target_env_is("msvc") && kind == LibraryKind::Dynamic {
            anyhow::bail!("Dynamic linking to LLVM is not supported on Windows");
        }

        let link_arg = match kind {
            LibraryKind::Static => "--link-static",
            LibraryKind::Dynamic => "--link-shared",
        };
        llvm_config_ex(llvm_config_path, ["--libnames", link_arg])
    }

    let LinkingPreferences {
        prefer_static,
        force,
    } = preferences;
    let one = [*prefer_static];
    let both = [*prefer_static, !*prefer_static];

    let preferences = if *force { &one[..] } else { &both[..] }
        .iter()
        .map(|is_static| {
            if *is_static {
                LibraryKind::Static
            } else {
                LibraryKind::Dynamic
            }
        });

    for kind in preferences {
        match get_link_libraries_impl(llvm_config_path, kind) {
            Ok(s) => return (kind, extract_library(&s, kind)),
            Err(err) => {
                println!(
                    "failed to get {} libraries from llvm-config: {err:?}",
                    kind.string()
                )
            }
        }
    }

    panic!("failed to get linking libraries from llvm-config",);
}

fn extract_library(s: &str, kind: LibraryKind) -> Vec<String> {
    s.split(&[' ', '\n'] as &[char])
        .filter(|s| !s.is_empty())
        .map(|name| {
            // --libnames gives library filenames. Extract only the name that
            // we need to pass to the linker.
            match kind {
                LibraryKind::Static => {
                    // Match static library
                    if let Some(name) = name
                        .strip_prefix("lib")
                        .and_then(|name| name.strip_suffix(".a"))
                    {
                        // Unix (Linux/Mac)
                        // libLLVMfoo.a
                        name
                    } else if let Some(name) = name.strip_suffix(".lib") {
                        // Windows
                        // LLVMfoo.lib
                        name
                    } else {
                        panic!("'{}' does not look like a static library name", name)
                    }
                }
                LibraryKind::Dynamic => {
                    // Match shared library
                    if let Some(name) = name
                        .strip_prefix("lib")
                        .and_then(|name| name.strip_suffix(".dylib"))
                    {
                        // Mac
                        // libLLVMfoo.dylib
                        name
                    } else if let Some(name) = name
                        .strip_prefix("lib")
                        .and_then(|name| name.strip_suffix(".so"))
                    {
                        // Linux
                        // libLLVMfoo.so
                        name
                    } else if let Some(name) = IntoIterator::into_iter([".dll", ".lib"])
                        .find_map(|suffix| name.strip_suffix(suffix))
                    {
                        // Windows
                        // LLVMfoo.{dll,lib}
                        name
                    } else {
                        panic!("'{}' does not look like a shared library name", name)
                    }
                }
            }
            .to_string()
        })
        .collect::<Vec<String>>()
}

#[derive(Clone, Copy)]
struct LinkingPreferences {
    /// Prefer static linking over dynamic linking.
    prefer_static: bool,
    /// Force the use of the preferred kind of linking.
    force: bool,
}

impl LinkingPreferences {
    fn init() -> LinkingPreferences {
        LinkingPreferences {
            prefer_static: true,
            force: false,
        }
    }
}

fn get_llvm_cflags(llvm_config_path: &Path) -> String {
    let output = llvm_config(llvm_config_path, ["--cflags"]);

    // llvm-config includes cflags from its own compilation with --cflags that
    // may not be relevant to us. In particularly annoying cases, these might
    // include flags that aren't understood by the default compiler we're
    // using. Unless requested otherwise, clean CFLAGS of options that are
    // known to be possibly-harmful.
    if target_env_is("msvc") {
        // MSVC doesn't accept -W... options, so don't try to strip them and
        // possibly strip something that should be retained. Also do nothing if
        // the user requests it.
        return output;
    }

    output
        .split(&[' ', '\n'][..])
        .filter(|word| !word.starts_with("-W"))
        .collect::<Vec<_>>()
        .join(" ")
}

/// Builds and links against LLVM
fn build(llvm_path: PathBuf) {
    if env::consts::OS == "windows" {
        println!("cargo:rustc-link-arg=/ignore:4099");
    }

    let llvm_config_path = locate_llvm_config(&llvm_path);

    unsafe {
        env::set_var(CFLAGS, get_llvm_cflags(&llvm_config_path));
    }

    cc::Build::new()
        .file("wrappers/target.c")
        .compile("targetwrappers");
    let libdir = llvm_config(&llvm_config_path, ["--libdir"]);

    // Export information to other crates
    println!("cargo:config_path={}", llvm_config_path.display()); // will be DEP_LLVM_CONFIG_PATH
    println!("cargo:libdir={}", libdir); // DEP_LLVM_LIBDIR

    let preferences = LinkingPreferences::init();

    if let Ok(found) = env::var(ZSTD_LIB_DIR) {
        println!("cargo:rustc-link-search=native={}", found);
    }

    // Link LLVM libraries
    println!("cargo:rustc-link-search=native={}", libdir);
    for link_search_dir in get_system_library_dirs() {
        println!("cargo:rustc-link-search=native={}", link_search_dir);
    }

    // We need to take note of what kind of libraries we linked to, so that
    // we can link to the same kind of system libraries
    let (kind, libs) = get_link_libraries(&llvm_config_path, &preferences);
    for name in libs {
        println!("cargo:rustc-link-lib={}={}", kind.string(), name);
    }

    // Link system libraries
    // We get the system libraries based on the kind of LLVM libraries we link to, but we link to
    // system libs based on the target environment.
    let sys_lib_kind = LibraryKind::Dynamic;
    for name in get_system_libraries(&llvm_config_path, kind) {
        println!("cargo:rustc-link-lib={}={}", sys_lib_kind.string(), name);
    }
}
