use anyhow::{anyhow, Error};
use std::collections::HashMap;
use std::path::PathBuf;
use syntax::{PackageDependency, PackageManifest, PackageInfo};
use tokio::fs;
use toml;

/// Loads a package manifest from a path
pub async fn load_manifest(path: &PathBuf) -> Result<PackageManifest, Error> {
    let manifest_path = path.join("raven.toml");
    let content = fs::read_to_string(manifest_path).await?;
    let raw_manifest: toml::Value = toml::from_str(&content)?;
    
    let package_info = raw_manifest.get("package")
        .ok_or_else(|| anyhow!("Package section missing in manifest"))?;
    
    let name = package_info.get("name")
        .and_then(|v| v.as_str())
        .ok_or_else(|| anyhow!("Package name missing"))?
        .to_string();
    
    let version = package_info.get("version")
        .and_then(|v| v.as_str())
        .ok_or_else(|| anyhow!("Package version missing"))?
        .to_string();
    
    let package = PackageInfo { name, version };
    
    let mut dependencies = HashMap::new();
    
    if let Some(deps) = raw_manifest.get("dependencies").and_then(|v| v.as_table()) {
        for (dep_name, dep_info) in deps {
            let dependency = match dep_info {
                toml::Value::Table(table) => {
                    let path = table.get("path")
                        .and_then(|v| v.as_str())
                        .map(|s| PathBuf::from(s));
                    
                    let version = table.get("version")
                        .and_then(|v| v.as_str())
                        .map(|s| s.to_string());
                    
                    PackageDependency {
                        name: dep_name.clone(),
                        path,
                        version,
                    }
                },
                toml::Value::String(version_str) => {
                    PackageDependency {
                        name: dep_name.clone(),
                        path: None,
                        version: Some(version_str.clone()),
                    }
                },
                _ => return Err(anyhow!("Invalid dependency format for {}", dep_name)),
            };
            
            dependencies.insert(dep_name.clone(), dependency);
        }
    }
    
    Ok(PackageManifest { package, dependencies })
}

/// Resolves dependencies and returns a map of package names to their root directories
pub async fn resolve_dependencies(manifest: &PackageManifest, base_path: &PathBuf) -> Result<HashMap<String, PathBuf>, Error> {
    let mut resolved = HashMap::new();
    
    for (name, dep) in &manifest.dependencies {
        match &dep.path {
            Some(rel_path) => {
                let resolved_path = base_path.join(rel_path);
                if !resolved_path.exists() {
                    return Err(anyhow!("Dependency path does not exist: {:?}", resolved_path));
                }
                resolved.insert(name.clone(), resolved_path);
            },
            None => {
                // For now, we only support path dependencies
                return Err(anyhow!("Registry dependencies not yet supported for {}", name));
            }
        }
    }
    
    Ok(resolved)
}

/// Discovers all test directories in a package and its dependencies
pub async fn discover_test_directories(package_roots: &HashMap<String, PathBuf>) -> Result<Vec<PathBuf>, Error> {
    let mut test_dirs = Vec::new();
    
    for (_package_name, package_path) in package_roots {
        let tests_path = package_path.join("tests");
        if tests_path.exists() && tests_path.is_dir() {
            test_dirs.push(tests_path);
        }
    }
    
    Ok(test_dirs)
}