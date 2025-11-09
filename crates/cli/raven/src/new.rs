//! New project command implementation

use anyhow::{Context, Result};
use colored::Colorize;
use std::fs;
use std::path::Path;

pub fn create_project(name: &str, template: &str) -> Result<()> {
    println!("{} project '{}'", "Creating".green().bold(), name);

    // Validate project name
    if !is_valid_project_name(name) {
        anyhow::bail!(
            "Invalid project name '{}'. Use only alphanumeric characters, hyphens, and underscores",
            name
        );
    }

    let project_dir = Path::new(name);

    if project_dir.exists() {
        anyhow::bail!("Directory '{}' already exists", name);
    }

    // Create project structure
    fs::create_dir_all(project_dir.join("src"))
        .context("Failed to create project directory")?;

    // Create Cargo.toml
    let cargo_toml = format!(
        r#"[package]
name = "{}"
version = "0.1.0"
edition = "2021"

[dependencies]
"#,
        name
    );

    fs::write(project_dir.join("Cargo.toml"), cargo_toml)
        .context("Failed to write Cargo.toml")?;

    // Create source file based on template
    match template {
        "bin" => {
            let main_rs = r#"fn main() {
    println("Hello, world!");
}
"#;
            fs::write(project_dir.join("src").join("main.rs"), main_rs)
                .context("Failed to write main.rs")?;

            println!("  {} Binary project created", "Created:".bold());
            println!("  {} src/main.rs", "File:".bold());
        }
        "lib" => {
            let lib_rs = r#"pub fn add(a: int, b: int) -> int {
    a + b
}

#[test]
fn test_add() {
    assert_eq!(add(2, 2), 4);
}
"#;
            fs::write(project_dir.join("src").join("lib.rs"), lib_rs)
                .context("Failed to write lib.rs")?;

            println!("  {} Library project created", "Created:".bold());
            println!("  {} src/lib.rs", "File:".bold());
        }
        _ => {
            anyhow::bail!("Unknown template: {}. Use 'bin' or 'lib'", template);
        }
    }

    // Create .gitignore
    let gitignore = r#"# Raven build artifacts
/target/

# IDE files
.vscode/
.idea/
*.swp
*.swo
*~

# OS files
.DS_Store
Thumbs.db
"#;

    fs::write(project_dir.join(".gitignore"), gitignore)
        .context("Failed to write .gitignore")?;

    println!();
    println!("{} Project '{}' created successfully!", "Success:".green().bold(), name);
    println!();
    println!("Next steps:");
    println!("  cd {}", name);
    println!("  raven build");
    println!("  raven run");

    Ok(())
}

fn is_valid_project_name(name: &str) -> bool {
    !name.is_empty()
        && name
            .chars()
            .all(|c| c.is_alphanumeric() || c == '-' || c == '_')
}
