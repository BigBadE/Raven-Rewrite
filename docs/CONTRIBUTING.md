# Contributing to Raven

Thank you for your interest in contributing to Raven! This guide will help you get started.

## Code of Conduct

- Be respectful and constructive
- Focus on technical merit
- Help others learn and grow
- Keep discussions on-topic

## Getting Started

### Prerequisites

- Rust 1.70+ (stable toolchain)
- Git
- A code editor (VS Code, Vim, etc.)

### Setting Up Your Development Environment

1. **Fork and clone the repository**
   ```bash
   git clone https://github.com/yourusername/raven.git
   cd raven
   ```

2. **Build the project**
   ```bash
   cargo build
   ```

3. **Run tests**
   ```bash
   cargo test --workspace
   ```

4. **Run the linter**
   ```bash
   cargo clippy --workspace
   ```

## Development Workflow

### 1. Choose an Issue

- Look for issues labeled `good-first-issue` or `help-wanted`
- Comment on the issue to claim it
- Ask questions if requirements are unclear

### 2. Create a Branch

```bash
git checkout -b feature/your-feature-name
# or
git checkout -b fix/bug-description
```

### 3. Make Your Changes

Follow the coding guidelines below and ensure:
- Code compiles without warnings
- All tests pass
- New functionality has tests
- Documentation is updated

### 4. Test Your Changes

```bash
# Run all tests
cargo test --workspace

# Run clippy (must pass with no warnings)
cargo clippy --workspace

# Format code
cargo fmt --all

# Check specific crate
cargo test -p rv-hir
```

### 5. Commit Your Changes

```bash
git add .
git commit -m "feat: add support for X"
```

Follow conventional commit format:
- `feat:` - New feature
- `fix:` - Bug fix
- `docs:` - Documentation changes
- `test:` - Test additions or changes
- `refactor:` - Code refactoring
- `perf:` - Performance improvements
- `chore:` - Maintenance tasks

### 6. Push and Create Pull Request

```bash
git push origin your-branch-name
```

Then create a pull request on GitHub.

## Coding Guidelines

### General Rules

1. **No `#[allow]` annotations**
   - All clippy warnings must be fixed
   - No suppression of lints

2. **File size limit: 500 lines**
   - Keep files focused and modular
   - Split large files into smaller modules

3. **Workspace dependencies**
   - Use `.workspace = true` format
   - Define versions in root `Cargo.toml`

4. **Crate naming**
   - Use `rv-` prefix for internal crates
   - Use `lang-` prefix for language adapters

5. **Error handling**
   - Use `Result<T>` for fallible operations
   - Provide context with `.context()` from anyhow
   - Never use `.unwrap()` in library code

### Testing Requirements

1. **No trivial tests**
   - Tests must verify behavior that can fail
   - Don't test that constructors return instances
   - Test actual logic and edge cases

2. **Test organization**
   ```rust
   #[cfg(test)]
   mod tests {
       use super::*;

       #[test]
       fn test_specific_behavior() {
           // Arrange
           let input = create_test_input();

           // Act
           let result = function_under_test(input);

           // Assert
           assert_eq!(result, expected_value);
       }
   }
   ```

3. **Integration tests**
   - Place in `tests/` directory
   - Test end-to-end workflows
   - Verify multiple components work together

### Code Style

1. **Use Rust idioms**
   ```rust
   // Good
   pub fn new() -> Self {
       Self { field: value }
   }

   // Bad
   pub fn new() -> MyStruct {
       MyStruct { field: value }
   }
   ```

2. **Document public APIs**
   ```rust
   /// Calculates cyclomatic complexity for a function
   ///
   /// # Arguments
   /// * `body` - The function body to analyze
   ///
   /// # Returns
   /// The cyclomatic complexity score (minimum 1)
   pub fn cyclomatic_complexity(body: &Body) -> usize {
       // ...
   }
   ```

3. **Use `#[must_use]` for builders and queries**
   ```rust
   #[must_use]
   pub fn with_max_complexity(mut self, max: usize) -> Self {
       self.max_complexity = max;
       self
   }
   ```

4. **Prefer match over if-let chains**
   ```rust
   // Good
   match expr {
       Expr::Literal { kind, .. } => handle_literal(kind),
       Expr::Variable { name, .. } => handle_variable(name),
       _ => handle_other(),
   }

   // Avoid
   if let Expr::Literal { kind, .. } = expr {
       handle_literal(kind)
   } else if let Expr::Variable { name, .. } = expr {
       handle_variable(name)
   }
   ```

### Architecture Guidelines

1. **Use arena indices instead of references**
   ```rust
   // Good
   pub struct Body {
       pub exprs: Arena<Expr>,
   }

   fn process_expr(body: &Body, expr_id: ExprId) {
       let expr = &body.exprs[expr_id];
   }

   // Bad
   fn process_expr(expr: &Expr) {
       // Can't access other expressions
   }
   ```

2. **Leverage Salsa queries**
   ```rust
   #[salsa::query_group(MyQueryGroupStorage)]
   pub trait MyQueryGroup: salsa::Database {
       #[salsa::input]
       fn source_file(&self, file_id: FileId) -> Arc<String>;

       fn parse_file(&self, file_id: FileId) -> ParseResult;
   }
   ```

3. **Keep IR transformations pure**
   - HIR lowering should not modify database
   - MIR lowering should not affect HIR
   - Backends should not modify MIR

## Project Structure

```
crates/
├── foundation/    # Core infrastructure
├── parser/        # Parsing layer
├── analysis/      # IR and type system
├── backend/       # Code generation
├── analyzer/      # Static analysis
├── cli/           # Command-line tools
└── language-support/  # Language adapters
```

### Adding a New Crate

1. Create directory: `crates/category/crate-name/`
2. Add `Cargo.toml` with workspace settings
3. Add to workspace members in root `Cargo.toml`
4. Follow naming conventions (`rv-` prefix)
5. Add documentation in crate root

## Verification Before Commit

Run this checklist before creating a PR:

```bash
# 1. Format code
cargo fmt --all

# 2. Run clippy (must have no warnings)
cargo clippy --workspace -- -D warnings

# 3. Run all tests
cargo test --workspace

# 4. Check file sizes (max 500 lines)
find crates -name "*.rs" -exec wc -l {} \; | awk '$1 > 500 {print}'

# 5. Check for #[allow] (should be none)
git grep "#\[allow" crates/

# 6. Build in release mode
cargo build --release
```

## Pull Request Process

1. **PR Title**
   - Use conventional commit format
   - Be descriptive: "feat: add type inference for match expressions"

2. **PR Description**
   - Explain the problem being solved
   - Describe your solution approach
   - Note any breaking changes
   - Reference related issues

3. **Review Process**
   - Address reviewer feedback
   - Keep commits clean (squash if needed)
   - Update documentation
   - Add tests for new features

4. **Merge Requirements**
   - All CI checks pass
   - At least one approval
   - No merge conflicts
   - Documentation updated

## Common Tasks

### Adding a New HIR Node

1. Add variant to `Expr` or `Stmt` enum in `rv-hir`
2. Update HIR lowering in `rv-hir-lower`
3. Add type inference support in `rv-ty`
4. Add MIR lowering in `rv-mir`
5. Update interpreter and JIT backends
6. Add tests

### Adding a New Lint Rule

1. Create struct implementing `LintRule` trait
2. Implement `name()` and `check_function()` methods
3. Add to default rules in `Linter::new()`
4. Add tests verifying rule triggers correctly
5. Document the rule in comments

### Adding a New Backend

1. Create crate in `crates/backend/`
2. Implement backend trait (if exists) or create new interface
3. Add MIR → backend IR translation
4. Implement execution/compilation
5. Add backend to CLI options
6. Add comparison tests with existing backends

## Getting Help

- Open a discussion on GitHub
- Join our Discord server (link in README)
- Comment on relevant issues
- Ask questions in pull requests

## Recognition

Contributors are recognized in:
- CONTRIBUTORS.md file
- Release notes
- Project documentation

Thank you for contributing to Raven!
