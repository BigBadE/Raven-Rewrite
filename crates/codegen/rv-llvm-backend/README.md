# rv-llvm-backend

LLVM backend for the Raven compiler. Translates MIR (Mid-level Intermediate Representation) to native machine code via LLVM.

## Features

- **Full LLVM Integration**: Leverages LLVM for production-quality code generation
- **Multiple Optimization Levels**: None, Less, Default, Aggressive
- **Target Independence**: Generates code for any LLVM-supported target
- **MIR Translation**: Direct lowering from Raven's MIR to LLVM IR

## Architecture

```
MIR → Type Lowering → LLVM IR → Optimization Passes → Object Code
```

### Components

1. **Type Lowering** (`types.rs`)
   - Maps Raven types to LLVM types
   - Handles primitives, pointers, arrays, structs
   - Function type creation

2. **Code Generation** (`codegen.rs`)
   - Function compilation
   - Basic block generation
   - Statement and expression lowering
   - Terminator handling (return, goto, switch, call)

3. **Optimization** (integrated with LLVM)
   - Instruction combining
   - Dead code elimination
   - Function inlining
   - Memory to register promotion
   - Tail call optimization

## Usage

### Basic Compilation

```rust
use rv_llvm_backend::{compile_to_native, OptLevel};
use rv_mir::MirFunction;
use std::path::Path;

// Compile MIR functions to object file
let functions = vec![/* your MIR functions */];
compile_to_native(&functions, Path::new("output.o"), OptLevel::Default)?;
```

### Generate LLVM IR

```rust
use rv_llvm_backend::{compile_to_llvm_ir, OptLevel};

let llvm_ir = compile_to_llvm_ir(&functions, OptLevel::Aggressive)?;
println!("{}", llvm_ir);
```

## Requirements

This crate requires LLVM 18.0 to be installed on your system.

### Installation

**Linux (Ubuntu/Debian):**
```bash
sudo apt-get install llvm-18 llvm-18-dev
```

**macOS:**
```bash
brew install llvm@18
```

**Windows:**
Download from https://releases.llvm.org/

### Optional Feature

The LLVM backend is behind a feature flag. To enable:

```toml
[dependencies]
rv-llvm-backend = { path = "...", features = ["llvm"] }
```

Without the feature enabled, the crate will compile but return errors when attempting to use LLVM functionality.

## Optimization Levels

- **None**: No optimization, fastest compilation
- **Less**: Basic optimizations, fast compilation
- **Default**: Standard optimizations, balanced
- **Aggressive**: Maximum optimization, slower compilation

## Supported Types

- Integers: `i32`, `i64`, `u32`, `u64`
- Floats: `f32`, `f64`
- Boolean: `bool`
- Unit: `()`
- Pointers: `*T`
- Arrays: `[T; N]`
- Structs: `struct { fields... }`
- Functions: `fn(params...) -> ret`

## Supported Operations

### Binary Operations
- Arithmetic: `+`, `-`, `*`, `/`, `%`
- Bitwise: `&`, `|`, `^`, `<<`, `>>`
- Comparison: `==`, `!=`, `<`, `<=`, `>`, `>=`

### Unary Operations
- Negation: `-x`
- Bitwise NOT: `!x`

### Control Flow
- Return statements
- Unconditional branches
- Conditional switches
- Function calls

## Example

```rust
use rv_mir::*;
use rv_llvm_backend::{compile_to_llvm_ir, OptLevel};

// Create function: fn add(a: i32, b: i32) -> i32 { a + b }
let mut func = MirFunction::new("add".to_string(), Type::I32);
func.add_parameter("a".to_string(), Type::I32);
func.add_parameter("b".to_string(), Type::I32);

let result = func.add_local("result".to_string(), Type::I32);
let bb0 = func.add_basic_block();

func.add_statement(bb0, Statement::Assign {
    place: Place::new(result),
    rvalue: Rvalue::BinaryOp {
        op: BinaryOp::Add,
        left: Operand::Copy(Place::new(0)),
        right: Operand::Copy(Place::new(1)),
    },
});

func.set_terminator(bb0, Terminator::Return(Some(Operand::Copy(Place::new(result)))));

// Compile to LLVM IR
let ir = compile_to_llvm_ir(&[func], OptLevel::Default)?;
println!("{}", ir);
```

## License

MIT OR Apache-2.0
