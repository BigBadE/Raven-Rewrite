# Analysis: Integrating Rust's Standard Library

## Executive Summary

Using Rust's standard library (std) in Raven-compiled code requires implementing several major compiler features that bridge the gap between our current minimal implementation and full Rust compatibility. This document analyzes what's required and provides a roadmap.

## Current State vs. Requirements

### What We Have ✅
- **MIR generation** - Control flow graphs with basic blocks
- **3 backends** - Interpreter, Cranelift JIT, LLVM AOT
- **Type inference** - Hindley-Milner with unification
- **Basic types** - Int, Float, Bool, String, Unit
- **Primitives** - Arithmetic, comparisons, if/else, function calls (internal only)
- **Name resolution** - Local variables, function names

### What std Requires ❌
- **External function calls** - FFI/linking to Rust runtime
- **Complex types** - Structs, enums, tuples, arrays, slices
- **Trait system** - Trait definitions, implementations, bounds
- **Generics** - Type parameters, monomorphization at call sites
- **Memory model** - Ownership, borrowing, lifetimes
- **Pattern matching** - Destructuring, exhaustiveness checking
- **Methods** - Impl blocks, self parameters, method call syntax
- **Standard library ABI** - Calling conventions, name mangling
- **Advanced features** - Closures, iterators, dynamic dispatch

## Required Components (Detailed Analysis)

### 1. External Function Calls & FFI

**What it is:**
Currently, Raven can only call functions defined within the same compilation unit. To use std, we need to call external functions from libstd.rlib (Rust's compiled standard library).

**Implementation Requirements:**

#### A. HIR Level
```rust
// rv-hir additions
pub enum Expr {
    // Existing variants...

    // NEW: External function call
    ExternalCall {
        function: Symbol,      // Fully qualified name like "std::vec::Vec::new"
        args: Vec<ExprId>,
        span: FileSpan,
    },
}

pub struct ExternalFunction {
    pub name: Symbol,          // "std::vec::Vec::new"
    pub mangled_name: String,  // "_ZN3std3vec3Vec3new17h1234567890abcdefE"
    pub params: Vec<TyId>,
    pub return_ty: TyId,
    pub is_unsafe: bool,
}
```

#### B. MIR Level
```rust
// rv-mir additions
pub enum Terminator {
    // Existing variants...

    // NEW: External call
    ExternalCall {
        function: String,      // Mangled name for linker
        args: Vec<Operand>,
        destination: Place,
        target: usize,         // Next basic block
    },
}
```

#### C. Backend Implementation

**Interpreter:**
- Cannot execute external calls directly
- Would need to either:
  - Dynamically load libstd.so and call via dlopen/dlsym
  - Or skip std execution in interpreter mode

**Cranelift:**
```rust
// In rv-cranelift
impl JitCompiler {
    fn compile_external_call(&mut self, name: &str, args: &[Value]) -> Value {
        // Look up function symbol in libstd
        let func_ptr = self.resolve_external_symbol(name)?;

        // Create Cranelift function signature
        let sig = self.create_signature_from_mangled_name(name)?;

        // Generate indirect call
        let func_ref = self.builder.ins().iconst(types::I64, func_ptr as i64);
        self.builder.ins().call_indirect(sig, func_ref, args)
    }
}
```

**LLVM:**
```rust
// In rv-llvm-backend
impl LLVMBackend {
    fn compile_external_call(&mut self, name: &str, args: &[Value]) -> Value {
        // Declare external function
        let func = self.module.add_function(name, func_type, None);
        func.set_linkage(Linkage::External);

        // Generate call instruction
        self.builder.build_call(func, args, "call_result")
    }
}
```

#### D. Linking
```bash
# Currently: Only link our generated .o file
ld.lld -o output.exe our_code.o

# With std: Must link against Rust runtime
ld.lld -o output.exe our_code.o \
    /path/to/rust/lib/libstd.rlib \
    /path/to/rust/lib/libcore.rlib \
    /path/to/rust/lib/liballoc.rlib \
    -lpthread -ldl -lm
```

**Complexity:** 🔴 **High** - Requires understanding Rust's ABI, name mangling, calling conventions

**Estimated Effort:** 2-3 weeks

---

### 2. Struct and Enum Types

**What it is:**
Rust's std is built on algebraic data types (ADTs) - structs and enums. For example, `Vec<T>` is a struct with fields `ptr`, `len`, `cap`.

**Implementation Requirements:**

#### A. HIR Additions
```rust
// rv-hir
pub struct StructDef {
    pub id: DefId,
    pub name: Symbol,
    pub fields: Vec<FieldDef>,
    pub generic_params: Vec<Symbol>,  // For Vec<T>, this is ["T"]
}

pub struct FieldDef {
    pub name: Symbol,
    pub ty: TyId,
    pub visibility: Visibility,
}

pub struct EnumDef {
    pub id: DefId,
    pub name: Symbol,
    pub variants: Vec<VariantDef>,
    pub generic_params: Vec<Symbol>,
}

pub struct VariantDef {
    pub name: Symbol,
    pub fields: VariantFields,
}

pub enum VariantFields {
    Unit,                           // None
    Tuple(Vec<TyId>),              // Some(T)
    Struct(Vec<FieldDef>),         // Point { x: i32, y: i32 }
}
```

#### B. Type System
```rust
// rv-ty additions
pub enum TyKind {
    // Existing: Int, Float, Bool, String, Unit, Function...

    // NEW:
    Struct {
        def_id: DefId,
        fields: Vec<(Symbol, TyId)>,
    },
    Enum {
        def_id: DefId,
        variants: Vec<(Symbol, VariantTy)>,
    },
    Tuple(Vec<TyId>),
    Array { element: TyId, size: usize },
    Slice { element: TyId },
}
```

#### C. MIR Additions
```rust
// rv-mir
pub enum Projection {
    Field { field_idx: usize },    // s.field_name
    Index { index: LocalId },      // array[i]
    Deref,                          // *ptr
}

pub struct Place {
    pub local: LocalId,
    pub projection: Vec<Projection>,  // NEW: Field access chain
}

// Example: s.foo.bar becomes:
// Place {
//     local: LocalId(0),  // s
//     projection: [
//         Projection::Field { field_idx: 0 },  // .foo
//         Projection::Field { field_idx: 1 },  // .bar
//     ]
// }
```

#### D. Memory Layout
```rust
// Need to calculate struct layout for backends
pub struct StructLayout {
    pub size: usize,
    pub align: usize,
    pub field_offsets: Vec<usize>,
}

impl StructLayout {
    fn compute(fields: &[(Symbol, TyId)]) -> Self {
        // Calculate size, alignment, field offsets
        // Following Rust's layout rules
    }
}
```

**Complexity:** 🟡 **Medium** - Core feature, but well-understood

**Estimated Effort:** 2-3 weeks

---

### 3. Trait System

**What it is:**
Traits are Rust's mechanism for polymorphism. Most std functions are implemented as trait methods. For example, `vec.push()` is actually `Vec::push(&mut self, value: T)` from the trait implementation.

**Implementation Requirements:**

#### A. HIR Additions
```rust
pub struct TraitDef {
    pub id: DefId,
    pub name: Symbol,
    pub items: Vec<TraitItem>,
    pub super_traits: Vec<DefId>,  // trait Foo: Bar
}

pub enum TraitItem {
    Method {
        name: Symbol,
        sig: FunctionSig,
        default_impl: Option<Body>,
    },
    AssociatedType {
        name: Symbol,
        bounds: Vec<DefId>,
    },
}

pub struct TraitImpl {
    pub trait_id: DefId,
    pub for_ty: TyId,
    pub items: Vec<ImplItem>,
}
```

#### B. Type Checking
```rust
// rv-ty additions
impl TypeInference {
    fn check_trait_bound(&mut self, ty: TyId, trait_id: DefId) -> Result<()> {
        // Check if type implements trait
        // Search for matching impl in HIR
    }

    fn resolve_trait_method(&mut self, receiver_ty: TyId, method: Symbol)
        -> Result<DefId> {
        // Find which trait provides this method
        // Check if receiver_ty implements that trait
        // Return the impl's method definition
    }
}
```

#### C. Monomorphization Impact
```rust
// Currently: MonoCollector only handles direct function calls
// With traits: Must handle trait method calls

impl MonoCollector {
    fn visit_trait_method_call(&mut self, receiver_ty: TyId, method: Symbol) {
        // Find the impl for (receiver_ty, trait)
        // Collect the method as a mono instance
        let impl_method = self.resolve_trait_method(receiver_ty, method);
        self.collect_function(impl_method);
    }
}
```

**Complexity:** 🔴 **Very High** - Complex type system feature

**Estimated Effort:** 4-6 weeks

---

### 4. Generics & Monomorphization

**What it is:**
Rust's std is heavily generic (Vec<T>, HashMap<K,V>, etc.). Every use of a generic type/function must be monomorphized (specialized) to a concrete type.

**Current State:**
- We have basic MonoContext/MonoCollector
- Only handles simple function instantiation
- No generic parameter substitution

**Requirements:**

#### A. Generic Parameter Tracking
```rust
pub struct GenericParams {
    pub types: Vec<Symbol>,        // <T, U>
    pub lifetimes: Vec<Symbol>,    // <'a, 'b>
    pub consts: Vec<Symbol>,       // <const N: usize>
}

pub struct MonoInstance {
    pub def_id: DefId,
    pub substs: Substitutions,     // T -> i32, U -> String
}

pub struct Substitutions {
    pub types: FxHashMap<Symbol, TyId>,
    pub lifetimes: FxHashMap<Symbol, Lifetime>,
    pub consts: FxHashMap<Symbol, ConstValue>,
}
```

#### B. Type Substitution During Lowering
```rust
// When lowering generic function to MIR
impl LoweringContext {
    fn lower_generic_function(
        &mut self,
        func: &Function,
        substs: &Substitutions
    ) -> MirFunction {
        // Replace all type variables with concrete types
        // T -> i32, U -> String

        for stmt in &func.body.stmts {
            let ty = self.get_expr_type(stmt.expr);
            let concrete_ty = self.substitute(ty, substs);
            // Use concrete_ty in MIR
        }
    }
}
```

#### C. Recursive Monomorphization
```rust
// Example: Vec<Vec<i32>>
// 1. Monomorphize Vec<Vec<i32>>
//    - Sees field: Vec<T> where T=i32
// 2. Monomorphize Vec<i32>
//    - Now have both instances

impl MonoCollector {
    fn collect_type(&mut self, ty: TyId, substs: &Substitutions) {
        match ty.kind() {
            TyKind::Struct { fields, .. } => {
                for (_, field_ty) in fields {
                    let concrete = self.substitute(field_ty, substs);
                    self.collect_type(concrete, substs);
                }
            }
            // ...
        }
    }
}
```

**Complexity:** 🔴 **Very High** - Core to Rust's design

**Estimated Effort:** 4-5 weeks

---

### 5. Pattern Matching

**What it is:**
Rust's match expressions with destructuring. Essential for working with enums like `Option<T>` and `Result<T, E>`.

```rust
match some_option {
    Some(value) => { /* use value */ },
    None => { /* handle None */ },
}
```

**Implementation Requirements:**

#### A. HIR
```rust
pub enum Expr {
    // ...
    Match {
        scrutinee: ExprId,
        arms: Vec<MatchArm>,
        span: FileSpan,
    },
}

pub struct MatchArm {
    pub pattern: PatternId,
    pub guard: Option<ExprId>,     // if condition
    pub body: ExprId,
}

pub enum Pattern {
    Wildcard,                      // _
    Literal(LiteralKind),          // 42, "foo"
    Binding(Symbol),               // x
    Tuple(Vec<PatternId>),        // (x, y, z)
    Struct {                       // Point { x, y }
        name: Symbol,
        fields: Vec<(Symbol, PatternId)>,
    },
    Enum {                         // Some(x)
        variant: Symbol,
        sub_patterns: Vec<PatternId>,
    },
}
```

#### B. MIR Lowering (Complex!)
```rust
// Match lowering creates a decision tree
// Example: match opt { Some(x) => x, None => 0 }

// Block 0: Test if variant is Some
let discriminant = read_discriminant(scrutinee);
SwitchInt {
    discriminant,
    targets: { 0 => block_some, 1 => block_none },
}

// Block Some: Extract value
let value = read_field(scrutinee, 0);  // Get T from Some(T)
assign(result, value);
goto block_after;

// Block None:
assign(result, 0);
goto block_after;

// Block After: Continue...
```

#### C. Exhaustiveness Checking
```rust
// Must ensure all variants are covered
fn check_exhaustiveness(patterns: &[Pattern], ty: TyId) -> Result<()> {
    match ty.kind() {
        TyKind::Enum { variants, .. } => {
            let covered = collect_covered_variants(patterns);
            let all_variants: HashSet<_> = variants.iter().collect();
            let missing = all_variants.difference(&covered);

            if !missing.is_empty() {
                return Err(Error::NonExhaustiveMatch { missing });
            }
        }
    }
    Ok(())
}
```

**Complexity:** 🔴 **Very High** - Complex algorithm

**Estimated Effort:** 3-4 weeks

---

### 6. Method Call Syntax

**What it is:**
Being able to write `vec.push(item)` instead of `Vec::push(&mut vec, item)`.

**Requirements:**

#### A. HIR
```rust
pub enum Expr {
    // ...
    MethodCall {
        receiver: ExprId,     // vec
        method: Symbol,       // "push"
        args: Vec<ExprId>,    // [item]
        span: FileSpan,
    },
}
```

#### B. Name Resolution
```rust
impl NameResolver {
    fn resolve_method_call(&mut self, receiver_ty: TyId, method: Symbol)
        -> Result<DefId> {
        // 1. Look for inherent impl: impl Vec<T> { fn push(...) }
        // 2. Look for trait impl: impl<T> Push<T> for Vec<T>
        // 3. Check auto-deref: if receiver is &T, try T
        // 4. Check auto-ref: if method expects &self, add &
    }
}
```

#### C. Auto-ref/Auto-deref
```rust
// Rust automatically inserts & and * as needed
vec.push(item)       // vec is Vec<T>
                     // push expects &mut self
                     // Becomes: Vec::push(&mut vec, item)

ptr.len()            // ptr is &Vec<T>
                     // len expects &self
                     // Becomes: Vec::len(ptr) (auto-deref)
```

**Complexity:** 🟡 **Medium-High** - Subtle rules

**Estimated Effort:** 2-3 weeks

---

### 7. Memory Model (Ownership/Borrowing/Lifetimes)

**What it is:**
Rust's core safety feature. Must track ownership, borrowing rules, and lifetime parameters.

**This is MASSIVE.** Would need:

#### A. Borrow Checker
```rust
pub struct BorrowChecker {
    loans: FxHashMap<Place, LoanData>,
}

pub struct LoanData {
    pub kind: BorrowKind,      // Shared, Mutable, Move
    pub lifetime: Lifetime,
    pub issued_at: Location,
}

impl BorrowChecker {
    fn check_function(&mut self, mir: &MirFunction) -> Vec<BorrowError> {
        // Track all borrows
        // Ensure no:
        // - Use after move
        // - Mutable alias
        // - Use after lifetime ends
    }
}
```

#### B. Lifetime Inference
```rust
pub struct LifetimeInference {
    constraints: Vec<LifetimeConstraint>,
}

pub enum LifetimeConstraint {
    Outlives { a: Lifetime, b: Lifetime },  // 'a: 'b
    Equal { a: Lifetime, b: Lifetime },      // 'a = 'b
}
```

#### C. Drop Elaboration
```rust
// Insert drop calls at end of scope
fn elaborate_drops(mir: &mut MirFunction) {
    for block in &mut mir.blocks {
        for local in &block.live_vars {
            if needs_drop(local.ty) {
                insert_drop_call(block, local);
            }
        }
    }
}
```

**Complexity:** 🔴🔴🔴 **Extremely High** - This alone is months of work

**Estimated Effort:** 8-12 weeks (or more)

---

### 8. Name Mangling

**What it is:**
Rust uses a specific name mangling scheme to encode function signatures in symbol names.

```rust
// Source: std::vec::Vec<i32>::new
// Mangled: _ZN3std3vec3Vec3new17h1234567890abcdefE
//          ^   ^   ^   ^   ^   ^   ^^^^^^^^^^^^^^^^
//          |   |   |   |   |   |   Hash of signature
//          |   |   |   |   |   Name
//          |   |   |   |   Namespace
//          |   |   |   Namespace
//          |   |   Namespace
//          |   Start
//          Prefix
```

**Implementation:**
```rust
pub fn mangle_name(path: &[Symbol], generics: &[TyId]) -> String {
    // Follow Rust's v0 mangling scheme
    // https://rust-lang.github.io/rfcs/2603-rust-symbol-name-mangling-v0.html
}

pub fn demangle_name(mangled: &str) -> Result<(Vec<Symbol>, Vec<TyId>)> {
    // Parse mangled name back to path + generics
}
```

**Complexity:** 🟡 **Medium** - Well-documented, but tedious

**Estimated Effort:** 1-2 weeks

---

## Implementation Roadmap

### Minimum Viable std Integration (Phase 1)

**Goal:** Call simple std functions like `println!` and use `Vec<T>`

**Requirements (in order):**
1. ✅ **Structs** (2-3 weeks)
   - Struct definitions in HIR
   - Field access in MIR
   - Memory layout calculation
   - Backend support for field access

2. ✅ **Basic Generics** (3-4 weeks)
   - Generic type parameters in HIR
   - Substitution during monomorphization
   - Type parameter tracking

3. ✅ **External Calls** (2-3 weeks)
   - External function declarations
   - Name mangling
   - Linking against libstd

4. ✅ **Method Calls** (2-3 weeks)
   - Method call syntax
   - Inherent impls
   - Basic auto-ref/deref

**Total:** ~10-13 weeks

**Result:** Can use `Vec::new()`, `Vec::push()`, `println!()` (via external call)

---

### Full std Support (Phase 2)

**Additional Requirements:**
5. ✅ **Enums** (2-3 weeks)
   - Enum definitions with variants
   - Discriminant tracking
   - Tag + payload layout

6. ✅ **Pattern Matching** (3-4 weeks)
   - Match expressions
   - Pattern compilation to MIR
   - Exhaustiveness checking

7. ✅ **Trait System** (4-6 weeks)
   - Trait definitions
   - Trait implementations
   - Trait method resolution
   - Trait bounds

8. ✅ **Advanced Generics** (3-4 weeks)
   - Where clauses
   - Associated types
   - Generic constraints

**Total:** +12-17 weeks (22-30 weeks cumulative)

**Result:** Can use `Option<T>`, `Result<T,E>`, `Iterator` trait, most std APIs

---

### Production Ready (Phase 3)

**Additional Requirements:**
9. ✅ **Borrowing** (8-12 weeks)
   - Borrow checker
   - Lifetime inference
   - Move semantics

10. ✅ **Advanced Features** (4-6 weeks)
    - Closures
    - Deref coercion
    - Drop elaboration
    - Trait objects (dyn Trait)

**Total:** +12-18 weeks (34-48 weeks cumulative)

**Result:** Full Rust compatibility

---

## Alternative Approach: Minimal Runtime

Instead of using Rust's full std, we could create a minimal runtime with just the essentials:

```rust
// raven-runtime/src/lib.rs

#[no_std]
pub mod vec {
    pub struct Vec<T> {
        ptr: *mut T,
        len: usize,
        cap: usize,
    }

    impl<T> Vec<T> {
        pub fn new() -> Self { /* ... */ }
        pub fn push(&mut self, value: T) { /* ... */ }
        // Minimal API
    }
}

pub mod string {
    pub struct String {
        vec: crate::vec::Vec<u8>,
    }
    // Minimal string operations
}

// etc.
```

**Advantages:**
- Much simpler to implement
- No trait system needed initially
- No complex generics
- Full control over ABI

**Disadvantages:**
- Not compatible with real Rust std
- Can't use existing crates
- Reimplementing basic functionality

**Estimated Effort:** 4-6 weeks for basic collections

---

## Recommendations

### Short Term (Next 3-6 months)
1. **Focus on language features first** - Structs, enums, methods
2. **Implement minimal runtime** - Just Vec, String, basic I/O
3. **Skip borrowing for now** - Use GC or reference counting
4. **Defer full std** - Not needed for most programs

### Medium Term (6-12 months)
1. **Add trait system** - Enables idiomatic Rust
2. **Implement pattern matching** - Essential for enums
3. **Basic generics** - Type parameters and substitution

### Long Term (12+ months)
1. **Borrowing checker** - For safety guarantees
2. **Full std compatibility** - Link against real libstd
3. **Advanced features** - Closures, trait objects, etc.

## Conclusion

**Using Rust's std is a MASSIVE undertaking.** Even the minimal viable version requires:
- Structs
- Generics
- External calls
- Methods
- Name mangling

This represents **10-13 weeks** of focused work.

**Full std support** with traits, pattern matching, and borrowing would take **34-48 weeks** (8-12 months).

**Recommendation:** Start with a minimal custom runtime to gain experience with these features before attempting full std integration.
