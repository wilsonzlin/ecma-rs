---
task_id: "03-implementation/09-using-await-using"
phase: "03-implementation"
title: "Implement using and await using Declarations"
dependencies:
  - "02-planning/02-design-ast-nodes"
  - "02-planning/03-plan-parser-extensions"
inputs:
  - "workspace/outputs/02-planning/02-design-ast-nodes/ast-extensions.md"
  - "workspace/outputs/02-planning/03-plan-parser-extensions/parser-plan.md"
outputs:
  - "parse-js/src/ast/stmt.rs" (modified)
  - "parse-js/src/parse/stmt.rs" (modified)
  - "parse-js/tests/using_declarations.rs"
  - "workspace/outputs/03-implementation/09-using-await-using/implementation-report.md"
estimated_duration: "3-4 hours"
complexity: "medium"
priority: "medium"
---

# Task: Implement using and await using Declarations

## Objective

Implement TypeScript 5.2+ `using` and `await using` declarations for explicit resource management (ECMAScript Explicit Resource Management proposal).

## Context

TypeScript 5.2 added support for the ECMAScript Explicit Resource Management proposal, which introduces:
- `using` declarations for synchronous resource disposal
- `await using` declarations for asynchronous resource disposal
- `Symbol.dispose` and `Symbol.asyncDispose` methods

### Use Case

```typescript
// Automatic resource cleanup
{
    using file = openFile("data.txt");
    // Use file...
}  // file.Symbol.dispose() called automatically

// Async resource cleanup
{
    await using connection = connectDB();
    // Use connection...
}  // await connection.Symbol.asyncDispose() called automatically

// Multiple resources
{
    using fs1 = openFile("a.txt");
    using fs2 = openFile("b.txt");
    // Both disposed in reverse order
}
```

### Current State
`using` and `await using` are likely not implemented yet.

### Target Features

```typescript
// 1. Basic using
using file = openFile("data.txt");

// 2. await using
await using connection = connectDB();

// 3. Destructuring
using { handle } = createResource();

// 4. Multiple declarations
using fs1 = openFile("a.txt"), fs2 = openFile("b.txt");

// 5. In for-of loops
for (using item of items) {
    // item disposed after each iteration
}

// 6. await using in for-await-of
for await (await using item of asyncItems) {
    // async disposal
}

// 7. Type annotations
using file: FileHandle = openFile("data.txt");

// 8. Null/undefined (no disposal)
using maybeFile = condition ? openFile() : null;
```

## Instructions

### Step 1: Check Current State

```bash
# Test using (likely fails)
cargo run --example parse -- 'using file = openFile("data.txt");'

# Test await using (likely fails)
cargo run --example parse -- 'await using conn = connectDB();'
```

### Step 2: Extend AST

**File**: `parse-js/src/ast/stmt.rs`

Add new declaration kind for `using`:

```rust
#[derive(Debug, Clone, Serialize)]
pub enum Stmt {
    // ... existing variants ...

    /// using/await using declaration
    UsingDecl(UsingDecl),

    // ... other variants ...
}

#[derive(Debug, Clone, Serialize)]
pub struct UsingDecl {
    pub is_await: bool,  // true for 'await using'
    pub declarators: Vec<UsingDeclarator>,
}

#[derive(Debug, Clone, Serialize)]
pub struct UsingDeclarator {
    pub pattern: BindingPattern,  // name or destructuring pattern
    pub type_annotation: Option<Node<TypeExpr>>,
    pub init: Node<Expr>,  // Required - using must have initializer
}

// Or, if you want to extend existing VarDecl:
#[derive(Debug, Clone, Serialize)]
pub struct VarDecl {
    pub kind: VarDeclKind,  // Updated to include Using
    pub declarators: Vec<VarDeclarator>,
}

#[derive(Debug, Clone, Copy, Serialize)]
pub enum VarDeclKind {
    Var,
    Let,
    Const,
    Using,       // ADD: using
    AwaitUsing,  // ADD: await using
}
```

**Recommendation**: Add `Using` and `AwaitUsing` to `VarDeclKind` - they're semantically similar to variable declarations.

### Step 3: Update Lexer (if needed)

Check if `using` needs to be a keyword:

**Answer**: `using` is a **contextual keyword** - only has special meaning at start of declaration statement.

**Action**: Don't add to lexer keywords. Handle in parser based on context.

### Step 4: Implement Parser

**File**: `parse-js/src/parse/stmt.rs`

#### 4.1: Update Statement Parser

```rust
impl<'a> Parser<'a> {
    fn statement(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<Stmt>> {
        match self.peek().typ {
            TT::KeywordVar | TT::KeywordLet | TT::KeywordConst => {
                self.variable_declaration(ctx)
            }

            // Check for 'using' keyword (contextual)
            TT::Identifier if self.peek().value == "using" => {
                // Look ahead to confirm it's a declaration
                // Could be: using x = ... or await using x = ...
                let next = self.peek_nth(1).typ;

                if matches!(next, TT::Identifier | TT::BraceOpen | TT::BracketOpen) {
                    // It's a using declaration
                    self.using_declaration(ctx)
                } else {
                    // It's an identifier 'using' (e.g., function call)
                    self.expression_statement(ctx)
                }
            }

            // Check for 'await using'
            TT::KeywordAwait => {
                let next = self.peek_nth(1);

                if next.typ == TT::Identifier && next.value == "using" {
                    // It's await using declaration
                    self.using_declaration(ctx)
                } else {
                    // Regular await expression
                    self.expression_statement(ctx)
                }
            }

            // ... other statement types ...
        }
    }

    fn using_declaration(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<Stmt>> {
        let start = self.lexer.loc_start();

        // Check for 'await'
        let is_await = if self.peek().typ == TT::KeywordAwait {
            self.consume();
            true
        } else {
            false
        };

        // Expect 'using'
        if self.peek().typ != TT::Identifier || self.peek().value != "using" {
            return Err(SyntaxError::expected("using"));
        }
        self.consume();

        // Parse declarators
        let mut declarators = Vec::new();

        loop {
            let declarator = self.using_declarator(ctx)?;
            declarators.push(declarator);

            if !self.consume_if(TT::Comma).is_match() {
                break;
            }
        }

        self.consume_semicolon();

        Ok(Node::new(
            self.loc_range(start),
            Stmt::VarDecl(VarDecl {
                kind: if is_await {
                    VarDeclKind::AwaitUsing
                } else {
                    VarDeclKind::Using
                },
                declarators: declarators.into_iter()
                    .map(|d| VarDeclarator {
                        pattern: d.pattern,
                        type_annotation: d.type_annotation,
                        init: Some(d.init),
                    })
                    .collect(),
            }),
        ))
    }

    fn using_declarator(&mut self, ctx: ParseCtx) -> SyntaxResult<UsingDeclarator> {
        // Parse pattern (identifier or destructuring)
        let pattern = self.binding_pattern(ctx)?;

        // Parse optional type annotation
        let type_annotation = if self.consume_if(TT::Colon).is_match() {
            Some(self.type_expr(ParseCtx::default())?)
        } else {
            None
        };

        // Require initializer
        if !self.consume_if(TT::Equals).is_match() {
            return Err(SyntaxError::new(
                "'using' declarations must have an initializer",
                self.peek().loc,
            ));
        }

        let init = self.assignment_expr(ctx)?;

        Ok(UsingDeclarator {
            pattern,
            type_annotation,
            init,
        })
    }
}
```

#### 4.2: Update for-of Loop Parser

**File**: `parse-js/src/parse/stmt.rs`

```rust
fn for_statement(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<Stmt>> {
    // ... existing code ...

    self.expect(TT::ParenOpen)?;

    // Check for 'await' (for-await-of)
    let is_await = self.consume_if(TT::KeywordAwait).is_match();

    // Check for 'using' or 'await using'
    let using_kind = if self.peek().typ == TT::Identifier && self.peek().value == "using" {
        self.consume();
        Some(if is_await {
            VarDeclKind::AwaitUsing
        } else {
            VarDeclKind::Using
        })
    } else {
        None
    };

    // Parse variable declaration or expression
    let init = if let Some(kind) = using_kind {
        // Parse using declaration in for-of
        let pattern = self.binding_pattern(ctx)?;

        // Type annotation optional
        let type_annotation = if self.consume_if(TT::Colon).is_match() {
            Some(self.type_expr(ParseCtx::default())?)
        } else {
            None
        };

        // No initializer in for-of
        ForInit::VarDecl(VarDecl {
            kind,
            declarators: vec![VarDeclarator {
                pattern,
                type_annotation,
                init: None,
            }],
        })
    } else {
        // ... existing code for other for loop types
        todo!()
    };

    // ... rest of for loop parsing ...
}
```

### Step 5: Write Tests

**File**: `parse-js/tests/using_declarations.rs`

```rust
use parse_js::*;

#[test]
fn test_using_basic() {
    let src = r#"using file = openFile("data.txt");"#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_await_using() {
    let src = r#"await using connection = connectDB();"#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_using_with_type() {
    let src = r#"using file: FileHandle = openFile("data.txt");"#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_using_destructuring() {
    let src = r#"using { handle, cleanup } = createResource();"#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_using_array_destructuring() {
    let src = r#"using [first, second] = getResources();"#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_using_multiple() {
    let src = r#"using fs1 = openFile("a.txt"), fs2 = openFile("b.txt");"#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_using_in_block() {
    let src = r#"
        {
            using file = openFile("data.txt");
            console.log(file);
        }
    "#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_using_for_of() {
    let src = r#"
        for (using item of items) {
            console.log(item);
        }
    "#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_await_using_for_await_of() {
    let src = r#"
        for await (await using item of asyncItems) {
            console.log(item);
        }
    "#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_using_null_coalescing() {
    let src = r#"using file = condition ? openFile() : null;"#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_using_without_initializer_fails() {
    let src = r#"using file;"#;
    let result = parse(src);
    assert!(result.is_err(), "using requires initializer");
}

#[test]
fn test_using_as_identifier() {
    // 'using' can be used as identifier in non-declaration contexts
    let src = r#"const using = 1;"#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_using_function_call() {
    let src = r#"using(arg1, arg2);"#;
    let result = parse(src);
    assert!(result.is_ok(), "'using' should work as function name");
}

#[test]
fn test_regular_var_still_works() {
    let src = r#"var x = 1; let y = 2; const z = 3;"#;
    let result = parse(src);
    assert!(result.is_ok());
}
```

### Step 6: Run Tests

```bash
cargo test using_declarations
cargo test
cargo test --release conformance_runner -- --filter "using"
```

### Step 7: Create Implementation Report

**File**: `workspace/outputs/03-implementation/09-using-await-using/implementation-report.md`

[Standard format]

## Verification Commands

```bash
cargo check
cargo test using_declarations
echo 'using x = openFile()' | cargo run --example parse
echo 'await using x = connectDB()' | cargo run --example parse
```

## Common Issues

### Issue 1: using as Identifier vs Keyword
**Problem**: `using` can be identifier name or keyword

**Solution**: Context-sensitive - at statement start before identifier/pattern = keyword, otherwise = identifier

### Issue 2: await using Ambiguity
**Problem**: `await using` could be `await` expression with `using` identifier

**Solution**: Look ahead - `await using <identifier> =` is declaration, `await using(...)` is function call

### Issue 3: Initializer Required
**Problem**: `using x;` without initializer

**Solution**: Return error - using declarations must have initializers (unlike let/const which don't require initializers in declarations)

## Acceptance Criteria

- [ ] `using` declarations parse correctly
- [ ] `await using` declarations parse correctly
- [ ] Works with destructuring patterns
- [ ] Works in for-of loops
- [ ] Requires initializer (error if missing)
- [ ] `using` usable as identifier in non-declaration contexts
- [ ] All tests pass
- [ ] Conformance tests improve
- [ ] Implementation report created

## Success Metrics

- All test cases pass
- Conformance improvement: +3-7%
- Zero regressions

## Resources

- TypeScript 5.2 Release Notes: Using Declarations and Explicit Resource Management
- ECMAScript Proposal: Explicit Resource Management
- TC39 Proposal: https://github.com/tc39/proposal-explicit-resource-management
- TypeScript source: `src/compiler/parser.ts` - `parseVariableStatement`

## Notes

The `using` and `await using` syntax is part of the ECMAScript Explicit Resource Management proposal (Stage 3 as of 2024). TypeScript adopted it in version 5.2. The semantic meaning (calling Symbol.dispose/Symbol.asyncDispose) is runtime behavior - the parser only needs to recognize the syntax.
