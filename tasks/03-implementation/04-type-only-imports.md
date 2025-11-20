---
task_id: "03-implementation/04-type-only-imports"
phase: "03-implementation"
title: "Implement Type-Only Import/Export Syntax"
dependencies:
  - "02-planning/02-design-ast-nodes"
  - "02-planning/03-plan-parser-extensions"
inputs:
  - "workspace/outputs/02-planning/02-design-ast-nodes/ast-extensions.md"
  - "workspace/outputs/02-planning/03-plan-parser-extensions/parser-plan.md"
outputs:
  - "parse-js/src/ast/stmt.rs" (modified)
  - "parse-js/src/parse/stmt.rs" (modified)
  - "parse-js/tests/type_only_imports.rs"
  - "workspace/outputs/03-implementation/04-type-only-imports/implementation-report.md"
estimated_duration: "4-5 hours"
complexity: "medium"
priority: "high"
---

# Task: Implement Type-Only Import/Export Syntax

## Objective

Implement full support for TypeScript's type-only import and export syntax:
- `import type { T } from "mod"`
- `export type { T }`
- `import { type T, value } from "mod"` (inline type specifier)
- `export { type T }`

## Context

TypeScript 3.8+ introduced `import type` and `export type` to explicitly mark imports/exports that are used only in type positions. This helps:
- **Bundlers**: Remove type-only imports completely (dead code elimination)
- **TypeScript**: Avoid circular dependency issues
- **Developers**: Document intent (type vs value import)

TypeScript 4.5+ added inline `type` specifiers to mix type and value imports in a single statement.

### Current State
Check if basic import/export parsing exists and whether type-only syntax is supported.

### Target Features

```typescript
// 1. Import type (entire import is type-only)
import type { User, Post } from "./types";
import type * as Types from "./types";
import type DefaultType from "./types";

// 2. Export type (entire export is type-only)
export type { User, Post };
export type { User as U };
export type * from "./types";
export type * as Types from "./types";

// 3. Inline type specifiers (mixed import)
import { type User, createUser } from "./api";
import { Component, type Props } from "react";

// 4. Inline type in export
export { type User, createUser };

// 5. Re-export with type
export { type User } from "./types";

// 6. Type-only default
import type React from "react";
export type { default as React } from "react";
```

## Instructions

### Step 1: Understand Current AST

Check existing import/export AST:

```bash
# Find AST definitions
rg "struct.*Import" parse-js/src/ast/
rg "struct.*Export" parse-js/src/ast/

# Test current parsing
cargo run --example parse -- 'import { User } from "mod"'
cargo run --example parse -- 'import type { User } from "mod"'
```

### Step 2: Extend AST (if needed)

**File**: `parse-js/src/ast/stmt.rs`

Expected structure:

```rust
#[derive(Debug, Clone, Serialize)]
pub struct ImportStmt {
    pub specifiers: Vec<ImportSpecifier>,
    pub source: String,
    pub type_only: bool,  // ADD: true for `import type`
}

#[derive(Debug, Clone, Serialize)]
pub enum ImportSpecifier {
    Named {
        imported: String,     // Original name
        local: String,        // Local name (after 'as')
        type_only: bool,      // ADD: true for inline `type` specifier
    },
    Default {
        local: String,
        type_only: bool,      // ADD: for `import type Default`
    },
    Namespace {
        local: String,        // Name after 'as'
        type_only: bool,      // ADD: for `import type * as NS`
    },
}

#[derive(Debug, Clone, Serialize)]
pub struct ExportStmt {
    pub specifiers: Option<Vec<ExportSpecifier>>,
    pub source: Option<String>,
    pub type_only: bool,  // ADD: true for `export type`
    // ... other fields
}

#[derive(Debug, Clone, Serialize)]
pub enum ExportSpecifier {
    Named {
        local: String,        // Local name
        exported: String,     // Exported name (after 'as')
        type_only: bool,      // ADD: inline type specifier
    },
    Namespace {
        exported: Option<String>,  // Name after 'as'
        type_only: bool,
    },
}
```

### Step 3: Implement Import Parser

**File**: `parse-js/src/parse/stmt.rs`

#### 3.1: Update Import Statement Parser

```rust
impl<'a> Parser<'a> {
    fn import_stmt(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<Stmt>> {
        let start = self.lexer.loc_start();

        self.expect(TT::KeywordImport)?;

        // Check for `import type`
        let type_only = if self.peek().typ == TT::Identifier
            && self.peek().value == "type"
        {
            // Could be `import type {` or `import type from`
            // Look ahead to distinguish
            let next = self.peek_nth(1).typ;

            if matches!(next, TT::BraceOpen | TT::Star | TT::Identifier) {
                // `import type {` or `import type *` or `import type Foo`
                self.consume();  // Consume 'type'
                true
            } else {
                // `import type from "mod"` - 'type' is identifier
                false
            }
        } else {
            false
        };

        let specifiers = self.parse_import_specifiers(type_only)?;

        // Expect 'from' keyword
        if self.peek().typ != TT::KeywordFrom {
            return Err(SyntaxError::expected("from"));
        }
        self.consume();

        let source = self.expect_string_literal()?;

        self.consume_semicolon();

        Ok(Node::new(
            self.loc_range(start),
            Stmt::Import(ImportStmt {
                specifiers,
                source,
                type_only,
            }),
        ))
    }

    fn parse_import_specifiers(&mut self, import_type_only: bool) -> SyntaxResult<Vec<ImportSpecifier>> {
        let mut specifiers = Vec::new();

        match self.peek().typ {
            // import * as NS
            TT::Star => {
                self.consume();
                self.expect(TT::KeywordAs)?;
                let local = self.expect_identifier()?;

                specifiers.push(ImportSpecifier::Namespace {
                    local,
                    type_only: import_type_only,
                });
            }

            // import Default or import Default, { ... }
            TT::Identifier if self.peek().value != "type" => {
                let local = self.expect_identifier()?;

                specifiers.push(ImportSpecifier::Default {
                    local,
                    type_only: import_type_only,
                });

                // Check for comma (mixed default + named)
                if self.consume_if(TT::Comma).is_match() {
                    // Parse named or namespace imports
                    if self.peek().typ == TT::Star {
                        self.consume();
                        self.expect(TT::KeywordAs)?;
                        let local = self.expect_identifier()?;

                        specifiers.push(ImportSpecifier::Namespace {
                            local,
                            type_only: import_type_only,
                        });
                    } else {
                        specifiers.extend(self.parse_named_imports(import_type_only)?);
                    }
                }
            }

            // import { ... }
            TT::BraceOpen => {
                specifiers.extend(self.parse_named_imports(import_type_only)?);
            }

            _ => {
                return Err(SyntaxError::unexpected_token(self.peek()));
            }
        }

        Ok(specifiers)
    }

    fn parse_named_imports(&mut self, import_type_only: bool) -> SyntaxResult<Vec<ImportSpecifier>> {
        self.expect(TT::BraceOpen)?;

        let mut specifiers = Vec::new();

        while self.peek().typ != TT::BraceClose {
            // Check for inline `type` specifier
            let inline_type_only = if self.peek().typ == TT::Identifier
                && self.peek().value == "type"
            {
                self.consume();
                true
            } else {
                false
            };

            let imported = self.expect_identifier()?;

            // Check for 'as' alias
            let local = if self.consume_if(TT::KeywordAs).is_match() {
                self.expect_identifier()?
            } else {
                imported.clone()
            };

            specifiers.push(ImportSpecifier::Named {
                imported,
                local,
                type_only: import_type_only || inline_type_only,
            });

            if !self.consume_if(TT::Comma).is_match() {
                break;
            }
        }

        self.expect(TT::BraceClose)?;

        Ok(specifiers)
    }
}
```

### Step 4: Implement Export Parser

**File**: `parse-js/src/parse/stmt.rs`

```rust
impl<'a> Parser<'a> {
    fn export_stmt(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<Stmt>> {
        let start = self.lexer.loc_start();

        self.expect(TT::KeywordExport)?;

        // Check for `export type`
        let type_only = if self.peek().typ == TT::Identifier
            && self.peek().value == "type"
        {
            // Look ahead: `export type {` or `export type *`
            let next = self.peek_nth(1).typ;

            if matches!(next, TT::BraceOpen | TT::Star) {
                self.consume();
                true
            } else {
                // `export type Foo = ...` - type alias declaration
                // Handle in different branch
                false
            }
        } else {
            false
        };

        match self.peek().typ {
            // export { ... }
            TT::BraceOpen => {
                let specifiers = self.parse_export_specifiers(type_only)?;

                // Check for 'from' clause
                let source = if self.peek().typ == TT::KeywordFrom {
                    self.consume();
                    Some(self.expect_string_literal()?)
                } else {
                    None
                };

                self.consume_semicolon();

                Ok(Node::new(
                    self.loc_range(start),
                    Stmt::Export(ExportStmt {
                        specifiers: Some(specifiers),
                        source,
                        type_only,
                        declaration: None,
                    }),
                ))
            }

            // export * from "mod"
            TT::Star => {
                self.consume();

                // export * as NS from "mod"
                let exported = if self.consume_if(TT::KeywordAs).is_match() {
                    Some(self.expect_identifier()?)
                } else {
                    None
                };

                self.expect(TT::KeywordFrom)?;
                let source = self.expect_string_literal()?;

                self.consume_semicolon();

                Ok(Node::new(
                    self.loc_range(start),
                    Stmt::Export(ExportStmt {
                        specifiers: Some(vec![ExportSpecifier::Namespace {
                            exported,
                            type_only,
                        }]),
                        source: Some(source),
                        type_only,
                        declaration: None,
                    }),
                ))
            }

            // export type TypeAlias = ... (type alias declaration)
            _ if type_only => {
                // This is a type alias, not a type-only export
                // Parse the type declaration
                let decl = self.declaration(ctx)?;

                Ok(Node::new(
                    self.loc_range(start),
                    Stmt::Export(ExportStmt {
                        specifiers: None,
                        source: None,
                        type_only: false,  // This is an export of a type declaration
                        declaration: Some(Box::new(decl)),
                    }),
                ))
            }

            // Regular export
            _ => {
                // Handle other export forms...
                // (existing code)
                todo!("Handle other export forms")
            }
        }
    }

    fn parse_export_specifiers(&mut self, export_type_only: bool) -> SyntaxResult<Vec<ExportSpecifier>> {
        self.expect(TT::BraceOpen)?;

        let mut specifiers = Vec::new();

        while self.peek().typ != TT::BraceClose {
            // Check for inline `type` specifier
            let inline_type_only = if self.peek().typ == TT::Identifier
                && self.peek().value == "type"
            {
                self.consume();
                true
            } else {
                false
            };

            let local = self.expect_identifier()?;

            // Check for 'as' alias
            let exported = if self.consume_if(TT::KeywordAs).is_match() {
                self.expect_identifier()?
            } else {
                local.clone()
            };

            specifiers.push(ExportSpecifier::Named {
                local,
                exported,
                type_only: export_type_only || inline_type_only,
            });

            if !self.consume_if(TT::Comma).is_match() {
                break;
            }
        }

        self.expect(TT::BraceClose)?;

        Ok(specifiers)
    }
}
```

### Step 5: Write Tests

**File**: `parse-js/tests/type_only_imports.rs`

```rust
use parse_js::*;

#[test]
fn test_import_type_named() {
    let src = r#"import type { User, Post } from "./types";"#;
    let result = parse(src);
    assert!(result.is_ok());
    // Assert type_only = true on ImportStmt
}

#[test]
fn test_import_type_namespace() {
    let src = r#"import type * as Types from "./types";"#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_import_type_default() {
    let src = r#"import type React from "react";"#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_import_inline_type() {
    let src = r#"import { type User, createUser } from "./api";"#;
    let result = parse(src);
    assert!(result.is_ok());
    // Assert User has type_only=true, createUser has type_only=false
}

#[test]
fn test_import_mixed_inline_types() {
    let src = r#"import { Component, type Props, type State } from "react";"#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_import_type_with_alias() {
    let src = r#"import type { User as U } from "./types";"#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_export_type_named() {
    let src = r#"export type { User, Post };"#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_export_type_from() {
    let src = r#"export type { User } from "./types";"#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_export_type_all() {
    let src = r#"export type * from "./types";"#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_export_type_namespace() {
    let src = r#"export type * as Types from "./types";"#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_export_inline_type() {
    let src = r#"export { type User, createUser };"#;
    let result = parse(src);
    assert!(result.is_ok());
}

#[test]
fn test_import_type_not_keyword() {
    let src = r#"import type from "./type";"#;
    let result = parse(src);
    assert!(result.is_ok());
    // 'type' is identifier, not keyword
}

#[test]
fn test_regular_import_still_works() {
    let src = r#"import { User } from "./types";"#;
    let result = parse(src);
    assert!(result.is_ok());
}
```

### Step 6: Run Tests

```bash
cargo test type_only_imports
cargo test
cargo test --release conformance_runner -- --filter "import"
```

### Step 7: Create Implementation Report

**File**: `workspace/outputs/03-implementation/04-type-only-imports/implementation-report.md`

[Standard implementation report format]

## Verification Commands

```bash
cargo check
cargo test type_only_imports
cargo test --release conformance_runner
```

## Common Issues

### Issue 1: `type` Ambiguity
**Problem**: `import type from "mod"` - is `type` a keyword or identifier?

**Solution**: Look ahead one token. If next token is `{`, `*`, or identifier (for default), then `type` is keyword. Otherwise, it's an identifier.

```rust
if self.peek().value == "type" {
    let next = self.peek_nth(1).typ;
    if matches!(next, TT::BraceOpen | TT::Star | TT::Identifier) {
        // Keyword
    } else {
        // Identifier
    }
}
```

### Issue 2: Inline Type Position
**Problem**: `import { type }` vs `import { type User }`

**Solution**: After consuming `type`, check if another identifier follows. If yes, it's inline type specifier. If no (next is `,` or `}`), `type` is the import name.

```rust
if self.peek().value == "type" {
    let next = self.peek_nth(1).typ;
    if next == TT::Identifier {
        // Inline type specifier
        self.consume();  // 'type'
        let name = self.expect_identifier()?;  // Actual import
    } else {
        // 'type' is the import name
        let name = self.expect_identifier()?;  // Gets 'type'
    }
}
```

### Issue 3: Type Alias vs Type-Only Export
**Problem**: `export type Foo = string` is different from `export type { Foo }`

**Solution**: Distinguish by looking at token after `type`:
- `export type {` → type-only export
- `export type Foo` → type alias declaration export

## Acceptance Criteria

- [ ] `import type` syntax parses correctly
- [ ] `export type` syntax parses correctly
- [ ] Inline `type` specifiers work
- [ ] Mixed type/value imports work
- [ ] All ambiguities handled correctly
- [ ] All tests pass
- [ ] Conformance tests improve
- [ ] Implementation report created

## Success Metrics

- All test cases pass
- Conformance improvement: +3-7%
- Zero regressions

## Resources

- TypeScript 3.8 Release Notes: Type-Only Imports/Exports
- TypeScript 4.5 Release Notes: Inline Type Specifiers
- TypeScript Handbook: Modules
