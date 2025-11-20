---
task_id: "03-implementation/10-jsdoc-types"
phase: "03-implementation"
title: "Implement JSDoc Type Parsing"
dependencies:
  - "02-planning/02-design-ast-nodes"
  - "02-planning/03-plan-parser-extensions"
inputs:
  - "workspace/outputs/02-planning/02-design-ast-nodes/ast-extensions.md"
  - "workspace/outputs/02-planning/03-plan-parser-extensions/parser-plan.md"
outputs:
  - "parse-js/src/parse/jsdoc.rs" (new or modified)
  - "parse-js/src/ast/jsdoc.rs" (new or modified)
  - "parse-js/tests/jsdoc_types.rs"
  - "workspace/outputs/03-implementation/10-jsdoc-types/implementation-report.md"
estimated_duration: "5-7 hours"
complexity: "high"
priority: "low"
---

# Task: Implement JSDoc Type Parsing

## Objective

Implement parsing of type annotations within JSDoc comments for JavaScript files. This enables ecma-rs to parse and understand type information in vanilla JavaScript files that use JSDoc for type documentation.

## Context

JSDoc is the de facto standard for adding type annotations to JavaScript files. TypeScript supports JSDoc annotations and can perform type checking on JavaScript files using `// @ts-check` or with `checkJs` enabled.

### Use Case

```javascript
/**
 * @param {string} name - The user's name
 * @param {number} age - The user's age
 * @returns {User}
 */
function createUser(name, age) {
    return { name, age };
}

/**
 * @type {import('./types').Config}
 */
const config = loadConfig();

/**
 * @typedef {Object} Point
 * @property {number} x - X coordinate
 * @property {number} y - Y coordinate
 */

/**
 * @template T
 * @param {T[]} items
 * @returns {T | undefined}
 */
function first(items) {
    return items[0];
}
```

### Current State
- Regular comments likely parsed and preserved
- JSDoc-specific type syntax likely not parsed
- Type information in JSDoc not extracted

### Target Features

```javascript
// 1. Basic type annotations
/** @type {string} */
/** @param {number} x */
/** @returns {boolean} */

// 2. Generic types
/** @type {Array<string>} */
/** @type {Map<string, number>} */

// 3. Union and intersection
/** @type {string | number} */
/** @type {A & B} */

// 4. Nullable
/** @type {?string} */  // Nullable (can be null)
/** @type {!string} */  // Non-nullable (cannot be null)

// 5. Optional parameters
/** @param {string=} optional */
/** @param {string} [optional] */

// 6. Rest parameters
/** @param {...string} args */

// 7. Import types
/** @type {import('./mod').Type} */

// 8. Function types
/** @type {function(string, number): boolean} */

// 9. Object types
/** @type {{x: number, y: number}} */

// 10. Tuple types
/** @type {[string, number]} */

// 11. Template types
/** @template T */
/** @template {string} T */

// 12. Type definitions
/** @typedef {Object} Name */
/** @typedef {import('./mod').Type} Alias */

// 13. Callback types
/** @callback MyCallback
 *  @param {string} x
 *  @returns {void}
 */
```

## Instructions

### Step 1: Understand Scope

**Important**: This task is about parsing JSDoc **type syntax**, not extracting JSDoc comments.

Two sub-tasks:
1. **Comment extraction** (may already be done)
2. **Type syntax parsing** (this task's focus)

Check if comments are already extracted:
```bash
# Test if comments are preserved
cargo run --example parse -- '/** Comment */ const x = 1' --keep-comments
```

### Step 2: Define AST for JSDoc

**File**: `parse-js/src/ast/jsdoc.rs` (create if doesn't exist)

```rust
use serde::Serialize;

#[derive(Debug, Clone, Serialize)]
pub struct JSDocComment {
    pub loc: Loc,
    pub tags: Vec<JSDocTag>,
    pub description: Option<String>,
}

#[derive(Debug, Clone, Serialize)]
pub struct JSDocTag {
    pub name: String,  // "param", "returns", "type", etc.
    pub type_: Option<JSDocType>,
    pub param_name: Option<String>,  // For @param
    pub description: Option<String>,
}

#[derive(Debug, Clone, Serialize)]
pub enum JSDocType {
    /// Simple name: string, number, MyType
    Name(String),

    /// Generic: Array<T>, Map<K, V>
    Generic {
        base: Box<JSDocType>,
        args: Vec<JSDocType>,
    },

    /// Union: A | B | C
    Union(Vec<JSDocType>),

    /// Intersection: A & B (less common in JSDoc)
    Intersection(Vec<JSDocType>),

    /// Nullable: ?string
    Nullable(Box<JSDocType>),

    /// Non-nullable: !string
    NonNullable(Box<JSDocType>),

    /// Optional: string=
    Optional(Box<JSDocType>),

    /// Rest: ...string
    Rest(Box<JSDocType>),

    /// Function: function(string, number): boolean
    Function {
        params: Vec<JSDocType>,
        return_type: Box<JSDocType>,
    },

    /// Object: {x: number, y: number}
    Object(Vec<JSDocProperty>),

    /// Tuple: [string, number]
    Tuple(Vec<JSDocType>),

    /// Import: import('./mod').Type
    Import {
        path: String,
        member: Option<String>,
    },

    /// Any: *
    Any,
}

#[derive(Debug, Clone, Serialize)]
pub struct JSDocProperty {
    pub name: String,
    pub type_: JSDocType,
    pub optional: bool,
}
```

### Step 3: Implement JSDoc Type Parser

**File**: `parse-js/src/parse/jsdoc.rs` (create if doesn't exist)

```rust
use crate::ast::jsdoc::*;
use crate::lex::*;

pub struct JSDocTypeParser<'a> {
    source: &'a str,
    pos: usize,
}

impl<'a> JSDocTypeParser<'a> {
    pub fn new(source: &'a str) -> Self {
        Self { source, pos: 0 }
    }

    pub fn parse(&mut self) -> Result<JSDocType, String> {
        self.parse_type()
    }

    fn parse_type(&mut self) -> Result<JSDocType, String> {
        self.skip_whitespace();

        // Union types: A | B | C
        let mut types = vec![self.parse_intersection()?];

        while self.peek() == '|' {
            self.consume();
            self.skip_whitespace();
            types.push(self.parse_intersection()?);
        }

        if types.len() == 1 {
            Ok(types.into_iter().next().unwrap())
        } else {
            Ok(JSDocType::Union(types))
        }
    }

    fn parse_intersection(&mut self) -> Result<JSDocType, String> {
        let mut types = vec![self.parse_prefix()?];

        while self.peek() == '&' {
            self.consume();
            self.skip_whitespace();
            types.push(self.parse_prefix()?);
        }

        if types.len() == 1 {
            Ok(types.into_iter().next().unwrap())
        } else {
            Ok(JSDocType::Intersection(types))
        }
    }

    fn parse_prefix(&mut self) -> Result<JSDocType, String> {
        self.skip_whitespace();

        match self.peek() {
            '?' => {
                self.consume();
                Ok(JSDocType::Nullable(Box::new(self.parse_postfix()?)))
            }
            '!' => {
                self.consume();
                Ok(JSDocType::NonNullable(Box::new(self.parse_postfix()?)))
            }
            '.' if self.peek_str(3) == "..." => {
                self.consume_n(3);
                Ok(JSDocType::Rest(Box::new(self.parse_postfix()?)))
            }
            _ => self.parse_postfix(),
        }
    }

    fn parse_postfix(&mut self) -> Result<JSDocType, String> {
        let mut base = self.parse_primary()?;

        loop {
            self.skip_whitespace();

            match self.peek() {
                '<' => {
                    // Generic type arguments
                    self.consume();
                    let args = self.parse_type_args()?;
                    self.expect('>')?;

                    base = JSDocType::Generic {
                        base: Box::new(base),
                        args,
                    };
                }
                '=' => {
                    // Optional (postfix)
                    self.consume();
                    base = JSDocType::Optional(Box::new(base));
                }
                _ => break,
            }
        }

        Ok(base)
    }

    fn parse_primary(&mut self) -> Result<JSDocType, String> {
        self.skip_whitespace();

        match self.peek() {
            '*' => {
                self.consume();
                Ok(JSDocType::Any)
            }

            '{' => {
                // Object type: {x: number, y: string}
                self.consume();
                let props = self.parse_object_properties()?;
                self.expect('}')?;
                Ok(JSDocType::Object(props))
            }

            '[' => {
                // Tuple type: [string, number]
                self.consume();
                let types = self.parse_tuple_elements()?;
                self.expect(']')?;
                Ok(JSDocType::Tuple(types))
            }

            '(' => {
                // Parenthesized or tuple
                self.consume();
                let inner = self.parse_type()?;
                self.expect(')')?;
                Ok(inner)
            }

            _ if self.peek_str(8) == "function" => {
                self.parse_function_type()
            }

            _ if self.peek_str(6) == "import" => {
                self.parse_import_type()
            }

            _ if self.is_identifier_start(self.peek()) => {
                Ok(JSDocType::Name(self.parse_identifier()))
            }

            c => Err(format!("Unexpected character in type: '{}'", c)),
        }
    }

    fn parse_function_type(&mut self) -> Result<JSDocType, String> {
        self.expect_str("function")?;
        self.skip_whitespace();
        self.expect('(')?;

        let params = self.parse_function_params()?;

        self.expect(')')?;
        self.skip_whitespace();

        let return_type = if self.peek() == ':' {
            self.consume();
            Box::new(self.parse_type()?)
        } else {
            Box::new(JSDocType::Any)
        };

        Ok(JSDocType::Function {
            params,
            return_type,
        })
    }

    fn parse_import_type(&mut self) -> Result<JSDocType, String> {
        self.expect_str("import")?;
        self.skip_whitespace();
        self.expect('(')?;
        self.skip_whitespace();

        // Parse string literal
        let path = self.parse_string_literal()?;

        self.expect(')')?;
        self.skip_whitespace();

        // Parse optional member access
        let member = if self.peek() == '.' {
            self.consume();
            Some(self.parse_identifier())
        } else {
            None
        };

        Ok(JSDocType::Import { path, member })
    }

    // Helper methods
    fn peek(&self) -> char {
        self.source[self.pos..].chars().next().unwrap_or('\0')
    }

    fn consume(&mut self) {
        if self.pos < self.source.len() {
            self.pos += self.peek().len_utf8();
        }
    }

    fn skip_whitespace(&mut self) {
        while self.peek().is_whitespace() {
            self.consume();
        }
    }

    fn is_identifier_start(&self, c: char) -> bool {
        c.is_alphabetic() || c == '_' || c == '$'
    }

    fn parse_identifier(&mut self) -> String {
        let start = self.pos;
        while self.is_identifier_char(self.peek()) {
            self.consume();
        }
        self.source[start..self.pos].to_string()
    }

    fn is_identifier_char(&self, c: char) -> bool {
        c.is_alphanumeric() || c == '_' || c == '$'
    }

    // ... implement other helper methods ...
}
```

### Step 4: Integrate JSDoc Parser

**File**: `parse-js/src/parse/stmt.rs` or main parser

```rust
// When comment is attached to statement:
fn parse_statement_with_jsdoc(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<Stmt>> {
    // Check if there's a JSDoc comment before this statement
    let jsdoc = self.parse_preceding_jsdoc()?;

    let stmt = self.statement(ctx)?;

    // Attach JSDoc to statement
    if let Some(jsdoc) = jsdoc {
        // Store in AST or separate table
    }

    Ok(stmt)
}
```

### Step 5: Write Tests

**File**: `parse-js/tests/jsdoc_types.rs`

```rust
use parse_js::*;

#[test]
fn test_jsdoc_type_simple() {
    let type_str = "string";
    let result = parse_jsdoc_type(type_str);
    assert!(result.is_ok());
}

#[test]
fn test_jsdoc_type_generic() {
    let type_str = "Array<string>";
    let result = parse_jsdoc_type(type_str);
    assert!(result.is_ok());
}

#[test]
fn test_jsdoc_type_union() {
    let type_str = "string | number";
    let result = parse_jsdoc_type(type_str);
    assert!(result.is_ok());
}

#[test]
fn test_jsdoc_type_nullable() {
    let type_str = "?string";
    let result = parse_jsdoc_type(type_str);
    assert!(result.is_ok());
}

#[test]
fn test_jsdoc_type_function() {
    let type_str = "function(string, number): boolean";
    let result = parse_jsdoc_type(type_str);
    assert!(result.is_ok());
}

#[test]
fn test_jsdoc_type_object() {
    let type_str = "{x: number, y: number}";
    let result = parse_jsdoc_type(type_str);
    assert!(result.is_ok());
}

#[test]
fn test_jsdoc_type_import() {
    let type_str = "import('./types').User";
    let result = parse_jsdoc_type(type_str);
    assert!(result.is_ok());
}

#[test]
fn test_jsdoc_param_tag() {
    let src = r#"
        /**
         * @param {string} name
         */
        function f(name) {}
    "#;
    let result = parse(src);
    assert!(result.is_ok());
}

// ... more tests ...
```

### Step 6: Run Tests

```bash
cargo test jsdoc_types
cargo test
```

### Step 7: Create Implementation Report

**File**: `workspace/outputs/03-implementation/10-jsdoc-types/implementation-report.md`

[Standard format]

## Verification Commands

```bash
cargo check
cargo test jsdoc_types
```

## Common Issues

### Issue 1: JSDoc vs TypeScript Syntax
**Problem**: JSDoc type syntax differs from TypeScript

**Solution**: Implement separate JSDoc type parser - don't reuse TypeScript parser

Examples of differences:
- Nullable: `?string` (JSDoc) vs `string | null` (TS)
- Function: `function(string): void` (JSDoc) vs `(x: string) => void` (TS)
- Generic: `Array<T>` (both) vs `T[]` (TS only)

### Issue 2: Comment Extraction
**Problem**: Need to extract JSDoc comments first

**Solution**: Lexer should preserve comments (may need configuration flag)

### Issue 3: Type vs Tag Parsing
**Problem**: Some tags have types, some don't

**Solution**: Parse tag-specific syntax:
- `@param {Type} name description` - has type
- `@returns {Type} description` - has type
- `@example` - no type, just text

## Acceptance Criteria

- [ ] JSDoc type syntax parses correctly
- [ ] All major JSDoc type forms supported
- [ ] JSDoc comments extracted and associated with code
- [ ] No interference with regular TypeScript parsing
- [ ] All tests pass
- [ ] Implementation report created

## Success Metrics

- Parse 90%+ of common JSDoc type patterns
- Enable type checking of JavaScript files (future work)

## Resources

- TypeScript JSDoc Reference: https://www.typescriptlang.org/docs/handbook/jsdoc-supported-types.html
- JSDoc Official: https://jsdoc.app/
- TypeScript source: `src/compiler/jsDocParser.ts`

## Notes

**Priority**: Low - JSDoc is primarily for JavaScript files. Since ecma-rs is focused on TypeScript parsing for minification, JSDoc support is a nice-to-have for JavaScript file support but not critical for the primary use case.

**Recommendation**: Implement if time allows, or defer to a later phase. Focus on core TypeScript features first.
