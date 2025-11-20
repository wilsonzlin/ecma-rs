---
task_id: "02-planning/03-plan-parser-extensions"
title: "Plan Parser Extensions and New Parsing Functions"
phase: "planning"
estimated_duration: "5-7 hours"
complexity: "high"
dependencies:
  - "01-analysis/04-audit-parser-coverage"
  - "02-planning/01-prioritize-features"
  - "02-planning/02-design-ast-nodes"
inputs:
  - "../../01-analysis/04-audit-parser-coverage/parser-coverage-map.json"
  - "../../02-planning/01-prioritize-features/prioritized-features.json"
  - "../../02-planning/02-design-ast-nodes/ast-extensions.md"
outputs:
  - "parser-plan.md"
  - "function-signatures.rs"
  - "lookahead-specifications.md"
  - "error-recovery-strategy.md"
skills_required:
  - "Parser theory"
  - "Rust programming"
  - "TypeScript syntax"
  - "Algorithm design"
---

# Task: Plan Parser Extensions and New Parsing Functions

## Objective

Design parser modifications to support new AST nodes and missing TypeScript syntax, including function signatures, lookahead strategies, error recovery, and implementation complexity estimates.

## Context

### Why This Matters

AST design (task 02) defined WHAT to represent. This task defines HOW to parse it:
1. **Which parser functions** to modify/create
2. **What lookahead logic** is needed
3. **How to handle ambiguity** (TypeScript has lots)
4. **Error recovery** strategies
5. **Implementation complexity** per feature

Good parser design:
- Handles ambiguous grammar correctly
- Recovers from errors gracefully
- Minimizes backtracking
- Provides clear error messages

### Input from Previous Tasks

From parser audit (04):
- Current parser functions
- Gaps in parsing
- Hot paths

From AST design (02):
- What nodes to populate
- What fields to set

From prioritization (01):
- What to implement first

### TypeScript Grammar Challenges

TypeScript has **ambiguous grammar**:
- `<T>` - Generic or less-than?
- `(x)` - Parenthesized type or tuple?
- `readonly` - Modifier or type?
- Arrow functions vs type annotations

**Need lookahead strategies for all.**

## Prerequisites

### Files to Read

1. **Current Parser** (`parse-js/src/parse/type_expr.rs`)
   - Understand existing patterns
   - Note lookahead functions
   - See error handling

2. **TypeScript Parser** (`parse-js/tests/TypeScript/src/compiler/parser.ts`)
   - Reference implementation
   - Disambiguation strategies
   - Edge cases

3. **Previous Task Outputs**
   - AST extensions (task 02)
   - Parser coverage map (task 04)

### Parser Patterns to Know

```rust
// Pattern 1: Simple keyword
TT::KeywordString => self.type_string()

// Pattern 2: Lookahead
if self.peek().typ == TT::BracketOpen {
    self.tuple_type()
}

// Pattern 3: Speculation (try parse, backtrack if fail)
let checkpoint = self.checkpoint();
if let Ok(result) = self.try_parse_type_arguments() {
    result
} else {
    self.restore(checkpoint);
    // fallback
}

// Pattern 4: Precedence climbing
self.parse_with_precedence(min_prec)
```

## Instructions

### Step 1: Categorize Parser Changes

Group by type of change needed:

**parser-plan.md** (start):

```markdown
# Parser Extensions Plan

## Change Categories

### Category A: Simple Keyword Additions
**Complexity**: LOW
**Pattern**: Add new match arm

Features:
- `using` keyword (statements)
- `await using` keyword
- `satisfies` operator (if missing)

**Example**:
```rust
TT::KeywordUsing => self.using_declaration()
```

### Category B: Field Population
**Complexity**: LOW
**Pattern**: Set new field on existing struct

Features:
- TypeParam.is_const
- TypeConstructor.is_abstract
- TypeTuple.readonly (if missing)

**Example**:
```rust
fn parse_type_parameter(&mut self) -> Result<TypeParam> {
    let is_const = self.consume_if(TT::KeywordConst).is_match();
    // ... rest of parsing
    TypeParam {
        name,
        is_const,  // Set new field
        // ...
    }
}
```

### Category C: New Lookahead Logic
**Complexity**: MEDIUM
**Pattern**: Add lookahead predicate

Features:
- `readonly [` - distinguish readonly tuple from readonly array
- `typeof import(` - typeof with import expression
- `abstract new` - abstract constructor

**Example**:
```rust
// In type_primary:
TT::KeywordReadonly => {
    let [_, next] = self.peek_n::<2>();
    if next.typ == TT::BracketOpen {
        // readonly tuple
    } else {
        // readonly type modifier
    }
}
```

### Category D: Extended Parsing Logic
**Complexity**: MEDIUM-HIGH
**Pattern**: Extend existing function with new branches

Features:
- Mapped type 'as' clause
- Template literal type parts
- Import typeof combination

**Example**:
```rust
fn mapped_type(&mut self) -> Result<TypeMapped> {
    // ... existing parsing

    // NEW: Parse 'as' clause
    let name_type = if self.consume_if(TT::KeywordAs).is_match() {
        Some(self.type_expr()?)
    } else {
        None
    };

    TypeMapped {
        // ...
        name_type,
    }
}
```

### Category E: Completely New Parsers
**Complexity**: HIGH
**Pattern**: Create new parsing function

Features:
- Using declarations
- New statement types
- Complex new type constructs

**Example**:
```rust
fn using_declaration(&mut self) -> Result<Stmt> {
    self.require(TT::KeywordUsing)?;
    let is_await = false;  // handle await prefix separately

    let declarations = self.variable_declarators()?;

    Ok(Stmt::Using(UsingDeclaration {
        is_await,
        declarations,
    }))
}
```
```

### Step 2: Design Lookahead Strategies

**lookahead-specifications.md**:

```markdown
# Lookahead Specifications

## Ambiguity Resolution Strategies

### Problem 1: readonly [ vs readonly T[]

**Ambiguity**:
```typescript
readonly [string, number]  // readonly tuple
readonly string[]          // readonly array type
```

**Current Parser**: Likely only handles second case

**Lookahead Strategy**:
```rust
TT::KeywordReadonly => {
    let [_, next_token] = self.peek_n::<2>();

    match next_token.typ {
        TT::BracketOpen => {
            // readonly [  → readonly tuple
            self.consume(); // consume 'readonly'
            self.tuple_type(true) // pass readonly=true
        }
        _ => {
            // readonly T  → readonly modifier on type
            self.consume(); // consume 'readonly'
            let inner = self.type_postfix()?;
            Ok(TypeExpr::Readonly(Box::new(inner)))
        }
    }
}
```

**Complexity**: LOW (single token lookahead)

**Alternative**: Multi-token lookahead
```rust
// Look for `readonly [` followed by type elements
// vs `readonly` followed by type expression
```

---

### Problem 2: typeof import(...) vs typeof x

**Ambiguity**:
```typescript
typeof import('./module')  // typeof on import expression
typeof x                   // typeof on identifier
```

**Current Parser**: Handles second case only

**Lookahead Strategy**:
```rust
fn typeof_type(&mut self) -> Result<TypeExpr> {
    self.require(TT::KeywordTypeof)?;

    if self.peek().typ == TT::KeywordImport {
        // typeof import(...)
        let import_expr = self.import_type()?;
        Ok(TypeExpr::TypeOf(TypeOfOperand::Import(Box::new(import_expr))))
    } else {
        // typeof entity.name
        let entity = self.type_entity_name()?;
        Ok(TypeExpr::TypeOf(TypeOfOperand::EntityName(entity)))
    }
}
```

**Complexity**: LOW (single token lookahead)

---

### Problem 3: <T> Generic vs < Comparison

**Ambiguity**:
```typescript
foo<T>()     // Generic call
foo < bar    // Comparison
```

**Current Parser**: Has `is_start_of_type_arguments()` predicate

**Strategy**: Speculation (try parse, backtrack if fails)

```rust
fn try_type_arguments(&mut self) -> Option<Vec<TypeExpr>> {
    let checkpoint = self.checkpoint();

    if self.consume_if(TT::Lt).is_match() {
        match self.parse_type_argument_list() {
            Ok(args) => {
                if self.consume_if(TT::Gt).is_match() {
                    return Some(args);
                }
            }
            Err(_) => {}
        }
    }

    // Failed, backtrack
    self.restore(checkpoint);
    None
}
```

**Complexity**: MEDIUM (speculation overhead)

**Optimization**: Cache result keyed by position

---

### Problem 4: abstract new vs abstract class

**Ambiguity**:
```typescript
abstract new (): T      // Abstract constructor signature
abstract class Foo {}   // Abstract class declaration
```

**Context**: Only in type positions

**Lookahead Strategy**:
```rust
// In type_member() or similar:
if self.peek().typ == TT::KeywordAbstract {
    let [_, next] = self.peek_n::<2>();

    if next.typ == TT::KeywordNew {
        // Abstract constructor signature
        self.consume(); // abstract
        return self.constructor_signature(is_abstract: true);
    } else {
        // Shouldn't happen in type context
        return Err("abstract class not allowed in type");
    }
}
```

**Complexity**: LOW (two-token lookahead)

---

### Problem 5: Mapped Type 'as' Clause

**Syntax**:
```typescript
{ [K in keyof T as NewKey<K>]: T[K] }
//               ^^^^^^^^^^^^
```

**No ambiguity**, just optional syntax

**Strategy**: Simple lookahead
```rust
fn mapped_type(&mut self) -> Result<TypeMapped> {
    // ... parse [K in keyof T] ...

    // Check for 'as' clause
    let name_type = if self.peek().typ == TT::KeywordAs {
        self.consume(); // consume 'as'
        Some(self.type_expr()?)
    } else {
        None
    };

    // ... continue
}
```

**Complexity**: LOW

---

## Lookahead Complexity Summary

| Feature | Lookahead Type | Tokens | Backtrack? | Complexity |
|---------|----------------|--------|------------|------------|
| readonly [ | Simple | 2 | No | LOW |
| typeof import | Simple | 1 | No | LOW |
| abstract new | Simple | 2 | No | LOW |
| <T> generics | Speculation | Many | Yes | MEDIUM |
| mapped 'as' | Simple | 1 | No | LOW |
| using | Simple | 1-2 | No | LOW |

## Lookahead Performance

**Concern**: `is_start_of_type_arguments()` is called frequently

**Current**: Scans tokens twice (lookahead + actual parse)

**Optimization Strategy**:

```rust
pub struct Parser {
    // ... existing fields
    speculation_cache: RefCell<HashMap<usize, Option<Vec<TypeExpr>>>>,
}

impl Parser {
    fn type_arguments_cached(&mut self) -> Option<Vec<TypeExpr>> {
        let pos = self.pos();

        // Check cache
        if let Some(cached) = self.speculation_cache.borrow().get(&pos) {
            return cached.clone();
        }

        // Try parse
        let result = self.try_type_arguments();

        // Cache
        self.speculation_cache.borrow_mut().insert(pos, result.clone());

        result
    }
}
```

**Trade-off**: Memory for speed
**Expected gain**: 3-5% parsing speed
```

### Step 3: Define Function Signatures

**function-signatures.rs**:

```rust
// This file contains proposed function signatures for parser extensions
// Use as reference when implementing

impl Parser {
    // ========== NEW FUNCTIONS ==========

    /// Parse using declaration
    /// Syntax: using x = expr; | await using x = expr;
    fn using_declaration(&mut self) -> SyntaxResult<Node<Stmt>> {
        // ...
    }

    /// Parse typeof operator with import expression
    /// Handles: typeof import('./module')
    fn typeof_with_import(&mut self) -> SyntaxResult<Node<TypeExpr>> {
        // ...
    }

    // ========== MODIFIED FUNCTIONS ==========

    /// Parse type parameter with const modifier
    /// Modified to handle: <const T extends U>
    fn parse_type_parameter(&mut self) -> SyntaxResult<Node<TypeParam>> {
        // Add:
        let is_const = self.consume_if(TT::KeywordConst).is_match();
        // ...
    }

    /// Parse tuple type with optional readonly modifier
    /// Modified to accept readonly parameter
    fn tuple_type(&mut self, readonly: bool) -> SyntaxResult<Node<TypeExpr>> {
        // Use readonly parameter instead of hardcoded false
        // ...
    }

    /// Parse mapped type with optional 'as' clause
    /// Modified to handle: { [K in T as NewK]: V }
    fn mapped_type(&mut self) -> SyntaxResult<Node<TypeExpr>> {
        // Add after parsing type parameter:
        let name_type = if self.consume_if(TT::KeywordAs).is_match() {
            Some(self.type_expr()?)
        } else {
            None
        };
        // ...
    }

    /// Parse constructor signature with optional abstract modifier
    /// Modified to handle: abstract new (): T
    fn constructor_signature(&mut self, is_abstract: bool) -> SyntaxResult<Node<TypeMember>> {
        // ...
    }

    /// Parse typeof type expression
    /// Modified to handle both entity names and import expressions
    fn typeof_type(&mut self) -> SyntaxResult<Node<TypeExpr>> {
        self.require(TT::KeywordTypeof)?;

        let operand = if self.peek().typ == TT::KeywordImport {
            let import_type = self.import_type()?;
            TypeOfOperand::Import(Box::new(import_type))
        } else {
            let entity = self.type_entity_name()?;
            TypeOfOperand::EntityName(entity)
        };

        Ok(Node::new(loc, TypeExpr::TypeOf(operand)))
    }

    /// Parse type primary expression
    /// Modified to handle readonly [ lookahead
    fn type_primary(&mut self, ctx: ParseCtx) -> SyntaxResult<Node<TypeExpr>> {
        match self.peek().typ {
            // ... existing cases

            TT::KeywordReadonly => {
                let [_, next] = self.peek_n::<2>();
                if next.typ == TT::BracketOpen {
                    // readonly tuple
                    self.consume(); // readonly
                    self.tuple_type(true)
                } else {
                    // readonly type modifier
                    self.consume(); // readonly
                    let inner = self.type_postfix(ctx)?;
                    Ok(Node::new(loc, TypeExpr::Readonly(Box::new(inner))))
                }
            }

            // ... rest
        }
    }

    // ========== HELPER FUNCTIONS ==========

    /// Check if next tokens form readonly tuple pattern
    fn is_readonly_tuple(&self) -> bool {
        let [current, next] = self.peek_n::<2>();
        current.typ == TT::KeywordReadonly && next.typ == TT::BracketOpen
    }

    /// Check if next tokens form abstract constructor pattern
    fn is_abstract_constructor(&self) -> bool {
        let [current, next] = self.peek_n::<2>();
        current.typ == TT::KeywordAbstract && next.typ == TT::KeywordNew
    }
}
```

### Step 4: Plan Error Recovery

**error-recovery-strategy.md**:

```markdown
# Error Recovery Strategy

## Current Error Handling

TypeScript parser is **permissive** for IDE use:
- Continues parsing after errors
- Produces partial AST
- Multiple error messages

ecma-rs parser can be **stricter**:
- Minification doesn't need partial AST
- Can fail fast on errors
- Simpler implementation

## Error Recovery Levels

### Level 1: No Recovery (Current)
Return error immediately, stop parsing.

**Pros**: Simple, clear error messages
**Cons**: Only see first error

### Level 2: Statement-Level Recovery
Skip to next statement after error.

**Pros**: Report multiple errors
**Cons**: More complex

### Level 3: Full Recovery (TypeScript-style)
Continue parsing, produce partial AST.

**Pros**: Best IDE experience
**Cons**: Complex, not needed for minifier

## Recommended: Level 1 (No Recovery)

For minification use case:
- First error is enough (fix & retry)
- Simpler parser
- Clearer error messages

## Error Messages

### Good Error Messages

**Bad**:
```
Error: Expected token
```

**Good**:
```
Error at line 42, column 15:
  Expected ':' after type parameter constraint

  type Foo<T extends U ??? V> = ...
                       ^

  Help: Type parameter syntax is: <T extends U = V>
```

### Error Context

Include in error messages:
- Line and column
- Snippet of source code
- What was expected
- What was found
- Suggestion (if obvious)

### Implementation

```rust
pub enum ParseError {
    UnexpectedToken {
        expected: Vec<TokenType>,
        found: Token,
        context: &'static str,
    },
    InvalidSyntax {
        message: String,
        location: Loc,
        help: Option<String>,
    },
    // ...
}

impl ParseError {
    pub fn pretty_print(&self, source: &str) -> String {
        match self {
            ParseError::UnexpectedToken { expected, found, context } => {
                format!(
                    "Error at {}:{}\n\
                     Expected {}, found {}\n\
                     Context: {}\n\
                     \n\
                     {}\n\
                     {}^",
                    found.loc.line(),
                    found.loc.col(),
                    expected.join(" or "),
                    found.typ,
                    context,
                    source_line(source, found.loc),
                    " ".repeat(found.loc.col()),
                )
            }
            // ...
        }
    }
}
```

## Type-Specific Errors

### Missing Type Annotation

```typescript
function foo(x) { ... }  // Error: missing type annotation
```

**For minifier**: This is valid! JavaScript allows it.
**Don't error**: Parser should handle untyped JS

### Invalid Type Syntax

```typescript
type T = string number;  // Error: missing operator
```

**Error message**:
```
Error: Invalid type syntax at line 1, column 17

  type T = string number;
                  ^

  Did you mean 'string | number' (union) or 'string & number' (intersection)?
```

### Mismatched Brackets

```typescript
type T = [string, number;  // Missing ]
```

**Error message**:
```
Error: Unclosed tuple type at line 1, column 27

  type T = [string, number;
                          ^

  Expected ']' to close tuple type
```
```

### Step 5: Estimate Implementation Complexity

**parser-plan.md** (continued):

```markdown
## Implementation Complexity Matrix

| Feature | Parser Change | Complexity | Time Estimate | Priority |
|---------|---------------|------------|---------------|----------|
| **Simple Field Additions** ||||
| TypeParam.is_const | Add modifier parsing | LOW | 1 hour | P2 |
| TypeConstructor.is_abstract | Add modifier check | LOW | 1 hour | P3 |
| TypeTuple.readonly | Add parameter | LOW | 1 hour | P1 |
| **Lookahead Extensions** ||||
| readonly [ tuple | 2-token lookahead | LOW | 2 hours | P1 |
| typeof import(...) | 1-token lookahead | LOW | 2 hours | P2 |
| abstract new | 2-token lookahead | LOW | 1 hour | P3 |
| **Extended Logic** ||||
| Mapped type 'as' | Add optional clause | MEDIUM | 3 hours | P2 |
| Type arguments cache | Add memoization | MEDIUM | 4 hours | P3 |
| **New Parsers** ||||
| Using declarations | New stmt parser | MEDIUM | 4 hours | P2 |
| await using | Extend using parser | LOW | 1 hour | P2 |
| **Refactoring** ||||
| Split type_primary | Extract functions | MEDIUM | 6 hours | P3 |
| Speculation cache | Thread through parser | MEDIUM | 5 hours | P3 |

**Total Implementation Time**: ~32 hours (4-5 days)

## Priority Grouping

### P1 (Must Have) - 4 hours
- TypeTuple.readonly
- readonly [ lookahead

### P2 (Important) - 14 hours
- TypeParam.is_const
- typeof import
- Mapped type 'as'
- Using declarations
- await using

### P3 (Nice to Have) - 14 hours
- TypeConstructor.is_abstract
- abstract new
- Optimizations (cache, refactor)

## Implementation Order

### Phase 1 (Week 1): High-Impact Low-Complexity
1. TypeTuple.readonly (1h)
2. readonly [ lookahead (2h)
3. typeof import (2h)
4. TypeParam.is_const (1h)

**Total**: 6 hours
**Impact**: Fixes ~50 conformance tests

### Phase 2 (Week 2): Medium Complexity
5. Mapped type 'as' clause (3h)
6. Using declarations (4h)
7. await using (1h)

**Total**: 8 hours
**Impact**: Fixes ~20 conformance tests

### Phase 3 (Week 2-3): Low Priority / Polish
8. TypeConstructor.is_abstract (1h)
9. abstract new lookahead (1h)
10. Type arguments cache (4h)
11. Refactor type_primary (6h)

**Total**: 12 hours
**Impact**: Performance, code quality

## Testing Plan Integration

For each parser change:
1. Write failing test
2. Implement parser change
3. Verify test passes
4. Run conformance tests
5. Check for regressions

**Test template**:
```rust
#[test]
fn test_feature_name() {
    let src = r#"type T = <TypeScript syntax>;"#;
    let ast = parse(src).unwrap();

    // Assert AST structure
    assert!(matches!(ast, ...));
}
```

## Performance Considerations

### Hot Path Changes

**Concern**: type_primary is 32.5% of parse time

**Changes affecting hot path**:
- readonly [ lookahead (adds one branch)
- type_arguments caching (should improve)

**Expected impact**:
- Lookahead additions: +1-2% time (minor)
- Speculation cache: -3-5% time (improvement)
- Net: ~3% faster

### Memory Impact

**New allocations**:
- Speculation cache: HashMap<usize, Option<Vec<TypeExpr>>>
- Estimated: 1-2 MB for large files

**Trade-off**: Acceptable for 3-5% speed gain

## Integration with AST Design

### Verification Checklist

For each AST node extension:
- [ ] Parser populates new field
- [ ] Default value correct
- [ ] Test covers new field
- [ ] Serialization works

### Cross-Reference

| AST Extension | Parser Function | File | Line |
|---------------|-----------------|------|------|
| TypeParam.is_const | parse_type_parameter | type_expr.rs | ~220 |
| TypeMapped.name_type | mapped_type | type_expr.rs | ~1050 |
| TypeTuple.readonly | tuple_type | type_expr.rs | ~1156 |
| TypeConstructor.is_abstract | constructor_signature | type_expr.rs | ~950 |

## Risks and Mitigations

### Risk: Lookahead breaks existing parsing

**Mitigation**:
- Test existing syntax extensively
- Regression test suite
- Careful with token consumption

### Risk: Speculation overhead

**Mitigation**:
- Profile before/after
- Add caching if needed
- Measure on real files

### Risk: Error messages get worse

**Mitigation**:
- Review all error paths
- Add context to errors
- Test with invalid syntax

## Success Criteria

- [ ] All planned parser changes documented
- [ ] Function signatures defined
- [ ] Lookahead strategies clear
- [ ] Complexity estimates realistic
- [ ] Implementation order prioritized
- [ ] Error recovery planned
- [ ] Performance impact assessed
- [ ] Ready for implementation phase
```

## Acceptance Criteria

### Required Outputs

✅ **parser-plan.md**: Complete parser modification plan

✅ **function-signatures.rs**: All function signatures

✅ **lookahead-specifications.md**: Ambiguity resolution strategies

✅ **error-recovery-strategy.md**: Error handling approach

### Quality Checks

- [ ] Every feature has parser plan
- [ ] All lookahead cases covered
- [ ] Complexity estimates provided
- [ ] Implementation order clear
- [ ] Error recovery designed
- [ ] Performance impact considered

### Success Metrics

- Parser plan complete
- All ambiguities addressed
- Ready for implementation
- Time estimates reasonable

## Common Issues & Solutions

### Issue: Unsure how to handle ambiguity

**Solution**:
- Check TypeScript's parser
- Try both interpretations in TS playground
- Use speculation if needed

### Issue: Multiple lookahead strategies possible

**Solution**:
- Document all options
- Pick simplest first
- Note optimization opportunities

### Issue: Function signature unclear

**Solution**:
- Write example usage
- Sketch AST it should produce
- Reference similar existing functions

## Time Estimate Breakdown

- Review current parser: 1.5 hours
- Plan lookahead strategies: 2 hours
- Design function signatures: 1.5 hours
- Error recovery strategy: 1 hour
- Complexity estimation: 1 hour
- Write documentation: 1 hour

**Total: 5-7 hours**

## Downstream Impact

Critical for:
- **03-implementation/***: Direct implementation guide
- **04-define-test-strategy**: What to test
- **Performance baseline**: Expected impact

## Notes for Agent

- Be specific - implementers will follow this exactly
- When unsure, document options
- Consider performance impact
- Error messages matter for debugging
- Your plan determines implementation success

---

**Ready?** Start with Step 1: Categorize Parser Changes
