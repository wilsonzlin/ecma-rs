---
task_id: "01-analysis/04-audit-parser-coverage"
title: "Audit Parser Coverage of TypeScript Features"
phase: "analysis"
estimated_duration: "4-6 hours"
complexity: "medium"
dependencies: []
inputs: []
outputs:
  - "parser-coverage-map.json"
  - "parser-coverage-report.md"
  - "parser-function-inventory.json"
  - "unreachable-code-analysis.md"
skills_required:
  - "Rust code reading"
  - "Parser theory"
  - "TypeScript syntax"
---

# Task: Audit Parser Coverage of TypeScript Features

## Objective

Systematically inventory all TypeScript type parsing functions currently implemented and identify which AST nodes are populated, which are orphaned (defined but never created), and which syntax patterns are missing parsers.

## Context

### Why This Matters

The AST audit (task 03) tells us what CAN be represented. This parser audit tells us:
1. **What IS parsed** - Which parsing functions exist
2. **What's NOT parsed** - Syntax with no corresponding parser
3. **Dead code** - AST nodes defined but never instantiated
4. **Partial parsers** - Functions that exist but may have bugs/gaps

Together, AST + Parser audits give complete picture of what's missing.

### Current State

The parser is implemented in:
- `parse-js/src/parse/type_expr.rs` (~1,743 lines) - Main type expression parser
- `parse-js/src/parse/ts_decl.rs` - TypeScript declarations
- `parse-js/src/parse/stmt.rs` - Type annotations on statements
- `parse-js/src/parse/expr.rs` - Type assertions, satisfies

### What We're Looking For

1. **Parser Functions**
   - `fn type_*()` - Primary type parsing functions
   - `fn parse_*_type()` - Helper functions
   - Entry points: `type_annotation()`, `type_expr()`

2. **AST Node Creation**
   - Where each TypeExpr variant is constructed
   - Which AST nodes are never instantiated

3. **Unreachable Code**
   - `match` arms that can't be reached
   - AST nodes defined but never created
   - Dead parser functions never called

## Prerequisites

### Files to Read

1. **Type Expression Parser** (`parse-js/src/parse/type_expr.rs` ~1,743 lines)
   - Main parser logic
   - Read every function definition
   - Note which TypeExpr variants are constructed

2. **TypeScript Declaration Parser** (`parse-js/src/parse/ts_decl.rs`)
   - Interface, type alias, enum parsing
   - Check completeness

3. **Statement Parser** (`parse-js/src/parse/stmt.rs`)
   - Type annotations on variables, functions
   - Parameter types, return types

4. **Expression Parser** (`parse-js/src/parse/expr.rs`)
   - Type assertions (`as`, `satisfies`)
   - Const assertions (`as const`)

### Tools

```bash
# Function name extraction
grep -n "^\s*fn\s\+\w\+.*type" parse-js/src/parse/type_expr.rs

# AST node construction
grep -n "TypeExpr::" parse-js/src/parse/type_expr.rs

# Match arm analysis
awk '/match.*{/,/^\s*}/' parse-js/src/parse/type_expr.rs
```

## Instructions

### Step 1: Inventory All Parser Functions

Extract complete function list:

```bash
cd /home/user/ecma-rs/parse-js

# Get all type-related functions in parser
grep -n "^\s*fn\s" src/parse/type_expr.rs | grep -i type > /tmp/type_functions.txt

# Count them
wc -l /tmp/type_functions.txt

# Categorize by name pattern
grep "fn type_" /tmp/type_functions.txt | wc -l  # Primary parsers
grep "fn parse_.*type" /tmp/type_functions.txt | wc -l  # Helpers
grep "fn is_.*type" /tmp/type_functions.txt | wc -l  # Lookahead predicates
```

Create **parser-function-inventory.json**:

```json
{
  "analysis_date": "2025-11-20",
  "total_functions": 67,
  "categories": {
    "entry_points": {
      "count": 3,
      "functions": [
        {"name": "type_expr", "line": 45, "purpose": "Main entry point for type expressions"},
        {"name": "type_annotation", "line": 120, "purpose": "Parse ': Type' annotation"},
        {"name": "type_arguments", "line": 580, "purpose": "Parse '<T, U>' arguments"}
      ]
    },

    "primary_parsers": {
      "count": 28,
      "functions": [
        {"name": "type_primary", "line": 320, "parses": "Primitive types, keywords, parenthesized"},
        {"name": "type_postfix", "line": 450, "parses": "Array types, property access"},
        {"name": "type_union", "line": 500, "parses": "Union types (A | B)"},
        {"name": "type_intersection", "line": 550, "parses": "Intersection types (A & B)"},
        {"name": "tuple_type", "line": 1156, "parses": "Tuple types [T, U]"},
        {"name": "object_type", "line": 800, "parses": "Object type literals"},
        {"name": "function_type", "line": 900, "parses": "Function types"},
        {"name": "constructor_type", "line": 950, "parses": "Constructor types"},
        {"name": "conditional_type", "line": 1000, "parses": "T extends U ? X : Y"},
        {"name": "mapped_type", "line": 1050, "parses": "Mapped types"},
        {"name": "template_literal_type", "line": 1100, "parses": "Template literal types"},
        {"name": "indexed_access_type", "line": 650, "parses": "T[K] types"}
      ]
    },

    "helper_parsers": {
      "count": 18,
      "functions": [
        {"name": "parse_type_parameters", "line": 200, "purpose": "Parse <T, U> parameter lists"},
        {"name": "parse_type_parameter", "line": 220, "purpose": "Single type parameter T extends U = V"},
        {"name": "parse_type_reference", "line": 680, "purpose": "Type references Foo<Bar>"},
        {"name": "parse_type_member", "line": 850, "purpose": "Object type members"},
        {"name": "tuple_element", "line": 1184, "purpose": "Single tuple element"},
        {"name": "parse_mapped_type_modifier", "line": 1070, "purpose": "+? -? readonly modifiers"}
      ]
    },

    "lookahead_predicates": {
      "count": 12,
      "functions": [
        {"name": "is_start_of_type", "line": 150, "purpose": "Check if token starts type"},
        {"name": "is_start_of_type_arguments", "line": 600, "purpose": "Disambiguate <T> vs <"},
        {"name": "is_start_of_function_type", "line": 920, "purpose": "Detect arrow function types"}
      ]
    },

    "type_operators": {
      "count": 6,
      "functions": [
        {"name": "typeof_type", "line": 700, "parses": "typeof operator"},
        {"name": "keyof_type", "line": 720, "parses": "keyof operator"},
        {"name": "readonly_type", "line": 740, "parses": "readonly operator"},
        {"name": "unique_type", "line": 760, "parses": "unique symbol"}
      ]
    }
  }
}
```

**Note**: Fill in actual line numbers and function names by reading the code!

### Step 2: Map Parser Functions to AST Nodes

For each parser function, identify which AST nodes it creates:

```bash
# Find where each TypeExpr variant is constructed
for variant in String Number Boolean Union Intersection Tuple Array; do
    echo "=== Type${variant} ==="
    grep -n "TypeExpr::${variant}" src/parse/type_expr.rs
done

# Example output:
# === TypeString ===
# 325:    Ok(Node::new(loc, TypeExpr::String(Node::new(loc, TypeString {}))))
```

Create mapping in **parser-coverage-map.json**:

```json
{
  "analysis_date": "2025-11-20",
  "total_ast_nodes": 45,
  "parsed_nodes": 38,
  "orphaned_nodes": 7,
  "coverage_percentage": 84.4,

  "node_coverage": {
    "TypeString": {
      "status": "parsed",
      "parser_function": "type_primary",
      "parser_line": 325,
      "token_trigger": "TT::KeywordString",
      "example": "type T = string"
    },

    "TypeNumber": {
      "status": "parsed",
      "parser_function": "type_primary",
      "parser_line": 330,
      "token_trigger": "TT::KeywordNumber",
      "example": "type T = number"
    },

    "TypeUnion": {
      "status": "parsed",
      "parser_function": "type_union",
      "parser_line": 500,
      "token_trigger": "TT::Pipe after type",
      "example": "type T = A | B"
    },

    "TypeTuple": {
      "status": "parsed",
      "parser_function": "tuple_type",
      "parser_line": 1156,
      "token_trigger": "TT::BracketOpen",
      "example": "type T = [string, number]",
      "notes": "readonly [T, ...U] combination may not work - verify"
    },

    "TypeConditional": {
      "status": "parsed",
      "parser_function": "conditional_type",
      "parser_line": 1000,
      "token_trigger": "TT::KeywordExtends in type context",
      "example": "type T = A extends B ? C : D"
    },

    "TypeMapped": {
      "status": "parsed",
      "parser_function": "mapped_type",
      "parser_line": 1050,
      "token_trigger": "{ [ after readonly/+?/-?",
      "example": "type T = { [K in keyof O]: O[K] }",
      "notes": "Check if 'as' clause supported"
    },

    "TypeImportTypeOf": {
      "status": "orphaned",
      "ast_defined": "type_expr.rs:250",
      "parser_function": null,
      "reason": "No parser for 'typeof import(...)' combination",
      "example": "type T = typeof import('./mod')"
    },

    "TypeAbstractConstructor": {
      "status": "orphaned",
      "ast_defined": "type_expr.rs:270",
      "parser_function": null,
      "reason": "Constructor parser doesn't check for 'abstract' keyword",
      "example": "abstract new (): T"
    }
  },

  "orphaned_nodes": [
    {
      "node": "TypeImportTypeOf",
      "reason": "typeof import(...) not parsed",
      "impact": "high",
      "estimated_failures": 20
    },
    {
      "node": "TypeAbstractConstructor",
      "reason": "abstract modifier not parsed",
      "impact": "low",
      "estimated_failures": 3
    },
    {
      "node": "TypeConstParameter",
      "reason": "const keyword on type params not parsed",
      "impact": "medium",
      "estimated_failures": 10
    }
  ],

  "parser_gaps": {
    "readonly_tuple_combination": {
      "syntax": "readonly [T, ...U[]]",
      "ast_support": "yes",
      "parser_support": "unknown",
      "function": "type_primary + tuple_type",
      "line": 322,
      "issue": "readonly keyword may not lookahead for [",
      "verification_needed": true
    },

    "mapped_as_clause": {
      "syntax": "{ [K in keyof T as NewK]: V }",
      "ast_support": "unknown",
      "parser_support": "no",
      "function": "mapped_type",
      "line": 1050,
      "issue": "No parsing of 'as' clause after K",
      "verification_needed": true
    },

    "import_type_typeof": {
      "syntax": "typeof import('./mod')",
      "ast_support": "unknown",
      "parser_support": "no",
      "function": "typeof_type",
      "line": 700,
      "issue": "typeof doesn't handle import() expressions",
      "verification_needed": false
    },

    "using_declarations": {
      "syntax": "using x = getResource()",
      "ast_support": "no",
      "parser_support": "no",
      "function": null,
      "issue": "TS 5.2 feature - completely missing",
      "verification_needed": false
    }
  }
}
```

### Step 3: Find Unreachable Code

Look for dead code patterns:

```bash
# Find TODO/FIXME comments
grep -rn "TODO\|FIXME" src/parse/type_expr.rs

# Find match arms that might be unreachable
# (This requires manual inspection)

# Find functions never called
# 1. Get all function definitions
grep "fn \w\+(" src/parse/type_expr.rs | sed 's/.*fn \(\w\+\).*/\1/' > /tmp/defined.txt

# 2. Get all function calls
grep -o "\w\+(" src/parse/type_expr.rs | sed 's/($//' > /tmp/called.txt

# 3. Find defined but never called
comm -23 <(sort -u /tmp/defined.txt) <(sort -u /tmp/called.txt)
```

Create **unreachable-code-analysis.md**:

```markdown
# Unreachable Code Analysis

## Orphaned AST Nodes (Defined but Never Created)

### High Impact

#### 1. TypeImportTypeOf
**Defined**: type_expr.rs:250
**Never created by parser**
**Syntax**: `typeof import('./module')`
**Impact**: 20+ conformance test failures
**Reason**: `typeof_type()` doesn't handle import expressions

**Fix Needed**:
```rust
fn typeof_type(&mut self) -> SyntaxResult<Node<TypeExpr>> {
    self.consume(); // typeof keyword

    // Check for import() expression
    if self.peek().typ == TT::KeywordImport {
        let import_expr = self.import_type()?;
        return Ok(TypeExpr::ImportTypeOf(import_expr));
    }

    // Regular typeof
    // ... existing code
}
```

#### 2. TypeConstParameter (if exists in AST)
**Verification needed**: Check if AST has this
**If exists**: Parser doesn't check for 'const' modifier
**Syntax**: `<const T extends readonly any[]>`
**Impact**: 10+ conformance test failures

### Low Impact

#### 3. TypeAbstractConstructor (if exists in AST)
**Defined**: Possibly in AST
**Never created**: `constructor_type()` doesn't check for 'abstract'
**Syntax**: `abstract new (): T`
**Impact**: 3-5 conformance test failures

## Unused Parser Functions

### Functions Defined But Never Called

(Run the analysis and list any found)

**Example findings**:
```
parse_old_style_type_assertion  # line 1234 - legacy feature?
is_definitely_type_argument     # line 567 - helper never used?
```

For each:
1. Verify it's truly unused (check all parser files)
2. Check git history - was it deprecated?
3. Determine if it should be removed or is WIP

## Unreachable Match Arms

### Type Primary Match

**File**: type_expr.rs:320
**Function**: type_primary

```rust
match self.peek().typ {
    TT::KeywordString => { /* REACHABLE */ },
    TT::KeywordNumber => { /* REACHABLE */ },
    // ...
    TT::KeywordFoo => { /* UNREACHABLE? - verify this keyword exists */ },
}
```

**Action**: Check if all match arms can actually be reached

### Potential Issues

1. **Token types that don't exist**: Match arm for token that's never produced by lexer
2. **Impossible lookahead**: Predicate that can never be true
3. **Dead branches**: After exhaustive if/else, unreachable code

## Dead Code Patterns

### Pattern 1: Commented-Out Code

```bash
# Find commented-out parsing logic
grep -n "//.*fn.*type" src/parse/type_expr.rs
grep -n "//.*TypeExpr::" src/parse/type_expr.rs
```

**Found**: (list any significant commented code)

### Pattern 2: Incomplete Implementations

```bash
# Find unimplemented!() or todo!()
grep -n "unimplemented!\|todo!\|panic!" src/parse/type_expr.rs
```

**Found**: (list locations)

### Pattern 3: Unreachable After Return

```rust
fn example() -> Result<T> {
    if condition {
        return Ok(...);
    }
    return Ok(...);

    // Unreachable code here
    let x = 5;  // Never executes
}
```

## Recommendations

### Immediate Actions

1. **Verify all "orphaned" nodes**
   - Some may be false positives
   - Some may be constructed in other files (ts_decl.rs, stmt.rs)
   - Create comprehensive grep search

2. **Remove dead code**
   - Delete commented-out sections if > 6 months old
   - Remove unused helper functions
   - Simplify unreachable match arms

3. **Document incomplete features**
   - Mark TODOs with issue numbers
   - Add tests for unimplemented features
   - Track in missing features list

### Planning Phase Input

**For 02-planning/03-plan-parser-extensions**:
- Which parser functions need extension
- Which new functions needed
- Which can be removed/refactored

**For 03-implementation**:
- Clear targets: orphaned nodes that need parsers
- Estimated complexity based on existing similar parsers
```

### Step 4: Analyze Parser Coverage by TypeScript Feature

Cross-reference with TypeScript syntax:

**parser-coverage-report.md**:

```markdown
# Parser Coverage Report

**Analysis Date**: 2025-11-20
**Parser LoC**: ~1,743 (type_expr.rs)
**Total Functions**: 67
**AST Nodes**: 45

## Executive Summary

- **Total TypeScript Type Syntax Patterns**: 87
- **Parsed by ecma-rs**: 73
- **Missing Parsers**: 14
- **Parser Coverage**: 83.9%
- **Orphaned AST Nodes**: 4-7 (verification needed)
- **Dead Parser Functions**: 0-3 (verification needed)

## Coverage by Feature Category

| Category | Syntax Patterns | Parsed | Missing | Coverage |
|----------|----------------|--------|---------|----------|
| Primitives | 12 | 12 | 0 | 100% |
| Object Types | 8 | 7 | 1 | 87.5% |
| Function Types | 4 | 4 | 0 | 100% |
| Array/Tuple | 8 | 7 | 1 | 87.5% |
| Unions/Intersections | 3 | 3 | 0 | 100% |
| Literal Types | 6 | 6 | 0 | 100% |
| Type Operators | 5 | 5 | 0 | 100% |
| Advanced Types | 9 | 8 | 1 | 88.9% |
| Type Parameters | 6 | 5 | 1 | 83.3% |
| Declarations | 8 | 8 | 0 | 100% |
| Modern Features | 4 | 1 | 3 | 25% |

## Parser Function Quality Assessment

### Well-Implemented Parsers (High Quality)

1. **type_union / type_intersection**
   - Clean implementation
   - Handles nested unions/intersections
   - Good error messages
   - **Quality**: ⭐⭐⭐⭐⭐

2. **conditional_type**
   - Complex feature well-structured
   - Handles distributive conditionals
   - Nested conditionals work
   - **Quality**: ⭐⭐⭐⭐⭐

3. **mapped_type**
   - Handles modifiers correctly (+? -? readonly)
   - Clean structure
   - **Potential gap**: 'as' clause (verify)
   - **Quality**: ⭐⭐⭐⭐

### Parsers Needing Attention

1. **type_primary**
   - **Issue**: Very long function (~200 lines)
   - **Issue**: Many match arms could be refactored
   - **Issue**: May not handle readonly+[ combination
   - **Recommendation**: Split into smaller functions
   - **Quality**: ⭐⭐⭐

2. **is_start_of_type_arguments**
   - **Issue**: Complex lookahead logic
   - **Issue**: May have false positives
   - **Concern**: Performance impact
   - **Recommendation**: Add speculation caching
   - **Quality**: ⭐⭐⭐

3. **tuple_type**
   - **Implementation**: Appears solid
   - **Gap**: Combination with readonly keyword
   - **Action**: Verify parser flow for `readonly [T, ...U]`
   - **Quality**: ⭐⭐⭐⭐

## Missing Parsers (High Priority)

### 1. Import TypeOf Parser
**Syntax**: `typeof import('./module')`
**Current State**: `typeof_type()` doesn't handle import expressions
**Impact**: HIGH - 20+ test failures
**Complexity**: LOW - extend existing function

**Implementation**:
```rust
fn typeof_type(&mut self) -> Result<TypeExpr> {
    self.require(TT::KeywordTypeof)?;

    if self.peek().typ == TT::KeywordImport {
        // Parse import type
        let import_type = self.import_type()?;
        return Ok(TypeExpr::TypeOf(Box::new(TypeExpr::Import(import_type))));
    }

    // Regular typeof
    let entity = self.type_entity_name()?;
    Ok(TypeExpr::TypeOf(entity))
}
```

### 2. Const Type Parameter Parser
**Syntax**: `<const T extends readonly any[]>`
**Current State**: `parse_type_parameter()` ignores 'const'
**Impact**: MEDIUM - 10+ test failures
**Complexity**: LOW - add modifier parsing

**Implementation**:
```rust
fn parse_type_parameter(&mut self) -> Result<TypeParam> {
    // Check for 'const' modifier
    let is_const = self.consume_if(TT::KeywordConst).is_match();

    let name = self.require_identifier()?;
    // ... rest of parsing

    TypeParam {
        name,
        is_const,  // Add this field to AST if missing
        // ...
    }
}
```

### 3. Using Declarations Parser
**Syntax**: `using x = getResource()`
**Current State**: No parser
**Impact**: MEDIUM - 5+ test failures
**Complexity**: MEDIUM - new statement type

**Implementation**: New parser in stmt.rs

## Orphaned AST Nodes Analysis

### Confirmed Orphaned

(After verification, list nodes that are truly never created)

### False Positives

(List nodes thought orphaned but actually created elsewhere)

## Dead Code Findings

### Unused Functions

(List after analysis)

### Unreachable Match Arms

(List after inspection)

### Commented Code

(List significant commented-out sections)

## Parser Architecture Assessment

### Strengths

1. **Recursive descent structure** - Easy to understand
2. **Precedence handling** - Union/intersection precedence correct
3. **Lookahead predicates** - Good for disambiguation
4. **Error recovery** - Some attempts at recovery

### Weaknesses

1. **Large functions** - type_primary() too long
2. **Speculation overhead** - is_start_of_type_arguments scans twice
3. **Error messages** - Could be more specific
4. **Code duplication** - Some patterns repeated

### Opportunities

1. **Refactoring** - Split type_primary into smaller functions
2. **Caching** - Memoize speculation results
3. **Fast paths** - Optimize common cases
4. **Better errors** - Context-aware error messages

## Recommendations

### For Planning Phase

1. **Parser Extensions Needed**:
   - typeof_type: Add import() handling
   - parse_type_parameter: Add const modifier
   - type_primary: Add readonly [ lookahead
   - mapped_type: Add 'as' clause (if missing)

2. **New Parsers Needed**:
   - using_declaration (stmt.rs)
   - await_using_declaration (stmt.rs)
   - jsdoc_type_annotation (if needed)

3. **Refactoring Opportunities**:
   - Split type_primary
   - Extract common patterns
   - Add speculation cache

### For Implementation Phase

1. **Easy Wins** (1-2 hours each):
   - typeof import()
   - const type parameters
   - readonly tuple combination (if issue confirmed)

2. **Medium Effort** (4-8 hours):
   - mapped type 'as' clause
   - using declarations
   - abstract constructors

3. **Low Priority**:
   - JSDoc types
   - Dead code removal
   - Refactoring

## Appendix: Parser Function Reference

### Primary Entry Points

- `type_expr()` - Main entry for type expressions
- `type_annotation()` - Parses `: Type` annotations
- `type_arguments()` - Parses `<T, U>` arguments

### Type Construction

- `type_primary()` - Keywords, identifiers, parenthesized
- `type_postfix()` - Array access, property access
- `type_union()` - Union types
- `type_intersection()` - Intersection types

### Complex Types

- `conditional_type()` - T extends U ? X : Y
- `mapped_type()` - { [K in T]: V }
- `template_literal_type()` - Template strings
- `tuple_type()` - Tuple types
- `object_type()` - Object type literals
- `function_type()` - Function types

### Helpers

- `parse_type_parameters()` - <T, U> lists
- `tuple_element()` - Single tuple element
- `parse_type_member()` - Object member

### Lookahead

- `is_start_of_type()` - Type detection
- `is_start_of_type_arguments()` - < vs generic
- `is_start_of_function_type()` - Arrow function

## Verification Commands

```bash
# Count parser functions
grep -c "^\s*fn\s" src/parse/type_expr.rs

# Find all TypeExpr constructions
grep -n "TypeExpr::" src/parse/type_expr.rs | wc -l

# Check specific node is created
grep -n "TypeExpr::Conditional" src/parse/type_expr.rs

# Find unreachable code warnings
cargo build 2>&1 | grep -i "unreachable"

# Check for panics
grep -n "panic!\|unimplemented!\|todo!" src/parse/type_expr.rs
```
```

## Acceptance Criteria

### Required Outputs

✅ **parser-coverage-map.json**: Node-by-node parser coverage

✅ **parser-coverage-report.md**: Human-readable analysis

✅ **parser-function-inventory.json**: Complete function inventory

✅ **unreachable-code-analysis.md**: Dead code findings

### Quality Checks

- [ ] All parser functions inventoried
- [ ] Each AST node checked for parser
- [ ] Orphaned nodes verified (not guessed)
- [ ] Parser gaps identified with examples
- [ ] Line numbers accurate
- [ ] JSON validates

### Success Metrics

- Complete parser coverage map
- All orphaned nodes found
- Parser gaps clearly documented
- Recommendations actionable

## Common Issues & Solutions

### Issue: Can't tell if node is created

**Solution**:
```bash
# Search all parser files
grep -rn "TypeExpr::NodeName" src/parse/

# If no results, node is orphaned
```

### Issue: Function seems unused but isn't

**Solution**:
- Check it's not called from other modules
- Search entire codebase: `grep -rn "function_name" src/`
- Check for method calls: `self.function_name`

### Issue: Can't understand complex parser

**Solution**:
1. Add debug prints and run on test case
2. Use debugger with breakpoint
3. Draw parse tree diagram
4. Compare with TypeScript's parser

## Time Estimate Breakdown

- File reading & setup: 1 hour
- Function inventory: 1.5 hours
- Node coverage mapping: 1.5 hours
- Dead code analysis: 1 hour
- Write reports: 1.5 hours
- Verification: 30 min

**Total: 4-6 hours**

## Downstream Impact

Provides critical input for:
- **02-planning/03-plan-parser-extensions**: Which functions to extend/create
- **03-implementation/***: Implementation complexity estimates
- **Code quality**: Dead code removal opportunities

## Notes for Agent

- Verify everything - don't assume
- "grep" is your best friend for this task
- When in doubt about dead code, leave it (better than breaking)
- Document uncertainties clearly
- Your findings directly impact implementation efficiency

---

**Ready?** Start with Step 1: Inventory All Parser Functions
