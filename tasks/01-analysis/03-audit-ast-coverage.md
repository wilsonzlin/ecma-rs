---
task_id: "01-analysis/03-audit-ast-coverage"
title: "Audit AST Coverage of TypeScript Features"
phase: "analysis"
estimated_duration: "3-5 hours"
complexity: "medium"
dependencies: []
inputs: []
outputs:
  - "ast-coverage-map.json"
  - "ast-coverage-report.md"
  - "missing-ast-nodes.md"
  - "ast-node-inventory.json"
skills_required:
  - "Rust code reading"
  - "TypeScript knowledge"
  - "Data analysis"
---

# Task: Audit AST Coverage of TypeScript Features

## Objective

Systematically inventory all TypeScript type-related AST nodes currently implemented in ecma-rs and identify gaps against the full TypeScript type system specification.

## Context

### Why This Matters

Before implementing missing parser features, we need to know:
1. **What AST nodes exist** - Inventory current type expression structures
2. **What's missing** - Compare against TypeScript's complete type grammar
3. **What's partial** - Identify nodes that exist but may lack fields
4. **What's unused** - Find defined nodes that parser doesn't populate

This analysis informs:
- Planning phase: What AST extensions are needed
- Implementation phase: Whether to extend existing nodes or create new ones
- Validation phase: Completeness metrics

### Current State

The AST is defined in:
- `parse-js/src/ast/type_expr.rs` (~427 lines) - Core type expressions
- `parse-js/src/ast/ts_stmt.rs` - TypeScript declarations (interfaces, enums, etc.)
- `parse-js/src/ast/expr.rs` - Type assertions, satisfies, as const
- `parse-js/src/ast/stmt.rs` - Type annotations on statements

### TypeScript Type Grammar Reference

TypeScript's complete type grammar:
- Primitive types: string, number, boolean, bigint, symbol, any, unknown, never, void, null, undefined
- Object types: interfaces, type literals, index signatures
- Function types: call signatures, construct signatures
- Array/Tuple types: T[], [T, U], [...T[]]
- Union/Intersection: T | U, T & U
- Literal types: "string", 123, true
- Operators: typeof, keyof, readonly, unique
- Advanced: conditional, mapped, template literal, indexed access, infer
- Modifiers: ?, +?, -?, readonly, abstract

## Prerequisites

### Files to Read

1. **Type Expression AST** (`parse-js/src/ast/type_expr.rs`)
   - Primary source of type-related structures
   - Read every `pub struct` and `pub enum`
   - Note derive macros and field types

2. **TypeScript Statement AST** (`parse-js/src/ast/ts_stmt.rs`)
   - Type aliases, interfaces, enums
   - Declaration structures

3. **Expression AST** (`parse-js/src/ast/expr.rs`)
   - Type assertions (`as`, `satisfies`)
   - Const assertions

4. **Statement AST** (`parse-js/src/ast/stmt.rs`)
   - Type annotations on variables, functions

### Reference Documentation

- TypeScript Handbook: https://www.typescriptlang.org/docs/handbook/2/everyday-types.html
- TypeScript Spec: https://github.com/microsoft/TypeScript/blob/main/doc/spec-ARCHIVED.md
- TypeScript AST Viewer: https://ts-ast-viewer.com/

## Instructions

### Step 1: Extract All Type-Related AST Nodes

Create a comprehensive inventory:

```bash
cd /home/user/ecma-rs/parse-js

# Extract all structs from type_expr.rs
grep -n "pub struct" src/ast/type_expr.rs > /tmp/type_structs.txt

# Extract all enum variants from TypeExpr
awk '/pub enum TypeExpr/,/^}/' src/ast/type_expr.rs > /tmp/type_expr_enum.txt

# Extract TypeScript declarations
grep -n "pub struct" src/ast/ts_stmt.rs > /tmp/ts_decl_structs.txt

# Count nodes
echo "Type structs: $(wc -l < /tmp/type_structs.txt)"
echo "TypeScript declarations: $(wc -l < /tmp/ts_decl_structs.txt)"
```

Create structured inventory: **ast-node-inventory.json**

```json
{
  "timestamp": "2025-11-20T10:00:00Z",
  "total_type_nodes": 45,
  "categories": {
    "primitive_types": {
      "count": 10,
      "nodes": [
        {"name": "TypeString", "file": "type_expr.rs", "line": 42},
        {"name": "TypeNumber", "file": "type_expr.rs", "line": 47},
        {"name": "TypeBoolean", "file": "type_expr.rs", "line": 52},
        {"name": "TypeAny", "file": "type_expr.rs", "line": 57},
        {"name": "TypeUnknown", "file": "type_expr.rs", "line": 62},
        {"name": "TypeNever", "file": "type_expr.rs", "line": 67},
        {"name": "TypeVoid", "file": "type_expr.rs", "line": 72},
        {"name": "TypeNull", "file": "type_expr.rs", "line": 77},
        {"name": "TypeUndefined", "file": "type_expr.rs", "line": 82},
        {"name": "TypeSymbol", "file": "type_expr.rs", "line": 87}
      ]
    },
    "object_types": {
      "count": 8,
      "nodes": [
        {"name": "TypeObject", "file": "type_expr.rs", "line": 120,
         "fields": ["members: Vec<TypeObjectMember>"]},
        {"name": "TypeObjectMember", "file": "type_expr.rs", "line": 125,
         "variants": ["Property", "Method", "CallSignature", "ConstructSignature", "IndexSignature"]},
        {"name": "TypeInterface", "file": "ts_stmt.rs", "line": 45,
         "fields": ["name", "type_parameters", "extends", "members"]},
        {"name": "TypeIndexSignature", "file": "type_expr.rs", "line": 180}
      ]
    },
    "function_types": {
      "count": 3,
      "nodes": [
        {"name": "TypeFunction", "file": "type_expr.rs", "line": 200},
        {"name": "TypeConstructor", "file": "type_expr.rs", "line": 215}
      ]
    },
    "array_tuple_types": {
      "count": 4,
      "nodes": [
        {"name": "TypeArray", "file": "type_expr.rs", "line": 92},
        {"name": "TypeTuple", "file": "type_expr.rs", "line": 151,
         "fields": ["readonly: bool", "elements: Vec<TypeTupleElement>"]},
        {"name": "TypeTupleElement", "file": "type_expr.rs", "line": 157,
         "fields": ["label", "optional", "rest", "type_expr"]}
      ]
    },
    "union_intersection": {
      "count": 2,
      "nodes": [
        {"name": "TypeUnion", "file": "type_expr.rs", "line": 97},
        {"name": "TypeIntersection", "file": "type_expr.rs", "line": 102}
      ]
    },
    "literal_types": {
      "count": 4,
      "nodes": [
        {"name": "TypeLitString", "file": "type_expr.rs", "line": 107},
        {"name": "TypeLitNumber", "file": "type_expr.rs", "line": 110},
        {"name": "TypeLitBoolean", "file": "type_expr.rs", "line": 113},
        {"name": "TypeLitBigInt", "file": "type_expr.rs", "line": 116}
      ]
    },
    "operators": {
      "count": 5,
      "nodes": [
        {"name": "TypeTypeOf", "file": "type_expr.rs", "line": 230},
        {"name": "TypeKeyOf", "file": "type_expr.rs", "line": 235},
        {"name": "TypeReadonly", "file": "type_expr.rs", "line": 240},
        {"name": "TypeUnique", "file": "type_expr.rs", "line": 245}
      ]
    },
    "advanced_types": {
      "count": 7,
      "nodes": [
        {"name": "TypeConditional", "file": "type_expr.rs", "line": 260},
        {"name": "TypeMapped", "file": "type_expr.rs", "line": 280},
        {"name": "TypeTemplateLiteral", "file": "type_expr.rs", "line": 300},
        {"name": "TypeIndexedAccess", "file": "type_expr.rs", "line": 320},
        {"name": "TypeInfer", "file": "type_expr.rs", "line": 340}
      ]
    },
    "declarations": {
      "count": 5,
      "nodes": [
        {"name": "TypeAliasDecl", "file": "ts_stmt.rs", "line": 30},
        {"name": "InterfaceDecl", "file": "ts_stmt.rs", "line": 45},
        {"name": "EnumDecl", "file": "ts_stmt.rs", "line": 80},
        {"name": "NamespaceDecl", "file": "ts_stmt.rs", "line": 120},
        {"name": "ModuleDecl", "file": "ts_stmt.rs", "line": 150}
      ]
    }
  }
}
```

**Note**: Fill in actual line numbers by reading the files!

### Step 2: Compare Against TypeScript Type Grammar

Create checklist of ALL TypeScript type features:

**ast-coverage-map.json**:

```json
{
  "coverage_date": "2025-11-20",
  "typescript_version": "5.6",
  "total_features": 87,
  "implemented": 73,
  "missing": 14,
  "coverage_percentage": 83.9,

  "features": {
    "primitives": {
      "string": {"status": "implemented", "ast_node": "TypeString"},
      "number": {"status": "implemented", "ast_node": "TypeNumber"},
      "boolean": {"status": "implemented", "ast_node": "TypeBoolean"},
      "bigint": {"status": "implemented", "ast_node": "TypeBigInt"},
      "symbol": {"status": "implemented", "ast_node": "TypeSymbol"},
      "any": {"status": "implemented", "ast_node": "TypeAny"},
      "unknown": {"status": "implemented", "ast_node": "TypeUnknown"},
      "never": {"status": "implemented", "ast_node": "TypeNever"},
      "void": {"status": "implemented", "ast_node": "TypeVoid"},
      "null": {"status": "implemented", "ast_node": "TypeNull"},
      "undefined": {"status": "implemented", "ast_node": "TypeUndefined"},
      "object": {"status": "implemented", "ast_node": "TypeObject"}
    },

    "object_types": {
      "type_literal": {"status": "implemented", "ast_node": "TypeObject"},
      "interface": {"status": "implemented", "ast_node": "InterfaceDecl"},
      "property_signature": {"status": "implemented", "ast_node": "TypeObjectMember::Property"},
      "method_signature": {"status": "implemented", "ast_node": "TypeObjectMember::Method"},
      "call_signature": {"status": "implemented", "ast_node": "TypeObjectMember::CallSignature"},
      "construct_signature": {"status": "implemented", "ast_node": "TypeObjectMember::ConstructSignature"},
      "index_signature": {"status": "implemented", "ast_node": "TypeIndexSignature"},
      "abstract_construct_signature": {"status": "unknown", "ast_node": null, "note": "Check if 'abstract' modifier supported"}
    },

    "function_types": {
      "function_type": {"status": "implemented", "ast_node": "TypeFunction"},
      "constructor_type": {"status": "implemented", "ast_node": "TypeConstructor"},
      "this_parameter": {"status": "implemented", "ast_node": "TypeFunction.this_param"},
      "rest_parameters": {"status": "implemented", "ast_node": "TypeFunction.params"}
    },

    "array_tuple": {
      "array_type": {"status": "implemented", "ast_node": "TypeArray"},
      "readonly_array": {"status": "implemented", "ast_node": "TypeArray with readonly"},
      "tuple_type": {"status": "implemented", "ast_node": "TypeTuple"},
      "readonly_tuple": {"status": "implemented", "ast_node": "TypeTuple.readonly"},
      "tuple_rest_element": {"status": "implemented", "ast_node": "TypeTupleElement.rest"},
      "tuple_optional_element": {"status": "implemented", "ast_node": "TypeTupleElement.optional"},
      "tuple_labeled_element": {"status": "implemented", "ast_node": "TypeTupleElement.label"},
      "readonly_tuple_with_rest": {"status": "unknown", "ast_node": "TypeTuple", "note": "Combination - check parser"}
    },

    "unions_intersections": {
      "union_type": {"status": "implemented", "ast_node": "TypeUnion"},
      "intersection_type": {"status": "implemented", "ast_node": "TypeIntersection"},
      "discriminated_union": {"status": "implemented", "ast_node": "TypeUnion", "note": "AST same as union"}
    },

    "literal_types": {
      "string_literal": {"status": "implemented", "ast_node": "TypeLitString"},
      "numeric_literal": {"status": "implemented", "ast_node": "TypeLitNumber"},
      "boolean_literal": {"status": "implemented", "ast_node": "TypeLitBoolean"},
      "bigint_literal": {"status": "implemented", "ast_node": "TypeLitBigInt"},
      "null_literal": {"status": "implemented", "ast_node": "TypeNull"},
      "undefined_literal": {"status": "implemented", "ast_node": "TypeUndefined"}
    },

    "type_operators": {
      "typeof": {"status": "implemented", "ast_node": "TypeTypeOf"},
      "keyof": {"status": "implemented", "ast_node": "TypeKeyOf"},
      "readonly": {"status": "implemented", "ast_node": "TypeReadonly"},
      "unique_symbol": {"status": "implemented", "ast_node": "TypeUnique"},
      "infer": {"status": "implemented", "ast_node": "TypeInfer"}
    },

    "advanced_types": {
      "conditional_type": {"status": "implemented", "ast_node": "TypeConditional"},
      "conditional_with_infer": {"status": "implemented", "ast_node": "TypeConditional + TypeInfer"},
      "conditional_distributive": {"status": "implemented", "ast_node": "TypeConditional", "note": "Semantic, not AST"},
      "mapped_type": {"status": "implemented", "ast_node": "TypeMapped"},
      "mapped_with_as": {"status": "unknown", "ast_node": "TypeMapped", "note": "Check if 'as' clause supported"},
      "mapped_readonly_modifier": {"status": "implemented", "ast_node": "TypeMapped.readonly_modifier"},
      "mapped_optional_modifier": {"status": "implemented", "ast_node": "TypeMapped.optional_modifier"},
      "template_literal_type": {"status": "implemented", "ast_node": "TypeTemplateLiteral"},
      "indexed_access": {"status": "implemented", "ast_node": "TypeIndexedAccess"}
    },

    "type_parameters": {
      "generic_type": {"status": "implemented", "ast_node": "TypeReference"},
      "type_parameter": {"status": "implemented", "ast_node": "TypeParam"},
      "type_constraint": {"status": "implemented", "ast_node": "TypeParam.constraint"},
      "type_default": {"status": "implemented", "ast_node": "TypeParam.default"},
      "const_type_parameter": {"status": "unknown", "ast_node": "TypeParam", "note": "Check if 'const' modifier exists"},
      "variance_annotations": {"status": "implemented", "ast_node": "TypeParam.variance"}
    },

    "type_predicates": {
      "type_predicate": {"status": "implemented", "ast_node": "TypePredicate"},
      "asserts_predicate": {"status": "implemented", "ast_node": "TypePredicate.asserts"},
      "asserts_this": {"status": "unknown", "ast_node": null, "note": "Check 'asserts this is T'"}
    },

    "module_types": {
      "import_type": {"status": "implemented", "ast_node": "TypeImport"},
      "import_typeof": {"status": "unknown", "ast_node": null, "note": "typeof import('...')"},
      "export_type": {"status": "implemented", "ast_node": "ExportDecl with type"}
    },

    "utility_syntax": {
      "parenthesized_type": {"status": "implemented", "ast_node": "TypeParen"},
      "type_reference": {"status": "implemented", "ast_node": "TypeReference"},
      "qualified_name": {"status": "implemented", "ast_node": "TypeReference.name"},
      "this_type": {"status": "implemented", "ast_node": "TypeThis"}
    },

    "declarations": {
      "type_alias": {"status": "implemented", "ast_node": "TypeAliasDecl"},
      "interface": {"status": "implemented", "ast_node": "InterfaceDecl"},
      "interface_extends": {"status": "implemented", "ast_node": "InterfaceDecl.extends"},
      "interface_merging": {"status": "implemented", "ast_node": "InterfaceDecl", "note": "Semantic, not AST"},
      "enum": {"status": "implemented", "ast_node": "EnumDecl"},
      "const_enum": {"status": "implemented", "ast_node": "EnumDecl.is_const"},
      "namespace": {"status": "implemented", "ast_node": "NamespaceDecl"},
      "module": {"status": "implemented", "ast_node": "ModuleDecl"},
      "ambient_module": {"status": "implemented", "ast_node": "ModuleDecl.ambient"}
    },

    "decorators": {
      "decorator": {"status": "implemented", "ast_node": "Decorator"},
      "decorator_metadata": {"status": "unknown", "ast_node": null, "note": "TS 5.2 feature"}
    },

    "modern_features": {
      "satisfies_operator": {"status": "implemented", "ast_node": "ExprSatisfies"},
      "using_declarations": {"status": "unknown", "ast_node": null, "note": "TS 5.2 feature"},
      "await_using": {"status": "unknown", "ast_node": null, "note": "TS 5.2 feature"}
    },

    "jsdoc_types": {
      "jsdoc_type_annotation": {"status": "unknown", "ast_node": null, "note": "For JS files"},
      "jsdoc_import_type": {"status": "unknown", "ast_node": null}
    }
  },

  "missing_features": [
    {"feature": "abstract_construct_signature", "priority": "medium"},
    {"feature": "mapped_with_as", "priority": "low"},
    {"feature": "const_type_parameter", "priority": "medium"},
    {"feature": "asserts_this", "priority": "low"},
    {"feature": "import_typeof", "priority": "high"},
    {"feature": "decorator_metadata", "priority": "low"},
    {"feature": "using_declarations", "priority": "medium"},
    {"feature": "await_using", "priority": "medium"},
    {"feature": "jsdoc_types", "priority": "low"}
  ],

  "unknown_coverage": [
    "abstract_construct_signature",
    "mapped_with_as",
    "const_type_parameter",
    "asserts_this",
    "import_typeof",
    "readonly_tuple_with_rest",
    "decorator_metadata",
    "using_declarations",
    "await_using",
    "jsdoc_types"
  ]
}
```

### Step 3: Verify Unknown Coverage Items

For each "unknown" status item, check the actual AST:

```bash
# Example: Check if const type parameters exist
grep -n "const" parse-js/src/ast/type_expr.rs

# Check if TypeParam has a const field
awk '/pub struct TypeParam/,/^}/' parse-js/src/ast/type_expr.rs
```

Update the JSON with actual findings.

### Step 4: Identify Missing AST Nodes

Create **missing-ast-nodes.md**:

```markdown
# Missing AST Nodes Analysis

## High Priority Missing Nodes

### 1. Import TypeOf
**TypeScript Syntax**: `type T = typeof import('./module')`
**Current State**: TypeImport exists, but combination with typeof unknown
**Recommendation**:
- Option A: Extend TypeTypeOf to handle import expressions
- Option B: Add TypeImportTypeOf variant
**Impact**: Used in declaration files, ambient modules

### 2. Const Type Parameters
**TypeScript Syntax**: `function f<const T>(x: T)`
**Current State**: TypeParam exists, but 'const' modifier unknown
**Recommendation**: Add `is_const: bool` field to TypeParam
**Impact**: TS 5.0+ feature, increasingly common

### 3. Using Declarations
**TypeScript Syntax**: `using resource = getResource()`
**Current State**: No AST node
**Recommendation**: Add VarDeclUsing or flag on VarDecl
**Impact**: TS 5.2 feature, resource management

## Medium Priority Missing Nodes

### 4. Abstract Constructor Signatures
**TypeScript Syntax**: `abstract new (): T`
**Current State**: Constructor signatures exist, abstract modifier unknown
**Recommendation**: Add `is_abstract: bool` to ConstructSignature
**Impact**: Rare in practice, but part of spec

### 5. Mapped Type 'as' Clause
**TypeScript Syntax**: `{ [K in keyof T as NewKey<K>]: T[K] }`
**Current State**: TypeMapped exists, but 'as' clause unknown
**Recommendation**: Add `name_type: Option<TypeExpr>` to TypeMapped
**Impact**: TS 4.1+ feature, used in advanced type utilities

## Low Priority Missing Nodes

### 6. JSDoc Type Annotations
**TypeScript Syntax**: `/** @type {string} */`
**Current State**: No representation
**Recommendation**: Extend Comment or add JSDocType
**Impact**: Only needed for JS files with type checking

## Complete or Partial Nodes Needing Extension

### TypeTuple
**Current**: `{ readonly: bool, elements: Vec<TypeTupleElement> }`
**Issue**: Combination `readonly [T, ...U[]]` may not parse
**Action**: Verify parser handles this combination

### TypeMapped
**Current**: Has readonly_modifier, optional_modifier
**Issue**: May be missing 'as' clause for key remapping
**Action**: Check for `name_type` field

### TypeParam
**Current**: Has constraint, default, variance
**Issue**: May be missing 'const' modifier (TS 5.0)
**Action**: Add `is_const: bool` if missing

### Decorator
**Current**: Decorator structure exists
**Issue**: TS 5.2 decorator metadata unknown
**Action**: Check if metadata field exists
```

### Step 5: Create Coverage Report

**ast-coverage-report.md**:

```markdown
# AST Coverage Report

**Analysis Date**: 2025-11-20
**TypeScript Version**: 5.6
**ecma-rs Commit**: c2f4063

## Executive Summary

- **Total TypeScript Type Features**: 87
- **Implemented in AST**: 73
- **Missing from AST**: 4
- **Unknown Status**: 10
- **Coverage Percentage**: 83.9%

## Coverage by Category

| Category | Total | Implemented | Missing | Coverage |
|----------|-------|-------------|---------|----------|
| Primitives | 12 | 12 | 0 | 100% |
| Object Types | 8 | 7 | 1 | 87.5% |
| Function Types | 4 | 4 | 0 | 100% |
| Array/Tuple | 8 | 7 | 1 | 87.5% |
| Unions/Intersections | 3 | 3 | 0 | 100% |
| Literal Types | 6 | 6 | 0 | 100% |
| Type Operators | 5 | 5 | 0 | 100% |
| Advanced Types | 9 | 8 | 1 | 88.9% |
| Type Parameters | 6 | 5 | 1 | 83.3% |
| Type Predicates | 3 | 2 | 1 | 66.7% |
| Module Types | 3 | 2 | 1 | 66.7% |
| Declarations | 8 | 8 | 0 | 100% |
| Modern Features | 4 | 1 | 3 | 25% |
| JSDoc | 2 | 0 | 2 | 0% |

## High-Impact Missing Nodes

### 1. Import TypeOf (Priority: HIGH)
**Impact**: Declaration files, ambient modules
**Syntax**: `typeof import('./module')`
**Workaround**: None - feature missing
**Estimated Failures**: 20-30 conformance tests

### 2. Const Type Parameters (Priority: MEDIUM)
**Impact**: TS 5.0+ code increasingly common
**Syntax**: `<const T extends readonly any[]>`
**Workaround**: Parse as regular generic, ignore const
**Estimated Failures**: 10-15 conformance tests

### 3. Using Declarations (Priority: MEDIUM)
**Impact**: TS 5.2 resource management
**Syntax**: `using x = getResource()`
**Workaround**: None - new statement type
**Estimated Failures**: 5-10 conformance tests

## Nodes That May Need Extension

### TypeTuple
- **Has**: `readonly: bool`, `elements: Vec<TypeTupleElement>`
- **May Need**: Verify `readonly [T, ...U[]]` combination works
- **Action**: Check parser, not AST

### TypeMapped
- **Has**: `readonly_modifier`, `optional_modifier`
- **May Need**: `name_type: Option<TypeExpr>` for 'as' clause
- **Action**: Verify field exists

### TypeParam
- **Has**: `constraint`, `default`, `variance`
- **May Need**: `is_const: bool` for const type parameters
- **Action**: Check struct definition

## Recommendations

### Immediate Actions

1. **Verify Unknown Coverage Items**
   - Read actual struct definitions
   - Update coverage map with reality
   - Some "unknown" may actually be implemented

2. **Document Partial Coverage**
   - Nodes exist but may lack fields
   - Example: TypeMapped may need 'as' clause field

3. **Prioritize Extensions**
   - High impact: Import typeof
   - Medium impact: Const type params, using declarations
   - Low impact: JSDoc types (only for minifying JS)

### Planning Phase Input

This analysis provides:
- **For 02-design-ast-nodes**: Which nodes to add/extend
- **For 03-plan-parser-extensions**: What parser changes needed
- **For implementation**: Estimated complexity per feature

## Detailed Node Inventory

### Primitives (12/12 ✅)
- TypeString ✅
- TypeNumber ✅
- TypeBoolean ✅
- TypeBigInt ✅
- TypeSymbol ✅
- TypeAny ✅
- TypeUnknown ✅
- TypeNever ✅
- TypeVoid ✅
- TypeNull ✅
- TypeUndefined ✅
- TypeObject ✅

### Object Types (7/8)
- TypeObject ✅
- TypeObjectMember ✅
- InterfaceDecl ✅
- TypeIndexSignature ✅
- PropertySignature ✅
- MethodSignature ✅
- CallSignature ✅
- AbstractConstructSignature ❌

### Function Types (4/4 ✅)
- TypeFunction ✅
- TypeConstructor ✅
- ThisParameter ✅
- RestParameters ✅

### Array/Tuple (7/8)
- TypeArray ✅
- ReadonlyArray ✅
- TypeTuple ✅
- ReadonlyTuple ✅
- TupleRestElement ✅
- TupleOptionalElement ✅
- TupleLabeledElement ✅
- ReadonlyTupleWithRest ❓ (combination - verify parser)

### Advanced Types (8/9)
- TypeConditional ✅
- TypeMapped ✅
- TypeTemplateLiteral ✅
- TypeIndexedAccess ✅
- TypeInfer ✅
- ConditionalWithInfer ✅
- MappedReadonlyModifier ✅
- MappedOptionalModifier ✅
- MappedAsClause ❓ (verify field exists)

### Modern Features (1/4)
- SatisfiesOperator ✅
- UsingDeclarations ❌
- AwaitUsing ❌
- DecoratorMetadata ❓

## Next Steps

1. **Verification** (01-analysis/04-audit-parser-coverage)
   - Check which nodes parser actually populates
   - Find "zombie nodes" (defined but never created)

2. **Planning** (02-planning/02-design-ast-nodes)
   - Design extensions for partial nodes
   - Design new nodes for missing features
   - Consider backward compatibility

3. **Implementation**
   - Start with high-priority missing nodes
   - Extend partial nodes as needed
   - Add tests for each new node type

## Appendix: Verification Commands

```bash
# Count total type structs
grep -c "pub struct.*Type" parse-js/src/ast/type_expr.rs

# List all TypeExpr variants
awk '/pub enum TypeExpr/,/^}/' parse-js/src/ast/type_expr.rs | grep "^\s*[A-Z]"

# Check specific field existence
awk '/pub struct TypeMapped/,/^}/' parse-js/src/ast/type_expr.rs | grep -i "name_type"

# Find TODO comments in AST
grep -rn "TODO.*type" parse-js/src/ast/
```
```

## Acceptance Criteria

### Required Outputs

✅ **ast-coverage-map.json**: Complete feature-by-feature coverage mapping

✅ **ast-coverage-report.md**: Human-readable analysis with recommendations

✅ **missing-ast-nodes.md**: Prioritized list of missing/partial nodes

✅ **ast-node-inventory.json**: Complete inventory of existing nodes

### Quality Checks

- [ ] All 87 TypeScript type features categorized
- [ ] Every "unknown" status verified against actual code
- [ ] Missing nodes prioritized (high/medium/low)
- [ ] Line numbers accurate for all node references
- [ ] JSON files validate with `jq`
- [ ] Coverage percentage calculated correctly

### Success Metrics

- Complete inventory of AST nodes
- Clear gap analysis
- Actionable recommendations for planning phase
- No guesswork - all "unknown" items verified

## Common Issues & Solutions

### Issue: Can't determine if feature implemented

**Solution**:
1. Search for keywords in AST files: `grep -i "feature_name" src/ast/*.rs`
2. Check TypeScript test cases that use the feature
3. Try parsing example code and inspecting AST output

### Issue: AST node exists but unclear if complete

**Solution**:
1. Compare struct fields against TypeScript spec
2. Look for TODO comments near the struct
3. Check git history: `git log -p --follow -- src/ast/type_expr.rs`

### Issue: TypeScript spec is ambiguous

**Solution**:
1. Check TypeScript source code: `parse-js/tests/TypeScript/src/compiler/types.ts`
2. Use ts-ast-viewer.com with example code
3. Read TypeScript GitHub issues/PRs for feature discussions

## Time Estimate Breakdown

- Setup & file reading: 1 hour
- Extract node inventory: 1 hour
- Compare against TS grammar: 1.5 hours
- Verify unknowns: 1 hour
- Write reports: 1.5 hours
- Validation: 30 min

**Total: 3-5 hours**

## Downstream Impact

This task provides critical input for:
- **02-planning/02-design-ast-nodes**: What to add/extend
- **02-planning/03-plan-parser-extensions**: Parser changes needed
- **03-implementation/***: Complexity estimates per feature

## Notes for Agent

- Be thorough - don't guess on "unknown" items
- Verify everything against actual source code
- Line numbers are important for planning phase
- Your accuracy directly impacts implementation success
- If confused about a feature, document the confusion

---

**Ready?** Start with Step 1: Extract All Type-Related AST Nodes
