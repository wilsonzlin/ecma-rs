---
task_id: "01-analysis/05-research-feature-usage"
title: "Research TypeScript Feature Usage in Real-World Code"
phase: "analysis"
estimated_duration: "3-4 hours"
complexity: "medium"
dependencies: []
inputs: []
outputs:
  - "feature-frequency-analysis.json"
  - "real-world-usage-report.md"
  - "popular-patterns.md"
  - "sample-snippets/"
skills_required:
  - "TypeScript knowledge"
  - "Data analysis"
  - "GitHub code search"
---

# Task: Research TypeScript Feature Usage in Real-World Code

## Objective

Analyze real-world TypeScript codebases to determine which type system features are actually used in practice, how frequently, and in what contexts. This data informs prioritization: implement commonly-used features first.

## Context

### Why This Matters

Not all TypeScript features are equally important:
- **High usage**: `type`, `interface`, `generics` → Must implement perfectly
- **Medium usage**: `conditional types`, `mapped types` → Important for libraries
- **Low usage**: `template literal types`, `unique symbol` → Can defer
- **Rare**: Some edge cases may not be worth implementing

**Data-driven prioritization** beats guessing.

### What We're Measuring

1. **Feature frequency**: How often each type feature appears
2. **Context of use**: Libraries vs applications, .d.ts vs .ts
3. **Patterns**: Common idioms and combinations
4. **Evolution**: New features (TS 4.x, 5.x) vs legacy (TS 2.x, 3.x)

### Sample Selection

Target codebases:
- **Libraries**: React, Vue, Angular, Express, Lodash
- **Frameworks**: Next.js, Remix, SvelteKit
- **Tools**: TypeScript itself, Babel, ESLint
- **Large apps**: VSCode, Notion (if public)

Rationale: These represent diverse usage patterns and are likely minification targets.

## Prerequisites

### Tools Needed

1. **GitHub Code Search**: https://github.com/search
2. **sourcegraph.com**: For cross-repo searches
3. **grep/ripgrep**: For local analysis
4. **jq**: JSON processing

### TypeScript Codebases to Clone

```bash
# Create workspace for samples
mkdir -p /tmp/typescript-samples
cd /tmp/typescript-samples

# Clone representative projects (shallow clone to save space)
git clone --depth 1 https://github.com/microsoft/TypeScript
git clone --depth 1 https://github.com/DefinitelyTyped/DefinitelyTyped
git clone --depth 1 https://github.com/facebook/react
git clone --depth 1 https://github.com/vuejs/core vue
git clone --depth 1 https://github.com/angular/angular
git clone --depth 1 https://github.com/vercel/next.js

# Declaration files are particularly interesting
# DefinitelyTyped has thousands of .d.ts files
```

## Instructions

### Step 1: Clone Sample Repositories

```bash
mkdir -p /tmp/typescript-samples
cd /tmp/typescript-samples

# Core projects (do these at minimum)
git clone --depth 1 https://github.com/microsoft/TypeScript
git clone --depth 1 https://github.com/DefinitelyTyped/DefinitelyTyped

# Pick 3-4 more based on relevance to minification use case
git clone --depth 1 https://github.com/facebook/react
git clone --depth 1 https://github.com/vuejs/core vue
git clone --depth 1 https://github.com/vercel/next.js
```

**Disk space**: ~2-3 GB total

### Step 2: Count Feature Occurrences

Create search patterns for each TypeScript feature:

```bash
cd /tmp/typescript-samples

# Helper function to count across all repos
count_pattern() {
    pattern=$1
    description=$2
    count=$(find . -name "*.ts" -o -name "*.tsx" -o -name "*.d.ts" | \
            xargs grep -c "$pattern" 2>/dev/null | \
            awk -F: '{sum+=$2} END {print sum}')
    echo "$description: $count"
}

# Primitives
count_pattern ": string" "String type annotation"
count_pattern ": number" "Number type annotation"
count_pattern ": boolean" "Boolean type annotation"

# Advanced features
count_pattern "extends.*\?" "Conditional types"
count_pattern "in keyof" "Mapped types"
count_pattern "\${.*}" "Template literal types (approximate)"
count_pattern "infer " "Infer keyword"

# Declarations
count_pattern "^type " "Type aliases"
count_pattern "^interface " "Interfaces"
count_pattern "^enum " "Enums"

# Type operators
count_pattern "typeof " "Typeof operator"
count_pattern "keyof " "Keyof operator"
count_pattern "readonly " "Readonly modifier"

# Store results
```

Create comprehensive frequency analysis: **feature-frequency-analysis.json**

```json
{
  "analysis_date": "2025-11-20",
  "repositories_analyzed": [
    {"name": "TypeScript", "files": 3542, "lines": 452893},
    {"name": "DefinitelyTyped", "files": 8234, "lines": 1283472},
    {"name": "React", "files": 423, "lines": 89234},
    {"name": "Vue", "files": 512, "lines": 67123},
    {"name": "Next.js", "files": 1234, "lines": 156789}
  ],
  "total_typescript_files": 13945,
  "total_lines_analyzed": 2049511,

  "feature_frequency": {
    "primitives": {
      "string_annotation": {
        "occurrences": 45230,
        "percentage": 22.1,
        "contexts": ["function params", "object properties", "variables"],
        "priority": "critical"
      },
      "number_annotation": {
        "occurrences": 28934,
        "percentage": 14.1,
        "priority": "critical"
      },
      "boolean_annotation": {
        "occurrences": 15672,
        "percentage": 7.6,
        "priority": "critical"
      },
      "any_annotation": {
        "occurrences": 12456,
        "percentage": 6.1,
        "note": "Often used as escape hatch",
        "priority": "critical"
      },
      "unknown_annotation": {
        "occurrences": 3421,
        "percentage": 1.7,
        "note": "Preferred over 'any' in modern code",
        "priority": "high"
      },
      "never_annotation": {
        "occurrences": 2134,
        "percentage": 1.0,
        "priority": "high"
      },
      "void_annotation": {
        "occurrences": 8923,
        "percentage": 4.4,
        "priority": "critical"
      }
    },

    "declarations": {
      "type_alias": {
        "occurrences": 34567,
        "percentage": 16.9,
        "contexts": ["utility types", "union types", "complex types"],
        "priority": "critical"
      },
      "interface": {
        "occurrences": 28934,
        "percentage": 14.1,
        "contexts": ["object shapes", "API contracts", "OOP"],
        "priority": "critical"
      },
      "enum": {
        "occurrences": 4521,
        "percentage": 2.2,
        "note": "Declining in favor of unions",
        "priority": "high"
      },
      "const_enum": {
        "occurrences": 1203,
        "percentage": 0.6,
        "note": "Used for performance",
        "priority": "medium"
      },
      "namespace": {
        "occurrences": 3421,
        "percentage": 1.7,
        "note": "Legacy, replaced by modules",
        "priority": "medium"
      }
    },

    "generics": {
      "generic_types": {
        "occurrences": 42134,
        "percentage": 20.6,
        "note": "Extremely common in libraries",
        "priority": "critical"
      },
      "generic_constraints": {
        "occurrences": 15234,
        "percentage": 7.4,
        "pattern": "T extends U",
        "priority": "critical"
      },
      "generic_defaults": {
        "occurrences": 5431,
        "percentage": 2.7,
        "pattern": "T = DefaultType",
        "priority": "high"
      }
    },

    "union_intersection": {
      "union_types": {
        "occurrences": 38742,
        "percentage": 18.9,
        "note": "Very common for options, variants",
        "priority": "critical"
      },
      "intersection_types": {
        "occurrences": 12456,
        "percentage": 6.1,
        "note": "Composition pattern",
        "priority": "high"
      },
      "discriminated_unions": {
        "occurrences": 8234,
        "percentage": 4.0,
        "note": "State machines, Redux actions",
        "priority": "high"
      }
    },

    "array_tuple": {
      "array_types": {
        "occurrences": 32145,
        "percentage": 15.7,
        "patterns": ["T[]", "Array<T>"],
        "priority": "critical"
      },
      "tuple_types": {
        "occurrences": 6234,
        "percentage": 3.0,
        "note": "Fixed-length arrays",
        "priority": "high"
      },
      "readonly_array": {
        "occurrences": 4521,
        "percentage": 2.2,
        "note": "Immutability pattern",
        "priority": "medium"
      },
      "tuple_with_rest": {
        "occurrences": 1234,
        "percentage": 0.6,
        "note": "Variable args with types",
        "priority": "low"
      },
      "readonly_tuple": {
        "occurrences": 892,
        "percentage": 0.4,
        "priority": "low"
      }
    },

    "advanced_types": {
      "conditional_types": {
        "occurrences": 8934,
        "percentage": 4.4,
        "note": "Heavy in utility libraries",
        "contexts": ["@types packages", "library internals"],
        "priority": "high"
      },
      "mapped_types": {
        "occurrences": 5421,
        "percentage": 2.6,
        "note": "Transformations (Partial, Pick, etc.)",
        "priority": "high"
      },
      "template_literal_types": {
        "occurrences": 2134,
        "percentage": 1.0,
        "note": "TS 4.1+, string manipulation",
        "priority": "medium"
      },
      "indexed_access": {
        "occurrences": 6789,
        "percentage": 3.3,
        "pattern": "T[K]",
        "priority": "high"
      },
      "infer_keyword": {
        "occurrences": 3421,
        "percentage": 1.7,
        "note": "Advanced utility types",
        "priority": "medium"
      }
    },

    "type_operators": {
      "typeof_operator": {
        "occurrences": 9234,
        "percentage": 4.5,
        "contexts": ["const to type", "import types"],
        "priority": "high"
      },
      "keyof_operator": {
        "occurrences": 7123,
        "percentage": 3.5,
        "contexts": ["mapped types", "constraints"],
        "priority": "high"
      },
      "readonly_modifier": {
        "occurrences": 8234,
        "percentage": 4.0,
        "note": "Immutability",
        "priority": "high"
      },
      "unique_symbol": {
        "occurrences": 234,
        "percentage": 0.1,
        "note": "Rare, nominal typing",
        "priority": "low"
      }
    },

    "type_assertions": {
      "as_assertion": {
        "occurrences": 15234,
        "percentage": 7.4,
        "note": "Type narrowing",
        "priority": "critical"
      },
      "satisfies_operator": {
        "occurrences": 1892,
        "percentage": 0.9,
        "note": "TS 4.9+, growing",
        "priority": "medium"
      },
      "non_null_assertion": {
        "occurrences": 12456,
        "percentage": 6.1,
        "note": "x! to assert non-null",
        "priority": "high"
      },
      "const_assertion": {
        "occurrences": 4521,
        "percentage": 2.2,
        "note": "as const for literals",
        "priority": "high"
      }
    },

    "modern_features": {
      "using_declarations": {
        "occurrences": 0,
        "percentage": 0.0,
        "note": "TS 5.2, too new",
        "priority": "low"
      },
      "const_type_parameters": {
        "occurrences": 423,
        "percentage": 0.2,
        "note": "TS 5.0, niche",
        "priority": "low"
      },
      "decorator_metadata": {
        "occurrences": 156,
        "percentage": 0.08,
        "note": "TS 5.2, experimental",
        "priority": "low"
      }
    },

    "jsdoc_types": {
      "jsdoc_annotations": {
        "occurrences": 3421,
        "percentage": 1.7,
        "note": "JS files with type checking",
        "contexts": ["legacy code", "gradual typing"],
        "priority": "low"
      }
    }
  },

  "priority_ranking": [
    {"feature": "string_annotation", "score": 100, "reason": "Most common, essential"},
    {"feature": "generic_types", "score": 98, "reason": "Universal in libraries"},
    {"feature": "union_types", "score": 95, "reason": "Very common pattern"},
    {"feature": "type_alias", "score": 92, "reason": "Core abstraction"},
    {"feature": "interface", "score": 90, "reason": "Object contracts"},
    {"feature": "array_types", "score": 88, "reason": "Collections everywhere"},
    {"feature": "number_annotation", "score": 85, "reason": "Second most common primitive"},
    {"feature": "as_assertion", "score": 82, "reason": "Type narrowing essential"},
    {"feature": "typeof_operator", "score": 75, "reason": "Value to type bridge"},
    {"feature": "conditional_types", "score": 70, "reason": "Library internals"},
    {"feature": "mapped_types", "score": 68, "reason": "Utility types"},
    {"feature": "keyof_operator", "score": 65, "reason": "Key extraction"},
    {"feature": "intersection_types", "score": 62, "reason": "Composition"},
    {"feature": "readonly_modifier", "score": 60, "reason": "Immutability"},
    {"feature": "tuple_types", "score": 55, "reason": "Fixed arrays"},
    {"feature": "indexed_access", "score": 52, "reason": "Type indexing"},
    {"feature": "const_assertion", "score": 50, "reason": "Literal inference"},
    {"feature": "enum", "score": 45, "reason": "Declining but still used"},
    {"feature": "template_literal_types", "score": 40, "reason": "TS 4.1+"},
    {"feature": "infer_keyword", "score": 38, "reason": "Advanced utility"},
    {"feature": "satisfies_operator", "score": 30, "reason": "TS 4.9+, growing"},
    {"feature": "const_enum", "score": 25, "reason": "Performance niche"},
    {"feature": "namespace", "score": 20, "reason": "Legacy"},
    {"feature": "unique_symbol", "score": 10, "reason": "Rare"},
    {"feature": "using_declarations", "score": 5, "reason": "Too new"}
  ]
}
```

### Step 3: Identify Common Patterns

Look for recurring idioms:

**popular-patterns.md**:

```markdown
# Popular TypeScript Patterns in Real-World Code

## Pattern Analysis from 13,945 Files

### Pattern 1: Utility Type Composition
**Frequency**: Very High (38% of type aliases)
**Example**:
```typescript
type PartialUser = Partial<User>;
type ReadonlyUser = Readonly<User>;
type PickUserName = Pick<User, 'name' | 'email'>;
type OmitPassword = Omit<User, 'password'>;
```
**Implication**: Must support mapped types for Partial, Readonly, Pick, Omit

---

### Pattern 2: Discriminated Unions for State
**Frequency**: High (8,234 occurrences)
**Example**:
```typescript
type RequestState =
  | { status: 'idle' }
  | { status: 'loading' }
  | { status: 'success'; data: Data }
  | { status: 'error'; error: Error };
```
**Implication**: Union types + literal types critical

---

### Pattern 3: Generic Constraints
**Frequency**: High (15,234 occurrences)
**Example**:
```typescript
function pick<T, K extends keyof T>(obj: T, keys: K[]): Pick<T, K>

interface Repository<T extends Model> {
  find(id: string): Promise<T>;
}
```
**Implication**: Generic constraints (T extends U) essential

---

### Pattern 4: Conditional Types for Overloads
**Frequency**: Medium (3,421 occurrences)
**Example**:
```typescript
type ElementType<T> = T extends (infer U)[] ? U : T;
type Awaited<T> = T extends Promise<infer U> ? U : T;
```
**Implication**: Conditional types + infer needed for libraries

---

### Pattern 5: Const Assertions for Config
**Frequency**: Medium (4,521 occurrences)
**Example**:
```typescript
const config = {
  apiUrl: "https://api.example.com",
  timeout: 5000,
  retries: 3,
} as const;

type Config = typeof config;
// Config = { readonly apiUrl: "https://..."; readonly timeout: 5000; ... }
```
**Implication**: as const + typeof combination important

---

### Pattern 6: Index Signatures for Dynamic Objects
**Frequency**: High (9,234 occurrences)
**Example**:
```typescript
interface Dictionary<T> {
  [key: string]: T;
}

interface LocaleMessages {
  [locale: string]: {
    [key: string]: string;
  };
}
```
**Implication**: Index signatures essential

---

### Pattern 7: Function Overloads
**Frequency**: Medium (5,621 occurrences)
**Example**:
```typescript
function createElement(tag: 'div'): HTMLDivElement;
function createElement(tag: 'span'): HTMLSpanElement;
function createElement(tag: string): HTMLElement;
function createElement(tag: string) {
  return document.createElement(tag);
}
```
**Implication**: Multiple function signatures needed

---

### Pattern 8: Mapped Types with Modifiers
**Frequency**: Medium (5,421 occurrences)
**Example**:
```typescript
type Partial<T> = { [K in keyof T]?: T[K] };
type Required<T> = { [K in keyof T]-?: T[K] };
type Readonly<T> = { readonly [K in keyof T]: T[K] };
type Mutable<T> = { -readonly [K in keyof T]: T[K] };
```
**Implication**: +? -? readonly modifiers in mapped types

---

### Pattern 9: Template Literal Types (Modern)
**Frequency**: Low-Medium (2,134 occurrences)
**Example**:
```typescript
type EventName<T extends string> = `on${Capitalize<T>}`;
type Direction = 'left' | 'right' | 'up' | 'down';
type MoveDirection = `move${Capitalize<Direction>}`;
// "moveLeft" | "moveRight" | "moveUp" | "moveDown"
```
**Implication**: TS 4.1+ feature, growing in usage

---

### Pattern 10: Recursive Types
**Frequency**: Low (1,234 occurrences)
**Example**:
```typescript
type JSONValue =
  | string
  | number
  | boolean
  | null
  | JSONValue[]
  | { [key: string]: JSONValue };

type DeepPartial<T> = {
  [K in keyof T]?: T[K] extends object ? DeepPartial<T[K]> : T[K];
};
```
**Implication**: Type recursion needed

---

## Patterns by Use Case

### Library Development (High Type Complexity)
- Conditional types (40% of type expressions)
- Infer keyword (15% of conditionals)
- Mapped types (25% of type aliases)
- Template literal types (growing)

### Application Development (Simpler Types)
- Interfaces for shapes (60% of declarations)
- Union types for variants (30% of types)
- Basic generics (Array<T>, Promise<T>)
- Utility types (Partial, Omit, Pick)

### Declaration Files (.d.ts)
- Namespace declarations (legacy APIs)
- Ambient declarations (declare global)
- Module augmentation (extending types)
- Complex overloads

## Declining Patterns

### Namespaces
**Usage**: Declining (3,421 → mostly legacy code)
**Replaced by**: ES modules
**Note**: Still needed for declaration file compatibility

### Const Enums
**Usage**: Low (1,203 occurrences)
**Replaced by**: Union of literals
**Note**: Performance benefit sometimes worth it

### Any Type
**Usage**: High but declining (12,456 → 10,234 year-over-year)
**Replaced by**: unknown, proper typing
**Note**: Still escape hatch for migrations

## Growing Patterns

### Satisfies Operator (TS 4.9+)
**Current**: 1,892 occurrences
**Growth**: +300% since release
**Trend**: Replacing some `as` assertions

### Template Literal Types (TS 4.1+)
**Current**: 2,134 occurrences
**Growth**: Steady increase
**Trend**: String-based APIs, CSS-in-JS

### Const Type Parameters (TS 5.0+)
**Current**: 423 occurrences
**Growth**: Early adoption
**Trend**: Tuple inference improvements

## Implications for Implementation Priority

### Tier 1 (Must Have - >10% usage)
1. Primitives (string, number, boolean)
2. Generics (T, constraints, defaults)
3. Unions/Intersections
4. Type aliases & Interfaces
5. Arrays

### Tier 2 (Important - 2-10% usage)
6. Conditional types
7. Mapped types
8. Type operators (typeof, keyof, readonly)
9. Index signatures
10. Tuple types

### Tier 3 (Nice to Have - <2% usage)
11. Template literal types
12. Infer keyword
13. Const assertions
14. Satisfies operator
15. Enums

### Tier 4 (Low Priority - <0.5% usage)
16. Namespaces
17. Const enums
18. Unique symbol
19. Using declarations
20. Decorator metadata
```

### Step 4: Extract Representative Snippets

Save interesting code samples for testing:

```bash
mkdir -p workspace/outputs/01-analysis/05-research-feature-usage/sample-snippets

# Extract examples of each major pattern
# Example: Find complex conditional types
grep -r "extends.*\?.*:.*" /tmp/typescript-samples --include="*.ts" -A 2 | \
    head -50 > sample-snippets/conditional-types.txt

# Find mapped types
grep -r "in keyof" /tmp/typescript-samples --include="*.ts" -A 2 | \
    head -50 > sample-snippets/mapped-types.txt

# Continue for each pattern...
```

### Step 5: Create Usage Report

**real-world-usage-report.md**:

```markdown
# Real-World TypeScript Usage Report

**Analysis Date**: 2025-11-20
**Repositories**: 5 major projects
**Files Analyzed**: 13,945 TypeScript files
**Lines of Code**: 2,049,511

## Executive Summary

### Key Findings

1. **70% of type expressions use basic features**
   - Primitives, generics, unions, interfaces
   - These must be perfect

2. **20% use advanced features**
   - Conditional types, mapped types, type operators
   - Critical for library code

3. **10% use modern features**
   - Template literals, satisfies, const parameters
   - Nice to have, not blocking

### Recommendation: Focus on Core 90%

Implementing the top 20 features covers 90% of real-world usage.
The long tail (40+ features) covers only 10%.

## Feature Prioritization Matrix

| Priority | Features | Usage % | Implementation Effort | ROI |
|----------|----------|---------|----------------------|-----|
| **P0** | Primitives, Generics, Unions, Interfaces | 60% | Low | ⭐⭐⭐⭐⭐ |
| **P1** | Arrays, Type aliases, Typeof, Keyof | 20% | Low-Medium | ⭐⭐⭐⭐ |
| **P2** | Conditional, Mapped, Indexed access | 10% | Medium | ⭐⭐⭐ |
| **P3** | Template literals, Infer, Const assertions | 5% | Medium-High | ⭐⭐ |
| **P4** | Enums, Namespaces, Unique symbol | 3% | Low | ⭐ |
| **P5** | Using, Decorator metadata, JSDoc | 2% | High | ⭐ |

## Usage by Repository Type

### Libraries (@types, React, Vue)
- **Complex types**: 40% of code
- **Advanced features**: Heavily used
- **Need**: Conditional types, mapped types, infer

### Applications (Next.js, typical apps)
- **Simple types**: 80% of code
- **Basic features**: Mostly used
- **Need**: Interfaces, unions, generics

### Declaration Files (.d.ts)
- **Legacy patterns**: Namespaces, ambient
- **Overloads**: Many function signatures
- **Need**: Compatibility with old TypeScript

## Comparative Analysis: TypeScript vs ecma-rs

### Well-Covered Features ✅
- Primitives (100% coverage expected)
- Basic generics
- Unions/Intersections
- Interfaces
- Type aliases

### Potentially Missing Features ⚠️
Based on frequency analysis, check these:
1. **Readonly tuple with rest** (892 occurrences)
2. **Typeof import** (1,234 occurrences)
3. **Const type parameters** (423 occurrences)
4. **Mapped type 'as' clause** (789 occurrences)

### Definitely Rare Features ✅ (OK to defer)
- Using declarations (0 occurrences - too new)
- Decorator metadata (156 occurrences)
- Unique symbol (234 occurrences)

## Recommendations

### For Planning Phase

1. **Prioritize by ROI**:
   - Start with P0/P1 features (80% coverage, low effort)
   - Add P2 features (90% coverage, medium effort)
   - Defer P3/P4/P5 unless conformance tests fail

2. **Test with Real Code**:
   - Use React types for validation
   - Test against DefinitelyTyped samples
   - Ensure popular patterns work

3. **Focus on Minification Use Case**:
   - Type stripping must be perfect for all P0/P1 features
   - Type-aware optimization can focus on common patterns:
     - Const assertions → inlining
     - Const enums → inlining
     - Never-returning functions → DCE

### For Implementation

**High ROI Quick Wins**:
1. Ensure readonly tuple + rest works (low effort, medium impact)
2. Add typeof import support (medium effort, medium impact)
3. Verify const assertions work (probably done, high impact)

**Medium ROI Important Features**:
1. Conditional types (likely done, verify completeness)
2. Mapped types (check for 'as' clause support)
3. Template literal types (TS 4.1+, growing usage)

**Low ROI Defer**:
1. Using declarations (too new, 0 usage)
2. Decorator metadata (experimental)
3. JSDoc types (only for JS files)

## Appendix: Search Queries Used

### GitHub Code Search

```
# Conditional types
"extends ? " language:TypeScript

# Mapped types
"[K in keyof" language:TypeScript

# Template literals (approximate)
"\${" language:TypeScript filename:*.d.ts

# Satisfies operator
"satisfies" language:TypeScript created:>2023-01-01

# Using declarations
"using " language:TypeScript created:>2024-01-01
```

### Local Grep Patterns

```bash
# Count type aliases
grep -r "^type \w\+ = " --include="*.ts" | wc -l

# Count interfaces
grep -r "^interface \w\+ " --include="*.ts" | wc -l

# Count conditional types
grep -r "extends.*\?" --include="*.ts" | wc -l
```

## Appendix: Sample Repositories

1. **TypeScript** (microsoft/TypeScript)
   - Self-hosted compiler
   - Extensive use of conditional types
   - Advanced type system features

2. **DefinitelyTyped**
   - 8,000+ type definition packages
   - Every TypeScript feature represented
   - Best dataset for feature frequency

3. **React**
   - Moderate type complexity
   - Generics, unions common
   - Application-level patterns

4. **Vue**
   - Heavy use of mapped types
   - Template literal types for props
   - Modern TypeScript patterns

5. **Next.js**
   - Application framework
   - Mix of simple and complex types
   - Real-world usage patterns
```

## Acceptance Criteria

### Required Outputs

✅ **feature-frequency-analysis.json**: Quantitative frequency data

✅ **real-world-usage-report.md**: Analysis with recommendations

✅ **popular-patterns.md**: Common TypeScript patterns

✅ **sample-snippets/**: Representative code examples

### Quality Checks

- [ ] At least 5 repositories analyzed
- [ ] 10,000+ TypeScript files sampled
- [ ] All major feature categories counted
- [ ] Priority ranking based on data, not opinion
- [ ] Patterns include real code examples
- [ ] JSON validates

### Success Metrics

- Data-driven feature prioritization
- Clear ROI for each feature
- Representative code samples collected
- Recommendations actionable

## Common Issues & Solutions

### Issue: Counting false positives

**Example**: `typeof x === "string"` vs `typeof import(...)`

**Solution**:
- Refine regex patterns
- Manual sampling to verify
- Accept some noise in statistics

### Issue: Repository too large

**Solution**:
- Use `--depth 1` for shallow clone
- Sample subset of files: `find . -name "*.ts" | shuf | head -1000`
- Focus on .d.ts files for feature detection

### Issue: Can't access certain repos

**Solution**:
- Use sourcegraph.com for search without cloning
- GitHub code search (limited to 100 results)
- Use archived TypeScript test cases

## Time Estimate Breakdown

- Setup & cloning: 30 min
- Feature counting: 1.5 hours
- Pattern analysis: 1 hour
- Report writing: 1 hour
- Sample collection: 30 min

**Total: 3-4 hours**

## Downstream Impact

Critical input for:
- **02-planning/01-prioritize-features**: Data-driven priorities
- **03-implementation/***: Focus on high-ROI features first
- **Testing**: Use real-world patterns for validation

## Notes for Agent

- More data = better prioritization
- Don't need perfect counts, just relative frequencies
- Look for surprising patterns (features more/less common than expected)
- Modern repos (created >2023) show TypeScript evolution
- Your analysis impacts months of implementation work

---

**Ready?** Start with Step 1: Clone Sample Repositories
