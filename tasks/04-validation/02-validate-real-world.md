---
task_id: "04-validation/02-validate-real-world"
phase: "04-validation"
title: "Validate Against Real-World TypeScript Projects"
dependencies:
  - "04-validation/01-run-conformance"
inputs:
  - "workspace/outputs/04-validation/01-run-conformance/final-results.json"
outputs:
  - "workspace/outputs/04-validation/02-validate-real-world/project-results.json"
  - "workspace/outputs/04-validation/02-validate-real-world/validation-report.md"
  - "workspace/outputs/04-validation/02-validate-real-world/real-world-issues.md"
estimated_duration: "4-6 hours"
complexity: "medium"
priority: "high"
---

# Task: Validate Against Real-World TypeScript Projects

## Objective

Test the enhanced parser against real-world TypeScript projects to ensure it handles production code correctly, identify edge cases not covered by conformance tests, and validate practical usability.

## Context

While conformance tests validate spec compliance, real-world projects often:
- Use bleeding-edge TypeScript features
- Combine features in unexpected ways
- Include large, complex type definitions
- Stress-test performance at scale

This validation ensures ecma-rs works on **actual production codebases**, not just test cases.

### Selected Projects (diverse ecosystem coverage)

1. **TypeScript itself** (~1.2M lines)
   - Repo: microsoft/TypeScript
   - Why: Most complex TS project, self-hosting compiler

2. **VS Code** (~500K lines TS)
   - Repo: microsoft/vscode
   - Why: Large enterprise application

3. **React** (type definitions)
   - Repo: DefinitelyTyped/DefinitelyTyped
   - Path: types/react
   - Why: Heavily used type definitions

4. **Vue 3** (~100K lines TS)
   - Repo: vuejs/core
   - Why: Modern framework with advanced types

5. **TypeORM** (~50K lines TS)
   - Repo: typeorm/typeorm
   - Why: Heavy use of decorators and metadata

6. **Apollo Client** (~80K lines TS)
   - Repo: apollographql/apollo-client
   - Why: Complex generic types

7. **RxJS** (~40K lines TS)
   - Repo: ReactiveX/rxjs
   - Why: Extensive use of operators and higher-kinded types

## Instructions

### Step 1: Clone Test Projects

```bash
mkdir -p workspace/real-world-projects
cd workspace/real-world-projects

# Clone selected projects (use shallow clones for speed)
git clone --depth=1 https://github.com/microsoft/TypeScript.git
git clone --depth=1 https://github.com/microsoft/vscode.git
git clone --depth=1 https://github.com/DefinitelyTyped/DefinitelyTyped.git
git clone --depth=1 https://github.com/vuejs/core.git vue3
git clone --depth=1 https://github.com/typeorm/typeorm.git
git clone --depth=1 https://github.com/apollographql/apollo-client.git
git clone --depth=1 https://github.com/ReactiveX/rxjs.git

cd ../..
```

### Step 2: Create Test Harness

**File**: `scripts/validate-real-world.sh`

```bash
#!/bin/bash

set -e

PROJECTS_DIR="workspace/real-world-projects"
OUTPUT_DIR="workspace/outputs/04-validation/02-validate-real-world"
mkdir -p "$OUTPUT_DIR"

# Function to test a project
test_project() {
    local project_name=$1
    local project_path=$2
    local pattern=${3:-"**/*.ts"}

    echo "Testing $project_name..."

    local start_time=$(date +%s)
    local total=0
    local success=0
    local failed=0
    local errors_file="$OUTPUT_DIR/${project_name}-errors.txt"

    > "$errors_file"  # Clear errors file

    # Find all TypeScript files
    find "$project_path" -name "*.ts" -o -name "*.tsx" | while read file; do
        ((total++))

        # Try to parse the file
        if cargo run --release --bin parse-file -- "$file" > /dev/null 2>> "$errors_file"; then
            ((success++))
        else
            ((failed++))
            echo "FAILED: $file" >> "$errors_file"
        fi

        # Progress indicator
        if [ $((total % 100)) -eq 0 ]; then
            echo -ne "\r  Processed: $total files"
        fi
    done

    local end_time=$(date +%s)
    local duration=$((end_time - start_time))

    echo ""
    echo "  Total files: $total"
    echo "  Successful: $success"
    echo "  Failed: $failed"
    echo "  Success rate: $(echo "scale=2; $success * 100 / $total" | bc)%"
    echo "  Duration: ${duration}s"

    # Return results as JSON
    cat <<EOF
{
  "project": "$project_name",
  "total_files": $total,
  "success": $success,
  "failed": $failed,
  "success_rate": $(echo "scale=4; $success / $total" | bc),
  "duration_seconds": $duration,
  "errors_file": "${project_name}-errors.txt"
}
EOF
}

# Test all projects
echo "=== Real-World Project Validation ==="
echo ""

# TypeScript
test_project "typescript" "$PROJECTS_DIR/TypeScript/src" > "$OUTPUT_DIR/typescript.json"

# VS Code
test_project "vscode" "$PROJECTS_DIR/vscode/src" > "$OUTPUT_DIR/vscode.json"

# React types
test_project "react-types" "$PROJECTS_DIR/DefinitelyTyped/types/react" > "$OUTPUT_DIR/react-types.json"

# Vue 3
test_project "vue3" "$PROJECTS_DIR/vue3/packages" > "$OUTPUT_DIR/vue3.json"

# TypeORM
test_project "typeorm" "$PROJECTS_DIR/typeorm/src" > "$OUTPUT_DIR/typeorm.json"

# Apollo Client
test_project "apollo-client" "$PROJECTS_DIR/apollo-client/src" > "$OUTPUT_DIR/apollo-client.json"

# RxJS
test_project "rxjs" "$PROJECTS_DIR/rxjs/src" > "$OUTPUT_DIR/rxjs.json"

echo ""
echo "=== Validation Complete ==="
```

### Step 3: Create Parse Binary (if not exists)

**File**: `parse-js/src/bin/parse-file.rs`

```rust
use parse_js::parse;
use std::env;
use std::fs;
use std::process;

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        eprintln!("Usage: parse-file <file.ts>");
        process::exit(1);
    }

    let file_path = &args[1];

    let source = match fs::read_to_string(file_path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("Error reading file: {}", e);
            process::exit(1);
        }
    };

    match parse(&source) {
        Ok(_ast) => {
            // Success - could optionally print AST
            process::exit(0);
        }
        Err(e) => {
            eprintln!("Parse error in {}: {:?}", file_path, e);
            process::exit(1);
        }
    }
}
```

Add to `Cargo.toml`:
```toml
[[bin]]
name = "parse-file"
path = "src/bin/parse-file.rs"
```

### Step 4: Run Validation

```bash
chmod +x scripts/validate-real-world.sh
./scripts/validate-real-world.sh
```

### Step 5: Aggregate Results

**File**: `scripts/aggregate-results.js`

```javascript
const fs = require('fs');
const path = require('path');

const resultsDir = 'workspace/outputs/04-validation/02-validate-real-world';
const projectFiles = [
    'typescript.json',
    'vscode.json',
    'react-types.json',
    'vue3.json',
    'typeorm.json',
    'apollo-client.json',
    'rxjs.json'
];

let results = projectFiles.map(file => {
    const data = fs.readFileSync(path.join(resultsDir, file), 'utf8');
    return JSON.parse(data);
});

const summary = {
    timestamp: new Date().toISOString(),
    projects_tested: results.length,
    total_files: results.reduce((sum, r) => sum + r.total_files, 0),
    total_success: results.reduce((sum, r) => sum + r.success, 0),
    total_failed: results.reduce((sum, r) => sum + r.failed, 0),
    overall_success_rate: 0,
    project_results: results
};

summary.overall_success_rate = summary.total_success / summary.total_files;

fs.writeFileSync(
    path.join(resultsDir, 'project-results.json'),
    JSON.stringify(summary, null, 2)
);

console.log('=== Real-World Validation Summary ===');
console.log(`Projects tested: ${summary.projects_tested}`);
console.log(`Total files: ${summary.total_files}`);
console.log(`Success: ${summary.total_success}`);
console.log(`Failed: ${summary.total_failed}`);
console.log(`Success rate: ${(summary.overall_success_rate * 100).toFixed(2)}%`);
```

```bash
node scripts/aggregate-results.js
```

### Step 6: Analyze Failures

**File**: `scripts/analyze-failures.sh`

```bash
#!/bin/bash

OUTPUT_DIR="workspace/outputs/04-validation/02-validate-real-world"

echo "=== Analyzing Failure Patterns ==="

# Combine all error files
cat "$OUTPUT_DIR"/*-errors.txt > "$OUTPUT_DIR/all-errors.txt"

# Extract error types
grep -o "Error: [^,]*" "$OUTPUT_DIR/all-errors.txt" | sort | uniq -c | sort -rn > "$OUTPUT_DIR/error-types.txt"

# Extract file patterns that fail
grep "FAILED:" "$OUTPUT_DIR/all-errors.txt" | sed 's/.*FAILED: //' | \
    while read file; do dirname "$file"; done | sort | uniq -c | sort -rn | head -20 > "$OUTPUT_DIR/failure-hotspots.txt"

echo "Top error types:"
head -10 "$OUTPUT_DIR/error-types.txt"

echo ""
echo "Failure hotspots:"
head -10 "$OUTPUT_DIR/failure-hotspots.txt"
```

### Step 7: Create Validation Report

**File**: `workspace/outputs/04-validation/02-validate-real-world/validation-report.md`

```markdown
# Real-World TypeScript Project Validation Report

## Executive Summary

Tested ecma-rs parser against **7 major TypeScript projects** representing diverse use cases.

- **Total files parsed**: X
- **Overall success rate**: Y%
- **Projects with >95% success**: Z/7
- **Critical issues found**: N

## Project Results

| Project | Files | Success | Failed | Rate | Issues |
|---------|-------|---------|--------|------|--------|
| TypeScript | A | B | C | D% | [link](#typescript) |
| VS Code | E | F | G | H% | [link](#vscode) |
| React Types | I | J | K | L% | [link](#react) |
| Vue 3 | M | N | O | P% | [link](#vue3) |
| TypeORM | Q | R | S | T% | [link](#typeorm) |
| Apollo Client | U | V | W | X% | [link](#apollo) |
| RxJS | Y | Z | AA | AB% | [link](#rxjs) |
| **Total** | **TOT** | **SUC** | **FAI** | **RAT%** | - |

## Detailed Analysis

### TypeScript (microsoft/TypeScript)

**Stats**:
- Files: X
- Success rate: Y%

**Key findings**:
- [Finding 1]
- [Finding 2]

**Sample failures**:
```
src/compiler/checker.ts:1234 - Error: ...
src/compiler/parser.ts:5678 - Error: ...
```

**Analysis**: [Why these fail]

---

### VS Code (microsoft/vscode)

[Similar structure for each project]

---

## Failure Pattern Analysis

### Top 5 Error Types

1. **[Error Type 1]** (XXX occurrences)
   - **Pattern**: [Describe]
   - **Examples**: [List files]
   - **Root cause**: [Analysis]
   - **Fix priority**: High/Medium/Low

2. **[Error Type 2]** (YYY occurrences)
   ...

### Failure Hotspots

Directories with highest failure rates:

1. `TypeScript/src/compiler/` - 45 failures
2. `vscode/src/vs/editor/` - 32 failures
3. ...

**Common characteristics**: [What these areas have in common]

## Edge Cases Discovered

### 1. [Edge Case Name]
**Discovered in**: [Project/file]

**Example**:
```typescript
[Code snippet that fails]
```

**Why it fails**: [Explanation]

**Conformance tests coverage**: ❌ Not covered / ✅ Covered

**Recommended action**: [Fix/document/defer]

---

### 2. [Next Edge Case]
...

## Performance Observations

### Parsing Speed
- **Average**: X ms/file
- **Slowest file**: path/to/file.ts (Y ms)
- **Total time**: Z minutes for all projects

### Memory Usage
- **Peak memory**: X GB
- **Average per file**: Y MB

## Comparison with Baseline

| Metric | Before Phase 3 | After Phase 3 | Improvement |
|--------|----------------|---------------|-------------|
| Success rate | A% | B% | +C% |
| Avg parse time | Dms | Ems | Fms |

## Real-World vs Conformance Tests

| Aspect | Conformance | Real-World |
|--------|-------------|------------|
| Pass rate | 95% | Y% |
| Coverage | Spec features | Production patterns |
| Edge cases | Known | Unknown |

**Insight**: [Are real-world results better/worse than conformance? Why?]

## Critical Issues

### Blocking Issues (Must Fix)
- [ ] Issue 1: [Description] - affects X% of files
- [ ] Issue 2: [Description] - affects Y% of files

### High Priority (Should Fix)
- [ ] Issue 3: [Description]
- [ ] Issue 4: [Description]

### Low Priority (Nice to Have)
- [ ] Issue 5: [Description]
- [ ] Issue 6: [Description]

## Recommendations

### Immediate Actions
1. Fix [critical issue] - would improve success rate by X%
2. Investigate [pattern] - appears in multiple projects

### Future Work
1. Add conformance tests for discovered edge cases
2. Performance optimization for [specific pattern]
3. Better error messages for [common failure]

## Conclusion

**Overall assessment**: [Success/Partial Success/Needs Work]

**Readiness for production**:
- ✅ / ❌ Can parse TypeScript compiler itself
- ✅ / ❌ Can parse large applications (VS Code)
- ✅ / ❌ Can parse complex type definitions
- ✅ / ❌ Performance is acceptable

**Next steps**: [Proceed to optimization / Fix critical issues / etc.]
```

### Step 8: Document Real-World Issues

**File**: `workspace/outputs/04-validation/02-validate-real-world/real-world-issues.md`

```markdown
# Real-World Issues Discovered

## Issue Template

For each issue discovered:

### Issue #1: [Short Description]

**Severity**: Critical / High / Medium / Low

**Affected projects**: [List]

**Frequency**: Appears in X files across Y projects

**Example**:
```typescript
// Failing code
[Minimal reproducible example]
```

**Error message**:
```
[Exact error from parser]
```

**Root cause**:
[Analysis of why this fails]

**Conformance test coverage**:
- ✅ Covered by conformance tests (unexpected failure)
- ❌ Not covered (gap in test suite)

**Workaround**:
[If any]

**Recommended fix**:
[Detailed fix plan]

**Estimated effort**:
[Hours/days]

---

[Repeat for each issue]
```

## Verification Commands

```bash
# Check all results generated
ls -lh workspace/outputs/04-validation/02-validate-real-world/

# View summary
jq '.' workspace/outputs/04-validation/02-validate-real-world/project-results.json

# Quick stats
jq '{projects: .projects_tested, files: .total_files, rate: .overall_success_rate}' \
    workspace/outputs/04-validation/02-validate-real-world/project-results.json
```

## Common Issues

### Issue 1: Network Failures Cloning Repos
**Solution**: Use cached clones or alternative mirrors

### Issue 2: Some Projects Don't Compile
**Solution**: We're only parsing, not compiling - that's fine

### Issue 3: Too Slow to Parse Large Projects
**Solution**: Use parallelization or sample subset of files

## Acceptance Criteria

- [ ] All 7 projects cloned successfully
- [ ] All projects tested completely
- [ ] Results JSON generated
- [ ] Validation report created
- [ ] Failure patterns analyzed
- [ ] Real-world issues documented
- [ ] Overall success rate >90%
- [ ] Critical issues (if any) identified and documented

## Success Metrics

**Minimum**: 85% success rate across all projects
**Target**: 90% success rate
**Exceptional**: 95% success rate

## Resources

- Project repositories: GitHub
- Parse binary: `parse-js/src/bin/parse-file.rs`

## Notes

Real-world validation often uncovers issues that conformance tests miss because:
- Production code uses newer TypeScript versions
- Developers combine features creatively
- Scale reveals performance issues
- Build configurations vary

Be thorough in documenting issues for future improvement.
