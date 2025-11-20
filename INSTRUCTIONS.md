# Agent Instructions: TypeScript Parsing Task Execution

## Welcome, Agent!

You've been assigned to work on a specific task in the **ecma-rs TypeScript type parsing implementation project**. This document tells you everything you need to know to execute your task successfully.

---

## 📋 Table of Contents

1. [Project Overview](#project-overview)
2. [Understanding Your Task](#understanding-your-task)
3. [The Task Execution Protocol](#the-task-execution-protocol)
4. [Quality Standards](#quality-standards)
5. [Common Patterns](#common-patterns)
6. [Troubleshooting](#troubleshooting)
7. [Success Checklist](#success-checklist)

---

## 🎯 Project Overview

### What We're Building

**ecma-rs** is a JavaScript/TypeScript parser and minifier written in Rust. We're adding comprehensive TypeScript type parsing support to enable:

1. **Type-preserving parsing** - Parse all TypeScript syntax correctly
2. **Type stripping** - Remove types for minification
3. **Type-aware optimization** - Use type information for better minification

### Current State

- ✅ **~85-90% TypeScript syntax already supported**
- ✅ **Complete type expression AST** (~427 lines)
- ✅ **Full type expression parser** (~1,743 lines)
- ✅ **21,065 TypeScript conformance tests** ready to run
- 🎯 **Goal: >95% conformance, production-ready parser**

### Your Role

You're working on **one specific task** in a larger parallel effort. Your task is:
- **Self-contained** - Everything you need is in your task file
- **Independent** - You don't need to coordinate with other agents
- **Well-defined** - Clear inputs, outputs, and success criteria

**Important**: Other agents may be working on other tasks simultaneously. You work in isolation.

---

## 📖 Understanding Your Task

### Task File Structure

Your task is defined in a Markdown file with this structure:

```markdown
---
task_id: "01-analysis/01-run-conformance-tests"
title: "Run TypeScript Conformance Tests"
phase: "analysis"
estimated_duration: "2-4 hours"
complexity: "low"
dependencies: []
inputs: []
outputs:
  - "test-results.json"
  - "test-summary.md"
skills_required:
  - "Rust development"
---

# Task: Title

## Objective
(What you're accomplishing)

## Context
(Why this matters)

## Instructions
(Step-by-step guide)

## Acceptance Criteria
(How to know you're done)
```

### Critical Sections

**READ THESE CAREFULLY**:

1. **Frontmatter (YAML)** - Task metadata
   - `dependencies`: What must complete before you start
   - `inputs`: Files you need to read from previous tasks
   - `outputs`: Files you must create

2. **Objective** - One-sentence goal

3. **Context** - Background and rationale

4. **Instructions** - Step-by-step process (FOLLOW EXACTLY)

5. **Acceptance Criteria** - How to verify success

6. **Common Issues & Solutions** - Debugging help

---

## 🚀 The Task Execution Protocol

### Step 1: Verify Prerequisites

#### Check Dependencies Are Met

```bash
# Your task frontmatter says:
# dependencies:
#   - "01-analysis/01-run-conformance-tests"

# Verify the dependency task is complete:
ls workspace/outputs/01-analysis/01-run-conformance-tests/

# Expected: All output files exist
```

**Rule**: Never start if dependencies aren't complete.

#### Check Input Files Exist

```bash
# Your task frontmatter says:
# inputs:
#   - "../../01-analysis/01-run-conformance-tests/test-results.json"

# Verify input exists:
cat workspace/outputs/01-analysis/01-run-conformance-tests/test-results.json

# Expected: Valid JSON file with data
```

**Rule**: If inputs missing, STOP and report issue.

### Step 2: Set Up Your Workspace

```bash
# Create your output directory
TASK_ID="01-analysis/01-run-conformance-tests"  # Your task ID
mkdir -p workspace/outputs/${TASK_ID}

# You'll write all outputs here
cd workspace/outputs/${TASK_ID}
```

**Rule**: All outputs go in `workspace/outputs/{your-task-id}/`

### Step 3: Read ALL Task Instructions

**Before doing anything**:

1. Read your task file **completely** from top to bottom
2. Read all input files specified in frontmatter
3. Review the "Common Issues & Solutions" section
4. Understand what outputs you need to create

**Do NOT skip ahead** - Task files are written to be read in order.

### Step 4: Execute Instructions Step-by-Step

**Follow the instructions EXACTLY**:

```markdown
### Step 1: Do X

```bash
command to run
```

Expected output: ...
```

**Your process**:
1. Read Step 1 completely
2. Understand what it asks
3. Execute the command/action
4. Verify expected output matches
5. Move to Step 2
6. Repeat

**Critical Rules**:
- ✅ DO follow instructions sequentially
- ✅ DO verify each step's output
- ✅ DO read code carefully before running
- ❌ DON'T skip steps
- ❌ DON'T assume you know better than instructions
- ❌ DON'T deviate from the plan without good reason

### Step 5: Create All Required Outputs

**From your frontmatter**:
```yaml
outputs:
  - "test-results.json"
  - "test-summary.md"
  - "failures.txt"
```

**Your responsibility**:
1. Create EVERY file listed
2. Match the format specified in instructions
3. Ensure files are complete and valid
4. Put them in `workspace/outputs/{task-id}/`

**Quality checks**:
```bash
# JSON files must be valid JSON
jq . test-results.json

# Markdown files should render
cat test-summary.md

# No empty files (unless explicitly expected)
[ -s test-results.json ] || echo "ERROR: Empty file!"
```

### Step 6: Verify Acceptance Criteria

**Every task has acceptance criteria**:

```markdown
## Acceptance Criteria

### Required Outputs
✅ test-results.json: Machine-readable summary
✅ test-summary.md: Human-readable report

### Quality Checks
- [ ] All numbers are accurate
- [ ] JSON is valid
- [ ] Files are non-empty
```

**Your job**: Check EVERY box before declaring done.

```bash
# Run verification commands from task file
jq . test-results.json  # Validates JSON

# Check file sizes
ls -lh workspace/outputs/${TASK_ID}/

# Review output quality
cat test-summary.md | less
```

### Step 7: Document Your Work

**If task includes notes/lessons sections**:

```markdown
# In your output file (e.g., implementation-notes.md):

## What Went Well
- X worked smoothly
- Y was easier than expected

## Challenges Encountered
- Z took longer because...
- Had to debug W issue

## Unexpected Discoveries
- Found that feature A actually exists
- Realized B is implemented differently than thought

## Time Breakdown
- Setup: 30 min
- Execution: 2 hours
- Documentation: 30 min
Total: 3 hours (estimated was 2-4 hours)
```

**Why this matters**: Helps future tasks and improves estimates.

---

## ✅ Quality Standards

### Output Quality

**All outputs must**:
- ✅ Be complete (no TODOs or placeholders)
- ✅ Be accurate (verified against source)
- ✅ Be well-formatted (valid JSON/Markdown/etc.)
- ✅ Include all required information
- ✅ Be usable by downstream tasks

**JSON Files**:
```bash
# Must validate
jq . output.json || echo "INVALID JSON"

# Must have expected structure
jq '.field_name' output.json  # Should not be null
```

**Markdown Files**:
```markdown
# Must have clear structure
# Heading 1: Title
## Heading 2: Sections
### Heading 3: Subsections

# Must be readable
# Use tables, lists, code blocks appropriately
```

**Code Files**:
```rust
// Must compile (if Rust code)
cargo check

// Must follow project style
cargo clippy

// Must have comments
// Explain non-obvious logic
```

### Accuracy Standards

**Numbers must be exact**:
```json
// DON'T estimate or round unless specified
{
  "total_tests": 21065,  // Exact count
  "passed": 18958,       // Exact count
  "failed": 2107         // Exact count
}
```

**Percentages must be calculated**:
```json
{
  "pass_rate": 90.00  // NOT "about 90%"
}
```

**Line numbers must be verified**:
```markdown
- TypeString defined at line 42  // Check the file!
```

### Completeness Standards

**If instructions say "list all"**:
- List ALL, not "some examples"
- Count and verify total

**If instructions say "analyze X"**:
- Actually analyze, don't just describe
- Provide specific findings

**If instructions say "create comprehensive Y"**:
- Cover all cases mentioned
- Don't skip sections

---

## 🔧 Common Patterns

### Pattern 1: Running Analysis and Saving Results

```bash
# Run command, capture output
cargo test --release --test conformance_runner 2>&1 | tee output.log

# Extract data from output
PASSED=$(grep "Passed:" output.log | awk '{print $2}')
FAILED=$(grep "Failed:" output.log | awk '{print $2}')

# Create structured output
cat > test-results.json << EOF
{
  "total": $((PASSED + FAILED)),
  "passed": ${PASSED},
  "failed": ${FAILED}
}
EOF

# Validate
jq . test-results.json
```

### Pattern 2: Reading Input from Previous Task

```bash
# Input file specified in frontmatter
INPUT_FILE="workspace/outputs/01-analysis/01-run-conformance-tests/test-results.json"

# Read and parse
PASS_RATE=$(jq '.pass_rate' ${INPUT_FILE})

# Use in your analysis
echo "Previous task found ${PASS_RATE}% pass rate"

# Include in your output
cat > analysis.md << EOF
# Analysis

Based on previous conformance test run (${PASS_RATE}% pass rate)...
EOF
```

### Pattern 3: Iterating Through Data

```bash
# Find all TypeScript files
find src/ast -name "*.rs" -type f | while read file; do
    # Extract struct names
    grep "pub struct Type" "$file" | while read line; do
        struct_name=$(echo "$line" | awk '{print $3}')
        echo "Found: $struct_name in $file"
    done
done > inventory.txt
```

### Pattern 4: Creating JSON Programmatically

```bash
# Build JSON incrementally
cat > data.json << 'EOF'
{
  "timestamp": "TIMESTAMP_PLACEHOLDER",
  "results": []
}
EOF

# Replace placeholder
TIMESTAMP=$(date -Iseconds)
sed -i "s/TIMESTAMP_PLACEHOLDER/${TIMESTAMP}/" data.json

# Or use jq to build properly
jq -n \
  --arg timestamp "$(date -Iseconds)" \
  --argjson passed 100 \
  --argjson failed 10 \
  '{
    timestamp: $timestamp,
    passed: $passed,
    failed: $failed,
    total: ($passed + $failed)
  }' > results.json
```

### Pattern 5: Handling Large Outputs

```bash
# If output is huge (>10MB), summarize
du -h large-file.txt  # Check size

# If too large, create summary
head -1000 large-file.txt > sample.txt
wc -l large-file.txt > stats.txt

# Note in your report
echo "Full output: $(wc -l < large-file.txt) lines" > summary.md
echo "Sample (first 1000 lines): see sample.txt" >> summary.md
```

---

## 🐛 Troubleshooting

### Issue: Input file missing

**Symptom**: Can't find input file specified in frontmatter

**Solution**:
1. Check if dependency task actually completed
2. Look in `workspace/outputs/{dependency-task-id}/`
3. Check spelling of filename
4. If truly missing, STOP and report issue

**Don't**: Guess or create fake input

### Issue: Command fails

**Symptom**: Instruction says run command, but it errors

**Solution**:
1. Read error message carefully
2. Check "Common Issues & Solutions" in task file
3. Verify you're in correct directory
4. Check prerequisites (dependencies installed?)
5. Try command manually to understand error
6. If blocker, document in output and note issue

**Don't**: Skip the step or ignore the error

### Issue: Don't understand instruction

**Symptom**: Instruction unclear or ambiguous

**Solution**:
1. Re-read Context section
2. Look for examples in task file
3. Check referenced files for clarity
4. Make best judgment and document assumption
5. If critical decision, note uncertainty in output

**Don't**: Guess silently

### Issue: Output format unclear

**Symptom**: Task says "create X" but format not specified

**Solution**:
1. Look for examples in instruction steps
2. Check similar tasks for patterns
3. Use common sense format (JSON for data, Markdown for reports)
4. Document format choice in output

**Don't**: Create unstructured output

### Issue: Taking longer than estimated

**Symptom**: Task estimated 2-4 hours, you're at 5 hours

**Solution**:
- This is OK! Estimates are estimates
- Document actual time in your notes
- If >2x estimate, note why (helps future estimates)
- Don't rush or cut corners

**Don't**: Skip steps to meet estimate

### Issue: Found something wrong in instructions

**Symptom**: Task instructions have error or outdated info

**Solution**:
1. Document the issue you found
2. Do what makes sense
3. Note correction in your output
4. Continue with best interpretation

**Don't**: Follow wrong instructions blindly

---

## 📋 Success Checklist

### Before You Start
- [ ] Read entire task file
- [ ] Verified all dependencies complete
- [ ] Confirmed all input files exist
- [ ] Understood objective and outputs
- [ ] Created output directory

### During Execution
- [ ] Following instructions sequentially
- [ ] Verifying each step before proceeding
- [ ] Taking notes of issues/discoveries
- [ ] Creating outputs as you go
- [ ] Checking output quality continuously

### Before Declaring Done
- [ ] All required outputs created
- [ ] All outputs in correct directory
- [ ] All acceptance criteria checked
- [ ] JSON files validated with `jq`
- [ ] Markdown files reviewed for completeness
- [ ] Numbers verified accurate
- [ ] No placeholders or TODOs left
- [ ] Ran verification commands from task
- [ ] Documented time spent
- [ ] Noted lessons learned (if applicable)

### Final Verification

```bash
#!/bin/bash
# Run this before declaring task complete

TASK_ID="your-task-id"  # e.g., "01-analysis/01-run-conformance-tests"
OUTPUT_DIR="workspace/outputs/${TASK_ID}"

echo "=== Verifying Task: ${TASK_ID} ==="

# Check output directory exists
if [ ! -d "${OUTPUT_DIR}" ]; then
    echo "❌ Output directory missing: ${OUTPUT_DIR}"
    exit 1
fi

echo "✅ Output directory exists"

# Check all required outputs (get from frontmatter)
REQUIRED_OUTPUTS=(
    "test-results.json"
    "test-summary.md"
    # Add your required outputs here
)

for output in "${REQUIRED_OUTPUTS[@]}"; do
    if [ ! -f "${OUTPUT_DIR}/${output}" ]; then
        echo "❌ Missing output: ${output}"
        exit 1
    fi

    # Check not empty
    if [ ! -s "${OUTPUT_DIR}/${output}" ]; then
        echo "❌ Empty output: ${output}"
        exit 1
    fi

    echo "✅ Output exists and non-empty: ${output}"
done

# Validate JSON files
for json_file in ${OUTPUT_DIR}/*.json; do
    if [ -f "$json_file" ]; then
        if jq . "$json_file" > /dev/null 2>&1; then
            echo "✅ Valid JSON: $(basename $json_file)"
        else
            echo "❌ Invalid JSON: $(basename $json_file)"
            exit 1
        fi
    fi
done

echo ""
echo "🎉 All checks passed!"
echo "Task ${TASK_ID} is complete."
```

---

## 💡 Pro Tips

### Tip 1: Use the Task File as Your Guide

The task file is your complete reference. When in doubt:
1. Re-read the relevant section
2. Follow examples given
3. Trust the instructions

**Don't** try to remember everything - keep the task file open.

### Tip 2: Verify Early and Often

Don't wait until the end to check outputs:
```bash
# After each step, verify
ls -lh workspace/outputs/${TASK_ID}/  # Files created?
jq . latest-output.json                # Valid JSON?
cat summary.md                         # Looks good?
```

### Tip 3: Document Unexpected Findings

If you discover something surprising:
```markdown
## Unexpected Discoveries

- Found that TypeMapped.name_type field already exists (line 1052)
- This means we don't need to add it, just populate it
- Changes our implementation approach
```

This helps downstream tasks and improves the plan.

### Tip 4: Time Tracking Helps Everyone

```markdown
## Time Breakdown

- Read task & setup: 30 min
- Run conformance tests: 25 min
- Analyze results: 1.5 hours
- Create outputs: 1 hour
- Verification: 15 min

**Total: 3.25 hours** (estimate was 2-4 hours)
**Accuracy: Within estimate ✅**
```

### Tip 5: When Stuck, Document and Continue

If blocked on something non-critical:
```markdown
## Blockers Encountered

**Issue**: Could not determine if feature X is implemented
**Impact**: Unable to complete coverage percentage for advanced types
**Workaround**: Marked as "unknown" and documented for manual review
**Recommendation**: Manual code review needed for type_expr.rs:800-850
```

Better to complete 95% perfectly than be 100% stuck.

---

## 🎯 Final Reminder: Your Mission

**You are ONE agent in a PARALLEL system.**

Your success means:
- ✅ Your task outputs are **complete and accurate**
- ✅ Downstream tasks can **use your outputs** without issues
- ✅ You've **documented what you learned**
- ✅ You've **verified your work** thoroughly

**You are NOT responsible for**:
- ❌ Other agents' tasks
- ❌ The overall project timeline
- ❌ Coordinating with other agents
- ❌ Fixing issues in other tasks

**Focus on YOUR task. Do it excellently. Trust the system.**

---

## 📞 What to Do If You're Truly Blocked

If you cannot complete your task:

1. **Document the blocker**:
   ```markdown
   # TASK INCOMPLETE - BLOCKER

   ## Task: {task-id}
   ## Blocker: {clear description}
   ## Impact: {what can't be done}
   ## Investigation done: {what you tried}
   ## Recommendation: {how to unblock}
   ```

2. **Save partial outputs**:
   - Save what you COULD complete
   - Mark incomplete sections clearly
   - Provide notes on what's missing

3. **Report the issue**:
   - Note blocker in your output README
   - Include enough detail for debugging
   - Suggest next steps if possible

**Remember**: A well-documented blocker is better than guessing or making up data.

---

## 🎓 Learning Resources

### Project Documentation

- **Comprehensive Plan**: `TYPE_PARSING_COMPREHENSIVE_PLAN.md`
- **Task System**: `TASK-SYSTEM-SUMMARY.md`
- **Task Graph**: `tasks/00-TASK-GRAPH.md`
- **Type Parsing Plan**: `type-parsing-plan/README.md`

### TypeScript References

- **TypeScript Handbook**: https://www.typescriptlang.org/docs/handbook/
- **TypeScript Spec**: `parse-js/tests/TypeScript/doc/spec-ARCHIVED.md`
- **TypeScript Source**: `parse-js/tests/TypeScript/src/compiler/`

### Rust Resources

- **Project README**: `README.md`
- **Parser Code**: `parse-js/src/parse/type_expr.rs`
- **AST Definitions**: `parse-js/src/ast/type_expr.rs`

---

## ✨ You've Got This!

**You have everything you need**:
- ✅ Complete task definition
- ✅ Clear instructions
- ✅ Expected outputs specified
- ✅ Verification steps provided
- ✅ Troubleshooting guide
- ✅ Examples throughout

**Follow the instructions. Trust the process. Deliver quality work.**

**Good luck, Agent! 🚀**

---

*Last updated: 2025-11-20*
*Task system version: 1.0*
*Project: ecma-rs TypeScript Type Parsing*
