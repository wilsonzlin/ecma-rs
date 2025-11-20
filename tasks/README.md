# Task-Based Parallel Implementation System

This directory contains a **task dependency graph** for implementing TypeScript type parsing. Each task is a self-contained unit that can be executed by an isolated agent in parallel with other tasks.

## 🎯 Key Concepts

### 1. Task Independence
Each task is **completely self-contained**:
- Reads only its own markdown file + specified inputs
- Cannot communicate with other running tasks
- Writes structured outputs for downstream tasks
- Includes all context needed to execute

### 2. Parallelization
Tasks with no dependencies run **simultaneously**:
- **Phase 1 (Analysis)**: 6 tasks in parallel
- **Phase 3 (Implementation)**: 10 features in parallel
- **Phase 5 (Optimization)**: 5 optimizations in parallel

### 3. Dependency Management
Tasks declare dependencies via frontmatter:
```yaml
dependencies:
  - "01-analysis/01-run-conformance-tests"
inputs:
  - "../01-analysis/01-run-conformance-tests/test-results.json"
```

Orchestrator ensures all dependencies complete before starting a task.

## 📁 Directory Structure

```
tasks/
├── 00-TASK-GRAPH.md           # Mermaid visualization
├── README.md                   # This file
├── 01-analysis/                # Phase 1: Discover what's needed
│   ├── 01-run-conformance-tests.md
│   ├── 02-categorize-failures.md
│   ├── 03-audit-ast-coverage.md
│   ├── 04-audit-parser-coverage.md
│   ├── 05-research-feature-usage.md
│   └── 06-baseline-performance.md
├── 02-planning/                # Phase 2: Decide what to build
│   ├── 01-prioritize-features.md
│   ├── 02-design-ast-nodes.md
│   ├── 03-plan-parser-extensions.md
│   └── 04-define-test-strategy.md
├── 03-implementation/          # Phase 3: Build features
│   ├── 01-readonly-tuples-rest.md
│   ├── 02-import-typeof.md
│   ├── 03-abstract-constructors.md
│   ├── 04-satisfies-operator.md
│   ├── 05-decorator-metadata.md
│   ├── 06-using-declarations.md
│   ├── 07-jsdoc-types.md
│   ├── 08-template-literal-types.md
│   ├── 09-infer-extends.md
│   └── 10-type-modifiers.md
├── 04-validation/              # Phase 4: Verify it works
│   ├── 01-run-conformance.md
│   ├── 02-validate-real-world.md
│   └── 03-benchmark-performance.md
└── 05-optimization/            # Phase 5: Make it fast
    ├── 01-arena-allocation.md
    ├── 02-simd-scanning.md
    ├── 03-speculation-cache.md
    ├── 04-fast-paths.md
    └── 05-compact-ast.md
```

## 🚀 Quick Start

### For Orchestrator (Managing Agents)

1. **Initialize workspace**:
```bash
mkdir -p workspace/outputs/{01-analysis,02-planning,03-implementation,04-validation,05-optimization}
```

2. **Start Phase 1 (all parallel)**:
```bash
# Launch 6 agents simultaneously
agent run tasks/01-analysis/01-run-conformance-tests.md &
agent run tasks/01-analysis/02-categorize-failures.md &
agent run tasks/01-analysis/03-audit-ast-coverage.md &
agent run tasks/01-analysis/04-audit-parser-coverage.md &
agent run tasks/01-analysis/05-research-feature-usage.md &
agent run tasks/01-analysis/06-baseline-performance.md &
wait
```

3. **Check outputs**:
```bash
ls -R workspace/outputs/01-analysis/
```

4. **Start Phase 2** (when Phase 1 complete):
```bash
agent run tasks/02-planning/01-prioritize-features.md
# ... etc
```

### For Agent (Executing Task)

1. **Read task file completely**:
```bash
cat tasks/01-analysis/01-run-conformance-tests.md
```

2. **Check frontmatter for inputs**:
```yaml
inputs:
  - "../02-planning/ast-extensions.md"
```

3. **Read all input files**:
```bash
cat workspace/outputs/02-planning/ast-extensions.md
```

4. **Execute task** (follow instructions in task file)

5. **Write outputs** (as specified in frontmatter):
```bash
# Create output directory
mkdir -p workspace/outputs/03-implementation/01-readonly-tuples-rest/

# Write outputs
echo "..." > workspace/outputs/.../implementation-notes.md
echo "..." > workspace/outputs/.../lessons-learned.md
```

6. **Signal completion** (for orchestrator to detect)

## 📊 Task Metadata

Each task file uses YAML frontmatter:

```yaml
---
task_id: "03-implementation/01-readonly-tuples-rest"
title: "Implement Readonly Tuples with Rest Elements"
phase: "implementation"
estimated_duration: "4-8 hours"
complexity: "medium"
dependencies:
  - "02-planning/02-design-ast-nodes"
  - "02-planning/03-plan-parser-extensions"
inputs:
  - "../../02-planning/02-design-ast-nodes/ast-extensions.md"
  - "../../02-planning/03-plan-parser-extensions/parser-plan.md"
outputs:
  - "implementation-notes.md"
  - "test-cases.rs"
  - "lessons-learned.md"
  - "git-patch.diff"
skills_required:
  - "Rust programming"
  - "Parser implementation"
---
```

### Field Meanings

- **task_id**: Unique identifier (matches file path)
- **title**: Human-readable name
- **phase**: analysis | planning | implementation | validation | optimization
- **estimated_duration**: Time estimate (for scheduling)
- **complexity**: low | medium | high (for agent assignment)
- **dependencies**: Tasks that must complete first
- **inputs**: Files from previous tasks to read
- **outputs**: Files this task will create
- **skills_required**: What agent needs to know

## 🔄 Output Propagation

### Output Types

Tasks produce various outputs for downstream consumption:

| Output Type | Description | Example |
|-------------|-------------|---------|
| **Data (JSON)** | Machine-readable structured data | `test-results.json`, `categories.json` |
| **Reports (MD)** | Human-readable analysis | `test-summary.md`, `analysis.md` |
| **Notes** | Implementation details | `implementation-notes.md` |
| **Lessons** | What was learned | `lessons-learned.md` |
| **Code** | Implementation | `git-patch.diff`, `test-cases.rs` |
| **Plans** | Decisions made | `roadmap.md`, `feature-specs.md` |

### Directory Structure

```
workspace/
├── outputs/
│   ├── 01-analysis/
│   │   ├── 01-run-conformance-tests/
│   │   │   ├── test-results.json
│   │   │   ├── test-summary.md
│   │   │   └── failures.txt
│   │   ├── 02-categorize-failures/
│   │   │   ├── categories.json
│   │   │   └── priority-matrix.md
│   │   └── ...
│   ├── 02-planning/
│   │   └── ...
│   └── ...
└── shared/
    ├── current-state.md        # Snapshot of codebase
    ├── typescript-spec.md      # Reference docs
    └── coding-standards.md     # Project conventions
```

## 🎓 Task Writing Guidelines

### For Task Authors

When creating new tasks:

1. **Be self-contained**: Agent has NO external knowledge
   - Include ALL context in task file
   - Link to reference materials
   - Explain WHY, not just WHAT

2. **Be specific**: Clear acceptance criteria
   - What outputs to produce
   - How to verify success
   - What "done" looks like

3. **Be realistic**: Honest time estimates
   - Account for research time
   - Include testing & documentation
   - Add buffer for debugging

4. **Be helpful**: Anticipate problems
   - Common issues & solutions
   - Verification commands
   - Debugging tips

### Task Template

```markdown
---
task_id: "XX-phase/YY-task-name"
title: "Task Title"
phase: "phase-name"
estimated_duration: "X-Y hours"
complexity: "low|medium|high"
dependencies: []
inputs: []
outputs: []
skills_required: []
---

# Task: Title

## Objective
(What to accomplish in 1-2 sentences)

## Context
(Why this matters, background info)

## Prerequisites
(What to read/understand first)

## Instructions

### Step 1: ...
(Detailed step-by-step instructions)

### Step 2: ...
(Continue...)

## Acceptance Criteria
(How to know you're done)

## Common Issues & Solutions
(Known problems and fixes)

## Time Estimate Breakdown
(Where time will be spent)

## Downstream Impact
(Who depends on this task)

## Notes for Agent
(Meta-guidance)
```

## 📈 Progress Tracking

### For Orchestrator

Track task completion:

```json
{
  "project": "typescript-type-parsing",
  "status": {
    "phase_1_analysis": {
      "total": 6,
      "completed": 4,
      "running": 2,
      "blocked": 0
    },
    "phase_2_planning": {
      "total": 4,
      "completed": 0,
      "running": 0,
      "blocked": 4
    }
  },
  "tasks": {
    "01-analysis/01-run-conformance-tests": {
      "status": "completed",
      "started": "2025-11-20T10:00:00Z",
      "completed": "2025-11-20T12:30:00Z",
      "duration_hours": 2.5,
      "agent": "agent-1"
    },
    "01-analysis/02-categorize-failures": {
      "status": "running",
      "started": "2025-11-20T10:30:00Z",
      "agent": "agent-2"
    }
  }
}
```

### Metrics to Track

- Tasks completed / total
- Average task duration vs estimate
- Bottlenecks (highly-dependent tasks)
- Agent efficiency
- Parallel utilization

## 🧪 Testing Tasks

Test your task definitions before deploying:

```bash
# Validate YAML frontmatter
yq eval tasks/03-implementation/01-readonly-tuples-rest.md

# Check all dependencies exist
./scripts/validate-task-graph.sh

# Simulate task execution (dry-run)
agent run --dry-run tasks/01-analysis/01-run-conformance-tests.md

# Check output completeness
./scripts/check-outputs.sh 01-analysis/01-run-conformance-tests
```

## 🔍 Debugging

### Task Not Starting

Check:
- [ ] All dependencies completed?
- [ ] Input files exist?
- [ ] Agent has required skills?

### Task Failing

Check:
- [ ] Task file has complete instructions?
- [ ] Input data is correct format?
- [ ] Environment set up properly?

### Outputs Missing

Check:
- [ ] Task completed successfully?
- [ ] Output paths in frontmatter correct?
- [ ] Agent has write permissions?

## 🎯 Best Practices

### DO

✅ Make tasks atomic (one clear goal)
✅ Write detailed instructions (assume zero context)
✅ Include examples and references
✅ Test tasks before deploying
✅ Document lessons learned in outputs
✅ Version control task definitions

### DON'T

❌ Assume agent knows project context
❌ Create tasks with hidden dependencies
❌ Skip acceptance criteria
❌ Forget to estimate duration
❌ Make tasks too large (>20 hours)

## 📚 Further Reading

- [00-TASK-GRAPH.md](00-TASK-GRAPH.md) - Visual dependency graph
- [../type-parsing-plan/README.md](../type-parsing-plan/README.md) - Overall project plan
- [../type-parsing-plan/ROADMAP.md](../type-parsing-plan/ROADMAP.md) - Timeline

## 🆘 Support

If you're an agent stuck on a task:
1. Re-read task file completely
2. Check all input files
3. Look for "Common Issues" section
4. Document the blocker in your output
5. Mark task as "blocked" for orchestrator

If you're an orchestrator with questions:
1. Check task frontmatter for errors
2. Verify dependencies make sense
3. Look at similar tasks for patterns
4. Consult project maintainers

---

**Ready to start?** Check out [00-TASK-GRAPH.md](00-TASK-GRAPH.md) to see the full dependency graph!
