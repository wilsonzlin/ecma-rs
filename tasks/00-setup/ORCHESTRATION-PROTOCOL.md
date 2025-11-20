# Task Orchestration Protocol

## Overview

This document defines how the orchestrator tracks task completion and launches dependent tasks.

## Task States

Each task has a status file: `workspace/status/{task_id}.json`

```json
{
  "task_id": "01-analysis/01-run-conformance-tests",
  "status": "completed|running|blocked|failed",
  "started_at": "2025-11-20T10:00:00Z",
  "completed_at": "2025-11-20T12:30:00Z",
  "agent_id": "agent-1",
  "outputs_validated": true,
  "duration_seconds": 9000,
  "exit_code": 0
}
```

## Phase Completion Gates

### Phase 1: Analysis Complete When

```bash
# All 6 analysis tasks have status=completed
[ -f workspace/status/01-analysis/01-run-conformance-tests.json ] &&
[ -f workspace/status/01-analysis/02-categorize-failures.json ] &&
[ -f workspace/status/01-analysis/03-audit-ast-coverage.json ] &&
[ -f workspace/status/01-analysis/04-audit-parser-coverage.json ] &&
[ -f workspace/status/01-analysis/05-research-feature-usage.json ] &&
[ -f workspace/status/01-analysis/06-baseline-performance.json ]

# AND all outputs exist
[ -f workspace/outputs/01-analysis/01-run-conformance-tests/test-results.json ] &&
# ... etc
```

### Phase 2: Planning Complete When

All planning tasks completed AND feature list generated.

### Phase 3: Implementation Complete When

All feature tasks completed (may be dynamically generated based on Phase 2 output).

## Task Launch Protocol

### 1. Check Dependencies

```python
def can_launch_task(task_id):
    task_file = read_task_frontmatter(f"tasks/{task_id}.md")

    for dep in task_file['dependencies']:
        status = read_status(f"workspace/status/{dep}.json")
        if status['status'] != 'completed':
            return False

        # Verify all required outputs exist
        for output in task_file['inputs']:
            if not os.path.exists(f"workspace/outputs/{output}"):
                return False

    return True
```

### 2. Launch Task

```bash
# Create status file
echo '{"task_id": "...", "status": "running", "started_at": "..."}' > workspace/status/{task_id}.json

# Launch agent
agent run tasks/{task_id}.md > workspace/logs/{task_id}.log 2>&1 &

# Track PID
echo $! > workspace/pids/{task_id}.pid
```

### 3. Monitor Completion

```bash
# Poll for completion
while true; do
    if ! ps -p $(cat workspace/pids/{task_id}.pid) > /dev/null; then
        # Process exited
        exit_code=$?

        # Update status
        jq '.status = "completed" | .completed_at = now | .exit_code = '$exit_code workspace/status/{task_id}.json

        # Validate outputs
        validate_outputs {task_id}

        break
    fi
    sleep 5
done
```

### 4. Validate Outputs

```bash
validate_outputs() {
    task_id=$1
    task_file="tasks/${task_id}.md"

    # Extract expected outputs from frontmatter
    expected_outputs=$(yq '.outputs[]' "$task_file")

    all_exist=true
    for output in $expected_outputs; do
        full_path="workspace/outputs/${task_id}/${output}"
        if [ ! -f "$full_path" ]; then
            echo "ERROR: Missing output: $full_path"
            all_exist=false
        fi
    done

    if $all_exist; then
        jq '.outputs_validated = true' workspace/status/${task_id}.json
    else
        jq '.status = "failed" | .error = "Missing outputs"' workspace/status/${task_id}.json
    fi
}
```

## Parallelization Strategy

### Max Parallel Tasks Per Phase

```python
PHASE_LIMITS = {
    'analysis': 6,      # All 6 can run together
    'planning': 3,      # 3 after prioritization done
    'implementation': 10, # All 10 features in parallel
    'validation': 2,    # Conformance + real-world in parallel
    'optimization': 5   # All 5 optimizations in parallel
}
```

### Resource Management

```python
AGENT_RESOURCES = {
    'max_cpu_per_agent': 4,
    'max_memory_gb': 8,
    'max_concurrent_agents': 10
}

def schedule_task(task_id):
    # Check resource availability
    current_agents = count_running_agents()
    if current_agents >= AGENT_RESOURCES['max_concurrent_agents']:
        queue_task(task_id)
        return

    # Launch task
    launch_task(task_id)
```

## Error Handling

### Task Failure

```bash
if task_failed {task_id}; then
    # Mark status
    jq '.status = "failed"' workspace/status/{task_id}.json

    # Check if blocking
    dependent_tasks=$(find_dependent_tasks {task_id})

    for dep_task in $dependent_tasks; do
        jq '.status = "blocked" | .blocked_by = "'${task_id}'"' workspace/status/${dep_task}.json
    done

    # Notify orchestrator
    echo "ALERT: Task ${task_id} failed, blocking ${#dependent_tasks} tasks"
fi
```

### Task Timeout

```bash
TASK_TIMEOUT_HOURS = {
    'analysis': 8,
    'planning': 6,
    'implementation': 12,
    'validation': 4,
    'optimization': 20
}

# Kill if exceeds timeout
if task_runtime > TASK_TIMEOUT_HOURS[phase]; then
    kill -9 $(cat workspace/pids/{task_id}.pid)
    jq '.status = "failed" | .error = "Timeout"' workspace/status/{task_id}.json
fi
```

## Progress Dashboard

### Real-Time View

```bash
#!/bin/bash
# scripts/show-progress.sh

echo "=== TypeScript Parsing Project Status ==="
echo ""

for phase in 01-analysis 02-planning 03-implementation 04-validation 05-optimization; do
    total=$(find tasks/${phase} -name "*.md" | wc -l)
    completed=$(find workspace/status/${phase} -name "*.json" | xargs jq -r '.status' | grep -c "completed")
    running=$(find workspace/status/${phase} -name "*.json" | xargs jq -r '.status' | grep -c "running")
    blocked=$(find workspace/status/${phase} -name "*.json" | xargs jq -r '.status' | grep -c "blocked")

    echo "Phase: ${phase}"
    echo "  Total: ${total}"
    echo "  Completed: ${completed} ($(( completed * 100 / total ))%)"
    echo "  Running: ${running}"
    echo "  Blocked: ${blocked}"
    echo ""
done
```

## Example Orchestrator Script

```python
#!/usr/bin/env python3
import os
import json
import subprocess
import time
from pathlib import Path

class TaskOrchestrator:
    def __init__(self):
        self.workspace = Path("workspace")
        self.tasks_dir = Path("tasks")

    def get_task_status(self, task_id):
        status_file = self.workspace / "status" / f"{task_id}.json"
        if not status_file.exists():
            return None
        with open(status_file) as f:
            return json.load(f)

    def can_launch(self, task_id):
        task_file = self.tasks_dir / f"{task_id}.md"
        # Parse frontmatter
        dependencies = self.parse_frontmatter(task_file)['dependencies']

        for dep in dependencies:
            status = self.get_task_status(dep)
            if not status or status['status'] != 'completed':
                return False
        return True

    def launch_task(self, task_id):
        print(f"Launching task: {task_id}")

        # Create output directory
        output_dir = self.workspace / "outputs" / task_id
        output_dir.mkdir(parents=True, exist_ok=True)

        # Create status file
        status = {
            "task_id": task_id,
            "status": "running",
            "started_at": time.time()
        }
        status_file = self.workspace / "status" / f"{task_id}.json"
        status_file.parent.mkdir(parents=True, exist_ok=True)
        with open(status_file, 'w') as f:
            json.dump(status, f)

        # Launch agent (example - adjust for your agent system)
        log_file = self.workspace / "logs" / f"{task_id}.log"
        log_file.parent.mkdir(parents=True, exist_ok=True)

        proc = subprocess.Popen(
            ["agent", "run", f"tasks/{task_id}.md"],
            stdout=open(log_file, 'w'),
            stderr=subprocess.STDOUT
        )

        # Track PID
        pid_file = self.workspace / "pids" / f"{task_id}.pid"
        pid_file.parent.mkdir(parents=True, exist_ok=True)
        with open(pid_file, 'w') as f:
            f.write(str(proc.pid))

    def main_loop(self):
        while True:
            # Find tasks ready to launch
            for task_file in self.tasks_dir.rglob("*.md"):
                if task_file.name in ["README.md", "TEMPLATE.md"]:
                    continue

                task_id = str(task_file.relative_to(self.tasks_dir).with_suffix(''))

                status = self.get_task_status(task_id)
                if status and status['status'] in ['completed', 'running']:
                    continue

                if self.can_launch(task_id):
                    self.launch_task(task_id)

            # Check for completion
            all_done = self.check_all_complete()
            if all_done:
                print("All tasks complete!")
                break

            time.sleep(10)

if __name__ == "__main__":
    orchestrator = TaskOrchestrator()
    orchestrator.main_loop()
```

## Testing the Orchestrator

```bash
# Dry run
./scripts/orchestrator.py --dry-run

# Run single phase
./scripts/orchestrator.py --phase 01-analysis

# Full run
./scripts/orchestrator.py
```
