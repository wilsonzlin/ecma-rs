#!/usr/bin/env python3
import json
import re
from collections import defaultdict, Counter

# Read the failures file
with open('workspace/outputs/01-analysis/01-run-conformance-tests/failures.txt', 'r') as f:
    content = f.read()

# Parse failures
failures = []
current_failure = {}

for line in content.split('\n'):
    if line.startswith('=' * 80):
        if current_failure:
            failures.append(current_failure)
        current_failure = {}
    elif line.startswith('File:'):
        file_path = line.replace('File:', '').strip()
        current_failure['file'] = file_path
        # Extract directory path
        if 'tests/cases/conformance/' in file_path:
            dir_path = file_path.replace('tests/TypeScript/tests/cases/conformance/', '')
            parts = dir_path.split('/')
            if len(parts) >= 2:
                current_failure['category'] = '/'.join(parts[:2])
            else:
                current_failure['category'] = parts[0] if parts else 'unknown'
    elif line.startswith('Duration:'):
        duration_str = line.replace('Duration:', '').strip()
        current_failure['duration'] = duration_str
    elif line.startswith('Error:'):
        error = line.replace('Error:', '').strip()
        current_failure['error'] = error

        # Extract error type
        if error.startswith('ExpectedSyntax'):
            match = re.search(r'ExpectedSyntax\("([^"]+)"\)', error)
            if match:
                current_failure['error_type'] = 'ExpectedSyntax'
                current_failure['expected_syntax'] = match.group(1)
        elif error.startswith('RequiredTokenNotFound'):
            match = re.search(r'RequiredTokenNotFound\((\w+)', error)
            if match:
                current_failure['error_type'] = 'RequiredTokenNotFound'
                current_failure['required_token'] = match.group(1)
        elif 'TIMEOUT' in error:
            current_failure['error_type'] = 'Timeout'
        elif 'PANIC' in error:
            current_failure['error_type'] = 'Panic'
        else:
            # Other error types
            error_type_match = re.match(r'(\w+)', error)
            if error_type_match:
                current_failure['error_type'] = error_type_match.group(1)

if current_failure:
    failures.append(current_failure)

# Categorize by directory
by_directory = defaultdict(int)
for f in failures:
    if 'category' in f:
        by_directory[f['category']] += 1

# Categorize by error type
by_error_type = defaultdict(int)
for f in failures:
    if 'error_type' in f:
        by_error_type[f['error_type']] += 1

# Extract expected syntax patterns
expected_syntax_patterns = defaultdict(int)
for f in failures:
    if 'expected_syntax' in f:
        expected_syntax_patterns[f['expected_syntax']] += 1

# Extract required token patterns
required_token_patterns = defaultdict(int)
for f in failures:
    if 'required_token' in f:
        required_token_patterns[f['required_token']] += 1

# Find specific missing features by analyzing file names and error patterns
missing_features = []

# Count specific patterns
decorator_failures = [f for f in failures if 'decorator' in f.get('file', '').lower()]
private_name_failures = [f for f in failures if 'privatename' in f.get('file', '').lower()]
using_failures = [f for f in failures if 'usingdeclaration' in f.get('file', '').lower()]

# Create categories JSON
categories = {
    "summary": {
        "total_failures": len(failures),
        "by_error_type": dict(sorted(by_error_type.items(), key=lambda x: x[1], reverse=True)),
        "by_directory": dict(sorted(by_directory.items(), key=lambda x: x[1], reverse=True)[:30]),
        "expected_syntax_patterns": dict(sorted(expected_syntax_patterns.items(), key=lambda x: x[1], reverse=True)),
        "required_token_patterns": dict(sorted(required_token_patterns.items(), key=lambda x: x[1], reverse=True))
    },
    "timeout_patterns": [],
    "panic_cases": []
}

# Save categories JSON
with open('workspace/outputs/01-analysis/02-categorize-failures/categories.json', 'w') as f:
    json.dump(categories, f, indent=2)

# Create feature gaps JSON
feature_gaps = []

# Analyze decorator-related failures
if decorator_failures:
    feature_gaps.append({
        "feature": "Decorators in error positions",
        "test_failures": len(decorator_failures),
        "priority": "medium",
        "difficulty": "medium",
        "typescript_version": "5.0+",
        "description": "Decorators on invalid positions or ES decorators syntax"
    })

# Analyze private names
if private_name_failures:
    feature_gaps.append({
        "feature": "Private name (#) syntax edge cases",
        "test_failures": len(private_name_failures),
        "priority": "low",
        "difficulty": "low",
        "typescript_version": "3.8+",
        "description": "Edge cases in private class member syntax"
    })

# Analyze using declarations
if using_failures:
    feature_gaps.append({
        "feature": "Using declarations",
        "test_failures": len(using_failures),
        "priority": "medium",
        "difficulty": "low",
        "typescript_version": "5.2",
        "description": "Resource management using declarations"
    })

# Error recovery issues
error_recovery_files = [f for f in failures if 'errorrecovery' in f.get('file', '').lower()]
if error_recovery_files:
    feature_gaps.append({
        "feature": "Error recovery parsing",
        "test_failures": len(error_recovery_files),
        "priority": "low",
        "difficulty": "high",
        "typescript_version": "all",
        "description": "Parser is too strict - TypeScript allows some errors for IDE friendliness"
    })

# Most common ExpectedSyntax patterns indicate missing parsers
if 'expression operand' in expected_syntax_patterns:
    feature_gaps.append({
        "feature": "Expression operand parsing edge cases",
        "test_failures": expected_syntax_patterns['expression operand'],
        "priority": "high",
        "difficulty": "medium",
        "typescript_version": "various",
        "description": "Unexpected tokens where expression operands are expected"
    })

if 'expression operator' in expected_syntax_patterns:
    feature_gaps.append({
        "feature": "Expression operator parsing edge cases",
        "test_failures": expected_syntax_patterns['expression operator'],
        "priority": "high",
        "difficulty": "medium",
        "typescript_version": "various",
        "description": "Unexpected tokens where expression operators are expected"
    })

# Save feature gaps JSON
with open('workspace/outputs/01-analysis/02-categorize-failures/feature-gaps.json', 'w') as f:
    json.dump(feature_gaps, f, indent=2)

print(f"Analyzed {len(failures)} failures")
print(f"Found {len(by_directory)} unique categories")
print(f"Found {len(feature_gaps)} feature gaps")
print("Generated: categories.json, feature-gaps.json")
