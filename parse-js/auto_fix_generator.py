#!/usr/bin/env python3
"""
Automated fix generator for TypeScript conformance test failures.
Analyzes failures and generates targeted fixes.
"""
import re
from collections import defaultdict, Counter
import os

# Read the failure report
with open('typescript_conformance_failures.txt', 'r') as f:
    content = f.read()

# Parse failures into structured data
failures = []
failure_blocks = content.split('=' * 80)[2:]  # Skip header
for block in failure_blocks:
    if not block.strip():
        continue

    file_match = re.search(r'File: (.+?)\.ts', block)
    error_match = re.search(r'Error: (.+?) \[token=(.+?)\] around loc \[(\d+):(\d+)\]', block)

    if file_match and error_match:
        failures.append({
            'file': file_match.group(1) + '.ts',
            'error_type': error_match.group(1),
            'token': error_match.group(2),
            'loc_start': int(error_match.group(3)),
            'loc_end': int(error_match.group(4)),
        })

print(f"Parsed {len(failures)} failures\n")

# Group failures by error pattern
error_patterns = defaultdict(list)
for f in failures:
    pattern = f['error_type']
    error_patterns[pattern].append(f)

# Analyze fixable patterns
print("=" * 80)
print("FIXABLE PATTERNS ANALYSIS")
print("=" * 80)

fixes_needed = {}

# Pattern 1: Expression operator errors with TypeScript keywords
ts_keyword_tokens = ['KeywordClass', 'KeywordInterface', 'KeywordEnum', 'KeywordNamespace',
                      'KeywordModule', 'KeywordType', 'KeywordAwait']

expr_op_errors = [f for f in failures if 'ExpectedSyntax("expression operator")' in f['error_type']]
ts_keyword_expr_ops = [f for f in expr_op_errors if any(kw in f['token'] for kw in ts_keyword_tokens)]

print(f"\n1. Expression operator with TS keywords: {len(ts_keyword_expr_ops)} errors")
print("   Fix: Allow these keywords to end expressions (treat as errors but parse successfully)")
for token in set(f['token'] for f in ts_keyword_expr_ops):
    count = sum(1 for f in ts_keyword_expr_ops if f['token'] == token)
    print(f"      {count:3d}x {token}")

#Pattern 2: Expression operand errors - need to allow more tokens as expression starts
expr_operand_errors = [f for f in failures if 'ExpectedSyntax("expression operand")' in f['error_type']]
print(f"\n2. Expression operand errors: {len(expr_operand_errors)} errors")
print("   Common tokens that should start expressions:")
operand_tokens = Counter(f['token'] for f in expr_operand_errors)
for token, count in operand_tokens.most_common(10):
    print(f"      {count:3d}x {token}")

# Pattern 3: Invalid character escapes in templates
invalid_escape_errors = [f for f in failures if 'InvalidCharacterEscape' in f['error_type']]
print(f"\n3. Invalid character escapes: {len(invalid_escape_errors)} errors")
print("   Fix: Allow invalid escapes in tagged templates (ES2018+)")

# Pattern 4: Decorator @ token
decorator_errors = [f for f in failures if f['token'] == 'Some(At)']
print(f"\n4. Decorator syntax (@): {len(decorator_errors)} errors")
print("   Fix: Improve decorator parsing to handle more contexts")

# Pattern 5: Generic type arguments (ChevronLeft)
generic_errors = [f for f in failures if 'ChevronLeft' in f['token']]
print(f"\n5. Generic type argument ambiguity: {len(generic_errors)} errors")
print("   Fix: Improve lookahead for < as type argument vs comparison")

# Pattern 6: Pattern parsing (await/yield in wrong contexts)
pattern_errors = [f for f in failures if 'ExpectedSyntax("pattern")' in f['error_type']]
print(f"\n6. Pattern parsing errors: {len(pattern_errors)} errors")
print("   Fix: Allow await/yield/async as parameter names in more contexts")
pattern_tokens = Counter(f['token'] for f in pattern_errors)
for token, count in pattern_tokens.most_common(5):
    print(f"      {count:3d}x {token}")

print("\n" + "=" * 80)
print("RECOMMENDED FIX PRIORITY")
print("=" * 80)
print("1. Expression parsing: Make more permissive (~275 fixes)")
print("2. Template literal escapes: Allow invalid escapes (~39 fixes)")
print("3. Generic type arguments: Improve < > handling (~43+ fixes)")
print("4. Decorator parsing: Better @ token handling (~27 fixes)")
print("5. Pattern parsing: Allow keywords as names (~43 fixes)")
print("\nEstimated potential: ~400+ tests fixed with these 5 changes")
