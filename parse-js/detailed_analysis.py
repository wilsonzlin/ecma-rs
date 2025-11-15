#!/usr/bin/env python3
"""
Detailed failure analysis to find fixable patterns.
"""
import re
from collections import defaultdict

# Read failures
with open('typescript_conformance_failures.txt', 'r') as f:
    content = f.read()

failures = []
blocks = content.split('=' * 80)[2:]  # Skip header

for block in blocks:
    if not block.strip():
        continue

    file_match = re.search(r'File: (.+)', block)
    error_match = re.search(r'Error: (.+?) \[token=(.+?)\] around loc \[(\d+):(\d+)\]', block)

    if file_match and error_match:
        failures.append({
            'file': file_match.group(1),
            'error_type': error_match.group(1),
            'token': error_match.group(2),
            'loc_start': int(error_match.group(3)),
            'loc_end': int(error_match.group(4)),
        })

print(f"Total failures: {len(failures)}\n")

# Group by error + token combination
error_token_combos = defaultdict(list)
for f in failures:
    key = f"{f['error_type']} + {f['token']}"
    error_token_combos[key].append(f)

# Sort by frequency
sorted_combos = sorted(error_token_combos.items(), key=lambda x: len(x[1]), reverse=True)

print("=" * 80)
print("TOP ERROR + TOKEN COMBINATIONS")
print("=" * 80)
for combo, failures_list in sorted_combos[:30]:
    count = len(failures_list)
    if count >= 3:  # Only show patterns with 3+ occurrences
        print(f"{count:3d} | {combo}")
        # Show sample files
        for f in failures_list[:2]:
            filename = f['file'].split('/')[-1]
            print(f"       - {filename}")
