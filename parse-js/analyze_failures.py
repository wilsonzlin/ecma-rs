#!/usr/bin/env python3
import re
from collections import defaultdict, Counter

# Read the failure report
with open('typescript_conformance_failures.txt', 'r') as f:
    content = f.read()

# Extract all error messages
error_pattern = r'Error: (.+?) \[token'
errors = re.findall(error_pattern, content)

# Categorize errors
error_counts = Counter(errors)

print("=" * 80)
print("ERROR PATTERN ANALYSIS")
print("=" * 80)
print(f"Total unique error patterns: {len(error_counts)}")
print(f"Total failures: {sum(error_counts.values())}\n")

print("Top 30 Error Patterns:")
print("=" * 80)
for error, count in error_counts.most_common(30):
    print(f"{count:4d} | {error}")

# Extract file paths and group by directory
file_pattern = r'File: (.+?)\.ts'
files = re.findall(file_pattern, content)

# Group by test category (directory)
categories = defaultdict(list)
for file in files:
    parts = file.split('/')
    if 'conformance' in parts:
        idx = parts.index('conformance')
        if idx + 1 < len(parts):
            category = parts[idx + 1]
            categories[category].append(file)

print("\n" + "=" * 80)
print("TOP FAILURE CATEGORIES BY TEST TYPE:")
print("=" * 80)
sorted_cats = sorted(categories.items(), key=lambda x: len(x[1]), reverse=True)
for cat, files in sorted_cats[:20]:
    print(f"{len(files):4d} | {cat}")

# Extract and analyze token types
token_pattern = r'\[token=Some\((.+?)\)\]'
tokens = re.findall(token_pattern, content)
token_counts = Counter(tokens)

print("\n" + "=" * 80)
print("TOP 20 PROBLEMATIC TOKENS:")
print("=" * 80)
for token, count in token_counts.most_common(20):
    print(f"{count:4d} | {token}")
