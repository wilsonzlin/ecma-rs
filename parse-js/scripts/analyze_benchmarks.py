#!/usr/bin/env python3
"""
Analyze criterion benchmark results and generate performance reports.
"""

import json
import os
from pathlib import Path
from datetime import datetime
import subprocess

def get_git_commit():
    """Get current git commit hash."""
    try:
        result = subprocess.run(
            ['git', 'rev-parse', '--short', 'HEAD'],
            capture_output=True,
            text=True,
            check=True
        )
        return result.stdout.strip()
    except:
        return "unknown"

def read_estimates(path):
    """Read estimates.json file from criterion output."""
    with open(path, 'r') as f:
        return json.load(f)

def analyze_criterion_results(criterion_dir):
    """Analyze criterion benchmark results."""
    results = {
        'parsing_speed': {
            'small_files': {},
            'medium_files': {},
            'large_files': {},
            'averages': {}
        },
        'feature_benchmarks': {},
        'real_world_patterns': {},
        'stress_test': {}
    }

    # File metadata
    file_metadata = {
        'primitive_types': {'lines': 27, 'bytes': 635},
        'simple_interface': {'lines': 53, 'bytes': 828},
        'complex_types': {'lines': 120, 'bytes': 3617},
        'medium_file': {'lines': 318, 'bytes': 6199},
        'large_file': {'lines': 836, 'bytes': 17478},
        'very_large_file': {'lines': 2508, 'bytes': 52434},
    }

    # Parse type_parsing benchmarks
    type_parsing_dir = Path(criterion_dir) / 'type_parsing'
    if type_parsing_dir.exists():
        for bench_name in file_metadata.keys():
            bench_dir = type_parsing_dir / bench_name / 'new'
            if not bench_dir.exists():
                bench_dir = type_parsing_dir / bench_name / 'base'

            if bench_dir.exists() and (bench_dir / 'estimates.json').exists():
                est = read_estimates(bench_dir / 'estimates.json')
                meta = file_metadata[bench_name]

                # Extract mean time in microseconds
                mean_time_ns = est['mean']['point_estimate']
                mean_time_us = mean_time_ns / 1000.0

                # Calculate throughput
                throughput_mib_s = (meta['bytes'] / (1024 * 1024)) / (mean_time_ns / 1e9)
                lines_per_second = meta['lines'] / (mean_time_ns / 1e9)

                data = {
                    'lines': meta['lines'],
                    'bytes': meta['bytes'],
                    'time_us': round(mean_time_us, 2),
                    'throughput_mib_s': round(throughput_mib_s, 2),
                    'lines_per_second': int(lines_per_second)
                }

                # Categorize by file size
                if meta['lines'] < 100:
                    results['parsing_speed']['small_files'][bench_name] = data
                elif meta['lines'] < 1000:
                    results['parsing_speed']['medium_files'][bench_name] = data
                else:
                    results['parsing_speed']['large_files'][bench_name] = data

    # Calculate averages
    for category in ['small_files', 'medium_files', 'large_files']:
        files = results['parsing_speed'][category]
        if files:
            avg_throughput = sum(f['throughput_mib_s'] for f in files.values()) / len(files)
            avg_lines = sum(f['lines_per_second'] for f in files.values()) / len(files)
            results['parsing_speed'][category + '_avg'] = {
                'throughput_mib_s': round(avg_throughput, 2),
                'lines_per_second': int(avg_lines)
            }

    # Overall average
    all_files = []
    for category in ['small_files', 'medium_files', 'large_files']:
        all_files.extend(results['parsing_speed'][category].values())
    if all_files:
        results['parsing_speed']['averages'] = {
            'overall_avg_throughput_mib_s': round(sum(f['throughput_mib_s'] for f in all_files) / len(all_files), 2),
            'overall_avg_lines_per_second': int(sum(f['lines_per_second'] for f in all_files) / len(all_files))
        }

    # Parse feature benchmarks
    features_dir = Path(criterion_dir) / 'type_features'
    if features_dir.exists():
        for bench_dir in features_dir.iterdir():
            if bench_dir.is_dir():
                est_file = bench_dir / 'new' / 'estimates.json'
                if not est_file.exists():
                    est_file = bench_dir / 'base' / 'estimates.json'

                if est_file.exists():
                    est = read_estimates(est_file)
                    mean_time_ns = est['mean']['point_estimate']
                    mean_time_us = mean_time_ns / 1000.0
                    results['feature_benchmarks'][bench_dir.name] = {
                        'time_us': round(mean_time_us, 2)
                    }

    # Parse real world patterns
    patterns_dir = Path(criterion_dir) / 'real_world_patterns'
    if patterns_dir.exists():
        for bench_dir in patterns_dir.iterdir():
            if bench_dir.is_dir():
                est_file = bench_dir / 'new' / 'estimates.json'
                if not est_file.exists():
                    est_file = bench_dir / 'base' / 'estimates.json'

                if est_file.exists():
                    est = read_estimates(est_file)
                    mean_time_ns = est['mean']['point_estimate']
                    mean_time_us = mean_time_ns / 1000.0
                    results['real_world_patterns'][bench_dir.name] = {
                        'time_us': round(mean_time_us, 2)
                    }

    # Parse stress tests
    stress_dir = Path(criterion_dir) / 'stress_test'
    if stress_dir.exists():
        for bench_dir in stress_dir.iterdir():
            if bench_dir.is_dir():
                est_file = bench_dir / 'new' / 'estimates.json'
                if not est_file.exists():
                    est_file = bench_dir / 'base' / 'estimates.json'

                if est_file.exists():
                    est = read_estimates(est_file)
                    mean_time_ns = est['mean']['point_estimate']
                    mean_time_us = mean_time_ns / 1000.0
                    results['stress_test'][bench_dir.name] = {
                        'time_us': round(mean_time_us, 2)
                    }

    return results

def generate_baseline_json(criterion_dir, output_file):
    """Generate baseline-performance.json."""
    results = analyze_criterion_results(criterion_dir)

    baseline = {
        'benchmark_date': datetime.now().strftime('%Y-%m-%d'),
        'git_commit': get_git_commit(),
        'rust_version': 'unknown',
        'cpu': 'unknown',
        'memory': 'unknown',
        'parsing_speed': results['parsing_speed'],
        'feature_benchmarks': results['feature_benchmarks'],
        'real_world_patterns': results['real_world_patterns'],
        'stress_test': results['stress_test'],
        'memory_usage': {
            'note': 'Memory profiling tools not available in environment',
            'estimated_small_file_mb': 'N/A',
            'estimated_medium_file_mb': 'N/A',
            'estimated_large_file_mb': 'N/A'
        },
        'profiling_insights': {
            'note': 'Flamegraph profiling requires perf which is not available',
            'top_functions_by_time': [],
            'recommendation': 'Install perf and run: cargo flamegraph --bench baseline_performance'
        },
        'bottlenecks_identified': [
            {
                'location': 'Performance analysis',
                'note': 'Detailed profiling requires perf/flamegraph',
                'recommendation': 'Run flamegraph in environment with perf support'
            }
        ],
        'comparison_with_others': {
            'note': 'Comparison parsers (tsc, oxc, swc) not available in environment',
            'ecma_rs_baseline': 'Established for future comparison'
        }
    }

    # Try to get Rust version
    try:
        result = subprocess.run(
            ['rustc', '--version'],
            capture_output=True,
            text=True,
            check=True
        )
        baseline['rust_version'] = result.stdout.strip()
    except:
        pass

    with open(output_file, 'w') as f:
        json.dump(baseline, f, indent=2)

    print(f"Generated {output_file}")
    return baseline

if __name__ == '__main__':
    import sys

    if len(sys.argv) != 3:
        print("Usage: analyze_benchmarks.py <criterion_dir> <output_file>")
        sys.exit(1)

    criterion_dir = sys.argv[1]
    output_file = sys.argv[2]

    generate_baseline_json(criterion_dir, output_file)
