# Profiling Data

## Status: Limited (Environment Constraints)

This directory would normally contain flamegraphs, memory profiles, and detailed performance analysis data. However, the required profiling tools are not available in the current environment.

## Missing Tools

### Flamegraph (Requires `perf`)

**Tool**: `cargo flamegraph`
**Requirement**: Linux `perf` command
**Status**: ❌ Not available

To generate flamegraph in a proper environment:

```bash
# Install perf
sudo apt-get install linux-tools-generic

# Generate flamegraph
cd parse-js
cargo flamegraph --bench baseline_performance -- --bench

# Output: flamegraph.svg
```

### Memory Profiling (Requires `valgrind` or `cargo-instruments`)

**Tools**:
- Linux: `valgrind --tool=massif`
- macOS: `cargo instruments -t Allocations`

**Status**: ❌ Not available

To profile memory in a proper environment:

```bash
# Linux - valgrind massif
valgrind --tool=massif \
    --massif-out-file=massif.out \
    cargo bench --bench baseline_performance

ms_print massif.out > memory_profile.txt

# macOS - Instruments
cargo instruments -t Allocations --bench baseline_performance
```

## Available Data

✅ **Benchmark results**: See ../benchmark-results/
✅ **Performance analysis**: See ../performance-report.md
✅ **Baseline metrics**: See ../baseline-performance.json

## Recommendations

For comprehensive profiling:

1. Run benchmarks in an environment with `perf` support
2. Generate flamegraph to identify hot paths
3. Use memory profiler to analyze allocations
4. Update this directory with actual profiling data
5. Re-analyze performance-report.md with real profiling insights

## Notes

The performance analysis in `performance-report.md` includes:
- Hypotheses about likely bottlenecks
- Recommendations for profiling
- Guidance on optimization priorities

These should be validated with actual profiling data when tools are available.

---

*Environment: Linux container without perf/valgrind*
*Date: 2025-11-20*
