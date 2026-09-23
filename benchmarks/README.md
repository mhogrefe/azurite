# Benchmarks

Each benchmark is described by a `<name>.toml` configuration in this directory.
Running it produces `<name>.txt` (the raw measurements, with a `#`-prefixed
metadata header recording the command, date and machine) and `<name>.svg` (the
chart; some benchmarks also emit a `<name>_heatmap.svg`). All three are
committed so results can be compared across changes without re-running.

## Running a benchmark

The Lean side is the `benchmark` executable (`Azurite/Benchmark/Main.lean`);
the Rust crate in `../benchmark-charts` drives it from a configuration and
renders the chart.

```bash
lake build benchmark                       # once, from the repository root
cd benchmark-charts
cargo run --release -- run ../benchmarks/az_nat_mul_vs_nat.toml
cargo run --release -- run --reuse ../benchmarks/az_nat_mul_vs_nat.toml   # re-render from the existing .txt
```

`run` spawns `lake env .lake/build/bin/benchmark <benchmark> <limit> <params>`
in the repository root, streams its output with a progress bar, and writes the
`.txt` and `.svg` next to the configuration.

A configuration looks like:

```toml
benchmark = "az_nat_mul_vs_nat"   # name understood by the benchmark executable
limit     = 10000                 # number of inputs
title     = "az_nat_mul_vs_nat: Nat (GMP) vs AzNat"
x_label   = "Input size (significant_bits of a + b)"

[params]                          # passed to the executable as key:value
meanBitLength = 4096
iters         = 100
```

The executable can also be run directly, which prints the raw measurements to
stdout:

```bash
lake env .lake/build/bin/benchmark <name> <limit> [key:value,...]
lake env .lake/build/bin/benchmark            # lists the valid names
```

The legacy chart flow `benchmark-charts <name> <input.txt> [output.svg]`
renders a chart from an existing measurement file.

## Other files

- `aprcl_timings.txt`: hand-recorded timings of the APR-CL primality test
  (`benchmark aprcl <limit> "digits:D|paper:180|paper:247,..."`), kept as a
  running log rather than a chart.
- `archive/legacy_charts/`: charts from an earlier, pre-configuration workflow,
  kept for reference.

Timings depend on the machine and on what else is running; keep the machine
quiet when measuring, and record the machine in the metadata header.
