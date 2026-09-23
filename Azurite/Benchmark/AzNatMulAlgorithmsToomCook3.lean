/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Random.NatGen
import Azurite.Random.Pair
import Azurite.AzNat.Mul
import Azurite.AzNat.Equiv.Basic
import Azurite.Benchmark.AzNatAdd -- reuse natSignificantBits
import Azurite.Benchmark.Common -- reuse timeNsIter, median3, configGetRat, configGetNat

open Azurite Azurite.Random Azurite.Benchmark

/--
Run the `az_nat_mul_algorithms_toomcook3` benchmark.
For each of `limit` pairs `(a, b)` of random `Nat`s (sampled with geometric
bit-length distribution of mean `meanBitLength`), time:
  - `mulKaratsuba karatsubaThreshold` (O(n^1.585) once `len ≥ karatsubaThreshold`)
  - `mulToomCook3 toomCook3Threshold` (O(n^log₃5 ≈ 1.46) once `len ≥ toomCook3Threshold`,
    falling back to `mulKaratsuba` below)

Both operate on the same `AzNat` values; both pad the shorter limb array with
high zero limbs so the slices have equal length.

Output format (one line per pair):
  `<bitsA>,<bitsB>;Karatsuba,<ns>;ToomCook3,<ns>`
where `<bitsA>`, `<bitsB>` are the significant bits of `a` and `b`. The
chart driver can derive the sum as needed for line plots, or use the pair
as coordinates for a 2-D heatmap.

Config keys:
  - `meanBitLength` (Rat, default 262144) — geometric mean of operand bit length.
    Higher than `az_nat_mul_algorithms` since the Karatsuba ↔ ToomCook3 crossover
    only matters at large sizes.
  - `iters` (Nat, default 10) — inner-loop iterations per timing sample (lower
    than schoolbook-comparison defaults since each call is far more expensive).
  - `karatsubaThreshold` (Nat, default 16) — Karatsuba schoolbook fallback (tuned).
  - `toomCook3Threshold` (Nat, default 32) — Toom-Cook 3 fallback to Karatsuba.
-/
def runAzNatMulAlgorithmsToomCook3 (limit : Nat) (cfg : Std.HashMap String String)
    (seed : UInt64) : IO Unit := do
  let meanBitLength := configGetRat cfg "meanBitLength" 262144
  let iters := configGetNat cfg "iters" 10
  let karatsubaThreshold := configGetNat cfg "karatsubaThreshold" 16
  let toomCook3Threshold := configGetNat cfg "toomCook3Threshold" 32
  let gen := mkPairRandomGenFromSingle (α := Nat) (mkNatRandomGen meanBitLength seed)
  let mut g := gen
  for _ in List.range limit do
    let ((a, b), g') := PairRandomGenFromSingle.next g
    let azA := Azurite.AzNat.ofNat a
    let azB := Azurite.AzNat.ofNat b
    let bitsA := natSignificantBits a
    let bitsB := natSignificantBits b
    -- Karatsuba
    let (rKar, ns1a) ← timeNsIter iters (fun _ => Azurite.AzNat.mulKaratsuba karatsubaThreshold azA azB)
    let (_,    ns1b) ← timeNsIter iters (fun _ => Azurite.AzNat.mulKaratsuba karatsubaThreshold azA azB)
    let (_,    ns1c) ← timeNsIter iters (fun _ => Azurite.AzNat.mulKaratsuba karatsubaThreshold azA azB)
    let ns1 := median3 ns1a ns1b ns1c
    -- Toom-Cook 3
    let (rToom, ns2a) ← timeNsIter iters (fun _ => Azurite.AzNat.mulToomCook3 toomCook3Threshold karatsubaThreshold azA azB)
    let (_,     ns2b) ← timeNsIter iters (fun _ => Azurite.AzNat.mulToomCook3 toomCook3Threshold karatsubaThreshold azA azB)
    let (_,     ns2c) ← timeNsIter iters (fun _ => Azurite.AzNat.mulToomCook3 toomCook3Threshold karatsubaThreshold azA azB)
    let ns2 := median3 ns2a ns2b ns2c
    if Azurite.AzNat.toNat rKar ≠ Azurite.AzNat.toNat rToom then
      IO.eprintln s!"BUG: karatsuba ≠ toomCook3 for a={a}, b={b}"
    IO.println s!"{bitsA},{bitsB};Karatsuba,{ns1};ToomCook3,{ns2}"
    g := g'
