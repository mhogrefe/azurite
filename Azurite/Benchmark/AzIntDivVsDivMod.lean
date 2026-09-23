/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Random.Int
import Azurite.Random.Pair
import Azurite.AzInt.DivMod
import Azurite.AzInt.Equiv.Basic
import Azurite.Benchmark.AzNatAdd -- reuse natSignificantBits
import Azurite.Benchmark.Common -- reuse timeNsIter, median3, configGetRat, configGetNat

open Azurite Azurite.Random Azurite.Benchmark

/--
Run the `az_int_div_vs_div_mod` benchmark.
For each of `limit` pairs `(a, b)` of random nonzero `Int`s (signs and
magnitudes independently sampled, both at mean magnitude `meanBitLength`),
time:
  - `a / b`         — the specialised `ediv` (skips remainder-side AzInt
                       construction in each branch).
  - `a.edivMod b`   — the full `edivMod` that builds both halves of the
                       AzInt pair.

The expected gap is the AzInt-level construction the specialised `ediv`
skips: `r'.toAzInt` / `mkNorm a.sign r'` / `mkNonzero a.sign r'` in the
first three branches, and the `b.abs - r'` multi-limb subtraction plus
`mkNonzero true (...)` wrap in the trickiest "increment-quotient"
branch.  The underlying `AzNat.divMod` call is unchanged.

Output format (one line per pair):
  `<sb>;Div,<ns>;DivMod,<ns>`
where `<sb> = sigBits |a| + sigBits |b|`.

Config keys:
  - `meanBitLength` (Rat, default 8192) — geometric mean of dividend and
    divisor magnitude.  Large enough that the multi-limb `b.abs - r'`
    subtraction in branch 4 is measurable.
  - `iters` (Nat, default 100) — inner-loop iterations per timing sample.
-/
def runAzIntDivVsDivMod (limit : Nat) (cfg : Std.HashMap String String)
    (seed : UInt64) : IO Unit := do
  let meanBitLength := configGetRat cfg "meanBitLength" 8192
  let iters := configGetNat cfg "iters" 100
  let gen := mkPairRandomGen
    (α := Int) (β := Int)
    (mkIntRandomGen meanBitLength)
    (mkNonzeroIntRandomGen meanBitLength)
    seed
  let mut g := gen
  for _ in List.range limit do
    let ((a, b), g') := PairRandomGen.next g
    let azA := Azurite.AzInt.ofInt a
    let azB := Azurite.AzInt.ofInt b
    let sb := natSignificantBits a.natAbs + natSignificantBits b.natAbs
    -- Specialised ediv (via `/`)
    let (rDiv, ns1a) ← timeNsIter iters (fun _ => azA / azB)
    let (_,    ns1b) ← timeNsIter iters (fun _ => azA / azB)
    let (_,    ns1c) ← timeNsIter iters (fun _ => azA / azB)
    let ns1 := median3 ns1a ns1b ns1c
    -- Full edivMod
    let (rDivMod, ns2a) ← timeNsIter iters (fun _ => azA.edivMod azB)
    let (_,       ns2b) ← timeNsIter iters (fun _ => azA.edivMod azB)
    let (_,       ns2c) ← timeNsIter iters (fun _ => azA.edivMod azB)
    let ns2 := median3 ns2a ns2b ns2c
    -- Sanity: the specialised ediv should agree with edivMod.1.
    if Azurite.AzInt.toInt rDiv ≠ Azurite.AzInt.toInt rDivMod.1 then
      IO.eprintln s!"BUG: ediv disagrees with edivMod.1 for a={a}, b={b}"
    IO.println s!"{sb};Div,{ns1};DivMod,{ns2}"
    g := g'
