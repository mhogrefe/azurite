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
Run the `az_int_mod_vs_div_mod` benchmark.
For each of `limit` pairs `(a, b)` of random nonzero `Int`s (signs and
magnitudes independently sampled, both at mean magnitude `meanBitLength`),
time:
  - `a % b`         — the specialised `emod` (skips quotient-side AzInt
                       construction in each branch).
  - `a.edivMod b`   — the full `edivMod` that builds both halves of the
                       AzInt pair.

The expected gap is the quotient-side AzInt construction `emod` skips:
`mkNorm (a.sign == b.sign) q'` in the first three branches, and the
`q'.addUInt64 1` + `mkNonzero (!b.sign) ...` wrap in the trickiest
"increment-quotient" branch.  The underlying `AzNat.divMod` call is
unchanged.

Output format (one line per pair):
  `<sb>;Mod,<ns>;DivMod,<ns>`
where `<sb> = sigBits |a| + sigBits |b|`.

Config keys:
  - `meanBitLength` (Rat, default 8192) — geometric mean of dividend and
    divisor magnitude.
  - `iters` (Nat, default 100) — inner-loop iterations per timing sample.
-/
def runAzIntModVsDivMod (limit : Nat) (cfg : Std.HashMap String String)
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
    -- Specialised emod (via `%`)
    let (rMod, ns1a) ← timeNsIter iters (fun _ => azA % azB)
    let (_,    ns1b) ← timeNsIter iters (fun _ => azA % azB)
    let (_,    ns1c) ← timeNsIter iters (fun _ => azA % azB)
    let ns1 := median3 ns1a ns1b ns1c
    -- Full edivMod
    let (rDivMod, ns2a) ← timeNsIter iters (fun _ => azA.edivMod azB)
    let (_,       ns2b) ← timeNsIter iters (fun _ => azA.edivMod azB)
    let (_,       ns2c) ← timeNsIter iters (fun _ => azA.edivMod azB)
    let ns2 := median3 ns2a ns2b ns2c
    -- Sanity: the specialised emod should agree with edivMod.2.
    if Azurite.AzInt.toInt rMod ≠ Azurite.AzInt.toInt rDivMod.2 then
      IO.eprintln s!"BUG: emod disagrees with edivMod.2 for a={a}, b={b}"
    IO.println s!"{sb};Mod,{ns1};DivMod,{ns2}"
    g := g'
