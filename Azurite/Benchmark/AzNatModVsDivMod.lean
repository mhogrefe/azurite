/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Random.NatGen
import Azurite.Random.Pair
import Azurite.AzNat.Div
import Azurite.AzNat.Equiv.Basic
import Azurite.Benchmark.AzNatAdd -- reuse natSignificantBits
import Azurite.Benchmark.Common -- reuse timeNsIter, median3, configGetRat, configGetNat

open Azurite Azurite.Random Azurite.Benchmark

/--
Run the `az_nat_mod_vs_div_mod` benchmark.
For each of `limit` pairs `(U, V)` of random `Nat`s (independently seeded so
the dividend and divisor are uncorrelated, both at mean bit length
`meanBitLength`), time:
  - `U % V`        — the specialised `mod` (skips quotient assembly).
  - `U.divMod V`   — the full divMod that produces both quotient and remainder.

The expected gap is the quotient-side `ofLimbs` assembly the specialised
mod skips: `ofLimbs #[qr.1]` in the 1-limb branch, `ofLimbs res.1` in the
n=2 branch, and `extract n (n+m) ++ #[res.2]` plus `ofLimbs` in the n ≥ 3
branch.

Output format (one line per pair):
  `<sb>;Mod,<ns>;DivMod,<ns>`
where `<sb> = sigBits U + sigBits V`.

Config keys:
  - `meanBitLength` (Rat, default 8192) — geometric mean of dividend and
    divisor bit length.  Larger than `az_nat_div_mod`'s 256 so the
    quotient-assembly savings are measurable.
  - `iters` (Nat, default 100) — inner-loop iterations per timing sample.
-/
def runAzNatModVsDivMod (limit : Nat) (cfg : Std.HashMap String String)
    (seed : UInt64) : IO Unit := do
  let meanBitLength := configGetRat cfg "meanBitLength" 8192
  let iters := configGetNat cfg "iters" 100
  let gen := mkPairRandomGen
    (α := Nat) (β := Nat)
    (mkNatRandomGen meanBitLength)
    (mkPositiveNatRandomGen meanBitLength)
    seed
  let mut g := gen
  for _ in List.range limit do
    let ((u, v), g') := PairRandomGen.next g
    let azU := Azurite.AzNat.ofNat u
    let azV := Azurite.AzNat.ofNat v
    let sb := natSignificantBits u + natSignificantBits v
    -- Specialised mod
    let (rMod, ns1a) ← timeNsIter iters (fun _ => azU % azV)
    let (_,    ns1b) ← timeNsIter iters (fun _ => azU % azV)
    let (_,    ns1c) ← timeNsIter iters (fun _ => azU % azV)
    let ns1 := median3 ns1a ns1b ns1c
    -- Full divMod
    let (rDivMod, ns2a) ← timeNsIter iters (fun _ => azU.divMod azV)
    let (_,       ns2b) ← timeNsIter iters (fun _ => azU.divMod azV)
    let (_,       ns2c) ← timeNsIter iters (fun _ => azU.divMod azV)
    let ns2 := median3 ns2a ns2b ns2c
    -- Sanity: the specialised mod should agree with the projected divMod.
    if Azurite.AzNat.toNat rMod ≠ Azurite.AzNat.toNat rDivMod.2 then
      IO.eprintln s!"BUG: mod disagrees with divMod.2 for u={u}, v={v}"
    IO.println s!"{sb};Mod,{ns1};DivMod,{ns2}"
    g := g'
