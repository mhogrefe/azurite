/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Random.NatGen
import Azurite.AzNat.Mul
import Azurite.AzNat.Square
import Azurite.AzNat.Equiv.Basic
import Azurite.Benchmark.AzNatAdd -- reuse natSignificantBits
import Azurite.Benchmark.Common   -- reuse timeNsIter, median3, configGetRat, configGetNat

open Azurite Azurite.Random Azurite.Benchmark

/--
Run the `az_nat_square_vs_mul` benchmark.
For each of `limit` random `Nat`s (sampled with geometric bit-length
distribution of mean `meanBitLength`), time `a * a` three ways:
  - `mulSchoolbook a a`         — uses `schoolbookMulLimbs` (n² wideMuls)
  - `squareSchoolbook a`        — uses `schoolbookSquareLimbs` (n(n+1)/2 wideMuls)
  - `squareKaratsuba threshold a` — uses `karatsubaSquareLimbs` (asymptotically n^log₂3)

All three are checked against each other at runtime; any disagreement is
reported to stderr.

Output format:
  `<sb>;mulSchoolbook,<ns>;squareSchoolbook,<ns>;squareKaratsuba,<ns>`
where `<sb>` is the significant-bit count of the input `a`.
-/
def runAzNatSquareVsMul (limit : Nat) (cfg : Std.HashMap String String) (seed : UInt64) : IO Unit := do
  let meanBitLength := configGetRat cfg "meanBitLength" 256
  let iters := configGetNat cfg "iters" 100
  let threshold := configGetNat cfg "threshold" 32
  let mut g := mkNatRandomGen meanBitLength seed
  for _ in List.range limit do
    let (a, g') := NatRandomGen.next g
    let azA := Azurite.AzNat.ofNat a
    let sb := natSignificantBits a
    let (rMul, ns1a) ← timeNsIter iters (fun _ => Azurite.AzNat.mulSchoolbook azA azA)
    let (_,    ns1b) ← timeNsIter iters (fun _ => Azurite.AzNat.mulSchoolbook azA azA)
    let (_,    ns1c) ← timeNsIter iters (fun _ => Azurite.AzNat.mulSchoolbook azA azA)
    let ns1 := median3 ns1a ns1b ns1c
    let (rSq, ns2a) ← timeNsIter iters (fun _ => Azurite.AzNat.squareSchoolbook azA)
    let (_,   ns2b) ← timeNsIter iters (fun _ => Azurite.AzNat.squareSchoolbook azA)
    let (_,   ns2c) ← timeNsIter iters (fun _ => Azurite.AzNat.squareSchoolbook azA)
    let ns2 := median3 ns2a ns2b ns2c
    let (rKar, ns3a) ← timeNsIter iters (fun _ => Azurite.AzNat.squareKaratsuba threshold azA)
    let (_,    ns3b) ← timeNsIter iters (fun _ => Azurite.AzNat.squareKaratsuba threshold azA)
    let (_,    ns3c) ← timeNsIter iters (fun _ => Azurite.AzNat.squareKaratsuba threshold azA)
    let ns3 := median3 ns3a ns3b ns3c
    let nMul := Azurite.AzNat.toNat rMul
    if Azurite.AzNat.toNat rSq ≠ nMul then
      IO.eprintln s!"BUG: squareSchoolbook disagrees with mulSchoolbook for a={a}"
    if Azurite.AzNat.toNat rKar ≠ nMul then
      IO.eprintln s!"BUG: squareKaratsuba disagrees with mulSchoolbook for a={a}"
    IO.println s!"{sb};mulSchoolbook,{ns1};squareSchoolbook,{ns2};squareKaratsuba,{ns3}"
    g := g'
