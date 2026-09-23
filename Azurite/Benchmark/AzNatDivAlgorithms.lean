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
Run the `az_nat_div_algorithms` benchmark.

Compares schoolbook division (Algorithm 1.6 of MCA) against
Brent–Zimmermann recursive D&C (Algorithm 1.8 of MCA) by running
`recursiveDivModFast` with two different thresholds:
  - Schoolbook: threshold = 999999 (forces pure schoolbook).
  - Recursive: threshold = configurable (default 32).

Output:
  `<bitsU>,<bitsV>;Schoolbook,<ns>;Recursive,<ns>`

Config keys:
  - `meanDividendBitLength` (Rat, default 32768)
  - `meanDivisorBitLength` (Rat, default 16384).
    The D&C ↔ schoolbook crossover is in the thousands of bits.
  - `iters` (Nat, default 10) — inner-loop iterations per timing sample.
  - `threshold` (Nat, default 32) — `m < threshold` falls back to
    schoolbook inside the recursive path.
-/
def runAzNatDivAlgorithms (limit : Nat) (cfg : Std.HashMap String String)
    (seed : UInt64) : IO Unit := do
  let meanDividendBitLength := configGetRat cfg "meanDividendBitLength" 32768
  let meanDivisorBitLength := configGetRat cfg "meanDivisorBitLength" 16384
  let iters := configGetNat cfg "iters" 10
  let threshold := configGetNat cfg "threshold" 32
  let gen := mkPairRandomGen
    (α := Nat) (β := Nat)
    (mkNatRandomGen meanDividendBitLength)
    (mkPositiveNatRandomGen meanDivisorBitLength)
    seed
  let mut g := gen
  for _ in List.range limit do
    let ((u, v), g') := PairRandomGen.next g
    let azU := Azurite.AzNat.ofNat u
    let azV := Azurite.AzNat.ofNat v
    let bitsU := natSignificantBits u
    let bitsV := natSignificantBits v
    let (rSch, ns1a) ← timeNsIter iters (fun _ => Azurite.AzNat.recursiveDivModFast 999999 azU azV)
    let (_,    ns1b) ← timeNsIter iters (fun _ => Azurite.AzNat.recursiveDivModFast 999999 azU azV)
    let (_,    ns1c) ← timeNsIter iters (fun _ => Azurite.AzNat.recursiveDivModFast 999999 azU azV)
    let ns1 := median3 ns1a ns1b ns1c
    let (rRec, ns2a) ← timeNsIter iters
      (fun _ => Azurite.AzNat.recursiveDivModFast threshold azU azV)
    let (_,    ns2b) ← timeNsIter iters
      (fun _ => Azurite.AzNat.recursiveDivModFast threshold azU azV)
    let (_,    ns2c) ← timeNsIter iters
      (fun _ => Azurite.AzNat.recursiveDivModFast threshold azU azV)
    let ns2 := median3 ns2a ns2b ns2c
    if Azurite.AzNat.toNat rSch.1 ≠ Azurite.AzNat.toNat rRec.1
       ∨ Azurite.AzNat.toNat rSch.2 ≠ Azurite.AzNat.toNat rRec.2 then
      IO.eprintln s!"BUG: schoolbook ≠ recursive for u={u}, v={v}"
    IO.println s!"{bitsU},{bitsV};Schoolbook,{ns1};Recursive,{ns2}"
    g := g'
