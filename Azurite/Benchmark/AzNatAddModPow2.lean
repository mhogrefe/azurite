/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Random.NatGen
import Azurite.Random.Pair
import Azurite.AzNat.AddModPow2
import Azurite.AzNat.Equiv.AddModPow2
import Azurite.AzNat.ModPow2
import Azurite.AzNat.Add
import Azurite.AzNat.Equiv.Basic
import Azurite.Benchmark.Common

open Azurite Azurite.Random Azurite.Benchmark

-- ── Input-size metric ───────────────────────────────────────────────────────

/-- Significant bits of a `Nat` (`log2 n + 1`, with `0 ↦ 0`). -/
def natSignificantBitsAMP (n : Nat) : Nat :=
  if n = 0 then 0 else n.log2 + 1

-- ── Benchmark ───────────────────────────────────────────────────────────────

/--
Run the `az_nat_add_mod_pow2` benchmark: fused add-and-mask vs. the naive
"add then mask".

For each of `limit` pairs `(a, b)` of random `Nat`s (geometric bit-length
distribution of mean `meanBitLength`), set `k = max (sigbits a) (sigbits b)` so
both operands are `k`-bit residues, then time on `AzNat`:
  - `addModPow2 a' b' k`           (fused single-pass low-`L` add-and-mask)
  - `modPow2 (a' + b') k`          (full `AzNat.add`, possibly appending a carry
                                    limb, then a separate masking pass)

Output format (one line per pair):
  `<k>;Fused,<ns>;Naive,<ns>`
where `<k>` is the modulus bit-width.
-/
def runAzNatAddModPow2 (limit : Nat) (cfg : Std.HashMap String String) (seed : UInt64) : IO Unit := do
  let meanBitLength := configGetRat cfg "meanBitLength" 256
  let iters := configGetNat cfg "iters" 1000
  let gen := mkPairRandomGenFromSingle (α := Nat) (mkNatRandomGen meanBitLength seed)
  let mut g := gen
  for _ in List.range limit do
    let ((a, b), g') := PairRandomGenFromSingle.next g
    let azA := Azurite.AzNat.ofNat a
    let azB := Azurite.AzNat.ofNat b
    let k := max (natSignificantBitsAMP a) (natSignificantBitsAMP b)
    -- Fused add-and-mask
    let (rFused, ns1a) ← timeNsIter iters (fun _ => Azurite.AzNat.addModPow2 azA azB k)
    let (_,      ns1b) ← timeNsIter iters (fun _ => Azurite.AzNat.addModPow2 azA azB k)
    let (_,      ns1c) ← timeNsIter iters (fun _ => Azurite.AzNat.addModPow2 azA azB k)
    let ns1 := median3 ns1a ns1b ns1c
    -- Naive add then mask
    let (rNaive, ns2a) ← timeNsIter iters (fun _ => Azurite.AzNat.modPow2 (azA + azB) k)
    let (_,      ns2b) ← timeNsIter iters (fun _ => Azurite.AzNat.modPow2 (azA + azB) k)
    let (_,      ns2c) ← timeNsIter iters (fun _ => Azurite.AzNat.modPow2 (azA + azB) k)
    let ns2 := median3 ns2a ns2b ns2c
    -- Sanity check: both must equal `(a + b) % 2^k`.
    let spec := (a + b) % 2 ^ k
    if Azurite.AzNat.toNat rFused ≠ spec then
      IO.eprintln s!"BUG: addModPow2 disagrees with spec for a={a}, b={b}, k={k}"
    if Azurite.AzNat.toNat rNaive ≠ spec then
      IO.eprintln s!"BUG: modPow2 (a+b) disagrees with spec for a={a}, b={b}, k={k}"
    IO.println s!"{k};Fused,{ns1};Naive,{ns2}"
    g := g'
