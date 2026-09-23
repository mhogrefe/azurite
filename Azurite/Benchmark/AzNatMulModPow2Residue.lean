/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Random.Nat
import Azurite.Random.Geometric
import Azurite.Random.Gen
import Azurite.AzNat.MulModPow2.Dispatch
import Azurite.AzNat.Mul
import Azurite.AzNat.ModPow2
import Azurite.AzNat.Equiv.Basic
import Azurite.Benchmark.Common

open Azurite Azurite.Random Azurite.Benchmark

/-!
# `az_nat_mul_mod_pow2_residue`

Size-dispatched low product `AzNat.mulDispatchModPow2 a c k` (the schoolbook,
Karatsuba, or Toom-3 low product, computing only the low `L = ⌈k/64⌉` limbs) vs.
the naive full product then mask `modPow2 (a * c) k` (computes the whole `2L`-limb
product, discards the top half), on full-width `k`-bit residues.
-/

/-- Run the `az_nat_mul_mod_pow2_residue` benchmark.  Both operands are exactly
`b`-bit (`k = b`); times fused `mulDispatchModPow2 a c k` vs `modPow2 (a * c) k`.
Output: `<k>;Fused,<ns>;Naive,<ns>`. -/
def runAzNatMulModPow2Residue (limit : Nat) (cfg : Std.HashMap String String)
    (seed : UInt64) : IO Unit := do
  let meanBitLength := configGetRat cfg "meanBitLength" 4096
  let iters := configGetNat cfg "iters" 50
  let mut geo := mkNatGeometricRandomGen meanBitLength (deriveSeed seed "bitlen")
  let mut sm := mkSplitMix64 (deriveSeed seed "operands")
  for _ in List.range limit do
    let (b0, geo') := NatGeometricRandomGen.next geo
    geo := geo'
    let b := max b0 1
    let bg : NatWithBitsRandomGen SplitMix64 := { gen := sm, b := b }
    let (a, bg1) := NatWithBitsRandomGen.next bg
    let (c, bg2) := NatWithBitsRandomGen.next bg1
    sm := bg2.gen
    let azA := Azurite.AzNat.ofNat a
    let azC := Azurite.AzNat.ofNat c
    let k := b
    -- Fused low product (only the low L limbs)
    let (rFused, ns1a) ← timeNsIter iters (fun _ => Azurite.AzNat.mulDispatchModPow2 azA azC k)
    let (_,      ns1b) ← timeNsIter iters (fun _ => Azurite.AzNat.mulDispatchModPow2 azA azC k)
    let (_,      ns1c) ← timeNsIter iters (fun _ => Azurite.AzNat.mulDispatchModPow2 azA azC k)
    let ns1 := median3 ns1a ns1b ns1c
    -- Naive full product then mask
    let (rNaive, ns2a) ← timeNsIter iters (fun _ => Azurite.AzNat.modPow2 (azA * azC) k)
    let (_,      ns2b) ← timeNsIter iters (fun _ => Azurite.AzNat.modPow2 (azA * azC) k)
    let (_,      ns2c) ← timeNsIter iters (fun _ => Azurite.AzNat.modPow2 (azA * azC) k)
    let ns2 := median3 ns2a ns2b ns2c
    -- Sanity check: both must equal `(a * c) % 2^k`.
    let spec := (a * c) % 2 ^ k
    if Azurite.AzNat.toNat rFused ≠ spec then
      IO.eprintln s!"BUG: mulDispatchModPow2 disagrees with spec for a={a}, c={c}, k={k}"
    if Azurite.AzNat.toNat rNaive ≠ spec then
      IO.eprintln s!"BUG: modPow2 (a*c) disagrees with spec for a={a}, c={c}, k={k}"
    IO.println s!"{k};Fused,{ns1};Naive,{ns2}"
