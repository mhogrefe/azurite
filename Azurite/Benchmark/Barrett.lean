/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Div
import Azurite.AzNat.ModPow2
import Azurite.AzNat.Mul
import Azurite.AzNat.MulModPow2.Schoolbook
import Azurite.AzNat.Pow
import Azurite.Benchmark.Common

/-!
# Benchmark: a Barrett reduction against `%`

`benchmark az_nat_barrett 1`: for moduli `V` of `n` limbs and products `x` of two residues
(`2n` limbs), the cost of `x % V` and of a Barrett reduction written with the operations of
`AzNat` (a prototype for this measurement only, not proven; its results are compared with `%`
here): with `μ = ⌊β^(2n) / V⌋` computed once,

  `q = ⌊⌊x / β^(n−1)⌋ μ / β^(n+1)⌋`,  `r = (x − q V) mod β^(n+1)`,  at most two subtractions
  of `V`.

Also the pieces: the shift of `x`, the full high product, the low product modulo `β^(n+1)`
(`mulSchoolbookModPow2`), and twice that low product — about what a reduction with a
schoolbook high short product would cost.  Nanoseconds per operation over 2000 operands.
-/

open Azurite Azurite.Benchmark

namespace Azurite.Benchmark.Barrett

/-- The prototype: `x mod V` for `x < β^(2n)`, `μ = ⌊β^(2n) / V⌋`, `K = β^(n+1)`. -/
@[noinline] def barrett (V μ K : AzNat) (n : Nat) (x : AzNat) : AzNat :=
  let q := ((x >>> (64 * (n - 1))) * μ) >>> (64 * (n + 1))
  let p := AzNat.mulSchoolbookModPow2 q V (64 * (n + 1))
  let xl := x.modPow2 (64 * (n + 1))
  let r := if p ≤ xl then xl - p else xl + K - p
  if r < V then r
  else
    let r1 := r - V
    if r1 < V then r1 else r1 - V

def run (_limit : Nat) (_cfg : Std.HashMap String String) : IO Unit := do
  for n in [2, 3, 4, 6, 8, 16, 32] do
    let V := (AzNat.pow (AzNat.ofNat 2) (64 * n) - AzNat.ofNat 159) >>> 5
    let μ := AzNat.pow (AzNat.ofNat 2) (128 * n) / V
    let K := AzNat.pow (AzNat.ofNat 2) (64 * (n + 1))
    let big := AzNat.pow (AzNat.ofNat 1000003) (7 * n + 3)
    let xs : Array AzNat := (Array.range 2000).map fun i =>
      (big * AzNat.ofNat (i * i + 7 * i + 11) + AzNat.ofNat i) % V
    let ys : Array AzNat := (Array.range 2000).map fun i =>
      (big * AzNat.ofNat (3 * i * i + i + 5) + AzNat.ofNat (2 * i + 1)) % V
    let ps : Array AzNat := (Array.range 2000).map fun i => xs[i]! * ys[i]!
    let qs : Array AzNat := ps.map fun (x : AzNat) =>
      ((x >>> (64 * (n - 1))) * μ) >>> (64 * (n + 1))
    let loop (f : Nat → Nat) : IO UInt64 := do
      let t0 ← IO.monoNanosNow
      let mut s := 0
      for i in [0:2000] do
        s := s + f i
      let t1 ← IO.monoNanosNow
      if s == 0 then IO.println "?"
      return ((t1 - t0) / 2000).toUInt64
    let tMod ← loop fun i => (ps[i]! % V).limbs.size + 1
    let tBar ← loop fun i => (barrett V μ K n ps[i]!).limbs.size + 1
    let tMul ← loop fun i => (xs[i]! * ys[i]!).limbs.size + 1
    let tShift ← loop fun i => (ps[i]! >>> (64 * (n - 1))).limbs.size + 1
    let tHigh ← loop fun i =>
      (((ps[i]! >>> (64 * (n - 1))) * μ) >>> (64 * (n + 1))).limbs.size + 1
    let tLow ← loop fun i =>
      (AzNat.mulSchoolbookModPow2 qs[i]! V (64 * (n + 1))).limbs.size + 1
    let tLow2 ← loop fun i =>
      (AzNat.mulSchoolbookModPow2 qs[i]! V (64 * (n + 1))).limbs.size +
        (AzNat.mulSchoolbookModPow2 xs[i]! μ (64 * (n + 1))).limbs.size + 1
    let tTail ← loop fun i =>
      let xl := ps[i]!.modPow2 (64 * (n + 1))
      let p := qs[i]!
      (if p ≤ xl then xl - p else xl + K - p).limbs.size + 1
    let same := (List.range 2000).all fun i => barrett V μ K n ps[i]! == ps[i]! % V
    let corr := (List.range 2000).foldl (fun (c : Nat × Nat) i =>
      let q := qs[i]!
      let d := (ps[i]! / V - q).toNat
      (if d == 1 then c.1 + 1 else c.1, if d ≥ 2 then c.2 + 1 else c.2)) (0, 0)
    IO.println s!"{n} limbs (ns): mod {tMod}, Barrett {tBar} ({same}; one correction {corr.1}, two {corr.2} of 2000), mul {tMul}; pieces: shift {tShift}, shift + high product + shift {tHigh}, low product {tLow}, two low products {tLow2}, low limbs + subtraction {tTail}"

end Azurite.Benchmark.Barrett
