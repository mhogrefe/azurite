/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzPolynomial.FastMul
import Azurite.AzPolynomial.DistinctDegreeFactorization
import Azurite.AzNat.Pow
import Azurite.Benchmark.Common

open Azurite Azurite.AzPolynomial Azurite.Benchmark

/-!
# Polynomial multiplication over `ℤ/m`: Kronecker substitution against Karatsuba

`benchmark poly_kronecker <iters>` times, for coefficients of several sizes and factors of
several lengths, the Kronecker product (`mulKronecker` over `AzZMod m`, `mulKroneckerInt`,
`mulKroneckerNat`), Karatsuba and the schoolbook `mulBasecaseFold` on the same pairs.
Microseconds per product.  `"nozmod:1"` skips the `AzZMod` part, `"maxlen:L"` bounds the
lengths.
-/

namespace Azurite.Benchmark.PolyKronecker

def us (ns : UInt64) : String :=
  let m := ns / 1000
  let f := (ns / 10) % 100
  s!"{m}.{if f < 10 then "0" else ""}{f}"

/-- A deterministic polynomial with `len` coefficients modulo `m`. -/
def testPoly (m : AzNat) [NeZero m.toNat] (len seed : Nat) : AzPolynomial (AzZMod m) :=
  let big := AzNat.pow (AzNat.ofNat (1000003 + seed)) (m.size / 16 + 3)
  normalize <| (Array.range len).map fun i =>
    AzZMod.ofAzNat m (big * AzNat.ofNat (i * i + 7 * i + 11 + seed) + AzNat.ofNat (i + 1))

/-- Time one multiplication routine over all the pairs; nanoseconds per product.  Every call
has its own operands, so that the compiler cannot share the calls. -/
@[noinline]
def timePairs {R : Type} [Semiring R] [DecidableEq R]
    (f : AzPolynomial R → AzPolynomial R → AzPolynomial R)
    (pairs : Array (AzPolynomial R × AzPolynomial R)) : IO (UInt64 × Nat) := do
  let t0 ← monoNanos
  let mut sum := 0
  for (p, q) in pairs do
    sum := sum + (f p q).coeffs.size
  let t1 ← monoNanos
  return ((t1 - t0) / pairs.size.toUInt64, sum)

/-- A deterministic polynomial with `len` natural coefficients of about `bits` bits. -/
def testNat (bits len seed : Nat) : AzPolynomial AzNat :=
  let big := AzNat.pow (AzNat.ofNat (1000003 + seed)) (bits / 20 + 1)
  let m := AzNat.pow (AzNat.ofNat 2) bits - AzNat.ofNat 3
  normalize <| (Array.range len).map fun i =>
    (big * AzNat.ofNat (i * i + 7 * i + 11 + seed) + AzNat.ofNat (i + 1)) % m

/-- The same with signs. -/
def testInt (bits len seed : Nat) : AzPolynomial AzInt :=
  normalize <| (testNat bits len seed).coeffs.mapIdx fun i c =>
    if (i + seed) % 3 == 0 then -c.toAzInt else c.toAzInt

def lens : List Nat := [2, 3, 4, 6, 8, 12, 16, 24, 32, 64, 128, 256]

def report {R : Type} [Semiring R] [DecidableEq R] (len : Nat)
    (fs : List (AzPolynomial R → AzPolynomial R → AzPolynomial R))
    (pairs : Array (AzPolynomial R × AzPolynomial R)) : IO Unit := do
  let mut out : List String := []
  let mut sums : List Nat := []
  for f in fs do
    let (t, s) ← timePairs f pairs
    let (t', _) ← timePairs f pairs
    out := out ++ [us (min t t')]
    sums := sums ++ [s]
  IO.println s!"   len {len}: {" / ".intercalate out}  ({sums.all (· == sums.head!)})"

def run (limit : Nat) (cfg : Std.HashMap String String) : IO Unit := do
  let iters := max limit 1
  let maxLen := configGetNat cfg "maxlen" 256
  let reps (len bits : Nat) : Nat :=
    min 2000 (max 2 (iters * 4096 / (len * len * (bits / 64 + 1))))
  if !cfg.contains "nozmod" then
    for bits in [20, 60, 120, 250, 500, 1000, 2000] do
      let m := AzNat.pow (AzNat.ofNat 2) bits - AzNat.ofNat 3
      if h : m.toNat ≠ 0 then
        have : NeZero m.toNat := ⟨h⟩
        IO.println s!"modulus {bits} bits (µs: kronecker / karatsuba 8 / schoolbook)"
        for len in lens do
          if len > maxLen then continue
          let pairs := (Array.range (reps len bits)).map fun r =>
            (testPoly m len (2 * r + 1), testPoly m len (2 * r + 2))
          report len [mulKronecker, mulKaratsubaWithThreshold 8, mulBasecaseFold] pairs
  for bits in [20, 60, 120, 250, 1000] do
    IO.println s!"AzInt, {bits}-bit coefficients (µs: kronecker / karatsuba 29 / schoolbook)"
    for len in lens do
      if len > maxLen then continue
      let pairs := (Array.range (reps len bits)).map fun r =>
        (testInt bits len (2 * r + 1), testInt bits len (2 * r + 2))
      report len [mulKroneckerInt, mulKaratsubaWithThreshold 29, mulBasecaseFold] pairs
  for bits in [20, 60, 120, 250, 1000] do
    IO.println s!"AzNat, {bits}-bit coefficients (µs: kronecker / schoolbook)"
    for len in lens do
      if len > maxLen then continue
      let pairs := (Array.range (reps len bits)).map fun r =>
        (testNat bits len (2 * r + 1), testNat bits len (2 * r + 2))
      report len [mulKroneckerNat, mulBasecaseFold] pairs

/-! ### The default product against the schoolbook one, through generic code

`benchmark poly_default <iters>` runs code that is generic in the coefficient ring with the
multiplication config of the coefficient type and with `.basecase` (what every product in
the library was before 2026-11-24): `*`, `pow`, and `powModByMonic` (the power in
`AzPolyMod`, the core of the finite field factorization). -/

def timeOne {α : Type} (f : Unit → α) : IO (α × UInt64) := timeNsIter 1 f

def runDefault (limit : Nat) (_cfg : Std.HashMap String String) : IO Unit := do
  let iters := max limit 1
  -- AzInt: product and fifth power
  IO.println "AzInt, 60-bit coefficients (µs: default / schoolbook)"
  for len in [8, 16, 32, 64, 128, 256] do
    let reps := min 500 (max 2 (iters * 4096 / (len * len)))
    let pairs := (Array.range reps).map fun r =>
      (testInt 60 len (2 * r + 1), testInt 60 len (2 * r + 2))
    report len [(· * ·), @AzPolynomial.mul AzInt _ _ .basecase] pairs
  IO.println "AzInt, 60-bit coefficients, p^5 (µs: default / schoolbook)"
  for len in [8, 32, 128] do
    let reps := min 100 (max 2 (iters * 1024 / (len * len)))
    let pairs := (Array.range reps).map fun r =>
      (testInt 60 len (2 * r + 1), testInt 60 len (2 * r + 2))
    report len [fun p _ => AzPolynomial.pow p 5,
      fun p _ => @AzPolynomial.pow AzInt _ _ .basecase p 5] pairs
  -- AzZMod: the power in the quotient ring
  for bits in [60, 250] do
    let m := AzNat.pow (AzNat.ofNat 2) bits - AzNat.ofNat 3
    if h : m.toNat ≠ 0 then
      have : NeZero m.toNat := ⟨h⟩
      IO.println s!"AzZMod, {bits}-bit modulus: x^(m) modulo a monic f (ms: default / schoolbook)"
      for d in [4, 8, 12, 16, 24, 32, 64, 128] do
        let f : AzPolynomial (AzZMod m) := AzPolynomial.monomial d 1 + testPoly m d 7
        let a : AzPolynomial (AzZMod m) := testPoly m d 3
        if _cfg.contains "parts" then
          -- one product and its reduction, piece by piece
          let b : AzPolynomial (AzZMod m) := testPoly m d 5
          let (ab, tP) ← timeOne fun _ => a * b
          let (r0, t0) ← timeOne fun _ => (divModByMonic ab f).2
          let (r1, t1) ← timeOne fun _ => modByMonic (ab + 0) f
          let (r2, t2) ← timeOne fun _ => modByMonicFast (ab + 0 + 0) f
          IO.println s!"   deg {d}: product {us tP}µs, divModByMonic.2 {us t0}µs, modByMonic {
            us t1}µs, modByMonicFast {us t2}µs  ({decide (r0 = r1) && decide (r1 = r2)})"
          let (_, t3) ← timeOne fun _ => (AzPolyMod.ofPoly (f := f) (ab + 0 + 0 + 0)).val
          let x : AzPolyMod f := AzPolyMod.ofPoly a
          let y : AzPolyMod f := AzPolyMod.ofPoly b
          let (_, t4) ← timeOne fun _ => (x * y).val
          let (_, t5) ← timeOne fun _ => (y * y).val
          let (_, t6) ← timeOne fun _ => (y ^ (AzNat.ofNat 2)).val
          let (_, t7) ← timeOne fun _ => (y ^ (AzNat.ofNat 1024)).val
          IO.println s!"      ofPoly {us t3}µs, x*y {us t4}µs, square {us t5}µs, y^2 {
            us t6}µs, y^1024 {us t7}µs"
          -- the power: plain (in-place reduction) against the precomputed inverse, whatever
          -- the threshold says
          let (g, tG) ← timeOne fun _ => AzPolynomial.invRev f
          let (p1, t8) ← timeOne fun _ => (Azurite.slidingWindowPowAzNat y m).val
          let (p2, t9) ← timeOne fun _ =>
            (@Azurite.slidingWindowPowAzNat (AzPolyMod f) ⟨AzPolyMod.mulInv g⟩ _
              (@instSquare _ ⟨AzPolyMod.mulInv g⟩) y m).val
          let (_, t10) ← timeOne fun _ => (AzPolyMod.mulInv g x y).val
          IO.println s!"      power: plain {us (t8 / 1000)}ms, by inverse {us (t9 / 1000)}ms ({
            decide (p1 = p2)}); invRev {us tG}µs, one mulInv {us t10}µs"
          continue
        let (r1, t1) ← timeOne fun _ => powModByMonic a m f
        let (r2, t2) ← timeOne fun _ =>
          @powModByMonic (AzZMod m) _ _ .basecase a (m + 1 - 1) f
        IO.println
          s!"   deg {d}: {us (t1 / 1000)} / {us (t2 / 1000)}  ({decide (r1 = r2)})"

end Azurite.Benchmark.PolyKronecker
