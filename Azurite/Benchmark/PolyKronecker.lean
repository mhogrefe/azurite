/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzPolynomial.FastMul
import Azurite.AzPolynomial.Equiv.Kronecker
import Azurite.AzPolynomial.DistinctDegreeFactorization
import Azurite.AzNat.Pow
import Azurite.AzNat.Mul.ShortProduct
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

/-- `benchmark poly_kronecker <iters> "split:1"`: the pieces of one Kronecker product over
`AzZMod m` — packing the two factors, the `AzNat` product, reading the blocks back, reducing
them modulo `m` — and the square of the packed number.  Microseconds per product. -/
def runSplit (iters : Nat) : IO Unit := do
  for bits in [60, 120, 250, 500, 1000] do
    let m := AzNat.pow (AzNat.ofNat 2) bits - AzNat.ofNat 3
    if h : m.toNat ≠ 0 then
      have : NeZero m.toNat := ⟨h⟩
      IO.println s!"modulus {bits} bits (µs: whole / pack / product / square / read / reduce)"
      for len in [4, 8, 16, 32, 64, 128] do
        let reps := min 1000 (max 2 (iters * 4096 / (len * len * (bits / 64 + 1))))
        let ps := (Array.range reps).map fun r => testPoly m len (2 * r + 1)
        let qs := (Array.range reps).map fun r => testPoly m len (2 * r + 2)
        let w := kroneckerWidth m (2 * len)
        let loop (f : Nat → Nat) : IO UInt64 := do
          let mut best : UInt64 := 0
          for round in [0:2] do
            let t0 ← monoNanos
            let mut s := 0
            for i in [0:reps] do
              s := s + f i
            let t1 ← monoNanos
            if s == 0 then IO.println "?"
            let t := (t1 - t0) / reps.toUInt64
            best := if round == 0 then t else min best t
          return best
        let tAll ← loop fun i => (mulKronecker ps[i]! qs[i]!).coeffs.size + 1
        let tPack ← loop fun i =>
          (AzNat.kroneckerPack w (ps[i]!.coeffs.map (·.val))).limbs.size +
            (AzNat.kroneckerPack w (qs[i]!.coeffs.map (·.val))).limbs.size + 1
        let as := ps.map fun (p : AzPolynomial (AzZMod m)) =>
          AzNat.kroneckerPack w (p.coeffs.map (·.val))
        let bs := qs.map fun (p : AzPolynomial (AzZMod m)) =>
          AzNat.kroneckerPack w (p.coeffs.map (·.val))
        let tMul ← loop fun i => (as[i]! * bs[i]!).limbs.size + 1
        let tSqr ← loop fun i => (AzNat.square as[i]!).limbs.size + 1
        let xs := (Array.range reps).map fun i => as[i]! * bs[i]!
        let tRead ← loop fun i =>
          (Array.ofFn fun (k : Fin (2 * len - 1)) => AzNat.kroneckerCoeff w xs[i]! k.val).size
        let cs := xs.map fun (x : AzNat) =>
          Array.ofFn fun (k : Fin (2 * len - 1)) => AzNat.kroneckerCoeff w x k.val
        let tRed ← loop fun i =>
          (cs[i]!.map fun (c : AzNat) => c % m).size
        IO.println s!"   len {len} (w = {w}): {us tAll} / {us tPack} / {us tMul} / {us tSqr} / {
          us tRead} / {us tRed}"
        -- the two-point product, piece by piece
        let w2 := (w + 1) / 2
        let tAll2 ← loop fun i => (mulKronecker2 ps[i]! qs[i]!).coeffs.size + 1
        let tEval ← loop fun i =>
          (AzNat.kroneckerEvalPair w2 (ps[i]!.coeffs.map (·.val))).1.limbs.size +
            (AzNat.kroneckerEvalPair w2 (qs[i]!.coeffs.map (·.val))).1.limbs.size + 1
        let tEven ← loop fun i =>
          (AzNat.kroneckerPackEven w2 (ps[i]!.coeffs.map (·.val))).limbs.size + 1
        let tOdd ← loop fun i =>
          (AzNat.kroneckerPackOdd w2 (ps[i]!.coeffs.map (·.val))).limbs.size + 1
        let as2 := ps.map fun (p : AzPolynomial (AzZMod m)) =>
          AzNat.kroneckerEvalPair w2 (p.coeffs.map (·.val))
        let bs2 := qs.map fun (p : AzPolynomial (AzZMod m)) =>
          AzNat.kroneckerEvalPair w2 (p.coeffs.map (·.val))
        let tMul2 ← loop fun i =>
          (as2[i]!.1 * bs2[i]!.1).limbs.size + (as2[i]!.2 * bs2[i]!.2).abs.limbs.size + 1
        let uvs := (Array.range reps).map fun i =>
          (as2[i]!.1 * bs2[i]!.1, as2[i]!.2 * bs2[i]!.2)
        let tHalf ← loop fun i =>
          let h := AzNat.kroneckerHalves uvs[i]!.1 uvs[i]!.2
          h.1.limbs.size + h.2.limbs.size + 1
        let hs := uvs.map fun (uv : AzNat × AzInt) => AzNat.kroneckerHalves uv.1 uv.2
        let tRead2 ← loop fun i =>
          (Array.ofFn fun (k : Fin (2 * len - 1)) =>
            AzNat.kroneckerCoeff2 w2 hs[i]!.1 hs[i]!.2 k.val).size
        IO.println s!"      two points: whole {us tAll2}, both pairs {us tEval} (one even {
          us tEven}, one odd {us tOdd}), products {us tMul2}, halves {us tHalf}, read {us tRead2}"

/-- `benchmark poly_kronecker <iters> "two:1"`: one point against two points, products and
squares.  Microseconds. -/
def runTwo (iters : Nat) : IO Unit := do
  for bits in [20, 30, 60, 64, 100, 120, 128, 190, 250, 500, 1000, 2000] do
    let m := AzNat.pow (AzNat.ofNat 2) bits - AzNat.ofNat 3
    if h : m.toNat ≠ 0 then
      have : NeZero m.toNat := ⟨h⟩
      IO.println s!"modulus {bits} bits (µs: one point / two points / square one / square two)"
      for len in [2, 3, 4, 6, 8, 12, 16, 32, 64, 128, 256] do
        let reps := min 1000 (max 2 (iters * 4096 / (len * len * (bits / 64 + 1))))
        let pairs := (Array.range reps).map fun r =>
          (testPoly m len (2 * r + 1), testPoly m len (2 * r + 2))
        let w := kroneckerWidth m (2 * len)
        IO.print s!"   w = {w}"
        report len [mulKronecker, mulKronecker2, fun p _ => mulKronecker p p,
          fun p _ => mulKronecker2 p p] pairs

/-- `benchmark poly_kronecker <iters> "low:1"`: the low short product `AzNat.mulLow` (thresholds
8, 16, 32, 64) against the full product, for two factors of `n` limbs.  Microseconds. -/
def runLow (iters : Nat) : IO Unit := do
  IO.println "limbs: full product / mulLow 8 / 16 / 32 / 64 (µs)"
  for n in [16, 32, 64, 128, 256, 512, 1024, 2048] do
    let reps := min 500 (max 4 (iters * 20000 / (n * n)))
    let big := AzNat.pow (AzNat.ofNat 1000003) (4 * n)
    let md := AzNat.pow (AzNat.ofNat 2) (64 * n) - AzNat.ofNat 159
    let xs := (Array.range reps).map fun i => (big * AzNat.ofNat (i * i + 7 * i + 11)) % md
    let ys := (Array.range reps).map fun i => (big * AzNat.ofNat (3 * i * i + i + 5)) % md
    let loop (f : Nat → Nat) : IO UInt64 := do
      let mut best : UInt64 := 0
      for round in [0:3] do
        let t0 ← monoNanos
        let mut s := 0
        for i in [0:reps] do
          s := s + f i
        let t1 ← monoNanos
        if s == 0 then IO.println "?"
        let t := (t1 - t0) / reps.toUInt64
        best := if round == 0 then t else min best t
      return best
    let tFull ← loop fun i => (xs[i]! * ys[i]!).limbs.size + 1
    let mut out := s!"   {n}: {us tFull}"
    for n0 in [8, 16, 32, 64] do
      let t ← loop fun i => (AzNat.mulLow n0 xs[i]! ys[i]! n).limbs.size + 1
      out := out ++ s!" / {us t}"
    IO.println out

def run (limit : Nat) (cfg : Std.HashMap String String) : IO Unit := do
  let iters := max limit 1
  if cfg.contains "low" then
    runLow iters
    return
  if cfg.contains "split" then
    runSplit iters
    return
  if cfg.contains "two" then
    runTwo iters
    return
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

/-! ### The product over `AzZMod m` as it was before 2026-11-25, for comparison -/

/-- The Kronecker product before 2026-11-25: one point, every block extracted and reduced by
`%`, no squaring. -/
def mulKroneckerOld {m : AzNat} [NeZero m.toNat] (p q : AzPolynomial (AzZMod m)) :
    AzPolynomial (AzZMod m) :=
  if p.coeffs.size == 0 || q.coeffs.size == 0 then 0
  else
    let w := kroneckerWidth m (p.coeffs.size + q.coeffs.size)
    let x := AzNat.kroneckerPack w (p.coeffs.map (·.val)) *
      AzNat.kroneckerPack w (q.coeffs.map (·.val))
    normalize <| Array.ofFn fun (k : Fin (p.coeffs.size + q.coeffs.size - 1)) =>
      AzZMod.ofAzNat m (AzNat.kroneckerCoeff w x k.val)

theorem mulKroneckerOld_eq {m : AzNat} [NeZero m.toNat] (p q : AzPolynomial (AzZMod m)) :
    mulKroneckerOld p q = mulKronecker p q := by
  unfold mulKroneckerOld mulKronecker
  split
  · rfl
  · dsimp only
    rw [kroneckerRead_eq]
    split
    · next hpq =>
      subst hpq
      have hx : AzNat.kroneckerPack (kroneckerWidth m (p.coeffs.size + p.coeffs.size))
            (p.coeffs.map (·.val)) *
          AzNat.kroneckerPack (kroneckerWidth m (p.coeffs.size + p.coeffs.size))
            (p.coeffs.map (·.val)) =
          AzNat.square (AzNat.kroneckerPack (kroneckerWidth m (p.coeffs.size + p.coeffs.size))
            (p.coeffs.map (·.val))) := by
        apply AzNat.toNat_injective
        rw [AzNat.toNat_square, AzNat.toNat_mul, sq]
      rw [hx]
    · rfl

/-- The multiplication config of `AzZMod m` before 2026-11-25. -/
@[reducible] def configOld {m : AzNat} [NeZero m.toNat] : AzPolynomialMulConfig (AzZMod m) where
  dmul p q :=
    if p.coeffs.size < kroneckerThreshold ∨ q.coeffs.size < kroneckerThreshold then
      mulBasecaseFold p q
    else mulKroneckerOld p q
  dmul_eq p q := by
    split
    · rfl
    · rw [mulKroneckerOld_eq]
      exact eq_mulBasecaseFold_of_toPoly (toPoly_mulKronecker p q)
  invThreshold := some 9

/-! ### The default product against the schoolbook one, through generic code

`benchmark poly_default <iters>` runs code that is generic in the coefficient ring with the
multiplication config of the coefficient type and with `.basecase` (what every product in
the library was before 2026-11-24): `*`, `pow`, and `powModByMonic` (the power in
`AzPolyMod`, the core of the finite field factorization). -/

def timeOne {α : Type} (f : Unit → α) : IO (α × UInt64) := timeNsIter 1 f

/-- A power in `AzPolyMod f`, plain (in-place reduction) against the precomputed inverse
whatever the config's threshold says.  Milliseconds. -/
def cmpPow {R : Type} [CommRing R] [DecidableEq R] [AzPolynomialMulConfig R]
    (label : String) (f : AzPolynomial R) (y : AzPolyMod f) (n : AzNat) : IO Unit := do
  let (g, tG) ← timeOne fun _ => AzPolynomial.invRev f
  let (p1, t1) ← timeOne fun _ => (Azurite.slidingWindowPowAzNat y n).val
  let (p2, t2) ← timeOne fun _ =>
    (@Azurite.slidingWindowPowAzNat (AzPolyMod f) ⟨AzPolyMod.mulInv g⟩ _
      (@instSquare _ ⟨AzPolyMod.mulInv g⟩) y n).val
  IO.println s!"   {label}: plain {us (t1 / 1000)}ms, by inverse {us (t2 / 1000)}ms ({
    decide (p1 = p2)}); invRev {us (tG / 1000)}ms"

/-- `benchmark poly_default 1 "inv:1"`: the two reductions for powers over `AzInt` and
`AzRat`, where the coefficients are not reduced and grow with the power. -/
def runInv : IO Unit := do
  for e in [8, 64] do
    IO.println s!"AzInt, modulus with coefficients in [-11, 11], y^{e}"
    for d in [8, 16, 32, 64] do
      let f : AzPolynomial AzInt := AzPolynomial.monomial d 1 +
        normalize ((Array.range d).map fun (i : Nat) =>
          AzInt.ofInt (((i : Int) * 37 + 4) % 23 - 11))
      let y : AzPolyMod f := AzPolyMod.ofPoly (normalize ((Array.range d).map fun (i : Nat) =>
        AzInt.ofInt (((i : Int) * (i : Int) * 5 + (i : Int) * 9 + 3) % 41 - 20)))
      cmpPow s!"deg {d}" f y (AzNat.ofNat e)
    IO.println s!"AzRat, modulus with coefficients k/7, y^{e}"
    for d in [8, 16, 32] do
      let f : AzPolynomial AzRat := AzPolynomial.monomial d 1 +
        normalize ((Array.range d).map fun (i : Nat) =>
          ((((i * 37 + 4) % 23 : Nat) : AzRat) - 11) / 7)
      let y : AzPolyMod f := AzPolyMod.ofPoly (normalize ((Array.range d).map fun (i : Nat) =>
        ((((i * i * 5 + i * 9 + 3) % 41 : Nat) : AzRat) - 20) / 3))
      cmpPow s!"deg {d}" f y (AzNat.ofNat e)

def runDefault (limit : Nat) (_cfg : Std.HashMap String String) : IO Unit := do
  if _cfg.contains "inv" then
    runInv
    return
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
  for bits in [20, 30, 60, 64, 120, 250, 500] do
    let m := AzNat.pow (AzNat.ofNat 2) bits - AzNat.ofNat 3
    if h : m.toNat ≠ 0 then
      have : NeZero m.toNat := ⟨h⟩
      IO.println s!"AzZMod, {bits}-bit modulus: x^(m) modulo a monic f (ms: default / before / schoolbook)"
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
        let (r3, t3) ← timeOne fun _ =>
          @powModByMonic (AzZMod m) _ _ configOld a (m + 2 - 2) f
        let (r1', t1') ← timeOne fun _ => powModByMonic a (m + 3 - 3) f
        let (_, t3') ← timeOne fun _ =>
          @powModByMonic (AzZMod m) _ _ configOld a (m + 4 - 4) f
        if _cfg.contains "nobase" then
          IO.println s!"   deg {d}: {us (min t1 t1' / 1000)} / before 2026-11-25 {
            us (min t3 t3' / 1000)}  ({decide (r1 = r3) && decide (r1 = r1')})"
        else
          let (r2, t2) ← timeOne fun _ =>
            @powModByMonic (AzZMod m) _ _ .basecase a (m + 1 - 1) f
          IO.println s!"   deg {d}: {us (min t1 t1' / 1000)} / before 2026-11-25 {
            us (min t3 t3' / 1000)} / {us (t2 / 1000)}  ({
            decide (r1 = r2) && decide (r1 = r3) && decide (r1 = r1')})"

end Azurite.Benchmark.PolyKronecker
