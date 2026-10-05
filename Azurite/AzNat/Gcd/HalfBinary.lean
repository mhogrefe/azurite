/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzInt.Add
import Azurite.AzInt.Conversion
import Azurite.AzInt.Mul
import Azurite.AzInt.Pow2
import Azurite.AzInt.ShiftLeft
import Azurite.AzInt.ShiftRight
import Azurite.AzInt.Size
import Azurite.AzInt.Sub
import Azurite.AzInt.TrailingZeros
import Azurite.AzNat.Gcd.Binary
import Azurite.AzNat.Size
import Azurite.AzNat.TestBit
import Azurite.AzZModPow2.Conversion
import Azurite.AzZModPow2.Inv
import Azurite.UInt64.TrailingZeros

/-!
## Half-binary GCD (MCA §1.6.3, Algorithms 1.21 and 1.22)

A subquadratic GCD built on the *binary remainder sequence*: `BinaryDivide a b` (Algorithm 1.21)
produces `q` with `|q| < 2^j`, `j = ν(b) − ν(a)`, and `r = a + q · 2^{−j} b` with `ν(r) > ν(b)`.
`HalfBinaryGcd a b k` (Algorithm 1.22) returns `j ≤ k` and a `2 × 2` integer matrix `R` of
determinant `±2^{2j}` such that `2^{−2j} R (a, b)ᵀ` are two consecutive terms of the remainder
sequence of `(a, b)` whose 2-adic valuations straddle `k` — computed recursively from the low
`2k + 1` bits of the inputs, so the cost is `O(M(n) log n)`.

**Correctness is proved from the determinant alone** (`Equiv/Gcd/HalfBinary.lean`): any matrix
of determinant `±2^{2j}` applied to `(a, b)` with exact division by `2^{2j}` preserves the odd part
of the GCD, and `binaryDivide` preserves it for *every* quotient.  The remainder-sequence theory
of MCA Theorem 1.9 therefore governs only progress, never validity; the driver checks exactness
of the two divisions at runtime and falls back to the proven binary GCD otherwise.

Leaves of the recursion (`k ≤ halfBinaryWordThreshold`) run the remainder sequence on single
machine words with the cofactor matrix in machine-sized `Int`s (`halfBinaryGcdWord`).
-/

namespace Azurite.AzNat

/-! ### 2 × 2 integer matrices -/

/-- The integer matrix `[a, b; c, d]`. -/
structure Mat2 where
  a : AzInt
  b : AzInt
  c : AzInt
  d : AzInt

namespace Mat2

/-- The identity matrix. -/
def one : Mat2 := ⟨1, 0, 0, 1⟩

/-- Matrix product `S * T`. -/
def mul (S T : Mat2) : Mat2 :=
  ⟨S.a * T.a + S.b * T.c, S.a * T.b + S.b * T.d, S.c * T.a + S.d * T.c, S.c * T.b + S.d * T.d⟩

/-- `[0, 2^j; 2^j, q] * R`: the matrix of one binary-division step applied to `R`. -/
def stepMul (j : Nat) (q : AzInt) (R : Mat2) : Mat2 :=
  ⟨R.c <<< j, R.d <<< j, (R.a <<< j) + q * R.c, (R.b <<< j) + q * R.d⟩

/-- `R * (x, y)ᵀ`. -/
def apply (R : Mat2) (x y : AzInt) : AzInt × AzInt := (R.a * x + R.b * y, R.c * x + R.d * y)

/-- The determinant `a d − b c`. -/
def det (R : Mat2) : AzInt := R.a * R.d - R.b * R.c

end Mat2

/-- The `AzInt` of a machine-size `Int`, or `none` when `|x| ≥ 2^64`. -/
def _root_.Azurite.AzInt.ofBoundedInt? (x : Int) : Option AzInt :=
  if x.natAbs < 2 ^ 64 then
    some (if 0 ≤ x then x.natAbs.toUInt64.toAzInt else -(x.natAbs.toUInt64.toAzInt))
  else none

/-- A matrix from four machine-size `Int`s (`none` if any entry is out of range). -/
def Mat2.ofInts? (M : Int × Int × Int × Int) : Option Mat2 :=
  match AzInt.ofBoundedInt? M.1, AzInt.ofBoundedInt? M.2.1, AzInt.ofBoundedInt? M.2.2.1,
      AzInt.ofBoundedInt? M.2.2.2 with
  | some a, some b, some c, some d => some ⟨a, b, c, d⟩
  | _, _, _, _ => none

/-! ### Signed helpers -/

/-- The nonnegative representative of `z mod 2^m`. -/
def _root_.Azurite.AzInt.lowBits (z : AzInt) (m : Nat) : AzInt :=
  (AzZModPow2.ofAzInt m z).val.toAzInt

/-- `z / 2^m` when the division is exact, `none` otherwise. -/
def _root_.Azurite.AzInt.exactShiftRight (z : AzInt) (m : Nat) : Option AzInt :=
  match z.trailingZeros with
  | none => some 0
  | some v => if m ≤ v then some (AzInt.mkNorm z.sign (z.abs >>> m)) else none

/-- The odd part `n / 2^ν(n)` (`0` for `0`). -/
def oddPart (n : AzNat) : AzNat :=
  match n.trailingZeros with
  | none => 0
  | some v => n >>> v

/-! ### Binary division (Algorithm 1.21) -/

/-- **Binary division.**  Given `a` and an odd `b'` (`b' = b >>> j` with `j = ν(b)`), returns
`(q, r)` with `q ≡ −a / b' mod 2^{j+1}`, `−2^j ≤ q < 2^j`, and `r = a + q · b'`; when `a` is odd this
makes `ν(r) > j`.  For an even `b'` (never the case in the algorithm) returns `(0, a)`.  The quotient
comes from the Newton inverse of `b'` in `ℤ / 2^{j+1}` (`AzZModPow2.invOdd`). -/
def binaryDivide (a b' : AzInt) (j : Nat) : AzInt × AzInt :=
  let bz : AzZModPow2 (j + 1) := AzZModPow2.ofAzInt (j + 1) b'
  if h : bz.isOdd then
    let t : AzNat := (AzZModPow2.ofAzInt (j + 1) (-a) * bz.invOdd h).val
    let q : AzInt := if t.testBit j then t.toAzInt - AzInt.pow2 (j + 1) else t.toAzInt
    (q, a + q * b')
  else (0, a)

/-! ### Word-level base case -/

/-- Inverse of an odd `b` modulo `2^64` by five Newton steps `x ↦ x (2 − b x)` from the seed `b`
(`b² ≡ 1 mod 8`, so the seed is correct to three bits, then 6, 12, 24, 48, 96). -/
def invOddUInt64 (b : UInt64) : UInt64 :=
  let x := b
  let x := x * (2 - b * x)
  let x := x * (2 - b * x)
  let x := x * (2 - b * x)
  let x := x * (2 - b * x)
  x * (2 - b * x)

/-- The binary remainder sequence on single words, accumulating the cofactor matrix
`(m₁₁, m₁₂, m₂₁, m₂₂)` in machine-size `Int`s, until the valuation would exceed `k`.  `A` is the
current odd term, `B` the current even one; both are only meaningful in their low `2(k − j) + 1`
bits.  Each step adds `ν(B) ≥ 1` to `j`, so `k + 1` units of fuel suffice. -/
def halfBinaryGcdWord.go (k : Nat) :
    Nat → UInt64 → UInt64 → Nat → Int × Int × Int × Int → Nat × (Int × Int × Int × Int)
  | 0, _, _, j, M => (j, M)
  | fuel + 1, A, B, j, M =>
    if B = 0 then (j, M)
    else
      let j₀ := B.trailingZeros
      if k < j + j₀ then (j, M)
      else
        let B' := B >>> j₀.toUInt64
        let half : UInt64 := 1 <<< j₀.toUInt64
        let t := ((0 - A) * invOddUInt64 B') &&& (2 * half - 1)
        let q : Int := if t < half then (t.toNat : Int) else (t.toNat : Int) - (2 * half).toNat
        let r : UInt64 := if t < half then A + t * B' else A - (2 * half - t) * B'
        let p : Int := 2 ^ j₀
        let M' : Int × Int × Int × Int :=
          (p * M.2.2.1, p * M.2.2.2, p * M.1 + q * M.2.2.1, p * M.2.1 + q * M.2.2.2)
        halfBinaryGcdWord.go k fuel B' (r >>> j₀.toUInt64) (j + j₀) M'

/-- Half-binary GCD on single words: the base case of `halfBinaryGcd` for `k ≤ 31`, where the
low `2k + 1 ≤ 63` bits of both inputs fit a `UInt64`. -/
def halfBinaryGcdWord (A B : UInt64) (k : Nat) : Nat × (Int × Int × Int × Int) :=
  halfBinaryGcdWord.go k (k + 1) A B 0 (1, 0, 0, 1)

/-- Largest `k` handled by the word-level base case (`2k + 1 ≤ 63`). -/
def halfBinaryWordThreshold : Nat := 31

/-! ### Half-binary GCD (Algorithm 1.22) -/

/-- **Half-binary GCD.**  `halfBinaryGcd fuel a b k` returns `(j, R)` with `j ≤ k` and
`|det R| = 2^{2j}` (proved unconditionally); when `ν(a) = 0 < ν(b)` the theory of MCA Theorem 1.9
makes `2^{−2j} R (a, b)ᵀ` two consecutive binary remainders of `(a, b)` with valuations `≤ k < ·`.
Both recursive calls use a smaller `k`, so `fuel = k + 1` suffices; the recursion is structural in
`fuel` so that the definition evaluates under `decide`. -/
def halfBinaryGcd : Nat → AzInt → AzInt → Nat → Nat × Mat2
  | 0, _, _, _ => (0, Mat2.one)
  | fuel + 1, a, b, k =>
    if k ≤ halfBinaryWordThreshold then
      let m := 2 * k + 1
      let A := (a.lowBits m).abs.limbs.getD 0 0
      let B := (b.lowBits m).abs.limbs.getD 0 0
      let jM := halfBinaryGcdWord A B k
      match Mat2.ofInts? jM.2 with
      | some M => (jM.1, M)
      | none => (0, Mat2.one)
    else
      let k₁ := k / 2
      let m₁ := 2 * k₁ + 1
      let jR := halfBinaryGcd fuel (a.lowBits m₁) (b.lowBits m₁) k₁
      let j₁ := jR.1
      let R := jR.2
      let ab := R.apply a b
      let a' := ab.1 >>> (2 * j₁)
      let b' := ab.2 >>> (2 * j₁)
      match b'.trailingZeros with
      | none => (j₁, R)
      | some j₀ =>
        if k < j₀ + j₁ then (j₁, R)
        else
          let b'' := b' >>> j₀
          let qr := binaryDivide a' b'' j₀
          let k₂ := k - (j₀ + j₁)
          let m₂ := 2 * k₂ + 1
          let jS := halfBinaryGcd fuel (b''.lowBits m₂) ((qr.2 >>> j₀).lowBits m₂) k₂
          (j₁ + j₀ + jS.1, jS.2.mul (Mat2.stepMul j₀ qr.1 R))

/-! ### Plain GCD driver -/

/-- Operands of at most this many bits use the binary GCD (`gcdBinary`); larger ones the
half-binary recursion.  Tuned 2026-10-05 (`az_nat_gcd`): the half-binary GCD overtakes the binary
GCD near 1024 operand bits, and thresholds from 768 to 1536 are within 10 % of each other. -/
def halfBinaryGcdThreshold : Nat := 1024

/-- The odd part of `gcd a b`, for signed `a`, `b`, by repeated halving: a half-binary GCD with
`k = n / 2` on the low `n + 1` bits, one exact application of its matrix, one binary division, and
recursion on the two new (half-size) remainders.  Every step preserves the odd part of the GCD, and
the divisions by powers of two are checked, so the result is exact whatever the inputs; the binary
GCD finishes operands of at most `threshold` bits and serves as the fallback. -/
def halfBinaryGcdDriver (threshold : Nat) : Nat → AzInt → AzInt → AzNat
  | 0, a, b => oddPart (gcdBinary a.abs b.abs)
  | fuel + 1, a, b =>
    let n := max a.size b.size
    if n ≤ threshold then oddPart (gcdBinary a.abs b.abs)
    else
      let k₁ := n / 2
      let m₁ := 2 * k₁ + 1
      let jR := halfBinaryGcd (k₁ + 1) (a.lowBits m₁) (b.lowBits m₁) k₁
      let ab := jR.2.apply a b
      match ab.1.exactShiftRight (2 * jR.1), ab.2.exactShiftRight (2 * jR.1) with
      | some a', some b' =>
        match b'.trailingZeros with
        | none => oddPart a'.abs
        | some j₀ =>
          let b'' := AzInt.mkNorm b'.sign (b'.abs >>> j₀)
          let qr := binaryDivide a' b'' j₀
          match qr.2.exactShiftRight j₀ with
          | some r' => halfBinaryGcdDriver threshold fuel b'' r'
          | none => oddPart (gcdBinary b''.abs qr.2.abs)
      | _, _ => oddPart (gcdBinary a.abs b.abs)

/-- **Half-binary GCD of two `AzNat`s** (MCA §1.6.3) with an explicit binary-GCD fallback
threshold (bits).  Strips the common power of two, arranges for the first operand to be odd and the
second even, and runs `halfBinaryGcdDriver`. -/
def gcdHalfBinaryWith (threshold : Nat) (a b : AzNat) : AzNat :=
  match a.trailingZeros, b.trailingZeros with
  | none, _ => b
  | _, none => a
  | some ta, some tb =>
    let t := min ta tb
    let a₁ := a >>> t
    let b₁ := b >>> t
    let x := if ta ≤ tb then a₁ else b₁
    let y := if ta ≤ tb then b₁ else a₁
    let y := if y.isOdd then x + y else y
    (halfBinaryGcdDriver threshold (max x.size y.size + 1) x.toAzInt y.toAzInt) <<< t

/-- **Half-binary GCD of two `AzNat`s** at the default threshold. -/
def gcdHalfBinary (a b : AzNat) : AzNat := gcdHalfBinaryWith halfBinaryGcdThreshold a b

end Azurite.AzNat
