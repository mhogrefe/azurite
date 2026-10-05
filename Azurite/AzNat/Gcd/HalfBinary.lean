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
import Azurite.UInt64.AddWithCarry
import Azurite.UInt64.MulWithCarry
import Azurite.UInt64.SubWithBorrow
import Azurite.UInt64.TrailingZeros
import Azurite.UInt64.WideMul

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

Leaves of the recursion (`k ≤ halfBinaryWordThreshold`) run the remainder sequence on two-word
operands with the cofactor matrix in `Int64`s (`halfBinaryGcdWord`); a runtime check that the
entries are small enough makes the wrapping arithmetic exact.
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

/-- A `2 × 2` matrix with `Int64` entries: the cofactor matrix of the word-level base case.  The
loop checks before every step that the entries are small enough for the wrapping `Int64`
arithmetic to be exact (`wordStep_exact`). -/
structure WordMat where
  m₁₁ : Int64
  m₁₂ : Int64
  m₂₁ : Int64
  m₂₂ : Int64

/-- A `Mat2` from a word matrix. -/
def Mat2.ofWord (M : WordMat) : Mat2 := ⟨M.m₁₁.toAzInt, M.m₁₂.toAzInt, M.m₂₁.toAzInt, M.m₂₂.toAzInt⟩

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

/-! ### Two-word values for the base case -/

/-- An unsigned 128-bit value `lo + 2^64 · hi`, the operand type of the word-level base case.
Its arithmetic is progress-only: nothing about these values enters the correctness proofs. -/
structure Word2 where
  lo : UInt64
  hi : UInt64

namespace Word2

/-- Trailing zeros (`128` for zero). -/
def trailingZeros (x : Word2) : Nat :=
  if x.lo = 0 then (if x.hi = 0 then 128 else 64 + x.hi.trailingZeros) else x.lo.trailingZeros

/-- Right shift by `s < 128` bits. -/
def shiftRight (x : Word2) (s : Nat) : Word2 :=
  if s = 0 then x
  else if s < 64 then
    ⟨(x.lo >>> s.toUInt64) ||| (x.hi <<< (64 - s).toUInt64), x.hi >>> s.toUInt64⟩
  else ⟨x.hi >>> (s - 64).toUInt64, 0⟩

/-- The low 128 bits of `x * u`. -/
def mulWord (x : Word2) (u : UInt64) : Word2 :=
  let p := UInt64.wideMul x.lo u
  ⟨p.2, p.1 + x.hi * u⟩

/-- Addition modulo `2^128`. -/
def add (x y : Word2) : Word2 :=
  let s := x.lo + y.lo
  ⟨s, x.hi + y.hi + (if s < x.lo then 1 else 0)⟩

/-- Subtraction modulo `2^128`. -/
def sub (x y : Word2) : Word2 :=
  ⟨x.lo - y.lo, x.hi - y.hi - (if x.lo < y.lo then 1 else 0)⟩

/-- The low `m` bits (`m ≥ 128` keeps everything). -/
def lowBits (x : Word2) (m : Nat) : Word2 :=
  if m ≥ 128 then x
  else if m ≥ 64 then ⟨x.lo, x.hi &&& ((1 <<< (m - 64).toUInt64) - 1)⟩
  else ⟨x.lo &&& ((1 <<< m.toUInt64) - 1), 0⟩

end Word2

/-- The low `m ≤ 128` bits of `z` in two's complement (`z mod 2^m` for `m < 128`). -/
def _root_.Azurite.AzInt.lowWord2 (z : AzInt) (m : Nat) : Word2 :=
  let w : Word2 := ⟨z.abs.limbs.getD 0 0, z.abs.limbs.getD 1 0⟩
  let w := if z.sign then w else Word2.sub ⟨0, 0⟩ w
  w.lowBits m

/-! ### Fused linear combination -/

/-- One pass over `fuel` limbs from index `i`: the limbs of `x·u + y·v` (`sub = false`, final
carry in the flag) or of `x·u − y·v` in two's complement (`sub = true`, final borrow in the
flag); limbs beyond an array read as zero.  `c₁`, `c₂` are the running carries of the two
products and `bo` the running carry/borrow of the sum; the final carries are returned too (they
are zero once the pass has read past both arrays). -/
def linCombLimbs.go (x y : Array UInt64) (u v : UInt64) (sub : Bool) :
    Nat → Nat → Array UInt64 → UInt64 → UInt64 → Bool → Array UInt64 × Bool × UInt64 × UInt64
  | 0, _, acc, c₁, c₂, bo => (acc, bo, c₁, c₂)
  | fuel + 1, i, acc, c₁, c₂, bo =>
    let p := UInt64.mulWithCarry (x.getD i 0) u c₁
    let q := UInt64.mulWithCarry (y.getD i 0) v c₂
    let d := if sub then UInt64.subWithBorrow p.2 q.2 bo else UInt64.addWithCarry p.2 q.2 bo
    linCombLimbs.go x y u v sub fuel (i + 1) (acc.push d.1) p.1 q.1 d.2

/-- `x·u ± y·v` over `max x.size y.size + 2` limbs, in one pass (see `linCombLimbs.go`); the
flag is the final carry (`sub = false`) or borrow (`sub = true`).  With two extra limbs the sum
always fits and the difference's two's complement is complete (the last limbs read are zero). -/
def linCombLimbs (x y : Array UInt64) (u v : UInt64) (sub : Bool) : Array UInt64 × Bool :=
  let n := max x.size y.size + 2
  let r := linCombLimbs.go x y u v sub n 0 (Array.mkEmpty n) 0 0 false
  (r.1, r.2.1)

/-- One limb of a right shift from the adjacent raw limbs `prev` (lower) and `d` (upper), with the
shift amounts hoisted as words: `rU = r`, `hiU = 64 − r`, and `mask0 = 0` when `r = 0` (where
`d <<< 64` would wrap to `d`) and all ones otherwise.  The two parts have disjoint bits, so `+` is
`|||`. -/
@[inline] def shiftLimbPair (rU hiU mask0 : UInt64) (prev d : UInt64) : UInt64 :=
  (prev >>> rU) + ((d <<< hiU) &&& mask0)

/-- The word parameters of `shiftLimbPair` for a shift by `r < 64` bits. -/
@[inline] def shiftMask0 (r : Nat) : UInt64 := if r = 0 then 0 else 0xFFFFFFFFFFFFFFFF

/-- The emission phase of the fused shifted pass (raw index `i > w`): every raw limb `dᵢ` emits
`shiftLimbPair rU hiU mask0 prev dᵢ`; no index tests in the loop. -/
def linCombShift.goHigh (x y : Array UInt64) (u v : UInt64) (sub : Bool) (rU hiU mask0 : UInt64) :
    Nat → Nat → Array UInt64 → UInt64 → UInt64 → UInt64 → Bool → Array UInt64 × UInt64 × Bool
  | 0, _, acc, prev, _, _, bo => (acc, prev, bo)
  | fuel + 1, i, acc, prev, c₁, c₂, bo =>
    let p := UInt64.mulWithCarry (x.getD i 0) u c₁
    let q := UInt64.mulWithCarry (y.getD i 0) v c₂
    let d := if sub then UInt64.subWithBorrow p.2 q.2 bo else UInt64.addWithCarry p.2 q.2 bo
    linCombShift.goHigh x y u v sub rU hiU mask0 fuel (i + 1)
      (acc.push (shiftLimbPair rU hiU mask0 prev d.1)) d.1 p.1 q.1 d.2

/-- The low phase of the fused shifted pass (raw index `i ≤ w`): raw limbs below `w` are only
checked to be zero (`ok`), the limb at `w` is checked in its low `r` bits and becomes `prev`, then
`goHigh` emits the rest.  Returns the emitted limbs, the last raw limb, the exactness flag and the
final carry/borrow. -/
def linCombShift.goLow (x y : Array UInt64) (u v : UInt64) (sub : Bool) (w r : Nat) :
    Nat → Nat → Bool → UInt64 → UInt64 → Bool → Array UInt64 × UInt64 × Bool × Bool
  | 0, _, ok, _, _, bo => (#[], 0, ok, bo)
  | fuel + 1, i, ok, c₁, c₂, bo =>
    let p := UInt64.mulWithCarry (x.getD i 0) u c₁
    let q := UInt64.mulWithCarry (y.getD i 0) v c₂
    let d := if sub then UInt64.subWithBorrow p.2 q.2 bo else UInt64.addWithCarry p.2 q.2 bo
    if i < w then linCombShift.goLow x y u v sub w r fuel (i + 1) (ok && d.1 == 0) p.1 q.1 d.2
    else
      let res := linCombShift.goHigh x y u v sub r.toUInt64 (64 - r).toUInt64 (shiftMask0 r) fuel
        (i + 1) (Array.mkEmpty fuel) d.1 p.1 q.1 d.2
      (res.1, res.2.1, ok && (d.1 &&& ((1 <<< r.toUInt64) - 1)) == 0, res.2.2)

/-- `(x·u ± y·v) >> sh` in one fused pass: the shifted limbs, whether the division was exact, and
the final carry/borrow of the unshifted combination (`linCombLimbs`).  Requires `sh < 64 n`. -/
def linCombShift (x y : Array UInt64) (u v : UInt64) (sub : Bool) (sh : Nat) :
    Array UInt64 × Bool × Bool :=
  let n := max x.size y.size + 2
  let w := sh / 64
  let r := sh % 64
  let res := linCombShift.goLow x y u v sub w r n 0 true 0 0 false
  (res.1.push (res.2.1 >>> r.toUInt64), res.2.2.1, res.2.2.2)

/-- Two's complement negation of a limb array (`2^{64 len} − T` for `0 < T < 2^{64 len}`), as a
fresh array of the same length. -/
def negLimbs.go (a : Array UInt64) : Nat → Nat → Array UInt64 → Bool → Array UInt64 × Bool
  | 0, _, acc, bo => (acc, bo)
  | fuel + 1, i, acc, bo =>
    let d := UInt64.subWithBorrow 0 (a.getD i 0) bo
    negLimbs.go a fuel (i + 1) (acc.push d.1) d.2

def negLimbs (a : Array UInt64) : Array UInt64 :=
  (negLimbs.go a a.size 0 (Array.mkEmpty a.size) false).1

/-- The magnitude of an `Int64` as a word (pure word arithmetic). -/
def int64Abs (m : Int64) : UInt64 := if 0 ≤ m then m.toUInt64 else 0 - m.toUInt64

/-- `(m₁ x + m₂ y) / 2^sh` when that division is exact, `none` otherwise, in one fused limb pass
(`linCombShift`): the signed combination in two's complement with the shift folded in.  When the
two terms have opposite signs and the pass ends with a borrow, the result is negative and its
magnitude is the two's complement negation of the shifted limbs within `64 n − sh` bits
(`negLimbs`, then `modPow2`). -/
def fusedCombine? (m₁ m₂ : Int64) (x y : AzInt) (sh : Nat) : Option AzInt :=
  let u : UInt64 := int64Abs m₁
  let v : UInt64 := int64Abs m₂
  let t₁ : Bool := decide (0 ≤ m₁) == x.sign
  let t₂ : Bool := decide (0 ≤ m₂) == y.sign
  let n := max x.abs.limbs.size y.abs.limbs.size + 2
  if 64 * n ≤ sh then none
  else
    let res := linCombShift x.abs.limbs y.abs.limbs u v (t₁ != t₂) sh
    if !res.2.1 then none
    else if t₁ == t₂ then some (AzInt.mkNorm t₁ (ofLimbs res.1))
    else if res.2.2 then
      some (AzInt.mkNorm (!t₁) ((ofLimbs (negLimbs res.1)).modPow2 (64 * n - sh)))
    else some (AzInt.mkNorm t₁ (ofLimbs res.1))

/-! ### Binary division (Algorithm 1.21) -/

/-- **Binary division.**  Given `a` and an odd `b'` (`b' = b >>> j` with `j = ν(b)`), returns
`(q, r)` with `q ≡ −a / b' mod 2^{j+1}`, `−2^j ≤ q < 2^j`, and `r = a + q · b'`; when `a` is odd
this makes `ν(r) > j`.  For an even `b'` (never the case in the algorithm) returns `(0, a)`.  The
quotient comes from the Newton inverse of `b'` in `ℤ / 2^{j+1}` (`AzZModPow2.invOdd`). -/
def binaryDivide (a b' : AzInt) (j : Nat) : AzInt × AzInt :=
  let bz : AzZModPow2 (j + 1) := AzZModPow2.ofAzInt (j + 1) b'
  if h : bz.isOdd then
    let t : AzNat := (AzZModPow2.ofAzInt (j + 1) (-a) * bz.invOdd h).val
    let q : AzInt := if t.testBit j then t.toAzInt - AzInt.pow2 (j + 1) else t.toAzInt
    (q, a + q * b')
  else (0, a)

/-! ### Word-level base case -/

/-- Inverse of an odd `b` modulo `2^bits` (`bits ≤ 64`) by Newton steps `x ↦ x (2 − b x)` from the
seed `b` (`b² ≡ 1 mod 8`, so the seed is correct to three bits, then 6, 12, 24, 48, 96); only as
many steps as `bits` requires. -/
def invOddUInt64 (b : UInt64) (bits : Nat) : UInt64 :=
  let x := b
  if bits ≤ 3 then x else
  let x := x * (2 - b * x)
  if bits ≤ 6 then x else
  let x := x * (2 - b * x)
  if bits ≤ 12 then x else
  let x := x * (2 - b * x)
  if bits ≤ 24 then x else
  let x := x * (2 - b * x)
  if bits ≤ 48 then x else
  x * (2 - b * x)

/-- The binary remainder sequence on two-word operands, accumulating the cofactor matrix in
`Int64`s, until the valuation would exceed `k`.  `A` is the current odd term, `B` the current even
one; both are only meaningful in their low `2(k − j) + 1` bits.  Each step adds `j₀ = ν(B) ≥ 1` to
`j`, so `k + 1` units of fuel suffice.  Before a step the loop checks that every cofactor is at
most `2^{61 − j₀}` in magnitude — then the step's `Int64` arithmetic is exact
(`wordStep_exact`) — and stops otherwise; by the size theory of the remainder sequence the
cofactors have about `j` bits, so with `k = 63` a call usually gets close to `j = 63`. -/
def halfBinaryGcdWord.go (k : Nat) : Nat → Word2 → Word2 → Nat → WordMat → Nat × WordMat
  | 0, _, _, j, M => (j, M)
  | fuel + 1, A, B, j, M =>
    let j₀ := B.trailingZeros
    if j₀ = 0 ∨ 61 < j₀ ∨ k < j + j₀ then (j, M)
    else
      let bound : Int64 := ((1 : UInt64) <<< (61 - j₀).toUInt64).toInt64
      if -bound ≤ M.m₁₁ ∧ M.m₁₁ ≤ bound ∧ -bound ≤ M.m₁₂ ∧ M.m₁₂ ≤ bound ∧
          -bound ≤ M.m₂₁ ∧ M.m₂₁ ≤ bound ∧ -bound ≤ M.m₂₂ ∧ M.m₂₂ ≤ bound then
        let B' := B.shiftRight j₀
        let half : UInt64 := 1 <<< j₀.toUInt64
        let t := ((0 - A.lo) * invOddUInt64 B'.lo (j₀ + 1)) &&& (2 * half - 1)
        let q : Int64 := if t < half then t.toInt64 else t.toInt64 - (2 * half).toInt64
        let r : Word2 :=
          if t < half then A.add (B'.mulWord t) else A.sub (B'.mulWord (2 * half - t))
        let p : Int64 := half.toInt64
        let M' : WordMat := ⟨p * M.m₂₁, p * M.m₂₂, p * M.m₁₁ + q * M.m₂₁, p * M.m₁₂ + q * M.m₂₂⟩
        halfBinaryGcdWord.go k fuel B' (r.shiftRight j₀) (j + j₀) M'
      else (j, M)

/-- Half-binary GCD on two-word operands: the base case of `halfBinaryGcd` for `k ≤ 63`, where
the low `2k + 1 ≤ 127` bits of both inputs fit a `Word2`. -/
def halfBinaryGcdWord (A B : Word2) (k : Nat) : Nat × WordMat :=
  halfBinaryGcdWord.go k (k + 1) A B 0 ⟨1, 0, 0, 1⟩

/-- Largest `k` handled by the word-level base case (`2k + 1 ≤ 127`). -/
def halfBinaryWordThreshold : Nat := 63

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
      let jM := halfBinaryGcdWord (a.lowWord2 m) (b.lowWord2 m) k
      (jM.1, Mat2.ofWord jM.2)
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

/-- Operands of at most this many bits use the binary GCD (`gcdBinary`, i.e. Euclid on a single
word); larger ones the half-binary driver (quadratic word rounds up to
`halfBinaryGcdQuadraticThreshold`, the full recursion above).  Tuned 2026-10-05 (`az_nat_gcd`):
the word rounds beat Stein's algorithm already at two limbs (3.3 µs against 8.6 µs at 170 operand
bits) and by 3.5–4× from 340 to 1400 bits. -/
def halfBinaryGcdThreshold : Nat := 64

/-- Operands of at most this many bits (but above `halfBinaryGcdThreshold`) use the **quadratic
middle layer**: each driver round runs only the word-level base case
(`k = halfBinaryWordThreshold`) on the low two words, so it removes up to about 60 bits with four
word-by-operand products — the LSB analogue of MCA Algorithm 1.17 (DoubleDigitGcd).  Above it the
rounds use `k = n / 2`, i.e. the subquadratic recursion.  Tuned 2026-10-05 (`az_nat_gcd`) with the
two-word base case and the fused two-pass round: the word rounds beat the recursion up to about
80000 operand bits (11.8 ms against 13.7 ms at 44000 bits) and tie with it at 87000. -/
def halfBinaryGcdQuadraticThreshold : Nat := 65536

/-- The odd part of `gcd a b`, for signed `a`, `b`, by repeated reduction rounds.  Above
`quadThreshold` bits: a half-binary GCD with `k = n / 2` on the low `n + 1` bits, one exact
application of its matrix, one binary division, and recursion on the two new half-size remainders.
Up to `quadThreshold` bits (the quadratic middle layer): the word base case on the low 127 bits,
applied with two fused limb passes per output (`fusedCombine?`), removing up to about 60 bits
per round.  Every step
preserves the odd part of the GCD, and the divisions by powers of two are checked, so the result
is exact whatever the inputs; the binary GCD finishes operands of at most `threshold` bits and
serves as the fallback. -/
def halfBinaryGcdDriver (threshold quadThreshold : Nat) : Nat → AzInt → AzInt → AzNat
  | 0, a, b => oddPart (gcdBinary a.abs b.abs)
  | fuel + 1, a, b =>
    let n := max a.size b.size
    if n ≤ threshold then oddPart (gcdBinary a.abs b.abs)
    else if n ≤ quadThreshold then
      -- quadratic round: the word base case on the low 127 bits, applied with two fused passes
      let jM := halfBinaryGcdWord (a.lowWord2 (2 * halfBinaryWordThreshold + 1))
        (b.lowWord2 (2 * halfBinaryWordThreshold + 1)) halfBinaryWordThreshold
      if jM.1 = 0 then oddPart (gcdBinary a.abs b.abs)
      else
        match fusedCombine? jM.2.m₁₁ jM.2.m₁₂ a b (2 * jM.1),
            fusedCombine? jM.2.m₂₁ jM.2.m₂₂ a b (2 * jM.1) with
        | some a', some b' => halfBinaryGcdDriver threshold quadThreshold fuel a' b'
        | _, _ => oddPart (gcdBinary a.abs b.abs)
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
          | some r' => halfBinaryGcdDriver threshold quadThreshold fuel b'' r'
          | none => oddPart (gcdBinary b''.abs qr.2.abs)
      | _, _ => oddPart (gcdBinary a.abs b.abs)

/-- **Half-binary GCD of two `AzNat`s** (MCA §1.6.3) with explicit thresholds (bits) for the
binary-GCD fallback and for the quadratic middle layer.  Strips the common power of two, arranges
for the first operand to be odd and the second even, and runs `halfBinaryGcdDriver`. -/
def gcdHalfBinaryWith (threshold quadThreshold : Nat) (a b : AzNat) : AzNat :=
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
    (halfBinaryGcdDriver threshold quadThreshold (max x.size y.size + 1) x.toAzInt y.toAzInt)
      <<< t

/-- **Half-binary GCD of two `AzNat`s** at the default thresholds. -/
def gcdHalfBinary (a b : AzNat) : AzNat :=
  gcdHalfBinaryWith halfBinaryGcdThreshold halfBinaryGcdQuadraticThreshold a b

end Azurite.AzNat
