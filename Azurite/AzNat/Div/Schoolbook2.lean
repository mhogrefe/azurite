/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Div.Schoolbook
import Azurite.UInt64.MulAddWithCarry

/-!
# Schoolbook division, two quotient limbs per pass

`schoolbookDivModLimbs` (Brent–Zimmermann, Algorithm 1.6) writes every limb of the remainder
once per quotient limb.  Here the same algorithm runs in base `2^128`: a step chooses **two**
quotient limbs from the top four limbs of the running remainder and the top two limbs of the
divisor (two applications of Möller–Granlund's `div3By2`), and subtracts the product of that
two-limb digit and the divisor in **one** pass (`subMul2Limbs`: two multiplications and one
write per limb, as the two-row `mulAdd2Limbs` of the multiplication).  The trial digit is at
least the true digit and exceeds the remainder by less than `2^(64 n)`, so it is corrected by
at most two additions of the divisor.

`schoolbookDivModLimbsFast` has the arguments and the result of `schoolbookDivModLimbs`
(`schoolbookDivModLimbs_eq_fast` in `Equiv/Div/Schoolbook2.lean`, a `@[csimp]` replacement):
divisors of one limb, and the last quotient limb of an odd count, go through the old code.
-/

namespace Azurite.AzNat

/-- `a − l − bw` for a borrow `bw ≤ 1`, with the borrow out as a limb `0` or `1`.  The borrow
is formed from conditional *scalars* (`if _ then 1 else 0`), not by branching on a pair, so
that the loop below keeps its state in registers (as the multiplication rows do). -/
@[inline]
def subBorrowLimb (a l bw : UInt64) : UInt64 × UInt64 :=
  let d := a - l
  (d - bw, (if a < l then 1 else 0) + (if d < bw then 1 else 0))

/-- Loop of `subMul2Limbs`: from position `k`, subtracts the low limb of
`b[loB + k] * (q₀ + q₁ 2^64) + carry` from `a[loA + k]`, threading the two-limb multiplication
carry `c₀ + c₁ 2^64` and the subtraction borrow `bw ≤ 1`; at the end the carry and the borrow
are subtracted from the two limbs above (without writing them), which gives the borrow out. -/
def subMul2Limbs.go (b : Array UInt64) (loB n : Nat) (q₀ q₁ : UInt64)
    (a : Array UInt64) (loA k : Nat) (c₀ c₁ bw : UInt64)
    (hA : loA + n + 2 ≤ a.size) (hB : loB + n ≤ b.size) :
    Array UInt64 × Bool :=
  if h : k < n then
    have hAi : loA + k < a.size := by omega
    have hBi : loB + k < b.size := by omega
    let m₁ := UInt64.mulWithCarry b[loB + k] q₀ c₀
    let m₂ := UInt64.mulAddWithCarry b[loB + k] q₁ m₁.1 c₁
    let s := subBorrowLimb a[loA + k] m₁.2 bw
    subMul2Limbs.go b loB n q₀ q₁ (a.set (loA + k) s.1) loA (k + 1) m₂.2 m₂.1 s.2
      (by rw [Array.size_set]; exact hA) hB
  else
    let t₀ := subBorrowLimb (a[loA + n]'(by omega)) c₀ bw
    let t₁ := subBorrowLimb (a[loA + n + 1]'(by omega)) c₁ t₀.2
    (a, t₁.2 != 0)
  termination_by n - k

/-- Size preservation of `subMul2Limbs.go`. -/
theorem subMul2Limbs.go_size (b : Array UInt64) (loB n : Nat) (q₀ q₁ : UInt64)
    (a : Array UInt64) (loA k : Nat) (c₀ c₁ bw : UInt64)
    (hA : loA + n + 2 ≤ a.size) (hB : loB + n ≤ b.size) :
    (subMul2Limbs.go b loB n q₀ q₁ a loA k c₀ c₁ bw hA hB).1.size = a.size := by
  induction h_sub : n - k generalizing a k c₀ c₁ bw with
  | zero =>
    have h_ge : n ≤ k := by omega
    rw [subMul2Limbs.go]; simp [Nat.not_lt.mpr h_ge]
  | succ p ih =>
    have h_lt : k < n := by omega
    rw [subMul2Limbs.go]
    simp only [h_lt, ↓reduceDIte]
    rw [ih _ _ _ _ _ _ (by omega), Array.size_set]

/-- Subtract `(q₀ + q₁ 2^64) * b[loB : loB + n)` from the `n + 2` limbs `a[loA : loA + n + 2)`,
writing only the low `n` limbs of the difference (the two top limbs are about to be replaced
by quotient limbs).  Returns the array and the borrow out of the top: `true` when the
difference is negative. -/
def subMul2Limbs (a b : Array UInt64) (loA loB n : Nat) (q₀ q₁ : UInt64)
    (hA : loA + n + 2 ≤ a.size) (hB : loB + n ≤ b.size) : Array UInt64 × Bool :=
  subMul2Limbs.go b loB n q₀ q₁ a loA 0 0 0 0 hA hB

/-- Size preservation of `subMul2Limbs`. -/
theorem subMul2Limbs_size (a b : Array UInt64) (loA loB n : Nat) (q₀ q₁ : UInt64)
    (hA : loA + n + 2 ≤ a.size) (hB : loB + n ≤ b.size) :
    (subMul2Limbs a b loA loB n q₀ q₁ hA hB).1.size = a.size :=
  subMul2Limbs.go_size _ _ _ _ _ _ _ _ _ _ _ _ _

/-- **The trial digit in base `2^128`**: `min (2^128 − 1) ⌊(a₃, a₂, a₁, a₀) / (d₁, d₀)⌋` as
`(high limb, low limb)`, for a normalized `(d₁, d₀)` with 3-by-2 reciprocal `v`. -/
@[inline]
def trialQuot2 (a₃ a₂ a₁ a₀ d₁ d₀ v : UInt64) : UInt64 × UInt64 :=
  if a₃ > d₁ ∨ (a₃ = d₁ ∧ a₂ ≥ d₀) then (0 - 1, 0 - 1)
  else
    let r := UInt64.div3By2 a₃ a₂ a₁ d₁ d₀ v
    let s := UInt64.div3By2 r.2.1 r.2.2 a₀ d₁ d₀ v
    (r.1, s.1)

/-- Store the two quotient limbs `(q₁, q₀) − k` above the remainder. -/
@[inline]
def schoolbookDivModLimbs.storeDigits (a : Array UInt64) (i : Nat) (q₁ q₀ k : UInt64)
    (h : i + 1 < a.size) : Array UInt64 :=
  (a.set i (q₀ - k) (by omega)).set (i + 1) (q₁ - (if q₀ < k then 1 else 0))
    (by rw [Array.size_set]; exact h)

/-- The end of a step: `arr` holds the window after the row, `neg` tells whether the
difference is negative.  Adds the divisor back (at most twice) and stores the corrected
digits. -/
@[inline]
def schoolbookDivModLimbs.correct2 (arr b : Array UInt64) (neg : Bool) (loA loB n j : Nat)
    (q₁ q₀ : UInt64) (hA : loA + j + n + 2 ≤ arr.size) (hB : loB + n ≤ b.size) :
    Array UInt64 :=
  if neg then
    let s := addSameLengthLimbs arr b (loA + j) loB n (by omega) hB
    have hs : s.1.size = arr.size := addSameLengthLimbs_size _ _ _ _ _ _ _
    if s.2 then
      schoolbookDivModLimbs.storeDigits s.1 (loA + j + n) q₁ q₀ 1 (by omega)
    else
      schoolbookDivModLimbs.storeDigits
        (addSameLengthLimbs s.1 b (loA + j) loB n (by omega) hB).1 (loA + j + n) q₁ q₀ 2
        (by rw [addSameLengthLimbs_size]; omega)
  else schoolbookDivModLimbs.storeDigits arr (loA + j + n) q₁ q₀ 0 (by omega)

/-- Size preservation of `correct2`. -/
theorem schoolbookDivModLimbs.correct2_size (arr b : Array UInt64) (neg : Bool)
    (loA loB n j : Nat) (q₁ q₀ : UInt64) (hA : loA + j + n + 2 ≤ arr.size)
    (hB : loB + n ≤ b.size) :
    (schoolbookDivModLimbs.correct2 arr b neg loA loB n j q₁ q₀ hA hB).size = arr.size := by
  unfold schoolbookDivModLimbs.correct2 schoolbookDivModLimbs.storeDigits
  simp only
  split
  · split
    · simp only [Array.size_set, addSameLengthLimbs_size]
    · simp only [Array.size_set, addSameLengthLimbs_size]
  · simp only [Array.size_set]

/-- A step with the trial digit `(q₁, q₀)` given: the row, then the correction. -/
@[inline]
def schoolbookDivModLimbs.finish2 (a b : Array UInt64) (loA loB n j : Nat) (q₁ q₀ : UInt64)
    (hA : loA + j + n + 2 ≤ a.size) (hB : loB + n ≤ b.size) : Array UInt64 :=
  let r := subMul2Limbs a b (loA + j) loB n q₀ q₁ hA hB
  schoolbookDivModLimbs.correct2 r.1 b r.2 loA loB n j q₁ q₀
    (by rw [subMul2Limbs_size]; exact hA) hB

/-- **One step producing two quotient limbs**: on the window `a[loA + j : loA + j + n + 2)`,
whose value is below `2^128 B` (`B` the divisor `b[loB : loB + n)`, normalized, `n ≥ 2`).
Afterwards the low `n` limbs of the window hold the remainder and its two top limbs the
quotient. -/
def schoolbookDivModLimbs.step2 (a b : Array UInt64) (loA loB n j : Nat) (d₁ d₀ v : UInt64)
    (hA : loA + j + n + 2 ≤ a.size) (hB : loB + n ≤ b.size) (hn : 2 ≤ n) : Array UInt64 :=
  let q := trialQuot2 (a[loA + j + n + 1]'(by omega)) (a[loA + j + n]'(by omega))
    (a[loA + j + (n - 2) + 1]'(by omega)) (a[loA + j + (n - 2)]'(by omega)) d₁ d₀ v
  schoolbookDivModLimbs.finish2 a b loA loB n j q.1 q.2 hA hB

/-- Size preservation of `step2`. -/
theorem schoolbookDivModLimbs.step2_size (a b : Array UInt64) (loA loB n j : Nat)
    (d₁ d₀ v : UInt64) (hA : loA + j + n + 2 ≤ a.size) (hB : loB + n ≤ b.size) (hn : 2 ≤ n) :
    (schoolbookDivModLimbs.step2 a b loA loB n j d₁ d₀ v hA hB hn).size = a.size := by
  unfold schoolbookDivModLimbs.step2 schoolbookDivModLimbs.finish2
  simp only
  rw [schoolbookDivModLimbs.correct2_size, subMul2Limbs_size]

/-- The loop of `schoolbookDivModLimbsFast`: the remaining `j` quotient limbs, two per step
(a last single one by the one-limb step of `schoolbookDivModLimbs.go`). -/
def schoolbookDivModLimbs.goFast (a b : Array UInt64) (loA loB n j : Nat) (d₁ d₀ v : UInt64)
    (hd : 2 ^ 63 ≤ d₁.toNat) (hA : loA + n + j ≤ a.size) (hB : loB + n ≤ b.size)
    (hn : 2 ≤ n) : Array UInt64 :=
  match j with
  | 0 => a
  | 1 => schoolbookDivModLimbs.go a b loA loB n 1 d₁ (UInt64.reciprocal d₁ hd) hA hB (by omega)
  | j + 2 =>
    schoolbookDivModLimbs.goFast
      (schoolbookDivModLimbs.step2 a b loA loB n j d₁ d₀ v (by omega) hB hn) b loA loB n j
      d₁ d₀ v hd (by rw [schoolbookDivModLimbs.step2_size]; omega) hB hn

/-- Size preservation of `goFast`. -/
theorem schoolbookDivModLimbs.goFast_size (a b : Array UInt64) (loA loB n j : Nat)
    (d₁ d₀ v : UInt64) (hd : 2 ^ 63 ≤ d₁.toNat) (hA : loA + n + j ≤ a.size)
    (hB : loB + n ≤ b.size) (hn : 2 ≤ n) :
    (schoolbookDivModLimbs.goFast a b loA loB n j d₁ d₀ v hd hA hB hn).size = a.size := by
  induction j using Nat.strong_induction_on generalizing a with
  | _ j ih =>
    match j with
    | 0 => rw [schoolbookDivModLimbs.goFast]
    | 1 => rw [schoolbookDivModLimbs.goFast, schoolbookDivModLimbs.go_size]
    | j + 2 =>
      rw [schoolbookDivModLimbs.goFast, ih j (by omega), schoolbookDivModLimbs.step2_size]

/-- **`schoolbookDivModLimbs` with two quotient limbs per pass**: same arguments, same result
(`schoolbookDivModLimbs_eq_fast`). -/
def schoolbookDivModLimbsFast (a b : Array UInt64) (loA loB n m : Nat)
    (h_n_pos : 0 < n) (hA : loA + n + m ≤ a.size) (hB : loB + n ≤ b.size)
    (hbn1 : 2 ^ 63 ≤ (b[loB + n - 1]'(by omega)).toNat) :
    Array UInt64 × UInt64 :=
  if hn : n < 2 then schoolbookDivModLimbs a b loA loB n m h_n_pos hA hB hbn1
  else
    let d₁ := b[loB + n - 1]'(by omega)
    let d₀ := b[loB + n - 2]'(by omega)
    let v := UInt64.reciprocal3By2 d₁ d₀ hbn1
    have h_top_slice : loA + m + n ≤ a.size := by omega
    if compareLimbs a b (loA + m) loB n h_top_slice hB = Ordering.lt then
      (schoolbookDivModLimbs.goFast a b loA loB n m d₁ d₀ v hbn1 (by omega) hB (by omega), 0)
    else
      let r := subSameLengthLimbs a b (loA + m) loB n h_top_slice hB
      have h_r_size : r.1.size = a.size := subSameLengthLimbs_size _ _ _ _ _ _ _
      (schoolbookDivModLimbs.goFast r.1 b loA loB n m d₁ d₀ v hbn1
        (by rw [h_r_size]; omega) hB (by omega), 1)

end Azurite.AzNat
