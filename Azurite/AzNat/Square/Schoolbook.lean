/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Mul
import Azurite.UInt64.AddWithCarry

/-!
# Schoolbook squaring for `AzNat` limb slices

`schoolbookSquareLimbs` computes the square of a limb slice with roughly
half the `wideMul` operations of `schoolbookMulLimbs`, by exploiting the
symmetry `a_i · a_j = a_j · a_i`.

The algorithm has three phases:

1. **Off-diagonal accumulation.** For each `i ∈ [0, len - 1)`, fuse-add
   `a[lo+i+1 .. lo+len) * a[lo+i]` into the accumulator at offset
   `2i + 1`, using the existing `mulAddLimbs`. After this phase the
   accumulator holds `Σ_{i < j} a_i · a_j · 2^{64·(i+j)}`.

2. **Doubling.** Shift the accumulator left by `1` bit, giving
   `2 · Σ_{i < j} a_i · a_j · 2^{64·(i+j)}`. The carry-out is `0`
   because the off-diagonal sum is bounded by `N² / 2` where `N` is
   the input value.

3. **Diagonal addition.** For each `i ∈ [0, len)`, add the `wideMul
   a_i a_i = (hi, lo)` at accumulator positions `(2i, 2i+1)` with
   carry propagation. The accumulator then holds `N²`.

The wideMul count drops from `len²` (schoolbook) to `len·(len-1)/2 + len
= len·(len+1)/2`, asymptotically half.
-/

namespace Azurite.AzNat

/-! ### Carry propagation -/

/-- Propagate a single Bool `carry` through `acc` starting at index `pos`,
    until either the carry becomes `false` or we reach the end of `acc`.
    If the carry would propagate past `acc.size`, it is silently dropped
    (caller responsibility to pre-allocate enough room). -/
def propagateCarry (acc : Array UInt64) (pos : Nat) (carry : Bool) :
    Array UInt64 :=
  match carry with
  | false => acc
  | true =>
    if h : pos < acc.size then
      let r := UInt64.addWithCarry acc[pos] 0 true
      propagateCarry (acc.set pos r.1) (pos + 1) r.2
    else
      acc
  termination_by acc.size - pos

theorem propagateCarry_size (acc : Array UInt64) (pos : Nat) (carry : Bool) :
    (propagateCarry acc pos carry).size = acc.size := by
  induction h_sub : acc.size - pos generalizing acc pos carry with
  | zero =>
    have h_ge : acc.size ≤ pos := by omega
    cases carry with
    | false => rw [propagateCarry]
    | true =>
      rw [propagateCarry]; simp [Nat.not_lt.mpr h_ge]
  | succ n ih =>
    cases carry with
    | false => rw [propagateCarry]
    | true =>
      rw [propagateCarry]
      have h_lt : pos < acc.size := by omega
      simp only [h_lt, ↓reduceDIte]
      rw [ih]
      · rw [Array.size_set]
      · rw [Array.size_set]; omega

/-! ### In-place doubling of an accumulator (shift left by 1 bit) -/

/-- Inner loop of `doubleLimbs`. At index `k`, replaces `acc[k]` with
    `(2 · acc[k] + carry) mod 2^64`, where `carry ∈ {0, 1}` is the
    overflow bit from the previous limb. Implemented via
    `UInt64.addWithCarry acc[k] acc[k] carry`, which threads the
    overflow bit naturally. Returns the resulting array; the final
    carry-out is silently dropped. -/
def doubleLimbs.go (acc : Array UInt64) (k : Nat) (carry : Bool) :
    Array UInt64 :=
  if h : k < acc.size then
    let r := UInt64.addWithCarry acc[k] acc[k] carry
    doubleLimbs.go (acc.set k r.1) (k + 1) r.2
  else
    acc
  termination_by acc.size - k

/-- Multiply `acc` by `2` (in place), interpreting `acc` as an LSB-first
    limb-list. The carry-out (a single bit at position `acc.size`) is
    silently dropped. -/
def doubleLimbs (acc : Array UInt64) : Array UInt64 :=
  doubleLimbs.go acc 0 false

theorem doubleLimbs.go_size (acc : Array UInt64) (k : Nat) (carry : Bool) :
    (doubleLimbs.go acc k carry).size = acc.size := by
  induction h_sub : acc.size - k generalizing acc k carry with
  | zero =>
    have h_ge : acc.size ≤ k := by omega
    rw [doubleLimbs.go]; simp [Nat.not_lt.mpr h_ge]
  | succ n ih =>
    have h_lt : k < acc.size := by omega
    rw [doubleLimbs.go]
    simp only [h_lt, ↓reduceDIte]
    rw [ih]
    · rw [Array.size_set]
    · rw [Array.size_set]; omega

theorem doubleLimbs_size (acc : Array UInt64) :
    (doubleLimbs acc).size = acc.size :=
  doubleLimbs.go_size acc 0 false

/-! ### Diagonal addition -/

/-- For each `i ∈ [start, len)`, compute `(hi, lo) := wideMul a[lo+i] a[lo+i]`
    and add the 128-bit number `hi · 2^64 + lo` to `acc[2i .. 2i+1]`,
    propagating any carry through the higher limbs. The accumulator must
    already have `2 * len ≤ acc.size`. -/
def addDiagonalLimbs.go (a : Array UInt64) (lo len : Nat) (acc : Array UInt64)
    (i : Nat) (hA : lo + len ≤ a.size) (hAcc : 2 * len ≤ acc.size) :
    Array UInt64 :=
  if h : i < len then
    have h_idx : lo + i < a.size := by omega
    have h_acc_lo : 2 * i < acc.size := by omega
    let x := a[lo + i]
    let p := UInt64.wideMul x x
    let r0 := UInt64.addWithCarry acc[2 * i] p.2 false
    let acc1 := acc.set (2 * i) r0.1
    have hAcc1 : 2 * len ≤ acc1.size := by rw [Array.size_set]; exact hAcc
    have h_acc_hi : 2 * i + 1 < acc1.size := by
      rw [Array.size_set]; omega
    let r1 := UInt64.addWithCarry acc1[2 * i + 1] p.1 r0.2
    let acc2 := acc1.set (2 * i + 1) r1.1
    have hAcc2 : 2 * len ≤ acc2.size := by rw [Array.size_set]; exact hAcc1
    let acc3 := propagateCarry acc2 (2 * i + 2) r1.2
    have hAcc3 : 2 * len ≤ acc3.size := by
      rw [propagateCarry_size]; exact hAcc2
    addDiagonalLimbs.go a lo len acc3 (i + 1) hA hAcc3
  else
    acc
  termination_by len - i

/-- Add the diagonal squares `Σ_i a[lo+i]² · 2^{128i}` into `acc`. -/
def addDiagonalLimbs (a : Array UInt64) (lo len : Nat) (acc : Array UInt64)
    (hA : lo + len ≤ a.size) (hAcc : 2 * len ≤ acc.size) : Array UInt64 :=
  addDiagonalLimbs.go a lo len acc 0 hA hAcc

theorem addDiagonalLimbs.go_size (a : Array UInt64) (lo len : Nat)
    (acc : Array UInt64) (i : Nat)
    (hA : lo + len ≤ a.size) (hAcc : 2 * len ≤ acc.size) :
    (addDiagonalLimbs.go a lo len acc i hA hAcc).size = acc.size := by
  induction h_sub : len - i generalizing acc i with
  | zero =>
    have h_ge : len ≤ i := by omega
    rw [addDiagonalLimbs.go]; simp [Nat.not_lt.mpr h_ge]
  | succ n ih =>
    have h_lt : i < len := by omega
    have h_sub' : len - (i + 1) = n := by omega
    rw [addDiagonalLimbs.go]
    simp only [h_lt, ↓reduceDIte]
    rw [ih _ _ _ h_sub']
    rw [propagateCarry_size, Array.size_set, Array.size_set]

theorem addDiagonalLimbs_size (a : Array UInt64) (lo len : Nat)
    (acc : Array UInt64)
    (hA : lo + len ≤ a.size) (hAcc : 2 * len ≤ acc.size) :
    (addDiagonalLimbs a lo len acc hA hAcc).size = acc.size :=
  addDiagonalLimbs.go_size a lo len acc 0 hA hAcc

/-! ### Off-diagonal accumulation -/

/-- Outer loop of the off-diagonal accumulation. For each `i ∈ [start,
    len - 1)`, fuse-add `a[lo+i+1 .. lo+len) * a[lo+i]` into the
    accumulator starting at index `2i + 1`, then stores the final carry
    from `mulAddLimbs` at `acc[i + len]` (which will be picked up by the
    next iteration's fuse-add as the last limb of its accumulator range,
    or, for the last iteration `i = len - 2`, remains as the final
    carry deposit at `acc[2 len - 2]`). -/
def schoolbookSquareLimbs.offDiag.go (a : Array UInt64) (lo len : Nat)
    (acc : Array UInt64) (i : Nat)
    (hA : lo + len ≤ a.size) (hAcc : 2 * len ≤ acc.size) : Array UInt64 :=
  if h : i + 1 < len then
    have h_inner_len : (lo + i + 1) + (len - i - 1) ≤ a.size := by omega
    have h_idx : lo + i < a.size := by omega
    have h_acc_row : (2 * i + 1) + (len - i - 1) ≤ acc.size := by omega
    let r := mulAddLimbs a (lo + i + 1) (len - i - 1) (2 * i + 1) a[lo + i]
              acc h_inner_len h_acc_row
    have h_r_size : r.1.size = acc.size := mulAddLimbs_size _ _ _ _ _ _ _ _
    have h_carry_idx : (2 * i + 1) + (len - i - 1) < r.1.size := by
      rw [h_r_size]; omega
    schoolbookSquareLimbs.offDiag.go a lo len
      (r.1.set ((2 * i + 1) + (len - i - 1)) r.2) (i + 1) hA
      (by rw [Array.size_set, h_r_size]; exact hAcc)
  else
    acc
  termination_by len - i

/-- Accumulate the off-diagonal contribution `Σ_{i < j} a[lo+i] · a[lo+j]
    · 2^{64·(i+j)}` into `acc`. -/
def schoolbookSquareLimbs.offDiag (a : Array UInt64) (lo len : Nat)
    (acc : Array UInt64)
    (hA : lo + len ≤ a.size) (hAcc : 2 * len ≤ acc.size) : Array UInt64 :=
  schoolbookSquareLimbs.offDiag.go a lo len acc 0 hA hAcc

theorem schoolbookSquareLimbs.offDiag.go_size (a : Array UInt64) (lo len : Nat)
    (acc : Array UInt64) (i : Nat)
    (hA : lo + len ≤ a.size) (hAcc : 2 * len ≤ acc.size) :
    (schoolbookSquareLimbs.offDiag.go a lo len acc i hA hAcc).size = acc.size := by
  induction h_sub : len - i generalizing acc i with
  | zero =>
    have h_ge : len ≤ i := by omega
    rw [schoolbookSquareLimbs.offDiag.go]
    have h_neg : ¬ i + 1 < len := by omega
    simp [h_neg]
  | succ n ih =>
    rw [schoolbookSquareLimbs.offDiag.go]
    by_cases h_lt : i + 1 < len
    · have h_sub' : len - (i + 1) = n := by omega
      simp only [h_lt, ↓reduceDIte]
      rw [ih _ _ _ h_sub']
      rw [Array.size_set, mulAddLimbs_size]
    · simp [h_lt]

theorem schoolbookSquareLimbs.offDiag_size (a : Array UInt64) (lo len : Nat)
    (acc : Array UInt64)
    (hA : lo + len ≤ a.size) (hAcc : 2 * len ≤ acc.size) :
    (schoolbookSquareLimbs.offDiag a lo len acc hA hAcc).size = acc.size :=
  schoolbookSquareLimbs.offDiag.go_size a lo len acc 0 hA hAcc

/-! ### Top-level: `schoolbookSquareLimbs` -/

/-- Schoolbook squaring of the limb slice `a[lo .. lo + len)`, producing a
    fresh array of size `2 · len`. Performs `len·(len+1)/2` `wideMul`
    operations versus `len²` for `schoolbookMulLimbs`. -/
def schoolbookSquareLimbs (a : Array UInt64) (lo len : Nat)
    (hA : lo + len ≤ a.size) : Array UInt64 :=
  let acc := Array.replicate (2 * len) 0
  have hAcc : 2 * len ≤ acc.size := by rw [Array.size_replicate]
  let acc1 := schoolbookSquareLimbs.offDiag a lo len acc hA hAcc
  have hAcc1 : 2 * len ≤ acc1.size := by
    rw [schoolbookSquareLimbs.offDiag_size]; exact hAcc
  let acc2 := doubleLimbs acc1
  have hAcc2 : 2 * len ≤ acc2.size := by
    rw [doubleLimbs_size]; exact hAcc1
  addDiagonalLimbs a lo len acc2 hA hAcc2

theorem schoolbookSquareLimbs_size (a : Array UInt64) (lo len : Nat)
    (hA : lo + len ≤ a.size) :
    (schoolbookSquareLimbs a lo len hA).size = 2 * len := by
  unfold schoolbookSquareLimbs
  rw [addDiagonalLimbs_size, doubleLimbs_size,
      schoolbookSquareLimbs.offDiag_size, Array.size_replicate]

end Azurite.AzNat
