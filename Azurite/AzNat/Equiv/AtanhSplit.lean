/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.AtanhSplit
import Azurite.AzNat.Equiv.Add
import Azurite.AzNat.Equiv.Pow
import Azurite.BrentZimmermann.Chapter4.Ln2BinarySplitting

/-!
# Equivalence: the binary splitting of `atanh(1/q)` computes the exact partial sums

`Spec q l n x` says that the state `x = (T, B, Q)` represents the range `[l, l+n)`:
`B = ∏_{k<n} (2(l+k)+1)`, `Q = (q²)^n` and `T/(B Q) = ∑_{k<n} 1/((2(l+k)+1) q^(2(k+1)))` (as
reals).  The leaf and the merge preserve it (`spec_atanhLeaf`, `spec_splitMerge`), hence so do
the sequential fallback and the splitting with any fuel (`spec_atanhSeq`,
`spec_atanhSplitFuel`), and `atanhNumDen_eq` gives
`num/den = ∑_{k<N} atanhTerm q k`, the partial sum of `Ln2BinarySplitting.lean`.
-/

namespace Azurite.AzNat

open Finset

/-- The range `[l, l+n)` of the normalized series: `∑_{k<n} 1/((2(l+k)+1) q^(2(k+1)))`. -/
noncomputable def atanhPartial (q : ℝ) (l n : ℕ) : ℝ :=
  ∑ k ∈ range n, 1 / ((2 * ((l + k : ℕ) : ℝ) + 1) * q ^ (2 * (k + 1)))

/-- The state `(T, B, Q)` represents the range `[l, l+n)`. -/
def Spec (q l n : ℕ) (x : SplitState) : Prop :=
  x.2.1.toNat = ∏ k ∈ range n, (2 * (l + k) + 1) ∧ x.2.2.toNat = (q ^ 2) ^ n ∧
    (x.1.toNat : ℝ) / (x.2.1.toNat * x.2.2.toNat) = atanhPartial q l n

theorem spec_splitEmpty (q l : ℕ) : Spec q l 0 splitEmpty := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [splitEmpty, atanhPartial]

theorem spec_atanhLeaf (q l : ℕ) : Spec q l 1 (atanhLeaf (ofNat (q * q)) l) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [atanhLeaf, toNat_ofNat]
  · simp [atanhLeaf, toNat_ofNat, sq]
  · simp only [atanhLeaf, toNat_ofNat, atanhPartial, sum_range_one, Nat.add_zero]
    push_cast
    ring

/-- The merge: if `x` represents `[l, l+m)` and `y` represents `[l+m, l+m+n)`, then
`splitMerge x y` represents `[l, l+m+n)`. -/
theorem spec_splitMerge {q l m n : ℕ} (hq : 0 < q) {x y : SplitState} (hx : Spec q l m x)
    (hy : Spec q (l + m) n y) : Spec q l (m + n) (splitMerge x y) := by
  obtain ⟨hxB, hxQ, hxT⟩ := hx
  obtain ⟨hyB, hyQ, hyT⟩ := hy
  have hB1 : (0 : ℝ) < x.2.1.toNat := by
    rw [hxB]; exact_mod_cast prod_pos fun k _ => by omega
  have hB2 : (0 : ℝ) < y.2.1.toNat := by
    rw [hyB]; exact_mod_cast prod_pos fun k _ => by omega
  have hQ1 : (0 : ℝ) < x.2.2.toNat := by rw [hxQ]; positivity
  have hQ2 : (0 : ℝ) < y.2.2.toNat := by rw [hyQ]; positivity
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  refine ⟨?_, ?_, ?_⟩
  · simp only [splitMerge, toNat_mul, hxB, hyB, prod_range_add]
    congr 1
    exact prod_congr rfl fun k _ => by ring_nf
  · simp only [splitMerge, toNat_mul, hxQ, hyQ, pow_add]
  · -- the second range's terms carry the factor `1/Q₁`
    have hsplit : atanhPartial q l (m + n)
        = atanhPartial q l m + atanhPartial q (l + m) n / ((q : ℝ) ^ 2) ^ m := by
      unfold atanhPartial
      rw [sum_range_add, sum_div]
      congr 1
      refine sum_congr rfl fun k _ => ?_
      rw [show l + (m + k) = l + m + k by omega, show 2 * (m + k + 1) = 2 * (k + 1) + 2 * m by ring,
        pow_add, ← pow_mul, div_div]
      ring
    simp only [splitMerge, toNat_add, toNat_mul]
    push_cast
    rw [hsplit, ← hxT, ← hyT, hxQ]
    push_cast
    have hB1' := hB1.ne'
    have hB2' := hB2.ne'
    have hQ2' := hQ2.ne'
    have hqr' := hqr.ne'
    field_simp

/-- The sequential fallback represents its range. -/
theorem spec_atanhSeq {q : ℕ} (hq : 0 < q) : ∀ n l, Spec q l n (atanhSeq (ofNat (q * q)) l n)
  | 0, l => spec_splitEmpty q l
  | n + 1, l => by
    rw [atanhSeq, show n + 1 = 1 + n by ring]
    exact spec_splitMerge hq (spec_atanhLeaf q l) (spec_atanhSeq hq n (l + 1))

/-- The splitting represents its range, for every fuel. -/
theorem spec_atanhSplitFuel {q : ℕ} (hq : 0 < q) :
    ∀ fuel l n, Spec q l n (atanhSplitFuel (ofNat (q * q)) fuel l n)
  | 0, l, n => by rw [atanhSplitFuel]; exact spec_atanhSeq hq n l
  | _ + 1, l, 0 => by rw [atanhSplitFuel]; exact spec_splitEmpty q l
  | _ + 1, l, 1 => by rw [atanhSplitFuel]; exact spec_atanhLeaf q l
  | fuel + 1, l, n + 2 => by
    simp only [atanhSplitFuel]
    have hm : (n + 2) / 2 ≤ n + 2 := Nat.div_le_self _ _
    have h := spec_splitMerge hq (spec_atanhSplitFuel hq fuel l ((n + 2) / 2))
      (spec_atanhSplitFuel hq fuel (l + (n + 2) / 2) (n + 2 - (n + 2) / 2))
    rwa [Nat.add_sub_cancel' hm] at h

theorem spec_atanhSplit {q : ℕ} (hq : 0 < q) (l n : ℕ) :
    Spec q l n (atanhSplit (ofNat (q * q)) l n) :=
  spec_atanhSplitFuel hq n l n

/-- The denominator `B · Q` is positive. -/
theorem atanhNumDen_den_pos {q : ℕ} (hq : 0 < q) (N : ℕ) : 0 < (atanhNumDen q N).2.toNat := by
  obtain ⟨hB, hQ, -⟩ := spec_atanhSplit hq (q := q) 0 N
  simp only [atanhNumDen, toNat_mul]
  rw [hB, hQ]
  exact Nat.mul_pos (prod_pos fun k _ => by omega) (by positivity)

/-- **The binary splitting computes the exact partial sum**:
`num/den = ∑_{k<N} 1/((2k+1) q^(2k+1))`. -/
theorem atanhNumDen_eq {q : ℕ} (hq : 0 < q) (N : ℕ) :
    ((atanhNumDen q N).1.toNat : ℝ) / (atanhNumDen q N).2.toNat
      = ∑ k ∈ range N, BZ.atanhTerm q k := by
  obtain ⟨-, -, hT⟩ := spec_atanhSplit hq (q := q) 0 N
  simp only [atanhNumDen, toNat_mul, toNat_ofNat]
  push_cast
  rw [mul_div_assoc, hT, atanhPartial, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [BZ.atanhTerm]
  simp only [zero_add]
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hk : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
  rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, pow_succ]
  field_simp

end Azurite.AzNat
