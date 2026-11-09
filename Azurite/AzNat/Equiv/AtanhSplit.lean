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
import Azurite.BrentZimmermann.Chapter4.PiBinarySplitting

/-!
# Equivalence: the binary splitting computes the exact partial sums

For a series `∑_k a k / (b k · r^(k+1))` (`SplitSeries`: `a k`, `b k` the numerator and the small
denominator factor of the term of index `k`, `r` the ratio), `SpecOf s l n x` says that the state
`x = (T, B, Q)` represents the range `[l, l+n)`: `B = ∏_{k<n} b (l+k)`, `Q = r^n` and
`T/(B Q) = ∑_{k<n} a (l+k) / (b (l+k) r^(k+1))` (as reals).  If the leaf represents its single
term, the merge preserves the invariant (`spec_splitMerge`), hence so do the sequential fallback
and the splitting with any fuel (`spec_seqOf`, `spec_splitFuelOf`, `spec_splitOf`).  Instances:
`atanh(1/q)` (`a = 1`, `b k = 2k+1`, `r = q²`; `atanhNumDen_eq` gives
`num/den = ∑_{k<N} atanhTerm q k`, the partial sum of `Ln2BinarySplitting.lean`) and
`arctan(1/q)` by pairs of terms (`a j = (4j+3) q² − (4j+1)`, `b j = (4j+1)(4j+3)`, `r = q⁴`;
`atanNumDen_eq` gives `num/den = ∑_{j<N} atanPair q j`, the pair sums of
`PiBinarySplitting.lean`).
-/

namespace Azurite.AzNat

open Finset

/-! ### The generic engine -/

/-- A series `∑_k a k / (b k · r^(k+1))` for binary splitting: the term of index `k` has the
real numerator `a k`, the positive small denominator factor `b k`, and the ratio `r` is positive.
-/
structure SplitSeries where
  /-- The numerator of the term of index `k`. -/
  a : ℕ → ℝ
  /-- The small denominator factor of the term of index `k`. -/
  b : ℕ → ℕ
  /-- The ratio: the term of index `k` carries `1/r^(k+1)` relative to the range start. -/
  r : ℕ
  b_pos : ∀ k, 0 < b k
  r_pos : 0 < r

/-- The range `[l, l+n)` of the series, normalized to its start:
`∑_{k<n} a (l+k) / (b (l+k) r^(k+1))`. -/
noncomputable def SplitSeries.partial (s : SplitSeries) (l n : ℕ) : ℝ :=
  ∑ k ∈ range n, s.a (l + k) / ((s.b (l + k) : ℝ) * (s.r : ℝ) ^ (k + 1))

/-- The state `(T, B, Q)` represents the range `[l, l+n)`. -/
def SpecOf (s : SplitSeries) (l n : ℕ) (x : SplitState) : Prop :=
  x.2.1.toNat = ∏ k ∈ range n, s.b (l + k) ∧ x.2.2.toNat = s.r ^ n ∧
    (x.1.toNat : ℝ) / (x.2.1.toNat * x.2.2.toNat) = s.partial l n

theorem spec_splitEmpty (s : SplitSeries) (l : ℕ) : SpecOf s l 0 splitEmpty := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [splitEmpty, SplitSeries.partial]

/-- The merge: if `x` represents `[l, l+m)` and `y` represents `[l+m, l+m+n)`, then
`splitMerge x y` represents `[l, l+m+n)`. -/
theorem spec_splitMerge {s : SplitSeries} {l m n : ℕ} {x y : SplitState} (hx : SpecOf s l m x)
    (hy : SpecOf s (l + m) n y) : SpecOf s l (m + n) (splitMerge x y) := by
  obtain ⟨hxB, hxQ, hxT⟩ := hx
  obtain ⟨hyB, hyQ, hyT⟩ := hy
  have hB1 : (0 : ℝ) < x.2.1.toNat := by
    rw [hxB]; exact_mod_cast prod_pos fun k _ => s.b_pos _
  have hB2 : (0 : ℝ) < y.2.1.toNat := by
    rw [hyB]; exact_mod_cast prod_pos fun k _ => s.b_pos _
  have hr : (0 : ℝ) < s.r := by exact_mod_cast s.r_pos
  have hQ1 : (0 : ℝ) < x.2.2.toNat := by rw [hxQ]; exact_mod_cast pow_pos s.r_pos _
  have hQ2 : (0 : ℝ) < y.2.2.toNat := by rw [hyQ]; exact_mod_cast pow_pos s.r_pos _
  refine ⟨?_, ?_, ?_⟩
  · simp only [splitMerge, toNat_mul, hxB, hyB, prod_range_add]
    congr 1
    exact prod_congr rfl fun k _ => by rw [add_assoc]
  · simp only [splitMerge, toNat_mul, hxQ, hyQ, pow_add]
  · -- the second range's terms carry the factor `1/Q₁`
    have hsplit : s.partial l (m + n) = s.partial l m + s.partial (l + m) n / (s.r : ℝ) ^ m := by
      unfold SplitSeries.partial
      rw [sum_range_add, sum_div]
      congr 1
      refine sum_congr rfl fun k _ => ?_
      rw [show l + (m + k) = l + m + k by omega, show m + k + 1 = (k + 1) + m by ring, pow_add,
        div_div]
      ring
    simp only [splitMerge, toNat_add, toNat_mul]
    push_cast
    rw [hsplit, ← hxT, ← hyT, hxQ]
    push_cast
    have hB1' := hB1.ne'
    have hB2' := hB2.ne'
    have hQ2' := hQ2.ne'
    have hr' := hr.ne'
    field_simp

/-- The sequential fallback represents its range, if the leaf represents its term. -/
theorem spec_seqOf {s : SplitSeries} {leaf : ℕ → SplitState} (hleaf : ∀ l, SpecOf s l 1 (leaf l)) :
    ∀ n l, SpecOf s l n (seqOf leaf l n)
  | 0, l => spec_splitEmpty s l
  | n + 1, l => by
    rw [seqOf, show n + 1 = 1 + n by ring]
    exact spec_splitMerge (hleaf l) (spec_seqOf hleaf n (l + 1))

/-- The splitting represents its range, for every fuel. -/
theorem spec_splitFuelOf {s : SplitSeries} {leaf : ℕ → SplitState}
    (hleaf : ∀ l, SpecOf s l 1 (leaf l)) :
    ∀ fuel l n, SpecOf s l n (splitFuelOf leaf fuel l n)
  | 0, l, n => by rw [splitFuelOf]; exact spec_seqOf hleaf n l
  | _ + 1, l, 0 => by rw [splitFuelOf]; exact spec_splitEmpty s l
  | _ + 1, l, 1 => by rw [splitFuelOf]; exact hleaf l
  | fuel + 1, l, n + 2 => by
    simp only [splitFuelOf]
    have hm : (n + 2) / 2 ≤ n + 2 := Nat.div_le_self _ _
    have h := spec_splitMerge (spec_splitFuelOf hleaf fuel l ((n + 2) / 2))
      (spec_splitFuelOf hleaf fuel (l + (n + 2) / 2) (n + 2 - (n + 2) / 2))
    rwa [Nat.add_sub_cancel' hm] at h

theorem spec_splitOf {s : SplitSeries} {leaf : ℕ → SplitState}
    (hleaf : ∀ l, SpecOf s l 1 (leaf l)) (l n : ℕ) : SpecOf s l n (splitOf leaf l n) :=
  spec_splitFuelOf hleaf n l n

/-- The denominator `B · Q` of a split range is positive. -/
theorem SpecOf.den_pos {s : SplitSeries} {l n : ℕ} {x : SplitState} (h : SpecOf s l n x) :
    0 < (x.2.1 * x.2.2).toNat := by
  obtain ⟨hB, hQ, -⟩ := h
  rw [toNat_mul, hB, hQ]
  exact Nat.mul_pos (prod_pos fun k _ => s.b_pos _) (pow_pos s.r_pos _)

/-! ### `atanh(1/q)` -/

/-- The series of `atanh(1/q)`: `a = 1`, `b k = 2k + 1`, `r = q²`. -/
def atanhSeries (q : ℕ) (hq : 0 < q) : SplitSeries :=
  ⟨fun _ => 1, fun k => 2 * k + 1, q ^ 2, fun _ => by omega, by positivity⟩

theorem spec_atanhLeaf {q : ℕ} (hq : 0 < q) (l : ℕ) :
    SpecOf (atanhSeries q hq) l 1 (atanhLeaf (ofNat (q * q)) l) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [atanhLeaf, toNat_ofNat, atanhSeries]
  · simp [atanhLeaf, toNat_ofNat, atanhSeries, sq]
  · simp only [atanhLeaf, toNat_ofNat, atanhSeries, SplitSeries.partial, sum_range_one,
      Nat.add_zero]
    push_cast
    ring

theorem spec_atanhSplit {q : ℕ} (hq : 0 < q) (l n : ℕ) :
    SpecOf (atanhSeries q hq) l n (atanhSplit (ofNat (q * q)) l n) :=
  spec_splitOf (spec_atanhLeaf hq) l n

/-- The denominator `B · Q` is positive. -/
theorem atanhNumDen_den_pos {q : ℕ} (hq : 0 < q) (N : ℕ) : 0 < (atanhNumDen q N).2.toNat :=
  (spec_atanhSplit hq 0 N).den_pos

/-- **The binary splitting computes the exact partial sum**:
`num/den = ∑_{k<N} 1/((2k+1) q^(2k+1))`. -/
theorem atanhNumDen_eq {q : ℕ} (hq : 0 < q) (N : ℕ) :
    ((atanhNumDen q N).1.toNat : ℝ) / (atanhNumDen q N).2.toNat
      = ∑ k ∈ range N, BZ.atanhTerm q k := by
  obtain ⟨-, -, hT⟩ := spec_atanhSplit hq 0 N
  simp only [atanhNumDen, toNat_mul, toNat_ofNat]
  push_cast
  rw [mul_div_assoc, hT, SplitSeries.partial, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  simp only [atanhSeries, BZ.atanhTerm, zero_add]
  push_cast
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hk : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
  rw [← pow_mul, show 2 * (k + 1) = 2 * k + 1 + 1 by ring, pow_succ]
  field_simp

/-! ### `arctan(1/q)` by pairs -/

/-- The series of pairs of `arctan(1/q)`: `a j = (4j+3) q² − (4j+1)`, `b j = (4j+1)(4j+3)`,
`r = q⁴`. -/
def atanSeries (q : ℕ) (hq : 0 < q) : SplitSeries :=
  ⟨fun j => (((4 * j + 3) * (q * q) - (4 * j + 1) : ℕ) : ℝ), fun j => (4 * j + 1) * (4 * j + 3),
    q ^ 4, fun _ => by positivity, by positivity⟩

theorem spec_atanLeaf {q : ℕ} (hq : 0 < q) (l : ℕ) :
    SpecOf (atanSeries q hq) l 1 (atanLeaf q (ofNat (q * q * (q * q))) l) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [atanLeaf, toNat_ofNat, atanSeries]
  · simp only [atanLeaf, toNat_ofNat, atanSeries, pow_one]; ring
  · simp only [atanLeaf, toNat_ofNat, atanSeries, SplitSeries.partial, sum_range_one,
      Nat.add_zero]
    push_cast
    ring

theorem spec_atanSplit {q : ℕ} (hq : 0 < q) (l n : ℕ) :
    SpecOf (atanSeries q hq) l n (splitOf (atanLeaf q (ofNat (q * q * (q * q)))) l n) :=
  spec_splitOf (spec_atanLeaf hq) l n

/-- The denominator `B · Q` is positive. -/
theorem atanNumDen_den_pos {q : ℕ} (hq : 0 < q) (N : ℕ) : 0 < (atanNumDen q N).2.toNat :=
  (spec_atanSplit hq 0 N).den_pos

/-- **The binary splitting computes the exact pair sums**:
`num/den = ∑_{j<N} [1/((4j+1) q^(4j+1)) − 1/((4j+3) q^(4j+3))]`. -/
theorem atanNumDen_eq {q : ℕ} (hq : 0 < q) (N : ℕ) :
    ((atanNumDen q N).1.toNat : ℝ) / (atanNumDen q N).2.toNat
      = ∑ j ∈ range N, BZ.atanPair q j := by
  obtain ⟨-, -, hT⟩ := spec_atanSplit hq 0 N
  simp only [atanNumDen, toNat_mul, toNat_ofNat]
  push_cast
  rw [mul_div_assoc, hT, SplitSeries.partial, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  simp only [atanSeries, BZ.atanPair, BZ.atanTerm, zero_add]
  have hsub : 4 * j + 1 ≤ (4 * j + 3) * (q * q) := by
    have : 1 ≤ q * q := Nat.one_le_iff_ne_zero.mpr (by positivity)
    nlinarith
  rw [Nat.cast_sub hsub]
  push_cast
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have h1 : (4 * (j : ℝ) + 1) ≠ 0 := by positivity
  have h3 : (4 * (j : ℝ) + 3) ≠ 0 := by positivity
  rw [← pow_mul, show 2 * (2 * j) + 1 = 4 * j + 1 by ring,
    show 2 * (2 * j + 1) + 1 = 4 * j + 3 by ring,
    show 4 * (j + 1) = 4 * j + 3 + 1 by ring, pow_succ,
    show 4 * j + 3 = 4 * j + 1 + 2 by ring, pow_add]
  field_simp
  ring

end Azurite.AzNat
