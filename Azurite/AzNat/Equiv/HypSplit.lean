/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.HypSplit
import Azurite.AzNat.Equiv.AtanhSplit
import Azurite.Transcendental.Catalan

/-!
# Equivalence: the hypergeometric binary splitting computes the exact partial sums

For a series `∑_k ∏_{j≤k} p(j)/q(j)` (`HypSeries`: natural `p`, positive natural `q`),
`HypSpec s l n x` says that the state `x = (P, Q, T)` represents the range `[l, l+n)`:
`P = ∏_{k<n} p(l+k)`, `Q = ∏_{k<n} q(l+k)` and `T/Q = ∑_{k<n} ∏_{j≤k} p(l+j)/q(l+j)` (as reals).
The merge preserves the invariant (`hypSpec_merge`), hence so do the sequential fallback and the
splitting with any fuel (`hypSpec_seq`, `hypSpec_splitFuel`, `hypSpec_split`).

Instances: `catalanNumDen_eq` (`num/den = (3/8) ∑_{k<N} 1/((2k+1)² C(2k,k))`) and
`atanhSqrtThreeNumDen_eq` (`num/den = (1/4) ∑_{k<N} 1/((2k+1) 3^{k+1})`, with the `(T, B, Q)`
engine of `AtanhSplit.lean`), the two series of `Azurite/Transcendental/Catalan.lean`.
-/

namespace Azurite.AzNat

open Finset

/-! ### The generic engine -/

/-- A series `∑_k ∏_{j≤k} p(j)/q(j)` for binary splitting. -/
structure HypSeries where
  /-- The numerator of the ratio of the term of index `k` to the previous one. -/
  p : ℕ → ℕ
  /-- The denominator of the ratio of the term of index `k` to the previous one. -/
  q : ℕ → ℕ
  q_pos : ∀ k, 0 < q k

/-- The range `[l, l+n)` of the series, normalized to its start:
`∑_{k<n} ∏_{j≤k} p(l+j)/q(l+j)`. -/
noncomputable def HypSeries.partial (s : HypSeries) (l n : ℕ) : ℝ :=
  ∑ k ∈ range n, ∏ j ∈ range (k + 1), ((s.p (l + j) : ℝ) / s.q (l + j))

/-- The state `(P, Q, T)` represents the range `[l, l+n)`. -/
def HypSpec (s : HypSeries) (l n : ℕ) (x : HypState) : Prop :=
  x.1.toNat = ∏ k ∈ range n, s.p (l + k) ∧ x.2.1.toNat = ∏ k ∈ range n, s.q (l + k) ∧
    (x.2.2.toNat : ℝ) / x.2.1.toNat = s.partial l n

theorem hypSpec_empty (s : HypSeries) (l : ℕ) : HypSpec s l 0 hypEmpty := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [hypEmpty, HypSeries.partial]

/-- The merge: if `x` represents `[l, l+m)` and `y` represents `[l+m, l+m+n)`, then
`hypMerge x y` represents `[l, l+m+n)`. -/
theorem hypSpec_merge {s : HypSeries} {l m n : ℕ} {x y : HypState} (hx : HypSpec s l m x)
    (hy : HypSpec s (l + m) n y) : HypSpec s l (m + n) (hypMerge x y) := by
  obtain ⟨hxP, hxQ, hxT⟩ := hx
  obtain ⟨hyP, hyQ, hyT⟩ := hy
  have hQ1 : (0 : ℝ) < x.2.1.toNat := by
    rw [hxQ]; exact_mod_cast prod_pos fun k _ => s.q_pos _
  have hQ2 : (0 : ℝ) < y.2.1.toNat := by
    rw [hyQ]; exact_mod_cast prod_pos fun k _ => s.q_pos _
  refine ⟨?_, ?_, ?_⟩
  · simp only [hypMerge, toNat_mul, hxP, hyP, prod_range_add]
    congr 1
    exact prod_congr rfl fun k _ => by rw [add_assoc]
  · simp only [hypMerge, toNat_mul, hxQ, hyQ, prod_range_add]
    congr 1
    exact prod_congr rfl fun k _ => by rw [add_assoc]
  · -- the second range's terms carry the factor `P₁/Q₁`
    have hsplit : s.partial l (m + n) = s.partial l m +
        (∏ j ∈ range m, ((s.p (l + j) : ℝ) / s.q (l + j))) * s.partial (l + m) n := by
      unfold HypSeries.partial
      rw [sum_range_add, mul_sum]
      congr 1
      refine sum_congr rfl fun k _ => ?_
      rw [show m + k + 1 = m + (k + 1) by ring, prod_range_add]
      congr 1
      exact prod_congr rfl fun j _ => by rw [add_assoc]
    have hPQ : ∏ j ∈ range m, ((s.p (l + j) : ℝ) / s.q (l + j)) =
        (x.1.toNat : ℝ) / x.2.1.toNat := by
      rw [prod_div_distrib, hxP, hxQ]
      push_cast
      rfl
    simp only [hypMerge, toNat_add, toNat_mul]
    push_cast
    rw [hsplit, hPQ, ← hxT, ← hyT]
    have h1 := hQ1.ne'
    have h2 := hQ2.ne'
    field_simp

/-- The sequential fallback represents its range, if the leaf represents its term. -/
theorem hypSpec_seq {s : HypSeries} {leaf : ℕ → HypState} (hleaf : ∀ l, HypSpec s l 1 (leaf l)) :
    ∀ n l, HypSpec s l n (hypSeq leaf l n)
  | 0, l => hypSpec_empty s l
  | n + 1, l => by
    rw [hypSeq, show n + 1 = 1 + n by ring]
    exact hypSpec_merge (hleaf l) (hypSpec_seq hleaf n (l + 1))

/-- The splitting represents its range, for every fuel. -/
theorem hypSpec_splitFuel {s : HypSeries} {leaf : ℕ → HypState}
    (hleaf : ∀ l, HypSpec s l 1 (leaf l)) :
    ∀ fuel l n, HypSpec s l n (hypSplitFuel leaf fuel l n)
  | 0, l, n => by rw [hypSplitFuel]; exact hypSpec_seq hleaf n l
  | _ + 1, l, 0 => by rw [hypSplitFuel]; exact hypSpec_empty s l
  | _ + 1, l, 1 => by rw [hypSplitFuel]; exact hleaf l
  | fuel + 1, l, n + 2 => by
    simp only [hypSplitFuel]
    have hm : (n + 2) / 2 ≤ n + 2 := Nat.div_le_self _ _
    have h := hypSpec_merge (hypSpec_splitFuel hleaf fuel l ((n + 2) / 2))
      (hypSpec_splitFuel hleaf fuel (l + (n + 2) / 2) (n + 2 - (n + 2) / 2))
    rwa [Nat.add_sub_cancel' hm] at h

theorem hypSpec_split {s : HypSeries} {leaf : ℕ → HypState}
    (hleaf : ∀ l, HypSpec s l 1 (leaf l)) (l n : ℕ) : HypSpec s l n (hypSplit leaf l n) :=
  hypSpec_splitFuel hleaf n l n

/-! ### `∑ 1/((2k+1)² C(2k,k))` -/

/-- The series `∑ 1/((2k+1)² C(2k,k))`: `p(0) = q(0) = 1`, `p(k) = k(2k−1)`,
`q(k) = 2(2k+1)²`. -/
def catalanSeries : HypSeries :=
  ⟨fun k => if k = 0 then 1 else k * (2 * k - 1),
    fun k => if k = 0 then 1 else 2 * (2 * k + 1) * (2 * k + 1), fun k => by
      split_ifs <;> positivity⟩

theorem hypSpec_catalanLeaf (l : ℕ) : HypSpec catalanSeries l 1 (catalanLeaf l) := by
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · refine ⟨?_, ?_, ?_⟩ <;> simp [catalanLeaf, catalanSeries, HypSeries.partial]
  · have hl0 : l ≠ 0 := hl.ne'
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [catalanLeaf, catalanSeries, HypSeries.partial, toNat_ofNat, hl0]

/-- The products of the term ratios are the terms. -/
theorem prod_catalanSeries (k : ℕ) :
    ∏ j ∈ range (k + 1), ((catalanSeries.p (0 + j) : ℝ) / catalanSeries.q (0 + j)) =
      Azurite.catalanTerm k := by
  induction k with
  | zero => simp [catalanSeries, Azurite.catalanTerm_zero]
  | succ k ih =>
    rw [prod_range_succ, ih, Azurite.catalanTerm_succ]
    congr 1
    simp only [catalanSeries, zero_add, Nat.succ_ne_zero, ite_false,
      show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
    push_cast
    ring

theorem catalanNumDen_den_pos (N : ℕ) : 0 < (catalanNumDen N).2.toNat := by
  obtain ⟨-, hQ, -⟩ := hypSpec_split hypSpec_catalanLeaf 0 N
  simp only [catalanNumDen, toNat_mul, toNat_ofNat, hQ]
  exact Nat.mul_pos (by norm_num) (prod_pos fun k _ => catalanSeries.q_pos _)

/-- **The binary splitting computes the exact partial sum**:
`num/den = (3/8) ∑_{k<N} 1/((2k+1)² C(2k,k))`. -/
theorem catalanNumDen_eq (N : ℕ) :
    ((catalanNumDen N).1.toNat : ℝ) / (catalanNumDen N).2.toNat
      = 3 / 8 * ∑ k ∈ range N, Azurite.catalanTerm k := by
  obtain ⟨-, hQ, hT⟩ := hypSpec_split hypSpec_catalanLeaf 0 N
  have hQ0 : (0 : ℝ) < (hypSplit catalanLeaf 0 N).2.1.toNat := by
    rw [hQ]; exact_mod_cast prod_pos fun k _ => catalanSeries.q_pos _
  have hsum : catalanSeries.partial 0 N = ∑ k ∈ range N, Azurite.catalanTerm k :=
    sum_congr rfl fun k _ => prod_catalanSeries k
  simp only [catalanNumDen, toNat_mul, toNat_ofNat]
  push_cast
  rw [← hsum, ← hT]
  field_simp

/-! ### `∑ 1/((2k+1) 3^{k+1})` -/

/-- The series `∑ 1/((2k+1) 3^{k+1})`: `a = 1`, `b k = 2k+1`, `r = 3`. -/
def atanhSqrtThreeSeries : SplitSeries :=
  ⟨fun _ => 1, fun k => 2 * k + 1, 3, fun _ => by omega, by norm_num⟩

theorem spec_atanhSqrtThreeLeaf (l : ℕ) :
    SpecOf atanhSqrtThreeSeries l 1 (atanhSqrtThreeLeaf l) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [atanhSqrtThreeLeaf, toNat_ofNat, atanhSqrtThreeSeries]
  · simp [atanhSqrtThreeLeaf, toNat_ofNat, atanhSqrtThreeSeries]
  · simp only [atanhSqrtThreeLeaf, toNat_ofNat, atanhSqrtThreeSeries, SplitSeries.partial,
      sum_range_one, Nat.add_zero]
    push_cast
    ring

theorem atanhSqrtThreeNumDen_den_pos (N : ℕ) : 0 < (atanhSqrtThreeNumDen N).2.toNat := by
  have h := (spec_splitOf spec_atanhSqrtThreeLeaf 0 N).den_pos
  simp only [atanhSqrtThreeNumDen, toNat_mul, toNat_ofNat] at h ⊢
  omega

/-- **The binary splitting computes the exact partial sum**:
`num/den = (1/4) ∑_{k<N} 1/((2k+1) 3^{k+1})`. -/
theorem atanhSqrtThreeNumDen_eq (N : ℕ) :
    ((atanhSqrtThreeNumDen N).1.toNat : ℝ) / (atanhSqrtThreeNumDen N).2.toNat
      = 1 / 4 * ∑ k ∈ range N, Azurite.atanhSqrtThreeTerm k := by
  obtain ⟨-, -, hT⟩ := spec_splitOf spec_atanhSqrtThreeLeaf 0 N
  have hsum : atanhSqrtThreeSeries.partial 0 N = ∑ k ∈ range N, Azurite.atanhSqrtThreeTerm k := by
    refine sum_congr rfl fun k _ => ?_
    simp only [atanhSqrtThreeSeries, Azurite.atanhSqrtThreeTerm, zero_add]
    push_cast
    ring
  simp only [atanhSqrtThreeNumDen, toNat_mul, toNat_ofNat]
  push_cast
  rw [← hsum, ← hT]
  rw [div_mul_eq_div_div_swap, div_eq_mul_one_div _ (4 : ℝ)]
  ring

end Azurite.AzNat
