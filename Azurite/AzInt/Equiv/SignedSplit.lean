/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzInt.SignedSplit
import Azurite.AzInt.Equiv.Add
import Azurite.AzInt.Equiv.Mul
import Azurite.AzNat.Equiv.Square.Dispatch
import Azurite.Transcendental.EulerGamma

/-!
# Equivalence: the signed binary splitting computes the exact partial sums

For a series `∑_k (a k / q k) ∏_{j≤k} p j / q j` (`SignedSeries`: real numerators `a k`, positive
small factors `q k`, and `p k`), `SignedSpecOf s l n x` says that the state `x = (P, Q, T)`
represents the range `[l, l+n)`: `P = ∏_{k<n} p (l+k)`, `Q = ∏_{k<n} q (l+k)` and
`T/Q² = ∑_{k<n} (a (l+k) / q (l+k)) ∏_{j≤k} p (l+j) / q (l+j)`.  If the leaf represents its
single term, the merge preserves the invariant (`spec_signedMerge`), hence so do the sequential
fallback and the splitting with any fuel (`spec_signedSeqOf`, `spec_signedSplitFuelOf`,
`spec_signedSplitOf`).  Instance: Sweeney's series for Euler's constant (`a k = (−1)^k`,
`q k = k + 1`, `p k = n`; `sweeneyNumDen_eq` gives `T/Q² = ∑_{k<N} sweeneyTerm n k`, the partial
sum of `Azurite/Transcendental/EulerGamma.lean`).
-/

namespace Azurite.AzInt

open Finset

/-! ### The generic engine -/

/-- A series `∑_k (a k / q k) ∏_{j≤k} p j / q j` for signed binary splitting. -/
structure SignedSeries where
  /-- The signed numerator of the term of index `k`. -/
  a : ℕ → ℝ
  /-- The numerator of the ratio of index `k`. -/
  p : ℕ → ℕ
  /-- The denominator of the ratio of index `k`, also the small denominator factor of the term. -/
  q : ℕ → ℕ
  q_pos : ∀ k, 0 < q k

/-- The product of the ratios `p/q` of the indices `l, …, l+k−1`. -/
noncomputable def SignedSeries.ratio (s : SignedSeries) (l k : ℕ) : ℝ :=
  ∏ j ∈ range k, ((s.p (l + j) : ℝ) / (s.q (l + j) : ℝ))

/-- The range `[l, l+n)` of the series, normalized to its start:
`∑_{k<n} (a (l+k) / q (l+k)) ∏_{j≤k} p (l+j) / q (l+j)`. -/
noncomputable def SignedSeries.partial (s : SignedSeries) (l n : ℕ) : ℝ :=
  ∑ k ∈ range n, s.a (l + k) / (s.q (l + k) : ℝ) * s.ratio l (k + 1)

/-- The state `(P, Q, T)` represents the range `[l, l+n)`. -/
def SignedSpecOf (s : SignedSeries) (l n : ℕ) (x : SignedSplitState) : Prop :=
  x.1.toNat = ∏ k ∈ range n, s.p (l + k) ∧ x.2.1.toNat = ∏ k ∈ range n, s.q (l + k) ∧
    (x.2.2.toInt : ℝ) / ((x.2.1.toNat : ℝ) * x.2.1.toNat) = s.partial l n

theorem SignedSeries.ratio_add (s : SignedSeries) (l m k : ℕ) :
    s.ratio l (m + k) = s.ratio l m * s.ratio (l + m) k := by
  unfold SignedSeries.ratio
  rw [prod_range_add]
  congr 1
  exact prod_congr rfl fun j _ => by rw [add_assoc]

theorem SignedSeries.ratio_eq_div (s : SignedSeries) (l m : ℕ) :
    s.ratio l m = (∏ k ∈ range m, s.p (l + k) : ℕ) / ((∏ k ∈ range m, s.q (l + k) : ℕ) : ℝ) := by
  unfold SignedSeries.ratio
  push_cast
  rw [prod_div_distrib]

theorem SignedSeries.partial_add (s : SignedSeries) (l m n : ℕ) :
    s.partial l (m + n) = s.partial l m + s.ratio l m * s.partial (l + m) n := by
  unfold SignedSeries.partial
  rw [sum_range_add, mul_sum]
  congr 1
  refine sum_congr rfl fun k _ => ?_
  rw [show l + (m + k) = l + m + k by omega, show m + k + 1 = m + (k + 1) by ring,
    SignedSeries.ratio_add]
  ring

theorem spec_signedEmpty (s : SignedSeries) (l : ℕ) : SignedSpecOf s l 0 signedEmpty := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [signedEmpty, SignedSeries.partial]

/-- The merge: if `x` represents `[l, l+m)` and `y` represents `[l+m, l+m+n)`, then
`signedMerge x y` represents `[l, l+m+n)`. -/
theorem spec_signedMerge {s : SignedSeries} {l m n : ℕ} {x y : SignedSplitState}
    (hx : SignedSpecOf s l m x) (hy : SignedSpecOf s (l + m) n y) :
    SignedSpecOf s l (m + n) (signedMerge x y) := by
  obtain ⟨hxP, hxQ, hxT⟩ := hx
  obtain ⟨hyP, hyQ, hyT⟩ := hy
  have hQ1 : (0 : ℝ) < x.2.1.toNat := by
    rw [hxQ]; exact_mod_cast prod_pos fun k _ => s.q_pos _
  have hQ2 : (0 : ℝ) < y.2.1.toNat := by
    rw [hyQ]; exact_mod_cast prod_pos fun k _ => s.q_pos _
  refine ⟨?_, ?_, ?_⟩
  · simp only [signedMerge, AzNat.toNat_mul, hxP, hyP, prod_range_add]
    congr 1
    exact prod_congr rfl fun k _ => by rw [add_assoc]
  · simp only [signedMerge, AzNat.toNat_mul, hxQ, hyQ, prod_range_add]
    congr 1
    exact prod_congr rfl fun k _ => by rw [add_assoc]
  · have hratio : s.ratio l m = (x.1.toNat : ℝ) / x.2.1.toNat := by
      rw [SignedSeries.ratio_eq_div, hxP, hxQ]
    simp only [signedMerge, toInt_add, toInt_mul, AzNat.toInt_toAzInt, AzNat.toNat_mul,
      AzNat.toNat_square]
    push_cast
    rw [SignedSeries.partial_add, ← hxT, ← hyT, hratio]
    have hQ1' := hQ1.ne'
    have hQ2' := hQ2.ne'
    field_simp

/-- The sequential fallback represents its range, if the leaf represents its term. -/
theorem spec_signedSeqOf {s : SignedSeries} {leaf : ℕ → SignedSplitState}
    (hleaf : ∀ l, SignedSpecOf s l 1 (leaf l)) :
    ∀ n l, SignedSpecOf s l n (signedSeqOf leaf l n)
  | 0, l => spec_signedEmpty s l
  | n + 1, l => by
    rw [signedSeqOf, show n + 1 = 1 + n by ring]
    exact spec_signedMerge (hleaf l) (spec_signedSeqOf hleaf n (l + 1))

/-- The splitting represents its range, for every fuel. -/
theorem spec_signedSplitFuelOf {s : SignedSeries} {leaf : ℕ → SignedSplitState}
    (hleaf : ∀ l, SignedSpecOf s l 1 (leaf l)) :
    ∀ fuel l n, SignedSpecOf s l n (signedSplitFuelOf leaf fuel l n)
  | 0, l, n => by rw [signedSplitFuelOf]; exact spec_signedSeqOf hleaf n l
  | _ + 1, l, 0 => by rw [signedSplitFuelOf]; exact spec_signedEmpty s l
  | _ + 1, l, 1 => by rw [signedSplitFuelOf]; exact hleaf l
  | fuel + 1, l, n + 2 => by
    simp only [signedSplitFuelOf]
    have hm : (n + 2) / 2 ≤ n + 2 := Nat.div_le_self _ _
    have h := spec_signedMerge (spec_signedSplitFuelOf hleaf fuel l ((n + 2) / 2))
      (spec_signedSplitFuelOf hleaf fuel (l + (n + 2) / 2) (n + 2 - (n + 2) / 2))
    rwa [Nat.add_sub_cancel' hm] at h

theorem spec_signedSplitOf {s : SignedSeries} {leaf : ℕ → SignedSplitState}
    (hleaf : ∀ l, SignedSpecOf s l 1 (leaf l)) (l n : ℕ) :
    SignedSpecOf s l n (signedSplitOf leaf l n) :=
  spec_signedSplitFuelOf hleaf n l n

/-- The denominator `Q²` of a split range is positive. -/
theorem SignedSpecOf.den_pos {s : SignedSeries} {l n : ℕ} {x : SignedSplitState}
    (h : SignedSpecOf s l n x) : 0 < (AzNat.square x.2.1).toNat := by
  obtain ⟨-, hQ, -⟩ := h
  rw [AzNat.toNat_square, hQ]
  exact pow_pos (prod_pos fun k _ => s.q_pos _) 2

/-! ### Sweeney's series -/

/-- Sweeney's series: `a k = (−1)^k`, `q k = k + 1`, `p k = n`. -/
def sweeneySeries (n : ℕ) : SignedSeries :=
  ⟨fun k => (-1) ^ k, fun _ => n, fun k => k + 1, fun _ => by omega⟩

theorem toInt_sweeneyLeaf (n : AzNat) (k : ℕ) :
    ((sweeneyLeaf n k).2.2.toInt : ℝ) = (-1) ^ k * n.toNat := by
  simp only [sweeneyLeaf]
  split_ifs with h
  · rw [AzNat.toInt_toAzInt, (Nat.even_iff.mpr h).neg_one_pow, one_mul]
    push_cast
    rfl
  · rw [toInt_neg, AzNat.toInt_toAzInt, (Nat.odd_iff.mpr (by omega)).neg_one_pow]
    push_cast
    ring

theorem spec_sweeneyLeaf (n l : ℕ) :
    SignedSpecOf (sweeneySeries n) l 1 (sweeneyLeaf (AzNat.ofNat n) l) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [sweeneyLeaf, AzNat.toNat_ofNat, sweeneySeries]
  · simp [sweeneyLeaf, AzNat.toNat_ofNat, sweeneySeries]
  · rw [toInt_sweeneyLeaf]
    simp only [sweeneyLeaf, AzNat.toNat_ofNat, sweeneySeries, SignedSeries.partial,
      SignedSeries.ratio, sum_range_one, Nat.add_zero]
    rw [prod_range_one]
    push_cast
    have h1 : ((l : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring

theorem spec_sweeneySplit (n l N : ℕ) :
    SignedSpecOf (sweeneySeries n) l N (signedSplitOf (sweeneyLeaf (AzNat.ofNat n)) l N) :=
  spec_signedSplitOf (spec_sweeneyLeaf n) l N

/-- The denominator `Q²` is positive. -/
theorem sweeneyNumDen_den_pos (n N : ℕ) : 0 < (sweeneyNumDen n N).2.toNat :=
  (spec_sweeneySplit n 0 N).den_pos

/-- The ratio of Sweeney's series: `∏_{j<k} n/(j+1) = n^k/k!`. -/
theorem sweeneySeries_ratio (n k : ℕ) :
    (sweeneySeries n).ratio 0 k = (n : ℝ) ^ k / (k.factorial : ℝ) := by
  simp only [SignedSeries.ratio, sweeneySeries, zero_add]
  rw [prod_div_distrib, prod_const, card_range]
  congr 1
  exact_mod_cast prod_range_add_one_eq_factorial k

/-- **The signed binary splitting computes the exact partial sum of Sweeney's series**:
`T/Q² = ∑_{k<N} (−1)^k n^(k+1) / ((k+1) (k+1)!)`. -/
theorem sweeneyNumDen_eq (n N : ℕ) :
    ((sweeneyNumDen n N).1.toInt : ℝ) / (sweeneyNumDen n N).2.toNat
      = ∑ k ∈ range N, sweeneyTerm (n : ℝ) k := by
  obtain ⟨-, -, hT⟩ := spec_sweeneySplit n 0 N
  simp only [sweeneyNumDen, AzNat.toNat_square]
  push_cast
  rw [sq]
  rw [hT, SignedSeries.partial]
  refine sum_congr rfl fun k _ => ?_
  rw [sweeneySeries_ratio]
  simp only [sweeneySeries, sweeneyTerm, zero_add]
  rw [Nat.factorial_succ]
  push_cast
  have h1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  have h2 : (k.factorial : ℝ) ≠ 0 := by positivity
  field_simp

end Azurite.AzInt
