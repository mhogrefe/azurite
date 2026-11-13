/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section14
import Mathlib.LinearAlgebra.Lagrange
import Azurite.DLMF.Chapter1.Section3

/-!
# DLMF §5.14: the Dixon–Anderson change of variables

Groundwork for the Dixon–Anderson integral (Forrester–Warnaar, *The importance of the Selberg
integral*, eq. (GWA)), the first step of Anderson's proof of Selberg's integral 5.14.4.

For nodes `a₀ > a₁ > ⋯ > aₙ` and points `t` interlacing them (`aᵢ₊₁ < tᵢ < aᵢ`,
`dixonRegion`), the residue weights
`wᵢ = ∏ⱼ (aᵢ − tⱼ) / ∏_{k≠i} (aᵢ − aₖ)` (`dixonW`)
are positive (`dixonW_pos`) and sum to `1` (`sum_dixonW`, Lagrange interpolation of the monic
`∏ⱼ (x − tⱼ)` at the `n + 1` nodes).
-/

open Finset Polynomial

namespace Azurite.DLMF

variable {n : ℕ}

/-- The interlacing region `aᵢ₊₁ < tᵢ < aᵢ`. -/
def dixonRegion (a : Fin (n + 1) → ℝ) : Set (Fin n → ℝ) :=
  {t | ∀ i, a i.succ < t i ∧ t i < a i.castSucc}

/-- The residue weights `wᵢ = ∏ⱼ (aᵢ − tⱼ) / ∏_{k≠i} (aᵢ − aₖ)`. -/
noncomputable def dixonW (a : Fin (n + 1) → ℝ) (t : Fin n → ℝ) (i : Fin (n + 1)) : ℝ :=
  (∏ j, (a i - t j)) / ∏ k ∈ univ.erase i, (a i - a k)

/-- `∑ᵢ wᵢ = 1`: the leading coefficient of `∏ⱼ (x − tⱼ)` by Lagrange interpolation. -/
theorem sum_dixonW {a : Fin (n + 1) → ℝ} (ha : Function.Injective a) (t : Fin n → ℝ) :
    ∑ i, dixonW a t i = 1 := by
  set P : ℝ[X] := ∏ j, (X - C (t j))
  have hP : P.Monic := monic_prod_of_monic _ _ fun j _ => monic_X_sub_C (t j)
  have hdeg : P.natDegree = n := by
    rw [natDegree_prod_of_monic _ _ fun j _ => monic_X_sub_C (t j)]
    simp
  have hlt : P.degree < #(univ : Finset (Fin (n + 1))) := by
    rw [degree_eq_natDegree hP.ne_zero, hdeg, card_univ, Fintype.card_fin]
    exact_mod_cast Nat.lt_succ_self n
  have h := Lagrange.coeff_eq_sum (s := univ) (v := a) (fun x _ y _ h => ha h) hlt
  have hc : P.coeff n = 1 := by
    have := hP.coeff_natDegree; rwa [hdeg] at this
  rw [card_univ, Fintype.card_fin, Nat.add_sub_cancel, hc] at h
  rw [h]
  refine sum_congr rfl fun i _ => ?_
  rw [dixonW, eval_prod]
  simp

/-- Sign bookkeeping: a product equals `(−1)^m` times the product of absolute values, where
`m` counts the negative factors. -/
theorem prod_eq_neg_one_pow_mul_prod_abs {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ∏ i ∈ s, f i = (-1) ^ #(s.filter fun i => f i < 0) * ∏ i ∈ s, |f i| := by
  have h : ∀ i, f i = (if f i < 0 then -1 else 1) * |f i| := fun i => by
    split_ifs with h
    · rw [abs_of_neg h]; ring
    · rw [abs_of_nonneg (not_lt.mp h)]; ring
  conv_lhs => rw [prod_congr rfl fun i _ => h i]
  rw [prod_mul_distrib, prod_ite, prod_const_one, mul_one, prod_const]

theorem card_neg_numer {a : Fin (n + 1) → ℝ} (ha : StrictAnti a) {t : Fin n → ℝ}
    (ht : t ∈ dixonRegion a) (i : Fin (n + 1)) :
    #(univ.filter fun j : Fin n => a i - t j < 0) = i.val := by
  have e : (univ.filter fun j : Fin n => a i - t j < 0) =
      univ.filter fun j : Fin n => j.val < i.val := by
    ext j
    simp only [mem_filter, mem_univ, true_and, sub_neg]
    constructor
    · intro h
      by_contra hji
      push Not at hji
      have h1 : i ≤ j.castSucc := by rw [Fin.le_iff_val_le_val]; simpa using hji
      have := (ht j).2
      linarith [ha.antitone h1]
    · intro h
      have h1 : j.succ ≤ i := by rw [Fin.le_iff_val_le_val]; simp; omega
      have := (ht j).1
      linarith [ha.antitone h1]
  rw [e, Fin.card_filter_val_lt]
  exact min_eq_right (by omega)

theorem card_neg_denom {a : Fin (n + 1) → ℝ} (ha : StrictAnti a) (i : Fin (n + 1)) :
    #((univ.erase i).filter fun k => a i - a k < 0) = i.val := by
  have e : ((univ.erase i).filter fun k => a i - a k < 0) = Iio i := by
    ext k
    simp only [mem_filter, mem_erase, mem_univ, and_true, sub_neg, mem_Iio]
    constructor
    · rintro ⟨-, h⟩; exact ha.lt_iff_gt.mp h
    · intro h; exact ⟨ne_of_lt h, ha h⟩
  rw [e, Fin.card_Iio]

/-- On the interlacing region, `wᵢ = ∏ⱼ |aᵢ − tⱼ| / ∏_{k≠i} |aᵢ − aₖ| > 0`. -/
theorem dixonW_eq_abs {a : Fin (n + 1) → ℝ} (ha : StrictAnti a) {t : Fin n → ℝ}
    (ht : t ∈ dixonRegion a) (i : Fin (n + 1)) :
    dixonW a t i = (∏ j, |a i - t j|) / ∏ k ∈ univ.erase i, |a i - a k| := by
  rw [dixonW, prod_eq_neg_one_pow_mul_prod_abs, prod_eq_neg_one_pow_mul_prod_abs (univ.erase i),
    card_neg_numer ha ht, card_neg_denom ha, mul_div_mul_left _ _ (pow_ne_zero _ (by norm_num))]

theorem dixonW_pos {a : Fin (n + 1) → ℝ} (ha : StrictAnti a) {t : Fin n → ℝ}
    (ht : t ∈ dixonRegion a) (i : Fin (n + 1)) : 0 < dixonW a t i := by
  rw [dixonW_eq_abs ha ht]
  refine div_pos (prod_pos fun j _ => abs_pos.mpr (sub_ne_zero.mpr fun h => ?_))
    (prod_pos fun k hk => abs_pos.mpr (sub_ne_zero.mpr fun h => (mem_erase.mp hk).1
      (ha.injective h).symm))
  -- `aᵢ ≠ tⱼ` on the interlacing region
  have h1 := (ht j).1
  have h2 := (ht j).2
  rcases lt_or_ge j.val i.val with hji | hji
  · have : j.succ ≤ i := by rw [Fin.le_iff_val_le_val]; simp; omega
    linarith [ha.antitone this]
  · have : i ≤ j.castSucc := by rw [Fin.le_iff_val_le_val]; simpa using hji
    linarith [ha.antitone this]

/-! ### Injectivity -/

/-- Interlacing points in the same gaps are equal if equal as sets. -/
theorem dixonRegion_eq_of_eq {a : Fin (n + 1) → ℝ} (ha : StrictAnti a) {t t' : Fin n → ℝ}
    (ht : t ∈ dixonRegion a) (ht' : t' ∈ dixonRegion a) {j k : Fin n} (h : t j = t' k) : j = k := by
  by_contra hjk
  rcases lt_or_gt_of_ne hjk with hlt | hlt
  · have h1 : j.succ ≤ k.castSucc := by rw [Fin.le_iff_val_le_val]; simp; omega
    have := (ht j).1; have := (ht' k).2
    linarith [ha.antitone h1]
  · have h1 : k.succ ≤ j.castSucc := by rw [Fin.le_iff_val_le_val]; simp; omega
    have := (ht j).2; have := (ht' k).1
    linarith [ha.antitone h1]

theorem natDegree_nodePoly (t : Fin n → ℝ) : (∏ j, (X - C (t j))).natDegree = n := by
  rw [natDegree_prod_of_monic _ _ fun j _ => monic_X_sub_C (t j)]; simp

theorem monic_nodePoly (t : Fin n → ℝ) : (∏ j, (X - C (t j))).Monic :=
  monic_prod_of_monic _ _ fun j _ => monic_X_sub_C (t j)

theorem prod_sub_ne_zero {a : Fin (n + 1) → ℝ} (ha : Function.Injective a) (i : Fin (n + 1)) :
    ∏ k ∈ univ.erase i, (a i - a k) ≠ 0 :=
  prod_ne_zero_iff.mpr fun _k hk => sub_ne_zero.mpr fun h => (mem_erase.mp hk).1 (ha h).symm

/-- `t ↦ (w₀, …, w_{n−1})` is injective on the interlacing region. -/
theorem dixonW_injOn {a : Fin (n + 1) → ℝ} (ha : StrictAnti a) :
    Set.InjOn (fun t : Fin n → ℝ => fun i : Fin n => dixonW a t i.castSucc) (dixonRegion a) := by
  intro t ht t' ht' h
  have hw : ∀ i : Fin n, dixonW a t i.castSucc = dixonW a t' i.castSucc := fun i =>
    congrFun h i
  have hall : ∀ i, dixonW a t i = dixonW a t' i := by
    intro i
    refine Fin.lastCases ?_ (fun i => hw i) i
    have h1 := sum_dixonW ha.injective t
    have h2 := sum_dixonW ha.injective t'
    rw [Fin.sum_univ_castSucc] at h1 h2
    simp_rw [hw] at h1
    linarith
  have hnum : ∀ i, ∏ j, (a i - t j) = ∏ j, (a i - t' j) := fun i => by
    have := hall i
    rw [dixonW, dixonW, div_left_inj' (prod_sub_ne_zero ha.injective i)] at this
    exact this
  have hpoly : ∏ j, (X - C (t j)) = ∏ j, (X - C (t' j)) := by
    refine Polynomial.eq_of_degree_sub_lt_of_eval_index_eq (s := univ) (v := a)
      (fun x _ y _ h => ha.injective h) ?_ fun i _ => ?_
    · refine (degree_sub_le _ _).trans_lt ?_
      rw [degree_eq_natDegree (monic_nodePoly t).ne_zero,
        degree_eq_natDegree (monic_nodePoly t').ne_zero, natDegree_nodePoly, natDegree_nodePoly,
        max_self, card_univ, Fintype.card_fin]
      exact_mod_cast Nat.lt_succ_self n
    · simp only [eval_prod, eval_sub, eval_X, eval_C]; exact hnum i
  funext j
  have hroot : eval (t j) (∏ k, (X - C (t' k))) = 0 := by
    rw [← hpoly, eval_prod]
    exact prod_eq_zero (mem_univ j) (by simp)
  rw [eval_prod, prod_eq_zero_iff] at hroot
  obtain ⟨k, -, hk⟩ := hroot
  simp only [eval_sub, eval_X, eval_C, sub_eq_zero] at hk
  rw [hk, dixonRegion_eq_of_eq ha ht ht' hk]

/-! ### Surjectivity onto the open simplex -/

/-- The open simplex `{w : wᵢ > 0, ∑ wᵢ < 1}`. -/
def openSimplexDLMF (n : ℕ) : Set (Fin n → ℝ) := {w | (∀ i, 0 < w i) ∧ ∑ i, w i < 1}

/-- The weights extended by `w_n = 1 − ∑ wᵢ`. -/
noncomputable def extendW (w : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.lastCases (1 - ∑ i, w i) w

theorem extendW_castSucc (w : Fin n → ℝ) (i : Fin n) : extendW w i.castSucc = w i := by
  simp [extendW]

theorem extendW_last (w : Fin n → ℝ) : extendW w (Fin.last n) = 1 - ∑ i, w i := by
  simp [extendW]

theorem sum_extendW (w : Fin n → ℝ) : ∑ i, extendW w i = 1 := by
  rw [Fin.sum_univ_castSucc]; simp [extendW_castSucc, extendW_last]

theorem extendW_pos {w : Fin n → ℝ} (hw : w ∈ openSimplexDLMF n) (i : Fin (n + 1)) :
    0 < extendW w i := by
  refine Fin.lastCases ?_ (fun i => ?_) i
  · rw [extendW_last]; linarith [hw.2]
  · rw [extendW_castSucc]; exact hw.1 i

/-- The partial-fraction numerator `F = ∑ᵢ Wᵢ ∏_{k≠i} (X − aₖ)`. -/
noncomputable def pfNumer (a : Fin (n + 1) → ℝ) (W : Fin (n + 1) → ℝ) : ℝ[X] :=
  ∑ i, C (W i) * ∏ k ∈ univ.erase i, (X - C (a k))

theorem eval_pfNumer_node {a : Fin (n + 1) → ℝ} (W : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    eval (a j) (pfNumer a W) = W j * ∏ k ∈ univ.erase j, (a j - a k) := by
  rw [pfNumer, eval_finsetSum, sum_eq_single j]
  · simp [eval_prod]
  · intro i _ hij
    rw [eval_mul, eval_prod]
    refine mul_eq_zero_of_right _ (prod_eq_zero (mem_erase.mpr ⟨Ne.symm hij, mem_univ j⟩) ?_)
    simp
  · simp

theorem natDegree_prod_erase (a : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    (∏ k ∈ univ.erase i, (X - C (a k))).natDegree = n := by
  rw [natDegree_prod_of_monic _ _ fun k _ => monic_X_sub_C (a k)]
  simp [card_erase_of_mem (mem_univ i)]

theorem monic_prod_erase (a : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    (∏ k ∈ univ.erase i, (X - C (a k))).Monic :=
  monic_prod_of_monic _ _ fun k _ => monic_X_sub_C (a k)

theorem coeff_pfNumer (a : Fin (n + 1) → ℝ) (W : Fin (n + 1) → ℝ) {m : ℕ} (hm : n ≤ m) :
    (pfNumer a W).coeff m = if m = n then ∑ i, W i else 0 := by
  rw [pfNumer, finsetSum_coeff]
  split_ifs with h
  · rw [h]
    refine sum_congr rfl fun i _ => ?_
    have hc : (∏ k ∈ univ.erase i, (X - C (a k))).coeff n = 1 := by
      have := (monic_prod_erase a i).coeff_natDegree; rwa [natDegree_prod_erase] at this
    rw [coeff_C_mul, hc, mul_one]
  · refine sum_eq_zero fun i _ => ?_
    rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt, mul_zero]
    rw [natDegree_prod_erase]; omega

/-- The sign of `F` at the nodes: `F(aⱼ) = (−1)^j × (positive)`. -/
theorem eval_pfNumer_sign {a : Fin (n + 1) → ℝ} (ha : StrictAnti a) (W : Fin (n + 1) → ℝ)
    (j : Fin (n + 1)) :
    eval (a j) (pfNumer a W) = (-1) ^ j.val * (W j * ∏ k ∈ univ.erase j, |a j - a k|) := by
  rw [eval_pfNumer_node, prod_eq_neg_one_pow_mul_prod_abs, card_neg_denom ha]
  ring

theorem pos_part_pfNumer {a : Fin (n + 1) → ℝ} (ha : StrictAnti a) {W : Fin (n + 1) → ℝ}
    (hW : ∀ i, 0 < W i) (j : Fin (n + 1)) : 0 < W j * ∏ k ∈ univ.erase j, |a j - a k| :=
  mul_pos (hW j) (prod_pos fun _k hk => abs_pos.mpr (sub_ne_zero.mpr fun h =>
    (mem_erase.mp hk).1 (ha.injective h).symm))

/-- A root of `F` in each gap `(aⱼ₊₁, aⱼ)`. -/
theorem exists_root_pfNumer {a : Fin (n + 1) → ℝ} (ha : StrictAnti a) {W : Fin (n + 1) → ℝ}
    (hW : ∀ i, 0 < W i) (j : Fin n) :
    ∃ x ∈ Set.Ioo (a j.succ) (a j.castSucc), eval x (pfNumer a W) = 0 := by
  have hlt : a j.succ < a j.castSucc := ha Fin.castSucc_lt_succ
  have hc : ContinuousOn (fun x => eval x (pfNumer a W)) (Set.Icc (a j.succ) (a j.castSucc)) :=
    (pfNumer a W).continuous.continuousOn
  have h1 := eval_pfNumer_sign ha W j.castSucc
  have h2 := eval_pfNumer_sign ha W j.succ
  have p1 := pos_part_pfNumer ha hW j.castSucc
  have p2 := pos_part_pfNumer ha hW j.succ
  simp only [Fin.val_castSucc, Fin.val_succ, pow_succ] at h1 h2
  rcases Nat.even_or_odd j.val with he | ho
  · rw [he.neg_one_pow, one_mul] at h1
    rw [he.neg_one_pow] at h2
    have := intermediate_value_Ioo hlt.le hc (show (0 : ℝ) ∈ Set.Ioo _ _ by
      constructor <;> simp only [h1, h2] <;> linarith)
    obtain ⟨x, hx, hx0⟩ := this
    exact ⟨x, hx, hx0⟩
  · rw [ho.neg_one_pow] at h1 h2
    have := intermediate_value_Ioo' hlt.le hc (show (0 : ℝ) ∈ Set.Ioo _ _ by
      constructor <;> simp only [h1, h2] <;> linarith)
    obtain ⟨x, hx, hx0⟩ := this
    exact ⟨x, hx, hx0⟩

/-- **Surjectivity**: every point of the open simplex is a weight vector. -/
theorem exists_dixonRegion_of_openSimplex {a : Fin (n + 1) → ℝ} (ha : StrictAnti a)
    {w : Fin n → ℝ} (hw : w ∈ openSimplexDLMF n) :
    ∃ t ∈ dixonRegion a, (fun i : Fin n => dixonW a t i.castSucc) = w := by
  set W := extendW w
  have hW := extendW_pos hw
  choose t ht hroot using exists_root_pfNumer ha hW
  have htR : t ∈ dixonRegion a := fun j => ht j
  refine ⟨t, htR, ?_⟩
  -- `F = ∏ (X − tⱼ)`
  have hF : pfNumer a W = ∏ j, (X - C (t j)) := by
    refine Polynomial.eq_of_degree_sub_lt_of_eval_index_eq (s := univ) (v := t)
      (fun x _ y _ h => dixonRegion_eq_of_eq ha htR htR h) ?_ fun j _ => ?_
    · rw [card_univ, Fintype.card_fin, degree_lt_iff_coeff_zero]
      intro m hm
      rw [coeff_sub, coeff_pfNumer a W hm]
      split_ifs with h
      · rw [h]
        have hc : (∏ j, (X - C (t j))).coeff n = 1 := by
          have := (monic_nodePoly t).coeff_natDegree; rwa [natDegree_nodePoly] at this
        rw [sum_extendW, hc, sub_self]
      · rw [coeff_eq_zero_of_natDegree_lt (by rw [natDegree_nodePoly]; omega), sub_zero]
    · rw [hroot j, eval_prod]
      exact (prod_eq_zero (mem_univ j) (by simp)).symm
  funext i
  have h := eval_pfNumer_node (a := a) W i.castSucc
  rw [hF, eval_prod] at h
  simp only [eval_sub, eval_X, eval_C] at h
  rw [dixonW, h, mul_div_assoc, div_self (prod_sub_ne_zero ha.injective _), mul_one]
  exact extendW_castSucc w i

/-- `Φ` maps the interlacing region onto the open simplex. -/
theorem dixonW_image {a : Fin (n + 1) → ℝ} (ha : StrictAnti a) :
    (fun t : Fin n → ℝ => fun i : Fin n => dixonW a t i.castSucc) '' dixonRegion a =
      openSimplexDLMF n := by
  apply Set.Subset.antisymm
  · rintro _ ⟨t, ht, rfl⟩
    refine ⟨fun i => dixonW_pos ha ht _, ?_⟩
    have h1 := sum_dixonW ha.injective t
    rw [Fin.sum_univ_castSucc] at h1
    have := dixonW_pos ha ht (Fin.last n)
    simp only
    linarith
  · intro w hw
    obtain ⟨t, ht, h⟩ := exists_dixonRegion_of_openSimplex ha hw
    exact ⟨t, ht, h⟩

/-! ### The Jacobian -/

/-- The chart `t ↦ (w₀, …, w_{n−1})`. -/
noncomputable def dixonPhi (a : Fin (n + 1) → ℝ) (t : Fin n → ℝ) : Fin n → ℝ :=
  fun i => dixonW a t i.castSucc

/-- The constants `cᵢ = (∏_{k≠i} (aᵢ − aₖ))⁻¹`. -/
noncomputable def dixonC (a : Fin (n + 1) → ℝ) (i : Fin n) : ℝ :=
  (∏ k ∈ univ.erase i.castSucc, (a i.castSucc - a k))⁻¹

/-- The Jacobian matrix `∂wᵢ/∂tⱼ = −cᵢ ∏_{k≠j} (aᵢ − tₖ)`. -/
noncomputable def dixonJac (a : Fin (n + 1) → ℝ) (t : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => -(dixonC a i * ∏ k ∈ univ.erase j, (a i.castSucc - t k))

theorem hasFDerivAt_dixonPhi (a : Fin (n + 1) → ℝ) (t : Fin n → ℝ) :
    HasFDerivAt (dixonPhi a)
      (LinearMap.toContinuousLinearMap (Matrix.toLin' (dixonJac a t))) t := by
  refine hasFDerivAt_pi'.mpr fun i => ?_
  have hg : ∀ j ∈ (univ : Finset (Fin n)), HasFDerivAt (fun t : Fin n → ℝ => a i.castSucc - t j)
      (-ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j) t := fun j _ =>
    (hasFDerivAt_apply j t).const_sub (a i.castSucc)
  have h := (HasFDerivAt.finsetProd hg).const_mul (dixonC a i)
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_) |>.congr_fderiv ?_
  · simp only [dixonPhi, dixonW, dixonC]
    rw [div_eq_inv_mul]
  · ext v
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.proj_apply,
      LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
      dixonJac, Matrix.of_apply, smul_apply, FunLike.coe_sum,
      Finset.sum_apply, neg_apply, smul_eq_mul, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    ring

theorem det_dixonPhi' (a : Fin (n + 1) → ℝ) (t : Fin n → ℝ) :
    (LinearMap.toContinuousLinearMap (Matrix.toLin' (dixonJac a t))).det = (dixonJac a t).det := by
  rw [LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin']

theorem node_ne_point {a : Fin (n + 1) → ℝ} (ha : StrictAnti a) {t : Fin n → ℝ}
    (ht : t ∈ dixonRegion a) (i : Fin (n + 1)) (j : Fin n) : a i ≠ t j := by
  intro h
  have h1 := (ht j).1
  have h2 := (ht j).2
  rcases lt_or_ge j.val i.val with hji | hji
  · have : j.succ ≤ i := by rw [Fin.le_iff_val_le_val]; simp; omega
    linarith [ha.antitone this]
  · have : i ≤ j.castSucc := by rw [Fin.le_iff_val_le_val]; simpa using hji
    linarith [ha.antitone this]

/-- The real Cauchy determinant (from DLMF 1.3.14). -/
theorem det_cauchy_real {m : ℕ} (A B : Fin m → ℝ) (hAB : ∀ j k, A j ≠ B k) :
    |(Matrix.of fun j k => (A j - B k)⁻¹).det| =
      (∏ j, ∏ k ∈ Ioi j, |A k - A j| * |B k - B j|) / ∏ j, ∏ k, |A j - B k| := by
  have h := dlmf_1_3_14 (fun j => (A j : ℂ)) (fun k => (B k : ℂ))
    (fun j k h => hAB j k (by exact_mod_cast h))
  have hmap : ((Matrix.of fun j k => (A j - B k)⁻¹).det : ℂ) =
      (Matrix.of fun j k => 1 / ((A j : ℂ) - B k)).det := by
    rw [show ((Matrix.of fun j k => (A j - B k)⁻¹).det : ℂ) =
      Complex.ofRealHom (Matrix.of fun j k => (A j - B k)⁻¹).det from rfl, RingHom.map_det]
    congr 1
    ext j k
    simp
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hmap, h, norm_div, norm_mul, norm_pow, norm_neg,
    norm_one, one_pow,
    one_mul, norm_prod, norm_prod]
  congr 1
  · refine prod_congr rfl fun j _ => ?_
    rw [norm_prod]
    refine prod_congr rfl fun k _ => ?_
    rw [norm_mul, ← Complex.ofReal_sub, ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
  · refine prod_congr rfl fun j _ => ?_
    rw [norm_prod]
    refine prod_congr rfl fun k _ => ?_
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

/-- `|det ∂w/∂t| = ∏ᵢ wᵢ · ∏_{j<k} |aₖ − aⱼ||tₖ − tⱼ| / ∏_{j,k} |aⱼ − tₖ|` (indices `< n`). -/
theorem abs_det_dixonJac {a : Fin (n + 1) → ℝ} (ha : StrictAnti a) {t : Fin n → ℝ}
    (ht : t ∈ dixonRegion a) :
    |(dixonJac a t).det| = (∏ i : Fin n, dixonW a t i.castSucc) *
      ((∏ j : Fin n, ∏ k ∈ Ioi j, |a k.castSucc - a j.castSucc| * |t k - t j|) /
        ∏ j : Fin n, ∏ k, |a j.castSucc - t k|) := by
  have hne := node_ne_point ha ht
  have hJ : dixonJac a t = Matrix.of fun i j => (-dixonW a t i.castSucc) *
      (a i.castSucc - t j)⁻¹ := by
    ext i j
    simp only [dixonJac, Matrix.of_apply, dixonW, dixonC]
    have hj := mul_prod_erase univ (fun k => a i.castSucc - t k) (mem_univ j)
    have h0 : a i.castSucc - t j ≠ 0 := sub_ne_zero.mpr (hne _ j)
    rw [← hj]
    field_simp
  rw [hJ, show (Matrix.of fun i j => (-dixonW a t i.castSucc) * (a i.castSucc - t j)⁻¹) =
      Matrix.of fun i j => (fun i => -dixonW a t i.castSucc) i *
        (Matrix.of fun i j => (a i.castSucc - t j)⁻¹ : Matrix (Fin n) (Fin n) ℝ) i j from rfl,
    Matrix.det_mul_column, abs_mul, det_cauchy_real _ _ fun j k => hne _ k, abs_prod]
  congr 1
  exact prod_congr rfl fun i _ => by rw [abs_neg, abs_of_pos (dixonW_pos ha ht _)]

/-! ### Index bookkeeping -/

/-- `∑ᵢ ∑_{k≠i} cᵢ f(i, k) = ∑ᵢ ∑_{k>i} (cᵢ + cₖ) f(i, k)` for symmetric `f`. -/
theorem sum_erase_eq_sum_Ioi {m : ℕ} (c : Fin m → ℂ) (f : Fin m → Fin m → ℂ)
    (hf : ∀ i k, f i k = f k i) :
    ∑ i, ∑ k ∈ univ.erase i, c i * f i k = ∑ i, ∑ k ∈ Ioi i, (c i + c k) * f i k := by
  have hsplit : ∀ i : Fin m, univ.erase i = Iio i ∪ Ioi i := fun i => by
    ext k
    simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_Iio, Finset.mem_Ioi,
      Finset.mem_univ, and_true]
    exact ne_iff_lt_or_gt (a := k) (b := i)
  have hdisj : ∀ i : Fin m, Disjoint (Iio i) (Ioi i) := fun i =>
    disjoint_left.mpr fun k h1 h2 => lt_asymm (mem_Iio.mp h1) (mem_Ioi.mp h2)
  simp_rw [hsplit, sum_union (hdisj _), sum_add_distrib, add_mul, sum_add_distrib]
  rw [add_comm]
  congr 1
  rw [sum_sigma', sum_sigma']
  refine sum_bij' (fun p _ => ⟨p.2, p.1⟩) (fun p _ => ⟨p.2, p.1⟩) ?_ ?_ ?_ ?_ ?_ <;>
    simp (config := { contextual := true }) [hf]

/-- Splitting `∑_{i<k≤n}` into `∑_{i<k<n}` and the terms with `k = n`. -/
theorem sum_Ioi_castSucc {M : Type*} [AddCommMonoid M] (h : Fin (n + 1) → Fin (n + 1) → M) :
    ∑ i, ∑ k ∈ Ioi i, h i k =
      ∑ j : Fin n, ∑ k ∈ Ioi j, h j.castSucc k.castSucc +
        ∑ j : Fin n, h j.castSucc (Fin.last n) := by
  have hlast : Ioi (Fin.last n) = ∅ := by ext k; simp [Fin.le_last]
  rw [Fin.sum_univ_castSucc, hlast, sum_empty, add_zero, ← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  have e : ∀ {m : ℕ} (i : Fin m) (g : Fin m → M), ∑ k ∈ Ioi i, g k =
      ∑ k, if i < k then g k else 0 := fun i g => by
    rw [← sum_filter]; congr 1; ext k; simp
  rw [e, e, Fin.sum_univ_castSucc]
  simp only [Fin.castSucc_lt_castSucc_iff, Fin.castSucc_lt_last, ↓reduceIte]

/-- `∑_{k≠i} g(k)` over `Fin (n+1)` at `i = j.castSucc`. -/
theorem sum_erase_castSucc {M : Type*} [AddCommGroup M] (g : Fin (n + 1) → M) (j : Fin n) :
    ∑ k ∈ univ.erase j.castSucc, g k = ∑ k ∈ univ.erase j, g k.castSucc + g (Fin.last n) := by
  rw [sum_erase_eq_sub (mem_univ _), sum_erase_eq_sub (mem_univ _), Fin.sum_univ_castSucc]
  abel

/-- The exponent identity behind the Dixon–Anderson integral, with `lp ≈ ln|aᵢ − tⱼ|`,
`lq ≈ ln|aᵢ − aₖ|`, `lr ≈ ln|tⱼ − tₖ|`, and `lw ≈ ln wᵢ`. -/
theorem dixon_exponent_identity (s : Fin (n + 1) → ℂ) (lp : Fin (n + 1) → Fin n → ℂ)
    (lq : Fin (n + 1) → Fin (n + 1) → ℂ) (hq : ∀ i k, lq i k = lq k i)
    (lr : Fin n → Fin n → ℂ) (hr : ∀ i k, lr i k = lr k i) :
    (∑ i : Fin n, (∑ j, lp i.castSucc j - ∑ k ∈ univ.erase i.castSucc, lq i.castSucc k) +
      (∑ j : Fin n, ∑ k ∈ Ioi j, (lq k.castSucc j.castSucc + lr k j) -
        ∑ j : Fin n, ∑ k : Fin n, lp j.castSucc k)) +
      ∑ i, (s i - 1) * (∑ j, lp i j - ∑ k ∈ univ.erase i, lq i k) =
    ∑ i : Fin n, ∑ j ∈ Ioi i, lr i j + ∑ i : Fin n, ∑ j, (s j - 1) * lp j i -
      ∑ i, ∑ k ∈ Ioi i, (s i + s k - 1) * lq i k := by
  set A := ∑ j : Fin n, ∑ k ∈ Ioi j, lq j.castSucc k.castSucc
  set B := ∑ j : Fin n, lq j.castSucc (Fin.last n)
  set D := ∑ i, ∑ k ∈ Ioi i, ((s i - 1) + (s k - 1)) * lq i k
  set LR := ∑ i : Fin n, ∑ j ∈ Ioi i, lr i j
  set SP := ∑ i, (s i - 1) * ∑ j, lp i j
  have h1 : ∑ i : Fin n, ∑ k ∈ univ.erase i.castSucc, lq i.castSucc k = 2 * A + B := by
    simp_rw [sum_erase_castSucc]
    rw [sum_add_distrib]
    have := sum_erase_eq_sum_Ioi (m := n) (fun _ => 1) (fun i k => lq i.castSucc k.castSucc)
      (fun i k => hq _ _)
    simp only [one_mul] at this
    rw [this]
    simp only [A, mul_sum]
    congr 1
    refine sum_congr rfl fun i _ => sum_congr rfl fun k _ => ?_
    ring
  have h2 : ∑ j : Fin n, ∑ k ∈ Ioi j, (lq k.castSucc j.castSucc + lr k j) = A + LR := by
    simp only [sum_add_distrib, A, LR]
    congr 1
    · exact sum_congr rfl fun j _ => sum_congr rfl fun k _ => hq _ _
    · exact sum_congr rfl fun j _ => sum_congr rfl fun k _ => hr _ _
  have h3 : ∑ i, (s i - 1) * (∑ j, lp i j - ∑ k ∈ univ.erase i, lq i k) = SP - D := by
    simp only [mul_sub, sum_sub_distrib, SP, D, mul_sum]
    congr 1
    exact sum_erase_eq_sum_Ioi (fun i => s i - 1) lq hq
  have h4 : ∑ i : Fin n, ∑ j, (s j - 1) * lp j i = SP := by
    simp only [SP, mul_sum]; exact sum_comm
  have h5 : ∑ i, ∑ k ∈ Ioi i, (s i + s k - 1) * lq i k = D + (A + B) := by
    rw [show (A + B) = ∑ i, ∑ k ∈ Ioi i, lq i k from (sum_Ioi_castSucc lq).symm]
    simp only [D, ← sum_add_distrib]
    exact sum_congr rfl fun i _ => sum_congr rfl fun k _ => by ring
  rw [sum_sub_distrib, h1, h2, h3, h4, h5]
  ring

/-! ### The pointwise identity -/

/-- The Dixon–Anderson integrand `∏_{i<j} (tᵢ − tⱼ) ∏ᵢ ∏ⱼ |tᵢ − aⱼ|^{sⱼ−1}`. -/
noncomputable def dixonIntegrand (a : Fin (n + 1) → ℝ) (s : Fin (n + 1) → ℂ) (t : Fin n → ℝ) : ℂ :=
  (∏ i, ∏ j ∈ Ioi i, ((t i - t j : ℝ) : ℂ)) * ∏ i, ∏ j, ((|t i - a j| : ℝ) : ℂ) ^ (s j - 1)

/-- The constant `∏_{i<j} (aᵢ − aⱼ)^{sᵢ+sⱼ−1}`. -/
noncomputable def dixonConst (a : Fin (n + 1) → ℝ) (s : Fin (n + 1) → ℂ) : ℂ :=
  ∏ i, ∏ k ∈ Ioi i, ((a i - a k : ℝ) : ℂ) ^ (s i + s k - 1)

theorem ofReal_eq_Complex.exp_log {r : ℝ} (hr : 0 < r) : (r : ℂ) = Complex.exp (Real.log r) := by
  rw [← Complex.ofReal_exp, Real.exp_log hr]

theorem prod_ofReal_eq_Complex.exp {ι : Type*} (u : Finset ι) {f : ι → ℝ} (hf : ∀ i ∈ u, 0 < f i) :
    ∏ i ∈ u, (f i : ℂ) = Complex.exp (∑ i ∈ u, (Real.log (f i) : ℂ)) := by
  rw [Complex.exp_sum]; exact prod_congr rfl fun i hi => ofReal_eq_Complex.exp_log (hf i hi)

theorem prod_cpow_eq_Complex.exp {ι : Type*} (u : Finset ι) {f : ι → ℝ} (hf : ∀ i ∈ u, 0 < f i)
    (w : ι → ℂ) : ∏ i ∈ u, (f i : ℂ) ^ w i = Complex.exp (∑ i ∈ u, w i * Real.log (f i)) := by
  rw [Complex.exp_sum]; exact prod_congr rfl fun i hi => cpow_pos_eq (hf i hi) _

theorem point_order {a : Fin (n + 1) → ℝ} (ha : StrictAnti a) {t : Fin n → ℝ}
    (ht : t ∈ dixonRegion a) {i j : Fin n} (hij : i < j) : t j < t i := by
  have h1 : i.succ ≤ j.castSucc := by rw [Fin.le_iff_val_le_val]; simp; omega
  have := (ht i).1; have := (ht j).2
  linarith [ha.antitone h1]

theorem log_dixonW {a : Fin (n + 1) → ℝ} (ha : StrictAnti a) {t : Fin n → ℝ}
    (ht : t ∈ dixonRegion a) (i : Fin (n + 1)) :
    Real.log (dixonW a t i) =
      ∑ j, Real.log |a i - t j| - ∑ k ∈ univ.erase i, Real.log |a i - a k| := by
  rw [dixonW_eq_abs ha ht, Real.log_div, Real.log_prod, Real.log_prod]
  · exact fun k hk => abs_ne_zero.mpr (sub_ne_zero.mpr fun h => (mem_erase.mp hk).1
      (ha.injective h).symm)
  · exact fun j _ => abs_ne_zero.mpr (sub_ne_zero.mpr (node_ne_point ha ht i j))
  · exact prod_ne_zero_iff.mpr fun j _ => abs_ne_zero.mpr (sub_ne_zero.mpr
      (node_ne_point ha ht i j))
  · exact prod_ne_zero_iff.mpr fun k hk => abs_ne_zero.mpr (sub_ne_zero.mpr fun h =>
      (mem_erase.mp hk).1 (ha.injective h).symm)

theorem log_abs_det_dixonJac {a : Fin (n + 1) → ℝ} (ha : StrictAnti a) {t : Fin n → ℝ}
    (ht : t ∈ dixonRegion a) :
    Real.log |(dixonJac a t).det| = ∑ i : Fin n, Real.log (dixonW a t i.castSucc) +
      (∑ j : Fin n, ∑ k ∈ Ioi j, (Real.log |a k.castSucc - a j.castSucc| + Real.log |t k - t j|) -
        ∑ j : Fin n, ∑ k : Fin n, Real.log |a j.castSucc - t k|) := by
  have hne := node_ne_point ha ht
  have hQR : ∀ j k : Fin n, j < k →
      |a k.castSucc - a j.castSucc| ≠ 0 ∧ |t k - t j| ≠ 0 := fun j k h =>
    ⟨abs_ne_zero.mpr (sub_ne_zero.mpr fun h' => ne_of_gt h (Fin.castSucc_injective n
      (ha.injective h'))), abs_ne_zero.mpr (sub_ne_zero.mpr (ne_of_lt (point_order ha ht h)))⟩
  rw [abs_det_dixonJac ha ht, Real.log_mul, Real.log_div, Real.log_prod, Real.log_prod,
    Real.log_prod]
  · congr 1; congr 1
    · refine sum_congr rfl fun j _ => ?_
      rw [Real.log_prod]
      · exact sum_congr rfl fun k hk => Real.log_mul (hQR j k (mem_Ioi.mp hk)).1
          (hQR j k (mem_Ioi.mp hk)).2
      · exact fun k hk => mul_ne_zero (hQR j k (mem_Ioi.mp hk)).1 (hQR j k (mem_Ioi.mp hk)).2
    · refine sum_congr rfl fun j _ => ?_
      rw [Real.log_prod]
      exact fun k _ => abs_ne_zero.mpr (sub_ne_zero.mpr (hne _ k))
  · exact fun j _ => prod_ne_zero_iff.mpr fun k _ => abs_ne_zero.mpr (sub_ne_zero.mpr (hne _ k))
  · exact fun j _ => prod_ne_zero_iff.mpr fun k hk =>
      mul_ne_zero (hQR j k (mem_Ioi.mp hk)).1 (hQR j k (mem_Ioi.mp hk)).2
  · exact fun i _ => (dixonW_pos ha ht _).ne'
  · exact prod_ne_zero_iff.mpr fun j _ => prod_ne_zero_iff.mpr fun k hk =>
      mul_ne_zero (hQR j k (mem_Ioi.mp hk)).1 (hQR j k (mem_Ioi.mp hk)).2
  · exact prod_ne_zero_iff.mpr fun j _ => prod_ne_zero_iff.mpr fun k _ =>
      abs_ne_zero.mpr (sub_ne_zero.mpr (hne _ k))
  · exact prod_ne_zero_iff.mpr fun i _ => (dixonW_pos ha ht _).ne'
  · exact div_ne_zero (prod_ne_zero_iff.mpr fun j _ => prod_ne_zero_iff.mpr fun k hk =>
      mul_ne_zero (hQR j k (mem_Ioi.mp hk)).1 (hQR j k (mem_Ioi.mp hk)).2)
      (prod_ne_zero_iff.mpr fun j _ => prod_ne_zero_iff.mpr fun k _ =>
        abs_ne_zero.mpr (sub_ne_zero.mpr (hne _ k)))

/-- **The pointwise identity**: `|det Φ′(t)| · (Dirichlet integrand at Φ(t)) =
(Dixon–Anderson integrand at t) / ∏_{i<j}(aᵢ − aⱼ)^{sᵢ+sⱼ−1}`. -/
theorem dixon_pointwise {a : Fin (n + 1) → ℝ} (ha : StrictAnti a) (s : Fin (n + 1) → ℂ)
    {t : Fin n → ℝ} (ht : t ∈ dixonRegion a) :
    ((|(dixonJac a t).det| : ℝ) : ℂ) *
      dirichletF n (fun i => s i.castSucc) (s (Fin.last n)) (dixonPhi a t) =
      dixonIntegrand a s t / dixonConst a s := by
  have hne := node_ne_point ha ht
  have hW := dixonW_pos ha ht
  have hdet0 : 0 < |(dixonJac a t).det| := by
    rw [abs_det_dixonJac ha ht]
    refine mul_pos (prod_pos fun i _ => hW _) (div_pos (prod_pos fun j _ => prod_pos fun k hk =>
      mul_pos (abs_pos.mpr (sub_ne_zero.mpr fun h => ne_of_gt (mem_Ioi.mp hk)
        (Fin.castSucc_injective n (ha.injective h)))) (abs_pos.mpr (sub_ne_zero.mpr
          (ne_of_lt (point_order ha ht (mem_Ioi.mp hk))))))
      (prod_pos fun j _ => prod_pos fun k _ => abs_pos.mpr (sub_ne_zero.mpr (hne _ k))))
  have hlast : (1 - ∑ i : Fin n, dixonPhi a t i) = dixonW a t (Fin.last n) := by
    have := sum_dixonW ha.injective t
    rw [Fin.sum_univ_castSucc] at this
    simp only [dixonPhi]; linarith
  -- the left side
  have hL : ((|(dixonJac a t).det| : ℝ) : ℂ) *
      dirichletF n (fun i => s i.castSucc) (s (Fin.last n)) (dixonPhi a t) =
      Complex.exp ((Real.log |(dixonJac a t).det| : ℂ) +
        ∑ i, (s i - 1) * (Real.log (dixonW a t i) : ℂ)) := by
    rw [dirichletF, hlast, ofReal_eq_Complex.exp_log hdet0]
    simp only [dixonPhi]
    rw [prod_cpow_eq_Complex.exp _ fun i _ => hW _, cpow_pos_eq (hW _), ← Complex.exp_add,
      ← Complex.exp_add, Fin.sum_univ_castSucc]
  -- the right side
  have hR : dixonIntegrand a s t / dixonConst a s =
      Complex.exp ((∑ i : Fin n, ∑ j ∈ Ioi i, (Real.log |t i - t j| : ℂ) +
        ∑ i : Fin n, ∑ j, (s j - 1) * (Real.log |a j - t i| : ℂ)) -
        ∑ i, ∑ k ∈ Ioi i, (s i + s k - 1) * (Real.log |a i - a k| : ℂ)) := by
    rw [dixonIntegrand, dixonConst, Complex.exp_sub, Complex.exp_add, Complex.exp_sum,
      Complex.exp_sum, Complex.exp_sum]
    congr 1
    · congr 1
      · refine prod_congr rfl fun i _ => ?_
        rw [Complex.exp_sum]
        refine prod_congr rfl fun j hj => ?_
        have h := point_order ha ht (mem_Ioi.mp hj)
        rw [abs_of_pos (by linarith), ofReal_eq_Complex.exp_log (by linarith)]
      · refine prod_congr rfl fun i _ => ?_
        rw [Complex.exp_sum]
        refine prod_congr rfl fun j _ => ?_
        rw [abs_sub_comm, cpow_pos_eq (abs_pos.mpr (sub_ne_zero.mpr (hne j i)))]
    · refine prod_congr rfl fun i _ => ?_
      rw [Complex.exp_sum]
      refine prod_congr rfl fun k hk => ?_
      have h := ha (mem_Ioi.mp hk)
      rw [abs_of_pos (by linarith), cpow_pos_eq (by linarith)]
  rw [hL, hR]
  congr 1
  rw [log_abs_det_dixonJac ha ht]
  simp only [log_dixonW ha ht]
  push_cast
  have hq : ∀ i k : Fin (n + 1), (Real.log |a i - a k| : ℂ) = Real.log |a k - a i| :=
    fun i k => by rw [abs_sub_comm]
  have hr : ∀ i k : Fin n, (Real.log |t i - t k| : ℂ) = Real.log |t k - t i| :=
    fun i k => by rw [abs_sub_comm]
  have hid := dixon_exponent_identity s (fun i j => (Real.log |a i - t j| : ℂ))
    (fun i k => (Real.log |a i - a k| : ℂ)) hq (fun i k => (Real.log |t i - t k| : ℂ)) hr
  rw [← hid]

/-! ### The integral -/

open MeasureTheory

theorem volume_sum_eq_one (n : ℕ) :
    volume {w : Fin n → ℝ | ∑ i, w i = 1} = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : {w : Fin 0 → ℝ | ∑ i, w i = 1} = ∅ := by ext w; simp
    rw [this, measure_empty]
  set L : (Fin n → ℝ) →ₗ[ℝ] ℝ := ∑ i, LinearMap.proj i
  set w₀ : Fin n → ℝ := Pi.single ⟨0, hn⟩ 1
  have hL : ∀ w, L w = ∑ i, w i := fun w => by simp [L]
  have hw₀ : L w₀ = 1 := by rw [hL]; simp [w₀]
  have hker : LinearMap.ker L ≠ ⊤ := fun h => by
    have : w₀ ∈ LinearMap.ker L := h ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, hw₀] at this; exact one_ne_zero this
  have he : {w : Fin n → ℝ | ∑ i, w i = 1} = (fun x => x + -w₀) ⁻¹' (LinearMap.ker L) := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, SetLike.mem_coe, LinearMap.mem_ker, map_add,
      map_neg, hw₀]
    rw [hL]
    constructor <;> intro h <;> linarith
  rw [he, measure_preimage_add_right, Measure.addHaar_submodule volume _ hker]

theorem volume_simplex_diff_open (n : ℕ) :
    volume (simplexDLMF n \ openSimplexDLMF n) = 0 := by
  refine measure_mono_null (t := (⋃ i, {w : Fin n → ℝ | w i = 0}) ∪
    {w | ∑ i, w i = 1}) ?_ (measure_union_null (measure_iUnion_null fun i => ?_)
      (volume_sum_eq_one n))
  · rintro w ⟨⟨h0, h1⟩, hno⟩
    simp only [openSimplexDLMF, Set.mem_ofPred_eq, not_and_or, not_forall, not_lt] at hno
    rcases hno with ⟨i, hi⟩ | h
    · exact Or.inl (Set.mem_iUnion.mpr ⟨i, le_antisymm hi (h0 i)⟩)
    · exact Or.inr (le_antisymm h1 h)
  · rw [volume_pi]; exact Measure.pi_hyperplane _ i 0

theorem openSimplex_subset (n : ℕ) : openSimplexDLMF n ⊆ simplexDLMF n :=
  fun _ hw => ⟨fun i => (hw.1 i).le, hw.2.le⟩

theorem isOpen_dixonRegion (a : Fin (n + 1) → ℝ) : IsOpen (dixonRegion a) := by
  have : dixonRegion a = ⋂ i, {t : Fin n → ℝ | a i.succ < t i ∧ t i < a i.castSucc} := by
    ext t; simp [dixonRegion]
  rw [this]
  exact isOpen_iInter_of_finite fun i => (isOpen_lt continuous_const (continuous_apply i)).inter
    (isOpen_lt (continuous_apply i) continuous_const)

/-- **The Dixon–Anderson integral**: for `a₀ > a₁ > ⋯ > aₙ` and `ℜsⱼ > 0`,
`∫_{aᵢ₊₁<tᵢ<aᵢ} ∏_{i<j}(tᵢ − tⱼ) ∏ᵢ∏ⱼ |tᵢ − aⱼ|^{sⱼ−1} dt =
∏ⱼ Γ(sⱼ)/Γ(∑ sⱼ) · ∏_{i<j}(aᵢ − aⱼ)^{sᵢ+sⱼ−1}`. -/
theorem dixon_anderson {a : Fin (n + 1) → ℝ} (ha : StrictAnti a) (s : Fin (n + 1) → ℂ)
    (hs : ∀ i, 0 < (s i).re) :
    ∫ t in dixonRegion a, dixonIntegrand a s t =
      (∏ i, Complex.Gamma (s i)) / Complex.Gamma (∑ i, s i) * dixonConst a s := by
  have hD := (dirichlet_integral n (fun i => s i.castSucc) (fun i => hs _) (hs (Fin.last n))).2
  rw [dirichletG, integral_indicator (measurableSet_simplexDLMF n),
    setIntegral_congr_set (ae_eq_set.mpr ⟨volume_simplex_diff_open n,
      by rw [Set.sdiff_eq_empty.mpr (openSimplex_subset n), measure_empty]⟩),
    ← dixonW_image ha] at hD
  rw [show (fun t : Fin n → ℝ => fun i : Fin n => dixonW a t i.castSucc) = dixonPhi a from rfl,
    integral_image_eq_integral_abs_det_fderiv_smul volume (isOpen_dixonRegion a).measurableSet
    (fun t _ => (hasFDerivAt_dixonPhi a t).hasFDerivWithinAt)
    (dixonW_injOn ha : Set.InjOn (dixonPhi a) (dixonRegion a))] at hD
  have hC : dixonConst a s ≠ 0 := prod_ne_zero_iff.mpr fun i _ => prod_ne_zero_iff.mpr
    fun k hk => by
      rw [Ne, Complex.cpow_eq_zero_iff]
      exact fun h => sub_ne_zero.mpr (fun h' => ne_of_gt (mem_Ioi.mp hk) (ha.injective h').symm)
        (by exact_mod_cast h.1)
  have hpt : ∀ t ∈ dixonRegion a,
      |(LinearMap.toContinuousLinearMap (Matrix.toLin' (dixonJac a t))).det| •
        dirichletF n (fun i => s i.castSucc) (s (Fin.last n)) (dixonPhi a t) =
      dixonIntegrand a s t / dixonConst a s := fun t ht => by
    rw [det_dixonPhi', Complex.real_smul, dixon_pointwise ha s ht]
  rw [setIntegral_congr_fun (isOpen_dixonRegion a).measurableSet hpt, integral_div] at hD
  rw [Fin.prod_univ_castSucc, Fin.sum_univ_castSucc]
  rw [div_eq_iff hC] at hD
  rw [hD]

theorem integrableOn_dixonIntegrand {a : Fin (n + 1) → ℝ} (ha : StrictAnti a)
    (s : Fin (n + 1) → ℂ) (hs : ∀ i, 0 < (s i).re) :
    IntegrableOn (dixonIntegrand a s) (dixonRegion a) := by
  have hI := (dirichlet_integral n (fun i => s i.castSucc) (fun i => hs _) (hs (Fin.last n))).1
  have hI' : IntegrableOn (dirichletF n (fun i => s i.castSucc) (s (Fin.last n)))
      (openSimplexDLMF n) := by
    have := (integrable_indicator_iff (measurableSet_simplexDLMF n)).mp hI
    exact this.mono_set (openSimplex_subset n)
  rw [← dixonW_image ha, show (fun t : Fin n → ℝ => fun i : Fin n => dixonW a t i.castSucc) =
    dixonPhi a from rfl, integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    (isOpen_dixonRegion a).measurableSet (fun t _ => (hasFDerivAt_dixonPhi a t).hasFDerivWithinAt)
    (dixonW_injOn ha : Set.InjOn (dixonPhi a) (dixonRegion a))] at hI'
  have hC : dixonConst a s ≠ 0 := prod_ne_zero_iff.mpr fun i _ => prod_ne_zero_iff.mpr
    fun k hk => by
      rw [Ne, Complex.cpow_eq_zero_iff]
      exact fun h => sub_ne_zero.mpr (fun h' => ne_of_gt (mem_Ioi.mp hk) (ha.injective h').symm)
        (by exact_mod_cast h.1)
  have h2 : IntegrableOn (fun t => |(LinearMap.toContinuousLinearMap (Matrix.toLin'
      (dixonJac a t))).det| • dirichletF n (fun i => s i.castSucc) (s (Fin.last n)) (dixonPhi a t) *
        dixonConst a s) (dixonRegion a) := hI'.mul_const _
  refine IntegrableOn.congr_fun h2 (fun t ht => ?_) (isOpen_dixonRegion a).measurableSet
  rw [det_dixonPhi', Complex.real_smul, dixon_pointwise ha s ht, div_mul_cancel₀ _ hC]

end Azurite.DLMF
