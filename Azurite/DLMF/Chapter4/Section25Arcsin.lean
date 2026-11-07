/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section25

/-!
# DLMF 4.25.3

`arcsin z/(1 − z²)^{1/2} = z/(1 − 1·2z²/(3 − 1·2z²/(5 − 3·4z²/(7 − 3·4z²/(9 − ⋯)))))` on the cut
plane of Figure 4.23.1(i).

* Markov's theorem and the Gauss error bound for integrable (possibly unbounded) weights:
  `gauss_tendsto_of_weight`, `gauss_err_bound_of_weight` (§4.9 required continuous weights).
* In `w = z²` the function is `z G(w)` with `G(w) = Φ(0, 0, 1)`,
  `Φ(α, β, γ) = ∫₀¹ s^α (1 − s²)^β/(1 − w(1 − s²))^γ ds` (`asPhi`, relations `asPhi_split`,
  `asPhi_mul`, `asPhi_parts`).
* Errors (`asin_err`): `E_{2k} = (2k)! w^{2k} Φ(2k, k, k + 1)`,
  `E_{2k+1} = (2k + 1)! w^{2k+1} Φ(2k, k + 1, k + 1)`.
* With `t = s² − 1`, `G(w) = ∫₋₁⁰ ω(t)/(1 + wt) dt`, `ω(t) = 1/(2√(1 + t))` (`integral_asinOmega`).
  The even convergents are the Gauss rules for `ω` (`asin_even_eq`), the odd ones
  `1 + w ×` the Gauss rules for `−t ω(t)` (`asin_odd_eq`), by Padé uniqueness. Markov's theorem
  gives the limit (`asin_tendsto`).
* The value `z G(z²) = arcsin z/(1 − z²)^{1/2}` comes from the 4.23.3 integral for `arctan` at
  `tan(arcsin z)` (`asin_value`).
* 4.25.3: `dlmf_4_25_3`.
-/

open Polynomial Finset Set MeasureTheory Filter Topology Complex
open scoped Real Nat

namespace Azurite.DLMF

variable {a b : ℝ} {w : ℝ → ℝ}

theorem IsGaussWeight.intervalIntegrable (hw : IsGaussWeight (Ioo a b) w) (hab : a ≤ b) :
    IntervalIntegrable w volume a b := by
  have h := hw.integrableOn 0
  simp only [pow_zero, one_mul] at h
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab]
  exact h

theorem IsGaussWeight.intervalIntegrable_ofReal (hw : IsGaussWeight (Ioo a b) w) (hab : a ≤ b) :
    IntervalIntegrable (fun x => (w x : ℂ)) volume a b := by
  have h := hw.intervalIntegrable hab
  exact ⟨h.1.ofReal, h.2.ofReal⟩

/-- **Markov's theorem** for an integrable weight. -/
theorem gauss_tendsto_of_weight (hw : IsGaussWeight (Ioo a b) w) (hab : a ≤ b)
    (hw0 : ∀ x ∈ Icc a b, 0 ≤ w x) {P : ℕ → ℝ[X]} (hP : ∀ n, IsOrthMonic (Ioo a b) w n (P n))
    {g : ℝ → ℂ} (hg : ContinuousOn g (Icc a b)) :
    Tendsto (fun n => gaussQuad a b w (P n) g) atTop (𝓝 (∫ x in a..b, (w x : ℂ) * g x)) := by
  set W := ∫ x in a..b, w x with hWdef
  have hW0 : 0 ≤ W := intervalIntegral.integral_nonneg hab hw0
  rw [Metric.tendsto_atTop]
  intro ε hε
  set ε' := ε / (4 * (W + 1)) with hε'def
  have hε' : 0 < ε' := div_pos hε (by positivity)
  obtain ⟨pr, hpr⟩ := exists_polynomial_near_of_continuousOn a b (fun x => (g x).re)
    (continuous_re.comp_continuousOn hg) ε' hε'
  obtain ⟨pi, hpi⟩ := exists_polynomial_near_of_continuousOn a b (fun x => (g x).im)
    (continuous_im.comp_continuousOn hg) ε' hε'
  refine ⟨max pr.natDegree pi.natDegree + 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hdr : pr.degree < (2 * n : ℕ) :=
    degree_le_natDegree.trans_lt (by exact_mod_cast (by omega : pr.natDegree < 2 * n))
  have hdi : pi.degree < (2 * n : ℕ) :=
    degree_le_natDegree.trans_lt (by exact_mod_cast (by omega : pi.natDegree < 2 * n))
  set q : ℝ → ℂ := fun x => ((pr.eval x : ℝ) : ℂ) + I * ((pi.eval x : ℝ) : ℂ) with hqdef
  have hq : ∀ x ∈ Icc a b, ‖q x - g x‖ ≤ 2 * ε' := by
    intro x hx
    have hsplit : q x - g x = ((pr.eval x - (g x).re : ℝ) : ℂ) +
        I * ((pi.eval x - (g x).im : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hqdef]
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_I, one_mul, norm_real, norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    linarith [hpr x hx, hpi x hx]
  have hwI := hw.intervalIntegrable_ofReal hab
  have hcont : ∀ f : ℝ[X], IntervalIntegrable (fun x => (w x : ℂ) * ((f.eval x : ℝ) : ℂ))
      volume a b := fun f => hwI.mul_continuousOn (continuous_ofReal.comp f.continuous).continuousOn
  have hexact : (∫ x in a..b, (w x : ℂ) * q x) = gaussQuad a b w (P n) q := by
    have hsplit : (fun x => (w x : ℂ) * q x) = fun x =>
        (w x : ℂ) * ((pr.eval x : ℝ) : ℂ) + I * ((w x : ℂ) * ((pi.eval x : ℝ) : ℂ)) := by
      funext x; simp only [hqdef]; ring
    rw [hsplit, intervalIntegral.integral_add (hcont pr)
      ((hcont pi).const_mul _), intervalIntegral.integral_const_mul,
      gauss_exact_C hw hab (hP n) hdr, gauss_exact_C hw hab (hP n) hdi]
    simp only [gaussQuad, hqdef, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun k _ => ?_
    ring
  have hc0 : ∀ k ∈ (P n).roots.toFinset, 0 < christoffel (Ioo a b) w (P n) k :=
    fun k hk => christoffel_pos hw (hP n) hk
  have hsum := gauss_sum_weights hw hab (hP n) hn1
  have hmem : ∀ k ∈ (P n).roots.toFinset, k ∈ Icc a b := fun k hk =>
    Ioo_subset_Icc_self (gauss_nodes_mem hw (hP n) hk)
  have hqc : ContinuousOn q (Icc a b) := by
    simp only [hqdef]
    exact ((continuous_ofReal.comp pr.continuous).add
      (continuous_const.mul (continuous_ofReal.comp pi.continuous))).continuousOn
  have hintg : IntervalIntegrable (fun x => (w x : ℂ) * g x) volume a b :=
    hwI.mul_continuousOn (by rw [uIcc_of_le hab]; exact hg)
  have hintq : IntervalIntegrable (fun x => (w x : ℂ) * q x) volume a b :=
    hwI.mul_continuousOn (by rw [uIcc_of_le hab]; exact hqc)
  have hdecomp : gaussQuad a b w (P n) g - ∫ x in a..b, (w x : ℂ) * g x =
      gaussQuad a b w (P n) (fun x => g x - q x) + ∫ x in a..b, (w x : ℂ) * (q x - g x) := by
    have h1 : (∫ x in a..b, (w x : ℂ) * (q x - g x)) =
        (∫ x in a..b, (w x : ℂ) * q x) - ∫ x in a..b, (w x : ℂ) * g x := by
      rw [← intervalIntegral.integral_sub hintq hintg]; congr 1; funext x; ring
    rw [h1, hexact]
    simp only [gaussQuad, mul_sub, sum_sub_distrib]
    ring
  have hb1 : ‖gaussQuad a b w (P n) (fun x => g x - q x)‖ ≤ 2 * ε' * W := by
    simp only [gaussQuad]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k ∈ (P n).roots.toFinset,
          ‖(christoffel (Ioo a b) w (P n) k : ℂ) * (g k - q k)‖
        ≤ ∑ k ∈ (P n).roots.toFinset, christoffel (Ioo a b) w (P n) k * (2 * ε') := by
          refine sum_le_sum fun k hk => ?_
          rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (hc0 k hk), norm_sub_rev]
          exact mul_le_mul_of_nonneg_left (hq k (hmem k hk)) (hc0 k hk).le
      _ = 2 * ε' * W := by rw [← sum_mul, hsum]; ring
  have hb2 : ‖∫ x in a..b, (w x : ℂ) * (q x - g x)‖ ≤ 2 * ε' * W := by
    have := intervalIntegral.norm_integral_le_of_norm_le hab
      (f := fun x => (w x : ℂ) * (q x - g x)) (g := fun x => w x * (2 * ε'))
      (Eventually.of_forall fun x hx => by
        have hx' : x ∈ Icc a b := Ioc_subset_Icc_self hx
        rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (hw0 x hx')]
        exact mul_le_mul_of_nonneg_left (hq x hx') (hw0 x hx'))
      ((hw.intervalIntegrable hab).mul_const _)
    rw [intervalIntegral.integral_mul_const] at this
    linarith
  rw [dist_eq_norm, hdecomp]
  calc ‖gaussQuad a b w (P n) (fun x => g x - q x) + ∫ x in a..b, (w x : ℂ) * (q x - g x)‖
      ≤ 2 * ε' * W + 2 * ε' * W := (norm_add_le _ _).trans (add_le_add hb1 hb2)
    _ = ε * (W / (W + 1)) := by rw [hε'def]; field_simp; ring
    _ < ε := mul_lt_of_lt_one_right hε ((div_lt_one (by positivity)).mpr (by linarith))


/-- The Gauss error bound for an integrable weight. -/
theorem gauss_err_bound_of_weight (hw : IsGaussWeight (Ioo a b) w) (hab : a ≤ b)
    (ha : -1 ≤ a) (hb : b ≤ 1) (hw0 : ∀ x ∈ Icc a b, 0 ≤ w x) {n : ℕ} {p : ℝ[X]}
    (hp : IsOrthMonic (Ioo a b) w n p) :
    ∃ C, ∀ z : ℂ, ‖z‖ ≤ 1 / 2 →
      ‖gaussB p z * (∫ x in a..b, (w x : ℂ) / (1 + z * x)) - gaussA a b w p z‖ ≤
        C * ‖z‖ ^ (2 * n) := by
  set S := p.roots.toFinset
  set W := ∫ x in a..b, w x
  have hW0 : 0 ≤ W := intervalIntegral.integral_nonneg hab hw0
  have hmem : ∀ k ∈ S, |k| ≤ 1 := fun k hk => by
    have := gauss_nodes_mem hw hp hk
    exact abs_le.mpr ⟨by linarith [this.1], by linarith [this.2]⟩
  have hc0 : ∀ k ∈ S, 0 < christoffel (Ioo a b) w p k := fun k hk => christoffel_pos hw hp hk
  set Sc := ∑ k ∈ S, christoffel (Ioo a b) w p k
  have hSc : 0 ≤ Sc := sum_nonneg fun k hk => (hc0 k hk).le
  refine ⟨2 ^ S.card * (2 * W + 2 * Sc), fun z hz => ?_⟩
  have hx : ∀ x ∈ uIcc a b, |x| ≤ 1 := fun x hx => by
    rw [uIcc_of_le hab] at hx
    exact abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hne : ∀ k ∈ S, 1 + z * k ≠ 0 := fun k hk => one_add_mul_ne_zero hz (hmem k hk)
  rw [gaussA_eq hne, ← mul_sub]
  set N := 2 * n
  -- the polynomial part is integrated exactly
  have hgeom : ∀ x : ℝ, |x| ≤ 1 → (1 : ℂ) / (1 + z * x) =
      ∑ j ∈ range N, (-z) ^ j * (x : ℂ) ^ j + (-z) ^ N * ((x : ℂ) ^ N / (1 + z * x)) := by
    intro x hx'
    rw [inv_one_add_eq_geom _ (one_add_mul_ne_zero hz hx') N]
    congr 1
    · refine sum_congr rfl fun j _ => ?_; ring
    · ring
  have hwI := hw.intervalIntegrable_ofReal hab
  have hcontI : ∀ j : ℕ, IntervalIntegrable (fun x : ℝ => (w x : ℂ) * (x : ℂ) ^ j) volume a b :=
    fun j => hwI.mul_continuousOn (continuous_ofReal.pow j).continuousOn
  have hcontR : IntervalIntegrable (fun x : ℝ => (w x : ℂ) * ((x : ℂ) ^ N / (1 + z * x)))
      volume a b :=
    hwI.mul_continuousOn (((continuous_ofReal.pow N).continuousOn).div
        (continuous_const.add (continuous_const.mul continuous_ofReal)).continuousOn
        fun x hx' => one_add_mul_ne_zero hz (hx x hx'))
  have hint_eq : (∫ x in a..b, (w x : ℂ) / (1 + z * x)) =
      ∑ j ∈ range N, (-z) ^ j * (∫ x in a..b, (w x : ℂ) * (x : ℂ) ^ j) +
        (-z) ^ N * ∫ x in a..b, (w x : ℂ) * ((x : ℂ) ^ N / (1 + z * x)) := by
    rw [intervalIntegral.integral_congr (g := fun x => ∑ j ∈ range N,
        (-z) ^ j * ((w x : ℂ) * (x : ℂ) ^ j) +
        (-z) ^ N * ((w x : ℂ) * ((x : ℂ) ^ N / (1 + z * x)))) fun x hx' => by
      simp only
      rw [div_eq_mul_one_div (w x : ℂ), hgeom x (hx x hx'), mul_add, mul_sum]
      congr 1
      · refine sum_congr rfl fun j _ => ?_; ring
      · ring]
    have hI1 : IntervalIntegrable (fun x : ℝ => ∑ j ∈ range N,
        (-z) ^ j * ((w x : ℂ) * (x : ℂ) ^ j)) volume a b :=
      (IntervalIntegrable.sum (range N) fun j _ => (hcontI j).const_mul ((-z) ^ j)).congr
        fun x _ => by simp only [Finset.sum_apply]
    rw [intervalIntegral.integral_add hI1 (hcontR.const_mul _),
      intervalIntegral.integral_finsetSum fun j _ => (hcontI j).const_mul _,
      intervalIntegral.integral_const_mul]
    simp only [intervalIntegral.integral_const_mul]
  have hsum_eq : gaussQuad a b w p (fun t => 1 / (1 + z * t)) =
      ∑ j ∈ range N, (-z) ^ j * gaussQuad a b w p (fun x => (x : ℂ) ^ j) +
        (-z) ^ N * gaussQuad a b w p (fun x => (x : ℂ) ^ N / (1 + z * x)) := by
    simp only [gaussQuad, mul_sum]
    rw [sum_comm, ← sum_add_distrib]
    refine sum_congr rfl fun k hk => ?_
    rw [hgeom k (hmem k hk), mul_add, mul_sum]
    congr 1
    · refine sum_congr rfl fun j _ => ?_; ring
    · ring
  have hexact : ∀ j ∈ range N, (∫ x in a..b, (w x : ℂ) * (x : ℂ) ^ j) =
      gaussQuad a b w p (fun x => (x : ℂ) ^ j) := fun j hj => by
    have := gauss_exact_C hw hab hp (f := X ^ j) (by
      rw [degree_X_pow]; exact_mod_cast mem_range.mp hj)
    simpa using this
  have hpoly : ∑ j ∈ range N, (-z) ^ j * (∫ x in a..b, (w x : ℂ) * (x : ℂ) ^ j) =
      ∑ j ∈ range N, (-z) ^ j * gaussQuad a b w p (fun x => (x : ℂ) ^ j) :=
    sum_congr rfl fun j hj => by rw [hexact j hj]
  rw [hint_eq, hsum_eq, hpoly, add_sub_add_left_eq_sub, ← mul_sub]
  -- bounds
  have hB : ‖gaussB p z‖ ≤ 2 ^ S.card := by
    simp only [gaussB]
    rw [norm_prod]
    refine (prod_le_prod₀ (fun k _ => norm_nonneg _) fun k hk => (?_ : _ ≤ (2 : ℝ))).trans
      (by rw [prod_const])
    have := norm_add_le (1 : ℂ) (z * k)
    rw [norm_one, norm_mul, norm_real, Real.norm_eq_abs] at this
    nlinarith [hmem k hk, norm_nonneg z, abs_nonneg k]
  have hR1 : ‖∫ x in a..b, (w x : ℂ) * ((x : ℂ) ^ N / (1 + z * x))‖ ≤ 2 * W := by
    have := intervalIntegral.norm_integral_le_of_norm_le hab
      (f := fun x => (w x : ℂ) * ((x : ℂ) ^ N / (1 + z * x))) (g := fun x => w x * 2)
      (Eventually.of_forall fun x hx' => by
        have hx'' : x ∈ Icc a b := Ioc_subset_Icc_self hx'
        have hxa : |x| ≤ 1 := abs_le.mpr ⟨by linarith [hx''.1], by linarith [hx''.2]⟩
        rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (hw0 x hx''), norm_div,
          norm_pow, norm_real, Real.norm_eq_abs]
        refine mul_le_mul_of_nonneg_left ?_ (hw0 x hx'')
        have h1 := norm_one_add_mul_ge hz hxa
        rw [div_le_iff₀ (by linarith)]
        have : |x| ^ N ≤ 1 := pow_le_one₀ (abs_nonneg x) hxa
        linarith)
      ((hw.intervalIntegrable hab).mul_const _)
    rw [intervalIntegral.integral_mul_const] at this
    linarith
  have hR2 : ‖gaussQuad a b w p (fun x => (x : ℂ) ^ N / (1 + z * x))‖ ≤ 2 * Sc := by
    simp only [gaussQuad]
    refine (norm_sum_le _ _).trans ?_
    rw [mul_sum]
    refine sum_le_sum fun k hk => ?_
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (hc0 k hk), norm_div, norm_pow,
      norm_real, Real.norm_eq_abs]
    have h1 := norm_one_add_mul_ge hz (hmem k hk)
    have : |k| ^ N ≤ 1 := pow_le_one₀ (abs_nonneg k) (hmem k hk)
    have h2 : |k| ^ N / ‖1 + z * k‖ ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
    nlinarith [hc0 k hk]
  rw [norm_mul, norm_mul, norm_pow, norm_neg]
  have h3 : ‖(∫ x in a..b, (w x : ℂ) * ((x : ℂ) ^ N / (1 + z * x))) -
      gaussQuad a b w p (fun x => (x : ℂ) ^ N / (1 + z * x))‖ ≤ 2 * W + 2 * Sc :=
    (norm_sub_le _ _).trans (add_le_add hR1 hR2)
  calc ‖gaussB p z‖ * (‖z‖ ^ N * ‖(∫ x in a..b, (w x : ℂ) * ((x : ℂ) ^ N / (1 + z * x))) -
        gaussQuad a b w p (fun x => (x : ℂ) ^ N / (1 + z * x))‖)
      ≤ 2 ^ S.card * (‖z‖ ^ N * (2 * W + 2 * Sc)) := by gcongr
    _ = 2 ^ S.card * (2 * W + 2 * Sc) * ‖z‖ ^ N := by ring


/-! ### The integrals `Φ(α, β, γ)` -/

/-- `Φ(α, β, γ) = ∫₀¹ s^α (1 − s²)^β / (1 − w(1 − s²))^γ ds`. -/
noncomputable def asPhi (α β γ : ℕ) (w : ℂ) : ℂ :=
  ∫ s in (0 : ℝ)..1, (s : ℂ) ^ α * (1 - (s : ℂ) ^ 2) ^ β / (1 - w * (1 - (s : ℂ) ^ 2)) ^ γ

variable {w : ℂ}

theorem asPhi_continuousOn (hD : ∀ s ∈ Icc (0 : ℝ) 1, 1 - w * (1 - (s : ℂ) ^ 2) ≠ 0)
    (α β γ : ℕ) : ContinuousOn (fun s : ℝ =>
      (s : ℂ) ^ α * (1 - (s : ℂ) ^ 2) ^ β / (1 - w * (1 - (s : ℂ) ^ 2)) ^ γ) (Icc 0 1) :=
  (((continuous_ofReal.pow α).mul ((continuous_const.sub (continuous_ofReal.pow 2)).pow β))
    |>.continuousOn).div
    ((continuous_const.sub (continuous_const.mul
      (continuous_const.sub (continuous_ofReal.pow 2)))).pow γ).continuousOn
    fun s hs => pow_ne_zero _ (hD s hs)

theorem asPhi_integrable (hD : ∀ s ∈ Icc (0 : ℝ) 1, 1 - w * (1 - (s : ℂ) ^ 2) ≠ 0)
    (α β γ : ℕ) : IntervalIntegrable (fun s : ℝ =>
      (s : ℂ) ^ α * (1 - (s : ℂ) ^ 2) ^ β / (1 - w * (1 - (s : ℂ) ^ 2)) ^ γ) volume 0 1 :=
  ContinuousOn.intervalIntegrable (by
    rw [Set.uIcc_of_le zero_le_one]; exact asPhi_continuousOn hD α β γ)

theorem asPhi_split (hD : ∀ s ∈ Icc (0 : ℝ) 1, 1 - w * (1 - (s : ℂ) ^ 2) ≠ 0) (α β γ : ℕ) :
    asPhi α (β + 1) γ w = asPhi α β γ w - asPhi (α + 2) β γ w := by
  rw [asPhi, asPhi, asPhi, ← intervalIntegral.integral_sub (asPhi_integrable hD α β γ)
    (asPhi_integrable hD (α + 2) β γ)]
  congr 1; funext s; ring

theorem asPhi_mul (hD : ∀ s ∈ Icc (0 : ℝ) 1, 1 - w * (1 - (s : ℂ) ^ 2) ≠ 0) (α β γ : ℕ) :
    asPhi α β γ w = asPhi α β (γ + 1) w - w * asPhi α (β + 1) (γ + 1) w := by
  rw [asPhi, asPhi, asPhi, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub (asPhi_integrable hD α β (γ + 1))
    ((asPhi_integrable hD α (β + 1) (γ + 1)).const_mul w)]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [Set.uIcc_of_le zero_le_one] at hs
  have h0 := hD s hs
  obtain ⟨d, hd⟩ : ∃ d, d = 1 - w * (1 - (s : ℂ) ^ 2) := ⟨_, rfl⟩
  rw [← hd] at h0 ⊢
  field_simp
  rw [hd]
  ring

theorem asPhi_parts (hD : ∀ s ∈ Icc (0 : ℝ) 1, 1 - w * (1 - (s : ℂ) ^ 2) ≠ 0) (α β γ : ℕ) :
    (α + 1 : ℂ) * asPhi α (β + 1) (γ + 1) w - 2 * (β + 1) * asPhi (α + 2) β (γ + 1) w -
      2 * (γ + 1) * w * asPhi (α + 2) (β + 1) (γ + 2) w = 0 := by
  set F : ℝ → ℂ := fun s => (s : ℂ) ^ (α + 1) * (1 - (s : ℂ) ^ 2) ^ (β + 1) /
    (1 - w * (1 - (s : ℂ) ^ 2)) ^ (γ + 1) with hF
  set F' : ℝ → ℂ := fun s => (α + 1 : ℂ) * ((s : ℂ) ^ α * (1 - (s : ℂ) ^ 2) ^ (β + 1) /
      (1 - w * (1 - (s : ℂ) ^ 2)) ^ (γ + 1)) -
    2 * (β + 1) * ((s : ℂ) ^ (α + 2) * (1 - (s : ℂ) ^ 2) ^ β /
      (1 - w * (1 - (s : ℂ) ^ 2)) ^ (γ + 1)) -
    2 * (γ + 1) * w * ((s : ℂ) ^ (α + 2) * (1 - (s : ℂ) ^ 2) ^ (β + 1) /
      (1 - w * (1 - (s : ℂ) ^ 2)) ^ (γ + 2)) with hF'
  have hd : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt F (F' s) s := by
    intro s hs
    rw [Set.uIcc_of_le zero_le_one] at hs
    have hDs := hD s hs
    have hN : HasDerivAt (fun x : ℂ => x ^ (α + 1) * (1 - x ^ 2) ^ (β + 1))
        ((α + 1 : ℂ) * (s : ℂ) ^ α * (1 - (s : ℂ) ^ 2) ^ (β + 1) +
          (s : ℂ) ^ (α + 1) * ((β + 1 : ℂ) * (1 - (s : ℂ) ^ 2) ^ β * (-(2 * (s : ℂ))))) s := by
      have h1 := hasDerivAt_pow (α + 1) (s : ℂ)
      have h2 := ((hasDerivAt_pow 2 (s : ℂ)).const_sub 1).fun_pow (β + 1)
      convert h1.mul h2 using 1
      push_cast; ring
    have hQ : HasDerivAt (fun x : ℂ => (1 - w * (1 - x ^ 2)) ^ (γ + 1))
        ((γ + 1 : ℂ) * (1 - w * (1 - (s : ℂ) ^ 2)) ^ γ * (2 * w * s)) s := by
      have := (((hasDerivAt_pow 2 (s : ℂ)).const_sub 1).const_mul w |>.const_sub 1).fun_pow
        (γ + 1)
      convert this using 1
      push_cast; ring
    have h := (hN.div hQ (pow_ne_zero _ hDs)).comp_ofReal
    convert h using 1
    simp only [hF']
    obtain ⟨d, hd⟩ : ∃ d, d = 1 - w * (1 - (s : ℂ) ^ 2) := ⟨_, rfl⟩
    rw [← hd] at hDs ⊢
    field_simp
    ring_nf
  have hint : IntervalIntegrable F' volume 0 1 := by
    simp only [hF']
    exact (((asPhi_integrable hD α (β + 1) (γ + 1)).const_mul _).sub
      ((asPhi_integrable hD (α + 2) β (γ + 1)).const_mul _)).sub
      ((asPhi_integrable hD (α + 2) (β + 1) (γ + 2)).const_mul _)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  simp only [hF] at hftc
  simp at hftc
  rw [hF', intervalIntegral.integral_sub (((asPhi_integrable hD α (β + 1) (γ + 1)).const_mul _).sub
      ((asPhi_integrable hD (α + 2) β (γ + 1)).const_mul _))
      ((asPhi_integrable hD (α + 2) (β + 1) (γ + 2)).const_mul _),
    intervalIntegral.integral_sub ((asPhi_integrable hD α (β + 1) (γ + 1)).const_mul _)
      ((asPhi_integrable hD (α + 2) β (γ + 1)).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hftc
  rw [asPhi, asPhi, asPhi]
  linear_combination hftc

theorem asPhi_zero_zero_zero (w : ℂ) : asPhi 0 0 0 w = 1 := by simp [asPhi]

/-! ### The continued fraction in `w = z²` and its errors -/

/-- `a₁ = 1`, `a_{2k} = a_{2k+1} = −(2k − 1)(2k) w` (with `bᵣ = 2r − 1`). -/
noncomputable def asinWa (w : ℂ) (r : ℕ) : ℂ :=
  if r = 1 then 1 else -((((2 * (r / 2) - 1) * (2 * (r / 2)) : ℕ) : ℂ)) * w

theorem asinWa_even (w : ℂ) (k : ℕ) :
    asinWa w (2 * k + 2) = -((2 * k + 1) * (2 * k + 2)) * w := by
  have h1 : 2 * k + 2 ≠ 1 := by omega
  have h2 : (2 * k + 2) / 2 = k + 1 := by omega
  simp only [asinWa, h1, ↓reduceIte, h2]
  push_cast [show 1 ≤ 2 * (k + 1) by omega]
  ring

theorem asinWa_odd (w : ℂ) (k : ℕ) :
    asinWa w (2 * k + 3) = -((2 * k + 1) * (2 * k + 2)) * w := by
  have h1 : 2 * k + 3 ≠ 1 := by omega
  have h2 : (2 * k + 3) / 2 = k + 1 := by omega
  simp only [asinWa, h1, ↓reduceIte, h2]
  push_cast [show 1 ≤ 2 * (k + 1) by omega]
  ring

theorem lg2b_eq (w : ℂ) (r : ℕ) (hr : r ≠ 0) : lg2b w r = 2 * (r : ℂ) - 1 := by
  simp [lg2b, hr]

/-- The errors `G Bᵣ − Aᵣ` with `G = Φ(0, 0, 1)`:
`E_{2k} = (2k)! w^{2k} Φ(2k, k, k + 1)`, `E_{2k+1} = (2k + 1)! w^{2k+1} Φ(2k, k + 1, k + 1)`. -/
theorem asin_err (hD : ∀ s ∈ Icc (0 : ℝ) 1, 1 - w * (1 - (s : ℂ) ^ 2) ≠ 0) (k : ℕ) :
    asPhi 0 0 1 w * cfB (asinWa w) (lg2b w) (2 * k) - cfA (asinWa w) (lg2b w) (2 * k) =
      ((2 * k)! : ℂ) * w ^ (2 * k) * asPhi (2 * k) k (k + 1) w ∧
    asPhi 0 0 1 w * cfB (asinWa w) (lg2b w) (2 * k + 1) - cfA (asinWa w) (lg2b w) (2 * k + 1) =
      ((2 * k + 1)! : ℂ) * w ^ (2 * k + 1) * asPhi (2 * k) (k + 1) (k + 1) w := by
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp [cfA, cfB, cfP, cfQ, lg2b]
    · have h := asPhi_mul hD 0 0 0
      rw [asPhi_zero_zero_zero] at h
      simp [cfA, cfB, cfP, cfQ, lg2b, asinWa]
      linear_combination -h
  | succ k ih =>
    obtain ⟨h0, h1⟩ := ih
    have hf1 : ((2 * k + 1)! : ℂ) = (2 * k + 1) * (2 * k)! := by
      push_cast [Nat.factorial_succ]; ring
    have hf2 : ((2 * (k + 1))! : ℂ) = (2 * k + 2) * ((2 * k + 1) * (2 * k)!) := by
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring]
      push_cast [Nat.factorial_succ]; ring
    have hf3 : ((2 * k + 3)! : ℂ) = (2 * k + 3) * ((2 * k + 2) * ((2 * k + 1) * (2 * k)!)) := by
      rw [show 2 * k + 3 = 2 * k + 1 + 1 + 1 by ring]
      push_cast [Nat.factorial_succ]; ring
    have hE2 : asPhi 0 0 1 w * cfB (asinWa w) (lg2b w) (2 * (k + 1)) -
        cfA (asinWa w) (lg2b w) (2 * (k + 1)) =
        ((2 * (k + 1))! : ℂ) * w ^ (2 * (k + 1)) * asPhi (2 * (k + 1)) (k + 1) (k + 1 + 1) w := by
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, cfErr_add_two, h0, h1, asinWa_even,
        lg2b_eq w _ (by omega)]
      rw [show 2 * k + 2 = 2 * (k + 1) by ring, hf2, hf1]
      have hp := asPhi_parts hD (2 * k) k k
      have hs := asPhi_split hD (2 * k) k (k + 1)
      push_cast at hp hs ⊢
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, show k + 1 + 1 = k + 2 by ring]
      linear_combination ((2 * k + 1 : ℂ) * ((2 * k)! : ℂ) * w ^ (2 * k + 1)) * hp +
        ((2 * k + 1 : ℂ) * ((2 * k)! : ℂ) * w ^ (2 * k + 1) * (2 * k + 2)) * hs
    refine ⟨hE2, ?_⟩
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by ring, cfErr_add_two,
      show 2 * k + 1 + 1 = 2 * (k + 1) by ring, hE2, h1,
      show 2 * k + 1 + 2 = 2 * k + 3 by ring, asinWa_odd, lg2b_eq w _ (by omega), hf2, hf1,
      hf3]
    have p1 := asPhi_parts hD (2 * k) k k
    have p2 := asPhi_parts hD (2 * k + 2) k k
    have m1 := asPhi_mul hD (2 * k + 2) k (k + 1)
    have m2 := asPhi_mul hD (2 * k + 2) (k + 1) (k + 1)
    have m3 := asPhi_mul hD (2 * k + 4) k (k + 1)
    have s1 := asPhi_split hD (2 * k + 2) k (k + 2)
    rw [show 2 * k + 2 + 2 = 2 * k + 4 by ring] at p2
    rw [show k + 1 + 1 = k + 2 by ring] at m1 m2 m3 ⊢
    rw [show 2 * (k + 1) = 2 * k + 2 by ring]
    push_cast at p1 p2 ⊢
    linear_combination ((2 * k + 2 : ℂ) * ((2 * k + 1) * ((2 * k)! : ℂ)) * w ^ (2 * k + 2)) *
      (-p1 - 2 * (k + 1) * m1 - (2 * k + 3) * m2 + (2 * k + 2) * s1 + p2 + 2 * (k + 1) * m3)

/-! ### Degrees -/

theorem isPolyFunDeg_asinWa (i : ℕ) (hi : i ≠ 1) : IsPolyFunDeg (fun w => asinWa w i) 1 :=
  (IsPolyFunDeg.const_mul_id (-((((2 * (i / 2) - 1) * (2 * (i / 2)) : ℕ) : ℂ)))).congr fun w => by
    simp only [asinWa, hi, ↓reduceIte]

theorem asin_deg (i : ℕ) : IsPolyFunDeg (fun w => cfP (asinWa w) (lg2b w) i) (i / 2 - 1) ∧
    IsPolyFunDeg (fun w => cfQ (asinWa w) (lg2b w) i) ((i - 1) / 2) := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    match i with
    | 0 => exact ⟨(IsPolyFunDeg.const 1).congr fun w => rfl,
        (IsPolyFunDeg.const 0).congr fun w => rfl⟩
    | 1 => exact ⟨(IsPolyFunDeg.const 0).congr fun w => by simp [cfP, lg2b],
        (IsPolyFunDeg.const 1).congr fun w => rfl⟩
    | 2 => exact ⟨(IsPolyFunDeg.const 1).congr fun w => by simp [cfP, asinWa, lg2b],
        (IsPolyFunDeg.const 1).congr fun w => by simp [cfQ, lg2b]; norm_num⟩
    | 3 =>
      have hq : IsPolyFunDeg (fun w => (3 : ℂ) + -2 * w) 1 :=
        (IsPolyFunDeg.const 3).mono (by omega) |>.add (IsPolyFunDeg.const_mul_id (-2))
      refine ⟨(IsPolyFunDeg.const 3).congr fun w => ?_, hq.congr fun w => ?_⟩
      · simp [cfP, asinWa, lg2b]; norm_num
      · simp [cfQ, asinWa, lg2b]; norm_num
    | k + 4 =>
      obtain ⟨p2, q2⟩ := ih (k + 3) (by omega)
      obtain ⟨p1, q1⟩ := ih (k + 2) (by omega)
      have hb : IsPolyFunDeg (fun w => lg2b w (k + 3)) 0 :=
        (IsPolyFunDeg.const (2 * ((k + 3 : ℕ) : ℂ) - 1)).congr fun w => by simp [lg2b]
      have ha := isPolyFunDeg_asinWa (k + 3) (by omega)
      exact ⟨(((hb.mul p2).mono (by omega)).add ((ha.mul p1).mono (by omega))).congr
          fun w => rfl,
        (((hb.mul q2).mono (by omega)).add ((ha.mul q1).mono (by omega))).congr fun w => rfl⟩

/-! ### The weights on `(−1, 0)` -/

/-- `ω(t) = 1/(2√(1 + t))`: `∫₋₁⁰ ω(t) f(t) dt = ∫₀¹ f(s² − 1) ds`. -/
noncomputable def asinOmega (t : ℝ) : ℝ := 1 / (2 * √(1 + t))

/-- `−t ω(t)`. -/
noncomputable def asinOmega1 (t : ℝ) : ℝ := -t * asinOmega t

theorem hasDerivAt_sqrt_one_add {t : ℝ} (ht : -1 < t) :
    HasDerivAt (fun t : ℝ => √(1 + t)) (asinOmega t) t := by
  have h := ((hasDerivAt_id t).const_add 1).sqrt (by simp; linarith)
  exact h

theorem asinOmega_intervalIntegrable : IntervalIntegrable asinOmega volume (-1) 0 :=
  intervalIntegral.intervalIntegrable_deriv_of_nonneg (g := fun t : ℝ => √(1 + t))
    (by fun_prop) (fun t ht => hasDerivAt_sqrt_one_add (by
      simp only [min_eq_left (by norm_num : (-1 : ℝ) ≤ 0)] at ht; exact ht.1))
    (fun t _ => by unfold asinOmega; positivity)

theorem asinOmega_nonneg (t : ℝ) : 0 ≤ asinOmega t := by unfold asinOmega; positivity

theorem isGaussWeight_of_bounded_mul {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (-1) 0))
    (hpos : ∀ x ∈ Ioo (-1 : ℝ) 0, 0 < f x * asinOmega x) :
    IsGaussWeight (Ioo (-1 : ℝ) 0) (fun x => f x * asinOmega x) where
  isOpen := isOpen_Ioo
  ordConnected := ordConnected_Ioo
  nonempty := ⟨-1 / 2, by norm_num, by norm_num⟩
  pos := hpos
  integrableOn k := by
    have h : IntervalIntegrable (fun x => asinOmega x * (x ^ k * f x)) volume (-1) 0 :=
      asinOmega_intervalIntegrable.mul_continuousOn
        (by rw [Set.uIcc_of_le (by norm_num)]; exact (continuousOn_pow k).mul hf)
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)] at h
    exact h.congr_fun (fun x _ => by ring) measurableSet_Ioo

theorem isGaussWeight_asinOmega : IsGaussWeight (Ioo (-1 : ℝ) 0) asinOmega := by
  have := isGaussWeight_of_bounded_mul (f := fun _ => 1) continuousOn_const fun x hx => by
    simp only [one_mul, asinOmega]
    have : 0 < 1 + x := by linarith [hx.1]
    positivity
  simpa using this

theorem isGaussWeight_asinOmega1 : IsGaussWeight (Ioo (-1 : ℝ) 0) asinOmega1 :=
  isGaussWeight_of_bounded_mul (f := fun x => -x) continuous_neg.continuousOn fun x hx => by
    simp only [asinOmega]
    have : 0 < 1 + x := by linarith [hx.1]
    have : 0 < -x := by linarith [hx.2]
    positivity

/-- `∫₋₁⁰ ω(t) f(t) dt = ∫₀¹ f(s² − 1) ds`. -/
theorem integral_asinOmega (f : ℝ → ℂ) :
    ∫ t in (-1 : ℝ)..0, (asinOmega t : ℂ) * f t = ∫ s in (0 : ℝ)..1, f (s ^ 2 - 1) := by
  have h := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg (a := 0) (b := 1)
    (f := fun s : ℝ => s ^ 2 - 1) (f' := fun s => 2 * s)
    (g := fun t => (asinOmega t : ℂ) * f t) (by fun_prop)
    (fun s _ => by simpa using (hasDerivAt_pow 2 s).sub_const 1)
    (fun s hs => by simp only [min_eq_left zero_le_one] at hs; linarith [hs.1])
  simp only [Function.comp, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    zero_sub, one_pow, sub_self] at h
  rw [← h]
  refine intervalIntegral.integral_congr_ae ?_
  refine Eventually.of_forall fun s hs => ?_
  rw [uIoc_of_le zero_le_one] at hs
  have hs0 : 0 < s := hs.1
  simp only [asinOmega, show 1 + (s ^ 2 - 1) = s ^ 2 by ring, Real.sqrt_sq hs0.le, real_smul]
  push_cast
  have : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  field_simp

/-! ### Identification with Gauss quadrature -/

theorem asinD_eq (w : ℂ) (s : ℝ) : 1 - w * (1 - (s : ℂ) ^ 2) = 1 + w * ((s ^ 2 - 1 : ℝ) : ℂ) := by
  push_cast; ring

/-- `1 − w(1 − s²) ≠ 0` on `[0, 1]` iff `1 + w t ≠ 0` on `[−1, 0]`. -/
theorem asin_noPole_iff :
    (∀ s ∈ Icc (0 : ℝ) 1, 1 - w * (1 - (s : ℂ) ^ 2) ≠ 0) ↔ ∀ t ∈ Icc (-1 : ℝ) 0, 1 + w * t ≠ 0 := by
  constructor
  · intro h t ht
    have h0 : 0 ≤ 1 + t := by linarith [ht.1]
    have hs := h (√(1 + t)) ⟨Real.sqrt_nonneg _, by
      rw [Real.sqrt_le_one]; linarith [ht.2]⟩
    rwa [asinD_eq, Real.sq_sqrt h0, show 1 + t - 1 = t by ring] at hs
  · intro h s hs
    rw [asinD_eq]
    exact h _ ⟨by nlinarith [hs.1], by nlinarith [hs.1, hs.2]⟩

theorem asin_noPole_small (hw : ‖w‖ ≤ 1 / 2) :
    ∀ s ∈ Icc (0 : ℝ) 1, 1 - w * (1 - (s : ℂ) ^ 2) ≠ 0 :=
  asin_noPole_iff.mpr (noPole_small le_rfl (by norm_num) hw)

theorem asPhi_bound (α β γ : ℕ) : ∃ C, ∀ w : ℂ, ‖w‖ ≤ 1 / 2 → ‖asPhi α β γ w‖ ≤ C := by
  refine ⟨2 ^ γ, fun w hw => ?_⟩
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := 2 ^ γ)
    (f := fun s : ℝ => (s : ℂ) ^ α * (1 - (s : ℂ) ^ 2) ^ β / (1 - w * (1 - (s : ℂ) ^ 2)) ^ γ)
    fun s hs => by
      rw [uIoc_of_le zero_le_one] at hs
      have hs0 := hs.1.le
      have hs1 := hs.2
      have hD : 1 / 2 ≤ ‖1 - w * (1 - (s : ℂ) ^ 2)‖ := by
        rw [asinD_eq]
        exact norm_one_add_mul_ge hw (abs_le.mpr ⟨by nlinarith, by nlinarith⟩)
      have hpos : 0 < ‖1 - w * (1 - (s : ℂ) ^ 2)‖ := by linarith
      rw [norm_div, norm_mul, norm_pow, norm_pow, norm_pow, div_le_iff₀ (pow_pos hpos _)]
      have h1 : ‖(s : ℂ)‖ ^ α ≤ 1 := by
        rw [norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]; exact pow_le_one₀ hs0 hs1
      have h2 : ‖1 - (s : ℂ) ^ 2‖ ^ β ≤ 1 := by
        rw [show (1 : ℂ) - (s : ℂ) ^ 2 = ((1 - s ^ 2 : ℝ) : ℂ) by push_cast; ring, norm_real,
          Real.norm_eq_abs, abs_of_nonneg (by nlinarith)]
        exact pow_le_one₀ (by nlinarith) (by nlinarith)
      have h3 : (1 / 2 : ℝ) ^ γ ≤ ‖1 - w * (1 - (s : ℂ) ^ 2)‖ ^ γ :=
        pow_le_pow_left₀ (by norm_num) hD γ
      calc ‖(s : ℂ)‖ ^ α * ‖1 - (s : ℂ) ^ 2‖ ^ β ≤ 1 * 1 :=
            mul_le_mul h1 h2 (by positivity) zero_le_one
        _ = 2 ^ γ * (1 / 2) ^ γ := by rw [← mul_pow]; norm_num
        _ ≤ 2 ^ γ * ‖1 - w * (1 - (s : ℂ) ^ 2)‖ ^ γ := by gcongr
  simpa [asPhi] using h

theorem asin_integral_omega (w : ℂ) :
    ∫ x in (-1 : ℝ)..0, (asinOmega x : ℂ) / (1 + w * x) = asPhi 0 0 1 w := by
  rw [show (fun x : ℝ => (asinOmega x : ℂ) / (1 + w * x)) =
    fun x => (asinOmega x : ℂ) * (1 / (1 + w * x)) from funext fun x => by ring,
    integral_asinOmega]
  simp only [asPhi, pow_zero, one_mul, pow_one]
  congr 1; funext s; rw [asinD_eq]

theorem asin_integral_omega1 (w : ℂ) :
    ∫ x in (-1 : ℝ)..0, (asinOmega1 x : ℂ) / (1 + w * x) = asPhi 0 1 1 w := by
  rw [show (fun x : ℝ => (asinOmega1 x : ℂ) / (1 + w * x)) =
    fun x => (asinOmega x : ℂ) * (-(x : ℂ) / (1 + w * x)) from funext fun x => by
      simp only [asinOmega1]; push_cast; ring,
    integral_asinOmega]
  simp only [asPhi, pow_zero, one_mul, pow_one]
  congr 1; funext s; rw [asinD_eq]; push_cast; ring

noncomputable def gQ0 (n : ℕ) : ℝ[X] := (exists_isOrthMonic isGaussWeight_asinOmega n).choose

theorem gQ0_spec (n : ℕ) : IsOrthMonic (Ioo (-1) 0) asinOmega n (gQ0 n) :=
  (exists_isOrthMonic isGaussWeight_asinOmega n).choose_spec

noncomputable def gQ1 (n : ℕ) : ℝ[X] := (exists_isOrthMonic isGaussWeight_asinOmega1 n).choose

theorem gQ1_spec (n : ℕ) : IsOrthMonic (Ioo (-1) 0) asinOmega1 n (gQ1 n) :=
  (exists_isOrthMonic isGaussWeight_asinOmega1 n).choose_spec

theorem asinOmega1_nonneg (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 0) : 0 ≤ asinOmega1 x :=
  mul_nonneg (by linarith [hx.2]) (asinOmega_nonneg x)

/-- The even convergents are the Gauss rules for the weight `ω` on `(−1, 0)`. -/
theorem asin_even_eq {n : ℕ} (hn : 1 ≤ n) (w : ℂ) :
    cfA (asinWa w) (lg2b w) (2 * n) * gaussB (gQ0 n) w =
      gaussA (-1) 0 asinOmega (gQ0 n) w * cfB (asinWa w) (lg2b w) (2 * n) := by
  have hcard := gauss_card isGaussWeight_asinOmega (gQ0_spec n)
  refine pade_unique (A := fun w => cfA (asinWa w) (lg2b w) (2 * n))
    (B := fun w => cfB (asinWa w) (lg2b w) (2 * n)) (A' := gaussA (-1) 0 asinOmega (gQ0 n))
    (B' := gaussB (gQ0 n)) (L := asPhi 0 0 1) (d := 2 * n - 1) (N := 2 * n) ?_ (by omega)
    (asin_deg (2 * n + 1)).2.continuous (isPolyFunDeg_gaussB _).continuous ?_ ?_ w
  · have hA := (asin_deg (2 * n + 1)).1
    have hB := (asin_deg (2 * n + 1)).2
    have hB' := isPolyFunDeg_gaussB (gQ0 n)
    have hA' := isPolyFunDeg_gaussA (-1) 0 asinOmega (gQ0 n)
    rw [hcard] at hB' hA'
    exact ((hA.mul hB').mono (by omega)).sub ((hA'.mul hB).mono (by omega))
  · obtain ⟨C, hC⟩ := asPhi_bound (2 * n) n (n + 1)
    obtain ⟨δ, hδ, C', hC'⟩ := bigO_of_formula (ψ := asPhi (2 * n) n (n + 1))
      (E := fun w => asPhi 0 0 1 w * cfB (asinWa w) (lg2b w) (2 * n) -
        cfA (asinWa w) (lg2b w) (2 * n)) (κ := ((2 * n)! : ℂ)) (N := 2 * n) ⟨C, hC⟩
      fun w hw => (asin_err (asin_noPole_small hw.le) n).1
    exact ⟨δ, hδ, C', fun w hw => by rw [mul_comm]; exact hC' w hw⟩
  · obtain ⟨C, hC⟩ := gauss_err_bound_of_weight isGaussWeight_asinOmega (by norm_num) le_rfl
      (by norm_num) (fun x _ => asinOmega_nonneg x) (gQ0_spec n)
    refine ⟨1 / 2, by norm_num, C, fun w hw => ?_⟩
    have h := hC w hw.le
    rwa [asin_integral_omega] at h

/-- The odd convergents are `1 + w ×` the Gauss rules for the weight `−t ω` on `(−1, 0)`. -/
theorem asin_odd_eq {n : ℕ} (hn : 1 ≤ n) (w : ℂ) :
    cfA (asinWa w) (lg2b w) (2 * n + 1) * gaussB (gQ1 n) w =
      (gaussB (gQ1 n) w + w * gaussA (-1) 0 asinOmega1 (gQ1 n) w) *
        cfB (asinWa w) (lg2b w) (2 * n + 1) := by
  have hcard := gauss_card isGaussWeight_asinOmega1 (gQ1_spec n)
  refine pade_unique (A := fun w => cfA (asinWa w) (lg2b w) (2 * n + 1))
    (B := fun w => cfB (asinWa w) (lg2b w) (2 * n + 1))
    (A' := fun w => gaussB (gQ1 n) w + w * gaussA (-1) 0 asinOmega1 (gQ1 n) w)
    (B' := gaussB (gQ1 n)) (L := asPhi 0 0 1) (d := 2 * n) (N := 2 * n + 1) ?_ (by omega)
    (asin_deg (2 * n + 2)).2.continuous (isPolyFunDeg_gaussB _).continuous ?_ ?_ w
  · have hA := (asin_deg (2 * n + 2)).1
    have hB := (asin_deg (2 * n + 2)).2
    have hB' := isPolyFunDeg_gaussB (gQ1 n)
    have hA2 := IsPolyFunDeg.id.mul (isPolyFunDeg_gaussA (-1) 0 asinOmega1 (gQ1 n))
    rw [hcard] at hB' hA2
    have hA' : IsPolyFunDeg (fun w => gaussB (gQ1 n) w + w * gaussA (-1) 0 asinOmega1 (gQ1 n) w)
        n := hB'.add (hA2.mono (by omega))
    exact ((hA.mul hB').mono (by omega)).sub ((hA'.mul hB).mono (by omega))
  · obtain ⟨C, hC⟩ := asPhi_bound (2 * n) (n + 1) (n + 1)
    obtain ⟨δ, hδ, C', hC'⟩ := bigO_of_formula (ψ := asPhi (2 * n) (n + 1) (n + 1))
      (E := fun w => asPhi 0 0 1 w * cfB (asinWa w) (lg2b w) (2 * n + 1) -
        cfA (asinWa w) (lg2b w) (2 * n + 1)) (κ := ((2 * n + 1)! : ℂ)) (N := 2 * n + 1)
      ⟨C, hC⟩ fun w hw => (asin_err (asin_noPole_small hw.le) n).2
    exact ⟨δ, hδ, C', fun w hw => by rw [mul_comm]; exact hC' w hw⟩
  · obtain ⟨C, hC⟩ := gauss_err_bound_of_weight isGaussWeight_asinOmega1 (by norm_num) le_rfl
      (by norm_num) asinOmega1_nonneg (gQ1_spec n)
    refine ⟨1 / 2, by norm_num, C, fun w hw => ?_⟩
    have h := hC w hw.le
    rw [asin_integral_omega1] at h
    have hm := asPhi_mul (asin_noPole_small hw.le) 0 0 0
    rw [asPhi_zero_zero_zero] at hm
    simp only [zero_add] at hm
    have hL : gaussB (gQ1 n) w * asPhi 0 0 1 w -
        (gaussB (gQ1 n) w + w * gaussA (-1) 0 asinOmega1 (gQ1 n) w) =
        w * (gaussB (gQ1 n) w * asPhi 0 1 1 w - gaussA (-1) 0 asinOmega1 (gQ1 n) w) := by
      linear_combination (-gaussB (gQ1 n) w) * hm
    rw [hL, norm_mul]
    calc ‖w‖ * ‖gaussB (gQ1 n) w * asPhi 0 1 1 w - gaussA (-1) 0 asinOmega1 (gQ1 n) w‖
        ≤ ‖w‖ * (C * ‖w‖ ^ (2 * n)) := by gcongr
      _ = C * ‖w‖ ^ (2 * n + 1) := by ring

/-! ### Nonvanishing denominators and the limit in `w` -/

theorem cfQ_of_a_zero_two {a' b' : ℕ → ℂ} (ha : ∀ k ≥ 2, a' k = 0) (r : ℕ) :
    cfQ a' b' (r + 1) = ∏ k ∈ Finset.Icc 1 r, b' k := by
  induction r with
  | zero => simp [cfQ]
  | succ r ih =>
    show b' (r + 1) * cfQ a' b' (r + 1) + a' (r + 1) * cfQ a' b' r = _
    rw [ih, prod_Icc_succ_top (by omega)]
    rcases r with _ | r
    · simp [cfQ]
    · rw [ha (r + 2) (by omega)]; ring

theorem asin_det (w : ℂ) (r : ℕ) :
    cfA (asinWa w) (lg2b w) r = 0 → cfB (asinWa w) (lg2b w) r = 0 → False := by
  intro hA hB
  by_cases hw0 : w = 0
  · subst hw0
    rw [cfB, cfQ_of_a_zero_two (fun k hk => by
      have : k ≠ 1 := by omega
      simp [asinWa, this])] at hB
    obtain ⟨k, hk, hk0⟩ := prod_eq_zero_iff.mp hB
    have hk1 := (Finset.mem_Icc.mp hk).1
    simp only [lg2b, show k ≠ 0 by omega, ↓reduceIte] at hk0
    have : ((2 * k - 1 : ℕ) : ℂ) = 0 := by push_cast [show 1 ≤ 2 * k by omega]; exact hk0
    exact absurd (Nat.cast_eq_zero.mp this) (by omega)
  · obtain ⟨k, hk, hk0⟩ := exists_a_zero_of_cf_zero hA hB
    have hk1 := (Finset.mem_Icc.mp hk).1
    by_cases h1 : k = 1
    · simp [asinWa, h1] at hk0
    · simp only [asinWa, h1, ↓reduceIte, neg_mul, neg_eq_zero, mul_eq_zero, hw0, or_false,
        Nat.cast_eq_zero] at hk0
      have : 1 ≤ k / 2 := by omega
      omega

theorem asin_tendsto (hz : ∀ t ∈ Icc (-1 : ℝ) 0, 1 + w * t ≠ 0) :
    (∀ᶠ r in atTop, cfB (asinWa w) (lg2b w) r ≠ 0) ∧
      Tendsto (fun r => cfA (asinWa w) (lg2b w) r / cfB (asinWa w) (lg2b w) r) atTop
        (𝓝 (asPhi 0 0 1 w)) := by
  have hev : ∀ n, 1 ≤ n → cfB (asinWa w) (lg2b w) (2 * n) ≠ 0 ∧
      cfA (asinWa w) (lg2b w) (2 * n) / cfB (asinWa w) (lg2b w) (2 * n) =
        gaussQuad (-1) 0 asinOmega (gQ0 n) (fun t => 1 / (1 + w * t)) := fun n hn => by
    have hne := gauss_ne_zero_of_noPole isGaussWeight_asinOmega (gQ0_spec n) hz
    obtain ⟨hB, hq⟩ := div_eq_of_cross (asin_even_eq hn w) (gaussB_ne_zero hne) (asin_det w _)
    refine ⟨hB, ?_⟩
    rw [hq, gaussA_eq hne]; field_simp [gaussB_ne_zero hne]
  have hod : ∀ n, 1 ≤ n → cfB (asinWa w) (lg2b w) (2 * n + 1) ≠ 0 ∧
      cfA (asinWa w) (lg2b w) (2 * n + 1) / cfB (asinWa w) (lg2b w) (2 * n + 1) =
        1 + w * gaussQuad (-1) 0 asinOmega1 (gQ1 n) (fun t => 1 / (1 + w * t)) :=
      fun n hn => by
    have hne := gauss_ne_zero_of_noPole isGaussWeight_asinOmega1 (gQ1_spec n) hz
    obtain ⟨hB, hq⟩ := div_eq_of_cross (asin_odd_eq hn w) (gaussB_ne_zero hne) (asin_det w _)
    refine ⟨hB, ?_⟩
    rw [hq, gaussA_eq hne]; field_simp [gaussB_ne_zero hne]
  have hg := continuousOn_inv_one_add hz
  have hT1 := gauss_tendsto_of_weight isGaussWeight_asinOmega (by norm_num)
    (fun x _ => asinOmega_nonneg x) gQ0_spec hg
  have hT2 := gauss_tendsto_of_weight isGaussWeight_asinOmega1 (by norm_num)
    asinOmega1_nonneg gQ1_spec hg
  have hI1 : (∫ x in (-1 : ℝ)..0, (asinOmega x : ℂ) * (1 / (1 + w * x))) = asPhi 0 0 1 w := by
    rw [← asin_integral_omega]; congr 1; funext x; ring
  have hI2 : (∫ x in (-1 : ℝ)..0, (asinOmega1 x : ℂ) * (1 / (1 + w * x))) = asPhi 0 1 1 w := by
    rw [← asin_integral_omega1]; congr 1; funext x; ring
  rw [hI1] at hT1
  rw [hI2] at hT2
  have hm := asPhi_mul (asin_noPole_iff.mpr hz) 0 0 0
  rw [asPhi_zero_zero_zero] at hm
  simp only [zero_add] at hm
  refine ⟨eventually_atTop.2 ⟨2, fun r hr => ?_⟩, tendsto_of_even_odd ?_ ?_⟩
  · rcases Nat.even_or_odd' r with ⟨n, rfl | rfl⟩
    · exact (hev n (by omega)).1
    · exact (hod n (by omega)).1
  · exact Tendsto.congr' (eventually_atTop.2 ⟨1, fun n hn => (hev n hn).2.symm⟩) hT1
  · refine Tendsto.congr' (eventually_atTop.2 ⟨1, fun n hn => (hod n hn).2.symm⟩) ?_
    have := tendsto_const_nhds (x := (1 : ℂ)) |>.add (hT2.const_mul w)
    convert this using 2
    linear_combination -hm

/-! ### 4.25.3 -/

/-- The partial numerators of 4.25.3: `a₁ = z`, `a_{2k} = a_{2k+1} = −(2k − 1)(2k) z²`. -/
noncomputable def asinCFa (z : ℂ) (r : ℕ) : ℂ :=
  if r = 1 then z else -((((2 * (r / 2) - 1) * (2 * (r / 2)) : ℕ) : ℂ)) * z ^ 2

/-- If `z²` is real and `≥ 1` then `z` lies on the cuts of `arcsin`. -/
theorem not_mem_arcsinCut_of_sq {z : ℂ} {x : ℝ} (hx : 1 ≤ x) (h : z ^ 2 = x) :
    z ∉ arcsinCut := by
  have h1 := congrArg re h
  have h2 := congrArg im h
  simp only [sq, mul_re, mul_im, ofReal_re, ofReal_im] at h1 h2
  intro hz
  rcases hz with hz | hz
  · have hx0 : z.re = 0 := by
      have : z.re * z.im = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h hz
    rw [hx0] at h1
    nlinarith [sq_nonneg z.im]
  · have := abs_lt.mp hz
    nlinarith [sq_nonneg z.im]

/-- `1 − z²(1 − s²) ≠ 0` for `s ∈ [0, 1]` and `z` off the cuts of `arcsin`. -/
theorem asin_noPole_of_mem {z : ℂ} (hz : z ∈ arcsinCut) :
    ∀ s ∈ Icc (0 : ℝ) 1, 1 - z ^ 2 * (1 - (s : ℂ) ^ 2) ≠ 0 := by
  intro s hs h
  have hs1 : s ^ 2 < 1 := by
    rcases hs.2.lt_or_eq with h' | h'
    · nlinarith [hs.1]
    · rw [h'] at h; norm_num at h
  have hne : (1 - (s : ℂ) ^ 2) ≠ 0 := by
    rw [show (1 : ℂ) - (s : ℂ) ^ 2 = ((1 - s ^ 2 : ℝ) : ℂ) by push_cast; ring]
    exact_mod_cast (by linarith : (1 - s ^ 2 : ℝ) ≠ 0)
  have hz2 : z ^ 2 = ((1 / (1 - s ^ 2) : ℝ) : ℂ) := by
    push_cast
    rw [eq_div_iff hne]
    linear_combination -h
  exact not_mem_arcsinCut_of_sq (by rw [le_div_iff₀ (by linarith)]; nlinarith) hz2 hz

/-- `z/(1 − z²)^{1/2}` (`= tan arcsin z`) lies off the cuts of `arctan`. -/
theorem div_sqrt_mem_arctanCut {z : ℂ} (hz : z ∈ arcsinCut) :
    z / (1 - z ^ 2) ^ (1 / 2 : ℂ) ∈ arctanCut := by
  set q := (1 - z ^ 2) ^ (1 / 2 : ℂ) with hq
  have hq2 : q ^ 2 = 1 - z ^ 2 := by rw [hq, one_div (2 : ℂ), cpow_ofNat_inv_pow]
  have hqre : 0 < q.re := re_cpow_half_pos_of_mem_slitPlane (by
    simpa using one_sub_sq_mem_slitPlane hz (s := 1) ⟨zero_le_one, le_rfl⟩)
  have hq0 : q ≠ 0 := fun h => by rw [h, zero_re] at hqre; exact lt_irrefl _ hqre
  by_contra hc
  rw [arctanCut, mem_ofPred_eq] at hc
  push Not at hc
  obtain ⟨hre, him⟩ := hc
  set y := (z / q).im
  have hc' : z / q = I * y := Complex.ext (by simp [hre]) (by simp [y])
  have hz' : z = I * y * q := by rw [← hc']; field_simp
  have hz2 : z ^ 2 = -(y : ℂ) ^ 2 * q ^ 2 := by
    rw [hz', mul_pow, mul_pow, I_sq]; ring
  have hrel : z ^ 2 * (1 - (y : ℂ) ^ 2) = -(y : ℂ) ^ 2 := by
    linear_combination hz2 - (y : ℂ) ^ 2 * hq2
  have hy2 : 1 ≤ y ^ 2 := one_le_sq_iff_one_le_abs _ |>.mpr him
  rcases hy2.lt_or_eq with hy | hy
  · have hne : ((y : ℂ) ^ 2 - 1) ≠ 0 := by
      rw [show (y : ℂ) ^ 2 - 1 = ((y ^ 2 - 1 : ℝ) : ℂ) by push_cast; ring]
      exact_mod_cast (by linarith : (y ^ 2 - 1 : ℝ) ≠ 0)
    have hz2' : z ^ 2 = ((y ^ 2 / (y ^ 2 - 1) : ℝ) : ℂ) := by
      push_cast
      rw [eq_div_iff hne]
      linear_combination -hrel
    exact not_mem_arcsinCut_of_sq (by rw [le_div_iff₀ (by linarith)]; linarith) hz2' hz
  · have : ((y : ℂ) ^ 2) = 1 := by exact_mod_cast hy.symm
    rw [this] at hrel
    norm_num at hrel

/-- `z ∫₀¹ ds/(1 − z²(1 − s²)) = arcsin z/(1 − z²)^{1/2}`. -/
theorem asin_value {z : ℂ} (hz : z ∈ arcsinCut) :
    z * asPhi 0 0 1 (z ^ 2) = arcsinD z / (1 - z ^ 2) ^ (1 / 2 : ℂ) := by
  set q := (1 - z ^ 2) ^ (1 / 2 : ℂ) with hq
  have hq2 : q ^ 2 = 1 - z ^ 2 := by rw [hq, one_div (2 : ℂ), cpow_ofNat_inv_pow]
  have hqre : 0 < q.re := re_cpow_half_pos_of_mem_slitPlane (by
    simpa using one_sub_sq_mem_slitPlane hz (s := 1) ⟨zero_le_one, le_rfl⟩)
  have hq0 : q ≠ 0 := fun h => by rw [h, zero_re] at hqre; exact lt_irrefl _ hqre
  obtain ⟨-, hvs, hsin, hcos⟩ := arcsinD_props hz
  set v := arcsinD z
  have htan : tan v = z / q := by rw [tan_eq_sin_div_cos, hsin, hcos]
  have harc : arctanD (z / q) = v := by
    rw [arctanD_eq (div_sqrt_mem_arctanCut hz), ← htan]
    refine arctan_tan (fun h => ?_) hvs.1 hvs.2.le
    have := hvs.2; rw [h] at this; simp at this
  have hD := asin_noPole_of_mem hz
  rw [← harc, arctanD, asPhi, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_div]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [Set.uIcc_of_le zero_le_one] at hs
  have h1 := hD s hs
  have hkey : 1 + ((s : ℂ) * (z / q)) ^ 2 = (1 - z ^ 2 * (1 - (s : ℂ) ^ 2)) / q ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hq0), add_mul, mul_pow, div_pow, mul_assoc,
      div_mul_cancel₀ _ (pow_ne_zero 2 hq0), hq2]
    ring
  simp only [pow_zero, one_mul, pow_one]
  rw [hkey]
  field_simp

theorem asin_cf_eq (z : ℂ) (r : ℕ) :
    cfA (asinCFa z) (lg2b z) r = z * cfA (asinWa (z ^ 2)) (lg2b (z ^ 2)) r ∧
      cfB (asinCFa z) (lg2b z) r = cfB (asinWa (z ^ 2)) (lg2b (z ^ 2)) r := by
  have hb : lg2b (z ^ 2) = lg2b z := rfl
  have hagree : ∀ r ≥ 2, asinCFa z r = asinWa (z ^ 2) r := by
    intro r hr
    have : r ≠ 1 := by omega
    simp [asinCFa, asinWa, this]
  have h1 : asinCFa z 1 = z * asinWa (z ^ 2) 1 := by simp [asinCFa, asinWa]
  rw [hb]
  exact ⟨cfP_scale_first z (by simp [lg2b]) h1 hagree r, cfQ_change_first hagree (r + 1)⟩

/-- **DLMF 4.25.3**: `arcsin z/(1 − z²)^{1/2} = z/(1 − 1·2z²/(3 − 1·2z²/(5 − 3·4z²/(7 −
3·4z²/(9 − ⋯)))))` for `z` in the open cut plane of Figure 4.23.1(i). The even convergents are
Gauss rules for `ω(t) = 1/(2√(1 + t))` on `(−1, 0)` (`asin_even_eq`), the odd ones `1 + w ×`
Gauss rules for `−t ω(t)` (`asin_odd_eq`), `w = z²`. -/
theorem dlmf_4_25_3 {z : ℂ} (hz : z ∈ arcsinCut) :
    (∀ᶠ r in atTop, cfB (asinCFa z) (lg2b z) r ≠ 0) ∧
      Tendsto (fun r => cfA (asinCFa z) (lg2b z) r / cfB (asinCFa z) (lg2b z) r) atTop
        (𝓝 (arcsinD z / (1 - z ^ 2) ^ (1 / 2 : ℂ))) := by
  have hD : ∀ t ∈ Icc (-1 : ℝ) 0, 1 + z ^ 2 * t ≠ 0 :=
    asin_noPole_iff.mp (asin_noPole_of_mem hz)
  obtain ⟨hB, hT⟩ := asin_tendsto hD
  refine ⟨hB.mono fun r hr => by rwa [(asin_cf_eq z r).2], ?_⟩
  rw [← asin_value hz]
  refine (hT.const_mul z).congr fun r => ?_
  rw [(asin_cf_eq z r).1, (asin_cf_eq z r).2, mul_div_assoc]

end Azurite.DLMF
