/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section16Derivatives

/-!
# DLMF §1.16(iv): The Heaviside function

https://dlmf.nist.gov/1.16.iv

* 1.16.13–1.16.16: `heavisideH` (with `H(0) = 0`), `DH(x − x₀) = δ_{x₀}` (`dlmf_1_16_16`).
  `δ_{x₀}` is the Lebesgue–Stieltjes measure of `α(x) = H(x − x₀)` (`diracDist_eq_stieltjesDist`).
  Mathlib's measure of a monotone function uses its right-continuous version, which is the
  `heaviside x₀` of §1.4(v). So 1.16.16 is also a case of 1.16.3_5 and 1.16.9_5
  (`dlmf_1_16_16_stieltjes`).
* 1.16.17–1.16.18: for `f` infinitely differentiable except at `x₀`, where it is given on each side
  by a smooth function (`IsPiecewiseSmooth`), the jumps `σₙ = f⁽ⁿ⁾(x₀+) − f⁽ⁿ⁾(x₀−)` (`jump`,
  `IsPiecewiseSmooth.tendsto_iteratedDeriv`). `Dᵐf = f⁽ᵐ⁾ + ∑ σₖ δ_{x₀}⁽ᵐ⁻¹⁻ᵏ⁾` (`dlmf_1_16_18`)
  follows by induction from the case `m = 1` (`distDeriv_piecewise`), which is integration by
  parts on the two half-lines.
* 1.16.19–1.16.20: `x₊^α` (`posPow`, `α > −1`) and `D x₊^α = α x₊^{α−1}` for `α > 0`.
* 1.16.21: `x₊^α = Dⁿ x₊^{α+n}/(α + 1)ₙ` for non-integer `α < −1` (`posPowDist`). It is
  independent of `n` (`posPowDist_indep`), agrees with the regular `x₊^α` for `α > −1`, and obeys
  the power rule (`derivDist_posPowDist`).
* 1.16.22–1.16.23: `ln₊ x` (`lnPos`) and `x₊^{−1−n} = D^{n+1} ln₊ x/((−1)ⁿ n!)` (`negPowDist`). It
  obeys the power rule (`derivDist_negPowDist`), and `x₊^{−1}` acts as `1/x` on test functions
  supported in `(0, ∞)` (`negPowDist_zero_apply_of_pos`).
-/

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace Azurite.DLMF

variable {I : Set ℝ}

/-! ### `H` and `DH = δ` (1.16.13–1.16.16) -/

/-- DLMF 1.16.13: the Heaviside function `H(x) = 1` for `x > 0`, `0` for `x ≤ 0`. -/
noncomputable def heavisideH (x : ℝ) : ℝ := if 0 < x then 1 else 0

/-- DLMF 1.16.14: `H(x − x₀) = 1` for `x > x₀`, `0` for `x ≤ x₀`. -/
theorem dlmf_1_16_14 (x₀ x : ℝ) : heavisideH (x - x₀) = if x₀ < x then 1 else 0 := by
  simp [heavisideH]

theorem heaviside_shift_eq_indicator (x₀ : ℝ) :
    (fun x => (heavisideH (x - x₀) : ℂ)) = (Ioi x₀).indicator fun _ => 1 := by
  funext x
  rw [dlmf_1_16_14]
  by_cases h : x₀ < x <;> simp [h, indicator]

theorem locallyIntegrableOn_heaviside (x₀ : ℝ) (I : Set ℝ) :
    LocallyIntegrableOn (fun x => (heavisideH (x - x₀) : ℂ)) I := by
  rw [heaviside_shift_eq_indicator]
  exact ((locallyIntegrable_const (1 : ℂ)).indicator measurableSet_Ioi).locallyIntegrableOn I

/-- `∫ φ' = −φ(x₀)` over `(x₀, ∞)` for a test function `φ`. -/
theorem integral_Ioi_deriv_testFunction {φ : ℝ → ℂ} (hφ : IsTestFunction I φ) (x₀ : ℝ) :
    ∫ x in Ioi x₀, deriv φ x = -φ x₀ := by
  obtain ⟨R₀, -, hR₀⟩ := exists_Ioo_superset_tsupport hφ.2.1
  obtain ⟨R₁, -, hR₁⟩ := exists_Ioo_superset_tsupport hφ.2.1.deriv
  set R := max (max R₀ R₁) (x₀ + 1)
  have h0 := le_max_left (max R₀ R₁) (x₀ + 1)
  have h1 := le_max_left R₀ R₁
  have h2 := le_max_right R₀ R₁
  have h3 := le_max_right (max R₀ R₁) (x₀ + 1)
  have hd : ContDiff ℝ 1 φ := hφ.1.of_le (by exact_mod_cast le_top)
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (s := Ioc x₀ R) measurableSet_Ioi
    Ioc_subset_Ioi_self fun x hx => hR₁ x fun h => hx.2 ⟨hx.1, by linarith [h.2]⟩,
    ← intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => (hd.differentiable one_ne_zero x).hasDerivAt)
      ((hd.continuous_deriv le_rfl).intervalIntegrable _ _),
    hR₀ R fun h => by linarith [h.2]]
  ring

/-- DLMF 1.16.16: `D H(x − x₀) = δ_{x₀}`. -/
theorem dlmf_1_16_16 (hI : IsOpen I) (x₀ : ℝ) :
    distDeriv hI (locallyIntegrableOn_heaviside x₀ I) = diracDist I x₀ := by
  ext φ
  rw [distDeriv_apply, dlmf_1_16_11,
    setIntegral_eq_integral_of_forall_compl_eq_zero (s := I) fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport fun h => hx (φ.2.2.2 (tsupport_deriv_subset h)),
        mul_zero]]
  have e : (fun x => (heavisideH (x - x₀) : ℂ) * deriv (φ : ℝ → ℂ) x) =
      (Ioi x₀).indicator (deriv (φ : ℝ → ℂ)) := funext fun x => by
    rw [dlmf_1_16_14]
    by_cases h : x₀ < x <;> simp [h, indicator]
  rw [e, integral_indicator measurableSet_Ioi, integral_Ioi_deriv_testFunction φ.2, neg_neg]

/-- DLMF 1.16.15: `DH = δ`. -/
theorem dlmf_1_16_15 (hI : IsOpen I) :
    distDeriv hI (locallyIntegrableOn_heaviside 0 I) = diracDist I 0 :=
  dlmf_1_16_16 hI 0

/-! ### `δ_{x₀}` as the Lebesgue–Stieltjes measure of `H(x − x₀)` -/

theorem monotone_heavisideH_shift (x₀ : ℝ) : Monotone fun x => heavisideH (x - x₀) := by
  intro x y hxy
  simp only [dlmf_1_16_14]
  by_cases h1 : x₀ < x
  · simp [h1, h1.trans_le hxy]
  · by_cases h2 : x₀ < y <;> simp [h1, h2]

/-- The Lebesgue–Stieltjes measure of the monotone `α(x) = H(x − x₀)` is that of its
right-continuous version, which is the Stieltjes function `heaviside x₀` of §1.4(v)
(`1_{x ≥ x₀}`). -/
theorem stieltjesFunction_heavisideH (x₀ : ℝ) :
    (monotone_heavisideH_shift x₀).stieltjesFunction = heaviside x₀ := by
  ext x
  rw [heaviside_apply]
  show Function.rightLim (fun x => heavisideH (x - x₀)) x = _
  split_ifs with h
  · refine rightLim_eq_of_tendsto (tendsto_const_nhds.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with y (hy : x < y)
    rw [dlmf_1_16_14, ite_eq_left (h.trans_lt hy)]
  · refine rightLim_eq_of_tendsto (tendsto_const_nhds.congr' ?_)
    filter_upwards [Ioo_mem_nhdsGT (not_le.mp h)] with y hy
    rw [dlmf_1_16_14, ite_eq_right (not_lt.mpr hy.2.le)]

/-- DLMF §1.16(iv): `δ_{x₀}` is the Lebesgue–Stieltjes measure `μ_α` of `α(x) = H(x − x₀)`. -/
theorem diracDist_eq_stieltjesDist (hI : IsOpen I) (x₀ : ℝ) :
    stieltjesDist hI ((monotone_heavisideH_shift x₀).stieltjesFunction) = diracDist I x₀ := by
  ext φ
  rw [dlmf_1_16_3_5, stieltjesFunction_heavisideH, heaviside_measure,
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
      image_eq_zero_of_notMem_tsupport fun h => hx (φ.2.2.2 h),
    integral_dirac, dlmf_1_16_11]

/-- 1.16.16 as the special case `α(x) = H(x − x₀)` of 1.16.3_5 and 1.16.9_5. -/
theorem dlmf_1_16_16_stieltjes (hI : IsOpen I) (x₀ : ℝ) :
    distDeriv hI
      (locallyIntegrableOn_stieltjes ((monotone_heavisideH_shift x₀).stieltjesFunction) I) =
      diracDist I x₀ := by
  rw [← dlmf_1_16_9_5, diracDist_eq_stieltjesDist]

/-! ### Jumps (1.16.17–1.16.18) -/

/-- `f` is infinitely differentiable except at `x₀`, with one-sided derivatives of all orders
there: `f = gl` on `x < x₀` and `f = gr` on `x > x₀` for smooth `gl`, `gr`. -/
def IsPiecewiseSmooth (f gl gr : ℝ → ℂ) (x₀ : ℝ) : Prop :=
  ContDiff ℝ ∞ gl ∧ ContDiff ℝ ∞ gr ∧ (∀ x, x < x₀ → f x = gl x) ∧ (∀ x, x₀ < x → f x = gr x)

namespace IsPiecewiseSmooth

variable {f gl gr : ℝ → ℂ} {x₀ : ℝ}

theorem deriv (h : IsPiecewiseSmooth f gl gr x₀) :
    IsPiecewiseSmooth (_root_.deriv f) (_root_.deriv gl) (_root_.deriv gr) x₀ := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨(contDiff_infty_iff_deriv.mp h1).2, (contDiff_infty_iff_deriv.mp h2).2,
    fun x hx => ?_, fun x hx => ?_⟩
  · exact EventuallyEq.deriv_eq (Filter.mem_of_superset (Iio_mem_nhds hx) fun y hy => h3 y hy)
  · exact EventuallyEq.deriv_eq (Filter.mem_of_superset (Ioi_mem_nhds hx) fun y hy => h4 y hy)

theorem iteratedDeriv (h : IsPiecewiseSmooth f gl gr x₀) (m : ℕ) :
    IsPiecewiseSmooth (_root_.iteratedDeriv m f) (_root_.iteratedDeriv m gl)
      (_root_.iteratedDeriv m gr) x₀ := by
  induction m with
  | zero => simpa using h
  | succ m ih => simpa only [iteratedDeriv_succ] using ih.deriv

theorem locallyIntegrableOn (h : IsPiecewiseSmooth f gl gr x₀) (I : Set ℝ) :
    LocallyIntegrableOn f I := by
  have hF : LocallyIntegrable ((Iio x₀).indicator gl + (Ici x₀).indicator gr) volume :=
    (h.1.continuous.locallyIntegrable.indicator measurableSet_Iio).add
      (h.2.1.continuous.locallyIntegrable.indicator measurableSet_Ici)
  refine (hF.locallyIntegrableOn I).congr (ae_restrict_of_ae ?_)
  filter_upwards [(countable_singleton x₀).ae_notMem volume] with x hx
  rcases lt_or_gt_of_ne (show x ≠ x₀ from fun e => hx (by rw [e]; rfl)) with hlt | hgt
  · simp [indicator, hlt, not_le.mpr hlt, h.2.2.1 x hlt]
  · simp [indicator, not_lt.mpr hgt.le, hgt.le, h.2.2.2 x hgt]

/-- DLMF 1.16.17: the one-sided limits of `f⁽ⁿ⁾` at `x₀`, whose difference is the jump `σₙ`. -/
theorem tendsto_iteratedDeriv (h : IsPiecewiseSmooth f gl gr x₀) (n : ℕ) :
    Tendsto (_root_.iteratedDeriv n f) (𝓝[>] x₀) (𝓝 (_root_.iteratedDeriv n gr x₀)) ∧
      Tendsto (_root_.iteratedDeriv n f) (𝓝[<] x₀) (𝓝 (_root_.iteratedDeriv n gl x₀)) := by
  obtain ⟨h1, h2, h3, h4⟩ := h.iteratedDeriv n
  refine ⟨((h2.continuous.tendsto x₀).mono_left nhdsWithin_le_nhds).congr' ?_,
    ((h1.continuous.tendsto x₀).mono_left nhdsWithin_le_nhds).congr' ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with x hx using (h4 x hx).symm
  · filter_upwards [self_mem_nhdsWithin] with x hx using (h3 x hx).symm

end IsPiecewiseSmooth

/-- DLMF 1.16.17: the jump `σₙ = f⁽ⁿ⁾(x₀+) − f⁽ⁿ⁾(x₀−)`. -/
noncomputable def jump (gl gr : ℝ → ℂ) (x₀ : ℝ) (n : ℕ) : ℂ :=
  iteratedDeriv n gr x₀ - iteratedDeriv n gl x₀

theorem integral_Iic_mul_deriv {g φ : ℝ → ℂ} (hg : ContDiff ℝ 1 g) (hφ : ContDiff ℝ 1 φ)
    (hs : HasCompactSupport φ) (x₀ : ℝ) :
    ∫ x in Iic x₀, g x * deriv φ x = g x₀ * φ x₀ - ∫ x in Iic x₀, deriv g x * φ x := by
  obtain ⟨R₀, -, hR₀⟩ := exists_Ioo_superset_tsupport hs
  obtain ⟨R₁, -, hR₁⟩ := exists_Ioo_superset_tsupport hs.deriv
  set a := min (min (-R₀) (-R₁)) (x₀ - 1)
  have ha0 : a ≤ -R₀ := (min_le_left _ _).trans (min_le_left _ _)
  have ha1 : a ≤ -R₁ := (min_le_left _ _).trans (min_le_right _ _)
  have hax : a < x₀ := by have := min_le_right (min (-R₀) (-R₁)) (x₀ - 1); linarith
  have hz0 : ∀ x ≤ a, φ x = 0 := fun x hx => hR₀ x fun h => by linarith [h.1]
  have hz1 : ∀ x ≤ a, deriv φ x = 0 := fun x hx => hR₁ x fun h => by linarith [h.1]
  have hout : ∀ x ∈ Iic x₀ \ Ioc a x₀, x ≤ a := fun x hx => by
    by_contra hc; exact hx.2 ⟨lt_of_not_ge hc, hx.1⟩
  have e1 : ∫ x in Iic x₀, g x * deriv φ x = ∫ x in a..x₀, g x * deriv φ x := by
    rw [intervalIntegral.integral_of_le hax.le,
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Iic Ioc_subset_Iic_self
        fun x hx => by rw [hz1 x (hout x hx), mul_zero]]
  have e2 : ∫ x in Iic x₀, deriv g x * φ x = ∫ x in a..x₀, deriv g x * φ x := by
    rw [intervalIntegral.integral_of_le hax.le,
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Iic Ioc_subset_Iic_self
        fun x hx => by rw [hz0 x (hout x hx), mul_zero]]
  rw [e1, e2, intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x _ => (hg.differentiable one_ne_zero x).hasDerivAt)
    (fun x _ => (hφ.differentiable one_ne_zero x).hasDerivAt)
    ((hg.continuous_deriv le_rfl).intervalIntegrable _ _)
    ((hφ.continuous_deriv le_rfl).intervalIntegrable _ _), hz0 a le_rfl, mul_zero, sub_zero]

theorem integral_Ioi_mul_deriv' {g φ : ℝ → ℂ} (hg : ContDiff ℝ 1 g) (hφ : ContDiff ℝ 1 φ)
    (hs : HasCompactSupport φ) (x₀ : ℝ) :
    ∫ x in Ioi x₀, g x * deriv φ x = -(g x₀ * φ x₀) - ∫ x in Ioi x₀, deriv g x * φ x := by
  obtain ⟨R₀, -, hR₀⟩ := exists_Ioo_superset_tsupport hs
  obtain ⟨R₁, -, hR₁⟩ := exists_Ioo_superset_tsupport hs.deriv
  set b := max (max R₀ R₁) (x₀ + 1)
  have hb0 : R₀ ≤ b := (le_max_left _ _).trans (le_max_left _ _)
  have hb1 : R₁ ≤ b := (le_max_right _ _).trans (le_max_left _ _)
  have hxb : x₀ < b := by have := le_max_right (max R₀ R₁) (x₀ + 1); linarith
  have hz0 : ∀ x, b ≤ x → φ x = 0 := fun x hx => hR₀ x fun h => by linarith [h.2]
  have hz1 : ∀ x, b ≤ x → deriv φ x = 0 := fun x hx => hR₁ x fun h => by linarith [h.2]
  have hout : ∀ x ∈ Ioi x₀ \ Ioc x₀ b, b ≤ x := fun x hx => by
    by_contra hc; exact hx.2 ⟨hx.1, (lt_of_not_ge hc).le⟩
  have e1 : ∫ x in Ioi x₀, g x * deriv φ x = ∫ x in x₀..b, g x * deriv φ x := by
    rw [intervalIntegral.integral_of_le hxb.le,
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
        fun x hx => by rw [hz1 x (hout x hx), mul_zero]]
  have e2 : ∫ x in Ioi x₀, deriv g x * φ x = ∫ x in x₀..b, deriv g x * φ x := by
    rw [intervalIntegral.integral_of_le hxb.le,
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
        fun x hx => by rw [hz0 x (hout x hx), mul_zero]]
  rw [e1, e2, intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x _ => (hg.differentiable one_ne_zero x).hasDerivAt)
    (fun x _ => (hφ.differentiable one_ne_zero x).hasDerivAt)
    ((hg.continuous_deriv le_rfl).intervalIntegrable _ _)
    ((hφ.continuous_deriv le_rfl).intervalIntegrable _ _), hz0 b le_rfl, mul_zero, zero_sub]

/-- The case `m = 1` of 1.16.18: `Df = f' + σ₀ δ_{x₀}`. -/
theorem distDeriv_piecewise (hI : IsOpen I) {f gl gr : ℝ → ℂ} {x₀ : ℝ}
    (h : IsPiecewiseSmooth f gl gr x₀) :
    distDeriv hI (h.locallyIntegrableOn I) =
      regularDist hI (h.deriv.locallyIntegrableOn I) + jump gl gr x₀ 0 • diracDist I x₀ := by
  ext φ
  simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, distDeriv_apply,
    dlmf_1_16_3, dlmf_1_16_11, jump, iteratedDeriv_zero]
  set ψ : ℝ → ℂ := (φ : ℝ → ℂ) with hψdef
  have hψ1 : ContDiff ℝ 1 ψ := φ.2.1.of_le (by exact_mod_cast le_top)
  have hzero : ∀ x ∉ I, ψ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun hh => hx (φ.2.2.2 hh)
  have hzero' : ∀ x ∉ I, deriv ψ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun hh => hx (φ.2.2.2 (tsupport_deriv_subset hh))
  have hA : ∫ x in I, f x * deriv ψ x = ∫ x, f x * deriv ψ x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by rw [hzero' x hx, mul_zero]
  have hB : ∫ x in I, deriv f x * ψ x = ∫ x, deriv f x * ψ x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by rw [hzero x hx, mul_zero]
  have hAi : Integrable fun x => f x * deriv ψ x :=
    (integrableOn_mul_testFunction hI (h.locallyIntegrableOn I)
      (isTestFunction_deriv φ.2)).integrable_of_forall_notMem_eq_zero
        fun x hx => by rw [hzero' x hx, mul_zero]
  have hBi : Integrable fun x => deriv f x * ψ x :=
    (integrableOn_mul_testFunction hI (h.deriv.locallyIntegrableOn I)
      φ.2).integrable_of_forall_notMem_eq_zero fun x hx => by
        rw [show (φ : ℝ → ℂ) x = 0 from hzero x hx, mul_zero]
  rw [hA, hB, ← integral_add_compl measurableSet_Iic hAi,
    ← integral_add_compl measurableSet_Iic hBi,
    compl_Iic]
  have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ ({x₀} : Set ℝ) :=
    (countable_singleton x₀).ae_notMem volume
  have hL : ∀ u v : ℝ → ℂ, (∀ x, x < x₀ → u x = v x) →
      ∫ x in Iic x₀, u x * ψ x = ∫ x in Iic x₀, v x * ψ x := fun u v huv =>
    setIntegral_congr_ae measurableSet_Iic (by
      filter_upwards [hne] with x hx hxI
      rw [huv x (lt_of_le_of_ne hxI fun e => hx (by rw [e]; rfl))])
  have hL' : ∀ u v : ℝ → ℂ, (∀ x, x < x₀ → u x = v x) →
      ∫ x in Iic x₀, u x * deriv ψ x = ∫ x in Iic x₀, v x * deriv ψ x := fun u v huv =>
    setIntegral_congr_ae measurableSet_Iic (by
      filter_upwards [hne] with x hx hxI
      rw [huv x (lt_of_le_of_ne hxI fun e => hx (by rw [e]; rfl))])
  rw [hL' f gl h.2.2.1, hL (deriv f) (deriv gl) h.deriv.2.2.1,
    setIntegral_congr_fun (f := fun x => f x * deriv ψ x) (g := fun x => gr x * deriv ψ x)
      measurableSet_Ioi fun x (hx : x₀ < x) => by simp only [h.2.2.2 x hx],
    setIntegral_congr_fun (f := fun x => deriv f x * ψ x) (g := fun x => deriv gr x * ψ x)
      measurableSet_Ioi fun x (hx : x₀ < x) => by simp only [h.deriv.2.2.2 x hx],
    integral_Iic_mul_deriv (h.1.of_le (by exact_mod_cast le_top)) hψ1 φ.2.2.1,
    integral_Ioi_mul_deriv' (h.2.1.of_le (by exact_mod_cast le_top)) hψ1 φ.2.2.1]
  ring

/-- Differentiation of distributions is linear. -/
noncomputable def derivDistₗ (I : Set ℝ) :
    (testSpace I →ₗ[ℂ] ℂ) →ₗ[ℂ] (testSpace I →ₗ[ℂ] ℂ) where
  toFun := derivDist
  map_add' Λ₁ Λ₂ := by ext φ; simp [dlmf_1_16_8]; ring
  map_smul' c Λ := by ext φ; simp [dlmf_1_16_8]

theorem derivDistₗ_apply (Λ : testSpace I →ₗ[ℂ] ℂ) : derivDistₗ I Λ = derivDist Λ := rfl

theorem regularDist_congr (hI : IsOpen I) {f g : ℝ → ℂ} (h : f = g)
    (hf : LocallyIntegrableOn f I) (hg : LocallyIntegrableOn g I) :
    regularDist hI hf = regularDist hI hg := by
  subst h; rfl

/-- DLMF 1.16.18: `Dᵐf = f⁽ᵐ⁾ + σ₀ δ_{x₀}⁽ᵐ⁻¹⁾ + σ₁ δ_{x₀}⁽ᵐ⁻²⁾ + ⋯ + σ_{m−1} δ_{x₀}`, with the
jumps `σₙ` of 1.16.17 (for `m = 0` the sum is empty). -/
theorem dlmf_1_16_18 (hI : IsOpen I) {f gl gr : ℝ → ℂ} {x₀ : ℝ}
    (h : IsPiecewiseSmooth f gl gr x₀) (m : ℕ) :
    derivDist^[m] (regularDist hI (h.locallyIntegrableOn I)) =
      regularDist hI ((h.iteratedDeriv m).locallyIntegrableOn I) +
        ∑ k ∈ Finset.range m, jump gl gr x₀ k • derivDist^[m - 1 - k] (diracDist I x₀) := by
  induction m with
  | zero =>
    simp only [Function.iterate_zero, id, Finset.range_zero, Finset.sum_empty, add_zero]
    exact regularDist_congr hI (iteratedDeriv_zero).symm _ _
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, ← derivDistₗ_apply, map_add, map_sum,
      derivDistₗ_apply]
    have hb := distDeriv_piecewise hI (h.iteratedDeriv m)
    rw [distDeriv] at hb
    rw [hb, Finset.sum_range_succ]
    have hj : jump (iteratedDeriv m gl) (iteratedDeriv m gr) x₀ 0 = jump gl gr x₀ m := by
      simp [jump]
    rw [hj, regularDist_congr hI (iteratedDeriv_succ (f := f)).symm _
      ((h.iteratedDeriv (m + 1)).locallyIntegrableOn I)]
    have hs : ∀ k ∈ Finset.range m, derivDistₗ I (jump gl gr x₀ k •
        derivDist^[m - 1 - k] (diracDist I x₀)) =
        jump gl gr x₀ k • derivDist^[m + 1 - 1 - k] (diracDist I x₀) := fun k hk => by
      rw [map_smul, derivDistₗ_apply, ← Function.iterate_succ_apply' derivDist]
      congr 2
      have := Finset.mem_range.mp hk
      omega
    rw [Finset.sum_congr rfl hs, show m + 1 - 1 - m = 0 by omega, Function.iterate_zero, id]
    abel

/-! ### `x₊^α` (1.16.19–1.16.20) -/

/-- The function `x ↦ g(x) H(x)` (cast to `ℂ`). -/
noncomputable def posPart (g : ℝ → ℝ) (x : ℝ) : ℂ := if 0 < x then (g x : ℂ) else 0

theorem locallyIntegrable_posPart {g : ℝ → ℝ} (hg : ∀ R, 0 ≤ R → IntegrableOn g (Ioc 0 R)) :
    LocallyIntegrable (posPart g) volume := by
  have he : posPart g = (Ioi 0).indicator fun x => (g x : ℂ) := funext fun x => by
    by_cases h : 0 < x <;> simp [posPart, h, indicator]
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  have hR' : K ⊆ Icc (-|R|) |R| := fun x hx => by
    have := hR hx
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    exact abs_le.mp (this.trans (le_abs_self R))
  refine IntegrableOn.mono_set ?_ hR'
  rw [he, IntegrableOn, integrable_indicator_iff measurableSet_Ioi, IntegrableOn,
    Measure.restrict_restrict measurableSet_Ioi]
  exact ((hg |R| (abs_nonneg R)).ofReal).mono_set fun x hx => ⟨hx.1, hx.2.2⟩

/-- DLMF 1.16.19: `x₊^α = x^α H(x)`. -/
noncomputable def posPow (α : ℝ) : ℝ → ℂ := posPart fun x => x ^ α

theorem dlmf_1_16_19 (α x : ℝ) : posPow α x = ((x ^ α * heavisideH x : ℝ) : ℂ) := by
  unfold posPow posPart heavisideH
  split_ifs <;> simp

theorem locallyIntegrable_posPow {α : ℝ} (hα : -1 < α) : LocallyIntegrable (posPow α) volume :=
  locallyIntegrable_posPart fun _ _ => (intervalIntegral.intervalIntegrable_rpow' hα).1

/-- Integrals against `g H` reduce to `∫_0^b` when the other factor vanishes off `I` and beyond
`b`. -/
theorem integral_posPart_mul (g : ℝ → ℝ) {ψ : ℝ → ℂ} (hψI : ∀ x ∉ I, ψ x = 0) {b : ℝ}
    (hb : 0 ≤ b) (hψb : ∀ x, b < x → ψ x = 0) :
    ∫ x in I, posPart g x * ψ x = ∫ x in (0 : ℝ)..b, (g x : ℂ) * ψ x := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by rw [hψI x hx, mul_zero],
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioc 0 b) fun x hx => ?_,
    intervalIntegral.integral_of_le hb]
  · exact setIntegral_congr_fun measurableSet_Ioc fun x hx => by simp [posPart, hx.1]
  · rw [mem_Ioc, not_and_or, not_lt, not_le] at hx
    rcases hx with hx | hx
    · simp [posPart, not_lt.mpr hx]
    · rw [hψb x hx, mul_zero]

theorem exists_bound_tsupport_testFunction {φ : ℝ → ℂ} (hφ : IsTestFunction I φ) :
    ∃ b : ℝ, 0 ≤ b ∧ (∀ x, b ≤ x → φ x = 0) ∧ ∀ x, b ≤ x → deriv φ x = 0 := by
  obtain ⟨R₀, hR₀0, hR₀⟩ := exists_Ioo_superset_tsupport hφ.2.1
  obtain ⟨R₁, -, hR₁⟩ := exists_Ioo_superset_tsupport hφ.2.1.deriv
  refine ⟨max R₀ R₁, hR₀0.le.trans (le_max_left _ _), fun x hx => hR₀ x fun h => ?_,
    fun x hx => hR₁ x fun h => ?_⟩
  · linarith [h.2, le_max_left R₀ R₁]
  · linarith [h.2, le_max_right R₀ R₁]

/-- DLMF 1.16.20: `D x₊^α = α x₊^{α−1}` for `α > 0`. -/
theorem dlmf_1_16_20 (hI : IsOpen I) {α : ℝ} (hα : 0 < α) :
    distDeriv hI ((locallyIntegrable_posPow (by linarith : -1 < α)).locallyIntegrableOn I) =
      (α : ℂ) • regularDist hI
        ((locallyIntegrable_posPow (by linarith : -1 < α - 1)).locallyIntegrableOn I) := by
  ext φ
  obtain ⟨b, hb, hφb, hφb'⟩ := exists_bound_tsupport_testFunction φ.2
  have hzero : ∀ x ∉ I, (φ : ℝ → ℂ) x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (φ.2.2.2 h)
  have hzero' : ∀ x ∉ I, deriv (φ : ℝ → ℂ) x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (φ.2.2.2 (tsupport_deriv_subset h))
  rw [distDeriv_apply, LinearMap.smul_apply, dlmf_1_16_3, smul_eq_mul]
  rw [show posPow α = posPart fun x => x ^ α from rfl,
    show posPow (α - 1) = posPart fun x => x ^ (α - 1) from rfl,
    integral_posPart_mul _ hzero' hb fun x hx => hφb' x hx.le,
    integral_posPart_mul _ hzero hb fun x hx => hφb x hx.le]
  have hφ1 : ContDiff ℝ 1 (φ : ℝ → ℂ) := φ.2.1.of_le (by exact_mod_cast le_top)
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun x => ((x ^ α : ℝ) : ℂ)) (u' := fun x => ((α * x ^ (α - 1) : ℝ) : ℂ))
    ((Complex.continuous_ofReal.comp (Real.continuous_rpow_const hα.le)).continuousOn)
    hφ1.continuous.continuousOn
    (fun x hx => by
      have hx0 : 0 < x := by simpa [hb] using hx.1
      exact (Real.hasDerivAt_rpow_const (Or.inl hx0.ne')).ofReal_comp)
    (fun x _ => (hφ1.differentiable one_ne_zero x).hasDerivAt)
    (by
      have h := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := b)
        (by linarith : -1 < α - 1)).const_mul α
      exact ⟨h.1.ofReal, h.2.ofReal⟩)
    ((hφ1.continuous_deriv le_rfl).intervalIntegrable _ _),
    hφb b le_rfl, Real.zero_rpow hα.ne']
  · rw [← intervalIntegral.integral_const_mul]
    simp only [Complex.ofReal_zero, zero_mul, mul_zero, sub_zero, zero_sub, neg_neg]
    refine intervalIntegral.integral_congr fun x _ => ?_
    push_cast; ring

/-! ### `x₊^α` for `α < −1` (1.16.21) -/

theorem derivDist_iterate_smul (n : ℕ) (c : ℂ) (Λ : testSpace I →ₗ[ℂ] ℂ) :
    derivDist^[n] (c • Λ) = c • derivDist^[n] Λ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply', ← derivDistₗ_apply,
      map_smul, derivDistₗ_apply]

/-- DLMF 1.16.21: `x₊^α = (1/(α + 1)ₙ) Dⁿ x₊^{α+n}`, for an integer `n` with `α + n > −1`. -/
noncomputable def posPowDist (hI : IsOpen I) (α : ℝ) (n : ℕ) (hn : -1 < α + n) :
    testSpace I →ₗ[ℂ] ℂ :=
  (((ascPochhammer ℝ n).eval (α + 1) : ℝ) : ℂ)⁻¹ •
    derivDist^[n] (regularDist hI ((locallyIntegrable_posPow hn).locallyIntegrableOn I))

/-- For `α > −1`, `n = 0` gives the regular distribution `x₊^α`. -/
theorem posPowDist_zero (hI : IsOpen I) {α : ℝ} (hα : -1 < α) :
    posPowDist hI α 0 (by simpa using hα) =
      regularDist hI ((locallyIntegrable_posPow hα).locallyIntegrableOn I) := by
  simp only [posPowDist, ascPochhammer_zero, Polynomial.eval_one, Complex.ofReal_one, inv_one,
    one_smul, Function.iterate_zero, id]
  exact regularDist_congr hI (by simp) _ _

theorem add_one_add_ne_zero {α : ℝ} (hα : ∀ k : ℤ, α ≠ k) (n : ℕ) : α + 1 + n ≠ 0 := by
  intro h
  exact hα (-(n + 1 : ℤ)) (by push_cast; linarith)

theorem posPowDist_succ (hI : IsOpen I) {α : ℝ} (hα : ∀ k : ℤ, α ≠ k) {n : ℕ}
    (hn : -1 < α + n) (hn' : -1 < α + ((n + 1 : ℕ) : ℝ)) :
    posPowDist hI α (n + 1) hn' = posPowDist hI α n hn := by
  unfold posPowDist
  have h20 := dlmf_1_16_20 (I := I) hI (α := α + ((n + 1 : ℕ) : ℝ)) (by push_cast; linarith)
  rw [distDeriv] at h20
  rw [Function.iterate_succ_apply, h20, regularDist_congr hI
    (show posPow (α + ((n + 1 : ℕ) : ℝ) - 1) = posPow (α + n) by congr 1; push_cast; ring) _
    ((locallyIntegrable_posPow hn).locallyIntegrableOn I), derivDist_iterate_smul, smul_smul,
    ascPochhammer_succ_eval]
  congr 1
  have hne : ((α + 1 + n : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (add_one_add_ne_zero hα n)
  rw [Complex.ofReal_mul, mul_inv, mul_assoc, show ((α + ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) =
    ((α + 1 + n : ℝ) : ℂ) by push_cast; ring, inv_mul_cancel₀ hne, mul_one]

/-- 1.16.21 does not depend on the choice of `n`. -/
theorem posPowDist_indep (hI : IsOpen I) {α : ℝ} (hα : ∀ k : ℤ, α ≠ k) {n m : ℕ}
    (hn : -1 < α + n) (hm : -1 < α + m) : posPowDist hI α n hn = posPowDist hI α m hm := by
  have key : ∀ (n j : ℕ) (hn : -1 < α + n) (hj : -1 < α + ((n + j : ℕ) : ℝ)),
      posPowDist hI α (n + j) hj = posPowDist hI α n hn := by
    intro n j
    induction j with
    | zero => intro _ _; rfl
    | succ j ih =>
      intro hn hj
      have hj' : -1 < α + ((n + j : ℕ) : ℝ) := by
        have : (0 : ℝ) ≤ j := j.cast_nonneg
        push_cast; linarith
      rw [← ih hn hj']
      exact posPowDist_succ hI hα hj' hj
  rcases le_total n m with h | h
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
    exact (key n j hn hm).symm
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
    exact key m j hm hn

/-- The power rule `D x₊^α = α x₊^{α−1}` for the distributions of 1.16.21. -/
theorem derivDist_posPowDist (hI : IsOpen I) {α : ℝ} (hα : ∀ k : ℤ, α ≠ k) {n : ℕ}
    (hn : -1 < α + n) (hn' : -1 < α - 1 + ((n + 1 : ℕ) : ℝ)) :
    derivDist (posPowDist hI α n hn) = (α : ℂ) • posPowDist hI (α - 1) (n + 1) hn' := by
  unfold posPowDist
  rw [← derivDistₗ_apply, map_smul, derivDistₗ_apply, ← Function.iterate_succ_apply' derivDist,
    regularDist_congr hI (show posPow (α - 1 + ((n + 1 : ℕ) : ℝ)) = posPow (α + n) by
      congr 1; push_cast; ring) _ ((locallyIntegrable_posPow hn).locallyIntegrableOn I),
    smul_smul, ascPochhammer_succ_left]
  congr 1
  have hα0 : (α : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by exact_mod_cast hα 0)
  simp only [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_one, sub_add_cancel, Complex.ofReal_mul]
  rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hα0, one_mul]

/-! ### `ln₊ x` and `x₊^{−1−n}` (1.16.22–1.16.23) -/

/-- DLMF 1.16.22: `ln₊ x = H(x) ln x`. -/
noncomputable def lnPos : ℝ → ℂ := posPart Real.log

theorem dlmf_1_16_22 (x : ℝ) : lnPos x = ((heavisideH x * Real.log x : ℝ) : ℂ) := by
  unfold lnPos posPart heavisideH
  split_ifs <;> simp

theorem locallyIntegrable_lnPos : LocallyIntegrable lnPos volume :=
  locallyIntegrable_posPart fun _ _ => intervalIntegral.intervalIntegrable_log'.1

/-- DLMF 1.16.23: the distribution `x₊^{−1−n}`, defined by
`(−1)ⁿ n! x₊^{−1−n} = D^{n+1} ln₊ x`. -/
noncomputable def negPowDist (hI : IsOpen I) (n : ℕ) : testSpace I →ₗ[ℂ] ℂ :=
  ((-1 : ℂ) ^ n * (n.factorial : ℂ))⁻¹ •
    derivDist^[n + 1] (regularDist hI (locallyIntegrable_lnPos.locallyIntegrableOn I))

theorem dlmf_1_16_23 (hI : IsOpen I) (n : ℕ) :
    ((-1 : ℂ) ^ n * (n.factorial : ℂ)) • negPowDist hI n =
      derivDist^[n + 1] (regularDist hI (locallyIntegrable_lnPos.locallyIntegrableOn I)) := by
  have hne : ((-1 : ℂ) ^ n * (n.factorial : ℂ)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast n.factorial_ne_zero)
  rw [negPowDist, smul_smul, mul_inv_cancel₀ hne, one_smul]

/-- The power rule `D x₊^{−1−n} = −(n + 1) x₊^{−2−n}` for the distributions of 1.16.23. -/
theorem derivDist_negPowDist (hI : IsOpen I) (n : ℕ) :
    derivDist (negPowDist hI n) = (-(n + 1 : ℂ)) • negPowDist hI (n + 1) := by
  unfold negPowDist
  rw [← derivDistₗ_apply, map_smul, derivDistₗ_apply, ← Function.iterate_succ_apply' derivDist,
    smul_smul]
  congr 1
  have h1 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem contDiffOn_lnPos : ContDiffOn ℝ 1 lnPos (Ioi 0) :=
  (Complex.ofRealCLM.contDiff.comp_contDiffOn
    (Real.contDiffOn_log.mono fun x (hx : 0 < x) => hx.ne')).congr fun x (hx : 0 < x) => by
    simp [lnPos, posPart, hx]

theorem deriv_lnPos {x : ℝ} (hx : 0 < x) : deriv lnPos x = ((x⁻¹ : ℝ) : ℂ) := by
  have hev : lnPos =ᶠ[𝓝 x] fun y => ((Real.log y : ℝ) : ℂ) := by
    filter_upwards [Ioi_mem_nhds hx] with y (hy : 0 < y)
    simp [lnPos, posPart, hy]
  rw [hev.deriv_eq]
  exact ((Real.hasDerivAt_log hx.ne').ofReal_comp).deriv

/-- Away from the origin `x₊^{−1} = D ln₊ x` is the function `1/x`: for test functions supported
in `(0, ∞)`, `⟨x₊^{−1}, φ⟩ = ∫ φ(x)/x dx`. -/
theorem negPowDist_zero_apply_of_pos (hI : IsOpen I) (φ : testSpace I)
    (hφ : tsupport (φ : ℝ → ℂ) ⊆ Ioi 0) :
    negPowDist hI 0 φ = ∫ x in I, ((x⁻¹ : ℝ) : ℂ) * (φ : ℝ → ℂ) x := by
  have hT : IsTestFunction (Ioi 0) (φ : ℝ → ℂ) := ⟨φ.2.1, φ.2.2.1, hφ⟩
  have h := distDeriv_of_contDiffOn isOpen_Ioi contDiffOn_lnPos ⟨φ, hT⟩
  rw [distDeriv_apply, dlmf_1_16_3] at h
  simp only [negPowDist, pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, inv_one, one_smul,
    zero_add, Function.iterate_one, dlmf_1_16_8, dlmf_1_16_3, coe_derivTest]
  have hzero' : ∀ x, x ∉ tsupport (φ : ℝ → ℂ) → deriv (φ : ℝ → ℂ) x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (tsupport_deriv_subset h)
  have hzero : ∀ x, x ∉ tsupport (φ : ℝ → ℂ) → (φ : ℝ → ℂ) x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport hx
  have e1 : ∫ x in I, lnPos x * deriv (φ : ℝ → ℂ) x =
      ∫ x in Ioi 0, lnPos x * deriv (φ : ℝ → ℂ) x := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        rw [hzero' x fun h => hx (φ.2.2.2 h), mul_zero],
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        rw [hzero' x fun h => hx (hφ h), mul_zero]]
  have e2 : ∫ x in I, ((x⁻¹ : ℝ) : ℂ) * (φ : ℝ → ℂ) x =
      ∫ x in Ioi 0, deriv lnPos x * (φ : ℝ → ℂ) x := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        rw [hzero x fun h => hx (φ.2.2.2 h), mul_zero],
      setIntegral_congr_fun measurableSet_Ioi fun x (hx : 0 < x) => by rw [deriv_lnPos hx],
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        rw [hzero x fun h => hx (hφ h), mul_zero]]
  rw [e1, e2, ← h]

end Azurite.DLMF
