/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section4
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# DLMF §1.15(vi): Fractional integrals

https://dlmf.nist.gov/1.15.vi

* 1.15.47: the Riemann–Liouville fractional integral `fracIntegral` (`I^α`), and its version
  `fracIntegralFrom a` with any lower limit `a ≤ x`.
* 1.15.48: the semigroup property `I^α I^β = I^{α+β}`. The general form `fracIntegralFrom_add`
  assumes only that `f` is integrable on `(a, x]` with `∫ |f(t)| (x − t)^{ℜα+ℜβ−1} dt < ∞`. The
  proof is Fubini on the triangle plus the shifted Beta integral `integral_beta_shift`.
  `dlmf_1_15_48` is the case of `f` continuous on `[0, ∞)`.
* Comparison with 1.4.31: for order `n + 1` the fractional integral is the `(n + 1)`-fold repeated
  integral (`fracIntegralFrom_natCast`).
* 1.15.49–1.15.50: termwise fractional integration of power series (`dlmf_1_15_50`), from
  `I^α tᵏ = k!/Γ(k + α + 1) x^{k+α}` (`fracIntegral_pow`).
* The closing remarks: the upper-limit variant `fracIntegralTo` (`∫_x^a (t − x)^{α−1} f(t) dt`),
  which is the reflection of the lower-limit one (`fracIntegralTo_eq`) and has the same
  semigroup property (`fracIntegralTo_add`). The Weyl variant `fracIntegralWeyl` (`a = ∞`) is the
  limit `a → ∞` (`tendsto_fracIntegralTo_atTop`).

DLMF does not say which `f` the definitions apply to. Here (1.15.48) assumes the weighted
integrability above, and (1.15.50) assumes absolute convergence `∑ |aₖ| xᵏ < ∞` at the point `x`.
-/

open MeasureTheory Filter Topology Set Complex
open scoped Real Nat

namespace Azurite.DLMF

/-! ### Definitions (1.15.47 and its variants) -/

/-- The Riemann–Liouville fractional integral with lower limit `a`:
`(1/Γ(α)) ∫_a^x (x − t)^{α−1} f(t) dt`, for `ℜα > 0` and `x ≥ a`. -/
noncomputable def fracIntegralFrom (a : ℝ) (α : ℂ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (Gamma α)⁻¹ * ∫ t in a..x, ((x - t : ℝ) : ℂ) ^ (α - 1) * f t

/-- DLMF 1.15.47: the Riemann–Liouville fractional integral
`I^α f(x) = (1/Γ(α)) ∫_0^x (x − t)^{α−1} f(t) dt`, for `ℜα > 0` and `x ≥ 0`. -/
noncomputable def fracIntegral (α : ℂ) (f : ℝ → ℂ) (x : ℝ) : ℂ := fracIntegralFrom 0 α f x

theorem dlmf_1_15_47 (α : ℂ) (f : ℝ → ℂ) (x : ℝ) :
    fracIntegral α f x = 1 / Gamma α * ∫ t in (0 : ℝ)..x, ((x - t : ℝ) : ℂ) ^ (α - 1) * f t := by
  rw [fracIntegral, fracIntegralFrom, one_div]

/-! ### The shifted Beta integral -/

/-- `∫_t^x (x − s)^{α−1} (s − t)^{β−1} ds = (x − t)^{α+β−1} Γ(α)Γ(β)/Γ(α+β)`. -/
theorem integral_beta_shift {α β : ℂ} (hα : 0 < α.re) (hβ : 0 < β.re) {t x : ℝ} (htx : t < x) :
    IntervalIntegrable (fun s : ℝ => ((x - s : ℝ) : ℂ) ^ (α - 1) * ((s - t : ℝ) : ℂ) ^ (β - 1))
      volume t x ∧
    ∫ s in t..x, ((x - s : ℝ) : ℂ) ^ (α - 1) * ((s - t : ℝ) : ℂ) ^ (β - 1) =
      ((x - t : ℝ) : ℂ) ^ (α + β - 1) * (Gamma α * Gamma β / Gamma (α + β)) := by
  set c := x - t with hcdef
  have hc : 0 < c := sub_pos.mpr htx
  set ψ : ℝ → ℂ := fun u => (u : ℂ) ^ (β - 1) * (1 - (u : ℂ)) ^ (α - 1) with hψ
  set K : ℂ := (c : ℂ) ^ (α - 1) * (c : ℂ) ^ (β - 1)
  have key : ∀ s ∈ uIcc t x, ((x - s : ℝ) : ℂ) ^ (α - 1) * ((s - t : ℝ) : ℂ) ^ (β - 1) =
      K * ψ (s / c - t / c) := fun s hs => by
    rw [uIcc_of_le htx.le] at hs
    have hu : s / c - t / c = (s - t) / c := by ring
    have hu0 : 0 ≤ (s - t) / c := div_nonneg (by linarith [hs.1]) hc.le
    have hu1 : 0 ≤ 1 - (s - t) / c := by
      rw [sub_nonneg, div_le_one hc]; linarith [hs.2]
    have e1 : ((x - s : ℝ) : ℂ) = (c : ℂ) * ((1 - (s - t) / c : ℝ) : ℂ) := by
      rw [← ofReal_mul]; congr 1; field_simp; ring
    have e2 : ((s - t : ℝ) : ℂ) = (c : ℂ) * (((s - t) / c : ℝ) : ℂ) := by
      rw [← ofReal_mul]; congr 1; field_simp
    rw [e1, e2, mul_cpow_ofReal_nonneg hc.le hu1, mul_cpow_ofReal_nonneg hc.le hu0, hu]
    simp only [ψ, K]
    push_cast
    ring
  have hψi : IntervalIntegrable ψ volume 0 1 := betaIntegral_convergent hβ hα
  have hint : IntervalIntegrable (fun s => K * ψ (s / c - t / c)) volume t x := by
    have h1 := (hψi.comp_mul_left (c := c⁻¹)).comp_sub_right t
    have h2 : IntervalIntegrable (fun s => ψ (s / c - t / c)) volume t x := by
      convert h1 using 1
      · funext s; congr 1; field_simp
      · simp
      · rw [one_div, inv_inv, hcdef]; ring
    exact h2.const_mul K
  refine ⟨hint.congr (fun s hs => (key s (uIoc_subset_uIcc hs)).symm), ?_⟩
  rw [intervalIntegral.integral_congr key, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_div_sub ψ hc.ne']
  have e3 : t / c - t / c = 0 := sub_self _
  have e4 : x / c - t / c = 1 := by rw [← sub_div, div_self hc.ne']
  rw [e3, e4]
  have hB : ∫ u in (0 : ℝ)..1, ψ u = betaIntegral α β := by
    rw [← betaIntegral_symm]; rfl
  rw [hB]
  have hG := Gamma_mul_Gamma_eq_betaIntegral hα hβ
  have hG0 : Gamma (α + β) ≠ 0 := Gamma_ne_zero_of_re_pos (by rw [add_re]; linarith)
  have hc0 : (c : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc.ne'
  rw [hG, mul_div_cancel_left₀ _ hG0, real_smul]
  simp only [K]
  rw [show α + β - 1 = (α - 1) + (β - 1) + 1 by ring, cpow_add _ _ hc0, cpow_add _ _ hc0,
    cpow_one]
  ring

/-! ### The semigroup property (1.15.48) -/

theorem Ioc_inter_Ici_eq {a x t : ℝ} (ht : a < t) : Ioc a x ∩ Ici t = Icc t x := by
  ext s
  simp only [mem_inter_iff, mem_Ioc, mem_Ici, mem_Icc]
  constructor
  · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨by linarith, h2⟩, h1⟩

/-- The inner integral of the semigroup property: for `a < t < x`,
`∫_{(a,x]} 1_{s ≥ t} (x − s)^{α−1} (s − t)^{β−1} c ds = (x − t)^{α+β−1} Γ(α)Γ(β)/Γ(α+β) c`. -/
theorem fracInner {α β : ℂ} (hα : 0 < α.re) (hβ : 0 < β.re) {a x t : ℝ} (ht : t ∈ Ioo a x)
    (c : ℂ) :
    IntegrableOn (fun s => (Ici t).indicator
      (fun s => ((x - s : ℝ) : ℂ) ^ (α - 1) * ((s - t : ℝ) : ℂ) ^ (β - 1) * c) s) (Ioc a x) ∧
    ∫ s in Ioc a x, (Ici t).indicator
      (fun s => ((x - s : ℝ) : ℂ) ^ (α - 1) * ((s - t : ℝ) : ℂ) ^ (β - 1) * c) s =
      ((x - t : ℝ) : ℂ) ^ (α + β - 1) * (Gamma α * Gamma β / Gamma (α + β)) * c := by
  obtain ⟨hi, he⟩ := integral_beta_shift hα hβ ht.2
  have hIcc : IntegrableOn
      (fun s => ((x - s : ℝ) : ℂ) ^ (α - 1) * ((s - t : ℝ) : ℂ) ^ (β - 1) * c) (Icc t x) :=
    (integrableOn_Icc_iff_integrableOn_Ioc (μ := volume)).mpr
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht.2.le).mp (hi.mul_const c))
  constructor
  · rw [IntegrableOn, integrable_indicator_iff measurableSet_Ici, IntegrableOn,
      Measure.restrict_restrict measurableSet_Ici, inter_comm, Ioc_inter_Ici_eq ht.1]
    exact hIcc
  · rw [setIntegral_indicator measurableSet_Ici, Ioc_inter_Ici_eq ht.1,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht.2.le,
      intervalIntegral.integral_mul_const, he]

/-- The real (norm) version of `fracInner`. -/
theorem fracInner_norm {α β : ℂ} (hα : 0 < α.re) (hβ : 0 < β.re) {a x t : ℝ}
    (ht : t ∈ Ioo a x) {r : ℝ} (hr : 0 ≤ r) :
    ∫ s in Ioc a x, (Ici t).indicator
      (fun s => (x - s) ^ (α.re - 1) * (s - t) ^ (β.re - 1) * r) s =
      (x - t) ^ (α.re + β.re - 1) *
        ‖Gamma α.re * Gamma β.re / Gamma ((α.re : ℂ) + β.re)‖ * r := by
  have h := (fracInner (α := α.re) (β := β.re) (by simpa using hα) (by simpa using hβ) ht
    (r : ℂ)).2
  have hcast : ∫ s in Ioc a x, (Ici t).indicator
      (fun s => ((x - s : ℝ) : ℂ) ^ ((α.re : ℂ) - 1) * ((s - t : ℝ) : ℂ) ^ ((β.re : ℂ) - 1) *
        (r : ℂ)) s =
      ((∫ s in Ioc a x, (Ici t).indicator
        (fun s => (x - s) ^ (α.re - 1) * (s - t) ^ (β.re - 1) * r) s : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    by_cases hts : t ≤ s
    · simp only [indicator, mem_Ici, hts, ite_true]
      rw [ofReal_mul, ofReal_mul, ofReal_cpow (by linarith [hs.2]),
        ofReal_cpow (by linarith)]
      push_cast
      ring
    · simp [indicator, mem_Ici, hts]
  rw [hcast] at h
  have hnn : 0 ≤ ∫ s in Ioc a x, (Ici t).indicator
      (fun s => (x - s) ^ (α.re - 1) * (s - t) ^ (β.re - 1) * r) s :=
    setIntegral_nonneg measurableSet_Ioc fun s hs => by
      by_cases hts : t ≤ s
      · simp only [indicator, mem_Ici, hts, ite_true]
        exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith [hs.2]) _)
          (Real.rpow_nonneg (by linarith) _)) hr
      · simp [indicator, hts]
  rw [← Real.norm_of_nonneg hnn, ← Complex.norm_real, h, norm_mul, norm_mul,
    norm_cpow_eq_rpow_re_of_pos (sub_pos.mpr ht.2), Complex.norm_real,
    Real.norm_of_nonneg hr]
  congr 2

/-- **Semigroup property** of fractional integrals with lower limit `a`:
`I_a^α I_a^β f(x) = I_a^{α+β} f(x)` for `ℜα, ℜβ > 0`, `x ≥ a`, `f` integrable on `(a, x]` with
`∫_a^x |f(t)| (x − t)^{ℜα+ℜβ−1} dt < ∞`. -/
theorem fracIntegralFrom_add {α β : ℂ} (hα : 0 < α.re) (hβ : 0 < β.re) {a x : ℝ}
    (hax : a ≤ x) {f : ℝ → ℂ} (hf : IntegrableOn f (Ioc a x))
    (hw : IntegrableOn (fun t => ‖f t‖ * (x - t) ^ (α.re + β.re - 1)) (Ioc a x)) :
    fracIntegralFrom a α (fracIntegralFrom a β f) x = fracIntegralFrom a (α + β) f x := by
  set μ := volume.restrict (Ioc a x)
  set S : Set (ℝ × ℝ) := {q | q.2 ≤ q.1}
  have hS : MeasurableSet S := measurableSet_le measurable_snd measurable_fst
  set G : ℝ × ℝ → ℂ := fun q => ((x - q.1 : ℝ) : ℂ) ^ (α - 1) *
    S.indicator (fun q => ((q.1 - q.2 : ℝ) : ℂ) ^ (β - 1) * f q.2) q with hGdef
  have hGm : AEStronglyMeasurable G (μ.prod μ) :=
    (by fun_prop : Measurable fun q : ℝ × ℝ => ((x - q.1 : ℝ) : ℂ) ^ (α - 1)).aestronglyMeasurable
      |>.mul (((by fun_prop : Measurable fun q : ℝ × ℝ => ((q.1 - q.2 : ℝ) : ℂ) ^ (β - 1))
        |>.aestronglyMeasurable.mul hf.1.comp_snd).indicator hS)
  have hae : ∀ᵐ t ∂μ, t ∈ Ioo a x := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioc : MeasurableSet (Ioc a x)),
      ae_restrict_of_ae ((countable_singleton x).ae_notMem volume)] with t h1 h2
    exact ⟨h1.1, lt_of_le_of_ne h1.2 fun h => h2 (by rw [h]; rfl)⟩
  have hGs : ∀ t ∈ Ioo a x, (fun s => G (s, t)) = fun s => (Ici t).indicator
      (fun s => ((x - s : ℝ) : ℂ) ^ (α - 1) * ((s - t : ℝ) : ℂ) ^ (β - 1) * f t) s :=
    fun t _ => funext fun s => by
      by_cases hts : t ≤ s
      · simp [hGdef, S, indicator, hts, mul_assoc]
      · simp [hGdef, S, indicator, hts]
  have hGi : Integrable G (μ.prod μ) := by
    rw [integrable_prod_iff' hGm]
    refine ⟨?_, ?_⟩
    · filter_upwards [hae] with t ht
      rw [hGs t ht]
      exact (fracInner hα hβ ht (f t)).1
    · refine (hw.mul_const ‖Gamma α.re * Gamma β.re / Gamma ((α.re : ℂ) + β.re)‖).congr ?_
      filter_upwards [hae] with t ht
      have hn : ∀ᵐ s ∂μ, ‖G (s, t)‖ = (Ici t).indicator
          (fun s => (x - s) ^ (α.re - 1) * (s - t) ^ (β.re - 1) * ‖f t‖) s := by
        filter_upwards [ae_restrict_mem (measurableSet_Ioc : MeasurableSet (Ioc a x)),
          ae_restrict_of_ae ((countable_singleton x).ae_notMem volume),
          ae_restrict_of_ae ((countable_singleton t).ae_notMem volume)] with s hs hsx hst
        rw [congrFun (hGs t ht) s]
        by_cases hts : t ≤ s
        · have h1 : 0 < x - s := sub_pos.mpr (lt_of_le_of_ne hs.2 fun h => hsx (by rw [h]; rfl))
          have h2 : 0 < s - t := sub_pos.mpr (lt_of_le_of_ne hts fun h => hst (by rw [h]; rfl))
          simp only [indicator, mem_Ici, hts, ite_true]
          rw [norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos h1,
            norm_cpow_eq_rpow_re_of_pos h2]
          simp
        · simp [indicator, hts]
      rw [integral_congr_ae hn, fracInner_norm hα hβ ht (norm_nonneg _)]
      ring
  -- the left-hand side as an iterated integral
  have hL : fracIntegralFrom a α (fracIntegralFrom a β f) x =
      (Gamma α)⁻¹ * ((Gamma β)⁻¹ * ∫ s, ∫ t, G (s, t) ∂μ ∂μ) := by
    rw [fracIntegralFrom, intervalIntegral.integral_of_le hax]
    congr 1
    rw [← integral_const_mul]
    refine setIntegral_congr_fun (measurableSet_Ioc : MeasurableSet (Ioc a x)) fun s hs => ?_
    simp only [fracIntegralFrom]
    have hi : ∫ t, G (s, t) ∂μ = ((x - s : ℝ) : ℂ) ^ (α - 1) *
        ∫ t in a..s, ((s - t : ℝ) : ℂ) ^ (β - 1) * f t := by
      simp only [hGdef]
      rw [integral_const_mul]
      congr 1
      have : (fun t => S.indicator (fun q => ((q.1 - q.2 : ℝ) : ℂ) ^ (β - 1) * f q.2) (s, t)) =
          (Iic s).indicator fun t => ((s - t : ℝ) : ℂ) ^ (β - 1) * f t := by
        funext t; simp [S, indicator]
      have hset : Ioc a x ∩ Iic s = Ioc a s := by
        ext t
        simp only [mem_inter_iff, mem_Ioc, mem_Iic]
        constructor
        · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.trans hs.2⟩, h2⟩
      rw [this, setIntegral_indicator measurableSet_Iic, hset,
        intervalIntegral.integral_of_le hs.1.le]
    rw [hi]
    ring
  have hR : ∫ t, ∫ s, G (s, t) ∂μ ∂μ =
      (Gamma α * Gamma β / Gamma (α + β)) *
        ∫ t in a..x, ((x - t : ℝ) : ℂ) ^ (α + β - 1) * f t := by
    rw [intervalIntegral.integral_of_le hax, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hae] with t ht
    rw [hGs t ht, (fracInner hα hβ ht (f t)).2]
    ring
  rw [hL, integral_integral_swap (f := fun s t => G (s, t)) hGi, hR, fracIntegralFrom]
  have hGa : Gamma α ≠ 0 := Gamma_ne_zero_of_re_pos hα
  have hGb : Gamma β ≠ 0 := Gamma_ne_zero_of_re_pos hβ
  have hGab : Gamma (α + β) ≠ 0 := Gamma_ne_zero_of_re_pos (by rw [add_re]; linarith)
  field_simp

theorem integrableOn_sub_rpow {a x r : ℝ} (hax : a ≤ x) (hr : -1 < r) :
    IntegrableOn (fun t => (x - t) ^ r) (Ioc a x) := by
  have h := (intervalIntegral.intervalIntegrable_rpow' (a := x - a) (b := 0) hr).comp_sub_left x
  rw [sub_sub_cancel, sub_zero] at h
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hax).mp h

/-- The semigroup property for `f` continuous on `[a, x]`. -/
theorem fracIntegralFrom_add_of_continuousOn {α β : ℂ} (hα : 0 < α.re) (hβ : 0 < β.re)
    {a x : ℝ} (hax : a ≤ x) {f : ℝ → ℂ} (hc : ContinuousOn f (Icc a x)) :
    fracIntegralFrom a α (fracIntegralFrom a β f) x = fracIntegralFrom a (α + β) f x := by
  have hf : IntegrableOn f (Ioc a x) := (hc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  have hw := integrableOn_sub_rpow hax (r := α.re + β.re - 1) (by linarith)
  refine fracIntegralFrom_add hα hβ hax hf ((hw.const_mul C).mono' ?_ ?_)
  · exact hf.1.norm.mul ((by fun_prop : Measurable fun t : ℝ => (x - t) ^ (α.re + β.re - 1))
      |>.aestronglyMeasurable)
  · filter_upwards [ae_restrict_mem (measurableSet_Ioc : MeasurableSet (Ioc a x))] with t ht
    have h0 : 0 ≤ (x - t) ^ (α.re + β.re - 1) := Real.rpow_nonneg (by linarith [ht.2]) _
    rw [norm_mul, norm_norm, Real.norm_of_nonneg h0]
    exact mul_le_mul_of_nonneg_right (hC t (Ioc_subset_Icc_self ht)) h0

/-- DLMF 1.15.48: `I^α I^β = I^{α+β}` for `ℜα, ℜβ > 0`, on `[0, ∞)`, for `f` continuous on
`[0, ∞)`. The general form with lower limit `a` and only a weighted integrability hypothesis is
`fracIntegralFrom_add`. -/
theorem dlmf_1_15_48 {α β : ℂ} (hα : 0 < α.re) (hβ : 0 < β.re) {f : ℝ → ℂ}
    (hc : ContinuousOn f (Ici 0)) {x : ℝ} (hx : 0 ≤ x) :
    fracIntegral α (fracIntegral β f) x = fracIntegral (α + β) f x :=
  fracIntegralFrom_add_of_continuousOn hα hβ hx (hc.mono Icc_subset_Ici_self)

/-- Comparison with 1.4.31: for a positive integer order `n + 1`, the fractional integral is the
`(n + 1)`-fold repeated integral. -/
theorem fracIntegralFrom_natCast {f : ℝ → ℝ} (hf : Continuous f) (a b : ℝ) (n : ℕ) :
    fracIntegralFrom a ((n : ℂ) + 1) (fun t => (f t : ℂ)) b = repeatedIntegral a n f b := by
  rw [dlmf_1_4_31 hf, fracIntegralFrom, Complex.Gamma_nat_eq_factorial, add_sub_cancel_right]
  have e : ∫ t in a..b, ((b - t : ℝ) : ℂ) ^ (n : ℂ) * (f t : ℂ) =
      ((∫ t in a..b, (b - t) ^ n * f t : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [cpow_natCast]
    push_cast
    ring
  rw [e]
  push_cast
  ring

/-! ### Power series (1.15.49–1.15.50) -/

/-- `I^α t^k = k!/Γ(k + α + 1) x^{k+α}`. -/
theorem fracIntegral_pow {α : ℂ} (hα : 0 < α.re) (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    fracIntegral α (fun t => (t : ℂ) ^ k) x =
      k ! / Gamma (k + α + 1) * (x : ℂ) ^ ((k : ℂ) + α) := by
  have hkα : (k : ℂ) + α ≠ 0 := fun h => by
    have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  rcases hx.eq_or_lt with rfl | hx
  · simp [fracIntegral, fracIntegralFrom, zero_cpow hkα]
  have hk : 0 < ((k : ℂ) + 1).re := by simp; positivity
  have h := (integral_beta_shift hα hk hx).2
  simp only [sub_zero, add_sub_cancel_right] at h
  rw [fracIntegral, fracIntegralFrom]
  have e : ∫ t in (0 : ℝ)..x, ((x - t : ℝ) : ℂ) ^ (α - 1) * (t : ℂ) ^ k =
      ∫ s in (0 : ℝ)..x, ((x - s : ℝ) : ℂ) ^ (α - 1) * (s : ℂ) ^ (k : ℂ) := by
    simp only [cpow_natCast]
  rw [e, h, Complex.Gamma_nat_eq_factorial,
    show α + ((k : ℂ) + 1) - 1 = (k : ℂ) + α by ring,
    show α + ((k : ℂ) + 1) = (k : ℂ) + α + 1 by ring]
  have hGa : Gamma α ≠ 0 := Gamma_ne_zero_of_re_pos hα
  field_simp

/-- DLMF 1.15.49–1.15.50: if `f(x) = ∑ aₖ xᵏ` with `∑ |aₖ| xᵏ < ∞`, then
`I^α f(x) = ∑ k!/Γ(k + α + 1) aₖ x^{k+α}`. -/
theorem dlmf_1_15_50 {α : ℂ} (hα : 0 < α.re) {a : ℕ → ℂ} {x : ℝ} (hx : 0 ≤ x)
    (hs : Summable fun k => ‖a k‖ * x ^ k) :
    HasSum (fun k => k ! / Gamma (k + α + 1) * a k * (x : ℂ) ^ ((k : ℂ) + α))
      (fracIntegral α (fun t => ∑' k, a k * (t : ℂ) ^ k) x) := by
  have hker : IntervalIntegrable (fun t : ℝ => ((x - t : ℝ) : ℂ) ^ (α - 1)) volume 0 x := by
    rcases hx.eq_or_lt with rfl | hx'
    · exact IntervalIntegrable.refl
    have h := (integral_beta_shift hα (β := 1) (by simp) hx').1
    simpa using h
  have hmem : ∀ t ∈ uIoc (0 : ℝ) x, 0 ≤ t ∧ t ≤ x := fun t ht => by
    rw [uIoc_of_le hx] at ht; exact ⟨ht.1.le, ht.2⟩
  have hsum : ∀ t ∈ uIoc (0 : ℝ) x, Summable fun k => a k * (t : ℂ) ^ k := fun t ht =>
    Summable.of_norm_bounded hs fun k => by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (hmem t ht).1]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hmem t ht).1 (hmem t ht).2 k)
        (norm_nonneg _)
  have h := intervalIntegral.hasSum_integral_of_dominated_convergence (a := 0) (b := x)
    (μ := volume) (F := fun k t => ((x - t : ℝ) : ℂ) ^ (α - 1) * (a k * (t : ℂ) ^ k))
    (f := fun t => ((x - t : ℝ) : ℂ) ^ (α - 1) * ∑' k, a k * (t : ℂ) ^ k)
    (fun k t => ‖((x - t : ℝ) : ℂ) ^ (α - 1)‖ * (‖a k‖ * x ^ k))
    (fun k => (by fun_prop : Measurable fun t : ℝ =>
      ((x - t : ℝ) : ℂ) ^ (α - 1) * (a k * (t : ℂ) ^ k)).aestronglyMeasurable)
    (fun k => ae_of_all _ fun t ht => by
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (hmem t ht).1]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (hmem t ht).1 (hmem t ht).2 k) (norm_nonneg _)) (norm_nonneg _))
    (ae_of_all _ fun t _ => hs.mul_left _)
    (by simpa only [tsum_mul_left] using hker.norm.mul_const (∑' k, ‖a k‖ * x ^ k))
    (ae_of_all _ fun t ht => (hsum t ht).hasSum.mul_left _)
  have h2 := h.mul_left (Gamma α)⁻¹
  convert h2 using 1
  swap
  · rfl
  funext k
  have e : ∫ t in (0 : ℝ)..x, ((x - t : ℝ) : ℂ) ^ (α - 1) * (a k * (t : ℂ) ^ k) =
      a k * ∫ t in (0 : ℝ)..x, ((x - t : ℝ) : ℂ) ^ (α - 1) * (t : ℂ) ^ k := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    ring
  have hp := fracIntegral_pow hα k hx
  rw [fracIntegral, fracIntegralFrom] at hp
  rw [e]
  linear_combination (-a k) * hp

/-! ### Other limits of integration -/

/-- The fractional integral with upper limit `a ≥ x`:
`(1/Γ(α)) ∫_x^a (t − x)^{α−1} f(t) dt`. -/
noncomputable def fracIntegralTo (a : ℝ) (α : ℂ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (Gamma α)⁻¹ * ∫ t in x..a, ((t - x : ℝ) : ℂ) ^ (α - 1) * f t

/-- The upper-limit variant with `a = ∞` (Weyl): `(1/Γ(α)) ∫_x^∞ (t − x)^{α−1} f(t) dt`. -/
noncomputable def fracIntegralWeyl (α : ℂ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (Gamma α)⁻¹ * ∫ t in Ioi x, ((t - x : ℝ) : ℂ) ^ (α - 1) * f t

/-- Reflection: the upper-limit fractional integral is the lower-limit one of `f(−t)`. -/
theorem fracIntegralTo_eq (a : ℝ) (α : ℂ) (f : ℝ → ℂ) (x : ℝ) :
    fracIntegralTo a α f x = fracIntegralFrom (-a) α (fun t => f (-t)) (-x) := by
  rw [fracIntegralTo, fracIntegralFrom]
  congr 1
  have h := intervalIntegral.integral_comp_neg (a := x) (b := a)
    (fun u => ((-x - u : ℝ) : ℂ) ^ (α - 1) * f (-u))
  simp only [neg_neg, sub_neg_eq_add] at h
  rw [← h]
  refine intervalIntegral.integral_congr fun t _ => ?_
  congr 2
  push_cast
  ring

/-- The semigroup property for the upper-limit variant, for `f` continuous on `[x, a]`. -/
theorem fracIntegralTo_add {α β : ℂ} (hα : 0 < α.re) (hβ : 0 < β.re) {a x : ℝ} (hxa : x ≤ a)
    {f : ℝ → ℂ} (hc : ContinuousOn f (Icc x a)) :
    fracIntegralTo a α (fracIntegralTo a β f) x = fracIntegralTo a (α + β) f x := by
  have hfun : (fun s => fracIntegralTo a β f (-s)) = fracIntegralFrom (-a) β fun t => f (-t) :=
    funext fun s => by rw [fracIntegralTo_eq, neg_neg]
  rw [fracIntegralTo_eq, hfun, fracIntegralTo_eq]
  refine fracIntegralFrom_add_of_continuousOn hα hβ (neg_le_neg hxa) ?_
  exact hc.comp continuousOn_neg fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩

/-- The case `a = ∞`: when the Weyl integrand is integrable, the upper-limit fractional integrals
converge to the Weyl fractional integral as `a → ∞`. -/
theorem tendsto_fracIntegralTo_atTop {α : ℂ} {f : ℝ → ℂ} {x : ℝ}
    (h : IntegrableOn (fun t => ((t - x : ℝ) : ℂ) ^ (α - 1) * f t) (Ioi x)) :
    Tendsto (fun a => fracIntegralTo a α f x) atTop (𝓝 (fracIntegralWeyl α f x)) :=
  (intervalIntegral_tendsto_integral_Ioi x h tendsto_id).const_mul _

end Azurite.DLMF
