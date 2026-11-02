/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section8
import Azurite.DLMF.Chapter2.Section7Series
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# DLMF §2.8(i): property (a) — `ξ` and `z` are analytic functions of each other

DLMF requires of the Liouville transformation that "(a) `ξ` and `z` are analytic functions of each
other at the transition point (if any)". For the choices 2.8.5–2.8.7, written in the `z`-form
(`ż = 1/ξ′(z)`):

* Case I (`dlmf_2_8_i_caseI`): if `f(z₀) ≠ 0`, there is `ξ` analytic at `z₀` with `ξ(z₀) = 0`,
  `ξ′(z₀) ≠ 0` and `ξ′² = f` (2.8.5, `ż² f = 1`).
* Case II (`dlmf_2_8_i_caseII`): at a simple zero of `f`, there is `ξ` analytic at `z₀` with
  `ξ(z₀) = 0`, `ξ′(z₀) ≠ 0` and `ξ ξ′² = f` (2.8.6, `ż² f = ξ`).
* Case III (`dlmf_2_8_i_caseIII`): at a simple pole of `f`, there is `ξ` analytic at `z₀` with
  `ξ(z₀) = 0`, `ξ′(z₀) ≠ 0` and `ξ′² = ξ f` near `z₀` (2.8.7, `ż² f = 1/ξ`).

In each case the inverse `z(ξ)` is analytic at `ξ = ξ(z₀)` (`exists_analytic_inverse`, from the
analytic inverse function theorem). The constructions: analytic roots of nonvanishing functions
(`exists_analytic_root`), and power-series solutions of `(z − z₀) K′ + a K = k` (`exists_euler_ode`,
coefficients `kₙ/(n + a)`), for `a = 1, 3/2, 1/2`, which realize `∫_{z₀}^{z} f^{1/2}` up to the
branch factor.
-/

open Filter Topology Set Complex Metric

namespace Azurite.DLMF

/-! ### Tools -/

/-- An analytic `n`-th root of a function analytic and nonvanishing at `z₀`. -/
theorem exists_analytic_root {h : ℂ → ℂ} {z₀ : ℂ} (hh : AnalyticAt ℂ h z₀) (h0 : h z₀ ≠ 0)
    {n : ℕ} (hn : n ≠ 0) : ∃ k : ℂ → ℂ, AnalyticAt ℂ k z₀ ∧ k z₀ ≠ 0 ∧ ∀ z, k z ^ n = h z := by
  refine ⟨fun z => h z₀ ^ ((n : ℂ)⁻¹) * (h z / h z₀) ^ ((n : ℂ)⁻¹), ?_, ?_, fun z => ?_⟩
  · refine analyticAt_const.mul
      ((hh.div_const : AnalyticAt ℂ (fun z => h z / h z₀) z₀).cpow analyticAt_const ?_)
    rw [div_self h0]
    exact one_mem_slitPlane
  · show h z₀ ^ ((n : ℂ)⁻¹) * (h z₀ / h z₀) ^ ((n : ℂ)⁻¹) ≠ 0
    rw [div_self h0, one_cpow, mul_one, Ne, cpow_eq_zero_iff]
    exact fun h => h0 h.1
  · show (h z₀ ^ ((n : ℂ)⁻¹) * (h z / h z₀) ^ ((n : ℂ)⁻¹)) ^ n = h z
    rw [mul_pow, cpow_nat_inv_pow _ hn, cpow_nat_inv_pow _ hn]
    field_simp

/-- A power series with radius `R` is analytic at its centre. -/
theorem HasRadiusGE.analyticAt_center {c : ℕ → ℂ} {R : ℝ} (h : HasRadiusGE c R) (hR : 0 < R)
    (z₀ : ℂ) : AnalyticAt ℂ (powerSeriesSum c z₀) z₀ :=
  DifferentiableOn.analyticAt (s := ball z₀ R)
    (fun _ hz => (h.hasDerivAt hz).differentiableAt.differentiableWithinAt)
    (isOpen_ball.mem_nhds (mem_ball_self hR))

/-- For `k` analytic at `z₀` and `ℜa > 0`, the equation `(z − z₀) K′ + a K = k` has an analytic
solution with `K(z₀) = k(z₀)/a` (coefficients `kₙ/(n + a)`). -/
theorem exists_euler_ode {k : ℂ → ℂ} {z₀ a : ℂ} (hk : AnalyticAt ℂ k z₀) (ha : 0 < a.re) :
    ∃ K : ℂ → ℂ, AnalyticAt ℂ K z₀ ∧ K z₀ = k z₀ / a ∧
      ∀ᶠ z in 𝓝 z₀, (z - z₀) * deriv K z + a * K z = k z := by
  obtain ⟨R, hR, c, hcs, hck⟩ := exists_summable_tsum_of_analyticAt hk
  have hc : HasRadiusGE c R := hasRadiusGE_of_summable hcs
  have hna : ∀ n : ℕ, a.re ≤ ‖(n : ℂ) + a‖ := fun n => by
    refine le_trans ?_ (re_le_norm _)
    simp
  set d : ℕ → ℂ := fun n => c n / ((n : ℂ) + a) with hd_def
  have hnz : ∀ n : ℕ, (n : ℂ) + a ≠ 0 := fun n h => by
    have := hna n; rw [h, norm_zero] at this; linarith
  have hd : HasRadiusGE d R := by
    intro ρ hρ hρR
    obtain ⟨K, hK⟩ := hc ρ hρ hρR
    refine ⟨K / a.re, fun s => ?_⟩
    rw [hd_def, norm_div, div_mul_eq_mul_div, le_div_iff₀ ha]
    calc ‖c s‖ * ρ ^ s / ‖(s : ℂ) + a‖ * a.re ≤ ‖c s‖ * ρ ^ s / a.re * a.re := by
          gcongr
          · exact hna s
      _ = ‖c s‖ * ρ ^ s := by field_simp
      _ ≤ K := hK s
  refine ⟨powerSeriesSum d z₀, hd.analyticAt_center hR z₀, ?_, ?_⟩
  · rw [powerSeriesSum_self, hck z₀ (mem_ball_self hR)]
    simp only [sub_self, hd_def]
    rw [tsum_eq_single 0 fun s hs => by simp [hs]]
    simp
  · filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hR)] with z hz
    rw [(hd.hasDerivAt hz).deriv]
    have h1 := hd.hasSum_natCast_mul hz
    have h2 := ((hd.summable hz).hasSum).mul_left a
    have h3 : HasSum (fun n => c n * (z - z₀) ^ n) (k z) := by
      rw [hck z hz]; exact (hcs z hz).of_norm.hasSum
    refine (h1.add h2).unique (h3.congr_fun fun n => ?_)
    simp only [hd_def]
    field_simp [hnz n]

/-- At `z₀` with `f(z₀) = 0`, `f(z) = (z − z₀) h(z)` with `h` analytic, `h(z₀) = f′(z₀)`. -/
theorem exists_factor_of_zero {f : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀) (h0 : f z₀ = 0) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h z₀ ∧ h z₀ = deriv f z₀ ∧ ∀ z, f z = (z - z₀) * h z := by
  obtain ⟨p, hp⟩ := hf
  refine ⟨dslope f z₀, hp.has_fpower_series_dslope_fslope.analyticAt, dslope_same f z₀,
    fun z => ?_⟩
  have := sub_smul_dslope f z₀ z
  rw [h0, sub_zero, smul_eq_mul] at this
  exact this.symm

/-- The analytic inverse function: if `ξ` is analytic at `z₀` with `ξ′(z₀) ≠ 0`, then `z` is an
analytic function of `ξ` near `ξ(z₀)`. -/
theorem exists_analytic_inverse {ξ : ℂ → ℂ} {z₀ : ℂ} (hξ : AnalyticAt ℂ ξ z₀)
    (hd : deriv ξ z₀ ≠ 0) :
    ∃ Z : ℂ → ℂ, AnalyticAt ℂ Z (ξ z₀) ∧ Z (ξ z₀) = z₀ ∧ (∀ᶠ z in 𝓝 z₀, Z (ξ z) = z) ∧
      ∀ᶠ ζ in 𝓝 (ξ z₀), ξ (Z ζ) = ζ :=
  ⟨_, hξ.analyticAt_localInverse hd,
    (hξ.hasStrictDerivAt.eventually_left_inverse hd).self_of_nhds,
    hξ.hasStrictDerivAt.eventually_left_inverse hd,
    hξ.hasStrictDerivAt.eventually_right_inverse hd⟩

theorem hasDerivAt_sub_mul {M : ℂ → ℂ} {z z₀ : ℂ} (hM : DifferentiableAt ℂ M z) :
    HasDerivAt (fun z => (z - z₀) * M z) (M z + (z - z₀) * deriv M z) z := by
  exact (((hasDerivAt_id z).sub_const z₀).mul hM.hasDerivAt).congr_deriv (by simp)

/-! ### Case I -/

/-- **DLMF §2.8(i)(a)**, Case I: if `f` is analytic with `f(z₀) ≠ 0`, `ξ = ∫_{z₀}^{z} f^{1/2}` is
analytic at `z₀`, `ξ′² = f` (2.8.5), `ξ′(z₀) ≠ 0`, and `z` is an analytic function of `ξ`. -/
theorem dlmf_2_8_i_caseI {f : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀) (h0 : f z₀ ≠ 0) :
    ∃ ξ : ℂ → ℂ, AnalyticAt ℂ ξ z₀ ∧ ξ z₀ = 0 ∧ deriv ξ z₀ ≠ 0 ∧
      (∀ᶠ z in 𝓝 z₀, deriv ξ z ^ 2 = f z) ∧
      ∃ Z : ℂ → ℂ, AnalyticAt ℂ Z 0 ∧ Z 0 = z₀ ∧ ∀ᶠ z in 𝓝 z₀, Z (ξ z) = z := by
  obtain ⟨k, hk, hk0, hkf⟩ := exists_analytic_root hf h0 two_ne_zero
  obtain ⟨M, hM, hM0, hMe⟩ := exists_euler_ode (a := 1) hk (by norm_num)
  have hξa : AnalyticAt ℂ (fun z => (z - z₀) * M z) z₀ :=
    (analyticAt_id.sub analyticAt_const).mul hM
  have hderiv : ∀ᶠ z in 𝓝 z₀, deriv (fun z => (z - z₀) * M z) z = k z := by
    filter_upwards [hMe, hM.eventually_analyticAt] with z hz hza
    rw [(hasDerivAt_sub_mul hza.differentiableAt).deriv]
    linear_combination hz
  have hd0 : deriv (fun z => (z - z₀) * M z) z₀ ≠ 0 := by
    rw [hderiv.self_of_nhds]; exact hk0
  obtain ⟨Z, hZ, hZ0, hZl, -⟩ := exists_analytic_inverse hξa hd0
  refine ⟨_, hξa, by simp, hd0, hderiv.mono fun z hz => by rw [hz, hkf], Z, ?_, ?_, hZl⟩
  · simpa using hZ
  · simpa using hZ0

/-! ### Case II -/

/-- **DLMF §2.8(i)(a)**, Case II: at a simple zero `z₀` of `f`, the variable `ξ` of 2.8.6
(`⅔ ξ^{3/2} = ∫_{z₀}^{z} f^{1/2}`) is analytic at `z₀`, with `ξ(z₀) = 0`, `ξ′(z₀) ≠ 0` and
`ξ ξ′² = f` (that is, `ż² f = ξ`), and `z` is an analytic function of `ξ`. -/
theorem dlmf_2_8_i_caseII {f g : ℂ → ℂ} {z₀ : ℂ} (hc : IsCaseII f g z₀) :
    ∃ ξ : ℂ → ℂ, AnalyticAt ℂ ξ z₀ ∧ ξ z₀ = 0 ∧ deriv ξ z₀ ≠ 0 ∧
      (∀ᶠ z in 𝓝 z₀, ξ z * deriv ξ z ^ 2 = f z) ∧
      ∃ Z : ℂ → ℂ, AnalyticAt ℂ Z 0 ∧ Z 0 = z₀ ∧ ∀ᶠ z in 𝓝 z₀, Z (ξ z) = z := by
  obtain ⟨hf, hf0, hf', -⟩ := hc
  obtain ⟨h, hh, hh0, hfh⟩ := exists_factor_of_zero hf hf0
  rw [← hh0] at hf'
  obtain ⟨k, hk, hk0, hkh⟩ := exists_analytic_root hh hf' two_ne_zero
  obtain ⟨K, hK, hK0, hKe⟩ := exists_euler_ode (a := 3 / 2) hk (by norm_num)
  have hKz : K z₀ ≠ 0 := by rw [hK0]; exact div_ne_zero hk0 (by norm_num)
  obtain ⟨L, hL, hL0, hLK⟩ := exists_analytic_root (h := fun z => 9 / 4 * K z ^ 2)
    ((analyticAt_const (v := (9 / 4 : ℂ))).mul (hK.pow 2))
    (mul_ne_zero (by norm_num) (pow_ne_zero 2 hKz)) (n := 3) (by norm_num)
  have hξa : AnalyticAt ℂ (fun z => (z - z₀) * L z) z₀ :=
    (analyticAt_id.sub analyticAt_const).mul hL
  -- `3 L² L′ = (9/2) K K′`, from `L³ = (9/4) K²` everywhere
  have hL3 : (fun z => L z ^ 3) = fun z => 9 / 4 * K z ^ 2 := funext hLK
  have hderiv : ∀ᶠ z in 𝓝 z₀, deriv (fun z => (z - z₀) * L z) z = L z + (z - z₀) * deriv L z :=
    hL.eventually_analyticAt.mono fun z hz => (hasDerivAt_sub_mul hz.differentiableAt).deriv
  have hLne : ∀ᶠ z in 𝓝 z₀, L z ≠ 0 := hL.continuousAt.eventually_ne hL0
  have hd0 : deriv (fun z => (z - z₀) * L z) z₀ ≠ 0 := by
    rw [hderiv.self_of_nhds, sub_self, zero_mul, add_zero]; exact hL0
  obtain ⟨Z, hZ, hZ0, hZl, -⟩ := exists_analytic_inverse hξa hd0
  refine ⟨_, hξa, by simp, hd0, ?_, Z, by simpa using hZ, by simpa using hZ0, hZl⟩
  filter_upwards [hKe, hderiv, hLne, hL.eventually_analyticAt, hK.eventually_analyticAt] with
    z e3 hdz hLz hLa hKa
  have e2 : 3 * L z ^ 2 * deriv L z = 9 / 2 * K z * deriv K z := by
    have hl1 : HasDerivAt (fun z => L z ^ 3) (3 * L z ^ 2 * deriv L z) z :=
      ((hLa.differentiableAt.hasDerivAt).pow 3).congr_deriv (by norm_num)
    have hl2 : HasDerivAt (fun z => 9 / 4 * K z ^ 2) (9 / 2 * K z * deriv K z) z :=
      (((hKa.differentiableAt.hasDerivAt).pow 2).const_mul (9 / 4 : ℂ)).congr_deriv
        (by norm_num; ring)
    have : deriv (fun z => L z ^ 3) z = deriv (fun z => 9 / 4 * K z ^ 2) z := by rw [hL3]
    rw [hl1.deriv, hl2.deriv] at this
    exact this
  have e1 := hLK z
  have e4 := hkh z
  rw [hdz, hfh z, ← e4]
  set D := z - z₀
  have hP : L z ^ 2 * (L z + D * deriv L z) = 3 / 2 * K z * k z := by
    linear_combination e1 + D / 3 * e2 + 3 / 2 * K z * e3
  have hcube : L z ^ 3 * (D * L z * (L z + D * deriv L z) ^ 2 - D * k z ^ 2) = 0 := by
    linear_combination D * (L z ^ 2 * (L z + D * deriv L z) + 3 / 2 * K z * k z) * hP -
      D * k z ^ 2 * e1
  have := (mul_eq_zero.mp hcube).resolve_left (pow_ne_zero 3 hLz)
  linear_combination this

/-! ### Case III -/

/-- **DLMF §2.8(i)(a)**, Case III: at a simple pole `z₀` of `f`, the variable `ξ` of 2.8.7
(`2 ξ^{1/2} = ∫_{z₀}^{z} f^{1/2}`) is analytic at `z₀`, with `ξ(z₀) = 0`, `ξ′(z₀) ≠ 0` and
`ξ′² = ξ f` near `z₀` (that is, `ż² f = 1/ξ`), and `z` is an analytic function of `ξ`. -/
theorem dlmf_2_8_i_caseIII {f g : ℂ → ℂ} {z₀ : ℂ} (hc : IsCaseIII f g z₀) :
    ∃ ξ : ℂ → ℂ, AnalyticAt ℂ ξ z₀ ∧ ξ z₀ = 0 ∧ deriv ξ z₀ ≠ 0 ∧
      (∀ᶠ z in 𝓝[≠] z₀, deriv ξ z ^ 2 = ξ z * f z) ∧
      ∃ Z : ℂ → ℂ, AnalyticAt ℂ Z 0 ∧ Z 0 = z₀ ∧ ∀ᶠ z in 𝓝 z₀, Z (ξ z) = z := by
  obtain ⟨⟨h, hh, hh0, hfh⟩, -⟩ := hc
  obtain ⟨k, hk, hk0, hkh⟩ := exists_analytic_root hh hh0 two_ne_zero
  obtain ⟨K, hK, hK0, hKe⟩ := exists_euler_ode (a := 1 / 2)
    (hk.div_const : AnalyticAt ℂ (fun z => k z / 2) z₀) (by norm_num)
  have hKz : K z₀ = k z₀ := by rw [hK0]; field_simp
  have hξa : AnalyticAt ℂ (fun z => (z - z₀) * K z ^ 2) z₀ :=
    (analyticAt_id.sub analyticAt_const).mul (hK.pow 2)
  have hderiv : ∀ᶠ z in 𝓝 z₀, deriv (fun z => (z - z₀) * K z ^ 2) z = K z * k z := by
    filter_upwards [hKe, hK.eventually_analyticAt] with z e3 hKa
    have hK2 : HasDerivAt (fun z => K z ^ 2) (2 * K z * deriv K z) z :=
      ((hKa.differentiableAt.hasDerivAt).pow 2).congr_deriv (by norm_num)
    rw [(hasDerivAt_sub_mul hK2.differentiableAt).deriv, hK2.deriv]
    linear_combination 2 * K z * e3
  have hd0 : deriv (fun z => (z - z₀) * K z ^ 2) z₀ ≠ 0 := by
    rw [hderiv.self_of_nhds, hKz, ← sq, hkh]; exact hh0
  obtain ⟨Z, hZ, hZ0, hZl, -⟩ := exists_analytic_inverse hξa hd0
  refine ⟨_, hξa, by simp, hd0, ?_, Z, by simpa using hZ, by simpa using hZ0, hZl⟩
  filter_upwards [hfh, nhdsWithin_le_nhds hderiv, self_mem_nhdsWithin] with z hfz hdz hz
  have hD : z - z₀ ≠ 0 := sub_ne_zero.mpr hz
  rw [hdz, hfz, ← hkh z]
  field_simp

end Azurite.DLMF
