/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section11Stirling
import Azurite.DLMF.Chapter5.Section9Boyd
import Azurite.BrentZimmermann.Chapter4.Exercises
import Azurite.DLMF.Chapter3.Section5Romberg

/-!
# DLMF §5.11(i): Stirling's formula (5.11.3–5.11.4)

Formalization of <https://dlmf.nist.gov/5.11>, equations 5.11.3 and 5.11.4: as `z → ∞` in
`|ph z| ≤ π − δ`,
`Γ(z) = e^{−z} z^z (2π/z)^{1/2} Γ*(z) ∼ e^{−z} z^z (2π/z)^{1/2} ∑_{k≥0} gₖ/zᵏ`,
`g₀ = 1`, `g₁ = 1/12`, `g₂ = 1/288`, `g₃ = −139/51840`, `g₄ = −571/2488320`,
`g₅ = 163879/209018880`, `g₆ = 5246819/75246796800`.

* `Γ*` is `scaledGamma` (§5.9(i)); `Γ*(z) = e^{J(z)}` on the slit plane
  (`scaledGamma_eq_exp_stirlingJ`)
  and the factorization `Γ(z) = e^{−z} z^z (2π/z)^{1/2} Γ*(z)` holds there (`dlmf_5_11_3_eq`).
* The exponential of an asymptotic expansion without constant term is an asymptotic expansion
  whose coefficients are the formal exponential `BZ.seriesExp` (Brent–Zimmermann, Exercise 4.42:
  `b₀ = 1`, `k bₖ = ∑ j aⱼ b_{k−j}`) of the coefficients (`isAsympExpansion_cexp`): with the
  truncations `P`, `E` of both series, `E′ − P′E` vanishes to order `N − 1` at `0`
  (`X_pow_dvd_trunc`), so `F = e^{−P} E` has `F(w) − 1 = O(w^N)` by the mean value inequality
  (`norm_cexp_trunc_sub_le`).
* 5.11.3 (`dlmf_5_11_3`): `Γ* ∼ ∑ gₖ z^{−k}` with `gₖ = BZ.stirlingCoeff k` (the formal exponential
  of Stirling's series 5.11.1), and `Γ* → 1` (`tendsto_scaledGamma`).
* 5.11.4 (`dlmf_5_11_4`): the seven values.
-/

open Complex Filter Topology Set MeasureTheory Polynomial
open scoped Real

namespace Azurite.DLMF

/-! ### `Γ*` on the slit plane -/

/-- `Γ*(z) = e^{J(z)}` on the slit plane. -/
theorem scaledGamma_eq_exp_stirlingJ {z : ℂ} (hz : z ∈ slitPlane) :
    scaledGamma z = cexp (stirlingJ z) := by
  have hz0 := slitPlane_ne_zero hz
  rw [scaledGamma, Gamma_eq_exp_stirlingJ hz, sqrt_two_pi_eq_exp, cpow_def_of_ne_zero hz0,
    ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_sub]
  congr 1
  ring

/-- **DLMF 5.11.3** (the factorization): `Γ(z) = e^{−z} z^z (2π/z)^{1/2} Γ*(z)` on the slit
plane. -/
theorem dlmf_5_11_3_eq {z : ℂ} (hz : z ∈ slitPlane) :
    Gamma z = cexp (-z) * z ^ z * (2 * π / z) ^ (1 / 2 : ℂ) * scaledGamma z := by
  have hz0 := slitPlane_ne_zero hz
  have hpi : (0 : ℝ) < 2 * π := by positivity
  have harg : arg z ≠ π := slitPlane_arg_ne_pi hz
  have hlog : Complex.log (2 * π / z) = Complex.log (2 * π) - Complex.log z := by
    rw [div_eq_mul_inv, show (2 * (π : ℂ)) = ((2 * π : ℝ) : ℂ) by push_cast; ring,
      Complex.log_ofReal_mul hpi (inv_ne_zero hz0), Complex.log_inv _ harg, ← ofReal_log hpi.le]
    ring
  have hden : (Real.sqrt (2 * π) : ℂ) * cexp (-z) * z ^ (z - 1 / 2) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ (Complex.exp_ne_zero _)) ?_
    · exact_mod_cast (Real.sqrt_pos.mpr hpi).ne'
    · rw [cpow_def_of_ne_zero hz0]; exact Complex.exp_ne_zero _
  rw [scaledGamma, mul_div_assoc', eq_div_iff hden]
  have hz2 : (2 * π / z) ≠ 0 := div_ne_zero (by exact_mod_cast hpi.ne') hz0
  rw [cpow_def_of_ne_zero hz0, cpow_def_of_ne_zero hz2, cpow_def_of_ne_zero hz0, hlog,
    sqrt_two_pi_eq_exp]
  simp only [← Complex.exp_add]
  rw [mul_comm (Gamma z)]
  congr 1
  congr 1
  ring

/-! ### Exponentiating an asymptotic expansion -/

/-- The truncation `∑_{s<N} cₛ Xˢ`. -/
noncomputable def truncPoly (c : ℕ → ℂ) (N : ℕ) : ℂ[X] := ∑ s ∈ Finset.range N, C (c s) * X ^ s

theorem coeff_truncPoly (c : ℕ → ℂ) (N j : ℕ) :
    (truncPoly c N).coeff j = if j < N then c j else 0 := by
  rw [truncPoly, finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range]

theorem eval_truncPoly (c : ℕ → ℂ) (N : ℕ) (w : ℂ) :
    (truncPoly c N).eval w = ∑ s ∈ Finset.range N, c s * w ^ s := by
  simp [truncPoly, eval_finsetSum]

/-- With `a` the coefficients and `b = seriesExp a`, `E′ − P′E` vanishes to order `N − 1`. -/
theorem X_pow_dvd_trunc (a : ℕ → ℚ) (N : ℕ) :
    X ^ (N - 1) ∣ derivative (truncPoly (fun s => (BZ.seriesExp a s : ℂ)) N) -
      derivative (truncPoly (fun s => (a s : ℂ)) N) *
        truncPoly (fun s => (BZ.seriesExp a s : ℂ)) N := by
  rw [X_pow_dvd_iff]
  intro j hj
  rw [coeff_sub, coeff_derivative, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    coeff_truncPoly, ite_eq_left (by omega)]
  have hsum : ∑ i ∈ Finset.range (j + 1),
      (derivative (truncPoly (fun s => (a s : ℂ)) N)).coeff i *
        (truncPoly (fun s => (BZ.seriesExp a s : ℂ)) N).coeff (j - i) =
      ∑ i ∈ Finset.range (j + 1), ((i + 1 : ℕ) : ℂ) * (a (i + 1) : ℂ) *
        (BZ.seriesExp a (j - i) : ℂ) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    rw [coeff_derivative, coeff_truncPoly, coeff_truncPoly, ite_eq_left (by omega),
      ite_eq_left (by omega)]
    push_cast
    ring
  rw [hsum, BZ.seriesExp_succ]
  push_cast
  field_simp
  ring

/-- `|e^{P(w)} − E(w)| ≤ C |w|^N` for `|w| ≤ 1`, `P`, `E` the truncations of `a` and of
`seriesExp a` (`a₀ = 0`). -/
theorem norm_cexp_trunc_sub_le (a : ℕ → ℚ) (ha : a 0 = 0) (N : ℕ) :
    ∃ C, ∀ w : ℂ, ‖w‖ ≤ 1 → ‖cexp ((truncPoly (fun s => (a s : ℂ)) N).eval w) -
      (truncPoly (fun s => (BZ.seriesExp a s : ℂ)) N).eval w‖ ≤ C * ‖w‖ ^ N := by
  set P := truncPoly (fun s => (a s : ℂ)) N with hP
  set E := truncPoly (fun s => (BZ.seriesExp a s : ℂ)) N with hE
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact ⟨1, fun w _ => by simp [hP, hE, truncPoly]⟩
  obtain ⟨Q, hQ⟩ := X_pow_dvd_trunc a N
  rw [← hP, ← hE] at hQ
  have hK : IsCompact (Metric.closedBall (0 : ℂ) 1) := isCompact_closedBall 0 1
  obtain ⟨M1, hM1⟩ := hK.exists_bound_of_continuousOn
    (f := fun v => cexp (-P.eval v)) (by fun_prop)
  obtain ⟨M2, hM2⟩ := hK.exists_bound_of_continuousOn (f := fun v => Q.eval v) (by fun_prop)
  obtain ⟨M3, hM3⟩ := hK.exists_bound_of_continuousOn
    (f := fun v => cexp (P.eval v)) (by fun_prop)
  have hM1' : 0 ≤ M1 := (norm_nonneg _).trans (hM1 0 (by simp))
  have hM2' : 0 ≤ M2 := (norm_nonneg _).trans (hM2 0 (by simp))
  have hM3' : 0 ≤ M3 := (norm_nonneg _).trans (hM3 0 (by simp))
  refine ⟨M3 * (M1 * M2), fun w hw => ?_⟩
  set F : ℂ → ℂ := fun v => cexp (-P.eval v) * E.eval v with hF
  have hderiv : ∀ v, HasDerivAt F (cexp (-P.eval v) * (v ^ (N - 1) * Q.eval v)) v := fun v => by
    have h1 : HasDerivAt (fun v => cexp (-P.eval v)) (cexp (-P.eval v) * -(P.derivative.eval v))
        v := ((P.hasDerivAt v).neg).cexp
    have h2 := h1.mul (E.hasDerivAt v)
    refine h2.congr_deriv ?_
    have := congrArg (eval v) hQ
    simp only [eval_sub, eval_mul, eval_pow, eval_X] at this
    rw [← this]
    ring
  have hball : Metric.closedBall (0 : ℂ) ‖w‖ ⊆ Metric.closedBall 0 1 :=
    Metric.closedBall_subset_closedBall hw
  have hbound : ∀ v ∈ Metric.closedBall (0 : ℂ) ‖w‖,
      ‖cexp (-P.eval v) * (v ^ (N - 1) * Q.eval v)‖ ≤ M1 * M2 * ‖w‖ ^ (N - 1) := fun v hv => by
    have hv1 := hball hv
    have hvw : ‖v‖ ≤ ‖w‖ := by simpa using hv
    rw [norm_mul, norm_mul, norm_pow]
    have h1 := hM1 v hv1
    have h2 := hM2 v hv1
    calc ‖cexp (-P.eval v)‖ * (‖v‖ ^ (N - 1) * ‖Q.eval v‖)
        ≤ M1 * (‖w‖ ^ (N - 1) * M2) := by gcongr
      _ = M1 * M2 * ‖w‖ ^ (N - 1) := by ring
  have hmvt := (convex_closedBall (0 : ℂ) ‖w‖).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun v _ => (hderiv v).hasDerivWithinAt) hbound (Metric.mem_closedBall_self (norm_nonneg w))
    (show w ∈ Metric.closedBall (0 : ℂ) ‖w‖ by simp)
  have hF0 : F 0 = 1 := by
    simp only [hF, ← coeff_zero_eq_eval_zero, hP, hE, coeff_truncPoly, ite_eq_left hN]
    simp [ha, BZ.seriesExp_zero]
  rw [hF0, sub_zero] at hmvt
  have hEw : E.eval w = cexp (P.eval w) * F w := by
    simp only [hF]
    rw [← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]
  rw [hEw, show cexp (P.eval w) - cexp (P.eval w) * F w = cexp (P.eval w) * (1 - F w) by ring,
    norm_mul, norm_sub_rev]
  calc ‖cexp (P.eval w)‖ * ‖F w - 1‖ ≤ M3 * (M1 * M2 * ‖w‖ ^ (N - 1) * ‖w‖) :=
        mul_le_mul (hM3 w (by simpa using hw)) hmvt (norm_nonneg _) hM3'
    _ = M3 * (M1 * M2) * ‖w‖ ^ N := by
        rw [mul_assoc (M1 * M2), ← pow_succ, Nat.sub_add_cancel hN]; ring

theorem eval_truncPoly_inv (c : ℕ → ℂ) (N : ℕ) (z : ℂ) :
    (truncPoly c N).eval z⁻¹ = ∑ s ∈ Finset.range N, c s * z ^ (-(s : ℤ)) := by
  rw [eval_truncPoly]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [zpow_neg, zpow_natCast, inv_pow]

/-- **The exponential of an asymptotic expansion**: if `f ∼ ∑ aₛ z^{−s}` with `a₀ = 0`, then
`e^f ∼ ∑ bₛ z^{−s}`, `b = seriesExp a` the formal exponential. -/
theorem isAsympExpansion_cexp {X : Set ℂ} {f : ℂ → ℂ} {a : ℕ → ℚ} (ha : a 0 = 0)
    (hf : IsAsympExpansionDLMF X f (fun s => (a s : ℂ))) :
    IsAsympExpansionDLMF X (fun z => cexp (f z)) (fun s => (BZ.seriesExp a s : ℂ)) := by
  intro n hn
  obtain ⟨B, hB⟩ := hf n hn
  rw [Filter.eventually_map] at hB
  obtain ⟨C, hC⟩ := norm_cexp_trunc_sub_le a ha n
  set P := truncPoly (fun s => (a s : ℂ)) n with hP
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    (f := fun v => cexp (P.eval v)) (by fun_prop)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by simp))
  have hB0 : ∀ᶠ z in Bornology.cobounded ℂ ⊓ 𝓟 X, max 1 B ≤ ‖z‖ :=
    (tendsto_norm_cobounded_atTop.eventually_ge_atTop _).filter_mono inf_le_left
  refine isBoundedUnder_of_eventually_le (a := 2 * M * B + C) ?_
  filter_upwards [hB, hB0] with z hz1 hz2
  have hz1' : 1 ≤ ‖z‖ := le_trans (le_max_left _ _) hz2
  have hzpos : 0 < ‖z‖ := by linarith
  have hz0 : z ≠ 0 := norm_pos_iff.mp hzpos
  have hzn : ‖z ^ (-(n : ℤ))‖ = 1 / ‖z‖ ^ n := by
    rw [norm_zpow, zpow_neg, zpow_natCast, one_div]
  have hzn0 : z ^ (-(n : ℤ)) ≠ 0 := zpow_ne_zero _ hz0
  have hzpow : 0 < ‖z‖ ^ n := by positivity
  set u := f z - ∑ s ∈ Finset.range n, (a s : ℂ) * z ^ (-(s : ℤ)) with hu
  have hu1 : ‖u‖ ≤ B / ‖z‖ ^ n := by
    have : ‖u / z ^ (-(n : ℤ))‖ ≤ B := hz1
    rw [norm_div, hzn, div_le_iff₀ (by positivity)] at this
    rw [div_eq_mul_one_div B]
    exact this
  have hB' : 0 ≤ B := (norm_nonneg _).trans hz1
  have hule : ‖u‖ ≤ 1 := by
    refine hu1.trans ?_
    rw [div_le_one hzpow]
    calc B ≤ max 1 B := le_max_right _ _
      _ ≤ ‖z‖ := hz2
      _ = ‖z‖ ^ 1 := (pow_one _).symm
      _ ≤ ‖z‖ ^ n := pow_le_pow_right₀ hz1' hn
  have hw : ‖z⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ hz1'
  have hS : ∑ s ∈ Finset.range n, (a s : ℂ) * z ^ (-(s : ℤ)) = P.eval z⁻¹ := by
    rw [hP, eval_truncPoly_inv]
  have hsplit : cexp (f z) - ∑ s ∈ Finset.range n, (BZ.seriesExp a s : ℂ) * z ^ (-(s : ℤ)) =
      cexp (P.eval z⁻¹) * (cexp u - 1) + (cexp (P.eval z⁻¹) -
        (truncPoly (fun s => (BZ.seriesExp a s : ℂ)) n).eval z⁻¹) := by
    rw [← hS, eval_truncPoly_inv, mul_sub, mul_one, ← Complex.exp_add, hu]
    ring_nf
  rw [hsplit, norm_div, hzn, div_div_eq_mul_div, div_one]
  have h1 : ‖cexp (P.eval z⁻¹) * (cexp u - 1)‖ ≤ M * (2 * (B / ‖z‖ ^ n)) := by
    rw [norm_mul]
    exact mul_le_mul (hM _ (by simpa using hw)) ((norm_exp_sub_one_le hule).trans
      (by linarith)) (norm_nonneg _) hM0
  have h2 := hC z⁻¹ hw
  rw [norm_inv, inv_pow] at h2
  calc ‖cexp (P.eval z⁻¹) * (cexp u - 1) + (cexp (P.eval z⁻¹) -
        (truncPoly (fun s => (BZ.seriesExp a s : ℂ)) n).eval z⁻¹)‖ * ‖z‖ ^ n
      ≤ (M * (2 * (B / ‖z‖ ^ n)) + C * (‖z‖ ^ n)⁻¹) * ‖z‖ ^ n := by
        gcongr
        exact (norm_add_le _ _).trans (add_le_add h1 h2)
    _ = 2 * M * B + C := by field_simp

/-! ### DLMF 5.11.3 -/

theorem isAsympExpansion_congr {X : Set ℂ} {f g : ℂ → ℂ} {a : ℕ → ℂ}
    (hfg : ∀ z ∈ X, f z = g z) (h : IsAsympExpansionDLMF X f a) : IsAsympExpansionDLMF X g a := by
  intro n hn
  obtain ⟨B, hB⟩ := h n hn
  rw [Filter.eventually_map] at hB
  refine isBoundedUnder_of_eventually_le (a := B) ?_
  filter_upwards [hB, mem_inf_of_right (mem_principal_self X)] with z hz hX
  simpa [hfg z hX] using hz

theorem stirlingSeriesCoeff_eq (s : ℕ) : stirlingSeriesCoeff s = (BZ.stirlingLogCoeff s : ℂ) := by
  rw [stirlingSeriesCoeff, BZ.stirlingLogCoeff]
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp
  rw [ite_eq_right hs.ne']
  rcases Nat.even_or_odd s with ⟨k, rfl⟩ | hodd
  · rw [ite_eq_right (by omega), bernoulli_eq_zero_of_odd ⟨k, by ring⟩ (by omega)]
    simp
  · rw [ite_eq_left (Nat.odd_iff.mp hodd)]
    push_cast
    ring

theorem mem_slitPlane_of_mem_closedSector {δ : ℝ} (hδ : 0 < δ) {z : ℂ}
    (hz : z ∈ closedSectorDLMF 0 (π - δ)) : z ∈ slitPlane := by
  obtain ⟨hz0, harg⟩ := hz
  simp only [ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, mul_one] at harg
  exact mem_slitPlane_iff_arg.mpr ⟨fun h => by
    rw [h, abs_of_pos Real.pi_pos] at harg; linarith, hz0⟩

/-- **DLMF 5.11.3**: as `z → ∞` in `|ph z| ≤ π − δ`, `Γ*(z) ∼ ∑_{k≥0} gₖ/zᵏ` with
`gₖ = BZ.stirlingCoeff k` (the formal exponential of Stirling's series 5.11.1); together with
`Γ(z) = e^{−z} z^z (2π/z)^{1/2} Γ*(z)` (`dlmf_5_11_3_eq`) this is
`Γ(z) ∼ e^{−z} z^z (2π/z)^{1/2} ∑ gₖ/zᵏ`. -/
theorem dlmf_5_11_3 {δ : ℝ} (hδ : 0 < δ) (hδπ : δ ≤ π) :
    IsAsympExpansionDLMF (closedSectorDLMF 0 (π - δ)) scaledGamma
      (fun k => (BZ.stirlingCoeff k : ℂ)) := by
  have hJ : IsAsympExpansionDLMF (closedSectorDLMF 0 (π - δ)) stirlingJ
      (fun s => (BZ.stirlingLogCoeff s : ℂ)) := by
    have := (dlmf_5_11_1 hδ hδπ).2
    rwa [show stirlingSeriesCoeff = fun s => (BZ.stirlingLogCoeff s : ℂ) from
      funext stirlingSeriesCoeff_eq] at this
  have hexp := isAsympExpansion_cexp (a := BZ.stirlingLogCoeff) (by simp [BZ.stirlingLogCoeff]) hJ
  exact isAsympExpansion_congr (fun z hz =>
    (scaledGamma_eq_exp_stirlingJ (mem_slitPlane_of_mem_closedSector hδ hz)).symm) hexp

/-- `Γ*(z) → 1` as `z → ∞` in `|ph z| ≤ π − δ` (the main property of `Γ*` stated after 5.11.6). -/
theorem tendsto_scaledGamma {δ : ℝ} (hδ : 0 < δ) (hδπ : δ ≤ π) :
    Tendsto scaledGamma (Bornology.cobounded ℂ ⊓ 𝓟 (closedSectorDLMF 0 (π - δ))) (𝓝 1) := by
  obtain ⟨B, hB⟩ := dlmf_5_11_3 hδ hδπ 1 one_pos
  rw [Filter.eventually_map] at hB
  have hinf : Tendsto (fun z : ℂ => B * ‖z‖⁻¹)
      (Bornology.cobounded ℂ ⊓ 𝓟 (closedSectorDLMF 0 (π - δ))) (𝓝 0) := by
    simpa using ((tendsto_norm_cobounded_atTop.mono_left inf_le_left).inv_tendsto_atTop).const_mul B
  refine tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun _ =>
    norm_nonneg _) ?_ hinf)
  filter_upwards [hB, mem_inf_of_right (mem_principal_self _)] with z hz hX
  have hz0 : z ≠ 0 := hX.1
  simp only [Finset.range_one, Finset.sum_singleton, BZ.stirlingCoeff_zero, Rat.cast_one,
    Nat.cast_zero, neg_zero, zpow_zero, mul_one, Nat.cast_one, zpow_neg_one, div_inv_eq_mul,
    norm_mul] at hz
  calc ‖scaledGamma z - 1‖ = ‖scaledGamma z - 1‖ * ‖z‖ * ‖z‖⁻¹ := by
        field_simp
    _ ≤ B * ‖z‖⁻¹ := by gcongr

/-! ### DLMF 5.11.4 -/

theorem stirlingLogCoeff_four : BZ.stirlingLogCoeff 4 = 0 := by simp [BZ.stirlingLogCoeff]

theorem stirlingLogCoeff_five : BZ.stirlingLogCoeff 5 = 1 / 1260 := by
  simp [BZ.stirlingLogCoeff, bernoulli_eq_bernoulli'_of_ne_one (show 6 ≠ 1 by norm_num),
    bernoulli'_six]
  norm_num

theorem stirlingLogCoeff_six : BZ.stirlingLogCoeff 6 = 0 := by simp [BZ.stirlingLogCoeff]

theorem stirlingCoeff_four : BZ.stirlingCoeff 4 = -571 / 2488320 := by
  have h1 := BZ.stirlingCoeff_one
  have h2 := BZ.stirlingCoeff_two
  have h3 := BZ.stirlingCoeff_three
  rw [BZ.stirlingCoeff] at h1 h2 h3 ⊢
  rw [BZ.seriesExp_succ]
  simp [Finset.sum_range_succ, BZ.stirlingLogCoeff_one, BZ.stirlingLogCoeff_two,
    BZ.stirlingLogCoeff_three, stirlingLogCoeff_four, BZ.seriesExp_zero, h1, h2, h3]
  norm_num

theorem stirlingCoeff_five : BZ.stirlingCoeff 5 = 163879 / 209018880 := by
  have h1 := BZ.stirlingCoeff_one
  have h2 := BZ.stirlingCoeff_two
  have h3 := BZ.stirlingCoeff_three
  have h4 := stirlingCoeff_four
  rw [BZ.stirlingCoeff] at h1 h2 h3 h4 ⊢
  rw [BZ.seriesExp_succ]
  simp [Finset.sum_range_succ, BZ.stirlingLogCoeff_one, BZ.stirlingLogCoeff_two,
    BZ.stirlingLogCoeff_three, stirlingLogCoeff_four, stirlingLogCoeff_five, BZ.seriesExp_zero,
    h1, h2, h3, h4]
  norm_num

theorem stirlingCoeff_six : BZ.stirlingCoeff 6 = 5246819 / 75246796800 := by
  have h1 := BZ.stirlingCoeff_one
  have h2 := BZ.stirlingCoeff_two
  have h3 := BZ.stirlingCoeff_three
  have h4 := stirlingCoeff_four
  have h5 := stirlingCoeff_five
  rw [BZ.stirlingCoeff] at h1 h2 h3 h4 h5 ⊢
  rw [BZ.seriesExp_succ]
  simp [Finset.sum_range_succ, BZ.stirlingLogCoeff_one, BZ.stirlingLogCoeff_two,
    BZ.stirlingLogCoeff_three, stirlingLogCoeff_four, stirlingLogCoeff_five,
    stirlingLogCoeff_six, BZ.seriesExp_zero, h1, h2, h3, h4, h5]
  norm_num

/-- **DLMF 5.11.4**: `g₀ = 1`, `g₁ = 1/12`, `g₂ = 1/288`, `g₃ = −139/51840`,
`g₄ = −571/2488320`, `g₅ = 163879/209018880`, `g₆ = 5246819/75246796800`. -/
theorem dlmf_5_11_4 :
    BZ.stirlingCoeff 0 = 1 ∧ BZ.stirlingCoeff 1 = 1 / 12 ∧ BZ.stirlingCoeff 2 = 1 / 288 ∧
      BZ.stirlingCoeff 3 = -139 / 51840 ∧ BZ.stirlingCoeff 4 = -571 / 2488320 ∧
      BZ.stirlingCoeff 5 = 163879 / 209018880 ∧ BZ.stirlingCoeff 6 = 5246819 / 75246796800 :=
  ⟨BZ.stirlingCoeff_zero, BZ.stirlingCoeff_one, BZ.stirlingCoeff_two, BZ.stirlingCoeff_three,
    stirlingCoeff_four, stirlingCoeff_five, stirlingCoeff_six⟩

end Azurite.DLMF
