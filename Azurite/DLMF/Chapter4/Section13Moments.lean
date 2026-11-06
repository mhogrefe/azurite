/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section13Primitive
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# DLMF §4.13: the moments `(1/π)∫₀^π ((sin t/t) e^{t cot t})ⁿ dt = nⁿ/n!`

These moments of `lamA t = (sin t/t) e^{t cot t}` (written `sinc t · e^{cos t/sinc t}`, continuous
on `(−π, π)`) give the Maclaurin coefficients of the integral representations 4.13.15–4.13.16.

Proof: in the logarithmic coordinate `w = ln z`, `e^{nz}/z^{n+1} dz = g(w) dw` with the entire
`g(w) = exp(n(eʷ − w))`. Along `w(t) = −ln sinc t + it` (the image of the curve
`z = t cot t + it`) `g(w(t)) = lamA(t)ⁿ` is real, so `∫_{−T}^{T} lamAⁿ = ℑ(Ψ(w(T)) − Ψ(w(−T)))` for
a primitive `Ψ` of `g` (`exists_primitive_of_simplyConnected` on `ℂ`). The same difference is the
integral of `g` over the vertical segment `ℜw = −ln sinc T`, which is the circle `|z| = 1/sinc T`
minus two arcs in `ℜz ≤ 0` of length `O(π − T)` where `|g| ≤ 1`; the circle gives `2πi nⁿ/n!`
(Cauchy's formula for derivatives).
-/

open Set Filter Topology Complex MeasureTheory intervalIntegral
open scoped Real Nat

namespace Azurite.DLMF

/-- `(sin t/t) e^{t cot t}`, as `sinc t · e^{cos t/sinc t}`. -/
noncomputable def lamA (t : ℝ) : ℝ := Real.sinc t * Real.exp (Real.cos t / Real.sinc t)

/-- `w(t) = −ln sinc t + it`, so `e^{w(t)} = t cot t + it`. -/
noncomputable def wPath (t : ℝ) : ℂ := ((-Real.log (Real.sinc t) : ℝ) : ℂ) + t * I

/-- The entire integrand `g(w) = exp(n(eʷ − w))` (`= e^{nz}/zⁿ` at `z = eʷ`). -/
noncomputable def lambertMomG (n : ℕ) (w : ℂ) : ℂ := exp (n * (exp w - w))

theorem sinc_pos_of_abs_lt {t : ℝ} (ht : |t| < π) : 0 < Real.sinc t := Real.sinc_pos ht

theorem sin_div_sinc {t : ℝ} (ht : |t| < π) : Real.sin t / Real.sinc t = t := by
  by_cases h0 : t = 0
  · simp [h0]
  · have hs := sinc_pos_of_abs_lt ht
    rw [Real.sinc_of_ne_zero h0] at hs ⊢
    have hsin : Real.sin t ≠ 0 := fun e => by rw [e, zero_div] at hs; exact lt_irrefl _ hs
    field_simp

theorem exp_wPath_sub {t : ℝ} (ht : |t| < π) :
    exp (wPath t) - wPath t = ((Real.cos t / Real.sinc t + Real.log (Real.sinc t) : ℝ) : ℂ) := by
  have hs := sinc_pos_of_abs_lt ht
  have h1 : exp (wPath t) = ((Real.sinc t)⁻¹ : ℝ) * exp (t * I) := by
    rw [wPath, exp_add, ← ofReal_exp, Real.exp_neg, Real.exp_log hs]
  rw [h1, exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  have h2 : (Real.sinc t)⁻¹ * Real.sin t = t := by
    rw [inv_mul_eq_div]; exact sin_div_sinc ht
  apply Complex.ext
  · simp [wPath]; field_simp
  · simp only [mul_im, ofReal_re, ofReal_im, add_im, I_re, I_im, wPath, sub_im]
    simp only [mul_zero, zero_mul, add_zero, mul_one, zero_add]
    linarith [h2]

theorem gMom_wPath (n : ℕ) {t : ℝ} (ht : |t| < π) :
    lambertMomG n (wPath t) = ((lamA t ^ n : ℝ) : ℂ) := by
  have hs := sinc_pos_of_abs_lt ht
  rw [lambertMomG, exp_wPath_sub ht, lamA, ← Real.exp_log hs, ← Real.exp_add, ← Real.exp_nat_mul,
    Real.exp_log hs]
  push_cast
  ring_nf

theorem hasDerivAt_wPath {t : ℝ} (ht : |t| < π) (h0 : t ≠ 0) :
    HasDerivAt wPath (((1 / t - Real.cos t / Real.sin t : ℝ) : ℂ) + I) t := by
  have hsin : Real.sin t ≠ 0 := by
    have hs := sinc_pos_of_abs_lt ht
    rw [Real.sinc_of_ne_zero h0] at hs
    exact fun e => by rw [e, zero_div] at hs; exact lt_irrefl _ hs
  have hq : HasDerivAt (fun x => Real.sin x / x) ((Real.cos t * t - Real.sin t * 1) / t ^ 2) t :=
    (Real.hasDerivAt_sin t).div (hasDerivAt_id t) h0
  have hl := (hq.log (div_ne_zero hsin h0)).neg
  have hev : (fun x => -Real.log (Real.sinc x)) =ᶠ[𝓝 t] fun x => -Real.log (Real.sin x / x) :=
    (eventually_ne_nhds h0).mono fun x hx => by simp [Real.sinc_of_ne_zero hx]
  have hl' := hl.congr_of_eventuallyEq hev
  have hval : -((Real.cos t * t - Real.sin t * 1) / t ^ 2 / (Real.sin t / t)) =
      1 / t - Real.cos t / Real.sin t := by
    field_simp; ring
  rw [hval] at hl'
  have h2 : HasDerivAt (fun x : ℝ => (x : ℂ) * I) (1 * I) t :=
    (hasDerivAt_id t).ofReal_comp.mul_const I
  have := hl'.ofReal_comp.add h2
  rw [one_mul] at this
  exact this

/-- Along `w(t)`, `ℑ(g(w) w′) = lamA(t)ⁿ`. -/
theorem im_gMom_mul_deriv (n : ℕ) {t : ℝ} (ht : |t| < π) :
    (lambertMomG n (wPath t) * (((1 / t - Real.cos t / Real.sin t : ℝ) : ℂ) + I)).im =
      lamA t ^ n := by
  rw [gMom_wPath n ht, mul_add, add_im, ← ofReal_mul, ofReal_im, zero_add, mul_I_im, ofReal_re]

/-! ### A primitive of `g` and the two halves of the curve -/

theorem isSimplyConnectedDLMF_univ : IsSimplyConnectedDLMF (univ : Set ℂ) := by
  rw [IsSimplyConnectedDLMF, image_univ, OnePoint.compl_range_coe]
  exact isConnected_singleton

theorem differentiable_gMom (n : ℕ) : Differentiable ℂ (lambertMomG n) := by
  unfold lambertMomG; fun_prop

theorem exists_primitive_gMom (n : ℕ) : ∃ Ψ : ℂ → ℂ, ∀ w, HasDerivAt Ψ (lambertMomG n w) w := by
  obtain ⟨Ψ, -, h⟩ := exists_primitive_of_simplyConnected isOpen_univ isConnected_univ
    isSimplyConnectedDLMF_univ (differentiable_gMom n).differentiableOn (mem_univ (0 : ℂ))
  exact ⟨Ψ, fun w => h w (mem_univ w)⟩

theorem continuousOn_lamA : ContinuousOn lamA {t | |t| < π} := by
  intro t ht
  have hs := sinc_pos_of_abs_lt ht
  exact ((Real.continuous_sinc.continuousAt.mul ((Real.continuous_cos.continuousAt.div
    Real.continuous_sinc.continuousAt hs.ne').rexp))).continuousWithinAt

theorem continuousOn_wPath : ContinuousOn wPath {t | |t| < π} := by
  intro t ht
  have hs := sinc_pos_of_abs_lt ht
  have h1 : ContinuousAt (fun x => -Real.log (Real.sinc x)) t :=
    (Real.continuous_sinc.continuousAt.log hs.ne').neg
  exact ((continuous_ofReal.continuousAt.comp h1).add
    ((continuous_ofReal.continuousAt).mul continuousAt_const)).continuousWithinAt

/-- `∫_a^b lamAⁿ = ℑ(Ψ(w(b)) − Ψ(w(a)))` on a half `0 ∉ (a, b)` of `(−π, π)`. -/
theorem integral_lamA_pow_half {n : ℕ} {Ψ : ℂ → ℂ} (hΨ : ∀ w, HasDerivAt Ψ (lambertMomG n w) w)
    {a b : ℝ} (hab : a ≤ b) (ha : -π < a) (hb : b < π) (h0 : ∀ t ∈ Ioo a b, t ≠ 0) :
    ∫ t in a..b, lamA t ^ n = (Ψ (wPath b)).im - (Ψ (wPath a)).im := by
  have hsub : Icc a b ⊆ {t | |t| < π} := fun t ht => by
    obtain ⟨h1, h2⟩ := ht; show |t| < π; exact abs_lt.mpr ⟨by linarith, by linarith⟩
  refine integral_eq_sub_of_hasDerivAt_of_le (f := fun t => (Ψ (wPath t)).im) hab ?_
    (fun t ht => ?_) ?_
  · have hc : ContinuousOn (fun t => Ψ (wPath t)) (Icc a b) :=
      (continuous_iff_continuousAt.mpr fun w => (hΨ w).continuousAt).comp_continuousOn
        (continuousOn_wPath.mono hsub)
    exact continuous_im.comp_continuousOn hc
  · have htπ : |t| < π := hsub (Ioo_subset_Icc_self ht)
    have hw := hasDerivAt_wPath htπ (h0 t ht)
    have hc := (hΨ (wPath t)).comp t hw
    have := (Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hc)
    simp only [Complex.imCLM_apply, Function.comp_def] at this
    rw [← im_gMom_mul_deriv n htπ]
    exact this
  · exact ((continuousOn_lamA.mono hsub).pow n).intervalIntegrable_of_Icc hab

/-- `∫_{−T}^{T} lamAⁿ = ℑ(Ψ(w(T)) − Ψ(w(−T)))`, `0 ≤ T < π`. -/
theorem integral_lamA_pow_sym {n : ℕ} {Ψ : ℂ → ℂ} (hΨ : ∀ w, HasDerivAt Ψ (lambertMomG n w) w)
    {T : ℝ} (hT0 : 0 ≤ T) (hT : T < π) :
    ∫ t in -T..T, lamA t ^ n = (Ψ (wPath T)).im - (Ψ (wPath (-T))).im := by
  have hπ := Real.pi_pos
  have h1 := integral_lamA_pow_half hΨ (a := -T) (b := 0) (by linarith) (by linarith) hπ
    (fun t ht => ht.2.ne)
  have h2 := integral_lamA_pow_half hΨ (a := 0) (b := T) hT0 (by linarith) hT
    (fun t ht => ht.1.ne')
  have hi1 : IntervalIntegrable (fun t => lamA t ^ n) volume (-T) 0 :=
    ((continuousOn_lamA.mono fun t ht => by
      obtain ⟨h1, h2⟩ := ht; show |t| < π; exact abs_lt.mpr ⟨by linarith, by linarith⟩).pow
      n).intervalIntegrable_of_Icc (by linarith)
  have hi2 : IntervalIntegrable (fun t => lamA t ^ n) volume 0 T :=
    ((continuousOn_lamA.mono fun t ht => by
      obtain ⟨h1, h2⟩ := ht; show |t| < π; exact abs_lt.mpr ⟨by linarith, by linarith⟩).pow
      n).intervalIntegrable_of_Icc hT0
  rw [← integral_add_adjacent_intervals hi1 hi2, h1, h2]
  ring

/-! ### The vertical segment and the circle -/

theorem continuous_gMom_vert (n : ℕ) (L : ℝ) :
    Continuous fun θ : ℝ => lambertMomG n ((L : ℂ) + θ * I) * I :=
  ((differentiable_gMom n).continuous.comp (by fun_prop)).mul continuous_const

/-- `Ψ(L + iT) − Ψ(L − iT) = ∫_{−T}^{T} g(L + iθ) i dθ`. -/
theorem primitive_vert {n : ℕ} {Ψ : ℂ → ℂ} (hΨ : ∀ w, HasDerivAt Ψ (lambertMomG n w) w) (L T : ℝ) :
    Ψ ((L : ℂ) + T * I) - Ψ ((L : ℂ) + ((-T : ℝ) : ℂ) * I) =
      ∫ θ in -T..T, lambertMomG n ((L : ℂ) + θ * I) * I := by
  refine (integral_eq_sub_of_hasDerivAt (f := fun θ : ℝ => Ψ ((L : ℂ) + θ * I))
    (fun θ _ => ?_) ((continuous_gMom_vert n L).intervalIntegrable _ _)).symm
  have hv : HasDerivAt (fun θ : ℝ => (L : ℂ) + θ * I) (1 * I) θ :=
    ((hasDerivAt_id θ).ofReal_comp.mul_const I).const_add _
  rw [one_mul] at hv
  exact (hΨ _).comp θ hv

theorem wPath_eq (T : ℝ) : wPath T = ((-Real.log (Real.sinc T) : ℝ) : ℂ) + T * I := rfl

theorem wPath_neg (T : ℝ) :
    wPath (-T) = ((-Real.log (Real.sinc T) : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * I := by
  rw [wPath, Real.sinc_neg]

/-- The full circle: `∫_{−π}^{π} g(L + iθ) i dθ = ∮_{|z| = e^L} e^{nz}/z^{n+1} dz = 2πi nⁿ/n!`. -/
theorem integral_gMom_circle (n : ℕ) (L : ℝ) :
    ∫ θ in -π..π, lambertMomG n ((L : ℂ) + θ * I) * I = 2 * π * I / n ! * (n : ℂ) ^ n := by
  set R := Real.exp L
  set F : ℂ → ℂ := fun z => (1 / (z - 0) ^ (n + 1)) • exp (n * z)
  set f : ℝ → ℂ := fun θ => (circleMap 0 R θ * I) • F (circleMap 0 R θ)
  have hpt : ∀ θ : ℝ, lambertMomG n ((L : ℂ) + θ * I) * I = f θ := by
    intro θ
    have hz : circleMap 0 R θ = exp ((L : ℂ) + θ * I) := by
      simp [circleMap, R, exp_add, ofReal_exp]
    have hz0 : exp ((L : ℂ) + θ * I) ≠ 0 := exp_ne_zero _
    simp only [f, F, hz, smul_eq_mul, sub_zero, lambertMomG]
    rw [mul_sub, exp_sub, exp_nat_mul ((L : ℂ) + θ * I) n]
    field_simp
    ring
  have hper : Function.Periodic f (2 * π) := fun θ => by
    simp only [f]; rw [periodic_circleMap 0 R θ]
  rw [integral_congr fun θ _ => hpt θ]
  have h1 := hper.intervalIntegral_add_eq (-π) 0
  rw [show -π + 2 * π = π by ring, zero_add] at h1
  rw [h1]
  have h2 : ∫ θ in (0 : ℝ)..2 * π, f θ = ∮ z in C(0, R), F z := by
    rw [circleIntegral]
    refine integral_congr fun θ _ => ?_
    simp only [f, deriv_circleMap]
  rw [h2]
  have hd : DifferentiableOn ℂ (fun z : ℂ => exp (n * z)) (Metric.closedBall 0 R) :=
    (by fun_prop : Differentiable ℂ fun z : ℂ => exp (n * z)).differentiableOn
  rw [hd.circleIntegral_one_div_sub_center_pow_smul (Real.exp_pos L) n,
    iteratedDeriv_cexp_const_mul]
  simp

/-! ### The estimates -/

theorem norm_gMom_vert_le (n : ℕ) {L θ : ℝ} (hL : 0 ≤ L) (hc : Real.cos θ ≤ 0) :
    ‖lambertMomG n ((L : ℂ) + θ * I) * I‖ ≤ 1 := by
  rw [norm_mul, norm_I, mul_one, lambertMomG, norm_exp]
  have hre : ((n : ℂ) * (exp ((L : ℂ) + θ * I) - ((L : ℂ) + θ * I))).re =
      n * (Real.exp L * Real.cos θ - L) := by
    simp [exp_re]
  rw [hre, Real.exp_le_one_iff]
  have : Real.exp L * Real.cos θ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos L).le hc
  exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) (by linarith)

theorem cos_nonpos_of_le_abs {θ T : ℝ} (hT : π / 2 ≤ T) (h1 : T ≤ |θ|) (h2 : |θ| ≤ π) :
    Real.cos θ ≤ 0 := by
  rw [← Real.cos_abs]
  exact Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith [Real.pi_pos])

/-- The two arcs `T ≤ |θ| ≤ π` contribute at most `2(π − T)`. -/
theorem norm_integral_gMom_sub_le (n : ℕ) {L T : ℝ} (hL : 0 ≤ L) (hT1 : π / 2 ≤ T)
    (hT2 : T < π) :
    ‖(∫ θ in -π..π, lambertMomG n ((L : ℂ) + θ * I) * I) -
      ∫ θ in -T..T, lambertMomG n ((L : ℂ) + θ * I) * I‖ ≤ 2 * (π - T) := by
  set h := fun θ : ℝ => lambertMomG n ((L : ℂ) + θ * I) * I
  have hi : ∀ a b : ℝ, IntervalIntegrable h volume a b :=
    fun a b => (continuous_gMom_vert n L).intervalIntegrable a b
  have hsplit : (∫ θ in -π..π, h θ) =
      (∫ θ in -π..-T, h θ) + (∫ θ in -T..T, h θ) + ∫ θ in T..π, h θ := by
    rw [integral_add_adjacent_intervals (hi _ _) (hi _ _),
      integral_add_adjacent_intervals (hi _ _) (hi _ _)]
  have hπ := Real.pi_pos
  have b1 : ‖∫ θ in -π..-T, h θ‖ ≤ 1 * |-T - -π| := by
    refine norm_integral_le_of_norm_le_const fun θ hθ => norm_gMom_vert_le n hL ?_
    rw [uIoc_of_le (by linarith)] at hθ
    obtain ⟨h1, h2⟩ := hθ
    exact cos_nonpos_of_le_abs hT1 (by rw [abs_of_neg (by linarith)]; linarith)
      (by rw [abs_of_neg (by linarith)]; linarith)
  have b2 : ‖∫ θ in T..π, h θ‖ ≤ 1 * |π - T| := by
    refine norm_integral_le_of_norm_le_const fun θ hθ => norm_gMom_vert_le n hL ?_
    rw [uIoc_of_le (by linarith)] at hθ
    obtain ⟨h1, h2⟩ := hθ
    exact cos_nonpos_of_le_abs hT1 (by rw [abs_of_pos (by linarith)]; linarith)
      (by rw [abs_of_pos (by linarith)]; linarith)
  rw [abs_of_pos (by linarith)] at b1 b2
  rw [hsplit, show ∀ a b c : ℂ, a + b + c - b = a + c from fun a b c => by ring]
  calc _ ≤ ‖∫ θ in -π..-T, h θ‖ + ‖∫ θ in T..π, h θ‖ := norm_add_le _ _
    _ ≤ _ := by linarith

theorem lamA_neg (t : ℝ) : lamA (-t) = lamA t := by simp [lamA, Real.sinc_neg]

theorem sinc_eq_zero_of_abs_eq_pi {t : ℝ} (ht : |t| = π) : Real.sinc t = 0 := by
  have h0 : t ≠ 0 := fun h => by rw [h, abs_zero] at ht; linarith [Real.pi_pos]
  rw [Real.sinc_of_ne_zero h0]
  rcases abs_eq Real.pi_pos.le |>.mp ht with h | h <;> simp [h]

/-- `0 ≤ lamA t ≤ e` on `[−π, π]`. -/
theorem lamA_mem_Icc {t : ℝ} (ht : |t| ≤ π) : 0 ≤ lamA t ∧ lamA t ≤ Real.exp 1 := by
  rcases ht.lt_or_eq with ht | ht
  · have hs := sinc_pos_of_abs_lt ht
    have hle : Real.cos t / Real.sinc t ≤ 1 := by
      by_cases hc : Real.cos t ≤ 0
      · exact (div_nonpos_of_nonpos_of_nonneg hc hs.le).trans zero_le_one
      · push Not at hc
        have hpi : |t| < π / 2 := by
          by_contra h; push Not at h
          exact absurd (cos_nonpos_of_le_abs le_rfl h ht.le) (not_le.mpr hc)
        rw [div_le_one hs]; exact Real.cos_le_sinc hpi
    refine ⟨mul_nonneg hs.le (Real.exp_pos _).le, ?_⟩
    calc lamA t ≤ 1 * Real.exp 1 :=
          mul_le_mul (Real.sinc_le_one t) (Real.exp_le_exp.mpr hle) (Real.exp_pos _).le
            zero_le_one
      _ = Real.exp 1 := one_mul _
  · rw [lamA, sinc_eq_zero_of_abs_eq_pi ht, zero_mul]; exact ⟨le_rfl, (Real.exp_pos 1).le⟩

theorem measurable_lamA : Measurable lamA := by
  unfold lamA
  exact Real.continuous_sinc.measurable.mul
    ((Real.measurable_cos.div Real.continuous_sinc.measurable).exp)

theorem intervalIntegrable_lamA_pow (n : ℕ) :
    IntervalIntegrable (fun t => lamA t ^ n) volume (-π) π := by
  refine (intervalIntegrable_const (c := Real.exp 1 ^ n)).mono_fun
    (measurable_lamA.pow_const n).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_uIoc fun t ht => ?_
  rw [uIoc_of_le (by linarith [Real.pi_pos])] at ht
  obtain ⟨h0, h1⟩ := lamA_mem_Icc (t := t) (abs_le.mpr ⟨ht.1.le, ht.2⟩)
  simp only [Real.norm_eq_abs, abs_pow, abs_of_nonneg h0, abs_of_pos (Real.exp_pos 1)]
  exact pow_le_pow_left₀ h0 h1 n

theorem abs_integral_lamA_pow_sub_le (n : ℕ) {T : ℝ} (hT0 : 0 ≤ T) (hT : T < π) :
    |(∫ t in -π..π, lamA t ^ n) - ∫ t in -T..T, lamA t ^ n| ≤ 2 * (π - T) * Real.exp 1 ^ n := by
  have hi := intervalIntegrable_lamA_pow n
  have hπ := Real.pi_pos
  have hi1 : IntervalIntegrable (fun t => lamA t ^ n) volume (-π) (-T) :=
    hi.mono_set (by rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)]
                    exact Icc_subset_Icc le_rfl (by linarith))
  have hi2 : IntervalIntegrable (fun t => lamA t ^ n) volume (-T) T :=
    hi.mono_set (by rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)]
                    exact Icc_subset_Icc (by linarith) (by linarith))
  have hi3 : IntervalIntegrable (fun t => lamA t ^ n) volume T π :=
    hi.mono_set (by rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)]
                    exact Icc_subset_Icc (by linarith) le_rfl)
  rw [← integral_add_adjacent_intervals hi1 (hi2.trans hi3),
    ← integral_add_adjacent_intervals hi2 hi3]
  have hb : ∀ {a b : ℝ}, -π ≤ a → b ≤ π → a ≤ b →
      ‖∫ t in a..b, lamA t ^ n‖ ≤ Real.exp 1 ^ n * |b - a| := by
    intro a b ha hb hab
    refine norm_integral_le_of_norm_le_const fun t ht => ?_
    rw [uIoc_of_le hab] at ht
    obtain ⟨h0, h1⟩ := lamA_mem_Icc (t := t)
      (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg h0]
    exact pow_le_pow_left₀ h0 h1 n
  have b1 := hb (a := -π) (b := -T) le_rfl (by linarith) (by linarith)
  have b3 := hb (a := T) (b := π) (by linarith) le_rfl hT.le
  have e1 : |-T - -π| = π - T := by rw [abs_of_nonneg (by linarith)]; ring
  have e3 : |π - T| = π - T := abs_of_nonneg (by linarith)
  rw [Real.norm_eq_abs, e1] at b1
  rw [Real.norm_eq_abs, e3] at b3
  rw [show ∀ a b c : ℝ, a + (b + c) - b = a + c from fun a b c => by ring]
  calc _ ≤ |∫ t in -π..-T, lamA t ^ n| + |∫ t in T..π, lamA t ^ n| := abs_add_le _ _
    _ ≤ _ := by nlinarith [pow_pos (Real.exp_pos 1) n]

theorem eq_zero_of_forall_abs_le {x K : ℝ} (hK : 0 ≤ K)
    (h : ∀ T, π / 2 ≤ T → T < π → |x| ≤ K * (π - T)) : x = 0 := by
  by_contra hx
  have hxpos := abs_pos.mpr hx
  set δ := min (π / 2) (|x| / (2 * (K + 1)))
  have hδ : 0 < δ := lt_min (by linarith [Real.pi_pos]) (by positivity)
  have h1 := h (π - δ) (by linarith [min_le_left (π / 2) (|x| / (2 * (K + 1)))]) (by linarith)
  rw [sub_sub_cancel] at h1
  have h2 : δ ≤ |x| / (2 * (K + 1)) := min_le_right _ _
  have h3 : K * δ ≤ K * (|x| / (2 * (K + 1))) := mul_le_mul_of_nonneg_left h2 hK
  have h4 : K * (|x| / (2 * (K + 1))) < |x| := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
  linarith

/-- **The moments**: `∫₀^π ((sin t/t) e^{t cot t})ⁿ dt = π nⁿ/n!`. -/
theorem integral_lamA_pow (n : ℕ) : ∫ t in (0 : ℝ)..π, lamA t ^ n = π * n ^ n / n ! := by
  obtain ⟨Ψ, hΨ⟩ := exists_primitive_gMom n
  have hπ := Real.pi_pos
  -- the symmetric integral over `(−π, π)` is `2π nⁿ/n!`
  have hsym : (∫ t in -π..π, lamA t ^ n) = 2 * π * n ^ n / n ! := by
    rw [← sub_eq_zero]
    refine eq_zero_of_forall_abs_le (K := 2 * (Real.exp 1 ^ n + 1)) (by positivity)
      fun T hT1 hT2 => ?_
    have hT0 : 0 ≤ T := by linarith
    set L := -Real.log (Real.sinc T)
    have hs := sinc_pos_of_abs_lt (t := T) (by rw [abs_of_nonneg hT0]; exact hT2)
    have hL : 0 ≤ L := by
      simp only [L, neg_nonneg]; exact Real.log_nonpos hs.le (Real.sinc_le_one T)
    have hST := integral_lamA_pow_sym hΨ hT0 hT2
    rw [wPath_eq, wPath_neg, ← sub_im, primitive_vert hΨ L T] at hST
    have hc := integral_gMom_circle n L
    have hnorm := norm_integral_gMom_sub_le n hL hT1 hT2
    rw [hc] at hnorm
    have hre : |(2 * π * n ^ n / n ! : ℝ) - ∫ t in -T..T, lamA t ^ n| ≤ 2 * (π - T) := by
      have hcI : 2 * (π : ℂ) * I / (n ! : ℂ) * (n : ℂ) ^ n =
          ((2 * π * n ^ n / n ! : ℝ) : ℂ) * I := by push_cast; ring
      rw [hcI] at hnorm
      rw [hST]
      refine le_trans ?_ hnorm
      refine le_trans (le_of_eq ?_) (abs_im_le_norm _)
      rw [sub_im, mul_I_im, ofReal_re]
    have hend := abs_integral_lamA_pow_sub_le n hT0 hT2
    calc _ ≤ |(∫ t in -π..π, lamA t ^ n) - ∫ t in -T..T, lamA t ^ n| +
          |(2 * π * n ^ n / n ! : ℝ) - ∫ t in -T..T, lamA t ^ n| := by
            rw [← abs_neg ((2 * π * n ^ n / n ! : ℝ) - _)]
            exact (le_of_eq (by ring_nf)).trans (abs_add_le _ _)
      _ ≤ _ := by nlinarith
  -- evenness
  have hi := intervalIntegrable_lamA_pow n
  have hi1 : IntervalIntegrable (fun t => lamA t ^ n) volume (-π) 0 :=
    hi.mono_set (by rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)]
                    exact Icc_subset_Icc le_rfl hπ.le)
  have hi2 : IntervalIntegrable (fun t => lamA t ^ n) volume 0 π :=
    hi.mono_set (by rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)]
                    exact Icc_subset_Icc (by linarith) le_rfl)
  have hneg : (∫ t in -π..0, lamA t ^ n) = ∫ t in (0 : ℝ)..π, lamA t ^ n := by
    have := integral_comp_neg (a := 0) (b := π) (fun t => lamA t ^ n)
    simp only [lamA_neg, neg_zero] at this
    exact this.symm
  rw [← integral_add_adjacent_intervals hi1 hi2, hneg] at hsym
  linear_combination hsym / 2

end Azurite.DLMF
