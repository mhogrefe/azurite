/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section9BoydFormula
import Azurite.DLMF.Chapter5.Section11Bounds

/-!
# DLMF §5.11(ii): Boyd's representation of the remainder `R_K(z)`

Toward 5.11.11 (Boyd 1994; proof as in G. Nemes, *Error bounds and exponential improvements for
the asymptotic expansions of the gamma function and its reciprocal*, arXiv:1310.0166, §2).

With `A(t) = e^{−2πt} Γ*(it)`, `B(t) = e^{−2πt} Γ*(−it)` (`boydA`, `boydB`), expanding the
Cauchy kernels of Boyd's formula 5.9.11_1 geometrically gives, for `ℜz > 0` and `K = n + 1 ≥ 1`
(Nemes (2.1)):
`R_K(z) = (2π z^K)⁻¹ (iⁿ ∫₀^∞ tⁿ A(t)/(1 − it/z) dt + (−i)ⁿ ∫₀^∞ tⁿ B(t)/(1 + it/z) dt)`
(`boydRem`, `stirlingR_eq_boydRem`). The coefficients produced along the way are the moments
`(2π)⁻¹ (iⁿ ∫ tⁿ A + (−i)ⁿ ∫ tⁿ B)` (`boydCoeff`), equal to `g_{n+1}` by uniqueness of
asymptotic expansions (`boydCoeff_eq`).

* `Γ*(z̄) = conj Γ*(z)` off the negative axis (`scaledGamma_conj`), hence with the reflection
  identity `|Γ*(±it)| = (1 − e^{−2πt})^{−1/2}` (`norm_scaledGamma_I`, `norm_scaledGamma_neg_I`)
  and `|A(t)| = |B(t)| = e^{−2πt}(1 − e^{−2πt})^{−1/2}` (`boydM`).
* `|1 − it/z|, |1 + it/z| ≥ cos(ph z)`, and one of them is `≥ 1` (by the sign of `ℑz`), so
  `|R_K(z)| ≤ (1 + sec(ph z)) (2π|z|^K)⁻¹ ∫₀^∞ t^{K−1} e^{−2πt}(1 − e^{−2πt})^{−1/2} dt`
  (`norm_boydRem_le`).
-/

open Complex Filter Topology Set MeasureTheory
open scoped Real ComplexConjugate

namespace Azurite.DLMF

/-! ### Conjugation and the modulus on the imaginary axis -/

/-- `Γ*(z̄) = conj Γ*(z)` for `ph z ≠ π`. -/
theorem scaledGamma_conj {w : ℂ} (hw : w.arg ≠ π) :
    scaledGamma (conj w) = conj (scaledGamma w) := by
  unfold scaledGamma
  rw [map_div₀, map_mul, map_mul, ← Gamma_conj, ← exp_conj, conj_ofReal, conj_cpow _ _ hw]
  simp [map_ofNat]

theorem arg_ofReal_mul_I_of_pos {t : ℝ} (ht : 0 < t) : arg ((t : ℂ) * I) = π / 2 := by
  rw [arg_real_mul I ht, arg_I]

theorem scaledGamma_mul_neg_I {t : ℝ} (ht : 0 < t) :
    scaledGamma ((t : ℂ) * -I) = conj (scaledGamma ((t : ℂ) * I)) := by
  rw [← scaledGamma_conj (by rw [arg_ofReal_mul_I_of_pos ht]; linarith [Real.pi_pos])]
  simp

theorem one_sub_exp_pos {t : ℝ} (ht : 0 < t) : 0 < 1 - Real.exp (-(2 * π * t)) := by
  have h := Real.exp_lt_exp.mpr (show -(2 * π * t) < 0 by nlinarith [Real.pi_pos])
  rw [Real.exp_zero] at h
  linarith

theorem cexp_neg_two_pi_mul (t : ℝ) :
    cexp (-(2 * π * (t : ℂ))) = (Real.exp (-(2 * π * t)) : ℂ) := by
  push_cast; rfl

/-- `|Γ*(it)|² = 1/(1 − e^{−2πt})` for `t > 0`. -/
theorem norm_scaledGamma_I_sq {t : ℝ} (ht : 0 < t) :
    ‖scaledGamma ((t : ℂ) * I)‖ ^ 2 = 1 / (1 - Real.exp (-(2 * π * t))) := by
  have h := scaledGamma_mul_scaledGamma_neg ht
  rw [show -((t : ℂ) * I) = (t : ℂ) * -I by ring, scaledGamma_mul_neg_I ht, mul_conj,
    cexp_neg_two_pi_mul] at h
  rw [← normSq_eq_norm_sq]
  exact_mod_cast h

theorem norm_scaledGamma_I {t : ℝ} (ht : 0 < t) :
    ‖scaledGamma ((t : ℂ) * I)‖ = 1 / Real.sqrt (1 - Real.exp (-(2 * π * t))) := by
  rw [← Real.sqrt_sq (norm_nonneg _), norm_scaledGamma_I_sq ht, one_div, Real.sqrt_inv, one_div]

theorem norm_scaledGamma_neg_I {t : ℝ} (ht : 0 < t) :
    ‖scaledGamma ((t : ℂ) * -I)‖ = 1 / Real.sqrt (1 - Real.exp (-(2 * π * t))) := by
  rw [scaledGamma_mul_neg_I ht, RCLike.norm_conj, norm_scaledGamma_I ht]

/-! ### The integrands -/

/-- `A(t) = e^{−2πt} Γ*(it)`. -/
noncomputable def boydA (t : ℝ) : ℂ := cexp (-(2 * π * t)) * scaledGamma ((t : ℂ) * I)

/-- `B(t) = e^{−2πt} Γ*(−it)`. -/
noncomputable def boydB (t : ℝ) : ℂ := cexp (-(2 * π * t)) * scaledGamma ((t : ℂ) * -I)

/-- `|A(t)| = |B(t)| = e^{−2πt}(1 − e^{−2πt})^{−1/2}`. -/
noncomputable def boydM (t : ℝ) : ℝ :=
  Real.exp (-(2 * π * t)) / Real.sqrt (1 - Real.exp (-(2 * π * t)))

theorem boydM_nonneg (t : ℝ) : 0 ≤ boydM t :=
  div_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)

theorem norm_boydA {t : ℝ} (ht : 0 < t) : ‖boydA t‖ = boydM t := by
  rw [boydA, norm_mul, cexp_neg_two_pi_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le, norm_scaledGamma_I ht, boydM]
  ring

theorem norm_boydB {t : ℝ} (ht : 0 < t) : ‖boydB t‖ = boydM t := by
  rw [boydB, norm_mul, cexp_neg_two_pi_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le, norm_scaledGamma_neg_I ht, boydM]
  ring

theorem continuousOn_boydA : ContinuousOn boydA (Ioi 0) := fun t ht => by
  have h := (continuousAt_scaledGamma_I (ne_of_gt ht)).1
  have hc : ContinuousAt (fun s : ℝ => scaledGamma ((s : ℂ) * I)) t :=
    h.comp (f := fun s : ℝ => (s : ℂ) * I) (by fun_prop)
  exact ((by fun_prop : Continuous fun s : ℝ => cexp (-(2 * π * (s : ℂ)))).continuousAt.mul
    hc).continuousWithinAt

theorem continuousOn_boydB : ContinuousOn boydB (Ioi 0) := fun t ht => by
  have ht' : (0 : ℝ) < t := ht
  have h := (continuousAt_scaledGamma_I (y := -t) (by linarith)).1
  have hc : ContinuousAt (fun s : ℝ => scaledGamma ((s : ℂ) * -I)) t := by
    have := h.comp_of_eq (f := fun s : ℝ => ((-s : ℝ) : ℂ) * I) (by fun_prop) rfl
    refine this.congr (Eventually.of_forall fun s => ?_)
    simp only [Function.comp_apply]
    congr 1
    push_cast
    ring
  exact ((by fun_prop : Continuous fun s : ℝ => cexp (-(2 * π * (s : ℂ)))).continuousAt.mul
    hc).continuousWithinAt

/-- `e^{−2πt}(1 − e^{−2πt})^{−1/2} ≤ e^{−πt}/√(2πt)`. -/
theorem boydM_le {t : ℝ} (ht : 0 < t) :
    boydM t ≤ Real.exp (-(π * t)) / Real.sqrt (2 * π * t) := by
  have hx : 0 < 2 * π * t := by positivity
  have he : Real.exp (-(2 * π * t)) = Real.exp (-(π * t)) * Real.exp (-(π * t)) := by
    rw [← Real.exp_add]; ring_nf
  have h1 : 2 * π * t * Real.exp (-(2 * π * t)) ≤ 1 - Real.exp (-(2 * π * t)) := by
    have h2 := Real.add_one_le_exp (2 * π * t)
    have h3 : Real.exp (2 * π * t) * Real.exp (-(2 * π * t)) = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-(2 * π * t))]
  have hs : Real.sqrt (2 * π * t * Real.exp (-(2 * π * t))) =
      Real.sqrt (2 * π * t) * Real.exp (-(π * t)) := by
    rw [Real.sqrt_mul hx.le, he, Real.sqrt_mul_self (Real.exp_pos _).le]
  unfold boydM
  rw [div_le_div_iff₀ (Real.sqrt_pos.mpr (one_sub_exp_pos ht)) (Real.sqrt_pos.mpr hx)]
  calc Real.exp (-(2 * π * t)) * Real.sqrt (2 * π * t)
      = Real.exp (-(π * t)) * (Real.sqrt (2 * π * t) * Real.exp (-(π * t))) := by rw [he]; ring
    _ ≤ Real.exp (-(π * t)) * Real.sqrt (1 - Real.exp (-(2 * π * t))) := by
        gcongr
        rw [← hs]
        exact Real.sqrt_le_sqrt h1

theorem measurable_boydM : Measurable boydM := by
  unfold boydM; fun_prop

theorem integrableOn_pow_mul_boydM (n : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ n * boydM t) (Ioi 0) := by
  have hint := (integrableOn_rpow_mul_exp_neg_mul (s := (n : ℝ) - 1 / 2) (b := π)
    (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]) Real.pi_pos).const_mul
    (Real.sqrt (2 * π))⁻¹
  refine Integrable.mono' hint ((measurable_id.pow_const n).mul
    measurable_boydM).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_))
  have ht' : (0 : ℝ) < t := ht
  rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg ht'.le n) (boydM_nonneg t))]
  have hpow : t ^ n / Real.sqrt t = t ^ ((n : ℝ) - 1 / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_sub ht', Real.rpow_natCast]
  calc t ^ n * boydM t ≤ t ^ n * (Real.exp (-(π * t)) / Real.sqrt (2 * π * t)) := by
        gcongr; exact boydM_le ht'
    _ = (Real.sqrt (2 * π))⁻¹ * (t ^ n / Real.sqrt t * Real.exp (-(π * t))) := by
        rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * π)]
        field_simp
    _ = _ := by rw [hpow]

/-- `∫₀^∞ tⁿ e^{−2πt}(1 − e^{−2πt})^{−1/2} dt`. -/
noncomputable def boydMom (n : ℕ) : ℝ := ∫ t in Ioi (0 : ℝ), t ^ n * boydM t

theorem boydMom_nonneg (n : ℕ) : 0 ≤ boydMom n :=
  setIntegral_nonneg measurableSet_Ioi fun t ht =>
    mul_nonneg (pow_nonneg (le_of_lt ht) n) (boydM_nonneg t)

/-- Integrability from a bound by a multiple of `tⁿ |A(t)|`. -/
theorem integrableOn_of_le_boydM {F : ℝ → ℂ} (hF : ContinuousOn F (Ioi 0)) (n : ℕ) {C : ℝ}
    (hb : ∀ t : ℝ, 0 < t → ‖F t‖ ≤ C * (t ^ n * boydM t)) : IntegrableOn F (Ioi 0) := by
  refine Integrable.mono' ((integrableOn_pow_mul_boydM n).const_mul |C|)
    (hF.aestronglyMeasurable measurableSet_Ioi)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_))
  exact (hb t ht).trans (mul_le_mul_of_nonneg_right (le_abs_self C)
    (mul_nonneg (pow_nonneg (le_of_lt ht) n) (boydM_nonneg t)))

theorem norm_integral_le_boydMom {F : ℝ → ℂ} (n : ℕ) {C : ℝ}
    (hb : ∀ t : ℝ, 0 < t → ‖F t‖ ≤ C * (t ^ n * boydM t)) :
    ‖∫ t in Ioi (0 : ℝ), F t‖ ≤ C * boydMom n := by
  rw [boydMom, ← integral_const_mul]
  exact norm_integral_le_of_norm_le ((integrableOn_pow_mul_boydM n).const_mul C)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hb))

/-! ### The Cauchy kernels -/

theorem ne_zero_of_pos_re {z : ℂ} (hz : 0 < z.re) : z ≠ 0 := fun h => by
  rw [h, zero_re] at hz; exact lt_irrefl 0 hz

theorem re_div_norm_le_sub {z : ℂ} (hz : 0 < z.re) (t : ℝ) :
    z.re / ‖z‖ ≤ ‖1 - (t : ℂ) * I / z‖ := by
  have hz0 := ne_zero_of_pos_re hz
  rw [show 1 - (t : ℂ) * I / z = (z - t * I) / z by field_simp, norm_div]
  gcongr
  calc z.re = (z - t * I).re := by simp
    _ ≤ ‖z - t * I‖ := re_le_norm _

theorem re_div_norm_le_add {z : ℂ} (hz : 0 < z.re) (t : ℝ) :
    z.re / ‖z‖ ≤ ‖1 + (t : ℂ) * I / z‖ := by
  have hz0 := ne_zero_of_pos_re hz
  rw [show 1 + (t : ℂ) * I / z = (z + t * I) / z by field_simp, norm_div]
  gcongr
  calc z.re = (z + t * I).re := by simp
    _ ≤ ‖z + t * I‖ := re_le_norm _

theorem one_le_norm_sub {z : ℂ} (hz0 : z ≠ 0) (him : z.im ≤ 0) {t : ℝ} (ht : 0 ≤ t) :
    1 ≤ ‖1 - (t : ℂ) * I / z‖ := by
  rw [show 1 - (t : ℂ) * I / z = (z - t * I) / z by field_simp, norm_div,
    one_le_div (norm_pos_iff.mpr hz0)]
  have h : ‖z‖ ^ 2 ≤ ‖z - t * I‖ ^ 2 := by
    rw [← normSq_eq_norm_sq, ← normSq_eq_norm_sq, normSq_apply, normSq_apply]
    simp only [sub_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
      sub_im, mul_im]
    nlinarith
  nlinarith [norm_nonneg z, norm_nonneg (z - t * I)]

theorem one_le_norm_add {z : ℂ} (hz0 : z ≠ 0) (him : 0 ≤ z.im) {t : ℝ} (ht : 0 ≤ t) :
    1 ≤ ‖1 + (t : ℂ) * I / z‖ := by
  rw [show 1 + (t : ℂ) * I / z = (z + t * I) / z by field_simp, norm_div,
    one_le_div (norm_pos_iff.mpr hz0)]
  have h : ‖z‖ ^ 2 ≤ ‖z + t * I‖ ^ 2 := by
    rw [← normSq_eq_norm_sq, ← normSq_eq_norm_sq, normSq_apply, normSq_apply]
    simp only [add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
      add_im, mul_im, add_zero]
    nlinarith
  nlinarith [norm_nonneg z, norm_nonneg (z + t * I)]

theorem sub_ne_zero_of_re_pos {z : ℂ} (hz : 0 < z.re) (t : ℝ) : 1 - (t : ℂ) * I / z ≠ 0 :=
  fun h => by
    have := re_div_norm_le_sub hz t
    rw [h, norm_zero] at this
    exact absurd this (not_le.mpr (div_pos hz (norm_pos_iff.mpr (ne_zero_of_pos_re hz))))

theorem add_ne_zero_of_re_pos {z : ℂ} (hz : 0 < z.re) (t : ℝ) : 1 + (t : ℂ) * I / z ≠ 0 :=
  fun h => by
    have := re_div_norm_le_add hz t
    rw [h, norm_zero] at this
    exact absurd this (not_le.mpr (div_pos hz (norm_pos_iff.mpr (ne_zero_of_pos_re hz))))

/-- `|1/(1 − it/z)| ≤ s` with `s = sec(ph z)`, or `s = 1` when `ℑz ≤ 0`. -/
theorem norm_inv_sub_le {z : ℂ} (hz : 0 < z.re) {t : ℝ} (ht : 0 ≤ t) {s : ℝ}
    (hs : ‖z‖ / z.re ≤ s ∨ (z.im ≤ 0 ∧ 1 ≤ s)) : ‖(1 - (t : ℂ) * I / z)⁻¹‖ ≤ s := by
  have hz0 := ne_zero_of_pos_re hz
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  rw [norm_inv]
  rcases hs with hs | ⟨him, hs⟩
  · refine le_trans ?_ hs
    rw [inv_le_comm₀ (norm_pos_iff.mpr (sub_ne_zero_of_re_pos hz t)) (div_pos hn hz), inv_div]
    exact re_div_norm_le_sub hz t
  · exact (inv_le_one_of_one_le₀ (one_le_norm_sub hz0 him ht)).trans hs

theorem norm_inv_add_le {z : ℂ} (hz : 0 < z.re) {t : ℝ} (ht : 0 ≤ t) {s : ℝ}
    (hs : ‖z‖ / z.re ≤ s ∨ (0 ≤ z.im ∧ 1 ≤ s)) : ‖(1 + (t : ℂ) * I / z)⁻¹‖ ≤ s := by
  have hz0 := ne_zero_of_pos_re hz
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  rw [norm_inv]
  rcases hs with hs | ⟨him, hs⟩
  · refine le_trans ?_ hs
    rw [inv_le_comm₀ (norm_pos_iff.mpr (add_ne_zero_of_re_pos hz t)) (div_pos hn hz), inv_div]
    exact re_div_norm_le_add hz t
  · exact (inv_le_one_of_one_le₀ (one_le_norm_add hz0 him ht)).trans hs

theorem one_le_norm_div_re {z : ℂ} (hz : 0 < z.re) : 1 ≤ ‖z‖ / z.re := by
  rw [one_le_div hz]; exact re_le_norm z

/-! ### Boyd's remainder and coefficients -/

/-- Boyd's remainder after `n + 1` terms (Nemes (2.1)):
`(2π z^{n+1})⁻¹ (iⁿ ∫₀^∞ tⁿ A(t)/(1 − it/z) dt + (−i)ⁿ ∫₀^∞ tⁿ B(t)/(1 + it/z) dt)`. -/
noncomputable def boydRem (n : ℕ) (z : ℂ) : ℂ :=
  1 / (2 * π * z ^ (n + 1)) *
    (I ^ n * (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ n * boydA t / (1 - t * I / z)) +
      (-I) ^ n * ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ n * boydB t / (1 + t * I / z))

/-- The coefficient of `z^{−(n+1)}`: `(2π)⁻¹ (iⁿ ∫₀^∞ tⁿ A(t) dt + (−i)ⁿ ∫₀^∞ tⁿ B(t) dt)`. -/
noncomputable def boydCoeff (n : ℕ) : ℂ :=
  1 / (2 * π) * (I ^ n * (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ n * boydA t) +
    (-I) ^ n * ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ n * boydB t)

theorem norm_pow_mul_boydA {t : ℝ} (ht : 0 < t) (n : ℕ) :
    ‖(t : ℂ) ^ n * boydA t‖ = t ^ n * boydM t := by
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht.le, norm_boydA ht]

theorem norm_pow_mul_boydB {t : ℝ} (ht : 0 < t) (n : ℕ) :
    ‖(t : ℂ) ^ n * boydB t‖ = t ^ n * boydM t := by
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht.le, norm_boydB ht]

theorem integrableOn_boydA (n : ℕ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ n * boydA t) (Ioi 0) :=
  integrableOn_of_le_boydM (((by fun_prop : Continuous fun t : ℝ => (t : ℂ) ^ n)).continuousOn.mul
    continuousOn_boydA) n (C := 1) fun t ht => by rw [norm_pow_mul_boydA ht, one_mul]

theorem integrableOn_boydB (n : ℕ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ n * boydB t) (Ioi 0) :=
  integrableOn_of_le_boydM (((by fun_prop : Continuous fun t : ℝ => (t : ℂ) ^ n)).continuousOn.mul
    continuousOn_boydB) n (C := 1) fun t ht => by rw [norm_pow_mul_boydB ht, one_mul]

theorem norm_boydA_div_le {z : ℂ} (hz : 0 < z.re) {t : ℝ} (ht : 0 < t) (n : ℕ) {s : ℝ}
    (hs : ‖z‖ / z.re ≤ s ∨ (z.im ≤ 0 ∧ 1 ≤ s)) :
    ‖(t : ℂ) ^ n * boydA t / (1 - t * I / z)‖ ≤ s * (t ^ n * boydM t) := by
  rw [div_eq_mul_inv, norm_mul, norm_pow_mul_boydA ht, mul_comm s]
  exact mul_le_mul_of_nonneg_left (norm_inv_sub_le hz ht.le hs)
    (mul_nonneg (pow_nonneg ht.le n) (boydM_nonneg t))

theorem norm_boydB_div_le {z : ℂ} (hz : 0 < z.re) {t : ℝ} (ht : 0 < t) (n : ℕ) {s : ℝ}
    (hs : ‖z‖ / z.re ≤ s ∨ (0 ≤ z.im ∧ 1 ≤ s)) :
    ‖(t : ℂ) ^ n * boydB t / (1 + t * I / z)‖ ≤ s * (t ^ n * boydM t) := by
  rw [div_eq_mul_inv, norm_mul, norm_pow_mul_boydB ht, mul_comm s]
  exact mul_le_mul_of_nonneg_left (norm_inv_add_le hz ht.le hs)
    (mul_nonneg (pow_nonneg ht.le n) (boydM_nonneg t))

theorem integrableOn_boydA_div {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ n * boydA t / (1 - t * I / z)) (Ioi 0) :=
  integrableOn_of_le_boydM ((((by fun_prop : Continuous fun t : ℝ => (t : ℂ) ^ n)).continuousOn.mul
    continuousOn_boydA).div (by fun_prop) fun t _ => sub_ne_zero_of_re_pos hz t) n
    fun t ht => norm_boydA_div_le hz ht n (Or.inl le_rfl)

theorem integrableOn_boydB_div {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ n * boydB t / (1 + t * I / z)) (Ioi 0) :=
  integrableOn_of_le_boydM ((((by fun_prop : Continuous fun t : ℝ => (t : ℂ) ^ n)).continuousOn.mul
    continuousOn_boydB).div (by fun_prop) fun t _ => add_ne_zero_of_re_pos hz t) n
    fun t ht => norm_boydB_div_le hz ht n (Or.inl le_rfl)

/-- Boyd's formula 5.9.11_1 as `Γ*(z) = 1 + R₁(z)`. -/
theorem scaledGamma_eq_one_add_boydRem {z : ℂ} (hz : 0 < z.re) :
    scaledGamma z = 1 + boydRem 0 z := by
  have hz0 := ne_zero_of_pos_re hz
  rw [dlmf_5_9_11_1 hz, cexp_pi_div_two_I_eq.1, cexp_pi_div_two_I_eq.2, boydRem]
  have e1 : ∫ t in Ioi (0 : ℝ), cexp (-(2 * π * t)) * scaledGamma (t * I) / (t + I * z) =
      (I * z)⁻¹ * ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ 0 * boydA t / (1 - t * I / z) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    have hd := sub_ne_zero_of_re_pos hz t
    have hd' : (t : ℂ) + I * z = I * z * (1 - t * I / z) := by
      field_simp; ring_nf; rw [I_sq]; ring
    rw [boydA, pow_zero, one_mul, hd']
    field_simp
  have e2 : ∫ t in Ioi (0 : ℝ), cexp (-(2 * π * t)) * scaledGamma (t * -I) / (t - I * z) =
      (-(I * z))⁻¹ * ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ 0 * boydB t / (1 + t * I / z) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    have hd := add_ne_zero_of_re_pos hz t
    have hd' : (t : ℂ) - I * z = -(I * z) * (1 + t * I / z) := by
      field_simp; ring_nf; rw [I_sq]; ring
    rw [boydB, pow_zero, one_mul, hd']
    field_simp
  rw [e1, e2]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  ring_nf
  rw [I_sq]
  ring

theorem geom_step_sub (X u : ℂ) (hu : 1 - u ≠ 0) : X / (1 - u) = X + u * X / (1 - u) := by
  field_simp; ring

theorem geom_step_add (X u : ℂ) (hu : 1 + u ≠ 0) : X / (1 + u) = X - u * X / (1 + u) := by
  field_simp; ring

/-- `R_{n+1}(z) = g_{n+1}/z^{n+1} + R_{n+2}(z)` (one more geometric step). -/
theorem boydRem_eq_succ {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    boydRem n z = boydCoeff n / z ^ (n + 1) + boydRem (n + 1) z := by
  have hz0 := ne_zero_of_pos_re hz
  have hA : ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ n * boydA t / (1 - t * I / z) =
      (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ n * boydA t) +
        I / z * ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (n + 1) * boydA t / (1 - t * I / z) := by
    rw [← integral_const_mul, ← integral_add (integrableOn_boydA n)
      ((integrableOn_boydA_div hz (n + 1)).const_mul _)]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [geom_step_sub _ _ (sub_ne_zero_of_re_pos hz t)]
    congr 1
    ring
  have hB : ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ n * boydB t / (1 + t * I / z) =
      (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ n * boydB t) -
        I / z * ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (n + 1) * boydB t / (1 + t * I / z) := by
    rw [← integral_const_mul, ← integral_sub (integrableOn_boydB n)
      ((integrableOn_boydB_div hz (n + 1)).const_mul _)]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [geom_step_add _ _ (add_ne_zero_of_re_pos hz t)]
    congr 1
    ring
  rw [boydRem, boydRem, boydCoeff, hA, hB]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  ring

/-- `Γ*(z) = 1 + ∑_{k<n} c_k/z^{k+1} + R_{n+1}(z)` for `ℜz > 0`. -/
theorem scaledGamma_eq_boyd_sum {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    scaledGamma z = 1 + ∑ k ∈ Finset.range n, boydCoeff k / z ^ (k + 1) + boydRem n z := by
  induction n with
  | zero => simpa using scaledGamma_eq_one_add_boydRem hz
  | succ n ih => rw [ih, boydRem_eq_succ hz n, Finset.sum_range_succ]; ring

/-- `|R_{n+1}(z)| ≤ (1 + sec(ph z)) (2π|z|^{n+1})⁻¹ ∫₀^∞ tⁿ |A(t)| dt` for `ℜz > 0`. -/
theorem norm_boydRem_le {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    ‖boydRem n z‖ ≤ (1 + ‖z‖ / z.re) / (2 * π * ‖z‖ ^ (n + 1)) * boydMom n := by
  have hz0 := ne_zero_of_pos_re hz
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hsec := one_le_norm_div_re hz
  set s := ‖z‖ / z.re
  have hM := boydMom_nonneg n
  -- one kernel is bounded by `sec`, the other by `1`
  obtain ⟨s₁, s₂, hs₁, hs₂, hsum⟩ : ∃ s₁ s₂ : ℝ, (s ≤ s₁ ∨ (z.im ≤ 0 ∧ 1 ≤ s₁)) ∧
      (s ≤ s₂ ∨ (0 ≤ z.im ∧ 1 ≤ s₂)) ∧ s₁ + s₂ = 1 + s := by
    rcases le_total z.im 0 with him | him
    · exact ⟨1, s, Or.inr ⟨him, le_rfl⟩, Or.inl le_rfl, rfl⟩
    · exact ⟨s, 1, Or.inl le_rfl, Or.inr ⟨him, le_rfl⟩, add_comm _ _⟩
  have h1 := norm_integral_le_boydMom (F := fun t : ℝ => (t : ℂ) ^ n * boydA t / (1 - t * I / z))
    n fun t ht => norm_boydA_div_le hz ht n hs₁
  have h2 := norm_integral_le_boydMom (F := fun t : ℝ => (t : ℂ) ^ n * boydB t / (1 + t * I / z))
    n fun t ht => norm_boydB_div_le hz ht n hs₂
  rw [boydRem, norm_mul]
  have hpre : ‖1 / (2 * π * z ^ (n + 1))‖ = 1 / (2 * π * ‖z‖ ^ (n + 1)) := by
    rw [norm_div, norm_one, norm_mul, norm_mul, norm_pow, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
  rw [hpre]
  have hpos : 0 ≤ 1 / (2 * π * ‖z‖ ^ (n + 1)) := by positivity
  calc 1 / (2 * π * ‖z‖ ^ (n + 1)) * ‖I ^ n * (∫ t in Ioi (0 : ℝ),
        (t : ℂ) ^ n * boydA t / (1 - t * I / z)) + (-I) ^ n * ∫ t in Ioi (0 : ℝ),
        (t : ℂ) ^ n * boydB t / (1 + t * I / z)‖
      ≤ 1 / (2 * π * ‖z‖ ^ (n + 1)) * (s₁ * boydMom n + s₂ * boydMom n) := by
        gcongr
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_neg, norm_I, one_pow, one_mul, one_mul]
        exact add_le_add h1 h2
    _ = (1 + s) / (2 * π * ‖z‖ ^ (n + 1)) * boydMom n := by
        rw [← add_mul, hsum]; ring

/-! ### The coefficients are Stirling's -/

/-- The positive real axis as the sector `|ph z| ≤ 0`. -/
theorem mem_closedSector_zero {x : ℂ} (hx : x ∈ closedSectorDLMF 0 (π - π)) :
    0 < x.re ∧ x.im = 0 ∧ ‖x‖ = x.re := by
  obtain ⟨hx0, harg⟩ := hx
  simp only [ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, mul_one, sub_self,
    abs_nonpos_iff] at harg
  obtain ⟨hre, him⟩ := arg_eq_zero_iff.mp harg
  have hre' : 0 < x.re := by
    rcases hre.lt_or_eq with h | h
    · exact h
    · exact absurd (Complex.ext h.symm him) hx0
  refine ⟨hre', him, ?_⟩
  rw [← re_add_im x, him, ofReal_zero, zero_mul, add_zero, Complex.norm_real,
    Real.norm_of_nonneg hre'.le]
  simp

theorem not_isBounded_closedSector_zero :
    ¬ Bornology.IsBounded (closedSectorDLMF 0 (π - π)) := by
  intro hb
  obtain ⟨R, hR⟩ := hb.subset_closedBall 0
  have hmem : ((max R 0 + 1 : ℝ) : ℂ) ∈ closedSectorDLMF 0 (π - π) := by
    refine ⟨ofReal_ne_zero.mpr (by positivity), ?_⟩
    simp only [ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, mul_one, sub_self]
    rw [arg_ofReal_of_nonneg (by positivity)]
    simp
  have := hR hmem
  rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)] at this
  linarith [le_max_left R 0]

/-- The sequence `1, c₀, c₁, …` (`c_k` the coefficient of `z^{−(k+1)}`). -/
noncomputable def boydSeq : ℕ → ℂ
  | 0 => 1
  | k + 1 => boydCoeff k

theorem isAsympExpansion_boydSeq :
    IsAsympExpansionDLMF (closedSectorDLMF 0 (π - π)) scaledGamma boydSeq := by
  intro N hN
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  refine isBoundedUnder_of_eventually_le (a := (1 + 1) / (2 * π) * boydMom n) ?_
  filter_upwards [mem_inf_of_right (mem_principal_self _)] with x hx
  obtain ⟨hre, -, hnorm⟩ := mem_closedSector_zero hx
  have hx0 := ne_zero_of_pos_re hre
  have hsum : scaledGamma x - ∑ s ∈ Finset.range (n + 1), boydSeq s * x ^ (-(s : ℤ)) =
      boydRem n x := by
    rw [scaledGamma_eq_boyd_sum hre n, Finset.sum_range_succ']
    simp only [boydSeq, Nat.cast_zero, neg_zero, zpow_zero, mul_one]
    have : ∀ k ∈ Finset.range n, boydCoeff k * x ^ (-((k + 1 : ℕ) : ℤ)) =
        boydCoeff k / x ^ (k + 1) := fun k _ => by
      rw [zpow_neg, zpow_natCast, div_eq_mul_inv]
    rw [Finset.sum_congr rfl this]
    ring
  rw [hsum, norm_div, zpow_neg, zpow_natCast, norm_inv, norm_pow, div_inv_eq_mul]
  have hb := norm_boydRem_le hre n
  rw [hnorm, div_self hre.ne'] at hb
  rw [hnorm]
  have hp : 0 < x.re ^ (n + 1) := pow_pos hre _
  calc ‖boydRem n x‖ * x.re ^ (n + 1)
      ≤ (1 + 1) / (2 * π * x.re ^ (n + 1)) * boydMom n * x.re ^ (n + 1) := by gcongr
    _ = (1 + 1) / (2 * π) * boydMom n := by field_simp

/-- `c_n = g_{n+1}`: Boyd's moments are the Stirling coefficients. -/
theorem boydCoeff_eq (n : ℕ) : boydCoeff n = (BZ.stirlingCoeff (n + 1) : ℂ) := by
  have h := dlmf_2_1_iii_unique not_isBounded_closedSector_zero isAsympExpansion_boydSeq
    (dlmf_5_11_3 Real.pi_pos le_rfl)
  exact congrFun h (n + 1)

/-- **Boyd's representation of `R_K`** (Nemes (2.1)): for `ℜz > 0`, `R_{n+1}(z)` of 5.11.10 is
`(2π z^{n+1})⁻¹ (iⁿ ∫₀^∞ tⁿ A(t)/(1 − it/z) dt + (−i)ⁿ ∫₀^∞ tⁿ B(t)/(1 + it/z) dt)`. -/
theorem stirlingR_eq_boydRem {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    stirlingR (n + 1) z = boydRem n z := by
  rw [stirlingR, scaledGamma_eq_boyd_sum hz n, Finset.sum_range_succ']
  simp only [BZ.stirlingCoeff_zero, Rat.cast_one, pow_zero, div_one]
  have : ∀ k ∈ Finset.range n, (BZ.stirlingCoeff (k + 1) : ℂ) / z ^ (k + 1) =
      boydCoeff k / z ^ (k + 1) := fun k _ => by rw [boydCoeff_eq]
  rw [Finset.sum_congr rfl this]
  ring

end Azurite.DLMF
