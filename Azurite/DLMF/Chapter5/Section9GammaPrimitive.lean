/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section9PsiEuler

/-!
# DLMF §5.9(ii): the integral of `Γ`

Formalization of <https://dlmf.nist.gov/5.9>, equation 5.9.20 (added in DLMF 1.2.6),
`∫_c^z Γ(t) dt = ∫₀^∞ (t^{z−1} − t^{c−1}) e^{−t} dt/ln t`, `ℜz > 0`, `ℜc > 0`.

The right side `R(z)` is differentiated under the integral sign (`hasDerivAt_gammaPrimitive`):
`∂/∂z t^{z−1}/ln t = t^{z−1}`, so `R′ = Γ` by 5.2.1; the integrand is dominated through the mean
value bound `|t^a − t^b| ≤ |a − b| |ln t| (t^{ℜa} + t^{ℜb})` (`norm_cpow_sub_cpow_le`). Both
sides vanish at `z = c`, so the fundamental theorem of calculus gives 5.9.20:

* `dlmf_5_9_20`: the complex form, `∫_c^z` along the segment from `c` to `z` (which lies in the
  half-plane `ℜ > 0`; by Cauchy's theorem any path there gives the same value), written
  `(z − c) ∫₀¹ Γ(c + s(z − c)) ds`;
* `dlmf_5_9_20_real`: the real form, `∫_c^z Γ(x) dx` for `c, z > 0`.
-/

open Complex Filter Topology Set MeasureTheory
open scoped Real

namespace Azurite.DLMF

/-- The mean value bound `|t^a − t^b| ≤ |a − b| |ln t| (t^{ℜa} + t^{ℜb})` for `t > 0`. -/
theorem norm_cpow_sub_cpow_le {t : ℝ} (ht : 0 < t) (a b : ℂ) :
    ‖(t : ℂ) ^ a - (t : ℂ) ^ b‖ ≤ ‖a - b‖ * |Real.log t| * (t ^ a.re + t ^ b.re) := by
  set g : ℝ → ℂ := fun s => (t : ℂ) ^ (b + s * (a - b)) with hg
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have hd : ∀ s : ℝ, HasDerivAt g ((t : ℂ) ^ (b + s * (a - b)) * Complex.log t * (a - b)) s :=
    fun s => by
      have h1 : HasDerivAt (fun w : ℂ => b + w * (a - b)) (a - b) (s : ℂ) := by
        simpa using ((hasDerivAt_id (s : ℂ)).mul_const (a - b)).const_add b
      exact (h1.const_cpow (Or.inl ht0)).comp_ofReal
  have hbound : ∀ s ∈ Ico (0 : ℝ) 1,
      ‖(t : ℂ) ^ (b + s * (a - b)) * Complex.log t * (a - b)‖ ≤
        ‖a - b‖ * |Real.log t| * (t ^ a.re + t ^ b.re) := fun s hs => by
    rw [norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos ht, ← ofReal_log ht.le,
      Complex.norm_real, Real.norm_eq_abs]
    have hre : (b + s * (a - b)).re = b.re + s * (a.re - b.re) := by simp
    rw [hre]
    have hpow : t ^ (b.re + s * (a.re - b.re)) ≤ t ^ a.re + t ^ b.re := by
      have hA := Real.rpow_pos_of_pos ht a.re
      have hB := Real.rpow_pos_of_pos ht b.re
      rcases le_total 1 t with h1 | h1
      · rcases le_total a.re b.re with hab | hab
        · have : t ^ (b.re + s * (a.re - b.re)) ≤ t ^ b.re :=
            Real.rpow_le_rpow_of_exponent_le h1 (by nlinarith [hs.1])
          linarith
        · have : t ^ (b.re + s * (a.re - b.re)) ≤ t ^ a.re :=
            Real.rpow_le_rpow_of_exponent_le h1 (by nlinarith [hs.2])
          linarith
      · rcases le_total a.re b.re with hab | hab
        · have : t ^ (b.re + s * (a.re - b.re)) ≤ t ^ a.re :=
            Real.rpow_le_rpow_of_exponent_ge ht h1 (by nlinarith [hs.2])
          linarith
        · have : t ^ (b.re + s * (a.re - b.re)) ≤ t ^ b.re :=
            Real.rpow_le_rpow_of_exponent_ge ht h1 (by nlinarith [hs.1])
          linarith
    calc t ^ (b.re + s * (a.re - b.re)) * |Real.log t| * ‖a - b‖
        ≤ (t ^ a.re + t ^ b.re) * |Real.log t| * ‖a - b‖ := by gcongr
      _ = _ := by ring
  have h := norm_image_sub_le_of_norm_deriv_le_segment' (a := 0) (b := 1)
    (fun s _ => (hd s).hasDerivWithinAt) hbound 1 (right_mem_Icc.mpr zero_le_one)
  simp only [hg, ofReal_one, one_mul, ofReal_zero, zero_mul, add_zero, add_sub_cancel] at h
  simpa using h

/-- The integrand `(t^{w−1} − t^{c−1}) e^{−t}/ln t` of 5.9.20. -/
noncomputable def gammaPrimitiveIntegrand (c w : ℂ) (t : ℝ) : ℂ :=
  ((t : ℂ) ^ (w - 1) - (t : ℂ) ^ (c - 1)) / Real.log t * Real.exp (-t)

/-- The right side of 5.9.20. -/
noncomputable def gammaPrimitive (c w : ℂ) : ℂ := ∫ t in Ioi (0 : ℝ), gammaPrimitiveIntegrand c w t

theorem norm_gammaPrimitiveIntegrand_le (c w : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖gammaPrimitiveIntegrand c w t‖ ≤
      ‖w - c‖ * (Real.exp (-t) * t ^ (w.re - 1) + Real.exp (-t) * t ^ (c.re - 1)) := by
  rw [gammaPrimitiveIntegrand, norm_mul, norm_div, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_of_nonneg (Real.exp_pos _).le]
  have h := norm_cpow_sub_cpow_le ht (w - 1) (c - 1)
  simp only [sub_re, one_re, sub_sub_sub_cancel_right] at h
  rcases eq_or_ne (Real.log t) 0 with hl | hl
  · rw [hl, abs_zero, div_zero, zero_mul]
    have := Real.exp_pos (-t)
    positivity
  · have hpos := abs_pos.mpr hl
    calc ‖(t : ℂ) ^ (w - 1) - (t : ℂ) ^ (c - 1)‖ / |Real.log t| * Real.exp (-t)
        ≤ ‖w - c‖ * |Real.log t| * (t ^ (w.re - 1) + t ^ (c.re - 1)) / |Real.log t| *
          Real.exp (-t) := by gcongr
      _ = _ := by field_simp

theorem integrableOn_exp_neg_mul_rpow {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ (s - 1)) (Ioi 0) :=
  Real.GammaIntegral_convergent hs

theorem aestronglyMeasurable_gammaPrimitiveIntegrand (c w : ℂ) :
    AEStronglyMeasurable (gammaPrimitiveIntegrand c w) (volume.restrict (Ioi 0)) := by
  unfold gammaPrimitiveIntegrand
  refine Measurable.aestronglyMeasurable ?_
  fun_prop

theorem integrableOn_gammaPrimitiveIntegrand {c w : ℂ} (hc : 0 < c.re) (hw : 0 < w.re) :
    IntegrableOn (gammaPrimitiveIntegrand c w) (Ioi 0) :=
  (((integrableOn_exp_neg_mul_rpow hw).add (integrableOn_exp_neg_mul_rpow hc)).const_mul
    ‖w - c‖).mono' (aestronglyMeasurable_gammaPrimitiveIntegrand c w)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun _ ht =>
      norm_gammaPrimitiveIntegrand_le c w ht))

theorem hasDerivAt_gammaPrimitive {c z : ℂ} (hc : 0 < c.re) (hz : 0 < z.re) :
    HasDerivAt (gammaPrimitive c) (Gamma z) z := by
  set r := z.re / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hre : ∀ w ∈ Metric.ball z r, r < w.re ∧ w.re < 2 * z.re := fun w hw => by
    have := (Complex.abs_re_le_norm (w - z)).trans_lt (by rwa [← dist_eq_norm])
    rw [sub_re, abs_lt] at this
    constructor <;> linarith [this.1, this.2]
  have hne1 : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), t ≠ 1 :=
    ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp (Real.volume_singleton (a := 1)))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun w t => gammaPrimitiveIntegrand c w t)
    (F' := fun w (t : ℝ) => (t : ℂ) ^ (w - 1) * Real.exp (-t)) (x₀ := z)
    (bound := fun t => Real.exp (-t) * t ^ (r - 1) + Real.exp (-t) * t ^ (2 * z.re - 1))
    (Metric.ball_mem_nhds z hr0)
    (Eventually.of_forall fun w => aestronglyMeasurable_gammaPrimitiveIntegrand c w)
    (integrableOn_gammaPrimitiveIntegrand hc hz)
    (by
      refine Measurable.aestronglyMeasurable ?_
      fun_prop)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht w hw => by
      have ht' : (0 : ℝ) < t := ht
      obtain ⟨h1, h2⟩ := hre w hw
      rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht', Complex.norm_real,
        Real.norm_of_nonneg (Real.exp_pos _).le, sub_re, one_re, mul_comm]
      have hA := Real.rpow_pos_of_pos ht' (r - 1)
      have hB := Real.rpow_pos_of_pos ht' (2 * z.re - 1)
      have hE := Real.exp_pos (-t)
      rcases le_total 1 t with h | h
      · have : t ^ (w.re - 1) ≤ t ^ (2 * z.re - 1) :=
          Real.rpow_le_rpow_of_exponent_le h (by linarith)
        nlinarith
      · have : t ^ (w.re - 1) ≤ t ^ (r - 1) :=
          Real.rpow_le_rpow_of_exponent_ge ht' h (by linarith)
        nlinarith))
    ((integrableOn_exp_neg_mul_rpow hr0).add (integrableOn_exp_neg_mul_rpow (by linarith)))
    (by
      filter_upwards [hne1, ae_restrict_mem measurableSet_Ioi] with t h1 ht w _
      have ht' : (0 : ℝ) < t := ht
      have hl : Real.log t ≠ 0 := fun h => h1 (Real.eq_one_of_pos_of_log_eq_zero ht' h)
      have hl' : (Real.log t : ℂ) ≠ 0 := ofReal_ne_zero.mpr hl
      have h0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht'.ne'
      have hd : HasDerivAt (fun w : ℂ => (t : ℂ) ^ (w - 1))
          ((t : ℂ) ^ (w - 1) * Complex.log t * 1) w :=
        ((hasDerivAt_id w).sub_const 1).const_cpow (Or.inl h0)
      have := ((hd.sub_const ((t : ℂ) ^ (c - 1))).div_const (Real.log t : ℂ)).mul_const
        ((Real.exp (-t) : ℝ) : ℂ)
      refine this.congr_deriv ?_
      rw [← ofReal_log ht'.le]
      field_simp)
  have hG : ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (z - 1) * Real.exp (-t) = Gamma z := by
    rw [Gamma_eq_integral hz, GammaIntegral]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only
    push_cast
    ring
  rw [← hG]
  exact key.2

theorem gammaPrimitive_self (c : ℂ) : gammaPrimitive c c = 0 := by
  simp [gammaPrimitive, gammaPrimitiveIntegrand]

/-- **DLMF 5.9.20**: for `ℜz > 0`, `ℜc > 0`,
`∫_c^z Γ(t) dt = ∫₀^∞ (t^{z−1} − t^{c−1}) e^{−t} dt/ln t`, the left side along the segment from
`c` to `z`, `∫_c^z Γ(t) dt = (z − c) ∫₀¹ Γ(c + s(z − c)) ds`. -/
theorem dlmf_5_9_20 {z c : ℂ} (hz : 0 < z.re) (hc : 0 < c.re) :
    (z - c) * ∫ s in (0 : ℝ)..1, Gamma (c + s * (z - c)) =
      ∫ t in Ioi (0 : ℝ), ((t : ℂ) ^ (z - 1) - (t : ℂ) ^ (c - 1)) / Real.log t * Real.exp (-t) := by
  have hpos : ∀ s ∈ uIcc (0 : ℝ) 1, 0 < (c + s * (z - c)).re := fun s hs => by
    rw [uIcc_of_le zero_le_one] at hs
    have : (c + s * (z - c)).re = (1 - s) * c.re + s * z.re := by simp; ring
    rw [this]
    rcases eq_or_lt_of_le hs.1 with h | h
    · rw [← h]; simp [hc]
    · have : 0 ≤ 1 - s := by linarith [hs.2]
      positivity
  have hd : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => gammaPrimitive c (c + s * (z - c)))
      (Gamma (c + s * (z - c)) * (z - c)) s := fun s hs => by
    have h1 : HasDerivAt (fun w : ℂ => c + w * (z - c)) (z - c) (s : ℂ) := by
      simpa using ((hasDerivAt_id (s : ℂ)).mul_const (z - c)).const_add c
    exact ((hasDerivAt_gammaPrimitive hc (hpos s hs)).comp (s : ℂ) h1).comp_ofReal
  have hcont : ContinuousOn (fun s : ℝ => Gamma (c + s * (z - c)) * (z - c)) (uIcc 0 1) :=
    fun s hs => ((differentiableAt_Gamma _ fun m h => by
      have := hpos s hs
      rw [h] at this
      simp at this
      linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]).continuousAt.comp
      (by fun_prop : Continuous fun s : ℝ => c + s * (z - c)).continuousAt).mul
      continuousAt_const |>.continuousWithinAt
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable)
  rw [intervalIntegral.integral_mul_const] at h
  simp only [ofReal_one, one_mul, add_sub_cancel, ofReal_zero, zero_mul, add_zero,
    gammaPrimitive_self, sub_zero] at h
  rw [mul_comm, h]
  rfl

/-- **DLMF 5.9.20**, real form: for `c, z > 0`,
`∫_c^z Γ(x) dx = ∫₀^∞ (t^{z−1} − t^{c−1}) e^{−t} dt/ln t`. -/
theorem dlmf_5_9_20_real {z c : ℝ} (hz : 0 < z) (hc : 0 < c) :
    ∫ x in c..z, Real.Gamma x =
      ∫ t in Ioi (0 : ℝ), (t ^ (z - 1) - t ^ (c - 1)) / Real.log t * Real.exp (-t) := by
  have hpos : ∀ x ∈ uIcc c z, 0 < x := fun x hx =>
    lt_of_lt_of_le (lt_min hc hz) (by rw [uIcc] at hx; exact hx.1)
  have hd : ∀ x ∈ uIcc c z, HasDerivAt (fun x : ℝ => gammaPrimitive c (x : ℂ))
      ((Real.Gamma x : ℝ) : ℂ) x := fun x hx => by
    rw [← Gamma_ofReal]
    exact (hasDerivAt_gammaPrimitive (by simpa using hc) (by simpa using hpos x hx)).comp_ofReal
  have hcont : ContinuousOn (fun x : ℝ => ((Real.Gamma x : ℝ) : ℂ)) (uIcc c z) := fun x hx =>
    (continuous_ofReal.continuousAt.comp (Real.differentiableAt_Gamma fun m h => by
      have := hpos x hx
      rw [h] at this
      linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]).continuousAt).continuousWithinAt
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hcont.intervalIntegrable
  rw [intervalIntegral.integral_ofReal, gammaPrimitive_self, sub_zero, gammaPrimitive] at h
  have e : ∫ t in Ioi (0 : ℝ), gammaPrimitiveIntegrand c z t = ∫ t in Ioi (0 : ℝ),
      (((t ^ (z - 1) - t ^ (c - 1)) / Real.log t * Real.exp (-t) : ℝ) : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht' : (0 : ℝ) ≤ t := le_of_lt ht
    simp only [gammaPrimitiveIntegrand]
    push_cast
    rw [ofReal_cpow ht', ofReal_cpow ht']
    push_cast
    ring
  rw [e, integral_complex_ofReal] at h
  exact_mod_cast h

end Azurite.DLMF
