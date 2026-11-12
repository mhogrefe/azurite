/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section12Pochhammer
import Azurite.DLMF.Chapter5.Section6Stirling
import Azurite.DLMF.Chapter1.Section14Mellin
import Azurite.DLMF.Chapter2.Section1Ritt

/-!
# DLMF §5.13: Integrals — the Mellin–Barnes pair

Formalization of <https://dlmf.nist.gov/5.13>, groundwork and 5.13.1–5.13.2.

* `Γ(s + a)Γ(b − s)` is the Mellin transform of `Γ(a + b)xᵃ(1 + x)^{−a−b}` in the strip
  `−ℜa < ℜs < ℜb` (`mellin_mellinPair`, from 5.12.3).
* On vertical lines `|Γ(w + it)| ≤ C_ε e^{−(π/2−ε)|t|}` for `ℜw > 0` (`exists_bound_Gamma_line`,
  from 5.6.9), so `Γ(s + a)Γ(b − s)` is integrable on `ℜs = c`.
* 5.13.1 (`dlmf_5_13_1`): Mellin inversion (1.14.35) for `z > 0`, then analytic continuation to
  `|ph z| < π` (`differentiableOn_integral_of_holo`, identity theorem on the slit plane).
* 5.13.2 (`dlmf_5_13_2`): 5.13.1 with `c = 0`, `b = a`, `z = e^{i(π−2b)}`.
-/

open Complex Filter Topology Set MeasureTheory
open scoped Real Nat

namespace Azurite.DLMF

/-! ### Exponential bounds -/

/-- `e^{−c|t|}` is integrable. -/
theorem integrable_exp_neg_mul_abs {c : ℝ} (hc : 0 < c) :
    Integrable fun t : ℝ => Real.exp (-(c * |t|)) := by
  refine (integrable_inv_one_add_sq.const_mul (max 1 (2 / c ^ 2))).mono'
    (by fun_prop : Continuous fun t : ℝ => Real.exp (-(c * |t|))).aestronglyMeasurable
    (ae_of_all _ fun t => ?_)
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_neg]
  have h := Real.quadratic_le_exp_of_nonneg (by positivity : 0 ≤ c * |t|)
  have hpos : 0 < 1 + t ^ 2 := by positivity
  rw [inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
  have h1 : (1 : ℝ) + t ^ 2 ≤ max 1 (2 / c ^ 2) * (1 + (c * |t|) ^ 2 / 2) := by
    have hm1 := le_max_left 1 (2 / c ^ 2)
    have hm2 := le_max_right 1 (2 / c ^ 2)
    have e : (c * |t|) ^ 2 = c ^ 2 * t ^ 2 := by rw [mul_pow, sq_abs]
    rw [e]
    have hc2 : 0 < c ^ 2 := by positivity
    have : t ^ 2 ≤ 2 / c ^ 2 * (c ^ 2 * t ^ 2 / 2) := by
      field_simp; rfl
    nlinarith [sq_nonneg t]
  calc (1 : ℝ) = (1 + t ^ 2)⁻¹ * (1 + t ^ 2) := by field_simp
    _ ≤ (1 + t ^ 2)⁻¹ * (max 1 (2 / c ^ 2) * (1 + (c * |t|) ^ 2 / 2)) := by gcongr
    _ ≤ (1 + t ^ 2)⁻¹ * (max 1 (2 / c ^ 2) * Real.exp (c * |t|)) := by
        gcongr; linarith [h, mul_nonneg hc.le (abs_nonneg t)]
    _ = _ := by ring

/-- `(1 + u)^n ≤ (n!/εⁿ) e^ε e^{εu}`. -/
theorem one_add_pow_le_exp {ε u : ℝ} (hε : 0 < ε) (hu : 0 ≤ u) (n : ℕ) :
    (1 + u) ^ n ≤ (Nat.factorial n : ℝ) / ε ^ n * Real.exp ε * Real.exp (ε * u) := by
  have h := Real.pow_div_factorial_le_exp _ (by positivity : 0 ≤ ε * (1 + u)) n
  rw [div_le_iff₀ (by positivity), mul_pow] at h
  rw [mul_assoc, ← Real.exp_add, show ε + ε * u = ε * (1 + u) by ring, div_mul_eq_mul_div,
    le_div_iff₀ (by positivity)]
  nlinarith [h]

/-- **Decay of `Γ` on vertical lines**: `|Γ(w + it)| ≤ C e^{−(π/2−ε)|t|}` for `ℜw > 0`. -/
theorem exists_bound_Gamma_line {w : ℂ} (hw : 0 < w.re) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖Gamma (w + t * I)‖ ≤ C * Real.exp (-((π / 2 - ε) * |t|)) := by
  set x := w.re
  set p := x - 1 / 2
  set n := Nat.ceil p
  set B := x ^ p + (1 + ‖w‖) ^ p
  set K := (Nat.factorial n : ℝ) / ε ^ n * Real.exp ε
  refine ⟨Real.sqrt (2 * π) * B * K * Real.exp (π * |w.im| / 2) * Real.exp (1 / 6 * x⁻¹),
    by positivity, fun t => ?_⟩
  set z := w + t * I
  have hzre : z.re = x := by simp [z, x]
  have hzim : z.im = w.im + t := by simp [z]
  have hz : 0 < z.re := by rw [hzre]; exact hw
  have hzn : x ≤ ‖z‖ := hzre ▸ re_le_norm z
  have hzup : ‖z‖ ≤ (1 + ‖w‖) * (1 + |t|) := by
    have := norm_add_le w (t * I)
    simp only [norm_mul, norm_real, Real.norm_eq_abs, norm_I, mul_one] at this
    nlinarith [norm_nonneg w, abs_nonneg t]
  have h1 := norm_Gamma_le_of_re_pos hz
  rw [hzre, hzim] at h1
  -- the power
  have hpow : ‖z‖ ^ p ≤ B * (1 + |t|) ^ n := by
    have h1t : (1 : ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
    have hn1 : 1 ≤ (1 + |t|) ^ n := one_le_pow₀ h1t
    rcases le_total p 0 with hp | hp
    · have := Real.rpow_le_rpow_of_nonpos hw hzn hp
      calc ‖z‖ ^ p ≤ x ^ p := this
        _ ≤ B := by simp only [B]; linarith [Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 1 + ‖w‖) p]
        _ ≤ B * (1 + |t|) ^ n := le_mul_of_one_le_right (by positivity) hn1
    · have h2 := Real.rpow_le_rpow (norm_nonneg _) hzup hp
      rw [Real.mul_rpow (by positivity) (by positivity)] at h2
      have h3 : (1 + |t|) ^ p ≤ (1 + |t|) ^ n := by
        rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le h1t (Nat.le_ceil p)
      calc ‖z‖ ^ p ≤ (1 + ‖w‖) ^ p * (1 + |t|) ^ p := h2
        _ ≤ B * (1 + |t|) ^ n := by
          gcongr
          simp only [B]; linarith [Real.rpow_nonneg hw.le p]
  have hpoly := one_add_pow_le_exp hε (abs_nonneg t) n
  have hexp : Real.exp (-(π * |w.im + t|) / 2) ≤
      Real.exp (π * |w.im| / 2) * Real.exp (-(π / 2 * |t|)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have := abs_sub_abs_le_abs_sub t (-w.im)
    rw [sub_neg_eq_add, add_comm t, abs_neg] at this
    nlinarith [Real.pi_pos]
  have hlast : Real.exp (1 / 6 * ‖z‖⁻¹) ≤ Real.exp (1 / 6 * x⁻¹) :=
    Real.exp_le_exp.mpr (by gcongr)
  calc ‖Gamma z‖ ≤ Real.sqrt (2 * π) * ‖z‖ ^ p * Real.exp (-(π * |w.im + t|) / 2) *
        Real.exp (1 / 6 * ‖z‖⁻¹) := h1
    _ ≤ Real.sqrt (2 * π) * (B * (K * Real.exp (ε * |t|))) *
        (Real.exp (π * |w.im| / 2) * Real.exp (-(π / 2 * |t|))) *
        Real.exp (1 / 6 * x⁻¹) := by
        gcongr
        exact hpow.trans (mul_le_mul_of_nonneg_left hpoly (by positivity))
    _ = Real.sqrt (2 * π) * B * K * Real.exp (π * |w.im| / 2) * Real.exp (1 / 6 * x⁻¹) *
        (Real.exp (ε * |t|) * Real.exp (-(π / 2 * |t|))) := by ring
    _ = _ := by
        rw [← Real.exp_add]; congr 2; ring

/-- Continuity of `Γ` on a vertical line in `ℜ > 0`. -/
theorem continuous_Gamma_line {w : ℂ} (hw : 0 < w.re) :
    Continuous fun t : ℝ => Gamma (w + t * I) := by
  refine continuous_iff_continuousAt.mpr fun t => ?_
  have hre : 0 < (w + t * I).re := by simpa using hw
  exact ((Complex.differentiableAt_Gamma _ fun m h => by
    have := congrArg re h; simp at this
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]).continuousAt).comp (f := fun t : ℝ => w + t * I)
    (by fun_prop)

/-- `Γ(w + it)Γ(w' − it)` is bounded by `C e^{−(π−2ε)|t|}` for `ℜw, ℜw' > 0`. -/
theorem exists_bound_Gamma_pair {w w' : ℂ} (hw : 0 < w.re) (hw' : 0 < w'.re) {ε : ℝ}
    (hε : 0 < ε) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖Gamma (w + t * I) * Gamma (w' - t * I)‖ ≤ C * Real.exp (-((π - 2 * ε) * |t|)) := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_bound_Gamma_line hw hε
  obtain ⟨C₂, hC₂, h₂⟩ := exists_bound_Gamma_line hw' hε
  refine ⟨C₁ * C₂, by positivity, fun t => ?_⟩
  have h2 := h₂ (-t)
  rw [show w' + ((-t : ℝ) : ℂ) * I = w' - t * I by push_cast; ring, abs_neg] at h2
  rw [norm_mul]
  calc ‖Gamma (w + t * I)‖ * ‖Gamma (w' - t * I)‖
      ≤ (C₁ * Real.exp (-((π / 2 - ε) * |t|))) * (C₂ * Real.exp (-((π / 2 - ε) * |t|))) :=
        mul_le_mul (h₁ t) h2 (norm_nonneg _) (by positivity)
    _ = _ := by rw [mul_mul_mul_comm, ← Real.exp_add]; congr 2; ring

/-! ### The Mellin pair -/

/-- `Γ(a + b)xᵃ(1 + x)^{−a−b}`, whose Mellin transform is `Γ(s + a)Γ(b − s)`. -/
noncomputable def mellinPair (a b : ℂ) (x : ℝ) : ℂ :=
  Gamma (a + b) * (x : ℂ) ^ a * (1 + (x : ℂ)) ^ (-(a + b))

theorem mellinPair_integrand_eq (a b s : ℂ) {x : ℝ} (hx : 0 < x) :
    (x : ℂ) ^ (s - 1) • mellinPair a b x =
      Gamma (a + b) * ((x : ℂ) ^ (s + a - 1) / (1 + (x : ℂ)) ^ (s + a + (b - s))) := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  rw [smul_eq_mul, mellinPair, show s + a + (b - s) = a + b by ring,
    show s + a - 1 = (s - 1) + a by ring, cpow_add _ _ hx0, cpow_neg, div_eq_mul_inv]
  ring

theorem mellinConvergent_mellinPair {a b s : ℂ} (ha : 0 < (s + a).re) (hb : 0 < (b - s).re) :
    MellinConvergent (mellinPair a b) s := by
  have h := (integrableOn_beta_Ioi ha hb).const_mul (Gamma (a + b))
  exact IntegrableOn.congr_fun h (fun x hx => (mellinPair_integrand_eq a b s hx).symm)
    measurableSet_Ioi

/-- **The Mellin pair**: `𝓜[Γ(a + b)xᵃ(1 + x)^{−a−b}](s) = Γ(s + a)Γ(b − s)` for
`−ℜa < ℜs < ℜb`. -/
theorem mellin_mellinPair {a b s : ℂ} (ha : 0 < (s + a).re) (hb : 0 < (b - s).re) :
    mellin (mellinPair a b) s = Gamma (s + a) * Gamma (b - s) := by
  have hab : 0 < (a + b).re := by
    have := add_pos ha hb; simp only [add_re, sub_re] at this ⊢; linarith
  rw [mellin,
    setIntegral_congr_fun measurableSet_Ioi (fun x hx => mellinPair_integrand_eq a b s hx),
    integral_const_mul, dlmf_5_12_3 ha hb, dlmfBeta, show s + a + (b - s) = a + b by ring]
  field_simp [Complex.Gamma_ne_zero_of_re_pos hab]

theorem continuousAt_mellinPair (a b : ℂ) {x : ℝ} (hx : 0 < x) :
    ContinuousAt (mellinPair a b) x := by
  have h1 : (1 : ℂ) + x ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inl (by simp; linarith))
  refine (continuousAt_const.mul (continuousAt_ofReal_cpow_const _ _ (Or.inr hx.ne'))).mul ?_
  exact ContinuousAt.cpow (by fun_prop) continuousAt_const h1

/-- The Mellin–Barnes integrand `G(t) = Γ(c + it + a)Γ(b − c − it)`. -/
noncomputable def mbG (a b : ℂ) (c t : ℝ) : ℂ :=
  Gamma ((c : ℂ) + t * I + a) * Gamma (b - ((c : ℂ) + t * I))

theorem continuous_mbG {a b : ℂ} {c : ℝ} (ha : 0 < c + a.re) (hb : c < b.re) :
    Continuous (mbG a b c) := by
  have hw : 0 < ((c : ℂ) + a).re := by simpa using ha
  have hw' : 0 < (b - c).re := by simp; linarith
  exact ((continuous_Gamma_line hw).congr fun t => by ring_nf).mul
    (((continuous_Gamma_line hw').comp continuous_neg).congr fun t => by
      simp only [Function.comp, ofReal_neg]; ring_nf)

theorem exists_bound_mbG {a b : ℂ} {c : ℝ} (ha : 0 < c + a.re) (hb : c < b.re) {ε : ℝ}
    (hε : 0 < ε) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖mbG a b c t‖ ≤ C * Real.exp (-((π - 2 * ε) * |t|)) := by
  have hw : 0 < ((c : ℂ) + a).re := by simpa using ha
  have hw' : 0 < (b - c).re := by simp; linarith
  obtain ⟨C, hC0, hC⟩ := exists_bound_Gamma_pair hw hw' hε
  refine ⟨C, hC0, fun t => ?_⟩
  have := hC t
  rw [show (c : ℂ) + a + t * I = (c : ℂ) + t * I + a by ring,
    show b - (c : ℂ) - t * I = b - ((c : ℂ) + t * I) by ring] at this
  exact this

/-- `Γ(c + it + a)Γ(b − c − it)` is integrable for `−ℜa < c < ℜb`. -/
theorem integrable_mbG {a b : ℂ} {c : ℝ} (ha : 0 < c + a.re) (hb : c < b.re) :
    Integrable (mbG a b c) := by
  obtain ⟨C, -, hC⟩ := exists_bound_mbG ha hb (ε := π / 4) (by positivity)
  refine ((integrable_exp_neg_mul_abs (c := π / 2) (by positivity)).const_mul C).mono'
    (continuous_mbG ha hb).aestronglyMeasurable (ae_of_all _ fun t => ?_)
  refine (hC t).trans (le_of_eq ?_)
  congr 2; ring

theorem verticalIntegrable_mellinPair {a b : ℂ} {c : ℝ} (ha : 0 < c + a.re) (hb : c < b.re) :
    VerticalIntegrable (mellin (mellinPair a b)) c := by
  refine (integrable_mbG ha hb).congr (ae_of_all _ fun t => ?_)
  simp only [mbG]
  rw [mellin_mellinPair (by simpa using ha) (by simp; linarith)]

/-! ### 5.13.1 -/

theorem mellinPair_eq (a b : ℂ) (x : ℝ) :
    mellinPair a b x = Gamma (a + b) * (x : ℂ) ^ a / (1 + (x : ℂ)) ^ (a + b) := by
  rw [mellinPair, cpow_neg, div_eq_mul_inv]

/-- 5.13.1 for `z = x > 0` (Mellin inversion). -/
theorem dlmf_5_13_1_pos {a b : ℂ} {c : ℝ} (ha : -a.re < c) (hb : c < b.re) {x : ℝ}
    (hx : 0 < x) : (2 * π : ℂ)⁻¹ * ∫ t : ℝ, mbG a b c t * (x : ℂ) ^ (-((c : ℂ) + t * I)) =
      Gamma (a + b) * (x : ℂ) ^ a / (1 + (x : ℂ)) ^ (a + b) := by
  have ha' : 0 < c + a.re := by linarith
  have h := dlmf_1_14_35 (mellinConvergent_mellinPair (s := c) (by simpa using ha')
    (by simp; linarith)) (verticalIntegrable_mellinPair ha' hb) hx (continuousAt_mellinPair a b hx)
  rw [← mellinPair_eq, h]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only
  rw [mellin_mellinPair (by simpa using ha') (by simp; linarith), mbG]
  ring

theorem one_add_mem_slitPlane_of_mem {z : ℂ} (hz : z ∈ slitPlane) : 1 + z ∈ slitPlane := by
  rw [mem_slitPlane_iff] at hz ⊢
  rcases hz with h | h
  · left; simp; linarith
  · right; simpa using h

/-- `‖z^{−(c+it)}‖ = ‖z‖^{−c} e^{t ph z}`. -/
theorem norm_cpow_neg_line {z : ℂ} (hz : z ≠ 0) (c t : ℝ) :
    ‖z ^ (-((c : ℂ) + t * I))‖ = ‖z‖ ^ (-c) * Real.exp (arg z * t) := by
  rw [norm_cpow_of_ne_zero hz]
  simp only [neg_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, sub_zero,
    mul_one, add_zero, neg_im, add_im, zero_add]
  rw [div_eq_mul_inv, ← Real.exp_neg]
  simp

/-- The left side of 5.13.1 is holomorphic in `z` on the slit plane. -/
theorem differentiableOn_mb {a b : ℂ} {c : ℝ} (ha : 0 < c + a.re) (hb : c < b.re) :
    DifferentiableOn ℂ (fun z : ℂ => ∫ t : ℝ, mbG a b c t * z ^ (-((c : ℂ) + t * I)))
      slitPlane := by
  have hG := continuous_mbG ha hb
  refine differentiableOn_integral_of_holo
    (F := fun z (t : ℝ) => mbG a b c t * z ^ (-((c : ℂ) + t * I)))
    (F' := fun z (t : ℝ) => mbG a b c t * ((-((c : ℂ) + t * I)) * z ^ (-((c : ℂ) + t * I) - 1)))
    (fun z hz => (hG.mul ((by fun_prop : Continuous fun t : ℝ => -((c : ℂ) + t * I)).const_cpow
      (Or.inl (slitPlane_ne_zero hz)))).aestronglyMeasurable)
    (fun z hz => (hG.mul ((by fun_prop : Continuous fun t : ℝ => -((c : ℂ) + t * I)).mul
      ((by fun_prop : Continuous fun t : ℝ => -((c : ℂ) + t * I) - 1).const_cpow
        (Or.inl (slitPlane_ne_zero hz))))).aestronglyMeasurable)
    fun z₀ hz₀ => ?_
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp isOpen_slitPlane z₀ hz₀
  set r := ρ / 4
  have hr : 0 < r := by positivity
  set K := Metric.closedBall z₀ (2 * r)
  have hKs : K ⊆ slitPlane := fun z hz => hball (by
    have := Metric.mem_closedBall.mp hz; rw [Metric.mem_ball]; simp only [r] at this; linarith)
  have hKc : IsCompact K := isCompact_closedBall _ _
  have hKne : K.Nonempty := ⟨z₀, Metric.mem_closedBall_self (by positivity)⟩
  -- uniform bounds on `K`
  obtain ⟨zA, hzA, hA⟩ := hKc.exists_isMaxOn hKne
    (f := fun z => |arg z|) (fun z hz => ((continuousAt_arg (hKs hz)).abs).continuousWithinAt)
  obtain ⟨zm, hzm, hm⟩ := hKc.exists_isMinOn hKne (f := fun z => ‖z‖) continuous_norm.continuousOn
  set A := |arg zA|
  have hAπ : A < π := lt_of_le_of_ne (abs_arg_le_pi zA) fun h => by
    have := hKs hzA
    rw [mem_slitPlane_iff_arg] at this
    rcases abs_eq (Real.pi_pos.le) |>.mp h with h' | h'
    · exact this.1 h'
    · exact absurd h' (by linarith [neg_pi_lt_arg zA])
  set m := ‖zm‖
  have hm0 : 0 < m := norm_pos_iff.mpr (slitPlane_ne_zero (hKs hzm))
  set M := ‖z₀‖ + 2 * r
  set η := π - A
  have hη : 0 < η := by simp only [η]; linarith
  obtain ⟨C, hC0, hC⟩ := exists_bound_mbG ha hb (ε := η / 4) (by positivity)
  refine ⟨r, hr, fun z hz => hKs (Metric.ball_subset_closedBall.trans
    (Metric.closedBall_subset_closedBall (by linarith)) hz),
    fun t => C * (m ^ (-c) + M ^ (-c)) * Real.exp (-(η / 2 * |t|)),
    (integrable_exp_neg_mul_abs (by positivity)).const_mul _, ae_of_all _ fun t z hz => ?_,
    ae_of_all _ fun t z hz => ?_⟩
  · have hs := hKs hz
    have := ((hasDerivAt_id z).cpow_const (c := -((c : ℂ) + t * I)) hs).const_mul (mbG a b c t)
    simpa [mul_comm, mul_assoc, mul_left_comm] using this
  · have hs := hKs hz
    have hz0 := slitPlane_ne_zero hs
    rw [norm_mul, norm_cpow_neg_line hz0]
    have hzn : m ≤ ‖z‖ := hm hz
    have hzM : ‖z‖ ≤ M := by
      have := Metric.mem_closedBall.mp hz
      rw [dist_eq_norm] at this
      have := norm_le_insert' z z₀
      simp only [M]; linarith
    have hpow : ‖z‖ ^ (-c) ≤ m ^ (-c) + M ^ (-c) := by
      rcases le_total 0 (-c) with h | h
      · have := Real.rpow_le_rpow (norm_nonneg _) hzM h
        linarith [Real.rpow_nonneg hm0.le (-c)]
      · have := Real.rpow_le_rpow_of_nonpos hm0 hzn h
        linarith [Real.rpow_nonneg (hm0.le.trans (hzn.trans hzM)) (-c)]
    have harg : Real.exp (arg z * t) ≤ Real.exp (A * |t|) := by
      refine Real.exp_le_exp.mpr ((le_abs_self _).trans ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hA hz) (abs_nonneg _)
    calc ‖mbG a b c t‖ * (‖z‖ ^ (-c) * Real.exp (arg z * t))
        ≤ (C * Real.exp (-((π - 2 * (η / 4)) * |t|))) * ((m ^ (-c) + M ^ (-c)) *
          Real.exp (A * |t|)) := by gcongr; exact hC t
      _ = C * (m ^ (-c) + M ^ (-c)) * Real.exp (-(η / 2 * |t|)) := by
          rw [show C * Real.exp (-((π - 2 * (η / 4)) * |t|)) * ((m ^ (-c) + M ^ (-c)) *
              Real.exp (A * |t|)) = C * (m ^ (-c) + M ^ (-c)) *
              (Real.exp (-((π - 2 * (η / 4)) * |t|)) * Real.exp (A * |t|)) by ring,
            ← Real.exp_add]
          congr 2
          rw [show η = π - A from rfl]; ring

/-- **DLMF 5.13.1**: `(2πi)⁻¹ ∫_{c−i∞}^{c+i∞} Γ(s + a)Γ(b − s)z^{−s} ds = Γ(a + b)zᵃ/(1 + z)^{a+b}`
for `−ℜa < c < ℜb` (so `ℜ(a + b) > 0`) and `|ph z| < π`; the path is `s = c + it`,
`ds = i dt`. -/
theorem dlmf_5_13_1 {a b z : ℂ} {c : ℝ} (ha : -a.re < c) (hb : c < b.re) (hz0 : z ≠ 0)
    (hz : |arg z| < π) :
    1 / (2 * π * I) * ∫ t : ℝ, Gamma ((c : ℂ) + t * I + a) * Gamma (b - ((c : ℂ) + t * I)) *
      z ^ (-((c : ℂ) + t * I)) * I = Gamma (a + b) * z ^ a / (1 + z) ^ (a + b) := by
  have ha' : 0 < c + a.re := by linarith
  have hzs : z ∈ slitPlane := mem_slitPlane_iff_arg.mpr ⟨fun h => by
    rw [h, abs_of_pos Real.pi_pos] at hz; exact lt_irrefl _ hz, hz0⟩
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have e : 1 / (2 * π * I) * ∫ t : ℝ, Gamma ((c : ℂ) + t * I + a) * Gamma (b - ((c : ℂ) + t * I)) *
      z ^ (-((c : ℂ) + t * I)) * I =
      (2 * π : ℂ)⁻¹ * ∫ t : ℝ, mbG a b c t * z ^ (-((c : ℂ) + t * I)) := by
    rw [integral_mul_const]
    simp only [mbG]
    field_simp
  rw [e]
  have hg : DifferentiableOn ℂ (fun z : ℂ => Gamma (a + b) * z ^ a / (1 + z) ^ (a + b))
      slitPlane := fun w hw => by
    have h1 := one_add_mem_slitPlane_of_mem hw
    refine (((differentiableAt_id.cpow (differentiableAt_const _) hw).const_mul _).div
      ((differentiableAt_id.const_add 1).cpow (differentiableAt_const _) h1)
        ?_).differentiableWithinAt
    rw [Ne, cpow_eq_zero_iff]; exact fun h => slitPlane_ne_zero h1 h.1
  exact eqOn_of_eq_on_pos_reals (((differentiableOn_mb ha' hb).const_mul _).analyticOnNhd
    isOpen_slitPlane) (hg.analyticOnNhd isOpen_slitPlane)
    (StarConvex.isPathConnected starConvex_one_slitPlane (by simp)).isConnected.isPreconnected
    isOpen_slitPlane (by simp [mem_slitPlane_iff]) (fun x hx _ => dlmf_5_13_1_pos ha hb hx) hzs

/-! ### 5.13.2 -/

theorem Gamma_mul_Gamma_conj_line (a t : ℝ) :
    Gamma ((a : ℂ) + t * I) * Gamma ((a : ℂ) - t * I) =
      ((‖Gamma ((a : ℂ) + t * I)‖ ^ 2 : ℝ) : ℂ) := by
  have h : (a : ℂ) - t * I = (starRingEnd ℂ) ((a : ℂ) + t * I) := by
    simp [Complex.ext_iff]
  rw [h, Complex.Gamma_conj, mul_conj, Complex.normSq_eq_norm_sq]

theorem norm_Gamma_line_neg (a t : ℝ) :
    ‖Gamma ((a : ℂ) + ((-t : ℝ) : ℂ) * I)‖ = ‖Gamma ((a : ℂ) + t * I)‖ := by
  have h : (a : ℂ) + ((-t : ℝ) : ℂ) * I = (starRingEnd ℂ) ((a : ℂ) + t * I) := by
    simp [Complex.ext_iff]
  rw [h, Complex.Gamma_conj, Complex.norm_conj]

/-- `1 + e^{iθ} = 2cos(θ/2) e^{iθ/2}`. -/
theorem one_add_exp_mul_I (θ : ℝ) :
    1 + cexp (θ * I) = ((2 * Real.cos (θ / 2) : ℝ) : ℂ) * cexp ((θ / 2 : ℝ) * I) := by
  push_cast
  rw [Complex.cos, show (θ : ℂ) * I = (θ / 2 : ℂ) * I + (θ / 2 : ℂ) * I by ring, Complex.exp_add]
  have h0 := Complex.exp_ne_zero ((θ / 2 : ℂ) * I)
  rw [show -(θ / 2 : ℂ) * I = -((θ / 2 : ℂ) * I) by ring, Complex.exp_neg]
  field_simp
  ring

/-- **DLMF 5.13.2**: `(2π)⁻¹ ∫_{−∞}^{∞} |Γ(a + it)|² e^{(2b−π)t} dt = Γ(2a)/(2 sin b)^{2a}`,
`a > 0`, `0 < b < π`. -/
theorem dlmf_5_13_2 {a b : ℝ} (ha : 0 < a) (hb0 : 0 < b) (hbπ : b < π) :
    1 / (2 * π) * ∫ t : ℝ, ‖Gamma ((a : ℂ) + t * I)‖ ^ 2 * Real.exp ((2 * b - π) * t) =
      Real.Gamma (2 * a) / (2 * Real.sin b) ^ (2 * a) := by
  have hπ := Real.pi_pos
  set θ := π - 2 * b
  have hθ1 : -π < θ := by simp only [θ]; linarith
  have hθ2 : θ < π := by simp only [θ]; linarith
  set z := cexp (θ * I)
  have hz0 : z ≠ 0 := Complex.exp_ne_zero _
  have hzarg : arg z = θ := arg_exp_mul_I_of_mem ⟨hθ1, hθ2.le⟩
  have h := dlmf_5_13_1 (a := a) (b := a) (c := 0) (z := z) (by simpa using ha) (by simpa using ha)
    hz0 (by rw [hzarg, abs_lt]; exact ⟨hθ1, hθ2⟩)
  -- the integrand
  have hint : ∀ t : ℝ, Gamma (((0 : ℝ) : ℂ) + t * I + a) * Gamma (a - (((0 : ℝ) : ℂ) + t * I)) *
      z ^ (-(((0 : ℝ) : ℂ) + t * I)) * I =
      ((‖Gamma ((a : ℂ) + t * I)‖ ^ 2 * Real.exp (θ * t) : ℝ) : ℂ) * I := fun t => by
    rw [show ((0 : ℝ) : ℂ) + t * I + a = (a : ℂ) + t * I by push_cast; ring,
      show (a : ℂ) - (((0 : ℝ) : ℂ) + t * I) = (a : ℂ) - t * I by push_cast; ring,
      Gamma_mul_Gamma_conj_line, cexp_cpow_of_im (by simpa using hθ1) (by simpa using hθ2.le)]
    push_cast
    congr 2
    rw [show (θ : ℂ) * I * -(0 + t * I) = θ * t * (-(I * I)) by ring, I_mul_I, neg_neg, mul_one,
      ← ofReal_mul, ← ofReal_exp]
  simp_rw [hint] at h
  rw [integral_mul_const, integral_complex_ofReal] at h
  -- reflect `t ↦ −t`
  have hrefl : ∫ t : ℝ, ‖Gamma ((a : ℂ) + t * I)‖ ^ 2 * Real.exp (θ * t) =
      ∫ t : ℝ, ‖Gamma ((a : ℂ) + t * I)‖ ^ 2 * Real.exp ((2 * b - π) * t) := by
    have := Measure.integral_comp_mul_left
      (fun t : ℝ => ‖Gamma ((a : ℂ) + t * I)‖ ^ 2 * Real.exp ((2 * b - π) * t)) (-1)
    simp only [inv_neg, inv_one, abs_neg, abs_one, one_smul, neg_one_mul] at this
    rw [← this]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only
    rw [show ((-t : ℝ) : ℂ) = ((-t : ℝ) : ℂ) from rfl, norm_Gamma_line_neg]
    congr 2
    simp only [θ]; ring
  -- the right side
  have hsin : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi hb0 hbπ
  have hcos : Real.cos (θ / 2) = Real.sin b := by
    rw [show θ / 2 = π / 2 - b by simp only [θ]; ring, Real.cos_pi_div_two_sub]
  have h1z : 1 + z = cexp ((Real.log (2 * Real.sin b) : ℂ) + (θ / 2 : ℝ) * I) := by
    rw [one_add_exp_mul_I, hcos, Complex.exp_add, ← ofReal_exp, Real.exp_log (by positivity)]
  have hrhs : Gamma ((a : ℂ) + a) * z ^ (a : ℂ) / (1 + z) ^ ((a : ℂ) + a) =
      ((Real.Gamma (2 * a) / (2 * Real.sin b) ^ (2 * a) : ℝ) : ℂ) := by
    rw [h1z, cexp_cpow_of_im (by simpa using hθ1) (by simpa using hθ2.le),
      cexp_cpow_of_im (by simp; linarith) (by simp; linarith),
      show (a : ℂ) + a = ((2 * a : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal,
      Real.rpow_def_of_pos (by positivity)]
    push_cast
    rw [eq_div_iff (Complex.exp_ne_zero _), div_mul_eq_mul_div, div_eq_iff (Complex.exp_ne_zero _),
      mul_assoc, mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  rw [hrhs, hrefl] at h
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  have hπ' : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  set X := ∫ t : ℝ, ‖Gamma ((a : ℂ) + t * I)‖ ^ 2 * Real.exp ((2 * b - π) * t)
  apply ofReal_injective
  rw [← h]
  push_cast
  field_simp

end Azurite.DLMF
