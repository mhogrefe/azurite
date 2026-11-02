/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section10Residue
import Azurite.DLMF.Chapter1.Section8
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# DLMF §2.10(iv): Taylor and Laurent Coefficients — Darboux's Method, 2.10.25–2.10.32

For `f` analytic on `0 < |z| < r` with Laurent coefficients `fₙ` (§1.10(iii), `laurentCoeff`):

* 2.10.25 (`dlmf_2_10_25`): `f(z) = ∑_{n=−∞}^{∞} fₙ zⁿ`.
* 2.10.26 (`dlmf_2_10_26`): `fₙ = (2πi)⁻¹ ∫_𝒞 f(z)/z^{n+1} dz` for every positively oriented Jordan
  curve `𝒞` in the annulus enclosing `0` (from the residue theorem 1.10.8); on circles,
  `laurentCoeff_fourier`: `fₙ = (2πρⁿ)⁻¹ ∫_0^{2π} f(ρe^{iθ}) e^{−inθ} dθ`.
* Darboux's method: a comparison function `g` analytic on the annulus (a), with
  (b) `f − g` continuous on `0 < |z| ≤ r`, or more generally (b´) (`DarbouxCond`): continuous on
  `0 < |z| ≤ r` except at finitely many `zⱼ` on `|z| = r`, where
  `f − g = O((z − zⱼ)^{σⱼ−1})`, `σⱼ > 0` (2.10.30).
  * 2.10.28 (`dlmf_2_10_28`): `fₙ − gₙ = (2πi)⁻¹ ∮_{|z|=r} (f − g)/z^{n+1} dz
    = (2πrⁿ)⁻¹ ∫_0^{2π} (f − g)(re^{iθ}) e^{−niθ} dθ` (the contour expanded to `|z| = r`, by
    dominated convergence with the bound `|e^{iθ} − e^{iθⱼ}|^{σⱼ−1}`,
    `integrable_norm_exp_sub_rpow`).
  * 2.10.29 (`dlmf_2_10_29`): `fₙ = gₙ + o(r^{−n})` as `n → ±∞` (Riemann–Lebesgue, §1.8(i)).
  * 2.10.31–2.10.32 (`dlmf_2_10_31`): if `f^{(m)} − g^{(m)}` satisfies (b) or (b´) (2.10.32), then
    `fₙ = gₙ + o(r^{−n}|n|^{−m})`; proved from 2.10.29 for the `m`-th derivatives and
    `(f^{(m)})_{n−m} = n(n−1)⋯(n−m+1) fₙ` (`laurentCoeff_iterate_deriv`).
-/

open Filter Topology Set Metric Complex MeasureTheory intervalIntegral Finset
open scoped Real Interval

namespace Azurite.DLMF

open Azurite.JordanCurve

/-! ### 2.10.25–2.10.26 -/

/-- **DLMF 2.10.25**: `f(z) = ∑_{n=−∞}^{∞} fₙ zⁿ` on `0 < |z| < r`. -/
theorem dlmf_2_10_25 {f : ℂ → ℂ} {r : ℝ} (hf : DifferentiableOn ℂ f (annulus 0 0 r)) {ρ : ℝ}
    (hρ : ρ ∈ Ioo 0 r) {z : ℂ} (hz : z ∈ annulus 0 0 r) :
    DoubleSeriesConverges (fun n : ℤ => laurentCoeff f 0 ρ n * z ^ n) (f z) := by
  have h := dlmf_1_10_6 le_rfl hf hρ hz
  simpa only [sub_zero] using h

/-- **DLMF 2.10.26**: `fₙ = (2πi)⁻¹ ∫_𝒞 f(z)/z^{n+1} dz` for a positively oriented Jordan curve
`𝒞` in the annulus `0 < |z| < r` that encloses `0`. -/
theorem dlmf_2_10_26 {c : ℝ → ℂ} {a b : ℝ} (P : ClosedPiecewiseC1 c a b)
    (hJ : IsJordanCurve c a b) (hpos : P.IsPositivelyOriented) {f : ℂ → ℂ} {r : ℝ}
    (hf : DifferentiableOn ℂ f (annulus 0 0 r)) (hcurve : c '' Icc a b ⊆ annulus 0 0 r)
    (h0 : (0 : ℂ) ∈ jordanInterior c a b) {ρ : ℝ} (hρ : ρ ∈ Ioo 0 r) (n : ℤ) :
    laurentCoeff f 0 ρ n =
      1 / (2 * π * I) * contourIntegral (fun z => f z / z ^ (n + 1)) c a b := by
  have hc : ContinuousOn c (Icc a b) := P.continuousOn
  -- the curve lies in a closed ball of radius `R' < r`
  have hcomp : IsCompact (c '' Icc a b) := isCompact_Icc.image_of_continuousOn hc
  obtain ⟨R', hR'0, hR'r, hR'⟩ : ∃ R', 0 ≤ R' ∧ R' < r ∧ c '' Icc a b ⊆ closedBall 0 R' := by
    rcases (c '' Icc a b).eq_empty_or_nonempty with he | hne
    · exact ⟨0, le_rfl, lt_trans hρ.1 hρ.2, by rw [he]; exact empty_subset _⟩
    · obtain ⟨z, hz, hmax⟩ := hcomp.exists_isMaxOn hne continuous_norm.continuousOn
      have hzr := (hcurve hz).2
      rw [sub_zero] at hzr
      exact ⟨‖z‖, norm_nonneg z, hzr, fun w hw => mem_closedBall_zero_iff.mpr (hmax hw)⟩
  have hint : jordanInterior c a b ⊆ closedBall 0 R' := jordanInterior_subset_closedBall hR'0 hR'
  have hdom : (jordanInterior c a b ∪ c '' Icc a b) \ {0} ⊆ annulus 0 0 r := by
    rintro w ⟨hw, hw0⟩
    have hwR : ‖w‖ ≤ R' := by
      rcases hw with hw | hw
      · exact mem_closedBall_zero_iff.mp (hint hw)
      · exact mem_closedBall_zero_iff.mp (hR' hw)
    refine ⟨?_, ?_⟩
    · rw [sub_zero, norm_pos_iff]; exact hw0
    · rw [sub_zero]; linarith
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (isOpen_jordanInterior hc) 0 h0
  set F := fun z : ℂ => f z / z ^ (n + 1)
  have hFd : DifferentiableOn ℂ F (annulus 0 0 r) := by
    intro w hw
    have hw0 : w ≠ 0 := by
      have := hw.1; rw [sub_zero, norm_pos_iff] at this; exact this
    exact ((hf w hw).div ((differentiableAt_id.zpow (Or.inl hw0)).differentiableWithinAt)
      (zpow_ne_zero _ hw0))
  have hres := dlmf_1_10_8 P hJ hpos (f := F) (S := {0}) (by simpa using h0)
    (hFd.continuousOn.mono (by simpa using hdom))
    (hFd.mono fun w hw => hdom ⟨Or.inl hw.1, by simpa using hw.2⟩) (fun _ => ε)
    (by simp [hε, hball])
  rw [Finset.sum_singleton] at hres
  rw [hres, residue]
  have e : laurentCoeff F 0 (ε / 2) (-1) = laurentCoeff f 0 (ε / 2) n := by
    simp only [laurentCoeff, F, sub_zero, neg_add_cancel, zpow_zero, div_one]
  rw [e]
  have hεr : ε / 2 < r := by
    by_contra h
    push Not at h
    have hm : ((ε / 2 : ℝ) : ℂ) ∈ ball (0 : ℂ) ε := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      linarith
    have := mem_closedBall_zero_iff.mp (hint (hball hm))
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)] at this
    linarith
  exact laurentCoeff_eq le_rfl hf hρ ⟨by linarith, hεr⟩ n

/-! ### The Fourier form of the coefficients -/

/-- `fₙ = (2πρⁿ)⁻¹ ∫_0^{2π} f(ρe^{iθ}) e^{−inθ} dθ` on the circle of radius `ρ > 0`. -/
theorem laurentCoeff_fourier (f : ℂ → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (n : ℤ) :
    laurentCoeff f 0 ρ n = 1 / (2 * π * (ρ : ℂ) ^ n) *
      ∫ θ in (0 : ℝ)..2 * π, f (ρ * cexp (θ * I)) * cexp (-(n * θ * I)) := by
  rw [laurentCoeff, circleIntegral, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [deriv_circleMap, circleMap, zero_add, sub_zero, smul_eq_mul]
  have hρ0 : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ.ne'
  have he : cexp (θ * I) ≠ 0 := Complex.exp_ne_zero _
  have hexp : cexp (-(n * θ * I)) = (cexp (θ * I) ^ n)⁻¹ := by
    rw [← Complex.exp_int_mul, ← Complex.exp_neg]
    ring_nf
  rw [hexp, mul_zpow, zpow_add₀ hρ0, zpow_add₀ he, zpow_one, zpow_one]
  have : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  have : (ρ : ℂ) ^ n ≠ 0 := zpow_ne_zero _ hρ0
  have : cexp (θ * I) ^ n ≠ 0 := zpow_ne_zero _ he
  field_simp

/-! ### Coefficients of derivatives -/

theorem continuousOn_sphere_of_annulus {r ρ : ℝ} (hρ : ρ ∈ Ioo 0 r) :
    ∀ z ∈ sphere (0 : ℂ) ρ, z ∈ annulus 0 0 r := fun z hz => by
  rw [mem_sphere_zero_iff_norm] at hz
  exact ⟨by rw [sub_zero, hz]; exact hρ.1, by rw [sub_zero, hz]; exact hρ.2⟩

/-- `(f′)ₖ = (k + 1) f_{k+1}`. -/
theorem laurentCoeff_deriv {f : ℂ → ℂ} {r : ℝ} (hf : DifferentiableOn ℂ f (annulus 0 0 r))
    {ρ : ℝ} (hρ : ρ ∈ Ioo 0 r) (k : ℤ) :
    laurentCoeff (deriv f) 0 ρ k = (k + 1) * laurentCoeff f 0 ρ (k + 1) := by
  have hopen := isOpen_annulus (0 : ℂ) 0 r
  have hmem := continuousOn_sphere_of_annulus hρ
  have hz0 : ∀ z ∈ sphere (0 : ℂ) ρ, z ≠ 0 := fun z hz h => by
    rw [mem_sphere_zero_iff_norm, h, norm_zero] at hz; linarith [hρ.1]
  have hd : ∀ z ∈ sphere (0 : ℂ) ρ, HasDerivAt (fun w => f w * w ^ (-(k + 1)))
      (deriv f z * z ^ (-(k + 1)) + f z * ((-(k + 1) : ℤ) * z ^ (-(k + 1) - 1))) z := by
    intro z hz
    exact ((hf.differentiableAt (hopen.mem_nhds (hmem z hz))).hasDerivAt).mul
      (hasDerivAt_zpow (-(k + 1)) z (Or.inl (hz0 z hz)))
  have h0 := circleIntegral.integral_eq_zero_of_hasDerivWithinAt hρ.1.le
    fun z hz => (hd z hz).hasDerivWithinAt
  have hci1 : CircleIntegrable (fun z => deriv f z * z ^ (-(k + 1))) 0 ρ := by
    refine ContinuousOn.circleIntegrable hρ.1.le fun z hz => ?_
    exact (((hf.deriv hopen).continuousOn z (hmem z hz)).mono_of_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds (hmem z hz)))).mul
      ((continuousAt_zpow₀ _ _ (Or.inl (hz0 z hz))).continuousWithinAt)
  have hci2 : CircleIntegrable (fun z => f z * ((-(k + 1) : ℤ) * z ^ (-(k + 1) - 1))) 0 ρ := by
    refine ContinuousOn.circleIntegrable hρ.1.le fun z hz => ?_
    exact ((hf.continuousOn z (hmem z hz)).mono_of_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds (hmem z hz)))).mul
      (continuousWithinAt_const.mul
        (continuousAt_zpow₀ _ _ (Or.inl (hz0 z hz))).continuousWithinAt)
  rw [circleIntegral.integral_add hci1 hci2] at h0
  unfold laurentCoeff
  have e1 : (∮ z in C(0, ρ), deriv f z / (z - 0) ^ (k + 1)) =
      ∮ z in C(0, ρ), deriv f z * z ^ (-(k + 1)) := by
    refine circleIntegral.integral_congr hρ.1.le fun z _ => ?_
    simp only [sub_zero, div_eq_mul_inv, zpow_neg]
  have e2 : (∮ z in C(0, ρ), f z * ((-(k + 1) : ℤ) * z ^ (-(k + 1) - 1))) =
      ((-(k + 1) : ℤ) : ℂ) * ∮ z in C(0, ρ), f z / (z - 0) ^ (k + 1 + 1) := by
    rw [← circleIntegral.integral_const_mul]
    refine circleIntegral.integral_congr hρ.1.le fun z hz => ?_
    simp only [sub_zero, div_eq_mul_inv]
    rw [show -(k + 1) - 1 = -(k + 1 + 1) by ring, zpow_neg]
    ring
  rw [e2] at h0
  rw [e1]
  push_cast at h0
  linear_combination (2 * π * I)⁻¹ * h0

/-- `(f^{(m)})ₖ = (k + 1)(k + 2)⋯(k + m) f_{k+m}`. -/
theorem laurentCoeff_iterate_deriv {f : ℂ → ℂ} {r : ℝ} (hf : DifferentiableOn ℂ f (annulus 0 0 r))
    {ρ : ℝ} (hρ : ρ ∈ Ioo 0 r) (m : ℕ) (k : ℤ) :
    laurentCoeff (deriv^[m] f) 0 ρ k =
      (∏ i ∈ range m, ((k : ℂ) + 1 + i)) * laurentCoeff f 0 ρ (k + m) := by
  induction m generalizing k with
  | zero => simp
  | succ m ih =>
    have hdm : DifferentiableOn ℂ (deriv^[m] f) (annulus 0 0 r) := by
      clear ih
      induction m with
      | zero => exact hf
      | succ m ihm =>
        rw [Function.iterate_succ_apply']
        exact ihm.deriv (isOpen_annulus 0 0 r)
    rw [Function.iterate_succ_apply', laurentCoeff_deriv hdm hρ, ih, prod_range_succ']
    push_cast
    rw [show k + 1 + (m : ℤ) = k + ((m : ℤ) + 1) by ring]
    have e : ∏ x ∈ range m, ((k : ℂ) + 1 + 1 + x) = ∏ x ∈ range m, ((k : ℂ) + 1 + (x + 1)) :=
      prod_congr rfl fun x _ => by ring
    rw [e]
    ring

/-! ### An integrable bound near the singularities -/

/-- `|x|^s` is integrable on `[−π, π]` for `s > −1`. -/
theorem intervalIntegrable_abs_rpow {s : ℝ} (hs : -1 < s) :
    IntervalIntegrable (fun x : ℝ => |x| ^ s) volume (-π) π := by
  have h1 : IntervalIntegrable (fun x : ℝ => |x| ^ s) volume 0 π := by
    refine (intervalIntegrable_rpow' hs).congr fun x hx => ?_
    rw [Set.uIoc_of_le Real.pi_pos.le] at hx
    rw [abs_of_pos hx.1]
  have h2 : IntervalIntegrable (fun x : ℝ => |x| ^ s) volume (-π) 0 := by
    have := h1.comp_mul_left (c := -1)
    simp only [neg_mul, one_mul, abs_neg, div_neg, div_one, neg_zero] at this
    exact this.symm
  exact h2.trans h1

/-- `‖e^{iθ} − e^{iφ}‖ ≥ (2/π)|θ − φ|` for `|θ − φ| ≤ π`. -/
theorem norm_exp_sub_exp_ge {θ φ : ℝ} (h : |θ - φ| ≤ π) :
    2 / π * |θ - φ| ≤ ‖cexp (θ * I) - cexp (φ * I)‖ := by
  have e : cexp (θ * I) - cexp (φ * I) = cexp (φ * I) * (cexp (I * ((θ - φ : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [e, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_exp_I_mul_ofReal_sub_one,
    Real.norm_eq_abs, abs_mul, abs_two]
  set t := θ - φ
  have hpi := Real.pi_pos
  have key : 2 / π * (|t| / 2) ≤ |Real.sin (t / 2)| := by
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
        (by rw [abs_of_nonneg ht] at h; linarith))]
      exact Real.mul_le_sin (by linarith) (by rw [abs_of_nonneg ht] at h; linarith)
    · rw [abs_of_nonpos ht, show t / 2 = -(-t / 2) by ring, Real.sin_neg, abs_neg,
        abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
          (by rw [abs_of_nonpos ht] at h; linarith))]
      have := Real.mul_le_sin (x := -t / 2) (by linarith) (by rw [abs_of_nonpos ht] at h; linarith)
      linarith
  have : 2 / π * |t| = 2 * (2 / π * (|t| / 2)) := by ring
  linarith

/-- `θ ↦ (c‖e^{iθ} − u‖)^s` is integrable over a period when `‖u‖ = 1`, `s > −1`, `c > 0`. -/
theorem integrable_norm_exp_sub_rpow {u : ℂ} (hu : ‖u‖ = 1) {s : ℝ} (hs : -1 < s) {c : ℝ}
    (hc : 0 < c) (a b : ℝ) :
    IntervalIntegrable (fun θ : ℝ => (c * ‖cexp (θ * I) - u‖) ^ s) volume a b := by
  set φ := arg u
  have hu' : u = cexp (φ * I) := by
    have := norm_mul_exp_arg_mul_I u
    rw [hu, Complex.ofReal_one, one_mul] at this
    exact this.symm
  have hper : Function.Periodic (fun θ : ℝ => (c * ‖cexp (θ * I) - u‖) ^ s) (2 * π) := by
    intro θ
    simp only
    rw [show ((θ + 2 * π : ℝ) : ℂ) * I = θ * I + 2 * π * I by push_cast; ring, Complex.exp_add,
      Complex.exp_two_pi_mul_I, mul_one]
  have hmeas : Measurable (fun θ : ℝ => (c * ‖cexp (θ * I) - u‖) ^ s) := by
    have : Continuous (fun θ : ℝ => c * ‖cexp (θ * I) - u‖) := by fun_prop
    exact this.measurable.pow_const s
  refine hper.intervalIntegrable (t := φ - π) (by positivity) ?_ a b
  rw [show φ - π + 2 * π = φ + π by ring]
  rcases le_or_gt 0 s with hs0 | hs0
  · have : Continuous (fun θ : ℝ => (c * ‖cexp (θ * I) - u‖) ^ s) :=
      (by fun_prop : Continuous (fun θ : ℝ => c * ‖cexp (θ * I) - u‖)).rpow_const
        fun _ => Or.inr hs0
    exact this.intervalIntegrable _ _
  · have hg : IntervalIntegrable (fun θ : ℝ => (2 * c / π) ^ s * |θ - φ| ^ s) volume
        (φ - π) (φ + π) := by
      have h := (intervalIntegrable_abs_rpow hs).comp_sub_right φ
      rw [show -π + φ = φ - π by ring, show π + φ = φ + π by ring] at h
      exact h.const_mul _
    refine hg.mono_fun' hmeas.aestronglyMeasurable ?_
    have hcount : ∀ᵐ θ ∂(volume.restrict (Ι (φ - π) (φ + π))), θ ≠ φ := by
      exact ae_restrict_of_ae (ae_iff.mpr (by simp))
    filter_upwards [ae_restrict_mem measurableSet_uIoc, hcount] with θ hθ hne
    rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hθ
    have habs : |θ - φ| ≤ π := abs_le.mpr ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
    have hpos : 0 < |θ - φ| := abs_pos.mpr (sub_ne_zero.mpr hne)
    have hge := norm_exp_sub_exp_ge habs
    rw [← hu'] at hge
    have hx : 0 < c * (2 / π * |θ - φ|) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    calc (c * ‖cexp (θ * I) - u‖) ^ s ≤ (c * (2 / π * |θ - φ|)) ^ s :=
          Real.rpow_le_rpow_of_nonpos hx (mul_le_mul_of_nonneg_left hge hc.le) hs0.le
      _ = (2 * c / π) ^ s * |θ - φ| ^ s := by
          rw [show c * (2 / π * |θ - φ|) = (2 * c / π) * |θ - φ| by ring,
            Real.mul_rpow (by positivity) (abs_nonneg _)]

/-! ### Darboux's method -/

/-- The punctured closed disk `0 < |z| ≤ r`. -/
def punctClosedDisk (r : ℝ) : Set ℂ := {z | 0 < ‖z‖ ∧ ‖z‖ ≤ r}

/-- **DLMF §2.10(iv), condition (b´)** (with 2.10.30): `h = f − g` is continuous on
`0 < |z| ≤ r` except at finitely many points `zⱼ` of `|z| = r`, at each of which
`h(z) = O((z − zⱼ)^{σⱼ−1})`, `σⱼ > 0`. Condition (b) is the case of no singularities
(`darbouxCond_of_continuousOn`). -/
def DarbouxCond (h : ℂ → ℂ) (r : ℝ) : Prop :=
  ∃ S : Finset ℂ, (∀ s ∈ S, ‖s‖ = r) ∧ ContinuousOn h (punctClosedDisk r \ ↑S) ∧
    ∀ s ∈ S, ∃ σ : ℝ, 0 < σ ∧ ∃ C δ : ℝ, 0 < δ ∧
      ∀ z ∈ punctClosedDisk r, z ≠ s → ‖z - s‖ < δ → ‖h z‖ ≤ C * ‖z - s‖ ^ (σ - 1)

/-- **Condition (b)**: `f − g` continuous on `0 < |z| ≤ r`. -/
theorem darbouxCond_of_continuousOn {h : ℂ → ℂ} {r : ℝ}
    (hc : ContinuousOn h (punctClosedDisk r)) : DarbouxCond h r :=
  ⟨∅, by simp, by simpa using hc, by simp⟩

/-- `‖ρu − s‖ ≥ (r/√2)‖u − s/r‖` for `‖u‖ = 1`, `‖s‖ = r`, `r/2 ≤ ρ ≤ r`. -/
theorem norm_sub_ge_of_circle {u s : ℂ} {r ρ : ℝ} (hu : ‖u‖ = 1) (hs : ‖s‖ = r) (hr : 0 < r)
    (hρ1 : r / 2 ≤ ρ) :
    r / √2 * ‖u - s / r‖ ≤ ‖(ρ : ℂ) * u - s‖ := by
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  set v := s / r with hv
  have hsv : s = r * v := by rw [hv]; field_simp
  have hvn : ‖v‖ = 1 := by rw [hv, norm_div, hs, Complex.norm_real, Real.norm_of_nonneg hr.le,
    div_self hr.ne']
  have hu2 : u.re ^ 2 + u.im ^ 2 = 1 := by
    have := Complex.sq_norm u; rw [hu, Complex.normSq_apply] at this; nlinarith
  have hv2 : v.re ^ 2 + v.im ^ 2 = 1 := by
    have := Complex.sq_norm v; rw [hvn, Complex.normSq_apply] at this; nlinarith
  have hsq1 : ‖(ρ : ℂ) * u - s‖ ^ 2 = (ρ * u.re - r * v.re) ^ 2 + (ρ * u.im - r * v.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hsv]; simp; ring
  have hsq2 : ‖u - v‖ ^ 2 = (u.re - v.re) ^ 2 + (u.im - v.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have h2 : (√2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hkey : (r / √2 * ‖u - v‖) ^ 2 ≤ ‖(ρ : ℂ) * u - s‖ ^ 2 := by
    rw [mul_pow, div_pow, h2, hsq1, hsq2]
    have hρr : r ^ 2 / 2 ≤ ρ * r := by nlinarith
    have h0 : 0 ≤ (u.re - v.re) ^ 2 + (u.im - v.im) ^ 2 := by positivity
    nlinarith [sq_nonneg (ρ - r)]
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp hkey

theorem countable_exp_eq (v : ℂ) : {θ : ℝ | cexp (θ * I) = v}.Countable := by
  rcases Set.eq_empty_or_nonempty {θ : ℝ | cexp (θ * I) = v} with he | ⟨θ₀, hθ₀⟩
  · rw [he]; exact countable_empty
  · refine (countable_range (fun k : ℤ => θ₀ + 2 * π * k)).mono fun θ hθ => ?_
    simp only [Set.mem_ofPred_eq] at hθ hθ₀
    rw [← hθ₀, Complex.exp_eq_exp_iff_exists_int] at hθ
    obtain ⟨k, hk⟩ := hθ
    refine ⟨k, ?_⟩
    have h := congrArg Complex.im hk
    simp at h
    linarith

/-- The radial limit: under (b´),
`∫_0^{2π} h(ρe^{iθ}) e^{−inθ} dθ → ∫_0^{2π} h(re^{iθ}) e^{−inθ} dθ` as `ρ → r−`. -/
theorem DarbouxCond.tendsto {h : ℂ → ℂ} {r : ℝ} (hr : 0 < r) (hD : DarbouxCond h r) (n : ℤ) :
    Tendsto (fun ρ : ℝ => ∫ θ in (0 : ℝ)..2 * π, h (ρ * cexp (θ * I)) * cexp (-(n * θ * I)))
      (𝓝[<] r) (𝓝 (∫ θ in (0 : ℝ)..2 * π, h (r * cexp (θ * I)) * cexp (-(n * θ * I)))) := by
  obtain ⟨S, hSr, hcont, hsing⟩ := hD
  choose! σ hσ C δ hδ hbd using hsing
  set δ' := fun s => min 1 (δ s)
  have hδ'0 : ∀ s ∈ S, 0 < δ' s := fun s hs => lt_min one_pos (hδ s hs)
  -- the compact set away from the singularities
  set K := {w : ℂ | r / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ r ∧ ∀ s ∈ S, δ' s / 2 ≤ ‖w - s‖}
  have hKsub : K ⊆ punctClosedDisk r \ ↑S := by
    rintro w ⟨h1, h2, h3⟩
    refine ⟨⟨by linarith, h2⟩, fun hwS => ?_⟩
    have := h3 w hwS
    rw [sub_self, norm_zero] at this
    linarith [hδ'0 w hwS]
  have hKc : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · have : K = {w : ℂ | r / 2 ≤ ‖w‖} ∩ {w : ℂ | ‖w‖ ≤ r} ∩
          ⋂ s ∈ S, {w : ℂ | δ' s / 2 ≤ ‖w - s‖} := by
        ext w; simp [K, and_assoc]
      rw [this]
      exact ((isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const)).inter
        (isClosed_biInter fun s _ => isClosed_le continuous_const
          (continuous_norm.comp (continuous_id.sub continuous_const)))
    · exact (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := r)).subset fun w hw =>
        mem_closedBall_zero_iff.mpr hw.2.1
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn (hcont.mono hKsub)
  set c := r / √2
  have hc : 0 < c := by positivity
  set B := fun θ : ℝ => max M 0 + ∑ s ∈ S, |C s| * (1 + (c * ‖cexp (θ * I) - s / r‖) ^ (σ s - 1))
  have hunit : ∀ s ∈ S, ‖s / (r : ℂ)‖ = 1 := fun s hs => by
    rw [norm_div, hSr s hs, Complex.norm_real, Real.norm_of_nonneg hr.le, div_self hr.ne']
  have hBint : IntervalIntegrable B volume 0 (2 * π) := by
    have hsum := IntervalIntegrable.sum S (μ := volume) (a := 0) (b := 2 * π)
      (f := fun s (θ : ℝ) => |C s| * (1 + (c * ‖cexp (θ * I) - s / r‖) ^ (σ s - 1)))
      fun s hs => ((intervalIntegrable_const (c := (1 : ℝ))).add
        (integrable_norm_exp_sub_rpow (hunit s hs) (by linarith [hσ s hs]) hc 0
          (2 * π))).const_mul _
    have hsum' : IntervalIntegrable (fun θ : ℝ => ∑ s ∈ S, |C s| *
        (1 + (c * ‖cexp (θ * I) - s / r‖) ^ (σ s - 1))) volume 0 (2 * π) := by
      convert hsum using 1
      funext θ
      simp [Finset.sum_apply]
    exact (intervalIntegrable_const (c := max M 0)).add hsum'
  -- the exceptional angles
  set E := ⋃ s ∈ S, {θ : ℝ | cexp (θ * I) = s / r}
  have hEc : E.Countable := S.countable_toSet.biUnion fun s _ => countable_exp_eq _
  have hEae : ∀ᵐ θ ∂volume, θ ∉ E := hEc.ae_notMem _
  have hnorm1 : ∀ θ : ℝ, ‖cexp (θ * I)‖ = 1 := fun θ => Complex.norm_exp_ofReal_mul_I θ
  have hmemD : ∀ ρ θ : ℝ, 0 < ρ → ρ < r → (ρ : ℂ) * cexp (θ * I) ∈ punctClosedDisk r \ ↑S := by
    intro ρ θ h0 h1
    have hn : ‖(ρ : ℂ) * cexp (θ * I)‖ = ρ := by
      rw [norm_mul, hnorm1, mul_one, Complex.norm_real, Real.norm_of_nonneg h0.le]
    refine ⟨⟨by rw [hn]; exact h0, by rw [hn]; exact h1.le⟩, fun hS => ?_⟩
    have := hSr _ hS
    rw [hn] at this
    linarith
  have hev : ∀ᶠ ρ in 𝓝[<] r, r / 2 < ρ ∧ ρ < r := by
    have h1 : ∀ᶠ ρ in 𝓝[<] r, r / 2 < ρ :=
      eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds (by linarith))
    filter_upwards [h1, self_mem_nhdsWithin] with ρ h1 h2 using ⟨h1, h2⟩
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence B ?_ ?_ hBint ?_
  · filter_upwards [hev] with ρ hρ
    have : Continuous fun θ : ℝ => h (ρ * cexp (θ * I)) * cexp (-(n * θ * I)) :=
      (hcont.comp_continuous (by fun_prop) fun θ => hmemD ρ θ (by linarith) hρ.2).mul
        (by fun_prop)
    exact this.aestronglyMeasurable
  · filter_upwards [hev] with ρ hρ
    filter_upwards [hEae] with θ hθE _
    rw [norm_mul, show -((n : ℂ) * θ * I) = ((-(n * θ) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
    set w := (ρ : ℂ) * cexp (θ * I)
    have hwD := hmemD ρ θ (by linarith) hρ.2
    have hBsum : 0 ≤ ∑ s ∈ S, |C s| * (1 + (c * ‖cexp (θ * I) - s / r‖) ^ (σ s - 1)) :=
      sum_nonneg fun s _ => mul_nonneg (abs_nonneg _) (by positivity)
    by_cases hK : w ∈ K
    · calc ‖h w‖ ≤ M := hM w hK
        _ ≤ B θ := by
            show M ≤ max M 0 + _
            linarith [le_max_left M 0]
    · have hwn : ‖w‖ = ρ := by
        rw [norm_mul, hnorm1, mul_one, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      simp only [K, Set.mem_ofPred_eq, not_and, not_forall, not_le] at hK
      obtain ⟨s, hs, hws⟩ := hK (by rw [hwn]; linarith) (by rw [hwn]; linarith)
      have hδs : ‖w - s‖ < δ s := by
        have := min_le_right 1 (δ s)
        linarith [hδ'0 s hs]
      have hws1 : ‖w - s‖ < 1 := by
        have := min_le_left 1 (δ s)
        linarith
      have hne : w ≠ s := by
        intro h'
        apply hwD.2
        show w ∈ (↑S : Set ℂ)
        rw [h']
        exact hs
      have hb := hbd s hs w hwD.1 hne hδs
      have hterm : ‖h w‖ ≤ |C s| * (1 + (c * ‖cexp (θ * I) - s / r‖) ^ (σ s - 1)) := by
        refine hb.trans ?_
        have hpos : 0 < ‖w - s‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
        have hC : C s * ‖w - s‖ ^ (σ s - 1) ≤ |C s| * ‖w - s‖ ^ (σ s - 1) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hpos.le _)
        refine hC.trans (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
        rcases le_or_gt 1 (σ s) with h1 | h1
        · have : ‖w - s‖ ^ (σ s - 1) ≤ 1 :=
            Real.rpow_le_one hpos.le hws1.le (by linarith)
          have : 0 ≤ (c * ‖cexp (θ * I) - s / r‖) ^ (σ s - 1) := Real.rpow_nonneg (by positivity) _
          linarith
        · have hθs : cexp (θ * I) ≠ s / r := fun h' => hθE (mem_biUnion hs h')
          have hx : 0 < c * ‖cexp (θ * I) - s / r‖ :=
            mul_pos hc (norm_pos_iff.mpr (sub_ne_zero.mpr hθs))
          have hge := norm_sub_ge_of_circle (ρ := ρ) (hnorm1 θ) (hSr s hs) hr (by linarith)
          have := Real.rpow_le_rpow_of_nonpos hx hge (show σ s - 1 ≤ 0 by linarith)
          have : 0 ≤ (1 : ℝ) := zero_le_one
          linarith
      calc ‖h w‖ ≤ |C s| * (1 + (c * ‖cexp (θ * I) - s / r‖) ^ (σ s - 1)) := hterm
        _ ≤ ∑ s ∈ S, |C s| * (1 + (c * ‖cexp (θ * I) - s / r‖) ^ (σ s - 1)) :=
            single_le_sum (f := fun s => |C s| * (1 + (c * ‖cexp (θ * I) - s / r‖) ^ (σ s - 1)))
              (fun s _ => mul_nonneg (abs_nonneg _) (by positivity)) hs
        _ ≤ B θ := by
            show _ ≤ max M 0 + _
            linarith [le_max_right M 0]
  · filter_upwards [hEae] with θ hθE _
    have hθS : (r : ℂ) * cexp (θ * I) ∉ (↑S : Set ℂ) := fun hS => by
      apply hθE
      refine mem_biUnion hS ?_
      show cexp (θ * I) = (r * cexp (θ * I)) / r
      have : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
      field_simp
    have hrD : (r : ℂ) * cexp (θ * I) ∈ punctClosedDisk r \ ↑S := by
      have hn : ‖(r : ℂ) * cexp (θ * I)‖ = r := by
        rw [norm_mul, hnorm1, mul_one, Complex.norm_real, Real.norm_of_nonneg hr.le]
      exact ⟨⟨by rw [hn]; exact hr, by rw [hn]⟩, hθS⟩
    have hcw := hcont _ hrD
    have hmap : Tendsto (fun ρ : ℝ => (ρ : ℂ) * cexp (θ * I)) (𝓝[<] r)
        (𝓝[punctClosedDisk r \ ↑S] ((r : ℂ) * cexp (θ * I))) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · exact ((continuous_ofReal.mul continuous_const).tendsto r).mono_left nhdsWithin_le_nhds
      · filter_upwards [hev] with ρ hρ using hmemD ρ θ (by linarith) hρ.2
    exact (hcw.tendsto.comp hmap).mul tendsto_const_nhds

/-! ### 2.10.28, 2.10.29, 2.10.31 -/

theorem circleIntegrable_div_zpow {f : ℂ → ℂ} {r : ℝ} (hf : DifferentiableOn ℂ f (annulus 0 0 r))
    {ρ : ℝ} (hρ : ρ ∈ Ioo 0 r) (n : ℤ) :
    CircleIntegrable (fun z => f z / (z - 0) ^ (n + 1)) 0 ρ := by
  refine ContinuousOn.circleIntegrable hρ.1.le fun z hz => ?_
  have hm := continuousOn_sphere_of_annulus hρ z hz
  have hz0 : z - 0 ≠ 0 := by
    rw [sub_zero]; intro h; rw [h] at hm; have := hm.1; simp at this
  exact ((hf.continuousOn z hm).mono_of_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds
    ((isOpen_annulus 0 0 r).mem_nhds hm))).div
    ((continuous_sub_right (0 : ℂ)).continuousAt.zpow₀ _ (Or.inl hz0)).continuousWithinAt
    (zpow_ne_zero _ hz0)

/-- `fₙ − gₙ` on the circle `ρ` is the Laurent coefficient of `h` when `h = f − g` there. -/
theorem laurentCoeff_sub {f g h : ℂ → ℂ} {r : ℝ} (hf : DifferentiableOn ℂ f (annulus 0 0 r))
    (hg : DifferentiableOn ℂ g (annulus 0 0 r)) (hh : ∀ z ∈ annulus 0 0 r, h z = f z - g z)
    {ρ : ℝ} (hρ : ρ ∈ Ioo 0 r) (n : ℤ) :
    laurentCoeff f 0 ρ n - laurentCoeff g 0 ρ n = laurentCoeff h 0 ρ n := by
  unfold laurentCoeff
  rw [← mul_sub, ← circleIntegral.integral_sub (circleIntegrable_div_zpow hf hρ n)
    (circleIntegrable_div_zpow hg hρ n)]
  congr 1
  refine circleIntegral.integral_congr hρ.1.le fun z hz => ?_
  rw [hh z (continuousOn_sphere_of_annulus hρ z hz), sub_div]

/-- **DLMF 2.10.28**: under (a), (b´), for every `n`,
`fₙ − gₙ = (2πi)⁻¹ ∮_{|z|=r} (f − g)/z^{n+1} dz = (2πrⁿ)⁻¹ ∫_0^{2π} (f − g)(re^{iθ}) e^{−niθ} dθ`; here `h` is `f − g` on the open annulus,
extended to `0 < |z| ≤ r` as in (b´). -/
theorem dlmf_2_10_28 {f g h : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (annulus 0 0 r)) (hg : DifferentiableOn ℂ g (annulus 0 0 r))
    (hh : ∀ z ∈ annulus 0 0 r, h z = f z - g z) (hD : DarbouxCond h r) {ρ : ℝ}
    (hρ : ρ ∈ Ioo 0 r) (n : ℤ) :
    laurentCoeff f 0 ρ n - laurentCoeff g 0 ρ n =
        (2 * π * I)⁻¹ * ∮ z in C(0, r), h z / z ^ (n + 1) ∧
      laurentCoeff f 0 ρ n - laurentCoeff g 0 ρ n = 1 / (2 * π * (r : ℂ) ^ n) *
        ∫ θ in (0 : ℝ)..2 * π, h (r * cexp (θ * I)) * cexp (-(n * θ * I)) := by
  have hdiff : DifferentiableOn ℂ h (annulus 0 0 r) :=
    (hf.sub hg).congr fun z hz => hh z hz
  -- the left side is constant in `ρ' ∈ (0, r)`
  have hconst : ∀ ρ' ∈ Ioo 0 r, laurentCoeff h 0 ρ' n =
      laurentCoeff f 0 ρ n - laurentCoeff g 0 ρ n := fun ρ' hρ' => by
    rw [← laurentCoeff_sub hf hg hh hρ', laurentCoeff_eq le_rfl hf hρ' hρ,
      laurentCoeff_eq le_rfl hg hρ' hρ]
  have hlim : Tendsto (fun ρ' : ℝ => 1 / (2 * π * (ρ' : ℂ) ^ n) *
      ∫ θ in (0 : ℝ)..2 * π, h (ρ' * cexp (θ * I)) * cexp (-(n * θ * I))) (𝓝[<] r)
      (𝓝 (1 / (2 * π * (r : ℂ) ^ n) *
        ∫ θ in (0 : ℝ)..2 * π, h (r * cexp (θ * I)) * cexp (-(n * θ * I)))) := by
    have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
    have hz : Tendsto (fun ρ' : ℝ => 1 / (2 * π * (ρ' : ℂ) ^ n)) (𝓝[<] r)
        (𝓝 (1 / (2 * π * (r : ℂ) ^ n))) := by
      refine (((continuous_ofReal.tendsto r).zpow₀ n (Or.inl hr0)).const_mul (2 * π : ℂ) |>.inv₀
        ?_ |>.const_mul 1).mono_left nhdsWithin_le_nhds |>.congr fun ρ' => ?_
      · exact mul_ne_zero (by simp [Real.pi_ne_zero]) (zpow_ne_zero _ hr0)
      · simp [div_eq_mul_inv]
    exact hz.mul (hD.tendsto hr n)
  have hev : ∀ᶠ ρ' : ℝ in 𝓝[<] r, laurentCoeff f 0 ρ n - laurentCoeff g 0 ρ n =
      1 / (2 * π * (ρ' : ℂ) ^ n) *
        ∫ θ in (0 : ℝ)..2 * π, h (ρ' * cexp (θ * I)) * cexp (-(n * θ * I)) := by
    have h1 : ∀ᶠ ρ' : ℝ in 𝓝[<] r, 0 < ρ' :=
      eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds hr)
    filter_upwards [h1, self_mem_nhdsWithin] with ρ' h1 h2
    rw [← hconst ρ' ⟨h1, h2⟩, laurentCoeff_fourier h h1]
  have heq := tendsto_nhds_unique (tendsto_const_nhds.congr' hev) hlim
  refine ⟨?_, heq⟩
  rw [heq, ← laurentCoeff_fourier h hr, laurentCoeff]
  simp only [sub_zero]

/-- **DLMF 2.10.29**: under (a), (b´), `fₙ = gₙ + o(r^{−n})` as `n → ±∞`, i.e.
`rⁿ (fₙ − gₙ) → 0`. -/
theorem dlmf_2_10_29 {f g h : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (annulus 0 0 r)) (hg : DifferentiableOn ℂ g (annulus 0 0 r))
    (hh : ∀ z ∈ annulus 0 0 r, h z = f z - g z) (hD : DarbouxCond h r) {ρ : ℝ}
    (hρ : ρ ∈ Ioo 0 r) :
    Tendsto (fun n : ℤ => (r : ℂ) ^ n * (laurentCoeff f 0 ρ n - laurentCoeff g 0 ρ n)) atTop
        (𝓝 0) ∧
      Tendsto (fun n : ℤ => (r : ℂ) ^ n * (laurentCoeff f 0 ρ n - laurentCoeff g 0 ρ n)) atBot
        (𝓝 0) := by
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  set φ := fun θ : ℝ => h (r * cexp (θ * I))
  have hRL := tendsto_intervalIntegral_mul_exp_cocompact φ 0 (2 * π)
  have key : ∀ n : ℤ, (r : ℂ) ^ n * (laurentCoeff f 0 ρ n - laurentCoeff g 0 ρ n) =
      1 / (2 * π) * ∫ θ in (0 : ℝ)..2 * π, φ θ * cexp ((-(n : ℝ) : ℝ) * θ * I) := by
    intro n
    rw [(dlmf_2_10_28 hr hf hg hh hD hρ n).2]
    have e : (∫ θ in (0 : ℝ)..2 * π, h (r * cexp (θ * I)) * cexp (-(n * θ * I))) =
        ∫ θ in (0 : ℝ)..2 * π, φ θ * cexp ((-(n : ℝ) : ℝ) * θ * I) := by
      refine intervalIntegral.integral_congr fun θ _ => ?_
      simp only [φ]
      congr 2
      push_cast
      ring
    rw [e, ← mul_assoc]
    congr 1
    have : (r : ℂ) ^ n ≠ 0 := zpow_ne_zero _ hr0
    have : (2 * π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
    field_simp
  have hlim : ∀ l : Filter ℤ, Tendsto (fun n : ℤ => (-(n : ℝ))) l (cocompact ℝ) →
      Tendsto (fun n : ℤ => (r : ℂ) ^ n * (laurentCoeff f 0 ρ n - laurentCoeff g 0 ρ n)) l
        (𝓝 0) := by
    intro l hl
    simp only [key]
    have := (hRL.comp hl).const_mul (1 / (2 * π) : ℂ)
    rw [mul_zero] at this
    exact this
  refine ⟨hlim _ ?_, hlim _ ?_⟩
  · exact (tendsto_neg_atTop_atBot.comp tendsto_intCast_atTop_atTop).mono_right atBot_le_cocompact
  · exact (tendsto_neg_atBot_atTop.comp (tendsto_intCast_atBot_iff.mpr tendsto_id)).mono_right
      atTop_le_cocompact

/-- `|n|^m ≤ 2^m |n(n−1)⋯(n−m+1)|` for `|n| ≥ 2m`. -/
theorem abs_pow_le_prod {m : ℕ} {n : ℤ} (hn : 2 * (m : ℝ) ≤ |(n : ℝ)|) :
    |(n : ℝ)| ^ m ≤ 2 ^ m * ‖∏ i ∈ range m, (((n - m : ℤ) : ℂ) + 1 + i)‖ := by
  rw [norm_prod]
  have hb : ∀ i ∈ range m, |(n : ℝ)| / 2 ≤ ‖(((n - m : ℤ) : ℂ) + 1 + i)‖ := by
    intro i hi
    have hi' : (i : ℝ) + 1 ≤ m := by exact_mod_cast mem_range.mp hi
    have e : (((n - m : ℤ) : ℂ) + 1 + i) = ((((n : ℝ) - m + 1 + i) : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs]
    have h1 : |(n : ℝ)| ≤ |(n : ℝ) - m + 1 + i| + (m - 1 - i) := by
      have := abs_sub_abs_le_abs_sub (n : ℝ) ((n : ℝ) - m + 1 + i)
      have h2 : |(n : ℝ) - ((n : ℝ) - m + 1 + i)| = m - 1 - i := by
        rw [show (n : ℝ) - ((n : ℝ) - m + 1 + i) = m - 1 - i by ring, abs_of_nonneg (by linarith)]
      linarith [abs_sub_abs_le_abs_sub (n : ℝ) ((n : ℝ) - m + 1 + i),
        abs_sub_comm (n : ℝ) ((n : ℝ) - m + 1 + i)]
    have : (m : ℝ) - 1 - i ≤ |(n : ℝ)| / 2 := by linarith [Nat.cast_nonneg (α := ℝ) i]
    linarith
  calc |(n : ℝ)| ^ m = 2 ^ m * ∏ _i ∈ range m, (|(n : ℝ)| / 2) := by
        rw [prod_const, card_range, div_pow, mul_div_cancel₀ _ (by positivity)]
    _ ≤ 2 ^ m * ∏ i ∈ range m, ‖(((n - m : ℤ) : ℂ) + 1 + i)‖ := by
        gcongr with i hi
        exact hb i hi

theorem differentiableOn_iterate_deriv {u : ℂ → ℂ} {r : ℝ}
    (hu : DifferentiableOn ℂ u (annulus 0 0 r)) (m : ℕ) :
    DifferentiableOn ℂ (deriv^[m] u) (annulus 0 0 r) := by
  induction m with
  | zero => exact hu
  | succ m ih =>
    rw [Function.iterate_succ']
    exact ih.deriv (isOpen_annulus 0 0 r)

/-- **DLMF 2.10.31–2.10.32**: if the `m`-th derivatives satisfy (b) (2.10.31) or (b´) with
2.10.32, i.e. `H = f^{(m)} − g^{(m)}` on the annulus and `H` satisfies `DarbouxCond`, then
`fₙ = gₙ + o(r^{−n}|n|^{−m})` as `n → ±∞`: `rⁿ |n|^m |fₙ − gₙ| → 0`. -/
theorem dlmf_2_10_31 {f g H : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (annulus 0 0 r)) (hg : DifferentiableOn ℂ g (annulus 0 0 r))
    (m : ℕ) (hH : ∀ z ∈ annulus 0 0 r, H z = deriv^[m] f z - deriv^[m] g z)
    (hD : DarbouxCond H r) {ρ : ℝ} (hρ : ρ ∈ Ioo 0 r) :
    Tendsto (fun n : ℤ => r ^ n * |(n : ℝ)| ^ m *
        ‖laurentCoeff f 0 ρ n - laurentCoeff g 0 ρ n‖) atTop (𝓝 0) ∧
      Tendsto (fun n : ℤ => r ^ n * |(n : ℝ)| ^ m *
        ‖laurentCoeff f 0 ρ n - laurentCoeff g 0 ρ n‖) atBot (𝓝 0) := by
  obtain ⟨h1, h2⟩ := dlmf_2_10_29 hr (differentiableOn_iterate_deriv hf m)
    (differentiableOn_iterate_deriv hg m) hH hD hρ
  -- `rⁿ⁻ᵐ P(n) (fₙ − gₙ) → 0`
  have hshift : ∀ n : ℤ, (r : ℂ) ^ (n - m) * (laurentCoeff (deriv^[m] f) 0 ρ (n - m) -
      laurentCoeff (deriv^[m] g) 0 ρ (n - m)) = (r : ℂ) ^ (n - m) *
        ((∏ i ∈ range m, (((n - m : ℤ) : ℂ) + 1 + i)) *
          (laurentCoeff f 0 ρ n - laurentCoeff g 0 ρ n)) := by
    intro n
    rw [laurentCoeff_iterate_deriv hf hρ, laurentCoeff_iterate_deriv hg hρ, sub_add_cancel]
    ring
  have hr0 : (0 : ℝ) < r := hr
  have main : ∀ l : Filter ℤ, Tendsto (fun n : ℤ => n - (m : ℤ)) l l →
      Tendsto (fun n : ℤ => (r : ℂ) ^ n * (laurentCoeff (deriv^[m] f) 0 ρ n -
        laurentCoeff (deriv^[m] g) 0 ρ n)) l (𝓝 0) →
      Tendsto (fun n : ℤ => |(n : ℝ)|) l atTop →
      Tendsto (fun n : ℤ => r ^ n * |(n : ℝ)| ^ m *
        ‖laurentCoeff f 0 ρ n - laurentCoeff g 0 ρ n‖) l (𝓝 0) := by
    intro l hsh hl habs
    have hc := (hl.comp hsh).norm.const_mul (r ^ m * 2 ^ m)
    rw [norm_zero, mul_zero] at hc
    refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hc
    filter_upwards [habs.eventually_ge_atTop (2 * (m : ℝ))] with n hn
    simp only [Function.comp_apply]
    rw [hshift n, norm_mul, norm_mul, norm_zpow, Complex.norm_real, Real.norm_of_nonneg hr.le]
    have hP := abs_pow_le_prod (m := m) hn
    have hrn : r ^ n = r ^ (m : ℤ) * r ^ (n - m) := by
      rw [← zpow_add₀ hr.ne']; ring_nf
    rw [hrn, zpow_natCast]
    have hz : 0 ≤ r ^ (n - m) := zpow_nonneg hr.le _
    have hd : 0 ≤ ‖laurentCoeff f 0 ρ n - laurentCoeff g 0 ρ n‖ := norm_nonneg _
    calc r ^ m * r ^ (n - m) * |(n : ℝ)| ^ m * ‖laurentCoeff f 0 ρ n - laurentCoeff g 0 ρ n‖
        ≤ r ^ m * r ^ (n - m) * (2 ^ m * ‖∏ i ∈ range m, (((n - m : ℤ) : ℂ) + 1 + i)‖) *
          ‖laurentCoeff f 0 ρ n - laurentCoeff g 0 ρ n‖ := by gcongr
      _ = r ^ m * 2 ^ m * (r ^ (n - m) * (‖∏ i ∈ range m, (((n - m : ℤ) : ℂ) + 1 + i)‖ *
          ‖laurentCoeff f 0 ρ n - laurentCoeff g 0 ρ n‖)) := by ring
  refine ⟨main atTop (tendsto_atTop_add_const_right _ _ tendsto_id) h1 ?_,
    main atBot (tendsto_atBot_add_const_right _ _ tendsto_id) h2 ?_⟩
  · exact tendsto_abs_atTop_atTop.comp tendsto_intCast_atTop_atTop
  · exact tendsto_abs_atBot_atTop.comp (tendsto_intCast_atBot_iff.mpr tendsto_id)

end Azurite.DLMF
