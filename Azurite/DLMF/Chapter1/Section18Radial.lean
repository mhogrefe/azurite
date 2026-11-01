/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# DLMF §1.18(viii), Example 2: radial Schrödinger operators in three dimensions

https://dlmf.nist.gov/1.18.viii

The radial operator (1.18.67) `ℒ_ℓ = −½ d²/dr² + ℓ(ℓ + 1)/(2r²) + V(r)` (`radialOp`), and DLMF's
claim that in three dimensions a dip below zero need not bind:

* `radial_eigen_eq_zero`: if `V ≥ −1/(8r²)` on `(0, ∞)`, no `E < 0` is an eigenvalue of `ℒ_ℓ`
  with an eigenfunction `u` such that `u, u′ ∈ L²(0, ∞)` and the boundary form
  `u u′ − u²/(2r)` vanishes at `0`. The proof is the Hardy-type identity
  `(½ u u′ − u²/(4r))′ = ½(u′ − u/(2r))² + ((ℓ(ℓ + 1)/2 + 1/8)/r² + V − E) u²`
  (`hasDerivAt_radialBoundary`), integrated over `[a, b]` (`radial_energy_le`). The boundary
  form vanishes for regular solutions with `u(0) = 0`
  (`tendsto_radialBoundaryForm_of_hasDerivAt`).
* `dlmf_1_18_viii_shallow_well`: `V(r) = −1/(8(1 + r)²)` is negative, tends to `0`, and binds
  nothing for any `ℓ`. In one dimension every such well binds (`Section18Simon`).
* `radial_L2_weight`: DLMF's measure `r² dr` belongs to `R = u/r`; for the `u` of (1.18.67)
  the measure is `dr`, since `∫ (u/r)² r² dr = ∫ u² dr`.

The Coulomb case is in `Section18Coulomb`, and the reduction from three dimensions in
`Section18Radial3D`.
-/

open Set Filter Topology MeasureTheory

namespace Azurite.DLMF

/-- DLMF (1.18.67): the radial operator
`ℒ_ℓ u = −½ u″ + (ℓ(ℓ + 1)/(2r²) + V(r)) u`. -/
noncomputable def radialOp (ℓ : ℕ) (V u : ℝ → ℝ) (r : ℝ) : ℝ :=
  -(1 / 2) * deriv (deriv u) r + ((ℓ : ℝ) * (ℓ + 1) / (2 * r ^ 2) + V r) * u r

/-- The measure `r² dr` of DLMF's `L²([0, ∞), r² dr)` belongs to the three-dimensional radial
function `R = u/r`; for the function `u` on which (1.18.67) acts the measure is `dr`. -/
theorem radial_L2_weight (u : ℝ → ℝ) :
    ∫ r in Ioi 0, (u r / r) ^ 2 * r ^ 2 = ∫ r in Ioi 0, u r ^ 2 := by
  refine setIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) => ?_
  field_simp

/-! ### No bound state for a shallow well -/

/-- The boundary form `G = ½ u u′ − u²/(4r)` of the Hardy-type identity. -/
noncomputable def radialBoundary (u : ℝ → ℝ) (r : ℝ) : ℝ :=
  u r * deriv u r / 2 - u r ^ 2 / (4 * r)

section Shallow

variable {ℓ : ℕ} {V u : ℝ → ℝ} {E : ℝ}
  (hd : ∀ r > 0, HasDerivAt u (deriv u r) r)
  (hdd : ∀ r > 0, HasDerivAt (deriv u) (deriv (deriv u) r) r)
  (heig : ∀ r > 0, radialOp ℓ V u r = E * u r)

include hd hdd heig in
/-- `G′ = ½(u′ − u/(2r))² + ((ℓ(ℓ + 1)/2 + 1/8)/r² + V − E) u²` for an eigenfunction. -/
theorem hasDerivAt_radialBoundary {r : ℝ} (hr : 0 < r) :
    HasDerivAt (radialBoundary u)
      ((deriv u r - u r / (2 * r)) ^ 2 / 2 +
        (((ℓ : ℝ) * (ℓ + 1) / 2 + 1 / 8) / r ^ 2 + V r - E) * u r ^ 2) r := by
  have h := (((hd r hr).mul (hdd r hr)).div_const 2).sub
    (((hd r hr).pow 2).div ((hasDerivAt_id r).const_mul 4) (by simp; exact hr.ne'))
  refine h.congr_deriv ?_
  have he := heig r hr
  simp only [radialOp] at he
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr.ne'
  have hu'' : deriv (deriv u) r =
      ((ℓ * (ℓ + 1) + 2 * r ^ 2 * V r) * u r - 2 * r ^ 2 * u r * E) / r ^ 2 := by
    field_simp
    field_simp at he
    linarith
  simp only [id, Pi.pow_apply, hu'']
  field_simp
  push_cast
  ring

include hd hdd heig in
theorem radial_energy_le (hV : ∀ r > 0, -(1 / (8 * r ^ 2)) ≤ V r)
    (hVc : ContinuousOn V (Ioi 0)) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    -E * ∫ r in a..b, u r ^ 2 ≤ radialBoundary u b - radialBoundary u a := by
  have hsub : uIcc a b ⊆ Ioi 0 := by
    rw [uIcc_of_le hab]; exact fun x hx => ha.trans_le hx.1
  have hcu : ContinuousOn u (uIcc a b) := fun x hx =>
    (hd x (hsub hx)).continuousAt.continuousWithinAt
  have hcu' : ContinuousOn (deriv u) (uIcc a b) := fun x hx =>
    (hdd x (hsub hx)).continuousAt.continuousWithinAt
  have hcV : ContinuousOn V (uIcc a b) := hVc.mono hsub
  have hne : ∀ x ∈ uIcc a b, x ≠ 0 := fun x hx => (hsub hx).ne'
  have hg : ContinuousOn (fun r => (deriv u r - u r / (2 * r)) ^ 2 / 2 +
      (((ℓ : ℝ) * (ℓ + 1) / 2 + 1 / 8) / r ^ 2 + V r - E) * u r ^ 2) (uIcc a b) := by
    refine ((hcu'.sub (hcu.div (continuousOn_const.mul continuousOn_id) fun x hx => ?_)).pow 2
      |>.div_const 2).add ((((continuousOn_const.div (continuousOn_id.pow 2) fun x hx => ?_).add
        hcV).sub continuousOn_const).mul (hcu.pow 2))
    · exact mul_ne_zero two_ne_zero (hne x hx)
    · exact pow_ne_zero 2 (hne x hx)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hasDerivAt_radialBoundary hd hdd heig (hsub hx)) hg.intervalIntegrable
  rw [← hftc, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on hab
    ((continuousOn_const.mul (hcu.pow 2)).intervalIntegrable) hg.intervalIntegrable fun x hx => ?_
  have hx : 0 < x := ha.trans_le hx.1
  have h1 := hV x hx
  have h2 : 0 ≤ ((ℓ : ℝ) * (ℓ + 1) / 2) / x ^ 2 := by positivity
  have h3 : 0 ≤ (1 / 8) / x ^ 2 + V x := by
    have : (1 / 8) / x ^ 2 = 1 / (8 * x ^ 2) := by field_simp
    linarith
  have h4 : 0 ≤ (deriv u x - u x / (2 * x)) ^ 2 / 2 := by positivity
  have h5 : ((ℓ : ℝ) * (ℓ + 1) / 2 + 1 / 8) / x ^ 2 = ((ℓ : ℝ) * (ℓ + 1) / 2) / x ^ 2 +
    (1 / 8) / x ^ 2 := add_div _ _ _
  rw [h5]
  nlinarith [sq_nonneg (u x)]

/-- An integrable function on `(0, ∞)` is small somewhere beyond any point. -/
theorem exists_ge_abs_lt_of_integrableOn {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0)) (M : ℝ)
    {ε : ℝ} (hε : 0 < ε) : ∃ b ≥ M, |f b| < ε := by
  by_contra h
  push Not at h
  have hi : IntegrableOn (fun _ => ε) (Ioi (max M 0)) := by
    refine ((hf.mono_set (Ioi_subset_Ioi (le_max_right M 0))).norm).mono'
      aestronglyMeasurable_const ((ae_restrict_iff' measurableSet_Ioi).mpr
        (ae_of_all _ fun x hx => ?_))
    rw [Real.norm_eq_abs, abs_of_pos hε]
    exact h x ((le_max_left M 0).trans (le_of_lt hx))
  rw [integrableOn_const_iff (by simp)] at hi
  rcases hi with hi | hi
  · simp at hi; linarith
  · simp at hi

include hd hdd heig in
/-- A shallow well binds nothing: if `V ≥ −1/(8r²)` on `(0, ∞)`, then `ℒ_ℓ` has no eigenvalue
`E < 0` with an eigenfunction `u` such that `u, u′ ∈ L²(0, ∞)` and the boundary form
`u u′ − u²/(2r)` vanishes at `0` (as it does for `u(0) = 0`, `u ∈ C¹`;
see `tendsto_radialBoundaryForm_of_hasDerivAt`). The proof is the Hardy-type identity
`G′ = ½(u′ − u/(2r))² + ((ℓ(ℓ + 1)/2 + 1/8)/r² + V − E)u²`. -/
theorem radial_eigen_eq_zero (hV : ∀ r > 0, -(1 / (8 * r ^ 2)) ≤ V r)
    (hVc : ContinuousOn V (Ioi 0)) (hE : E < 0)
    (h0 : Tendsto (fun r => u r * deriv u r - u r ^ 2 / (2 * r)) (𝓝[>] 0) (𝓝 0))
    (hL2 : IntegrableOn (fun r => u r ^ 2 + deriv u r ^ 2) (Ioi 0)) : ∀ r > 0, u r = 0 := by
  by_contra hne
  push Not at hne
  obtain ⟨r0, hr0, hu0⟩ := hne
  have hS : {r | 0 < u r ^ 2} ∩ Ioi 0 ∈ 𝓝 r0 :=
    inter_mem (((hd r0 hr0).continuousAt.pow 2).eventually
      (lt_mem_nhds (pow_pos (abs_pos.mpr hu0) 2 |>.trans_eq (sq_abs _))))
      (Ioi_mem_nhds hr0)
  obtain ⟨l, l', ⟨hl, hl'⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hS
  set a0 := (l + r0) / 2
  set b0 := (r0 + l') / 2
  have ha0 : 0 < a0 := by
    have := (hsub ⟨show l < a0 by simp only [a0]; linarith, by simp only [a0]; linarith⟩).2
    exact this
  have hab0 : a0 < b0 := by simp only [a0, b0]; linarith
  have hI0 : 0 < ∫ r in a0..b0, u r ^ 2 := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ (fun x hx => (hsub
      ⟨by simp only [a0] at hx; linarith [hx.1], by simp only [b0] at hx; linarith [hx.2]⟩).1)
      hab0
    exact (ContinuousOn.pow (fun x hx => (hd x (ha0.trans_le (by
      rw [uIcc_of_le hab0.le] at hx; exact hx.1))).continuousAt.continuousWithinAt) 2)
      |>.intervalIntegrable
  set η := -E * (∫ r in a0..b0, u r ^ 2) / 2
  have hη : 0 < η := by
    have : 0 < -E := by linarith
    exact div_pos (mul_pos this hI0) two_pos
  -- the left endpoint
  have hG0 : Tendsto (radialBoundary u) (𝓝[>] 0) (𝓝 0) := by
    have := h0.div_const 2
    rw [zero_div] at this
    refine this.congr' (eventually_nhdsWithin_of_forall fun r (hr : 0 < r) => ?_)
    simp only [radialBoundary]
    field_simp
    ring
  obtain ⟨a, ⟨haη, ha⟩⟩ := ((hG0.eventually (Metric.ball_mem_nhds 0 hη)).and
    (Ioo_mem_nhdsGT ha0)).exists
  rw [Real.dist_eq, sub_zero] at haη
  -- the right endpoint
  obtain ⟨b, hb, hbη⟩ := exists_ge_abs_lt_of_integrableOn hL2 (max b0 1) hη
  have hb1 : 1 ≤ b := (le_max_right _ _).trans hb
  have hbb0 : b0 ≤ b := (le_max_left _ _).trans hb
  have hGb : |radialBoundary u b| < η := by
    have hb0 : 0 < b := by linarith
    have h1 : |u b * deriv u b / 2| ≤ (u b ^ 2 + deriv u b ^ 2) / 4 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (u b - deriv u b),
        sq_nonneg (u b + deriv u b)]
    have h2 : u b ^ 2 / (4 * b) ≤ (u b ^ 2 + deriv u b ^ 2) / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg (u b), sq_nonneg (deriv u b)]
    have h3 : 0 ≤ u b ^ 2 / (4 * b) := by positivity
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ u b ^ 2 + deriv u b ^ 2)] at hbη
    unfold radialBoundary
    calc |u b * deriv u b / 2 - u b ^ 2 / (4 * b)|
        ≤ |u b * deriv u b / 2| + |u b ^ 2 / (4 * b)| := abs_sub _ _
      _ ≤ (u b ^ 2 + deriv u b ^ 2) / 4 + (u b ^ 2 + deriv u b ^ 2) / 4 := by
        rw [abs_of_nonneg h3]; linarith
      _ < η := by linarith
  -- combine
  have hab : a ≤ b := by linarith [ha.2]
  have henergy := radial_energy_le hd hdd heig hV hVc ha.1 hab
  have hmono : ∫ r in a0..b0, u r ^ 2 ≤ ∫ r in a..b, u r ^ 2 := by
    refine intervalIntegral.integral_mono_interval ha.2.le hab0.le hbb0
      (ae_of_all _ fun x => sq_nonneg (u x)) ?_
    refine ContinuousOn.intervalIntegrable (ContinuousOn.pow (fun x hx => ?_) 2)
    rw [uIcc_of_le hab] at hx
    exact (hd x (ha.1.trans_le hx.1)).continuousAt.continuousWithinAt
  have : -E * ∫ r in a0..b0, u r ^ 2 ≤ -E * ∫ r in a..b, u r ^ 2 :=
    mul_le_mul_of_nonneg_left hmono (by linarith)
  have h1 := abs_lt.mp hGb
  have h2 := abs_lt.mp haη
  simp only [η] at h1 h2
  linarith

end Shallow

/-- The regular boundary condition: if `u(0) = 0` and `u` is `C¹` at `0` from the right, the
boundary form `u u′ − u²/(2r)` tends to `0` as `r → 0⁺`. -/
theorem tendsto_radialBoundaryForm_of_hasDerivAt {u : ℝ → ℝ} {d : ℝ} (hu : HasDerivAt u d 0)
    (hu0 : u 0 = 0) (hd : Tendsto (deriv u) (𝓝[>] 0) (𝓝 d)) :
    Tendsto (fun r => u r * deriv u r - u r ^ 2 / (2 * r)) (𝓝[>] 0) (𝓝 0) := by
  have hs := (hasDerivAt_iff_tendsto_slope.mp hu).mono_left
    (nhdsWithin_mono _ fun x (hx : 0 < x) => hx.ne')
  have hc : Tendsto u (𝓝[>] 0) (𝓝 0) := by
    have := hu.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    rwa [hu0] at this
  have h := (hc.mul hd).sub ((hc.mul hs).div_const 2)
  simp only [zero_mul, zero_div, sub_zero] at h
  refine h.congr' (eventually_nhdsWithin_of_forall fun r (hr : 0 < r) => ?_)
  simp only [slope_def_field, hu0, sub_zero]
  field_simp

/-- A potential well with no bound state for any `ℓ`: `V(r) = −1/(8(1 + r)²)`. -/
noncomputable def shallowWell (r : ℝ) : ℝ := -(1 / (8 * (1 + r) ^ 2))

/-- **DLMF §1.18(viii), Example 2**: in three dimensions a well need not bind. The potential
`V(r) = −1/(8(1 + r)²)` is negative everywhere and tends to `0`, yet for no `ℓ` does `ℒ_ℓ`
have a negative eigenvalue with a regular eigenfunction `u, u′ ∈ L²(0, ∞)`. -/
theorem dlmf_1_18_viii_shallow_well :
    (∀ r, shallowWell r < 0 ∨ r = -1) ∧ Tendsto shallowWell atTop (𝓝 0) ∧
    ∀ (ℓ : ℕ) (u : ℝ → ℝ) (E : ℝ), E < 0 →
      (∀ r > 0, HasDerivAt u (deriv u r) r) →
      (∀ r > 0, HasDerivAt (deriv u) (deriv (deriv u) r) r) →
      (∀ r > 0, radialOp ℓ shallowWell u r = E * u r) →
      Tendsto (fun r => u r * deriv u r - u r ^ 2 / (2 * r)) (𝓝[>] 0) (𝓝 0) →
      IntegrableOn (fun r => u r ^ 2 + deriv u r ^ 2) (Ioi 0) → ∀ r > 0, u r = 0 := by
  refine ⟨fun r => ?_, ?_, fun ℓ u E hE hd hdd heig h0 hL2 =>
    radial_eigen_eq_zero hd hdd heig (fun r hr => ?_) ?_ hE h0 hL2⟩
  · by_cases h : r = -1
    · exact Or.inr h
    · left
      have : 0 < (1 + r) ^ 2 := by
        have : 1 + r ≠ 0 := fun h' => h (by linarith)
        positivity
      unfold shallowWell
      have : 0 < 1 / (8 * (1 + r) ^ 2) := by positivity
      linarith
  · have h : Tendsto (fun r : ℝ => 8 * (1 + r) ^ 2) atTop atTop :=
      (tendsto_pow_atTop two_ne_zero).comp (tendsto_atTop_add_const_left _ 1 tendsto_id)
        |>.const_mul_atTop (by norm_num)
    have := (h.inv_tendsto_atTop).neg
    rw [neg_zero] at this
    refine this.congr fun r => ?_
    simp [shallowWell]
  · unfold shallowWell
    rw [neg_le_neg_iff]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  · refine fun r (hr : 0 < r) => ContinuousAt.continuousWithinAt ?_
    unfold shallowWell
    have : 8 * (1 + r) ^ 2 ≠ 0 := by positivity
    fun_prop (disch := assumption)

end Azurite.DLMF
