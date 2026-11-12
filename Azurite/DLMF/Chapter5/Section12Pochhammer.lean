/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section12Loop

/-!
# DLMF §5.12: Pochhammer's integral 5.12.12

`∫_P^{(1+,0+,1−,0−)} t^{a−1}(1 − t)^{b−1} dt = −4e^{πi(a+b)} sin(πa) sin(πb) B(a, b)` for all
`a, b ∈ ℂ` (`dlmf_5_12_12`, and `dlmf_5_12_12_gamma` in the entire form
`−4π²e^{πi(a+b)}/(Γ(1 − a)Γ(1 − b)Γ(a + b))`, which also covers the poles of `B`).

The contour (`pochhammer`) is the double loop of Figure 5.12.3 collapsed onto `[δ, 1 − ε]`: from
`P` to `1 − ε`, around `1` counterclockwise (`|t − 1| = ε`), back to `δ`, around `0`
counterclockwise (`|t| = δ`), to `1 − ε`, around `1` clockwise, back to `δ`, around `0`
clockwise, and back to `P`, for any `0 < δ ≤ P ≤ 1 − ε`, `ε > 0`. The powers are continued along
the path from their principal values at `P`: circling `0` (resp. `1`) once counterclockwise
multiplies the integrand by `A = e^{2πi(a−1)}` (resp. `B = e^{2πi(b−1)}`), so the nine pieces carry
the phases `1, 1, B, B, AB, AB, A, A, 1`.

Proof: the clockwise circles are `−B⁻¹` and `−A⁻¹` times the counterclockwise ones
(`pochC1m_eq`, `pochC0m_eq`), which `arc0_eq` evaluates for `ℜa, ℜb > 0`; the segments then add up
to `(1 − A)(1 − B)B(a, b)`. Both sides are entire in `a` and in `b` separately.
-/

open Complex Filter Topology Set MeasureTheory
open scoped Real

namespace Azurite.DLMF

/-- Euler's integrand `t^{a−1}(1 − t)^{b−1}` (principal powers on `(0, 1)`). -/
noncomputable def eulerF (a b : ℂ) (t : ℝ) : ℂ := (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1)

/-- Counterclockwise around `1`: `t = 1 − εe^{iθ}`, `(1 − t)^{b−1} = ε^{b−1}e^{i(b−1)θ}`. -/
noncomputable def pochC1p (a b : ℂ) (ε : ℝ) : ℂ :=
  ∫ θ in (0 : ℝ)..(2 * π), (1 - ε * cexp (θ * I)) ^ (a - 1) *
    ((ε : ℂ) ^ (b - 1) * cexp ((b - 1) * θ * I)) * (-(I * ε * cexp (θ * I)))

/-- Counterclockwise around `0`: `t = δe^{iθ}`, `t^{a−1} = δ^{a−1}e^{i(a−1)θ}`. -/
noncomputable def pochC0p (a b : ℂ) (δ : ℝ) : ℂ :=
  ∫ θ in (0 : ℝ)..(2 * π), ((δ : ℂ) ^ (a - 1) * cexp ((a - 1) * θ * I)) *
    (1 - δ * cexp (θ * I)) ^ (b - 1) * (I * δ * cexp (θ * I))

/-- Clockwise around `1`: `t = 1 − εe^{−iθ}`, `(1 − t)^{b−1} = ε^{b−1}e^{−i(b−1)θ}`. -/
noncomputable def pochC1m (a b : ℂ) (ε : ℝ) : ℂ :=
  ∫ θ in (0 : ℝ)..(2 * π), (1 - ε * cexp (-(θ * I))) ^ (a - 1) *
    ((ε : ℂ) ^ (b - 1) * cexp (-((b - 1) * θ * I))) * (I * ε * cexp (-(θ * I)))

/-- Clockwise around `0`: `t = δe^{−iθ}`, `t^{a−1} = δ^{a−1}e^{−i(a−1)θ}`. -/
noncomputable def pochC0m (a b : ℂ) (δ : ℝ) : ℂ :=
  ∫ θ in (0 : ℝ)..(2 * π), ((δ : ℂ) ^ (a - 1) * cexp (-((a - 1) * θ * I))) *
    (1 - δ * cexp (-(θ * I))) ^ (b - 1) * (-(I * δ * cexp (-(θ * I))))

/-- **Pochhammer's double loop** `∫_P^{(1+,0+,1−,0−)} t^{a−1}(1 − t)^{b−1} dt` (see the module
docstring), with `A = e^{2πi(a−1)}`, `B = e^{2πi(b−1)}`. -/
noncomputable def pochhammer (a b : ℂ) (P δ ε : ℝ) : ℂ :=
  let A := cexp (2 * π * (a - 1) * I)
  let B := cexp (2 * π * (b - 1) * I)
  (∫ t in P..(1 - ε), eulerF a b t) + pochC1p a b ε + B * (∫ t in (1 - ε)..δ, eulerF a b t) +
    B * pochC0p a b δ + A * B * (∫ t in δ..(1 - ε), eulerF a b t) + A * B * pochC1m a b ε +
    A * (∫ t in (1 - ε)..δ, eulerF a b t) + A * pochC0m a b δ + ∫ t in δ..P, eulerF a b t

theorem cexp_two_pi_sub_one_mul (s : ℂ) : cexp (2 * π * (s - 1) * I) = cexp (2 * π * s * I) := by
  rw [show 2 * π * (s - 1) * I = 2 * π * s * I + -(2 * π * I) by ring, Complex.exp_add,
    Complex.exp_neg, exp_two_pi_mul_I, inv_one, mul_one]

theorem cexp_neg_two_pi_mul_I_sub (θ : ℝ) :
    cexp (-((((2 * π - θ) : ℝ) : ℂ) * I)) = cexp (θ * I) := by
  rw [ofReal_sub, sub_mul, neg_sub, show (θ : ℂ) * I - ((2 * π : ℝ) : ℂ) * I = θ * I + -(2 * π * I)
    by push_cast; ring, Complex.exp_add, Complex.exp_neg, exp_two_pi_mul_I, inv_one, mul_one]

/-- The clockwise circle around `1` is `−B⁻¹` times the counterclockwise one. -/
theorem pochC1m_eq (a b : ℂ) (ε : ℝ) :
    pochC1m a b ε = -(cexp (2 * π * (b - 1) * I))⁻¹ * pochC1p a b ε := by
  have h := intervalIntegral.integral_comp_sub_left (fun θ : ℝ =>
    (1 - ε * cexp (-(θ * I))) ^ (a - 1) * ((ε : ℂ) ^ (b - 1) * cexp (-((b - 1) * θ * I))) *
      (I * ε * cexp (-(θ * I)))) (a := 0) (b := 2 * π) (2 * π)
  rw [sub_zero, sub_self] at h
  rw [pochC1m, ← h, pochC1p, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  have e : cexp (-((b - 1) * (((2 * π - θ) : ℝ) : ℂ) * I)) =
      (cexp (2 * π * (b - 1) * I))⁻¹ * cexp ((b - 1) * θ * I) := by
    rw [← Complex.exp_neg, ← Complex.exp_add]; congr 1; push_cast; ring
  simp only [cexp_neg_two_pi_mul_I_sub, e]
  ring

/-- The clockwise circle around `0` is `−A⁻¹` times the counterclockwise one. -/
theorem pochC0m_eq (a b : ℂ) (δ : ℝ) :
    pochC0m a b δ = -(cexp (2 * π * (a - 1) * I))⁻¹ * pochC0p a b δ := by
  have h := intervalIntegral.integral_comp_sub_left (fun θ : ℝ =>
    ((δ : ℂ) ^ (a - 1) * cexp (-((a - 1) * θ * I))) * (1 - δ * cexp (-(θ * I))) ^ (b - 1) *
      (-(I * δ * cexp (-(θ * I))))) (a := 0) (b := 2 * π) (2 * π)
  rw [sub_zero, sub_self] at h
  rw [pochC0m, ← h, pochC0p, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  have e : cexp (-((a - 1) * (((2 * π - θ) : ℝ) : ℂ) * I)) =
      (cexp (2 * π * (a - 1) * I))⁻¹ * cexp ((a - 1) * θ * I) := by
    rw [← Complex.exp_neg, ← Complex.exp_add]; congr 1; push_cast; ring
  simp only [cexp_neg_two_pi_mul_I_sub, e]
  ring

/-- The double loop in terms of the counterclockwise circles (all `a, b`). -/
theorem pochhammer_eq (a b : ℂ) {P δ ε : ℝ} :
    pochhammer a b P δ ε =
      (∫ t in P..(1 - ε), eulerF a b t) + (∫ t in δ..P, eulerF a b t) +
      (cexp (2 * π * (a - 1) * I) * cexp (2 * π * (b - 1) * I) - cexp (2 * π * (b - 1) * I) -
        cexp (2 * π * (a - 1) * I)) * (∫ t in δ..(1 - ε), eulerF a b t) +
      (1 - cexp (2 * π * (a - 1) * I)) * pochC1p a b ε +
      (cexp (2 * π * (b - 1) * I) - 1) * pochC0p a b δ := by
  have hA := Complex.exp_ne_zero (2 * π * (a - 1) * I)
  have hB := Complex.exp_ne_zero (2 * π * (b - 1) * I)
  simp only [pochhammer]
  rw [pochC1m_eq, pochC0m_eq, intervalIntegral.integral_symm (1 - ε) δ]
  field_simp
  ring

theorem pochC0p_eq_arc0 (a b : ℂ) (δ : ℝ) :
    pochC0p a b δ = arc0 (fun u => (1 - u) ^ (b - 1)) a δ :=
  intervalIntegral.integral_congr fun θ _ => by ring

theorem pochC1p_eq_arc0 (a b : ℂ) (ε : ℝ) :
    pochC1p a b ε = -arc0 (fun u => (1 - u) ^ (a - 1)) b ε := by
  rw [arc0, ← intervalIntegral.integral_neg]
  exact intervalIntegral.integral_congr fun θ _ => by ring

theorem pochhammer_eq_of_re_pos {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) {P δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) (hδP : δ ≤ P) (hPε : P ≤ 1 - ε) :
    pochhammer a b P δ ε = (1 - cexp (2 * π * a * I)) * (1 - cexp (2 * π * b * I)) *
      dlmfBeta a b := by
  have hd := hasDerivAt_id (0 : ℂ)
  have hdiff : ∀ c : ℂ, DifferentiableOn ℂ (fun u : ℂ => (1 - u) ^ c) (Metric.ball 0 1) :=
    fun c u hu => ((differentiableAt_id.const_sub 1).cpow_const
      (one_sub_mem_slitPlane_of_lt_one (by simpa using hu))).differentiableWithinAt
  have h0 := arc0_eq hδ (by linarith) (hdiff (b - 1)) ha
  have h1 := arc0_eq hε (by linarith) (hdiff (a - 1)) hb
  rw [integral_reflect] at h1
  have h0' : ∫ r in (0 : ℝ)..δ, (1 - (r : ℂ)) ^ (b - 1) * (r : ℂ) ^ (a - 1) =
      ∫ t in (0 : ℝ)..δ, eulerF a b t :=
    intervalIntegral.integral_congr fun r _ => by simp only [eulerF]; ring
  have hi : IntervalIntegrable (eulerF a b) volume 0 1 := Complex.betaIntegral_convergent ha hb
  have hsub : ∀ x y : ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 →
      IntervalIntegrable (eulerF a b) volume x y := fun x y hx0 hx1 hy0 hy1 =>
    hi.mono_set (uIcc_subset_uIcc (by rw [uIcc_of_le zero_le_one]; exact ⟨hx0, hx1⟩)
      (by rw [uIcc_of_le zero_le_one]; exact ⟨hy0, hy1⟩))
  have hB := (dlmf_5_12_1 ha hb).1
  have hsplit1 := intervalIntegral.integral_add_adjacent_intervals
    (hsub 0 δ le_rfl zero_le_one hδ.le (by linarith)) (hsub δ (1 - ε) hδ.le (by linarith)
      (by linarith) (by linarith))
  have hsplit2 := intervalIntegral.integral_add_adjacent_intervals
    (hsub 0 (1 - ε) le_rfl zero_le_one (by linarith) (by linarith))
    (hsub (1 - ε) 1 (by linarith) (by linarith) zero_le_one le_rfl)
  have hsplitP := intervalIntegral.integral_add_adjacent_intervals
    (hsub δ P hδ.le (by linarith) (by linarith) (by linarith))
    (hsub P (1 - ε) (by linarith) (by linarith) (by linarith) (by linarith))
  have hBeq : dlmfBeta a b = ∫ t in (0 : ℝ)..1, eulerF a b t := hB
  rw [pochhammer_eq, pochC0p_eq_arc0, pochC1p_eq_arc0, h0, h1, h0', cexp_two_pi_sub_one_mul,
    cexp_two_pi_sub_one_mul, hBeq, ← hsplit2, ← hsplit1, ← hsplitP]
  simp only [eulerF]
  ring

/-! ### Holomorphy in each parameter -/

/-- `s ↦ ∫₀^{2π} A(θ)e^{(s−1)L(θ)} dθ` is entire for continuous `A`, `L`. -/
theorem differentiable_arc_param {A L : ℝ → ℂ} (hA : Continuous A) (hL : Continuous L) :
    Differentiable ℂ fun s : ℂ => ∫ θ in (0 : ℝ)..(2 * π), A θ * cexp ((s - 1) * L θ) := by
  have h := (differentiable_integral_mul_cexp hA hL.neg 0 (2 * π)).comp
    (differentiable_id.sub_const (1 : ℂ))
  convert h using 2 with s
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [id, Pi.neg_apply]
  congr 2
  ring

/-- `s ↦ ∫ₓʸ w(t)e^{(s−1)ℓ(t)} dt` is entire for `w` integrable and `ℓ` bounded on `[x, y]`. -/
theorem differentiable_seg_param {w ℓ : ℝ → ℂ} {x y : ℝ} (hxy : x ≤ y)
    (hw : IntegrableOn w (Ioc x y)) (hℓ : Measurable ℓ) {M : ℝ}
    (hM : ∀ t ∈ Ioc x y, ‖ℓ t‖ ≤ M) :
    Differentiable ℂ fun s : ℂ => ∫ t in x..y, w t * cexp ((s - 1) * ℓ t) := by
  have h := (differentiable_integral_mul_cexp_of_bounded (μ := volume.restrict (Ioc x y)) hw
    hℓ.aestronglyMeasurable (ae_restrict_of_forall_mem measurableSet_Ioc hM)).comp
    (differentiable_id.sub_const (1 : ℂ))
  convert h using 2 with s
  rw [intervalIntegral.integral_of_le hxy]
  rfl

theorem norm_log_le_of_mem {x y t : ℝ} (hx : 0 < x) (hy : y < 1) (ht : t ∈ Ioc x y) :
    ‖((Real.log t : ℝ) : ℂ)‖ ≤ -Real.log x ∧
      ‖((Real.log (1 - t) : ℝ) : ℂ)‖ ≤ -Real.log (1 - y) := by
  have h0 : 0 < t := hx.trans ht.1
  have h1 : 0 < 1 - t := by linarith [ht.2]
  rw [norm_real, norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonpos (Real.log_nonpos h0.le (by linarith [ht.2])),
    abs_of_nonpos (Real.log_nonpos h1.le (by linarith [ht.1]))]
  exact ⟨neg_le_neg (Real.log_le_log hx ht.1.le),
    neg_le_neg (Real.log_le_log (by linarith) (by linarith [ht.2]))⟩

theorem continuousOn_eulerF (a b : ℂ) {x y : ℝ} (hx : 0 < x) (hy : y < 1) :
    ContinuousOn (eulerF a b) (Icc x y) := fun t ht => by
  have h0 : 0 < t := hx.trans_le ht.1
  have h1 : (0 : ℝ) < 1 - t := by linarith [ht.2]
  refine ContinuousAt.continuousWithinAt ?_
  refine (continuousAt_ofReal_cpow_const _ _ (Or.inr h0.ne')).mul ?_
  refine ContinuousAt.cpow (by fun_prop) continuousAt_const ?_
  exact mem_slitPlane_iff.mpr (Or.inl (by simpa using h1))

theorem eulerF_eq_a {a b : ℂ} {t : ℝ} (ht : 0 < t) :
    eulerF a b t = (1 - (t : ℂ)) ^ (b - 1) * cexp ((a - 1) * ((Real.log t : ℝ) : ℂ)) := by
  rw [eulerF, cpow_pos_eq ht, mul_comm]

theorem eulerF_eq_b {a b : ℂ} {t : ℝ} (ht : t < 1) :
    eulerF a b t = (t : ℂ) ^ (a - 1) * cexp ((b - 1) * ((Real.log (1 - t) : ℝ) : ℂ)) := by
  rw [eulerF, show (1 : ℂ) - t = ((1 - t : ℝ) : ℂ) by push_cast; ring,
    cpow_pos_eq (x := 1 - t) (by linarith)]

/-- Segments `[x, y] ⊂ (0, 1)` are entire in `a` and in `b`. -/
theorem differentiable_seg_ab {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y < 1) (a b : ℂ) :
    (Differentiable ℂ fun a' => ∫ t in x..y, eulerF a' b t) ∧
      Differentiable ℂ fun b' => ∫ t in x..y, eulerF a b' t := by
  have hint : ∀ a b : ℂ, IntegrableOn (eulerF a b) (Ioc x y) := fun a b =>
    ((continuousOn_eulerF a b hx hy).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  constructor
  · have hw : IntegrableOn (fun t : ℝ => (1 - (t : ℂ)) ^ (b - 1)) (Ioc x y) := by
      refine ((ContinuousOn.integrableOn_Icc ?_)).mono_set Ioc_subset_Icc_self
      intro t ht
      refine ContinuousAt.continuousWithinAt (ContinuousAt.cpow (by fun_prop) continuousAt_const ?_)
      exact mem_slitPlane_iff.mpr (Or.inl (by simp; linarith [ht.2]))
    convert differentiable_seg_param hxy hw (by fun_prop) (M := -Real.log x)
      (fun t ht => (norm_log_le_of_mem hx hy ht).1) using 2 with a'
    exact intervalIntegral.integral_congr_ae (ae_of_all _ fun t ht => by
      rw [uIoc_of_le hxy] at ht; exact eulerF_eq_a (hx.trans ht.1))
  · have hw : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (a - 1)) (Ioc x y) := by
      refine ((ContinuousOn.integrableOn_Icc ?_)).mono_set Ioc_subset_Icc_self
      intro t ht
      exact (continuousAt_ofReal_cpow_const _ _ (Or.inr (hx.trans_le ht.1).ne')).continuousWithinAt
    convert differentiable_seg_param hxy hw (by fun_prop) (M := -Real.log (1 - y))
      (fun t ht => (norm_log_le_of_mem hx hy ht).2) using 2 with b'
    exact intervalIntegral.integral_congr_ae (ae_of_all _ fun t ht => by
      rw [uIoc_of_le hxy] at ht; exact eulerF_eq_b (by linarith [ht.2]))

theorem continuous_log_one_sub_circle {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Continuous fun θ : ℝ => Complex.log (1 - r * cexp (θ * I)) :=
  continuous_iff_continuousAt.mpr fun θ =>
    ContinuousAt.comp (f := fun θ : ℝ => 1 - (r : ℂ) * cexp (θ * I)) (x := θ)
      (continuousAt_clog (one_sub_mem_slitPlane_of_lt_one (by
        rw [norm_ofReal_mul_cexp hr0]; exact hr1))) (by fun_prop)

theorem one_sub_circle_ne_zero {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (θ : ℝ) :
    (1 : ℂ) - r * cexp (θ * I) ≠ 0 :=
  slitPlane_ne_zero (one_sub_mem_slitPlane_of_lt_one (by rw [norm_ofReal_mul_cexp hr0]; exact hr1))

theorem continuous_cpow_one_sub_circle {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (c : ℂ) :
    Continuous fun θ : ℝ => (1 - r * cexp (θ * I)) ^ c :=
  Continuous.cpow (by fun_prop) continuous_const fun θ =>
    one_sub_mem_slitPlane_of_lt_one (by rw [norm_ofReal_mul_cexp hr0]; exact hr1)

theorem differentiable_pochC0p {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (a b : ℂ) :
    (Differentiable ℂ fun a' => pochC0p a' b δ) ∧ Differentiable ℂ fun b' => pochC0p a b' δ := by
  constructor
  · convert differentiable_arc_param (A := fun θ : ℝ => (1 - δ * cexp (θ * I)) ^ (b - 1) *
      (I * δ * cexp (θ * I))) (L := fun θ : ℝ => ((Real.log δ : ℝ) : ℂ) + θ * I)
      ((continuous_cpow_one_sub_circle hδ0.le hδ1 _).mul (by fun_prop)) (by fun_prop)
      using 2 with a'
    refine intervalIntegral.integral_congr fun θ _ => ?_
    rw [cpow_pos_eq hδ0, ← Complex.exp_add]
    ring_nf
  · convert differentiable_arc_param (A := fun θ : ℝ => ((δ : ℂ) ^ (a - 1) *
      cexp ((a - 1) * θ * I)) * (I * δ * cexp (θ * I)))
      (L := fun θ : ℝ => Complex.log (1 - δ * cexp (θ * I))) (by fun_prop)
      (continuous_log_one_sub_circle hδ0.le hδ1) using 2 with b'
    refine intervalIntegral.integral_congr fun θ _ => ?_
    rw [cpow_def_of_ne_zero (one_sub_circle_ne_zero hδ0.le hδ1 θ)]
    ring_nf

theorem differentiable_pochC1p {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (a b : ℂ) :
    (Differentiable ℂ fun a' => pochC1p a' b ε) ∧ Differentiable ℂ fun b' => pochC1p a b' ε := by
  constructor
  · convert differentiable_arc_param (A := fun θ : ℝ => ((ε : ℂ) ^ (b - 1) *
      cexp ((b - 1) * θ * I)) * (-(I * ε * cexp (θ * I))))
      (L := fun θ : ℝ => Complex.log (1 - ε * cexp (θ * I))) (by fun_prop)
      (continuous_log_one_sub_circle hε0.le hε1) using 2 with a'
    refine intervalIntegral.integral_congr fun θ _ => ?_
    rw [cpow_def_of_ne_zero (one_sub_circle_ne_zero hε0.le hε1 θ)]
    ring_nf
  · convert differentiable_arc_param (A := fun θ : ℝ => (1 - ε * cexp (θ * I)) ^ (a - 1) *
      (-(I * ε * cexp (θ * I)))) (L := fun θ : ℝ => ((Real.log ε : ℝ) : ℂ) + θ * I)
      ((continuous_cpow_one_sub_circle hε0.le hε1 _).mul (by fun_prop)) (by fun_prop)
      using 2 with b'
    refine intervalIntegral.integral_congr fun θ _ => ?_
    rw [cpow_pos_eq hε0, ← Complex.exp_add]
    ring_nf

theorem differentiable_pochhammer {P δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hδP : δ ≤ P)
    (hPε : P ≤ 1 - ε) (a b : ℂ) :
    (Differentiable ℂ fun a' => pochhammer a' b P δ ε) ∧
      Differentiable ℂ fun b' => pochhammer a b' P δ ε := by
  have hδ1 : δ < 1 := by linarith
  have hε1 : ε < 1 := by linarith
  have s1' := differentiable_seg_ab (by linarith : 0 < P) hPε (by linarith) a b
  have s2 := differentiable_seg_ab hδ hδP (by linarith) a b
  have s3 := differentiable_seg_ab hδ (by linarith : δ ≤ 1 - ε) (by linarith) a b
  have c0 := differentiable_pochC0p hδ hδ1 a b
  have c1 := differentiable_pochC1p hε hε1 a b
  have hphase : Differentiable ℂ fun s : ℂ => cexp (2 * π * (s - 1) * I) := by fun_prop
  simp_rw [pochhammer_eq]
  constructor
  · exact (((s1'.1.add s2.1).add (((hphase.mul (differentiable_const _)).sub
      (differentiable_const _) |>.sub hphase).mul s3.1)).add
      (((differentiable_const _).sub hphase).mul c1.1)).add
      ((differentiable_const _).mul c0.1)
  · exact (((s1'.2.add s2.2).add ((((differentiable_const _).mul hphase).sub hphase
      |>.sub (differentiable_const _)).mul s3.2)).add
      ((differentiable_const _).mul c1.2)).add
      ((hphase.sub (differentiable_const _)).mul c0.2)

/-! ### 5.12.12 -/

/-- The entire form of the right side of 5.12.12. -/
noncomputable def pochhammerG (a b : ℂ) : ℂ :=
  -4 * cexp (π * I * (a + b)) * π ^ 2 * (Gamma (1 - a))⁻¹ * (Gamma (1 - b))⁻¹ * (Gamma (a + b))⁻¹

theorem not_neg_nat_of_re_pos {w : ℂ} (hw : 0 < w.re) : ∀ n : ℕ, w ≠ -n := fun n h => by
  have := congrArg re h; simp at this; rw [this] at hw; simp at hw
  linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-- DLMF's right side of 5.12.12 is the entire form off the poles of `B`. -/
theorem pochhammer_rhs_eq {a b : ℂ} (ha : ∀ n : ℕ, a ≠ -n) (hb : ∀ n : ℕ, b ≠ -n) :
    -4 * cexp (π * I * (a + b)) * Complex.sin (π * a) * Complex.sin (π * b) * dlmfBeta a b =
      pochhammerG a b := by
  have h1 := sin_mul_Gamma ha
  have h2 := sin_mul_Gamma hb
  rw [dlmfBeta, pochhammerG]
  calc -4 * cexp (π * I * (a + b)) * Complex.sin (π * a) * Complex.sin (π * b) *
        (Gamma a * Gamma b / Gamma (a + b))
      = -4 * cexp (π * I * (a + b)) * (Complex.sin (π * a) * Gamma a) *
        (Complex.sin (π * b) * Gamma b) * (Gamma (a + b))⁻¹ := by ring
    _ = _ := by rw [h1, h2]; ring

theorem pochhammer_eq_G_of_re_pos {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) {P δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) (hδP : δ ≤ P) (hPε : P ≤ 1 - ε) :
    pochhammer a b P δ ε = pochhammerG a b := by
  rw [pochhammer_eq_of_re_pos ha hb hδ hε hδP hPε, ← pochhammer_rhs_eq
    (not_neg_nat_of_re_pos ha) (not_neg_nat_of_re_pos hb)]
  have e1 : 1 - cexp (2 * π * a * I) = -(2 * I * cexp (π * a * I) * Complex.sin (π * a)) := by
    rw [← exp_two_pi_mul_sub_one]; ring
  have e2 : 1 - cexp (2 * π * b * I) = -(2 * I * cexp (π * b * I) * Complex.sin (π * b)) := by
    rw [← exp_two_pi_mul_sub_one]; ring
  rw [e1, e2, show π * I * (a + b) = π * a * I + π * b * I by ring, Complex.exp_add]
  ring_nf
  rw [I_sq]
  ring

theorem differentiable_pochhammerG_left (b : ℂ) : Differentiable ℂ fun a => pochhammerG a b := by
  have hinv : Differentiable ℂ fun z : ℂ => (Gamma z)⁻¹ := by
    simpa [one_div] using Complex.differentiable_one_div_Gamma
  unfold pochhammerG
  exact ((((by fun_prop : Differentiable ℂ fun a : ℂ => -4 * cexp (π * I * (a + b)) * π ^ 2)).mul
    (hinv.comp (differentiable_id.const_sub 1))).mul_const _).mul
    (hinv.comp (differentiable_id.add_const b))

theorem differentiable_pochhammerG_right (a : ℂ) : Differentiable ℂ fun b => pochhammerG a b := by
  have hinv : Differentiable ℂ fun z : ℂ => (Gamma z)⁻¹ := by
    simpa [one_div] using Complex.differentiable_one_div_Gamma
  unfold pochhammerG
  exact ((((by fun_prop : Differentiable ℂ fun b : ℂ =>
    -4 * cexp (π * I * (a + b)) * π ^ 2)).mul_const
    _).mul (hinv.comp (differentiable_id.const_sub 1))).mul
    (hinv.comp (differentiable_id.const_add a))

/-- Identity theorem for entire functions agreeing on `ℜs > 0`. -/
theorem eq_of_eq_on_re_pos {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (h : ∀ s : ℂ, 0 < s.re → f s = g s) (s : ℂ) : f s = g s := by
  have heq := (hf.differentiableOn.analyticOnNhd isOpen_univ).eqOn_of_preconnected_of_eventuallyEq
    (hg.differentiableOn.analyticOnNhd isOpen_univ) isPreconnected_univ (mem_univ 1) (by
      filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
        (show (1 : ℂ) ∈ {w : ℂ | 0 < w.re} by simp)] with w hw
      exact h w hw)
  exact heq (mem_univ s)

/-- **DLMF 5.12.12**, entire form: Pochhammer's integral equals
`−4π²e^{πi(a+b)}/(Γ(1 − a)Γ(1 − b)Γ(a + b))` for all `a, b ∈ ℂ`. -/
theorem dlmf_5_12_12_gamma (a b : ℂ) {P δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hδP : δ ≤ P)
    (hPε : P ≤ 1 - ε) : pochhammer a b P δ ε = pochhammerG a b := by
  have hd := differentiable_pochhammer hδ hε hδP hPε
  have step1 : ∀ a b : ℂ, 0 < b.re → pochhammer a b P δ ε = pochhammerG a b := fun a b hb =>
    eq_of_eq_on_re_pos (hd a b).1 (differentiable_pochhammerG_left b)
      (fun a ha => pochhammer_eq_G_of_re_pos ha hb hδ hε hδP hPε) a
  exact eq_of_eq_on_re_pos (hd a b).2 (differentiable_pochhammerG_right a)
    (fun b hb => step1 a b hb) b

/-- **DLMF 5.12.12** (Pochhammer's integral):
`∫_P^{(1+,0+,1−,0−)} t^{a−1}(1 − t)^{b−1} dt = −4e^{πi(a+b)} sin(πa) sin(πb) B(a, b)`, on the
double loop `pochhammer` for any `0 < δ ≤ P ≤ 1 − ε`, `ε > 0` (`a, b ≠ 0, −1, −2, …`, where
`B(a, b)` has poles; `dlmf_5_12_12_gamma` covers all `a, b`). -/
theorem dlmf_5_12_12 {a b : ℂ} (ha : ∀ n : ℕ, a ≠ -n) (hb : ∀ n : ℕ, b ≠ -n) {P δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) (hδP : δ ≤ P) (hPε : P ≤ 1 - ε) :
    pochhammer a b P δ ε =
      -4 * cexp (π * I * (a + b)) * Complex.sin (π * a) * Complex.sin (π * b) * dlmfBeta a b := by
  rw [dlmf_5_12_12_gamma a b hδ hε hδP hPε, pochhammer_rhs_eq ha hb]

end Azurite.DLMF
