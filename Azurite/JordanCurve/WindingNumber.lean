/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.JordanCurve.Theorem
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Winding numbers of closed piecewise-`C¹` curves in the plane

For a closed piecewise-`C¹` path `c : ℝ → ℂ` on `[a, b]` (`ClosedPiecewiseC1`), the contour
integral `∮_c f(z) dz` (`contourIntegral`) and the winding number
`windingNumber c p = (2πi)⁻¹ ∮_c dz/(z − p)` about a point `p` off the curve.  The winding number
is an integer (`exp (∮ dz/(z − p)) = 1`, by the constancy of `exp(−∫ c'/(c − p)) (c − p)`), is
locally constant off the curve, hence constant on each connected component of the complement, and
vanishes on the unbounded component.  These are the ingredients of Green's theorem for the winding
number (`Azurite/JordanCurve/Green.lean`).
-/

namespace Azurite.JordanCurve

open Set Filter Topology MeasureTheory Complex
open scoped Real

/-- A closed piecewise-`C¹` path `c` on `[a, b]`: a subdivision `a = t 0 < ⋯ < t n = b` such
that on each closed piece `[t i, t (i+1)]` the path agrees with a `C¹` function `g i`, and
`c a = c b`. -/
structure ClosedPiecewiseC1 (c : ℝ → ℂ) (a b : ℝ) where
  n : ℕ
  t : ℕ → ℝ
  g : ℕ → ℝ → ℂ
  lt : ∀ i < n, t i < t (i + 1)
  first : t 0 = a
  last : t n = b
  contDiff : ∀ i < n, ContDiff ℝ 1 (g i)
  eqOn : ∀ i < n, EqOn c (g i) (Icc (t i) (t (i + 1)))
  closed : c a = c b

namespace ClosedPiecewiseC1

variable {c : ℝ → ℂ} {a b : ℝ} (P : ClosedPiecewiseC1 c a b)

theorem t_mono : ∀ {i j : ℕ}, i ≤ j → j ≤ P.n → P.t i ≤ P.t j := by
  intro i j hij hjn
  induction j with
  | zero => rw [Nat.le_zero.mp hij]
  | succ j ih =>
    rcases Nat.of_le_succ hij with h | rfl
    · exact (ih h (Nat.le_of_succ_le hjn)).trans (P.lt j hjn).le
    · exact le_rfl

theorem t_mem_Icc {i : ℕ} (hi : i ≤ P.n) : P.t i ∈ Icc a b := by
  have h0 := P.t_mono (Nat.zero_le i) hi
  have h1 := P.t_mono hi le_rfl
  rw [P.first] at h0
  rw [P.last] at h1
  exact ⟨h0, h1⟩

include P in
theorem a_le_b : a ≤ b :=
  (P.t_mem_Icc (Nat.zero_le P.n)).1.trans (P.t_mem_Icc (Nat.zero_le P.n)).2

/-- The image of the path, a compact set. -/
def curve (_ : ClosedPiecewiseC1 c a b) : Set ℂ := c '' Icc a b

theorem mem_curve_of_mem_piece {i : ℕ} (hi : i < P.n) {s : ℝ}
    (hs : s ∈ Icc (P.t i) (P.t (i + 1))) : P.g i s ∈ P.curve :=
  ⟨s, Icc_subset_Icc (P.t_mem_Icc hi.le).1 (P.t_mem_Icc hi).2 hs, P.eqOn i hi hs⟩

include P in
theorem continuousOn : ContinuousOn c (Icc a b) := by
  have key : ∀ k ≤ P.n, ContinuousOn c (Icc a (P.t k)) := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [P.first, Icc_self]
      exact continuousOn_singleton c a
    | succ k ih =>
      intro hk
      have h1 := ih (Nat.le_of_succ_le hk)
      have h2 : ContinuousOn c (Icc (P.t k) (P.t (k + 1))) :=
        ((P.contDiff k hk).continuous.continuousOn).congr (P.eqOn k hk)
      rw [← Icc_union_Icc_eq_Icc (P.t_mem_Icc (Nat.le_of_succ_le hk)).1 (P.lt k hk).le]
      exact h1.union_of_isClosed h2 isClosed_Icc isClosed_Icc
  simpa [P.last] using key P.n le_rfl

theorem isCompact_curve : IsCompact P.curve := isCompact_Icc.image_of_continuousOn P.continuousOn

theorem isOpen_compl_curve : IsOpen P.curveᶜ := P.isCompact_curve.isClosed.isOpen_compl

/-- The contour integral `∮_c f(z) dz = ∑ᵢ ∫_{tᵢ}^{tᵢ₊₁} f(gᵢ(s)) gᵢ'(s) ds`. -/
noncomputable def contourIntegral (f : ℂ → ℂ) : ℂ :=
  ∑ i ∈ Finset.range P.n, ∫ s in P.t i..P.t (i + 1), f (P.g i s) * deriv (P.g i) s

/-- `(2πi)⁻¹ ∮_c dz/(z − p)`, a complex number which is an integer for `p` off the curve. -/
noncomputable def windingQuot (p : ℂ) : ℂ :=
  P.contourIntegral (fun z => (z - p)⁻¹) / (2 * π * I)

/-- Telescoping product of quotients. -/
theorem prod_div_succ (u : ℕ → ℂ) (hu : ∀ i, u i ≠ 0) (n : ℕ) :
    ∏ i ∈ Finset.range n, u (i + 1) / u i = u n / u 0 := by
  induction n with
  | zero => simp [hu 0]
  | succ n ih =>
    rw [Finset.prod_range_succ, ih]
    field_simp [hu 0, hu n]

/-- On one piece, `exp (∫ gᵢ'/(gᵢ − p)) = (gᵢ(tᵢ₊₁) − p)/(gᵢ(tᵢ) − p)`. -/
theorem exp_piece_integral {p : ℂ} (hp : p ∉ P.curve) {i : ℕ} (hi : i < P.n) :
    exp (∫ s in P.t i..P.t (i + 1), (P.g i s - p)⁻¹ * deriv (P.g i) s) =
      (P.g i (P.t (i + 1)) - p) / (P.g i (P.t i) - p) := by
  set g := P.g i with hg
  have hgc : ContDiff ℝ 1 g := P.contDiff i hi
  set U : Set ℝ := {s | g s ≠ p} with hU
  have hUo : IsOpen U := isOpen_ne_fun hgc.continuous continuous_const
  have hsub : Icc (P.t i) (P.t (i + 1)) ⊆ U := fun s hs h => hp (h ▸ P.mem_curve_of_mem_piece hi hs)
  set h : ℝ → ℂ := fun s => (g s - p)⁻¹ * deriv g s with hh
  have hcont : ContinuousOn h U :=
    ((hgc.continuous.sub continuous_const).continuousOn.inv₀ fun s hs => sub_ne_zero.mpr hs).mul
      (hgc.continuous_deriv le_rfl).continuousOn
  set J : ℝ → ℂ := fun s => ∫ u in P.t i..s, h u with hJ
  have hJd : ∀ s ∈ Icc (P.t i) (P.t (i + 1)), HasDerivAt J (h s) s := fun s hs => by
    have hsU : s ∈ U := hsub hs
    refine intervalIntegral.integral_hasDerivAt_right ((hcont.mono ?_).intervalIntegrable)
      (hcont.stronglyMeasurableAtFilter hUo s hsU) (hcont.continuousAt (hUo.mem_nhds hsU))
    rw [uIcc_of_le hs.1]
    exact (Icc_subset_Icc le_rfl hs.2).trans hsub
  set φ : ℝ → ℂ := fun s => exp (-J s) * (g s - p) with hφ
  have hφd : ∀ s ∈ Icc (P.t i) (P.t (i + 1)), HasDerivAt φ 0 s := fun s hs => by
    have hne : g s - p ≠ 0 := sub_ne_zero.mpr (hsub hs)
    have h1 := ((hJd s hs).neg.cexp).mul ((hgc.differentiable one_ne_zero s).hasDerivAt.sub_const p)
    convert h1 using 1
    simp only [hh]
    field_simp
    ring
  have hconst := constant_of_has_deriv_right_zero (f := φ) (a := P.t i) (b := P.t (i + 1))
    (fun s hs => (hφd s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hφd s ⟨hs.1, hs.2.le⟩).hasDerivWithinAt)
  have hend := hconst (P.t (i + 1)) (right_mem_Icc.mpr (P.lt i hi).le)
  simp only [hφ, hJ, intervalIntegral.integral_same, neg_zero, exp_zero, one_mul] at hend
  have h0 : g (P.t i) - p ≠ 0 := sub_ne_zero.mpr (hsub (left_mem_Icc.mpr (P.lt i hi).le))
  rw [eq_div_iff h0, ← hend, ← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul]

/-- `exp (∮_c dz/(z − p)) = 1` for `p` off the curve: `∮_c dz/(z − p) ∈ 2πi ℤ`. -/
theorem exp_contourIntegral_inv {p : ℂ} (hp : p ∉ P.curve) :
    exp (P.contourIntegral fun z => (z - p)⁻¹) = 1 := by
  rw [contourIntegral, exp_sum]
  set u : ℕ → ℂ := fun i => c (P.t (min i P.n)) - p with hu
  have hu' : ∀ i, u i ≠ 0 := fun i =>
    sub_ne_zero.mpr fun h => hp ⟨P.t (min i P.n), P.t_mem_Icc (min_le_right _ _), h⟩
  calc ∏ i ∈ Finset.range P.n, exp (∫ s in P.t i..P.t (i + 1), (P.g i s - p)⁻¹ * deriv (P.g i) s)
      = ∏ i ∈ Finset.range P.n, u (i + 1) / u i := by
        refine Finset.prod_congr rfl fun i hi => ?_
        have hi' := Finset.mem_range.mp hi
        rw [P.exp_piece_integral hp hi', hu]
        simp only [min_eq_left hi'.le, min_eq_left (Nat.succ_le_of_lt hi')]
        rw [P.eqOn i hi' (left_mem_Icc.mpr (P.lt i hi').le),
          P.eqOn i hi' (right_mem_Icc.mpr (P.lt i hi').le)]
    _ = u P.n / u 0 := prod_div_succ u hu' P.n
    _ = 1 := by
        simp only [hu, min_self, Nat.zero_min, P.first, P.last, P.closed]
        exact div_self (sub_ne_zero.mpr fun h => hp ⟨b, right_mem_Icc.mpr P.a_le_b, h⟩)

theorem exists_int_windingQuot {p : ℂ} (hp : p ∉ P.curve) : ∃ m : ℤ, P.windingQuot p = m := by
  obtain ⟨m, hm⟩ := exp_eq_one_iff.mp (P.exp_contourIntegral_inv hp)
  refine ⟨m, ?_⟩
  rw [windingQuot, hm]
  have : (2 * (π : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  field_simp

open Classical in
/-- The winding number of the curve about `p` (an integer; `0` by convention on the curve). -/
noncomputable def windingNumber (p : ℂ) : ℤ :=
  if h : ∃ m : ℤ, P.windingQuot p = m then h.choose else 0

theorem windingQuot_eq_windingNumber {p : ℂ} (hp : p ∉ P.curve) :
    P.windingQuot p = P.windingNumber p := by
  have h := P.exists_int_windingQuot hp
  simp only [windingNumber, h, ↓reduceDIte]
  exact h.choose_spec

/-- `∮_c dz/(z − p) = 2πi · windingNumber p`. -/
theorem contourIntegral_inv_eq {p : ℂ} (hp : p ∉ P.curve) :
    P.contourIntegral (fun z => (z - p)⁻¹) = 2 * π * I * P.windingNumber p := by
  have h := P.windingQuot_eq_windingNumber hp
  have h2 : (2 * (π : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  rw [windingQuot, div_eq_iff h2] at h
  rw [h]
  ring

/-- `∮_c dz/(z − p)` depends continuously on `p` off the curve. -/
theorem continuousAt_contourIntegral_inv {p₀ : ℂ} (hp₀ : p₀ ∉ P.curve) :
    ContinuousAt (fun p => P.contourIntegral fun z => (z - p)⁻¹) p₀ := by
  unfold contourIntegral
  refine tendsto_finsetSum (Finset.range P.n) fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  set g := P.g i with hg
  have hgc : ContDiff ℝ 1 g := P.contDiff i hi'
  have hle := (P.lt i hi').le
  obtain ⟨s₀, hs₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hle)
    ((hgc.continuous.sub continuous_const).norm.continuousOn (s := Icc (P.t i) (P.t (i + 1))))
  set m := ‖g s₀ - p₀‖ with hm
  have hm0 : 0 < m := norm_pos_iff.mpr (sub_ne_zero.mpr fun h =>
    hp₀ (h ▸ P.mem_curve_of_mem_piece hi' hs₀))
  have hlow : ∀ s ∈ Icc (P.t i) (P.t (i + 1)), ∀ p ∈ Metric.ball p₀ (m / 2),
      m / 2 ≤ ‖g s - p‖ := by
    intro s hs p hp
    have h1 : m ≤ ‖g s - p₀‖ := hmin hs
    have h2 : ‖p - p₀‖ < m / 2 := by rwa [Metric.mem_ball, dist_eq_norm] at hp
    calc m / 2 = m - m / 2 := by ring
      _ ≤ ‖g s - p₀‖ - ‖p - p₀‖ := by linarith
      _ ≤ ‖(g s - p₀) - (p - p₀)‖ := norm_sub_norm_le _ _
      _ = ‖g s - p‖ := by ring_nf
  have hcont : ∀ p ∈ Metric.ball p₀ (m / 2),
      ContinuousOn (fun s => (g s - p)⁻¹ * deriv g s) (Icc (P.t i) (P.t (i + 1))) := fun p hp =>
    ((hgc.continuous.sub continuous_const).continuousOn.inv₀ fun s hs =>
      norm_pos_iff.mp (lt_of_lt_of_le (half_pos hm0) (hlow s hs p hp))).mul
      (hgc.continuous_deriv le_rfl).continuousOn
  refine intervalIntegral.continuousAt_of_dominated_interval
    (bound := fun s => 2 / m * ‖deriv g s‖) ?_ ?_ ?_ ?_
  · filter_upwards [Metric.ball_mem_nhds p₀ (half_pos hm0)] with p hp
    exact ((hcont p hp).mono (by rw [uIoc_of_le hle]; exact Ioc_subset_Icc_self))
      |>.aestronglyMeasurable measurableSet_uIoc
  · filter_upwards [Metric.ball_mem_nhds p₀ (half_pos hm0)] with p hp
    refine ae_of_all _ fun s hs => ?_
    rw [uIoc_of_le hle] at hs
    have := hlow s (Ioc_subset_Icc_self hs) p hp
    rw [norm_mul, norm_inv]
    calc ‖g s - p‖⁻¹ * ‖deriv g s‖ ≤ (m / 2)⁻¹ * ‖deriv g s‖ :=
          mul_le_mul_of_nonneg_right (inv_anti₀ (half_pos hm0) this) (norm_nonneg _)
      _ = 2 / m * ‖deriv g s‖ := by rw [inv_div]
  · exact (continuous_const.mul (hgc.continuous_deriv le_rfl).norm).intervalIntegrable _ _
  · refine ae_of_all _ fun s hs => ?_
    rw [uIoc_of_le hle] at hs
    have hne : g s - p₀ ≠ 0 := sub_ne_zero.mpr fun h =>
      hp₀ (h ▸ P.mem_curve_of_mem_piece hi' (Ioc_subset_Icc_self hs))
    exact ((continuousAt_const.sub continuousAt_id).inv₀ hne).mul continuousAt_const

/-- The winding number is locally constant off the curve. -/
theorem eventually_windingNumber_eq {p₀ : ℂ} (hp₀ : p₀ ∉ P.curve) :
    ∀ᶠ p in 𝓝 p₀, P.windingNumber p = P.windingNumber p₀ := by
  have hopen : ∀ᶠ p in 𝓝 p₀, p ∈ P.curveᶜ := P.isOpen_compl_curve.mem_nhds hp₀
  have hcont : ContinuousAt P.windingQuot p₀ :=
    (P.continuousAt_contourIntegral_inv hp₀).div_const _
  have hnear : ∀ᶠ p in 𝓝 p₀, ‖P.windingQuot p - P.windingQuot p₀‖ < 1 := by
    filter_upwards [Metric.tendsto_nhds.mp hcont 1 one_pos] with p hp
    rwa [dist_eq_norm] at hp
  filter_upwards [hopen, hnear] with p hp hlt
  rw [P.windingQuot_eq_windingNumber hp, P.windingQuot_eq_windingNumber hp₀, ← Int.cast_sub,
    Complex.norm_intCast] at hlt
  have : |P.windingNumber p - P.windingNumber p₀| < 1 := by exact_mod_cast hlt
  exact sub_eq_zero.mp (Int.abs_lt_one_iff.mp this)

theorem continuousAt_windingNumber {p₀ : ℂ} (hp₀ : p₀ ∉ P.curve) :
    ContinuousAt P.windingNumber p₀ := by
  rw [ContinuousAt, nhds_discrete ℤ]
  exact Filter.tendsto_pure.mpr (P.eventually_windingNumber_eq hp₀)

/-- The winding number is constant on connected subsets of the complement of the curve. -/
theorem windingNumber_eq_of_isPreconnected {S : Set ℂ} (hS : IsPreconnected S)
    (hSc : S ⊆ P.curveᶜ) {p q : ℂ} (hp : p ∈ S) (hq : q ∈ S) :
    P.windingNumber p = P.windingNumber q :=
  hS.constant (fun _ hx => (P.continuousAt_windingNumber (hSc hx)).continuousWithinAt) hp hq

/-- Far from the curve the winding number vanishes. -/
theorem exists_forall_windingNumber_eq_zero :
    ∃ R : ℝ, ∀ p : ℂ, R < ‖p‖ → P.windingNumber p = 0 := by
  obtain ⟨M, hM⟩ := P.isCompact_curve.isBounded.subset_closedBall 0
  set L := ∑ i ∈ Finset.range P.n, ∫ s in P.t i..P.t (i + 1), ‖deriv (P.g i) s‖ with hL
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun i hi =>
    intervalIntegral.integral_nonneg (P.lt i (Finset.mem_range.mp hi)).le fun _ _ => norm_nonneg _
  refine ⟨max M 0 + L / (2 * π) + 1, fun p hp => ?_⟩
  set d := ‖p‖ - max M 0 with hd
  have hd0 : L / (2 * π) + 1 < d := by rw [hd]; linarith
  have hdpos : 0 < d := by
    have : 0 ≤ L / (2 * π) := div_nonneg hL0 (by positivity)
    linarith
  have hpc : p ∉ P.curve := fun h => by
    have := hM h
    rw [mem_closedBall_zero_iff] at this
    linarith [le_max_left M 0]
  have hpiece : ∀ i < P.n, ‖∫ s in P.t i..P.t (i + 1), (P.g i s - p)⁻¹ * deriv (P.g i) s‖ ≤
      (∫ s in P.t i..P.t (i + 1), ‖deriv (P.g i) s‖) / d := by
    intro i hi
    have hle := (P.lt i hi).le
    have hgc := P.contDiff i hi
    have hne : ∀ s ∈ Icc (P.t i) (P.t (i + 1)), d ≤ ‖P.g i s - p‖ := fun s hs => by
      have h1 : ‖P.g i s‖ ≤ M := by
        have := hM (P.mem_curve_of_mem_piece hi hs)
        rwa [mem_closedBall_zero_iff] at this
      calc d = ‖p‖ - max M 0 := rfl
        _ ≤ ‖p‖ - ‖P.g i s‖ := by linarith [le_max_left M 0]
        _ ≤ ‖P.g i s - p‖ := by rw [norm_sub_rev]; exact norm_sub_norm_le _ _
    refine (intervalIntegral.norm_integral_le_integral_norm hle).trans ?_
    rw [← intervalIntegral.integral_div]
    refine intervalIntegral.integral_mono_on hle ?_ ?_ fun s hs => ?_
    · refine (ContinuousOn.intervalIntegrable ?_)
      rw [uIcc_of_le hle]
      exact (((hgc.continuous.sub continuous_const).continuousOn.inv₀ fun s hs =>
        norm_pos_iff.mp (lt_of_lt_of_le hdpos (hne s hs))).mul
        (hgc.continuous_deriv le_rfl).continuousOn).norm
    · exact ((hgc.continuous_deriv le_rfl).norm.div_const _).intervalIntegrable _ _
    · rw [norm_mul, norm_inv, div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_right (inv_anti₀ hdpos (hne s hs)) (norm_nonneg _)
  have htot : ‖P.contourIntegral fun z => (z - p)⁻¹‖ ≤ L / d := by
    rw [contourIntegral, hL, Finset.sum_div]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => hpiece i (Finset.mem_range.mp hi))
  rw [P.contourIntegral_inv_eq hpc, norm_mul, norm_mul, norm_mul, Complex.norm_intCast,
    Complex.norm_two, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_I,
    mul_one] at htot
  have hLd : L / d < 2 * π := by
    rw [div_lt_iff₀ hdpos]
    nlinarith [Real.pi_pos, (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * π)).mp
      (show L / (2 * π) < d by linarith)]
  have habs : |(P.windingNumber p : ℝ)| < 1 := by
    by_contra h
    push Not at h
    have : 2 * π ≤ 2 * π * |(P.windingNumber p : ℝ)| := by nlinarith [Real.pi_pos]
    linarith
  exact Int.abs_lt_one_iff.mp (by exact_mod_cast habs)

/-- The exterior of a closed ball in `ℂ` is connected. -/
theorem isConnected_compl_closedBall_complex {R : ℝ} (hR : 0 ≤ R) :
    IsConnected {z : ℂ | R < ‖z‖} := by
  have h := (isConnected_compl_closedBall hR).image Arcs.complexLIE.symm
    Arcs.complexLIE.symm.continuous.continuousOn
  convert h using 1
  ext z
  constructor
  · intro hz
    exact ⟨Arcs.complexLIE z, by simpa using hz, by simp⟩
  · rintro ⟨w, hw, rfl⟩
    simpa using hw

/-- The winding number vanishes on the unbounded component of the complement. -/
theorem windingNumber_eq_zero_of_not_isBounded {p : ℂ} (hp : p ∉ P.curve)
    (hb : ¬ Bornology.IsBounded (connectedComponentIn P.curveᶜ p)) : P.windingNumber p = 0 := by
  obtain ⟨R, hR⟩ := P.exists_forall_windingNumber_eq_zero
  obtain ⟨M, hM⟩ := P.isCompact_curve.isBounded.subset_closedBall 0
  set T := max (max R M) 0 with hT
  have hnot : ¬ connectedComponentIn P.curveᶜ p ⊆ Metric.closedBall 0 T := fun h =>
    hb ((Metric.isBounded_iff_subset_closedBall 0).mpr ⟨T, h⟩)
  obtain ⟨q, hqC, hqT⟩ := not_subset.mp hnot
  rw [mem_closedBall_zero_iff, not_le] at hqT
  have hE : IsConnected {z : ℂ | T < ‖z‖} := isConnected_compl_closedBall_complex (le_max_right _ _)
  have hEsub : {z : ℂ | T < ‖z‖} ⊆ P.curveᶜ := fun z hz hzc => by
    have := hM hzc
    rw [mem_closedBall_zero_iff] at this
    have hz' : T < ‖z‖ := hz
    linarith [le_max_right R M, le_max_left (max R M) 0]
  have hEC : {z : ℂ | T < ‖z‖} ⊆ connectedComponentIn P.curveᶜ p := by
    rw [connectedComponentIn_eq hqC]
    exact hE.isPreconnected.subset_connectedComponentIn hqT hEsub
  have hq0 : P.windingNumber q = 0 :=
    hR q (lt_of_le_of_lt ((le_max_left R M).trans (le_max_left _ 0)) hqT)
  rw [← hq0]
  exact P.windingNumber_eq_of_isPreconnected isPreconnected_connectedComponentIn
    (connectedComponentIn_subset _ _) (mem_connectedComponentIn hp) hqC

end ClosedPiecewiseC1

end Azurite.JordanCurve
