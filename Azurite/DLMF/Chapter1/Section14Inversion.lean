/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section14
import Azurite.DLMF.Chapter1.Section8Poisson

/-!
# DLMF §1.14(i): Fourier inversion

Formalizations of (1.14.3) and (1.14.4).

**Method.**
* The Dirichlet integral `∫₀ᴿ sin z / z dz → π/2` (`sinInt`, `tendsto_sinInt`), which Mathlib
  lacks. It is derived from `∫₀^{1/2} Dₖ = ½` for the Dirichlet kernel of §1.8, since
  `1/sin(πy) − 1/(πy)` is bounded and Riemann–Lebesgue applies.
* Jordan's lemma for the kernel `sin(Rs)/s`: monotone case through the second mean value theorem
  (`tendsto_integral_monotone_mul_sinc`), bounded variation through the variation decomposition
  (`tendsto_integral_bv_mul_sinc`), complex-valued functions through real and imaginary parts
  (`tendsto_integral_bv_mul_sinc_complex`).
* Fubini turns the partial inverse transform into `π^{−1} ∫ f(u + s) sin(Rs)/s ds`
  (`partial_inverse_eq`). Splitting at `|s| = δ` leaves Riemann–Lebesgue far from `0`
  (`tendsto_integral_mul_sin_line`) and Jordan's lemma for `f(u ± s)` near `0`.

**Results.**
* 1.14.3 (`dlmf_1_14_3`): for `f` integrable and of bounded variation on `[u − δ, u + δ]`, the
  principal value `lim_{R→∞} (2π)^{−1/2} ∫_{−R}^{R} 𝓕(f)(x) e^{−ixu} dx` is `½(f(u+) + f(u−))`.
  The one-sided limits exist (`exists_tendsto_of_bv`, `dlmf_1_14_3'`).
* 1.14.4 (`dlmf_1_14_4`): for `f` integrable and `C¹`, the same principal value is `f(t)`. DLMF
  writes an ordinary integral, which need not converge absolutely.
-/

open MeasureTheory Filter Topology Set

namespace Azurite.DLMF

/-! ### The Dirichlet integral -/

/-- `Si(R) = ∫₀ᴿ sin z / z dz`. -/
noncomputable def sinInt (R : ℝ) : ℝ := ∫ z in (0 : ℝ)..R, Real.sin z / z

theorem abs_sin_div_le (z : ℝ) : |Real.sin z / z| ≤ 1 := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  rw [abs_div, div_le_one (abs_pos.mpr hz)]
  exact Real.abs_sin_le_abs

theorem intervalIntegrable_sin_div (a b : ℝ) :
    IntervalIntegrable (fun z => Real.sin z / z) volume a b :=
  (intervalIntegrable_const (c := (1 : ℝ))).mono_fun'
    ((by fun_prop : Measurable fun z : ℝ => Real.sin z / z).aestronglyMeasurable)
    (ae_of_all _ fun z => by
      show ‖Real.sin z / z‖ ≤ 1
      rw [Real.norm_eq_abs]; exact abs_sin_div_le z)

theorem continuous_sinInt : Continuous sinInt :=
  intervalIntegral.continuous_primitive (fun a b => intervalIntegrable_sin_div a b) 0

/-- `1/sin(πy) − 1/(πy)`, bounded on `(0, ½]`. -/
noncomputable def sinRemainder (y : ℝ) : ℝ := 1 / Real.sin (Real.pi * y) - 1 / (Real.pi * y)

theorem abs_sinRemainder_le {y : ℝ} (hy : y ∈ Ioc (0 : ℝ) (1 / 2)) : |sinRemainder y| ≤ 1 := by
  have hπ := Real.pi_pos
  set x := Real.pi * y with hxdef
  have hx0 : 0 < x := mul_pos hπ hy.1
  have hx2 : x ≤ 2 := by nlinarith [hy.2, Real.pi_le_four]
  have hxπ : x ≤ Real.pi / 2 := by nlinarith [hy.2]
  have hs0 : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx0 (by linarith)
  have hs1 := Real.sin_lt hx0
  have hs2 := Real.sin_gt_sub_cube hx0
  unfold sinRemainder
  rw [← hxdef, div_sub_div _ _ hs0.ne' hx0.ne', abs_le]
  constructor
  · have : 0 ≤ (1 * x - Real.sin x * 1) / (Real.sin x * x) :=
      div_nonneg (by linarith) (by positivity)
    linarith
  · rw [div_le_one (by positivity)]
    nlinarith [mul_nonneg (sq_nonneg x) (show 0 ≤ 6 - x - x ^ 2 by nlinarith),
      mul_lt_mul_of_pos_left hs2 hx0]

theorem intervalIntegrable_sinRemainder :
    IntervalIntegrable sinRemainder volume 0 (1 / 2) :=
  (intervalIntegrable_const (c := (1 : ℝ))).mono_fun'
    ((by unfold sinRemainder; fun_prop : Measurable sinRemainder).aestronglyMeasurable)
    ((ae_restrict_iff' measurableSet_uIoc).mpr (ae_of_all _ fun y hy => by
      rw [uIoc_of_le (by norm_num)] at hy
      show ‖sinRemainder y‖ ≤ 1
      rw [Real.norm_eq_abs]; exact abs_sinRemainder_le hy))

theorem integral_sin_mul_div {M : ℝ} (hM : 0 < M) :
    ∫ y in (0 : ℝ)..(1 / 2), Real.sin (M * y) / (Real.pi * y) = sinInt (M / 2) / Real.pi := by
  have hπ := Real.pi_pos
  have h1 : (fun y : ℝ => Real.sin (M * y) / (Real.pi * y)) =
      fun y => (M / Real.pi) * (Real.sin (M * y) / (M * y)) := by
    funext y
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    · field_simp
  rw [h1, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun z => Real.sin z / z) hM.ne', smul_eq_mul,
    mul_zero, sinInt]
  field_simp

theorem intervalIntegrable_sin_mul_div {M : ℝ} (hM : 0 < M) :
    IntervalIntegrable (fun y : ℝ => Real.sin (M * y) / (Real.pi * y)) volume 0 (1 / 2) := by
  have hπ := Real.pi_pos
  refine (intervalIntegrable_const (c := M / Real.pi)).mono_fun'
    ((by fun_prop : Measurable fun y : ℝ => Real.sin (M * y) / (Real.pi * y)).aestronglyMeasurable)
    (ae_of_all _ fun y => ?_)
  show ‖Real.sin (M * y) / (Real.pi * y)‖ ≤ M / Real.pi
  rw [Real.norm_eq_abs]
  rcases eq_or_ne y 0 with rfl | hy
  · simp; positivity
  rw [abs_div, div_le_div_iff₀ (abs_pos.mpr (by positivity)) hπ, abs_mul, abs_of_pos hπ]
  have := Real.abs_sin_le_abs (x := M * y)
  rw [abs_mul, abs_of_pos hM] at this
  nlinarith

/-- `Si((K + ½)π) → π/2`, from `∫₀^{1/2} Dₖ = ½`. -/
theorem tendsto_sinInt_half_odd :
    Tendsto (fun K : ℕ => sinInt ((2 * K + 1) * Real.pi / 2)) atTop (𝓝 (Real.pi / 2)) := by
  have hπ := Real.pi_pos
  have hM : ∀ K : ℕ, 0 < (2 * (K : ℝ) + 1) * Real.pi := fun K => by positivity
  have hsplit : ∀ K : ℕ, sinInt ((2 * K + 1) * Real.pi / 2) =
      Real.pi * (1 / 2 - ∫ y in (0 : ℝ)..(1 / 2),
        sinRemainder y * Real.sin ((2 * K + 1) * Real.pi * y)) := fun K => by
    have hD := integral_dirichlet1_half K
    have hr : IntervalIntegrable (fun y => sinRemainder y * Real.sin ((2 * K + 1) * Real.pi * y))
        volume 0 (1 / 2) :=
      intervalIntegrable_sinRemainder.mul_continuousOn (by fun_prop)
    have heq : ∫ y in (0 : ℝ)..(1 / 2), dirichlet1 K y =
        (∫ y in (0 : ℝ)..(1 / 2), Real.sin ((2 * K + 1) * Real.pi * y) / (Real.pi * y)) +
          ∫ y in (0 : ℝ)..(1 / 2), sinRemainder y * Real.sin ((2 * K + 1) * Real.pi * y) := by
      rw [← intervalIntegral.integral_add (intervalIntegrable_sin_mul_div (hM K)) hr]
      refine intervalIntegral.integral_congr_ae (ae_of_all _ fun y hy => ?_)
      rw [uIoc_of_le (by norm_num)] at hy
      have hs : 0 < Real.sin (Real.pi * y) :=
        Real.sin_pos_of_pos_of_lt_pi (mul_pos hπ hy.1) (by nlinarith [hy.2])
      have hd := dirichlet1_mul_sin K y
      have hy0 : y ≠ 0 := hy.1.ne'
      unfold sinRemainder
      field_simp
      rw [← hd]
      ring
    rw [integral_sin_mul_div (hM K)] at heq
    rw [hD, eq_comm, ← eq_sub_iff_add_eq, div_eq_iff hπ.ne'] at heq
    rw [heq]
    ring
  have hRL := tendsto_integral_mul_sin_real intervalIntegrable_sinRemainder
  have hlam : Tendsto (fun K : ℕ => (2 * (K : ℝ) + 1) * Real.pi) atTop atTop :=
    Tendsto.atTop_mul_const hπ (tendsto_atTop_add_const_right _ _
      (tendsto_natCast_atTop_atTop.const_mul_atTop two_pos))
  have := ((hRL.comp hlam).const_sub (1 / 2 : ℝ)).const_mul Real.pi
  rw [sub_zero, show Real.pi * (1 / 2) = Real.pi / 2 by ring] at this
  refine this.congr fun K => ?_
  rw [hsplit K]
  rfl

/-- **The Dirichlet integral**: `∫₀ᴿ sin z / z dz → π/2` as `R → ∞`. -/
theorem tendsto_sinInt : Tendsto sinInt atTop (𝓝 (Real.pi / 2)) := by
  have hπ := Real.pi_pos
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K₀, hK₀⟩ := (Metric.tendsto_atTop.mp tendsto_sinInt_half_odd) (ε / 2) (by positivity)
  obtain ⟨K₁, hK₁⟩ := exists_nat_gt (2 / ε)
  set m := max K₀ K₁
  refine ⟨(2 * m + 1) * Real.pi / 2, fun R hR => ?_⟩
  set K := ⌊R / Real.pi - 1 / 2⌋₊
  have hR0 : 0 ≤ R / Real.pi - 1 / 2 := by
    rw [sub_nonneg, le_div_iff₀ hπ]
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  have hKm : m ≤ K := Nat.le_floor (by
    rw [le_sub_iff_add_le, le_div_iff₀ hπ]; nlinarith)
  have hK1 : (K : ℝ) ≤ R / Real.pi - 1 / 2 := Nat.floor_le hR0
  have hK2 : R / Real.pi - 1 / 2 < K + 1 := Nat.lt_floor_add_one _
  set a := (2 * (K : ℝ) + 1) * Real.pi / 2
  have ha : 0 < a := by positivity
  have haR : a ≤ R := by
    have := (le_div_iff₀ hπ).mp (show (K : ℝ) + 1 / 2 ≤ R / Real.pi by linarith)
    simp only [a]; nlinarith
  have hRa : R - a ≤ Real.pi := by
    have := (div_lt_iff₀ hπ).mp (show R / Real.pi < K + 1 + 1 / 2 by linarith)
    simp only [a]; nlinarith
  have hdiff : |sinInt R - sinInt a| ≤ 2 / (2 * K + 1) := by
    rw [sinInt, sinInt, intervalIntegral.integral_interval_sub_left
      (intervalIntegrable_sin_div _ _) (intervalIntegrable_sin_div _ _), ← Real.norm_eq_abs]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := 1 / a) fun z hz => ?_).trans ?_
    · rw [uIoc_of_le haR] at hz
      have hz0 : 0 < z := ha.trans hz.1
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hz0]
      calc |Real.sin z| / z ≤ 1 / z := div_le_div_of_nonneg_right (Real.abs_sin_le_one z) hz0.le
        _ ≤ 1 / a := one_div_le_one_div_of_le ha hz.1.le
    · rw [abs_of_nonneg (by linarith)]
      calc 1 / a * (R - a) ≤ 1 / a * Real.pi := mul_le_mul_of_nonneg_left hRa (by positivity)
        _ = 2 / (2 * K + 1) := by simp only [a]; field_simp
  have hKK₁ : 2 / (2 * (K : ℝ) + 1) < ε / 2 := by
    have hk : (K₁ : ℝ) ≤ K := by exact_mod_cast (le_max_right K₀ K₁).trans hKm
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε] at hK₁
    nlinarith
  have h1 := hK₀ K ((le_max_left K₀ K₁).trans hKm)
  rw [Real.dist_eq] at h1 ⊢
  calc |sinInt R - Real.pi / 2| ≤ |sinInt R - sinInt a| + |sinInt a - Real.pi / 2| :=
        abs_sub_le _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt (hdiff.trans hKK₁.le) h1
    _ = ε := by ring

/-! ### Jordan's lemma for the kernel `sin(Rs)/s` -/

theorem exists_bound_sinInt : ∃ B, 0 ≤ B ∧ ∀ x, 0 ≤ x → |sinInt x| ≤ B := by
  obtain ⟨X, hX⟩ := (Metric.tendsto_atTop.mp tendsto_sinInt) 1 one_pos
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := 0) (b := X)).exists_bound_of_continuousOn
    continuous_sinInt.continuousOn
  refine ⟨max (max C (Real.pi / 2 + 1)) 0, le_max_right _ _, fun x hx => ?_⟩
  rcases le_total x X with h | h
  · have := hC x ⟨hx, h⟩
    rw [Real.norm_eq_abs] at this
    exact this.trans ((le_max_left _ _).trans (le_max_left _ _))
  · have := hX x h
    rw [Real.dist_eq] at this
    have hπ := Real.pi_pos
    refine le_trans ?_ ((le_max_right _ _).trans (le_max_left _ _))
    rw [abs_lt] at this
    rw [abs_le]
    constructor <;> linarith [this.1, this.2]

theorem intervalIntegrable_sinc (R a b : ℝ) :
    IntervalIntegrable (fun s : ℝ => Real.sin (R * s) / s) volume a b :=
  (intervalIntegrable_const (c := |R|)).mono_fun'
    ((by fun_prop : Measurable fun s : ℝ => Real.sin (R * s) / s).aestronglyMeasurable)
    (ae_of_all _ fun s => by
      show ‖Real.sin (R * s) / s‖ ≤ |R|
      rw [Real.norm_eq_abs]
      rcases eq_or_ne s 0 with rfl | hs
      · simp
      rw [abs_div, div_le_iff₀ (abs_pos.mpr hs)]
      have := Real.abs_sin_le_abs (x := R * s)
      rwa [abs_mul] at this)

theorem abs_sinc_le (R s : ℝ) : |Real.sin (R * s) / s| ≤ |R| := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp
  rw [abs_div, div_le_iff₀ (abs_pos.mpr hs)]
  have := Real.abs_sin_le_abs (x := R * s)
  rwa [abs_mul] at this

theorem intervalIntegrable_mul_sinc {g : ℝ → ℝ} {a b : ℝ} (hg : IntervalIntegrable g volume a b)
    (R : ℝ) : IntervalIntegrable (fun s => g s * (Real.sin (R * s) / s)) volume a b := by
  have hm : AEStronglyMeasurable (fun s : ℝ => Real.sin (R * s) / s) :=
    (by fun_prop : Measurable fun s : ℝ => Real.sin (R * s) / s).aestronglyMeasurable
  exact ⟨hg.1.mul_bdd (c := |R|) hm.restrict (ae_of_all _ fun s => by
      rw [Real.norm_eq_abs]; exact abs_sinc_le R s),
    hg.2.mul_bdd (c := |R|) hm.restrict (ae_of_all _ fun s => by
      rw [Real.norm_eq_abs]; exact abs_sinc_le R s)⟩

theorem integral_sinc {R : ℝ} (hR : 0 < R) (a b : ℝ) :
    ∫ s in a..b, Real.sin (R * s) / s = sinInt (R * b) - sinInt (R * a) := by
  have h1 : (fun s : ℝ => Real.sin (R * s) / s) = fun s => R * (Real.sin (R * s) / (R * s)) := by
    funext s
    rcases eq_or_ne s 0 with rfl | hs
    · simp
    · field_simp
  rw [h1, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun z => Real.sin z / z) hR.ne', smul_eq_mul,
    ← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul, sinInt, sinInt,
    intervalIntegral.integral_interval_sub_left (intervalIntegrable_sin_div _ _)
      (intervalIntegrable_sin_div _ _)]

theorem abs_integral_sinc_le {B : ℝ} (hB : ∀ x, 0 ≤ x → |sinInt x| ≤ B) {R : ℝ} (hR : 0 < R)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : |∫ s in a..b, Real.sin (R * s) / s| ≤ 2 * B := by
  rw [integral_sinc hR]
  have h1 := hB (R * b) (by nlinarith)
  have h2 := hB (R * a) (by positivity)
  calc |sinInt (R * b) - sinInt (R * a)| ≤ |sinInt (R * b)| + |sinInt (R * a)| := abs_sub _ _
    _ ≤ 2 * B := by linarith

/-- **Jordan's lemma**, monotone case: for nondecreasing `h` with right limit `L` at `0`,
`∫₀^δ h(s) sin(Rs)/s ds → (π/2) L` as `R → ∞`. -/
theorem tendsto_integral_monotone_mul_sinc {h : ℝ → ℝ} (hmono : Monotone h) {L : ℝ}
    (hL : Tendsto h (𝓝[>] 0) (𝓝 L)) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun R => ∫ s in (0 : ℝ)..δ, h s * (Real.sin (R * s) / s)) atTop
      (𝓝 (Real.pi / 2 * L)) := by
  obtain ⟨B, hB0, hB⟩ := exists_bound_sinInt
  have hhint : ∀ c d, IntervalIntegrable (fun y => h y - L) volume c d := fun c d =>
    hmono.intervalIntegrable.sub intervalIntegrable_const
  have hge : ∀ y, 0 < y → L ≤ h y := fun y hy => le_of_tendsto hL (by
    filter_upwards [mem_nhdsGT_zero_of_pos hy (subset_refl _)] with z hz
    exact hmono hz.2.le)
  have hsub : ∀ R, 0 < R → (∫ s in (0 : ℝ)..δ, h s * (Real.sin (R * s) / s)) =
      (∫ s in (0 : ℝ)..δ, (h s - L) * (Real.sin (R * s) / s)) + L * sinInt (R * δ) :=
    fun R hR => by
      have := integral_sinc hR 0 δ
      rw [mul_zero, show sinInt 0 = 0 from intervalIntegral.integral_same, sub_zero] at this
      rw [← this, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add
        (intervalIntegrable_mul_sinc (hhint 0 δ) R) ((intervalIntegrable_sinc R 0 δ).const_mul L)]
      refine intervalIntegral.integral_congr fun y _ => ?_
      ring
  have hlimL : Tendsto (fun R => L * sinInt (R * δ)) atTop (𝓝 (Real.pi / 2 * L)) := by
    rw [mul_comm]
    exact (tendsto_sinInt.comp (tendsto_id.atTop_mul_const hδ)).const_mul L
  suffices hmain : Tendsto (fun R => ∫ s in (0 : ℝ)..δ, (h s - L) * (Real.sin (R * s) / s))
      atTop (𝓝 0) by
    have := hmain.add hlimL
    rw [zero_add] at this
    refine this.congr' ?_
    filter_upwards [Ioi_mem_atTop 0] with R (hR : 0 < R)
    exact (hsub R hR).symm
  rw [Metric.tendsto_atTop]
  intro ε hε
  set ε' := ε / (2 * B + 2)
  have hε' : 0 < ε' := by positivity
  obtain ⟨η, hη0, hηδ, hηε⟩ : ∃ η, 0 < η ∧ η ≤ δ ∧ h η - L ≤ ε' := by
    have hev : ∀ᶠ y in 𝓝[>] (0 : ℝ), h y < L + ε' := hL.eventually (gt_mem_nhds (by linarith))
    obtain ⟨u, hu, hsub'⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
    have hu0 : (0 : ℝ) < u := hu
    refine ⟨min (u / 2) δ, lt_min (by linarith) hδ, min_le_right _ _, ?_⟩
    have := hsub' (show min (u / 2) δ ∈ Ioo 0 u from
      ⟨lt_min (by linarith) hδ, (min_le_left _ _).trans_lt (by linarith)⟩)
    simp only [Set.mem_ofPred_eq] at this
    linarith
  -- near `0`: second mean value theorem
  have hnear : ∀ R, 0 < R →
      |∫ s in (0 : ℝ)..η, (h s - L) * (Real.sin (R * s) / s)| ≤ 2 * B * ε' := fun R hR => by
    set φ : ℝ → ℝ := fun y => max (h y - L) 0
    have hcongr : ∫ s in (0 : ℝ)..η, (h s - L) * (Real.sin (R * s) / s) =
        ∫ s in (0 : ℝ)..η, φ s • (Real.sin (R * s) / s) := by
      refine intervalIntegral.integral_congr_ae (ae_of_all _ fun y hy => ?_)
      rw [Set.uIoc_of_le hη0.le] at hy
      simp only [φ, smul_eq_mul, max_eq_left (sub_nonneg.mpr (hge y hy.1))]
    obtain ⟨ξ, hξ, hb⟩ := exists_le_const_mul_norm_intervalIntegral_of_nonneg_of_monotoneOn
      (f := φ) hη0.le (le_max_right _ _ : (0 : ℝ) ≤ φ 0)
      (fun y _ z _ hyz => by
        simp only [φ]; exact max_le_max (sub_le_sub_right (hmono hyz) L) le_rfl)
      (intervalIntegrable_sinc R 0 η)
    rw [hcongr, ← Real.norm_eq_abs]
    refine hb.trans ?_
    have h1 : φ η ≤ ε' := max_le hηε hε'.le
    have h2 : ‖∫ s in ξ..η, Real.sin (R * s) / s‖ ≤ 2 * B := by
      rw [Real.norm_eq_abs]; exact abs_integral_sinc_le hB hR hξ.1 hξ.2
    calc φ η * ‖∫ s in ξ..η, Real.sin (R * s) / s‖ ≤ ε' * (2 * B) :=
          mul_le_mul h1 h2 (norm_nonneg _) hε'.le
      _ = 2 * B * ε' := by ring
  -- away from `0`: Riemann–Lebesgue
  have hfar : Tendsto (fun R => ∫ s in η..δ, (h s - L) * (Real.sin (R * s) / s)) atTop
      (𝓝 0) := by
    have hg : IntervalIntegrable (fun s => (h s - L) * (1 / s)) volume η δ :=
      (hhint η δ).mul_continuousOn (ContinuousOn.div continuousOn_const continuousOn_id
        fun y hy => by
          rw [uIcc_of_le hηδ] at hy
          exact (hη0.trans_le hy.1).ne')
    refine (tendsto_integral_mul_sin_real hg).congr fun R => ?_
    refine intervalIntegral.integral_congr fun y _ => ?_
    ring
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hfar) ε' hε'
  refine ⟨max N 1, fun R hR => ?_⟩
  have hR0 : 0 < R := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hR)
  have h3 := hN R ((le_max_left _ _).trans hR)
  rw [Real.dist_eq, sub_zero] at h3 ⊢
  rw [← intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_mul_sinc (hhint 0 η) R)
    (intervalIntegrable_mul_sinc (hhint η δ) R)]
  have h4 := hnear R hR0
  calc |(∫ s in (0 : ℝ)..η, (h s - L) * (Real.sin (R * s) / s)) +
        ∫ s in η..δ, (h s - L) * (Real.sin (R * s) / s)|
      ≤ |∫ s in (0 : ℝ)..η, (h s - L) * (Real.sin (R * s) / s)| +
          |∫ s in η..δ, (h s - L) * (Real.sin (R * s) / s)| := abs_add_le _ _
    _ < 2 * B * ε' + ε' := by linarith
    _ = (2 * B + 1) * ε' := by ring
    _ ≤ ε := by
        simp only [ε']
        rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
        nlinarith

/-- The clamp of `y` to `[0, δ]`. -/
noncomputable def clampTo (δ y : ℝ) : ℝ := max 0 (min y δ)

theorem clampTo_mem {δ : ℝ} (hδ : 0 ≤ δ) (y : ℝ) : clampTo δ y ∈ Icc 0 δ :=
  ⟨le_max_left _ _, max_le hδ (min_le_right _ _)⟩

theorem clampTo_mono (δ : ℝ) : Monotone (clampTo δ) := fun _ _ h =>
  max_le_max le_rfl (min_le_min h le_rfl)

theorem clampTo_of_mem {δ y : ℝ} (hy : y ∈ Icc 0 δ) : clampTo δ y = y := by
  simp only [clampTo]; rw [min_eq_left hy.2, max_eq_right hy.1]

/-- **Jordan's lemma**: for `g` of bounded variation on `[0, δ]` with right limit `L` at `0`,
`∫₀^δ g(s) sin(Rs)/s ds → (π/2) L`. -/
theorem tendsto_integral_bv_mul_sinc {g : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hg : BoundedVariationOn g (Icc 0 δ)) {L : ℝ} (hL : Tendsto g (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun R => ∫ s in (0 : ℝ)..δ, g s * (Real.sin (R * s) / s)) atTop
      (𝓝 (Real.pi / 2 * L)) := by
  set s : Set ℝ := Icc 0 δ
  have hs0 : (0 : ℝ) ∈ s := ⟨le_rfl, hδ.le⟩
  have hloc := hg.locallyBoundedVariationOn
  set P := variationOnFromTo g s 0
  set Q := variationOnFromTo g s 0 - g
  have hP : MonotoneOn P s := variationOnFromTo.monotoneOn hloc hs0
  have hQ : MonotoneOn Q s := variationOnFromTo.sub_self_monotoneOn hloc hs0
  set P' := fun y => P (clampTo δ y)
  set Q' := fun y => Q (clampTo δ y)
  have hP' : Monotone P' := fun y z hyz =>
    hP (clampTo_mem hδ.le y) (clampTo_mem hδ.le z) (clampTo_mono δ hyz)
  have hQ' : Monotone Q' := fun y z hyz =>
    hQ (clampTo_mem hδ.le y) (clampTo_mem hδ.le z) (clampTo_mono δ hyz)
  have hLP := hP'.tendsto_nhdsGT 0
  have hLQ := hQ'.tendsto_nhdsGT 0
  have hJP := tendsto_integral_monotone_mul_sinc hP' hLP hδ
  have hJQ := tendsto_integral_monotone_mul_sinc hQ' hLQ hδ
  have hgPQ : ∀ y ∈ s, g y = P' y - Q' y := fun y hy => by
    show g y = P (clampTo δ y) - (P (clampTo δ y) - g (clampTo δ y))
    rw [clampTo_of_mem hy]; ring
  have hs_mem : s ∈ 𝓝[>] (0 : ℝ) := mem_nhdsGT_zero_of_pos hδ Ioo_subset_Icc_self
  have hlim : sInf (P' '' Ioi 0) - sInf (Q' '' Ioi 0) = L := by
    have h1 : Tendsto g (𝓝[>] 0) (𝓝 (sInf (P' '' Ioi 0) - sInf (Q' '' Ioi 0))) :=
      (hLP.sub hLQ).congr' (by
        filter_upwards [hs_mem] with y hy
        exact (hgPQ y hy).symm)
    exact tendsto_nhds_unique h1 hL
  have hint : ∀ R, ∫ y in (0 : ℝ)..δ, g y * (Real.sin (R * y) / y) =
      (∫ y in (0 : ℝ)..δ, P' y * (Real.sin (R * y) / y)) -
        ∫ y in (0 : ℝ)..δ, Q' y * (Real.sin (R * y) / y) := fun R => by
    rw [← intervalIntegral.integral_sub (intervalIntegrable_mul_sinc hP'.intervalIntegrable R)
      (intervalIntegrable_mul_sinc hQ'.intervalIntegrable R)]
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [Set.uIcc_of_le hδ.le] at hy
    rw [hgPQ y hy]
    ring
  simp_rw [hint]
  rw [← hlim, mul_sub]
  exact hJP.sub hJQ

/-- Jordan's lemma for complex-valued `φ`, through the real and imaginary parts. -/
theorem tendsto_integral_bv_mul_sinc_complex {φ : ℝ → ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hφ : BoundedVariationOn φ (Icc 0 δ)) (hφi : IntervalIntegrable φ volume 0 δ) {L : ℂ}
    (hL : Tendsto φ (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun R => ∫ s in (0 : ℝ)..δ, φ s * ((Real.sin (R * s) / s : ℝ) : ℂ)) atTop
      (𝓝 (((Real.pi / 2 : ℝ) : ℂ) * L)) := by
  have hre := tendsto_integral_bv_mul_sinc hδ
    (Complex.reCLM.lipschitzWith.comp_boundedVariationOn hφ) (L := L.re)
    ((Complex.continuous_re.tendsto L).comp hL)
  have him := tendsto_integral_bv_mul_sinc hδ
    (Complex.imCLM.lipschitzWith.comp_boundedVariationOn hφ) (L := L.im)
    ((Complex.continuous_im.tendsto L).comp hL)
  have hint : ∀ R, IntervalIntegrable (fun s => φ s * ((Real.sin (R * s) / s : ℝ) : ℂ))
      volume 0 δ := fun R => by
    have hm : AEStronglyMeasurable (fun s : ℝ => ((Real.sin (R * s) / s : ℝ) : ℂ)) :=
      (by fun_prop : Measurable fun s : ℝ => ((Real.sin (R * s) / s : ℝ) : ℂ)).aestronglyMeasurable
    exact ⟨hφi.1.mul_bdd (c := |R|) hm.restrict (ae_of_all _ fun s => by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_sinc_le R s),
      hφi.2.mul_bdd (c := |R|) hm.restrict (ae_of_all _ fun s => by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_sinc_le R s)⟩
  have hdecomp : ∀ R, ∫ s in (0 : ℝ)..δ, φ s * ((Real.sin (R * s) / s : ℝ) : ℂ) =
      ((∫ s in (0 : ℝ)..δ, (φ s).re * (Real.sin (R * s) / s) : ℝ) : ℂ) +
        ((∫ s in (0 : ℝ)..δ, (φ s).im * (Real.sin (R * s) / s) : ℝ) : ℂ) * Complex.I :=
    fun R => by
      have h1 := Complex.reCLM.intervalIntegral_comp_comm (hint R)
      have h2 := Complex.imCLM.intervalIntegral_comp_comm (hint R)
      simp only [Complex.reCLM_apply, Complex.imCLM_apply, Complex.re_mul_ofReal,
        Complex.im_mul_ofReal] at h1 h2
      apply Complex.ext <;> simp [h1, h2]
  have := (((Complex.continuous_ofReal.tendsto _).comp hre).add
    (((Complex.continuous_ofReal.tendsto _).comp him).mul_const Complex.I))
  refine (this.congr fun R => (hdecomp R).symm).trans (le_of_eq ?_)
  congr 1
  apply Complex.ext <;> simp

/-! ### The partial inverse transform as a Dirichlet integral -/

open Complex in
theorem integral_exp_I_mul {R : ℝ} (a : ℝ) (ha : a ≠ 0) :
    ∫ x in (-R)..R, cexp (I * x * a) = 2 * ((Real.sin (R * a) / a : ℝ) : ℂ) := by
  have hc : I * (a : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr ha)
  have := integral_exp_mul_complex (a := -R) (b := R) hc
  rw [show (fun x : ℝ => cexp (I * x * a)) = fun x : ℝ => cexp (I * a * x) from
    funext fun x => by ring_nf, this]
  have ha' : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha
  push_cast
  rw [Complex.sin]
  field_simp
  ring_nf
  rw [I_sq]
  ring_nf

open Complex in
/-- For integrable `f` and `R > 0`:
`(2π)^{−1/2} ∫_{−R}^{R} 𝓕(f)(x) e^{−ixu} dx = π^{−1} ∫ f(u + s) sin(Rs)/s ds`. -/
theorem partial_inverse_eq {f : ℝ → ℂ} (hf : Integrable f) (u : ℝ) {R : ℝ} (hR : 0 < R) :
    ((√(2 * Real.pi) : ℝ) : ℂ)⁻¹ * ∫ x in (-R)..R, dlmfFourier f x * cexp (-(I * x * u)) =
      (Real.pi : ℂ)⁻¹ * ∫ s, f (u + s) * ((Real.sin (R * s) / s : ℝ) : ℂ) := by
  set c : ℂ := ((√(2 * Real.pi) : ℝ) : ℂ)⁻¹ with hc
  have hπ := Real.pi_pos
  have hcc : c * c = ((2 * Real.pi : ℝ) : ℂ)⁻¹ := by
    rw [hc, ← mul_inv, ← ofReal_mul, Real.mul_self_sqrt (by positivity)]
  have hfin : IsFiniteMeasure (volume.restrict (Ioc (-R) R)) :=
    isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
  -- the integrand as a function of `(x, t)`
  set F : ℝ → ℝ → ℂ := fun x t => f t * cexp (I * x * (t - u)) with hF
  have hFi : Integrable (Function.uncurry F) ((volume.restrict (Ioc (-R) R)).prod volume) := by
    refine Integrable.mono' (hf.norm.comp_snd _) ?_ (ae_of_all _ fun p => ?_)
    · exact (hf.1.comp_snd).mul (Continuous.aestronglyMeasurable (by fun_prop))
    · simp only [Function.uncurry, hF, norm_mul, norm_exp]
      rw [show (I * (p.1 : ℂ) * ((p.2 : ℂ) - u)).re = 0 by simp, Real.exp_zero, mul_one]
  have hstep1 : ∫ x in (-R)..R, dlmfFourier f x * cexp (-(I * x * u)) =
      c * ∫ x in Ioc (-R) R, ∫ t, F x t := by
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun x _ => ?_
    simp only [dlmfFourier, hF, mul_assoc]
    rw [← hc, ← integral_mul_const]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only
    rw [mul_assoc, ← Complex.exp_add]
    ring_nf
  have hstep2 : ∫ x in Ioc (-R) R, ∫ t, F x t = ∫ t, ∫ x in Ioc (-R) R, F x t :=
    integral_integral_swap hFi
  have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ u := by
    rw [ae_iff]; simp
  have hstep3 : ∫ t, ∫ x in Ioc (-R) R, F x t =
      2 * ∫ t, f t * ((Real.sin (R * (t - u)) / (t - u) : ℝ) : ℂ) := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hne] with t ht
    simp only [hF]
    rw [integral_const_mul, ← intervalIntegral.integral_of_le (by linarith),
      show (fun x : ℝ => cexp (I * x * (t - u))) = fun x : ℝ => cexp (I * x * ((t - u : ℝ) : ℂ))
        from funext fun x => by push_cast; ring_nf,
      integral_exp_I_mul (t - u) (sub_ne_zero.mpr ht)]
    ring
  have hshift : ∫ t, f t * ((Real.sin (R * (t - u)) / (t - u) : ℝ) : ℂ) =
      ∫ s, f (u + s) * ((Real.sin (R * s) / s : ℝ) : ℂ) := by
    rw [← integral_add_left_eq_self
      (fun t => f t * ((Real.sin (R * (t - u)) / (t - u) : ℝ) : ℂ)) u]
    refine integral_congr_ae (ae_of_all _ fun s => ?_)
    simp only [add_sub_cancel_left]
  rw [hstep1, hstep2, hstep3, hshift, ← mul_assoc, ← mul_assoc, hcc]
  push_cast
  field_simp

/-! ### The inversion theorem -/

open Complex in
/-- The Riemann–Lebesgue part: `∫ G(s) sin(Rs) ds → 0` for integrable `G`. -/
theorem tendsto_integral_mul_sin_line {G : ℝ → ℂ} (hG : Integrable G) :
    Tendsto (fun R : ℝ => ∫ s, G s * ((Real.sin (R * s) : ℝ) : ℂ)) atTop (𝓝 0) := by
  have h1 := dlmf_1_14_i_tendsto_atTop G
  have h2 := (dlmf_1_14_i_tendsto_atBot G).comp tendsto_neg_atTop_atBot
  have hs : ((√(2 * Real.pi) : ℝ) : ℂ) ≠ 0 := sqrt_two_pi_ne_zero
  have hI : (2 * I) ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero
  have hint : ∀ x : ℝ, ∫ t, G t * cexp (I * x * t) =
      ((√(2 * Real.pi) : ℝ) : ℂ) * dlmfFourier G x := fun x => by
    rw [dlmfFourier, ← mul_assoc, mul_inv_cancel₀ hs, one_mul]
  have heq : ∀ R : ℝ, ∫ s, G s * ((Real.sin (R * s) : ℝ) : ℂ) =
      (((√(2 * Real.pi) : ℝ) : ℂ) * dlmfFourier G R -
        ((√(2 * Real.pi) : ℝ) : ℂ) * dlmfFourier G (-R)) / (2 * I) := fun R => by
    rw [← hint, ← hint, ← integral_sub (integrable_mul_exp hG R) (integrable_mul_exp hG (-R)),
      ← integral_div]
    refine integral_congr_ae (ae_of_all _ fun s => ?_)
    simp only
    rw [ofReal_sin, Complex.sin]
    push_cast
    field_simp
    ring_nf
    rw [I_sq]
    ring
  have := ((h1.const_mul ((√(2 * Real.pi) : ℝ) : ℂ)).sub
    (h2.const_mul ((√(2 * Real.pi) : ℝ) : ℂ))).div_const (2 * I)
  rw [mul_zero, sub_zero, zero_div] at this
  exact this.congr fun R => (heq R).symm

theorem tendsto_nhdsGT_add {f : ℝ → ℂ} {u : ℝ} {L : ℂ} (h : Tendsto f (𝓝[>] u) (𝓝 L)) :
    Tendsto (fun s => f (u + s)) (𝓝[>] 0) (𝓝 L) := by
  refine h.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_)
  · have : Tendsto (fun s : ℝ => u + s) (𝓝 0) (𝓝 (u + 0)) :=
      tendsto_const_nhds.add tendsto_id
    rw [add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
    show u < u + s
    linarith

theorem tendsto_nhdsGT_sub {f : ℝ → ℂ} {u : ℝ} {L : ℂ} (h : Tendsto f (𝓝[<] u) (𝓝 L)) :
    Tendsto (fun s => f (u - s)) (𝓝[>] 0) (𝓝 L) := by
  refine h.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_)
  · have : Tendsto (fun s : ℝ => u - s) (𝓝 0) (𝓝 (u - 0)) :=
      tendsto_const_nhds.sub tendsto_id
    rw [sub_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
    show u - s < u
    linarith

open Complex in
/-- **DLMF (1.14.3)** (Fourier inversion): if `f` is absolutely integrable and of bounded variation
on a neighborhood `[u − δ, u + δ]` of `u`, with one-sided limits `f(u+)`, `f(u−)`, then the
Cauchy principal value `(2π)^{−1/2} ⨍ 𝓕(f)(x) e^{−ixu} dx = lim_{R→∞} ∫_{−R}^{R}` equals
`½ (f(u+) + f(u−))`. -/
theorem dlmf_1_14_3 {f : ℝ → ℂ} (hf : Integrable f) {u δ : ℝ} (hδ : 0 < δ)
    (hbv : BoundedVariationOn f (Icc (u - δ) (u + δ))) {Lp Lm : ℂ}
    (hp : Tendsto f (𝓝[>] u) (𝓝 Lp)) (hm : Tendsto f (𝓝[<] u) (𝓝 Lm)) :
    Tendsto (fun R : ℝ => ((√(2 * Real.pi) : ℝ) : ℂ)⁻¹ *
      ∫ x in (-R)..R, dlmfFourier f x * cexp (-(I * x * u))) atTop (𝓝 ((Lp + Lm) / 2)) := by
  have hπ := Real.pi_pos
  set k : ℝ → ℝ → ℂ := fun R s => ((Real.sin (R * s) / s : ℝ) : ℂ) with hk
  have hfu : Integrable fun s => f (u + s) := hf.comp_add_left u
  have hfu' : Integrable fun s => f (u - s) := hf.comp_sub_left u
  -- the two one-sided pieces
  have hbv1 : BoundedVariationOn (fun s => f (u + s)) (Icc 0 δ) :=
    ne_top_of_le_ne_top hbv (eVariationOn.comp_le_of_monotoneOn f (fun s => u + s)
      (fun a _ b _ hab => by simp only; linarith)
      (fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩))
  have hbv2 : BoundedVariationOn (fun s => f (u - s)) (Icc 0 δ) :=
    ne_top_of_le_ne_top hbv (eVariationOn.comp_le_of_antitoneOn f (fun s => u - s)
      (fun a _ b _ hab => by simp only; linarith)
      (fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩))
  have hJ1 := tendsto_integral_bv_mul_sinc_complex hδ hbv1 hfu.intervalIntegrable
    (tendsto_nhdsGT_add hp)
  have hJ2 := tendsto_integral_bv_mul_sinc_complex hδ hbv2 hfu'.intervalIntegrable
    (tendsto_nhdsGT_sub hm)
  -- the outer piece
  set G : ℝ → ℂ := (Ioc (-δ) δ)ᶜ.indicator fun s => f (u + s) / s with hGdef
  have hG : Integrable G := by
    rw [hGdef, integrable_indicator_iff measurableSet_Ioc.compl]
    refine Integrable.mono' ((hfu.norm.div_const δ).integrableOn) ?_ ?_
    · exact (hfu.1.mul (by fun_prop : Measurable fun s : ℝ => ((s : ℂ))⁻¹).aestronglyMeasurable
        ).restrict.congr (ae_of_all _ fun s => (div_eq_mul_inv _ _).symm)
    · refine (ae_restrict_iff' measurableSet_Ioc.compl).mpr (ae_of_all _ fun s hs => ?_)
      have hs' : δ ≤ |s| := by
        simp only [mem_compl_iff, mem_Ioc, not_and_or, not_lt, not_le] at hs
        rcases hs with hs | hs
        · rw [abs_of_nonpos (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
      exact div_le_div_of_nonneg_left (norm_nonneg _) hδ hs'
  have hout := tendsto_integral_mul_sin_line hG
  -- the decomposition
  have hH : ∀ R, Integrable fun s => f (u + s) * k R s := fun R =>
    hfu.mul_bdd (c := |R|) ((by fun_prop : Measurable fun s : ℝ =>
      ((Real.sin (R * s) / s : ℝ) : ℂ)).aestronglyMeasurable)
      (ae_of_all _ fun s => by rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_sinc_le R s)
  have hsplit : ∀ R, ∫ s, f (u + s) * k R s =
      (∫ s in (0 : ℝ)..δ, f (u + s) * k R s) + (∫ s in (0 : ℝ)..δ, f (u - s) * k R s) +
        ∫ s, G s * ((Real.sin (R * s) : ℝ) : ℂ) := fun R => by
    rw [← integral_add_compl (s := Ioc (-δ) δ) measurableSet_Ioc (hH R),
      ← intervalIntegral.integral_of_le (show -δ ≤ δ by linarith),
      ← intervalIntegral.integral_add_adjacent_intervals (a := -δ) (b := 0)
      (c := δ) ((hH R).intervalIntegrable) ((hH R).intervalIntegrable)]
    have hneg : ∫ s in (-δ)..0, f (u + s) * k R s = ∫ s in (0 : ℝ)..δ, f (u - s) * k R s := by
      have := intervalIntegral.integral_comp_neg (a := 0) (b := δ)
        (fun s => f (u + s) * k R s)
      rw [neg_zero] at this
      rw [← this]
      refine intervalIntegral.integral_congr fun s _ => ?_
      simp only [hk, ← sub_eq_add_neg, mul_neg, Real.sin_neg, neg_div_neg_eq]
    have hcompl : ∫ s in (Ioc (-δ) δ)ᶜ, f (u + s) * k R s =
        ∫ s, G s * ((Real.sin (R * s) : ℝ) : ℂ) := by
      rw [← integral_indicator measurableSet_Ioc.compl]
      refine integral_congr_ae (ae_of_all _ fun s => ?_)
      by_cases hs : s ∈ (Ioc (-δ) δ)ᶜ
      · have hs0 : s ≠ 0 := by
          rintro rfl
          exact hs ⟨by linarith, hδ.le⟩
        simp only [hGdef, indicator_of_mem hs, hk]
        push_cast
        field_simp
      · simp only [hGdef, indicator_of_notMem hs, zero_mul]
    rw [hneg, hcompl]
    ring
  have hlim := (hJ1.add hJ2).add hout
  rw [add_zero] at hlim
  have hfinal := hlim.const_mul ((Real.pi : ℂ)⁻¹)
  have hval : (Real.pi : ℂ)⁻¹ * (((Real.pi / 2 : ℝ) : ℂ) * Lp + ((Real.pi / 2 : ℝ) : ℂ) * Lm) =
      (Lp + Lm) / 2 := by
    have : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr hπ.ne'
    push_cast
    field_simp
  rw [hval] at hfinal
  refine hfinal.congr' ?_
  filter_upwards [Ioi_mem_atTop 0] with R (hR : 0 < R)
  rw [partial_inverse_eq hf u hR]
  congr 1
  exact (hsplit R).symm

open Complex in
/-- **DLMF (1.14.4)**: if `f` is absolutely integrable with continuous derivative, then
`f(t) = (2π)^{−1/2} ∫ 𝓕(f)(x) e^{−ixt} dx`, the integral taken as a principal value
`lim_{R→∞} ∫_{−R}^{R}` (DLMF writes an ordinary integral, which need not converge absolutely). -/
theorem dlmf_1_14_4 {f : ℝ → ℂ} (hf : Integrable f) (hc : ContDiff ℝ 1 f) (t : ℝ) :
    Tendsto (fun R : ℝ => ((√(2 * Real.pi) : ℝ) : ℂ)⁻¹ *
      ∫ x in (-R)..R, dlmfFourier f x * cexp (-(I * x * t))) atTop (𝓝 (f t)) := by
  obtain ⟨K, hK⟩ := hc.contDiffOn.exists_lipschitzOnWith (s := Icc (t - 1) (t + 1))
    one_ne_zero (convex_Icc _ _) isCompact_Icc
  have hbv : BoundedVariationOn f (Icc (t - 1) (t + 1)) := by
    have := hK.locallyBoundedVariationOn (t - 1) (t + 1) ⟨le_rfl, by linarith⟩
      ⟨by linarith, le_rfl⟩
    rwa [inter_self] at this
  have hcont := hc.continuous.continuousAt (x := t)
  have := dlmf_1_14_3 hf one_pos hbv (hcont.tendsto.mono_left nhdsWithin_le_nhds)
    (hcont.tendsto.mono_left nhdsWithin_le_nhds)
  rwa [add_self_div_two] at this

/-! ### One-sided limits of functions of bounded variation -/

theorem exists_tendsto_of_bv_real {g : ℝ → ℝ} {a u b : ℝ} (hau : a < u) (hub : u < b)
    (hg : BoundedVariationOn g (Icc a b)) :
    (∃ L, Tendsto g (𝓝[>] u) (𝓝 L)) ∧ ∃ L, Tendsto g (𝓝[<] u) (𝓝 L) := by
  set s := Icc a b
  have ha : a ∈ s := ⟨le_rfl, (hau.trans hub).le⟩
  have hus : u ∈ s := ⟨hau.le, hub.le⟩
  have hloc := hg.locallyBoundedVariationOn
  set P := variationOnFromTo g s a
  set Q := variationOnFromTo g s a - g
  have hP : MonotoneOn P s := variationOnFromTo.monotoneOn hloc ha
  have hQ : MonotoneOn Q s := variationOnFromTo.sub_self_monotoneOn hloc ha
  have hR : Ioo u b ⊆ s := fun y hy => ⟨by linarith [hy.1], hy.2.le⟩
  have hL : Ioo a u ⊆ s := fun y hy => ⟨hy.1.le, by linarith [hy.2]⟩
  have hgPQ : ∀ y, g y = P y - Q y := fun y => by
    show g y = P y - (P y - g y)
    ring
  have hne1 : (Ioo u b).Nonempty := nonempty_Ioo.mpr hub
  have hne2 : (Ioo a u).Nonempty := nonempty_Ioo.mpr hau
  have hbP1 : BddBelow (P '' Ioo u b) := ⟨P u, by
    rintro _ ⟨y, hy, rfl⟩; exact hP hus (hR hy) hy.1.le⟩
  have hbQ1 : BddBelow (Q '' Ioo u b) := ⟨Q u, by
    rintro _ ⟨y, hy, rfl⟩; exact hQ hus (hR hy) hy.1.le⟩
  have hbP2 : BddAbove (P '' Ioo a u) := ⟨P u, by
    rintro _ ⟨y, hy, rfl⟩; exact hP (hL hy) hus hy.2.le⟩
  have hbQ2 : BddAbove (Q '' Ioo a u) := ⟨Q u, by
    rintro _ ⟨y, hy, rfl⟩; exact hQ (hL hy) hus hy.2.le⟩
  refine ⟨⟨_, ((hP.mono hR).tendsto_nhdsWithin_Ioo_right hne1 hbP1).sub
      ((hQ.mono hR).tendsto_nhdsWithin_Ioo_right hne1 hbQ1) |>.congr fun y => (hgPQ y).symm⟩,
    ⟨_, ((hP.mono hL).tendsto_nhdsWithin_Ioo_left hne2 hbP2).sub
      ((hQ.mono hL).tendsto_nhdsWithin_Ioo_left hne2 hbQ2) |>.congr fun y => (hgPQ y).symm⟩⟩

theorem tendsto_of_re_im {l : Filter ℝ} {f : ℝ → ℂ} {a b : ℝ}
    (hre : Tendsto (fun x => (f x).re) l (𝓝 a)) (him : Tendsto (fun x => (f x).im) l (𝓝 b)) :
    Tendsto f l (𝓝 (a + b * Complex.I)) := by
  have := ((Complex.continuous_ofReal.tendsto a).comp hre).add
    (((Complex.continuous_ofReal.tendsto b).comp him).mul_const Complex.I)
  exact this.congr fun x => by simp [Complex.re_add_im]

/-- A function of bounded variation on a neighborhood of `u` has one-sided limits `f(u±)`. -/
theorem exists_tendsto_of_bv {f : ℝ → ℂ} {a u b : ℝ} (hau : a < u) (hub : u < b)
    (hf : BoundedVariationOn f (Icc a b)) :
    (∃ L, Tendsto f (𝓝[>] u) (𝓝 L)) ∧ ∃ L, Tendsto f (𝓝[<] u) (𝓝 L) := by
  obtain ⟨⟨r1, hr1⟩, ⟨r2, hr2⟩⟩ := exists_tendsto_of_bv_real hau hub
    (Complex.reCLM.lipschitzWith.comp_boundedVariationOn hf)
  obtain ⟨⟨i1, hi1⟩, ⟨i2, hi2⟩⟩ := exists_tendsto_of_bv_real hau hub
    (Complex.imCLM.lipschitzWith.comp_boundedVariationOn hf)
  exact ⟨⟨_, tendsto_of_re_im hr1 hi1⟩, ⟨_, tendsto_of_re_im hr2 hi2⟩⟩

open Complex in
/-- **DLMF (1.14.3)**, with the existence of `f(u±)`: if `f` is absolutely integrable and of
bounded variation near `u`, then `f(u±)` exist and the principal value inverse transform at `u`
is `½(f(u+) + f(u−))`. -/
theorem dlmf_1_14_3' {f : ℝ → ℂ} (hf : Integrable f) {u δ : ℝ} (hδ : 0 < δ)
    (hbv : BoundedVariationOn f (Icc (u - δ) (u + δ))) :
    ∃ Lp Lm, Tendsto f (𝓝[>] u) (𝓝 Lp) ∧ Tendsto f (𝓝[<] u) (𝓝 Lm) ∧
      Tendsto (fun R : ℝ => ((√(2 * Real.pi) : ℝ) : ℂ)⁻¹ *
        ∫ x in (-R)..R, dlmfFourier f x * cexp (-(I * x * u))) atTop (𝓝 ((Lp + Lm) / 2)) := by
  obtain ⟨⟨Lp, hp⟩, ⟨Lm, hm⟩⟩ := exists_tendsto_of_bv (a := u - δ) (u := u) (b := u + δ)
    (by linarith) (by linarith) hbv
  exact ⟨Lp, Lm, hp, hm, dlmf_1_14_3 hf hδ hbv hp hm⟩

end Azurite.DLMF
