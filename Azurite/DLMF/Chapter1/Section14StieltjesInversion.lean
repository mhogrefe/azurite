/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section14Stieltjes
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# DLMF §1.14(vi): inversion of the Stieltjes transform (1.14.49)

* `stieltjesPartial_sub`: `(𝒮f(−σ − iε) − 𝒮f(−σ + iε))/(2πi)` is the Poisson integral
  `∫ f(t) ε/(π((t − σ)² + ε²)) dt` (`poissonK`); `tendsto_poisson_integral`.
* Near `σ`: `integral_poissonK` (arctan), `tendsto_arctan_div`, `abs_integral_near_le`.
* The conditionally convergent tail beyond `σ + δ` is `O(ε)` (`exists_norm_tail_le`): Abel's bound
  for `f/(1 + t)` against the multiplier `tailH = (1 + t)·kernel`, decreasing there for `ε ≤ δ`.
* **`dlmf_1_14_49`**: the limit is `(f(σ+) + f(σ−))/2` at every `σ > 0` where both one-sided
  limits exist.
-/

open Set Filter Topology MeasureTheory Complex
open scoped Real Interval

namespace Azurite.DLMF

/-- The Poisson kernel `ε / (π (u² + ε²))`. -/
noncomputable def poissonK (ε u : ℝ) : ℝ := ε / (π * (u ^ 2 + ε ^ 2))

theorem poissonK_pos {ε : ℝ} (hε : 0 < ε) (u : ℝ) : 0 < poissonK ε u := by
  unfold poissonK; positivity

theorem hasDerivAt_arctan_div {ε : ℝ} (hε : 0 < ε) (σ t : ℝ) :
    HasDerivAt (fun t => Real.arctan ((t - σ) / ε) / π) (poissonK ε (t - σ)) t := by
  have h1 : HasDerivAt (fun t : ℝ => (t - σ) / ε) (1 / ε) t := by
    simpa using ((hasDerivAt_id t).sub_const σ).div_const ε
  convert (h1.arctan).div_const π using 1
  unfold poissonK
  field_simp
  ring

theorem integral_poissonK {ε : ℝ} (hε : 0 < ε) (σ a b : ℝ) :
    ∫ t in a..b, poissonK ε (t - σ) =
      Real.arctan ((b - σ) / ε) / π - Real.arctan ((a - σ) / ε) / π :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_arctan_div hε σ t)
    (Continuous.intervalIntegrable (by
      unfold poissonK; exact continuous_const.div (by fun_prop) fun x => by positivity) _ _)

theorem tendsto_arctan_div {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun ε => Real.arctan (δ / ε) / π) (𝓝[>] 0) (𝓝 (1 / 2)) := by
  have h1 : Tendsto (fun ε : ℝ => δ / ε) (𝓝[>] 0) atTop := by
    simpa [div_eq_mul_inv] using tendsto_inv_nhdsGT_zero.const_mul_atTop hδ
  have h2 := (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp h1
  have := h2.div_const π
  rwa [show π / 2 / π = 1 / 2 by field_simp] at this

/-- The difference of the transforms at `−σ ∓ iε` is the Poisson integral. -/
theorem stieltjesPartial_sub {f : ℝ → ℝ} (hf : ∀ R, IntegrableOn f (Icc 0 R)) {σ ε : ℝ}
    (hε : 0 < ε) {R : ℝ} (hR : 0 ≤ R) :
    (stieltjesPartial f (-σ - ε * I) R - stieltjesPartial f (-σ + ε * I) R) / (2 * π * I) =
      ∫ t in (0 : ℝ)..R, (f t : ℂ) * (poissonK ε (t - σ) : ℂ) := by
  have hs1 : (-σ - ε * I : ℂ) ∈ slitPlane := by
    rw [mem_slitPlane_iff]; right; simp; exact hε.ne'
  have hs2 : (-σ + ε * I : ℂ) ∈ slitPlane := by
    rw [mem_slitPlane_iff]; right; simp; exact hε.ne'
  unfold stieltjesPartial
  rw [← intervalIntegral.integral_sub (by simpa using intervalIntegrable_div_pow hf hs1 1 hR)
    (by simpa using intervalIntegrable_div_pow hf hs2 1 hR), ← intervalIntegral.integral_div]
  refine intervalIntegral.integral_congr fun t _ => ?_
  have h1 : (-σ - ε * I : ℂ) + t ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; exact hε.ne' this
  have h2 : (-σ + ε * I : ℂ) + t ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; exact hε.ne' this
  have h3 : ((t - σ) ^ 2 + ε ^ 2 : ℂ) ≠ 0 := by
    have : 0 < (t - σ) ^ 2 + ε ^ 2 := by positivity
    exact_mod_cast this.ne'
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [poissonK]
  push_cast
  field_simp
  have hI3 : I ^ 3 = -I := by rw [pow_succ, I_sq, neg_one_mul]
  ring_nf
  rw [hI3]
  ring

/-- `H(t) = (1 + t) · ε/(π((t − σ)² + ε²))`, the multiplier turning `f/(1 + t)` into
`f · kernel`. -/
noncomputable def tailH (ε σ t : ℝ) : ℝ := (1 + t) * poissonK ε (t - σ)

/-- Its derivative. -/
noncomputable def tailH' (ε σ t : ℝ) : ℝ :=
  ε / π * (((t - σ) ^ 2 + ε ^ 2 - 2 * (1 + t) * (t - σ)) / ((t - σ) ^ 2 + ε ^ 2) ^ 2)

theorem hasDerivAt_tailH {ε : ℝ} (hε : 0 < ε) (σ t : ℝ) :
    HasDerivAt (tailH ε σ) (tailH' ε σ t) t := by
  have hD : (t - σ) ^ 2 + ε ^ 2 ≠ 0 := by positivity
  have h1 : HasDerivAt (fun t : ℝ => (t - σ) ^ 2 + ε ^ 2) (2 * (t - σ)) t := by
    have := (((hasDerivAt_id t).sub_const σ).mul ((hasDerivAt_id t).sub_const σ)).add_const
      (ε ^ 2)
    convert this using 1
    · funext y; simp only [Pi.mul_apply, id]; ring
    · simp only [id]; ring
  have h2 : HasDerivAt (fun t : ℝ => ε * (π * ((t - σ) ^ 2 + ε ^ 2))⁻¹)
      (ε * (-(π * (2 * (t - σ))) / (π * ((t - σ) ^ 2 + ε ^ 2)) ^ 2)) t :=
    ((h1.const_mul π).inv (by positivity)).const_mul ε
  have h3 := ((hasDerivAt_id t).const_add 1).mul h2
  convert h3 using 1
  · funext y; simp [tailH, poissonK, div_eq_mul_inv]
  · simp only [tailH', id]; field_simp; ring

theorem continuous_tailH' {ε : ℝ} (hε : 0 < ε) (σ : ℝ) : Continuous (tailH' ε σ) := by
  unfold tailH'
  exact continuous_const.mul (Continuous.div (by fun_prop) (by fun_prop) fun t => by positivity)

theorem tailH'_nonpos {ε σ δ t : ℝ} (hε : 0 < ε) (hεδ : ε ≤ δ) (hσ : 0 < σ) (ht : σ + δ ≤ t) :
    tailH' ε σ t ≤ 0 := by
  unfold tailH'
  refine mul_nonpos_of_nonneg_of_nonpos (by positivity) (div_nonpos_of_nonpos_of_nonneg ?_
    (by positivity))
  nlinarith

/-- **The tail beyond `σ + δ`** is `O(ε)` (Abel's bound with the decreasing multiplier `H`). -/
theorem exists_norm_tail_le {f : ℝ → ℝ} (hf : ∀ R, IntegrableOn f (Icc 0 R)) {s₀ : ℂ}
    (hs₀ : s₀ ∈ slitPlane) (hconv : StieltjesConverges f s₀) {σ δ : ℝ} (hσ : 0 < σ)
    (hδ : 0 < δ) : ∃ C, ∀ ε, 0 < ε → ε ≤ δ → ∀ R, σ + δ ≤ R →
      ‖∫ t in (σ + δ)..R, (f t : ℂ) * (poissonK ε (t - σ) : ℂ)‖ ≤ C * ε := by
  have h1 : (1 : ℂ) ∈ slitPlane := by rw [mem_slitPlane_iff]; left; norm_num
  set g : ℝ → ℂ := fun t => (f t : ℂ) / (1 + t) with hg
  have hgI : ∀ R, 0 ≤ R → IntervalIntegrable g volume 0 R := fun R hR => by
    simpa [hg] using intervalIntegrable_div_pow hf h1 1 hR
  have hL : Tendsto (fun R => ∫ t in (0 : ℝ)..R, g t) atTop (𝓝 (stieltjes f 1)) :=
    tendsto_stieltjesPartial hf hs₀ hconv h1
  obtain ⟨B, hB⟩ := exists_bound_of_tendsto_integral hgI hL
  refine ⟨2 * B * ((1 + σ + δ) / (π * δ ^ 2)), fun ε hε hεδ R hR => ?_⟩
  set A := σ + δ
  have hA0 : 0 ≤ A := by positivity
  have e1 : ∫ t in A..R, (f t : ℂ) * (poissonK ε (t - σ) : ℂ) =
      ∫ t in A..R, g t * (tailH ε σ t : ℂ) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hR] at ht
    have hne : (1 + (t : ℂ)) ≠ 0 := by
      have : (0 : ℝ) < 1 + t := by linarith [ht.1]
      exact_mod_cast this.ne'
    simp only [hg, tailH]; push_cast; field_simp
  rw [e1]
  have hAbel := norm_integral_mul_le_abel hR ((hgI A hA0).symm.trans (hgI R (hA0.trans hR)))
    (h := fun t => (tailH ε σ t : ℂ)) (h' := fun t => (tailH' ε σ t : ℂ))
    (fun t _ => (hasDerivAt_tailH hε σ t).ofReal_comp)
    (continuous_ofReal.comp (continuous_tailH' hε σ)).continuousOn
    (B := 2 * B) (fun u hu => by
      rw [← intervalIntegral.integral_interval_sub_left (hgI u (hA0.trans hu.1)) (hgI A hA0)]
      have := norm_sub_le (∫ t in (0 : ℝ)..u, g t) (∫ t in (0 : ℝ)..A, g t)
      linarith [hB u (hA0.trans hu.1), hB A hA0])
  have hHnn : ∀ t, 0 ≤ tailH ε σ t → ‖(tailH ε σ t : ℂ)‖ = tailH ε σ t := fun t h => by
    rw [Complex.norm_real, Real.norm_of_nonneg h]
  have hHR : 0 ≤ tailH ε σ R := by
    unfold tailH; exact mul_nonneg (by linarith) (poissonK_pos hε _).le
  have hint : ∫ t in A..R, ‖(tailH' ε σ t : ℂ)‖ = tailH ε σ A - tailH ε σ R := by
    rw [intervalIntegral.integral_congr (g := fun t => -tailH' ε σ t) fun t ht => by
      rw [uIcc_of_le hR] at ht
      simp only
      rw [Complex.norm_real, Real.norm_of_nonpos (tailH'_nonpos hε hεδ hσ ht.1)] ]
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hasDerivAt_tailH hε σ t) ((continuous_tailH' hε σ).intervalIntegrable _ _)]
    ring
  rw [hHnn R hHR, hint] at hAbel
  have hHA : tailH ε σ A ≤ (1 + σ + δ) / (π * δ ^ 2) * ε := by
    unfold tailH poissonK
    simp only [A, add_sub_cancel_left]
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    have e : (1 + σ + δ) / (π * δ ^ 2) * ε * (π * (δ ^ 2 + ε ^ 2)) =
        (1 + σ + δ) * ε * ((δ ^ 2 + ε ^ 2) / δ ^ 2) := by field_simp
    have hq : 1 ≤ (δ ^ 2 + ε ^ 2) / δ ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; nlinarith [sq_nonneg ε]
    rw [e]
    have : 0 ≤ (1 + σ + δ) * ε := by positivity
    nlinarith
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 le_rfl)
  calc _ ≤ 2 * B * (tailH ε σ R + (tailH ε σ A - tailH ε σ R)) := hAbel
    _ = 2 * B * tailH ε σ A := by ring
    _ ≤ 2 * B * ((1 + σ + δ) / (π * δ ^ 2) * ε) := mul_le_mul_of_nonneg_left hHA (by positivity)
    _ = _ := by ring

theorem continuous_poissonK {ε : ℝ} (hε : 0 < ε) (σ : ℝ) :
    Continuous fun t => poissonK ε (t - σ) := by
  unfold poissonK; exact continuous_const.div (by fun_prop) fun x => by positivity

theorem arctan_div_lt_one {x : ℝ} : Real.arctan x / π < 1 := by
  rw [div_lt_one Real.pi_pos]; linarith [Real.arctan_lt_pi_div_two x, Real.pi_pos]

theorem arctan_div_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.arctan x / π :=
  div_nonneg (Real.arctan_nonneg.mpr hx) Real.pi_pos.le

/-- **The part near `σ`**: within `η` of the one-sided limits on `(σ − δ, σ)` and `(σ, σ + δ]`. -/
theorem abs_integral_near_le {f : ℝ → ℝ} (hf : ∀ R, IntegrableOn f (Icc 0 R)) {σ δ ε a b η : ℝ}
    (hδ : 0 < δ) (hδσ : δ < σ) (hε : 0 < ε) (hfa : ∀ t ∈ Ioc σ (σ + δ), |f t - a| ≤ η)
    (hfb : ∀ t ∈ Ioo (σ - δ) σ, |f t - b| ≤ η) :
    |(∫ t in (0 : ℝ)..σ + δ, f t * poissonK ε (t - σ)) - (a + b) / 2| ≤
      2 * η + |a + b| * |Real.arctan (δ / ε) / π - 1 / 2| +
        ε / (π * δ ^ 2) * ∫ t in (0 : ℝ)..σ - δ, |f t| := by
  have hη : 0 ≤ η := (abs_nonneg _).trans (hfa (σ + δ) ⟨by linarith, le_rfl⟩)
  set k : ℝ → ℝ := fun t => poissonK ε (t - σ) with hk
  have hkc : Continuous k := continuous_poissonK hε σ
  have hfI : IntervalIntegrable f volume 0 (σ + δ) :=
    intervalIntegrable_of_integrableOn hf (by linarith)
  have hI : ∀ x y, x ∈ Icc 0 (σ + δ) → y ∈ Icc 0 (σ + δ) →
      IntervalIntegrable (fun t => f t * k t) volume x y := fun x y hx hy =>
    (hfI.mul_continuousOn hkc.continuousOn).mono_set (uIcc_subset_uIcc (by
      rw [uIcc_of_le (by linarith)]; exact hx) (by rw [uIcc_of_le (by linarith)]; exact hy))
  have m0 : (0 : ℝ) ∈ Icc 0 (σ + δ) := ⟨le_rfl, by linarith⟩
  have m1 : σ - δ ∈ Icc 0 (σ + δ) := ⟨by linarith, by linarith⟩
  have m2 : σ ∈ Icc 0 (σ + δ) := ⟨by linarith, by linarith⟩
  have m3 : σ + δ ∈ Icc 0 (σ + δ) := ⟨by linarith, le_rfl⟩
  have hsplit : ∫ t in (0 : ℝ)..σ + δ, f t * k t = (∫ t in (0 : ℝ)..σ - δ, f t * k t) +
      (∫ t in σ - δ..σ, f t * k t) + ∫ t in σ..σ + δ, f t * k t := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hI _ _ m0 m1) (hI _ _ m1 m2),
      intervalIntegral.integral_add_adjacent_intervals (hI _ _ m0 m2) (hI _ _ m2 m3)]
  have hq : ∫ t in σ..σ + δ, k t = Real.arctan (δ / ε) / π := by
    rw [hk, integral_poissonK hε]; simp
  have hq' : ∫ t in σ - δ..σ, k t = Real.arctan (δ / ε) / π := by
    rw [hk, integral_poissonK hε]
    simp [neg_div, Real.arctan_neg]
  have hkI : ∀ x y, IntervalIntegrable k volume x y := fun x y => hkc.intervalIntegrable x y
  -- the piece near `σ` on the right
  have hXa : |(∫ t in σ..σ + δ, f t * k t) - a * Real.arctan (δ / ε) / π| ≤ η := by
    have e : (∫ t in σ..σ + δ, f t * k t) - a * Real.arctan (δ / ε) / π =
        ∫ t in σ..σ + δ, (f t - a) * k t := by
      simp_rw [sub_mul]
      rw [intervalIntegral.integral_sub (hI _ _ m2 m3) ((hkI _ _).const_mul a),
        intervalIntegral.integral_const_mul, hq, mul_div_assoc]
    rw [e, ← Real.norm_eq_abs]
    calc ‖∫ t in σ..σ + δ, (f t - a) * k t‖ ≤ ∫ t in σ..σ + δ, η * k t :=
          intervalIntegral.norm_integral_le_of_norm_le (by linarith) (ae_of_all _ fun t ht => by
            rw [Real.norm_eq_abs, abs_mul, abs_of_pos (poissonK_pos hε _)]
            exact mul_le_mul_of_nonneg_right (hfa t ht) (poissonK_pos hε _).le)
            ((hkI _ _).const_mul η)
      _ = η * (Real.arctan (δ / ε) / π) := by rw [intervalIntegral.integral_const_mul, hq]
      _ ≤ η * 1 := mul_le_mul_of_nonneg_left arctan_div_lt_one.le hη
      _ = η := mul_one η
  -- the piece near `σ` on the left (the point `σ` itself is null)
  have hXb : |(∫ t in σ - δ..σ, f t * k t) - b * Real.arctan (δ / ε) / π| ≤ η := by
    have e : (∫ t in σ - δ..σ, f t * k t) - b * Real.arctan (δ / ε) / π =
        ∫ t in σ - δ..σ, (f t - b) * k t := by
      simp_rw [sub_mul]
      rw [intervalIntegral.integral_sub (hI _ _ m1 m2) ((hkI _ _).const_mul b),
        intervalIntegral.integral_const_mul, hq', mul_div_assoc]
    rw [e, ← Real.norm_eq_abs]
    calc ‖∫ t in σ - δ..σ, (f t - b) * k t‖ ≤ ∫ t in σ - δ..σ, η * k t := by
          refine intervalIntegral.norm_integral_le_of_norm_le (by linarith) ?_
            ((hkI _ _).const_mul η)
          filter_upwards [Measure.ae_ne volume σ] with t hne ht
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (poissonK_pos hε _)]
          exact mul_le_mul_of_nonneg_right (hfb t ⟨ht.1, lt_of_le_of_ne ht.2 hne⟩)
            (poissonK_pos hε _).le
      _ = η * (Real.arctan (δ / ε) / π) := by rw [intervalIntegral.integral_const_mul, hq']
      _ ≤ η * 1 := mul_le_mul_of_nonneg_left arctan_div_lt_one.le hη
      _ = η := mul_one η
  -- the part away from `σ` on the left
  have hX0 : |∫ t in (0 : ℝ)..σ - δ, f t * k t| ≤
      ε / (π * δ ^ 2) * ∫ t in (0 : ℝ)..σ - δ, |f t| := by
    rw [← Real.norm_eq_abs, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.norm_integral_le_of_norm_le (by linarith) (ae_of_all _ fun t ht => ?_)
      ((intervalIntegrable_of_integrableOn hf (by linarith)).abs.const_mul _)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (poissonK_pos hε _), mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    simp only [poissonK]
    have hsq : δ ^ 2 ≤ (t - σ) ^ 2 + ε ^ 2 := by nlinarith [ht.2, sq_nonneg ε]
    exact div_le_div_of_nonneg_left hε.le (by positivity) (by nlinarith [Real.pi_pos])
  rw [hsplit]
  have e2 : (∫ t in (0 : ℝ)..σ - δ, f t * k t) + (∫ t in σ - δ..σ, f t * k t) +
      (∫ t in σ..σ + δ, f t * k t) - (a + b) / 2 =
      (∫ t in (0 : ℝ)..σ - δ, f t * k t) +
      ((∫ t in σ - δ..σ, f t * k t) - b * Real.arctan (δ / ε) / π) +
      ((∫ t in σ..σ + δ, f t * k t) - a * Real.arctan (δ / ε) / π) +
      (a + b) * (Real.arctan (δ / ε) / π - 1 / 2) := by ring
  rw [e2]
  calc _ ≤ |∫ t in (0 : ℝ)..σ - δ, f t * k t| +
        |(∫ t in σ - δ..σ, f t * k t) - b * Real.arctan (δ / ε) / π| +
        |(∫ t in σ..σ + δ, f t * k t) - a * Real.arctan (δ / ε) / π| +
        |(a + b) * (Real.arctan (δ / ε) / π - 1 / 2)| := by
        exact (abs_add_le _ _).trans (add_le_add (abs_add_three _ _ _) le_rfl)
    _ ≤ _ := by rw [abs_mul]; linarith

/-- The difference quotient of (1.14.49) as an improper Poisson integral. -/
theorem tendsto_poisson_integral {f : ℝ → ℝ} (hf : ∀ R, IntegrableOn f (Icc 0 R)) {s₀ : ℂ}
    (hs₀ : s₀ ∈ slitPlane) (hconv : StieltjesConverges f s₀) {σ ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun R => ∫ t in (0 : ℝ)..R, (f t : ℂ) * (poissonK ε (t - σ) : ℂ)) atTop
      (𝓝 ((stieltjes f (-σ - ε * I) - stieltjes f (-σ + ε * I)) / (2 * π * I))) := by
  have hs1 : (-σ - ε * I : ℂ) ∈ slitPlane := by
    rw [mem_slitPlane_iff]; right; simp; exact hε.ne'
  have hs2 : (-σ + ε * I : ℂ) ∈ slitPlane := by
    rw [mem_slitPlane_iff]; right; simp; exact hε.ne'
  have h := ((tendsto_stieltjesPartial hf hs₀ hconv hs1).sub
    (tendsto_stieltjesPartial hf hs₀ hconv hs2)).div_const (2 * π * I)
  refine h.congr' ((eventually_ge_atTop 0).mono fun R hR => ?_)
  exact stieltjesPartial_sub hf hε hR

/-- **DLMF 1.14.49** (inversion of the Stieltjes transform): if `f` is absolutely integrable on
every `[0, R]` and (1.14.47) converges, then
`lim_{ε→0+} (𝒮f(−σ − iε) − 𝒮f(−σ + iε))/(2πi) = (f(σ+) + f(σ−))/2` at every `σ > 0` where the
one-sided limits `f(σ±)` exist. -/
theorem dlmf_1_14_49 {f : ℝ → ℝ} (hf : ∀ R, IntegrableOn f (Icc 0 R)) {s₀ : ℂ}
    (hs₀ : s₀ ∈ slitPlane) (hconv : StieltjesConverges f s₀) {σ : ℝ} (hσ : 0 < σ) {a b : ℝ}
    (ha : Tendsto f (𝓝[>] σ) (𝓝 a)) (hb : Tendsto f (𝓝[<] σ) (𝓝 b)) :
    Tendsto (fun ε : ℝ => (stieltjes f (-σ - ε * I) - stieltjes f (-σ + ε * I)) / (2 * π * I))
      (𝓝[>] 0) (𝓝 (((a + b) / 2 : ℝ) : ℂ)) := by
  rw [Metric.tendsto_nhds]
  intro η' hη'
  set η := η' / 6
  have hη : 0 < η := by positivity
  obtain ⟨δa, hδa, hfa⟩ := Metric.tendsto_nhdsWithin_nhds.mp ha η hη
  obtain ⟨δb, hδb, hfb⟩ := Metric.tendsto_nhdsWithin_nhds.mp hb η hη
  set δ := min (min δa δb) σ / 2
  have hδ : 0 < δ := by positivity
  have hδa' : δ < δa := by
    have := min_le_left (min δa δb) σ; have := min_le_left δa δb; simp only [δ]; linarith
  have hδb' : δ < δb := by
    have := min_le_left (min δa δb) σ; have := min_le_right δa δb; simp only [δ]; linarith
  have hδσ : δ < σ := by have := min_le_right (min δa δb) σ; simp only [δ]; linarith
  have hfa' : ∀ t ∈ Ioc σ (σ + δ), |f t - a| ≤ η := fun t ht => by
    have := hfa (x := t) ht.1 (by
      rw [Real.dist_eq, abs_of_pos (by linarith [ht.1])]; linarith [ht.2])
    rw [Real.dist_eq] at this; exact this.le
  have hfb' : ∀ t ∈ Ioo (σ - δ) σ, |f t - b| ≤ η := fun t ht => by
    have := hfb (x := t) ht.2 (by
      rw [Real.dist_eq, abs_of_neg (by linarith [ht.2])]; linarith [ht.1])
    rw [Real.dist_eq] at this; exact this.le
  obtain ⟨C, hC⟩ := exists_norm_tail_le hf hs₀ hconv hσ hδ
  set I₀ := ∫ t in (0 : ℝ)..σ - δ, |f t|
  -- the three error terms tend to `0`
  have t1 : Tendsto (fun ε : ℝ => C * ε) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((continuous_const_mul C).tendsto 0).mono_left nhdsWithin_le_nhds
  have t2 : Tendsto (fun ε : ℝ => ε / (π * δ ^ 2) * I₀) (𝓝[>] 0) (𝓝 0) := by
    have : Continuous fun ε : ℝ => ε / (π * δ ^ 2) * I₀ := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have t3 : Tendsto (fun ε : ℝ => |a + b| * |Real.arctan (δ / ε) / π - 1 / 2|) (𝓝[>] 0)
      (𝓝 0) := by
    have := (((tendsto_arctan_div hδ).sub_const (1 / 2)).abs).const_mul |a + b|
    simpa using this
  filter_upwards [self_mem_nhdsWithin, Ioc_mem_nhdsGT hδ, t1.eventually (gt_mem_nhds hη),
    t2.eventually (gt_mem_nhds hη), t3.eventually (gt_mem_nhds hη)] with ε hε0 hεδ h1 h2 h3
  have hε : 0 < ε := hε0
  set A := σ + δ
  set E : ℝ := ∫ t in (0 : ℝ)..A, f t * poissonK ε (t - σ)
  have hfk : ∀ R, 0 ≤ R → IntervalIntegrable (fun t => (f t : ℂ) * (poissonK ε (t - σ) : ℂ))
      volume 0 R := fun R hR =>
    intervalIntegrable_mul_of_continuousOn hf hR
      (continuous_ofReal.comp (continuous_poissonK hε σ)).continuousOn
  have hA0 : 0 ≤ A := by positivity
  -- the tail estimate passes to the limit
  have htail : ‖(stieltjes f (-σ - ε * I) - stieltjes f (-σ + ε * I)) / (2 * π * I) - E‖ ≤
      C * ε := by
    have hE : (E : ℂ) = ∫ t in (0 : ℝ)..A, (f t : ℂ) * (poissonK ε (t - σ) : ℂ) := by
      simp only [E]; rw [← intervalIntegral.integral_ofReal]; push_cast; rfl
    rw [hE]
    refine le_of_tendsto ((tendsto_poisson_integral hf hs₀ hconv hε).sub_const _).norm ?_
    filter_upwards [eventually_ge_atTop A] with R hR
    rw [intervalIntegral.integral_interval_sub_left (hfk R (hA0.trans hR)) (hfk A hA0)]
    exact hC ε hε hεδ.2 R hR
  have hnear := abs_integral_near_le hf hδ hδσ hε hfa' hfb'
  rw [dist_eq_norm]
  calc ‖(stieltjes f (-σ - ε * I) - stieltjes f (-σ + ε * I)) / (2 * π * I) -
        (((a + b) / 2 : ℝ) : ℂ)‖
      ≤ ‖(stieltjes f (-σ - ε * I) - stieltjes f (-σ + ε * I)) / (2 * π * I) - E‖ +
        ‖(E : ℂ) - (((a + b) / 2 : ℝ) : ℂ)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ C * ε + |E - (a + b) / 2| := by
        rw [← ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; exact add_le_add htail le_rfl
    _ ≤ C * ε + (2 * η + |a + b| * |Real.arctan (δ / ε) / π - 1 / 2| +
        ε / (π * δ ^ 2) * I₀) := add_le_add le_rfl hnear
    _ < η' := by simp only [η] at h1 h2 h3 ⊢; linarith

end Azurite.DLMF
