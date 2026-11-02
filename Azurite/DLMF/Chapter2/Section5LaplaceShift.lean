/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section5Laplace

/-!
# DLMF §2.5(iii), 2.5.41: the first contour shift

`I₁(x) = (2πi)⁻¹ ∫_{p₁} x^{−z} Γ(1 − z) 𝓜h₁(z) dz` (2.5.40) with `−c < p₁ < 1`. Since `𝓜h₁(z)` is
analytic for `ℜz > −c`, the contour can be moved to `ℜz = ρ`, `1 < ρ < 2`, across the simple pole
of `Γ(1 − z)` at `z = 1`:

`I₁(x) = 𝓜h₁(1) x^{−1} + (2πi)⁻¹ ∫_{ρ−i∞}^{ρ+i∞} x^{−z} Γ(1 − z) 𝓜h₁(z) dz` (`dlmf_2_5_41`).

The ingredients, all reused for 2.5.42–2.5.44:

* the residue of `A(z)/(z − n) + g(z)` at `n` is `A(n)` (`residue_eq_of_eq_div_add`);
* the Laurent data of `Γ` at `−m`: `Γ(w) = GammaNum m w / (w + m)` with
  `GammaNum m w = Γ(w + m + 1)/∏_{j<m}(w + j)` analytic near `−m` and
  `GammaNum m (−m) = (−1)^m/m!`;
* `|Γ(σ + iy)| ≤ M/|y|^k` uniformly for `σ` in a compact interval (`exists_Gamma_strip_bound`),
  which is DLMF's appeal to 2.5.14;
* `|𝓜h₁(z)| ≤ ∫₀¹ t^{a−1}|h(t)| dt` for `ℜz ≥ a > −c` (`norm_mellin_trunc₁_le`).
-/

open MeasureTheory Filter Topology Set Complex Metric Asymptotics
open scoped Real Nat

namespace Azurite.DLMF

/-! ### Residues of simple poles -/

/-- If `F(z) = A(z)/(z − n) + g(z)` on a punctured disc about `n` with `A`, `g` analytic on the
disc, then `res_{z=n} F = A(n)`. -/
theorem residue_eq_of_eq_div_add {F A g : ℂ → ℂ} {n : ℂ} {R : ℝ} (hR : 0 < R)
    (hA : DifferentiableOn ℂ A (ball n R)) (hg : DifferentiableOn ℂ g (ball n R))
    (hF : ∀ z ∈ annulus n 0 R, F z = A z / (z - n) + g z) : residue F n R = A n := by
  have hr : R / 2 ∈ Ioo 0 R := ⟨by positivity, by linarith⟩
  have hball : closedBall n (R / 2) ⊆ ball n R := closedBall_subset_ball (by linarith)
  have hFd : DifferentiableOn ℂ F (annulus n 0 R) := by
    intro z hz
    have hz0 : z - n ≠ 0 := norm_pos_iff.mp hz.1
    have hzb : z ∈ ball n R := by rw [mem_ball, dist_eq_norm]; exact hz.2
    have hd : DifferentiableAt ℂ (fun w => A w / (w - n) + g w) z :=
      ((hA.differentiableAt (isOpen_ball.mem_nhds hzb)).div (differentiableAt_id.sub_const n)
        hz0).add (hg.differentiableAt (isOpen_ball.mem_nhds hzb))
    refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [(isOpen_annulus n 0 R).mem_nhds hz] with w hw
    exact hF w hw
  rw [residue_eq hFd hr]
  have hsph : ∀ z ∈ sphere n (R / 2), z - n ≠ 0 := fun z hz => by
    rw [mem_sphere, dist_eq_norm] at hz
    exact norm_pos_iff.mp (by rw [hz]; exact hr.1)
  have hcongr : ∀ z ∈ sphere n (R / 2), F z = (z - n)⁻¹ • A z + g z := fun z hz => by
    have hzA : z ∈ annulus n 0 R := by
      rw [mem_sphere, dist_eq_norm] at hz
      exact ⟨by rw [hz]; exact hr.1, by rw [hz]; exact hr.2⟩
    rw [hF z hzA, smul_eq_mul, div_eq_inv_mul]
  have hsub : sphere n (R / 2) ⊆ ball n R := sphere_subset_closedBall.trans hball
  have hAc : ContinuousOn A (sphere n (R / 2)) := (hA.mono hsub).continuousOn
  have hgc : ContinuousOn g (sphere n (R / 2)) := (hg.mono hsub).continuousOn
  have hsubc : ContinuousOn (fun z : ℂ => (z - n)⁻¹) (sphere n (R / 2)) :=
    (continuous_id.sub continuous_const).continuousOn.inv₀ hsph
  have hc1 : ContinuousOn (fun z : ℂ => (z - n)⁻¹ • A z) (sphere n (R / 2)) := hsubc.smul hAc
  have i1 : CircleIntegrable (fun z => (z - n)⁻¹ • A z) n (R / 2) :=
    ContinuousOn.circleIntegrable hr.1.le hc1
  have i2 : CircleIntegrable g n (R / 2) := ContinuousOn.circleIntegrable hr.1.le hgc
  have e3 : (∮ z in C(n, R / 2), g z) = 0 :=
    circleIntegral_eq_zero_of_differentiable_on_off_countable hr.1.le countable_empty
      (hg.mono hball).continuousOn fun z hz =>
        hg.differentiableAt (isOpen_ball.mem_nhds (hball (ball_subset_closedBall hz.1)))
  rw [circleIntegral.integral_congr hr.1.le hcongr, circleIntegral.integral_add i1 i2,
    (hA.mono hball).circleIntegral_sub_inv_smul (mem_ball_self hr.1), e3, add_zero, smul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ (by simp [Real.pi_ne_zero] : (2 * π * I : ℂ) ≠ 0), one_mul]

/-! ### The Laurent data of `Γ` at `−m` -/

/-- `Γ(w + m + 1) / ∏_{j<m} (w + j)`: the analytic factor in `Γ(w) = GammaNum m w / (w + m)`. -/
noncomputable def GammaNum (m : ℕ) (w : ℂ) : ℂ :=
  Gamma (w + m + 1) / ∏ j ∈ Finset.range m, (w + j)

theorem Gamma_eq_GammaNum_div {m : ℕ} {w : ℂ} (hw : ∀ j ≤ m, w + j ≠ 0) :
    Gamma w = GammaNum m w / (w + m) := by
  have := Gamma_add_nat_eq_prod_mul w (m + 1) fun j hj => hw j (Nat.lt_succ_iff.mp hj)
  rw [Finset.prod_range_succ, show w + ((m + 1 : ℕ) : ℂ) = w + m + 1 by push_cast; ring] at this
  have hP : (∏ j ∈ Finset.range m, (w + j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j hj => hw j (Finset.mem_range.mp hj).le
  have hm : w + m ≠ 0 := hw m le_rfl
  rw [GammaNum, eq_div_iff hm, eq_div_iff hP, this]
  ring

theorem prod_range_cast_sub (m : ℕ) : ∏ j ∈ Finset.range m, ((m : ℂ) - j) = m ! := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ', Nat.factorial_succ]
    push_cast
    rw [← ih]
    simp only [add_sub_add_right_eq_sub, sub_zero]
    ring

/-- `GammaNum m (−m) = (−1)^m / m!`: the residue of `Γ` at `−m`. -/
theorem GammaNum_neg_nat (m : ℕ) : GammaNum m (-(m : ℂ)) = (-1) ^ m / m ! := by
  have hprod : ∏ j ∈ Finset.range m, (-(m : ℂ) + j) = (-1) ^ m * m ! := by
    calc ∏ j ∈ Finset.range m, (-(m : ℂ) + j) = ∏ j ∈ Finset.range m, ((-1) * ((m : ℂ) - j)) :=
          Finset.prod_congr rfl fun j _ => by ring
      _ = (∏ _j ∈ Finset.range m, (-1 : ℂ)) * ∏ j ∈ Finset.range m, ((m : ℂ) - j) :=
          Finset.prod_mul_distrib
      _ = (-1) ^ m * m ! := by rw [Finset.prod_const, Finset.card_range, prod_range_cast_sub]
  simp only [GammaNum, hprod]
  rw [show -(m : ℂ) + m + 1 = 1 by ring, Gamma_one]
  have hm : (m ! : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have h1 : ((-1 : ℂ) ^ m) ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
  rw [← pow_mul, mul_comm, pow_mul]
  simp

theorem differentiable_prod_range_add (m : ℕ) :
    Differentiable ℂ fun w : ℂ => ∏ j ∈ Finset.range m, (w + (j : ℂ)) := by
  induction m with
  | zero => simp [differentiable_const]
  | succ m ih =>
    simp only [Finset.prod_range_succ]
    exact ih.mul (differentiable_id.add_const _)

theorem differentiableOn_GammaNum (m : ℕ) :
    DifferentiableOn ℂ (GammaNum m) (ball (-(m : ℂ)) 1) := by
  intro w hw
  rw [mem_ball, dist_eq_norm] at hw
  have hre : -1 < w.re + m := by
    have h1 := (abs_le.mp (abs_re_le_norm (w + m))).1
    rw [show w - -(m : ℂ) = w + m by ring] at hw
    simp only [add_re, natCast_re] at h1
    linarith
  refine DifferentiableAt.differentiableWithinAt (DifferentiableAt.div ?_ ?_ ?_)
  · refine (differentiableAt_Gamma _ fun n h => ?_).comp w
      ((differentiableAt_id.add_const _).add_const _)
    have := congrArg Complex.re h
    simp at this
    linarith [n.cast_nonneg (α := ℝ)]
  · exact (differentiable_prod_range_add m).differentiableAt
  · refine Finset.prod_ne_zero_iff.mpr fun j hj h => ?_
    have hj : j < m := Finset.mem_range.mp hj
    rw [show w - -(m : ℂ) = (w + j) + ((m - j : ℕ) : ℂ) by
      rw [Nat.cast_sub hj.le]; ring, h, zero_add, Complex.norm_natCast] at hw
    have : (1 : ℝ) ≤ ((m - j : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
    linarith

/-- `−Γ(1 − z) = GammaNum m (1 − z) / (z − (m + 1))` away from the poles `1, 2, …, m + 1`. -/
theorem neg_Gamma_one_sub_eq {m : ℕ} {z : ℂ} (hz : ∀ j ≤ m, (1 - z) + j ≠ 0) :
    -Gamma (1 - z) = GammaNum m (1 - z) / (z - (m + 1)) := by
  rw [Gamma_eq_GammaNum_div hz, ← div_neg]
  congr 1
  ring

/-! ### Uniform bounds on strips -/

/-- `|Γ(σ + iy)| ≤ M/|y|^k` uniformly for `σ ∈ [a, b]`, whenever `a + k > 0`. -/
theorem exists_Gamma_strip_bound {a b : ℝ} (k : ℕ) (hk : 0 < a + k) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ σ ∈ Icc a b, ∀ y : ℝ, y ≠ 0 → ‖Gamma (σ + y * I)‖ ≤ M / |y| ^ k := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := a + k) (b := b + k)).exists_bound_of_continuousOn
    (continuousOn_of_forall_continuousAt fun u hu =>
      (Real.differentiableAt_Gamma fun n h => by
        linarith [hu.1, n.cast_nonneg (α := ℝ)]).continuousAt)
  refine ⟨|M|, abs_nonneg _, fun σ hσ y hy => ?_⟩
  have hb := norm_Gamma_le_div_pow_im (s := σ + y * I) (k := k) (by simp; linarith [hσ.1])
    (by simpa using hy)
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero, add_im, mul_im, zero_add] at hb
  refine hb.trans (div_le_div_of_nonneg_right ?_ (by positivity))
  have := hM (σ + k) ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  rw [Real.norm_eq_abs] at this
  exact (le_abs_self _).trans (this.trans (le_abs_self M))

/-- A statement holding for all `|y| ≥ Y` holds eventually in `cocompact ℝ`. -/
theorem eventually_cocompact_of_abs_ge {P : ℝ → Prop} (Y : ℝ) (h : ∀ y : ℝ, Y ≤ |y| → P y) :
    ∀ᶠ y in cocompact ℝ, P y := by
  rw [cocompact_eq_atBot_atTop, eventually_sup]
  refine ⟨eventually_atBot.mpr ⟨-Y, fun y hy => h y ?_⟩,
    eventually_atTop.mpr ⟨Y, fun y hy => h y ?_⟩⟩
  · exact le_trans (by linarith) (neg_le_abs y)
  · exact hy.trans (le_abs_self y)

/-- `|𝓜h₁(z)| ≤ ∫₀¹ t^{a−1} |h(t)| dt` for `ℜz ≥ a > −c`. -/
theorem norm_mellin_trunc₁_le {h : ℝ → ℂ} (hloc : LocallyIntegrableOn h (Ioi 0)) {c : ℝ}
    (hzero : h =O[𝓝[>] 0] (· ^ c)) {a : ℝ} (ha : -c < a) {z : ℂ} (hz : a ≤ z.re) :
    ‖mellin (trunc₁ h) z‖ ≤ ∫ t in Ioi (0 : ℝ), t ^ (a - 1) * ‖trunc₁ h t‖ := by
  have hconv : MellinConvergent (trunc₁ h) a := mellinConvergent_trunc₁ hloc hzero (by simpa)
  have hint : IntegrableOn (fun t : ℝ => t ^ (a - 1) * ‖trunc₁ h t‖) (Ioi 0) := by
    refine IntegrableOn.congr_fun hconv.norm (fun t ht => ?_) measurableSet_Ioi
    have ht : (0 : ℝ) < t := ht
    simp [norm_cpow_eq_rpow_re_of_pos ht]
  refine norm_integral_le_of_norm_le hint ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht : (0 : ℝ) < t := ht
  rw [norm_smul, norm_cpow_eq_rpow_re_of_pos ht, sub_re, one_re]
  rcases le_or_gt t 1 with h1 | h1
  · exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge ht h1 (by linarith))
      (norm_nonneg _)
  · simp [trunc₁_apply_of_one_lt h1]

/-- The bound of `norm_mellin_trunc₁_le` as a single constant. -/
theorem exists_norm_mellin_trunc₁_le {h : ℝ → ℂ} (hloc : LocallyIntegrableOn h (Ioi 0)) {c : ℝ}
    (hzero : h =O[𝓝[>] 0] (· ^ c)) {a : ℝ} (ha : -c < a) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, a ≤ z.re → ‖mellin (trunc₁ h) z‖ ≤ M :=
  ⟨_, setIntegral_nonneg measurableSet_Ioi fun _ ht =>
    mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (norm_nonneg _),
    fun _ hz => norm_mellin_trunc₁_le hloc hzero ha hz⟩

/-! ### 2.5.41 -/

namespace LaplaceSmallSetup

variable {h : ℝ → ℂ} {bs β : ℕ → ℂ} {κ p c : ℝ} (H : LaplaceSmallSetup h bs β κ p c)
include H

/-- `Γ(1 − z) 𝓜h₁(z)` is analytic on `−c < ℜz < 2` except at `z = 1`. -/
theorem differentiableOn_Gamma_mul_h₁ :
    DifferentiableOn ℂ (fun z => Gamma (1 - z) * mellin (trunc₁ h) z)
      ({z : ℂ | -c < z.re ∧ z.re < 2} \ ↑({1} : Finset ℂ)) := by
  intro z hz
  obtain ⟨⟨h1, h2⟩, h3⟩ := hz
  have h3 : z ≠ 1 := by simpa using h3
  refine DifferentiableAt.differentiableWithinAt
    (DifferentiableAt.mul ?_ (H.differentiableAt_h₁ h1))
  refine (differentiableAt_Gamma _ fun n hn => ?_).comp z
    ((differentiableAt_const _).sub differentiableAt_id)
  have hre := congrArg Complex.re hn
  simp at hre
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0
    simp at hn
    exact h3 (by linear_combination -hn)
  · have : (1 : ℝ) ≤ n := by exact_mod_cast h0
    linarith

/-- **DLMF 2.5.34** for `Γ(1 − z) 𝓜h₁(z)` on the strip `p₁ ≤ ℜz ≤ ρ` (`−c < p₁`, `ρ < 2`): the
supremum over the strip tends to `0` as `y → ±∞`. -/
theorem sup_Gamma_mul_h₁_tendsto {p₁ ρ : ℝ} (hp₁ : -c < p₁) (hρ : ρ < 2) :
    ∀ ε > 0, ∀ᶠ y : ℝ in cocompact ℝ, ∀ σ ∈ Icc p₁ ρ,
      ‖Gamma (1 - (σ + y * I)) * mellin (trunc₁ h) (σ + y * I)‖ ≤ ε := by
  obtain ⟨M₁, hM₁0, hM₁⟩ := exists_norm_mellin_trunc₁_le H.h_loc H.h_zero hp₁
  obtain ⟨M, hM0, hM⟩ := exists_Gamma_strip_bound (a := 1 - ρ) (b := 1 - p₁) 2
    (by push_cast; linarith)
  intro ε hε
  refine eventually_cocompact_of_abs_ge (max 1 (Real.sqrt ((M * M₁ + 1) / ε))) fun y hy σ hσ => ?_
  have hy1 : 1 ≤ |y| := (le_max_left _ _).trans hy
  have hy0 : y ≠ 0 := fun h => by rw [h, abs_zero] at hy1; linarith
  have hsq : (M * M₁ + 1) / ε ≤ |y| ^ 2 := by
    have := (le_max_right _ _).trans hy
    calc (M * M₁ + 1) / ε = Real.sqrt ((M * M₁ + 1) / ε) ^ 2 :=
          (Real.sq_sqrt (by positivity)).symm
      _ ≤ |y| ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) this 2
  have hG : ‖Gamma (1 - (σ + y * I))‖ ≤ M / |y| ^ 2 := by
    have := hM (1 - σ) ⟨by linarith [hσ.2], by linarith [hσ.1]⟩ (-y) (neg_ne_zero.mpr hy0)
    rw [abs_neg] at this
    have e : (1 : ℂ) - (σ + y * I) = ((1 - σ : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [e]
    exact this
  have hh : ‖mellin (trunc₁ h) (σ + y * I)‖ ≤ M₁ := hM₁ _ (by simpa using hσ.1)
  rw [norm_mul]
  calc ‖Gamma (1 - (σ + y * I))‖ * ‖mellin (trunc₁ h) (σ + y * I)‖ ≤ M / |y| ^ 2 * M₁ :=
        mul_le_mul hG hh (norm_nonneg _) (by positivity)
    _ = M * M₁ / |y| ^ 2 := by ring
    _ ≤ ε := by
        rw [div_le_iff₀ (by positivity)]
        rw [div_le_iff₀ hε] at hsq
        nlinarith

/-- `Γ(1 − z) 𝓜h₁(z)` is integrable on the line `ℜz = σ` for `−c < σ`, `σ ≠ 1, 2, …`. -/
theorem integrable_Gamma_mul_h₁_line {σ : ℝ} (hσ : -c < σ) (hσ' : ∀ n : ℕ, σ ≠ n + 1) :
    Integrable fun y : ℝ => Gamma (1 - (σ + y * I)) * mellin (trunc₁ h) (σ + y * I) := by
  obtain ⟨M₁, hM₁0, hM₁⟩ := exists_norm_mellin_trunc₁_le H.h_loc H.h_zero hσ
  have hpole : ∀ n : ℕ, (1 - σ : ℝ) ≠ -n := fun n h => hσ' n (by linarith)
  have hΓ : Integrable fun y : ℝ => Gamma (1 - (σ + y * I)) := by
    have := (integrable_Gamma_vertical hpole).comp_mul_left' (R := (-1 : ℝ)) (by norm_num)
    refine this.congr (ae_of_all _ fun y => ?_)
    dsimp only
    congr 1
    push_cast
    ring
  refine (hΓ.norm.const_mul M₁).mono' ?_ (ae_of_all _ fun y => ?_)
  · refine (Continuous.aestronglyMeasurable ?_)
    refine Continuous.mul ?_ ?_
    · exact (continuous_Gamma_vertical hpole).comp (continuous_neg) |>.congr fun y => by
        simp only [Function.comp]
        congr 1
        push_cast
        ring
    · refine continuous_iff_continuousAt.mpr fun y => ?_
      exact (H.differentiableAt_h₁ (z := σ + y * I) (by simpa)).continuousAt.comp
        (f := fun y : ℝ => (σ : ℂ) + y * I) (by fun_prop)
  · rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hM₁ _ (by simp)) (norm_nonneg _)

/-- **DLMF 2.5.41**: for `1 < ρ < 2` and `x > 0`,
`I₁(x) = 𝓜h₁(1) x^{−1} + (2πi)⁻¹ ∫_{ρ−i∞}^{ρ+i∞} x^{−z} Γ(1 − z) 𝓜h₁(z) dz`: the contour of
2.5.40 is moved from `ℜz = p₁` to `ℜz = ρ` across the simple pole of `Γ(1 − z)` at `z = 1`. -/
theorem dlmf_2_5_41 {ρ : ℝ} (hρ1 : 1 < ρ) (hρ2 : ρ < 2) {x : ℝ} (hx : 0 < x) :
    mellinConvInt expNeg (trunc₁ h) x = mellin (trunc₁ h) 1 * (x : ℂ) ^ (-1 : ℂ) +
      (2 * π : ℂ)⁻¹ * ∫ y : ℝ, (x : ℂ) ^ (-((ρ : ℂ) + y * I)) *
        (Gamma (1 - (ρ + y * I)) * mellin (trunc₁ h) (ρ + y * I)) := by
  have hc := H.c_gt
  set p₁ : ℝ := (1 - c) / 2 with hp₁def
  have hp₁ : -c < p₁ := by rw [hp₁def]; linarith
  have hp₁' : p₁ < 1 := by rw [hp₁def]; linarith
  set G : ℂ → ℂ := fun z => Gamma (1 - z) * mellin (trunc₁ h) z with hGdef
  set U : Set ℂ := {z : ℂ | -c < z.re ∧ z.re < 2} with hUdef
  have hU : IsOpen U := (isOpen_lt continuous_const continuous_re).inter
    (isOpen_lt continuous_re continuous_const)
  set R : ℝ := min (1 + c) 1 / 2 with hRdef
  have hmin : 0 < min (1 + c) 1 := lt_min (by linarith) one_pos
  have hR0 : 0 < R := by rw [hRdef]; positivity
  have hR1 : R < 1 + c := by
    rw [hRdef]; have := min_le_left (1 + c) 1; linarith
  have hR2 : R < 1 := by
    rw [hRdef]; have := min_le_right (1 + c) 1; linarith
  have hball : ball (1 : ℂ) R ⊆ U := fun z hz => by
    rw [mem_ball, dist_eq_norm] at hz
    have := abs_re_le_norm (z - 1)
    rw [sub_re, one_re] at this
    have := abs_le.mp (this.trans hz.le)
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  have key := dlmf_2_5_35 (fj := expNeg) (hk := trunc₁ h) (p := p₁) (q := ρ) (by linarith)
    (mellinConvergent_expNeg (by simp; linarith)) (H.mellinConvergent_h₁ (by simpa))
    (Or.inr (integrable_mellin_expNeg_line hp₁')) hx hU
    (fun z hz => ⟨by linarith [hz.1], by linarith [hz.2]⟩) (S := {1})
    (fun s hs => by simp at hs; subst hs; simp; constructor <;> linarith)
    (H.differentiableOn_Gamma_mul_h₁) (fun y => by rw [mellinG_expNeg _ (by simp; linarith)])
    (H.sup_Gamma_mul_h₁_tendsto hp₁ hρ2)
    (H.integrable_Gamma_mul_h₁_line hp₁ fun n => by linarith [n.cast_nonneg (α := ℝ)])
    (H.integrable_Gamma_mul_h₁_line (by linarith) fun n hn => by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0; simp at hn; linarith
      · have : (1 : ℝ) ≤ n := by exact_mod_cast h0
        linarith)
    (fun _ => R) (fun s hs => by
      simp at hs; subst hs
      exact ⟨hR0, hball, fun t ht hne => by simp at ht; exact absurd ht hne⟩)
  rw [key, Finset.sum_singleton]
  congr 1
  -- the residue at `z = 1`
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hpow : Differentiable ℂ fun z : ℂ => (x : ℂ) ^ (-z) :=
    fun z => ((hasDerivAt_neg z).const_cpow (Or.inl hx0)).differentiableAt
  have hA : DifferentiableOn ℂ
      (fun z => (x : ℂ) ^ (-z) * mellin (trunc₁ h) z * GammaNum 0 (1 - z)) (ball 1 R) := by
    refine (hpow.differentiableOn.mul fun z hz =>
      (H.differentiableAt_h₁ (hball hz).1).differentiableWithinAt).mul ?_
    refine (differentiableOn_GammaNum 0).comp
      ((differentiableOn_const _).sub differentiableOn_id) ?_
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz ⊢
    simpa [norm_sub_rev] using hz.trans hR2
  have hres := residue_eq_of_eq_div_add (F := fun z => -((x : ℂ) ^ (-z) * G z)) (n := 1) hR0 hA
    (differentiableOn_const 0) fun z hz => by
      have hz1 : z ≠ 1 := fun h => by
        have := hz.1
        rw [h, sub_self, norm_zero] at this
        exact lt_irrefl _ this
      have hpole : ∀ j : ℕ, j ≤ 0 → (1 - z) + (j : ℂ) ≠ 0 := fun j hj => by
        rw [Nat.le_zero.mp hj]
        simp only [Nat.cast_zero, add_zero, ne_eq, sub_eq_zero]
        exact fun h => hz1 h.symm
      simp only [hGdef, add_zero]
      rw [show -((x : ℂ) ^ (-z) * (Gamma (1 - z) * mellin (trunc₁ h) z)) =
        (x : ℂ) ^ (-z) * mellin (trunc₁ h) z * -Gamma (1 - z) by ring, neg_Gamma_one_sub_eq hpole]
      push_cast
      ring
  rw [hres]
  simp only [sub_self]
  rw [show GammaNum 0 0 = 1 by simpa using GammaNum_neg_nat 0]
  ring

end LaplaceSmallSetup

end Azurite.DLMF
