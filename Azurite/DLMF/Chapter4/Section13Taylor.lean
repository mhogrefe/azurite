/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section13Abel
import Azurite.DLMF.Chapter4.Section13Deriv
import Mathlib.Analysis.Complex.TaylorSeries

/-!
# DLMF §4.13: Maclaurin series of the Lambert `W`-function

`W₀` is analytic on `|z| < e⁻¹` (`ball_subset_cutW0`), so it equals its Taylor series there. The
derivatives at `0` follow from `z(1 + W)W′ = W` by the Leibniz rule (`iteratedDeriv_W0_rec`) and
the Abel identity (`abel_identity`).

* 4.13.5: `dlmf_4_13_5`; 4.13.5_1 (`e^{−aW₀}`): `dlmf_4_13_5_1`; 4.13.5_2: `dlmf_4_13_5_2`;
  4.13.5_3: `dlmf_4_13_5_3`.
-/

open Set Filter Topology Complex Finset
open scoped Real Nat

namespace Azurite.DLMF

/-! ### Setup -/

theorem ball_subset_cutW0 : Metric.ball (0 : ℂ) (Real.exp (-1)) ⊆ cutW0 := by
  intro z hz ⟨_, hre⟩
  have h1 := (neg_abs_le z.re).trans hre
  have h2 : |z.re| < Real.exp (-1) :=
    (abs_re_le_norm z).trans_lt (by simpa using hz)
  linarith

theorem zero_mem_cutW0 : (0 : ℂ) ∈ cutW0 :=
  ball_subset_cutW0 (Metric.mem_ball_self (Real.exp_pos _))

theorem one_add_lambertW_zero_ne_zero {z : ℂ} (hz : z ∈ cutW0) : 1 + lambertW 0 z ≠ 0 := by
  intro h
  have hm1 : lambertW 0 z = -1 := by linear_combination h
  have hW := dlmf_4_13_1 0 z
  rw [hm1] at hW
  apply hz
  rw [← hW, show (-1 : ℂ) * exp (-1) = ((-Real.exp (-1) : ℝ) : ℂ) by push_cast; ring]
  exact ⟨ofReal_im _, le_of_eq (ofReal_re _)⟩

theorem analyticAt_W0 {z : ℂ} (hz : z ∈ cutW0) : AnalyticAt ℂ (lambertW 0) z :=
  analyticOnNhd_lambertW_zero z hz

theorem lambertW_zero_zero : lambertW 0 0 = 0 := lambertW_zero_arg 0

/-- `z (1 + W) W′ = W` on `ℂ ∖ (−∞, −e⁻¹]`. -/
theorem W0_ode {z : ℂ} (hz : z ∈ cutW0) :
    (1 + lambertW 0 z) * (z * deriv (lambertW 0) z) = lambertW 0 z := by
  rw [(dlmf_4_13_W0_analytic hz).deriv]
  have h1 := one_add_lambertW_zero_ne_zero hz
  have hW := dlmf_4_13_1 0 z
  generalize lambertW 0 z = w at h1 hW ⊢
  subst hW
  rw [exp_neg]
  field_simp

/-- `(zF)^{(n)}(0) = n F^{(n−1)}(0)`. -/
theorem iteratedDeriv_id_mul_zero {F : ℂ → ℂ} {n : ℕ} (hF : ContDiffAt ℂ n F 0) :
    iteratedDeriv n (fun z => z * F z) 0 = n * iteratedDeriv (n - 1) F 0 := by
  have hid : ContDiffAt ℂ n (fun a : ℂ => a) 0 := contDiffAt_id
  rw [iteratedDeriv_fun_mul hid hF]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [iteratedDeriv_fun_id_zero]
  · rw [sum_eq_single 1 (fun i _ hi => by rw [iteratedDeriv_fun_id_zero]; simp [hi])
      (fun h => absurd (mem_range.mpr (by omega)) h)]
    rw [iteratedDeriv_fun_id_zero]; simp

/-- `D n = W₀^{(n)}(0)`. -/
noncomputable def dW (n : ℕ) : ℂ := iteratedDeriv n (lambertW 0) 0

theorem dW_def (n : ℕ) : iteratedDeriv n (lambertW 0) 0 = dW n := rfl

theorem dW_zero : dW 0 = 0 := by simp [dW, lambertW_zero_zero]

theorem iteratedDeriv_deriv_W0 (j : ℕ) : iteratedDeriv j (deriv (lambertW 0)) 0 = dW (j + 1) := by
  simp only [dW, iteratedDeriv_succ']

theorem contDiffAt_W0 (n : ℕ) : ContDiffAt ℂ n (lambertW 0) 0 :=
  (analyticAt_W0 zero_mem_cutW0).contDiffAt

theorem contDiffAt_deriv_W0 (n : ℕ) : ContDiffAt ℂ n (deriv (lambertW 0)) 0 :=
  (analyticAt_W0 zero_mem_cutW0).deriv.contDiffAt

/-- The Leibniz recursion: `D_m = m D_m + ∑_{i=1}^{m} C(m, i) D_i (m − i) D_{m−i}`. -/
theorem iteratedDeriv_W0_rec (m : ℕ) :
    dW m = m * dW m + ∑ i ∈ Icc 1 m, (m.choose i : ℂ) * dW i * ((m - i : ℕ) * dW (m - i)) := by
  have hev : (fun z => (1 + lambertW 0 z) * (z * deriv (lambertW 0) z)) =ᶠ[𝓝 0] lambertW 0 :=
    eventually_of_mem (isOpen_cutW0.mem_nhds zero_mem_cutW0) fun z hz => W0_ode hz
  have h := hev.iteratedDeriv_eq m
  have hf : ContDiffAt ℂ m (fun z => 1 + lambertW 0 z) 0 := contDiffAt_const.add (contDiffAt_W0 m)
  have hg : ContDiffAt ℂ m (fun z => z * deriv (lambertW 0) z) 0 :=
    contDiffAt_id.mul (contDiffAt_deriv_W0 m)
  rw [iteratedDeriv_fun_mul hf hg] at h
  conv_lhs => rw [show dW m = iteratedDeriv m (lambertW 0) 0 from rfl, ← h]
  rw [sum_range_succ']
  have hterm : ∀ i ∈ range m, (m.choose (i + 1) : ℂ) *
      iteratedDeriv (i + 1) (fun z => 1 + lambertW 0 z) 0 *
      iteratedDeriv (m - (i + 1)) (fun z => z * deriv (lambertW 0) z) 0 =
      (m.choose (i + 1) : ℂ) * dW (i + 1) * ((m - (i + 1) : ℕ) * dW (m - (i + 1))) := by
    intro i hi
    rw [iteratedDeriv_const_add (by omega), iteratedDeriv_id_mul_zero (contDiffAt_deriv_W0 _)]
    rcases Nat.eq_zero_or_pos (m - (i + 1)) with h0 | h0
    · rw [h0]; simp
    · rw [iteratedDeriv_deriv_W0, show m - (i + 1) - 1 + 1 = m - (i + 1) by omega]; rfl
  rw [sum_congr rfl hterm]
  have h0 : iteratedDeriv 0 (fun z => 1 + lambertW 0 z) 0 = 1 := by
    simp [lambertW_zero_zero]
  rw [h0, iteratedDeriv_id_mul_zero (contDiffAt_deriv_W0 _)]
  have hshift : ∑ i ∈ range m, (m.choose (i + 1) : ℂ) * dW (i + 1) *
      ((m - (i + 1) : ℕ) * dW (m - (i + 1))) =
      ∑ i ∈ Icc 1 m, (m.choose i : ℂ) * dW i * ((m - i : ℕ) * dW (m - i)) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
    refine sum_congr rfl fun i _ => ?_
    rw [add_comm 1 i]
  rw [hshift]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · simp only [Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, one_mul]
    rw [iteratedDeriv_deriv_W0, show m - 1 + 1 = m by omega]
    ring

/-- The candidate `(−n)^{n−1}` (and `0` for `n = 0`). -/
noncomputable def dWc (n : ℕ) : ℂ := if n = 0 then 0 else (-(n : ℂ)) ^ (n - 1)

/-- **The derivatives of `W₀` at `0`**: `W₀^{(n)}(0) = (−n)^{n−1}`, `n ≥ 1`. -/
theorem dW_eq (n : ℕ) : dW n = dWc n := by
  induction n using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.lt_or_ge m 2 with hm | hm
    · interval_cases m
      · simp [dW, dWc, lambertW_zero_zero]
      · simp only [dW, dWc, iteratedDeriv_one, (dlmf_4_13_W0_analytic zero_mem_cutW0).deriv,
          lambertW_zero_zero]
        simp
    · obtain ⟨p, rfl⟩ : ∃ p, m = p + 2 := ⟨m - 2, by omega⟩
      have hrec := iteratedDeriv_W0_rec (p + 2)
      have hsum : ∑ i ∈ Icc 1 (p + 2), ((p + 2).choose i : ℂ) * dW i *
          ((p + 2 - i : ℕ) * dW (p + 2 - i)) = ∑ i ∈ Icc 1 (p + 2),
          ((-1 : ℂ) ^ (p + 2) * (((p + 2).choose i : ℂ) * (i : ℂ) ^ (i - 1) *
            ((0 : ℂ) + ((p + 2 : ℕ) : ℂ) - i) ^ (p + 2 - i)) -
          if i = p + 2 then (-1 : ℂ) ^ (p + 2) * ((p + 2 : ℕ) : ℂ) ^ (p + 1) else 0) := by
        refine sum_congr rfl fun i hi => ?_
        obtain ⟨hi1, hi2⟩ := mem_Icc.mp hi
        rcases hi2.lt_or_eq with hlt | rfl
        · rw [ih i hlt, ih (p + 2 - i) (by omega), ite_eq_right_iff.mpr (fun h => absurd h hlt.ne)]
          obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
          obtain ⟨l, hl⟩ : ∃ l, p + 2 = j + 1 + (l + 1) := ⟨p - j, by omega⟩
          rw [hl, show j + 1 + (l + 1) - (j + 1) = l + 1 by omega]
          simp only [dWc, show j + 1 ≠ 0 by omega, show l + 1 ≠ 0 by omega, ↓reduceIte,
            show j + 1 - 1 = j by omega, show l + 1 - 1 = l by omega]
          rw [neg_pow (((l + 1 : ℕ) : ℂ)), neg_pow (((j + 1 : ℕ) : ℂ))]
          push_cast
          ring
        · simp only [Nat.sub_self, ↓reduceIte, Nat.cast_zero, zero_mul, mul_zero, pow_zero,
            Nat.choose_self, Nat.cast_one, one_mul, mul_one]
          push_cast
          ring
      rw [hsum, sum_sub_distrib, ← mul_sum, sum_ite_eq' (Icc 1 (p + 2)) (p + 2)] at hrec
      have habel := abel_identity (p + 2) (by omega) 0
      rw [abelSum] at habel
      rw [habel] at hrec
      simp only [Finset.mem_Icc, show 1 ≤ p + 2 by omega, le_refl, and_self, ↓reduceIte] at hrec
      simp only [dWc, show p + 2 ≠ 0 by omega, ↓reduceIte, show p + 2 - 1 = p + 1 by omega]
      have hm1 : (1 - ((p + 2 : ℕ) : ℂ)) ≠ 0 := by
        push_cast; intro h; have := congrArg re h; simp at this; linarith
      apply mul_left_cancel₀ hm1
      rw [neg_pow]
      push_cast at hrec ⊢
      linear_combination hrec

/-! ### 4.13.5 -/

theorem differentiableOn_W0_ball :
    DifferentiableOn ℂ (lambertW 0) (Metric.ball (0 : ℂ) (Real.exp (-1))) :=
  fun _ hz => (dlmf_4_13_W0_analytic (ball_subset_cutW0 hz)).differentiableAt.differentiableWithinAt

/-- The Taylor series of `W₀` at `0` on `|z| < e⁻¹`, all terms. -/
theorem hasSum_W0 {z : ℂ} (hz : ‖z‖ < Real.exp (-1)) :
    HasSum (fun n : ℕ => (n ! : ℂ)⁻¹ * z ^ n * dWc n) (lambertW 0 z) := by
  have h := Complex.hasSum_taylorSeries_on_ball differentiableOn_W0_ball (by simpa using hz)
  simp only [sub_zero, smul_eq_mul] at h
  convert h using 2 with n
  rw [← dW_eq, dW]; ring

/-- **DLMF 4.13.5**: `W₀(z) = ∑_{n=1}^∞ (−n)^{n−1}/n! zⁿ`, `|z| < e⁻¹`. -/
theorem dlmf_4_13_5 {z : ℂ} (hz : ‖z‖ < Real.exp (-1)) :
    HasSum (fun n : ℕ => (-((n + 1 : ℕ) : ℂ)) ^ n / ((n + 1)! : ℂ) * z ^ (n + 1))
      (lambertW 0 z) := by
  have h := (hasSum_nat_add_iff' 1).mpr (hasSum_W0 hz)
  simp only [range_one, sum_singleton, dWc, ↓reduceIte, mul_zero, sub_zero] at h
  convert h using 2 with n
  simp only [show n + 1 ≠ 0 by omega, ↓reduceIte, show n + 1 - 1 = n by omega]
  field_simp

/-- `|W₀(z)| < 1` for `|z| < e⁻¹` (the coefficients are dominated by `−W₀(−|z|) < 1`). -/
theorem norm_W0_lt_one {z : ℂ} (hz : ‖z‖ < Real.exp (-1)) : ‖lambertW 0 z‖ < 1 := by
  set r := ‖z‖
  have hr : ‖((-r : ℝ) : ℂ)‖ < Real.exp (-1) := by
    rw [norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg (norm_nonneg z)]; exact hz
  have hreal := hasSum_W0 hr
  rw [lambertW_zero_ofReal (by linarith [norm_nonneg z])] at hreal
  have hneg := hreal.neg
  have hbound : ∀ n, ‖(n ! : ℂ)⁻¹ * z ^ n * dWc n‖ ≤
      -((n ! : ℂ)⁻¹ * ((-r : ℝ) : ℂ) ^ n * dWc n).re := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [dWc]
    · simp only [dWc, show n ≠ 0 by omega, ↓reduceIte, norm_mul, norm_inv, norm_pow, norm_neg,
        Complex.norm_natCast]
      have : ((n ! : ℂ)⁻¹ * ((-r : ℝ) : ℂ) ^ n * (-(n : ℂ)) ^ (n - 1)) =
          ((-((n ! : ℝ)⁻¹ * r ^ n * (n : ℝ) ^ (n - 1)) : ℝ) : ℂ) := by
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        simp only [show m + 1 - 1 = m by omega]
        rw [neg_pow (((m + 1 : ℕ) : ℂ)) m]
        push_cast
        rw [neg_pow (r : ℂ) (m + 1)]
        have h2 : (-1 : ℂ) ^ (m + 1) * (-1) ^ m = -1 := by
          rw [← pow_add, show m + 1 + m = 2 * m + 1 by ring, pow_succ, pow_mul]; norm_num
        linear_combination (((m + 1)! : ℂ))⁻¹ * (r : ℂ) ^ (m + 1) * ((m : ℂ) + 1) ^ m * h2
      rw [this, ofReal_re, neg_neg]
  have hre := (Complex.reCLM.hasSum hneg)
  simp only [reCLM_apply, neg_re] at hre
  have hle := (hasSum_W0 hz).norm_le_of_bounded hre hbound
  have hW := lambertW0_gt (y := -r) (by linarith [norm_nonneg z])
  simp only [ofReal_re] at hle
  linarith

/-! ### 4.13.5_2 and 4.13.5_3 -/

/-- **DLMF 4.13.5_2**: `1/(1 + W₀(−z)) = ∑_{n=0}^∞ nⁿ/n! zⁿ`, `|z| < e⁻¹`. -/
theorem dlmf_4_13_5_2 {z : ℂ} (hz : ‖z‖ < Real.exp (-1)) :
    HasSum (fun n : ℕ => ((n : ℂ)) ^ n / (n ! : ℂ) * z ^ n) (1 / (1 + lambertW 0 (-z))) := by
  set h : ℂ → ℂ := fun z => 1 / (1 + lambertW 0 z)
  have hdiff : DifferentiableOn ℂ h (Metric.ball (0 : ℂ) (Real.exp (-1))) :=
    (differentiableOn_const 1).div (differentiableOn_const 1 |>.add differentiableOn_W0_ball)
      fun z hz => one_add_lambertW_zero_ne_zero (ball_subset_cutW0 hz)
  have hev : h =ᶠ[𝓝 0] fun z => 1 - z * deriv (lambertW 0) z := by
    filter_upwards [isOpen_cutW0.mem_nhds zero_mem_cutW0] with z hz
    have := W0_ode hz
    have h1 := one_add_lambertW_zero_ne_zero hz
    simp only [h]
    field_simp
    linear_combination this
  have hcoef : ∀ n, iteratedDeriv n h 0 = (-(n : ℂ)) ^ n := by
    intro n
    rw [hev.iteratedDeriv_eq]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [iteratedDeriv_const_sub hn, iteratedDeriv_neg, iteratedDeriv_id_mul_zero
        (contDiffAt_deriv_W0 _), iteratedDeriv_deriv_W0, show n - 1 + 1 = n by omega, dW_eq]
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      simp only [dWc, show m + 1 ≠ 0 by omega, ↓reduceIte, show m + 1 - 1 = m by omega]
      rw [pow_succ]; ring
  have hmz : ‖-z‖ < Real.exp (-1) := by rwa [norm_neg]
  have hs := Complex.hasSum_taylorSeries_on_ball hdiff (z := -z) (by simpa using hmz)
  simp only [sub_zero, smul_eq_mul, hcoef] at hs
  convert hs using 2 with n
  rw [show (-z) ^ n * (-(n : ℂ)) ^ n = (n : ℂ) ^ n * z ^ n by rw [← mul_pow]; ring]
  field_simp

/-- **DLMF 4.13.5_3**: `(1 + W₀(z))² = 1 − 2 ∑_{n=1}^∞ n^{n−2}/n! (−z)ⁿ`, `|z| < e⁻¹`, written as
`(1 − (1 + W₀)²)/2 = ∑_{n≥1} n^{n−2} (−z)ⁿ/n!`. -/
theorem dlmf_4_13_5_3 {z : ℂ} (hz : ‖z‖ < Real.exp (-1)) :
    HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℂ) ^ (n - 1) / ((n + 1)! : ℂ) * (-z) ^ (n + 1))
      ((1 - (1 + lambertW 0 z) ^ 2) / 2) := by
  set Q : ℂ → ℂ := fun z => (1 + lambertW 0 z) ^ 2
  have hdiff : DifferentiableOn ℂ Q (Metric.ball (0 : ℂ) (Real.exp (-1))) :=
    ((differentiableOn_const 1).add differentiableOn_W0_ball).pow 2
  have hQan : AnalyticAt ℂ Q 0 :=
    (analyticAt_const.add (analyticAt_W0 zero_mem_cutW0)).pow 2
  have hev : (fun z => z * deriv Q z) =ᶠ[𝓝 0] fun z => 2 * lambertW 0 z := by
    filter_upwards [isOpen_cutW0.mem_nhds zero_mem_cutW0] with z hz
    have hd : HasDerivAt Q (2 * (1 + lambertW 0 z) * deriv (lambertW 0) z) z := by
      have := ((dlmf_4_13_W0_analytic hz).differentiableAt.hasDerivAt.const_add 1).pow 2
      convert this using 1; push_cast; ring
    rw [hd.deriv]
    have := W0_ode hz
    linear_combination 2 * this
  have hcoef : ∀ n, iteratedDeriv (n + 1) Q 0 = 2 * dWc (n + 1) / (n + 1) := by
    intro n
    have h1 := hev.iteratedDeriv_eq (n + 1)
    rw [iteratedDeriv_id_mul_zero (hQan.deriv.contDiffAt), iteratedDeriv_const_mul _
      (contDiffAt_W0 _), show n + 1 - 1 = n by omega, ← iteratedDeriv_succ', ← dW,
      dW_eq] at h1
    push_cast at h1
    rw [eq_div_iff (by exact_mod_cast Nat.succ_ne_zero n)]
    linear_combination h1
  have hs := Complex.hasSum_taylorSeries_on_ball hdiff (by simpa using hz)
  simp only [sub_zero, smul_eq_mul] at hs
  have hs1 := (hasSum_nat_add_iff' 1).mpr hs
  simp only [range_one, sum_singleton, Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero,
    one_mul, iteratedDeriv_zero, Q, lambertW_zero_zero, add_zero, one_pow, hcoef] at hs1
  have := (hs1.mul_left (-1 / 2))
  convert this using 1
  · funext n
    simp only [dWc, show n + 1 ≠ 0 by omega, ↓reduceIte, show n + 1 - 1 = n by omega]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp; ring
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      simp only [show m + 1 - 1 = m by omega]
      rw [neg_pow z (m + 1 + 1), neg_pow (((m + 1 + 1 : ℕ) : ℂ)) (m + 1), pow_succ (-1 : ℂ) (m + 1),
        pow_succ (((m + 1 + 1 : ℕ) : ℂ)) m]
      have h0 : ((m : ℂ) + 1 + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (m + 1)
      rw [Nat.factorial_succ (m + 1)]
      push_cast
      field_simp
  · ring

/-! ### 4.13.5_1 -/

/-- `e^{−aW₀(z)}`. -/
noncomputable def expW (a z : ℂ) : ℂ := exp (-a * lambertW 0 z)

theorem expW_ode (a : ℂ) {z : ℂ} (hz : z ∈ cutW0) :
    (1 + lambertW 0 z) * (z * deriv (expW a) z) = -a * (lambertW 0 z * expW a z) := by
  have hd : HasDerivAt (expW a) (expW a z * (-a * deriv (lambertW 0) z)) z := by
    have := ((dlmf_4_13_W0_analytic hz).differentiableAt.hasDerivAt.const_mul (-a)).cexp
    exact this
  rw [hd.deriv]
  have := W0_ode hz
  linear_combination (-a * expW a z) * this

theorem analyticAt_expW (a : ℂ) : AnalyticAt ℂ (expW a) 0 :=
  (analyticAt_const.mul (analyticAt_W0 zero_mem_cutW0)).cexp

/-- The Leibniz recursion for `e^{−aW₀}`. -/
theorem iteratedDeriv_expW_rec (a : ℂ) (m : ℕ) :
    m * iteratedDeriv m (expW a) 0 + ∑ i ∈ Icc 1 m, (m.choose i : ℂ) * dW i *
        ((m - i : ℕ) * iteratedDeriv (m - i) (expW a) 0) =
      -a * ∑ i ∈ Icc 1 m, (m.choose i : ℂ) * dW i * iteratedDeriv (m - i) (expW a) 0 := by
  have hev : (fun z => (1 + lambertW 0 z) * (z * deriv (expW a) z)) =ᶠ[𝓝 0]
      fun z => -a * (lambertW 0 z * expW a z) :=
    eventually_of_mem (isOpen_cutW0.mem_nhds zero_mem_cutW0) fun z hz => expW_ode a hz
  have h := hev.iteratedDeriv_eq m
  have hG := analyticAt_expW a
  have hf : ContDiffAt ℂ m (fun z => 1 + lambertW 0 z) 0 := contDiffAt_const.add (contDiffAt_W0 m)
  have hg : ContDiffAt ℂ m (fun z => z * deriv (expW a) z) 0 :=
    contDiffAt_id.mul hG.deriv.contDiffAt
  have hWG : ContDiffAt ℂ m (fun z => lambertW 0 z * expW a z) 0 :=
    (contDiffAt_W0 m).mul hG.contDiffAt
  rw [iteratedDeriv_fun_mul hf hg, iteratedDeriv_const_mul _ hWG,
    iteratedDeriv_fun_mul (contDiffAt_W0 m) hG.contDiffAt] at h
  rw [sum_range_succ'] at h
  rw [sum_range_succ'] at h
  simp only [dW_def, dW_zero, mul_zero, zero_mul, add_zero] at h
  have hterm : ∀ i ∈ range m, (m.choose (i + 1) : ℂ) *
      iteratedDeriv (i + 1) (fun z => 1 + lambertW 0 z) 0 *
      iteratedDeriv (m - (i + 1)) (fun z => z * deriv (expW a) z) 0 =
      (m.choose (i + 1) : ℂ) * dW (i + 1) *
        ((m - (i + 1) : ℕ) * iteratedDeriv (m - (i + 1)) (expW a) 0) := by
    intro i hi
    rw [iteratedDeriv_const_add (by omega), iteratedDeriv_id_mul_zero hG.deriv.contDiffAt]
    rcases Nat.eq_zero_or_pos (m - (i + 1)) with h0 | h0
    · rw [h0]; simp
    · rw [← iteratedDeriv_succ', show m - (i + 1) - 1 + 1 = m - (i + 1) by omega]; rfl
  rw [sum_congr rfl hterm] at h
  have hshift : ∀ F : ℕ → ℂ, ∑ i ∈ range m, F (i + 1) = ∑ i ∈ Icc 1 m, F i := by
    intro F
    rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
    exact sum_congr rfl fun i _ => by rw [add_comm 1 i]
  rw [hshift (fun i => (m.choose i : ℂ) * dW i * ((m - i : ℕ) * iteratedDeriv (m - i) (expW a) 0)),
    hshift (fun i => (m.choose i : ℂ) * dW i * iteratedDeriv (m - i) (expW a) 0)] at h
  rw [← h]
  have h0 : iteratedDeriv 0 (fun z => 1 + lambertW 0 z) 0 = 1 := by simp [lambertW_zero_zero]
  rw [h0, iteratedDeriv_id_mul_zero hG.deriv.contDiffAt]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · rw [← iteratedDeriv_succ']
    simp only [Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, one_mul]
    rw [show m - 1 + 1 = m by omega]
    ring

/-- The coefficients `(−1)ⁿ a (n + a)^{n−1}` (and `1` for `n = 0`). -/
noncomputable def expWc (a : ℂ) (n : ℕ) : ℂ := if n = 0 then 1 else (-1) ^ n * a * (n + a) ^ (n - 1)

theorem iteratedDeriv_expW (a : ℂ) (n : ℕ) : iteratedDeriv n (expW a) 0 = expWc a n := by
  induction n using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [expW, expWc, lambertW_zero_zero]
    · have hrec := iteratedDeriv_expW_rec a m
      have hsum : ∑ i ∈ Icc 1 m, (m.choose i : ℂ) * dW i *
            ((m - i : ℕ) * iteratedDeriv (m - i) (expW a) 0) +
          a * ∑ i ∈ Icc 1 m, (m.choose i : ℂ) * dW i * iteratedDeriv (m - i) (expW a) 0 =
          (-1 : ℂ) ^ (m - 1) * a * abelSum m a := by
        rw [abelSum, mul_sum, mul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun i hi => ?_
        obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.mp hi
        rw [ih (m - i) (by omega), dW_eq]
        obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        rcases hi2.lt_or_eq with hlt | heq
        · obtain ⟨l, hl⟩ : ∃ l, m = j + 1 + (l + 1) := ⟨m - j - 2, by omega⟩
          subst hl
          rw [show j + 1 + (l + 1) - (j + 1) = l + 1 by omega]
          simp only [dWc, expWc, show j + 1 ≠ 0 by omega, show l + 1 ≠ 0 by omega, ↓reduceIte,
            show j + 1 - 1 = j by omega, show l + 1 - 1 = l by omega,
            show j + 1 + (l + 1) - 1 = j + l + 1 by omega]
          rw [neg_pow (((j + 1 : ℕ) : ℂ)) j]
          push_cast
          rw [show (-1 : ℂ) ^ (j + l + 1) = (-1) ^ j * (-1) ^ (l + 1) by
            rw [← pow_add]; ring_nf]
          ring
        · subst heq
          simp only [Nat.sub_self, dWc, expWc, show j + 1 ≠ 0 by omega, ↓reduceIte,
            show j + 1 - 1 = j by omega, Nat.choose_self, Nat.cast_one, Nat.cast_zero,
            mul_zero, zero_add, pow_zero, one_mul, mul_one]
          rw [neg_pow (((j + 1 : ℕ) : ℂ)) j]
          push_cast
          ring
      rw [abel_identity m hm] at hsum
      simp only [expWc, show m ≠ 0 by omega, ↓reduceIte]
      have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
      apply mul_left_cancel₀ hm0
      obtain ⟨p, rfl⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
      simp only [show p + 1 - 1 = p by omega] at hsum ⊢
      rw [pow_succ (-1 : ℂ) p]
      linear_combination hrec - hsum

/-- **DLMF 4.13.5_1**: `(W₀(z)/z)^a = e^{−aW₀(z)} = ∑_{n=0}^∞ a(n + a)^{n−1}/n! (−z)ⁿ`
(`|z| < e⁻¹`; the `n = 0` term is `1`). -/
theorem dlmf_4_13_5_1 (a : ℂ) {z : ℂ} (hz : ‖z‖ < Real.exp (-1)) :
    HasSum (fun n : ℕ => (if n = 0 then 1 else a * (n + a) ^ (n - 1)) / (n ! : ℂ) * (-z) ^ n)
      (exp (-a * lambertW 0 z)) ∧
      (z ≠ 0 → (lambertW 0 z / z) ^ a = exp (-a * lambertW 0 z)) := by
  refine ⟨?_, fun hz0 => ?_⟩
  · have hdiff : DifferentiableOn ℂ (expW a) (Metric.ball (0 : ℂ) (Real.exp (-1))) :=
      fun y hy => ((((dlmf_4_13_W0_analytic (ball_subset_cutW0 hy)).differentiableAt.const_mul
        (-a)).cexp).differentiableWithinAt)
    have hs := Complex.hasSum_taylorSeries_on_ball hdiff (by simpa using hz)
    simp only [sub_zero, smul_eq_mul, iteratedDeriv_expW] at hs
    rw [show exp (-a * lambertW 0 z) = expW a z from rfl]
    convert hs using 2 with n
    simp only [expWc]
    split_ifs with h
    · simp [h]
    · rw [neg_pow z]; field_simp
  · have hW := dlmf_4_13_1 0 z
    have hW0 : lambertW 0 z ≠ 0 := lambertW_ne_zero 0 hz0
    have hq : lambertW 0 z / z = exp (-lambertW 0 z) := by
      calc lambertW 0 z / z = lambertW 0 z / (lambertW 0 z * exp (lambertW 0 z)) := by rw [hW]
        _ = exp (-lambertW 0 z) := by rw [exp_neg]; field_simp
    have h1 := norm_W0_lt_one hz
    have him : |(lambertW 0 z).im| < 1 := (abs_im_le_norm _).trans_lt h1
    rw [hq, cpow_def_of_ne_zero (exp_ne_zero _), log_exp]
    · ring_nf
    · simp only [neg_im]; linarith [(abs_lt.mp him).2, Real.pi_gt_three]
    · simp only [neg_im]; linarith [(abs_lt.mp him).1, Real.pi_gt_three]

end Azurite.DLMF
