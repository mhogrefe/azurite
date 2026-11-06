/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section13Series

/-!
# DLMF §4.13: the expansion 4.13.9_1 of `W₀` in powers of `(ez + 1)^{1/2}`

`vD p = W((p² − 1)/e)`, glued from `W₀` (`ℜp > 0`), `W₁`, `W_{−1}` (`ℜp < 0`) as in `uT`, is
analytic on `|p| < 1`. For the principal square root `p = (ez + 1)^{1/2}` it is `W₀(z)`. With
`q = 1 + vD`, `(q²)′(p² − 1) = 4p·vD`, and the Leibniz rule gives 4.13.9_2.

* 4.13.9_1: `dlmf_4_13_9_1`; 4.13.9_2: `dlmf_4_13_9_2` (values) and `dlmf_4_13_9_2_rec`.
-/

open Set Filter Topology Complex Finset
open scoped Real Nat

namespace Azurite.DLMF

/-- `z = (p² − 1)/e`. -/
noncomputable def zD (p : ℂ) : ℂ := (p ^ 2 - 1) * ((Real.exp (-1) : ℝ) : ℂ)

/-- `W((p² − 1)/e)` on the sheet selected by `p` (4.13.9_1). -/
noncomputable def vD (p : ℂ) : ℂ := lambertGlue p (zD p)

theorem zD_re (p : ℂ) : (zD p).re = (p.re ^ 2 - p.im ^ 2 - 1) * Real.exp (-1) := by
  simp only [zD, mul_re, mul_im, sub_re, sub_im, one_re, one_im, ofReal_re, ofReal_im, sq]; ring

theorem zD_im (p : ℂ) : (zD p).im = 2 * (p.re * p.im) * Real.exp (-1) := by
  simp only [zD, mul_re, mul_im, sub_re, sub_im, one_re, one_im, ofReal_re, ofReal_im, sq]; ring

theorem zD_ofReal (r : ℝ) : zD r = (((r ^ 2 - 1) * Real.exp (-1) : ℝ) : ℂ) := by
  simp [zD]

theorem zD_zero : zD 0 = ((-Real.exp (-1) : ℝ) : ℂ) := by simp [zD]

theorem imSign_zD (p : ℂ) : ImSign p (zD p) := by
  have he := Real.exp_pos (-1)
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> rw [zD_im]
  · positivity
  · nlinarith

theorem continuousAt_vD {p₀ : ℂ} (hp : ‖p₀‖ < 1) : ContinuousAt vD p₀ := by
  have hcZ : Continuous zD := by unfold zD; fun_prop
  have he := Real.exp_pos (-1)
  have hn : p₀.re ^ 2 + p₀.im ^ 2 < 1 := by
    have := sq_lt_one_iff₀ (norm_nonneg p₀) |>.mpr hp
    rwa [← Complex.normSq_eq_norm_sq, normSq_apply, ← sq, ← sq] at this
  refine continuousAt_lambertGlue hcZ.continuousAt (fun hr => ?_) (fun hr hi => ?_)
    (fun hr hi => ?_) (fun hr hi => ?_) (fun h => by rw [h, zD_zero])
    (fun _ => Eventually.of_forall imSign_zD)
  · rintro ⟨him, hle⟩
    rw [zD_im] at him
    have hi : p₀.im = 0 := by
      rcases mul_eq_zero.mp him with h | h
      · rcases mul_eq_zero.mp h with h | h
        · norm_num at h
        · rcases mul_eq_zero.mp h with h | h
          · linarith
          · exact h
      · linarith
    rw [zD_re, hi] at hle
    nlinarith [sq_pos_of_pos hr]
  · rw [mem_slitPlane_iff]; right
    rw [zD_im]
    exact mul_ne_zero (mul_ne_zero two_ne_zero (mul_ne_zero hr.ne hi)) he.ne'
  · refine ⟨(p₀.re ^ 2 - 1) * Real.exp (-1), ?_, ?_, ?_⟩
    · nlinarith [sq_pos_of_neg hr]
    · rw [hi] at hn; nlinarith
    · have ht0 : p₀ = (p₀.re : ℂ) := Complex.ext (by simp) (by simp [hi])
      conv_lhs => rw [ht0]
      rw [zD_ofReal]
  · refine ⟨(-p₀.im ^ 2 - 1) * Real.exp (-1), ?_, ?_⟩
    · nlinarith [sq_pos_of_ne_zero hi]
    · have ht0 : p₀ = (p₀.im : ℂ) * I := Complex.ext (by simp [hr]) (by simp)
      conv_lhs => rw [ht0]
      rw [zD]; push_cast; ring_nf; rw [I_sq]; ring

theorem zD_eq_neg_exp {p : ℂ} (h : zD p = ((-Real.exp (-1) : ℝ) : ℂ)) : p = 0 := by
  have h2 : p ^ 2 * ((Real.exp (-1) : ℝ) : ℂ) = 0 := by
    rw [zD] at h; push_cast at h ⊢; linear_combination h
  rcases mul_eq_zero.mp h2 with h | h
  · exact pow_eq_zero_iff (two_ne_zero) |>.mp h
  · exact absurd h (by exact_mod_cast (Real.exp_pos _).ne')

theorem differentiableOn_vD : DifferentiableOn ℂ vD (Metric.ball 0 1) :=
  differentiableOn_lambertGlue (Z := zD) Metric.isOpen_ball (Metric.mem_ball_self one_pos)
    (by unfold zD; fun_prop) (fun p hp => continuousAt_vD (by simpa using hp))
    fun _ _ h => zD_eq_neg_exp h

theorem vD_zero : vD 0 = -1 := by
  rw [vD, zD_zero]
  simp only [lambertGlue, zero_re, zero_im, lt_irrefl, le_refl, and_self, or_true, ↓reduceIte]
  exact dlmf_4_13_2.1

theorem vD_ofReal_pos {r : ℝ} (hr : 0 < r) :
    vD r = (lambertW0 ((r ^ 2 - 1) * Real.exp (-1)) : ℂ) := by
  have hx : -Real.exp (-1) < (r ^ 2 - 1) * Real.exp (-1) := by
    nlinarith [Real.exp_pos (-1), sq_pos_of_pos hr]
  rw [vD, zD_ofReal]
  simp only [lambertGlue, ofReal_re, hr, true_or, ↓reduceIte]
  exact lambertW_zero_ofReal hx.le

/-! ### The differential equation `(1 + v)v′(p² − 1) = 2pv` -/

theorem hasDerivAt_vD {p : ℂ} (hp : ‖p‖ < 1) : HasDerivAt vD (deriv vD p) p :=
  (differentiableOn_vD.differentiableAt
    (Metric.isOpen_ball.mem_nhds (by simpa using hp))).hasDerivAt

theorem vD_ode {p : ℂ} (hp : ‖p‖ < 1) :
    deriv vD p * (1 + vD p) * (p ^ 2 - 1) = 2 * p * vD p := by
  have hv := hasDerivAt_vD hp
  have h1 : HasDerivAt (fun p => vD p * exp (vD p))
      (deriv vD p * exp (vD p) + vD p * (exp (vD p) * deriv vD p)) p := hv.mul hv.cexp
  have hfun : (fun p => vD p * exp (vD p)) = zD := funext fun p => lambertGlue_mul_exp p (zD p)
  rw [hfun] at h1
  have h2 : HasDerivAt zD (2 * p * ((Real.exp (-1) : ℝ) : ℂ)) p :=
    (((hasDerivAt_pow 2 p).sub_const 1).mul_const ((Real.exp (-1) : ℝ) : ℂ)).congr_deriv
      (by push_cast; ring)
  have h := h1.unique h2
  have hz : vD p * exp (vD p) = (p ^ 2 - 1) * ((Real.exp (-1) : ℝ) : ℂ) :=
    lambertGlue_mul_exp p (zD p)
  have he : ((Real.exp (-1) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos _).ne'
  apply mul_right_cancel₀ he
  linear_combination vD p * h - deriv vD p * (1 + vD p) * hz

theorem iteratedDeriv_id_mul_id_mul_zero {F : ℂ → ℂ} {n : ℕ} (hF : ContDiffAt ℂ n F 0) :
    iteratedDeriv n (fun p => p * (p * F p)) 0 =
      n * ((n - 1 : ℕ) * iteratedDeriv (n - 1 - 1) F 0) := by
  rw [iteratedDeriv_id_mul_zero (F := fun p => p * F p) (contDiffAt_id.mul hF),
    iteratedDeriv_id_mul_zero (hF.of_le (by exact_mod_cast Nat.sub_le n 1))]

/-- The Leibniz form of the ODE at order `m + 2`. -/
theorem vD_rec (m : ℕ) :
    ((m + 2 : ℕ) : ℂ) * ((m + 1 : ℕ) * (((m + 1)! : ℂ) *
        ∑ i ∈ range (m + 2), tcoef (fun p => 1 + vD p) i *
          tcoef (fun p => 1 + vD p) (m + 1 - i))) -
      ((m + 3)! : ℂ) * ∑ i ∈ range (m + 4), tcoef (fun p => 1 + vD p) i *
          tcoef (fun p => 1 + vD p) (m + 3 - i) =
      ((m + 2 : ℕ) : ℂ) * (4 * iteratedDeriv (m + 1) vD 0) := by
  have h0 : (0 : ℂ) ∈ Metric.ball 0 1 := Metric.mem_ball_self one_pos
  have han : AnalyticAt ℂ vD 0 :=
    differentiableOn_vD.analyticAt (Metric.isOpen_ball.mem_nhds h0)
  set Q := fun p => (1 + vD p) * (1 + vD p)
  have hQ : AnalyticAt ℂ Q 0 := (analyticAt_const.add han).mul (analyticAt_const.add han)
  have hF : ContDiffAt ℂ (m + 2) (deriv Q) 0 := hQ.deriv.contDiffAt
  have hev : (fun p => p * (p * deriv Q p) - deriv Q p) =ᶠ[𝓝 0]
      fun p => p * (4 * vD p) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds h0] with p hp
    have hp' : ‖p‖ < 1 := by simpa using hp
    have hv := hasDerivAt_vD hp'
    have hQd : HasDerivAt Q _ p := (hv.const_add 1).mul (hv.const_add 1)
    rw [hQd.deriv]
    linear_combination 2 * vD_ode hp'
  have h := hev.iteratedDeriv_eq (m + 2)
  rw [iteratedDeriv_fun_sub (f := fun p => p * (p * deriv Q p)) (g := deriv Q)
      (contDiffAt_id.mul (contDiffAt_id.mul hF)) hF,
    iteratedDeriv_id_mul_id_mul_zero hF,
    iteratedDeriv_id_mul_zero (contDiffAt_const.mul han.contDiffAt),
    iteratedDeriv_const_mul_field] at h
  have hq : ∀ k, ContDiffAt ℂ k (fun p => 1 + vD p) 0 :=
    fun k => contDiffAt_const.add han.contDiffAt
  rw [show m + 2 - 1 - 1 = m by omega, show m + 2 - 1 = m + 1 by omega,
    ← iteratedDeriv_succ', ← iteratedDeriv_succ', iteratedDeriv_mul_self_zero (hq _),
    iteratedDeriv_mul_self_zero (hq _)] at h
  rw [← h]

/-! ### The coefficients `d_n` -/

/-- **DLMF 4.13.9_1** coefficients: `d_n = v^{(n)}(0)/n!`. -/
noncomputable def lambertD (n : ℕ) : ℂ := tcoef vD n

theorem tcoef_qD_zero : tcoef (fun p => 1 + vD p) 0 = 0 := by simp [tcoef, vD_zero]

theorem tcoef_qD (n : ℕ) (hn : 0 < n) : tcoef (fun p => 1 + vD p) n = lambertD n :=
  tcoef_const_add vD hn 1

theorem lambertD_one_sq : lambertD 1 ^ 2 = 2 := by
  -- order 1: `−(q²)″(0) = 4 v(0)`
  have h0 : (0 : ℂ) ∈ Metric.ball 0 1 := Metric.mem_ball_self one_pos
  have han : AnalyticAt ℂ vD 0 :=
    differentiableOn_vD.analyticAt (Metric.isOpen_ball.mem_nhds h0)
  set Q := fun p => (1 + vD p) * (1 + vD p)
  have hQ : AnalyticAt ℂ Q 0 := (analyticAt_const.add han).mul (analyticAt_const.add han)
  have hF : ContDiffAt ℂ 1 (deriv Q) 0 := hQ.deriv.contDiffAt
  have hev : (fun p => p * (p * deriv Q p) - deriv Q p) =ᶠ[𝓝 0]
      fun p => p * (4 * vD p) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds h0] with p hp
    have hp' : ‖p‖ < 1 := by simpa using hp
    have hv := hasDerivAt_vD hp'
    have hQd : HasDerivAt Q _ p := (hv.const_add 1).mul (hv.const_add 1)
    rw [hQd.deriv]
    linear_combination 2 * vD_ode hp'
  have h := hev.iteratedDeriv_eq 1
  rw [iteratedDeriv_fun_sub (f := fun p => p * (p * deriv Q p)) (g := deriv Q)
      (contDiffAt_id.mul (contDiffAt_id.mul hF)) hF,
    iteratedDeriv_id_mul_id_mul_zero hF,
    iteratedDeriv_id_mul_zero (contDiffAt_const.mul han.contDiffAt)] at h
  have e1 : iteratedDeriv 1 (deriv Q) 0 = iteratedDeriv 2 Q 0 :=
    congrFun (iteratedDeriv_succ' (n := 1) (f := Q)).symm 0
  rw [e1, iteratedDeriv_mul_self_zero (contDiffAt_const.add han.contDiffAt),
    sum_range_mul_eq_Icc tcoef_qD_zero, show 2 - 1 = 1 by rfl, Finset.Icc_self, sum_singleton,
    show 2 - 1 = 1 by rfl, tcoef_qD 1 one_pos] at h
  simp only [Nat.sub_self, Nat.cast_zero, zero_mul, mul_zero, zero_sub, Nat.cast_one,
    iteratedDeriv_zero, vD_zero] at h
  norm_num at h
  linear_combination h / 2

theorem lambertD_one : lambertD 1 = (√2 : ℝ) := by
  set a := lambertD 1
  have ha : a = deriv vD 0 := by simp [a, lambertD, tcoef, iteratedDeriv_one]
  have hd : HasDerivAt vD a 0 := by rw [ha]; exact hasDerivAt_vD (by simp)
  have hr := (hd.comp_ofReal (z := 0)).tendsto_slope_zero_right
  have hre : 0 ≤ a.re := by
    refine ge_of_tendsto ((continuous_re.tendsto a).comp (by simpa using hr)) ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr0 : 0 < r)
    simp only [Function.comp_apply, vD_zero, ← ofReal_inv, re_ofReal_mul, sub_neg_eq_add]
    rw [vD_ofReal_pos hr0, add_re, ofReal_re, one_re]
    have hx : -Real.exp (-1) < (r ^ 2 - 1) * Real.exp (-1) := by
      nlinarith [Real.exp_pos (-1), sq_pos_of_pos hr0]
    have := lambertW0_gt hx
    exact mul_nonneg (inv_pos.mpr hr0).le (by linarith)
  have hs : ((√2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have h2 : (a - (√2 : ℝ)) * (a + (√2 : ℝ)) = 0 := by
    linear_combination lambertD_one_sq - hs
  rcases mul_eq_zero.mp h2 with h | h
  · linear_combination h
  · have : a = -((√2 : ℝ) : ℂ) := by linear_combination h
    rw [this, neg_re, ofReal_re] at hre
    have := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
    linarith

theorem sum_Icc_two_shift (f : ℕ → ℂ) (m : ℕ) :
    ∑ i ∈ Finset.Icc 2 (m + 1), f i = ∑ k ∈ Finset.Icc 1 m, f (k + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range, ← Finset.Ico_add_one_right_eq_Icc,
    sum_Ico_eq_sum_range, show m + 1 + 1 - 2 = m by omega, show m + 1 - 1 = m by omega]
  refine sum_congr rfl fun k _ => ?_
  congr 1; ring

/-- **DLMF 4.13.9_2** (recurrence): for `n ≥ 1`, `(n + 2) d₁ d_{n+1} = −2dₙ +
(n/2) ∑_{k=1}^{n−1} d_k d_{n−k} − ((n + 2)/2) ∑_{k=1}^{n−1} d_{k+1} d_{n−k+1}`. -/
theorem dlmf_4_13_9_2_rec (n : ℕ) (hn : 1 ≤ n) :
    (n + 2) * lambertD 1 * lambertD (n + 1) = -2 * lambertD n +
      n / 2 * ∑ k ∈ Finset.Icc 1 (n - 1), lambertD k * lambertD (n - k) -
      (n + 2) / 2 * ∑ k ∈ Finset.Icc 1 (n - 1), lambertD (k + 1) * lambertD (n - k + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h := vD_rec m
  rw [sum_range_mul_eq_Icc tcoef_qD_zero, sum_range_mul_eq_Icc tcoef_qD_zero,
    show m + 1 - 1 = m by omega, show m + 3 - 1 = m + 2 by omega] at h
  have hq1 : ∀ i ∈ Finset.Icc 1 m, tcoef (fun p => 1 + vD p) i *
      tcoef (fun p => 1 + vD p) (m + 1 - i) = lambertD i * lambertD (m + 1 - i) := by
    intro i hi
    obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.mp hi
    rw [tcoef_qD i (by omega), tcoef_qD _ (by omega)]
  have hq3 : ∀ i ∈ Finset.Icc 1 (m + 2), tcoef (fun p => 1 + vD p) i *
      tcoef (fun p => 1 + vD p) (m + 3 - i) = lambertD i * lambertD (m + 3 - i) := by
    intro i hi
    obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.mp hi
    rw [tcoef_qD i (by omega), tcoef_qD _ (by omega)]
  rw [sum_congr rfl hq1, sum_congr rfl hq3, sum_Icc_mul_split, sum_Icc_two_shift,
    iteratedDeriv_eq_tcoef] at h
  have hshift : ∑ k ∈ Finset.Icc 1 m, lambertD (k + 1) * lambertD (m + 3 - (k + 1)) =
      ∑ k ∈ Finset.Icc 1 m, lambertD (k + 1) * lambertD (m + 1 - k + 1) := by
    refine sum_congr rfl fun k hk => ?_
    rw [show m + 3 - (k + 1) = m + 1 - k + 1 by have := (Finset.mem_Icc.mp hk).2; omega]
  rw [hshift] at h
  rw [show m + 1 - 1 = m by omega, show m + 1 + 1 = m + 2 by omega]
  have hf3 : ((m + 3)! : ℂ) = (m + 3) * (m + 2) * ((m + 1)! : ℂ) := by
    rw [show m + 3 = (m + 1) + 1 + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]
    push_cast; ring
  rw [hf3] at h
  have hfac : ((m + 1)! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hm2 : ((m : ℂ) + 2) ≠ 0 := by exact_mod_cast (by omega : m + 2 ≠ 0)
  unfold lambertD at h ⊢
  push_cast at h ⊢
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hfac hm2) (two_ne_zero (α := ℂ)))
  linear_combination -h

/-- **DLMF 4.13.9_2** (values): `d₀ = −1`, `d₁ = √2`, `d₂ = −2/3`, `d₃ = (11/36)√2`,
`d₄ = −43/135`. -/
theorem dlmf_4_13_9_2 : lambertD 0 = -1 ∧ lambertD 1 = (√2 : ℝ) ∧ lambertD 2 = -2 / 3 ∧
    lambertD 3 = 11 / 36 * (√2 : ℝ) ∧ lambertD 4 = -43 / 135 := by
  have d0 : lambertD 0 = -1 := by simp [lambertD, tcoef, vD_zero]
  have d1 := lambertD_one
  have hs : ((√2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hs0 : ((√2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have d2 : lambertD 2 = -2 / 3 := by
    have h := dlmf_4_13_9_2_rec 1 le_rfl
    rw [show Finset.Icc 1 (1 - 1) = ∅ by rfl, sum_empty, sum_empty] at h
    rw [d1] at h
    apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (3 : ℂ) ≠ 0) hs0)
    push_cast at h; linear_combination h
  have d3 : lambertD 3 = 11 / 36 * (√2 : ℝ) := by
    have h := dlmf_4_13_9_2_rec 2 (by norm_num)
    rw [show Finset.Icc 1 (2 - 1) = {1} by rfl, sum_singleton, sum_singleton] at h
    rw [d1, d2] at h
    apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) hs0)
    push_cast at h; linear_combination h - 2 / 9 * hs
  have d4 : lambertD 4 = -43 / 135 := by
    have h := dlmf_4_13_9_2_rec 3 (by norm_num)
    rw [show Finset.Icc 1 (3 - 1) = {1, 2} by rfl, sum_pair (by norm_num),
      sum_pair (by norm_num)] at h
    norm_num at h
    rw [d1, d2, d3] at h
    apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (5 : ℂ) ≠ 0) hs0)
    linear_combination h
  exact ⟨d0, d1, d2, d3, d4⟩

/-! ### 4.13.9_1 -/

/-- The principal square root lies in `ℜp > 0` or on the upper imaginary axis. -/
theorem sqrt_region (x : ℂ) :
    0 < (x ^ (1 / 2 : ℂ)).re ∨ ((x ^ (1 / 2 : ℂ)).re = 0 ∧ 0 ≤ (x ^ (1 / 2 : ℂ)).im) := by
  by_cases hx : x = 0
  · right; simp [hx]
  rw [cpow_def_of_ne_zero hx, exp_re, exp_im]
  have him : (log x * (1 / 2)).im = arg x / 2 := by simp [log_im]; ring
  rw [him]
  have h1 := neg_pi_lt_arg x
  have h2 := arg_le_pi x
  rcases h2.lt_or_eq with h | h
  · left
    exact mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩)
  · right
    rw [h, Real.cos_pi_div_two, Real.sin_pi_div_two]
    exact ⟨by simp, by simp [(Real.exp_pos _).le]⟩

theorem vD_sqrt {z : ℂ} : vD ((exp 1 * z + 1) ^ (1 / 2 : ℂ)) = lambertW 0 z := by
  set p := (exp 1 * z + 1) ^ (1 / 2 : ℂ)
  have hp2 : p ^ 2 = exp 1 * z + 1 := by
    rw [← cpow_natCast, ← cpow_mul]
    · norm_num
    · simp [log_im]; linarith [neg_pi_lt_arg (exp 1 * z + 1), Real.pi_pos]
    · simp [log_im]; linarith [arg_le_pi (exp 1 * z + 1), Real.pi_pos]
  have hz : zD p = z := by
    rw [zD, hp2, ofReal_exp]; push_cast
    rw [add_sub_cancel_right, mul_comm, ← mul_assoc, ← exp_add]; norm_num
  rw [vD, hz]
  exact ite_eq_left_of_eq_true _ _ (eq_true (sqrt_region _))

/-- **DLMF 4.13.9_1**: `W₀(z) = ∑ dₙ (ez + 1)^{n/2}`, `|ez + 1| < 1`. -/
theorem dlmf_4_13_9_1 {z : ℂ} (hz : ‖exp 1 * z + 1‖ < 1) :
    HasSum (fun n : ℕ => lambertD n * (exp 1 * z + 1) ^ ((n : ℂ) / 2)) (lambertW 0 z) := by
  set p := (exp 1 * z + 1) ^ (1 / 2 : ℂ)
  have hp : ‖p‖ < 1 := by
    have h : ‖p‖ ^ 2 = ‖exp 1 * z + 1‖ := by
      rw [← norm_pow, ← cpow_natCast, ← cpow_mul]
      · norm_num
      · simp [log_im]; linarith [neg_pi_lt_arg (exp 1 * z + 1), Real.pi_pos]
      · simp [log_im]; linarith [arg_le_pi (exp 1 * z + 1), Real.pi_pos]
    nlinarith [norm_nonneg p]
  have h := hasSum_tcoef differentiableOn_vD hp
  rw [vD_sqrt] at h
  convert h using 2 with n
  rw [lambertD, div_eq_mul_one_div, cpow_nat_mul]

end Azurite.DLMF
