/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the
Apache License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section13BranchPoint
import Azurite.DLMF.Chapter4.Section13Taylor

/-!
# DLMF §4.13: the expansion 4.13.6 about the branch point `−e⁻¹`

`uT t = W(−e^{−1−t²/2})` glues `W₀` (`ℜt > 0`), `W₁` and `W_{−1}` (`ℜt < 0`) into one function
which is analytic on `|t| < 2√π` (`differentiableOn_uT`): it is continuous
(`continuousAt_lambertGlue`), hence analytic off `t = 0` by the inverse function theorem and at
`t = 0` by the removable singularity theorem. With `q = 1 + uT`, `(q²)′ = −2t·uT`, and the
Leibniz rule gives the coefficient recurrence.

* 4.13.6: `dlmf_4_13_6` (all `|t| < 2√π`), `dlmf_4_13_6_W0` (`t ≥ 0`), `dlmf_4_13_6_Wm1`
  (`t ≤ 0`, `W_{−1}(x + 0i)`; equal to `W₁(x − 0i)` by `tendsto_lambertW_one_below`).
* 4.13.7: `dlmf_4_13_7`; 4.13.8: `dlmf_4_13_8`.

DLMF's sign `(−1)^{n−1}` is written `(−1)^{n+1}` (the same integer power; `n − 1` truncates in
`ℕ`).
-/

open Set Filter Topology Complex Finset
open scoped Real Nat

namespace Azurite.DLMF

/-! ### Taylor coefficients and the Leibniz rule for squares -/

/-- The Taylor coefficient `G^{(k)}(0)/k!`. -/
noncomputable def tcoef (G : ℂ → ℂ) (k : ℕ) : ℂ := iteratedDeriv k G 0 / k !

theorem iteratedDeriv_eq_tcoef (G : ℂ → ℂ) (k : ℕ) :
    iteratedDeriv k G 0 = k ! * tcoef G k := by
  have : (k ! : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  rw [tcoef]; field_simp

theorem hasSum_tcoef {G : ℂ → ℂ} {R : ℝ} (hG : DifferentiableOn ℂ G (Metric.ball 0 R)) {p : ℂ}
    (hp : ‖p‖ < R) : HasSum (fun n => tcoef G n * p ^ n) (G p) := by
  have h := Complex.hasSum_taylorSeries_on_ball hG (by simpa using hp)
  simp only [sub_zero, smul_eq_mul] at h
  convert h using 2 with n
  rw [tcoef]; ring

theorem iteratedDeriv_mul_self_zero {G : ℂ → ℂ} {m : ℕ} (hG : ContDiffAt ℂ m G 0) :
    iteratedDeriv m (fun p => G p * G p) 0 =
      m ! * ∑ i ∈ range (m + 1), tcoef G i * tcoef G (m - i) := by
  rw [iteratedDeriv_fun_mul hG hG, mul_sum]
  refine sum_congr rfl fun i hi => ?_
  have hi' : i ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hi)
  rw [iteratedDeriv_eq_tcoef G i, iteratedDeriv_eq_tcoef G (m - i)]
  have h' : ((m.choose i : ℕ) : ℂ) * (i ! : ℂ) * ((m - i)! : ℂ) = (m ! : ℂ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi'
  linear_combination (tcoef G i * tcoef G (m - i)) * h'

theorem tcoef_const_add (G : ℂ → ℂ) {k : ℕ} (hk : 0 < k) (c : ℂ) :
    tcoef (fun p => c + G p) k = tcoef G k := by
  rw [tcoef, tcoef, iteratedDeriv_const_add hk]

/-- Dropping the vanishing end terms of a Cauchy square. -/
theorem sum_range_mul_eq_Icc {g : ℕ → ℂ} (hg : g 0 = 0) (N : ℕ) :
    ∑ i ∈ range (N + 1), g i * g (N - i) = ∑ i ∈ Icc 1 (N - 1), g i * g (N - i) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [hg]
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  rw [sum_range_succ, sum_range_succ', Nat.sub_self, hg]
  simp only [mul_zero, zero_mul, add_zero, Nat.sub_zero, Nat.add_sub_cancel]
  rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  refine sum_congr rfl fun i _ => ?_
  rw [add_comm 1 i]

/-- Splitting off the two end terms `2 g₁ g_{N−1}` (`N ≥ 3`). -/
theorem sum_Icc_mul_split (g : ℕ → ℂ) (M : ℕ) :
    ∑ i ∈ Icc 1 (M + 2), g i * g (M + 3 - i) =
      2 * g 1 * g (M + 2) + ∑ i ∈ Icc 2 (M + 1), g i * g (M + 3 - i) := by
  rw [sum_Icc_succ_top (by omega), Icc_eq_cons_Ioc (by omega), sum_cons,
    ← Finset.Icc_add_one_left_eq_Ioc]
  rw [show M + 3 - 1 = M + 2 by omega, show M + 3 - (M + 1 + 1) = 1 by omega]
  ring_nf

/-! ### The function `W(−e^{−1−t²/2})` -/

/-- The argument `−e^{−1−t²/2}` of 4.13.6. -/
noncomputable def zT (t : ℂ) : ℂ := -exp (-1 - t ^ 2 / 2)

/-- `W(−e^{−1−t²/2})` on the sheet selected by `t` (4.13.6). -/
noncomputable def uT (t : ℂ) : ℂ := lambertGlue t (zT t)

theorem zT_arg (t : ℂ) :
    (-1 - t ^ 2 / 2 : ℂ) = ⟨-1 - (t.re ^ 2 - t.im ^ 2) / 2, -(t.re * t.im)⟩ := by
  apply Complex.ext
  · simp [sq]
  · simp [sq]; ring

theorem zT_re (t : ℂ) :
    (zT t).re = -Real.exp (-1 - (t.re ^ 2 - t.im ^ 2) / 2) * Real.cos (t.re * t.im) := by
  rw [zT, neg_re, zT_arg, exp_re]; simp [Real.cos_neg]

theorem zT_im (t : ℂ) :
    (zT t).im = Real.exp (-1 - (t.re ^ 2 - t.im ^ 2) / 2) * Real.sin (t.re * t.im) := by
  rw [zT, neg_im, zT_arg, exp_im]; simp [Real.sin_neg]

theorem zT_ofReal (r : ℝ) : zT r = ((-Real.exp (-1 - r ^ 2 / 2) : ℝ) : ℂ) := by
  rw [zT]; push_cast; rfl

theorem zT_zero : zT 0 = ((-Real.exp (-1) : ℝ) : ℂ) := by
  rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) by simp, zT_ofReal]; simp

theorem abs_re_mul_im_lt {t : ℂ} (ht : ‖t‖ < 2 * √π) : |t.re * t.im| < 2 * π := by
  have h1 : t.re ^ 2 + t.im ^ 2 < 4 * π := by
    have h := sq_lt_sq' (by linarith [norm_nonneg t, Real.sqrt_nonneg π]) ht
    rw [mul_pow, Real.sq_sqrt Real.pi_pos.le, ← Complex.normSq_eq_norm_sq, normSq_apply] at h
    nlinarith
  rw [abs_lt]; constructor <;> nlinarith [sq_nonneg (t.re + t.im), sq_nonneg (t.re - t.im)]

/-- If `zT t` is real (and `|t| < 2√π`), then either `ℜt ℑt = 0` or `zT t > 0`. -/
theorem zT_real_cases {t : ℂ} (ht : ‖t‖ < 2 * √π) (him : (zT t).im = 0) :
    t.re * t.im = 0 ∨ 0 < (zT t).re := by
  have hb := abs_re_mul_im_lt ht
  rw [zT_im] at him
  have hs : Real.sin (t.re * t.im) = 0 := by
    rcases mul_eq_zero.mp him with h | h
    · exact absurd h (Real.exp_pos _).ne'
    · exact h
  have hc : Real.cos (t.re * t.im) = 1 ∨ Real.cos (t.re * t.im) = -1 := by
    have := Real.sin_sq_add_cos_sq (t.re * t.im)
    rw [hs] at this
    have : (Real.cos (t.re * t.im) - 1) * (Real.cos (t.re * t.im) + 1) = 0 := by
      linear_combination this
    rcases mul_eq_zero.mp this with h | h
    · left; linarith
    · right; linarith
  rcases hc with hc | hc
  · left
    exact (Real.cos_eq_one_iff_of_lt_of_lt (by linarith [(abs_lt.mp hb).1])
      (abs_lt.mp hb).2).mp hc
  · right; rw [zT_re, hc]; simp [Real.exp_pos]

theorem zT_eq_neg_exp {t : ℂ} (ht : ‖t‖ < 2 * √π) (h : zT t = ((-Real.exp (-1) : ℝ) : ℂ)) :
    t = 0 := by
  have him : (zT t).im = 0 := by rw [h, ofReal_im]
  have hre : (zT t).re = -Real.exp (-1) := by rw [h, ofReal_re]
  rcases zT_real_cases ht him with h0 | h0
  · rw [zT_re, h0, Real.cos_zero, mul_one, neg_inj] at hre
    have ha := Real.exp_injective hre
    have h2 : t.re ^ 2 = t.im ^ 2 := by linarith
    have h3 : t.re = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact h
      · rw [h] at h2; simpa using h2
    have h4 : t.im = 0 := by rw [h3] at h2; simpa using h2.symm
    exact Complex.ext h3 h4
  · rw [hre] at h0; linarith [Real.exp_pos (-1)]

theorem imSign_of_abs_lt_pi {t : ℂ} (h : |t.re * t.im| < π) : ImSign t (zT t) := by
  obtain ⟨h1, h2⟩ := abs_lt.mp h
  refine ⟨fun hb => ?_, fun hb => ?_⟩
  · rw [zT_im]
    exact mul_nonneg (Real.exp_pos _).le (Real.sin_nonneg_of_nonneg_of_le_pi hb h2.le)
  · rw [zT_im]
    exact mul_neg_of_pos_of_neg (Real.exp_pos _) (Real.sin_neg_of_neg_of_neg_pi_lt hb h1)

theorem continuousAt_uT {t₀ : ℂ} (ht : ‖t₀‖ < 2 * √π) : ContinuousAt uT t₀ := by
  have hcZ : Continuous zT := by unfold zT; fun_prop
  refine continuousAt_lambertGlue hcZ.continuousAt (fun hr => ?_) (fun hr hi => ?_)
    (fun hr hi => ?_) (fun hr hi => ?_) (fun h => by rw [h, zT_zero]) (fun _ => ?_)
  · rintro ⟨him, hle⟩
    rcases zT_real_cases ht him with h | h
    · have hi : t₀.im = 0 := by
        rcases mul_eq_zero.mp h with h | h
        · linarith
        · exact h
      rw [zT_re, h, hi, Real.cos_zero, mul_one] at hle
      have : Real.exp (-1 - (t₀.re ^ 2 - 0 ^ 2) / 2) < Real.exp (-1) :=
        Real.exp_lt_exp.mpr (by nlinarith)
      linarith
    · linarith [Real.exp_pos (-1)]
  · rw [mem_slitPlane_iff]
    by_contra hc; push Not at hc
    rcases zT_real_cases ht hc.2 with h | h
    · rcases mul_eq_zero.mp h with h | h
      · linarith
      · exact hi h
    · linarith [hc.1]
  · refine ⟨-Real.exp (-1 - t₀.re ^ 2 / 2), ?_, ?_, ?_⟩
    · have : Real.exp (-1 - t₀.re ^ 2 / 2) < Real.exp (-1) :=
        Real.exp_lt_exp.mpr (by nlinarith)
      linarith
    · linarith [Real.exp_pos (-1 - t₀.re ^ 2 / 2)]
    · have ht0 : t₀ = (t₀.re : ℂ) := Complex.ext (by simp) (by simp [hi])
      conv_lhs => rw [ht0]
      rw [zT_ofReal]
  · refine ⟨-Real.exp (-1 + t₀.im ^ 2 / 2), ?_, ?_⟩
    · have : Real.exp (-1) < Real.exp (-1 + t₀.im ^ 2 / 2) :=
        Real.exp_lt_exp.mpr (by have := pow_pos (abs_pos.mpr hi) 2; rw [sq_abs] at this; linarith)
      linarith
    · have ht0 : t₀ = (t₀.im : ℂ) * I := Complex.ext (by simp [hr]) (by simp)
      conv_lhs => rw [ht0]
      rw [zT, show (-1 - ((t₀.im : ℂ) * I) ^ 2 / 2) = ((-1 + t₀.im ^ 2 / 2 : ℝ) : ℂ) by
        push_cast; ring_nf; rw [I_sq]; ring, ← ofReal_exp]
      push_cast; ring
  · have hb : Tendsto (fun t : ℂ => t.re * t.im) (𝓝 t₀) (𝓝 (t₀.re * t₀.im)) :=
      (continuous_re.mul continuous_im).tendsto t₀
    have h0 : t₀.re * t₀.im = 0 := by
      rcases ‹t₀.re = 0 ∨ t₀.im = 0› with h | h <;> simp [h]
    rw [h0] at hb
    filter_upwards [hb.eventually (Metric.ball_mem_nhds 0 Real.pi_pos)] with t ht
    exact imSign_of_abs_lt_pi (by simpa [Real.dist_eq] using ht)

theorem differentiableOn_uT : DifferentiableOn ℂ uT (Metric.ball 0 (2 * √π)) := by
  refine differentiableOn_lambertGlue (Z := zT) Metric.isOpen_ball
    (Metric.mem_ball_self (by positivity)) (by unfold zT; fun_prop)
    (fun t ht => continuousAt_uT (by simpa using ht))
    fun t ht h => zT_eq_neg_exp (by simpa using ht) h

theorem uT_zero : uT 0 = -1 := by
  rw [uT, zT_zero]
  simp only [lambertGlue, zero_re, zero_im, lt_irrefl, le_refl, and_self, or_true, ↓reduceIte]
  exact dlmf_4_13_2.1

theorem uT_ofReal_pos {r : ℝ} (hr : 0 < r) :
    uT r = (lambertW0 (-Real.exp (-1 - r ^ 2 / 2)) : ℂ) := by
  have hx : -Real.exp (-1) < -Real.exp (-1 - r ^ 2 / 2) := by
    have : Real.exp (-1 - r ^ 2 / 2) < Real.exp (-1) := Real.exp_lt_exp.mpr (by nlinarith)
    linarith
  rw [uT, zT_ofReal]
  simp only [lambertGlue, ofReal_re, hr, true_or, ↓reduceIte]
  exact lambertW_zero_ofReal hx.le

theorem uT_ofReal_nonpos {r : ℝ} (hr : r ≤ 0) :
    uT r = lambertW (-1) ((-Real.exp (-1 - r ^ 2 / 2) : ℝ) : ℂ) := by
  rcases hr.lt_or_eq with hr | rfl
  · rw [uT, zT_ofReal]
    simp [lambertGlue, not_lt.mpr hr.le, hr.ne]
  · rw [show ((0 : ℝ) : ℂ) = 0 by simp, uT_zero, show (-1 - (0 : ℝ) ^ 2 / 2) = -1 by norm_num,
      dlmf_4_13_2.2.1]

/-! ### The differential equation `(1 + u)u′ = −t u` -/

theorem hasDerivAt_uT {t : ℂ} (ht : ‖t‖ < 2 * √π) : HasDerivAt uT (deriv uT t) t :=
  (differentiableOn_uT.differentiableAt
    (Metric.isOpen_ball.mem_nhds (by simpa using ht))).hasDerivAt

theorem uT_ode {t : ℂ} (ht : ‖t‖ < 2 * √π) : deriv uT t * (1 + uT t) = -t * uT t := by
  have hu := hasDerivAt_uT ht
  have h1 : HasDerivAt (fun t => uT t * exp (uT t))
      (deriv uT t * exp (uT t) + uT t * (exp (uT t) * deriv uT t)) t := hu.mul hu.cexp
  have hfun : (fun t => uT t * exp (uT t)) = zT := funext fun t => lambertGlue_mul_exp t (zT t)
  rw [hfun] at h1
  have h2a : HasDerivAt (fun x : ℂ => -1 - x ^ 2 / 2) (-t) t := by
    have := ((hasDerivAt_pow 2 t).div_const 2).const_sub (-1)
    convert this using 1; push_cast; ring
  have h2 : HasDerivAt zT (-(exp (-1 - t ^ 2 / 2) * -t)) t := h2a.cexp.neg
  have h := h1.unique h2
  have hz : uT t * exp (uT t) = -exp (-1 - t ^ 2 / 2) := lambertGlue_mul_exp t (zT t)
  have he := exp_ne_zero (uT t)
  apply mul_right_cancel₀ he
  linear_combination h + t * hz

/-- The Leibniz form of the ODE: `(n + 1)! ∑ qᵢ q_{n+1−i} = −2n u^{(n−1)}(0)`, `q = 1 + u`. -/
theorem uT_rec (n : ℕ) :
    ((n + 1)! : ℂ) * ∑ i ∈ range (n + 2), tcoef (fun t => 1 + uT t) i *
      tcoef (fun t => 1 + uT t) (n + 1 - i) = n * (-2 * iteratedDeriv (n - 1) uT 0) := by
  have h0 : (0 : ℂ) ∈ Metric.ball 0 (2 * √π) := Metric.mem_ball_self (by positivity)
  have han : AnalyticAt ℂ uT 0 :=
    differentiableOn_uT.analyticAt (Metric.isOpen_ball.mem_nhds h0)
  have hq : ContDiffAt ℂ (n + 1) (fun t => 1 + uT t) 0 := contDiffAt_const.add han.contDiffAt
  rw [← iteratedDeriv_mul_self_zero hq, iteratedDeriv_succ']
  have hev : deriv (fun t => (1 + uT t) * (1 + uT t)) =ᶠ[𝓝 0] fun t => t * (-2 * uT t) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds h0] with t ht
    have ht' : ‖t‖ < 2 * √π := by simpa using ht
    have hu := hasDerivAt_uT ht'
    have hQ : HasDerivAt (fun t => (1 + uT t) * (1 + uT t)) _ t :=
      (hu.const_add 1).mul (hu.const_add 1)
    rw [hQ.deriv]
    linear_combination 2 * uT_ode ht'
  rw [hev.iteratedDeriv_eq, iteratedDeriv_id_mul_zero (contDiffAt_const.mul han.contDiffAt),
    iteratedDeriv_const_mul_field]

/-! ### The coefficients `c_n` -/

/-- **DLMF 4.13.6** coefficients: `c_n = (−1)^{n+1} u^{(n)}(0)/n!`. -/
noncomputable def lambertC (n : ℕ) : ℂ := (-1) ^ (n + 1) * tcoef uT n

theorem tcoef_uT_eq (n : ℕ) : tcoef uT n = (-1) ^ (n + 1) * lambertC n := by
  rw [lambertC, ← mul_assoc, ← pow_add, show n + 1 + (n + 1) = 2 * (n + 1) by ring, pow_mul]
  simp

theorem tcoef_q_zero : tcoef (fun t => 1 + uT t) 0 = 0 := by
  simp [tcoef, uT_zero]

theorem tcoef_q (n : ℕ) (hn : 0 < n) : tcoef (fun t => 1 + uT t) n = tcoef uT n :=
  tcoef_const_add uT hn 1

theorem tcoef_uT_one_sq : tcoef uT 1 ^ 2 = 1 := by
  have h := uT_rec 1
  rw [sum_range_mul_eq_Icc tcoef_q_zero] at h
  simp only [show 1 + 1 - 1 = 1 by rfl, Finset.Icc_self, sum_singleton, Nat.sub_self,
    iteratedDeriv_zero, uT_zero, tcoef_q 1 one_pos] at h
  norm_num at h
  linear_combination h

theorem tcoef_uT_one : tcoef uT 1 = 1 := by
  set a := tcoef uT 1
  have ha : a = deriv uT 0 := by simp [a, tcoef, iteratedDeriv_one]
  have hd : HasDerivAt uT a 0 := by
    rw [ha]; exact hasDerivAt_uT (by simp; positivity)
  -- the right-hand slopes along `ℝ` have positive real part
  have hr := (hd.comp_ofReal (z := 0)).tendsto_slope_zero_right
  have hre : 0 ≤ a.re := by
    refine ge_of_tendsto ((continuous_re.tendsto a).comp (by simpa using hr)) ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr0 : 0 < r)
    simp only [Function.comp_apply, uT_zero, ← ofReal_inv, re_ofReal_mul, sub_neg_eq_add]
    rw [uT_ofReal_pos hr0, add_re, ofReal_re, one_re]
    have hx : -Real.exp (-1) < -Real.exp (-1 - r ^ 2 / 2) := by
      have : Real.exp (-1 - r ^ 2 / 2) < Real.exp (-1) := Real.exp_lt_exp.mpr (by nlinarith)
      linarith
    have := lambertW0_gt hx
    exact mul_nonneg (inv_pos.mpr hr0).le (by linarith)
  have h2 : (a - 1) * (a + 1) = 0 := by linear_combination tcoef_uT_one_sq
  rcases mul_eq_zero.mp h2 with h | h
  · linear_combination h
  · have : a = -1 := by linear_combination h
    rw [this] at hre; norm_num at hre

/-- **DLMF 4.13.8**: `c_n = c_{n−1}/(n + 1) − ½ ∑_{k=2}^{n−1} c_k c_{n+1−k}`, `n ≥ 2`. -/
theorem dlmf_4_13_8 (n : ℕ) (hn : 2 ≤ n) :
    lambertC n = lambertC (n - 1) / (n + 1) -
      1 / 2 * ∑ k ∈ Icc 2 (n - 1), lambertC k * lambertC (n + 1 - k) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h := uT_rec (m + 2)
  rw [sum_range_mul_eq_Icc tcoef_q_zero, show m + 2 + 1 - 1 = m + 2 by omega] at h
  have hq : ∀ i ∈ Finset.Icc 1 (m + 2), tcoef (fun t => 1 + uT t) i *
      tcoef (fun t => 1 + uT t) (m + 2 + 1 - i) =
      (-1) ^ (m + 1) * (lambertC i * lambertC (m + 3 - i)) := by
    intro i hi
    obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.mp hi
    rw [tcoef_q i (by omega), tcoef_q _ (by omega), tcoef_uT_eq, tcoef_uT_eq,
      show m + 2 + 1 - i = m + 3 - i by omega]
    have hp : ((-1 : ℂ) ^ (i + 1)) * (-1) ^ (m + 3 - i + 1) = (-1) ^ (m + 1) := by
      rw [← pow_add, show i + 1 + (m + 3 - i + 1) = m + 1 + 2 * 2 by omega, pow_add, pow_mul]
      norm_num
    linear_combination (lambertC i * lambertC (m + 3 - i)) * hp
  rw [sum_congr rfl hq, ← mul_sum, sum_Icc_mul_split] at h
  have hc1 : lambertC 1 = 1 := by rw [lambertC, tcoef_uT_one]; norm_num
  rw [hc1, show m + 2 - 1 = m + 1 by omega, iteratedDeriv_eq_tcoef, tcoef_uT_eq] at h
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 + 1 = m + 3 by omega]
  have hf : ((m + 2 + 1)! : ℂ) = (m + 3) * (m + 2) * ((m + 1)! : ℂ) := by
    rw [show m + 2 + 1 = (m + 1) + 1 + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]
    push_cast; ring
  rw [hf] at h
  have hsgn : ((-1 : ℂ) ^ (m + 1 + 1)) = -(-1) ^ (m + 1) := by rw [pow_succ]; ring
  rw [hsgn] at h
  have hfac : ((m + 1)! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hs : ((-1 : ℂ) ^ (m + 1)) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hm2 : ((m : ℂ) + 2) ≠ 0 := by exact_mod_cast (by omega : m + 2 ≠ 0)
  have hm3 : ((m : ℂ) + 3) ≠ 0 := by exact_mod_cast (by omega : m + 3 ≠ 0)
  have hm3' : (((m + 2 : ℕ) : ℂ) + 1) = (m : ℂ) + 3 := by push_cast; ring
  rw [hm3']
  field_simp
  push_cast at h ⊢
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hfac hs) hm2)
  linear_combination h

/-- **DLMF 4.13.7**: `c₀ = 1`, `c₁ = 1`, `c₂ = 1/3`, `c₃ = 1/36`, `c₄ = −1/270`. -/
theorem dlmf_4_13_7 : lambertC 0 = 1 ∧ lambertC 1 = 1 ∧ lambertC 2 = 1 / 3 ∧
    lambertC 3 = 1 / 36 ∧ lambertC 4 = -1 / 270 := by
  have c0 : lambertC 0 = 1 := by simp [lambertC, tcoef, uT_zero]
  have c1 : lambertC 1 = 1 := by rw [lambertC, tcoef_uT_one]; norm_num
  have c2 : lambertC 2 = 1 / 3 := by
    rw [dlmf_4_13_8 2 le_rfl]; simp [c1]; norm_num
  have c3 : lambertC 3 = 1 / 36 := by
    rw [dlmf_4_13_8 3 (by norm_num)]; simp [c2]; norm_num
  have c4 : lambertC 4 = -1 / 270 := by
    rw [dlmf_4_13_8 4 (by norm_num)]
    rw [show (4 - 1 : ℕ) = 2 + 1 by rfl, sum_Icc_succ_top (by norm_num), Finset.Icc_self,
      sum_singleton]
    simp [c2, c3]; norm_num
  exact ⟨c0, c1, c2, c3, c4⟩

/-! ### 4.13.6 -/

/-- **DLMF 4.13.6**: `W(−e^{−1−t²/2}) = ∑ (−1)^{n−1} c_n tⁿ` on `|t| < 2√π` (on the sheet selected
by `t`, see `uT`). -/
theorem dlmf_4_13_6 {t : ℂ} (ht : ‖t‖ < 2 * √π) :
    HasSum (fun n => (-1) ^ (n + 1) * lambertC n * t ^ n) (uT t) := by
  convert hasSum_tcoef differentiableOn_uT ht using 2 with n
  rw [tcoef_uT_eq]

/-- **DLMF 4.13.6** for `W₀`, `0 ≤ t < 2√π`. -/
theorem dlmf_4_13_6_W0 {t : ℝ} (h0 : 0 ≤ t) (ht : t < 2 * √π) :
    HasSum (fun n => (-1) ^ (n + 1) * lambertC n * (t : ℂ) ^ n)
      (lambertW 0 ((-Real.exp (-1 - t ^ 2 / 2) : ℝ) : ℂ)) := by
  have h := dlmf_4_13_6 (t := t) (by rw [norm_real, Real.norm_eq_abs, abs_of_nonneg h0]; exact ht)
  rcases h0.lt_or_eq with hp | rfl
  · have : Real.exp (-1 - t ^ 2 / 2) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by nlinarith)
    rw [lambertW_zero_ofReal (by linarith)]
    rwa [uT_ofReal_pos hp] at h
  · rw [show (-1 - (0 : ℝ) ^ 2 / 2) = -1 by norm_num, dlmf_4_13_2.1]
    rw [show ((0 : ℝ) : ℂ) = 0 by simp, uT_zero] at h
    simpa using h

/-- **DLMF 4.13.6** for `W_{±1}(x ∓ 0i)` (the real branch `≤ −1`), `−2√π < t ≤ 0`. -/
theorem dlmf_4_13_6_Wm1 {t : ℝ} (h0 : t ≤ 0) (ht : -(2 * √π) < t) :
    HasSum (fun n => (-1) ^ (n + 1) * lambertC n * (t : ℂ) ^ n)
      (lambertW (-1) ((-Real.exp (-1 - t ^ 2 / 2) : ℝ) : ℂ)) := by
  have h := dlmf_4_13_6 (t := t)
    (by rw [norm_real, Real.norm_eq_abs, abs_of_nonpos h0]; linarith)
  rwa [uT_ofReal_nonpos h0] at h

end Azurite.DLMF
