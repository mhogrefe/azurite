/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter2.Section11ExpintAsymp
import Azurite.DLMF.Chapter2.Section4Inverse
import Azurite.DLMF.Chapter5.Section12
import Azurite.DLMF.Chapter6.Section7Aux

/-!
# DLMF §6.12(i): asymptotic expansions of the exponential and logarithmic integrals

Formalizations of <https://dlmf.nist.gov/6.12.i>.

## Main results

* `genExpInt_one_eq_E1Gen`: §2.11(ii)'s `E_p` at `p = 1` is §6.4's continuation `E1Gen` of `E₁`.
* `dlmf_6_12_1`: `E₁(z) = e^{−z}/z ∑_{s<n} (−1)^s s!/z^s + O(|e^{−z}|/|z|^{n+1})` for
  `|ph z| ≤ 3π/2 − δ` on the Riemann surface (from DLMF 2.11.6); `dlmf_6_12_1_principal` for
  the principal value.
* The remainder bounds: `dlmf_6_12_1_remainder_right` (`|ph z| ≤ π/2`: at most the first
  neglected term), `dlmf_6_12_1_remainder_real` (`ph z = 0`: also of the same sign),
  `dlmf_6_12_1_remainder_left` (`z` off the real axis, in particular `½π ≤ |ph z| < π`: at most
  `csc |ph z|` times the first neglected term).  All three come from the exact remainder
  `(−1)ⁿ n! ∫_z^∞ e^{−t} t^{−n−1} dt` (`E1Gen_sub_e1Asymp`) on a ray from `z` that stays at
  distance `≥ |z|` from the origin: horizontal for `ℜz ≥ 0`, perpendicular to `z` otherwise.
* `dlmf_6_12_2`: `Ei(x) = eˣ/x ∑_{s<n} s!/x^s + O(eˣ/x^{n+1})`, via
  `Ei(x) = −E₁(x e^{πi}) − πi` (`Ei_eq_E1Gen`).
* `dlmf_6_12_li`: `li(x) = x/ln x ∑_{s<n} s!/(ln x)^s + O(x/(ln x)^{n+1})` (6.2.8 and 6.12.2).

* `dlmf_6_12_2_remainder`: the remainder of 6.12.2 after `n` terms is at most `1 + χ(n+1)` times
  the next term, `χ` of 9.7.3 (`olverChi`).  Proof after Olver (1997b, Ch. 6, Ex. 13.5): one more
  partial integration leaves `(n+1)! ∫ e^{−t} t^{−n−2} dt` from `x e^{πi}` (`Ei_sub_eiAsymp_eq`),
  bounded on the vertical ray from `−x` as the limit of tilted rays (`norm_eiP_upper_le`) by
  `eˣ x^{−n−1} ∫_0^∞ (1 + σ²)^{−(n+2)/2} dσ = eˣ x^{−n−1} χ(n+1)/(n+1)` (Olver's Lemma 13.1,
  `integral_one_add_sq_rpow_eq_olverChi`, from the Beta integral 5.12.3).
-/

open Complex Filter Topology Set MeasureTheory
open scoped Real Nat

namespace Azurite.DLMF

/-! ### `E₁ = E_1` on the Riemann surface of the logarithm -/

/-- §2.11(ii)'s generalized exponential integral `E_p` at `p = 1` is §6.4's analytic continuation
`E1Gen` of `E₁`: both are entire with derivative `−exp(−eʷ)` and vanish as `w → +∞`. -/
theorem genExpInt_one_eq_E1Gen : genExpInt 1 = E1Gen := by
  have h1 : genExpInt 1 = eiP 1 := funext fun w => by simp [genExpInt]
  set f : ℂ → ℂ := fun w => eiP 1 w - E1Gen w with hf
  have hd : ∀ w, HasDerivAt f 0 w := fun w => by
    refine ((hasDerivAt_eiP 1 w).sub (hasDerivAt_E1Gen w)).congr_deriv ?_
    simp [eiF]
  have hc : ∀ w, f w = f 0 := fun w =>
    is_const_of_deriv_eq_zero (fun w => (hd w).differentiableAt) (fun w => (hd w).deriv) w 0
  have hlim : Tendsto (fun x : ℝ => f x) atTop (𝓝 0) := by
    have hE : Tendsto (fun x : ℝ => E1Gen x) atTop (𝓝 0) := by
      have e : ∀ x : ℝ, E1Gen x = expIntE₁ (cexp x) := fun x =>
        dlmf_6_4_1.2.1 x (by simp [logStrip, Real.pi_pos])
      simp only [e, ← ofReal_exp]
      refine tendsto_expIntE₁_zero (r₀ := 0) (Eventually.of_forall fun x => ?_)
        (Eventually.of_forall fun x => ?_) ?_
      · exact ofReal_mem_slitPlane.2 (Real.exp_pos x)
      · rw [ofReal_re]; exact (Real.exp_pos x).le
      · simp only [ofReal_re, ofReal_im, abs_zero]
        exact tendsto_atTop_mono (fun x => le_max_right _ _) Real.tendsto_exp_atTop
    simpa [hf] using (tendsto_eiP_atTop 1).sub hE
  have hconst : f 0 = 0 := by
    have e : (fun x : ℝ => f x) = fun _ => f 0 := funext fun x => hc x
    rw [e] at hlim
    exact tendsto_nhds_unique tendsto_const_nhds hlim
  rw [h1]
  funext w
  exact sub_eq_zero.1 ((hc w).trans hconst)

/-! ### 6.12.1 -/

/-- The partial sum `e^{−z}/z ∑_{s<n} (−1)^s s!/z^s` of 6.12.1. -/
noncomputable def e1Asymp (n : ℕ) (z : ℂ) : ℂ :=
  cexp (-z) / z * ∑ s ∈ Finset.range n, (-1) ^ s * (s ! : ℂ) / z ^ s

/-- The `n`-th term `e^{−z}/z · (−1)^n n!/z^n` of 6.12.1 (the first one neglected by
`e1Asymp n`). -/
noncomputable def e1Term (n : ℕ) (z : ℂ) : ℂ := cexp (-z) / z * ((-1) ^ n * (n ! : ℂ) / z ^ n)

theorem e1Asymp_succ (n : ℕ) (z : ℂ) : e1Asymp (n + 1) z = e1Asymp n z + e1Term n z := by
  rw [e1Asymp, e1Asymp, e1Term, Finset.sum_range_succ, mul_add]

theorem norm_e1Term (n : ℕ) (z : ℂ) :
    ‖e1Term n z‖ = n ! * ‖cexp (-z)‖ / ‖z‖ ^ (n + 1) := by
  rw [e1Term, norm_mul, norm_div, norm_div, norm_mul, norm_pow, norm_pow, norm_neg, norm_one,
    one_pow, one_mul, Complex.norm_natCast, pow_succ]
  ring

/-- **DLMF 6.12.1** on the Riemann surface of the logarithm: for `z = eʷ`, `|z| ≥ 1`,
`|ph z| ≤ 3π/2 − δ`, the remainder after `n` terms is `O(|e^{−z}|/|z|^{n+1})` (DLMF 2.11.6 at
`p = 1`). -/
theorem dlmf_6_12_1 (n : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ π) :
    ∃ C : ℝ, ∀ w : ℂ, |w.im| ≤ 3 * π / 2 - δ → 0 ≤ w.re →
      ‖E1Gen w - e1Asymp n (cexp w)‖ ≤ C * (‖cexp (-cexp w)‖ / ‖cexp w‖ ^ (n + 1)) := by
  obtain ⟨C, hC⟩ := dlmf_2_11_6 1 n hδ hδ'
  refine ⟨C, fun w h1 h2 => ?_⟩
  simpa only [genExpInt_one_eq_E1Gen, ascPochhammer_eval_one, e1Asymp] using hC w h1 h2

theorem E1Gen_log {z : ℂ} (hz : z ∈ slitPlane) : E1Gen (log z) = expIntE₁ z := by
  rw [dlmf_6_4_1.2.1 _ (log_mem_logStrip hz), exp_log (slitPlane_ne_zero hz)]

/-- **DLMF 6.12.1** for the principal value: `|ph z| < π`, `|z| ≥ 1`. -/
theorem dlmf_6_12_1_principal (n : ℕ) :
    ∃ C : ℝ, ∀ z ∈ slitPlane, 1 ≤ ‖z‖ →
      ‖expIntE₁ z - e1Asymp n z‖ ≤ C * (‖cexp (-z)‖ / ‖z‖ ^ (n + 1)) := by
  obtain ⟨C, hC⟩ := dlmf_6_12_1 n (δ := π / 2) (by positivity) (by linarith [Real.pi_pos])
  refine ⟨C, fun z hz h1 => ?_⟩
  have h := hC (log z) (by rw [log_im]; linarith [abs_arg_le_pi z])
    (by rw [log_re]; exact Real.log_nonneg h1)
  rwa [E1Gen_log hz, exp_log (slitPlane_ne_zero hz)] at h

/-! ### The remainder bounds after 6.12.1 -/

/-- The exact remainder: `E₁(eʷ) − (first n terms) = (−1)ⁿ n! ∫_z^∞ e^{−t} t^{−n−1} dt`. -/
theorem E1Gen_sub_e1Asymp (n : ℕ) (w : ℂ) :
    E1Gen w - e1Asymp n (cexp w) = (-1) ^ n * n ! * eiP (n + 1) w := by
  have h := genExpInt_expansion 1 w n
  simp only [genExpInt_one_eq_E1Gen, ascPochhammer_eval_one] at h
  rw [h, e1Asymp, sub_self, zero_mul, Complex.exp_zero, one_mul, add_comm (1 : ℂ)]
  ring

/-- The ray bound of `∫_z^∞ e^{−t} t^{−n−1} dt` along `t = z(1 + σe)` when `|1 + σe| ≥ 1`. -/
theorem norm_eiP_succ_le_ray (n : ℕ) {w e : ℂ}
    (hslit : ∀ σ : ℝ, 0 ≤ σ → 1 + σ * e ∈ slitPlane) (hcb : ∀ σ : ℝ, 0 ≤ σ → 1 ≤ ‖1 + σ * e‖)
    (he : e ∈ slitPlane) (hdec : 0 < (cexp w * e).re) (harg : |w.im + arg e| < π / 2) :
    ‖eiP (n + 1) w‖ ≤ ‖e‖ * ‖cexp (-cexp w)‖ / (‖cexp w‖ ^ n * (cexp w * e).re) := by
  have h := norm_eiP_le_ray (p := n + 1) (by simp; positivity) hslit one_pos hcb he hdec harg
  have e1 : ‖cexp ((1 - (n + 1)) * w)‖ = (‖cexp w‖ ^ n)⁻¹ := by
    rw [show (1 - ((n : ℂ) + 1)) * w = -(n * w) by ring, Complex.exp_neg, norm_inv,
      Complex.exp_nat_mul, norm_pow]
  have e2 : ((n : ℂ) + 1).im = 0 := by simp
  rw [e1, e2, abs_zero, mul_zero, Real.exp_zero, Real.one_rpow, mul_one, mul_one] at h
  refine h.trans (le_of_eq ?_)
  have : ‖cexp w‖ ≠ 0 := by simp [Complex.exp_ne_zero]
  field_simp

/-- **DLMF §6.12(i)**: for `|ph z| ≤ π/2` (here `ℜz ≥ 0`, `z ≠ 0`) the remainder of 6.12.1 is
bounded in magnitude by the first neglected term. -/
theorem dlmf_6_12_1_remainder_right (n : ℕ) {z : ℂ} (hz : z ≠ 0) (hre : 0 ≤ z.re) :
    ‖expIntE₁ z - e1Asymp n z‖ ≤ ‖e1Term n z‖ := by
  have hzs : z ∈ slitPlane := by
    rw [mem_slitPlane_iff]
    by_contra! h
    exact hz (Complex.ext (le_antisymm h.1 hre) h.2)
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
  set e : ℂ := ((‖z‖⁻¹ : ℝ) : ℂ) * (starRingEnd ℂ) z with he_def
  have hre_e : e.re = ‖z‖⁻¹ * z.re := by simp [e]
  have hze : cexp (log z) * e = (‖z‖ : ℂ) := by
    rw [exp_log hz, he_def, mul_left_comm, mul_conj, normSq_eq_norm_sq]
    push_cast
    field_simp
  have hne : ‖e‖ = 1 := by
    rw [he_def, norm_mul, Complex.norm_real, Complex.norm_conj, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 hn), inv_mul_cancel₀ hn.ne']
  have hes : e ∈ slitPlane := by
    rw [mem_slitPlane_iff] at hzs ⊢
    rcases hzs with h | h
    · left; rw [hre_e]; positivity
    · right; simp [e, h, hn.ne']
  have hre1 : ∀ σ : ℝ, 0 ≤ σ → 1 ≤ (1 + σ * e).re := fun σ hσ => by
    simp only [add_re, one_re, re_ofReal_mul, hre_e]
    have : 0 ≤ σ * (‖z‖⁻¹ * z.re) := by positivity
    linarith
  have hb := norm_eiP_succ_le_ray n (w := log z) (e := e)
    (fun σ hσ => mem_slitPlane_of_re_pos (by linarith [hre1 σ hσ]))
    (fun σ hσ => (hre1 σ hσ).trans (re_le_norm _)) hes
    (by rw [hze, ofReal_re]; exact hn)
    (by
      rw [log_im, he_def, arg_real_mul _ (inv_pos.2 hn), arg_conj,
        ite_eq_right_iff.2 fun h => absurd h (mem_slitPlane_iff_arg.1 hzs).1]
      simp [Real.pi_pos])
  rw [← E1Gen_log hzs, show e1Asymp n z = e1Asymp n (cexp (log z)) by rw [exp_log hz],
    E1Gen_sub_e1Asymp, norm_e1Term, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    one_mul, Complex.norm_natCast]
  rw [hne, hze, ofReal_re, exp_log hz, one_mul] at hb
  calc (n ! : ℝ) * ‖eiP (n + 1) (log z)‖ ≤ n ! * (‖cexp (-z)‖ / (‖z‖ ^ n * ‖z‖)) := by gcongr
    _ = _ := by rw [pow_succ]; ring

theorem abs_im_eq_norm_mul_sin (z : ℂ) : |z.im| = ‖z‖ * Real.sin |arg z| := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  have hs := Complex.sin_arg z
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
  rcases abs_cases (arg z) with ⟨h, h0⟩ | ⟨h, h0⟩
  · rw [h, hs, mul_div_cancel₀ _ hn.ne']
    refine (abs_of_nonneg ?_)
    have := Real.sin_nonneg_of_nonneg_of_le_pi h0 (arg_le_pi z)
    rw [hs] at this
    exact (div_nonneg_iff.1 this).elim (fun h => h.1) fun h => absurd h.2 (not_le.2 hn)
  · rw [h, Real.sin_neg, hs, mul_neg, mul_div_cancel₀ _ hn.ne']
    refine abs_of_neg ?_
    exact (arg_neg_iff).1 h0

/-- **DLMF §6.12(i)**: for `½π ≤ |ph z| < π` the remainder of 6.12.1 is bounded in magnitude by
`csc |ph z|` times the first neglected term.  (The bound holds for every `z` off the real axis.) -/
theorem dlmf_6_12_1_remainder_left (n : ℕ) {z : ℂ} (hz : z.im ≠ 0) :
    ‖expIntE₁ z - e1Asymp n z‖ ≤ (Real.sin |arg z|)⁻¹ * ‖e1Term n z‖ := by
  have hzs : z ∈ slitPlane := mem_slitPlane_iff.2 (Or.inr hz)
  have hz0 : z ≠ 0 := slitPlane_ne_zero hzs
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz0
  -- the ray `t = z ∓ iσ|z|`, perpendicular to `z` and away from the origin
  obtain ⟨e, hes, hne, hslit, hcb, hdec, harg⟩ : ∃ e : ℂ, e ∈ slitPlane ∧ ‖e‖ = 1 ∧
      (∀ σ : ℝ, 0 ≤ σ → 1 + σ * e ∈ slitPlane) ∧ (∀ σ : ℝ, 0 ≤ σ → 1 ≤ ‖1 + σ * e‖) ∧
      (cexp (log z) * e).re = |z.im| ∧ |(log z).im + arg e| < π / 2 := by
    have hr : ∀ e : ℂ, e.re = 0 → ∀ σ : ℝ, (1 + σ * e).re = 1 := fun e he σ => by
      simp [he]
    rcases lt_or_gt_of_ne hz with h | h
    · refine ⟨I, by simp [mem_slitPlane_iff], by simp, fun σ _ => mem_slitPlane_of_re_pos
        (by rw [hr I (by simp)]; exact one_pos), fun σ _ => ?_, ?_, ?_⟩
      · rw [← hr I (by simp) σ]; exact re_le_norm _
      · rw [exp_log hz0, abs_of_neg h]; simp
      · rw [log_im, arg_I, abs_lt]
        constructor <;> linarith [neg_pi_lt_arg z, (arg_neg_iff).2 h]
    · refine ⟨-I, by simp [mem_slitPlane_iff], by simp, fun σ _ => mem_slitPlane_of_re_pos
        (by rw [hr (-I) (by simp)]; exact one_pos), fun σ _ => ?_, ?_, ?_⟩
      · rw [← hr (-I) (by simp) σ]; exact re_le_norm _
      · rw [exp_log hz0, abs_of_pos h]; simp
      · have h0 : 0 < arg z :=
          lt_of_le_of_ne (arg_nonneg_iff.2 h.le) fun h' => hz (arg_eq_zero_iff.1 h'.symm).2
        have h1 : arg z < π := (arg_lt_pi_iff).2 (Or.inr hz)
        rw [log_im, arg_neg_I, abs_lt]
        constructor <;> linarith
  have hb := norm_eiP_succ_le_ray n hslit hcb hes (by rw [hdec]; exact abs_pos.2 hz) harg
  rw [hne, hdec, exp_log hz0, one_mul, abs_im_eq_norm_mul_sin] at hb
  have hsin : 0 < Real.sin |arg z| := by
    have := abs_pos.2 hz
    rw [abs_im_eq_norm_mul_sin] at this
    exact pos_of_mul_pos_right this hn.le
  rw [← E1Gen_log hzs, show e1Asymp n z = e1Asymp n (cexp (log z)) by rw [exp_log hz0],
    E1Gen_sub_e1Asymp, norm_e1Term, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    one_mul, Complex.norm_natCast]
  calc (n ! : ℝ) * ‖eiP (n + 1) (log z)‖
      ≤ n ! * (‖cexp (-z)‖ / (‖z‖ ^ n * (‖z‖ * Real.sin |arg z|))) := by gcongr
    _ = _ := by field_simp; ring

/-- **DLMF §6.12(i)**: for `ph z = 0` the remainder of 6.12.1 is real, bounded in magnitude by the
first neglected term, and has its sign `(−1)ⁿ`. -/
theorem dlmf_6_12_1_remainder_real (n : ℕ) {x : ℝ} (hx : 0 < x) :
    ∃ r : ℝ, expIntE₁ x - e1Asymp n x = r ∧ 0 < (-1) ^ n * r ∧
      |r| ≤ n ! * Real.exp (-x) / x ^ (n + 1) := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx.ne'
  have hxs : (x : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.2 hx
  set f : ℝ → ℝ := fun σ => Real.exp (-(x * (1 + σ))) * ((1 + σ) ^ (n + 1))⁻¹ with hf
  have hfm : Measurable f := by fun_prop
  have hfint : IntegrableOn f (Ioi 0) := by
    refine ((exp_neg_integrableOn_Ioi 0 hx).const_mul (Real.exp (-x))).mono'
      hfm.aestronglyMeasurable ((ae_restrict_iff' measurableSet_Ioi).2
        (Eventually.of_forall fun σ (hσ : 0 < σ) => ?_))
    have h1 : 1 ≤ (1 + σ) ^ (n + 1) := one_le_pow₀ (by linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← Real.exp_add,
      show -x + -x * σ = -(x * (1 + σ)) by ring]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (inv_le_one_of_one_le₀ h1)
  have hJ : 0 < ∫ σ in Ioi (0 : ℝ), f σ := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun σ (hσ : 0 < σ) =>
        by positivity)) hfint]
    have : Ioi (0 : ℝ) ⊆ Function.support f ∩ Ioi 0 := fun σ (hσ : 0 < σ) =>
      ⟨(by positivity : 0 < f σ).ne', hσ⟩
    exact lt_of_lt_of_le (by simp) (measure_mono this)
  have hray := eiP_eq_ray (p := n + 1) (w := log x) (e := 1) (by simp; positivity)
    (fun σ hσ => mem_slitPlane_of_re_pos (by simp; linarith)) one_pos
    (fun σ hσ => by
      rw [mul_one, ← ofReal_one, ← ofReal_add, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith)]
      linarith)
    (by simp [mem_slitPlane_iff]) (by rw [exp_log hx0, mul_one, ofReal_re]; exact hx)
    (by rw [log_im, arg_ofReal_of_nonneg hx.le, arg_one]; simp [Real.pi_pos])
  have hint : ∫ σ in Ioi (0 : ℝ), cexp (-(cexp (log x) * (1 + σ * 1))) *
      (1 + σ * 1) ^ (-((n : ℂ) + 1)) = ((∫ σ in Ioi (0 : ℝ), f σ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun σ hσ => ?_
    have hσ' : (0 : ℝ) < 1 + σ := by simp only [mem_Ioi] at hσ; linarith
    rw [exp_log hx0, mul_one, show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by push_cast; ring,
      cpow_neg, cpow_natCast, hf]
    push_cast
    ring_nf
  have hpre : cexp ((1 - ((n : ℂ) + 1)) * log x) * 1 = (((x ^ n)⁻¹ : ℝ) : ℂ) := by
    rw [mul_one, show (1 - ((n : ℂ) + 1)) * log x = -(n * log x) by ring, Complex.exp_neg,
      Complex.exp_nat_mul, exp_log hx0]
    push_cast
    rfl
  rw [hint, hpre] at hray
  set r : ℝ := (-1) ^ n * n ! * ((x ^ n)⁻¹ * ∫ σ in Ioi (0 : ℝ), f σ) with hr
  have hR : expIntE₁ x - e1Asymp n x = r := by
    rw [← E1Gen_log hxs, show e1Asymp n x = e1Asymp n (cexp (log x)) by rw [exp_log hx0],
      E1Gen_sub_e1Asymp, hray, hr]
    push_cast
    ring
  refine ⟨r, hR, ?_, ?_⟩
  · rw [hr, show (-1 : ℝ) ^ n * ((-1) ^ n * n ! * ((x ^ n)⁻¹ * ∫ σ in Ioi (0 : ℝ), f σ)) =
        ((-1) * (-1)) ^ n * (n ! * ((x ^ n)⁻¹ * ∫ σ in Ioi (0 : ℝ), f σ)) by rw [mul_pow]; ring,
      neg_one_mul, neg_neg, one_pow, one_mul]
    positivity
  · have hb := dlmf_6_12_1_remainder_right n hx0 (by simp [hx.le])
    rw [hR, Complex.norm_real, Real.norm_eq_abs, norm_e1Term, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hx, ← ofReal_neg, ← ofReal_exp, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hb
    exact hb

/-! ### 6.12.2 and the logarithmic integral -/

/-- The partial sum `eˣ/x ∑_{s<n} s!/x^s` of 6.12.2. -/
noncomputable def eiAsymp (n : ℕ) (x : ℝ) : ℝ :=
  Real.exp x / x * ∑ s ∈ Finset.range n, (s ! : ℝ) / x ^ s

/-- `Ei(x) = −E₁(x e^{πi}) − πi` for `x > 0`, with `E₁` continued by `E1Gen`. -/
theorem Ei_eq_E1Gen {x : ℝ} (hx : 0 < x) :
    (Ei x : ℂ) = -E1Gen (log x + π * I) - π * I := by
  rw [(dlmf_6_2_7 hx).1, E1Gen, exp_log_add_pi_mul_I (ofReal_ne_zero.2 hx.ne'),
    ← ofReal_log hx.le]
  ring

theorem e1Asymp_neg (n : ℕ) {x : ℝ} (hx : 0 < x) :
    e1Asymp n (-(x : ℂ)) = -((eiAsymp n x : ℝ) : ℂ) := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx.ne'
  rw [e1Asymp, eiAsymp, neg_neg]
  push_cast
  rw [div_neg, neg_mul]
  congr 2
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [neg_pow (x : ℂ) s, mul_div_mul_left _ _ (pow_ne_zero _ (by norm_num : (-1 : ℂ) ≠ 0))]

/-- **DLMF 6.12.2**: `Ei(x) = eˣ/x ∑_{s<n} s!/x^s + O(eˣ/x^{n+1})` as `x → +∞`. -/
theorem dlmf_6_12_2 (n : ℕ) :
    ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → |Ei x - eiAsymp n x| ≤ C * (Real.exp x / x ^ (n + 1)) := by
  obtain ⟨C, hC⟩ := dlmf_6_12_1 n (δ := π / 2) (by positivity) (by linarith [Real.pi_pos])
  refine ⟨C + π * (n + 1) !, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hxc : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx0.ne'
  set w : ℂ := log x + π * I
  have hw : cexp w = -x := exp_log_add_pi_mul_I hxc
  have hlogx : log (x : ℂ) = (Real.log x : ℂ) := (ofReal_log hx0.le).symm
  have h := hC w (by simp [w, hlogx, abs_of_pos Real.pi_pos]; linarith)
    (by simp [w, hlogx, Real.log_nonneg hx])
  rw [hw, e1Asymp_neg n hx0, neg_neg, norm_neg, ← ofReal_exp, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hx0] at h
  have e : ((Ei x - eiAsymp n x : ℝ) : ℂ) =
      -(E1Gen w - -((eiAsymp n x : ℝ) : ℂ)) - π * I := by
    push_cast
    rw [Ei_eq_E1Gen hx0]
    ring
  have hA : 0 < Real.exp x / x ^ (n + 1) := by positivity
  have hfac : 1 ≤ (n + 1) ! * (Real.exp x / x ^ (n + 1)) := by
    have := Real.pow_div_factorial_le_exp x hx0.le (n + 1)
    rw [div_le_iff₀ (by positivity)] at this
    rw [mul_div_assoc', le_div_iff₀ (by positivity), one_mul, mul_comm]
    exact this
  calc |Ei x - eiAsymp n x| = ‖((Ei x - eiAsymp n x : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ‖E1Gen w - -((eiAsymp n x : ℝ) : ℂ)‖ + π := by
        rw [e]
        refine (norm_sub_le _ _).trans ?_
        rw [norm_neg, norm_mul, Complex.norm_real, norm_I, mul_one, Real.norm_eq_abs,
          abs_of_pos Real.pi_pos]
    _ ≤ C * (Real.exp x / x ^ (n + 1)) + π * ((n + 1) ! * (Real.exp x / x ^ (n + 1))) := by
        gcongr
        exact le_mul_of_one_le_right Real.pi_pos.le hfac
    _ = _ := by ring

/-- **DLMF §6.12(i)**: the asymptotic expansion of `li(x)` from 6.2.8 and 6.12.2,
`li(x) = x/ln x ∑_{s<n} s!/(ln x)^s + O(x/(ln x)^{n+1})` as `x → +∞`. -/
theorem dlmf_6_12_li (n : ℕ) :
    ∃ C : ℝ, ∀ x : ℝ, Real.exp 1 ≤ x →
      |li x - eiAsymp n (Real.log x)| ≤ C * (x / Real.log x ^ (n + 1)) := by
  obtain ⟨C, hC⟩ := dlmf_6_12_2 n
  refine ⟨C, fun x hx => ?_⟩
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hx
  have hl : 1 ≤ Real.log x := by rwa [Real.le_log_iff_exp_le hx0]
  have h1 : 1 < x := lt_of_lt_of_le (by simp) hx
  have h := hC (Real.log x) hl
  rwa [Real.exp_log hx0, ← (dlmf_6_2_8 h1).2] at h

/-! ### The remainder bound for 6.12.2 (Olver 1997b, Ch. 6, Ex. 13.5) -/

/-- **DLMF 9.7.3** (Olver 1997b, (13.02), p. 225): `χ(x) = π^{1/2} Γ(x/2 + 1)/Γ(x/2 + 1/2)`. -/
noncomputable def olverChi (x : ℝ) : ℝ :=
  √π * Real.Gamma (x / 2 + 1) / Real.Gamma (x / 2 + 1 / 2)

/-- Olver's Lemma 13.1 on a half-line: `∫_0^∞ (1 + σ²)^{−(a+1)/2} dσ = χ(a)/a`, `a > 0`. -/
theorem integral_one_add_sq_rpow_eq_olverChi {a : ℝ} (ha : 0 < a) :
    ∫ σ in Ioi (0 : ℝ), (1 + σ ^ 2) ^ (-(a + 1) / 2) = olverChi a / a := by
  set s : ℝ := (a + 1) / 2 with hs
  -- the Beta integral with `t = σ²`
  have hB := dlmf_5_12_3 (a := (1 / 2 : ℂ)) (b := (a / 2 : ℝ)) (by norm_num)
    (by simp; positivity)
  have hsub := integral_comp_rpow_Ioi (fun t : ℝ => t ^ (-(1 / 2 : ℝ)) * (1 + t) ^ (-s))
    (p := 2) two_ne_zero
  have hl : ∫ σ in Ioi (0 : ℝ), (|(2 : ℝ)| * σ ^ ((2 : ℝ) - 1)) •
      ((σ ^ (2 : ℝ)) ^ (-(1 / 2 : ℝ)) * (1 + σ ^ (2 : ℝ)) ^ (-s)) =
      ∫ σ in Ioi (0 : ℝ), 2 * (1 + σ ^ 2) ^ (-(a + 1) / 2) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun σ (hσ : 0 < σ) => ?_
    have h2 : (σ ^ (2 : ℝ)) ^ (-(1 / 2 : ℝ)) = σ⁻¹ := by
      rw [← Real.rpow_mul hσ.le, show (2 : ℝ) * -(1 / 2) = -1 by norm_num, Real.rpow_neg_one]
    rw [h2, smul_eq_mul, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, abs_two,
      Real.rpow_two, hs, neg_div]
    field_simp
  rw [hl, integral_const_mul] at hsub
  have hr : ((∫ t in Ioi (0 : ℝ), t ^ (-(1 / 2 : ℝ)) * (1 + t) ^ (-s) : ℝ) : ℂ) =
      dlmfBeta (1 / 2) (a / 2 : ℝ) := by
    rw [← hB, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
    have h1 : (0 : ℝ) ≤ 1 + t := by linarith
    rw [div_eq_mul_inv _ ((1 + (t : ℂ)) ^ _), ← cpow_neg, ofReal_mul, ofReal_cpow ht.le,
      ofReal_cpow h1]
    push_cast
    congr 2
    · norm_num
    · rw [hs]; push_cast; ring
  rw [dlmfBeta, show (1 / 2 : ℂ) + ((a / 2 : ℝ) : ℂ) = ((s : ℝ) : ℂ) by rw [hs]; push_cast; ring,
    show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal,
    Complex.Gamma_ofReal, Complex.Gamma_ofReal, Real.Gamma_one_half_eq] at hr
  norm_cast at hr
  rw [hr] at hsub
  set J := ∫ σ in Ioi (0 : ℝ), (1 + σ ^ 2) ^ (-(a + 1) / 2) with hJ
  have hg : Real.Gamma (a / 2 + 1) = a / 2 * Real.Gamma (a / 2) :=
    Real.Gamma_add_one (by positivity)
  rw [olverChi, hg, show a / 2 + 1 / 2 = s by rw [hs]; ring]
  have hΓ : 0 < Real.Gamma s := Real.Gamma_pos_of_pos (by rw [hs]; positivity)
  rw [eq_div_iff hΓ.ne'] at hsub
  field_simp
  linarith

/-- The integrand `|1 − σe^{iθ}|^{−p}` of the tilted rays from `−x`. -/
noncomputable def tiltG (p : ℕ) (θ σ : ℝ) : ℝ := (1 - 2 * σ * Real.cos θ + σ ^ 2) ^ (-(p : ℝ) / 2)

theorem tiltG_nonneg (p : ℕ) (θ σ : ℝ) : 0 ≤ tiltG p θ σ :=
  Real.rpow_nonneg (by nlinarith [sq_nonneg (σ - Real.cos θ), Real.cos_sq_le_one θ]) _

theorem measurable_tiltG (p : ℕ) (θ : ℝ) : Measurable (tiltG p θ) := by
  unfold tiltG; fun_prop

theorem tiltG_le (p : ℕ) {θ : ℝ} (hc0 : 0 ≤ Real.cos θ) (hc : Real.cos θ ≤ 1 / 2) (σ : ℝ) :
    tiltG p θ σ ≤ 2 ^ ((p : ℝ) / 2) * (1 + σ ^ 2) ^ (-(p : ℝ) / 2) := by
  have h1 : (1 + σ ^ 2) / 2 ≤ 1 - 2 * σ * Real.cos θ + σ ^ 2 := by nlinarith [sq_nonneg (1 - σ)]
  have h2 : 0 < (1 + σ ^ 2) / 2 := by positivity
  calc tiltG p θ σ ≤ ((1 + σ ^ 2) / 2) ^ (-(p : ℝ) / 2) :=
        Real.rpow_le_rpow_of_nonpos h2 h1 (by have := p.cast_nonneg (α := ℝ); linarith)
    _ = _ := by
        rw [Real.div_rpow (by positivity) (by norm_num), div_eq_mul_inv, mul_comm,
          ← Real.rpow_neg (by norm_num), neg_div, neg_neg]

theorem integrableOn_tiltG_bound {p : ℕ} (hp : 2 ≤ p) :
    IntegrableOn (fun σ : ℝ => 2 ^ ((p : ℝ) / 2) * (1 + σ ^ 2) ^ (-(p : ℝ) / 2)) (Ioi 0) :=
  ((integrable_one_add_sq_rpow (r := p) (by exact_mod_cast hp)).const_mul _).integrableOn

/-- The bound on one tilted ray: `t = −x(1 − σe^{iθ})`, `π/3 < θ < π/2`. -/
theorem norm_eiP_upper_le_tilt {p : ℕ} (hp : 2 ≤ p) {x : ℝ} (hx : 0 < x) {θ : ℝ}
    (hθ1 : π / 3 < θ) (hθ2 : θ < π / 2) :
    ‖eiP p (log x + π * I)‖ ≤
      x ^ (1 - (p : ℝ)) * Real.exp x * ∫ σ in Ioi (0 : ℝ), tiltG p θ σ := by
  have hxc : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx.ne'
  set w : ℂ := log x + π * I with hw_def
  have hw : cexp w = -x := exp_log_add_pi_mul_I hxc
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ2⟩
  have hc2 : Real.cos θ < 1 / 2 := by
    rw [← Real.cos_pi_div_three]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos]) hθ1
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos])
    (by linarith [Real.pi_pos])
  set e : ℂ := (Real.cos (θ - π) : ℂ) + Real.sin (θ - π) * I with he_def
  have hre : e.re = -Real.cos θ := by
    rw [he_def]
    simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero]
    rw [Real.cos_sub_pi]; ring
  have him : e.im = -Real.sin θ := by
    rw [he_def]
    simp only [add_im, ofReal_re, mul_im, I_re, I_im, ofReal_im, mul_zero, mul_one, zero_add]
    rw [Real.sin_sub_pi]; ring
  have harg_e : arg e = θ - π := by
    rw [he_def, ofReal_cos, ofReal_sin]
    exact arg_cos_add_sin_mul_I ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hne : ‖e‖ = 1 := by
    rw [he_def, ofReal_cos, ofReal_sin, ← exp_mul_I, norm_exp_ofReal_mul_I]
  have hsq : ∀ σ : ℝ, ‖1 + σ * e‖ ^ 2 = 1 - 2 * σ * Real.cos θ + σ ^ 2 := fun σ => by
    rw [Complex.sq_norm, normSq_apply]
    simp only [add_re, one_re, re_ofReal_mul, hre, add_im, one_im, im_ofReal_mul, him]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hslit : ∀ σ : ℝ, 0 ≤ σ → 1 + σ * e ∈ slitPlane := fun σ hσ => by
    rw [mem_slitPlane_iff]
    rcases hσ.eq_or_lt with h | h
    · left; simp [← h]
    · right; simp only [add_im, one_im, im_ofReal_mul, him]; nlinarith
  have hcb : ∀ σ : ℝ, 0 ≤ σ → Real.sin θ ≤ ‖1 + σ * e‖ := fun σ _ => by
    refine abs_le_of_sq_le_sq' ?_ (norm_nonneg _) |>.2
    rw [hsq]
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (σ - Real.cos θ)]
  have hes : e ∈ slitPlane := mem_slitPlane_iff.2 (Or.inr (by rw [him]; linarith))
  have hdec : 0 < (cexp w * e).re := by
    rw [hw, neg_mul, neg_re, re_ofReal_mul, hre]; nlinarith
  have harg : |w.im + arg e| < π / 2 := by
    rw [harg_e, hw_def, add_im, log_im, arg_ofReal_of_nonneg hx.le]
    simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero, zero_add]
    rw [show π + (θ - π) = θ by ring, abs_of_pos (by linarith [Real.pi_pos])]
    exact hθ2
  have hray := eiP_eq_ray (p := (p : ℂ)) (by simp) hslit hs hcb hes hdec harg
  have hpre : ‖cexp ((1 - (p : ℂ)) * w) * e‖ = x ^ (1 - (p : ℝ)) := by
    rw [norm_mul, hne, mul_one, Complex.norm_exp, Real.rpow_def_of_pos hx]
    congr 1
    simp [w, mul_re, log_re, mul_comm]
  have hint : IntegrableOn (fun σ => Real.exp x * tiltG p θ σ) (Ioi 0) :=
    ((integrableOn_tiltG_bound hp).const_mul (Real.exp x)).mono'
      ((measurable_tiltG p θ).const_mul _).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun σ (hσ : 0 < σ) => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos x).le
          (tiltG_nonneg p θ σ))]
        gcongr
        exact tiltG_le p hc.le hc2.le σ))
  rw [hray, norm_mul, hpre, mul_assoc, ← integral_const_mul]
  gcongr
  refine norm_integral_le_of_norm_le hint ((ae_restrict_iff' measurableSet_Ioi).2
    (Eventually.of_forall fun σ (hσ : 0 < σ) => ?_))
  have hz : (1 : ℂ) + σ * e ≠ 0 := slitPlane_ne_zero (hslit σ hσ.le)
  rw [norm_mul, Complex.norm_exp, cpow_neg, cpow_natCast, norm_inv, norm_pow]
  gcongr
  · rw [hw]
    simp only [neg_re, mul_re, ofReal_re, ofReal_im, add_re, one_re, hre, add_im, one_im,
      im_ofReal_mul, him, neg_im, neg_zero, zero_mul, sub_zero]
    nlinarith [mul_pos (mul_pos hx hσ) hc]
  · rw [tiltG, ← hsq, neg_div, Real.rpow_neg (sq_nonneg _), ← Real.rpow_natCast (‖_‖) 2,
      ← Real.rpow_mul (norm_nonneg _), show ((2 : ℕ) : ℝ) * ((p : ℝ) / 2) = ((p : ℕ) : ℝ) by
        push_cast; ring, Real.rpow_natCast]

/-- **Vertical-ray bound** (Olver Ch. 6, Ex. 13.5): on the upper side of the negative axis,
`|∫_z^∞ e^{−t} t^{−p} dt| ≤ x^{1−p} eˣ ∫_0^∞ (1 + σ²)^{−p/2} dσ`, `z = x e^{πi}`, `p ≥ 2`. -/
theorem norm_eiP_upper_le {p : ℕ} (hp : 2 ≤ p) {x : ℝ} (hx : 0 < x) :
    ‖eiP p (log x + π * I)‖ ≤
      x ^ (1 - (p : ℝ)) * Real.exp x * ∫ σ in Ioi (0 : ℝ), (1 + σ ^ 2) ^ (-(p : ℝ) / 2) := by
  have hlim : Tendsto (fun θ => ∫ σ in Ioi (0 : ℝ), tiltG p θ σ) (𝓝[<] (π / 2))
      (𝓝 (∫ σ in Ioi (0 : ℝ), (1 + σ ^ 2) ^ (-(p : ℝ) / 2))) := by
    have hev : ∀ᶠ θ in 𝓝[<] (π / 2), θ ∈ Ioo (π / 3) (π / 2) :=
      Ioo_mem_nhdsLT (a := π / 3) (by linarith [Real.pi_pos])
    refine tendsto_integral_filter_of_dominated_convergence
      (fun σ => 2 ^ ((p : ℝ) / 2) * (1 + σ ^ 2) ^ (-(p : ℝ) / 2))
      (Eventually.of_forall fun θ => (measurable_tiltG p θ).aestronglyMeasurable)
      (hev.mono fun θ hθ => (ae_restrict_iff' measurableSet_Ioi).2
        (Eventually.of_forall fun σ (hσ : 0 < σ) => ?_))
      (integrableOn_tiltG_bound hp) (Eventually.of_forall fun σ => ?_)
    · obtain ⟨hθ1, hθ2⟩ := hθ
      have hc : 0 < Real.cos θ :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ2⟩
      have hc2 : Real.cos θ ≤ 1 / 2 := by
        rw [← Real.cos_pi_div_three]
        exact (Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos])
          hθ1).le
      rw [Real.norm_eq_abs, abs_of_nonneg (tiltG_nonneg p θ σ)]
      exact tiltG_le p hc.le hc2 σ
    · have hca : ContinuousAt (fun θ : ℝ => tiltG p θ σ) (π / 2) := by
        unfold tiltG
        refine ContinuousAt.rpow_const (by fun_prop) (Or.inl ?_)
        rw [Real.cos_pi_div_two]; exact ne_of_gt (by nlinarith [sq_nonneg σ])
      have := hca.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio (π / 2)))
      simpa [tiltG, Real.cos_pi_div_two] using this
  have hev : ∀ᶠ θ in 𝓝[<] (π / 2), ‖eiP p (log x + π * I)‖ ≤
      x ^ (1 - (p : ℝ)) * Real.exp x * ∫ σ in Ioi (0 : ℝ), tiltG p θ σ :=
    Filter.eventually_of_mem (Ioo_mem_nhdsLT (by linarith [Real.pi_pos] : π / 3 < π / 2))
      fun θ hθ =>
      norm_eiP_upper_le_tilt hp hx hθ.1 hθ.2
  exact ge_of_tendsto (hlim.const_mul _) hev

/-- `Ei(x) − eˣ/x ∑_{s<m} s!/x^s = −(−1)^m m! ∫_z^∞ e^{−t}t^{−m−1} dt − πi`, `z = x e^{πi}`. -/
theorem Ei_sub_eiAsymp_eq (m : ℕ) {x : ℝ} (hx : 0 < x) :
    ((Ei x - eiAsymp m x : ℝ) : ℂ) = -((-1) ^ m * m ! * eiP (m + 1) (log x + π * I)) - π * I := by
  have h := E1Gen_sub_e1Asymp m (log x + π * I)
  rw [exp_log_add_pi_mul_I (ofReal_ne_zero.2 hx.ne'), e1Asymp_neg m hx] at h
  push_cast
  rw [Ei_eq_E1Gen hx]
  linear_combination -h

/-- **DLMF §6.12(i)** (Olver 1997b, Ch. 6, Ex. 13.5): if 6.12.2 is terminated after `n` terms,
the remainder is bounded by `1 + χ(n+1)` times the next term `n! eˣ/x^{n+1}`. -/
theorem dlmf_6_12_2_remainder (n : ℕ) {x : ℝ} (hx : 0 < x) :
    |Ei x - eiAsymp n x| ≤ (1 + olverChi (n + 1)) * (n ! * Real.exp x / x ^ (n + 1)) := by
  set T : ℝ := n ! * Real.exp x / x ^ (n + 1) with hT
  have hsucc : eiAsymp (n + 1) x = eiAsymp n x + T := by
    rw [eiAsymp, eiAsymp, Finset.sum_range_succ, mul_add, hT]
    field_simp
    ring
  -- the remainder after `n + 1` terms
  have h1 : |Ei x - eiAsymp (n + 1) x| ≤ (n + 1) ! * ‖eiP (n + 2 : ℕ) (log x + π * I)‖ := by
    have h := congrArg Complex.re (Ei_sub_eiAsymp_eq (n + 1) hx)
    rw [ofReal_re] at h
    rw [h, show ((n + 1 : ℕ) : ℂ) + 1 = ((n + 2 : ℕ) : ℂ) by push_cast; ring, sub_re, neg_re,
      show ((π : ℂ) * I).re = 0 by simp, sub_zero, abs_neg]
    refine (abs_re_le_norm _).trans (le_of_eq ?_)
    rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_natCast]
  -- the vertical-ray bound and Lemma 13.1
  have h2 := norm_eiP_upper_le (p := n + 2) (by omega) hx
  have hχ := integral_one_add_sq_rpow_eq_olverChi (a := (n : ℝ) + 1) (by positivity)
  rw [show -(((n + 2 : ℕ) : ℝ)) / 2 = -((n : ℝ) + 1 + 1) / 2 by push_cast; ring, hχ,
    show (1 : ℝ) - ((n + 2 : ℕ) : ℝ) = -((n + 1 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_neg hx.le, Real.rpow_natCast] at h2
  have hsplit : Ei x - eiAsymp n x = (Ei x - eiAsymp (n + 1) x) + T := by rw [hsucc]; ring
  have hT0 : 0 ≤ T := by positivity
  have hfac : ((n + 1)! : ℝ) = (n + 1) * n ! := by push_cast [Nat.factorial_succ]; ring
  calc |Ei x - eiAsymp n x| ≤ |Ei x - eiAsymp (n + 1) x| + T := by
        rw [hsplit]
        exact (abs_add_le _ _).trans (by rw [abs_of_nonneg hT0])
    _ ≤ (n + 1)! * ((x ^ (n + 1))⁻¹ * Real.exp x * (olverChi (n + 1) / (n + 1))) + T := by
        gcongr
        exact h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
    _ = _ := by
        rw [hfac, hT]
        field_simp
        ring

end Azurite.DLMF
