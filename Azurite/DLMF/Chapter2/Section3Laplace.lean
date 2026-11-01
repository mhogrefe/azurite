/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section18WeylLC
import Azurite.DLMF.Chapter2.Section3Fourier
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# DLMF §2.3(i): integration by parts for Laplace transforms (2.3.1–2.3.3)

* `dlmf_2_3_2`: if the Laplace transform `∫₀^∞ e^{−xt} q(t) dt` (2.3.1, the improper integral
  `laplaceIntegral`) converges for all large `x` and `q` is infinitely differentiable on
  `(−δ, δ)`, then it is `∼ ∑ q⁽ˢ⁾(0)/x^{s+1}`. Proof: repeated integration by parts on `[0, δ/2]`
  (`laplaceFin_iter`) and an exponentially small tail (`laplace_tail_le`, by parts against the
  bounded primitive of `e^{−x₀t} q(t)`).
* `sigmaDLMF` (2.3.3) and `dlmf_2_3_3`: if `q` is infinitely differentiable on `[0, ∞)`,
  `q⁽ⁿ⁾(0) ≠ 0` and `σₙ` is finite, the `n`th error term is at most `|q⁽ⁿ⁾(0)|/(xⁿ(x − σₙ))` for
  `x > max(0, σₙ)`. The general form `laplace_error_le` assumes `|q⁽ⁿ⁾(t)| ≤ |q⁽ⁿ⁾(0)| e^{σt}`;
  `iteratedDeriv_growth` propagates this to the lower derivatives, so all the integrals converge
  absolutely (`laplaceIntegral_eq_integral`).
* `dlmf_2_3_2_of_sigma`: the expansion 2.3.2 from these bounds for every `n`.
-/

open Set Filter Topology Asymptotics Complex MeasureTheory
open scoped ContDiff

namespace Azurite.DLMF

/-! ### Exponential growth bounds -/

theorem integrableOn_one_add_pow_mul_exp_neg (k : ℕ) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => (1 + t) ^ k * Real.exp (-(c * t))) (Ioi 0) := by
  refine integrable_of_isBigO_exp_neg (b := c / 2) (half_pos hc) (by fun_prop) ?_
  have h := (tendsto_pow_mul_exp_neg_mul k (half_pos hc)).comp
    (tendsto_atTop_add_const_left atTop 1 tendsto_id)
  have hg : (fun t : ℝ => (1 + t) ^ k * Real.exp (-(c / 2 * (1 + t))) * Real.exp (c / 2))
      =O[atTop] (fun _ => (1 : ℝ)) := (h.mul_const _).isBigO_one ℝ
  refine (hg.mul (isBigO_refl (fun t : ℝ => Real.exp (-(c / 2) * t)) atTop)).congr' ?_ ?_
  · filter_upwards with t
    rw [show -(c * t) = -(c / 2 * (1 + t)) + c / 2 + -(c / 2) * t by ring, Real.exp_add,
      Real.exp_add]
    ring
  · filter_upwards with t
    rw [one_mul]

section Growth

variable {q : ℝ → ℂ} {U : Set ℝ} (hU : IsOpen U) (hIU : Ici 0 ⊆ U) (hq : ContDiffOn ℝ ∞ q U)
include hU hIU hq

/-- From `|q^{(n)}(t)| ≤ |q^{(n)}(0)| e^{σt}`: `|q^{(s)}(t)| ≤ M(1 + t)ⁿ e^{ρt}` for `s ≤ n`,
`ρ = max(σ, 0)`. -/
theorem iteratedDeriv_growth {n : ℕ} {σ : ℝ}
    (hσ : ∀ t, 0 < t → ‖iteratedDeriv n q t‖ ≤ ‖iteratedDeriv n q 0‖ * Real.exp (σ * t)) :
    ∀ s ≤ n, ∃ M, 0 ≤ M ∧ ∀ t, 0 ≤ t →
      ‖iteratedDeriv s q t‖ ≤ M * (1 + t) ^ (n - s) * Real.exp (max σ 0 * t) := by
  set ρ := max σ 0
  have hρ : 0 ≤ ρ := le_max_right _ _
  suffices h : ∀ k, ∀ s, s + k = n → ∃ M, 0 ≤ M ∧ ∀ t, 0 ≤ t →
      ‖iteratedDeriv s q t‖ ≤ M * (1 + t) ^ k * Real.exp (ρ * t) by
    intro s hs
    obtain ⟨M, hM, h'⟩ := h (n - s) s (by omega)
    exact ⟨M, hM, h'⟩
  intro k
  induction k with
  | zero =>
    intro s hs
    rw [add_zero] at hs; subst hs
    refine ⟨‖iteratedDeriv s q 0‖, norm_nonneg _, fun t ht => ?_⟩
    rw [pow_zero, mul_one]
    rcases ht.lt_or_eq with ht | ht
    · refine (hσ t ht).trans ?_
      gcongr; exact le_max_left _ _
    · subst ht; simp
  | succ k ih =>
    intro s hs
    obtain ⟨M, hM, hb⟩ := ih (s + 1) (by omega)
    refine ⟨‖iteratedDeriv s q 0‖ + M, by positivity, fun t ht => ?_⟩
    have hmv := norm_image_sub_le_of_norm_deriv_le_segment' (f := iteratedDeriv s q)
      (f' := iteratedDeriv (s + 1) q) (a := 0) (b := t)
      (C := M * (1 + t) ^ k * Real.exp (ρ * t))
      (fun u hu => (hasDerivAt_iteratedDeriv_of_contDiffOn hU hq s
        (hIU (mem_Ici.mpr hu.1))).hasDerivWithinAt)
      (fun u hu => (hb u hu.1).trans (by gcongr <;> linarith [hu.1, hu.2])) t
      ⟨ht, le_rfl⟩
    rw [sub_zero] at hmv
    have h1 : (1 : ℝ) ≤ (1 + t) ^ (k + 1) * Real.exp (ρ * t) :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith))
        (Real.one_le_exp (by positivity))
    have h2 : t * (1 + t) ^ k ≤ (1 + t) ^ (k + 1) := by
      rw [pow_succ]; nlinarith [pow_nonneg (show (0 : ℝ) ≤ 1 + t by linarith) k]
    have htri := norm_sub_norm_le (iteratedDeriv s q t) (iteratedDeriv s q 0)
    calc ‖iteratedDeriv s q t‖
        ≤ ‖iteratedDeriv s q 0‖ + ‖iteratedDeriv s q t - iteratedDeriv s q 0‖ := by linarith
      _ ≤ ‖iteratedDeriv s q 0‖ * ((1 + t) ^ (k + 1) * Real.exp (ρ * t)) +
          M * (t * (1 + t) ^ k) * Real.exp (ρ * t) := by
        gcongr
        · nlinarith [norm_nonneg (iteratedDeriv s q 0)]
        · calc _ ≤ M * (1 + t) ^ k * Real.exp (ρ * t) * t := hmv
            _ = _ := by ring
      _ ≤ ‖iteratedDeriv s q 0‖ * ((1 + t) ^ (k + 1) * Real.exp (ρ * t)) +
          M * (1 + t) ^ (k + 1) * Real.exp (ρ * t) := by gcongr
      _ = _ := by ring

end Growth

/-! ### Integration by parts for Laplace transforms -/

theorem tendsto_one_add_pow_mul_exp_neg (k : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℝ => (1 + t) ^ k * Real.exp (-(c * t))) atTop (𝓝 0) := by
  have h := ((tendsto_pow_mul_exp_neg_mul k hc).comp
    (tendsto_atTop_add_const_left atTop 1 tendsto_id)).mul_const (Real.exp c)
  rw [zero_mul] at h
  refine h.congr fun t => ?_
  simp only [Function.comp_apply, id]
  rw [show -(c * t) = -(c * (1 + t)) + c by ring, Real.exp_add]
  ring

theorem norm_cexp_neg_ofReal_mul (x t : ℝ) : ‖cexp (-(x : ℂ) * t)‖ = Real.exp (-(x * t)) := by
  rw [Complex.norm_exp]
  congr 1
  simp

theorem hasDerivAt_laplaceKernel {x : ℝ} (hx : (x : ℂ) ≠ 0) (t : ℝ) :
    HasDerivAt (fun t : ℝ => -cexp (-(x : ℂ) * t) / x) (cexp (-(x : ℂ) * t)) t := by
  have h0 : HasDerivAt (fun y : ℝ => cexp (-(x : ℂ) * y)) (cexp (-(x : ℂ) * t) * (-(x : ℂ)))
      t := by
    have h := ((hasDerivAt_id (t : ℂ)).const_mul (-(x : ℂ))).cexp
    rw [mul_one] at h
    exact h.comp_ofReal
  convert h0.neg.div_const (x : ℂ) using 1
  field_simp

section LaplaceIBP

variable {q : ℝ → ℂ} {U : Set ℝ} (hU : IsOpen U) (hIU : Ici 0 ⊆ U) (hq : ContDiffOn ℝ ∞ q U)
  {n : ℕ} {σ : ℝ}
  (hσ : ∀ t, 0 < t → ‖iteratedDeriv n q t‖ ≤ ‖iteratedDeriv n q 0‖ * Real.exp (σ * t))
include hU hIU hq hσ

theorem laplace_integrableOn {s : ℕ} (hs : s ≤ n) {x : ℝ} (hx : max σ 0 < x) :
    IntegrableOn (fun t : ℝ => cexp (-(x : ℂ) * t) * iteratedDeriv s q t) (Ioi 0) := by
  obtain ⟨M, hM, hb⟩ := iteratedDeriv_growth hU hIU hq hσ s hs
  have hc : 0 < x - max σ 0 := by linarith
  refine Integrable.mono' ((integrableOn_one_add_pow_mul_exp_neg (n - s) hc).const_mul M)
    ?_ ?_
  · exact ((by fun_prop : Continuous fun t : ℝ => cexp (-(x : ℂ) * t)).continuousOn.mul
      ((continuousOn_iteratedDeriv_of_contDiffOn hU hq s).mono
        (Ioi_subset_Ici_self.trans hIU))).aestronglyMeasurable measurableSet_Ioi
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    rw [norm_mul, norm_cexp_neg_ofReal_mul]
    calc Real.exp (-(x * t)) * ‖iteratedDeriv s q t‖
        ≤ Real.exp (-(x * t)) * (M * (1 + t) ^ (n - s) * Real.exp (max σ 0 * t)) := by
          gcongr; exact hb t (le_of_lt ht)
      _ = M * ((1 + t) ^ (n - s) * Real.exp (-((x - max σ 0) * t))) := by
          rw [show -((x - max σ 0) * t) = -(x * t) + max σ 0 * t by ring, Real.exp_add]; ring

/-- One integration by parts: `∫₀^∞ e^{−xt} q⁽ˢ⁾ = q⁽ˢ⁾(0)/x + x⁻¹ ∫₀^∞ e^{−xt} q⁽ˢ⁺¹⁾`. -/
theorem laplace_ibp_step {s : ℕ} (hs : s < n) {x : ℝ} (hx : max σ 0 < x) :
    ∫ t : ℝ in Ioi 0, cexp (-(x : ℂ) * t) * iteratedDeriv s q t =
      iteratedDeriv s q 0 / x +
        (1 / x) * ∫ t : ℝ in Ioi 0, cexp (-(x : ℂ) * t) * iteratedDeriv (s + 1) q t := by
  have hx0 : (0 : ℝ) < x := lt_of_le_of_lt (le_max_right _ _) hx
  have hxc : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx0.ne'
  set v : ℝ → ℂ := fun t => -cexp (-(x : ℂ) * t) / x with hvdef
  obtain ⟨M, hM, hb⟩ := iteratedDeriv_growth hU hIU hq hσ s hs.le
  have hc : 0 < x - max σ 0 := by linarith
  have huv' : IntegrableOn (iteratedDeriv s q * fun t : ℝ => cexp (-(x : ℂ) * t)) (Ioi 0) :=
    (laplace_integrableOn hU hIU hq hσ hs.le hx).congr_fun
      (fun t _ => by simp only [Pi.mul_apply]; ring) measurableSet_Ioi
  have hu'v : IntegrableOn (iteratedDeriv (s + 1) q * v) (Ioi 0) :=
    IntegrableOn.congr_fun ((laplace_integrableOn hU hIU hq hσ (Nat.succ_le_of_lt hs) hx).const_mul
      (-(1 / (x : ℂ))))
      (fun t _ => by simp only [Pi.mul_apply, hvdef]; ring) measurableSet_Ioi
  have hzero : Tendsto (iteratedDeriv s q * v) (𝓝[>] 0) (𝓝 (iteratedDeriv s q 0 * v 0)) :=
    ((hasDerivAt_iteratedDeriv_of_contDiffOn hU hq s (hIU self_mem_Ici)).continuousAt.mul
      (hasDerivAt_laplaceKernel hxc 0).continuousAt).tendsto.mono_left nhdsWithin_le_nhds
  have hinf : Tendsto (iteratedDeriv s q * v) atTop (𝓝 0) := by
    have h := ((tendsto_one_add_pow_mul_exp_neg (n - s) hc).const_mul (M / x))
    rw [mul_zero] at h
    refine squeeze_zero_norm' ?_ h
    filter_upwards [eventually_ge_atTop 0] with t ht
    rw [Pi.mul_apply, norm_mul, hvdef, norm_div, norm_neg, norm_cexp_neg_ofReal_mul,
      Complex.norm_real, Real.norm_of_nonneg hx0.le]
    calc ‖iteratedDeriv s q t‖ * (Real.exp (-(x * t)) / x)
        ≤ M * (1 + t) ^ (n - s) * Real.exp (max σ 0 * t) * (Real.exp (-(x * t)) / x) := by
          gcongr; exact hb t ht
      _ = M / x * ((1 + t) ^ (n - s) * Real.exp (-((x - max σ 0) * t))) := by
          rw [show -((x - max σ 0) * t) = -(x * t) + max σ 0 * t by ring, Real.exp_add]; ring
  have key := integral_Ioi_mul_deriv_eq_deriv_mul
    (fun t ht => hasDerivAt_iteratedDeriv_of_contDiffOn hU hq s
      (hIU (mem_Ici.mpr (mem_Ioi.mp ht).le)))
    (fun t _ => hasDerivAt_laplaceKernel hxc t) huv' hu'v hzero hinf
  have e1 : ∫ t : ℝ in Ioi 0, cexp (-(x : ℂ) * t) * iteratedDeriv s q t =
      ∫ t : ℝ in Ioi 0, iteratedDeriv s q t * cexp (-(x : ℂ) * t) := by
    simp_rw [mul_comm (cexp _)]
  have e2 : ∫ t : ℝ in Ioi 0, iteratedDeriv (s + 1) q t * v t =
      -(1 / (x : ℂ)) * ∫ t : ℝ in Ioi 0, cexp (-(x : ℂ) * t) * iteratedDeriv (s + 1) q t := by
    rw [← integral_const_mul]
    congr 1
    ext t
    simp only [hvdef]
    ring
  rw [e1, key, e2, hvdef]
  simp only [ofReal_zero, mul_zero, Complex.exp_zero]
  ring

theorem laplace_ibp_iter {x : ℝ} (hx : max σ 0 < x) (m : ℕ) (hm : m ≤ n) :
    ∫ t : ℝ in Ioi 0, cexp (-(x : ℂ) * t) * q t =
      ∑ s ∈ Finset.range m, iteratedDeriv s q 0 / (x : ℂ) ^ (s + 1) +
        (1 / (x : ℂ)) ^ m * ∫ t : ℝ in Ioi 0, cexp (-(x : ℂ) * t) * iteratedDeriv m q t := by
  have hx0 : (0 : ℝ) < x := lt_of_le_of_lt (le_max_right _ _) hx
  have hxc : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx0.ne'
  induction m with
  | zero => simp
  | succ m ih =>
    rw [ih (by omega), laplace_ibp_step hU hIU hq hσ (by omega : m < n) hx,
      Finset.sum_range_succ]
    ring

/-- **DLMF §2.3(i)**, the error bound: if `|q⁽ⁿ⁾(t)| ≤ |q⁽ⁿ⁾(0)| e^{σt}` on `(0, ∞)`, then for
`x > max(0, σ)` the `n`th error term of 2.3.2 is at most `|q⁽ⁿ⁾(0)|/(xⁿ(x − σ))`. -/
theorem laplace_error_le {x : ℝ} (hx0 : 0 < x) (hxσ : σ < x) :
    ‖(∫ t : ℝ in Ioi 0, cexp (-(x : ℂ) * t) * q t) -
        ∑ s ∈ Finset.range n, iteratedDeriv s q 0 / (x : ℂ) ^ (s + 1)‖ ≤
      ‖iteratedDeriv n q 0‖ / (x ^ n * (x - σ)) := by
  have hx : max σ 0 < x := max_lt hxσ hx0
  have hxs : 0 < x - σ := by linarith
  rw [laplace_ibp_iter hU hIU hq hσ hx n le_rfl, add_sub_cancel_left, norm_mul]
  have h1 : ‖(1 / (x : ℂ)) ^ n‖ = (1 / x) ^ n := by
    rw [norm_pow, norm_div, norm_one, Complex.norm_real, Real.norm_of_nonneg hx0.le]
  have hg : IntegrableOn (fun t : ℝ => ‖iteratedDeriv n q 0‖ * Real.exp ((σ - x) * t))
      (Ioi 0) := (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul _
  have hI : ‖∫ t : ℝ in Ioi 0, cexp (-(x : ℂ) * t) * iteratedDeriv n q t‖ ≤
      ‖iteratedDeriv n q 0‖ / (x - σ) := by
    calc _ ≤ ∫ t : ℝ in Ioi 0, ‖iteratedDeriv n q 0‖ * Real.exp ((σ - x) * t) := by
          refine norm_integral_le_of_norm_le hg
            (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
          rw [norm_mul, norm_cexp_neg_ofReal_mul]
          calc Real.exp (-(x * t)) * ‖iteratedDeriv n q t‖
              ≤ Real.exp (-(x * t)) * (‖iteratedDeriv n q 0‖ * Real.exp (σ * t)) := by
                gcongr; exact hσ t ht
            _ = _ := by
                rw [show (σ - x) * t = σ * t + -(x * t) by ring, Real.exp_add]; ring
      _ = _ := by
          rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) 0, mul_zero,
            Real.exp_zero, show σ - x = -(x - σ) by ring, neg_div_neg_eq, mul_one_div]
  rw [h1]
  calc (1 / x) ^ n * ‖∫ t : ℝ in Ioi 0, cexp (-(x : ℂ) * t) * iteratedDeriv n q t‖
      ≤ (1 / x) ^ n * (‖iteratedDeriv n q 0‖ / (x - σ)) := by gcongr
    _ = _ := by rw [one_div_pow]; field_simp

end LaplaceIBP

/-! ### The Laplace expansion 2.3.2 -/

theorem norm_intervalIntegral_le_exp {f : ℝ → ℂ} {a b c K : ℝ} (hab : a ≤ b) (hc : 0 < c)
    (hK : 0 ≤ K) (hf : ∀ t ∈ Ioc a b, ‖f t‖ ≤ K * Real.exp (-(c * t))) :
    ‖∫ t in a..b, f t‖ ≤ K * Real.exp (-(c * a)) / c := by
  simp_rw [← neg_mul] at hf ⊢
  calc ‖∫ t in a..b, f t‖ ≤ ∫ t in a..b, K * Real.exp (-c * t) :=
        intervalIntegral.norm_integral_le_of_norm_le hab (ae_of_all _ hf)
          ((by fun_prop : Continuous fun t : ℝ => K * Real.exp (-c * t)).intervalIntegrable a b)
    _ = ∫ t in Ioc a b, K * Real.exp (-c * t) := intervalIntegral.integral_of_le hab
    _ ≤ ∫ t in Ioi a, K * Real.exp (-c * t) :=
        setIntegral_mono_set ((integrableOn_exp_mul_Ioi (by linarith) a).const_mul K)
          (ae_of_all _ fun t => by simp only [Pi.zero_apply]; positivity)
          Ioc_subset_Ioi_self.eventuallyLE
    _ = _ := by
        rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) a, neg_div_neg_eq,
          mul_div_assoc]

section LaplaceFinite

variable {q : ℝ → ℂ} {U : Set ℝ} {b : ℝ} (hb : 0 ≤ b) (hU : IsOpen U) (hIU : Icc 0 b ⊆ U)
  (hq : ContDiffOn ℝ ∞ q U)
include hb hU hIU hq

theorem laplaceFin_step (s : ℕ) {x : ℝ} (hx : 0 < x) :
    ∫ t in (0 : ℝ)..b, cexp (-(x : ℂ) * t) * iteratedDeriv s q t =
      (iteratedDeriv s q 0 - cexp (-(x : ℂ) * b) * iteratedDeriv s q b) / x +
        (1 / x) * ∫ t in (0 : ℝ)..b, cexp (-(x : ℂ) * t) * iteratedDeriv (s + 1) q t := by
  have hxc : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hI : uIcc 0 b ⊆ U := by rw [uIcc_of_le hb]; exact hIU
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := iteratedDeriv s q) (v := fun t : ℝ => -cexp (-(x : ℂ) * t) / x)
    (fun t ht => hasDerivAt_iteratedDeriv_of_contDiffOn hU hq s (hI ht))
    (fun t _ => hasDerivAt_laplaceKernel hxc t)
    (((continuousOn_iteratedDeriv_of_contDiffOn hU hq (s + 1)).mono hI).intervalIntegrable)
    ((by fun_prop : Continuous fun t : ℝ => cexp (-(x : ℂ) * t)).intervalIntegrable 0 b)
  have e1 : ∫ t in (0 : ℝ)..b, cexp (-(x : ℂ) * t) * iteratedDeriv s q t =
      ∫ t in (0 : ℝ)..b, iteratedDeriv s q t * cexp (-(x : ℂ) * t) := by
    simp_rw [mul_comm (cexp _)]
  have e2 : ∫ t in (0 : ℝ)..b, iteratedDeriv (s + 1) q t * (-cexp (-(x : ℂ) * t) / x) =
      -(1 / (x : ℂ)) * ∫ t in (0 : ℝ)..b, cexp (-(x : ℂ) * t) * iteratedDeriv (s + 1) q t := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    ext t
    ring
  rw [e1, key, e2]
  simp only [ofReal_zero, mul_zero, Complex.exp_zero]
  field_simp
  ring

theorem laplaceFin_iter {x : ℝ} (hx : 0 < x) (m : ℕ) :
    ∫ t in (0 : ℝ)..b, cexp (-(x : ℂ) * t) * q t =
      ∑ s ∈ Finset.range m,
          (iteratedDeriv s q 0 - cexp (-(x : ℂ) * b) * iteratedDeriv s q b) / (x : ℂ) ^ (s + 1) +
        (1 / (x : ℂ)) ^ m * ∫ t in (0 : ℝ)..b, cexp (-(x : ℂ) * t) * iteratedDeriv m q t := by
  have hxc : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  induction m with
  | zero => simp
  | succ m ih =>
    rw [ih, laplaceFin_step hb hU hIU hq m hx, Finset.sum_range_succ]
    ring

end LaplaceFinite

/-- Abel-type tail bound: if `|∫_b^t e^{−x₀u} q(u) du| ≤ B` on `[b, R]` and `x > x₀`, then
`|∫_b^R e^{−xt} q(t) dt| ≤ 2B e^{−(x−x₀)b}`. -/
theorem laplace_tail_le {q : ℝ → ℂ} {b x₀ x B R : ℝ} (hbR : b ≤ R) (hx : x₀ < x)
    (hk : IntervalIntegrable (fun u : ℝ => cexp (-(x₀ : ℂ) * u) * q u) volume b R)
    (hB : ∀ t ∈ Icc b R, ‖∫ u in b..t, cexp (-(x₀ : ℂ) * u) * q u‖ ≤ B) :
    ‖∫ t in b..R, cexp (-(x : ℂ) * t) * q t‖ ≤ 2 * B * Real.exp (-((x - x₀) * b)) := by
  set c := x - x₀ with hcdef
  have hc : 0 < c := sub_pos.mpr hx
  have hB0 : 0 ≤ B := by
    have := hB b (left_mem_Icc.mpr hbR)
    rwa [intervalIntegral.integral_same, norm_zero] at this
  set k := fun u : ℝ => cexp (-(x₀ : ℂ) * u) * q u with hkdef
  set Φ := fun t : ℝ => ∫ u in b..t, k u with hΦdef
  set ψ := fun t : ℝ => cexp (-(c : ℂ) * t) with hψdef
  have hψ : ∀ t, HasDerivAt ψ (-(c : ℂ) * ψ t) t := fun t => by
    have h := ((hasDerivAt_id (t : ℂ)).const_mul (-(c : ℂ))).cexp
    rw [mul_one] at h
    have h2 := h.comp_ofReal
    simp only [id_eq] at h2
    rw [mul_comm] at h2
    exact h2
  have hψc : Continuous ψ := by fun_prop
  have key := integral_primitive_mul_deriv_on hbR hk (fun t _ => hψ t)
    (by fun_prop : Continuous fun t : ℝ => -(c : ℂ) * ψ t).continuousOn
  have hks : ∀ u, k u * ψ u = cexp (-(x : ℂ) * u) * q u := fun u => by
    simp only [hkdef, hψdef]
    rw [mul_right_comm, ← Complex.exp_add]
    congr 2
    rw [hcdef]
    push_cast
    ring
  have hsplit : ∫ u in b..R, k u * (ψ R - ψ u) =
      ψ R * Φ R - ∫ u in b..R, cexp (-(x : ℂ) * u) * q u := by
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub (hk.mul_continuousOn continuousOn_const)
      (hk.mul_continuousOn hψc.continuousOn)]
    simp_rw [hks]
    congr 1
    rw [intervalIntegral.integral_mul_const]
    exact mul_comm _ _
  have heq : ∫ u in b..R, cexp (-(x : ℂ) * u) * q u =
      ψ R * Φ R - ∫ t in b..R, Φ t * (-(c : ℂ) * ψ t) := by
    linear_combination key + hsplit
  have hnψ : ∀ t, ‖ψ t‖ = Real.exp (-(c * t)) := fun t => norm_cexp_neg_ofReal_mul c t
  have h1 : ‖ψ R * Φ R‖ ≤ B * Real.exp (-(c * b)) := by
    rw [norm_mul, hnψ, mul_comm]
    gcongr
    exact hB R (right_mem_Icc.mpr hbR)
  have h2 : ‖∫ t in b..R, Φ t * (-(c : ℂ) * ψ t)‖ ≤ B * Real.exp (-(c * b)) := by
    have := norm_intervalIntegral_le_exp (f := fun t => Φ t * (-(c : ℂ) * ψ t)) (K := B * c)
      hbR hc (by positivity) fun t ht => by
        rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hc.le, hnψ]
        have := hB t (Ioc_subset_Icc_self ht)
        calc ‖Φ t‖ * (c * Real.exp (-(c * t))) ≤ B * (c * Real.exp (-(c * t))) := by gcongr
          _ = _ := by ring
    calc _ ≤ B * c * Real.exp (-(c * b)) / c := this
      _ = _ := by field_simp
  rw [heq]
  calc _ ≤ ‖ψ R * Φ R‖ + ‖∫ t in b..R, Φ t * (-(c : ℂ) * ψ t)‖ := norm_sub_le _ _
    _ ≤ _ := by linarith

/-- The Laplace transform 2.3.1 as an improper integral `lim_{R→∞} ∫₀^R e^{−xt} q(t) dt`. -/
noncomputable def laplaceIntegral (q : ℝ → ℂ) (x : ℝ) : ℂ :=
  limUnder atTop fun R => ∫ t in (0 : ℝ)..R, cexp (-(x : ℂ) * t) * q t

/-- The terms `q⁽ˢ⁾(0)/x^{s+1}` of 2.3.2. -/
noncomputable def laplaceTerm (q : ℝ → ℂ) (s : ℕ) (x : ℝ) : ℂ :=
  iteratedDeriv s q 0 / (x : ℂ) ^ (s + 1)

theorem intervalIntegrable_laplace_mul {q : ℝ → ℂ}
    (hloc : ∀ R, 0 ≤ R → IntervalIntegrable q volume 0 R) (y : ℝ) {α β : ℝ} (hα : 0 ≤ α)
    (hαβ : α ≤ β) :
    IntervalIntegrable (fun t : ℝ => cexp (-(y : ℂ) * t) * q t) volume α β := by
  have h := (hloc β (hα.trans hαβ)).mono_set (by
    rw [uIcc_of_le hαβ, uIcc_of_le (hα.trans hαβ)]; exact Icc_subset_Icc_left hα)
  exact h.continuousOn_mul (by fun_prop)

/-- The tail of a Laplace transform convergent at `x₀`: for `x > x₀`,
`|∫_b^∞ e^{−xt} q(t) dt| ≤ 2B e^{−(x−x₀)b}` with `B` independent of `x`. -/
theorem laplace_tail_exists {q : ℝ → ℂ} {x₀ b : ℝ} (hb : 0 < b)
    (hloc : ∀ R, 0 ≤ R → IntervalIntegrable q volume 0 R)
    (hconv : ∃ L, Tendsto (fun R => ∫ t in (0 : ℝ)..R, cexp (-(x₀ : ℂ) * t) * q t) atTop
      (𝓝 L)) :
    ∃ B, 0 ≤ B ∧ ∀ x, x₀ < x → ∀ L,
      Tendsto (fun R => ∫ t in (0 : ℝ)..R, cexp (-(x : ℂ) * t) * q t) atTop (𝓝 L) →
      ‖L - ∫ t in (0 : ℝ)..b, cexp (-(x : ℂ) * t) * q t‖ ≤
        2 * B * Real.exp (-((x - x₀) * b)) := by
  have hii := intervalIntegrable_laplace_mul hloc
  obtain ⟨L₀, hL₀⟩ := hconv
  set Φ := fun t : ℝ => ∫ u in b..t, cexp (-(x₀ : ℂ) * u) * q u with hΦdef
  set Λ := L₀ - ∫ u in (0 : ℝ)..b, cexp (-(x₀ : ℂ) * u) * q u
  have hΦt : Tendsto Φ atTop (𝓝 Λ) := by
    refine (hL₀.sub_const _).congr' ?_
    filter_upwards [eventually_ge_atTop b] with t ht
    rw [hΦdef, ← intervalIntegral.integral_add_adjacent_intervals
      (hii x₀ le_rfl hb.le) (hii x₀ hb.le ht), add_sub_cancel_left]
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hΦt.norm.eventually (gt_mem_nhds (lt_add_one ‖Λ‖)))
  set T' := max T b
  have hΦc : ContinuousOn Φ (Icc b T') := by
    have h := intervalIntegral.continuousOn_primitive_interval' (hii x₀ hb.le
      (le_max_right T b)) (a := b) left_mem_uIcc
    rwa [uIcc_of_le (le_max_right _ _)] at h
  obtain ⟨B₁, hB₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hΦc
  set B := max B₁ (‖Λ‖ + 1)
  have hBall : ∀ t, b ≤ t → ‖Φ t‖ ≤ B := by
    intro t ht
    rcases le_or_gt t T' with h | h
    · exact (hB₁ t ⟨ht, h⟩).trans (le_max_left _ _)
    · exact (hT t ((le_max_left _ _).trans h.le)).le.trans (le_max_right _ _)
  refine ⟨B, (norm_nonneg _).trans (hBall b le_rfl), fun x hxx₀ L hL => ?_⟩
  refine le_of_tendsto ((hL.sub_const _).norm) ?_
  filter_upwards [eventually_ge_atTop b] with R hR
  rw [← intervalIntegral.integral_add_adjacent_intervals (hii x le_rfl hb.le)
    (hii x hb.le hR), add_sub_cancel_left]
  exact laplace_tail_le hR hxx₀ (hii x₀ hb.le hR) (fun t ht => hBall t ht.1)

theorem eventually_exp_neg_le_inv_pow (n : ℕ) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ x : ℝ in atTop, Real.exp (-(b * x)) ≤ x⁻¹ ^ n := by
  filter_upwards [(tendsto_pow_mul_exp_neg_mul n hb).eventually (ge_mem_nhds zero_lt_one),
    eventually_gt_atTop 0] with x hx hx0
  rw [inv_pow, le_inv_comm₀ (by positivity) (by positivity), ← one_div,
    le_div_iff₀ (by positivity)]
  linarith [mul_comm (x ^ n) (Real.exp (-(b * x)))]

/-- **DLMF 2.3.2**: if the Laplace transform 2.3.1 converges for all sufficiently large `x`
and `q` is infinitely differentiable in a neighborhood of the origin, then
`∫₀^∞ e^{−xt} q(t) dt ∼ ∑ q⁽ˢ⁾(0)/x^{s+1}` as `x → +∞`. The integral is the improper
integral `lim_{R→∞} ∫₀^R`, with `q` integrable on every `[0, R]`. -/
theorem dlmf_2_3_2 {q : ℝ → ℂ} {δ x₀ : ℝ} (hδ : 0 < δ) (hq : ContDiffOn ℝ ∞ q (Ioo (-δ) δ))
    (hloc : ∀ R, 0 ≤ R → IntervalIntegrable q volume 0 R)
    (hconv : ∀ x, x₀ ≤ x → ∃ L,
      Tendsto (fun R => ∫ t in (0 : ℝ)..R, cexp (-(x : ℂ) * t) * q t) atTop (𝓝 L)) :
    IsGenAsympExpansionDLMF atTop invPowScale (laplaceIntegral q) (laplaceTerm q) := by
  refine ⟨isAsympScale_invPowScale, fun n => ?_⟩
  set b := δ / 2 with hbdef
  have hb : 0 < b := half_pos hδ
  have hIU : Icc 0 b ⊆ Ioo (-δ) δ := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((continuousOn_iteratedDeriv_of_contDiffOn isOpen_Ioo hq n).mono hIU)
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 (left_mem_Icc.mpr hb.le))
  obtain ⟨B, hB0, hBt⟩ := laplace_tail_exists hb hloc (hconv x₀ le_rfl)
  set S := ∑ s ∈ Finset.range n, ‖iteratedDeriv s q b‖
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
  apply isBigODLMF_invPowScale (C := 2 * B * Real.exp (x₀ * b) + S + K)
  filter_upwards [eventually_exp_neg_le_inv_pow (n + 1) hb, eventually_gt_atTop (max x₀ 1)]
    with x hex hx
  have hxx₀ : x₀ < x := (le_max_left _ _).trans_lt hx
  have hx1 : 1 < x := (le_max_right _ _).trans_lt hx
  have hx0 : 0 < x := zero_lt_one.trans hx1
  obtain ⟨L, hL⟩ := hconv x hxx₀.le
  have hF : laplaceIntegral q x = L := hL.limUnder_eq
  have htail := hBt x hxx₀ L hL
  have hhead := laplaceFin_iter hb.le isOpen_Ioo hIU hq hx0 n
  have hDn : ‖∫ t in (0 : ℝ)..b, cexp (-(x : ℂ) * t) * iteratedDeriv n q t‖ ≤ K / x := by
    have := norm_intervalIntegral_le_exp hb.le hx0 hK0 (f := fun t =>
        cexp (-(x : ℂ) * t) * iteratedDeriv n q t) fun t ht => by
      rw [norm_mul, norm_cexp_neg_ofReal_mul, mul_comm]
      gcongr
      exact hK t (Ioc_subset_Icc_self ht)
    simpa using this
  have hdec : laplaceIntegral q x - ∑ s ∈ Finset.range n, laplaceTerm q s x =
      (L - ∫ t in (0 : ℝ)..b, cexp (-(x : ℂ) * t) * q t) -
        ∑ s ∈ Finset.range n, cexp (-(x : ℂ) * b) * iteratedDeriv s q b / (x : ℂ) ^ (s + 1) +
        (1 / (x : ℂ)) ^ n * ∫ t in (0 : ℝ)..b, cexp (-(x : ℂ) * t) * iteratedDeriv n q t := by
    rw [hF]
    simp only [laplaceTerm]
    rw [hhead]
    simp only [sub_div, Finset.sum_sub_distrib]
    ring
  have hmid : ‖∑ s ∈ Finset.range n,
      cexp (-(x : ℂ) * b) * iteratedDeriv s q b / (x : ℂ) ^ (s + 1)‖ ≤
      Real.exp (-(b * x)) * S := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [norm_div, norm_mul, norm_cexp_neg_ofReal_mul, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg hx0.le, mul_comm x b]
    exact div_le_self (by positivity) (one_le_pow₀ hx1.le)
  have hlast : ‖(1 / (x : ℂ)) ^ n *
      ∫ t in (0 : ℝ)..b, cexp (-(x : ℂ) * t) * iteratedDeriv n q t‖ ≤ K * x⁻¹ ^ (n + 1) := by
    rw [norm_mul, norm_pow, norm_div, norm_one, Complex.norm_real, Real.norm_of_nonneg hx0.le]
    calc (1 / x) ^ n * ‖∫ t in (0 : ℝ)..b, cexp (-(x : ℂ) * t) * iteratedDeriv n q t‖
        ≤ (1 / x) ^ n * (K / x) := by gcongr
      _ = _ := by rw [one_div, pow_succ]; ring
  have hexp2 : Real.exp (-((x - x₀) * b)) = Real.exp (x₀ * b) * Real.exp (-(b * x)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hdec]
  calc _ ≤ ‖L - ∫ t in (0 : ℝ)..b, cexp (-(x : ℂ) * t) * q t‖ +
        ‖∑ s ∈ Finset.range n,
          cexp (-(x : ℂ) * b) * iteratedDeriv s q b / (x : ℂ) ^ (s + 1)‖ +
        ‖(1 / (x : ℂ)) ^ n *
          ∫ t in (0 : ℝ)..b, cexp (-(x : ℂ) * t) * iteratedDeriv n q t‖ :=
        (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _)
    _ ≤ 2 * B * (Real.exp (x₀ * b) * Real.exp (-(b * x))) + Real.exp (-(b * x)) * S +
        K * x⁻¹ ^ (n + 1) := by rw [← hexp2]; gcongr
    _ ≤ 2 * B * (Real.exp (x₀ * b) * x⁻¹ ^ (n + 1)) + x⁻¹ ^ (n + 1) * S +
        K * x⁻¹ ^ (n + 1) := by
        gcongr
    _ = _ := by ring

/-! ### The error bound with DLMF's `σₙ` (2.3.3) -/

/-- **DLMF 2.3.3**: `σₙ = sup_{(0,∞)} t⁻¹ ln |q⁽ⁿ⁾(t)/q⁽ⁿ⁾(0)|`. -/
noncomputable def sigmaDLMF (q : ℝ → ℂ) (n : ℕ) : ℝ :=
  sSup ((fun t => t⁻¹ * Real.log ‖iteratedDeriv n q t / iteratedDeriv n q 0‖) '' Ioi 0)

/-- `σₙ` finite gives `|q⁽ⁿ⁾(t)| ≤ |q⁽ⁿ⁾(0)| e^{σₙt}` on `(0, ∞)`. -/
theorem norm_iteratedDeriv_le_sigmaDLMF {q : ℝ → ℂ} {n : ℕ} (h0 : iteratedDeriv n q 0 ≠ 0)
    (hbdd : BddAbove
      ((fun t => t⁻¹ * Real.log ‖iteratedDeriv n q t / iteratedDeriv n q 0‖) '' Ioi 0))
    {t : ℝ} (ht : 0 < t) :
    ‖iteratedDeriv n q t‖ ≤ ‖iteratedDeriv n q 0‖ * Real.exp (sigmaDLMF q n * t) := by
  have hle : t⁻¹ * Real.log ‖iteratedDeriv n q t / iteratedDeriv n q 0‖ ≤ sigmaDLMF q n :=
    le_csSup hbdd (mem_image_of_mem _ ht)
  have hlog : Real.log ‖iteratedDeriv n q t / iteratedDeriv n q 0‖ ≤ sigmaDLMF q n * t := by
    have := mul_le_mul_of_nonneg_left hle ht.le
    rwa [← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul, mul_comm t] at this
  have hn0 : 0 < ‖iteratedDeriv n q 0‖ := norm_pos_iff.mpr h0
  rcases eq_or_ne (iteratedDeriv n q t) 0 with h | h
  · rw [h, norm_zero]; positivity
  · have hr : 0 < ‖iteratedDeriv n q t / iteratedDeriv n q 0‖ :=
      norm_pos_iff.mpr (div_ne_zero h h0)
    have := Real.exp_le_exp.mpr hlog
    rw [Real.exp_log hr, norm_div, div_le_iff₀ hn0] at this
    linarith

section Sigma

variable {q : ℝ → ℂ} {U : Set ℝ} (hU : IsOpen U) (hIU : Ici 0 ⊆ U) (hq : ContDiffOn ℝ ∞ q U)
include hU hIU hq

/-- Under a bound `|q⁽ⁿ⁾(t)| ≤ |q⁽ⁿ⁾(0)| e^{σt}`, the Laplace transform 2.3.1 converges
absolutely for `x > max(0, σ)`, and its improper value is the Lebesgue integral. -/
theorem laplaceIntegral_eq_integral {n : ℕ} {σ : ℝ}
    (hσ : ∀ t, 0 < t → ‖iteratedDeriv n q t‖ ≤ ‖iteratedDeriv n q 0‖ * Real.exp (σ * t))
    {x : ℝ} (hx : max σ 0 < x) :
    laplaceIntegral q x = ∫ t : ℝ in Ioi 0, cexp (-(x : ℂ) * t) * q t := by
  have h := laplace_integrableOn hU hIU hq hσ (Nat.zero_le n) hx
  simp only [iteratedDeriv_zero] at h
  exact (intervalIntegral_tendsto_integral_Ioi 0 h tendsto_id).limUnder_eq

/-- **DLMF §2.3(i)**, the error bound in 2.3.2 under 2.3.3: if `q` is infinitely
differentiable on `[0, ∞)`, `q⁽ⁿ⁾(0) ≠ 0` and `σₙ` is finite, then for `x > max(0, σₙ)`
the `n`th error term is bounded by `|q⁽ⁿ⁾(0)|/(xⁿ(x − σₙ))`. -/
theorem dlmf_2_3_3 {n : ℕ} (h0 : iteratedDeriv n q 0 ≠ 0)
    (hbdd : BddAbove
      ((fun t => t⁻¹ * Real.log ‖iteratedDeriv n q t / iteratedDeriv n q 0‖) '' Ioi 0))
    {x : ℝ} (hx0 : 0 < x) (hxσ : sigmaDLMF q n < x) :
    ‖laplaceIntegral q x - ∑ s ∈ Finset.range n, laplaceTerm q s x‖ ≤
      ‖iteratedDeriv n q 0‖ / (x ^ n * (x - sigmaDLMF q n)) := by
  have hσ := fun t (ht : 0 < t) => norm_iteratedDeriv_le_sigmaDLMF h0 hbdd ht
  rw [laplaceIntegral_eq_integral hU hIU hq hσ (max_lt hxσ hx0)]
  exact laplace_error_le hU hIU hq hσ hx0 hxσ

/-- The expansion 2.3.2 with the error bounds of 2.3.3: if every `q⁽ⁿ⁾` satisfies
`|q⁽ⁿ⁾(t)| ≤ |q⁽ⁿ⁾(0)| e^{σₙt}`, the Lebesgue Laplace integral has the expansion
`∑ q⁽ˢ⁾(0)/x^{s+1}`. -/
theorem dlmf_2_3_2_of_sigma {σ : ℕ → ℝ}
    (hσ : ∀ n t, 0 < t →
      ‖iteratedDeriv n q t‖ ≤ ‖iteratedDeriv n q 0‖ * Real.exp (σ n * t)) :
    IsGenAsympExpansionDLMF atTop invPowScale
      (fun x => ∫ t : ℝ in Ioi 0, cexp (-(x : ℂ) * t) * q t) (laplaceTerm q) := by
  refine ⟨isAsympScale_invPowScale, fun n => ?_⟩
  set ρ := max (σ n) 0
  apply isBigODLMF_invPowScale (C := 2 * ‖iteratedDeriv n q 0‖)
  filter_upwards [eventually_gt_atTop (2 * ρ)] with x hx
  have hρ0 : 0 ≤ ρ := le_max_right _ _
  have hσρ : σ n ≤ ρ := le_max_left _ _
  have hx0 : 0 < x := by linarith
  have hxσ : σ n < x := by linarith
  have h := laplace_error_le hU hIU hq (hσ n) hx0 hxσ
  refine h.trans ?_
  have hx2 : x / 2 ≤ x - σ n := by linarith
  calc ‖iteratedDeriv n q 0‖ / (x ^ n * (x - σ n))
      ≤ ‖iteratedDeriv n q 0‖ / (x ^ n * (x / 2)) := by gcongr
    _ = _ := by rw [inv_pow, pow_succ]; field_simp

end Sigma

end Azurite.DLMF
