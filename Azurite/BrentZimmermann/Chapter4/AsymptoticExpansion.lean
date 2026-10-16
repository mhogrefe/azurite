/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BrentZimmermann.Chapter4.SplittingComplexity
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Brent–Zimmermann §4.5: Asymptotic expansions (introduction)

Different parts of the domain call for different methods.  The exponential integral
`E₁(x) = ∫_x^∞ e^(−u)/u du` (4.25), `x > 0`, has the power series (4.26)
`E₁(x) + γ + ln x = ∑_{j≥1} (−1)^(j−1) x^j/(j! j)`, useless for large `x` (cancellation, §4.4);
there one uses instead

  `e^x E₁(x) = ∑_{j=1}^k (j−1)! (−1)^(j−1) / x^j + R_k(x)`,                                (4.27)
  `R_k(x) = k! (−1)^k e^x ∫_x^∞ e^(−u)/u^(k+1) du`,  `|R_k(x)| < k! / x^(k+1)`.           (4.28)

So `R_k(x) → 0` as `x → ∞` for fixed `k`, but not as `k → ∞`: the series diverges and is an
*asymptotic* series, `e^x E₁(x) ~ ∑ (j−1)!(−1)^(j−1)/x^j` (4.29).  Often the error is bounded by
the first omitted term, and for alternating series the value lies between two consecutive
partial sums — true here for real `x > 0`.  With `k = ⌊x⌋` the relative error is
`O(x^(1/2) e^(−x))` since `|R_k(k)| ≤ k!/k^(k+1) = O(k^(−1/2) e^(−k))` (4.30), by Stirling, so the
expansion gives precision `n` once `x > n ln 2 + O(ln n)`.

What is formalized (the integrals are Lebesgue integrals over `Ioi x`):

* `expTail k x = ∫_x^∞ e^(−u)/u^(k+1) du`, `expIntegral x = E₁(x) = expTail 0 x`;
  `integrableOn_expTail`, `expTail_nonneg`, `expTail_pos`, `expTail_le` (`≤ e^(−x)/x^(k+1)`).
* `expTail_succ` — the integration by parts `I_k(x) = e^(−x)/x^(k+1) − (k+1) I_{k+1}(x)`.
* `asymptoticTerm j x = j! (−1)^j / x^(j+1)` (the text's term `j+1`), `asymptoticRemainder k x`
  (4.28), and (4.27) as `exp_mul_expIntegral_eq`.
* `abs_asymptoticRemainder_le` — `|R_k(x)| ≤ k!/x^(k+1) = |first omitted term|`;
  `tendsto_asymptoticRemainder_atTop` — `R_k(x) → 0` as `x → ∞`.
* `not_summable_asymptoticTerm` — the series diverges for every `x > 0` (4.29 is asymptotic).
* `sign_asymptoticRemainder` — `R_k(x)` has the sign `(−1)^k`; `between_partialSums` — the
  value lies strictly between the partial sums with `k` and `k + 1` terms.
* `factorial_le_stirling_upper` — `k! ≤ e √k (k/e)^k` from the antitone Stirling sequence
  (Mathlib has the matching lower bound `Stirling.le_factorial_stirling`), and (4.30) as
  `abs_asymptoticRemainder_self_le`: `|R_k(k)| ≤ e · e^(−k) / √k`.

Not formalized: the power series (4.26) (needs the Euler–Mascheroni constant and the integral
representation), `Ei`, `li`, the complex domain `|arg x| < π`, the finer Stirling bound with
`e^(1/(12k))`, the threshold `x > n ln 2 + O(ln n)` as a statement about `n`.
-/

namespace Azurite

namespace BZ

open Real MeasureTheory Set Filter Topology Finset

/-! ### The tails `∫_x^∞ e^(−u) / u^(k+1) du` -/

/-- `I_k(x) = ∫_x^∞ e^(−u) / u^(k+1) du`. -/
noncomputable def expTail (k : ℕ) (x : ℝ) : ℝ := ∫ u in Ioi x, exp (-u) / u ^ (k + 1)

/-- The exponential integral `E₁(x) = ∫_x^∞ e^(−u)/u du` (4.25). -/
noncomputable def expIntegral (x : ℝ) : ℝ := expTail 0 x

theorem expIntegral_eq (x : ℝ) : expIntegral x = ∫ u in Ioi x, exp (-u) / u := by
  simp [expIntegral, expTail]

theorem continuousOn_expTail_integrand {x : ℝ} (hx : 0 < x) (k : ℕ) :
    ContinuousOn (fun u : ℝ => exp (-u) / u ^ (k + 1)) (Ioi x) :=
  (continuous_exp.comp continuous_neg).continuousOn.div (continuousOn_pow _)
    fun _ hu => pow_ne_zero _ (lt_trans hx hu).ne'

/-- The integrand is dominated by `e^(−u) x^(−(k+1))` on `Ioi x`. -/
theorem integrableOn_expTail {x : ℝ} (hx : 0 < x) (k : ℕ) :
    IntegrableOn (fun u : ℝ => exp (-u) / u ^ (k + 1)) (Ioi x) := by
  have hg : IntegrableOn (fun u : ℝ => exp (-u) * (x ^ (k + 1))⁻¹) (Ioi x) :=
    (integrableOn_exp_neg_Ioi x).mul_const _
  refine Integrable.mono' hg
    ((continuousOn_expTail_integrand hx k).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 < u := lt_trans hx hu
  rw [Real.norm_eq_abs, abs_of_pos (by positivity), div_eq_mul_inv]
  gcongr
  exact le_of_lt hu

theorem expTail_nonneg {x : ℝ} (hx : 0 < x) (k : ℕ) : 0 ≤ expTail k x :=
  setIntegral_nonneg measurableSet_Ioi fun u hu => by
    have : 0 < u := lt_trans hx hu
    positivity

theorem expTail_pos {x : ℝ} (hx : 0 < x) (k : ℕ) : 0 < expTail k x := by
  unfold expTail
  rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · refine lt_of_lt_of_le ENNReal.zero_lt_top ?_
    rw [← Real.volume_Ioi (a := x)]
    refine measure_mono fun u hu => ⟨?_, hu⟩
    have : 0 < u := lt_trans hx hu
    exact (by positivity : (0 : ℝ) < exp (-u) / u ^ (k + 1)).ne'
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have : 0 < u := lt_trans hx hu
    positivity
  · exact integrableOn_expTail hx k

/-- `I_k(x) ≤ e^(−x) / x^(k+1)`. -/
theorem expTail_le {x : ℝ} (hx : 0 < x) (k : ℕ) : expTail k x ≤ exp (-x) / x ^ (k + 1) := by
  unfold expTail
  calc ∫ u in Ioi x, exp (-u) / u ^ (k + 1)
      ≤ ∫ u in Ioi x, exp (-u) * (x ^ (k + 1))⁻¹ := by
        refine setIntegral_mono_on (integrableOn_expTail hx k)
          ((integrableOn_exp_neg_Ioi x).mul_const _) measurableSet_Ioi fun u hu => ?_
        have hu0 : 0 < u := lt_trans hx hu
        rw [div_eq_mul_inv]
        gcongr
        exact le_of_lt hu
    _ = exp (-x) / x ^ (k + 1) := by
        rw [integral_mul_const, integral_exp_neg_Ioi, div_eq_mul_inv]

/-- Integration by parts: `I_k(x) = e^(−x)/x^(k+1) − (k+1) I_{k+1}(x)`. -/
theorem expTail_succ {x : ℝ} (hx : 0 < x) (k : ℕ) :
    expTail k x = exp (-x) / x ^ (k + 1) - (k + 1) * expTail (k + 1) x := by
  -- `u t = (t^(k+1))⁻¹`, `v t = −e^(−t)`
  have hu : ∀ t ∈ Ioi x, HasDerivAt (fun t : ℝ => (t ^ (k + 1))⁻¹)
      (-(((k + 1 : ℕ) : ℝ) * t ^ (k + 1 - 1)) / (t ^ (k + 1)) ^ 2) t :=
    fun t ht => (hasDerivAt_pow (k + 1) t).inv (pow_ne_zero _ (lt_trans hx ht).ne')
  have hv : ∀ t ∈ Ioi x, HasDerivAt (fun t : ℝ => -exp (-t)) (exp (-t)) t := by
    intro t _
    have h : HasDerivAt (fun t : ℝ => -exp (-t)) (-(exp (-t) * -1)) t :=
      ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)).neg
    exact h.congr_deriv (by ring)
  -- integrability of `u v'` and `u' v`
  have huv' : IntegrableOn ((fun t : ℝ => (t ^ (k + 1))⁻¹) * fun t => exp (-t)) (Ioi x) :=
    (integrableOn_expTail hx k).congr_fun (fun t _ => by simp [div_eq_mul_inv, mul_comm])
      measurableSet_Ioi
  have hu'v : IntegrableOn
      ((fun t : ℝ => -(((k + 1 : ℕ) : ℝ) * t ^ (k + 1 - 1)) / (t ^ (k + 1)) ^ 2)
        * fun t => -exp (-t)) (Ioi x) := by
    refine IntegrableOn.congr_fun ((integrableOn_expTail hx (k + 1)).const_mul ((k + 1 : ℕ) : ℝ))
      (fun t ht => ?_) measurableSet_Ioi
    have ht0 : (t : ℝ) ≠ 0 := (lt_trans hx ht).ne'
    simp only [Pi.mul_apply, Nat.add_sub_cancel]
    field_simp
    ring
  -- the boundary terms
  have h_zero : Tendsto ((fun t : ℝ => (t ^ (k + 1))⁻¹) * fun t => -exp (-t)) (𝓝[>] x)
      (𝓝 ((x ^ (k + 1))⁻¹ * -exp (-x))) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    exact (((continuous_pow (k + 1)).continuousAt.inv₀ (pow_ne_zero _ hx.ne')).mul
      ((continuous_exp.comp continuous_neg).continuousAt.neg))
  have h_infty : Tendsto ((fun t : ℝ => (t ^ (k + 1))⁻¹) * fun t => -exp (-t)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hg : Tendsto (fun t : ℝ => exp (-t) * (x ^ (k + 1))⁻¹) atTop (𝓝 0) := by
      simpa using tendsto_exp_neg_atTop_nhds_zero.mul_const ((x ^ (k + 1))⁻¹)
    refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_ hg
    filter_upwards [eventually_gt_atTop x] with t ht
    have ht0 : 0 < t := lt_trans hx ht
    rw [Pi.mul_apply, norm_mul, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < (t ^ (k + 1))⁻¹), abs_of_pos (exp_pos _), mul_comm]
    gcongr
  have key := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v h_zero h_infty
  -- identify the two integrals
  have hL : ∫ t in Ioi x, (t ^ (k + 1))⁻¹ * exp (-t) = expTail k x := by
    unfold expTail
    exact setIntegral_congr_fun measurableSet_Ioi fun t _ => by rw [div_eq_mul_inv, mul_comm]
  have hR : ∫ t in Ioi x, -(((k + 1 : ℕ) : ℝ) * t ^ (k + 1 - 1)) / (t ^ (k + 1)) ^ 2 * -exp (-t)
      = (k + 1) * expTail (k + 1) x := by
    unfold expTail
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (t : ℝ) ≠ 0 := (lt_trans hx ht).ne'
    simp only [Nat.add_sub_cancel]
    push_cast
    field_simp
    ring
  rw [hL, hR] at key
  rw [key]
  ring

/-! ### The asymptotic expansion (4.27)–(4.29) -/

/-- The `j`-th term `j! (−1)^j / x^(j+1)` (the text's term number `j + 1`). -/
noncomputable def asymptoticTerm (j : ℕ) (x : ℝ) : ℝ := j.factorial * (-1) ^ j / x ^ (j + 1)

/-- The remainder (4.28), `R_k(x) = k! (−1)^k e^x I_k(x)`. -/
noncomputable def asymptoticRemainder (k : ℕ) (x : ℝ) : ℝ :=
  k.factorial * (-1) ^ k * exp x * expTail k x

/-- One step of the expansion: `R_k = t_k + R_{k+1}`. -/
theorem asymptoticRemainder_succ {x : ℝ} (hx : 0 < x) (k : ℕ) :
    asymptoticRemainder k x = asymptoticTerm k x + asymptoticRemainder (k + 1) x := by
  unfold asymptoticRemainder asymptoticTerm
  rw [expTail_succ hx k, Nat.factorial_succ, pow_succ]
  push_cast
  have : exp x * exp (-x) = 1 := by rw [← exp_add]; simp
  linear_combination ((k.factorial : ℝ) * (-1) ^ k / x ^ (k + 1)) * this

/-- (4.27): `e^x E₁(x) = ∑_{j<k} j! (−1)^j / x^(j+1) + R_k(x)`. -/
theorem exp_mul_expIntegral_eq {x : ℝ} (hx : 0 < x) (k : ℕ) :
    exp x * expIntegral x = ∑ j ∈ range k, asymptoticTerm j x + asymptoticRemainder k x := by
  induction k with
  | zero => simp [asymptoticRemainder, expIntegral]
  | succ k ih => rw [sum_range_succ, ih, asymptoticRemainder_succ hx k]; ring

/-- `|R_k(x)| ≤ k! / x^(k+1)`, the first omitted term. -/
theorem abs_asymptoticRemainder_le {x : ℝ} (hx : 0 < x) (k : ℕ) :
    |asymptoticRemainder k x| ≤ k.factorial / x ^ (k + 1) := by
  unfold asymptoticRemainder
  rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one,
    abs_of_pos (exp_pos x), abs_of_nonneg (expTail_nonneg hx k),
    abs_of_pos (by positivity : (0 : ℝ) < k.factorial)]
  calc (k.factorial : ℝ) * exp x * expTail k x
      ≤ k.factorial * exp x * (exp (-x) / x ^ (k + 1)) := by gcongr; exact expTail_le hx k
    _ = k.factorial / x ^ (k + 1) := by
        have : exp x * exp (-x) = 1 := by rw [← exp_add]; simp
        rw [mul_assoc, ← mul_div_assoc, this, mul_one_div]

/-- The error is bounded by the first omitted term. -/
theorem abs_asymptoticRemainder_le_abs_term {x : ℝ} (hx : 0 < x) (k : ℕ) :
    |asymptoticRemainder k x| ≤ |asymptoticTerm k x| := by
  rw [asymptoticTerm, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one,
    abs_of_pos (by positivity : (0 : ℝ) < k.factorial), abs_of_pos (pow_pos hx (k + 1))]
  exact abs_asymptoticRemainder_le hx k

/-- For fixed `k`, `R_k(x) → 0` as `x → +∞`. -/
theorem tendsto_asymptoticRemainder_atTop (k : ℕ) :
    Tendsto (asymptoticRemainder k) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hg : Tendsto (fun x : ℝ => (k.factorial : ℝ) * (x ^ (k + 1))⁻¹) atTop (𝓝 0) := by
    simpa using
      ((tendsto_pow_atTop (by omega : k + 1 ≠ 0)).inv_tendsto_atTop).const_mul (k.factorial : ℝ)
  refine squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) ?_ hg
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [Real.norm_eq_abs, ← div_eq_mul_inv]
  exact abs_asymptoticRemainder_le hx k

/-- The series (4.29) diverges for every `x > 0`: it is only asymptotic. -/
theorem not_summable_asymptoticTerm {x : ℝ} (hx : 0 < x) :
    ¬ Summable (fun j => asymptoticTerm j x) := by
  have habs : ∀ j, ‖asymptoticTerm j x‖ = j.factorial / x ^ (j + 1) := fun j => by
    rw [Real.norm_eq_abs, asymptoticTerm, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
      mul_one, abs_of_pos (by positivity : (0 : ℝ) < j.factorial), abs_of_pos (by positivity)]
  refine not_summable_of_ratio_norm_eventually_ge (r := 2) (by norm_num)
    (Eventually.of_forall fun j => by rw [habs]; positivity).frequently ?_
  filter_upwards [eventually_ge_atTop ⌈2 * x⌉₊] with j hj
  rw [habs, habs, Nat.factorial_succ]
  push_cast
  have h2x : 2 * x ≤ j := (Nat.le_ceil _).trans (by exact_mod_cast hj)
  rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity), pow_succ x (j + 1)]
  have hf : (0 : ℝ) ≤ j.factorial * x ^ (j + 1) := by positivity
  nlinarith [hf]

/-- `R_k(x)` has the sign `(−1)^k`. -/
theorem sign_asymptoticRemainder {x : ℝ} (hx : 0 < x) (k : ℕ) :
    0 < (-1) ^ k * asymptoticRemainder k x := by
  unfold asymptoticRemainder
  have : ((-1 : ℝ) ^ k) * ((-1) ^ k) = 1 := by rw [← mul_pow]; simp
  have hpos : 0 < (k.factorial : ℝ) * exp x * expTail k x := by
    have := expTail_pos hx k; positivity
  calc (0 : ℝ) < (k.factorial : ℝ) * exp x * expTail k x := hpos
    _ = (-1) ^ k * (k.factorial * (-1) ^ k * exp x * expTail k x) := by
        linear_combination (-(k.factorial : ℝ) * exp x * expTail k x) * this

/-- The value lies strictly between the partial sums with `k` and `k + 1` terms: the two
remainders have opposite signs. -/
theorem between_partialSums {x : ℝ} (hx : 0 < x) (k : ℕ) :
    (exp x * expIntegral x - ∑ j ∈ range k, asymptoticTerm j x)
      * (exp x * expIntegral x - ∑ j ∈ range (k + 1), asymptoticTerm j x) < 0 := by
  have e1 := exp_mul_expIntegral_eq hx k
  have e2 := exp_mul_expIntegral_eq hx (k + 1)
  have h1 : exp x * expIntegral x - ∑ j ∈ range k, asymptoticTerm j x
      = asymptoticRemainder k x := by linarith
  have h2 : exp x * expIntegral x - ∑ j ∈ range (k + 1), asymptoticTerm j x
      = asymptoticRemainder (k + 1) x := by linarith
  rw [h1, h2]
  have s1 := sign_asymptoticRemainder hx k
  have s2 := sign_asymptoticRemainder hx (k + 1)
  rw [pow_succ] at s2
  have hsq : ((-1 : ℝ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  nlinarith [mul_pos s1 s2, hsq]

/-! ### (4.30): the error at `k = x` -/

/-- The upper Stirling bound `k! ≤ e √k (k/e)^k`, from the antitone Stirling sequence
(`stirlingSeq k ≤ stirlingSeq 1 = e/√2`). -/
theorem factorial_le_stirling_upper {k : ℕ} (hk : 1 ≤ k) :
    (k.factorial : ℝ) ≤ exp 1 * Real.sqrt k * (k / exp 1) ^ k := by
  have hanti := Stirling.stirlingSeq'_antitone (Nat.sub_le_sub_right hk 1)
  simp only [Function.comp, Nat.sub_add_cancel hk, Nat.succ_eq_add_one, Nat.zero_add,
    Nat.sub_self] at hanti
  rw [Stirling.stirlingSeq_one, Stirling.stirlingSeq] at hanti
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hden : 0 < Real.sqrt (2 * k : ℝ) * (k / exp 1) ^ k := by positivity
  rw [div_le_iff₀ hden] at hanti
  calc (k.factorial : ℝ) ≤ exp 1 / Real.sqrt 2 * (Real.sqrt (2 * k : ℝ) * (k / exp 1) ^ k) := hanti
    _ = exp 1 * Real.sqrt k * (k / exp 1) ^ k := by
        rw [Real.sqrt_mul (by norm_num) (k : ℝ)]
        have hs2 : Real.sqrt 2 ≠ 0 := by positivity
        field_simp

/-- (4.30): `|R_k(k)| ≤ k!/k^(k+1) ≤ e · e^(−k) / √k`, so the expansion with `k = ⌊x⌋` terms has
error `O(k^(−1/2) e^(−k))`. -/
theorem abs_asymptoticRemainder_self_le {k : ℕ} (hk : 1 ≤ k) :
    |asymptoticRemainder k k| ≤ exp 1 * exp (-(k : ℝ)) / Real.sqrt k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  refine (abs_asymptoticRemainder_le hk0 k).trans ?_
  have hs := factorial_le_stirling_upper hk
  have hsk : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hk0
  rw [div_le_div_iff₀ (by positivity) hsk]
  have hpow : ((k : ℝ) / exp 1) ^ k = (k : ℝ) ^ k * exp (-(k : ℝ)) := by
    rw [div_pow, ← Real.exp_nat_mul, mul_one, exp_neg, div_eq_mul_inv]
  have hsq : Real.sqrt (k : ℝ) * Real.sqrt (k : ℝ) = k := Real.mul_self_sqrt hk0.le
  calc (k.factorial : ℝ) * Real.sqrt k ≤ exp 1 * Real.sqrt k * (k / exp 1) ^ k * Real.sqrt k :=
        mul_le_mul_of_nonneg_right hs hsk.le
    _ = exp 1 * exp (-(k : ℝ)) * (k : ℝ) ^ (k + 1) := by
        rw [hpow, pow_succ]
        linear_combination (exp 1 * exp (-(k : ℝ)) * (k : ℝ) ^ k) * hsq

end BZ

end Azurite
