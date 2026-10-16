/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BrentZimmermann.Chapter4.AsymptoticExamples
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Brent–Zimmermann §4.5: the error function

The series (4.22), (4.23) for `erf x` need `Ω(x²)` terms (`erf 1000` to six digits: 2718279 terms
from (4.22)).  Instead the complementary error function `erfc x = 1 − erf x` has the asymptotic
expansion

  `erfc x ~ e^(−x²) / (x √π) · ∑_{j=0}^k (−1)^j (2j)! / j! · (2x)^(−2j)`,                     (4.37)

with error bounded by the next term and of its sign; `erfc 1000 ≈ 1.86 · 10^(−434298)`, so the
leading term alone gives `erf 1000` extremely accurately.  The sum diverges — its `j`-th term is
`~ √2 (j / (e x²))^j` — and the terms decrease while `j < x² + 1/2`, the smallest being of order
`e^(−x²)`, so `n`-bit accuracy needs `x > √(n ln 2)` (`833` for `n = 10⁶`).  Since
`erfc x ≈ 2^(−λ)`, only `m = n − λ` bits of `erfc` are
needed for `n` bits of `erf`.  For `j < x²` the terms `x^(2j)/j!` of (4.22) increase while those of
(4.37) decrease, so (4.37) is preferable whenever it is accurate enough.  Algorithm 4.2 `Erf`:
`m = ⌈n − (x² + ln x + ln π / 2) / ln 2⌉`; if `(m + 1/2) ln 2 < x²` use (4.37) at precision `m`
and return `1 − t`; else (4.22) for `x < 1`, (4.23) otherwise; the series needs about `j₀` terms,
the root of `j (ln j − 2 ln x − 1) = n ln 2`, and the expansion fewer than `x² + 1/2`.

What is formalized (Lebesgue integrals on `Ioi x`, `x > 0`):

* `gaussTail k x = ∫_x^∞ e^(−u²)/u^(2k) du`, `erfc x = (2/√π) gaussTail 0 x`, `erf x = 1 − erfc x`;
  `integrableOn_gaussTail`, `gaussTail_pos`, the integration by parts `gaussTail_succ`
  (`J_k = e^(−x²)/(2x^(2k+1)) − (2k+1)/2 · J_{k+1}`) and `gaussTail_le`.
* `erfcCoeff j = (2j)!/(j! 4^j)` (`= (2j−1)!!/2^j`) with `erfcCoeff_succ`; the expansion (4.37)
  `erfc_eq_sum_add_rem` with `erfcTerm`/`erfcRem`, `abs_erfcRem_le_abs_term` (error ≤ next
  term), `sign_erfcRem` (its sign), `erfc_le_leading`, `leading_mul_le_erfc`
  (`erfc x ∈ [L (1 − 1/(2x²)), L]`, `L = e^(−x²)/(x√π)`).
* `erfcTermMag_succ_lt` (the terms of (4.37) decrease while `2j + 1 < 2x²`),
  `pow_div_factorial_le_succ` (those of (4.22) increase while `j + 1 ≤ x²`),
  `erfcCoeff_le_stirling` (`c_j ≤ (e/√π)(j/e)^j`), `erfcTermMag_le` (`≤ (e/√π)(j/(e x²))^j`,
  `≤ (e/√π) e^(−j)` for `j ≤ x²`): the smallest term is of order `e^(−x²)`.
* `erfSeriesTerm_le_two_pow` — the `j₀` criterion: `n ln 2 ≤ j (ln j − 2 ln x − 1)` gives
  `x^(2j)/j! ≤ 2^(−n)`; `erf_error_of_erfc` — `m` bits of `erfc` give `n` bits of `erf`;
  `asymptotic_gives_bits` — `(m + 4) ln 2 ≤ x²` suffices for a relative error `2^(−m)` of (4.37)
  with `⌊x²⌋` terms (the text's `(m + 1/2) ln 2 < x²`, with a cruder constant).

Not formalized: the connection `erf x = (2/√π) ∫_0^x e^(−u²)` and oddness (needs the Gaussian
integral), (4.22)/(4.23) as series of `erf`, the numerical examples, the continued fraction (4.40).
-/

namespace Azurite

namespace BZ

open Real MeasureTheory Set Filter Topology Finset

/-! ### The tails `∫_x^∞ e^(−u²) / u^(2k) du` -/

/-- `J_k(x) = ∫_x^∞ e^(−u²) / u^(2k) du`. -/
noncomputable def gaussTail (k : ℕ) (x : ℝ) : ℝ := ∫ u in Ioi x, exp (-u ^ 2) / u ^ (2 * k)

/-- `erfc x = (2/√π) ∫_x^∞ e^(−u²) du`. -/
noncomputable def erfc (x : ℝ) : ℝ := 2 / Real.sqrt π * gaussTail 0 x

/-- `erf x = 1 − erfc x`. -/
noncomputable def erf (x : ℝ) : ℝ := 1 - erfc x

theorem integrableOn_exp_neg_sq_Ioi (x : ℝ) : IntegrableOn (fun u : ℝ => exp (-u ^ 2)) (Ioi x) := by
  have := (integrable_exp_neg_mul_sq (b := 1) one_pos).integrableOn (s := Ioi x)
  refine this.congr_fun (fun u _ => ?_) measurableSet_Ioi
  simp

theorem continuousOn_gaussTail_integrand {x : ℝ} (hx : 0 < x) (k : ℕ) :
    ContinuousOn (fun u : ℝ => exp (-u ^ 2) / u ^ (2 * k)) (Ioi x) :=
  (continuous_exp.comp (continuous_pow 2).neg).continuousOn.div (continuousOn_pow _)
    fun _ hu => pow_ne_zero _ (lt_trans hx hu).ne'

theorem integrableOn_gaussTail {x : ℝ} (hx : 0 < x) (k : ℕ) :
    IntegrableOn (fun u : ℝ => exp (-u ^ 2) / u ^ (2 * k)) (Ioi x) := by
  have hg : IntegrableOn (fun u : ℝ => exp (-u ^ 2) * (x ^ (2 * k))⁻¹) (Ioi x) :=
    (integrableOn_exp_neg_sq_Ioi x).mul_const _
  refine Integrable.mono' hg
    ((continuousOn_gaussTail_integrand hx k).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 < u := lt_trans hx hu
  rw [Real.norm_eq_abs, abs_of_pos (by positivity), div_eq_mul_inv]
  gcongr
  exact le_of_lt hu

theorem gaussTail_nonneg {x : ℝ} (hx : 0 < x) (k : ℕ) : 0 ≤ gaussTail k x :=
  setIntegral_nonneg measurableSet_Ioi fun u hu => by
    have : 0 < u := lt_trans hx hu
    positivity

theorem gaussTail_pos {x : ℝ} (hx : 0 < x) (k : ℕ) : 0 < gaussTail k x := by
  unfold gaussTail
  rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · refine lt_of_lt_of_le ENNReal.zero_lt_top ?_
    rw [← Real.volume_Ioi (a := x)]
    refine measure_mono fun u hu => ⟨?_, hu⟩
    have : 0 < u := lt_trans hx hu
    exact (by positivity : (0 : ℝ) < exp (-u ^ 2) / u ^ (2 * k)).ne'
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have : 0 < u := lt_trans hx hu
    positivity
  · exact integrableOn_gaussTail hx k

/-- Integration by parts: `J_k(x) = e^(−x²)/(2 x^(2k+1)) − (2k+1)/2 · J_{k+1}(x)`. -/
theorem gaussTail_succ {x : ℝ} (hx : 0 < x) (k : ℕ) :
    gaussTail k x
      = exp (-x ^ 2) / (2 * x ^ (2 * k + 1)) - (2 * k + 1) / 2 * gaussTail (k + 1) x := by
  -- `u t = (t^(2k+1))⁻¹`, `v t = −e^(−t²)/2`, `v' t = t e^(−t²)`
  have hu : ∀ t ∈ Ioi x, HasDerivAt (fun t : ℝ => (t ^ (2 * k + 1))⁻¹)
      (-(((2 * k + 1 : ℕ) : ℝ) * t ^ (2 * k + 1 - 1)) / (t ^ (2 * k + 1)) ^ 2) t :=
    fun t ht => (hasDerivAt_pow (2 * k + 1) t).inv (pow_ne_zero _ (lt_trans hx ht).ne')
  have hv : ∀ t ∈ Ioi x, HasDerivAt (fun t : ℝ => -exp (-t ^ 2) / 2) (t * exp (-t ^ 2)) t := by
    intro t _
    have hin : HasDerivAt (fun t : ℝ => -t ^ 2) (-(2 * t)) t :=
      (hasDerivAt_pow 2 t).neg.congr_deriv (by norm_num)
    have h := (((Real.hasDerivAt_exp (-t ^ 2)).comp t hin).neg).div_const 2
    exact h.congr_deriv (by ring)
  have huv' : IntegrableOn ((fun t : ℝ => (t ^ (2 * k + 1))⁻¹) * fun t => t * exp (-t ^ 2))
      (Ioi x) :=
    (integrableOn_gaussTail hx k).congr_fun (fun t ht => by
      have ht0 : (t : ℝ) ≠ 0 := (lt_trans hx ht).ne'
      simp only [Pi.mul_apply]
      field_simp
      ring) measurableSet_Ioi
  have hu'v : IntegrableOn
      ((fun t : ℝ => -(((2 * k + 1 : ℕ) : ℝ) * t ^ (2 * k + 1 - 1)) / (t ^ (2 * k + 1)) ^ 2)
        * fun t => -exp (-t ^ 2) / 2) (Ioi x) := by
    refine IntegrableOn.congr_fun
      ((integrableOn_gaussTail hx (k + 1)).const_mul (((2 * k + 1 : ℕ) : ℝ) / 2))
      (fun t ht => ?_) measurableSet_Ioi
    have ht0 : (t : ℝ) ≠ 0 := (lt_trans hx ht).ne'
    simp only [Pi.mul_apply, Nat.add_sub_cancel]
    field_simp
    ring
  have h_zero : Tendsto ((fun t : ℝ => (t ^ (2 * k + 1))⁻¹) * fun t => -exp (-t ^ 2) / 2) (𝓝[>] x)
      (𝓝 ((x ^ (2 * k + 1))⁻¹ * (-exp (-x ^ 2) / 2))) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    exact (((continuous_pow (2 * k + 1)).continuousAt.inv₀ (pow_ne_zero _ hx.ne')).mul
      (((continuous_exp.comp (continuous_pow 2).neg).continuousAt.neg).div_const 2))
  have h_infty : Tendsto ((fun t : ℝ => (t ^ (2 * k + 1))⁻¹) * fun t => -exp (-t ^ 2) / 2) atTop
      (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hg : Tendsto (fun t : ℝ => exp (-t) * ((x ^ (2 * k + 1))⁻¹ / 2)) atTop (𝓝 0) := by
      simpa using tendsto_exp_neg_atTop_nhds_zero.mul_const ((x ^ (2 * k + 1))⁻¹ / 2)
    refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_ hg
    filter_upwards [eventually_gt_atTop (max x 1)] with t ht
    have ht0 : 0 < t := lt_trans hx (lt_of_le_of_lt (le_max_left _ _) ht)
    have ht1 : 1 < t := lt_of_le_of_lt (le_max_right _ _) ht
    have htx : x < t := lt_of_le_of_lt (le_max_left _ _) ht
    rw [Pi.mul_apply, norm_mul, norm_div, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < (t ^ (2 * k + 1))⁻¹),
      abs_of_pos (exp_pos _), abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hexp : exp (-t ^ 2) ≤ exp (-t) := exp_le_exp.mpr (by nlinarith)
    calc (t ^ (2 * k + 1))⁻¹ * (exp (-t ^ 2) / 2)
        ≤ (x ^ (2 * k + 1))⁻¹ * (exp (-t) / 2) := by gcongr
      _ = exp (-t) * ((x ^ (2 * k + 1))⁻¹ / 2) := by ring
  have key := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v h_zero h_infty
  have hL : ∫ t in Ioi x, (t ^ (2 * k + 1))⁻¹ * (t * exp (-t ^ 2)) = gaussTail k x := by
    unfold gaussTail
    exact setIntegral_congr_fun measurableSet_Ioi fun t ht => by
      have ht0 : (t : ℝ) ≠ 0 := (lt_trans hx ht).ne'
      field_simp
      ring
  have hR : ∫ t in Ioi x,
      -(((2 * k + 1 : ℕ) : ℝ) * t ^ (2 * k + 1 - 1)) / (t ^ (2 * k + 1)) ^ 2 * (-exp (-t ^ 2) / 2)
        = (2 * k + 1) / 2 * gaussTail (k + 1) x := by
    unfold gaussTail
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

/-- `J_k(x) ≤ e^(−x²) / (2 x^(2k+1))`. -/
theorem gaussTail_le {x : ℝ} (hx : 0 < x) (k : ℕ) :
    gaussTail k x ≤ exp (-x ^ 2) / (2 * x ^ (2 * k + 1)) := by
  have h := gaussTail_succ hx k
  have := gaussTail_nonneg hx (k + 1)
  have hk : (0 : ℝ) ≤ (2 * k + 1) / 2 := by positivity
  nlinarith

/-! ### The expansion (4.37) -/

/-- `c_j = (2j)! / (j! 4^j) = (2j−1)!! / 2^j`, the magnitude of the `j`-th coefficient of (4.37). -/
noncomputable def erfcCoeff (j : ℕ) : ℝ := (2 * j).factorial / (j.factorial * 4 ^ j)

theorem erfcCoeff_pos (j : ℕ) : 0 < erfcCoeff j := by unfold erfcCoeff; positivity

/-- `c_{j+1} = c_j (2j+1)/2`. -/
theorem erfcCoeff_succ (j : ℕ) : erfcCoeff (j + 1) = erfcCoeff j * ((2 * j + 1) / 2) := by
  unfold erfcCoeff
  rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
    Nat.factorial_succ, pow_succ]
  push_cast
  field_simp
  ring

theorem erfcCoeff_zero : erfcCoeff 0 = 1 := by simp [erfcCoeff]

/-- The `j`-th term of (4.37): `(−1)^j c_j e^(−x²) / (√π x^(2j+1))`. -/
noncomputable def erfcTerm (j : ℕ) (x : ℝ) : ℝ :=
  (-1) ^ j * erfcCoeff j * exp (-x ^ 2) / (Real.sqrt π * x ^ (2 * j + 1))

/-- The remainder after `k` terms, `(2/√π) (−1)^k c_k J_k(x)`. -/
noncomputable def erfcRem (k : ℕ) (x : ℝ) : ℝ :=
  2 / Real.sqrt π * ((-1) ^ k * erfcCoeff k) * gaussTail k x

theorem erfcRem_succ {x : ℝ} (hx : 0 < x) (k : ℕ) :
    erfcRem k x = erfcTerm k x + erfcRem (k + 1) x := by
  unfold erfcRem erfcTerm
  rw [gaussTail_succ hx k, erfcCoeff_succ, pow_succ]
  have hπ : 0 < Real.sqrt π := Real.sqrt_pos.mpr pi_pos
  field_simp
  ring

/-- (4.37): `erfc x = ∑_{j<k} (−1)^j c_j e^(−x²)/(√π x^(2j+1)) + R_k(x)`. -/
theorem erfc_eq_sum_add_rem {x : ℝ} (hx : 0 < x) (k : ℕ) :
    erfc x = ∑ j ∈ range k, erfcTerm j x + erfcRem k x := by
  induction k with
  | zero => simp [erfc, erfcRem, erfcCoeff_zero]
  | succ k ih => rw [sum_range_succ, ih, erfcRem_succ hx k]; ring

/-- The error is bounded by the next term: `|R_k(x)| ≤ |t_k(x)|`. -/
theorem abs_erfcRem_le_abs_term {x : ℝ} (hx : 0 < x) (k : ℕ) :
    |erfcRem k x| ≤ |erfcTerm k x| := by
  have hπ : 0 < Real.sqrt π := Real.sqrt_pos.mpr pi_pos
  have hc := erfcCoeff_pos k
  have hJ := gaussTail_le hx k
  have hJ0 := gaussTail_pos hx k
  have hL : |erfcRem k x| = 2 / Real.sqrt π * erfcCoeff k * gaussTail k x := by
    unfold erfcRem
    simp only [abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hπ, abs_of_pos hc, abs_of_pos hJ0]
  have hR : |erfcTerm k x| = erfcCoeff k * exp (-x ^ 2) / (Real.sqrt π * x ^ (2 * k + 1)) := by
    unfold erfcTerm
    simp only [abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    rw [abs_of_pos hc, abs_of_pos (exp_pos _), abs_of_pos hπ, abs_of_pos hx]
  rw [hL, hR]
  calc 2 / Real.sqrt π * erfcCoeff k * gaussTail k x
      ≤ 2 / Real.sqrt π * erfcCoeff k * (exp (-x ^ 2) / (2 * x ^ (2 * k + 1))) := by gcongr
    _ = erfcCoeff k * exp (-x ^ 2) / (Real.sqrt π * x ^ (2 * k + 1)) := by
        field_simp

/-- `R_k(x)` has the sign `(−1)^k`. -/
theorem sign_erfcRem {x : ℝ} (hx : 0 < x) (k : ℕ) : 0 < (-1) ^ k * erfcRem k x := by
  unfold erfcRem
  have hsq : ((-1 : ℝ) ^ k) * ((-1) ^ k) = 1 := by rw [← mul_pow]; simp
  have hπ : 0 < Real.sqrt π := Real.sqrt_pos.mpr pi_pos
  have hpos : 0 < 2 / Real.sqrt π * erfcCoeff k * gaussTail k x := by
    have := gaussTail_pos hx k; have := erfcCoeff_pos k; positivity
  calc (0 : ℝ) < 2 / Real.sqrt π * erfcCoeff k * gaussTail k x := hpos
    _ = (-1) ^ k * (2 / Real.sqrt π * ((-1) ^ k * erfcCoeff k) * gaussTail k x) := by
        linear_combination (-(2 / Real.sqrt π * erfcCoeff k * gaussTail k x)) * hsq

/-- `erfc x ≤ e^(−x²) / (x √π)`: the leading term is an upper bound. -/
theorem erfc_le_leading {x : ℝ} (hx : 0 < x) : erfc x ≤ exp (-x ^ 2) / (x * Real.sqrt π) := by
  have h := gaussTail_le hx 0
  have hπ : 0 < Real.sqrt π := Real.sqrt_pos.mpr pi_pos
  unfold erfc
  simp only [mul_zero, zero_add, pow_one] at h
  calc 2 / Real.sqrt π * gaussTail 0 x ≤ 2 / Real.sqrt π * (exp (-x ^ 2) / (2 * x)) := by gcongr
    _ = exp (-x ^ 2) / (x * Real.sqrt π) := by field_simp

/-- `erfc x ≥ e^(−x²)/(x√π) · (1 − 1/(2x²))`: two terms of (4.37) bracket `erfc x`. -/
theorem leading_mul_le_erfc {x : ℝ} (hx : 0 < x) :
    exp (-x ^ 2) / (x * Real.sqrt π) * (1 - 1 / (2 * x ^ 2)) ≤ erfc x := by
  have h := erfc_eq_sum_add_rem hx 2
  have hs : 0 < erfcRem 2 x := by
    have := sign_erfcRem hx 2
    rwa [show ((-1 : ℝ)) ^ 2 = 1 by norm_num, one_mul] at this
  have hπ : 0 < Real.sqrt π := Real.sqrt_pos.mpr pi_pos
  simp only [sum_range_succ, sum_range_zero, zero_add] at h
  have h2 : erfcTerm 0 x + erfcTerm 1 x
      = exp (-x ^ 2) / (x * Real.sqrt π) * (1 - 1 / (2 * x ^ 2)) := by
    unfold erfcTerm
    rw [erfcCoeff_succ, erfcCoeff_zero]
    simp only [mul_zero, zero_add, pow_zero, pow_one, one_mul, mul_one]
    field_simp
    ring
  linarith

/-! ### The behaviour of the terms -/

/-- The magnitude of the `j`-th term of the sum in (4.37) relative to the leading factor,
`c_j / x^(2j) = (2j)! / (j! (2x)^(2j))`. -/
noncomputable def erfcTermMag (j : ℕ) (x : ℝ) : ℝ := erfcCoeff j / x ^ (2 * j)

/-- The terms of (4.37) decrease while `2j + 1 < 2x²` (i.e. `j + 1 < x² + 1/2`). -/
theorem erfcTermMag_succ_lt {x : ℝ} (hx : 0 < x) {j : ℕ} (hj : 2 * (j : ℝ) + 1 < 2 * x ^ 2) :
    erfcTermMag (j + 1) x < erfcTermMag j x := by
  unfold erfcTermMag
  have hc := erfcCoeff_pos j
  have hxj : 0 < x ^ (2 * j) := by positivity
  rw [erfcCoeff_succ, show 2 * (j + 1) = 2 * j + 2 by ring, pow_add,
    div_lt_div_iff₀ (by positivity) hxj]
  have hcx := mul_pos hc hxj
  nlinarith [hcx, hj]

/-- The terms `x^(2j)/j!` of (4.22) increase while `j + 1 ≤ x²`. -/
theorem pow_div_factorial_le_succ {x : ℝ} {j : ℕ} (hj : (j : ℝ) + 1 ≤ x ^ 2) :
    x ^ (2 * j) / j.factorial ≤ x ^ (2 * (j + 1)) / (j + 1).factorial := by
  rw [Nat.factorial_succ, show 2 * (j + 1) = 2 * j + 2 by ring, pow_add]
  push_cast
  have hf : (0 : ℝ) < j.factorial := by positivity
  have hf' : (0 : ℝ) < ((j : ℝ) + 1) * j.factorial := by positivity
  rw [div_le_div_iff₀ hf hf']
  have hx2 : 0 ≤ x ^ (2 * j) := Even.pow_nonneg (even_two_mul j) x
  nlinarith [mul_nonneg hx2 hf.le]

/-- Stirling: `c_j ≤ (e/√π) (j/e)^j` for `j ≥ 1`. -/
theorem erfcCoeff_le_stirling {j : ℕ} (hj : 1 ≤ j) :
    erfcCoeff j ≤ exp 1 / Real.sqrt π * (j / exp 1) ^ j := by
  unfold erfcCoeff
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hup := factorial_le_stirling_upper (k := 2 * j) (by omega)
  have hlo := Stirling.le_factorial_stirling j
  have hπ : 0 < Real.sqrt π := Real.sqrt_pos.mpr pi_pos
  have hden : 0 < (j.factorial : ℝ) * 4 ^ j := by positivity
  rw [div_le_iff₀ hden]
  push_cast at hup hlo
  have h4 : (4 : ℝ) ^ j = 2 ^ j * 2 ^ j := by rw [← mul_pow]; norm_num
  have hpow : ((2 * j : ℝ) / exp 1) ^ (2 * j) = 4 ^ j * ((j / exp 1) ^ j) ^ 2 := by
    rw [pow_mul, show ((2 * j : ℝ) / exp 1) ^ 2 = 4 * (j / exp 1) ^ 2 by ring, mul_pow, ← pow_mul,
      ← pow_mul, mul_comm 2 j]
  have hsqrt : Real.sqrt (2 * j : ℝ) = Real.sqrt 2 * Real.sqrt j := Real.sqrt_mul (by norm_num) _
  have hsqrt2 : Real.sqrt (2 * π * j) = Real.sqrt 2 * Real.sqrt π * Real.sqrt j := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num)]
  calc ((2 * j).factorial : ℝ)
      ≤ exp 1 * Real.sqrt (2 * j : ℝ) * ((2 * j : ℝ) / exp 1) ^ (2 * j) := hup
    _ = exp 1 / Real.sqrt π * (j / exp 1) ^ j
        * ((Real.sqrt (2 * π * j) * (j / exp 1) ^ j) * 4 ^ j) := by
        rw [hpow, hsqrt, hsqrt2]
        field_simp
    _ ≤ exp 1 / Real.sqrt π * (j / exp 1) ^ j * (j.factorial * 4 ^ j) := by gcongr

/-- The terms of (4.37) are at most `(e/√π) (j / (e x²))^j`, and at most `(e/√π) e^(−j)` for
`j ≤ x²`: the smallest term is of order `e^(−x²)`. -/
theorem erfcTermMag_le {x : ℝ} (hx : 0 < x) {j : ℕ} (hj : 1 ≤ j) :
    erfcTermMag j x ≤ exp 1 / Real.sqrt π * (j / (exp 1 * x ^ 2)) ^ j ∧
      ((j : ℝ) ≤ x ^ 2 → erfcTermMag j x ≤ exp 1 / Real.sqrt π * exp (-(j : ℝ))) := by
  have hπ : 0 < Real.sqrt π := Real.sqrt_pos.mpr pi_pos
  have h1 : erfcTermMag j x ≤ exp 1 / Real.sqrt π * (j / (exp 1 * x ^ 2)) ^ j := by
    unfold erfcTermMag
    rw [div_le_iff₀ (by positivity)]
    calc erfcCoeff j ≤ exp 1 / Real.sqrt π * (j / exp 1) ^ j := erfcCoeff_le_stirling hj
      _ = exp 1 / Real.sqrt π * (j / (exp 1 * x ^ 2)) ^ j * x ^ (2 * j) := by
          rw [mul_assoc, pow_mul, ← mul_pow]
          congr 2
          field_simp
  refine ⟨h1, fun hjx => h1.trans ?_⟩
  gcongr
  calc ((j : ℝ) / (exp 1 * x ^ 2)) ^ j ≤ (1 / exp 1) ^ j := by
        refine pow_le_pow_left₀ (by positivity) ?_ j
        rw [div_le_div_iff₀ (by positivity) (exp_pos 1)]
        nlinarith [exp_pos 1]
    _ = exp (-(j : ℝ)) := by
        rw [one_div, inv_pow, ← Real.exp_nat_mul, mul_one, exp_neg]

/-! ### Algorithm 4.2 `Erf`: the bookkeeping -/

/-- The `j₀` criterion for the series (4.22)/(4.23): if `n ln 2 ≤ j (ln j − 2 ln x − 1)` then
`x^(2j)/j! ≤ 2^(−n)` (Stirling's lower bound `j! ≥ (j/e)^j`). -/
theorem erfSeriesTerm_le_two_pow {x : ℝ} (hx : 0 < x) {j : ℕ} (hj : 1 ≤ j) {n : ℕ}
    (h : (n : ℝ) * Real.log 2 ≤ j * (Real.log j - 2 * Real.log x - 1)) :
    x ^ (2 * j) / j.factorial ≤ (2 : ℝ) ^ (-(n : ℤ)) := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hlo := Stirling.le_factorial_stirling j
  have hlo' : ((j : ℝ) / exp 1) ^ j ≤ j.factorial := by
    refine le_trans ?_ hlo
    have : 1 ≤ Real.sqrt (2 * π * j) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]
      have : (1 : ℝ) ≤ j := by exact_mod_cast hj
      nlinarith [Real.pi_gt_three]
    nlinarith [pow_pos (div_pos hj0 (exp_pos 1)) j]
  have hf : (0 : ℝ) < j.factorial := by positivity
  calc x ^ (2 * j) / j.factorial ≤ x ^ (2 * j) / ((j : ℝ) / exp 1) ^ j :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hlo'
    _ = exp (-(j * (Real.log j - 2 * Real.log x - 1))) := by
        have hxe : x ^ (2 * j) = exp (((2 * j : ℕ) : ℝ) * Real.log x) := by
          conv_lhs => rw [← Real.exp_log hx]
          rw [← Real.exp_nat_mul]
        have hje : ((j : ℝ) / exp 1) ^ j = exp ((j : ℝ) * (Real.log j - 1)) := by
          have : (j : ℝ) / exp 1 = exp (Real.log j - 1) := by
            rw [Real.exp_sub, Real.exp_log hj0]
          conv_lhs => rw [this]
          rw [← Real.exp_nat_mul]
        rw [hxe, hje, ← Real.exp_sub]
        congr 1
        push_cast
        ring
    _ ≤ (2 : ℝ) ^ (-(n : ℤ)) := by
        rw [zpow_neg, zpow_natCast, ← Real.exp_log (by positivity : (0 : ℝ) < 2 ^ n), Real.log_pow,
          ← Real.exp_neg]
        exact exp_le_exp.mpr (by linarith)

/-- `m` bits of `erfc x` give `n` bits of `erf x = 1 − erfc x`: an approximation `t` of `erfc x`
with absolute error `ε` gives `1 − t` with the same absolute error. -/
theorem erf_error_of_erfc (x t ε : ℝ) (h : |t - erfc x| ≤ ε) : |(1 - t) - erf x| ≤ ε := by
  unfold erf
  rw [show (1 - t) - (1 - erfc x) = -(t - erfc x) by ring, abs_neg]
  exact h

/-- The condition of Algorithm `Erf` (with a cruder constant): if `(m + 4) ln 2 ≤ x²` then (4.37)
with `k = ⌊x²⌋` terms has relative error at most `2^(−m)`. -/
theorem asymptotic_gives_bits {x : ℝ} (hx : 1 ≤ x) {m : ℕ}
    (hm : ((m : ℝ) + 4) * Real.log 2 ≤ x ^ 2) :
    |erfcRem ⌊x ^ 2⌋₊ x| ≤ (2 : ℝ) ^ (-(m : ℤ)) * erfc x := by
  have hx0 : 0 < x := by linarith
  have hπ : 0 < Real.sqrt π := Real.sqrt_pos.mpr pi_pos
  set k := ⌊x ^ 2⌋₊ with hk
  have hk1 : 1 ≤ k := by
    rw [hk]; exact Nat.le_floor (by push_cast; nlinarith)
  have hkx : (k : ℝ) ≤ x ^ 2 := Nat.floor_le (by positivity)
  have hxk : x ^ 2 < k + 1 := Nat.lt_floor_add_one _
  -- `|R_k| ≤ |t_k| = c_k/x^(2k) · L`, `L = e^(−x²)/(x√π)`
  have hL : 0 < exp (-x ^ 2) / (x * Real.sqrt π) := by positivity
  have hterm : |erfcTerm k x| = erfcTermMag k x * (exp (-x ^ 2) / (x * Real.sqrt π)) := by
    unfold erfcTerm erfcTermMag
    rw [abs_div, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_pos (erfcCoeff_pos k), abs_of_pos (exp_pos _), abs_mul, abs_of_pos hπ,
      abs_of_pos (pow_pos hx0 _), pow_succ]
    field_simp
    ring
  -- `erfc x ≥ L/2` since `x ≥ 1`
  have hlow : exp (-x ^ 2) / (x * Real.sqrt π) / 2 ≤ erfc x := by
    have h := leading_mul_le_erfc hx0
    have : (1 : ℝ) / 2 ≤ 1 - 1 / (2 * x ^ 2) := by
      have : 1 / (2 * x ^ 2) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
      linarith
    nlinarith
  -- the term bound `erfcTermMag k x ≤ (e/√π) e^(−k) ≤ (e²/√π) e^(−x²)`
  have hmag := (erfcTermMag_le hx0 hk1).2 hkx
  have hek : exp (-(k : ℝ)) ≤ exp 1 * exp (-x ^ 2) := by
    rw [← exp_add]; exact exp_le_exp.mpr (by linarith)
  -- `(2e²/√π) e^(−x²) ≤ 16 e^(−x²) ≤ 2^(−m)` from `(m + 4) ln 2 ≤ x²`
  have hconst : 2 * (exp 1 / Real.sqrt π * exp 1) ≤ 16 := by
    have he : exp 1 ≤ 2.72 := by linarith [Real.exp_one_lt_d9]
    have hπ' : 1 ≤ Real.sqrt π := by
      rw [Real.le_sqrt (by norm_num) pi_pos.le]; nlinarith [Real.pi_gt_three]
    have : exp 1 / Real.sqrt π ≤ exp 1 := div_le_self (exp_pos 1).le hπ'
    nlinarith [exp_pos 1]
  have hexp : 16 * exp (-x ^ 2) ≤ (2 : ℝ) ^ (-(m : ℤ)) := by
    rw [zpow_neg, zpow_natCast, ← Real.exp_log (by positivity : (0 : ℝ) < 2 ^ m), Real.log_pow,
      ← exp_neg, show (16 : ℝ) = exp (Real.log 16) by rw [Real.exp_log (by norm_num)], ← exp_add]
    apply exp_le_exp.mpr
    have h16 : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; push_cast; ring
    rw [h16]; linarith
  calc |erfcRem k x| ≤ |erfcTerm k x| := abs_erfcRem_le_abs_term hx0 k
    _ = erfcTermMag k x * (exp (-x ^ 2) / (x * Real.sqrt π)) := hterm
    _ ≤ exp 1 / Real.sqrt π * (exp 1 * exp (-x ^ 2)) * (exp (-x ^ 2) / (x * Real.sqrt π)) := by
        gcongr
        exact hmag.trans (by gcongr)
    _ = 2 * (exp 1 / Real.sqrt π * exp 1) * exp (-x ^ 2)
          * (exp (-x ^ 2) / (x * Real.sqrt π) / 2) := by
        ring
    _ ≤ 16 * exp (-x ^ 2) * erfc x := by gcongr
    _ ≤ (2 : ℝ) ^ (-(m : ℤ)) * erfc x := by
        have herfc : 0 ≤ erfc x := le_trans (by positivity) hlow
        gcongr

end BZ

end Azurite
