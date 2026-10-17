/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BrentZimmermann.Chapter4.BitBurst
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Brent–Zimmermann §4.10: Contour integration

With `f(z) = ∑ a_j z^j` holomorphic on `|z| < R`, `R > 1`, Cauchy gives
`a_j = (2πi)⁻¹ ∮_{|z|=1} f(z) z^(−j−1) dz` (4.83), approximated by the discrete sums
`S_{j,k} = (1/k) ∑_{m<k} f(e^(2πim/k)) e^(−2πijm/k)` (4.84); for `j < k`,
`S_{j,k} − a_j = a_{j+k} + a_{j+2k} + ⋯` (4.85), so `|S_{j,k} − a_j| = O((R − δ)^(−(j+k)))`.  For
`f(z) = z/(e^z − 1) + z/2` (4.86), `a_{2j} = B_{2j}/(2j)!` and `R = 2π`, giving (4.87) and
`B_{2j}` with relative error `O((2π)^(−k))` from `k` evaluations on the unit circle; `O(j)` guard
digits are needed (cancellation), the time is `O(j n M(n))` and the space `O(n)` — against
`Θ(jn)` space for the recurrence method of §4.7.2.

What is formalized (all proven):

* (4.83) `hasSum_cauchy_coeff`: for `f` complex-differentiable on the closed unit disc,
  `f(z) = ∑_j ((2πi)⁻¹ ∮_{|w|=1} f(w)/w^(j+1) dw) z^j` on `|z| < 1` (Mathlib's
  `DifferentiableOn.hasFPowerSeriesOnBall` and `cauchyPowerSeries_apply`).
* (4.84)/(4.85) for a series `f(z) = ∑ a_l z^l` with `∑ ‖a_l‖ < ∞`: `aliasSum a j k` is `S_{j,k}`
  with `f` given by the series, `sum_zpow_primitiveRoot` is the orthogonality
  `∑_{m<k} ζ^(dm) = k·[k ∣ d]`, `aliasSum_eq_tsum : S_{j,k} = ∑_{m≥0} a_{j+mk}` and
  `aliasSum_sub_eq : S_{j,k} − a_j = ∑_{m≥1} a_{j+mk}` (no contour integral is needed for this
  half of (4.85)); the bound `norm_aliasSum_sub_le`: `‖a_l‖ ≤ C r^l`, `r < 1` ⇒
  `‖S_{j,k} − a_j‖ ≤ C r^(j+k)/(1 − r^k)`.
* (4.86)/(4.87): `bernoulliCoeff l` = the `l`-th coefficient of `z/(e^z − 1) + z/2` (the formal
  series `scaledBernoulliPowerSeries` of §4.7.2, `= B_l/l!` for `l ≠ 1`), with the Cauchy-type
  bound `norm_bernoulliCoeff_le : ‖a_l‖ ≤ (π²/3)(2π)^(−l)` (from `abs_scaledBernoulli_le`), hence
  `bernoulli_aliasSum_sub_eq` (4.87) and the relative error `norm_bernoulli_aliasSum_sub_le`:
  `‖S_{2j,k} − B_{2j}/(2j)!‖ ≤ (π²/6)(2π)^(−k)/(1 − (2π)^(−k)) · ‖B_{2j}/(2j)!‖`.

Not formalized: the contour-integral form of (4.85) (Exercise 4.50; the series form above is what
the error analysis uses), the identification of the function `z/(e^z − 1) + z/2` with its series
on `|z| < 2π` (radius `2π` is not in Mathlib — the formal series is used directly), the
cancellation/guard-digit remark, and the time `O(jnM(n))`/space `O(n)` statements.
-/

namespace Azurite

namespace BZ

open Complex Finset

/-! ### (4.83) Cauchy's coefficient formula -/

/-- (4.83): on `|z| < 1`, `f(z) = ∑_j a_j z^j` with `a_j = (2πi)⁻¹ ∮_{|w|=1} f(w)/w^(j+1) dw`, for
`f` complex-differentiable on the closed unit disc. -/
theorem hasSum_cauchy_coeff {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (Metric.closedBall 0 1))
    {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun j : ℕ => ((2 * Real.pi * I)⁻¹ * ∮ w in C(0, 1), f w / w ^ (j + 1)) * z ^ j)
      (f z) := by
  have hf' : DifferentiableOn ℂ f (Metric.closedBall 0 ((1 : NNReal) : ℝ)) := by simpa using hf
  have h := hf'.hasFPowerSeriesOnBall one_pos
  have hz' : z ∈ Metric.eball (0 : ℂ) ((1 : NNReal) : ENNReal) := by
    rw [Metric.mem_eball, edist_dist, dist_zero_right, ENNReal.coe_one, ← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff one_pos).mpr hz
  have h2 := h.hasSum hz'
  rw [zero_add] at h2
  simp only [NNReal.coe_one] at h2
  convert h2 using 1
  funext n
  rw [cauchyPowerSeries_apply]
  simp only [sub_zero, smul_eq_mul]
  have e' : (∮ w in C(0, 1), (z / w) ^ n * (w⁻¹ * f w))
      = z ^ n * ∮ w in C(0, 1), f w / w ^ (n + 1) := by
    rw [← circleIntegral.integral_const_mul]
    congr 1
    funext w
    rw [div_pow, pow_succ]
    ring
  rw [e']
  ring

/-! ### (4.84)/(4.85) the aliasing identity -/

variable {a : ℕ → ℂ}

/-- `S_{j,k} = (1/k) ∑_{m<k} f(ζ^m) ζ^(−jm)` with `ζ = e^(2πi/k)` and `f(z) = ∑ a_l z^l`. -/
noncomputable def aliasSum (a : ℕ → ℂ) (j k : ℕ) : ℂ :=
  (1 / k : ℂ) * ∑ m ∈ range k,
    (∑' l : ℕ, a l * (exp (2 * Real.pi * I / k) ^ m) ^ l) * (exp (2 * Real.pi * I / k))⁻¹ ^ (j * m)

/-- Orthogonality of the roots of unity: `∑_{m<k} (ζ^d)^m = k` if `k ∣ d`, else `0`. -/
theorem sum_zpow_primitiveRoot {ζ : ℂ} {k : ℕ} (hζ : IsPrimitiveRoot ζ k) (d : ℤ) :
    ∑ m ∈ range k, (ζ ^ d) ^ m = if (k : ℤ) ∣ d then (k : ℂ) else 0 := by
  split_ifs with h
  · rw [(hζ.zpow_eq_one_iff_dvd d).mpr h]
    simp
  · have hne : ζ ^ d ≠ 1 := fun h1 => h ((hζ.zpow_eq_one_iff_dvd d).mp h1)
    rw [geom_sum_eq hne, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      hζ.pow_eq_one, one_zpow, sub_self, zero_div]

theorem summable_mul_zpow_pow (ha : Summable fun l => ‖a l‖) {ζ : ℂ} (hζ : ‖ζ‖ = 1) (d : ℤ)
    (m : ℕ) : Summable fun l : ℕ => a l * (ζ ^ ((l : ℤ) - d)) ^ m :=
  Summable.of_norm_bounded ha fun l => by
    rw [norm_mul, norm_pow, norm_zpow, hζ, one_zpow, one_pow, mul_one]

/-- `S_{j,k} = ∑_{m≥0} a_{j+mk}` for `j < k`: the discrete sum aliases the coefficients. -/
theorem aliasSum_eq_tsum (ha : Summable fun l => ‖a l‖) {j k : ℕ} (hjk : j < k) :
    aliasSum a j k = ∑' m : ℕ, a (j + m * k) := by
  have hk : 0 < k := by omega
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  set ζ : ℂ := exp (2 * Real.pi * I / k) with hζdef
  have hζ : IsPrimitiveRoot ζ k := Complex.isPrimitiveRoot_exp k hk.ne'
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hk.ne'
  have hnorm : ‖ζ‖ = 1 := hζ.norm'_eq_one hk.ne'
  have hterm : ∀ m : ℕ, (∑' l : ℕ, a l * (ζ ^ m) ^ l) * ζ⁻¹ ^ (j * m)
      = ∑' l : ℕ, a l * (ζ ^ ((l : ℤ) - j)) ^ m := by
    intro m
    rw [← tsum_mul_right]
    refine tsum_congr fun l => ?_
    rw [mul_assoc]
    congr 1
    simp only [← zpow_natCast, ← zpow_mul]
    rw [inv_zpow, ← zpow_neg, ← zpow_add₀ hζ0]
    congr 1
    push_cast
    ring
  unfold aliasSum
  rw [← hζdef]
  simp_rw [hterm]
  rw [← Summable.tsum_finsetSum fun m _ => summable_mul_zpow_pow ha hnorm j m]
  simp_rw [← mul_sum, sum_zpow_primitiveRoot hζ]
  rw [← tsum_mul_left]
  have hite : ∀ l : ℕ, (1 / k : ℂ) * (a l * if (k : ℤ) ∣ (l : ℤ) - j then (k : ℂ) else 0)
      = if (k : ℤ) ∣ (l : ℤ) - j then a l else 0 := by
    intro l
    split_ifs
    · field_simp
    · simp
  simp_rw [hite]
  symm
  have hinj : Function.Injective fun m : ℕ => j + m * k := fun m₁ m₂ h => by
    have : m₁ * k = m₂ * k := by simpa using h
    exact Nat.eq_of_mul_eq_mul_right hk this
  have hsupp : Function.support (fun l : ℕ => if (k : ℤ) ∣ (l : ℤ) - j then a l else 0)
      ⊆ Set.range fun m : ℕ => j + m * k := by
    intro l hl
    rw [Function.mem_support] at hl
    have hdvd : (k : ℤ) ∣ (l : ℤ) - j := by
      by_contra h
      exact hl (ite_eq_right h)
    obtain ⟨q, hq⟩ := hdvd
    have hq0 : 0 ≤ q := by
      by_contra h
      push Not at h
      have hjk' : (j : ℤ) < k := by exact_mod_cast hjk
      have hl0 : (0 : ℤ) ≤ l := by positivity
      nlinarith [mul_le_mul_of_nonneg_left (show q ≤ -1 by omega) (show (0 : ℤ) ≤ k by positivity)]
    refine ⟨q.toNat, ?_⟩
    show j + q.toNat * k = l
    zify
    rw [Int.toNat_of_nonneg hq0]
    linarith
  calc ∑' m : ℕ, a (j + m * k)
      = ∑' m : ℕ, (if (k : ℤ) ∣ ((j + m * k : ℕ) : ℤ) - j then a (j + m * k) else 0) :=
        tsum_congr fun m => by
          rw [ite_eq_left]
          push_cast
          exact ⟨m, by ring⟩
    _ = _ := hinj.tsum_eq hsupp

/-- (4.85): `S_{j,k} − a_j = ∑_{m≥1} a_{j+mk}` for `j < k`. -/
theorem aliasSum_sub_eq (ha : Summable fun l => ‖a l‖) {j k : ℕ} (hjk : j < k) :
    aliasSum a j k - a j = ∑' m : ℕ, a (j + (m + 1) * k) := by
  have hk : 0 < k := by omega
  have hinj : Function.Injective fun m : ℕ => j + m * k := fun m₁ m₂ h => by
    have : m₁ * k = m₂ * k := by simpa using h
    exact Nat.eq_of_mul_eq_mul_right hk this
  have hs : Summable fun m : ℕ => a (j + m * k) := ha.of_norm.comp_injective hinj
  rw [aliasSum_eq_tsum ha hjk, ← Summable.sum_add_tsum_nat_add' (f := fun m => a (j + m * k))
    (k := 1) ((summable_nat_add_iff (f := fun m => a (j + m * k)) 1).mpr hs), sum_range_one]
  simp only [zero_mul, add_zero]
  ring

/-- Coefficients bounded by `C r^l` are absolutely summable (`r < 1`). -/
theorem summable_norm_of_le {C r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hC : ∀ l, ‖a l‖ ≤ C * r ^ l) :
    Summable fun l => ‖a l‖ :=
  ((summable_geometric_of_lt_one hr0 hr1).mul_left C).of_nonneg_of_le (fun _ => norm_nonneg _) hC

/-- The error of (4.84): with `‖a_l‖ ≤ C r^l`, `r < 1`, `‖S_{j,k} − a_j‖ ≤ C r^(j+k)/(1 − r^k)`
(the text's `O((R − δ)^(−(j+k)))` with `r = 1/(R − δ)`). -/
theorem norm_aliasSum_sub_le {C r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hC : ∀ l, ‖a l‖ ≤ C * r ^ l) {j k : ℕ} (hjk : j < k) :
    ‖aliasSum a j k - a j‖ ≤ C * r ^ (j + k) / (1 - r ^ k) := by
  have hk : 0 < k := by omega
  have ha := summable_norm_of_le hr0 hr1 hC
  have hrk : r ^ k < 1 := pow_lt_one₀ hr0 hr1 hk.ne'
  have hrk0 : 0 ≤ r ^ k := pow_nonneg hr0 k
  rw [aliasSum_sub_eq ha hjk]
  have hbound : ∀ m : ℕ, ‖a (j + (m + 1) * k)‖ ≤ C * r ^ (j + k) * (r ^ k) ^ m := by
    intro m
    refine (hC _).trans (le_of_eq ?_)
    rw [← pow_mul, mul_assoc, ← pow_add]
    congr 2
    ring
  have hgeo : Summable fun m : ℕ => C * r ^ (j + k) * (r ^ k) ^ m :=
    (summable_geometric_of_lt_one hrk0 hrk).mul_left _
  have hnorm : Summable fun m : ℕ => ‖a (j + (m + 1) * k)‖ :=
    hgeo.of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  calc ‖∑' m : ℕ, a (j + (m + 1) * k)‖ ≤ ∑' m : ℕ, ‖a (j + (m + 1) * k)‖ :=
        norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' m : ℕ, C * r ^ (j + k) * (r ^ k) ^ m := hnorm.tsum_le_tsum hbound hgeo
    _ = C * r ^ (j + k) / (1 - r ^ k) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hrk0 hrk, div_eq_mul_inv]

/-! ### (4.86)/(4.87) the Bernoulli numbers -/

/-- The coefficients of `z/(e^z − 1) + z/2` (the formal series `scaledBernoulliPowerSeries` of
§4.7.2), as complex numbers. -/
noncomputable def bernoulliCoeff (l : ℕ) : ℂ :=
  ((PowerSeries.coeff l scaledBernoulliPowerSeries : ℚ) : ℂ)

theorem bernoulliCoeff_two_mul (j : ℕ) : bernoulliCoeff (2 * j) = (scaledBernoulli j : ℂ) := by
  rw [bernoulliCoeff, coeff_scaledBernoulliPowerSeries_even]

theorem bernoulliCoeff_odd (j : ℕ) : bernoulliCoeff (2 * j + 1) = 0 := by
  rw [bernoulliCoeff, coeff_scaledBernoulliPowerSeries_odd]
  simp

/-- `a_l = B_l/l!` for `l ≠ 1` (the odd Bernoulli numbers beyond `B₁` vanish). -/
theorem bernoulliCoeff_eq {l : ℕ} (hl : l ≠ 1) :
    bernoulliCoeff l = ((bernoulli l / l.factorial : ℚ) : ℂ) := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' l
  · rw [bernoulliCoeff_two_mul, scaledBernoulli]
  · rw [bernoulliCoeff_odd, bernoulli_eq_zero_of_odd ⟨j, by ring⟩ (by omega)]
    simp

/-- The Cauchy-type bound `‖a_l‖ ≤ (π²/3) (2π)^(−l)` (radius of convergence `2π`). -/
theorem norm_bernoulliCoeff_le (l : ℕ) :
    ‖bernoulliCoeff l‖ ≤ Real.pi ^ 2 / 3 * (1 / (2 * Real.pi)) ^ l := by
  have hpi := Real.pi_gt_three
  have hC : (1 : ℝ) ≤ Real.pi ^ 2 / 3 := by nlinarith
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' l
  · rw [bernoulliCoeff_two_mul]
    have hnorm : ‖(scaledBernoulli j : ℂ)‖ = |(scaledBernoulli j : ℝ)| := by
      rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [scaledBernoulli_zero]
      linarith
    · refine (abs_scaledBernoulli_le hj).trans (le_of_eq ?_)
      rw [one_div_pow, div_eq_mul_one_div]
  · rw [bernoulliCoeff_odd, norm_zero]
    positivity

/-- (4.87): `S_{2j,k} − B_{2j}/(2j)! = ∑_{m≥1} a_{2j+mk}` for `2j < k`. -/
theorem bernoulli_aliasSum_sub_eq {j k : ℕ} (hjk : 2 * j < k) :
    aliasSum bernoulliCoeff (2 * j) k - (scaledBernoulli j : ℂ)
      = ∑' m : ℕ, bernoulliCoeff (2 * j + (m + 1) * k) := by
  rw [← bernoulliCoeff_two_mul]
  exact aliasSum_sub_eq (summable_norm_of_le (by positivity)
    (by rw [div_lt_one (by positivity)]; linarith [Real.pi_gt_three]) norm_bernoulliCoeff_le) hjk

/-- `‖B_{2j}/(2j)!‖ ≥ 2 (2π)^(−2j)` for `j ≥ 1`. -/
theorem two_mul_le_norm_scaledBernoulli {j : ℕ} (hj : 1 ≤ j) :
    2 * (1 / (2 * Real.pi)) ^ (2 * j) ≤ ‖(scaledBernoulli j : ℂ)‖ := by
  rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs, scaledBernoulli_eq_zeta hj,
    abs_div, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_two,
    abs_of_pos (by positivity : (0 : ℝ) < (2 * Real.pi) ^ (2 * j)),
    abs_of_pos (lt_of_lt_of_le one_pos (one_le_zetaReal_two_mul hj)), one_div_pow,
    div_eq_mul_one_div, le_div_iff₀ (by positivity)]
  have := one_le_zetaReal_two_mul hj
  have hpos : (0 : ℝ) < (2 * Real.pi) ^ (2 * j) := by positivity
  rw [one_mul, mul_assoc, one_div_mul_cancel hpos.ne', mul_one]
  linarith

/-- The relative error of the contour method for `B_{2j}`: `O((2π)^(−k))`. -/
theorem norm_bernoulli_aliasSum_sub_le {j k : ℕ} (hj : 1 ≤ j) (hjk : 2 * j < k) :
    ‖aliasSum bernoulliCoeff (2 * j) k - (scaledBernoulli j : ℂ)‖
      ≤ Real.pi ^ 2 / 6 * (1 / (2 * Real.pi)) ^ k / (1 - (1 / (2 * Real.pi)) ^ k)
        * ‖(scaledBernoulli j : ℂ)‖ := by
  have hr0 : (0 : ℝ) ≤ 1 / (2 * Real.pi) := by positivity
  have hr1 : 1 / (2 * Real.pi) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith [Real.pi_gt_three]
  have hk : 0 < k := by omega
  have hrk : (1 / (2 * Real.pi)) ^ k < 1 := pow_lt_one₀ hr0 hr1 hk.ne'
  have h := norm_aliasSum_sub_le (a := bernoulliCoeff) hr0 hr1 norm_bernoulliCoeff_le hjk
  rw [bernoulliCoeff_two_mul] at h
  have hB := two_mul_le_norm_scaledBernoulli hj
  refine h.trans ?_
  have hD : 0 < 1 - (1 / (2 * Real.pi)) ^ k := by linarith
  have e : Real.pi ^ 2 / 6 * (1 / (2 * Real.pi)) ^ k / (1 - (1 / (2 * Real.pi)) ^ k)
      * ‖(scaledBernoulli j : ℂ)‖
      = Real.pi ^ 2 / 6 * (1 / (2 * Real.pi)) ^ k * ‖(scaledBernoulli j : ℂ)‖
        / (1 - (1 / (2 * Real.pi)) ^ k) := by ring
  rw [pow_add, e, div_le_div_iff_of_pos_right hD]
  have hR : 0 ≤ Real.pi ^ 2 / 6 * (1 / (2 * Real.pi)) ^ k := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hB hR]

end BZ

end Azurite
