/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BrentZimmermann.Chapter4.PowerSeriesEval
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.PSeries

/-!
# Brent–Zimmermann §4.4: the assumption on the coefficients, and the radius of convergence

**Assumption.**  The power series `∑ a_j x^j` has `a_{j+δ} / a_j = R(j)` a rational function of
`j`, for a fixed `δ ≥ 1` (usually `1` or `2`), so the coefficients are cheap to generate in
sequence; e.g. `exp` has `δ = 1`, `a_{j+1}/a_j = 1/(j+1)`.  This covers the hypergeometric
functions (holonomic functions: §4.9.2).  `tan` does not satisfy it (tangent numbers, §4.7.2)
but is reached through `arctan` by Newton (§4.2.5) or as `sin / cos`.

**Radius of convergence.**  For an entire function (`exp`, `sin`) the series converges
everywhere and `deg den R > deg num R`; otherwise (`ln`, `arctan`) a singularity on the boundary
limits the disk: `ln(1 + x)` and `arctan x` both have radius `1` — `arctan` because of its
singularities at `±i`, although it is bounded on the real line.

* `RationalRatio a δ` — the assumption, with the ratio as a quotient of polynomials whose
  denominator does not vanish at the naturals; `RationalRatio.eq_mul_prod` — the sequential
  evaluation `a (δk + r) = a r · ∏_{i<k} R(δi + r)`.
* `expRatio`, `logRatio`, `arctanRatio` — the instances (`exp`: `1/(j+1)`; `ln(1+x)` written as
  `x ∑ (−1)^j x^j/(j+1)`: `−(j+1)/(j+2)`; `arctan`: `δ = 2`, `−j/(j+2)`) on the coefficient
  sequences `expCoeff`, `logCoeff`, `arctanCoeff`.
* `RationalRatio.tendsto_zero_of_degree_lt`, `tendsto_leadingCoeff_div_of_degree_eq` — the
  limit of the ratio (`δ = 1`) from the degrees.
* `summable_of_ratio_tendsto`, `not_summable_of_ratio_tendsto` — the ratio test: if
  `a_{j+1}/a_j → L` then `∑ a_j x^j` converges for `|x| |L| < 1` and diverges for `|x| |L| > 1`
  (radius `1/|L|`; `L = 0` is the entire case, `summable_of_ratio_tendsto_zero`);
  `RationalRatio.tendsto_ratio_of_degree_eq` gives `L` from the leading coefficients.
* `summable_logCoeff_of_abs_lt_one`, `not_summable_logCoeff_of_one_lt_abs`,
  `not_summable_logCoeff_neg_one` (the harmonic series) — radius exactly `1` for `ln(1 + x)`;
  `arctanCompressedRatio`, `not_summable_arctanCompressedCoeff_of_one_lt_abs` — radius `1` for
  `arctan` (in `y = x²`).
-/

namespace Azurite

namespace BZ

open Finset Filter Topology Polynomial

/-! ### The assumption -/

/-- The coefficients `a` of a power series whose term ratio `a (j + δ) / a j` is a rational
function `R(j) = num(j) / den(j)` of `j`, with `den` nonvanishing at the naturals. -/
structure RationalRatio (a : ℕ → ℝ) (δ : ℕ) where
  /-- The numerator of `R`. -/
  num : ℝ[X]
  /-- The denominator of `R`. -/
  den : ℝ[X]
  /-- `den (j) ≠ 0` for every natural `j`. -/
  den_ne_zero : ∀ j : ℕ, den.eval (j : ℝ) ≠ 0
  /-- `a (j + δ) = R(j) a j`. -/
  ratio : ∀ j : ℕ, a (j + δ) = num.eval (j : ℝ) / den.eval (j : ℝ) * a j

namespace RationalRatio

variable {a : ℕ → ℝ} {δ : ℕ}

/-- The ratio `R(j)`. -/
noncomputable def R (h : RationalRatio a δ) (j : ℕ) : ℝ := h.num.eval (j : ℝ) / h.den.eval (j : ℝ)

theorem ratio' (h : RationalRatio a δ) (j : ℕ) : a (j + δ) = h.R j * a j := h.ratio j

/-- Sequential evaluation: `a (δ k + r) = a r · ∏_{i<k} R(δ i + r)`. -/
theorem eq_mul_prod (h : RationalRatio a δ) (r k : ℕ) :
    a (δ * k + r) = a r * ∏ i ∈ range k, h.R (δ * i + r) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [prod_range_succ, show δ * (k + 1) + r = (δ * k + r) + δ by ring, h.ratio', ih]
    ring

/-- With `δ = 1`: `a j = a 0 · ∏_{i<j} R(i)`. -/
theorem eq_mul_prod_one (h : RationalRatio a 1) (j : ℕ) :
    a j = a 0 * ∏ i ∈ range j, h.R i := by
  have := h.eq_mul_prod 0 j
  simpa using this

/-- If `deg num < deg den`, the ratio tends to `0` (the entire case). -/
theorem tendsto_zero_of_degree_lt (h : RationalRatio a δ) (hdeg : h.num.degree < h.den.degree) :
    Tendsto h.R atTop (𝓝 0) :=
  (div_tendsto_atTop_zero_of_degree_lt h.num h.den hdeg).comp tendsto_natCast_atTop_atTop

/-- If `deg num = deg den`, the ratio tends to the quotient of the leading coefficients. -/
theorem tendsto_leadingCoeff_div_of_degree_eq (h : RationalRatio a δ)
    (hdeg : h.num.degree = h.den.degree) :
    Tendsto h.R atTop (𝓝 (h.num.leadingCoeff / h.den.leadingCoeff)) :=
  (div_tendsto_atTop_leadingCoeff_div_of_degree_eq h.num h.den hdeg).comp
    tendsto_natCast_atTop_atTop

end RationalRatio

/-! ### The instances -/

/-- The coefficients of `exp`, `1/j!`. -/
noncomputable def expCoeff (j : ℕ) : ℝ := 1 / j.factorial

/-- `exp`: `δ = 1`, `R(j) = 1/(j+1)`. -/
noncomputable def expRatio : RationalRatio expCoeff 1 where
  num := C 1
  den := X + C 1
  den_ne_zero j := by simp; positivity
  ratio j := by
    simp only [expCoeff, eval_C, eval_add, eval_X, Nat.factorial_succ]
    push_cast
    field_simp

/-- The coefficients of `ln(1 + x) / x`, `(−1)^j / (j + 1)`. -/
noncomputable def logCoeff (j : ℕ) : ℝ := (-1) ^ j / (j + 1)

/-- `ln(1 + x) = x ∑ logCoeff j · x^j`: `δ = 1`, `R(j) = −(j+1)/(j+2)`. -/
noncomputable def logRatio : RationalRatio logCoeff 1 where
  num := -(X + C 1)
  den := X + C 2
  den_ne_zero j := by simp; positivity
  ratio j := by
    simp only [logCoeff, eval_neg, eval_add, eval_X, eval_C, pow_succ]
    push_cast
    field_simp
    ring

/-- The coefficients of `arctan`, `(−1)^k/(2k+1)` at the odd index `2k+1` and `0` at even
indices. -/
noncomputable def arctanCoeff (j : ℕ) : ℝ := if j % 2 = 1 then (-1) ^ (j / 2) / j else 0

/-- `arctan`: `δ = 2`, `R(j) = −j/(j+2)`. -/
noncomputable def arctanRatio : RationalRatio arctanCoeff 2 where
  num := -X
  den := X + C 2
  den_ne_zero j := by simp; positivity
  ratio j := by
    simp only [arctanCoeff, eval_neg, eval_X, eval_add, eval_C]
    by_cases hj : j % 2 = 1
    · have h2 : (j + 2) % 2 = 1 := by omega
      have h3 : (j + 2) / 2 = j / 2 + 1 := by omega
      rw [ite_eq_left h2, ite_eq_left hj, h3, pow_succ]
      have hj0 : (j : ℝ) ≠ 0 := by
        have : j ≠ 0 := by omega
        exact_mod_cast this
      push_cast
      field_simp
    · have h2 : ¬ (j + 2) % 2 = 1 := by omega
      rw [ite_eq_right h2, ite_eq_right hj, mul_zero]

/-! ### The ratio test: radius of convergence `1/|L|` -/

/-- For `δ = 1` and nonvanishing coefficients, `a (j+1) / a j = R j`, so the ratio tends to the
quotient of the leading coefficients when the degrees agree. -/
theorem RationalRatio.tendsto_ratio_of_degree_eq {a : ℕ → ℝ} (h : RationalRatio a 1)
    (ha : ∀ j, a j ≠ 0) (hdeg : h.num.degree = h.den.degree) :
    Tendsto (fun j => a (j + 1) / a j) atTop (𝓝 (h.num.leadingCoeff / h.den.leadingCoeff)) := by
  refine (h.tendsto_leadingCoeff_div_of_degree_eq hdeg).congr fun j => ?_
  rw [h.ratio', mul_div_assoc, div_self (ha j), mul_one]

/-- The term ratio of `∑ a_j x^j` in absolute value: `|x| |a (j+1) / a j|`. -/
theorem norm_term_ratio_eq {a : ℕ → ℝ} (ha : ∀ j, a j ≠ 0) {x : ℝ} (hx : x ≠ 0) :
    (fun j => ‖a (j + 1) * x ^ (j + 1)‖ / ‖a j * x ^ j‖) = fun j => |x| * |a (j + 1) / a j| := by
  funext j
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_pow, pow_succ, abs_div]
  have := pow_ne_zero j (abs_ne_zero.mpr hx)
  have := abs_ne_zero.mpr (ha j)
  field_simp

/-- If `a_{j+1}/a_j → L` with all `a_j ≠ 0`, the series `∑ a_j x^j` converges for `|x| |L| < 1`. -/
theorem summable_of_ratio_tendsto {a : ℕ → ℝ} {L : ℝ} (ha : ∀ j, a j ≠ 0)
    (hL : Tendsto (fun j => a (j + 1) / a j) atTop (𝓝 L)) {x : ℝ} (hx : |x| * |L| < 1) :
    Summable (fun j => a j * x ^ j) := by
  by_cases hx0 : x = 0
  · subst hx0
    exact summable_of_ne_finset_zero (s := {0}) fun j hj => by
      simp only [mem_singleton] at hj
      rw [zero_pow hj, mul_zero]
  refine summable_of_ratio_test_tendsto_lt_one (l := |x| * |L|) hx
    (Eventually.of_forall fun j => mul_ne_zero (ha j) (pow_ne_zero _ hx0)) ?_
  rw [norm_term_ratio_eq ha hx0]
  exact hL.abs.const_mul |x|

/-- If `a_{j+1}/a_j → L`, the series `∑ a_j x^j` diverges for `|x| |L| > 1`. -/
theorem not_summable_of_ratio_tendsto {a : ℕ → ℝ} {L : ℝ} (ha : ∀ j, a j ≠ 0)
    (hL : Tendsto (fun j => a (j + 1) / a j) atTop (𝓝 L)) {x : ℝ} (hx : 1 < |x| * |L|) :
    ¬ Summable (fun j => a j * x ^ j) := by
  have hx0 : x ≠ 0 := by rintro rfl; norm_num at hx
  refine not_summable_of_ratio_test_tendsto_gt_one (l := |x| * |L|) hx ?_
  rw [norm_term_ratio_eq ha hx0]
  exact hL.abs.const_mul |x|

/-- The entire case: if the ratio tends to `0`, the series converges for every `x`. -/
theorem summable_of_ratio_tendsto_zero {a : ℕ → ℝ} (ha : ∀ j, a j ≠ 0)
    (hL : Tendsto (fun j => a (j + 1) / a j) atTop (𝓝 0)) (x : ℝ) :
    Summable (fun j => a j * x ^ j) :=
  summable_of_ratio_tendsto ha hL (by simp)

/-! ### Radius `1` for `ln(1 + x)` and `arctan` -/

theorem logCoeff_ne_zero (j : ℕ) : logCoeff j ≠ 0 := by
  unfold logCoeff
  have : ((j : ℝ) + 1) ≠ 0 := by positivity
  exact div_ne_zero (pow_ne_zero _ (by norm_num)) this

/-- The ratio of the `ln(1 + x)` coefficients tends to `−1`. -/
theorem tendsto_logCoeff_ratio :
    Tendsto (fun j => logCoeff (j + 1) / logCoeff j) atTop (𝓝 (-1)) := by
  have hn : logRatio.num = -(X + C 1) := rfl
  have hd : logRatio.den = X + C 2 := rfl
  have h := logRatio.tendsto_ratio_of_degree_eq logCoeff_ne_zero (by
    rw [hn, hd, degree_neg, degree_X_add_C, degree_X_add_C])
  have hlc : (-(X + C 1) : ℝ[X]).leadingCoeff / (X + C 2 : ℝ[X]).leadingCoeff = (-1 : ℝ) := by
    rw [leadingCoeff_neg, leadingCoeff_X_add_C, leadingCoeff_X_add_C]; norm_num
  rw [hn, hd, hlc] at h
  exact h

/-- The series of `ln(1 + x)` converges for `|x| < 1`. -/
theorem summable_logCoeff_of_abs_lt_one {x : ℝ} (hx : |x| < 1) :
    Summable (fun j => logCoeff j * x ^ j) :=
  summable_of_ratio_tendsto logCoeff_ne_zero tendsto_logCoeff_ratio (by simpa using hx)

/-- … and diverges for `|x| > 1`: the radius of convergence is `1`. -/
theorem not_summable_logCoeff_of_one_lt_abs {x : ℝ} (hx : 1 < |x|) :
    ¬ Summable (fun j => logCoeff j * x ^ j) :=
  not_summable_of_ratio_tendsto logCoeff_ne_zero tendsto_logCoeff_ratio (by simpa using hx)

/-- At `x = −1` the series of `ln(1 + x)` is the harmonic series: it diverges (the singularity
of `ln` at the origin). -/
theorem not_summable_logCoeff_neg_one : ¬ Summable (fun j => logCoeff j * (-1) ^ j) := by
  have hfun : (fun j => logCoeff j * (-1 : ℝ) ^ j) = fun j : ℕ => 1 / ((j + 1 : ℕ) : ℝ) := by
    funext j
    unfold logCoeff
    rw [div_mul_eq_mul_div, ← pow_add, ← two_mul, pow_mul]
    push_cast
    norm_num
  rw [hfun]
  intro h
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).mp h)

/-- The `arctan` series in `y = x²`: `arctan x = x ∑ (−1)^k y^k / (2k + 1)`. -/
noncomputable def arctanCompressedCoeff (k : ℕ) : ℝ := (-1) ^ k / (2 * k + 1)

theorem arctanCompressedCoeff_ne_zero (k : ℕ) : arctanCompressedCoeff k ≠ 0 := by
  unfold arctanCompressedCoeff
  exact div_ne_zero (pow_ne_zero _ (by norm_num)) (by positivity)

/-- Its ratio is `−(2k+1)/(2k+3) = −(k + 1/2)/(k + 3/2)`. -/
noncomputable def arctanCompressedRatio : RationalRatio arctanCompressedCoeff 1 where
  num := -(X + C (1 / 2))
  den := X + C (3 / 2)
  den_ne_zero j := by simp; positivity
  ratio j := by
    simp only [arctanCompressedCoeff, eval_neg, eval_add, eval_X, eval_C, pow_succ]
    push_cast
    field_simp
    ring

/-- The radius of convergence of the `arctan` series is `1`: the compressed series diverges for
`|y| > 1`, although `arctan` is bounded on the real line. -/
theorem not_summable_arctanCompressedCoeff_of_one_lt_abs {y : ℝ} (hy : 1 < |y|) :
    ¬ Summable (fun k => arctanCompressedCoeff k * y ^ k) := by
  have hn : arctanCompressedRatio.num = -(X + C (1 / 2)) := rfl
  have hd : arctanCompressedRatio.den = X + C (3 / 2) := rfl
  have h := arctanCompressedRatio.tendsto_ratio_of_degree_eq arctanCompressedCoeff_ne_zero (by
    rw [hn, hd, degree_neg, degree_X_add_C, degree_X_add_C])
  have hlc : (-(X + C (1 / 2)) : ℝ[X]).leadingCoeff / (X + C (3 / 2) : ℝ[X]).leadingCoeff
      = (-1 : ℝ) := by
    rw [leadingCoeff_neg, leadingCoeff_X_add_C, leadingCoeff_X_add_C]; norm_num
  rw [hn, hd, hlc] at h
  exact not_summable_of_ratio_tendsto arctanCompressedCoeff_ne_zero h (by simpa using hy)

end BZ

end Azurite
