/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BrentZimmermann.Chapter4.ContinuedFractionEval
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Brent–Zimmermann §4.7: Recurrence relations (introduction: Bessel functions)

The Bessel functions of the first kind `J_ν(x)`, for `ν ∈ ℤ` and `x ∈ ℝ`, are given by the
generating function

  `exp((x/2)(t − 1/t)) = ∑_{ν=−∞}^{∞} t^ν J_ν(x)`                                            (4.47)

or by the power series (valid for non-integer `ν` as well)

  `J_ν(x) = (x/2)^ν ∑_{j≥0} (−x²/4)^j / (j! Γ(ν+j+1))`.                                    (4.48)

The Bessel functions of the second kind are

  `Y_ν(x) = lim_{μ→ν} (J_μ(x) cos(πμ) − J_{−μ}(x)) / sin(πμ)`,                              (4.49)

and both solve Bessel's differential equation

  `x² y'' + x y' + (x² − ν²) y = 0`.                                                       (4.50)

What is formalized:

* `besselJTerm`, `besselJ ν x` — the series (4.48) for `ν ∈ ℤ`.  Mathlib's `Real.Gamma`
  vanishes at the non-positive integers, so `1/Γ(ν+j+1) = 0` kills the first `−ν` terms when
  `ν < 0`, exactly the standard convention; `abs_inv_Gamma_int_le_one`, `summable_besselJTerm`.
* `besselCoeff n j = (−1)^j / (j! (n+j)!)` and `besselJNat n x = ∑ besselCoeff n j (x/2)^(2j+n)`
  — the factorial form for `n ∈ ℕ`; `besselJ_natCast` identifies it with (4.48), and
  `besselJ_neg` gives `J_{−n} = (−1)^n J_n`.  `besselJ_zero_left` (`J_0(0) = 1`) and
  `besselJ_zero_of_ne` (`J_ν(0) = 0` for `ν ≠ 0`).
* `besselBound R n j = (4(R+1))^(2j+n) / j!` — a summable majorant of the series and of its
  first two termwise derivatives on `|x| ≤ R` (`abs_besselCoeff_mul_le`,
  `summable_besselBound`).
* (4.47): `hasSum_besselJ_generating` — for `t ≠ 0`, `HasSum (fun ν : ℤ => t^ν J_ν(x))
  (exp((x/2)(t − 1/t)))`, by the Cauchy product of two exponential series regrouped along the
  fibers of `(a, b) ↦ a − b` (`pairEquiv : ℕ × ℕ ≃ ℤ × ℕ`).
* (4.50): `hasDerivAt_besselJNat`, `hasDerivAt_besselJNat'` (termwise differentiation on a
  ball, via `hasDerivAt_tsum_of_isPreconnected`), the series identity `bessel_ode_series`, and
  `besselJNat_ode`, `besselJ_ode` (`x² J_ν'' + x J_ν' + (x² − ν²) J_ν = 0` with `deriv`).
* `besselJReal μ x` — (4.48) for real order (`rpow`, meant for `x > 0`; `besselJReal_intCast`),
  and `besselY ν x` — (4.49) as a `limUnder`.

Not formalized: existence of the limit (4.49) and that `Y_ν` solves (4.50) (needs the
derivative of `J_μ` in the order `μ`), complex `ν`, `x`.
-/

namespace Azurite

namespace BZ

open Filter Topology Finset Metric

/-! ### The series (4.48) for integer order -/

/-- The `j`-th term of (4.48): `(−x²/4)^j / (j! Γ(ν+j+1))`. -/
noncomputable def besselJTerm (ν : ℤ) (x : ℝ) (j : ℕ) : ℝ :=
  (-x ^ 2 / 4) ^ j / (j.factorial * Real.Gamma (ν + j + 1))

/-- The Bessel function of the first kind `J_ν(x)`, `ν ∈ ℤ`, by the power series (4.48). -/
noncomputable def besselJ (ν : ℤ) (x : ℝ) : ℝ := (x / 2) ^ ν * ∑' j, besselJTerm ν x j

/-- At integer arguments `Γ` is `0` or a factorial, so `|1/Γ| ≤ 1`. -/
theorem abs_inv_Gamma_int_le_one (k : ℤ) : |(Real.Gamma k)⁻¹| ≤ 1 := by
  rcases k with n | n
  · rcases n with _ | m
    · simp [Real.Gamma_zero]
    · rw [Int.ofNat_eq_natCast, Int.cast_natCast, Nat.cast_succ, Real.Gamma_nat_eq_factorial,
        abs_inv, Nat.abs_cast, inv_le_one₀ (Nat.cast_pos.mpr (Nat.factorial_pos m))]
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero m)
  · rw [Int.cast_negSucc, Real.Gamma_neg_nat_eq_zero]
    simp

theorem abs_besselJTerm_le (ν : ℤ) (x : ℝ) (j : ℕ) :
    |besselJTerm ν x j| ≤ (x ^ 2 / 4) ^ j / j.factorial := by
  unfold besselJTerm
  have h : |(Real.Gamma (ν + j + 1))⁻¹| ≤ 1 := by
    have := abs_inv_Gamma_int_le_one (ν + j + 1)
    push_cast at this
    exact this
  rw [abs_div, abs_mul, Nat.abs_cast, abs_pow, abs_div, abs_neg, abs_of_nonneg (sq_nonneg x),
    abs_of_pos (by norm_num : (0:ℝ) < 4), div_mul_eq_div_div,
    div_eq_mul_inv ((x ^ 2 / 4) ^ j / (j.factorial : ℝ)), ← abs_inv]
  calc (x ^ 2 / 4) ^ j / (j.factorial : ℝ) * |(Real.Gamma (ν + j + 1))⁻¹|
      ≤ (x ^ 2 / 4) ^ j / (j.factorial : ℝ) * 1 := by gcongr
    _ = (x ^ 2 / 4) ^ j / j.factorial := mul_one _

theorem summable_besselJTerm (ν : ℤ) (x : ℝ) : Summable (besselJTerm ν x) :=
  (Real.summable_pow_div_factorial (x ^ 2 / 4)).of_norm_bounded fun j => by
    rw [Real.norm_eq_abs]; exact abs_besselJTerm_le ν x j

/-! ### The factorial form for `n ∈ ℕ` -/

/-- `(−1)^j / (j! (n+j)!)`, the coefficient of `(x/2)^(2j+n)` in `J_n`. -/
noncomputable def besselCoeff (n j : ℕ) : ℝ := (-1) ^ j / (j.factorial * (n + j).factorial)

/-- `J_n(x) = ∑ besselCoeff n j · (x/2)^(2j+n)` for `n ∈ ℕ`. -/
noncomputable def besselJNat (n : ℕ) (x : ℝ) : ℝ :=
  ∑' j, besselCoeff n j * (x / 2) ^ (2 * j + n)

theorem besselCoeff_succ (n j : ℕ) :
    besselCoeff n (j + 1) = -besselCoeff n j / ((j + 1) * (n + j + 1)) := by
  unfold besselCoeff
  rw [Nat.factorial_succ, show n + (j + 1) = n + j + 1 by ring, Nat.factorial_succ, pow_succ]
  push_cast
  field_simp

/-- A majorant: `(4(R+1))^(2j+n) / j!`. -/
noncomputable def besselBound (R : ℝ) (n j : ℕ) : ℝ := (4 * (R + 1)) ^ (2 * j + n) / j.factorial

theorem summable_besselBound (R : ℝ) (n : ℕ) : Summable (besselBound R n) := by
  have : besselBound R n
      = fun j => (4 * (R + 1)) ^ n * (((4 * (R + 1)) ^ 2) ^ j / j.factorial) := by
    funext j
    unfold besselBound
    rw [pow_add, pow_mul]
    ring
  rw [this]
  exact (Real.summable_pow_div_factorial _).mul_left _

theorem abs_besselCoeff_eq (n j : ℕ) :
    |besselCoeff n j| = 1 / (j.factorial * (n + j).factorial) := by
  unfold besselCoeff
  rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos (by positivity)]

/-- `m^k ≤ 4^m` for `k ≤ 2`. -/
theorem pow_le_four_pow (m k : ℕ) (hk : k ≤ 2) : m ^ k ≤ 4 ^ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rcases k with _ | k
    · simp
    · simp
  · calc m ^ k ≤ m ^ 2 := Nat.pow_le_pow_right hm hk
      _ ≤ (2 ^ m) ^ 2 := le_of_lt (Nat.pow_lt_pow_left (Nat.lt_two_pow_self (n := m)) (by norm_num))
      _ = 4 ^ m := by rw [← pow_mul, mul_comm, pow_mul]; norm_num

/-- The common bound on the series terms and their first two derivatives: for `|x| ≤ R` and
`k ≤ 2`, `|c_j| (2j+n)^k |x/2|^(2j+n−k) ≤ besselBound R n j`. -/
theorem abs_besselCoeff_mul_le {R x : ℝ} (hR : 0 ≤ R) (hx : |x| ≤ R) (n j k : ℕ) (hk : k ≤ 2) :
    |besselCoeff n j| * ((2 * j + n : ℕ) : ℝ) ^ k * |x / 2| ^ (2 * j + n - k)
      ≤ besselBound R n j := by
  rw [abs_besselCoeff_eq]
  unfold besselBound
  set m := 2 * j + n with hm
  have hfac : (1 : ℝ) ≤ (n + j).factorial := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h1 : ((m : ℕ) : ℝ) ^ k ≤ 4 ^ m := by exact_mod_cast pow_le_four_pow m k hk
  have hx2 : |x / 2| ≤ R + 1 := by
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    linarith [div_le_self (abs_nonneg x) (by norm_num : (1:ℝ) ≤ 2)]
  have h2 : |x / 2| ^ (m - k) ≤ (R + 1) ^ m := by
    calc |x / 2| ^ (m - k) ≤ (R + 1) ^ (m - k) := by gcongr
      _ ≤ (R + 1) ^ m := pow_le_pow_right₀ (by linarith) (Nat.sub_le _ _)
  have h3 : (1 : ℝ) / (j.factorial * (n + j).factorial) ≤ 1 / j.factorial := by
    apply one_div_le_one_div_of_le (by positivity)
    calc (j.factorial : ℝ) = j.factorial * 1 := (mul_one _).symm
      _ ≤ j.factorial * (n + j).factorial := by gcongr
  calc 1 / (j.factorial * (n + j).factorial : ℝ) * ((m : ℕ) : ℝ) ^ k * |x / 2| ^ (m - k)
      ≤ 1 / (j.factorial : ℝ) * 4 ^ m * (R + 1) ^ m := by gcongr
    _ = (4 * (R + 1)) ^ m / j.factorial := by rw [mul_pow]; ring

theorem norm_besselCoeff_mul_pow_le {R x : ℝ} (hR : 0 ≤ R) (hx : |x| ≤ R) (n j : ℕ) :
    ‖besselCoeff n j * (x / 2) ^ (2 * j + n)‖ ≤ besselBound R n j := by
  have := abs_besselCoeff_mul_le hR hx n j 0 (by norm_num)
  rw [pow_zero, mul_one, Nat.sub_zero] at this
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  exact this

theorem summable_besselJNat_term (n : ℕ) (x : ℝ) :
    Summable fun j => besselCoeff n j * (x / 2) ^ (2 * j + n) :=
  (summable_besselBound |x| n).of_norm_bounded fun j =>
    norm_besselCoeff_mul_pow_le (abs_nonneg x) le_rfl n j

/-- Term by term, (4.48) at `ν = n ∈ ℕ` is the factorial series. -/
theorem besselJTerm_natCast (n : ℕ) (x : ℝ) (j : ℕ) :
    (x / 2) ^ n * besselJTerm n x j = besselCoeff n j * (x / 2) ^ (2 * j + n) := by
  unfold besselJTerm besselCoeff
  have hΓ : Real.Gamma (((n : ℤ) : ℝ) + j + 1) = (n + j).factorial := by
    rw [show ((n : ℤ) : ℝ) + j + 1 = ((n + j : ℕ) : ℝ) + 1 by push_cast; ring,
      Real.Gamma_nat_eq_factorial]
  rw [hΓ, show (-x ^ 2 / 4) ^ j = (-1) ^ j * ((x / 2) ^ 2) ^ j by rw [← mul_pow]; congr 1; ring,
    pow_add, pow_mul]
  ring

theorem besselJ_natCast (n : ℕ) (x : ℝ) : besselJ n x = besselJNat n x := by
  unfold besselJ besselJNat
  rw [zpow_natCast, ← tsum_mul_left]
  exact tsum_congr (besselJTerm_natCast n x)

/-- The terms of (4.48) at `ν = −n` vanish for `j < n`. -/
theorem besselJTerm_neg_of_lt (n : ℕ) (x : ℝ) {j : ℕ} (hj : j < n) :
    besselJTerm (-n) x j = 0 := by
  have hΓ : Real.Gamma (((-(n : ℤ) : ℤ) : ℝ) + j + 1) = 0 := by
    have : (((-(n : ℤ) : ℤ) : ℝ) + j + 1) = -((n - j - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub hj.le]
      push_cast
      ring
    rw [this, Real.Gamma_neg_nat_eq_zero]
  unfold besselJTerm
  rw [hΓ]
  simp

/-- The terms of (4.48) at `ν = −n`, shifted by `n`, are `(−x²/4)^n` times those at `ν = n`. -/
theorem besselJTerm_neg_add (n : ℕ) (x : ℝ) (i : ℕ) :
    besselJTerm (-n) x (i + n) = (-x ^ 2 / 4) ^ n * besselJTerm n x i := by
  have hΓ1 : Real.Gamma (((-(n : ℤ) : ℤ) : ℝ) + ((i + n : ℕ) : ℝ) + 1) = i.factorial := by
    rw [show ((-(n : ℤ) : ℤ) : ℝ) + ((i + n : ℕ) : ℝ) + 1 = ((i : ℕ) : ℝ) + 1 by push_cast; ring,
      Real.Gamma_nat_eq_factorial]
  have hΓ2 : Real.Gamma (((n : ℤ) : ℝ) + i + 1) = (n + i).factorial := by
    rw [show ((n : ℤ) : ℝ) + i + 1 = ((n + i : ℕ) : ℝ) + 1 by push_cast; ring,
      Real.Gamma_nat_eq_factorial]
  unfold besselJTerm
  rw [hΓ1, hΓ2, pow_add, add_comm i n]
  ring

/-- `J_{−n}(x) = (−1)^n J_n(x)` (4.48 with the `1/Γ = 0` convention). -/
theorem besselJ_neg (n : ℕ) (x : ℝ) : besselJ (-n) x = (-1) ^ n * besselJ n x := by
  unfold besselJ
  have hsum : ∑' j, besselJTerm (-n) x j = (-x ^ 2 / 4) ^ n * ∑' j, besselJTerm n x j := by
    rw [← Summable.sum_add_tsum_nat_add' (f := besselJTerm (-n) x) (k := n)
      ((summable_nat_add_iff (f := besselJTerm (-n) x) n).mpr (summable_besselJTerm (-n) x))]
    rw [Finset.sum_eq_zero fun j hj => besselJTerm_neg_of_lt n x (Finset.mem_range.mp hj),
      zero_add, ← tsum_mul_left]
    exact tsum_congr (besselJTerm_neg_add n x)
  rw [hsum]
  rcases eq_or_ne x 0 with rfl | hx
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.cast_zero, neg_zero, zpow_zero, pow_zero, one_mul]
    · rw [zero_div, zero_zpow _ (by omega), zpow_natCast, zero_pow hn.ne']
      ring
  · have h : (x / 2) ^ n * ((x / 2) ^ n)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ (by positivity))
    rw [zpow_neg, zpow_natCast, show (-x ^ 2 / 4) ^ n = (-1) ^ n * ((x / 2) ^ n) ^ 2 by
      rw [show -x ^ 2 / 4 = -1 * (x / 2) ^ 2 by ring, mul_pow, ← pow_mul, mul_comm 2 n, pow_mul]]
    linear_combination ((-1) ^ n * (x / 2) ^ n * ∑' j, besselJTerm n x j) * h

theorem besselJ_zero_left : besselJ 0 0 = 1 := by
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) by rfl, besselJ_natCast]
  unfold besselJNat
  rw [tsum_eq_single 0 fun j hj => by simp [hj]]
  simp [besselCoeff]

theorem besselJ_zero_of_ne {ν : ℤ} (hν : ν ≠ 0) : besselJ ν 0 = 0 := by
  unfold besselJ
  rw [zero_div, zero_zpow _ hν, zero_mul]

/-! ### The generating function (4.47) -/

/-- `(a, b) ↦ (a − b, min a b)`: pairs of naturals, indexed by their difference and their
minimum. -/
def pairEquiv : ℕ × ℕ ≃ ℤ × ℕ where
  toFun p := ((p.1 : ℤ) - p.2, min p.1 p.2)
  invFun q := (q.2 + q.1.toNat, q.2 + (-q.1).toNat)
  left_inv p := by
    obtain ⟨a, b⟩ := p
    simp only [Prod.mk.injEq]
    omega
  right_inv q := by
    obtain ⟨ν, i⟩ := q
    simp only [Prod.mk.injEq]
    omega

theorem pairEquiv_symm_natCast (n i : ℕ) : pairEquiv.symm ((n : ℤ), i) = (i + n, i) := by
  simp [pairEquiv]

theorem pairEquiv_symm_negSucc (n i : ℕ) :
    pairEquiv.symm (Int.negSucc n, i) = (i, i + (n + 1)) := by
  simp [pairEquiv]

/-- The fiber over `n ≥ 0` of the Cauchy product of `exp(ut)` and `exp(−u/t)`, summed over the
minimum `i`: `t^n ∑ c_j u^(2j+n)`. -/
theorem hasSum_fiber_nonneg {t : ℝ} (ht : t ≠ 0) (u : ℝ) (n : ℕ) :
    HasSum (fun i : ℕ => (u * t) ^ (i + n) / (i + n).factorial * ((-u / t) ^ i / i.factorial))
      (t ^ n * ∑' j, besselCoeff n j * u ^ (2 * j + n)) := by
  have hsum : Summable fun j => besselCoeff n j * u ^ (2 * j + n) := by
    have := summable_besselJNat_term n (2 * u)
    simpa [mul_div_cancel_left₀ u (two_ne_zero' ℝ)] using this
  refine (hsum.hasSum.mul_left (t ^ n)).congr_fun fun i => ?_
  unfold besselCoeff
  have h : t ^ i * (t ^ i)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ ht)
  rw [div_pow, neg_pow, mul_pow, pow_add u, pow_add t, div_eq_mul_inv ((-1) ^ i * u ^ i),
    add_comm n i]
  linear_combination (u ^ i * u ^ n * t ^ n * (-1) ^ i * u ^ i
    / ((i + n).factorial * i.factorial)) * h

/-- The fiber over `−(n+1)`: `t^{−(n+1)} (−1)^(n+1) ∑ c_j u^(2j+n+1)`. -/
theorem hasSum_fiber_neg {t : ℝ} (ht : t ≠ 0) (u : ℝ) (n : ℕ) :
    HasSum (fun i : ℕ => (u * t) ^ i / i.factorial *
      ((-u / t) ^ (i + (n + 1)) / (i + (n + 1)).factorial))
      ((t ^ (n + 1))⁻¹ * (-1) ^ (n + 1) * ∑' j, besselCoeff (n + 1) j * u ^ (2 * j + (n + 1))) := by
  have hsum : Summable fun j => besselCoeff (n + 1) j * u ^ (2 * j + (n + 1)) := by
    have := summable_besselJNat_term (n + 1) (2 * u)
    simpa [mul_div_cancel_left₀ u (two_ne_zero' ℝ)] using this
  refine (hsum.hasSum.mul_left ((t ^ (n + 1))⁻¹ * (-1) ^ (n + 1))).congr_fun fun i => ?_
  unfold besselCoeff
  have h : t ^ i * (t ^ i)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ ht)
  rw [div_pow, neg_pow, mul_pow, pow_add (-1 : ℝ) i, pow_add u i, pow_add t i,
    div_eq_mul_inv ((-1) ^ i * (-1) ^ (n + 1) * (u ^ i * u ^ (n + 1))), mul_inv,
    add_comm (n + 1) i]
  linear_combination (u ^ i * (t ^ (n + 1))⁻¹ * (-1) ^ i * (-1) ^ (n + 1) * u ^ i * u ^ (n + 1)
    / (i.factorial * (i + (n + 1)).factorial)) * h

/-- The generating function (4.47): for `t ≠ 0`,
`∑_{ν ∈ ℤ} t^ν J_ν(x) = exp((x/2)(t − 1/t))`, as a `HasSum` over `ℤ`. -/
theorem hasSum_besselJ_generating {t : ℝ} (ht : t ≠ 0) (x : ℝ) :
    HasSum (fun ν : ℤ => t ^ ν * besselJ ν x) (Real.exp (x / 2 * (t - 1 / t))) := by
  -- the Cauchy product of the two exponential series
  have hf : Summable fun a : ℕ => ‖(x / 2 * t) ^ a / a.factorial‖ := by
    simp only [Real.norm_eq_abs]
    exact (hasSum_exp_series (x / 2 * t)).summable.abs
  have hg : Summable fun b : ℕ => ‖(-(x / 2) / t) ^ b / b.factorial‖ := by
    simp only [Real.norm_eq_abs]
    exact (hasSum_exp_series (-(x / 2) / t)).summable.abs
  have hF : HasSum (fun p : ℕ × ℕ => (x / 2 * t) ^ p.1 / p.1.factorial *
      ((-(x / 2) / t) ^ p.2 / p.2.factorial)) (Real.exp (x / 2 * (t - 1 / t))) := by
    have hmul := summable_mul_of_summable_norm hf hg
    convert hmul.hasSum using 1
    have := tsum_mul_tsum_of_summable_norm hf hg
    rw [(hasSum_exp_series (x / 2 * t)).tsum_eq, (hasSum_exp_series (-(x / 2) / t)).tsum_eq,
      ← Real.exp_add] at this
    refine Eq.trans ?_ this
    congr 1
    field_simp
    ring
  -- regroup along the fibers of `(a, b) ↦ a − b`
  have hF' := (pairEquiv.symm.hasSum_iff).mpr hF
  refine hF'.prod_fiberwise fun ν => ?_
  rcases ν with n | n
  · rw [Int.ofNat_eq_natCast, zpow_natCast, besselJ_natCast]
    refine (hasSum_fiber_nonneg ht (x / 2) n).congr_fun fun i => ?_
    simp only [Function.comp_apply, pairEquiv_symm_natCast]
  · have h : HasSum (fun i : ℕ => (x / 2 * t) ^ i / i.factorial *
        ((-(x / 2) / t) ^ (i + (n + 1)) / (i + (n + 1)).factorial))
        ((t ^ (n + 1))⁻¹ * (-1) ^ (n + 1) * besselJNat (n + 1) x) :=
      hasSum_fiber_neg ht (x / 2) n
    have hval : t ^ Int.negSucc n * besselJ (Int.negSucc n) x
        = (t ^ (n + 1))⁻¹ * (-1) ^ (n + 1) * besselJNat (n + 1) x := by
      rw [zpow_negSucc, Int.negSucc_eq, ← Nat.cast_succ, besselJ_neg, besselJ_natCast, mul_assoc]
    rw [hval]
    refine h.congr_fun fun i => ?_
    simp only [Function.comp_apply, pairEquiv_symm_negSucc]

/-! ### Bessel's differential equation (4.50) -/

/-- The termwise first derivative of `besselJNat n`. -/
noncomputable def besselJNat' (n : ℕ) (x : ℝ) : ℝ :=
  ∑' j, besselCoeff n j * (((2 * j + n : ℕ) : ℝ) * (x / 2) ^ (2 * j + n - 1) * (1 / 2))

/-- The termwise second derivative of `besselJNat n`. -/
noncomputable def besselJNat'' (n : ℕ) (x : ℝ) : ℝ :=
  ∑' j, besselCoeff n j * (((2 * j + n : ℕ) : ℝ) *
    (((2 * j + n - 1 : ℕ) : ℝ) * (x / 2) ^ (2 * j + n - 1 - 1) * (1 / 2)) * (1 / 2))

theorem norm_besselCoeff_mul_deriv_le {R x : ℝ} (hR : 0 ≤ R) (hx : |x| ≤ R) (n j : ℕ) :
    ‖besselCoeff n j * (((2 * j + n : ℕ) : ℝ) * (x / 2) ^ (2 * j + n - 1) * (1 / 2))‖
      ≤ besselBound R n j := by
  have := abs_besselCoeff_mul_le hR hx n j 1 (by norm_num)
  rw [pow_one] at this
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_pow, Nat.abs_cast,
    abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
  calc |besselCoeff n j| * (((2 * j + n : ℕ) : ℝ) * |x / 2| ^ (2 * j + n - 1) * (1 / 2))
      ≤ |besselCoeff n j| * (((2 * j + n : ℕ) : ℝ) * |x / 2| ^ (2 * j + n - 1) * 1) := by
        gcongr; norm_num
    _ = |besselCoeff n j| * ((2 * j + n : ℕ) : ℝ) * |x / 2| ^ (2 * j + n - 1) := by ring
    _ ≤ besselBound R n j := this

theorem norm_besselCoeff_mul_deriv2_le {R x : ℝ} (hR : 0 ≤ R) (hx : |x| ≤ R) (n j : ℕ) :
    ‖besselCoeff n j * (((2 * j + n : ℕ) : ℝ) *
      (((2 * j + n - 1 : ℕ) : ℝ) * (x / 2) ^ (2 * j + n - 1 - 1) * (1 / 2)) * (1 / 2))‖
      ≤ besselBound R n j := by
  have := abs_besselCoeff_mul_le hR hx n j 2 (by norm_num)
  rw [show 2 * j + n - 2 = 2 * j + n - 1 - 1 by omega] at this
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_pow, Nat.abs_cast,
    Nat.abs_cast, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
  have hm : (((2 * j + n - 1 : ℕ) : ℝ)) ≤ ((2 * j + n : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_le _ _
  calc |besselCoeff n j| * (((2 * j + n : ℕ) : ℝ) * (((2 * j + n - 1 : ℕ) : ℝ)
        * |x / 2| ^ (2 * j + n - 1 - 1) * (1 / 2)) * (1 / 2))
      ≤ |besselCoeff n j| * (((2 * j + n : ℕ) : ℝ) * (((2 * j + n : ℕ) : ℝ)
        * |x / 2| ^ (2 * j + n - 1 - 1) * 1) * 1) := by gcongr <;> norm_num
    _ = |besselCoeff n j| * ((2 * j + n : ℕ) : ℝ) ^ 2 * |x / 2| ^ (2 * j + n - 1 - 1) := by ring
    _ ≤ besselBound R n j := this

/-- `d/dx (x/2)^m = m (x/2)^(m−1) · (1/2)`. -/
theorem hasDerivAt_half_pow (m : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => (y / 2) ^ m) (((m : ℕ) : ℝ) * (x / 2) ^ (m - 1) * (1 / 2)) x := by
  have h : HasDerivAt (fun y : ℝ => y / 2) (1 / 2) x := by
    simpa using (hasDerivAt_id x).div_const 2
  exact h.pow m

theorem mem_ball_abs_add_one (x : ℝ) : x ∈ ball (0 : ℝ) (|x| + 1) := by
  rw [mem_ball_zero_iff, Real.norm_eq_abs]; linarith

theorem abs_le_of_mem_ball {x y : ℝ} (hy : y ∈ ball (0 : ℝ) (|x| + 1)) : |y| ≤ |x| + 1 := by
  rw [← Real.norm_eq_abs]; exact (mem_ball_zero_iff.mp hy).le

/-- `J_n` is differentiable with derivative the termwise derivative. -/
theorem hasDerivAt_besselJNat (n : ℕ) (x : ℝ) :
    HasDerivAt (besselJNat n) (besselJNat' n x) x :=
  hasDerivAt_tsum_of_isPreconnected (summable_besselBound (|x| + 1) n) isOpen_ball
    isPreconnected_ball
    (fun j y _ => (hasDerivAt_half_pow (2 * j + n) y).const_mul (besselCoeff n j))
    (fun j y hy => norm_besselCoeff_mul_deriv_le (by positivity) (abs_le_of_mem_ball hy) n j)
    (mem_ball_abs_add_one x) (summable_besselJNat_term n x) (mem_ball_abs_add_one x)

/-- The termwise derivative is differentiable with derivative the termwise second derivative. -/
theorem hasDerivAt_besselJNat' (n : ℕ) (x : ℝ) :
    HasDerivAt (besselJNat' n) (besselJNat'' n x) x := by
  have hsum : Summable fun j =>
      besselCoeff n j * (((2 * j + n : ℕ) : ℝ) * (x / 2) ^ (2 * j + n - 1) * (1 / 2)) :=
    (summable_besselBound |x| n).of_norm_bounded fun j =>
      norm_besselCoeff_mul_deriv_le (abs_nonneg x) le_rfl n j
  exact hasDerivAt_tsum_of_isPreconnected (summable_besselBound (|x| + 1) n) isOpen_ball
    isPreconnected_ball
    (fun j y _ => (((hasDerivAt_half_pow (2 * j + n - 1) y).const_mul
      ((2 * j + n : ℕ) : ℝ)).mul_const (1 / 2)).const_mul (besselCoeff n j))
    (fun j y hy => norm_besselCoeff_mul_deriv2_le (by positivity) (abs_le_of_mem_ball hy) n j)
    (mem_ball_abs_add_one x) hsum (mem_ball_abs_add_one x)

/-- The termwise identity behind (4.50): with `m = 2j+n` and `u = x/2`,
`c_j (m(m−1) u^(m−2)/4 · x² + m u^(m−1)/2 · x − n² u^m) = 4j(j+n) c_j u^m`. -/
theorem bessel_ode_term (n j : ℕ) (x : ℝ) :
    x ^ 2 * (besselCoeff n j * (((2 * j + n : ℕ) : ℝ) *
        (((2 * j + n - 1 : ℕ) : ℝ) * (x / 2) ^ (2 * j + n - 1 - 1) * (1 / 2)) * (1 / 2)))
      + x * (besselCoeff n j * (((2 * j + n : ℕ) : ℝ) * (x / 2) ^ (2 * j + n - 1) * (1 / 2)))
      - (n : ℝ) ^ 2 * (besselCoeff n j * (x / 2) ^ (2 * j + n))
      = 4 * j * (j + n) * besselCoeff n j * (x / 2) ^ (2 * j + n) := by
  rcases Nat.lt_or_ge (2 * j + n) 2 with h | h
  · obtain rfl : j = 0 := by omega
    have hn : n < 2 := by omega
    interval_cases n
    · simp
    · simp
      ring
  · have hp : (x / 2) ^ (2 * j + n - 1 - 1) * (x / 2) ^ 2 = (x / 2) ^ (2 * j + n) := by
      rw [← pow_add, show 2 * j + n - 1 - 1 + 2 = 2 * j + n by omega]
    have hq : (x / 2) ^ (2 * j + n - 1) * (x / 2) = (x / 2) ^ (2 * j + n) := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    have hc : (((2 * j + n - 1 : ℕ) : ℝ)) = 2 * j + n - 1 := by
      rw [Nat.cast_pred (by omega)]
      push_cast
      ring
    rw [hc]
    push_cast
    linear_combination (besselCoeff n j * (2 * j + n) * (2 * j + n - 1)) * hp
      + (besselCoeff n j * (2 * j + n)) * hq

/-- The series identity `x² S₂ + x S₁ − n² S₀ = −x² S₀` for the termwise sums. -/
theorem bessel_ode_series (n : ℕ) (x : ℝ) :
    x ^ 2 * besselJNat'' n x + x * besselJNat' n x - (n : ℝ) ^ 2 * besselJNat n x
      = -(x ^ 2 * besselJNat n x) := by
  have h0 := summable_besselJNat_term n x
  have h1 : Summable fun j =>
      besselCoeff n j * (((2 * j + n : ℕ) : ℝ) * (x / 2) ^ (2 * j + n - 1) * (1 / 2)) :=
    (summable_besselBound |x| n).of_norm_bounded fun j =>
      norm_besselCoeff_mul_deriv_le (abs_nonneg x) le_rfl n j
  have h2 : Summable fun j => besselCoeff n j * (((2 * j + n : ℕ) : ℝ) *
      (((2 * j + n - 1 : ℕ) : ℝ) * (x / 2) ^ (2 * j + n - 1 - 1) * (1 / 2)) * (1 / 2)) :=
    (summable_besselBound |x| n).of_norm_bounded fun j =>
      norm_besselCoeff_mul_deriv2_le (abs_nonneg x) le_rfl n j
  unfold besselJNat besselJNat' besselJNat''
  rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left,
    ← Summable.tsum_add (h2.mul_left _) (h1.mul_left _),
    ← Summable.tsum_sub ((h2.mul_left _).add (h1.mul_left _)) (h0.mul_left _), ← tsum_neg]
  have hT : (fun j => x ^ 2 * (besselCoeff n j * (((2 * j + n : ℕ) : ℝ) *
      (((2 * j + n - 1 : ℕ) : ℝ) * (x / 2) ^ (2 * j + n - 1 - 1) * (1 / 2)) * (1 / 2)))
      + x * (besselCoeff n j * (((2 * j + n : ℕ) : ℝ) * (x / 2) ^ (2 * j + n - 1) * (1 / 2)))
      - (n : ℝ) ^ 2 * (besselCoeff n j * (x / 2) ^ (2 * j + n)))
      = fun j => 4 * j * (j + n) * besselCoeff n j * (x / 2) ^ (2 * j + n) :=
    funext fun j => bessel_ode_term n j x
  have hS : Summable fun j : ℕ =>
      4 * (j : ℝ) * (j + n) * besselCoeff n j * (x / 2) ^ (2 * j + n) := by
    have := ((h2.mul_left (x ^ 2)).add (h1.mul_left x)).sub (h0.mul_left ((n : ℝ) ^ 2))
    rwa [hT] at this
  rw [hT, hS.tsum_eq_zero_add]
  simp only [Nat.cast_zero, mul_zero, zero_mul, zero_add]
  refine tsum_congr fun j => ?_
  rw [besselCoeff_succ, show 2 * (j + 1) + n = 2 * j + n + 2 by ring, pow_add]
  have hne : ((j : ℝ) + 1) * (n + j + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- Bessel's equation (4.50) for `J_n`, `n ∈ ℕ`: `x² J'' + x J' + (x² − n²) J = 0`. -/
theorem besselJNat_ode (n : ℕ) (x : ℝ) :
    x ^ 2 * deriv (deriv (besselJNat n)) x + x * deriv (besselJNat n) x
      + (x ^ 2 - (n : ℝ) ^ 2) * besselJNat n x = 0 := by
  have hd : deriv (besselJNat n) = besselJNat' n :=
    funext fun y => (hasDerivAt_besselJNat n y).deriv
  rw [hd, (hasDerivAt_besselJNat' n x).deriv]
  linear_combination bessel_ode_series n x

/-- Bessel's equation (4.50) for `J_ν`, `ν ∈ ℤ`. -/
theorem besselJ_ode (ν : ℤ) (x : ℝ) :
    x ^ 2 * deriv (deriv (besselJ ν)) x + x * deriv (besselJ ν) x
      + (x ^ 2 - (ν : ℝ) ^ 2) * besselJ ν x = 0 := by
  rcases ν with n | n
  · have : besselJ (Int.ofNat n) = besselJNat n := funext (besselJ_natCast n)
    rw [this, Int.ofNat_eq_natCast, Int.cast_natCast]
    exact besselJNat_ode n x
  · have : besselJ (Int.negSucc n) = fun y => (-1) ^ (n + 1) * besselJNat (n + 1) y := by
      funext y
      rw [Int.negSucc_eq, ← Nat.cast_succ, besselJ_neg, besselJ_natCast]
    rw [this, Int.cast_negSucc]
    simp only [deriv_const_mul_field']
    have h := besselJNat_ode (n + 1) x
    push_cast at h ⊢
    linear_combination (-1 : ℝ) ^ (n + 1) * h

/-! ### Real order and the second kind (4.49) -/

/-- (4.48) for real order `μ` (with `rpow`; meant for `x > 0`). -/
noncomputable def besselJReal (μ x : ℝ) : ℝ :=
  (x / 2) ^ μ * ∑' j : ℕ, (-x ^ 2 / 4) ^ j / (j.factorial * Real.Gamma (μ + j + 1))

theorem besselJReal_intCast (ν : ℤ) (x : ℝ) : besselJReal ν x = besselJ ν x := by
  unfold besselJReal besselJ besselJTerm
  rw [Real.rpow_intCast]

/-- The Bessel function of the second kind `Y_ν(x)`, `ν ∈ ℤ`, by the limit (4.49) (as a
`limUnder`; its existence is not proven here). -/
noncomputable def besselY (ν : ℤ) (x : ℝ) : ℝ :=
  limUnder (𝓝[≠] (ν : ℝ)) fun μ =>
    (besselJReal μ x * Real.cos (Real.pi * μ) - besselJReal (-μ) x) / Real.sin (Real.pi * μ)

end BZ

end Azurite
