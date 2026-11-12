/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Analysis.Complex.Basic

/-!
# DLMF §5.11(iii): formal series for the gamma ratios

Formal-power-series groundwork for <https://dlmf.nist.gov/5.11#iii>.

* `cSeriesExp a`: the formal exponential of `∑ aₖ Xᵏ` over `ℂ` (`b₀ = 1`,
  `(k+1) b_{k+1} = ∑ᵢ (i+1) a_{i+1} b_{k−i}`), the complex counterpart of `BZ.seriesExp`;
  `expPS a = ∑ bₖ Xᵏ` is the unique series with constant term `1` and `E′ = A′E`
  (`eq_expPS_of_derivative`), so `exp(a + b) = exp a · exp b` (`expPS_add`) and
  `exp(xX) = ∑ xᵏXᵏ/k!` (`expPS_linear`).
* The logarithm of Bernoulli's generating function: `ln(t/(eᵗ − 1)) = −∑_{k≥1} B′ₖ tᵏ/(k·k!)`
  (`bernLog`, with `B′₁ = +½`), i.e. `exp(bernLog) = ∑ Bₖ tᵏ/k!` (`expPS_bernLog`), from
  `t F′ = F − tF − F²` for `F = t/(eᵗ − 1)`.
* **Generalized Bernoulli polynomials** (DLMF §24.16(i), 24.16.1):
  `(t/(eᵗ − 1))^ℓ e^{xt} = ∑ B_n^{(ℓ)}(x) tⁿ/n!`, defined formally as
  `B_n^{(ℓ)}(x) = n! [tⁿ] exp(ℓ ln(t/(eᵗ − 1)) + xt)` (`genBernoulli`); the first values
  (`genBernoulli_zero/one/two`), the symmetry `B_n^{(ℓ)}(ℓ − x) = (−1)ⁿ B_n^{(ℓ)}(x)`
  (`genBernoulli_sub`), and for `ℓ = 1 − n` the generating function
  `((eᵗ − 1)/t)^{n−1} e^{xt}` (`mk_genBernoulli_one_sub`).
-/

open PowerSeries
open scoped Nat

namespace Azurite.DLMF

/-! ### The formal exponential over `ℂ` -/

/-- The formal exponential: `b₀ = 1`, `(k+1) b_{k+1} = ∑_{i ≤ k} (i+1) a_{i+1} b_{k−i}`. -/
noncomputable def cSeriesExp (a : ℕ → ℂ) : ℕ → ℂ
  | 0 => 1
  | k + 1 => (∑ i ∈ Finset.range (k + 1), ((i + 1 : ℕ) : ℂ) * a (i + 1) * cSeriesExp a (k - i)) /
      (k + 1)
termination_by k => k
decreasing_by omega

theorem cSeriesExp_zero (a : ℕ → ℂ) : cSeriesExp a 0 = 1 := by rw [cSeriesExp]

theorem cSeriesExp_succ (a : ℕ → ℂ) (k : ℕ) :
    cSeriesExp a (k + 1) = (∑ i ∈ Finset.range (k + 1),
      ((i + 1 : ℕ) : ℂ) * a (i + 1) * cSeriesExp a (k - i)) / (k + 1) := by
  rw [cSeriesExp]

theorem cSeriesExp_one (a : ℕ → ℂ) : cSeriesExp a 1 = a 1 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, cSeriesExp_succ]
  simp [cSeriesExp_zero]

/-- `exp(∑ aₖ Xᵏ)` as a power series. -/
noncomputable def expPS (a : ℕ → ℂ) : ℂ⟦X⟧ := mk (cSeriesExp a)

theorem coeff_derivative_mul_eq (a : ℕ → ℂ) (F : ℂ⟦X⟧) (k : ℕ) :
    coeff k (d⁄dX (mk a) * F) =
      ∑ i ∈ Finset.range (k + 1), ((i + 1 : ℕ) : ℂ) * a (i + 1) * coeff (k - i) F := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_derivative, coeff_mk]
  push_cast
  ring

theorem derivative_expPS (a : ℕ → ℂ) : d⁄dX (expPS a) = d⁄dX (mk a) * expPS a := by
  ext k
  rw [coeff_derivative_mul_eq, coeff_derivative, expPS, coeff_mk, cSeriesExp_succ]
  simp only [coeff_mk]
  have : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  field_simp

/-- Uniqueness: `F(0) = 1` and `F′ = A′F` force `F = exp A`. -/
theorem eq_expPS_of_derivative {F : ℂ⟦X⟧} (a : ℕ → ℂ) (h0 : constantCoeff F = 1)
    (hD : d⁄dX F = d⁄dX (mk a) * F) : F = expPS a := by
  ext k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | k
    · rw [coeff_zero_eq_constantCoeff_apply, h0, expPS, coeff_mk, cSeriesExp_zero]
    · have h := congrArg (coeff k) hD
      rw [coeff_derivative, coeff_derivative_mul_eq] at h
      have hs : ∑ i ∈ Finset.range (k + 1), ((i + 1 : ℕ) : ℂ) * a (i + 1) * coeff (k - i) F =
          ∑ i ∈ Finset.range (k + 1), ((i + 1 : ℕ) : ℂ) * a (i + 1) * cSeriesExp a (k - i) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [ih (k - i) (by omega), expPS, coeff_mk]
      rw [hs] at h
      rw [expPS, coeff_mk, cSeriesExp_succ, ← h]
      have : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      field_simp

theorem constantCoeff_expPS (a : ℕ → ℂ) : constantCoeff (expPS a) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, expPS, coeff_mk, cSeriesExp_zero]

theorem mk_add' (a b : ℕ → ℂ) : mk (fun k => a k + b k) = mk a + mk b := by
  ext k; simp

/-- `exp(a + b) = exp a · exp b`. -/
theorem expPS_add (a b : ℕ → ℂ) : expPS (fun k => a k + b k) = expPS a * expPS b := by
  symm
  refine eq_expPS_of_derivative _ (by rw [map_mul, constantCoeff_expPS, constantCoeff_expPS,
    one_mul]) ?_
  rw [Derivation.leibniz, derivative_expPS, derivative_expPS, mk_add', map_add, smul_eq_mul,
    smul_eq_mul]
  ring

theorem expPS_zero : expPS (fun _ => 0) = 1 := by
  symm
  refine eq_expPS_of_derivative _ (by simp) ?_
  have : mk (fun _ : ℕ => (0 : ℂ)) = 0 := by ext; simp
  rw [this, map_zero, derivative_one, zero_mul]

theorem expPS_neg_mul (a : ℕ → ℂ) : expPS (fun k => -a k) * expPS a = 1 := by
  rw [← expPS_add]
  simp only [neg_add_cancel]
  exact expPS_zero

theorem expPS_nsmul (a : ℕ → ℂ) (m : ℕ) : expPS (fun k => (m : ℂ) * a k) = expPS a ^ m := by
  induction m with
  | zero => simpa using expPS_zero
  | succ m ih =>
    rw [pow_succ, ← ih, ← expPS_add]
    congr 1
    funext k
    push_cast
    ring

/-- `exp(xX) = ∑ xᵏ Xᵏ/k!`. -/
theorem expPS_linear (x : ℂ) :
    expPS (fun k => if k = 1 then x else 0) = mk fun k => x ^ k / (k ! : ℂ) := by
  symm
  refine eq_expPS_of_derivative _ (by simp) ?_
  ext k
  rw [coeff_derivative_mul_eq, Finset.sum_eq_single 0 (fun i _ hi => by simp [hi])
    (by simp)]
  simp only [coeff_derivative, coeff_mk, Nat.sub_zero, zero_add, Nat.cast_one, one_mul,
    ite_true]
  rw [Nat.factorial_succ]
  push_cast
  have : (k ! : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  field_simp
  ring

/-- Rescaling: `exp(∑ rᵏ aₖ Xᵏ)` has coefficients `rᵏ bₖ`. -/
theorem cSeriesExp_rescale (r : ℂ) (a : ℕ → ℂ) (k : ℕ) :
    cSeriesExp (fun j => r ^ j * a j) k = r ^ k * cSeriesExp a k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | k
    · simp [cSeriesExp_zero]
    · rw [cSeriesExp_succ, cSeriesExp_succ, mul_div_assoc', Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' := Finset.mem_range.mp hi
      rw [ih (k - i) (by omega)]
      have : r ^ (k + 1) = r ^ (i + 1) * r ^ (k - i) := by
        rw [← pow_add]; congr 1; omega
      rw [this]
      ring

/-! ### The logarithm of `t/(eᵗ − 1)` -/

/-- Bernoulli's generating function `t/(eᵗ − 1) = ∑ Bₙ tⁿ/n!`. -/
noncomputable def bernGen : ℂ⟦X⟧ := mk fun n => (bernoulli n : ℂ) / (n ! : ℂ)

/-- `ln(t/(eᵗ − 1)) = −∑_{k≥1} B′ₖ tᵏ/(k·k!)` (`B′₁ = +½`, `B′ₖ = Bₖ` otherwise). -/
noncomputable def bernLog (k : ℕ) : ℂ := -(bernoulli' k : ℂ) / ((k : ℂ) * (k ! : ℂ))

theorem bernLog_zero : bernLog 0 = 0 := by simp [bernLog]

theorem bernGen_mul_exp : bernGen * (exp ℂ - 1) = X := by
  have h := bernoulliPowerSeries_mul_exp_sub_one ℂ
  convert h using 2
  ext n
  simp [bernGen, bernoulliPowerSeries, map_div₀]

theorem derivative_exp' : d⁄dX (exp ℂ) = exp ℂ := by
  ext n
  rw [coeff_derivative, coeff_exp, coeff_exp, Nat.factorial_succ]
  push_cast
  have : (n ! : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simp only [map_div₀, map_one, map_mul, map_natCast, map_add]
  field_simp

theorem exp_sub_one_ne_zero : (exp ℂ - 1 : ℂ⟦X⟧) ≠ 0 := by
  intro h
  have := congrArg (coeff 1) h
  simp [coeff_exp] at this

/-- `t F′ = F − tF − F²` for `F = t/(eᵗ − 1)`. -/
theorem X_mul_derivative_bernGen :
    X * d⁄dX bernGen = bernGen - X * bernGen - bernGen ^ 2 := by
  have hB := bernGen_mul_exp
  have h1 : d⁄dX bernGen * (exp ℂ - 1) + bernGen * exp ℂ = 1 := by
    have := congrArg (d⁄dX) hB
    rw [Derivation.leibniz, map_sub, derivative_exp', derivative_one, sub_zero, derivative_X,
      smul_eq_mul, smul_eq_mul] at this
    linear_combination this
  refine mul_left_cancel₀ exp_sub_one_ne_zero ?_
  linear_combination X * h1 + (bernGen - 1) * hB

theorem X_mul_derivative_bernLog : X * d⁄dX (mk bernLog) = 1 - bernGen - X := by
  ext k
  rcases k with _ | k
  · simp [bernGen]
  · rw [coeff_succ_X_mul, coeff_derivative, coeff_mk, map_sub, map_sub, bernGen, coeff_mk,
      coeff_one, coeff_X]
    rcases k with _ | k
    · simp [bernLog]; norm_num
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), bernLog,
        bernoulli_eq_bernoulli'_of_ne_one (by omega)]
      have : ((k + 1 + 1 : ℕ) ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      have : (((k + 1 : ℕ) : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (k + 1)
      push_cast at *
      field_simp
      ring

/-- `exp(ln(t/(eᵗ − 1))) = t/(eᵗ − 1)`. -/
theorem expPS_bernLog : expPS bernLog = bernGen := by
  symm
  refine eq_expPS_of_derivative _ (by simp [bernGen]) ?_
  refine mul_left_cancel₀ (X_ne_zero (R := ℂ)) ?_
  rw [X_mul_derivative_bernGen, ← mul_assoc, X_mul_derivative_bernLog]
  ring

/-- `(eᵗ − 1)/t = ∑ tᵏ/(k + 1)!`. -/
noncomputable def expDivGen : ℂ⟦X⟧ := mk fun k => 1 / ((k + 1)! : ℂ)

theorem X_mul_expDivGen : X * expDivGen = exp ℂ - 1 := by
  ext k
  rcases k with _ | k
  · simp
  · rw [coeff_succ_X_mul, expDivGen, coeff_mk, map_sub, coeff_exp, coeff_one]
    simp

theorem bernGen_mul_expDivGen : bernGen * expDivGen = 1 := by
  refine mul_left_cancel₀ (X_ne_zero (R := ℂ)) ?_
  rw [mul_one, mul_left_comm, X_mul_expDivGen, bernGen_mul_exp]

/-! ### Generalized Bernoulli polynomials (DLMF 24.16.1) -/

/-- The coefficients of `ℓ ln(t/(eᵗ − 1)) + xt`. -/
noncomputable def genBernoulliSeq (ℓ x : ℂ) (k : ℕ) : ℂ :=
  ℓ * bernLog k + if k = 1 then x else 0

/-- **DLMF 24.16.1**: the generalized Bernoulli polynomials, defined by
`(t/(eᵗ − 1))^ℓ e^{xt} = ∑ B_n^{(ℓ)}(x) tⁿ/n!`; formally `B_n^{(ℓ)}(x) = n! [tⁿ]
exp(ℓ ln(t/(eᵗ − 1)) + xt)`. -/
noncomputable def genBernoulli (ℓ x : ℂ) (n : ℕ) : ℂ :=
  (n ! : ℂ) * cSeriesExp (genBernoulliSeq ℓ x) n

theorem genBernoulli_zero (ℓ x : ℂ) : genBernoulli ℓ x 0 = 1 := by
  simp [genBernoulli, cSeriesExp_zero]

theorem genBernoulli_one (ℓ x : ℂ) : genBernoulli ℓ x 1 = x - ℓ / 2 := by
  rw [genBernoulli, cSeriesExp_succ]
  simp [cSeriesExp_zero, genBernoulliSeq, bernLog]
  ring

theorem genBernoulli_two (ℓ x : ℂ) :
    genBernoulli ℓ x 2 = x ^ 2 - ℓ * x + ℓ * (3 * ℓ - 1) / 12 := by
  rw [genBernoulli, cSeriesExp_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
  norm_num [cSeriesExp_one, cSeriesExp_zero, genBernoulliSeq, bernLog, bernoulli'_two,
    bernoulli'_one, Nat.factorial]
  ring

/-- `ℓ = 1`: the ordinary generating function `t/(eᵗ − 1) e^{xt}`. -/
theorem expPS_genBernoulliSeq (ℓ x : ℂ) :
    expPS (genBernoulliSeq ℓ x) = expPS (fun k => ℓ * bernLog k) *
      mk fun k => x ^ k / (k ! : ℂ) := by
  rw [← expPS_linear, ← expPS_add]
  rfl

theorem bernLog_odd {k : ℕ} (hk : Odd k) (h1 : 1 < k) : bernLog k = 0 := by
  simp [bernLog, bernoulli'_eq_zero_of_odd hk h1]

theorem genBernoulliSeq_sub (ℓ x : ℂ) (k : ℕ) :
    genBernoulliSeq ℓ (ℓ - x) k = (-1) ^ k * genBernoulliSeq ℓ x k := by
  rcases Nat.lt_trichotomy k 1 with h | rfl | h
  · obtain rfl : k = 0 := by omega
    simp [genBernoulliSeq, bernLog_zero]
  · simp [genBernoulliSeq, bernLog]; ring
  · rcases Nat.even_or_odd k with he | ho
    · simp [genBernoulliSeq, he.neg_one_pow, ite_eq_right (show k ≠ 1 by omega)]
    · simp [genBernoulliSeq, ho.neg_one_pow, bernLog_odd ho h, ite_eq_right (show k ≠ 1 by omega)]

/-- **Symmetry** (DLMF §24.16(i)): `B_n^{(ℓ)}(ℓ − x) = (−1)ⁿ B_n^{(ℓ)}(x)`. -/
theorem genBernoulli_sub (ℓ x : ℂ) (n : ℕ) :
    genBernoulli ℓ (ℓ - x) n = (-1) ^ n * genBernoulli ℓ x n := by
  rw [genBernoulli, genBernoulli, show genBernoulliSeq ℓ (ℓ - x) =
    fun k => (-1) ^ k * genBernoulliSeq ℓ x k from funext (genBernoulliSeq_sub ℓ x),
    cSeriesExp_rescale]
  ring

/-- `B_n^{(ℓ)}(ℓ/2) = 0` for odd `n`. -/
theorem genBernoulli_half_odd (ℓ : ℂ) {n : ℕ} (hn : Odd n) : genBernoulli ℓ (ℓ / 2) n = 0 := by
  have h := genBernoulli_sub ℓ (ℓ / 2) n
  rw [show ℓ - ℓ / 2 = ℓ / 2 by ring, hn.neg_one_pow] at h
  linear_combination h / 2

/-- The generating function at `ℓ = 1 − n`: `∑ B_k^{(1−n)}(x) tᵏ/k! = ((eᵗ − 1)/t)^{n−1} e^{xt}`. -/
theorem mk_genBernoulli_one_sub (n : ℕ) (x : ℂ) :
    (mk fun k => genBernoulli (1 - (n + 1 : ℕ)) x k / (k ! : ℂ)) =
      expDivGen ^ n * mk fun k => x ^ k / (k ! : ℂ) := by
  have hcoef : (mk fun k => genBernoulli (1 - (n + 1 : ℕ)) x k / (k ! : ℂ)) =
      expPS (genBernoulliSeq (1 - (n + 1 : ℕ)) x) := by
    ext k
    rw [coeff_mk, genBernoulli, expPS, coeff_mk]
    have : (k ! : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    field_simp
  rw [hcoef, expPS_genBernoulliSeq]
  congr 1
  -- `exp(−n·bernLog) = ((eᵗ − 1)/t)ⁿ`
  have hneg := expPS_neg_mul (fun k => (n : ℂ) * bernLog k)
  rw [expPS_nsmul, expPS_bernLog] at hneg
  have hfun : (fun k => (1 - ((n + 1 : ℕ) : ℂ)) * bernLog k) =
      fun k => -((n : ℂ) * bernLog k) := by
    funext k; push_cast; ring
  rw [hfun]
  calc expPS (fun k => -((n : ℂ) * bernLog k))
      = expPS (fun k => -((n : ℂ) * bernLog k)) * (bernGen * expDivGen) ^ n := by
        rw [bernGen_mul_expDivGen, one_pow, mul_one]
    _ = (expPS (fun k => -((n : ℂ) * bernLog k)) * bernGen ^ n) * expDivGen ^ n := by ring
    _ = expDivGen ^ n := by rw [hneg, one_mul]

end Azurite.DLMF
