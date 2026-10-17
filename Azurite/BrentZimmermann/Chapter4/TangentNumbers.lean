/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BrentZimmermann.Chapter4.BernoulliRecurrence
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Brent–Zimmermann §4.7.2 (continued): Tangent numbers

The tangent numbers `T_j` are defined by

  `tan x = ∑_{j≥1} T_j x^(2j−1)/(2j−1)!`,                                                     (4.61)

are positive integers, and are related to the Bernoulli numbers by

  `T_j = (−1)^(j−1) 2^(2j) (2^(2j) − 1) B_{2j} / (2j)`,                                       (4.62)

conversely `B_j = (−1)^(j/2−1) j T_{j/2} / (4^j − 2^j)` for even `j > 0` (`B_0 = 1`, `B_1 = −1/2`,
`B_j = 0` for odd `j > 1`).  (4.62) shows that the odd primes in the denominator of `B_{2j}` divide
`2^(2j) − 1` (in fact, by von Staudt–Clausen, `p ∣ den B_{2j}` iff `(p − 1) ∣ 2j`).

With `t = tan x` and `D = d/dx`, `Dt = 1 + t²` and `D(tⁿ) = n tⁿ⁻¹ (1 + t²)`, so `Dⁿ t = P_n(t)`
for polynomials `P_n(t) = ∑_j p_{n,j} t^j` with `P_0 = t`, `P_n = D P_{n−1}`, `deg P_n = n + 1` and

  `p_{n,j} = (j − 1) p_{n−1,j−1} + (j + 1) p_{n−1,j+1}`;                                      (4.63)

`p_{n,j} = 0` when `n + j` is even (`P_{2k}` odd, `P_{2k+1}` even polynomials).

What is formalized:

* `tanDerivPoly n : ℤ[X]` (`P_n`): `P_0 = X`, `P_{n+1} = P_n' (1 + X²)`; (4.63) as
  `coeff_tanDerivPoly_succ_zero` (`p_{n+1,0} = p_{n,1}`) and `coeff_tanDerivPoly_succ`
  (`p_{n+1,j+1} = j p_{n,j} + (j+2) p_{n,j+2}`); `coeff_tanDerivPoly_nonneg`; the parity
  `coeff_tanDerivPoly_eq_zero_of_even`; `coeff_tanDerivPoly_eq_zero_of_lt`,
  `coeff_tanDerivPoly_top` (`p_{n,n+1} = n!`) and `natDegree_tanDerivPoly` (`= n + 1`).
* `tanDerivPoly_succ_eq_sum` — the Leibniz form `P_{n+1} = [n = 0] + ∑_a C(n,a) P_a P_{n−a}`
  (so the exponential generating function `∑ P_n(0) xⁿ/n!` solves `y' = 1 + y²`).
* `iteratedDeriv_tan`: `Dⁿ tan x = P_n(tan x)` wherever `cos x ≠ 0`, hence
  `iteratedDeriv_tan_zero`: `Dⁿ tan 0 = p_{n,0}` — the Taylor coefficients of (4.61) are the
  `p_{2j−1,0}`.
* `tangentNumber j := p_{2j−1,0}` (so `T_j = D^(2j−1) tan 0`, `iteratedDeriv_tan_zero_eq`);
  `tangentNumber_one = 1`, `tangentNumber_two = 2`, `tangentNumber_three = 16`.
* (4.62) `tangentNumber_eq_bernoulli` and its inverse `bernoulli_two_mul_eq_tangentNumber`,
  proved through formal power series over `ℚ`: `tanDerivSeries = ∑ p_{n,0} Xⁿ/n!` satisfies
  `y' = 1 + y²` (from the Leibniz identity); the hyperbolic series `coshSeries`, `sinhSeries`,
  `tanhSeries = sinh/cosh` satisfy `tanh' = 1 − tanh²` and, from (4.57) scaled by `2` and `4`,
  `X tanh = ∑ (16^k − 4^k) C_k X^(2k)` (`X_mul_tanhSeries`), so
  `coeff (2k+1) tanh = (16^(k+1) − 4^(k+1)) C_{k+1}` and the even coefficients vanish; the
  sign-twisted `tanSeries` (`(−1)^k` at `X^(2k+1)`) then satisfies `y' = 1 + y²`
  (`derivative_tanSeries`), and the formal ODE with `y(0) = 0` has a unique solution
  (`eq_of_derivative_eq_one_add_sq`), giving `tanDerivSeries = tanSeries`.
* `tangentNumber_pos` (`T_j > 0`, from the sign of `B_{2j}`), `bernoulli_den_dvd`
  (`den B_{2j} ∣ 4^j (4^j − 1)`) and `odd_prime_dvd_den_bernoulli` (an odd prime dividing
  `den B_{2j}` divides `2^(2j) − 1`).

Not formalized: the analytic identity (4.61) itself (convergence for `|x| < π/2`; Mathlib has
no Taylor series for `tan`) — the Taylor coefficients are identified instead via
`iteratedDeriv_tan_zero`; von Staudt–Clausen is Mathlib's `Bernoulli.vonStaudt_clausen`.
-/

namespace Azurite

namespace BZ

open Finset

section Polys

open Polynomial

/-! ### The derivative polynomials `P_n` and the recurrence (4.63) -/

/-- `P_n`, with `Dⁿ tan = P_n(tan)`: `P_0 = X`, `P_{n+1} = P_n' (1 + X²)`. -/
noncomputable def tanDerivPoly : ℕ → ℤ[X]
  | 0 => X
  | n + 1 => derivative (tanDerivPoly n) * (1 + X ^ 2)

theorem tanDerivPoly_zero : tanDerivPoly 0 = X := rfl

theorem tanDerivPoly_succ (n : ℕ) :
    tanDerivPoly (n + 1) = derivative (tanDerivPoly n) * (1 + X ^ 2) := rfl

theorem tanDerivPoly_one : tanDerivPoly 1 = 1 + X ^ 2 := by
  rw [tanDerivPoly_succ, tanDerivPoly_zero, derivative_X, one_mul]

/-- (4.63) at `j = 0`: `p_{n+1,0} = p_{n,1}`. -/
theorem coeff_tanDerivPoly_succ_zero (n : ℕ) :
    (tanDerivPoly (n + 1)).coeff 0 = (tanDerivPoly n).coeff 1 := by
  rw [tanDerivPoly_succ, mul_add, mul_one, coeff_add, coeff_mul_X_pow', coeff_derivative]
  simp

/-- (4.63): `p_{n+1,j+1} = j p_{n,j} + (j+2) p_{n,j+2}`. -/
theorem coeff_tanDerivPoly_succ (n j : ℕ) :
    (tanDerivPoly (n + 1)).coeff (j + 1)
      = j * (tanDerivPoly n).coeff j + (j + 2) * (tanDerivPoly n).coeff (j + 2) := by
  rw [tanDerivPoly_succ, mul_add, mul_one, coeff_add, coeff_mul_X_pow', coeff_derivative]
  rcases j with _ | j
  · simp
    ring
  · rw [ite_eq_left (by omega), show j + 1 + 1 - 2 = j by omega, coeff_derivative,
      show j + 1 + 2 = j + 1 + 1 + 1 from rfl]
    push_cast
    ring

theorem coeff_tanDerivPoly_nonneg (n j : ℕ) : 0 ≤ (tanDerivPoly n).coeff j := by
  induction n generalizing j with
  | zero =>
    rw [tanDerivPoly_zero, coeff_X]
    split_ifs <;> norm_num
  | succ n ih =>
    rcases j with _ | j
    · rw [coeff_tanDerivPoly_succ_zero]; exact ih 1
    · rw [coeff_tanDerivPoly_succ]
      have h1 := ih j
      have h2 := ih (j + 2)
      positivity

/-- `p_{n,j} = 0` when `n + j` is even: `P_{2k}` is odd and `P_{2k+1}` is even. -/
theorem coeff_tanDerivPoly_eq_zero_of_even (n : ℕ) : ∀ j, Even (n + j) →
    (tanDerivPoly n).coeff j = 0 := by
  induction n with
  | zero =>
    intro j hj
    obtain ⟨m, hm⟩ := hj
    rw [tanDerivPoly_zero, coeff_X, ite_eq_right (by omega)]
  | succ n ih =>
    intro j hj
    obtain ⟨m, hm⟩ := hj
    rcases j with _ | j
    · rw [coeff_tanDerivPoly_succ_zero, ih 1 ⟨m, by omega⟩]
    · rw [coeff_tanDerivPoly_succ, ih j ⟨m - 1, by omega⟩, ih (j + 2) ⟨m, by omega⟩]
      ring

theorem coeff_tanDerivPoly_eq_zero_of_lt (n : ℕ) : ∀ j, n + 1 < j →
    (tanDerivPoly n).coeff j = 0 := by
  induction n with
  | zero =>
    intro j hj
    rw [tanDerivPoly_zero, coeff_X, ite_eq_right (by omega)]
  | succ n ih =>
    intro j hj
    rcases j with _ | j
    · omega
    · rw [coeff_tanDerivPoly_succ, ih j (by omega), ih (j + 2) (by omega)]
      ring

/-- The leading coefficient: `p_{n,n+1} = n!`. -/
theorem coeff_tanDerivPoly_top (n : ℕ) : (tanDerivPoly n).coeff (n + 1) = n.factorial := by
  induction n with
  | zero => simp [tanDerivPoly_zero, coeff_X]
  | succ n ih =>
    rw [coeff_tanDerivPoly_succ, ih, coeff_tanDerivPoly_eq_zero_of_lt n (n + 1 + 2) (by omega),
      Nat.factorial_succ]
    push_cast
    ring

/-- `deg P_n = n + 1`. -/
theorem natDegree_tanDerivPoly (n : ℕ) : (tanDerivPoly n).natDegree = n + 1 :=
  natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr fun N hN => coeff_tanDerivPoly_eq_zero_of_lt n N hN)
    (by rw [coeff_tanDerivPoly_top]; exact_mod_cast Nat.factorial_ne_zero n)

/-! ### The Leibniz identity -/

/-- Pascal's rule, summed: the inductive step of a binomial-type identity. -/
theorem pascal_sum {R : Type*} [CommSemiring R] (q : ℕ → ℕ → R) (n : ℕ) :
    ∑ a ∈ range (n + 1), (n.choose a : R) * (q (a + 1) (n - a) + q a (n - a + 1))
      = ∑ a ∈ range (n + 2), ((n + 1).choose a : R) * q a (n + 1 - a) := by
  rw [sum_range_succ' (fun a => ((n + 1).choose a : R) * q a (n + 1 - a))]
  simp only [Nat.choose_succ_succ', Nat.cast_add, add_mul, Nat.choose_zero_right, Nat.cast_one,
    one_mul, Nat.sub_zero, Nat.add_sub_add_right, mul_add]
  rw [sum_add_distrib, sum_add_distrib, sum_range_succ (fun a => (n.choose (a + 1) : R) *
    q (a + 1) (n - a)), Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero,
    sum_range_succ' (fun a => (n.choose a : R) * q a (n - a + 1))]
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
  have : ∀ a ∈ range n, (n.choose (a + 1) : R) * q (a + 1) (n - (a + 1) + 1)
      = (n.choose (a + 1) : R) * q (a + 1) (n - a) := fun a ha => by
    rw [show n - (a + 1) + 1 = n - a by have := mem_range.mp ha; omega]
  rw [sum_congr rfl this]
  ring

/-- `P_{n+1} = [n = 0] + ∑_{a ≤ n} C(n, a) P_a P_{n−a}`: the Leibniz rule for `Dⁿ(1 + t²)`. -/
theorem tanDerivPoly_succ_eq_sum (n : ℕ) :
    tanDerivPoly (n + 1)
      = (if n = 0 then 1 else 0)
        + ∑ a ∈ range (n + 1), (n.choose a : ℤ[X]) * (tanDerivPoly a * tanDerivPoly (n - a)) := by
  induction n with
  | zero =>
    rw [tanDerivPoly_one, sum_range_one]
    simp [tanDerivPoly_zero]
    ring
  | succ n ih =>
    rw [tanDerivPoly_succ, ih, derivative_add, derivative_sum, add_mul, sum_mul,
      ite_eq_right (Nat.succ_ne_zero n), zero_add]
    have hd : derivative (if n = 0 then (1 : ℤ[X]) else 0) = 0 := by split_ifs <;> simp
    rw [hd, zero_mul, zero_add]
    have hterm : ∀ a ∈ range (n + 1),
        derivative ((n.choose a : ℤ[X]) * (tanDerivPoly a * tanDerivPoly (n - a))) * (1 + X ^ 2)
          = (n.choose a : ℤ[X]) * (tanDerivPoly (a + 1) * tanDerivPoly (n - a)
            + tanDerivPoly a * tanDerivPoly (n - a + 1)) := fun a _ => by
      rw [derivative_natCast_mul, derivative_mul, tanDerivPoly_succ, tanDerivPoly_succ]
      ring
    rw [sum_congr rfl hterm]
    exact pascal_sum (fun a b => tanDerivPoly a * tanDerivPoly b) n

/-! ### `Dⁿ tan = P_n(tan)` -/

/-- `Dⁿ tan x = P_n(tan x)` wherever `cos x ≠ 0`. -/
theorem iteratedDeriv_tan (n : ℕ) : ∀ x : ℝ, Real.cos x ≠ 0 →
    iteratedDeriv n Real.tan x
      = ((tanDerivPoly n).map (Int.castRingHom ℝ)).eval (Real.tan x) := by
  induction n with
  | zero => intro x _; simp [tanDerivPoly_zero]
  | succ n ih =>
    intro x hx
    have hU : IsOpen {y : ℝ | Real.cos y ≠ 0} := isOpen_ne_fun Real.continuous_cos continuous_const
    have heq : iteratedDeriv n Real.tan =ᶠ[nhds x]
        fun y => ((tanDerivPoly n).map (Int.castRingHom ℝ)).eval (Real.tan y) :=
      Filter.eventuallyEq_of_mem (hU.mem_nhds hx) fun y hy => ih y hy
    rw [iteratedDeriv_succ, heq.deriv_eq]
    have hd : HasDerivAt (fun y => ((tanDerivPoly n).map (Int.castRingHom ℝ)).eval (Real.tan y))
        ((derivative ((tanDerivPoly n).map (Int.castRingHom ℝ))).eval (Real.tan x)
          * (1 / Real.cos x ^ 2)) x :=
      (Polynomial.hasDerivAt _ (Real.tan x)).comp x (Real.hasDerivAt_tan hx)
    rw [hd.deriv, tanDerivPoly_succ, Polynomial.map_mul, derivative_map, eval_mul, one_div,
      ← Real.inv_one_add_tan_sq hx, inv_inv]
    simp

/-- `Dⁿ tan 0 = p_{n,0}`: the Taylor coefficients of `tan` at `0` are the constant terms of the
`P_n`. -/
theorem iteratedDeriv_tan_zero (n : ℕ) :
    iteratedDeriv n Real.tan 0 = ((tanDerivPoly n).coeff 0 : ℝ) := by
  rw [iteratedDeriv_tan n 0 (by simp), Real.tan_zero, ← coeff_zero_eq_eval_zero, coeff_map,
    eq_intCast]

/-! ### Tangent numbers -/

/-- The tangent numbers `T_j = p_{2j−1,0} = D^(2j−1) tan 0` (`j ≥ 1`). -/
noncomputable def tangentNumber (j : ℕ) : ℤ := (tanDerivPoly (2 * j - 1)).coeff 0

theorem iteratedDeriv_tan_zero_eq (j : ℕ) :
    iteratedDeriv (2 * j - 1) Real.tan 0 = (tangentNumber j : ℝ) :=
  iteratedDeriv_tan_zero _

theorem tangentNumber_one : tangentNumber 1 = 1 := by
  simp [tangentNumber, tanDerivPoly_one]

theorem tangentNumber_two : tangentNumber 2 = 2 := by
  rw [tangentNumber, show 2 * 2 - 1 = 2 + 1 by rfl, coeff_tanDerivPoly_succ_zero,
    coeff_tanDerivPoly_succ, tanDerivPoly_one]
  simp [coeff_X_pow, coeff_one]

theorem tangentNumber_three : tangentNumber 3 = 16 := by
  rw [tangentNumber, show 2 * 3 - 1 = 4 + 1 by rfl, coeff_tanDerivPoly_succ_zero,
    show (4 : ℕ) = 3 + 1 by rfl, coeff_tanDerivPoly_succ, show (3 : ℕ) = 2 + 1 by rfl,
    coeff_tanDerivPoly_succ, show (2 : ℕ) = 1 + 1 by rfl, coeff_tanDerivPoly_succ,
    coeff_tanDerivPoly_succ, coeff_tanDerivPoly_succ, coeff_tanDerivPoly_succ,
    coeff_tanDerivPoly_succ, tanDerivPoly_one]
  simp [tanDerivPoly_zero, coeff_X]

end Polys

section Series

open PowerSeries

/-! ### The formal power series of `tan` from the polynomials -/

/-- `∑ p_{n,0} Xⁿ/n!`, the formal Taylor series of `tan` computed from the `P_n`. -/
noncomputable def tanDerivSeries : PowerSeries ℚ :=
  PowerSeries.mk fun n => ((tanDerivPoly n).coeff 0 : ℚ) / n.factorial

/-- The Leibniz identity at `t = 0`, divided by `n!`. -/
theorem coeff_zero_tanDerivPoly_succ_div (n : ℕ) :
    ((tanDerivPoly (n + 1)).coeff 0 : ℚ) / n.factorial
      = (if n = 0 then 1 else 0) + ∑ a ∈ range (n + 1),
          ((tanDerivPoly a).coeff 0 : ℚ) / a.factorial
            * (((tanDerivPoly (n - a)).coeff 0 : ℚ) / (n - a).factorial) := by
  have h := congrArg (fun p : Polynomial ℤ => (p.coeff 0 : ℚ)) (tanDerivPoly_succ_eq_sum n)
  simp only [Polynomial.coeff_add, Polynomial.finsetSum_coeff, ← Polynomial.C_eq_natCast,
    Polynomial.mul_coeff_zero, Polynomial.coeff_C_zero] at h
  rw [h]
  have hite : ((if n = 0 then (1 : Polynomial ℤ) else 0).coeff 0 : ℚ) / n.factorial
      = if n = 0 then 1 else 0 := by
    split_ifs with hn <;> simp [hn]
  push_cast
  rw [add_div, hite, sum_div]
  congr 1
  refine sum_congr rfl fun a ha => ?_
  have ha' : a ≤ n := by have := mem_range.mp ha; omega
  rw [Nat.cast_choose ℚ ha']
  have h1 : (a.factorial : ℚ) ≠ 0 := by positivity
  have h2 : ((n - a).factorial : ℚ) ≠ 0 := by positivity
  have h3 : (n.factorial : ℚ) ≠ 0 := by positivity
  field_simp

/-- `tanDerivSeries` solves `y' = 1 + y²`. -/
theorem derivative_tanDerivSeries : d⁄dX tanDerivSeries = 1 + tanDerivSeries ^ 2 := by
  ext n
  rw [coeff_derivative, map_add, coeff_one, pow_two, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [tanDerivSeries, coeff_mk]
  have h := coeff_zero_tanDerivPoly_succ_div n
  rw [Nat.factorial_succ] at *
  push_cast at *
  have h3 : (n.factorial : ℚ) ≠ 0 := by positivity
  have h4 : ((n : ℚ) + 1) ≠ 0 := by positivity
  rw [← h]
  field_simp

/-! ### The hyperbolic series over `ℚ` -/

/-- `e^(−x)`. -/
noncomputable def expNeg : PowerSeries ℚ := rescale (-1 : ℚ) (exp ℚ)

theorem exp_mul_expNeg : exp ℚ * expNeg = 1 := exp_mul_exp_neg_eq_one (A := ℚ)

theorem derivative_exp : d⁄dX (exp ℚ) = exp ℚ := by
  ext n
  rw [coeff_derivative, coeff_exp, coeff_exp, algebraMap_rat_rat, algebraMap_rat_rat,
    Nat.factorial_succ]
  push_cast
  field_simp

theorem derivative_rescale (a : ℚ) (f : PowerSeries ℚ) :
    d⁄dX (rescale a f) = C a * rescale a (d⁄dX f) := by
  ext n
  rw [coeff_derivative, coeff_rescale, coeff_C_mul, coeff_rescale, coeff_derivative, pow_succ]
  ring

theorem derivative_expNeg : d⁄dX expNeg = -expNeg := by
  unfold expNeg
  rw [derivative_rescale, derivative_exp, map_neg, map_one, neg_one_mul]

/-- `cosh x = (e^x + e^(−x))/2`. -/
noncomputable def coshSeries : PowerSeries ℚ := C (1 / 2 : ℚ) * (exp ℚ + expNeg)

/-- `sinh x = (e^x − e^(−x))/2`. -/
noncomputable def sinhSeries : PowerSeries ℚ := C (1 / 2 : ℚ) * (exp ℚ - expNeg)

/-- `tanh x = sinh x / cosh x`. -/
noncomputable def tanhSeries : PowerSeries ℚ := sinhSeries * coshSeries⁻¹

theorem derivative_coshSeries : d⁄dX coshSeries = sinhSeries := by
  unfold coshSeries sinhSeries
  rw [Derivation.leibniz, derivative_C, smul_zero, add_zero, map_add, derivative_exp,
    derivative_expNeg, smul_eq_mul, sub_eq_add_neg]

theorem derivative_sinhSeries : d⁄dX sinhSeries = coshSeries := by
  unfold coshSeries sinhSeries
  rw [Derivation.leibniz, derivative_C, smul_zero, add_zero, map_sub, derivative_exp,
    derivative_expNeg, smul_eq_mul, sub_neg_eq_add]

theorem coshSeries_sq_sub_sinhSeries_sq : coshSeries ^ 2 - sinhSeries ^ 2 = 1 := by
  unfold coshSeries sinhSeries
  have hc : C (1 / 2 : ℚ) * 2 = (1 : PowerSeries ℚ) := by
    rw [show (2 : PowerSeries ℚ) = C 2 from (map_ofNat C 2).symm, ← map_mul]
    norm_num
  have h := exp_mul_expNeg
  linear_combination (C (1 / 2 : ℚ) * 2) ^ 2 * h + (C (1 / 2 : ℚ) * 2 + 1) * hc

theorem constantCoeff_coshSeries : constantCoeff coshSeries = 1 := by
  unfold coshSeries expNeg
  simp only [map_mul, map_add, ← coeff_zero_eq_constantCoeff_apply, coeff_rescale, coeff_exp,
    algebraMap_rat_rat]
  norm_num

theorem coshSeries_mul_inv : coshSeries * coshSeries⁻¹ = 1 :=
  PowerSeries.mul_inv_cancel _ (by rw [constantCoeff_coshSeries]; exact one_ne_zero)

/-- `tanh' = 1 − tanh²`. -/
theorem derivative_tanhSeries : d⁄dX tanhSeries = 1 - tanhSeries ^ 2 := by
  unfold tanhSeries
  have hinv := coshSeries_mul_inv
  have hdinv : d⁄dX coshSeries⁻¹ = -coshSeries⁻¹ ^ 2 • d⁄dX coshSeries :=
    Derivation.leibniz_of_mul_eq_one d⁄dX (PowerSeries.inv_mul_cancel _
      (by rw [constantCoeff_coshSeries]; exact one_ne_zero))
  rw [Derivation.leibniz, hdinv, derivative_sinhSeries, derivative_coshSeries, smul_eq_mul,
    smul_eq_mul, smul_eq_mul]
  linear_combination hinv

theorem constantCoeff_tanhSeries : constantCoeff tanhSeries = 0 := by
  unfold tanhSeries sinhSeries expNeg
  simp only [map_mul, map_sub, ← coeff_zero_eq_constantCoeff_apply, coeff_rescale, coeff_exp,
    algebraMap_rat_rat]
  norm_num

theorem rescale_C' (a r : ℚ) : rescale a (C r : PowerSeries ℚ) = C r := by
  ext n
  rw [coeff_rescale, coeff_C]
  split_ifs with h <;> simp [h]

/-- (4.57) rescaled by `2`: `S(2x) (e^x − e^(−x)) = x (e^x + e^(−x))`. -/
theorem rescale_two_scaledBernoulliPowerSeries_mul :
    rescale (2 : ℚ) scaledBernoulliPowerSeries * (exp ℚ - expNeg) = X * (exp ℚ + expNeg) := by
  have h := congrArg (rescale (2 : ℚ)) scaledBernoulliPowerSeries_mul_sinh
  have hc : C (1 / 2 : ℚ) * C (2 : ℚ) = (1 : PowerSeries ℚ) := by rw [← map_mul]; norm_num
  simp only [map_mul, map_sub, map_add, rescale_X, rescale_C'] at h
  rw [← RingHom.comp_apply, ← rescale_mul, ← RingHom.comp_apply, ← rescale_mul] at h
  rw [show (1 / 2 : ℚ) * 2 = 1 by norm_num, show (-1 / 2 : ℚ) * 2 = -1 by norm_num, rescale_one,
    RingHom.id_apply] at h
  unfold expNeg
  linear_combination h + (X * (exp ℚ + rescale (-1 : ℚ) (exp ℚ))) * hc

/-- (4.57) rescaled by `4`: `S(4x) (e^(2x) − e^(−2x)) = 2x (e^(2x) + e^(−2x))`. -/
theorem rescale_four_scaledBernoulliPowerSeries_mul :
    rescale (4 : ℚ) scaledBernoulliPowerSeries * (exp ℚ ^ 2 - expNeg ^ 2)
      = C 2 * X * (exp ℚ ^ 2 + expNeg ^ 2) := by
  have h := congrArg (rescale (4 : ℚ)) scaledBernoulliPowerSeries_mul_sinh
  have hc : C (1 / 2 : ℚ) * C (4 : ℚ) = C (2 : ℚ) := by rw [← map_mul]; norm_num
  simp only [map_mul, map_sub, map_add, rescale_X, rescale_C'] at h
  rw [← RingHom.comp_apply, ← rescale_mul, ← RingHom.comp_apply, ← rescale_mul] at h
  rw [show (1 / 2 : ℚ) * 4 = ((2 : ℕ) : ℚ) by norm_num, show (-1 / 2 : ℚ) * 4 = -1 + -1 by norm_num,
    ← exp_pow_eq_rescale_exp, ← exp_mul_exp_eq_exp_add, ← pow_two] at h
  unfold expNeg
  linear_combination h + (X * (exp ℚ ^ 2 + rescale (-1 : ℚ) (exp ℚ) ^ 2)) * hc

/-- `x tanh x = S(4x) − S(2x) = ∑ (16^k − 4^k) C_k x^(2k)`, i.e. `tanh x = 2 coth 2x − coth x`. -/
theorem X_mul_tanhSeries :
    X * tanhSeries = rescale (4 : ℚ) scaledBernoulliPowerSeries
      - rescale (2 : ℚ) scaledBernoulliPowerSeries := by
  set S₂ := rescale (2 : ℚ) scaledBernoulliPowerSeries
  set S₄ := rescale (4 : ℚ) scaledBernoulliPowerSeries
  set u := exp ℚ
  set v := expNeg
  have h2 : S₂ * (u - v) = X * (u + v) := rescale_two_scaledBernoulliPowerSeries_mul
  have h4 : S₄ * (u ^ 2 - v ^ 2) = C 2 * X * (u ^ 2 + v ^ 2) :=
    rescale_four_scaledBernoulliPowerSeries_mul
  have huv : u * v = 1 := exp_mul_expNeg
  have hc : C (2 : ℚ) = (2 : PowerSeries ℚ) := map_ofNat C 2
  rw [hc] at h4
  -- `(S₄ − S₂)(u + v)(u − v) = X (u − v)²`
  have hkey : (S₄ - S₂) * (u + v) * (u - v) = X * (u - v) ^ 2 := by
    linear_combination h4 - (u + v) * h2
  have hne : u - v ≠ 0 := by
    intro h0
    have := congrArg (coeff 1) h0
    rw [map_sub, map_zero] at this
    simp [u, v, expNeg, coeff_rescale, coeff_exp] at this
  have hcosh : (S₄ - S₂) * (u + v) = X * (u - v) := by
    apply mul_right_cancel₀ hne
    rw [hkey]; ring
  -- divide by `2 cosh`
  have hinv := coshSeries_mul_inv
  unfold tanhSeries sinhSeries
  have hcosh' : (S₄ - S₂) * coshSeries = X * (C (1 / 2 : ℚ) * (u - v)) := by
    unfold coshSeries
    linear_combination (C (1 / 2 : ℚ)) * hcosh
  calc X * (C (1 / 2 : ℚ) * (u - v) * coshSeries⁻¹)
      = (S₄ - S₂) * coshSeries * coshSeries⁻¹ := by rw [hcosh']; ring
    _ = S₄ - S₂ := by rw [mul_assoc, hinv, mul_one]

theorem coeff_tanhSeries_odd (k : ℕ) :
    coeff (2 * k + 1) tanhSeries
      = (4 ^ (2 * (k + 1)) - 2 ^ (2 * (k + 1))) * scaledBernoulli (k + 1) := by
  have h := congrArg (coeff (2 * (k + 1))) X_mul_tanhSeries
  rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, coeff_succ_X_mul, map_sub, coeff_rescale,
    coeff_rescale, show 2 * k + 1 + 1 = 2 * (k + 1) by ring,
    coeff_scaledBernoulliPowerSeries_even] at h
  rw [h]
  ring

theorem coeff_tanhSeries_even (k : ℕ) : coeff (2 * k) tanhSeries = 0 := by
  rcases k with _ | k
  · rw [mul_zero, coeff_zero_eq_constantCoeff_apply, constantCoeff_tanhSeries]
  · have h := congrArg (coeff (2 * (k + 1) + 1)) X_mul_tanhSeries
    rw [coeff_succ_X_mul, map_sub, coeff_rescale, coeff_rescale,
      coeff_scaledBernoulliPowerSeries_odd] at h
    rw [h]
    ring

/-! ### The sign twist `tanh ↦ tan` and the formal ODE -/

/-- The formal series of `tan` obtained from `tanh` by the sign twist `(−1)^k` at `x^(2k+1)`
(`tan x = −i tanh(ix)`). -/
noncomputable def tanSeries : PowerSeries ℚ :=
  PowerSeries.mk fun n => (-1) ^ (n / 2) * coeff n tanhSeries

theorem coeff_tanSeries (n : ℕ) : coeff n tanSeries = (-1) ^ (n / 2) * coeff n tanhSeries :=
  coeff_mk _ _

/-- Products of two odd coefficients: the twist contributes `−(−1)^k` on the antidiagonal of `2k`.
-/
theorem tanSeries_mul_term {k : ℕ} {p : ℕ × ℕ} (hp : p ∈ antidiagonal (2 * k)) :
    coeff p.1 tanSeries * coeff p.2 tanSeries
      = -(-1) ^ k * (coeff p.1 tanhSeries * coeff p.2 tanhSeries) := by
  have hsum := mem_antidiagonal.mp hp
  rw [coeff_tanSeries, coeff_tanSeries]
  rcases Nat.even_or_odd p.1 with ⟨a, ha⟩ | ⟨a, ha⟩
  · rw [show p.1 = 2 * a by omega, coeff_tanhSeries_even]
    ring
  · obtain ⟨b, hb⟩ : ∃ b, p.2 = 2 * b + 1 := ⟨p.2 / 2, by omega⟩
    obtain rfl : k = a + b + 1 := by omega
    rw [show p.1 = 2 * a + 1 by omega, hb, show (2 * a + 1) / 2 = a by omega,
      show (2 * b + 1) / 2 = b by omega]
    ring

/-- `tan' = 1 + tan²` (from `tanh' = 1 − tanh²` and the sign twist). -/
theorem derivative_tanSeries : d⁄dX tanSeries = 1 + tanSeries ^ 2 := by
  ext n
  rw [coeff_derivative, coeff_tanSeries, map_add, coeff_one, pow_two, coeff_mul]
  have hh := congrArg (coeff n) derivative_tanhSeries
  rw [coeff_derivative, map_sub, coeff_one, pow_two, coeff_mul] at hh
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · obtain rfl : n = 2 * k := by omega
    rw [sum_congr rfl fun p hp => tanSeries_mul_term hp, ← mul_sum,
      show (2 * k + 1) / 2 = k by omega]
    have hodd : (if 2 * k = 0 then (1 : ℚ) else 0) = (-1) ^ k * (if 2 * k = 0 then 1 else 0) := by
      split_ifs with h0
      · rw [show k = 0 by omega]; ring
      · ring
    rw [hodd]
    linear_combination (-1 : ℚ) ^ k * hh
  · obtain rfl : n = 2 * k + 1 := by omega
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, coeff_tanhSeries_even, mul_zero, zero_mul,
      ite_eq_right (by omega), zero_add]
    symm
    refine sum_eq_zero fun p hp => ?_
    have hsum := mem_antidiagonal.mp hp
    rw [coeff_tanSeries, coeff_tanSeries]
    rcases Nat.even_or_odd p.1 with ⟨a, ha⟩ | ⟨a, ha⟩
    · rw [show p.1 = 2 * a by omega, coeff_tanhSeries_even]; ring
    · rw [show p.2 = 2 * (p.2 / 2) by omega, coeff_tanhSeries_even]; ring

/-- The formal ODE `y' = 1 + y²` with given `y(0)` has at most one solution. -/
theorem eq_of_derivative_eq_one_add_sq {f g : PowerSeries ℚ} (hf : d⁄dX f = 1 + f ^ 2)
    (hg : d⁄dX g = 1 + g ^ 2) (h0 : constantCoeff f = constantCoeff g) : f = g := by
  ext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, h0]
    · have hf' := congrArg (coeff n) hf
      have hg' := congrArg (coeff n) hg
      rw [coeff_derivative] at hf' hg'
      have hsq : coeff n (f ^ 2) = coeff n (g ^ 2) := by
        rw [pow_two, pow_two, coeff_mul, coeff_mul]
        refine sum_congr rfl fun p hp => ?_
        have := mem_antidiagonal.mp hp
        rw [ih p.1 (by omega), ih p.2 (by omega)]
      have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
      apply mul_right_cancel₀ hn
      rw [hf', hg', map_add, map_add, hsq]

theorem tanDerivSeries_eq_tanSeries : tanDerivSeries = tanSeries :=
  eq_of_derivative_eq_one_add_sq derivative_tanDerivSeries derivative_tanSeries (by
    rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply,
      coeff_tanSeries, tanDerivSeries, coeff_mk, tanDerivPoly_zero,
      coeff_zero_eq_constantCoeff_apply, constantCoeff_tanhSeries]
    simp)

/-! ### (4.62) and consequences -/

/-- (4.62): `T_{k+1} = (−1)^k 4^(k+1) (4^(k+1) − 1) B_{2(k+1)} / (2(k+1))`. -/
theorem tangentNumber_eq_bernoulli (k : ℕ) :
    (tangentNumber (k + 1) : ℚ)
      = (-1) ^ k * 4 ^ (k + 1) * (4 ^ (k + 1) - 1) * bernoulli (2 * (k + 1)) / (2 * (k + 1)) := by
  have h := congrArg (coeff (2 * k + 1)) tanDerivSeries_eq_tanSeries
  rw [tanDerivSeries, coeff_mk, coeff_tanSeries, coeff_tanhSeries_odd,
    show (2 * k + 1) / 2 = k by omega] at h
  unfold tangentNumber scaledBernoulli at *
  rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
  rw [show (2 * (k + 1)).factorial = (2 * (k + 1)) * (2 * k + 1).factorial by
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Nat.factorial_succ],
    show (4 : ℚ) ^ (2 * (k + 1)) = (4 ^ (k + 1)) ^ 2 by rw [← pow_mul, mul_comm],
    show (2 : ℚ) ^ (2 * (k + 1)) = 4 ^ (k + 1) by rw [pow_mul]; norm_num] at h
  have hf : ((2 * k + 1).factorial : ℚ) ≠ 0 := by positivity
  have h2 : ((2 * (k + 1) : ℕ) : ℚ) ≠ 0 := by positivity
  push_cast at h h2 ⊢
  field_simp at h
  rw [eq_div_iff (by positivity)]
  linear_combination h

/-- The inverse of (4.62): `B_{2(k+1)} = (−1)^k (2(k+1)) T_{k+1} / (4^(2(k+1)) − 2^(2(k+1)))`. -/
theorem bernoulli_two_mul_eq_tangentNumber (k : ℕ) :
    bernoulli (2 * (k + 1))
      = (-1) ^ k * (2 * (k + 1)) * tangentNumber (k + 1)
        / (4 ^ (2 * (k + 1)) - 2 ^ (2 * (k + 1))) := by
  have h := tangentNumber_eq_bernoulli k
  have h4 : (1 : ℚ) < 4 ^ (k + 1) := one_lt_pow₀ (by norm_num) (by omega)
  have hne : (4 : ℚ) ^ (2 * (k + 1)) - 2 ^ (2 * (k + 1)) ≠ 0 := by
    rw [show (4 : ℚ) ^ (2 * (k + 1)) = (4 ^ (k + 1)) ^ 2 by rw [← pow_mul, mul_comm],
      show (2 : ℚ) ^ (2 * (k + 1)) = 4 ^ (k + 1) by rw [pow_mul]; norm_num]
    nlinarith
  have h2 : (2 * ((k : ℚ) + 1)) ≠ 0 := by positivity
  rw [eq_div_iff h2] at h
  have hsq : ((-1 : ℚ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  rw [eq_div_iff hne,
    show (4 : ℚ) ^ (2 * (k + 1)) = (4 ^ (k + 1)) ^ 2 by rw [← pow_mul, mul_comm],
    show (2 : ℚ) ^ (2 * (k + 1)) = 4 ^ (k + 1) by rw [pow_mul]; norm_num]
  linear_combination (-(-1 : ℚ) ^ k) * h
    - (4 ^ (k + 1) * (4 ^ (k + 1) - 1) * bernoulli (2 * (k + 1))) * hsq

/-- The tangent numbers are positive. -/
theorem tangentNumber_pos (k : ℕ) : 0 < tangentNumber (k + 1) := by
  have h := congrArg (Rat.cast : ℚ → ℝ) (tangentNumber_eq_bernoulli k)
  push_cast at h
  have hs := sign_bernoulli_two_mul (k := k + 1) (by omega)
  rw [show (-1 : ℝ) ^ (k + 1 + 1) = (-1) ^ k by rw [pow_succ, pow_succ]; ring] at hs
  have h4 : (0 : ℝ) < 4 ^ (k + 1) - 1 := by
    have : (1 : ℝ) < 4 ^ (k + 1) := one_lt_pow₀ (by norm_num) (by omega)
    linarith
  have hpos : (0 : ℝ) < (tangentNumber (k + 1) : ℝ) := by
    rw [h, show (-1 : ℝ) ^ k * 4 ^ (k + 1) * (4 ^ (k + 1) - 1) * (bernoulli (2 * (k + 1)) : ℝ)
        = 4 ^ (k + 1) * (4 ^ (k + 1) - 1) * ((-1) ^ k * (bernoulli (2 * (k + 1)) : ℝ)) by ring]
    positivity
  exact_mod_cast hpos

/-- `den B_{2(k+1)} ∣ 4^(k+1) (4^(k+1) − 1)`. -/
theorem bernoulli_den_dvd (k : ℕ) :
    ((bernoulli (2 * (k + 1))).den : ℤ) ∣ 4 ^ (k + 1) * (4 ^ (k + 1) - 1) := by
  have h := bernoulli_two_mul_eq_tangentNumber k
  have heq : bernoulli (2 * (k + 1))
      = Rat.divInt ((-1) ^ k * (2 * (k + 1)) * tangentNumber (k + 1) : ℤ)
        (4 ^ (k + 1) * (4 ^ (k + 1) - 1) : ℤ) := by
    rw [Rat.divInt_eq_div, h,
      show (4 : ℚ) ^ (2 * (k + 1)) = (4 ^ (k + 1)) ^ 2 by rw [← pow_mul, mul_comm],
      show (2 : ℚ) ^ (2 * (k + 1)) = 4 ^ (k + 1) by rw [pow_mul]; norm_num]
    push_cast
    ring
  rw [heq]
  exact Rat.den_dvd _ _

/-- An odd prime dividing the denominator of `B_{2(k+1)}` divides `2^(2(k+1)) − 1`. -/
theorem odd_prime_dvd_den_bernoulli {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (k : ℕ)
    (h : p ∣ (bernoulli (2 * (k + 1))).den) : p ∣ 2 ^ (2 * (k + 1)) - 1 := by
  have h1 : (p : ℤ) ∣ 4 ^ (k + 1) * (4 ^ (k + 1) - 1) :=
    (Int.natCast_dvd_natCast.mpr h).trans (bernoulli_den_dvd k)
  have h4 : 1 ≤ 4 ^ (k + 1) := Nat.one_le_pow _ _ (by norm_num)
  have h1' : p ∣ 4 ^ (k + 1) * (4 ^ (k + 1) - 1) := by
    have : ((4 ^ (k + 1) * (4 ^ (k + 1) - 1) : ℕ) : ℤ) = 4 ^ (k + 1) * (4 ^ (k + 1) - 1) := by
      push_cast [Nat.cast_sub h4]; ring
    rw [← this] at h1
    exact Int.natCast_dvd_natCast.mp h1
  rw [show 2 ^ (2 * (k + 1)) = 4 ^ (k + 1) by rw [pow_mul]; norm_num]
  rcases (Nat.Prime.dvd_mul hp).mp h1' with h5 | h5
  · exfalso
    have h6 : p ∣ 4 := hp.dvd_of_dvd_pow h5
    have h7 : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by norm_num; exact h6)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h7)
  · exact h5

end Series

end BZ

end Azurite
