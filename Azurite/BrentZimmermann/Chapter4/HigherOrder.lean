/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BrentZimmermann.Chapter4.FormalPowerSeries
import Azurite.BrentZimmermann.Chapter4.FunctionalInverse
import Azurite.BrentZimmermann.Chapter4.InverseRoot
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Brent–Zimmermann §4.2.6: Higher-order Newton-like methods

A second-order Taylor approximation in place of the linearization gives, from
`0 = f(x_0) + e f'(x_0) + e²/2 f''(x_0) + O(e³)` with `e = ζ − x_0` (4.12), the cubic iteration

  `x_{j+1} = x_j − f(x_j)/f'(x_j) − f(x_j)² f''(x_j) / (2 f'(x_j)³)`,

which for the reciprocal `f(x) = y − 1/x` is

  `x_{j+1} = x_j + x_j (1 − x_j y) + x_j (1 − x_j y)²`                                   (4.13)

and for the exponential by functional inversion is

  `x_{j+1} = x_j + x_j (y − ln x_j) + x_j (y − ln x_j)² / 2`.                            (4.14)

Systematically: with `ε_j = 1 − x_j y`, `1/y = x_j / (1 − ε_j) = x_j (1 + ε_j + ε_j² + …)` and
truncating after `ε_j^(k−1)` gives the `k`-th order iteration

  `x_{j+1} = x_j (1 + ε_j + … + ε_j^(k−1))`                                              (4.15)

(`k = 2` Newton, `k = 3` (4.13)); with `ε_j = y − ln x_j`, `e^y / x_j = exp ε_j = ∑ ε_j^m / m!` and
truncating after `k` terms gives

  `x_{j+1} = x_j ∑_{m<k} ε_j^m / m!`                                                      (4.16)

(`k = 2` Newton (4.11), `k = 3` (4.14)).

* `cubicStep` — the generic cubic iteration; `cubicStep_inverseRootFun_one` (= (4.13)) and
  `cubicStep_log` (= (4.14)) identify the two instances, and `taylor_three` is (4.12).
* `recipOrderStep k` — (4.15); `recipOrderStep_two` (Newton), `recipOrderStep_three` ((4.13)),
  `ringRecipError_recipOrderStep` (`ε' = ε^k`: order `k` exactly), `ringRecipError_recipOrderSeq`
  (`ε_j = ε_0^(k^j)`), `inv_eq_mul_tsum_geometric` (`1/y = x ∑ ε^m` for `|ε| < 1`).
* `expOrderStep k` — (4.16); `expOrderStep_two` (= (4.11)), `expOrderStep_three` (= (4.14)),
  `exp_eq_mul_exp_sub_log` (`e^y = x exp(y − ln x)`), `exp_eq_mul_tsum`, and the order-`k`
  error bound `abs_expOrderStep_sub_exp_le`: for `|ε| ≤ 1`,
  `|x_{j+1} − e^y| ≤ x_j |ε|^k (k+1)/(k!·k)`.
-/

namespace Azurite

namespace BZ

open Finset Real

/-! ### The generic cubic iteration -/

/-- The cubic Newton-like step `x − f x / f' x − f x ² f'' x / (2 f' x ³)`, from the
second-order Taylor approximation (4.12). -/
noncomputable def cubicStep (f f' f'' : ℝ → ℝ) (x : ℝ) : ℝ :=
  x - f x / f' x - f x ^ 2 * f'' x / (2 * f' x ^ 3)

/-- For the reciprocal, `f(x) = y − 1/x`, the cubic step is (4.13). -/
theorem cubicStep_inverseRootFun_one (y : ℝ) {x : ℝ} (hx : x ≠ 0) :
    cubicStep (inverseRootFun 1 y) (inverseRootFun' 1) (inverseRootFun'' 1) x
      = x + x * (1 - x * y) + x * (1 - x * y) ^ 2 := by
  unfold cubicStep inverseRootFun inverseRootFun' inverseRootFun''
  push_cast
  field_simp
  ring

/-- For the exponential by functional inversion, `f(x) = y − ln x`, the cubic step is (4.14). -/
theorem cubicStep_log (y : ℝ) {x : ℝ} (hx : x ≠ 0) :
    cubicStep (fun x => y - log x) (fun x => -x⁻¹) (fun x => (x ^ 2)⁻¹) x
      = x + x * (y - log x) + x * (y - log x) ^ 2 / 2 := by
  unfold cubicStep
  field_simp
  ring

/-! ### Iterations of arbitrary order for the reciprocal, (4.15) -/

section Ring

variable {α : Type*} [CommRing α]

/-- The `k`-th order reciprocal step (4.15), `x (1 + ε + … + ε^(k−1))` with `ε = 1 − x y`. -/
def recipOrderStep (k : ℕ) (y x : α) : α := x * ∑ m ∈ range k, (1 - x * y) ^ m

/-- The iterates of (4.15) from `x₀`. -/
def recipOrderSeq (k : ℕ) (y x₀ : α) : ℕ → α
  | 0 => x₀
  | n + 1 => recipOrderStep k y (recipOrderSeq k y x₀ n)

/-- `k = 2` is Newton's iteration (4.5). -/
theorem recipOrderStep_two (y x : α) : recipOrderStep 2 y x = ringReciprocalStep y x := by
  simp [recipOrderStep, ringReciprocalStep, Finset.sum_range_succ]
  ring

/-- `k = 3` is the cubic iteration (4.13). -/
theorem recipOrderStep_three (y x : α) :
    recipOrderStep 3 y x = x + x * (1 - x * y) + x * (1 - x * y) ^ 2 := by
  simp [recipOrderStep, Finset.sum_range_succ]
  ring

/-- The `k`-th order step has order exactly `k`: `ε' = ε^k`. -/
theorem ringRecipError_recipOrderStep (k : ℕ) (y x : α) :
    ringRecipError y (recipOrderStep k y x) = ringRecipError y x ^ k := by
  unfold ringRecipError recipOrderStep
  have h := mul_neg_geom_sum (1 - x * y) k
  linear_combination -h

/-- `ε_j = ε_0^(k^j)`. -/
theorem ringRecipError_recipOrderSeq (k : ℕ) (y x₀ : α) (j : ℕ) :
    ringRecipError y (recipOrderSeq k y x₀ j) = ringRecipError y x₀ ^ (k ^ j) := by
  induction j with
  | zero => simp [recipOrderSeq]
  | succ j ih =>
    show ringRecipError y (recipOrderStep k y (recipOrderSeq k y x₀ j)) = _
    rw [ringRecipError_recipOrderStep, ih, ← pow_mul, pow_succ]

end Ring

/-- The identity behind (4.15): for `|ε| < 1`, `1/y = x ∑ ε^m` with `ε = 1 − x y`. -/
theorem inv_eq_mul_tsum_geometric {y x : ℝ} (hy : y ≠ 0) (hε : |1 - x * y| < 1) :
    y⁻¹ = x * ∑' m : ℕ, (1 - x * y) ^ m := by
  rw [tsum_geometric_of_abs_lt_one hε, sub_sub_cancel]
  have hxy : x * y ≠ 0 := by
    intro h; rw [h, sub_zero, abs_one] at hε; exact lt_irrefl _ hε
  have hx : x ≠ 0 := left_ne_zero_of_mul hxy
  field_simp

/-! ### Iterations of arbitrary order for the exponential, (4.16) -/

/-- The `k`-th order exponential step (4.16), `x ∑_{m<k} ε^m / m!` with `ε = y − ln x`. -/
noncomputable def expOrderStep (k : ℕ) (y x : ℝ) : ℝ :=
  x * ∑ m ∈ range k, (y - log x) ^ m / m.factorial

/-- `k = 2` is Newton's iteration (4.11). -/
theorem expOrderStep_two (y x : ℝ) : expOrderStep 2 y x = expStep y x := by
  simp [expOrderStep, expStep, Finset.sum_range_succ]
  ring

/-- `k = 3` is the cubic iteration (4.14). -/
theorem expOrderStep_three (y x : ℝ) :
    expOrderStep 3 y x = x + x * (y - log x) + x * (y - log x) ^ 2 / 2 := by
  simp [expOrderStep, Finset.sum_range_succ, Nat.factorial]
  ring

/-- `e^y / x = exp(y − ln x)` for `x > 0`. -/
theorem exp_eq_mul_exp_sub_log (y : ℝ) {x : ℝ} (hx : 0 < x) : exp y = x * exp (y - log x) := by
  rw [exp_sub, exp_log hx, mul_div_cancel₀ _ hx.ne']

/-- The identity behind (4.16): `e^y = x ∑ ε^m / m!` with `ε = y − ln x`. -/
theorem exp_eq_mul_tsum (y : ℝ) {x : ℝ} (hx : 0 < x) :
    exp y = x * ∑' m : ℕ, (y - log x) ^ m / m.factorial := by
  rw [exp_eq_mul_exp_sub_log y hx, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

/-- The error of the `k`-th order exponential step: for `x > 0`, `k > 0` and `|ε| ≤ 1`,
`|x_{j+1} − e^y| ≤ x_j |ε|^k (k + 1) / (k! · k)` — order `k`. -/
theorem abs_expOrderStep_sub_exp_le {k : ℕ} (hk : 0 < k) (y : ℝ) {x : ℝ} (hx : 0 < x)
    (hε : |y - log x| ≤ 1) :
    |expOrderStep k y x - exp y|
      ≤ x * (|y - log x| ^ k * ((k + 1 : ℕ) / (k.factorial * k : ℝ))) := by
  have h := Real.exp_bound hε hk
  rw [expOrderStep, exp_eq_mul_exp_sub_log y hx, ← mul_sub, abs_mul, abs_of_pos hx, abs_sub_comm]
  exact mul_le_mul_of_nonneg_left h hx.le

end BZ

end Azurite
