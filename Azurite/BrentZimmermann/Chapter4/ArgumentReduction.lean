/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Brent–Zimmermann §4.3: Argument reduction

To evaluate `f` at `x`: *reduce* `x` to `x'`, *evaluate* `f` (or another function `g`) at `x'`,
and *reconstruct* `f x` from the result by a functional identity.  The identities are the
addition formulae (4.17)

  `exp (x + y) = exp x · exp y`,  `log (x y) = log x + log y`,
  `sin (x + y) = sin x cos y + cos x sin y`,  `tan (x + y) = (tan x + tan y) / (1 − tan x tan y)`,

their doubling special cases such as `exp (2x) = (exp x)²` (4.18), and occasionally tripling
formulae such as `sin (3x) = 3 sin x − 4 sin³ x`, which involves one function only (the doubling
`sin (2x) = 2 sin x cos x` involves two).  Reductions are *additive*, `x' = x − k c` (periodic
functions, `c = 2π` for `sin`, `cos`), or *multiplicative*, `x' = x / c^k` (`c = 2` for `exp`
with (4.18)); the same function may admit both.  Sometimes the identity is used to *increase* the
argument, as `x Γ(x) = Γ(x + 1)` for the Gamma function (§4.5).  No reduction is known for the
error function — an observation, not a theorem.

* `ArgumentReduction f` — the scheme as a structure: `reduce`, the evaluated function `g`,
  `reconstruct`, and the correctness `f x = reconstruct x (g (reduce x))`.
* `exp_add'`, `log_mul'`, `sin_add'`, `tan_add'` — (4.17); `exp_two_mul'` (4.18),
  `sin_two_mul'`, `sin_three_mul'`, `sin_add_pi_div_two'` (`sin (x + π/2) = cos x`).
* `exp_eq_pow_two_pow` — the multiplicative reduction `exp x = (exp (x / 2^k))^(2^k)`;
  `sin_sub_int_mul_two_pi`, `cos_sub_int_mul_two_pi` — the additive one.
* `expHalving k`, `sinPeriodic k`, `sinTripling`, `sinToCos` — the scheme instantiated.
* `Gamma_add_nat` — `Γ(x + n) = Γ(x) ∏_{i<n} (x + i)` for `x > 0`, the repeated increase of
  the argument.
-/

namespace Azurite

namespace BZ

open Real

/-- The three-step scheme: `f x` is recovered from `g` evaluated at the reduced argument. -/
structure ArgumentReduction (f : ℝ → ℝ) where
  /-- Argument reduction `x ↦ x'`. -/
  reduce : ℝ → ℝ
  /-- The function evaluated at the reduced argument (often `f` itself). -/
  g : ℝ → ℝ
  /-- Reconstruction of `f x` from `x` and `g x'`. -/
  reconstruct : ℝ → ℝ → ℝ
  /-- The functional identity that makes the scheme correct. -/
  spec : ∀ x, f x = reconstruct x (g (reduce x))

/-! ### The addition formulae (4.17) -/

theorem exp_add' (x y : ℝ) : exp (x + y) = exp x * exp y := exp_add x y

theorem log_mul' {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) : log (x * y) = log x + log y :=
  log_mul hx hy

theorem sin_add' (x y : ℝ) : sin (x + y) = sin x * cos y + cos x * sin y := sin_add x y

/-- The addition formula for the tangent, where both tangents and the quotient are defined. -/
theorem tan_add' {x y : ℝ} (hx : cos x ≠ 0) (hy : cos y ≠ 0) (hxy : 1 - tan x * tan y ≠ 0) :
    tan (x + y) = (tan x + tan y) / (1 - tan x * tan y) := by
  have hc : cos (x + y) ≠ 0 := by
    rw [cos_add]
    intro h
    apply hxy
    rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos]
    field_simp
    linear_combination h
  rw [tan_eq_sin_div_cos, sin_add, cos_add, tan_eq_sin_div_cos, tan_eq_sin_div_cos]
  rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos] at hxy
  field_simp

/-! ### Doubling and tripling formulae -/

/-- (4.18). -/
theorem exp_two_mul' (x : ℝ) : exp (2 * x) = exp x ^ 2 := by
  rw [two_mul, exp_add, sq]

theorem sin_two_mul' (x : ℝ) : sin (2 * x) = 2 * sin x * cos x := sin_two_mul x

theorem sin_three_mul' (x : ℝ) : sin (3 * x) = 3 * sin x - 4 * sin x ^ 3 := sin_three_mul x

/-- Evaluating a different function: `sin (x + π/2) = cos x`. -/
theorem sin_add_pi_div_two' (x : ℝ) : sin (x + π / 2) = cos x := sin_add_pi_div_two x

/-! ### Multiplicative and additive reductions -/

/-- Multiplicative reduction by `2^k` for the exponential: `exp x = (exp (x / 2^k))^(2^k)`. -/
theorem exp_eq_pow_two_pow (x : ℝ) (k : ℕ) : exp x = exp (x / 2 ^ k) ^ (2 ^ k) := by
  rw [← exp_nat_mul]
  congr 1
  push_cast
  field_simp

/-- Additive reduction by the period: `sin x = sin (x − k · 2π)`. -/
theorem sin_sub_int_mul_two_pi (x : ℝ) (k : ℤ) : sin x = sin (x - k * (2 * π)) := by
  conv_lhs => rw [show x = (x - k * (2 * π)) + k * (2 * π) by ring, sin_add_int_mul_two_pi]

theorem cos_sub_int_mul_two_pi (x : ℝ) (k : ℤ) : cos x = cos (x - k * (2 * π)) := by
  conv_lhs => rw [show x = (x - k * (2 * π)) + k * (2 * π) by ring, cos_add_int_mul_two_pi]

/-- Multiplicative reduction of `exp` by `2^k`, reconstructed by `k` squarings. -/
noncomputable def expHalving (k : ℕ) : ArgumentReduction exp where
  reduce x := x / 2 ^ k
  g := exp
  reconstruct _ t := t ^ (2 ^ k)
  spec x := exp_eq_pow_two_pow x k

/-- Additive reduction of `sin` by `k` periods, trivial reconstruction. -/
noncomputable def sinPeriodic (k : ℤ) : ArgumentReduction sin where
  reduce x := x - k * (2 * π)
  g := sin
  reconstruct _ t := t
  spec x := sin_sub_int_mul_two_pi x k

/-- Multiplicative reduction of `sin` by `3`, reconstructed by the tripling formula, which only
involves `sin`. -/
noncomputable def sinTripling : ArgumentReduction sin where
  reduce x := x / 3
  g := sin
  reconstruct _ t := 3 * t - 4 * t ^ 3
  spec x := by
    have h := sin_three_mul (x / 3)
    rw [show 3 * (x / 3) = x by ring] at h
    exact h

/-- Evaluating `cos` in place of `sin` after shifting by `π/2`. -/
noncomputable def sinToCos : ArgumentReduction sin where
  reduce x := x - π / 2
  g := cos
  reconstruct _ t := t
  spec x := by
    have h := sin_add_pi_div_two (x - π / 2)
    rw [sub_add_cancel] at h
    exact h

/-! ### Increasing the argument: the Gamma function -/

/-- Repeated use of `x Γ(x) = Γ(x + 1)`: for `x > 0`, `Γ(x + n) = Γ(x) ∏_{i<n} (x + i)`. -/
theorem Gamma_add_nat {x : ℝ} (hx : 0 < x) (n : ℕ) :
    Gamma (x + n) = Gamma x * ∏ i ∈ Finset.range n, (x + i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hpos : x + n ≠ 0 := by positivity
    rw [Finset.prod_range_succ, show x + ((n + 1 : ℕ) : ℝ) = (x + n) + 1 by push_cast; ring,
      Gamma_add_one hpos, ih]
    ring

end BZ

end Azurite
