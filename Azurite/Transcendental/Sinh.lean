/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Transcendental.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Irrationality of `sinh q`, `cosh q` and `tanh q`

`sinh q`, `cosh q` and `tanh q` are irrational for every nonzero rational `q`
(`irrational_sinh_rat`, `irrational_cosh_rat`, `irrational_tanh_rat`): were `sinh q` or
`cosh q` a rational `r`, then `y = e^q` would be a root of `y² − 2 r y − 1`, resp.
`y² − 2 r y + 1`, against the transcendence of `e^q` (`transcendental_exp_rat`, from Hermite's
theorem); and a rational `tanh q = r` gives the rational `e^(2q) = (1 + r)/(1 − r)`.  This makes
the rounding loops of the `AzFloat` hyperbolic functions provably terminating.
-/

open Polynomial

namespace Azurite

/-- A real `y` with `y² + b y + c = 0` for rationals `b`, `c` is algebraic. -/
theorem isAlgebraic_of_quadratic {y : ℝ} (b c : ℚ) (h : y ^ 2 + b * y + c = 0) :
    IsAlgebraic ℚ y := by
  refine ⟨X ^ 2 + C b * X + C c, ?_, ?_⟩
  · intro h0
    have := congrArg (fun P : ℚ[X] => P.coeff 2) h0
    simp at this
  · simpa using h

/-- `sinh q` is irrational for every nonzero rational `q`. -/
theorem irrational_sinh_rat {q : ℚ} (hq : q ≠ 0) : Irrational (Real.sinh q) := by
  rintro ⟨r, hr⟩
  apply transcendental_exp_rat hq
  have hpos := Real.exp_pos (q : ℝ)
  have hs := Real.sinh_eq (q : ℝ)
  rw [← hr, Real.exp_neg] at hs
  refine isAlgebraic_of_quadratic (-(2 * r)) (-1) ?_
  push_cast
  field_simp at hs
  linarith

/-- `cosh q` is irrational for every nonzero rational `q`. -/
theorem irrational_cosh_rat {q : ℚ} (hq : q ≠ 0) : Irrational (Real.cosh q) := by
  rintro ⟨r, hr⟩
  apply transcendental_exp_rat hq
  have hpos := Real.exp_pos (q : ℝ)
  have hs := Real.cosh_eq (q : ℝ)
  rw [← hr, Real.exp_neg] at hs
  refine isAlgebraic_of_quadratic (-(2 * r)) 1 ?_
  push_cast
  field_simp at hs
  linarith

/-- `e^(2x) = (1 + tanh x)/(1 − tanh x)`. -/
theorem exp_two_mul_eq_tanh (x : ℝ) :
    Real.exp (2 * x) = (1 + Real.tanh x) / (1 - Real.tanh x) := by
  have hpos := Real.exp_pos x
  have h1 := Real.tanh_lt_one x
  rw [eq_div_iff (by linarith), Real.tanh_eq, Real.exp_neg, two_mul, Real.exp_add]
  field_simp
  ring

/-- `tanh q` is irrational for every nonzero rational `q`. -/
theorem irrational_tanh_rat {q : ℚ} (hq : q ≠ 0) : Irrational (Real.tanh q) := by
  rintro ⟨r, hr⟩
  have h2 : (2 * q : ℚ) ≠ 0 := mul_ne_zero two_ne_zero hq
  apply irrational_exp_rat h2
  refine ⟨(1 + r) / (1 - r), ?_⟩
  push_cast
  rw [exp_two_mul_eq_tanh, hr]

end Azurite
