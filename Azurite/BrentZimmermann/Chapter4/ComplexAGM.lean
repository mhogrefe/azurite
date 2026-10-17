/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BrentZimmermann.Chapter4.SecondAGMLog
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Brent–Zimmermann §4.8.5: The complex AGM

Some asymptotically fastest algorithms need complex arithmetic for a real result:
`arctan x = ℑ ln(1 + ix)` (and `arcsin`, `arccos` through it), and `cos x + i sin x = exp(ix)`
with the complex exponential by Newton from the complex logarithm.  The AGM theory extends to
complex `z ∉ (−∞, 0]` with the square root of positive real part.  Complex multiplication costs
three real ones (Karatsuba), complex squaring two; in the FFT domain (one multiplication = three
transforms) a squaring costs `2M(n)/3`, a complex product `2M(n)` (four forward, two backward
transforms) and a complex square `4M(n)/3` (two and two) — Table 4.1 (the remaining rows come from
§4.12).

What is formalized (all proven):

* `arctan_eq_im_log`: `arctan x = ℑ ln(1 + ix)` (the principal `Complex.log`, from
  `tan (arg z) = ℑz/ℜz` and `|arg z| < π/2` for `ℜz > 0`); the reductions
  `arcsin_eq_arctan'`, `arccos_eq_arctan` (`arcsin x = arctan(x/√(1 − x²))`,
  `arccos x = π/2 − arctan(x/√(1 − x²))` for `|x| < 1`).
* `exp_mul_I_eq`: `exp(ix) = cos x + i sin x` for real `x`.
* The Karatsuba identities `complex_mul_three_products`
  (`(a+ib)(c+id) = (ac − bd) + i((a+b)(c+d) − ac − bd)`: three real products) and
  `complex_sq_two_products` (`(a+ib)² = (a+b)(a−b) + i(2ab)`: two real products).
* The FFT transform-count model `fftCost` (a product = three transforms, cost `1`) with the four
  first rows of Table 4.1: `fftCost_real_sq = 2/3`, `fftCost_real_mul = 1`,
  `fftCost_complex_mul = 2`, `fftCost_complex_sq = 4/3`.

Not formalized: the convergence of the complex AGM and `ln z` for `z ∉ (−∞, 0]` (would need the
complex Landen/Gauss theory), the Newton evaluation of the complex exponential (Eqn. (4.11) over
`ℂ`), and the rows of Table 4.1 that rest on §4.12 (reciprocal, division, square root, AGM
iteration, `log` via AGM).
-/

namespace Azurite

namespace BZ

open Complex

/-! ### Inverse trigonometric functions through the complex logarithm -/

/-- `arctan x = ℑ ln(1 + ix)`. -/
theorem arctan_eq_im_log (x : ℝ) : Real.arctan x = (Complex.log (1 + x * I)).im := by
  rw [Complex.log_im]
  have hre : 0 < (1 + (x : ℂ) * I).re := by simp
  have harg : |arg (1 + (x : ℂ) * I)| < Real.pi / 2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  have htan : Real.tan (arg (1 + (x : ℂ) * I)) = x := by
    rw [tan_arg]
    simp
  conv_lhs => rw [← htan]
  exact Real.arctan_tan (abs_lt.mp harg).1 (abs_lt.mp harg).2

/-- `arcsin x = arctan(x/√(1 − x²))` for `|x| < 1`. -/
theorem arcsin_eq_arctan' {x : ℝ} (hx : |x| < 1) :
    Real.arcsin x = Real.arctan (x / Real.sqrt (1 - x ^ 2)) :=
  Real.arcsin_eq_arctan (abs_lt.mp hx)

/-- `arccos x = π/2 − arctan(x/√(1 − x²))` for `|x| < 1`. -/
theorem arccos_eq_arctan {x : ℝ} (hx : |x| < 1) :
    Real.arccos x = Real.pi / 2 - Real.arctan (x / Real.sqrt (1 - x ^ 2)) := by
  rw [Real.arccos_eq_pi_div_two_sub_arcsin, arcsin_eq_arctan' hx]

/-- Euler: `exp(ix) = cos x + i sin x` for real `x`. -/
theorem exp_mul_I_eq (x : ℝ) : Complex.exp (x * I) = Real.cos x + Real.sin x * I := by
  rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

/-! ### Karatsuba for complex products and squares -/

/-- `(a + ib)(c + id) = (ac − bd) + i((a + b)(c + d) − ac − bd)`: three real products. -/
theorem complex_mul_three_products (a b c d : ℝ) :
    ((a : ℂ) + b * I) * (c + d * I)
      = ((a * c - b * d : ℝ) : ℂ) + (((a + b) * (c + d) - a * c - b * d : ℝ) : ℂ) * I := by
  push_cast
  ring_nf
  rw [I_sq]
  ring

/-- `(a + ib)² = (a + b)(a − b) + i(2ab)`: two real products. -/
theorem complex_sq_two_products (a b : ℝ) :
    ((a : ℂ) + b * I) ^ 2 = (((a + b) * (a - b) : ℝ) : ℂ) + ((2 * a * b : ℝ) : ℂ) * I := by
  push_cast
  ring_nf
  rw [I_sq]
  ring

/-! ### The FFT-domain cost model (Table 4.1, first rows) -/

/-- Cost in units of `M(n)` of an operation using `f` forward and `b` backward transforms, in the
model where one multiplication is three transforms. -/
def fftCost (f b : ℕ) : ℚ := (f + b : ℚ) / 3

/-- A real squaring: one forward, one backward transform, `2M(n)/3`. -/
theorem fftCost_real_sq : fftCost 1 1 = 2 / 3 := by norm_num [fftCost]

/-- A real multiplication: two forward, one backward transform, `M(n)`. -/
theorem fftCost_real_mul : fftCost 2 1 = 1 := by norm_num [fftCost]

/-- A complex multiplication `(ac − bd) + i(ad + bc)`: four forward, two backward, `2M(n)`. -/
theorem fftCost_complex_mul : fftCost 4 2 = 2 := by norm_num [fftCost]

/-- A complex squaring `(a + b)(a − b) + i(2ab)`: two forward, two backward, `4M(n)/3`. -/
theorem fftCost_complex_sq : fftCost 2 2 = 4 / 3 := by norm_num [fftCost]

end BZ

end Azurite
