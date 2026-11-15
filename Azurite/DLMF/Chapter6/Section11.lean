/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter6.Section2

/-!
# DLMF §6.11: relations to other functions

Formalizations of <https://dlmf.nist.gov/6.11>.

## Main results

* `incGammaUpper`: the incomplete gamma function `Γ(a, z) = ∫_z^∞ t^{a−1} e^{−t} dt` of
  DLMF 8.2.2 (principal value, horizontal ray from `z`).
* `dlmf_6_11_1`: `E₁(z) = Γ(0, z)`.

6.11.2 `E₁(z) = e^{−z} U(1, 1, z)` and 6.11.3 `g(z) + i f(z) = U(1, 1, −iz)` are deferred until
Chapter 13 defines Kummer's function `U` (13.2.6).
-/

open Complex Set MeasureTheory

namespace Azurite.DLMF

/-- **DLMF 8.2.2**: the principal value of the incomplete gamma function
`Γ(a, z) = ∫_z^∞ t^{a−1} e^{−t} dt`, along the horizontal ray `t = z + s`, `s ≥ 0`, with the
principal power `t^{a−1}`.  For `z` off the cut `(−∞, 0]` this path neither crosses the negative
real axis nor passes through the origin, as 8.2.2 requires; on the cut the value is a junk
value. -/
noncomputable def incGammaUpper (a z : ℂ) : ℂ :=
  ∫ s in Ioi (0 : ℝ), (z + s) ^ (a - 1) * cexp (-(z + s))

/-- **DLMF 6.11.1**: `E₁(z) = Γ(0, z)`.  Both sides are the principal values along the same
path, so the identity holds for every `z` (on the cut both sides carry the same junk value). -/
theorem dlmf_6_11_1 (z : ℂ) : expIntE₁ z = incGammaUpper 0 z := by
  rw [expIntE₁, incGammaUpper]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  rw [zero_sub, Complex.cpow_neg_one, div_eq_inv_mul]

end Azurite.DLMF
