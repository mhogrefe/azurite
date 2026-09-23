/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzPolynomialQ.Basic
import Azurite.AzPolynomial.Eval

/-!
# AzPolynomialQ Evaluation

This module defines evaluation of `AzPolynomialQ` polynomials using BPR
Algorithm 8.8 (special evaluation) on the underlying integer numerator polynomial.
All intermediate computations are performed in `ℤ`, avoiding rational arithmetic
in the inner loop — only a single final division produces the `ℚ` result.

## Main definitions

- `AzPolynomialQ.eval` — evaluate `p : AzPolynomialQ` at `x ∈ ℚ`

## Equivalence proofs

For the bidirectional equivalence with Mathlib `Polynomial.eval`, see
`Azurite.AzPolynomialQ.Equiv.Eval`.
-/

namespace Azurite

/-- Evaluate `p : AzPolynomialQ` at `x ∈ ℚ` using BPR special evaluation
    on the integer numerator polynomial.

    For `p = ∑ (n_i / d) X^i` and `x = b / c` (with `b = x.num`, `c = x.den`),
    computes `evalSpecial(intPoly, b, c) / (d · c^natDeg)`, where `intPoly`
    is the `AzPolynomial ℤ` of numerators.

    This equals `c^natDeg · d · P(b/c) / (d · c^natDeg) = P(x)`.

    All intermediate arithmetic is in `ℤ`; only the final division is rational. -/
def AzPolynomialQ.eval (p : AzPolynomialQ) (x : ℚ) : ℚ :=
  let intP : AzPolynomial ℤ := ⟨p.numerators, p.last_ne_zero⟩
  (intP.evalSpecial x.num (x.den : ℤ) : ℚ) /
    ((p.denom : ℤ) * (x.den : ℤ) ^ p.natDegree : ℚ)

-- P = 3x²+2x+1, eval at 5/2 = 75/4 + 5 + 1 = 99/4
#guard AzPolynomialQ.eval ⟨#[1, 2, 3], 1, by omega, by simp, by simp [listIntGcd]⟩ (5/2) == 99/4

-- P = 1 + (1/2)x + (1/3)x² = numerators #[6,3,2]/denom 6, eval at 6 = 16
#guard AzPolynomialQ.eval ⟨#[6, 3, 2], 6, by omega, by simp, by simp [listIntGcd]⟩ 6 == 16

-- x²+1 at 3 = 10
#guard AzPolynomialQ.eval ⟨#[1, 0, 1], 1, by omega, by simp, by simp [listIntGcd]⟩ 3 == 10

-- Zero poly at anything = 0
#guard AzPolynomialQ.eval ⟨#[], 1, by omega, by simp, by simp [listIntGcd]⟩ 42 == 0

-- (1/2)x + 1 at 6 = 4
#guard AzPolynomialQ.eval ⟨#[2, 1], 2, by omega, by simp, by simp [listIntGcd]⟩ 6 == 4

end Azurite
