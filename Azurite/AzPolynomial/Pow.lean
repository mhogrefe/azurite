/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Algorithm.SlidingWindowPow
import Azurite.AzPolynomial.Mul
import Azurite.AzPolynomial.Parse

/-!
# Sliding-Window Exponentiation for AzPolynomial

Computable polynomial exponentiation using the generic `slidingWindowPow` algorithm.

The `^` operator on `AzPolynomial R` (from the `Semiring` instance in `Equiv/Algebra.lean`)
already uses `slidingWindowPow` internally, so `p.pow n = p ^ n`. This file provides the explicit
`pow` function for direct use and adds `#guard` tests.

## Main Definition

- `Azurite.AzPolynomial.pow p n`: computes `p ^ n` in O(log n) polynomial multiplications.
-/

namespace Azurite.AzPolynomial

variable {R : Type _} [Semiring R] [DecidableEq R] [AzPolynomialMulConfig R]

/-- Computable exponentiation for `AzPolynomial R` via sliding-window exponentiation.
    Uses the multiplication of the coefficient type (`AzPolynomialMulConfig`).
    Agrees with `p ^ n` (the `Semiring`'s `Pow` instance). -/
def pow (p : AzPolynomial R) (n : ℕ) : AzPolynomial R :=
  Azurite.slidingWindowPow p n

-- ═══════════════════════════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════════════════════════

-- (the tests are in `FastMul.lean`, where the multiplication of `AzInt` is available)

end Azurite.AzPolynomial
