/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzPolynomial.Comp
import Azurite.AzPolynomial.Parse

/-!
# Polynomial Translation (BPR Algorithm 8.9)

Computes `P(X - c)` for a univariate polynomial `P ∈ A[X]` and element `c ∈ A`,
by composing `P` with the linear polynomial `X - c`.

The linear polynomial `X - c` is constructed directly from the coefficient array
`#[-c, 1]` (constant term `-c`, linear coefficient `1`), avoiding any use of
polynomial subtraction or the `C` constructor at the `AzPolynomial` level.

## Main definitions

- `AzPolynomial.xSubC c` — the polynomial `X - c` as an `AzPolynomial`
- `AzPolynomial.translate p c` — computes `P(X - c)`

## BPR Reference

Algorithm 8.9 [Translation]. Given `P = aₚXᵖ + ⋯ + a₀ ∈ A[X]` and `c ∈ A`,
compute `P(X - c)`.

**Azurite implementation:** Uses `comp` (Algorithm 8.7's Horner composition).
-/

namespace Azurite.AzPolynomial

variable {R : Type _} [CommRing R] [DecidableEq R]

/-- The polynomial `X - c`, constructed directly from coefficients `#[-c, 1]`.
    In the zero ring (`1 = 0`), this reduces to `0`. -/
def xSubC (c : R) : AzPolynomial R :=
  if h : (1 : R) = 0 then 0
  else ⟨#[-c, 1], by simp [h]⟩

/-- **BPR Algorithm 8.9 (Translation).** Computes `P(X - c)` by composing `P`
    with the linear polynomial `X - c`.

    The roots of the result are the roots of `P`, each shifted by `+c`. -/
def translate [AzPolynomialMulConfig R] (p : AzPolynomial R) (c : R) : AzPolynomial R :=
  p.comp (xSubC c)

-- ═══════════════════════════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════════════════════════

section Tests

-- (x² + 1) translated by 1: (x-1)² + 1 = x² - 2x + 2
#guard toChars ((parseAzPolynomial (R := AzInt) "x^2+1").get!.translate 1)
    == "x^2-2*x+2"

-- x³ translated by -1: (x+1)³ = x³ + 3x² + 3x + 1
#guard toChars ((parseAzPolynomial (R := AzInt) "x^3").get!.translate (-1))
    == "x^3+3*x^2+3*x+1"

-- Constant translated by anything: unchanged
#guard toChars ((parseAzPolynomial (R := AzInt) "5").get!.translate 42)
    == "5"

-- Zero translated: zero
#guard toChars ((0 : AzPolynomial AzInt).translate 7) == "0"

-- 2x + 3 translated by 5: 2(x-5) + 3 = 2x - 7
#guard toChars ((parseAzPolynomial (R := AzInt) "2*x+3").get!.translate 5)
    == "2*x-7"

end Tests

end Azurite.AzPolynomial
