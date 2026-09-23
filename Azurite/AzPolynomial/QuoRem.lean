/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzPolynomial.Basic
import Azurite.AzPolynomial.Add
import Azurite.AzPolynomial.Sub
import Azurite.AzPolynomial.Mul
import Azurite.AzPolynomial.Monomial
import Azurite.AzPolynomial.SMul
import Azurite.AzPolynomial.Parse

import Mathlib.Algebra.Field.Defs

/-!
# Euclidean Division (Quotient and Remainder) of Univariate Polynomials

This module implements **Algorithm 8.3** from Basu, Pollack, Roy,
*Algorithms in Real Algebraic Geometry* (2006), p. 285.

Given polynomials `P` and `Q` over a field `K` with `Q ≠ 0`, compute
the unique quotient `C` and remainder `R` such that `P = C * Q + R`
and `deg R < deg Q`.

## Algorithm

- **Initialization:** `C := 0`, `R := P`.
- **For** `j` from `p` down to `q` (where `p = deg P`, `q = deg Q`):
  - `C := C + (coeff_j R / b_q) * X^{j-q}`
  - `R := R - (coeff_j R / b_q) * X^{j-q} * Q`
- **Output:** `(C, R)`.
-/

namespace Azurite.AzPolynomial

variable {K : Type _} [Field K] [DecidableEq K]

/-- One step of the Euclidean division algorithm (BPR Algorithm 8.3).

    Given the current quotient `C` and remainder `R`, the degree index `j`,
    the divisor `Q`, and its leading coefficient `bq`, perform:
    - `t := coeff_j(R) / bq`
    - `C' := C + t * X^{j - q}`
    - `R' := R - t * X^{j - q} * Q` -/
def quoRemStep (q : ℕ) (bq : K) (Q : AzPolynomial K) (j : ℕ)
    (cr : AzPolynomial K × AzPolynomial K) : AzPolynomial K × AzPolynomial K :=
  let (C, R) := cr
  let t := R.coeff j / bq
  let m := monomial (j - q) t -- t * X^{j-q}
  (C + m, R - mulBasecaseFold m Q)

/-- **Algorithm 8.3** (BPR): Euclidean division of `P` by `Q`.

    Returns `(Quo(P, Q), Rem(P, Q))` such that `P = Quo * Q + Rem`
    and `deg Rem < deg Q`.

    Requires `Q ≠ 0` (i.e. `Q.coeffs` is nonempty and its leading
    coefficient is nonzero by the `AzPolynomial` invariant).

    If `deg P < deg Q`, the loop body does not execute and the result
    is `(0, P)`. -/
def quoRem (P Q : AzPolynomial K) : AzPolynomial K × AzPolynomial K :=
  if Q.coeffs.size = 0 then (0, P)  -- guard: Q = 0 → no division
  else if P.coeffs.size = 0 then (0, P)  -- P = 0
  else if P.coeffs.size < Q.coeffs.size then (0, P)  -- deg P < deg Q
  else
    let p := P.coeffs.size - 1 -- natDegree of P
    let q := Q.coeffs.size - 1 -- natDegree of Q
    let bq := Q.leadingCoeff    -- leading coefficient of Q (nonzero by invariant)
    let numSteps := P.coeffs.size - Q.coeffs.size + 1
    (List.range numSteps).foldl
      (fun cr k => quoRemStep q bq Q (p - k) cr)
      (0, P)

/-- The quotient of the Euclidean division of `P` by `Q`. -/
def quo (P Q : AzPolynomial K) : AzPolynomial K :=
  (quoRem P Q).1

/-- The remainder of the Euclidean division of `P` by `Q`. -/
def rem (P Q : AzPolynomial K) : AzPolynomial K :=
  (quoRem P Q).2

-- ── Tests ──────────────────────────────────────────────────────────────────

-- Basic: (x^2 + 2x + 1) / (x + 1) = (x + 1, 0)
#guard toChars (quo (parseAzPolynomial (R := AzRat) "x^2+2*x+1").get! (parseAzPolynomial (R := AzRat) "x+1").get!)
  == "x+1"
#guard toChars (rem (parseAzPolynomial (R := AzRat) "x^2+2*x+1").get! (parseAzPolynomial (R := AzRat) "x+1").get!)
  == "0"

-- With nonzero remainder: (x^2 + 1) / (x + 1) = (x - 1, 2)
#guard toChars (quo (parseAzPolynomial (R := AzRat) "x^2+1").get! (parseAzPolynomial (R := AzRat) "x+1").get!)
  == "x-1"
#guard toChars (rem (parseAzPolynomial (R := AzRat) "x^2+1").get! (parseAzPolynomial (R := AzRat) "x+1").get!)
  == "2"

-- Division by a constant: (3x^2 + 6x) / 3 = (x^2 + 2x, 0)
#guard toChars (quo (parseAzPolynomial (R := AzRat) "3*x^2+6*x").get! (parseAzPolynomial (R := AzRat) "3").get!)
  == "x^2+2*x"
#guard toChars (rem (parseAzPolynomial (R := AzRat) "3*x^2+6*x").get! (parseAzPolynomial (R := AzRat) "3").get!)
  == "0"

-- deg P < deg Q: (x + 1) / (x^2 + 1) = (0, x + 1)
#guard toChars (quo (parseAzPolynomial (R := AzRat) "x+1").get! (parseAzPolynomial (R := AzRat) "x^2+1").get!)
  == "0"
#guard toChars (rem (parseAzPolynomial (R := AzRat) "x+1").get! (parseAzPolynomial (R := AzRat) "x^2+1").get!)
  == "x+1"

-- P = 0: 0 / (x + 1) = (0, 0)
#guard toChars (quo (0 : AzPolynomial AzRat) (parseAzPolynomial (R := AzRat) "x+1").get!)
  == "0"

-- Non-monic divisor: (2x^2 + 3x + 1) / (2x + 1) = (x + 1, 0)
#guard toChars (quo (parseAzPolynomial (R := AzRat) "2*x^2+3*x+1").get! (parseAzPolynomial (R := AzRat) "2*x+1").get!)
  == "x+1"
#guard toChars (rem (parseAzPolynomial (R := AzRat) "2*x^2+3*x+1").get! (parseAzPolynomial (R := AzRat) "2*x+1").get!)
  == "0"

#guard toChars (quo (parseAzPolynomial (R := AzRat) "x^3+1").get! (parseAzPolynomial (R := AzRat) "2*x^2+3*x+1").get!) == "1/2*x-3/4"
#guard toChars (rem (parseAzPolynomial (R := AzRat) "x^3+1").get! (parseAzPolynomial (R := AzRat) "2*x^2+3*x+1").get!) == "7/4*x+7/4"

end Azurite.AzPolynomial
