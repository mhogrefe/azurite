/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite

/-!
# Basic usage of `AzPolynomial`

Constructing, printing, parsing and casting univariate polynomials over the computable
coefficient types `AzInt`, `AzRat`, `AzNat` and `AzZMod m`.  Every statement here is a `#guard`,
checked when the file is built.
-/

open Azurite Azurite.AzPolynomial

/-! ## Construction and printing

`AzPolynomial.normalize` builds a polynomial from its coefficient array (lowest degree first),
stripping trailing zeros so that the representation is canonical. -/

-- 1 + 2x + 3x²
def p1a : AzPolynomial AzInt := normalize #[1, 2, 3]
def p1b : AzPolynomial AzInt := normalize #[10, 11, 12]

#guard toString p1a == "3*x^2+2*x+1"
#guard toString (0 : AzPolynomial AzInt) == "0"
#guard toString (1 : AzPolynomial AzInt) == "1"
#guard p1a != p1b

-- Coefficients in `ℤ/5`: 6, 7, 8 reduce to 1, 2, 3.
def p2 : AzPolynomial (AzZMod (AzNat.ofNat 5)) := normalize #[6, 7, 8]

#guard toString p2 == "3*x^2+2*x+1"
#guard toString (-p2) == "2*x^2+3*x+4"

-- Rational coefficients.
def p3 : AzPolynomial AzRat := normalize #[1/2, 3/4, 5/8]

#guard toString p3 == "5/8*x^2+3/4*x+1/2"

/-! ## Degrees, constants, monomials -/

#guard (0 : AzPolynomial AzInt).degree == none
#guard (0 : AzPolynomial AzInt).natDegree == 0
#guard p1a.leadingCoeff = 3
#guard !p1a.Monic
#guard toString (C (0 : AzInt)) == "0"
#guard toString (C (5 : AzInt)) == "5"
#guard toString (X : AzPolynomial AzInt) == "x"
#guard toString (monomial 10 (5 : AzInt)) == "5*x^10"
#guard toString (p1a.erase 1) == "3*x^2+1"
#guard toString (p1a.erase 2) == "2*x+1"
#guard toString ((C (5 : AzInt)).erase 0) == "0"

/-! ## Coefficient-type casts (`AzPolynomial.Cast`) -/

-- `AzNat` to `AzInt`.
def pN : AzPolynomial AzNat := normalize #[1, 2, 3]
#guard toString (mapAzNatToAzInt pN) == "3*x^2+2*x+1"

-- `AzInt` to `AzRat`.
def pZ : AzPolynomial AzInt := normalize #[1, -2, 3]
#guard toString (mapAzIntToAzRat pZ) == "3*x^2-2*x+1"

-- `AzZMod 5` to `AzNat` (representatives in `[0, 5)`).
def pZMod5 : AzPolynomial (AzZMod (AzNat.ofNat 5)) := normalize #[1, 2, 3, 4]
#guard toString (mapAzZModToAzNat pZMod5) == "4*x^3+3*x^2+2*x+1"

-- `AzNat` to `AzZMod 5`: the leading coefficient 5 becomes 0 and is stripped.
def pNLarge : AzPolynomial AzNat := normalize #[1, 2, 3, 5]
#guard (mapAzNatToAzZMod (m := AzNat.ofNat 5) pNLarge).coeffs == #[1, 2, 3]

-- `AzInt` to `AzZMod 5`: `-2 ↦ 3`, and the trailing `10 ↦ 0` is stripped.
def pZLarge : AzPolynomial AzInt := normalize #[1, -2, 3, 10]
#guard (mapAzIntToAzZMod (m := AzNat.ofNat 5) pZLarge).coeffs == #[1, 3, 3]

/-! ## Parsing -/

#guard (parseAzPolynomial (R := AzInt) "3*x^4-x^2+1").map (·.coeffs) == some #[1, 0, -1, 0, 3]
#guard (parseAzPolynomial (R := AzInt) "-x^2+1").map (·.coeffs) == some #[1, 0, -1]
#guard (parseAzPolynomial (R := AzRat) "-2/3*x^2-1/2").map (·.coeffs) == some #[-1/2, 0, -2/3]
