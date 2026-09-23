/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzRationalFunction.Basic
import Azurite.AzPolynomial.ToString
import Azurite.AzPolynomial.SMul

/-!
# Printing an `AzRationalFunction`

The display form reconstitutes the integer fraction from the factored
representation: with `factor = ±a/b`, the displayed numerator is
`(±a) • num` and the displayed denominator is `b • den` (a reduced,
content-coprime integer fraction with positive-leading-coefficient
denominator). Format:

* denominator `1`: just the numerator string;
* otherwise `num/den`, with the numerator wrapped in parentheses exactly
  when it has more than one nonzero term, and the denominator wrapped
  unless it is a constant or a monic monomial — so `x/2`, `3/x`, `1/x^2`
  stay bare while `3/(2*x)` is parenthesized (never `3/2*x`, which would
  read as `(3/2)·x`).
-/

namespace Azurite.AzRationalFunction

open Azurite.AzPolynomial

/-- Number of nonzero terms (nonzero coefficients). -/
def numTerms (p : AzPolynomial AzInt) : ℕ :=
  p.coeffs.foldl (fun k c => if c == 0 then k else k + 1) 0

/-- The displayed numerator: `(±a) • num` for `factor = ±a/b`. -/
def displayNum (r : AzRationalFunction) : AzPolynomial AzInt :=
  (⟨r.factor.sign, r.factor.num, r.factor.zero_sign⟩ : AzInt) • r.num

/-- The displayed denominator: `b • den` for `factor = ±a/b`. -/
def displayDen (r : AzRationalFunction) : AzPolynomial AzInt :=
  (⟨true, r.factor.den, fun _ => rfl⟩ : AzInt) • r.den

/-- A component string, parenthesized when it has more than one term. -/
def wrapComponent (p : AzPolynomial AzInt) : String :=
  if numTerms p ≤ 1 then AzPolynomial.toChars p
  else "(" ++ AzPolynomial.toChars p ++ ")"

/-- The denominator string, parenthesized unless it is a constant or a
monic monomial (there `…/den` already reads unambiguously; a coefficient
would bind to the wrong side, e.g. `3/2*x` reads as `(3/2)·x`). The display
denominator has a positive leading coefficient, so no sign cases arise. -/
def wrapDenominator (p : AzPolynomial AzInt) : String :=
  if p.natDegree = 0 ∨ (numTerms p ≤ 1 ∧ p.leadingCoeff = 1) then
    AzPolynomial.toChars p
  else "(" ++ AzPolynomial.toChars p ++ ")"

/-- **String form** of a rational function: the reduced integer fraction
`num/den` (parenthesizing a multi-term numerator and any denominator other
than a constant or monic monomial), or just the numerator when the
denominator is `1`. -/
def toString (r : AzRationalFunction) : String :=
  if displayDen r == 1 then AzPolynomial.toChars (displayNum r)
  else wrapComponent (displayNum r) ++ "/" ++ wrapDenominator (displayDen r)

instance : ToString AzRationalFunction := ⟨toString⟩

end Azurite.AzRationalFunction
