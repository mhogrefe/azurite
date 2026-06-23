import Azurite.AzPolynomialQ.Parse
import Azurite.AzPolynomialQ.Equiv.Basic
import Azurite.AzPolynomialQ.Equiv.ToString
import Azurite.AzPolynomial.ParseToString

/-!
# AzPolynomialQ ↔ AzPolynomial ℚ parse equivalence

This module proves that `parseAzPolynomialQ` agrees with
`AzPolynomial.parseAzPolynomial (R := AzRat)`, and that the
toString → parse roundtrip recovers the original `AzPolynomialQ`.
-/

namespace Azurite

open AzPolynomial

namespace AzPolynomialQ

/-- **Main roundtrip theorem**: converting an `AzPolynomialQ` to its string
    representation and parsing it back recovers the original polynomial. -/
theorem parseAzPolynomialQ_toChars (p : AzPolynomialQ) :
    parseAzPolynomialQ (toString p) = some p := by
  show (AzPolynomial.parseAzPolynomial (R := AzRat) (toChars p)).map ofAzRatPolynomial = some p
  rw [toChars_eq, parseAzPolynomial_toChars, Option.map_some, ofAzRatPolynomial_toAzRatPolynomial]

end AzPolynomialQ

end Azurite
