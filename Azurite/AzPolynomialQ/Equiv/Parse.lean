import Azurite.AzPolynomialQ.Parse
import Azurite.AzPolynomialQ.Equiv.Basic
import Azurite.AzPolynomialQ.Equiv.ToString
import Azurite.AzPolynomial.ParseToString

/-!
# AzPolynomialQ ↔ AzPolynomial ℚ parse equivalence

This module proves that `parseAzPolynomialQ` agrees with
`AzPolynomial.parseAzPolynomial (R := ℚ)`, and that the
toString → parse roundtrip recovers the original `AzPolynomialQ`.
-/

namespace Azurite

open AzPolynomial

namespace AzPolynomialQ

/-- Parsing to `AzPolynomialQ` and converting back to `AzPolynomial ℚ`
    is the same as parsing directly to `AzPolynomial ℚ`. -/
theorem parseAzPolynomialQ_eq (s : String) :
    (parseAzPolynomialQ s).map toAzPolynomial = AzPolynomial.parseAzPolynomial (R := ℚ) s := by
  simp only [parseAzPolynomialQ]
  cases h : AzPolynomial.parseAzPolynomial (R := ℚ) s with
  | none => simp
  | some p => simp [toAzPolynomial_ofAzPolynomial]

/-- **Main roundtrip theorem**: converting an `AzPolynomialQ` to its string
    representation and parsing it back recovers the original polynomial. -/
theorem parseAzPolynomialQ_toChars (p : AzPolynomialQ) :
    parseAzPolynomialQ (toString p) = some p := by
  show (AzPolynomial.parseAzPolynomial (R := ℚ) (toChars p)).map ofAzPolynomial = some p
  rw [toChars_eq, parseAzPolynomial_toChars, Option.map_some, ofAzPolynomial_toAzPolynomial]

end AzPolynomialQ

end Azurite
