import Azurite.AzPolynomialQ.Basic
import Azurite.AzPolynomialQ.Equiv.Basic
import Azurite.AzPolynomial.Parse

/-!
# AzPolynomialQ parsing

This module provides `parseAzPolynomialQ`, which parses a polynomial string
into an `AzPolynomialQ` by reusing the existing `AzPolynomial ℚ` parser
and converting via `ofAzPolynomial`.

For the proof that parsing agrees with `AzPolynomial.parseAzPolynomial`,
see `Azurite.AzPolynomialQ.Equiv.Parse`.
-/

namespace Azurite

open AzPolynomial

namespace AzPolynomialQ

/-- Parse a string into an `AzPolynomialQ`.
    Delegates to the `AzPolynomial ℚ` parser and converts the result
    via `ofAzPolynomial`. -/
def parseAzPolynomialQ (s : String) : Option AzPolynomialQ :=
  (AzPolynomial.parseAzPolynomial (R := ℚ) s).map AzPolynomialQ.ofAzPolynomial

end AzPolynomialQ

end Azurite
