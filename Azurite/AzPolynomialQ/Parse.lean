import Azurite.AzPolynomialQ.Basic
import Azurite.AzPolynomialQ.Equiv.Basic
import Azurite.AzPolynomial.Parse
import Azurite.AzMvPolynomial.ParsableCoeff.AzRat

/-!
# AzPolynomialQ parsing

This module provides `parseAzPolynomialQ`, which parses a polynomial string
into an `AzPolynomialQ` by reusing the existing `AzPolynomial AzRat` parser
and converting via `ofAzRatPolynomial`.

For the proof that parsing agrees with `AzPolynomial.parseAzPolynomial`,
see `Azurite.AzPolynomialQ.Equiv.Parse`.
-/

namespace Azurite

open AzPolynomial

namespace AzPolynomialQ

/-- Parse a string into an `AzPolynomialQ`.
    Delegates to the `AzPolynomial AzRat` parser and converts the result
    via `ofAzRatPolynomial`. -/
def parseAzPolynomialQ (s : String) : Option AzPolynomialQ :=
  (AzPolynomial.parseAzPolynomial (R := AzRat) s).map AzPolynomialQ.ofAzRatPolynomial

end AzPolynomialQ

end Azurite
