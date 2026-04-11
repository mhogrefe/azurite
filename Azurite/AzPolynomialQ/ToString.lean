import Azurite.AzPolynomialQ.Basic
import Azurite.AzPolynomialQ.Equiv.Basic
import Azurite.AzPolynomial.ToString

/-!
# AzPolynomialQ toString

`AzPolynomialQ.toChars` is a thin wrapper that converts to `AzPolynomial ℚ`
and defers to `AzPolynomial.toChars`.
-/

namespace Azurite

open AzPolynomial

namespace AzPolynomialQ

/-- Format a `AzPolynomialQ` as a human-readable polynomial string via
    `AzPolynomial.toChars` applied to `p.toAzPolynomial`. -/
def toChars (p : AzPolynomialQ) : String :=
  AzPolynomial.toChars p.toAzPolynomial

instance : ToString AzPolynomialQ where
  toString := toChars

end AzPolynomialQ

end Azurite
