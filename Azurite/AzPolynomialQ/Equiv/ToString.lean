import Azurite.AzPolynomialQ.ToString
import Azurite.AzPolynomialQ.Equiv.Basic
import Azurite.AzPolynomial.ToString

/-!
# AzPolynomialQ ↔ AzPolynomial ℚ toString equivalence

`AzPolynomialQ.toChars` is defined as `AzPolynomial.toChars ∘ toAzPolynomial`,
so the equivalence is by definition.
-/

namespace Azurite

open _root_.Azurite.AzPolynomial

namespace AzPolynomialQ

/-- `AzPolynomialQ.toChars` agrees with `AzPolynomial.toChars` applied to
    `p.toAzRatPolynomial`. -/
theorem toChars_eq (p : AzPolynomialQ) :
    p.toChars = AzPolynomial.toChars p.toAzRatPolynomial := rfl

end AzPolynomialQ

end Azurite
