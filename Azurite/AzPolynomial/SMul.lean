import Azurite.AzPolynomial.Basic
import Azurite.AzPolynomial.Parse

namespace Azurite.AzPolynomial

variable {R S : Type _} [Semiring R] [SMulZeroClass S R] [DecidableEq R]

/-- Scalar multiplies a AzPolynomialnomial by mapping `r • c` over its coefficients. -/
def smul (r : S) (p : AzPolynomial R) : AzPolynomial R :=
  normalize (p.coeffs.map (r • ·))

instance : SMul S (AzPolynomial R) := ⟨smul⟩

-- Testing the implementation using Integer polynomials
#guard toChars ((2 : AzInt) • (parseAzPolynomial (R := AzInt) "x^2+1").get!) == "2*x^2+2"
#guard toChars ((-1 : AzInt) • (parseAzPolynomial (R := AzInt) "x^2+x").get!) == "-x^2-x"
#guard toChars ((0 : AzInt) • (parseAzPolynomial (R := AzInt) "x^2+1").get!) == "0"

end Azurite.AzPolynomial
