import Azurite.AzPolynomial.Basic
import Azurite.AzPolynomial.Parse

namespace Azurite.AzPolynomial

variable {R S : Type _} [Semiring R] [SMulZeroClass S R] [DecidableEq R]

/-- Scalar multiplies a AzPolynomialnomial by mapping `r • c` over its coefficients. -/
def smul (r : S) (p : AzPolynomial R) : AzPolynomial R :=
  normalize (p.coeffs.map (r • ·))

instance : SMul S (AzPolynomial R) := ⟨smul⟩

-- Testing the implementation using Integer polynomials
#guard (2 : ℤ) • (parseAzPolynomial (R := ℤ) "x^2+1").get! == (parseAzPolynomial (R := ℤ) "2*x^2+2").get!
#guard (-1 : ℤ) • (parseAzPolynomial (R := ℤ) "x^2+x").get! == (parseAzPolynomial (R := ℤ) "-x^2-x").get!
#guard (0 : ℤ) • (parseAzPolynomial (R := ℤ) "x^2+1").get! == (0 : AzPolynomial ℤ)

end Azurite.AzPolynomial
