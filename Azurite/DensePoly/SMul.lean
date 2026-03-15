import Azurite.DensePoly.Basic
import Azurite.DensePoly.Parse

namespace Azurite.DensePoly

variable {R S : Type _} [Semiring R] [SMulZeroClass S R] [DecidableEq R]

/-- Scalar multiplies a DensePolynomial by mapping `r • c` over its coefficients. -/
def smul (r : S) (p : DensePoly R) : DensePoly R :=
  normalize (p.coeffs.map (r • ·))

instance : SMul S (DensePoly R) := ⟨smul⟩

-- Testing the implementation using Integer polynomials
#guard (2 : ℤ) • (parseDensePoly (R := ℤ) "x^2+1").get! == (parseDensePoly (R := ℤ) "2*x^2+2").get!
#guard (-1 : ℤ) • (parseDensePoly (R := ℤ) "x^2+x").get! == (parseDensePoly (R := ℤ) "-x^2-x").get!
#guard (0 : ℤ) • (parseDensePoly (R := ℤ) "x^2+1").get! == (0 : DensePoly ℤ)

end Azurite.DensePoly
