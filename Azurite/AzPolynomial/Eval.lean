import Azurite.AzPolynomial.Basic
import Azurite.AzPolynomial.Parse

namespace Azurite.AzPolynomial

variable {R : Type _} [Semiring R]

/-- Evaluates `p` at a value `x` in the semiring `R` using Horner's method. -/
def eval (p : AzPolynomial R) (x : R) : R :=
  p.coeffs.foldr (init := 0) (fun a acc => a + acc * x)

#guard (parseAzPolynomial (R := ℤ) "3*x^4-x^2+1").get!.eval 2 == 45
#guard (parseAzPolynomial (R := ℤ) "3*x^4-x^2+1").get!.eval 0 == 1
#guard (parseAzPolynomial (R := ℤ) "3*x^4+x^3+8*x^2+2*x+1").get!.eval 10 == 31821

end Azurite.AzPolynomial
