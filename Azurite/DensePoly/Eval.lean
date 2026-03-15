import Azurite.DensePoly.Basic
import Azurite.DensePoly.Parse

namespace Azurite.DensePoly

variable {R : Type _} [Semiring R]

/-- Evaluates `p` at a value `x` in the semiring `R` using Horner's method. -/
def eval (p : DensePoly R) (x : R) : R :=
  p.coeffs.foldr (init := 0) (fun a acc => a + acc * x)

#guard (parseDensePoly (R := ℤ) "3*x^4-x^2+1").get!.eval 2 == 45
#guard (parseDensePoly (R := ℤ) "3*x^4-x^2+1").get!.eval 0 == 1
#guard (parseDensePoly (R := ℤ) "3*x^4+x^3+8*x^2+2*x+1").get!.eval 10 == 31821

end Azurite.DensePoly
