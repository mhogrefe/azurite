import Azurite.DensePoly.Add
import Azurite.DensePoly.Neg
import Azurite.DensePoly.Parse

namespace Azurite.DensePoly

variable {R : Type _} [Ring R] [DecidableEq R]

/-- Subtracts two DensePolynomials by adding the negation. -/
def sub (p q : DensePoly R) : DensePoly R :=
  p + -q

instance : Sub (DensePoly R) := ⟨sub⟩

-- Testing the implementation using Integer polynomials
#guard (parseDensePoly (R := ℤ) "x^2+1").get! - (parseDensePoly (R := ℤ) "x+2").get! == (parseDensePoly (R := ℤ) "x^2-x-1").get!
#guard (parseDensePoly (R := ℤ) "x^2+x").get! - (parseDensePoly (R := ℤ) "x^2+1").get! == (parseDensePoly (R := ℤ) "x-1").get!
#guard (parseDensePoly (R := ℤ) "x^2").get! - (parseDensePoly (R := ℤ) "x^2").get! == (0 : DensePoly ℤ)
#guard (0 : DensePoly ℤ) - (parseDensePoly (R := ℤ) "x").get! == (parseDensePoly (R := ℤ) "-x").get!

end Azurite.DensePoly
