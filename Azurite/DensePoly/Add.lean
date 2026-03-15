import Azurite.DensePoly.Basic
import Azurite.DensePoly.Parse

namespace Azurite.DensePoly

variable {R : Type _} [Semiring R] [DecidableEq R]

/-- Adds two DensePolynomials and normalizes the resulting array to drop any trailing zeros. -/
def add (p q : DensePoly R) : DensePoly R :=
  let maxLen := max p.coeffs.size q.coeffs.size
  let arr := Array.ofFn (fun (i : Fin maxLen) => p.coeff i.val + q.coeff i.val)
  normalize arr

instance : Add (DensePoly R) := ⟨add⟩

-- Testing the implementation using Integer polynomials
#guard (parseDensePoly (R := ℤ) "x^2+1").get! + (parseDensePoly (R := ℤ) "x+2").get! == (parseDensePoly (R := ℤ) "x^2+x+3").get!
#guard (parseDensePoly (R := ℤ) "x^2+x").get! + (parseDensePoly (R := ℤ) "-x^2+1").get! == (parseDensePoly (R := ℤ) "x+1").get!
#guard (parseDensePoly (R := ℤ) "x^2").get! + (parseDensePoly (R := ℤ) "-x^2").get! == (0 : DensePoly ℤ)
#guard (0 : DensePoly ℤ) + (parseDensePoly (R := ℤ) "x").get! == (parseDensePoly (R := ℤ) "x").get!

end Azurite.DensePoly
