import Azurite.DensePoly.Basic
import Azurite.DensePoly.Parse

import Mathlib.Algebra.Polynomial.Coeff
open Polynomial

namespace Azurite.DensePoly

variable {R : Type _} [Semiring R] [DecidableEq R]

/-- Standard O(n^2) polynomial multiplication basecase mapped via antidiagonal coefficients -/
def mulBasecase (p q : DensePoly R) : DensePoly R :=
  if p.coeffs.size == 0 || q.coeffs.size == 0 then 0
  else normalize <| Array.ofFn (fun (n : Fin (p.coeffs.size + q.coeffs.size - 1)) =>
    (List.range (n.val + 1)).map (fun i => p.coeff i * q.coeff (n.val - i)) |>.sum
  )

/-- Multiplies two DensePolynomials, delegating to the O(n^2) basecase for now. -/
def mul (p q : DensePoly R) : DensePoly R :=
  mulBasecase p q

instance : Mul (DensePoly R) := ⟨mul⟩

-- Testing the implementation using Integer polynomials
#guard (parseDensePoly (R := ℤ) "x+1").get! * (parseDensePoly (R := ℤ) "x+2").get! == (parseDensePoly (R := ℤ) "x^2+3*x+2").get!
#guard (parseDensePoly (R := ℤ) "2*x^2+x").get! * (parseDensePoly (R := ℤ) "x-1").get! == (parseDensePoly (R := ℤ) "2*x^3-x^2-x").get!
#guard (0 : DensePoly ℤ) * (parseDensePoly (R := ℤ) "x^2+1").get! == 0
#guard (parseDensePoly (R := ℤ) "3").get! * (parseDensePoly (R := ℤ) "4").get! == (parseDensePoly (R := ℤ) "12").get!

end Azurite.DensePoly
