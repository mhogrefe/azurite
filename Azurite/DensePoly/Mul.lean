import Azurite.DensePoly.Basic
import Azurite.DensePoly.Parse

import Mathlib.Algebra.Polynomial.Coeff
open Polynomial

namespace Azurite.DensePoly

variable {R : Type _} [Semiring R] [DecidableEq R]

/-- Original O(n^2) multiplication using List.range.map.sum.
    Allocates an intermediate list per output coefficient.
    Kept for comparison with the optimized version. -/
def mulBasecaseList (p q : DensePoly R) : DensePoly R :=
  if p.coeffs.size == 0 || q.coeffs.size == 0 then 0
  else normalize <| Array.ofFn (fun (n : Fin (p.coeffs.size + q.coeffs.size - 1)) =>
    (List.range (n.val + 1)).map (fun i => p.coeff i * q.coeff (n.val - i)) |>.sum
  )

/-- Optimized O(n^2) multiplication using Finset.sum over range.
    Avoids allocating intermediate lists per output coefficient. -/
def mulBasecase (p q : DensePoly R) : DensePoly R :=
  if p.coeffs.size == 0 || q.coeffs.size == 0 then 0
  else normalize <| Array.ofFn (fun (n : Fin (p.coeffs.size + q.coeffs.size - 1)) =>
    ∑ i ∈ Finset.range (n.val + 1), p.coeff i * q.coeff (n.val - i)
  )

/-- O(n^2) multiplication using Fin.foldl — a direct accumulating fold with
    no intermediate data structures (no List, no Finset/Multiset wrapper). -/
def mulBasecaseFold (p q : DensePoly R) : DensePoly R :=
  if p.coeffs.size == 0 || q.coeffs.size == 0 then 0
  else normalize <| Array.ofFn (fun (n : Fin (p.coeffs.size + q.coeffs.size - 1)) =>
    Fin.foldl (n.val + 1) (fun acc i => acc + p.coeff i.val * q.coeff (n.val - i.val)) 0
  )

/-- Multiplies two DensePolynomials, delegating to the optimized O(n^2) basecase. -/
def mul (p q : DensePoly R) : DensePoly R :=
  mulBasecaseFold p q

instance : Mul (DensePoly R) := ⟨mul⟩

-- Testing the implementation using Integer polynomials
#guard (parseDensePoly (R := ℤ) "x+1").get! * (parseDensePoly (R := ℤ) "x+2").get! == (parseDensePoly (R := ℤ) "x^2+3*x+2").get!
#guard (parseDensePoly (R := ℤ) "2*x^2+x").get! * (parseDensePoly (R := ℤ) "x-1").get! == (parseDensePoly (R := ℤ) "2*x^3-x^2-x").get!
#guard (0 : DensePoly ℤ) * (parseDensePoly (R := ℤ) "x^2+1").get! == 0
#guard (parseDensePoly (R := ℤ) "3").get! * (parseDensePoly (R := ℤ) "4").get! == (parseDensePoly (R := ℤ) "12").get!

-- Verify old implementation still works
#guard mulBasecaseList (parseDensePoly (R := ℤ) "x+1").get! (parseDensePoly (R := ℤ) "x+2").get! == (parseDensePoly (R := ℤ) "x^2+3*x+2").get!

-- Verify fold implementation works
#guard mulBasecaseFold (parseDensePoly (R := ℤ) "x+1").get! (parseDensePoly (R := ℤ) "x+2").get! == (parseDensePoly (R := ℤ) "x^2+3*x+2").get!

end Azurite.DensePoly
