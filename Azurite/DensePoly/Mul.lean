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

/-- O(n^2) basecase convolution on raw coefficient arrays using Fin.foldl.
    Produces an un-normalized array of product coefficients.
    Shared by `mulBasecaseFold` and `mulKaratsuba`. -/
def mulBasecaseCoeffs (a b : Array R) : Array R :=
  if a.size == 0 || b.size == 0 then #[]
  else Array.ofFn (fun (n : Fin (a.size + b.size - 1)) =>
    Fin.foldl (n.val + 1) (fun acc i =>
      acc + ((a[i.val]?).getD 0) * ((b[n.val - i.val]?).getD 0)) 0)

/-- O(n^2) multiplication using Fin.foldl — a direct accumulating fold with
    no intermediate data structures (no List, no Finset/Multiset wrapper). -/
def mulBasecaseFold (p q : DensePoly R) : DensePoly R :=
  normalize (mulBasecaseCoeffs p.coeffs q.coeffs)

-- ── Multiplication config typeclass ─────────────────────────────────────────

/-- Configuration typeclass for `DensePoly` multiplication.
    Instances select the algorithm and (for Karatsuba) the threshold.

    Priority convention:
    - 100: basecase O(n²) for any `Semiring` (default)
    - 200: Karatsuba with default threshold for `CommRing`
    - 300: type-specific tuned Karatsuba thresholds -/
class DensePolyMulConfig (R : Type _) [Semiring R] [DecidableEq R] where
  /-- The multiplication implementation. -/
  dmul : DensePoly R → DensePoly R → DensePoly R

/-- Default: O(n²) basecase multiplication for any Semiring.
    Overridden by higher-priority Karatsuba instances when `Karatsuba.lean`
    is imported. -/
instance (priority := 100) : DensePolyMulConfig R where
  dmul := mulBasecaseFold

/-- Multiplies two DensePolynomials using the best available algorithm
    for the coefficient type `R`, as determined by `DensePolyMulConfig`. -/
def mul [DensePolyMulConfig R] (p q : DensePoly R) : DensePoly R :=
  DensePolyMulConfig.dmul p q

instance [DensePolyMulConfig R] : Mul (DensePoly R) := ⟨mul⟩

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
