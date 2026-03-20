import Azurite.AzPolynomial.Basic
import Azurite.AzPolynomial.Parse

import Mathlib.Algebra.Polynomial.Coeff
open Polynomial

namespace Azurite.AzPolynomial

variable {R : Type _} [Semiring R] [DecidableEq R]

/-- Original O(n^2) multiplication using List.range.map.sum.
    Allocates an intermediate list per output coefficient.
    Kept for comparison with the optimized version. -/
def mulBasecaseList (p q : AzPolynomial R) : AzPolynomial R :=
  if p.coeffs.size == 0 || q.coeffs.size == 0 then 0
  else normalize <| Array.ofFn (fun (n : Fin (p.coeffs.size + q.coeffs.size - 1)) =>
    (List.range (n.val + 1)).map (fun i => p.coeff i * q.coeff (n.val - i)) |>.sum
  )

/-- Optimized O(n^2) multiplication using Finset.sum over range.
    Avoids allocating intermediate lists per output coefficient. -/
def mulBasecase (p q : AzPolynomial R) : AzPolynomial R :=
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
def mulBasecaseFold (p q : AzPolynomial R) : AzPolynomial R :=
  normalize (mulBasecaseCoeffs p.coeffs q.coeffs)

-- ── Multiplication config typeclass ─────────────────────────────────────────

/-- Configuration typeclass for `AzPolynomial` multiplication.
    Instances select the algorithm and (for Karatsuba) the threshold.

    Priority convention:
    - 100: basecase O(n²) for any `Semiring` (default)
    - 200: Karatsuba with default threshold for `CommRing`
    - 300: type-specific tuned Karatsuba thresholds -/
class AzPolynomialMulConfig (R : Type _) [Semiring R] [DecidableEq R] where
  /-- The multiplication implementation. -/
  dmul : AzPolynomial R → AzPolynomial R → AzPolynomial R

/-- Default: O(n²) basecase multiplication for any Semiring.
    Overridden by higher-priority Karatsuba instances when `Karatsuba.lean`
    is imported. -/
instance (priority := 100) : AzPolynomialMulConfig R where
  dmul := mulBasecaseFold

/-- Multiplies two AzPolynomialnomials using the best available algorithm
    for the coefficient type `R`, as determined by `AzPolynomialMulConfig`. -/
def mul [AzPolynomialMulConfig R] (p q : AzPolynomial R) : AzPolynomial R :=
  AzPolynomialMulConfig.dmul p q

instance [AzPolynomialMulConfig R] : Mul (AzPolynomial R) := ⟨mul⟩

-- Testing the implementation using Integer polynomials
#guard (parseAzPolynomial (R := ℤ) "x+1").get! * (parseAzPolynomial (R := ℤ) "x+2").get! == (parseAzPolynomial (R := ℤ) "x^2+3*x+2").get!
#guard (parseAzPolynomial (R := ℤ) "2*x^2+x").get! * (parseAzPolynomial (R := ℤ) "x-1").get! == (parseAzPolynomial (R := ℤ) "2*x^3-x^2-x").get!
#guard (0 : AzPolynomial ℤ) * (parseAzPolynomial (R := ℤ) "x^2+1").get! == 0
#guard (parseAzPolynomial (R := ℤ) "3").get! * (parseAzPolynomial (R := ℤ) "4").get! == (parseAzPolynomial (R := ℤ) "12").get!

-- Verify old implementation still works
#guard mulBasecaseList (parseAzPolynomial (R := ℤ) "x+1").get! (parseAzPolynomial (R := ℤ) "x+2").get! == (parseAzPolynomial (R := ℤ) "x^2+3*x+2").get!

-- Verify fold implementation works
#guard mulBasecaseFold (parseAzPolynomial (R := ℤ) "x+1").get! (parseAzPolynomial (R := ℤ) "x+2").get! == (parseAzPolynomial (R := ℤ) "x^2+3*x+2").get!

end Azurite.AzPolynomial
