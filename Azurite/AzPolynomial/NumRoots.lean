import Azurite.AzPolynomial.CauchyIndex

/-!
# Computable real-root count on `AzPolynomial`

Computable functions counting the (distinct) real roots of a polynomial,
derived from **BPR Theorem 2.50 (Sturm)**:

`Var(SRemS(P, P'); a, b) = #{distinct roots of P in (a, b)}`.

We expose:
* `numRootsOn P a b` for the open-interval count, with `a, b : ExtendedPoint K`.
* `numRoots P` for the full real line, equal to `numRootsOn P .negInf .posInf`.

Internally these reduce to `cauchyIndexOn P.derivative P` (BPR Theorem 2.58
gives `Var(SRemS(P, P'); a, b) = Ind(P'/P; a, b)`, and Sturm identifies
this Cauchy index with the root count).
-/

namespace Azurite.AzPolynomial

open Azurite.BPR (ExtendedPoint)

/-- **Computable real-root count on an open interval.** `numRootsOn P a b`
    computes `#{distinct real roots of P in (a, b)} : ℤ` via Sturm's
    theorem (BPR Theorem 2.50). -/
def numRootsOn {K : Type _} [Field K] [LinearOrder K] [DecidableEq K]
    [PolynomialDerivative K]
    (P : AzPolynomial K) (a b : ExtendedPoint K) : ℤ :=
  cauchyIndexOn P.derivative P a b

/-- **Computable real-root count on the full real line.**
    `numRoots P = numRootsOn P −∞ +∞`. -/
def numRoots {K : Type _} [Field K] [LinearOrder K] [DecidableEq K]
    [PolynomialDerivative K] (P : AzPolynomial K) : ℤ :=
  numRootsOn P .negInf .posInf

/-- Real-root count for `AzPolynomial ℤ` with `ℚ`-endpoints, computed by
    lifting to `AzPolynomial ℚ` via `mapIntToRat`. -/
def numRootsOnInt (P : AzPolynomial ℤ) (a b : ExtendedPoint ℚ) : ℤ :=
  numRootsOn (mapIntToRat P) a b

/-- Real-root count for `AzPolynomial ℤ` on the full line, computed via
    `mapIntToRat`. -/
def numRootsInt (P : AzPolynomial ℤ) : ℤ :=
  numRoots (mapIntToRat P)

/-! ## Worked examples -/

/-- BPR Example 2.52: `P = X⁴ − 5X² + 4 = (X−1)(X+1)(X−2)(X+2)` has
    four distinct real roots. -/
private def P_2_52' : AzPolynomial ℚ := (parseAzPolynomial "x^4-5*x^2+4").get!

#guard numRoots P_2_52' = 4
#guard numRootsOn P_2_52' (.finite 0) .posInf = 2
#guard numRootsOn P_2_52' .negInf (.finite 0) = 2
#guard numRootsOn P_2_52' (.finite (-3 : ℚ)) (.finite 3) = 4
#guard numRootsOn P_2_52' (.finite (3/2 : ℚ)) .posInf = 1

/-- `P = X² + 1` has no real roots. -/
private def P_no_roots : AzPolynomial ℚ := (parseAzPolynomial "x^2+1").get!

#guard numRoots P_no_roots = 0

/-- `P = X² − 1` has roots at `±1`. -/
private def P_two_roots : AzPolynomial ℚ := (parseAzPolynomial "x^2-1").get!

#guard numRoots P_two_roots = 2
#guard numRootsOn P_two_roots (.finite 0) .posInf = 1

-- Integer-coefficient examples.
#guard numRootsInt (parseAzPolynomial (R := ℤ) "x^4-5*x^2+4").get! = 4
#guard numRootsInt (parseAzPolynomial (R := ℤ) "x^2+1").get! = 0

end Azurite.AzPolynomial
