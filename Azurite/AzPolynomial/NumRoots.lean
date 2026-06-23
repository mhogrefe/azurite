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

/-- Real-root count for `AzPolynomial AzInt` with `AzRat`-endpoints, computed by
    lifting to `AzPolynomial AzRat` via `mapAzIntToAzRat`. -/
def numRootsOnInt (P : AzPolynomial AzInt) (a b : ExtendedPoint AzRat) : ℤ :=
  numRootsOn (mapAzIntToAzRat P) a b

/-- Real-root count for `AzPolynomial AzInt` on the full line, computed via
    `mapAzIntToAzRat`. -/
def numRootsInt (P : AzPolynomial AzInt) : ℤ :=
  numRoots (mapAzIntToAzRat P)

/-! ## Worked examples -/

/-- `P = X² + 1` has no real roots. -/
private def P_no_roots : AzPolynomial AzRat := (parseAzPolynomial "x^2+1").get!

#guard numRoots P_no_roots = 0

/-- `P = X² − 1` has roots at `±1`. -/
private def P_two_roots : AzPolynomial AzRat := (parseAzPolynomial "x^2-1").get!

#guard numRoots P_two_roots = 2
#guard numRootsOn P_two_roots (.finite 0) .posInf = 1

-- Integer-coefficient examples.
#guard numRootsInt ((parseAzPolynomial "x^4-5*x^2+4").get! : AzPolynomial AzInt) = 4
#guard numRootsInt ((parseAzPolynomial "x^2+1").get! : AzPolynomial AzInt) = 0

end Azurite.AzPolynomial
