import Azurite.AzPolynomial.SRemS
import Azurite.AzPolynomial.Eval
import Azurite.AzPolynomial.Cast
import Azurite.AzPolynomial.Derivative
import Azurite.AzPolynomial.Mul
import Azurite.BasuPollackRoy.Chapter2.Section2_2

/-!
# Computable Cauchy Index and Tarski Query on `AzPolynomial`

Computable implementations of `Ind(Q/P; a, b)` and `TaQ(Q, P; a, b)`
derived from **BPR Theorems 2.58 and 2.61**:

* `Var(SRemS(P, Q); a, b) = Ind(Q/P; a, b)`,
* `Var(SRemS(P, P'·Q); a, b) = TaQ(Q, P; a, b)`.

Endpoints come from the existing `Azurite.BPR.ExtendedPoint K` (an
inductive type, fully computable). Sign-variation counting reuses the
existing `Azurite.BPR.Var` (also computable).

Allowed coefficient types: any computable ordered field. For `ℤ`
coefficients the convenience function `cauchyIndexOnInt` lifts to `ℚ`
through `mapIntToRat`.
-/

namespace Azurite.AzPolynomial

open Azurite.BPR (ExtendedPoint)

/-- Evaluation of `P : AzPolynomial K` at an extended point.

    * `finite a`: ordinary evaluation `P(a)`.
    * `posInf`: leading coefficient (sign of `P(x)` for large `x`).
    * `negInf`: `(-1)^natDegree · leadingCoeff`. Encoded via parity of
      `coeffs.size`: when `coeffs.size` is odd, `natDegree = size - 1`
      is even, so `(-1)^natDegree = 1`. -/
def evalPolyExt {K : Type _} [Ring K] (P : AzPolynomial K)
    (x : ExtendedPoint K) : K :=
  match x with
  | .finite a => P.eval a
  | .posInf => P.leadingCoeff
  | .negInf =>
      if P.coeffs.size % 2 = 1 then P.leadingCoeff else -P.leadingCoeff

/-- Sign-variation count of a list of polynomials at an extended point.
    Reuses the computable `Azurite.BPR.Var`. -/
def varAt {K : Type _} [Ring K] [LinearOrder K] [DecidableEq K]
    (L : List (AzPolynomial K)) (x : ExtendedPoint K) : ℕ :=
  Azurite.BPR.Var (L.map (fun P => evalPolyExt P x))

/-- **Computable Cauchy index.** `cauchyIndexOn Q P a b` computes
    `Ind(Q/P; a, b) : ℤ` via `Var(SRemS(P, Q); a, b)` (BPR Theorem 2.58).

    The truncation length `Q.coeffs.size + 2` captures every nonzero
    entry of the SRemS sequence: degrees strictly decrease starting from
    `Q`, hitting zero by index `Q.natDegree + 2 ≤ Q.coeffs.size + 2`. -/
def cauchyIndexOn {K : Type _} [Field K] [LinearOrder K] [DecidableEq K]
    (Q P : AzPolynomial K) (a b : ExtendedPoint K) : ℤ :=
  let L := sRemSList P Q (Q.coeffs.size + 2)
  (varAt L a : ℤ) - (varAt L b : ℤ)

/-- Cauchy index for `AzPolynomial ℤ` with `ℚ`-endpoints, computed by
    lifting to `AzPolynomial ℚ` via `mapIntToRat`. -/
def cauchyIndexOnInt (Q P : AzPolynomial ℤ) (a b : ExtendedPoint ℚ) : ℤ :=
  cauchyIndexOn (mapIntToRat Q) (mapIntToRat P) a b

/-! ## Worked examples -/

/-- BPR Example 2.52: `P = X⁴ − 5X² + 4 = (X−1)(X+1)(X−2)(X+2)` has
    four distinct real roots, so `Ind(P'/P; −∞, +∞) = 4`. -/
private def P_2_52 : AzPolynomial ℚ := (parseAzPolynomial "x^4-5*x^2+4").get!
private def P'_2_52 : AzPolynomial ℚ :=
  (parseAzPolynomial "4*x^3-10*x").get!

#guard cauchyIndexOn P'_2_52 P_2_52 .negInf .posInf = 4

/-- `P = X² − 1` has roots at `±1`, so `Ind(P'/P; −∞, +∞) = 2`. -/
private def Q_ex : AzPolynomial ℚ := (parseAzPolynomial "x^2-1").get!
private def Q'_ex : AzPolynomial ℚ := (parseAzPolynomial "2*x").get!

#guard cauchyIndexOn Q'_ex Q_ex .negInf .posInf = 2

-- `Ind(P'/P; 0, +∞)` counts roots in `(0, +∞)` — `2` for
-- `P = X⁴ − 5X² + 4` (roots `1`, `2`).
#guard cauchyIndexOn P'_2_52 P_2_52 (.finite 0) .posInf = 2

/-- Integer-coefficient example: `P = X² − 1`, `P' = 2X`. -/
private def Q_int : AzPolynomial ℤ := (parseAzPolynomial "x^2-1").get!
private def Q'_int : AzPolynomial ℤ := (parseAzPolynomial "2*x").get!

#guard cauchyIndexOnInt Q'_int Q_int .negInf .posInf = 2

-- Trivial: `Q = 0` gives Ind = 0.
#guard cauchyIndexOn (0 : AzPolynomial ℚ) Q_ex .negInf .posInf = 0

/-- **Computable Tarski query.** `tarskiQueryOn Q P a b` computes
    `TaQ(Q, P; a, b) := ∑_{x ∈ (a, b), P(x) = 0} sign(Q(x)) : ℤ` via
    `Var(SRemS(P, P'·Q); a, b)` (BPR Theorem 2.61).

    The truncation length `(P'·Q).coeffs.size + 2` captures every nonzero
    entry of the SRemS sequence: degrees strictly decrease starting from
    `P'·Q`, hitting zero by index `(P'·Q).natDegree + 2 ≤
    (P'·Q).coeffs.size + 2`. -/
def tarskiQueryOn {K : Type _} [Field K] [LinearOrder K] [DecidableEq K]
    [PolynomialDerivative K]
    (Q P : AzPolynomial K) (a b : ExtendedPoint K) : ℤ :=
  let P'Q := P.derivative * Q
  let L := sRemSList P P'Q (P'Q.coeffs.size + 2)
  (varAt L a : ℤ) - (varAt L b : ℤ)

/-- Tarski query for `AzPolynomial ℤ` with `ℚ`-endpoints, computed by
    lifting to `AzPolynomial ℚ` via `mapIntToRat`. -/
def tarskiQueryOnInt (Q P : AzPolynomial ℤ) (a b : ExtendedPoint ℚ) : ℤ :=
  tarskiQueryOn (mapIntToRat Q) (mapIntToRat P) a b

/-! ### Worked examples (Tarski query)

`P = X² − 1` has roots `±1`. With `Q = X`:
* `TaQ(Q, P; −∞, +∞) = sign(1) + sign(−1) = 0`,
* `TaQ(Q, P; 0, +∞) = sign(1) = 1`,
* `TaQ(Q, P; −∞, 0) = sign(−1) = −1`. -/

private def Q_taQ_ex : AzPolynomial ℚ := (parseAzPolynomial "x").get!

#guard tarskiQueryOn Q_taQ_ex Q_ex .negInf .posInf = 0
#guard tarskiQueryOn Q_taQ_ex Q_ex (.finite 0) .posInf = 1
#guard tarskiQueryOn Q_taQ_ex Q_ex .negInf (.finite 0) = -1

-- Trivial: `Q = 1` gives `TaQ = #roots in interval`.
#guard tarskiQueryOn (1 : AzPolynomial ℚ) Q_ex .negInf .posInf = 2

-- Integer-coefficient example.
#guard tarskiQueryOnInt (parseAzPolynomial (R := ℤ) "x").get! Q_int
  .negInf .posInf = 0

/-! ### BPR Example 2.54

With

`P = (X−3)² (X−1) (X+3)`
`Q = (X−5) (X−4) (X−2) (X+1) (X+2) (X+4)`

we have:

* `Ind(Q/P; −∞, +∞) = 0`,
* `Ind(Q/P; −∞, 0) = 1`,
* `Ind(Q/P; 0, +∞) = −1`. -/
/-- Linear factor `X − r`. -/
private def linFactor (r : ℚ) : AzPolynomial ℚ := X - C r

private def P_2_54 : AzPolynomial ℚ :=
  linFactor 3 * linFactor 3 * linFactor 1 * linFactor (-3)

private def Q_2_54 : AzPolynomial ℚ :=
  linFactor 5 * linFactor 4 * linFactor 2 *
    linFactor (-1) * linFactor (-2) * linFactor (-4)

#guard cauchyIndexOn Q_2_54 P_2_54 .negInf .posInf = 0
#guard cauchyIndexOn Q_2_54 P_2_54 .negInf (.finite 0) = 1
#guard cauchyIndexOn Q_2_54 P_2_54 (.finite 0) .posInf = -1

end Azurite.AzPolynomial
