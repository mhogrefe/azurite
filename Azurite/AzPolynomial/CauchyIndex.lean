import Azurite.AzPolynomial.SRemS
import Azurite.AzPolynomial.Eval
import Azurite.AzPolynomial.Cast
import Azurite.AzPolynomial.Derivative
import Azurite.AzPolynomial.Mul
import Azurite.AzPolynomial.SignedSubresultant
import Azurite.AzPolynomial.PRem
import Azurite.AzInt.Equiv.Compare
import Azurite.BasuPollackRoy.Chapter2.Section2_2.Notation_2_34
import Azurite.BasuPollackRoy.Chapter4.Section4_2.Notation_4_31

/-!
# Computable Cauchy Index and Tarski Query on `AzPolynomial`

Computable implementations of `Ind(Q/P; a, b)` and `TaQ(Q, P; a, b)`
derived from **BPR Theorems 2.58 and 2.61**:

* `Var(SRemS(P, Q); a, b) = Ind(Q/P; a, b)`,
* `Var(SRemS(P, P'·Q); a, b) = TaQ(Q, P; a, b)`.

Endpoints come from the existing `Azurite.BPR.ExtendedPoint K` (an
inductive type, fully computable). Sign-variation counting reuses the
existing `Azurite.BPR.Var` (also computable).

Allowed coefficient types: any computable ordered field. For `AzInt`
coefficients the convenience function `cauchyIndexOnIntSRem` lifts to `AzRat`
through `mapAzIntToAzRat`.
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

/-- **Computable Cauchy index.** `cauchyIndexOnSRem Q P a b` computes
    `Ind(Q/P; a, b) : ℤ` via `Var(SRemS(P, Q); a, b)` (BPR Theorem 2.58).

    The truncation length `Q.coeffs.size + 2` captures every nonzero
    entry of the SRemS sequence: degrees strictly decrease starting from
    `Q`, hitting zero by index `Q.natDegree + 2 ≤ Q.coeffs.size + 2`. -/
def cauchyIndexOnSRem {K : Type _} [Field K] [LinearOrder K] [DecidableEq K]
    (Q P : AzPolynomial K) (a b : ExtendedPoint K) : ℤ :=
  let L := sRemSList P Q (Q.coeffs.size + 2)
  (varAt L a : ℤ) - (varAt L b : ℤ)

/-- Cauchy index for `AzPolynomial AzInt` with `AzRat`-endpoints, computed by
    lifting to `AzPolynomial AzRat` via `mapAzIntToAzRat`. -/
def cauchyIndexOnIntSRem (Q P : AzPolynomial AzInt) (a b : ExtendedPoint AzRat) : ℤ :=
  cauchyIndexOnSRem (mapAzIntToAzRat Q) (mapAzIntToAzRat P) a b

/-! ## Worked examples -/

/-- `P = X² − 1` has roots at `±1`, so `Ind(P'/P; −∞, +∞) = 2`. -/
private def Q_ex : AzPolynomial AzRat := (parseAzPolynomial "x^2-1").get!
private def Q'_ex : AzPolynomial AzRat := (parseAzPolynomial "2*x").get!

#guard cauchyIndexOnSRem Q'_ex Q_ex .negInf .posInf = 2

/-- Integer-coefficient example: `P = X² − 1`, `P' = 2X`. -/
private def Q_int : AzPolynomial AzInt := (parseAzPolynomial "x^2-1").get!
private def Q'_int : AzPolynomial AzInt := (parseAzPolynomial "2*x").get!

#guard cauchyIndexOnIntSRem Q'_int Q_int .negInf .posInf = 2

-- Trivial: `Q = 0` gives Ind = 0.
#guard cauchyIndexOnSRem (0 : AzPolynomial AzRat) Q_ex .negInf .posInf = 0

/-- **Computable Tarski query.** `tarskiQueryOnSRem Q P a b` computes
    `TaQ(Q, P; a, b) := ∑_{x ∈ (a, b), P(x) = 0} sign(Q(x)) : ℤ` via
    `Var(SRemS(P, P'·Q); a, b)` (BPR Theorem 2.61).

    The truncation length `(P'·Q).coeffs.size + 2` captures every nonzero
    entry of the SRemS sequence: degrees strictly decrease starting from
    `P'·Q`, hitting zero by index `(P'·Q).natDegree + 2 ≤
    (P'·Q).coeffs.size + 2`. -/
def tarskiQueryOnSRem {K : Type _} [Field K] [LinearOrder K] [DecidableEq K]
    [PolynomialDerivative K]
    (Q P : AzPolynomial K) (a b : ExtendedPoint K) : ℤ :=
  let P'Q := P.derivative * Q
  let L := sRemSList P P'Q (P'Q.coeffs.size + 2)
  (varAt L a : ℤ) - (varAt L b : ℤ)

/-- Tarski query for `AzPolynomial AzInt` with `AzRat`-endpoints, computed by
    lifting to `AzPolynomial AzRat` via `mapAzIntToAzRat`. -/
def tarskiQueryOnIntSRem (Q P : AzPolynomial AzInt) (a b : ExtendedPoint AzRat) : ℤ :=
  tarskiQueryOnSRem (mapAzIntToAzRat Q) (mapAzIntToAzRat P) a b

/-! ### Worked examples (Tarski query)

`P = X² − 1` has roots `±1`. With `Q = X`:
* `TaQ(Q, P; −∞, +∞) = sign(1) + sign(−1) = 0`,
* `TaQ(Q, P; 0, +∞) = sign(1) = 1`,
* `TaQ(Q, P; −∞, 0) = sign(−1) = −1`. -/

private def Q_taQ_ex : AzPolynomial AzRat := (parseAzPolynomial "x").get!

#guard tarskiQueryOnSRem Q_taQ_ex Q_ex .negInf .posInf = 0
#guard tarskiQueryOnSRem Q_taQ_ex Q_ex (.finite 0) .posInf = 1
#guard tarskiQueryOnSRem Q_taQ_ex Q_ex .negInf (.finite 0) = -1

-- Trivial: `Q = 1` gives `TaQ = #roots in interval`.
#guard tarskiQueryOnSRem (1 : AzPolynomial AzRat) Q_ex .negInf .posInf = 2

-- Integer-coefficient example (`Q = X`).
#guard tarskiQueryOnIntSRem ((parseAzPolynomial "x").get! : AzPolynomial AzInt) Q_int
  .negInf .posInf = 0

/-! ## Signed subresultant Cauchy index (BPR Algorithm 9.4)

An alternative computation of the whole-line Cauchy index `Ind(Q/P)` that stays
inside the ordered integral domain `R` — no fraction field, no coefficient
blow-up — using the signed subresultant sequence instead of the signed remainder
sequence. This is the natural integral-domain counterpart of
`cauchyIndexOnSRem _ _ (-∞) (+∞)`, which lifts to a fraction field; the two agree on
the whole line. The provisional name `cauchyIndex` is kept distinct pending
a benchmark comparison; if it wins, it can take over the default name. -/

/-- **BPR Algorithm 9.4 (Signed Subresultant Cauchy Index).** Computes the Cauchy
    index `Ind(Q/P) : ℤ` over all of `R`, for `P ≠ 0` and `Q` in `R[X]` over an
    ordered integral domain `R`.

    When `deg Q ≥ deg P`, `Q` is first replaced by its signed pseudo-remainder
    `pRem Q P` (degree `< deg P`, same Cauchy index — the scaling factor
    `lcof(P)^d` is an even power, hence a nonnegative square). The principal signed
    subresultant coefficients `sRes(P, Q)` (Algorithm 8.21, `signedSubresultant`)
    are then formed and fed — highest index first — to the generalized
    permanences-minus-variations `PmV` (Notation 4.31,
    `Azurite.BPR.Chapter4.PmV`).

    Correctness is BPR Theorem 4.32, `PmV(sRes(P, Q)) = Ind(Q/P)`, to be bridged
    through `toPoly` later. Unlike `cauchyIndexOnSRem`, this needs only `[CommRing R]
    [LinearOrder R] [DecidableEq R] [ExactDiv R]` — no field — so it runs directly
    on `AzInt` coefficients. -/
def cauchyIndex {R : Type _} [CommRing R] [LinearOrder R] [DecidableEq R]
    [Azurite.ExactDiv R] (Q P : AzPolynomial R) : ℤ :=
  let Q' := if P.natDegree ≤ Q.natDegree then pRem Q P else Q
  Azurite.BPR.Chapter4.PmV (signedSubresultant P Q').2.toList.reverse

/-! ### Worked examples (signed subresultant Cauchy index)

All over `AzInt` directly (no fraction field), cross-checked against the signed
remainder whole-line index `cauchyIndexOnIntSRem _ _ (-∞) (+∞)`. -/

private def ppI (str : String) : AzPolynomial AzInt := (parseAzPolynomial (R := AzInt) str).get!

-- `P = X² − 1` (roots `±1`), `Q = P' = 2X` ⇒ `Ind(P'/P) = #real roots = 2`.
#guard cauchyIndex (ppI "2*x") (ppI "x^2-1") = 2
-- `P = X³ − X` (roots `0, ±1`), `Q = P' = 3X² − 1` ⇒ `3`.
#guard cauchyIndex (ppI "3*x^2-1") (ppI "x^3-x") = 3
-- Defective: `P = X⁴ − 1` (real roots `±1`), `Q = P' = 4X³` ⇒ `2`.
#guard cauchyIndex (ppI "4*x^3") (ppI "x^4-1") = 2
-- `Ind(X/(X² − 1)) = 2` (both poles jump `−∞ → +∞`).
#guard cauchyIndex (ppI "x") (ppI "x^2-1") = 2
-- `deg Q > deg P` triggers the `pRem` normalization.
#guard cauchyIndex (ppI "x^3") (ppI "x^2-1") = 2
-- `deg Q = deg P` also triggers `pRem`.
#guard cauchyIndex (ppI "x^2+x") (ppI "x^2-1") = 1
-- `P ∣ Q` ⇒ `pRem = 0` ⇒ `Ind = 0`.
#guard cauchyIndex (ppI "2*x^2-2") (ppI "x^2-1") = 0

-- Agreement with the signed-remainder whole-line Cauchy index on each input.
#guard cauchyIndex (ppI "2*x") (ppI "x^2-1")
        = cauchyIndexOnIntSRem (ppI "2*x") (ppI "x^2-1") .negInf .posInf
#guard cauchyIndex (ppI "5*x^4-1") (ppI "x^5-x")
        = cauchyIndexOnIntSRem (ppI "5*x^4-1") (ppI "x^5-x") .negInf .posInf
#guard cauchyIndex (ppI "x^3") (ppI "x^2-1")
        = cauchyIndexOnIntSRem (ppI "x^3") (ppI "x^2-1") .negInf .posInf

/-! ## Signed subresultant Tarski query (BPR Algorithm 9.5)

The fraction-free counterpart of `tarskiQueryOnSRem _ _ (-∞) (+∞)`: it computes the
whole-line Tarski query `TaQ(Q, P) = ∑_{P(x)=0} sign(Q(x))` inside the ordered
integral domain `R` (no fraction field), via signed subresultants + `PmV`. It
cases on `deg Q`, using the more efficient subresultant computation of BPR
Algorithm 9.5 in each range rather than the naive `Ind(P'·Q / P)`. The
provisional name `tarskiQuery` is kept distinct pending a benchmark. -/

/-- **BPR Algorithm 9.5 (Signed Subresultant Tarski Query).** Computes
    `TaQ(Q, P) : ℤ` for `P ≠ 0` and `Q` in `R[X]` over an ordered integral domain,
    fraction-free. Casing on `q = deg Q` (`p = deg P`, `P' = ` derivative):

    * `q = 0` (`Q = b₀`): `sign(b₀) · PmV(sRes(P, P'))` — `PmV(sRes(P, P'))` counts
      the distinct real roots of `P` (Sturm), scaled by the sign of the constant.
    * `q = 1` (`Q = b₁X + b₀`): `PmV(sRes(P, R))` with `R := P'·Q − (p·b₁)·P`
      (constructed to have degree `< p`).
    * `q > 1`: `PmV(sRes(−P'·Q, P))`, plus `sign(b_q)` when `q − 1` is odd.

    Matches `tarskiQueryOnSRem _ _ (-∞) (+∞)` on the whole line; needs only
    `[CommRing R] [LinearOrder R] [DecidableEq R] [ExactDiv R]
    [PolynomialDerivative R]` — no field — so it runs directly on `AzInt`.
    Correctness is BPR Lemma 4.36, to be bridged through `toPoly` later. -/
def tarskiQuery {R : Type _} [CommRing R] [LinearOrder R] [DecidableEq R]
    [Azurite.ExactDiv R] [PolynomialDerivative R] (Q P : AzPolynomial R) : ℤ :=
  let P' := derivative P
  let p := P.natDegree
  let q := Q.natDegree
  if q = 0 then
    (SignType.sign (Q.coeff 0) : ℤ) * Azurite.BPR.Chapter4.PmV
      (signedSubresultant P P').2.toList.reverse
  else if q = 1 then
    let Rp := P' * Q - ((p : R) * Q.coeff 1) • P
    Azurite.BPR.Chapter4.PmV (signedSubresultant P Rp).2.toList.reverse
  else
    let pmv := Azurite.BPR.Chapter4.PmV (signedSubresultant (-(P' * Q)) P).2.toList.reverse
    if (q - 1) % 2 = 1 then pmv + (SignType.sign Q.leadingCoeff : ℤ) else pmv

/-! ### Worked examples (signed subresultant Tarski query)

Over `AzInt` directly, cross-checked against the signed-remainder whole-line
Tarski query `tarskiQueryOnIntSRem _ _ (-∞) (+∞)`. `P = X² − 1` has roots `±1`. -/

-- `q = 0`: `TaQ(1, P) = #real roots = 2`; `TaQ(−3, P) = −2`.
#guard tarskiQuery (ppI "1") (ppI "x^2-1") = 2
#guard tarskiQuery (ppI "-3") (ppI "x^2-1") = -2
-- `q = 1`: `TaQ(X, P) = sign(1) + sign(−1) = 0`.
#guard tarskiQuery (ppI "x") (ppI "x^2-1") = 0
-- `q > 1`: `TaQ(X², P) = sign(1) + sign(1) = 2`.
#guard tarskiQuery (ppI "x^2") (ppI "x^2-1") = 2

-- Agreement with the signed-remainder whole-line Tarski query.
#guard tarskiQuery (ppI "x+2") (ppI "x^2-1")
        = tarskiQueryOnIntSRem (ppI "x+2") (ppI "x^2-1") .negInf .posInf
#guard tarskiQuery (ppI "x^2+1") (ppI "x^3-x")
        = tarskiQueryOnIntSRem (ppI "x^2+1") (ppI "x^3-x") .negInf .posInf
#guard tarskiQuery (ppI "x^3+2") (ppI "x^3-x")
        = tarskiQueryOnIntSRem (ppI "x^3+2") (ppI "x^3-x") .negInf .posInf

end Azurite.AzPolynomial
