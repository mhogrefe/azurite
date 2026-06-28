import Azurite.AzPolynomial.Basic
import Azurite.AzPolynomial.Neg
import Azurite.AzPolynomial.SMul
import Azurite.AzPolynomial.ExactDiv
import Azurite.AzInt.ExactDiv

/-!
# BPR Algorithm 8.21: Signed Subresultant

This file implements **Algorithm 8.21 (Signed Subresultant)** of Basu, Pollack, Roy on
`AzPolynomial R` over an ordered integral domain `R` (concretely `AzInt`, `AzRat`, …), using only
**exact division** — no fraction field is needed, so the coefficients stay in `R` and never blow up.

Given `P, Q` with `deg P = p > q = deg Q`, the algorithm returns

* `sResP_p, …, sResP_0`: the signed subresultant **polynomials**, and
* `a_p, s_{p-1}, …, s_0`: the signed subresultant **coefficients** (`a_p = lcof(P)`).

The procedure walks the subresultant degrees once (`p → deg sResP_{p-1} → …`), at each
non-defective step taking one exact pseudo-remainder, and at each defective step filling the degree
gap with the closed-form recurrence of Theorem 8.34.  All polynomial divisions are by the leading
coefficient and are exact by the structure theorem, so they are realized with `exactDivQuoRem`
(Euclidean remainder over a ring) and coefficient-wise exact division.

The intended correctness statement (future work) is that, after the `toPoly` bridge,
`signedSubresultant P Q` agrees with `Azurite.BPR.Chapter8.sResP` / the signed subresultant
coefficients; the `#guard` tests below validate it against the (independently computable) signed
remainder sequence via the proportionality of Corollary 8.38.
-/

namespace Azurite.AzPolynomial

variable {R : Type _} [CommRing R] [DecidableEq R] [Azurite.ExactDiv R]

/-- The sign `ε_n = (-1)^{n(n-1)/2}` of Notation 8.33 (the reversal sign of `n` rows). -/
def epsilonSign (n : ℕ) : R := if (n * (n - 1) / 2) % 2 = 0 then 1 else -1

/-- Divide every coefficient of `p` by the ring element `c` using exact ring division.  Exact when
    `c` divides every coefficient (guaranteed for the inputs arising in Algorithm 8.21). -/
def divByRingElt (c : R) (p : AzPolynomial R) : AzPolynomial R :=
  normalize (p.coeffs.map (fun x => Azurite.ExactDiv.exactDiv x c))

/-- Exact Euclidean remainder `Rem(A, B)` over a ring: the remainder of `A` by `B` computed with
    exact division of leading coefficients.  Valid (stays in `R[X]`) precisely when `A` has been
    pre-scaled so the reduction by `lcof(B)` is exact, as in Algorithm 8.21. -/
def remExact (A B : AzPolynomial R) : AzPolynomial R := (exactDivQuoRem A B).2

/-- **One block of Algorithm 8.21's main loop**, as a pure recursion.

`ssAux fuel j Si Sj sj ti` produces the descending list of `(sResP_ℓ, s_ℓ)` pairs for
`ℓ = j-1, j-2, …, 0`, given the carried state:

* `Si = sResP_{i-1}`, `Sj = sResP_{j-1}` — the two relevant subresultants (no array reads needed),
* `sj = s_j`, `ti = t_{i-1}` — the two coefficients that carry the `= 1` conventions at the top.

`t_{j-1} = lcof(Sj)` is recovered locally.  Each step reads `k = deg(Sj)`:

* **non-defective** (`k = j-1`): emit `(Sj, t_{j-1})` and recurse on `sResP_{k-1}`;
* **defective** (`k < j-1`): emit `(Sj, 0)`, the gap zeros, then `(sResP_k, s_k)` with the
  closed-form `s_k = ε_{j-k}·t_{j-1}^{j-k}/s_j^{j-k-1}` (Proposition 8.46), and recurse.

`fuel` bounds the iteration count (`p + 1` suffices); `fuel`/`Sj = 0` exhaustion yields zeros. -/
def ssAux : ℕ → ℕ → AzPolynomial R → AzPolynomial R → R → R → List (AzPolynomial R × R)
  | 0, j, _, _, _, _ => List.replicate j (0, 0)
  | fuel + 1, j, Si, Sj, sj, ti =>
    if Sj = 0 then List.replicate j (0, 0)
    else
      let k := Sj.natDegree
      let tj := Sj.leadingCoeff
      let denom := sj * ti
      if k = j - 1 then
        -- non-defective
        if k = 0 then [(Sj, tj)]
        else
          let Skm1 := divByRingElt denom (-(remExact (tj ^ 2 • Si) Sj))
          (Sj, tj) :: ssAux fuel k Sj Skm1 tj tj
      else
        -- defective: degree drop `> 1`
        let sk := Azurite.ExactDiv.exactDiv (epsilonSign (j - k) * tj ^ (j - k)) (sj ^ (j - k - 1))
        let Spk := divByRingElt tj (sk • Sj)
        let gaps : List (AzPolynomial R × R) := List.replicate (j - k - 2) (0, 0)
        if k = 0 then (Sj, 0) :: (gaps ++ [(Spk, sk)])
        else
          let Skm1 := divByRingElt denom (-(remExact ((tj * sk) • Si) Sj))
          (Sj, 0) :: (gaps ++ ((Spk, sk) :: ssAux fuel k Sj Skm1 sk tj))

/-- **BPR Algorithm 8.21 (Signed Subresultant).**  For `P, Q` with `deg P = p > q = deg Q` and
    `Q ≠ 0`, returns `(sResP, sRes)` where `sResP[ℓ] = sResP_ℓ(P, Q)` and `sRes[ℓ] = s_ℓ` for
    `ℓ = 0, …, p` (with `sRes[p] = lcof(P) = a_p`).  Returns `(#[], #[])` on malformed input
    (`Q = 0` or `p ≤ q`).

    Implemented by the pure recursion `ssAux` carrying the loop state; the inner degree-gap loop of
    the textbook algorithm is replaced by the closed-form coefficient of Proposition 8.46. -/
def signedSubresultant (P Q : AzPolynomial R) : Array (AzPolynomial R) × Array R :=
  if Q = 0 ∨ P.natDegree ≤ Q.natDegree then (#[], #[])
  else
    let p := P.natDegree
    -- descending `ℓ = p, p-1, …, 0`; `s_p = a_p = lcof P`, `s_p`/`t_p` conventions are `1`
    let lst := (P, P.leadingCoeff) :: ssAux (p + 1) p P Q 1 1
    let asc := lst.reverse
    ((asc.map Prod.fst).toArray, (asc.map Prod.snd).toArray)

/-! ### Tests over `AzInt`

Validated against the signed remainder sequence (Corollary 8.38): for these inputs the proportionality
constants are `1`, so the signed subresultants equal the signed remainders at the matching degrees. -/

private def pp (str : String) : AzPolynomial AzInt := (parseAzPolynomial (R := AzInt) str).get!

-- `P = X² + 1`, `Q = X`: non-defective, degrees `2, 1, 0`.
--   sResP = [-1, X, X²+1],  s = [-1, 1, a₂=1].
#guard (signedSubresultant (pp "x^2+1") (pp "x")).1 == #[pp "-1", pp "x", pp "x^2+1"]
#guard (signedSubresultant (pp "x^2+1") (pp "x")).2 == #[(-1 : AzInt), 1, 1]

-- `P = X² `, `Q = X + 1`:  sResP_0 = -(0 + 1) = -1.
#guard (signedSubresultant (pp "x^2") (pp "x+1")).1 == #[pp "-1", pp "x+1", pp "x^2"]
#guard (signedSubresultant (pp "x^2") (pp "x+1")).2 == #[(-1 : AzInt), 1, 1]

-- `P = X³ + X + 1`, `Q = X² + 1`: defective (degree drop `2 → 0`, gap at degree 1).
--   sResP = [-1, -1, X²+1, X³+X+1],  s = [-1, 0, 1, a₃=1].
#guard (signedSubresultant (pp "x^3+x+1") (pp "x^2+1")).1
        == #[pp "-1", pp "-1", pp "x^2+1", pp "x^3+x+1"]
#guard (signedSubresultant (pp "x^3+x+1") (pp "x^2+1")).2 == #[(-1 : AzInt), 0, 1, 1]

-- `P = X⁴ + 1`, `Q = X³`: defective with a degree-2 gap (degrees `3 → 0`), so the inner
--   recurrence runs twice with alternating signs.
--   sResP = [1, 0, -1, X³, X⁴+1],  s = [1, 0, 0, 1, a₄=1].
#guard (signedSubresultant (pp "x^4+1") (pp "x^3")).1
        == #[pp "1", pp "0", pp "-1", pp "x^3", pp "x^4+1"]
#guard (signedSubresultant (pp "x^4+1") (pp "x^3")).2 == #[(1 : AzInt), 0, 0, 1, 1]

end Azurite.AzPolynomial
