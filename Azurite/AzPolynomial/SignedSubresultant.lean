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

/-- **One block of Algorithm 8.22's main loop** (Extended Signed Subresultant), as a pure recursion.

Mirrors `ssAux` but additionally carries the Bézout cofactors and emits
`(sResP_ℓ, s_ℓ, sResU_ℓ, sResV_ℓ)` 4-tuples.  The carried state adds
`Ui = sResU_{i-1}`, `Vi = sResV_{i-1}`, `Uj = sResU_{j-1}`, `Vj = sResV_{j-1}`.

The cofactors are transported by the **same** quotient `C = Quo(d·sResP_{i-1}, sResP_{j-1})` and the
same `divByRingElt denom` (`denom = s_j·t_{i-1}`) used for `sResP_k`, so the Bézout relation
`sResP_ℓ = sResU_ℓ·P + sResV_ℓ·Q` is preserved by linearity (BPR's correctness remark).

When the sequence terminates (`sResP_{j-1} = 0`, i.e. `j` is the gcd degree), the **boundary
cofactors** `sResU_{j-1}, sResV_{j-1}` are still emitted (alongside `sResP_{j-1} = 0`): they are
nonzero — `sResV_{j-1}` is the gcd-free part of `P` with respect to `Q` (Proposition 10.14, used
by Algorithm 10.1) — and satisfy the Bézout relation `sResU_{j-1}·P + sResV_{j-1}·Q = 0`. Deeper
entries stay at their initialized value `0`, per BPR's algorithmic convention. -/
def ssAuxExt : ℕ → ℕ → AzPolynomial R → AzPolynomial R → R → R →
    AzPolynomial R → AzPolynomial R → AzPolynomial R → AzPolynomial R →
    List (AzPolynomial R × R × AzPolynomial R × AzPolynomial R)
  | 0, j, _, _, _, _, _, _, _, _ => List.replicate j (0, 0, 0, 0)
  | fuel + 1, j, Si, Sj, sj, ti, Ui, Vi, Uj, Vj =>
    if Sj = 0 then
      if j = 0 then []
      else (0, 0, Uj, Vj) :: List.replicate (j - 1) (0, 0, 0, 0)
    else
      let k := Sj.natDegree
      let tj := Sj.leadingCoeff
      let denom := sj * ti
      if k = j - 1 then
        -- non-defective
        if k = 0 then [(Sj, tj, Uj, Vj)]
        else
          let C := (exactDivQuoRem (tj ^ 2 • Si) Sj).1
          let Skm1 := divByRingElt denom (-(remExact (tj ^ 2 • Si) Sj))
          let Ukm1 := divByRingElt denom (C * Uj - tj ^ 2 • Ui)
          let Vkm1 := divByRingElt denom (C * Vj - tj ^ 2 • Vi)
          (Sj, tj, Uj, Vj) :: ssAuxExt fuel k Sj Skm1 tj tj Uj Vj Ukm1 Vkm1
      else
        -- defective: degree drop `> 1`
        let sk := Azurite.ExactDiv.exactDiv (epsilonSign (j - k) * tj ^ (j - k)) (sj ^ (j - k - 1))
        let Spk := divByRingElt tj (sk • Sj)
        let Upk := divByRingElt tj (sk • Uj)
        let Vpk := divByRingElt tj (sk • Vj)
        let gaps : List (AzPolynomial R × R × AzPolynomial R × AzPolynomial R) :=
          List.replicate (j - k - 2) (0, 0, 0, 0)
        if k = 0 then (Sj, 0, Uj, Vj) :: (gaps ++ [(Spk, sk, Upk, Vpk)])
        else
          let C := (exactDivQuoRem ((tj * sk) • Si) Sj).1
          let Skm1 := divByRingElt denom (-(remExact ((tj * sk) • Si) Sj))
          let Ukm1 := divByRingElt denom (C * Uj - (tj * sk) • Ui)
          let Vkm1 := divByRingElt denom (C * Vj - (tj * sk) • Vi)
          (Sj, 0, Uj, Vj) :: (gaps ++ ((Spk, sk, Upk, Vpk) :: ssAuxExt fuel k Sj Skm1 sk tj Uj Vj Ukm1 Vkm1))

/-- **BPR Algorithm 8.22 (Extended Signed Subresultant).**  For `P, Q` with `deg P = p > q = deg Q`
    and `Q ≠ 0`, returns `(sResP, sRes, sResU, sResV)` where `sResP[ℓ] = sResP_ℓ`, `sRes[ℓ] = s_ℓ`,
    `sResU[ℓ] = sResU_ℓ`, `sResV[ℓ] = sResV_ℓ` for `ℓ = 0, …, p`.  The cofactors satisfy the Bézout
    relation `sResP_ℓ = sResU_ℓ·P + sResV_ℓ·Q`.  Returns `(#[], #[], #[], #[])` on malformed input.

    Built on `ssAuxExt`; the `sResP`/`sRes` components coincide with `signedSubresultant`. -/
def extendedSignedSubresultant (P Q : AzPolynomial R) :
    Array (AzPolynomial R) × Array R × Array (AzPolynomial R) × Array (AzPolynomial R) :=
  if Q = 0 ∨ P.natDegree ≤ Q.natDegree then (#[], #[], #[], #[])
  else
    let p := P.natDegree
    -- `sResU_p = sResV_{p-1} = 1`, `sResV_p = sResU_{p-1} = 0`
    let lst := (P, P.leadingCoeff, (1 : AzPolynomial R), (0 : AzPolynomial R))
      :: ssAuxExt (p + 1) p P Q 1 1 1 0 0 1
    let asc := lst.reverse
    ((asc.map (·.1)).toArray, (asc.map (·.2.1)).toArray,
     (asc.map (·.2.2.1)).toArray, (asc.map (·.2.2.2)).toArray)

/-! ### Tests over `AzInt`

Validated against the signed remainder sequence (Corollary 8.38): for these inputs the proportionality
constants are `1`, so the signed subresultants equal the signed remainders at the matching degrees. -/

private def pp (str : String) : AzPolynomial AzInt := (parseAzPolynomial (R := AzInt) str).get!

-- `P = X² + 1`, `Q = X`: non-defective, degrees `2, 1, 0`.
--   sResP = [-1, X, X²+1],  s = [-1, 1, a₂=1].
#guard ((signedSubresultant (pp "x^2+1") (pp "x")).1).map toChars == #["-1", "x", "x^2+1"]
#guard (signedSubresultant (pp "x^2+1") (pp "x")).2 == #[(-1 : AzInt), 1, 1]

-- `P = X² `, `Q = X + 1`:  sResP_0 = -(0 + 1) = -1.
#guard ((signedSubresultant (pp "x^2") (pp "x+1")).1).map toChars == #["-1", "x+1", "x^2"]
#guard (signedSubresultant (pp "x^2") (pp "x+1")).2 == #[(-1 : AzInt), 1, 1]

-- `P = X³ + X + 1`, `Q = X² + 1`: defective (degree drop `2 → 0`, gap at degree 1).
--   sResP = [-1, -1, X²+1, X³+X+1],  s = [-1, 0, 1, a₃=1].
#guard ((signedSubresultant (pp "x^3+x+1") (pp "x^2+1")).1).map toChars
        == #["-1", "-1", "x^2+1", "x^3+x+1"]
#guard (signedSubresultant (pp "x^3+x+1") (pp "x^2+1")).2 == #[(-1 : AzInt), 0, 1, 1]

-- `P = X⁴ + 1`, `Q = X³`: defective with a degree-2 gap (degrees `3 → 0`), so the inner
--   recurrence runs twice with alternating signs.
--   sResP = [1, 0, -1, X³, X⁴+1],  s = [1, 0, 0, 1, a₄=1].
#guard ((signedSubresultant (pp "x^4+1") (pp "x^3")).1).map toChars
        == #["1", "0", "-1", "x^3", "x^4+1"]
#guard (signedSubresultant (pp "x^4+1") (pp "x^3")).2 == #[(1 : AzInt), 0, 0, 1, 1]

/-! ### Tests for `extendedSignedSubresultant` (Algorithm 8.22) -/

-- The `sResP`/`sRes` components coincide with `signedSubresultant`.
#guard ((extendedSignedSubresultant (pp "x^3+x+1") (pp "x^2+1")).1).map toChars
        == ((signedSubresultant (pp "x^3+x+1") (pp "x^2+1")).1).map toChars
#guard (extendedSignedSubresultant (pp "x^3+x+1") (pp "x^2+1")).2.1
        == (signedSubresultant (pp "x^3+x+1") (pp "x^2+1")).2

/-- Check the Bézout relation `sResU_ℓ · P + sResV_ℓ · Q = sResP_ℓ` at every output index. -/
private def bezoutOK (P Q : AzPolynomial AzInt) : Bool :=
  let r := extendedSignedSubresultant P Q
  ((r.2.2.1.zip r.2.2.2).zip r.1).all (fun t => toChars (t.1.1 * P + t.1.2 * Q) == toChars t.2)

#guard bezoutOK (pp "x^2+1") (pp "x")
#guard bezoutOK (pp "x^2") (pp "x+1")
#guard bezoutOK (pp "x^3+x+1") (pp "x^2+1")
#guard bezoutOK (pp "x^4+1") (pp "x^3")
#guard bezoutOK (pp "2*x^3+x+3") (pp "5*x^2+x+1")

end Azurite.AzPolynomial
