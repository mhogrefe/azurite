import Azurite.AzPolynomial.SignedSubresultant
import Azurite.AzPolynomial.Content
import Azurite.AzPolynomial.Parse
import Azurite.AzInt.ParsableElement
import Azurite.AzRat.Instances
import Azurite.AzRat.ParsableElement

/-!
# BPR Algorithm 10.1: Gcd and Gcd-free Part

Computes the greatest common divisor of `P` and `Q` and the gcd-free part of
`P` with respect to `Q` (both up to a multiplicative constant) over an
integral domain `D` with exact division, via **Algorithm 8.22 (Extended
Signed Subresultants)** — fraction-free, so coefficients stay in `D` with no
intermediate blowup:

* if `p = q`, first replace `Q` by `a_p·Q − b_q·P`;
* run `extendedSignedSubresultant P Q` and locate
  `j = deg(gcd(P, Q))` — the smallest index with `sResP_j ≠ 0` (a single
  ascending scan);
* output `(sResP_j, sResV_{j−1})` (`gcdGcdFreePart`); over `ℤ`, output the
  normalized `(a_p·sResP_j / s_j, a_p·sResV_{j−1} / lcof(sResV_{j−1}))`
  (`gcdGcdFreePartInt`) — the divisions are exact by Lemma 10.17
  (the normalizing factors divide `a_p`), and `a_p·sResP_j / s_j` is the
  *monic-times-`a_p`* representative.

Correctness (BPR): the non-`ℤ` case is Corollary 10.15 applied through the
correctness of Algorithm 8.22; the `ℤ` case additionally uses Lemma 10.17
for integrality of the normalized outputs. The abstract chain
(Proposition 10.14, Corollary 10.15, Lemmas 10.16/10.17) is formalized in
`Azurite.BasuPollackRoy.Chapter10.Section10_1`; the `toPoly` bridge for
Algorithm 8.21/8.22 itself is the standing future-work item noted in
`Azurite.AzPolynomial.SignedSubresultant`.

If only the gcd is needed, the **non-extended** Algorithm 8.21 suffices
(`gcdSubresultant`): each loop step then updates one polynomial instead of
three (no `U`/`V` cofactor transport), a constant-factor saving at the same
`O(p·q)` coefficient-operation count.

Degenerate inputs: `Q = 0` (or proportional inputs collapsing to it after
the `p = q` step) return `(P, 1)` — the gcd is `P` and the gcd-free part is
constant.
-/

namespace Azurite.AzPolynomial

variable {R : Type _} [CommRing R] [DecidableEq R] [Azurite.ExactDiv R]

/-- The degree of the gcd: the smallest index `j` with `sResP_j ≠ 0`, from
the ascending subresultant array. -/
def firstNonzero (arr : Array (AzPolynomial R)) : Option ℕ :=
  arr.toList.findIdx? (· != 0)

/-- The `p = q` pre-step of Algorithm 10.1: `a_p·Q − b_q·P`, which drops the
degree strictly below `deg P` when `deg P = deg Q`. -/
def preStep (P Q : AzPolynomial R) : AzPolynomial R :=
  P.leadingCoeff • Q - Q.leadingCoeff • P

/-- The subresultant-gcd **core**: the last nonzero signed subresultant of
`(P, Q)`, for `deg P > deg Q ≥ 1` and `P, Q ≠ 0` (the fallback `P` on the
`none` branch is unreachable in that regime, since `sResP_p = P ≠ 0`). The
output is a gcd of `P` and `Q` up to a multiplicative constant. -/
def subresGcd (P Q : AzPolynomial R) : AzPolynomial R :=
  let sP := (signedSubresultant P Q).1
  match firstNonzero sP with
  | none => P
  | some j => sP[j]!

/-- Core of Algorithm 10.1 after the `p = q` reduction: requires
`deg P > deg Q`, `Q ≠ 0`. Returns `(sResP_j, sResV_{j−1})`; at `j = 0`
(coprime case) the gcd-free part is `P` itself. -/
private def gcdGcdFreePartCore (P Q : AzPolynomial R) :
    AzPolynomial R × AzPolynomial R :=
  let (sP, _, _, sV) := extendedSignedSubresultant P Q
  match firstNonzero sP with
  | none => (P, 1)              -- unreachable: `sResP_p = P ≠ 0`
  | some 0 => (sP[0]!, P)       -- coprime: gcd constant, gcd-free part ∝ P
  | some j => (sP[j]!, sV[j-1]!)

/-- **BPR Algorithm 10.1 (Gcd and Gcd-free Part)**, generic integral-domain
branch, raw subresultant outputs `(sResP_j, sResV_{j−1})`. Returns the gcd
of `P` and `Q` and the gcd-free part of `P` with respect to `Q`, each up to
a multiplicative constant, for `deg P ≥ deg Q`. For the exactly-normalized
uniform interface use `gcd`/`gcdGcdFreePart` (the `GcdImpl` typeclass). -/
def gcdGcdFreePartRaw (P Q : AzPolynomial R) : AzPolynomial R × AzPolynomial R :=
  if Q = 0 then (P, 1)
  else if P.natDegree = Q.natDegree then
    -- replace `Q` by `a_p·Q − b_q·P` (degree drops)
    if preStep P Q = 0 then (P, 1) else gcdGcdFreePartCore P (preStep P Q)
  else gcdGcdFreePartCore P Q

/-- Core of the `ℤ` branch: normalized outputs
`(a_p·sResP_j / s_j, a_p·sResV_{j−1} / lcof(sResV_{j−1}))`; exact divisions
by Lemma 10.17. -/
private def gcdGcdFreePartIntCore (P Q : AzPolynomial AzInt) :
    AzPolynomial AzInt × AzPolynomial AzInt :=
  let ap := P.leadingCoeff
  let (sP, s, _, sV) := extendedSignedSubresultant P Q
  match firstNonzero sP with
  | none => (P, 1)
  | some 0 => (divByRingElt s[0]! (ap • sP[0]!), P)
  | some j =>
    (divByRingElt s[j]! (ap • sP[j]!),
     divByRingElt (sV[j-1]!).leadingCoeff (ap • sV[j-1]!))

/-- **BPR Algorithm 10.1 (Gcd and Gcd-free Part)** over `ℤ` (`AzInt`), with
the normalized integer outputs `a_p·sResP_j / s_j` and
`a_p·sResV_{j−1} / lcof(sResV_{j−1})` (exact divisions by Lemma 10.17). -/
def gcdGcdFreePartInt (P Q : AzPolynomial AzInt) :
    AzPolynomial AzInt × AzPolynomial AzInt :=
  if Q = 0 then (P, 1)
  else if P.natDegree = Q.natDegree then
    if preStep P Q = 0 then (P, 1) else gcdGcdFreePartIntCore P (preStep P Q)
  else gcdGcdFreePartIntCore P Q

/-- **Gcd only**, via the non-extended Algorithm 8.21 — no `U`/`V` cofactor
transport, a constant-factor saving over `gcdGcdFreePart` when the gcd-free
part is not needed. -/
def gcdSubresultant (P Q : AzPolynomial R) : AzPolynomial R :=
  if Q = 0 then P
  else if P.natDegree = Q.natDegree then
    if preStep P Q = 0 then P else subresGcd P (preStep P Q)
  else subresGcd P Q

/-! ### Exact normalization: matching Mathlib's `Polynomial` gcd

The subresultant gcd is only canonical up to a multiplicative constant. The
entry points below normalize it to agree *exactly* with Mathlib's
`NormalizedGCDMonoid` gcd of the represented polynomials:

* over a field, the normalized gcd is the **monic** gcd (`gcdMonic`);
* over `ℤ`, it is `gcd(cont P, cont Q)` times the **primitive positive**
  gcd of the primitive parts (`gcdNormalizedInt`) — the subresultant chain
  computes the gcd of the polynomial parts (a `ℚ[X]` gcd descended to
  `ℤ[X]`), so the content factor `gcd(cont P, cont Q)` is reinstated from
  the original inputs (in particular it is *unpolluted* by the `p = q`
  pre-step, which can inject spurious content into the chain), and the sign
  is fixed so the leading coefficient is positive.

Degenerate cases follow Mathlib: `gcd 0 0 = 0` and `gcd P 0 = normalize P`
(sign- resp. monic-normalized `P`, with no content extraction). -/

/-- The canonical embedding of a nonnegative magnitude. -/
def azNatToAzInt (n : AzNat) : AzInt := ⟨true, n, fun _ => rfl⟩

/-- Sign normalization over `ℤ`: `normalize P` (positive leading
coefficient). -/
def signNorm (p : AzPolynomial AzInt) : AzPolynomial AzInt :=
  if p.leadingCoeff.sign then p else -p

/-- The primitive part with positive leading coefficient. -/
def primPos (g : AzPolynomial AzInt) : AzPolynomial AzInt :=
  let c := azNatToAzInt g.content
  divByRingElt (if g.leadingCoeff.sign then c else -c) g

/-- Monic normalization over a field: `normalize P`. -/
def monicize {K : Type _} [Field K] [DecidableEq K] (p : AzPolynomial K) :
    AzPolynomial K :=
  divByRingElt p.leadingCoeff p

/-- The gcd of the contents, as a (nonnegative) `AzInt`. -/
def contentGcdInt (P Q : AzPolynomial AzInt) : AzInt :=
  azNatToAzInt (AzNat.gcd P.content Q.content)

/-- The gcd, normalized to match Mathlib's `ℤ[X]` gcd **exactly**:
`gcd(cont P, cont Q)` times the primitive gcd with positive leading
coefficient. Total in `P, Q` (zero, constant and swapped-degree inputs
included; constant branches are explicit so that each recursion-free case
is separately provable). -/
def gcdNormalizedInt (P Q : AzPolynomial AzInt) : AzPolynomial AzInt :=
  if P = 0 then signNorm Q
  else if Q = 0 then signNorm P
  else if P.natDegree = 0 ∨ Q.natDegree = 0 then
    contentGcdInt P Q • (1 : AzPolynomial AzInt)
  else if P.natDegree = Q.natDegree then
    if preStep P Q = 0 then contentGcdInt P Q • primPos P
    else if (preStep P Q).natDegree = 0 then contentGcdInt P Q • (1 : AzPolynomial AzInt)
    else contentGcdInt P Q • primPos (subresGcd P (preStep P Q))
  else if P.natDegree < Q.natDegree then contentGcdInt P Q • primPos (subresGcd Q P)
  else contentGcdInt P Q • primPos (subresGcd P Q)

/-- The gcd over a field, normalized to match Mathlib's `K[X]` gcd
**exactly**: the monic gcd. Total in `P, Q` (constant branches explicit,
as in `gcdNormalizedInt`). -/
def gcdMonic {K : Type _} [Field K] [DecidableEq K] (P Q : AzPolynomial K) :
    AzPolynomial K :=
  if P = 0 ∧ Q = 0 then 0
  else if P = 0 then monicize Q
  else if Q = 0 then monicize P
  else if P.natDegree = 0 ∨ Q.natDegree = 0 then 1
  else if P.natDegree = Q.natDegree then
    if preStep P Q = 0 then monicize P
    else if (preStep P Q).natDegree = 0 then 1
    else monicize (subresGcd P (preStep P Q))
  else if P.natDegree < Q.natDegree then monicize (subresGcd Q P)
  else monicize (subresGcd P Q)

/-! ### The `GcdImpl` typeclass: a uniform `gcd`/`gcdGcdFreePart` interface

Different coefficient types normalize their polynomial gcds differently
(monic over a field, content-times-primitive-positive over `ℤ`), so the
uniform interface is a typeclass indexed by the coefficient type. The class
operations are exported into `Azurite.AzPolynomial`, so `gcd P Q` and
`P.gcd Q` just work.

Contract: `gcd` agrees exactly with Mathlib's normalized gcd of the
represented polynomials, and `gcdGcdFreePart P Q = (g, P/g)` where
`g = gcd P Q` — the *canonical* gcd-free part, the exact quotient by the
normalized gcd (matching the abstract `gcdFreePart P Q = P / gcd P Q` and,
at `Q = P′`, the separable part of Lemma 10.13). The BPR-normalized raw
outputs of Algorithm 10.1 remain available as `gcdGcdFreePartRaw` /
`gcdGcdFreePartInt`.

(Interaction note: inside `namespace Azurite.AzPolynomial`, a file importing
this one sees the exported `gcd`; refer to Mathlib's as `_root_.gcd` if both
are needed.) -/

/-- Coefficient-type-directed gcd (and gcd-free part) implementations for
`AzPolynomial`. -/
class GcdImpl (R : Type _) [Semiring R] where
  /-- The gcd, exactly matching Mathlib's normalized gcd of the represented
  polynomials. -/
  gcd : AzPolynomial R → AzPolynomial R → AzPolynomial R
  /-- The gcd together with the canonical gcd-free part `P / gcd P Q`. -/
  gcdGcdFreePart : AzPolynomial R → AzPolynomial R → AzPolynomial R × AzPolynomial R

/-- The normalized gcd, dispatched by coefficient type. -/
abbrev gcd {R : Type _} [Semiring R] [GcdImpl R] :
    AzPolynomial R → AzPolynomial R → AzPolynomial R := GcdImpl.gcd

/-- The gcd with the canonical gcd-free part `P / gcd P Q`, dispatched by
coefficient type. -/
abbrev gcdGcdFreePart {R : Type _} [Semiring R] [GcdImpl R] :
    AzPolynomial R → AzPolynomial R → AzPolynomial R × AzPolynomial R :=
  GcdImpl.gcdGcdFreePart

/-- `ℤ` coefficients: the content-times-primitive-positive normalized gcd. -/
instance : GcdImpl AzInt where
  gcd := gcdNormalizedInt
  gcdGcdFreePart P Q :=
    let g := gcdNormalizedInt P Q
    (g, if g = 0 then 0 else (exactDivQuoRem P g).1)

/-- Field coefficients: the monic normalized gcd. -/
instance {K : Type _} [Field K] [DecidableEq K] : GcdImpl K where
  gcd := gcdMonic
  gcdGcdFreePart P Q :=
    let g := gcdMonic P Q
    (g, if g = 0 then 0 else (exactDivQuoRem P g).1)

-- ═══════════════════════════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════════════════════════

section Tests

private def pp (s : String) : AzPolynomial AzInt := (parseAzPolynomial s).get!
private def pq (s : String) : AzPolynomial AzRat := (parseAzPolynomial s).get!

/- Test inputs.
`P₁ = (X−1)(X+2)²` and `Q₁ = (X−1)(X+2)(X−3)`: equal degrees, exercising the
`p = q` pre-step; `gcd = (X−1)(X+2) = X²+X−2` and the gcd-free part of `P₁`
with respect to `Q₁` is `X+2`.
`P₂ = (X−1)³(X+1)` and `Q₂ = (X−1)²(X+5)`: higher multiplicity;
`gcd = (X−1)² = X²−2X+1` and the gcd-free part is `(X−1)(X+1) = X²−1`. -/
private def P₁ : AzPolynomial AzInt := pp "x^3+3*x^2-4"
private def Q₁ : AzPolynomial AzInt := pp "x^3-2*x^2-5*x+6"
private def P₂ : AzPolynomial AzInt := pp "x^4-2*x^3+2*x-1"
private def Q₂ : AzPolynomial AzInt := pp "x^3+3*x^2-9*x+5"

-- ── Algorithm 10.1, `ℤ`-normalized outputs (`a_p·sResP_j/s_j`,
--    `a_p·sResV_{j−1}/lcof`) ──
#guard gcdGcdFreePartInt P₁ Q₁ == (pp "x^2+x-2", pp "x+2")
-- the leading coefficient `a_p = 2` enters both outputs
#guard gcdGcdFreePartInt (pp "2*x^3+6*x^2-8") Q₁ == (pp "2*x^2+2*x-4", pp "2*x+4")
#guard gcdGcdFreePartInt P₂ Q₂ == (pp "x^2-2*x+1", pp "x^2-1")
-- coprime: constant gcd, gcd-free part `= P`
#guard gcdGcdFreePartInt (pp "x^2+1") (pp "x-1") == (pp "1", pp "x^2+1")
-- degenerate: zero and proportional inputs
#guard gcdGcdFreePartInt (pp "x^2+1") (pp "0") == (pp "x^2+1", pp "1")
#guard gcdGcdFreePartInt (pp "3*x^2+3") (pp "x^2+1") == (pp "3*x^2+3", pp "1")

-- ── Algorithm 10.1, generic-domain branch: raw subresultant outputs,
--    proportional to the normalized ones (`−5(X²+X−2)`, `−5(X+2)`) ──
#guard gcdGcdFreePartRaw P₁ Q₁ == (pp "-5*x^2-5*x+10", pp "-5*x-10")

-- ── gcd only, via the non-extended Algorithm 8.21 ──
#guard gcdSubresultant P₁ Q₁ == pp "-5*x^2-5*x+10"
#guard gcdSubresultant (pp "x^2+1") (pp "x-1") == pp "-2"

-- ── `gcdNormalizedInt`: exactly Mathlib's normalized `ℤ[X]` gcd ──
-- primitive part independent of input scaling; content gcd reinstated
#guard gcdNormalizedInt P₁ Q₁ == pp "x^2+x-2"
#guard gcdNormalizedInt (pp "2*x^3+6*x^2-8") Q₁ == pp "x^2+x-2"
#guard gcdNormalizedInt (pp "2*x^3+6*x^2-8") (pp "2*x^3-4*x^2-10*x+12")
        == pp "2*x^2+2*x-4"
-- proportional and constant arguments: `gcd(2X+2, 4X+4) = 2X+2`,
-- `gcd(−3X−3, 6) = 3`
#guard gcdNormalizedInt (pp "2*x+2") (pp "4*x+4") == pp "2*x+2"
#guard gcdNormalizedInt (pp "-3*x-3") (pp "6") == pp "3"
-- zero conventions and sign normalization; swapped degrees
#guard gcdNormalizedInt (pp "0") (pp "-2*x") == pp "2*x"
#guard gcdNormalizedInt (pp "0") (pp "0") == pp "0"
#guard gcdNormalizedInt (pp "x-1") (pp "x^2-1") == pp "x-1"

-- ── `gcdMonic`: exactly Mathlib's monic `K[X]` gcd (over `AzRat`) ──
#guard gcdMonic (pq "2*x^2+2*x-4") (pq "x^2+3*x+2") == pq "x+2"
#guard gcdMonic (pq "x^3+3*x^2-4") (pq "x^3-2*x^2-5*x+6") == pq "x^2+x-2"
#guard gcdMonic (pq "0") (pq "2*x+4") == pq "x+2"
#guard gcdMonic (pq "0") (pq "0") == pq "0"

-- ── the `GcdImpl` typeclass: uniform `gcd`/`gcdGcdFreePart`, dispatched by
--    coefficient type; the pair is the canonical `(g, P/g)` ──
#guard gcd P₁ Q₁ == pp "x^2+x-2"
#guard gcd (pq "x^3+3*x^2-4") (pq "x^3-2*x^2-5*x+6") == pq "x^2+x-2"
#guard gcdGcdFreePart P₁ Q₁ == (pp "x^2+x-2", pp "x+2")
-- content-scaled `P`: the canonical free part keeps `P`'s content
#guard gcdGcdFreePart (pp "2*x^3+6*x^2-8") Q₁ == (pp "x^2+x-2", pp "2*x+4")
-- field: monic gcd, free part carries `P`'s leading coefficient
#guard gcdGcdFreePart (pq "2*x^2+2*x-4") (pq "x^2+3*x+2") == (pq "x+2", pq "2*x-2")
-- zero conventions: `gcd P 0 = normalize P` with unit free part
#guard gcdGcdFreePart (pp "0") (pp "0") == (pp "0", pp "0")
#guard gcdGcdFreePart (pp "-2*x") (pp "0") == (pp "2*x", pp "-1")

end Tests

end Azurite.AzPolynomial
