import Azurite.Algorithm.DetExpansion
import Azurite.AzPolynomial.Gcd
import Azurite.AzPolynomial.Monomial
import Azurite.AzPolynomial.Equiv.Algebra
import Azurite.AzPolynomial.Equiv.Monomial

/-!
# Determinant-route signed subresultants: the general-ring fallback

BPR Remark 10.18: Algorithm 8.22 uses exact divisions and needs an integral
domain; over a general commutative ring the signed subresultant coefficients
can always be computed as determinants (Remark 8.23), and hence the
separable and gcd-free parts.

This file implements that route computably, mirroring the abstract
determinant definitions verbatim:

* `sResPDet P Q j` — the signed subresultant polynomial, assembled from the
  `pdetRing` coefficient-ring minors, each computed by the division-free
  expansion determinant `detFn`;
* `sResVDet P Q j` — the `V`-cofactor, as the `detFn`-determinant of the
  `sResVMat` matrix over `AzPolynomial R`;
* `gcdGcdFreePartDet P Q` — the **fallback pair** `(sResP_j, sResV_{j−1})`
  (`j` the last nonzero index), requiring only `[CommRing R] [DecidableEq R]`
  — no exact division. Over an integral domain the outputs are the gcd and
  the gcd-free part of `P` with respect to `Q`, up to multiplicative
  constants (see `Azurite.AzPolynomial.Equiv.GcdDet`); over a general ring
  they are the determinant-defined quantities themselves.

This is **not** registered as a `GcdImpl` instance: over a non-domain ring
"the gcd" is not well-defined (no normalization; gcds need not exist), so
the fallback exposes the raw subresultant outputs instead of pretending to
the `GcdImpl` contract. Cost: `detFn` is `O(m!)` — a correctness-first
fallback (Berkowitz's `O(m⁴)` division-free determinant is the upgrade
path); over domains use `gcd`/`gcdGcdFreePart`.
-/

namespace Azurite.AzPolynomial

variable {R : Type _} [CommRing R] [DecidableEq R]

/-- Entry generator of the Sylvester–Habicht matrix `SyHa_j(P, Q)`: the
coefficient at degree `d` of the `i`-th family polynomial
(`X^{q−j−1−i}·P` for `i < q−j`, else `X^{i−(q−j)}·Q`). -/
def syhaEntry (P Q : AzPolynomial R) (j i d : ℕ) : R :=
  if i < Q.natDegree - j then
    (if Q.natDegree - j - 1 - i ≤ d then P.coeff (d - (Q.natDegree - j - 1 - i)) else 0)
  else
    (if i - (Q.natDegree - j) ≤ d then Q.coeff (d - (i - (Q.natDegree - j))) else 0)

/-- **Signed subresultant polynomial by determinants** (the Remark 10.18 /
8.23 route): mirrors the abstract `Chapter8.sResP` verbatim, with each
`pdetRing` minor computed by the division-free `detFn`. Valid over any
commutative ring. -/
def sResPDet (P Q : AzPolynomial R) (j : ℕ) : AzPolynomial R :=
  if j ≤ Q.natDegree then
    normalize (Array.ofFn (n := P.natDegree + Q.natDegree - j
        - (P.natDegree + Q.natDegree - 2 * j) + 1) fun i =>
      detFn (P.natDegree + Q.natDegree - 2 * j) (fun r c =>
        syhaEntry P Q j r
          (if c + 1 < P.natDegree + Q.natDegree - 2 * j then
            P.natDegree + Q.natDegree - j - 1 - c
          else (i : ℕ))))
  else if j = P.natDegree then P
  else if j = P.natDegree - 1 then Q
  else 0

/-- **`V`-cofactor by determinants**: the `detFn`-determinant of the
`sResVMat` matrix (constant columns from `SyHa_j`, last column the ascending
monomials on the `Q`-block rows), over `AzPolynomial R`. -/
def sResVDet (P Q : AzPolynomial R) (j : ℕ) : AzPolynomial R :=
  detFn (P.natDegree + Q.natDegree - 2 * j) (fun i k =>
    if k + 1 < P.natDegree + Q.natDegree - 2 * j then
      monomial 0 (syhaEntry P Q j i (P.natDegree + Q.natDegree - j - 1 - k))
    else if i < Q.natDegree - j then 0
    else monomial (i - (Q.natDegree - j)) 1)

/-- First `j` with `sResPDet P Q j ≠ 0`, scanning `j = 0, 1, …, q`. -/
def firstNonzeroDet (P Q : AzPolynomial R) : Option ℕ :=
  (List.range (Q.natDegree + 1)).find? (fun j => sResPDet P Q j != 0)

/-- **The general-ring fallback pair** (BPR Remark 10.18): the last nonzero
signed subresultant `sResP_j` and the cofactor `sResV_{j−1}`, both computed
by division-free determinants — no `ExactDiv`, any `CommRing`. Over an
integral domain (with `deg P > deg Q ≥ 1`, both nonzero) these are the gcd
of `P, Q` and the gcd-free part of `P` with respect to `Q`, each up to a
multiplicative constant. Degenerate inputs return `(P, 1)`; the coprime
case `j = 0` returns `(sResP_0, P)`. -/
def gcdGcdFreePartDet (P Q : AzPolynomial R) : AzPolynomial R × AzPolynomial R :=
  if Q = 0 then (P, 1)
  else if P.natDegree = Q.natDegree then
    if preStep P Q = 0 then (P, 1)
    else
      match firstNonzeroDet P (preStep P Q) with
      | none => (P, 1)
      | some 0 => (sResPDet P (preStep P Q) 0, P)
      | some j => (sResPDet P (preStep P Q) j, sResVDet P (preStep P Q) (j - 1))
  else
    match firstNonzeroDet P Q with
    | none => (P, 1)
    | some 0 => (sResPDet P Q 0, P)
    | some j => (sResPDet P Q j, sResVDet P Q (j - 1))

-- ═══════════════════════════════════════════════════════════════════
-- Tests (cross-validated against the exact-division route over `AzInt`)
-- ═══════════════════════════════════════════════════════════════════

section Tests

private def pp (s : String) : AzPolynomial AzInt := (parseAzPolynomial s).get!

-- `sResPDet` agrees with Algorithm 8.21's output (both are the abstract
-- `sResP` — proven, not just tested; see `Equiv.GcdDet`)
#guard (List.range 4).all (fun j =>
  toChars (sResPDet (pp "x^3+3*x^2-4") (pp "-5*x^2-5*x+10") j)
    == toChars ((signedSubresultant (pp "x^3+3*x^2-4") (pp "-5*x^2-5*x+10")).1[j]!))

-- fallback pair on the running example: `gcd ∝ (X−1)(X+2)`,
-- free part `∝ X+2`
#guard toChars ((gcdGcdFreePartDet (pp "x^3+3*x^2-4") (pp "x^3-2*x^2-5*x+6")).1)
    == "-5*x^2-5*x+10"
#guard toChars ((gcdGcdFreePartDet (pp "x^3+3*x^2-4") (pp "x^3-2*x^2-5*x+6")).2)
    == "-5*x-10"
-- higher multiplicity: `P = (X−1)³(X+1)`, `Q = (X−1)²(X+5)`
#guard (let (g, f) := gcdGcdFreePartDet (pp "x^4-2*x^3+2*x-1") (pp "x^3+3*x^2-9*x+5")
        g.natDegree == 2 && f.natDegree == 2)
-- coprime: constant gcd, free part `= P`
#guard toChars ((gcdGcdFreePartDet (pp "x^2+1") (pp "x-1")).2) == "x^2+1"
-- degenerate
#guard (let (g, f) := gcdGcdFreePartDet (pp "x^2+1") (pp "0"); toChars g == "x^2+1" && toChars f == "1")

end Tests

end Azurite.AzPolynomial
