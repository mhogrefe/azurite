import Azurite.BasuPollackRoy.Chapter4.Section4_2.Proposition_4_16

/-!
# BPR Proposition 4.21: functoriality of the resultant

For polynomials `P, Q : D[X]` with formal degrees `p, q` and any
commutative-ring homomorphism `f : D → D'`,

  `f(Res(P, Q, p, q)) = Res(f(P), f(Q), p, q)`.

BPR states this under the auxiliary hypotheses that `P` is monic and
`deg Q ≤ deg P`. Those hypotheses are not actually required for the
identity itself — they only ensure that `deg f(P) = deg P` so that the
``natural'' choice of formal degrees on the right-hand side
(taking `f(P).natDegree` and `f(Q).natDegree`) agrees with the
left-hand side. By making the formal degrees `p, q` explicit
parameters, the identity holds for arbitrary `P, Q : D[X]` and arbitrary
ring homomorphism `f`.

The proof is the underlying `Res_map` lemma (Proposition 4.16's
auxiliary functoriality lemma): the Sylvester matrix is built
entry-wise from coefficients of `P` and `Q`, so coefficient maps
commute with the construction; the determinant then commutes with the
ring homomorphism applied entry-wise (`RingHom.map_det`).
-/

namespace Azurite.BPR.Chapter4

open Polynomial

variable {D : Type*} [CommRing D]
variable {D' : Type*} [CommRing D']

/-- **BPR Proposition 4.21.** The resultant is functorial in the
    coefficient ring: for any ring homomorphism `f : D → D'`,

      `f(Res(P, Q, p, q)) = Res(f(P), f(Q), p, q)`. -/
theorem Proposition_4_21 (P Q : D[X]) (p q : ℕ) (f : D →+* D') :
    f (Res P p Q q) = Res (P.map f) p (Q.map f) q :=
  Res_map f P p Q q

end Azurite.BPR.Chapter4
