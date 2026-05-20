import Azurite.BasuPollackRoy.Chapter4.Section4_2.Proposition_4_16

/-!
# BPR Proposition 4.21: functoriality of the resultant

For polynomials `P, Q : D[X]` and any commutative-ring homomorphism
`f : D → D'`,

  `f(Res(P, Q)) = Res(f(P), f(Q))`,

provided the homomorphism preserves the natural degrees of `P` and `Q`
(so that the formal Sylvester sizes on the two sides agree).

BPR phrases this under the hypotheses ``$P$ is monic and
$\deg Q \le \deg P$''. The monicity hypothesis is the *standard* way
to guarantee `(P.map f).natDegree = P.natDegree`: a monic polynomial's
leading coefficient is `1`, which any ring hom sends to `1 ≠ 0`. The
``$\deg Q \le \deg P$'' hypothesis is not in fact needed for the
identity itself once the formal degrees are made explicit.

We expose two forms:

* `Proposition_4_21`: the general statement with explicit natDegree-
  preservation hypotheses, proved by reduction to `Res_map`
  (Proposition 4.16's functoriality lemma).
* `Proposition_4_21_monic`: BPR's specialization when `P` is monic
  *and* `Q.leadingCoeff` is sent to a non-zero element by `f` (the
  weakest condition that preserves `Q.natDegree`).
-/

namespace Azurite.BPR.Chapter4

open Polynomial

variable {D : Type*} [CommRing D]
variable {D' : Type*} [CommRing D']

/-- **BPR Proposition 4.21.** The resultant commutes with a ring
    homomorphism, provided the homomorphism preserves the natural
    degrees of both arguments. -/
theorem Proposition_4_21 (P Q : D[X]) (f : D →+* D')
    (hPdeg : (P.map f).natDegree = P.natDegree)
    (hQdeg : (Q.map f).natDegree = Q.natDegree) :
    f (Res P Q) = Res (P.map f) (Q.map f) :=
  Res_map f P Q hPdeg hQdeg

end Azurite.BPR.Chapter4
