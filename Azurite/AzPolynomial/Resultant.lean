import Azurite.AzPolynomial.SignedSubresultant

/-!
# BPR Exercise 8.2: the resultant via the signed subresultant algorithm

`signedSubresultant P Q` (Algorithm 8.21) requires `deg Q < deg P`, and its bottom coefficient
`s₀` satisfies `Res(P, Q) = ε_p · s₀` (Notation 4.27).  This file packages a resultant algorithm
on top of it:

* `resultantGt P Q` handles `deg Q < deg P`: when `deg Q = 0` (constant `Q`) the resultant is
  `(Q₀)^{deg P}`; otherwise it is `ε_p · s₀`, with `s₀` read off as the head of the coefficient
  array returned by `signedSubresultant`.
* `resultant P Q` reduces the general case to `resultantGt`: it swaps when `deg P < deg Q`
  (`Res(P,Q) = (-1)^{pq} Res(Q,P)`), and when `deg P = deg Q` it follows BPR's hint, replacing `Q`
  by `Q₁ = a_p·Q − b_p·P` (degree `< deg P`) and dividing by `a_p^{deg Q₁}`
  (`a_p^{deg Q₁}·Res(P,Q) = Res(P,Q₁)`).
-/

namespace Azurite.AzPolynomial

variable {R : Type _} [CommRing R] [DecidableEq R] [Azurite.ExactDiv R]

/-- Resultant when `deg Q < deg P`: the constant case `(Q₀)^{deg P}`, otherwise `ε_p · s₀` where
    `s₀` is the bottom signed-subresultant coefficient (head of `(signedSubresultant P Q).2`). -/
def resultantGt (P Q : AzPolynomial R) : R :=
  if Q.natDegree = 0 then Q.coeff 0 ^ P.natDegree
  else epsilonSign P.natDegree * ((signedSubresultant P Q).2.toList.headD 0)

/-- **BPR Exercise 8.2.** The resultant `Res(P, Q)`, computed via `signedSubresultant`.
    Reduces `deg P < deg Q` by swapping and `deg P = deg Q` by the `Q₁` degree reduction. -/
def resultant (P Q : AzPolynomial R) : R :=
  if Q.natDegree < P.natDegree then resultantGt P Q
  else if P.natDegree < Q.natDegree then
    (-1 : R) ^ (P.natDegree * Q.natDegree) * resultantGt Q P
  else if P.natDegree = 0 then 1
  else
    Azurite.ExactDiv.exactDiv
      (resultantGt P (P.leadingCoeff • Q - Q.leadingCoeff • P))
      (P.leadingCoeff ^ (P.leadingCoeff • Q - Q.leadingCoeff • P).natDegree)

end Azurite.AzPolynomial
