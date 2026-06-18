import Azurite.BasuPollackRoy.Chapter4.Section4_4.IdealOfPolynomials
import Mathlib.RingTheory.MvPolynomial.MonomialOrder

/-!
# BPR Definition 4.67: Gröbner basis

A **Gröbner basis** of an ideal `I ⊆ K[X₁, …, X_k]` for the monomial ordering `m` is a finite
set `𝒢 ⊆ I` such that:
* the leading monomial of any element of `I` is a multiple of the leading monomial of some
  element of `𝒢`;
* the leading monomial of any element of `𝒢` is not a multiple of the leading monomial of
  another element of `𝒢`.

Here `lmon(P) = m.degree P` (the leading-monomial exponent), and "`X^α` is a multiple of
`X^β`" means `X^β ∣ X^α`, i.e. `β ≤ α` componentwise (`def:monomial-order`).

A **Gröbner basis** for `m` is a finite set `𝒢` that is a Gröbner basis of the ideal it
generates, `Ideal(𝒢, K)`.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {k : ℕ} {K : Type*} [Field K]

/-- **BPR Definition 4.67.** `𝒢` is a *Gröbner basis of the ideal `I`* for the monomial
ordering `m` if `𝒢 ⊆ I`, the leading monomial of every nonzero element of `I` is a multiple of
the leading monomial of some element of `𝒢`, and no leading monomial of an element of `𝒢` is a
multiple of the leading monomial of another. (Divisibility of monomials `X^β ∣ X^α` is the
componentwise order `β ≤ α` on exponents.) -/
def IsGrobnerBasisOf (m : MonomialOrder (Fin k)) (I : Ideal (MvPolynomial (Fin k) K))
    (𝒢 : Finset (MvPolynomial (Fin k) K)) : Prop :=
  (∀ G ∈ 𝒢, G ∈ I) ∧
  (∀ P ∈ I, P ≠ 0 → ∃ G ∈ 𝒢, G ≠ 0 ∧ m.degree G ≤ m.degree P) ∧
  (∀ G ∈ 𝒢, ∀ G' ∈ 𝒢, G ≠ G' → ¬ m.degree G' ≤ m.degree G)

/-- **BPR Definition 4.67 (second part).** A *Gröbner basis* for the monomial ordering `m` is a
finite set `𝒢 ⊆ K[X₁, …, X_k]` which is a Gröbner basis of the ideal `Ideal(𝒢, K)` it
generates. -/
def IsGrobnerBasis (m : MonomialOrder (Fin k)) (𝒢 : Finset (MvPolynomial (Fin k) K)) : Prop :=
  IsGrobnerBasisOf m (idealOfPolys 𝒢) 𝒢

end Azurite.BPR.Chapter4
