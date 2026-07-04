import Mathlib.RingTheory.Polynomial.Content

/-!
# BPR Lemma 10.16 (Gauss): products of primitive polynomials are primitive

`lemma_10_16`: for `P₁, P₂ ∈ ℤ[X]` with `cont(P₁) = cont(P₂) = 1`,
`cont(P₁·P₂) = 1`.

BPR's proof reduces modulo an arbitrary prime `p`: the reductions of `P₁`
and `P₂` are nonzero in the integral domain `𝔽_p[X]`, so their product is
too, whence no prime divides `cont(P₁·P₂)`.

The formalization invokes Mathlib's Gauss lemma in its full multiplicative
form, `Polynomial.content_mul : cont(P·Q) = cont(P)·cont(Q)` (valid over any
normalized GCD monoid, not just `ℤ`), of which the statement is the
primitive-polynomial case.
-/

namespace Azurite.BPR

open Polynomial

/-- **BPR Lemma 10.16.** If `cont(P₁) = cont(P₂) = 1`, then
`cont(P₁·P₂) = 1`. -/
theorem lemma_10_16 {P₁ P₂ : ℤ[X]} (h₁ : P₁.content = 1) (h₂ : P₂.content = 1) :
    (P₁ * P₂).content = 1 := by
  rw [Polynomial.content_mul, h₁, h₂, mul_one]

end Azurite.BPR
