import Mathlib.Data.Nat.Size
import Mathlib.Algebra.MvPolynomial.Basic

/-!
# BPR §8.1: Bitsize of a sum of two multivariate polynomials

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*,
> Springer 2006, §8.1.

An unnumbered BPR fact: if every coefficient of two multivariate
polynomials `P, Q ∈ ℤ[X₁, …, Xₖ]` has bitsize `≤ τ`, then every
coefficient of `P + Q` has bitsize `≤ τ + 1`.

Proof: for each monomial `m`, `coeff m (P + Q) = coeff m P + coeff m Q`,
and `|a + b| ≤ |a| + |b| < 2^τ + 2^τ = 2^{τ + 1}`.
-/

namespace Azurite.BPR

/-- `bitsize(a + b) ≤ τ + 1` when `bitsize a ≤ τ` and `bitsize b ≤ τ`. -/
theorem Int.size_add_le (a b : ℤ) (τ : ℕ)
    (ha : a.natAbs.size ≤ τ) (hb : b.natAbs.size ≤ τ) :
    (a + b).natAbs.size ≤ τ + 1 := by
  rw [Nat.size_le] at ha hb ⊢
  have hab : (a + b).natAbs ≤ a.natAbs + b.natAbs := Int.natAbs_add_le a b
  have : 2 ^ τ + 2 ^ τ = 2 ^ (τ + 1) := by rw [pow_succ]; omega
  omega

/-- **BPR §8.1 (unnumbered lemma).** Adding two multivariate polynomials
    over `ℤ` whose coefficient bitsizes are bounded by `τ` produces a
    polynomial whose coefficient bitsizes are bounded by `τ + 1`. -/
theorem MvPolynomial.bitsize_coeff_add_le {σ : Type _}
    {P Q : MvPolynomial σ ℤ} {τ : ℕ}
    (hP : ∀ m, (P.coeff m).natAbs.size ≤ τ)
    (hQ : ∀ m, (Q.coeff m).natAbs.size ≤ τ) :
    ∀ m, ((P + Q).coeff m).natAbs.size ≤ τ + 1 := by
  intro m
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  exact Int.size_add_le _ _ τ (hP m) (hQ m)

end Azurite.BPR
