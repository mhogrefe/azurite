import Azurite.AzMvPolynomial.Basic
import Azurite.AzMvPolynomial.Equiv.Algebra

/-!
# Generic Evaluation (`eval₂`, `aeval`) for AzMvPolynomial

Generalizes `bind₁`: where `bind₁` can only substitute variables with elements
of the same `AzMvPolynomial σ R ord` type, `eval₂` evaluates into any
commutative semiring `S` via a coefficient embedding `φ : R →+* S`.

`aeval` is the specialization to the case where `S` is an `R`-algebra — it
uses `algebraMap R S` as the coefficient embedding, matching Mathlib's
`MvPolynomial.aeval`.

## Implementation

Reuses the existing computable `MonicMonomial.eval` (which computes
`∏ᵢ f(vᵢ)^eᵢ` using `Finset.univ.prod`).

1. **`Monomial.eval₂`**: `φ(coeff) * MonicMonomial.eval f`
2. **`AzMvPolynomial.eval₂`**: `Σⱼ Monomial.eval₂(termⱼ)`
3. **`AzMvPolynomial.aeval`**: `eval₂ (algebraMap R S)`

## Relationship to `bind₁`

`bind₁` is the special case `eval₂ CHom` where `CHom : R →+* AzMvPolynomial σ R ord`
is the constant polynomial embedding. Equivalently, `bind₁ = aeval` with the
self-algebra `Algebra R (AzMvPolynomial σ R ord)`.
-/

namespace Azurite

open AzMvPolynomial MonicMonomial Monomial

variable {R : Type _} [CommSemiring R] [DecidableEq R]
  {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n] {ord : MonomialOrder}

/-- Evaluate a monomial at variable values `f : σ → S` using the coefficient
    embedding `φ : R →+* S`. Computes `φ(coeff) * ∏ᵢ f(vᵢ)^eᵢ` in `S`. -/
def Monomial.eval₂ {S : Type _} [CommSemiring S]
    (φ : R →+* S) (f : σ → S) (m : Monomial σ R ord) : S :=
  φ m.coeff.val * m.monic.eval f

/-- Evaluate a multivariate polynomial at variable values `f : σ → S` using the
    coefficient embedding `φ : R →+* S`. Computes `Σⱼ φ(cⱼ) * ∏ᵢ f(vᵢ)^eⱼᵢ` in `S`.

    Matches `MvPolynomial.eval₂` from Mathlib. Like `bind₁`, but more general:
    the target type `S` can be any commutative semiring, not just
    `AzMvPolynomial σ R ord`. -/
def AzMvPolynomial.eval₂ {S : Type _} [CommSemiring S]
    (φ : R →+* S) (f : σ → S) (p : AzMvPolynomial σ R ord) : S :=
  p.terms.foldl (init := 0) fun acc m => acc + m.eval₂ φ f

/-- Evaluate a multivariate polynomial as an `R`-algebra homomorphism:
    `aeval f p = eval₂ (algebraMap R S) f p`.

    Matches `MvPolynomial.aeval` from Mathlib. -/
def AzMvPolynomial.aeval {S : Type _} [CommSemiring S] [Algebra R S]
    (f : σ → S) (p : AzMvPolynomial σ R ord) : S :=
  p.eval₂ (algebraMap R S) f

end Azurite
