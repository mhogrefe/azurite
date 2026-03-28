import Azurite.AzMvPolynomial.Pow
import Azurite.AzMvPolynomial.Mul
import Azurite.AzMvPolynomial.SMul
import Azurite.AzMvPolynomial.Add

/-!
# Variable Substitution (bind₁) for AzMvPolynomial

Implements `bind₁`, the multivariate polynomial analogue of composition:
given `f : σ → AzMvPolynomial σ R ord`, substitute `f(v)` for each variable `v`.

Matches `MvPolynomial.bind₁` from Mathlib, which is defined as `aeval f`.

## Implementation

Built bottom-up:

1. **`MonicMonomial.bind₁`**: `∏ᵢ f(varᵢ) ^ exponentᵢ`
2. **`Monomial.bind₁`**: `coeff • MonicMonomial.bind₁`
3. **`AzMvPolynomial.bind₁`**: `Σⱼ Monomial.bind₁(termⱼ)`

Uses the existing `AzMvPolynomial.pow` (with single-monomial fast path) for
each `f(varᵢ) ^ eᵢ`, and existing `*`, `+`, `•` for combining.
-/

namespace Azurite

open AzMvPolynomial MonicMonomial Monomial

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]
  {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n] {ord : MonomialOrder}

/-- Auxiliary for `MonicMonomial.bind₁`: fold over variable indices `i = 0, ..., n-1`,
    accumulating `acc * f(varᵢ)^eᵢ`. -/
def monicBind₁Aux (m : MonicMonomial σ ord)
    (f : σ → AzMvPolynomial σ R ord) (i : ℕ) (acc : AzMvPolynomial σ R ord) :
    AzMvPolynomial σ R ord :=
  if h : i < n then
    let e := m.exponents[i]
    monicBind₁Aux m f (i + 1) (acc * (f (Var.ofFin ⟨i, h⟩)).pow e)
  else acc
termination_by n - i

/-- Substitute polynomials for variables in a monic monomial:
    computes `∏ᵢ f(varᵢ) ^ exponentᵢ`. -/
def MonicMonomial.bind₁ (m : MonicMonomial σ ord)
    (f : σ → AzMvPolynomial σ R ord) : AzMvPolynomial σ R ord :=
  monicBind₁Aux m f 0 1

/-- Substitute polynomials for variables in a monomial:
    computes `coeff • ∏ᵢ f(varᵢ) ^ exponentᵢ`. -/
def Monomial.bind₁ (m : Monomial σ R ord)
    (f : σ → AzMvPolynomial σ R ord) : AzMvPolynomial σ R ord :=
  m.coeff.val • m.monic.bind₁ f

/-- Substitute polynomials for variables in a multivariate polynomial.
    Computes `Σⱼ coeff_j • ∏ᵢ f(varᵢ) ^ exponent_ji`.

    Matches `MvPolynomial.bind₁` from Mathlib, which is `aeval f`. -/
def AzMvPolynomial.bind₁ (p : AzMvPolynomial σ R ord)
    (f : σ → AzMvPolynomial σ R ord) : AzMvPolynomial σ R ord :=
  p.terms.foldl (init := 0) fun acc m => acc + m.bind₁ f

end Azurite
