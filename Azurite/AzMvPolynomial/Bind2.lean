import Azurite.AzMvPolynomial.Mul
import Azurite.AzMvPolynomial.Add

/-!
# Coefficient Substitution (bind₂) for AzMvPolynomial

Implements `bind₂`, the operation that replaces each coefficient `r` in a polynomial
with `f(r)`, while keeping the variable structure unchanged.

Matches `MvPolynomial.bind₂` from Mathlib, which is defined as `eval₂Hom f X`.

## Key property

For a monomial `r · x^d`:
  `bind₂ f (r · x^d) = f(r) * x^d`

The variable type `σ` stays the same; the coefficient ring changes from `R` to `S`.
-/

namespace Azurite

open AzMvPolynomial MonicMonomial Monomial

variable {R S : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]
  [CommSemiring S] [NoZeroDivisors S] [DecidableEq S]
  {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n] {ord : MonomialOrder}

/-- Create a single-term polynomial from a monic monomial with coefficient 1 in `S`.
    Returns 0 if `1 = 0` in `S` (trivial ring). -/
def MonicMonomial.toAzMvPoly [DecidableEq S]
    (m : MonicMonomial σ ord) : AzMvPolynomial σ S ord :=
  if h : (1 : S) = 0 then 0
  else AzMvPolynomial.ofMonomial ⟨⟨1, h⟩, m⟩

/-- Apply `bind₂` to a single monomial: replace its coefficient `c` with `f(c)`,
    then multiply by the monic monomial `m` (viewed as a polynomial with coeff 1). -/
def Monomial.bind₂ (f : R → AzMvPolynomial σ S ord)
    (m : Monomial σ R ord) : AzMvPolynomial σ S ord :=
  f m.coeff.val * m.monic.toAzMvPoly

/-- Substitute coefficients in a multivariate polynomial using `f`.
    For each term `c · x^d`, computes `f(c) * x^d` and sums the results.

    Matches `MvPolynomial.bind₂` from Mathlib, which is `eval₂Hom f X`. -/
def AzMvPolynomial.bind₂ (f : R → AzMvPolynomial σ S ord)
    (p : AzMvPolynomial σ R ord) : AzMvPolynomial σ S ord :=
  p.terms.foldl (init := 0) fun acc m => acc + m.bind₂ f

end Azurite
