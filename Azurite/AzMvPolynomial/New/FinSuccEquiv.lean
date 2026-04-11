import Azurite.AzMvPolynomial.New.Eval2
import Azurite.AzMvPolynomial.New.Rename
import Azurite.AzMvPolynomial.New.Equiv.Algebra
import Azurite.AzPolynomial.Equiv.Algebra

/-!
# `finSuccEquiv` for AzMvPolynomialNew

Fin-only companion to `AzMvPolynomial.FinSuccEquiv`. Converts a polynomial
in `n + 1` variables (indexed by `Fin (n+1)`) into a univariate polynomial
whose coefficients are themselves polynomials in the remaining `n` variables:

```
AzMvPolynomialNew (n+1) R ord  →  AzPolynomial (AzMvPolynomialNew n R ord)
```

The variable `Fin.0` is replaced by the outer `AzPolynomial.X`, and each
`Fin.succ k` is replaced by `AzPolynomial.C (AzMvPolynomialNew.X k)`.
-/

namespace Azurite

open AzMvPolynomialNew

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]

/-- Convert a polynomial in `n + 1` variables into a univariate polynomial
    whose coefficients are polynomials in the first `n` variables.

    Matches `MvPolynomial.finSuccEquiv` from Mathlib (forward direction). -/
def AzMvPolynomialNew.finSuccEquiv {n : ℕ} {ord : MonomialOrder}
    (p : AzMvPolynomialNew (n+1) R ord) :
    AzPolynomial (AzMvPolynomialNew n R ord) :=
  p.eval₂ (AzPolynomial.CHom.comp (AzMvPolynomialNew.CHom (n := n) (ord := ord)))
    (fun i => Fin.cases AzPolynomial.X
      (fun k => AzPolynomial.C (AzMvPolynomialNew.X (ord := ord) k)) i)

/-- Inverse direction of `finSuccEquiv`: convert a univariate polynomial whose
    coefficients are multivariate in `Fin n` into a multivariate polynomial in
    `Fin (n+1)`. The outer variable becomes `X 0`, and each inner variable `k`
    is shifted up to `Fin.succ k`.

    Implemented via Horner's method: `Σ_i cᵢ (X 0)^i` is computed as
    `c₀ + (X 0) · (c₁ + (X 0) · (c₂ + …))`, where each `cᵢ` is first renamed
    via `Fin.succ` into the `Fin (n+1)` variable space. -/
def AzMvPolynomialNew.finSuccEquivSymm {n : ℕ} {ord : MonomialOrder}
    (p : AzPolynomial (AzMvPolynomialNew n R ord)) :
    AzMvPolynomialNew (n+1) R ord :=
  p.coeffs.foldr (init := (0 : AzMvPolynomialNew (n+1) R ord))
    (fun c acc =>
      AzMvPolynomialNew.renameInjective c Fin.succ (Fin.succ_injective n) +
      acc * AzMvPolynomialNew.X (ord := ord) (0 : Fin (n+1)))

end Azurite
