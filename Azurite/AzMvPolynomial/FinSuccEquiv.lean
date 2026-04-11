import Azurite.AzMvPolynomial.Eval2
import Azurite.AzMvPolynomial.Rename
import Azurite.AzMvPolynomial.Equiv.Algebra
import Azurite.AzPolynomial.Equiv.Algebra

/-!
# `finSuccEquiv` for AzMvPolynomial

Fin-only companion to `AzMvPolynomial.FinSuccEquiv`. Converts a polynomial
in `n + 1` variables (indexed by `Fin (n+1)`) into a univariate polynomial
whose coefficients are themselves polynomials in the remaining `n` variables:

```
AzMvPolynomial (n+1) R ord →  AzPolynomial (AzMvPolynomial n R ord)
```

The variable `Fin.0` is replaced by the outer `AzPolynomial.X`, and each
`Fin.succ k` is replaced by `AzPolynomial.C (AzMvPolynomial.X k)`.
-/

namespace Azurite

open AzMvPolynomial

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]

/-- Convert a polynomial in `n + 1` variables into a univariate polynomial
    whose coefficients are polynomials in the first `n` variables.

    Matches `MvPolynomial.finSuccEquiv` from Mathlib (forward direction). -/
def AzMvPolynomial.finSuccEquiv {n : ℕ} {ord : MonomialOrder}
    (p : AzMvPolynomial (n+1) R ord) :
    AzPolynomial (AzMvPolynomial n R ord) :=
  p.eval₂ (AzPolynomial.CHom.comp (AzMvPolynomial.CHom (n := n) (ord := ord)))
    (fun i => Fin.cases AzPolynomial.X
      (fun k => AzPolynomial.C (AzMvPolynomial.X (ord := ord) k)) i)

/-- Inverse direction of `finSuccEquiv`: convert a univariate polynomial whose
    coefficients are multivariate in `Fin n` into a multivariate polynomial in
    `Fin (n+1)`. The outer variable becomes `X 0`, and each inner variable `k`
    is shifted up to `Fin.succ k`.

    Implemented via Horner's method: `Σ_i cᵢ (X 0)^i` is computed as
    `c₀ + (X 0) · (c₁ + (X 0) · (c₂ + …))`, where each `cᵢ` is first renamed
    via `Fin.succ` into the `Fin (n+1)` variable space. -/
def AzMvPolynomial.finSuccEquivSymm {n : ℕ} {ord : MonomialOrder}
    (p : AzPolynomial (AzMvPolynomial n R ord)) :
    AzMvPolynomial (n+1) R ord :=
  p.coeffs.foldr (init := (0 : AzMvPolynomial (n+1) R ord))
    (fun c acc =>
      AzMvPolynomial.renameInjective c Fin.succ (Fin.succ_injective n) +
      acc * AzMvPolynomial.X (ord := ord) (0 : Fin (n+1)))

end Azurite
