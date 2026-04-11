import Azurite.AzMvPolynomial.Eval2
import Azurite.AzMvPolynomial.Rename
import Azurite.AzPolynomial.Equiv.Algebra

/-!
# `finSuccEquiv` for AzMvPolynomial

Matches `MvPolynomial.finSuccEquiv` from Mathlib. Converts a polynomial
in `n + 1` variables (indexed by `Fin (n+1)`) into a univariate polynomial
whose coefficients are themselves polynomials in the remaining `n` variables:

```
AzMvPolynomial (Fin (n+1)) R ord  →  AzPolynomial (AzMvPolynomial (Fin n) R ord)
```

The variable `Fin.0` is replaced by the outer `AzPolynomial.X`, and each
`Fin.succ k` is replaced by `AzPolynomial.C (AzMvPolynomial.X k)` — the
inner variable `k` embedded as a constant of the outer polynomial.

Built on `eval₂` with the composite coefficient embedding
`AzPolynomial.CHom.comp AzMvPolynomial.CHom : R →+* AzPolynomial (AzMvPolynomial (Fin n) R ord)`.

This is the forward direction only; bundling as an `AlgEquiv` is left to
a future equivalence-proof module.
-/

namespace Azurite

open AzMvPolynomial

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]

/-- Convert a polynomial in `n + 1` variables into a univariate polynomial
    whose coefficients are polynomials in the first `n` variables.

    Matches `MvPolynomial.finSuccEquiv` from Mathlib (forward direction). -/
def AzMvPolynomial.finSuccEquiv {n : ℕ} {ord : MonomialOrder}
    (p : AzMvPolynomial (Fin (n+1)) R ord) :
    AzPolynomial (AzMvPolynomial (Fin n) R ord) :=
  p.eval₂ (AzPolynomial.CHom.comp (AzMvPolynomial.CHom (σ := Fin n) (ord := ord)))
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
    (p : AzPolynomial (AzMvPolynomial (Fin n) R ord)) :
    AzMvPolynomial (Fin (n+1)) R ord :=
  p.coeffs.foldr (init := (0 : AzMvPolynomial (Fin (n+1)) R ord))
    (fun c acc =>
      AzMvPolynomial.renameInjective c Fin.succ (Fin.succ_injective n) +
      acc * AzMvPolynomial.X (ord := ord) (0 : Fin (n+1)))

end Azurite
