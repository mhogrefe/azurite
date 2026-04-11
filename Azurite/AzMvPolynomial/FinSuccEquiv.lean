import Azurite.AzMvPolynomial.Eval2
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

end Azurite
