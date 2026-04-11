import Azurite.AzMvPolynomial.Equiv.SumAlgEquiv
import Azurite.AzMvPolynomial.Equiv.RenameHom

/-!
# `commAlgEquiv` for AzMvPolynomial

Swaps the outer and inner variables:

```
AzMvPolynomial m (AzMvPolynomial n R ord) ord
    ≃ₐ[R]  AzMvPolynomial n (AzMvPolynomial m R ord) ord
```

Built as the composition of
`sumAlgEquiv.symm` → `renameHom swap` → `sumAlgEquiv`,
where the middle `swap` is the `Fin (m+n) ≃ Fin (n+m)` obtained from
`Equiv.sumComm (Fin m) (Fin n)` via `finSumFinEquiv`.

The composition is assembled at the function level (rather than via
`AlgEquiv.trans`) to sidestep an instance-diamond between
`instAlgebraAzMvPolynomial` and `mvAlgebraOfAlgebra` on
`AzMvPolynomial (m+n) R ord`; the intermediate `rename` is a ring-hom
composition, so no algebra-instance unification is required.

This is the Fin-only counterpart of Mathlib's
`MvPolynomial.commAlgEquiv`.
-/

namespace Azurite

open AzMvPolynomial

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]

/-- The `Fin (m+n) ≃ Fin (n+m)` induced by swapping the summands. -/
def AzMvPolynomial.finAddSwap (m n : ℕ) : Fin (m+n) ≃ Fin (n+m) :=
  finSumFinEquiv.symm.trans
    ((Equiv.sumComm (Fin m) (Fin n)).trans finSumFinEquiv)

variable {m n : ℕ} {ord : MonomialOrder}

/-- The underlying function of `commAlgEquiv`: send a nested polynomial
    through `sumAlgEquiv.symm`, rename via `finAddSwap`, then through
    `sumAlgEquiv` in the swapped index order. -/
def AzMvPolynomial.commEquivFun
    (p : AzMvPolynomial m (AzMvPolynomial n R ord) ord) :
    AzMvPolynomial n (AzMvPolynomial m R ord) ord :=
  (AzMvPolynomial.sumAlgEquiv (R := R) (m := n) (n := m) (ord := ord))
    ((AzMvPolynomial.renameHom (R := R) (ord := ord)
        (AzMvPolynomial.finAddSwap m n))
      ((AzMvPolynomial.sumAlgEquiv (R := R) (m := m) (n := n) (ord := ord)).symm
        p))

/-- Inverse direction of `commEquivFun`. -/
def AzMvPolynomial.commEquivInv
    (q : AzMvPolynomial n (AzMvPolynomial m R ord) ord) :
    AzMvPolynomial m (AzMvPolynomial n R ord) ord :=
  (AzMvPolynomial.sumAlgEquiv (R := R) (m := m) (n := n) (ord := ord))
    ((AzMvPolynomial.renameHom (R := R) (ord := ord)
        (AzMvPolynomial.finAddSwap m n).symm)
      ((AzMvPolynomial.sumAlgEquiv (R := R) (m := n) (n := m) (ord := ord)).symm
        q))

/-- Commutativity `R`-algebra isomorphism between nested `AzMvPolynomial`
    rings: swapping which `m` / `n` variables are outer vs. inner. -/
def AzMvPolynomial.commAlgEquiv :
    AzMvPolynomial m (AzMvPolynomial n R ord) ord ≃ₐ[R]
      AzMvPolynomial n (AzMvPolynomial m R ord) ord where
  toFun := AzMvPolynomial.commEquivFun
  invFun := AzMvPolynomial.commEquivInv
  left_inv p := by
    unfold AzMvPolynomial.commEquivFun AzMvPolynomial.commEquivInv
    rw [AlgEquiv.symm_apply_apply,
        AzMvPolynomial.renameHom_comp_renameHom,
        show ((AzMvPolynomial.finAddSwap m n).symm ∘
                (AzMvPolynomial.finAddSwap m n) : Fin (m+n) → Fin (m+n)) = id
          from funext (AzMvPolynomial.finAddSwap m n).left_inv,
        AzMvPolynomial.renameHom_id, AlgEquiv.apply_symm_apply]
  right_inv q := by
    unfold AzMvPolynomial.commEquivFun AzMvPolynomial.commEquivInv
    rw [AlgEquiv.symm_apply_apply,
        AzMvPolynomial.renameHom_comp_renameHom,
        show ((AzMvPolynomial.finAddSwap m n) ∘
                (AzMvPolynomial.finAddSwap m n).symm : Fin (n+m) → Fin (n+m)) = id
          from funext (AzMvPolynomial.finAddSwap m n).right_inv,
        AzMvPolynomial.renameHom_id, AlgEquiv.apply_symm_apply]
  map_add' p q := by
    unfold AzMvPolynomial.commEquivFun
    rw [map_add, map_add, map_add]
  map_mul' p q := by
    unfold AzMvPolynomial.commEquivFun
    rw [map_mul, map_mul, map_mul]
  commutes' r := by
    unfold AzMvPolynomial.commEquivFun
    rw [AlgEquiv.commutes]
    show (AzMvPolynomial.sumAlgEquiv (R := R) (m := n) (n := m) (ord := ord))
          ((AzMvPolynomial.renameHom (R := R) (ord := ord)
              (AzMvPolynomial.finAddSwap m n))
            (AzMvPolynomial.C r : AzMvPolynomial (m+n) R ord)) = _
    rw [AzMvPolynomial.renameHom_C]
    exact AlgEquiv.commutes _ _

end Azurite
