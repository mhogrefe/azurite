import Azurite.AzMvPolynomial.Equiv.Rename
import Azurite.AzMvPolynomial.Equiv.Algebra
import Azurite.AzMvPolynomial.Equiv.AlgebraOfAlgebra

/-!
# Bundled ring-hom and alg-equiv forms of `rename`

Provides:

* `AzMvPolynomial.renameMonotoneHom` — wraps `renameMonotone` (strictly
  monotone `f`) as a bundled ring homomorphism. Used by `sumAlgEquiv`.
* `AzMvPolynomial.renameHom` — wraps the general `rename` (any `f`) as a
  bundled ring homomorphism.
* `AzMvPolynomial.renameAlgEquiv` — wraps `rename` along an `Equiv`
  `Fin n₁ ≃ Fin n₂` as a bundled `R`-algebra isomorphism. Used by
  `commAlgEquiv` for the middle swap step.

Ring-hom axioms are proved by transfer along the bridge theorems
(`toMvPoly_renameMonotone`, `toMvPoly_rename`) to `MvPolynomial.rename`.
-/

namespace Azurite

open AzMvPolynomial

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]
    {n₁ n₂ : ℕ} {ord : MonomialOrder}

/-- Bundled ring-hom form of `renameMonotone`. -/
noncomputable def AzMvPolynomial.renameMonotoneHom
    (f : Fin n₁ → Fin n₂) (hg : StrictMono f) :
    AzMvPolynomial n₁ R ord →+* AzMvPolynomial n₂ R ord where
  toFun p := p.renameMonotone f hg
  map_zero' := toMvPoly_injective (by
    rw [toMvPoly_renameMonotone,
        show (0 : AzMvPolynomial n₁ R ord).toMvPoly = (0 : MvPolynomial (Fin n₁) R)
          from toMvPoly_zero,
        map_zero,
        show (0 : AzMvPolynomial n₂ R ord).toMvPoly = (0 : MvPolynomial (Fin n₂) R)
          from toMvPoly_zero])
  map_one' := toMvPoly_injective (by
    rw [toMvPoly_renameMonotone,
        show (1 : AzMvPolynomial n₁ R ord).toMvPoly = (1 : MvPolynomial (Fin n₁) R)
          from toMvPoly_one,
        map_one,
        show (1 : AzMvPolynomial n₂ R ord).toMvPoly = (1 : MvPolynomial (Fin n₂) R)
          from toMvPoly_one])
  map_add' p q := toMvPoly_injective (by
    rw [toMvPoly_renameMonotone, toMvPoly_add, map_add, toMvPoly_add,
        toMvPoly_renameMonotone, toMvPoly_renameMonotone])
  map_mul' p q := toMvPoly_injective (by
    rw [toMvPoly_renameMonotone, toMvPoly_mul, map_mul, toMvPoly_mul,
        toMvPoly_renameMonotone, toMvPoly_renameMonotone])

/-- `renameMonotoneHom` evaluated on `C r` equals `C r`. -/
@[simp] theorem AzMvPolynomial.renameMonotoneHom_C
    (f : Fin n₁ → Fin n₂) (hg : StrictMono f) (r : R) :
    (AzMvPolynomial.renameMonotoneHom (ord := ord) f hg)
        (AzMvPolynomial.C r : AzMvPolynomial n₁ R ord) =
      (AzMvPolynomial.C r : AzMvPolynomial n₂ R ord) :=
  toMvPoly_injective (by
    show (((AzMvPolynomial.C r : AzMvPolynomial n₁ R ord).renameMonotone f hg)).toMvPoly
        = (AzMvPolynomial.C r : AzMvPolynomial n₂ R ord).toMvPoly
    rw [toMvPoly_renameMonotone, toMvPoly_C, toMvPoly_C, MvPolynomial.rename_C])

/-- `renameMonotoneHom` evaluated on `X i` equals `X (f i)`. -/
@[simp] theorem AzMvPolynomial.renameMonotoneHom_X
    (f : Fin n₁ → Fin n₂) (hg : StrictMono f) (i : Fin n₁) :
    (AzMvPolynomial.renameMonotoneHom (ord := ord) f hg)
        (AzMvPolynomial.X i : AzMvPolynomial n₁ R ord) =
      (AzMvPolynomial.X (f i) : AzMvPolynomial n₂ R ord) :=
  toMvPoly_injective (by
    show (((AzMvPolynomial.X i : AzMvPolynomial n₁ R ord).renameMonotone f hg)).toMvPoly
        = (AzMvPolynomial.X (f i) : AzMvPolynomial n₂ R ord).toMvPoly
    rw [toMvPoly_renameMonotone, toMvPoly_X, toMvPoly_X, MvPolynomial.rename_X])

/-- Bundled ring-hom form of the general `rename` (any `f : Fin n₁ → Fin n₂`).
    Non-injective `f` may merge exponents; ring-hom axioms are still valid
    because `MvPolynomial.rename` is always a ring homomorphism. -/
noncomputable def AzMvPolynomial.renameHom
    (f : Fin n₁ → Fin n₂) :
    AzMvPolynomial n₁ R ord →+* AzMvPolynomial n₂ R ord where
  toFun p := p.rename f ord
  map_zero' := toMvPoly_injective (by
    rw [toMvPoly_rename,
        show (0 : AzMvPolynomial n₁ R ord).toMvPoly = (0 : MvPolynomial (Fin n₁) R)
          from toMvPoly_zero,
        map_zero,
        show (0 : AzMvPolynomial n₂ R ord).toMvPoly = (0 : MvPolynomial (Fin n₂) R)
          from toMvPoly_zero])
  map_one' := toMvPoly_injective (by
    rw [toMvPoly_rename,
        show (1 : AzMvPolynomial n₁ R ord).toMvPoly = (1 : MvPolynomial (Fin n₁) R)
          from toMvPoly_one,
        map_one,
        show (1 : AzMvPolynomial n₂ R ord).toMvPoly = (1 : MvPolynomial (Fin n₂) R)
          from toMvPoly_one])
  map_add' p q := toMvPoly_injective (by
    rw [toMvPoly_rename, toMvPoly_add, map_add, toMvPoly_add,
        toMvPoly_rename, toMvPoly_rename])
  map_mul' p q := toMvPoly_injective (by
    rw [toMvPoly_rename, toMvPoly_mul, map_mul, toMvPoly_mul,
        toMvPoly_rename, toMvPoly_rename])

@[simp] theorem AzMvPolynomial.renameHom_C
    (f : Fin n₁ → Fin n₂) (r : R) :
    (AzMvPolynomial.renameHom (ord := ord) f)
        (AzMvPolynomial.C r : AzMvPolynomial n₁ R ord) =
      (AzMvPolynomial.C r : AzMvPolynomial n₂ R ord) :=
  toMvPoly_injective (by
    show (((AzMvPolynomial.C r : AzMvPolynomial n₁ R ord).rename f ord)).toMvPoly
        = (AzMvPolynomial.C r : AzMvPolynomial n₂ R ord).toMvPoly
    rw [toMvPoly_rename, toMvPoly_C, toMvPoly_C, MvPolynomial.rename_C])

@[simp] theorem AzMvPolynomial.renameHom_X
    (f : Fin n₁ → Fin n₂) (i : Fin n₁) :
    (AzMvPolynomial.renameHom (ord := ord) f)
        (AzMvPolynomial.X i : AzMvPolynomial n₁ R ord) =
      (AzMvPolynomial.X (f i) : AzMvPolynomial n₂ R ord) :=
  toMvPoly_injective (by
    show (((AzMvPolynomial.X i : AzMvPolynomial n₁ R ord).rename f ord)).toMvPoly
        = (AzMvPolynomial.X (f i) : AzMvPolynomial n₂ R ord).toMvPoly
    rw [toMvPoly_rename, toMvPoly_X, toMvPoly_X, MvPolynomial.rename_X])

/-- Composition of `renameHom`s composes the underlying functions. -/
theorem AzMvPolynomial.renameHom_comp_renameHom {n₃ : ℕ}
    (f : Fin n₁ → Fin n₂) (g : Fin n₂ → Fin n₃) (p : AzMvPolynomial n₁ R ord) :
    (AzMvPolynomial.renameHom (ord := ord) g)
        ((AzMvPolynomial.renameHom (ord := ord) f) p) =
      (AzMvPolynomial.renameHom (ord := ord) (g ∘ f)) p :=
  toMvPoly_injective (by
    show ((p.rename f ord).rename g ord).toMvPoly
        = (p.rename (g ∘ f) ord).toMvPoly
    rw [toMvPoly_rename, toMvPoly_rename, toMvPoly_rename,
        MvPolynomial.rename_rename])

/-- `renameHom id` is the identity. -/
theorem AzMvPolynomial.renameHom_id (p : AzMvPolynomial n₁ R ord) :
    (AzMvPolynomial.renameHom (ord := ord) (id : Fin n₁ → Fin n₁)) p = p :=
  toMvPoly_injective (by
    show (p.rename id ord).toMvPoly = p.toMvPoly
    rw [toMvPoly_rename, MvPolynomial.rename_id]
    rfl)

/-- Given an equivalence `e : Fin n₁ ≃ Fin n₂`, renaming along `e` is an
    `R`-algebra isomorphism of `AzMvPolynomial`. -/
noncomputable def AzMvPolynomial.renameAlgEquiv (e : Fin n₁ ≃ Fin n₂) :
    AzMvPolynomial n₁ R ord ≃ₐ[R] AzMvPolynomial n₂ R ord where
  toFun p := (AzMvPolynomial.renameHom (ord := ord) e) p
  invFun p := (AzMvPolynomial.renameHom (ord := ord) e.symm) p
  left_inv p := by
    show (AzMvPolynomial.renameHom (ord := ord) e.symm)
          ((AzMvPolynomial.renameHom (ord := ord) e) p) = p
    rw [AzMvPolynomial.renameHom_comp_renameHom]
    show (AzMvPolynomial.renameHom (ord := ord) (e.symm ∘ e)) p = p
    rw [show (e.symm ∘ e : Fin n₁ → Fin n₁) = id from funext e.left_inv,
        AzMvPolynomial.renameHom_id]
  right_inv p := by
    show (AzMvPolynomial.renameHom (ord := ord) e)
          ((AzMvPolynomial.renameHom (ord := ord) e.symm) p) = p
    rw [AzMvPolynomial.renameHom_comp_renameHom]
    show (AzMvPolynomial.renameHom (ord := ord) (e ∘ e.symm)) p = p
    rw [show (e ∘ e.symm : Fin n₂ → Fin n₂) = id from funext e.right_inv,
        AzMvPolynomial.renameHom_id]
  map_add' p q := (AzMvPolynomial.renameHom (ord := ord) e).map_add p q
  map_mul' p q := (AzMvPolynomial.renameHom (ord := ord) e).map_mul p q
  commutes' r := AzMvPolynomial.renameHom_C (ord := ord) (e : Fin n₁ → Fin n₂) r

end Azurite
