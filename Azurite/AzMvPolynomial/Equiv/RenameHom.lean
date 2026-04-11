import Azurite.AzMvPolynomial.Equiv.Rename
import Azurite.AzMvPolynomial.Equiv.Algebra

/-!
# Bundled ring-hom form of `renameMonotone`

Provides `AzMvPolynomial.renameMonotoneHom`, which wraps `renameMonotone`
(renaming variables along a strictly monotone `f : Fin n₁ → Fin n₂`) as a
bundled ring homomorphism. Ring-hom axioms are proved by transfer along the
`toMvPoly_renameMonotone` bridge to `MvPolynomial.rename`.

Used by `sumAlgEquiv`, where the reverse direction passes this ring hom as
the coefficient embedding of `eval₂`.
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

end Azurite
