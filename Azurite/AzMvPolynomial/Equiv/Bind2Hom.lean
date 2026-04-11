import Azurite.AzMvPolynomial.Equiv.Bind2
import Azurite.AzMvPolynomial.Equiv.Algebra
import Azurite.AzMvPolynomial.Equiv.AlgebraOfAlgebra

/-!
# Bundled ring-hom form of `AzMvPolynomial.bind₂`

Provides `AzMvPolynomial.bind₂Hom`: given a ring homomorphism
`f : R →+* AzMvPolynomial n S ord`, the map `p ↦ p.bind₂ f` is a ring
homomorphism `AzMvPolynomial n R ord →+* AzMvPolynomial n S ord`.

Fin-only counterpart of Mathlib's `MvPolynomial.bind₂`, which is already
bundled as `MvPolynomial σ R →+* MvPolynomial σ S` (for `f : R →+* MvPolynomial σ S`).
-/

namespace Azurite

open AzMvPolynomial

variable {R S : Type _}
    [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]
    [CommSemiring S] [NoZeroDivisors S] [DecidableEq S]
    {n : ℕ} {ord : MonomialOrder}

omit [NoZeroDivisors R] [DecidableEq R] in
/-- Ring-hom-friendly bridge: for a ring hom `f : R →+* AzMvPolynomial n S ord`,
    the composition `toMvPoly ∘ (·.bind₂ f)` agrees with
    `MvPolynomial.bind₂ (toMvPolyHom.comp f) ∘ toMvPoly`. -/
private theorem toMvPoly_bind₂_ringHom (f : R →+* AzMvPolynomial n S ord)
    (p : AzMvPolynomial n R ord) :
    (p.bind₂ (fun r => f r)).toMvPoly =
      (MvPolynomial.bind₂
        ((AzMvPolynomial.toMvPolyHom : AzMvPolynomial n S ord →+*
            MvPolynomial (Fin n) S).comp f)) p.toMvPoly := by
  have hfun : (fun r => (f r : AzMvPolynomial n S ord)) =
      (fun r => AzMvPolynomial.ofMvPoly
        (((AzMvPolynomial.toMvPolyHom : AzMvPolynomial n S ord →+*
            MvPolynomial (Fin n) S).comp f) r)) := by
    funext r
    show f r = AzMvPolynomial.ofMvPoly (AzMvPolynomial.toMvPoly (f r))
    exact (ofMvPoly_toMvPoly (f r)).symm
  rw [hfun, toMvPoly_bind₂]

/-- Bundled ring-hom form of `AzMvPolynomial.bind₂`. -/
def AzMvPolynomial.bind₂Hom (f : R →+* AzMvPolynomial n S ord) :
    AzMvPolynomial n R ord →+* AzMvPolynomial n S ord where
  toFun p := p.bind₂ (fun r => f r)
  map_zero' := toMvPoly_injective (by
    rw [toMvPoly_bind₂_ringHom,
        show (0 : AzMvPolynomial n R ord).toMvPoly = (0 : MvPolynomial (Fin n) R)
          from toMvPoly_zero,
        map_zero,
        show (0 : AzMvPolynomial n S ord).toMvPoly = (0 : MvPolynomial (Fin n) S)
          from toMvPoly_zero])
  map_one' := toMvPoly_injective (by
    rw [toMvPoly_bind₂_ringHom,
        show (1 : AzMvPolynomial n R ord).toMvPoly = (1 : MvPolynomial (Fin n) R)
          from toMvPoly_one,
        map_one,
        show (1 : AzMvPolynomial n S ord).toMvPoly = (1 : MvPolynomial (Fin n) S)
          from toMvPoly_one])
  map_add' p q := toMvPoly_injective (by
    rw [toMvPoly_bind₂_ringHom, toMvPoly_add, map_add, toMvPoly_add,
        toMvPoly_bind₂_ringHom, toMvPoly_bind₂_ringHom])
  map_mul' p q := toMvPoly_injective (by
    rw [toMvPoly_bind₂_ringHom, toMvPoly_mul, map_mul, toMvPoly_mul,
        toMvPoly_bind₂_ringHom, toMvPoly_bind₂_ringHom])

@[simp] theorem AzMvPolynomial.bind₂Hom_C
    (f : R →+* AzMvPolynomial n S ord) (r : R) :
    (AzMvPolynomial.bind₂Hom f) (AzMvPolynomial.C r : AzMvPolynomial n R ord) =
      f r :=
  toMvPoly_injective (by
    show ((AzMvPolynomial.C r : AzMvPolynomial n R ord).bind₂
          (fun r => (f r : AzMvPolynomial n S ord))).toMvPoly = (f r).toMvPoly
    rw [toMvPoly_bind₂_ringHom, toMvPoly_C, MvPolynomial.bind₂_C_right,
        RingHom.comp_apply]
    rfl)

@[simp] theorem AzMvPolynomial.bind₂Hom_X
    (f : R →+* AzMvPolynomial n S ord) (i : Fin n) :
    (AzMvPolynomial.bind₂Hom f) (AzMvPolynomial.X i : AzMvPolynomial n R ord) =
      (AzMvPolynomial.X i : AzMvPolynomial n S ord) :=
  toMvPoly_injective (by
    show ((AzMvPolynomial.X i : AzMvPolynomial n R ord).bind₂
          (fun r => (f r : AzMvPolynomial n S ord))).toMvPoly =
         (AzMvPolynomial.X i : AzMvPolynomial n S ord).toMvPoly
    rw [toMvPoly_bind₂_ringHom, toMvPoly_X, toMvPoly_X, MvPolynomial.bind₂_X_right])

end Azurite
