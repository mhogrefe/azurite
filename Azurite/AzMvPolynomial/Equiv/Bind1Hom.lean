import Azurite.AzMvPolynomial.Equiv.Bind1
import Azurite.AzMvPolynomial.Equiv.Algebra
import Azurite.AzMvPolynomial.Equiv.AlgebraOfAlgebra

/-!
# Bundled `R`-algebra-hom form of `AzMvPolynomial.bind₁`

Provides `AzMvPolynomial.bind₁Hom`: given a substitution
`f : Fin n → AzMvPolynomial n R ord`, the map `p ↦ p.bind₁ f` is an
`R`-algebra homomorphism from `AzMvPolynomial n R ord` to itself.

Fin-only counterpart of Mathlib's `MvPolynomial.bind₁`, which is already
bundled as `MvPolynomial σ R →ₐ[R] MvPolynomial σ R`.
-/

namespace Azurite

open AzMvPolynomial

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]
    {n : ℕ} {ord : MonomialOrder}

/-- Bundled `R`-algebra-hom form of `AzMvPolynomial.bind₁`. -/
def AzMvPolynomial.bind₁Hom (f : Fin n → AzMvPolynomial n R ord) :
    AzMvPolynomial n R ord →ₐ[R] AzMvPolynomial n R ord where
  toFun p := p.bind₁ f
  map_zero' := toMvPoly_injective (by
    rw [toMvPoly_bind₁,
        show (0 : AzMvPolynomial n R ord).toMvPoly = (0 : MvPolynomial (Fin n) R)
          from toMvPoly_zero,
        map_zero])
  map_one' := toMvPoly_injective (by
    rw [toMvPoly_bind₁,
        show (1 : AzMvPolynomial n R ord).toMvPoly = (1 : MvPolynomial (Fin n) R)
          from toMvPoly_one,
        map_one])
  map_add' p q := toMvPoly_injective (by
    simp [toMvPoly_bind₁, toMvPoly_add])
  map_mul' p q := toMvPoly_injective (by
    simp [toMvPoly_bind₁, toMvPoly_mul])
  commutes' r := toMvPoly_injective (by
    show ((AzMvPolynomial.C r : AzMvPolynomial n R ord).bind₁ f).toMvPoly =
         (AzMvPolynomial.C r : AzMvPolynomial n R ord).toMvPoly
    rw [toMvPoly_bind₁, toMvPoly_C, MvPolynomial.bind₁_C_right])

@[simp] theorem AzMvPolynomial.bind₁Hom_C
    (f : Fin n → AzMvPolynomial n R ord) (r : R) :
    (AzMvPolynomial.bind₁Hom f) (AzMvPolynomial.C r : AzMvPolynomial n R ord) =
      (AzMvPolynomial.C r : AzMvPolynomial n R ord) :=
  (AzMvPolynomial.bind₁Hom f).commutes r

@[simp] theorem AzMvPolynomial.bind₁Hom_X
    (f : Fin n → AzMvPolynomial n R ord) (i : Fin n) :
    (AzMvPolynomial.bind₁Hom f) (AzMvPolynomial.X i : AzMvPolynomial n R ord) =
      f i :=
  toMvPoly_injective (by
    show ((AzMvPolynomial.X i : AzMvPolynomial n R ord).bind₁ f).toMvPoly =
         (f i).toMvPoly
    rw [toMvPoly_bind₁, toMvPoly_X, MvPolynomial.bind₁_X_right])

end Azurite
