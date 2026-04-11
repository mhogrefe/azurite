import Azurite.AzMvPolynomial.New.Join2
import Azurite.AzMvPolynomial.New.Equiv.Bind2

/-!
# Equivalence: `AzMvPolynomialNew.join₂` ↔ `MvPolynomial.join₂`

Since `join₂ = bind₂ id`, the equivalence follows directly from `toMvPoly_bind₂_new`.
The key relationship is:

  `toMvPoly (p.join₂) = bind₂ toMvPolyRingHomNew (toMvPoly p)`

where `toMvPolyRingHomNew` is `toMvPoly` viewed as a ring homomorphism from
`AzMvPolynomialNew n R ord` to `MvPolynomial (Fin n) R`.
-/

namespace Azurite
open AzMvPolynomialNew

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]
  {n : ℕ} {ord : MonomialOrder}

/-- The ring homomorphism `AzMvPolynomialNew n R ord →+* MvPolynomial (Fin n) R`. -/
noncomputable def toMvPolyRingHomNew :
    AzMvPolynomialNew n R ord →+* MvPolynomial (Fin n) R where
  toFun := AzMvPolynomialNew.toMvPoly
  map_zero' := toMvPoly_zero_new
  map_one' := toMvPoly_one_new
  map_add' := toMvPoly_add_new
  map_mul' := toMvPoly_mul_new

/-- Forward: `toMvPoly (join₂ p) = bind₂ toMvPolyRingHomNew (toMvPoly p)`. -/
@[simp] theorem toMvPoly_join₂_new
    (p : AzMvPolynomialNew n (AzMvPolynomialNew n R ord) ord) :
    toMvPoly (p.join₂) =
    (MvPolynomial.bind₂ toMvPolyRingHomNew) (toMvPoly p) := by
  unfold AzMvPolynomialNew.join₂
  rw [show (id : AzMvPolynomialNew n R ord → AzMvPolynomialNew n R ord) =
    (fun r => ofMvPoly (toMvPolyRingHomNew r)) from by
    ext r; simp [toMvPolyRingHomNew, ofMvPoly_toMvPoly_new]]
  exact toMvPoly_bind₂_new (R := AzMvPolynomialNew n R ord) (S := R) toMvPolyRingHomNew p

@[simp] theorem ofMvPoly_join₂_new
    (p : MvPolynomial (Fin n) (AzMvPolynomialNew n R ord)) :
    (AzMvPolynomialNew.ofMvPoly p :
      AzMvPolynomialNew n (AzMvPolynomialNew n R ord) ord).join₂ =
    AzMvPolynomialNew.ofMvPoly ((MvPolynomial.bind₂ toMvPolyRingHomNew) p) :=
  toMvPoly_injective_new (by rw [toMvPoly_join₂_new]; simp only [toMvPoly_ofMvPoly_new])

end Azurite
