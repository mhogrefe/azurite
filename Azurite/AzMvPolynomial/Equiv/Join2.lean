import Azurite.AzMvPolynomial.Join2
import Azurite.AzMvPolynomial.Equiv.Bind2

/-!
# Equivalence: `AzMvPolynomial.join₂` ↔ `MvPolynomial.join₂`

Since `join₂ = bind₂ id`, the equivalence follows directly from `toMvPoly_bind₂ `.
The key relationship is:

  `toMvPoly (p.join₂) = bind₂ toMvPolyRingHom (toMvPoly p)`

where `toMvPolyRingHom` is `toMvPoly` viewed as a ring homomorphism from
`AzMvPolynomial n R ord` to `MvPolynomial (Fin n) R`.
-/

namespace Azurite
open AzMvPolynomial

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]
  {n : ℕ} {ord : MonomialOrder}

/-- The ring homomorphism `AzMvPolynomial n R ord →+* MvPolynomial (Fin n) R`. -/
noncomputable def toMvPolyRingHom :
    AzMvPolynomial n R ord →+* MvPolynomial (Fin n) R where
  toFun := AzMvPolynomial.toMvPoly
  map_zero' := toMvPoly_zero
  map_one' := toMvPoly_one
  map_add' := toMvPoly_add
  map_mul' := toMvPoly_mul

/-- Forward: `toMvPoly (join₂ p) = bind₂ toMvPolyRingHom (toMvPoly p)`. -/
@[simp] theorem toMvPoly_join₂
    (p : AzMvPolynomial n (AzMvPolynomial n R ord) ord) :
    toMvPoly (p.join₂) =
    (MvPolynomial.bind₂ toMvPolyRingHom) (toMvPoly p) := by
  unfold AzMvPolynomial.join₂
  rw [show (id : AzMvPolynomial n R ord → AzMvPolynomial n R ord) =
    (fun r => ofMvPoly (toMvPolyRingHom r)) from by
    ext r; simp [toMvPolyRingHom, ofMvPoly_toMvPoly]]
  exact toMvPoly_bind₂  (R := AzMvPolynomial n R ord) (S := R) toMvPolyRingHom p

@[simp] theorem ofMvPoly_join₂
    (p : MvPolynomial (Fin n) (AzMvPolynomial n R ord)) :
    (AzMvPolynomial.ofMvPoly p :
      AzMvPolynomial n (AzMvPolynomial n R ord) ord).join₂ =
    AzMvPolynomial.ofMvPoly ((MvPolynomial.bind₂ toMvPolyRingHom) p) :=
  toMvPoly_injective (by rw [toMvPoly_join₂ ]; simp only [toMvPoly_ofMvPoly])

end Azurite
