import Azurite.AzMvPolynomial.Join2
import Azurite.AzMvPolynomial.Equiv.Bind2

/-!
# Equivalence: AzMvPolynomial.join₂ ↔ MvPolynomial.join₂

Since `join₂ = bind₂ id`, the equivalence follows directly from `toMvPoly_bind₂`.
The key relationship is:

  `toMvPoly (p.join₂) = bind₂ toMvPolyRingHom (toMvPoly p)`

where `toMvPolyRingHom` is `toMvPoly` viewed as a ring homomorphism from
`AzMvPolynomial σ R ord` to `MvPolynomial σ R`.
-/

namespace Azurite
open AzMvPolynomial

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]
  {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n] {ord : MonomialOrder}

/-- The ring homomorphism `AzMvPolynomial σ R ord →+* MvPolynomial σ R`. -/
noncomputable def toMvPolyRingHom :
    AzMvPolynomial σ R ord →+* MvPolynomial σ R where
  toFun := AzMvPolynomial.toMvPoly
  map_zero' := toMvPoly_zero
  map_one' := toMvPoly_one
  map_add' := toMvPoly_add
  map_mul' := toMvPoly_mul

/-- Forward: `toMvPoly (join₂ p) = bind₂ toMvPolyRingHom (toMvPoly p)`.

The outer `toMvPoly` converts the result from `AzMvPolynomial σ R` to `MvPolynomial σ R`.
On the RHS, `toMvPoly p` produces `MvPolynomial σ (AzMvPolynomial σ R)` (coefficients are
still Azurite polynomials), and `bind₂ toMvPolyRingHom` maps each coefficient through
`toMvPoly` and flattens. -/
@[simp] theorem toMvPoly_join₂
    (p : AzMvPolynomial σ (AzMvPolynomial σ R ord) ord) :
    toMvPoly (p.join₂) =
    (MvPolynomial.bind₂ toMvPolyRingHom) (toMvPoly p) := by
  unfold AzMvPolynomial.join₂
  rw [show (id : AzMvPolynomial σ R ord → AzMvPolynomial σ R ord) =
    (fun r => ofMvPoly (toMvPolyRingHom r)) from by
    ext r; simp [toMvPolyRingHom, ofMvPoly_toMvPoly]]
  exact toMvPoly_bind₂ (R := AzMvPolynomial σ R ord) (S := R) toMvPolyRingHom p

@[simp] theorem ofMvPoly_join₂
    (p : MvPolynomial σ (AzMvPolynomial σ R ord)) :
    (AzMvPolynomial.ofMvPoly p : AzMvPolynomial σ (AzMvPolynomial σ R ord) ord).join₂ =
    AzMvPolynomial.ofMvPoly ((MvPolynomial.bind₂ toMvPolyRingHom) p) :=
  toMvPoly_injective (by rw [toMvPoly_join₂]; simp only [toMvPoly_ofMvPoly])

end Azurite
