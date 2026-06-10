import Azurite.AzRat.Div
import Azurite.AzRat.Equiv.Mul

/-!
# Correctness of `AzRat` division

The key fact is structural: although `AzRat.div` is implemented directly
(to avoid allocating an intermediate `y⁻¹`), it is *definitionally* the
composition `x * y⁻¹` — `inv` swaps the divisor's fields, so `mul`'s
cross-gcds against `y⁻¹` are syntactically `div`'s cross-gcds against `y`
(`div_eq_mul_inv`). Field-level correctness in both directions
(`toRat_div`, `ofRat_div`) then follows from the multiplication and
reciprocal theorems, with `x / 0 = 0` matching `ℚ`'s convention.
-/

namespace Azurite.AzRat

/-- `AzRat.div` is `x * y⁻¹`, structurally: the two sides compute the same
gcds on the same operands and build the same fields, so the equality holds
by unfolding — no `toRat`-level reasoning needed. The direct implementation
just avoids materializing the intermediate `y⁻¹`. -/
theorem div_eq_mul_inv (x y : AzRat) : x / y = x * y⁻¹ := by
  show AzRat.div x y = AzRat.mul x (AzRat.inv y)
  by_cases hx : x.num = 0
  · by_cases hy : y.num = 0
    · rw [AzRat.div, dif_pos hx, AzRat.inv, dif_pos hy, AzRat.mul, dif_pos hx]
    · rw [AzRat.div, dif_pos hx, AzRat.inv, dif_neg hy, AzRat.mul, dif_pos hx]
  · by_cases hy : y.num = 0
    · rw [AzRat.div, dif_neg hx, dif_pos hy, AzRat.inv, dif_pos hy, AzRat.mul,
          dif_neg hx, dif_pos (show (0 : AzRat).num = 0 from rfl)]
    · rw [AzRat.div, dif_neg hx, dif_neg hy, AzRat.inv, dif_neg hy, AzRat.mul,
          dif_neg hx, dif_neg (show ¬((⟨y.sign, y.den, y.num, hy,
            fun h => absurd h y.den_nz,
            (AzNat.coprime_iff _ _).mpr ((AzNat.coprime_iff _ _).mp y.reduced).symm⟩ :
              AzRat).num = 0) from y.den_nz)]

@[simp] theorem toRat_div (x y : AzRat) : toRat (x / y) = toRat x / toRat y := by
  rw [div_eq_mul_inv, toRat_mul, toRat_inv, _root_.div_eq_mul_inv]

@[simp] theorem ofRat_div (r s : ℚ) : ofRat (r / s) = ofRat r / ofRat s :=
  toRat_injective (by rw [toRat_ofRat, toRat_div, toRat_ofRat, toRat_ofRat])

end Azurite.AzRat
