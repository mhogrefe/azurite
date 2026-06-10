import Azurite.AzInt.Equiv.Add
import Azurite.AzInt.Equiv.Compare
import Azurite.AzInt.Equiv.Mul
import Azurite.AzInt.Instances
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Order.Hom.Basic

/-!
# Bundled equivalences between `AzInt` and `ℤ`

`toInt`/`ofInt` upgraded from the bare bijection `equivInt : AzInt ≃ ℤ` to

* `ringEquivInt : AzInt ≃+* ℤ` — a `RingEquiv`, so Mathlib's generic
  `map_*` lemmas (`map_add`, `map_mul`, `map_neg`, `map_sub`, `map_pow`,
  …) apply to `toInt` directly;
* `toIntRingHom : AzInt →+* ℤ` — the underlying ring homomorphism;
* `orderIsoInt : AzInt ≃o ℤ` — an `OrderIso`, giving monotonicity and
  order-reflection of `toInt` for free.

The component facts (`toInt_add`, `toInt_mul`, `le_iff_toInt_le`, …) are
proven in the sibling `Equiv` files; this file only packages them.
-/

namespace Azurite.AzInt

/-- `toInt` bundled as a ring equivalence `AzInt ≃+* ℤ`. -/
def ringEquivInt : AzInt ≃+* Int :=
  { equivInt with
    map_add' := toInt_add
    map_mul' := toInt_mul }

@[simp] theorem ringEquivInt_apply (z : AzInt) : ringEquivInt z = z.toInt := rfl

@[simp] theorem ringEquivInt_symm_apply (i : Int) : ringEquivInt.symm i = ofInt i := rfl

/-- `toInt` bundled as a ring homomorphism `AzInt →+* ℤ`. -/
def toIntRingHom : AzInt →+* Int := ringEquivInt.toRingHom

@[simp] theorem toIntRingHom_apply (z : AzInt) : toIntRingHom z = z.toInt := rfl

/-- `toInt` bundled as an order isomorphism `AzInt ≃o ℤ`. -/
def orderIsoInt : AzInt ≃o Int :=
  { equivInt with
    map_rel_iff' := fun {a b} => (le_iff_toInt_le a b).symm }

@[simp] theorem orderIsoInt_apply (z : AzInt) : orderIsoInt z = z.toInt := rfl

@[simp] theorem orderIsoInt_symm_apply (i : Int) : orderIsoInt.symm i = ofInt i := rfl

end Azurite.AzInt
