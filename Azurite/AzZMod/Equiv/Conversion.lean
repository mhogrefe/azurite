import Azurite.AzZMod.Conversion
import Azurite.AzZMod.Equiv.Basic
import Azurite.AzInt.Equiv.Basic

namespace Azurite.AzZMod

/-- **`ofAzInt` agrees with the `ZMod` cast.**  Converting an `AzInt` and then
viewing it in `ZMod m.toNat` is the same as casting its integer value. -/
@[simp] theorem toZMod_ofAzInt (m : AzNat) [NeZero m.toNat] (z : AzInt) :
    toZMod (ofAzInt m z) = (z.toInt : ZMod m.toNat) := by
  unfold ofAzInt AzInt.toInt
  by_cases h : z.sign = true
  · rw [if_pos h, if_pos h, toZMod_ofAzNat]; norm_cast
  · rw [if_neg h, if_neg h, toZMod_neg, toZMod_ofAzNat, Int.cast_neg, Int.cast_natCast]

end Azurite.AzZMod
