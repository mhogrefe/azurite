import Azurite.AzZModPow2.Conversion
import Azurite.AzZModPow2.Equiv.Basic
import Azurite.AzInt.Equiv.Basic

namespace Azurite.AzZModPow2

variable {k : Nat}

/-- **`ofAzInt` agrees with the `ZMod` cast.**  Converting an `AzInt` and then
viewing it in `ZMod (2^k)` is the same as casting its integer value. -/
@[simp] theorem toZMod_ofAzInt (k : Nat) (z : AzInt) :
    toZMod (ofAzInt k z) = (z.toInt : ZMod (2 ^ k)) := by
  unfold ofAzInt AzInt.toInt
  by_cases h : z.sign = true
  · rw [ite_eq_left h, ite_eq_left h, toZMod_ofAzNat]; norm_cast
  · rw [ite_eq_right h, ite_eq_right h, toZMod_neg, toZMod_ofAzNat, Int.cast_neg, Int.cast_natCast]

end Azurite.AzZModPow2
