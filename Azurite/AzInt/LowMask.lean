import Azurite.AzInt.Basic
import Azurite.AzNat.LowMask

namespace Azurite

/-- Construct the AzInt with the lowest `k` bits set, equal to `2 ^ k - 1`. -/
def AzInt.lowMask (k : Nat) : AzInt where
  sign := true
  abs := AzNat.lowMask k
  zero_sign := by
    intro h
    have := (AzNat.lowMask k).last_ne_zero
    rw [h] at this

end Azurite
