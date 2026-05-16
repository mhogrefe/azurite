import Azurite.AzNat.Basic
import Azurite.AzNat.OfLimbs
import Azurite.AzNat.Pow2

namespace Azurite

/-- Test whether `n` is a multiple of `2 ^ k`, i.e. whether its `k` least-significant
bits are all zero. Efficient: only examines the lowest `k / 64 + 1` limbs. -/
def AzNat.isMultipleOfPow2 (n : AzNat) (k : Nat) : Bool :=
  let q := k / 64
  let r := k % 64
  if hq : q < n.limbs.size then
    AzNat.allZeroLoop n.limbs q (by omega) &&
      (r == 0 || n.limbs[q] &&& ((1 <<< UInt64.ofNat r) - 1) == 0)
  else
    n.limbs.size == 0

end Azurite
