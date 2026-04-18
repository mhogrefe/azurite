import Azurite.AzNat.Basic
import Azurite.AzNat.Parse
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

-- 0 is a multiple of every 2^k
#guard (Azurite.AzNat.parse "0".toList).get!.isMultipleOfPow2 0 == true
#guard (Azurite.AzNat.parse "0".toList).get!.isMultipleOfPow2 1000 == true
-- every n is a multiple of 2^0 = 1
#guard (Azurite.AzNat.parse "1".toList).get!.isMultipleOfPow2 0 == true
#guard (Azurite.AzNat.parse "123456789".toList).get!.isMultipleOfPow2 0 == true
-- 1 is not a multiple of 2
#guard (Azurite.AzNat.parse "1".toList).get!.isMultipleOfPow2 1 == false
-- 8 = 2^3
#guard (Azurite.AzNat.parse "8".toList).get!.isMultipleOfPow2 3 == true
#guard (Azurite.AzNat.parse "8".toList).get!.isMultipleOfPow2 4 == false
-- 12 = 1100₂ is a multiple of 4 but not 8
#guard (Azurite.AzNat.parse "12".toList).get!.isMultipleOfPow2 2 == true
#guard (Azurite.AzNat.parse "12".toList).get!.isMultipleOfPow2 3 == false
-- 2^64
#guard (Azurite.AzNat.parse "18446744073709551616".toList).get!.isMultipleOfPow2 64 == true
#guard (Azurite.AzNat.parse "18446744073709551616".toList).get!.isMultipleOfPow2 65 == false
-- 3 * 2^128 has 128 trailing zeros
#guard (Azurite.AzNat.parse "1020847100762815390390123822295304634368".toList).get!.isMultipleOfPow2 128 == true
#guard (Azurite.AzNat.parse "1020847100762815390390123822295304634368".toList).get!.isMultipleOfPow2 129 == false
-- k well beyond the size of the number returns false for nonzero values
#guard (Azurite.AzNat.parse "8".toList).get!.isMultipleOfPow2 1000 == false

end Azurite
