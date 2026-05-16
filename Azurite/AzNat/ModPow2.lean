import Azurite.AzNat.Basic
import Azurite.AzNat.OfLimbs
import Azurite.AzNat.Parse

namespace Azurite

/-- `modPow2 n k` returns `n mod 2 ^ k`, i.e. the lowest `k` bits of `n`.

    Examples: `modPow2 n 0 = 0`, `modPow2 n 1` is `1` if `n` is odd
    and `0` otherwise, `modPow2 n 64` is the lowest limb of `n`. Only
    examines the lowest `k / 64 + 1` limbs. -/
def AzNat.modPow2 (n : AzNat) (k : Nat) : AzNat :=
  let q := k / 64
  let r := k % 64
  if hq : q ≥ n.limbs.size then
    -- `2 ^ k` exceeds `n`'s bit-width; `n mod 2 ^ k = n`.
    n
  else if r = 0 then
    -- Take the first `q` limbs verbatim.
    AzNat.ofLimbs (n.limbs.extract 0 q)
  else
    -- Take the first `q` limbs and mask the `q`-th limb to `r` bits.
    have hlt : q < n.limbs.size := Nat.lt_of_not_le hq
    let lowLimbs := n.limbs.extract 0 q
    let mask := ((1 : UInt64) <<< UInt64.ofNat r) - 1
    let masked := n.limbs[q] &&& mask
    AzNat.ofLimbs (lowLimbs.push masked)

-- Sanity checks.
-- `n mod 2^0 = 0`.
#guard ((Azurite.AzNat.parse "0".toList).get!.modPow2 0).toNat == 0
#guard ((Azurite.AzNat.parse "123456789".toList).get!.modPow2 0).toNat == 0

-- `n mod 2^1` is the parity (0 or 1).
#guard ((Azurite.AzNat.parse "0".toList).get!.modPow2 1).toNat == 0
#guard ((Azurite.AzNat.parse "1".toList).get!.modPow2 1).toNat == 1
#guard ((Azurite.AzNat.parse "8".toList).get!.modPow2 1).toNat == 0
#guard ((Azurite.AzNat.parse "123456789".toList).get!.modPow2 1).toNat == 1

-- 12 = 1100₂. `12 mod 2 = 0`, `12 mod 4 = 0`, `12 mod 8 = 4`, `12 mod 16 = 12`.
#guard ((Azurite.AzNat.parse "12".toList).get!.modPow2 2).toNat == 0
#guard ((Azurite.AzNat.parse "12".toList).get!.modPow2 3).toNat == 4
#guard ((Azurite.AzNat.parse "12".toList).get!.modPow2 4).toNat == 12
#guard ((Azurite.AzNat.parse "12".toList).get!.modPow2 1000).toNat == 12

-- `2^64 mod 2^64 = 0`; `2^64 mod 2^65 = 2^64`.
#guard ((Azurite.AzNat.parse "18446744073709551616".toList).get!.modPow2 64).toNat == 0
#guard ((Azurite.AzNat.parse "18446744073709551616".toList).get!.modPow2 65).toNat ==
       18446744073709551616

-- `(2^65 + 1) mod 2^65 = 1`; `(2^65 + 1) mod 2^66 = 2^65 + 1`.
#guard ((Azurite.AzNat.parse "36893488147419103233".toList).get!.modPow2 65).toNat == 1
#guard ((Azurite.AzNat.parse "36893488147419103233".toList).get!.modPow2 66).toNat ==
       36893488147419103233

-- `3 * 2^128 mod 2^128 = 0`; `3 * 2^128 mod 2^129 = 2^128`.
#guard ((Azurite.AzNat.parse "1020847100762815390390123822295304634368".toList).get!.modPow2 128).toNat
       == 0
#guard ((Azurite.AzNat.parse "1020847100762815390390123822295304634368".toList).get!.modPow2 129).toNat
       == 340282366920938463463374607431768211456

end Azurite
