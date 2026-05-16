import Azurite.AzNat.GetBits
import Azurite.AzNat.ParseBase

namespace Azurite

-- `n = 0b...1010 1100 = 0xAC = 172`. Bits: [0,1,1,0,1,0,1,0, ...].
#guard (AzNat.parse "172").get!.getBitsAsLimb 0 4 (by omega) == 12  -- 0b1100
#guard (AzNat.parse "172").get!.getBitsAsLimb 4 8 (by omega) == 10  -- 0b1010
#guard (AzNat.parse "172").get!.getBitsAsLimb 0 8 (by omega) == 172
#guard (AzNat.parse "172").get!.getBitsAsLimb 2 6 (by omega) == 11  -- 0b1011

-- Single-limb extraction agrees with the spec on large `n`.
#guard (AzNat.parse "123456789").get!.getBitsAsLimb 0 64 (by omega) == 123456789
#guard (AzNat.parse "123456789").get!.getBitsAsLimb 0 0 (by omega) == 0
#guard (AzNat.parse "123456789").get!.getBitsAsLimb 100 164 (by omega) == 0

-- Cross-limb extraction: `n = 2^63 + 2^65 = 46116860184273879040`.
-- Bit 63 = 1, bit 64 = 0, bit 65 = 1, others 0.
-- Bits [60, 68) = 0b 0010 1000 = 40.
#guard (AzNat.parse "46116860184273879040").get!.getBitsAsLimb 60 68 (by omega)
       == 40

-- `getBits` parallels `getBitsAsLimb` but allows wide ranges.
#guard ((AzNat.parse "172").get!.getBits 0 8).toNat == 172
#guard ((AzNat.parse "172").get!.getBits 4 8).toNat == 10
#guard ((AzNat.parse "172").get!.getBits 0 0).toNat == 0

-- Wide extraction crossing the 64-bit boundary.
-- `n = 2^65 + 1 = 36893488147419103233`. Bits 0 and 65 set.
-- getBits 0 66: bits [0, 66) includes both 0 and 65 → value 2^65 + 1 = n.
#guard ((AzNat.parse "36893488147419103233").get!.getBits 0 66).toNat
       == 36893488147419103233
-- getBits 1 66: bits [1, 66), bit 0 of result = bit 1 of n = 0, bit 64 of result = bit 65 of n = 1.
-- Value = 2^64 = 18446744073709551616.
#guard ((AzNat.parse "36893488147419103233").get!.getBits 1 66).toNat
       == 18446744073709551616

-- getBits agrees with the naive spec `(n >>> i).modPow2 (j - i)` on a wider example.
#guard ((AzNat.parse "36893488147419103233").get!.getBits 30 100)
       == (((AzNat.parse "36893488147419103233").get!.shiftRight 30).modPow2 70)

#guard ((AzNat.parse "36893488147419103233").get!.getBits 0 200)
       == (AzNat.parse "36893488147419103233").get!

end Azurite
