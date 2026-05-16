import Azurite.AzNat.OfLimbDigitsPow2
import Azurite.AzNat.ParseBase

namespace Azurite

-- k = 64 short-circuit: digits ARE the limbs.
-- 2^64 has limbs [0, 1].
#guard (AzNat.ofLimbDigitsPow2 64 #[0, 1]) = (AzNat.parse "18446744073709551616").get!
#guard (AzNat.ofLimbDigitsPow2 64 #[100]) = (AzNat.parse "100").get!
#guard (AzNat.ofLimbDigitsPow2 64 #[]) = (0 : AzNat)
-- Trailing-zero digits get trimmed (input was unnormalized).
#guard (AzNat.ofLimbDigitsPow2 64 #[7, 0, 0]) = (AzNat.parse "7").get!

-- k | 64 with k < 64 (digits never span limb boundaries).
-- 100 = 0x64 in base 16 has LSB-first digits [4, 6]. Round-trip.
#guard (AzNat.ofLimbDigitsPow2 4 #[4, 6]) = (AzNat.parse "100").get!
-- Sixteen Fs in base 16 reconstruct 0xFFFF_FFFF_FFFF_FFFF.
#guard (AzNat.ofLimbDigitsPow2 4
         #[0xF, 0xF, 0xF, 0xF, 0xF, 0xF, 0xF, 0xF,
           0xF, 0xF, 0xF, 0xF, 0xF, 0xF, 0xF, 0xF])
       = (AzNat.parse "18446744073709551615").get!  -- 2^64 - 1
-- Cross-limb base-2^32: digits [1, 0, 1] → 1 + 1·2^64.
#guard (AzNat.ofLimbDigitsPow2 32 #[1, 0, 1]) = (AzNat.parse "18446744073709551617").get!
-- Empty input → zero.
#guard (AzNat.ofLimbDigitsPow2 4 #[]) = (0 : AzNat)

-- k ∤ 64 (digits span limb boundaries).
-- 100 = 0o144 in base 8 has LSB-first digits [4, 4, 1]. Round-trip.
#guard (AzNat.ofLimbDigitsPow2 3 #[4, 4, 1]) = (AzNat.parse "100").get!
-- 2^65 in base 32: digit 13 = 1, others 0. Reconstructs 2^65 = 36893488147419103232.
#guard (AzNat.ofLimbDigitsPow2 5 #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])
       = (AzNat.parse "36893488147419103232").get!
-- Zero digits → zero.
#guard (AzNat.ofLimbDigitsPow2 3 #[]) = (0 : AzNat)

-- Degenerate (k out of range).
#guard (AzNat.ofLimbDigitsPow2 0 #[42]) = (0 : AzNat)
#guard (AzNat.ofLimbDigitsPow2 65 #[42]) = (0 : AzNat)

-- Round-trip with `limbDigitsPow2`: `ofLimbDigitsPow2 k (limbDigitsPow2 k n) = n`.
#guard AzNat.ofLimbDigitsPow2 64 ((AzNat.parse "18446744073709551616").get!.limbDigitsPow2 64)
       = (AzNat.parse "18446744073709551616").get!
#guard AzNat.ofLimbDigitsPow2 4 ((AzNat.parse "100").get!.limbDigitsPow2 4)
       = (AzNat.parse "100").get!
#guard AzNat.ofLimbDigitsPow2 3 ((AzNat.parse "100").get!.limbDigitsPow2 3)
       = (AzNat.parse "100").get!
#guard AzNat.ofLimbDigitsPow2 5 ((AzNat.parse "36893488147419103232").get!.limbDigitsPow2 5)
       = (AzNat.parse "36893488147419103232").get!
-- Larger cross-limb round-trip.
#guard AzNat.ofLimbDigitsPow2 7
         ((AzNat.parse "36893488147419103233").get!.limbDigitsPow2 7)
       = (AzNat.parse "36893488147419103233").get!

end Azurite
