import Azurite.AzNat.OfLimbDigits
import Azurite.AzNat.ParseBase

namespace Azurite

-- Direct reconstruction in various bases.
#guard AzNat.ofLimbDigits 10 #[5, 4, 3, 2, 1] = (AzNat.parse "12345").get!
#guard AzNat.ofLimbDigits 10 #[] = (0 : AzNat)

-- Base-10 specialisation agrees with the general path.
#guard AzNat.ofBase10Digits #[5, 4, 3, 2, 1] = (AzNat.parse "12345").get!
#guard AzNat.ofBase10Digits #[] = (0 : AzNat)
-- Cross-`10^19` super-digit boundary: 2^65 + 1 = 36893488147419103233 has 20
-- decimal digits, so it spans two super-digits.
#guard AzNat.ofBase10Digits ((AzNat.parse "36893488147419103233").get!.limbDigits 10)
       = (AzNat.parse "36893488147419103233").get!
#guard AzNat.ofLimbDigits 16 #[0xF, 0xE, 0xE, 0xB, 0xD, 0xA, 0xE, 0xD] =
       (AzNat.parse "3735928559").get!  -- 0xDEADBEEF
#guard AzNat.ofLimbDigits 2 #[0, 1, 1, 0, 1] = (AzNat.parse "22").get!  -- 0b10110
#guard AzNat.ofLimbDigits 8 #[5, 5, 7] = (AzNat.parse "493").get!  -- 0o755

-- Degenerate bases.
#guard AzNat.ofLimbDigits 0 #[1, 2, 3] = (0 : AzNat)
#guard AzNat.ofLimbDigits 1 #[0, 0] = (0 : AzNat)

-- Round-trip with limbDigits across multiple bases.
#guard AzNat.ofLimbDigits 10 ((AzNat.parse "12345").get!.limbDigits 10)
       = (AzNat.parse "12345").get!
#guard AzNat.ofLimbDigits 16 ((AzNat.parse "3735928559").get!.limbDigits 16)
       = (AzNat.parse "3735928559").get!
#guard AzNat.ofLimbDigits 2 ((AzNat.parse "3735928559").get!.limbDigits 2)
       = (AzNat.parse "3735928559").get!
-- Multi-limb round-trip (2^65 + 1).
#guard AzNat.ofLimbDigits 10
         ((AzNat.parse "36893488147419103233").get!.limbDigits 10)
       = (AzNat.parse "36893488147419103233").get!
-- Large base, multi-limb.
#guard AzNat.ofLimbDigits 7
         ((AzNat.parse "36893488147419103233").get!.limbDigits 7)
       = (AzNat.parse "36893488147419103233").get!
-- Power-of-two base (delegates to ofLimbDigitsPow2).
#guard AzNat.ofLimbDigits 16
         ((AzNat.parse "36893488147419103233").get!.limbDigits 16)
       = (AzNat.parse "36893488147419103233").get!

end Azurite
