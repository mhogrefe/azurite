/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.OfLimbDigits
import Azurite.AzNat.ParseBase
import Azurite.AzNat.ToStringBase

namespace Azurite

-- Direct reconstruction in various bases.
#guard AzNat.toString (AzNat.ofLimbDigits 10 #[5, 4, 3, 2, 1]) == "12345"
#guard AzNat.toString (AzNat.ofLimbDigits 10 #[]) == "0"

-- Base-10 specialisation agrees with the general path.
#guard AzNat.toString (AzNat.ofBase10Digits #[5, 4, 3, 2, 1]) == "12345"
#guard AzNat.toString (AzNat.ofBase10Digits #[]) == "0"
-- Cross-`10^19` super-digit boundary: 2^65 + 1 = 36893488147419103233 has 20
-- decimal digits, so it spans two super-digits.
#guard AzNat.toString (AzNat.ofBase10Digits ((AzNat.parse "36893488147419103233").get!.limbDigits 10))
       == "36893488147419103233"
#guard AzNat.toString (AzNat.ofLimbDigits 16 #[0xF, 0xE, 0xE, 0xB, 0xD, 0xA, 0xE, 0xD]) ==
       "3735928559"  -- 0xDEADBEEF
#guard AzNat.toString (AzNat.ofLimbDigits 2 #[0, 1, 1, 0, 1]) == "22"  -- 0b10110
#guard AzNat.toString (AzNat.ofLimbDigits 8 #[5, 5, 7]) == "493"  -- 0o755

-- Degenerate bases.
#guard AzNat.toString (AzNat.ofLimbDigits 0 #[1, 2, 3]) == "0"
#guard AzNat.toString (AzNat.ofLimbDigits 1 #[0, 0]) == "0"

-- Round-trip with limbDigits across multiple bases.
#guard AzNat.toString (AzNat.ofLimbDigits 10 ((AzNat.parse "12345").get!.limbDigits 10))
       == "12345"
#guard AzNat.toString (AzNat.ofLimbDigits 16 ((AzNat.parse "3735928559").get!.limbDigits 16))
       == "3735928559"
#guard AzNat.toString (AzNat.ofLimbDigits 2 ((AzNat.parse "3735928559").get!.limbDigits 2))
       == "3735928559"
-- Multi-limb round-trip (2^65 + 1).
#guard AzNat.toString (AzNat.ofLimbDigits 10
         ((AzNat.parse "36893488147419103233").get!.limbDigits 10))
       == "36893488147419103233"
-- Large base, multi-limb.
#guard AzNat.toString (AzNat.ofLimbDigits 7
         ((AzNat.parse "36893488147419103233").get!.limbDigits 7))
       == "36893488147419103233"
-- Power-of-two base (delegates to ofLimbDigitsPow2).
#guard AzNat.toString (AzNat.ofLimbDigits 16
         ((AzNat.parse "36893488147419103233").get!.limbDigits 16))
       == "36893488147419103233"

end Azurite
