/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.OfLimbDigitsPow2
import Azurite.AzNat.ParseBase
import Azurite.AzNat.ToStringBase

namespace Azurite

-- k = 64 short-circuit: digits ARE the limbs.
-- 2^64 has limbs [0, 1].
#guard AzNat.toString (AzNat.ofLimbDigitsPow2 64 #[0, 1]) == "18446744073709551616"
#guard AzNat.toString (AzNat.ofLimbDigitsPow2 64 #[100]) == "100"
#guard AzNat.toString (AzNat.ofLimbDigitsPow2 64 #[]) == "0"
-- Trailing-zero digits get trimmed (input was unnormalized).
#guard AzNat.toString (AzNat.ofLimbDigitsPow2 64 #[7, 0, 0]) == "7"

-- k | 64 with k < 64 (digits never span limb boundaries).
-- 100 = 0x64 in base 16 has LSB-first digits [4, 6]. Round-trip.
#guard AzNat.toString (AzNat.ofLimbDigitsPow2 4 #[4, 6]) == "100"
-- Sixteen Fs in base 16 reconstruct 0xFFFF_FFFF_FFFF_FFFF.
#guard AzNat.toString (AzNat.ofLimbDigitsPow2 4
         #[0xF, 0xF, 0xF, 0xF, 0xF, 0xF, 0xF, 0xF,
           0xF, 0xF, 0xF, 0xF, 0xF, 0xF, 0xF, 0xF])
       == "18446744073709551615"  -- 2^64 - 1
-- Cross-limb base-2^32: digits [1, 0, 1] → 1 + 1·2^64.
#guard AzNat.toString (AzNat.ofLimbDigitsPow2 32 #[1, 0, 1]) == "18446744073709551617"
-- Empty input → zero.
#guard AzNat.toString (AzNat.ofLimbDigitsPow2 4 #[]) == "0"

-- k ∤ 64 (digits span limb boundaries).
-- 100 = 0o144 in base 8 has LSB-first digits [4, 4, 1]. Round-trip.
#guard AzNat.toString (AzNat.ofLimbDigitsPow2 3 #[4, 4, 1]) == "100"
-- 2^65 in base 32: digit 13 = 1, others 0. Reconstructs 2^65 = 36893488147419103232.
#guard AzNat.toString (AzNat.ofLimbDigitsPow2 5 #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])
       == "36893488147419103232"
-- Zero digits → zero.
#guard AzNat.toString (AzNat.ofLimbDigitsPow2 3 #[]) == "0"

-- Degenerate (k out of range).
#guard AzNat.toString (AzNat.ofLimbDigitsPow2 0 #[42]) == "0"
#guard AzNat.toString (AzNat.ofLimbDigitsPow2 65 #[42]) == "0"

-- Round-trip with `limbDigitsPow2`: `ofLimbDigitsPow2 k (limbDigitsPow2 k n) = n`.
#guard AzNat.toString (AzNat.ofLimbDigitsPow2 64 ((AzNat.parse "18446744073709551616").get!.limbDigitsPow2 64))
       == "18446744073709551616"
#guard AzNat.toString (AzNat.ofLimbDigitsPow2 4 ((AzNat.parse "100").get!.limbDigitsPow2 4))
       == "100"
#guard AzNat.toString (AzNat.ofLimbDigitsPow2 3 ((AzNat.parse "100").get!.limbDigitsPow2 3))
       == "100"
#guard AzNat.toString (AzNat.ofLimbDigitsPow2 5 ((AzNat.parse "36893488147419103232").get!.limbDigitsPow2 5))
       == "36893488147419103232"
-- Larger cross-limb round-trip.
#guard AzNat.toString (AzNat.ofLimbDigitsPow2 7
         ((AzNat.parse "36893488147419103233").get!.limbDigitsPow2 7))
       == "36893488147419103233"

end Azurite
