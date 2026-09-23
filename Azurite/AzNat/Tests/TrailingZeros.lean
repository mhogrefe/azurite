/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.ParseBase
import Azurite.AzNat.TrailingZeros

namespace Azurite.AzNat

-- 0 has infinitely many trailing zeros
#guard (AzNat.parse "0").get!.trailingZeros == none
-- 1 = ...001₂, 0 trailing zeros
#guard (AzNat.parse "1").get!.trailingZeros == some 0
-- 8 = 1000₂, 3 trailing zeros
#guard (AzNat.parse "8").get!.trailingZeros == some 3
-- 12 = 1100₂, 2 trailing zeros
#guard (AzNat.parse "12").get!.trailingZeros == some 2
-- 2^64, so 64 trailing zeros
#guard (AzNat.parse "18446744073709551616").get!.trailingZeros == some 64
-- 3 * 2^128, so 128 trailing zeros
#guard (AzNat.parse "1020847100762815390390123822295304634368").get!.trailingZeros == some 128

end Azurite.AzNat
