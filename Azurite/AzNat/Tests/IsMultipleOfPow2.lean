/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.IsMultipleOfPow2
import Azurite.AzNat.ParseBase

namespace Azurite

-- 0 is a multiple of every 2^k
#guard (AzNat.parse "0").get!.isMultipleOfPow2 0 == true
#guard (AzNat.parse "0").get!.isMultipleOfPow2 1000 == true
-- every n is a multiple of 2^0 = 1
#guard (AzNat.parse "1").get!.isMultipleOfPow2 0 == true
#guard (AzNat.parse "123456789").get!.isMultipleOfPow2 0 == true
-- 1 is not a multiple of 2
#guard (AzNat.parse "1").get!.isMultipleOfPow2 1 == false
-- 8 = 2^3
#guard (AzNat.parse "8").get!.isMultipleOfPow2 3 == true
#guard (AzNat.parse "8").get!.isMultipleOfPow2 4 == false
-- 12 = 1100₂ is a multiple of 4 but not 8
#guard (AzNat.parse "12").get!.isMultipleOfPow2 2 == true
#guard (AzNat.parse "12").get!.isMultipleOfPow2 3 == false
-- 2^64
#guard (AzNat.parse "18446744073709551616").get!.isMultipleOfPow2 64 == true
#guard (AzNat.parse "18446744073709551616").get!.isMultipleOfPow2 65 == false
-- 3 * 2^128 has 128 trailing zeros
#guard (AzNat.parse "1020847100762815390390123822295304634368").get!.isMultipleOfPow2 128 == true
#guard (AzNat.parse "1020847100762815390390123822295304634368").get!.isMultipleOfPow2 129 == false
-- k well beyond the size of the number returns false for nonzero values
#guard (AzNat.parse "8").get!.isMultipleOfPow2 1000 == false

end Azurite
