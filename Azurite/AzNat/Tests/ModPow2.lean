/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.ModPow2
import Azurite.AzNat.ParseBase

namespace Azurite

-- `n mod 2^0 = 0`.
#guard ((AzNat.parse "0").get!.modPow2 0).toNat == 0
#guard ((AzNat.parse "123456789").get!.modPow2 0).toNat == 0

-- `n mod 2^1` is the parity (0 or 1).
#guard ((AzNat.parse "0").get!.modPow2 1).toNat == 0
#guard ((AzNat.parse "1").get!.modPow2 1).toNat == 1
#guard ((AzNat.parse "8").get!.modPow2 1).toNat == 0
#guard ((AzNat.parse "123456789").get!.modPow2 1).toNat == 1

-- 12 = 1100₂. `12 mod 2 = 0`, `12 mod 4 = 0`, `12 mod 8 = 4`, `12 mod 16 = 12`.
#guard ((AzNat.parse "12").get!.modPow2 2).toNat == 0
#guard ((AzNat.parse "12").get!.modPow2 3).toNat == 4
#guard ((AzNat.parse "12").get!.modPow2 4).toNat == 12
#guard ((AzNat.parse "12").get!.modPow2 1000).toNat == 12

-- `2^64 mod 2^64 = 0`; `2^64 mod 2^65 = 2^64`.
#guard ((AzNat.parse "18446744073709551616").get!.modPow2 64).toNat == 0
#guard ((AzNat.parse "18446744073709551616").get!.modPow2 65).toNat ==
       18446744073709551616

-- `(2^65 + 1) mod 2^65 = 1`; `(2^65 + 1) mod 2^66 = 2^65 + 1`.
#guard ((AzNat.parse "36893488147419103233").get!.modPow2 65).toNat == 1
#guard ((AzNat.parse "36893488147419103233").get!.modPow2 66).toNat ==
       36893488147419103233

-- `3 * 2^128 mod 2^128 = 0`; `3 * 2^128 mod 2^129 = 2^128`.
#guard ((AzNat.parse "1020847100762815390390123822295304634368").get!.modPow2 128).toNat
       == 0
#guard ((AzNat.parse "1020847100762815390390123822295304634368").get!.modPow2 129).toNat
       == 340282366920938463463374607431768211456

end Azurite
