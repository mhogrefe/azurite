/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.RootInt
import Azurite.AzNat.ParseBase

namespace Azurite.AzNat

/-! `#guard` tests for `rootInt` (MCA Algorithm 1.14) and `isPow`. -/

-- 10^6 = 100^3; neighbours
#guard (rootInt (AzNat.parse "1000000").get! 3).toNat = 100
#guard (rootInt (AzNat.parse "999999").get! 3).toNat = 99
#guard (rootInt (AzNat.parse "1000001").get! 3).toNat = 100

-- multi-limb: 2^200 and 2^200 − 1, k = 5 (root 2^40)
#guard (rootInt (AzNat.parse "1606938044258990275541962092341162602522202993782792835301376").get! 5).toNat
  = 2 ^ 40
#guard (rootInt (AzNat.parse "1606938044258990275541962092341162602522202993782792835301375").get! 5).toNat
  = 2 ^ 40 - 1

-- 10^70, k = 7 (root 10^10); 10^70 + 1 has the same root
#guard (rootInt (AzNat.parse ("1" ++ String.ofList (List.replicate 70 '0'))).get! 7).toNat = 10 ^ 10
#guard (rootInt (AzNat.parse ("1" ++ String.ofList (List.replicate 69 '0') ++ "1")).get! 7).toNat = 10 ^ 10

-- k = 2 agrees with the integer square root
#guard (rootInt (AzNat.parse "340282366920938463463374607431768211455").get! 2).toNat
  = Nat.sqrt 340282366920938463463374607431768211455

-- edge cases
#guard (rootInt (0 : AzNat) 7).toNat = 0
#guard (rootInt (1 : AzNat) 7).toNat = 1
#guard (rootInt (AzNat.parse "12345").get! 1).toNat = 12345

-- perfect-power test
#guard isPow (AzNat.parse "1000000").get! 3 = true
#guard isPow (AzNat.parse "1000001").get! 3 = false
#guard isPow (AzNat.parse "1606938044258990275541962092341162602522202993782792835301376").get! 5 = true
#guard isPow (AzNat.parse "1606938044258990275541962092341162602522202993782792835301376").get! 3 = false

end Azurite.AzNat
