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

-- a root index at least the bit length: the root is `1` (`0` for `0`), returned without
-- computing `2^(k − 1)`
#guard rootInt (ofNat 3) (2 ^ 60) = ofNat 1
#guard rootInt (ofNat 0) (2 ^ 60) = ofNat 0
#guard rootInt (ofNat 1) (2 ^ 60) = ofNat 1
#guard rootInt (ofNat 255) 8 = ofNat 1
#guard rootInt (ofNat 256) 8 = ofNat 2
#guard rootInt (ofNat 255) 9 = ofNat 1
#guard rootInt (ofNat 128) 7 = ofNat 2
#guard isPow (ofNat 3) (2 ^ 60) = false
#guard isPow (ofNat 1) (2 ^ 60) = true
#guard isPow (ofNat 0) (2 ^ 60) = true

-- large index with a large root: the initial guess `2^⌈b/k⌉` is refined by bisection (Newton's
-- iteration alone needs about `k` steps from there when `k` does not divide the bit length)
private def big : AzNat := ofNat 1234567890123456789
#guard rootInt (big.pow 100) 100 = big
#guard rootInt (big.pow 100 + 1) 100 = big
#guard rootInt (big.pow 100 - 1) 100 = big - 1
#guard rootInt (big.pow 37 + big) 37 = big
#guard rootInt ((big.pow 37).pow 8) 37 = big.pow 8
#guard isPow (big.pow 257) 257
#guard !isPow (big.pow 257 + 2) 257
#guard ∀ k ∈ [8, 9, 15, 16, 17, 31, 64, 100, 127], ∀ c ∈ [2, 3, 5, 255, 256, 65537, 10 ^ 12],
  rootInt ((ofNat c).pow k) k = ofNat c ∧ rootInt ((ofNat c).pow k - 1) k = ofNat (c - 1)
    ∧ rootInt ((ofNat c).pow k + 1) k = ofNat c
#guard ∀ k ∈ [8, 13, 40], ∀ n ∈ [10 ^ 30 + 7, 2 ^ 200 - 1, 2 ^ 200, 3 ^ 150, 7 ^ 77 + 1],
  (rootInt (ofNat n) k).toNat = rootIntNat n k

end Azurite.AzNat
