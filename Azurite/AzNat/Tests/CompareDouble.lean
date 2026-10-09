/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.CompareDouble
import Azurite.AzNat.Compare
import Azurite.AzNat.ParseBase
import Azurite.AzNat.ShiftLeft

/-!
# Tests for `cmpDouble` (compare `x` with `2 y` without forming `2 y`)
-/

namespace Azurite.AzNat

private def N (s : String) : AzNat := (AzNat.parse s).get!
private def D (x y : String) : Ordering := cmpDouble (N x) (N y)
/-- The reference: compare against the actually doubled operand. -/
private def R (x y : String) : Ordering := compare (N x) (N y <<< 1)

-- small values
#guard D "0" "0" == .eq
#guard D "1" "0" == .gt
#guard D "0" "1" == .lt
#guard D "2" "1" == .eq
#guard D "3" "1" == .gt
#guard D "1" "1" == .lt
#guard D "100" "50" == .eq
#guard D "99" "50" == .lt
#guard D "101" "50" == .gt
-- the carry out of the top limb: 2 · 2^63 = 2^64, 2 · (2^63 − 1) = 2^64 − 2
#guard D "18446744073709551616" "9223372036854775808" == .eq
#guard D "18446744073709551616" "9223372036854775807" == .gt
#guard D "18446744073709551615" "9223372036854775808" == .lt
#guard D "18446744073709551614" "9223372036854775807" == .eq
-- multi-limb with the top bit set: y = 2^191 + 5, 2 y = 2^192 + 10
#guard D "6277101735386680763835789423207666416102355444464034512906"
  "3138550867693340381917894711603833208051177722232017256453" == .eq
#guard D "6277101735386680763835789423207666416102355444464034512907"
  "3138550867693340381917894711603833208051177722232017256453" == .gt
#guard D "6277101735386680763835789423207666416102355444464034512905"
  "3138550867693340381917894711603833208051177722232017256453" == .lt
-- different limb counts
#guard D "5" "340282366920938463463374607431768211455" == .lt
#guard D "6277101735386680763835789423207666416102355444464034512896" "7" == .gt
-- agreement with the doubled operand on a batch of pairs
#guard [("0", "0"), ("12345678901234567890", "6172839450617283945"),
    ("12345678901234567891", "6172839450617283945"),
    ("12345678901234567889", "6172839450617283945"),
    ("340282366920938463463374607431768211455", "170141183460469231731687303715884105727"),
    ("340282366920938463463374607431768211455", "170141183460469231731687303715884105728"),
    ("1", "340282366920938463463374607431768211455"),
    ("340282366920938463463374607431768211456", "1")].all fun (x, y) => D x y == R x y

end Azurite.AzNat
