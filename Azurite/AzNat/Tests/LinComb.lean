/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.LinComb
import Azurite.AzNat.ParseBase

/-!
# Tests for `AzNat.linComb`
-/

namespace Azurite

private def N (s : String) : AzNat := (AzNat.parse s).get!

private def L (x y : String) (s t : Nat) : String := toString (AzNat.linComb (N x) (N y) s t)

#guard L "0" "0" 0 0 == "0"
#guard L "0" "0" 5 7 == "0"
#guard L "3" "4" 0 0 == "0"
#guard L "3" "4" 5 0 == "15"
#guard L "3" "4" 0 7 == "28"
#guard L "3" "4" 5 7 == "43"
#guard L "0" "4" 5 7 == "28"
#guard L "3" "0" 5 7 == "15"
-- carries across limbs: (2^64 − 1) · (2^63 − 1) twice
#guard L "18446744073709551615" "18446744073709551615" 9223372036854775807 9223372036854775807
  == "340282366920938463408034375210639556610"
-- operands of different lengths
#guard L "340282366920938463463374607431768211455" "1" 3 2
  == "1020847100762815390390123822295304634367"
#guard L "1" "340282366920938463463374607431768211455" 2 3
  == "1020847100762815390390123822295304634367"
-- a coefficient of 2^63 or more: the general products
#guard L "3" "4" 9223372036854775808 1 == "27670116110564327428"
#guard L "3" "4" 1 18446744073709551616 == "73786976294838206467"
#guard L "18446744073709551616" "5" 340282366920938463463374607431768211456 1
  == "6277101735386680763835789423207666416102355444464034512901"

end Azurite
