/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.LogBase2
import Azurite.AzNat.ParseBase

/-!
# Tests for the base-2 logarithms of `AzNat`
-/

namespace Azurite

private def N (s : String) : AzNat := (AzNat.parse s).get!

#guard (N "0").checkedLogBase2 == none
#guard (N "1").checkedLogBase2 == some 0
#guard (N "2").checkedLogBase2 == some 1
#guard (N "3").checkedLogBase2 == none
#guard (N "1024").checkedLogBase2 == some 10
#guard (N "1023").checkedLogBase2 == none
#guard (N "18446744073709551616").checkedLogBase2 == some 64          -- 2^64
#guard (N "18446744073709551615").checkedLogBase2 == none
#guard (N "1267650600228229401496703205376").checkedLogBase2 == some 100  -- 2^100
#guard (N "1267650600228229401496703205377").checkedLogBase2 == none
#guard (N "2535301200456458802993406410752").checkedLogBase2 == some 101

#guard (N "0").floorLogBase2 == none
#guard (N "1").floorLogBase2 == some 0
#guard (N "2").floorLogBase2 == some 1
#guard (N "3").floorLogBase2 == some 1
#guard (N "4").floorLogBase2 == some 2
#guard (N "1023").floorLogBase2 == some 9
#guard (N "1024").floorLogBase2 == some 10
#guard (N "1025").floorLogBase2 == some 10
#guard (N "18446744073709551615").floorLogBase2 == some 63
#guard (N "18446744073709551616").floorLogBase2 == some 64
#guard (N "1267650600228229401496703205377").floorLogBase2 == some 100

#guard (N "0").ceilingLogBase2 == none
#guard (N "1").ceilingLogBase2 == some 0
#guard (N "2").ceilingLogBase2 == some 1
#guard (N "3").ceilingLogBase2 == some 2
#guard (N "4").ceilingLogBase2 == some 2
#guard (N "5").ceilingLogBase2 == some 3
#guard (N "1023").ceilingLogBase2 == some 10
#guard (N "1024").ceilingLogBase2 == some 10
#guard (N "1025").ceilingLogBase2 == some 11
#guard (N "18446744073709551615").ceilingLogBase2 == some 64
#guard (N "18446744073709551616").ceilingLogBase2 == some 64
#guard (N "18446744073709551617").ceilingLogBase2 == some 65
#guard (N "1267650600228229401496703205377").ceilingLogBase2 == some 101

-- base 16 (`k = 4`) and base 8 (`k = 3`)
#guard (N "0").floorLogBasePowerOf2 4 == none
#guard (N "1").floorLogBasePowerOf2 0 == none
#guard (N "1").floorLogBasePowerOf2 4 == some 0
#guard (N "15").floorLogBasePowerOf2 4 == some 0
#guard (N "16").floorLogBasePowerOf2 4 == some 1
#guard (N "255").floorLogBasePowerOf2 4 == some 1
#guard (N "256").floorLogBasePowerOf2 4 == some 2
#guard (N "4096").floorLogBasePowerOf2 4 == some 3
#guard (N "18446744073709551616").floorLogBasePowerOf2 4 == some 16
#guard (N "18446744073709551615").floorLogBasePowerOf2 4 == some 15
#guard (N "511").floorLogBasePowerOf2 3 == some 2
#guard (N "512").floorLogBasePowerOf2 3 == some 3
#guard (N "1024").floorLogBasePowerOf2 3 == some 3   -- 2^10 = 8^3 · 4
#guard (N "0").ceilingLogBasePowerOf2 4 == none
#guard (N "1").ceilingLogBasePowerOf2 4 == some 0
#guard (N "2").ceilingLogBasePowerOf2 4 == some 1
#guard (N "16").ceilingLogBasePowerOf2 4 == some 1
#guard (N "17").ceilingLogBasePowerOf2 4 == some 2
#guard (N "256").ceilingLogBasePowerOf2 4 == some 2
#guard (N "257").ceilingLogBasePowerOf2 4 == some 3
#guard (N "18446744073709551616").ceilingLogBasePowerOf2 4 == some 16
#guard (N "18446744073709551617").ceilingLogBasePowerOf2 4 == some 17
#guard (N "512").ceilingLogBasePowerOf2 3 == some 3
#guard (N "513").ceilingLogBasePowerOf2 3 == some 4
#guard (N "1024").ceilingLogBasePowerOf2 3 == some 4
#guard (N "0").checkedLogBasePowerOf2 4 == none
#guard (N "1").checkedLogBasePowerOf2 0 == none
#guard (N "1").checkedLogBasePowerOf2 4 == some 0
#guard (N "2").checkedLogBasePowerOf2 4 == none
#guard (N "16").checkedLogBasePowerOf2 4 == some 1
#guard (N "32").checkedLogBasePowerOf2 4 == none
#guard (N "256").checkedLogBasePowerOf2 4 == some 2
#guard (N "18446744073709551616").checkedLogBasePowerOf2 4 == some 16
#guard (N "18446744073709551616").checkedLogBasePowerOf2 3 == none   -- 3 ∤ 64
#guard (N "1267650600228229401496703205376").checkedLogBasePowerOf2 10 == some 10 -- 1024^10
#guard (N "1267650600228229401496703205376").checkedLogBasePowerOf2 3 == none

end Azurite
