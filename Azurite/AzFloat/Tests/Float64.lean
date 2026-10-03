/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Arith
import Azurite.AzFloat.Float64
import Azurite.AzFloat.Shift
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for the `Float` conversions
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def inf : Float := 1.0 / 0.0
private def maxF : Float := Float.ofBits 0x7FEFFFFFFFFFFFFF
private def minSub : Float := Float.ofBits 1

/-! ## `ofFloat64` is exact -/

#guard ofFloat64 2.5 == F "5/2" 53
#guard ofFloat64 0.1 == F "1/10" 53
#guard ofFloat64 (-3.0) == F "-3" 53
#guard ofFloat64 1.0 == F "1" 53
#guard ofFloat64 0.0 == zero
#guard ofFloat64 (-0.0) == zero
#guard ofFloat64 inf == infinity true
#guard ofFloat64 (-inf) == infinity false
#guard (ofFloat64 (0.0 / 0.0)).isNaN
#guard ofFloat64 maxF == setPrec ((F "9007199254740991" 53) <<< 971) 53
#guard ofFloat64 minSub == setPrec (one >>> 1074) 53
#guard ofFloat64 (Float.ofBits 0x000FFFFFFFFFFFFF)
  == setPrec ((F "4503599627370495" 52) >>> 1074) 53

/-! ## `toFloat64` -/

#guard toFloat64 (F "1/3" 53) == 1.0 / 3.0
#guard toFloat64 (F "1/10" 53) == 0.1
#guard toFloat64 (F "-5/2" 3) == -2.5
#guard toFloat64 one == 1.0
#guard toFloat64 zero == 0.0
#guard toFloat64 (infinity false) == -inf
#guard (toFloat64 nan).isNaN
#guard toFloat64 (sqrt (F "2" 1000)) == Float.sqrt 2.0
#guard toFloat64 (F "1/3" 100) == 1.0 / 3.0
#guard toFloat64 (F "1/3" 100) .Floor == 1.0 / 3.0                 -- 1.0/3.0 is below 1/3
#guard toFloat64 (F "1/3" 100) .Ceiling
  == Float.ofBits ((1.0 / 3.0 : Float).toBits + 1)
#guard toFloat64 (F "2/3" 100) == 2.0 / 3.0
-- overflow
#guard toFloat64 (one <<< 2000) == inf
#guard toFloat64 (one <<< 2000) .Down == maxF
#guard toFloat64 (one <<< 2000) .Floor == maxF
#guard toFloat64 (one <<< 2000) .Ceiling == inf
#guard toFloat64 (-(one <<< 2000)) .Ceiling == -maxF
#guard toFloat64 (-(one <<< 2000)) .Floor == -inf
#guard toFloat64 (ofFloat64 maxF + setPrec (one <<< 970) 53) == inf     -- tie, to even (∞)
#guard toFloat64 (ofFloat64 maxF + setPrec (one <<< 969) 53) == maxF
-- subnormals
#guard toFloat64 (one >>> 1074) == minSub
#guard toFloat64 (one >>> 1075) == 0.0                                           -- tie to even: 0
#guard toFloat64 (one >>> 1075) .Up == minSub
#guard toFloat64 (one >>> 1076) == 0.0
#guard toFloat64 ((F "3" 2) >>> 1076) == minSub                 -- 0.75 ulp → 1 ulp
#guard toFloat64 ((F "3" 2) >>> 1075) == Float.ofBits 2         -- 1.5 ulp → 2 ulp (even)
#guard toFloat64 ((F "5" 3) >>> 1075) == Float.ofBits 2         -- 2.5 ulp → 2 ulp (even)
#guard toFloat64 (one >>> 1022) == Float.ofBits 0x0010000000000000   -- least normal
#guard toFloat64 (one >>> 1023) == Float.ofBits 0x0008000000000000   -- subnormal 2^-1023

/-! ## Round trips -/

private def rt (x : AzFloat) : Bool := ofFloat64 (toFloat64 x) == x
#guard rt (F "1/3" 53)
#guard rt (F "1/10" 53)
#guard rt (setPrec (one <<< 1000) 53)
#guard rt (setPrec (one >>> 1000) 53)
#guard rt (setPrec (one >>> 1074) 53)
#guard rt (ofFloat64 maxF)
private def rtf (f : Float) : Bool := toFloat64 (ofFloat64 f) == f
#guard rtf 2.5
#guard rtf 0.1
#guard rtf (-1e300)
#guard rtf maxF
#guard rtf minSub
#guard rtf inf
