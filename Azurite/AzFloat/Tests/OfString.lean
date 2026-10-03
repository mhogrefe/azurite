/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Arith
import Azurite.AzFloat.OfString
import Azurite.AzFloat.Shift
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for decimal input
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def R (s : String) (p : Nat) (m : RoundingMode := .Nearest) : Option (AzFloat × Ordering) :=
  ofDecimalStringRound s p m

/-! ## Values and tags -/

#guard R "0.1" 53 == some (F "1/10" 53, .gt)                         -- binary64 0.1 is above 1/10
#guard R "0.1" 53 .Floor == some (F "1/10" 53 - (F "1/10" 53).ulp?.get!, .lt)
#guard R "1.5e-30" 53 == some (F "15/10000000000000000000000000000000" 53, .lt)
#guard R "-2" 5 == some (F "-2" 5, .eq)
#guard R "+2.50" 4 == some (F "5/2" 4, .eq)
#guard R "1E3" 1 == some (F "1024" 1, .gt)
#guard R "0" 7 == some (zero, .eq)
#guard R "0.000" 7 == some (zero, .eq)
#guard R "123456789" 20 == some (F "123456789" 20, .lt)                -- 27 bits, rounded down

/-! ## Special values and rejections -/

#guard R "NaN" 3 == some (nan, .eq)
#guard R "Infinity" 3 == some (infinity true, .eq)
#guard R "-Infinity" 3 == some (infinity false, .eq)
#guard R "inf" 3 == none
#guard R "1/3" 3 == none
#guard R "1.2.3" 3 == none
#guard R "" 3 == none
#guard R "0x10" 3 == none

/-! ## Round trips through `toString` -/

private def rt (x : AzFloat) : Bool :=
  ofDecimalString (toString x) (x.precision?.getD 1) == some x

#guard rt (F "1/3" 53)
#guard rt (F "1/10" 53)
#guard rt (sqrt (F "2" 53))
#guard rt (sqrt (F "2" 1000))
#guard rt (F "1000000" 20)
#guard rt (one >>> 17 |> fun x => setPrec x 1)
#guard rt (one <<< 1000)
#guard rt (F "-1/3" 2)
#guard rt (F "12676506002282294014967032053760" 53)
#guard ofDecimalString "NaN" 5 == some nan
#guard ofDecimalString "-Infinity" 5 == some (infinity false)
#guard ofDecimalString (toString zero) 5 == some zero
