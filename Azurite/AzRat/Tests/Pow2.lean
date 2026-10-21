/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzRat.Pow2
import Azurite.AzRat.LogBase2
import Azurite.AzRat.Parse
import Azurite.AzInt.Conversion

/-!
# Tests for `AzRat.isPowerOfTwo` and `AzRat.checkedLogBase2`
-/

open Azurite Azurite.AzRat

private def Q (s : String) : AzRat := (AzRat.parse s).get!

#guard (Q "1").isPowerOfTwo == true
#guard (Q "2").isPowerOfTwo == true
#guard (Q "8").isPowerOfTwo == true
#guard (Q "1/8").isPowerOfTwo == true
#guard (Q "1267650600228229401496703205376").isPowerOfTwo == true
#guard (Q "0").isPowerOfTwo == false
#guard (Q "-8").isPowerOfTwo == false
#guard (Q "-1/8").isPowerOfTwo == false
#guard (Q "3").isPowerOfTwo == false
#guard (Q "6").isPowerOfTwo == false
#guard (Q "3/4").isPowerOfTwo == false
#guard (Q "1/6").isPowerOfTwo == false
#guard (Q "1").powerOfTwoExponent.toInt64 == 0
#guard (Q "8").powerOfTwoExponent.toInt64 == 3
#guard (Q "1/8").powerOfTwoExponent.toInt64 == -3
#guard (Q "1267650600228229401496703205376").powerOfTwoExponent.toInt64 == 100
#guard (Q "1/1267650600228229401496703205376").powerOfTwoExponent.toInt64 == -100

private def L (s : String) : Option Int64 := (Q s).checkedLogBase2.map AzInt.toInt64
#guard L "1" == some 0
#guard L "2" == some 1
#guard L "8" == some 3
#guard L "1/8" == some (-3)
#guard L "1/2" == some (-1)
#guard L "1267650600228229401496703205376" == some 100
#guard L "1/1267650600228229401496703205376" == some (-100)
#guard L "0" == none
#guard L "-1" == none
#guard L "-8" == none
#guard L "3" == none
#guard L "6" == none
#guard L "3/4" == none
#guard L "1/6" == none

