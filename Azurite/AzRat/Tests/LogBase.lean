/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzRat.LogBase
import Azurite.AzRat.Parse
import Azurite.AzRat.Pow

/-!
# Tests for the logarithms of `AzRat` in a general base
-/

open Azurite Azurite.AzRat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def Fl (b : UInt64) (s : String) : ℤ := floorLogBaseAbs b (Q s)
private def Cl (b : UInt64) (s : String) : ℤ := ceilingLogBaseAbs b (Q s)
private def Ck (b : UInt64) (s : String) : Option ℤ := checkedLogBaseAbs b (Q s)

-- zero (the documented `0`; `none` for the checked logarithm)
#guard Fl 10 "0" == 0
#guard Cl 10 "0" == 0
#guard Ck 10 "0" == none

-- base 10: integers, fractions, negatives (absolute value)
#guard Fl 10 "1" == 0
#guard Fl 10 "9" == 0
#guard Fl 10 "10" == 1
#guard Fl 10 "1/10" == -1
#guard Fl 10 "1/11" == -2
#guard Fl 10 "-250" == 2
#guard Cl 10 "1" == 0
#guard Cl 10 "2" == 1
#guard Cl 10 "10" == 1
#guard Cl 10 "11" == 2
#guard Cl 10 "1/10" == -1
#guard Cl 10 "1/9" == 0
#guard Cl 10 "1/11" == -1
#guard Cl 10 "-250" == 3
#guard Cl 10 "-1000" == 3
#guard Ck 10 "1" == some 0
#guard Ck 10 "10" == some 1
#guard Ck 10 "1/10" == some (-1)
#guard Ck 10 "1/1000" == some (-3)
#guard Ck 10 "-100" == some 2
#guard Ck 10 "2" == none
#guard Ck 10 "1/2" == none
#guard Ck 10 "1000000000000000000" == some 18
#guard Ck 10 "1000000000000000001" == none

-- base 3
#guard Fl 3 "8" == 1
#guard Fl 3 "9" == 2
#guard Fl 3 "1/9" == -2
#guard Fl 3 "1/10" == -3
#guard Cl 3 "8" == 2
#guard Cl 3 "9" == 2
#guard Cl 3 "10" == 3
#guard Cl 3 "1/9" == -2
#guard Cl 3 "1/8" == -1
#guard Cl 3 "1/10" == -2
#guard Ck 3 "3486784401" == some 20
#guard Ck 3 "1/3486784401" == some (-20)
#guard Ck 3 "3486784402" == none
#guard Ck 3 "2/3" == none

-- base 2 agrees with `checkedLogBase2`
#guard Ck 2 "1024" == (Q "1024").checkedLogBase2.map AzInt.toInt
#guard Ck 2 "1/1024" == (Q "1/1024").checkedLogBase2.map AzInt.toInt
#guard Ck 2 "3/4" == none
#guard Cl 2 "3/4" == 0
#guard Cl 2 "5/4" == 1

/-! ## Rational bases -/

private def Flr (b s : String) : Option ℤ := floorLogBaseRatAbs (Q b) (Q s)
private def Clr (b s : String) : Option ℤ := ceilingLogBaseRatAbs (Q b) (Q s)
private def Ckr (b s : String) : Option ℤ := checkedLogBaseRatAbs (Q b) (Q s)

-- invalid bases and zero
#guard Flr "1" "5" == none
#guard Flr "0" "5" == none
#guard Flr "-2" "5" == none
#guard Flr "3/2" "0" == none
#guard Clr "1" "5" == none
#guard Ckr "-3/2" "9/4" == none
#guard Ckr "3/2" "0" == none

-- base 3/2
#guard Flr "3/2" "1" == some 0
#guard Flr "3/2" "9/4" == some 2
#guard Clr "3/2" "9/4" == some 2
#guard Ckr "3/2" "9/4" == some 2
#guard Flr "3/2" "2" == some 1
#guard Clr "3/2" "2" == some 2
#guard Ckr "3/2" "2" == none
#guard Flr "3/2" "-2" == some 1           -- absolute value
#guard Flr "3/2" "1/2" == some (-2)
#guard Clr "3/2" "1/2" == some (-1)
#guard Ckr "3/2" "3/2" == some 1
#guard Ckr "3/2" "8/27" == some (-3)
#guard Ckr "3/2" "4/9" == some (-2)
#guard Ckr "3/2" "2/3" == some (-1)
#guard Flr "3/2" "2/3" == some (-1)
#guard Clr "3/2" "2/3" == some (-1)
private def big : AzRat := AzRat.pow (Q "2") 1000
#guard floorLogBaseRatAbs (Q "3/2") big == some 1709   -- 2^1000
#guard ceilingLogBaseRatAbs (Q "3/2") big == some 1710
#guard floorLogBaseRatAbs (Q "3/2") big⁻¹ == some (-1710)
#guard ceilingLogBaseRatAbs (Q "3/2") big⁻¹ == some (-1709)

-- base 2/3 (below 1): `log_{2/3} x = −log_{3/2} x`
#guard Flr "2/3" "9/4" == some (-2)
#guard Clr "2/3" "9/4" == some (-2)
#guard Ckr "2/3" "9/4" == some (-2)
#guard Flr "2/3" "2" == some (-2)
#guard Clr "2/3" "2" == some (-1)
#guard Flr "2/3" "1/2" == some 1
#guard Clr "2/3" "1/2" == some 2
#guard Ckr "2/3" "4/9" == some 2
#guard Ckr "2/3" "3/2" == some (-1)
#guard Ckr "2/3" "1/2" == none

-- a base close to 1: the exponent is large
#guard Flr "1001/1000" "1000000" == some 13822
#guard Clr "1001/1000" "1000000" == some 13823
#guard Ckr "1001/1000" "1000000" == none
#guard Ckr "1001/1000" "1002001/1000000" == some 2

-- integer bases agree with the `UInt64` versions
#guard Flr "10" "1/11" == some (Fl 10 "1/11")
#guard Clr "10" "-250" == some (Cl 10 "-250")
#guard Ckr "10" "1/1000" == Ck 10 "1/1000"
#guard Ckr "1/10" "1000" == some (-3)
#guard Flr "1/10" "250" == some (-3)
#guard Clr "1/10" "250" == some (-2)

/-! ## Power-of-two bases -/

private def Flp (s : String) (k : Nat) : Option ℤ := floorLogBasePowerOf2Abs (Q s) k
private def Clp (s : String) (k : Nat) : Option ℤ := ceilingLogBasePowerOf2Abs (Q s) k
private def Ckp (s : String) (k : Nat) : Option ℤ := checkedLogBasePowerOf2Abs (Q s) k

#guard Flp "0" 4 == none
#guard Flp "5" 0 == none
#guard Ckp "16" 0 == none
-- base 16
#guard Flp "1" 4 == some 0
#guard Flp "15" 4 == some 0
#guard Flp "16" 4 == some 1
#guard Flp "255" 4 == some 1
#guard Flp "256" 4 == some 2
#guard Flp "1/16" 4 == some (-1)
#guard Flp "1/17" 4 == some (-2)
#guard Flp "1/15" 4 == some (-1)
#guard Flp "-1/2" 4 == some (-1)
#guard Flp "3/4" 4 == some (-1)
#guard Clp "1" 4 == some 0
#guard Clp "2" 4 == some 1
#guard Clp "16" 4 == some 1
#guard Clp "17" 4 == some 2
#guard Clp "1/16" 4 == some (-1)
#guard Clp "1/15" 4 == some 0
#guard Clp "1/17" 4 == some (-1)
#guard Clp "3/4" 4 == some 0
#guard Clp "-1/256" 4 == some (-2)
#guard Ckp "1" 4 == some 0
#guard Ckp "16" 4 == some 1
#guard Ckp "256" 4 == some 2
#guard Ckp "1/16" 4 == some (-1)
#guard Ckp "1/4096" 4 == some (-3)
#guard Ckp "-256" 4 == some 2           -- absolute value
#guard Ckp "2" 4 == none
#guard Ckp "1/2" 4 == none
#guard Ckp "3/16" 4 == none
-- base 8 and base 1024
#guard Flp "1024" 3 == some 3
#guard Clp "1024" 3 == some 4
#guard Ckp "1024" 3 == none
#guard Ckp "512" 3 == some 3
#guard Ckp "1/512" 3 == some (-3)
#guard Ckp "1267650600228229401496703205376" 10 == some 10   -- 2^100 = 1024^10
#guard Ckp "1/1267650600228229401496703205376" 10 == some (-10)
#guard Flp "1267650600228229401496703205375" 10 == some 9
#guard Clp "1267650600228229401496703205377" 10 == some 11
-- base 2 agrees
#guard Flp "1/11" 1 == some (floorLogBase2Abs (Q "1/11"))
#guard Clp "1/11" 1 == some (ceilingLogBase2Abs (Q "1/11"))

