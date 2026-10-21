/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.LogBase
import Azurite.AzNat.ParseBase

/-!
# Tests for the logarithms of `AzNat` in a general base
-/

namespace Azurite

private def N (s : String) : AzNat := (AzNat.parse s).get!
private def Fl (b n : String) : Option Nat := AzNat.floorLogBase (N b) (N n)
private def Cl (b n : String) : Option Nat := AzNat.ceilingLogBase (N b) (N n)
private def Ck (b n : String) : Option Nat := AzNat.checkedLogBase (N b) (N n)

-- degenerate bases and zero
#guard Fl "0" "5" == none
#guard Fl "1" "5" == none
#guard Fl "2" "0" == none
#guard Cl "1" "5" == none
#guard Ck "1" "1" == none
#guard Ck "3" "0" == none

-- base 10
#guard Fl "10" "1" == some 0
#guard Fl "10" "9" == some 0
#guard Fl "10" "10" == some 1
#guard Fl "10" "99" == some 1
#guard Fl "10" "100" == some 2
#guard Fl "10" "999999999999999999" == some 17
#guard Fl "10" "1000000000000000000" == some 18
#guard Fl "10" "1000000000000000001" == some 18
#guard Cl "10" "1" == some 0
#guard Cl "10" "2" == some 1
#guard Cl "10" "10" == some 1
#guard Cl "10" "11" == some 2
#guard Cl "10" "100" == some 2
#guard Cl "10" "101" == some 3
#guard Ck "10" "1" == some 0
#guard Ck "10" "10" == some 1
#guard Ck "10" "100" == some 2
#guard Ck "10" "1000000000000000000" == some 18
#guard Ck "10" "1000000000000000001" == none
#guard Ck "10" "99" == none

-- base 3, around the powers
#guard Fl "3" "2" == some 0
#guard Fl "3" "3" == some 1
#guard Fl "3" "8" == some 1
#guard Fl "3" "9" == some 2
#guard Fl "3" "3486784400" == some 19   -- 3^20 − 1
#guard Fl "3" "3486784401" == some 20   -- 3^20
#guard Fl "3" "3486784402" == some 20
#guard Cl "3" "3486784400" == some 20
#guard Cl "3" "3486784401" == some 20
#guard Cl "3" "3486784402" == some 21
#guard Ck "3" "3486784401" == some 20
#guard Ck "3" "3486784402" == none

-- base 2 agrees with the base-2 functions
#guard Fl "2" "1023" == some 9
#guard Fl "2" "1024" == some 10
#guard Cl "2" "1025" == some 11
#guard Ck "2" "1024" == some 10

-- large arguments and bases: 2^200 in base 7, base 2^100 + 1
#guard Fl "7" "1606938044258990275541962092341162602522202993782792835301376" == some 71
#guard Ck "7" "1606938044258990275541962092341162602522202993782792835301376" == none
#guard Fl "1267650600228229401496703205377"
  "1606938044258990275541962092341162602522202993782792835301376" == some 1
#guard Cl "1267650600228229401496703205377"
  "1606938044258990275541962092341162602522202993782792835301376" == some 2
#guard Fl "1267650600228229401496703205376"
  "1606938044258990275541962092341162602522202993782792835301376" == some 2
#guard Ck "1267650600228229401496703205376"
  "1606938044258990275541962092341162602522202993782792835301376" == some 2
-- base 1000, 1000^100 and its neighbors
private def p : String := "1" ++ "".pushn '0' 300
#guard Fl "1000" p == some 100
#guard Ck "1000" p == some 100
#guard Fl "1000" ("9" ++ "".pushn '9' 299) == some 99
#guard Cl "1000" ("9" ++ "".pushn '9' 299) == some 100
#guard Cl "1000" ("1" ++ "".pushn '0' 299 ++ "1") == some 101

end Azurite
