/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzRat.FromSci
import Azurite.AzRat.Parse
import Azurite.AzRat.Shift
import Azurite.AzRat.ToSci
import Azurite.AzRat.ToString

/-!
# Tests for `fromSci`

Expected values from the author's Malachite tests, plus round trips through `toSci`.
-/

open Azurite Azurite.AzRat

private def Q (s : String) : AzRat := (AzRat.parse s).get!

/-- `fromSci` rendered as a fraction, `"<none>"` on rejection. -/
private def F (s : String) (b : UInt64 := 10) : String :=
  ((fromSci s b).map AzRat.toString).getD "<none>"

/-! ## Zero -/

#guard F "0" == "0"
#guard F "00" == "0"
#guard F "+0" == "0"
#guard F "-0" == "0"
#guard F "0.00" == "0"
#guard F "0e1" == "0"
#guard F "0e+1" == "0"
#guard F "0e-1" == "0"
#guard F "+0e+1" == "0"
#guard F "-0e+1" == "0"
#guard F "+0.0e+1" == "0"
#guard F "-0.0e+1" == "0"
#guard F ".0" == "0"
#guard F ".00" == "0"
#guard F ".00e0" == "0"
#guard F ".00e1" == "0"
#guard F ".00e-1" == "0"
#guard F "-.0" == "0"
#guard F "-.00" == "0"
#guard F "-.00e0" == "0"
#guard F "-.00e1" == "0"
#guard F "-.00e-1" == "0"
#guard F "+.0" == "0"
#guard F "+.00" == "0"
#guard F "+.00e0" == "0"
#guard F "+.00e1" == "0"
#guard F "+.00e-1" == "0"

/-! ## Integers -/

#guard F "123" == "123"
#guard F "00123" == "123"
#guard F "+123" == "123"
#guard F "123.00" == "123"
#guard F "123e0" == "123"
#guard F "12.3e1" == "123"
#guard F "1.23e2" == "123"
#guard F "1.23E2" == "123"
#guard F "1.23e+2" == "123"
#guard F "1.23E+2" == "123"
#guard F ".123e3" == "123"
#guard F "0.123e3" == "123"
#guard F "+0.123e3" == "123"
#guard F "0.0123e4" == "123"
#guard F "1230e-1" == "123"
#guard F "12300e-2" == "123"
#guard F "12300E-2" == "123"
#guard F "-123" == "-123"
#guard F "-00123" == "-123"
#guard F "-123.00" == "-123"
#guard F "-123e0" == "-123"
#guard F "-12.3e1" == "-123"
#guard F "-1.23e2" == "-123"
#guard F "-1.23E2" == "-123"
#guard F "-1.23e+2" == "-123"
#guard F "-1.23E+2" == "-123"
#guard F "-.123e3" == "-123"
#guard F "-0.123e3" == "-123"
#guard F "-0.0123e4" == "-123"
#guard F "-1230e-1" == "-123"
#guard F "-12300e-2" == "-123"
#guard F "-12300E-2" == "-123"
#guard F "1." == "1"
#guard F "1.e2" == "100"

/-! ## Fractions -/

#guard F "123.4" == "617/5"
#guard F "123.8" == "619/5"
#guard F "123.5" == "247/2"
#guard F "124.5" == "249/2"
#guard F "127.49" == "12749/100"
#guard F "-123.4" == "-617/5"
#guard F "-123.8" == "-619/5"
#guard F "-123.5" == "-247/2"
#guard F "-124.5" == "-249/2"
#guard F "-127.49" == "-12749/100"
#guard F "-127.5" == "-255/2"
#guard F "0.5" == "1/2"
#guard F "0.3333333333333333" == "3333333333333333/10000000000000000"
#guard F "0.25" == "1/4"
#guard F "0.2" == "1/5"
#guard F "0.125" == "1/8"
#guard F "0.1" == "1/10"
#guard F "0.0" == "0"
#guard F "0.3" == "3/10"
#guard F "0.4" == "2/5"
#guard F "0.6" == "3/5"
#guard F "0.7" == "7/10"
#guard F "0.8" == "4/5"
#guard F "0.9" == "9/10"
#guard F "0.00" == "0"
#guard F "0.10" == "1/10"
#guard F "0.20" == "1/5"
#guard F "0.30" == "3/10"
#guard F "0.40" == "2/5"
#guard F "0.50" == "1/2"
#guard F "0.60" == "3/5"
#guard F "0.70" == "7/10"
#guard F "0.80" == "4/5"
#guard F "0.90" == "9/10"
#guard F "123.456456456456" == "15432057057057/125000000000"
#guard F "2.718281828459045" == "543656365691809/200000000000000"
#guard F "1e-3" == "1/1000"
#guard F "5e-1" == "1/2"
#guard F "25e-2" == "1/4"

/-! ## Rejected -/

#guard F "" == "<none>"
#guard F "+" == "<none>"
#guard F "-" == "<none>"
#guard F "." == "<none>"
#guard F "e" == "<none>"
#guard F "e5" == "<none>"
#guard F "10e" == "<none>"
#guard F "++1" == "<none>"
#guard F "+-1" == "<none>"
#guard F "-+1" == "<none>"
#guard F "--1" == "<none>"
#guard F "1.0.0" == "<none>"
#guard F "1e++1" == "<none>"
#guard F "1e+-1" == "<none>"
#guard F "1e0.1" == "<none>"
#guard F "1e2e3" == "<none>"
#guard F "--.0" == "<none>"
#guard F "++.0" == "<none>"
#guard F ".+2" == "<none>"
#guard F ".-2" == "<none>"
#guard F "1.+2" == "<none>"
#guard F "0.000a" == "<none>"
#guard F "0.00ae-10" == "<none>"
#guard F "0e10000000000000000000000000000" == "<none>"
#guard F "0e-10000000000000000000000000000" == "<none>"
#guard F "0e9223372036854775807" == "0"
#guard F "0e9223372036854775808" == "<none>"
#guard F "0e-9223372036854775808" == "0"
#guard F "0e-9223372036854775809" == "<none>"
#guard F "0.0e-9223372036854775808" == "<none>"
#guard F " 1" == "<none>"
#guard F "1 " == "<none>"
#guard F "0x10" == "<none>"
#guard F "0b1" == "<none>"
#guard F "1_000" == "<none>"
#guard F "1" 1 == "<none>"
#guard F "1" 37 == "<none>"

/-! ## Other bases -/

#guard F "1e+5" 2 == "32"
#guard F "1e5" 2 == "32"
#guard F "1e+5" 3 == "243"
#guard F "1e5" 3 == "243"
#guard F "1e+5" 4 == "1024"
#guard F "1e5" 4 == "1024"
#guard F "1e+5" 5 == "3125"
#guard F "1e5" 5 == "3125"
#guard F "1e+5" 8 == "32768"
#guard F "1e5" 8 == "32768"
#guard F "1e+5" 16 == "1048576"
#guard F "1e5" 16 == "485"
#guard F "1e+5" 32 == "33554432"
#guard F "1e5" 32 == "1477"
#guard F "1e+5" 36 == "60466176"
#guard F "1E+5" 36 == "60466176"
#guard F "1e5" 36 == "1805"
#guard F "ff" 16 == "255"
#guard F "fF" 16 == "255"
#guard F "Ff" 16 == "255"
#guard F "FF" 16 == "255"
#guard F "-ff" 16 == "-255"
#guard F "1e-5" 16 == "1/1048576"
#guard F "f.8" 16 == "31/2"
#guard F "f.8e+1" 16 == "248"
#guard F "f.8e-1" 16 == "31/32"
#guard F "1.01" 2 == "5/4"
#guard F "1.1" 2 == "3/2"
#guard F "1.11" 2 == "7/4"
#guard F "0.01" 2 == "1/4"
#guard F "0.1" 2 == "1/2"
#guard F "0.11" 2 == "3/4"
#guard F "1.1" 3 == "4/3"
#guard F "1.11" 3 == "13/9"
#guard F "1.111" 3 == "40/27"
#guard F "1.112" 3 == "41/27"
#guard F "0.1" 3 == "1/3"
#guard F "0.11" 3 == "4/9"
#guard F "0.111" 3 == "13/27"
#guard F "0.112" 3 == "14/27"
#guard F "2" 2 == "<none>"
#guard F "102" 2 == "<none>"
#guard F "12e4" 2 == "<none>"
#guard F "12e-4" 2 == "<none>"
#guard F "1.2" 2 == "<none>"
#guard F "0.2" 2 == "<none>"
#guard F "0.002" 2 == "<none>"
#guard F "e" 16 == "14"
#guard F "e+1" 16 == "<none>"
#guard F "e" 15 == "14"
#guard F "ee" 15 == "224"
#guard F "e" 14 == "<none>"
#guard F "zz" 36 == "1295"
#guard F "-zz.z" 36 == "-46655/36"

/-! ## Round trips through `toSci` -/

private def RT (q : AzRat) (o : SciOptions := {}) : Option AzRat :=
  (q.toSci o).bind (fromSci · o.base)

#guard RT (Q "0") == some (Q "0")
#guard RT (Q "123") == some (Q "123")
#guard RT (Q "-123") == some (Q "-123")
#guard RT (Q "22/7") == some (Q "3142857142857143/1000000000000000")
#guard RT (Q "-22/7") == some (Q "-3142857142857143/1000000000000000")
#guard RT (Q "1/1000000000") == some (Q "1/1000000000")
#guard RT (Q "1/7") { size := .scale 3 } == some (Q "143/1000")
#guard RT (Q "1/7") { size := .scale 3, format := { includeTrailingZeros := true } }
  == some (Q "143/1000")
#guard RT (Q "1/7") { size := .complete } == none
#guard RT (Q "3/8") { size := .complete } == some (Q "3/8")
#guard RT ((Q "1") <<< 100) == some (Q "1267650600228229000000000000000")
#guard RT ((Q "1") >>> 100)
  == some (Q "7888609052210118/10000000000000000000000000000000000000000000000")
#guard RT (Q "-1/3") { base := 2, size := .precision 10 } == some (Q "-683/2048")
#guard RT (Q "1/3") { base := 16, size := .precision 4 } == some (Q "21845/65536")
#guard RT (Q "255/16") { base := 16, size := .scale 1 } == some (Q "255/16")
#guard RT (Q "255/16") { base := 16, size := .scale 1, format := { lowercase := false } }
  == some (Q "255/16")
#guard RT ((Q "1") <<< 40) { base := 16, size := .precision 3 } == some ((Q "1") <<< 40)
#guard RT ((Q "1") >>> 40) { base := 16, size := .precision 3 } == some ((Q "1") >>> 40)
#guard RT ((Q "1") >>> 40) { base := 16, size := .precision 3, format := { eLowercase := false } }
  == some ((Q "1") >>> 40)
#guard RT (Q "1000000") { format := { negExpThreshold := -3 } } == some (Q "1000000")
#guard RT (Q "1/1000") { format := { negExpThreshold := -3 } } == some (Q "1/1000")
#guard RT (Q "-1/1000") { format := { forceExponentPlusSign := true } } == some (Q "-1/1000")
#guard RT (Q "12345678") { format := { forceExponentPlusSign := true }, size := .precision 3 }
  == some (Q "12300000")
#guard RT (Q "-1/10000000000") { size := .precision 1 } == some (Q "-1/10000000000")
