/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzRat.LengthAfterPoint
import Azurite.AzRat.LogBase
import Azurite.AzRat.Parse
import Azurite.AzRat.Shift
import Azurite.AzRat.Unary
import Azurite.AzRat.ToSci

/-!
# Tests for `toSci` and its helpers

Expected values from the author's Malachite tests and doc examples.
-/

open Azurite Azurite.AzRat

private def Q (s : String) : AzRat := (AzRat.parse s).get!

/-! ## `lengthAfterPoint` -/

#guard lengthAfterPoint 10 (Q "3/8") == some 3        -- 0.375
#guard lengthAfterPoint 10 (Q "1/20") == some 2       -- 0.05
#guard lengthAfterPoint 10 (Q "1/7") == none          -- non-terminating
#guard lengthAfterPoint 21 (Q "1/7") == some 1        -- 0.3 in base 21
#guard lengthAfterPoint 10 (Q "5") == some 0
#guard lengthAfterPoint 10 (Q "0") == some 0
#guard lengthAfterPoint 2 (Q "1/1024") == some 10
#guard lengthAfterPoint 4 (Q "1/1024") == some 5
#guard lengthAfterPoint 8 (Q "1/1024") == some 4      -- ⌈10/3⌉
#guard lengthAfterPoint 36 (Q "1/3") == some 1
#guard lengthAfterPoint 36 (Q "1/48") == some 2       -- 48 = 2^4·3: ⌈4/2⌉ = 2, ⌈1/2⌉ = 1
#guard lengthAfterPoint 10 (Q "1/1000000000000000000000") == some 21
#guard lengthAfterPoint 10 (Q "1/3000000000000000000000") == none
#guard lengthAfterPoint 1 (Q "1/2") == none
#guard lengthAfterPoint 37 (Q "1/2") == none

/-! ## `floorLogBaseAbs` -/

#guard floorLogBaseAbs 10 (Q "22/7") == 0
#guard floorLogBaseAbs 10 (Q "-22/7") == 0
#guard floorLogBaseAbs 10 (Q "936851431250/1397") == 8        -- 6.70617e8
#guard floorLogBaseAbs 10 (Q "123/45678909876") == -9         -- 2.69e-9
#guard floorLogBaseAbs 10 ((Q "1") >>> 30) == -10             -- 2^-30 ≈ 9.3e-10
#guard floorLogBaseAbs 10 ((Q "1") <<< 1000000) == 301029
#guard floorLogBaseAbs 10 ((Q "1") >>> 1000000) == -301030
#guard floorLogBaseAbs 10 (Q "1") == 0
#guard floorLogBaseAbs 10 (Q "10") == 1
#guard floorLogBaseAbs 10 (Q "9") == 0
#guard floorLogBaseAbs 10 (Q "1/10") == -1
#guard floorLogBaseAbs 10 (Q "1/11") == -2
#guard floorLogBaseAbs 10 (Q "999999999999999999999") == 20
#guard floorLogBaseAbs 10 (Q "1000000000000000000000") == 21
#guard floorLogBaseAbs 2 (Q "22/7") == 1
#guard floorLogBaseAbs 16 (Q "1/16") == -1
#guard floorLogBaseAbs 16 (Q "1/17") == -2
#guard floorLogBaseAbs 8 (Q "64") == 2
#guard floorLogBaseAbs 8 (Q "63") == 1
#guard floorLogBaseAbs 3 (Q "1/3") == -1
#guard floorLogBaseAbs 3 (Q "1/2") == -1
#guard floorLogBaseAbs 3 (Q "2") == 0
#guard floorLogBaseAbs 3 (Q "3") == 1
#guard floorLogBaseAbs 3 (Q "26") == 2
#guard floorLogBaseAbs 3 (Q "27") == 3
#guard floorLogBaseAbs 36 (Q "1296") == 2
#guard floorLogBaseAbs 36 (Q "1295") == 1

/-! ## `toSci` with the default options (Malachite `test_to_sci`) -/

private def S (s : String) : String := (Q s).toSciString

#guard S "1/2" == "0.5"
#guard S "1/3" == "0.3333333333333333"
#guard S "1/4" == "0.25"
#guard S "1/5" == "0.2"
#guard S "1/6" == "0.1666666666666667"
#guard S "1/7" == "0.1428571428571429"
#guard S "1/8" == "0.125"
#guard S "1/9" == "0.1111111111111111"
#guard S "1/10" == "0.1"
#guard S "1/11" == "0.09090909090909091"
#guard S "1/137" == "0.007299270072992701"
#guard S "22/7" == "3.142857142857143"
#guard S "245850922/78256779" == "3.141592653589793"
#guard S "936851431250/1397" == "670616629.3843951"
#guard S "1/123456789" == "8.100000073710001e-9"
#guard S "0" == "0"
#guard S "1" == "1"
#guard S "10" == "10"
#guard S "1000000000000000" == "1000000000000000"
#guard S "10000000000000000" == "1e16"
#guard S "100000000000000000" == "1e17"
#guard S "1/100000" == "0.00001"
#guard S "1/1000000" == "1e-6"
#guard S "1/10000000" == "1e-7"
#guard S "999999999999999" == "999999999999999"
#guard S "9999999999999999" == "9999999999999999"
#guard S "99999999999999999" == "1e17"
#guard S "999999999999999999" == "1e18"
#guard S "-1" == "-1"
#guard S "-1000000000000000" == "-1000000000000000"
#guard S "-10000000000000000" == "-1e16"
#guard S "-1/100000" == "-0.00001"
#guard S "-1/1000000" == "-1e-6"
-- `2^±100000` (Malachite tests `2^±1000000`, which takes minutes in the interpreter; the
-- expected strings below come from an exact independent computation checked against
-- Malachite's values at `2^±1000000`)
#guard ((Q "1") <<< 100000).toSciString == "9.990020930143845e30102"
#guard (-((Q "1") <<< 100000)).toSciString == "-9.990020930143845e30102"
#guard ((Q "1") >>> 100000).toSciString == "1.000998903798694e-30103"
#guard (-((Q "1") >>> 100000)).toSciString == "-1.000998903798694e-30103"

/-! ## `toSci` with options (Malachite `test_to_sci_with_options`) -/

private def U128 : AzRat := Q "340282366920938463463374607431768211455"
private def U64 : AzRat := Q "18446744073709551615"
private def T (q : AzRat) (o : SciOptions) : String := (q.toSci o).getD "<none>"
private def O : SciOptions := {}

#guard T (Q "0") { O with format := { includeTrailingZeros := true } } == "0.000000000000000"
#guard T (Q "1") { O with format := { includeTrailingZeros := true } } == "1.000000000000000"
#guard T (Q "10") { O with format := { includeTrailingZeros := true } } == "10.00000000000000"
#guard T (Q "100000000000000") { O with format := { includeTrailingZeros := true } }
  == "100000000000000.0"
#guard T (Q "1000000000000000") { O with format := { includeTrailingZeros := true } }
  == "1000000000000000"
#guard T (Q "10000000000000000") { O with format := { includeTrailingZeros := true } }
  == "1.000000000000000e16"
#guard T U64 { O with format := { includeTrailingZeros := true } } == "1.844674407370955e19"
#guard T U128 { O with format := { includeTrailingZeros := true } } == "3.402823669209385e38"
#guard T (Q "999999999999999") { O with format := { includeTrailingZeros := true } }
  == "999999999999999.0"
#guard T (Q "99999999999999999") { O with format := { includeTrailingZeros := true } }
  == "1.000000000000000e17"
#guard T U128 { O with base := 2 } == "1e128"
#guard T U128 { O with base := 3 } == "2.022011021210021e80"
#guard T U128 { O with base := 4 } == "1e64"
#guard T U128 { O with base := 5 } == "1.103111044120131e55"
#guard T U128 { O with base := 8 } == "4e42"
#guard T U128 { O with base := 16 } == "1e+32"
#guard T U128 { O with base := 32 } == "8e+25"
#guard T U128 { O with base := 36 } == "f.5lxx1zz5pnorynqe+24"
#guard T U128 { O with base := 3, format := { forceExponentPlusSign := true } }
  == "2.022011021210021e+80"
#guard T U128 { O with base := 36, format := { lowercase := false } } == "F.5LXX1ZZ5PNORYNQe+24"
#guard T U128 { O with base := 36, format := { eLowercase := false } } == "f.5lxx1zz5pnorynqE+24"
#guard T U128 { O with base := 36, format := { lowercase := false, eLowercase := false } }
  == "F.5LXX1ZZ5PNORYNQE+24"
#guard T U128 { O with base := 2, size := .complete }
  == "11111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111"
#guard T U128 { O with base := 3, size := .complete }
  == "202201102121002021012000211012011021221022212021111001022110211020010021100121010"
#guard T U128 { O with base := 4, size := .complete }
  == "3333333333333333333333333333333333333333333333333333333333333333"
#guard T U128 { O with base := 8, size := .complete } == "3777777777777777777777777777777777777777777"
#guard T U128 { O with base := 16, size := .complete } == "ffffffffffffffffffffffffffffffff"
#guard T U128 { O with base := 32, size := .complete } == "7vvvvvvvvvvvvvvvvvvvvvvvvv"
#guard T U128 { O with base := 36, size := .complete } == "f5lxx1zz5pnorynqglhzmsp33"
-- precision 4, trailing zeros
#guard T (Q "0") { O with size := .precision 4, format := { includeTrailingZeros := true } } == "0.000"
#guard T (Q "1") { O with size := .precision 4, format := { includeTrailingZeros := true } } == "1.000"
#guard T (Q "10") { O with size := .precision 4, format := { includeTrailingZeros := true } } == "10.00"
#guard T (Q "100") { O with size := .precision 4, format := { includeTrailingZeros := true } } == "100.0"
#guard T (Q "1000") { O with size := .precision 4, format := { includeTrailingZeros := true } } == "1000"
#guard T (Q "10000") { O with size := .precision 4, format := { includeTrailingZeros := true } } == "1.000e4"
#guard T (Q "999") { O with size := .precision 4, format := { includeTrailingZeros := true } } == "999.0"
#guard T (Q "9999") { O with size := .precision 4, format := { includeTrailingZeros := true } } == "9999"
#guard T (Q "99999") { O with size := .precision 4, format := { includeTrailingZeros := true } } == "1.000e5"
#guard T (Q "0") { O with size := .precision 4 } == "0"
#guard T (Q "10000") { O with size := .precision 4 } == "1e4"
#guard T (Q "99999") { O with size := .precision 4 } == "1e5"
-- precision 1
#guard T (Q "0") { O with size := .precision 1, format := { includeTrailingZeros := true } } == "0"
#guard T (Q "1") { O with size := .precision 1 } == "1"
#guard T (Q "10") { O with size := .precision 1 } == "1e1"
#guard T (Q "9") { O with size := .precision 1 } == "9"
#guard T (Q "99") { O with size := .precision 1 } == "1e2"
#guard T (Q "99999") { O with size := .precision 1 } == "1e5"
-- scale 2
#guard T (Q "0") { O with size := .scale 2, format := { includeTrailingZeros := true } } == "0.00"
#guard T (Q "1") { O with size := .scale 2, format := { includeTrailingZeros := true } } == "1.00"
#guard T (Q "99999") { O with size := .scale 2, format := { includeTrailingZeros := true } } == "99999.00"
#guard T (Q "0") { O with size := .scale 2 } == "0"
#guard T (Q "999") { O with size := .scale 2 } == "999"
-- doc examples: 22/7
#guard T (Q "22/7") { O with size := .precision 3 } == "3.14"
#guard T (Q "22/7") { O with size := .precision 3, mode := .Ceiling } == "3.15"
#guard T (Q "22/7") { O with base := 20 } == "3.2h2h2h2h2h2h2h3"
#guard T (Q "22/7") { O with base := 2, mode := .Floor, size := .precision 19 } == "11.001001001001001"
private def OB2 : SciOptions := { O with base := 2, mode := .Floor, size := .precision 19 }
#guard T (Q "22/7") { OB2 with format := { includeTrailingZeros := true } } == "11.00100100100100100"
#guard T (Q "936851431250/1397") { O with size := .precision 6 } == "6.70617e8"
#guard T (Q "123/45678909876") { O with format := { negExpThreshold := -10 } }
  == "0.000000002692708743135418"
#guard T ((Q "1") >>> 30) O == "9.313225746154785e-10"
#guard T ((Q "1") >>> 30) { O with size := .complete } == "9.31322574615478515625e-10"
#guard T (Q "1/3") { O with size := .complete } == "<none>"
#guard T (Q "1/3") { O with size := .complete, base := 36 } == "0.c"
-- validity / exactness
#guard (Q "123").toSciExact O == true
#guard U128.toSciExact O == false
#guard U128.toSciExact { O with size := .precision 50 } == true
#guard (Q "1/3").toSciExact { O with size := .complete } == false
#guard (Q "1/3").toSciExact { O with size := .complete, base := 36 } == true
#guard (Q "1/3").toSci { O with base := 1 } == none

-- rounding modes at precision 2
#guard T (Q "123") { O with size := .precision 2 } == "1.2e2"
#guard T (Q "123") { O with size := .precision 2, mode := .Down } == "1.2e2"
#guard T (Q "123") { O with size := .precision 2, mode := .Floor } == "1.2e2"
#guard T (Q "123") { O with size := .precision 2, mode := .Up } == "1.3e2"
#guard T (Q "123") { O with size := .precision 2, mode := .Ceiling } == "1.3e2"
#guard T (Q "135") { O with size := .precision 2 } == "1.4e2"
#guard T (Q "135") { O with size := .precision 2, mode := .Down } == "1.3e2"
#guard T (Q "135") { O with size := .precision 2, mode := .Floor } == "1.3e2"
#guard T (Q "135") { O with size := .precision 2, mode := .Up } == "1.4e2"
#guard T (Q "135") { O with size := .precision 2, mode := .Ceiling } == "1.4e2"
#guard T (Q "140") { O with size := .precision 2 } == "1.4e2"
#guard (Q "140").toSciExact { O with size := .precision 2 } == true
#guard (Q "135").toSciExact { O with size := .precision 2 } == false
#guard T (Q "999") { O with size := .precision 2 } == "1e3"
#guard T (Q "999") { O with size := .precision 2, mode := .Down } == "9.9e2"
#guard T (Q "999") { O with size := .precision 2, mode := .Floor } == "9.9e2"
#guard T (Q "999") { O with size := .precision 2, mode := .Up } == "1e3"
#guard T (Q "999") { O with size := .precision 2, mode := .Ceiling } == "1e3"
-- negatives
private def I128MAX : AzRat := Q "170141183460469231731687303715884105727"
private def I128MIN : AzRat := Q "-170141183460469231731687303715884105728"
#guard T (Q "-1") { O with format := { includeTrailingZeros := true } } == "-1.000000000000000"
#guard T (Q "-100000000000000") { O with format := { includeTrailingZeros := true } }
  == "-100000000000000.0"
#guard T (Q "-10000000000000000") { O with format := { includeTrailingZeros := true } }
  == "-1.000000000000000e16"
#guard T I128MIN { O with format := { includeTrailingZeros := true } } == "-1.701411834604692e38"
#guard T (Q "-999999999999999999") { O with format := { includeTrailingZeros := true } }
  == "-1.000000000000000e18"
#guard T I128MAX { O with base := 2 } == "1e127"
#guard T I128MIN { O with base := 2 } == "-1e127"
#guard T I128MAX { O with base := 3 } == "1.01100201022001e80"
#guard T I128MIN { O with base := 36 } == "-7.ksyyizzkutudzbve+24"
#guard T I128MIN { O with base := 36, format := { lowercase := false, eLowercase := false } }
  == "-7.KSYYIZZKUTUDZBVE+24"
#guard T I128MAX { O with base := 16, size := .complete } == "7fffffffffffffffffffffffffffffff"

-- negative values and rounding modes
#guard T (Q "-123") { O with size := .precision 2, mode := .Floor } == "-1.3e2"
#guard T (Q "-123") { O with size := .precision 2, mode := .Ceiling } == "-1.2e2"
#guard T (Q "-135") { O with size := .precision 2 } == "-1.4e2"
#guard T (Q "-135") { O with size := .precision 2, mode := .Down } == "-1.3e2"
#guard T (Q "-135") { O with size := .precision 2, mode := .Up } == "-1.4e2"
#guard T (Q "-999") { O with size := .precision 2, mode := .Down } == "-9.9e2"
#guard T (Q "-999") { O with size := .precision 2, mode := .Floor } == "-1e3"
#guard T (Q "-999") { O with size := .precision 2, mode := .Ceiling } == "-9.9e2"
#guard T (Q "-10000") { O with size := .precision 4, format := { includeTrailingZeros := true } }
  == "-1.000e4"
#guard T (Q "-99999") { O with size := .precision 1 } == "-1e5"
#guard T (Q "-9999") { O with size := .scale 2, format := { includeTrailingZeros := true } }
  == "-9999.00"
-- fractions with a scale
#guard T (Q "1/3") { O with size := .scale 2 } == "0.33"
#guard T (Q "1/3") { O with size := .scale 1 } == "0.3"
#guard T (Q "1/3") { O with size := .scale 0 } == "0"
#guard T (Q "1/300") { O with size := .scale 4 } == "0.0033"
#guard T (Q "1/300") { O with size := .scale 3 } == "0.003"
#guard T (Q "1/300") { O with size := .scale 2 } == "0"
#guard T (Q "1/300") { O with size := .scale 1 } == "0"

-- complete expansions
#guard T (Q "1/2") { O with size := .complete } == "0.5"
#guard T (Q "1/8") { O with size := .complete } == "0.125"
#guard T (Q "1/8") { O with size := .complete, base := 2 } == "0.001"
#guard T (Q "1/9") { O with size := .complete, base := 3 } == "0.01"
#guard T (Q "1/8") { O with size := .complete, base := 4 } == "0.02"
#guard T (Q "1/9") { O with size := .complete, base := 6 } == "0.04"
#guard T (Q "1/7") { O with size := .complete, base := 7 } == "0.1"
#guard T (Q "1/3") { O with size := .complete, base := 9 } == "0.3"
-- the smallest positive `f32` subnormal, `2^-149`
private def F32MIN : AzRat := (Q "1") >>> 149
#guard T F32MIN { O with size := .complete }
  == "1.40129846432481707092372958328991613128026194187651577175706828388979108268586060148663818836212158203125e-45"
#guard T F32MIN { O with size := .complete, base := 2 } == "1e-149"
#guard T F32MIN { O with size := .complete, base := 32 } == "2e-30"
#guard T F32MIN { O with size := .complete, base := 36 }
  == "1.whin9rvdkphvrmxkdwtoq8t963n428tj1p07aaum2yy14ie-29"
#guard T F32MIN { O with size := .complete, base := 36, format := { lowercase := false } }
  == "1.WHIN9RVDKPHVRMXKDWTOQ8T963N428TJ1P07AAUM2YY14Ie-29"
#guard T F32MIN { O with size := .complete, format := { negExpThreshold := -200 } }
  == "0.00000000000000000000000000000000000000000000140129846432481707092372958328991613128026194187651577175706828388979108268586060148663818836212158203125"
-- the exponent threshold
#guard T (Q "1/1000") { O with format := { negExpThreshold := -200 } } == "0.001"
#guard T (Q "1/1000") { O with format := { negExpThreshold := -3 } } == "1e-3"
#guard T (Q "1/100") { O with format := { negExpThreshold := -3 } } == "0.01"
#guard T (Q "1/100") { O with format := { negExpThreshold := -2 } } == "1e-2"
#guard T (Q "1/10") { O with format := { negExpThreshold := -2 } } == "0.1"
#guard T (Q "1/10") { O with format := { negExpThreshold := -1 } } == "1e-1"
-- bankers' rounding: 1/2 in base 3 at scale 1 is equidistant from 0.1 and 0.2; the even one wins
#guard T (Q "1/2") { O with base := 3, size := .scale 1 } == "0.2"
-- a negative value rounding to zero keeps its sign, as in Malachite
#guard T (Q "-1/300") { O with size := .scale 2 } == "-0"

-- Ceiling with a scale
#guard T (Q "1/3") { O with size := .scale 2, mode := .Ceiling } == "0.34"
#guard T (Q "1/3") { O with size := .scale 1, mode := .Ceiling } == "0.4"
#guard T (Q "1/3") { O with size := .scale 0, mode := .Ceiling } == "1"
#guard T (Q "1/300") { O with size := .scale 4, mode := .Ceiling } == "0.0034"
#guard T (Q "1/300") { O with size := .scale 3, mode := .Ceiling } == "0.004"
#guard T (Q "1/300") { O with size := .scale 2, mode := .Ceiling } == "0.01"
#guard T (Q "1/300") { O with size := .scale 1, mode := .Ceiling } == "0.1"
-- a rational close to π in several bases, default options
private def PI : AzRat := Q "245850922/78256779"
#guard T PI { O with base := 2 } == "11.0010010001"
#guard T PI { O with base := 3 } == "10.01021101222201"
#guard T PI { O with base := 4 } == "3.021003331222202"
#guard T PI { O with base := 5 } == "3.032322143033433"
#guard T PI { O with base := 8 } == "3.110375524210264"
#guard T PI { O with base := 16 } == "3.243f6a8885a3033"
#guard T PI { O with base := 32 } == "3.4gvml245kc1j1qs"
#guard T PI { O with base := 36 } == "3.53i5ab8p5fhzpkj"
