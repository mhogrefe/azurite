/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.Shift
import Azurite.AzNat.Pow2
import Azurite.AzRat.Parse
import Azurite.AzRat.ToString

/-!
# Tests for the `AzFloat` core

Expected values computed by hand from the definitions (`q` rounded to `p` significant bits).
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!

/-- The exact value as a fraction, `"<none>"` for `NaN` and `±∞`. -/
private def R (x : AzFloat) : String := (x.toAzRat?.map toString).getD "<none>"

private def F (s : String) (p : Nat) (mode : RoundingMode := .Nearest) : AzFloat × Ordering :=
  ofAzRatRound (Q s) p mode

private def E (z : Int) : Option AzInt := some (AzInt.ofInt z)

/-! ## Special values and constants -/

#guard nan.isNaN
#guard !nan.isFinite
#guard nan.sign? == none
#guard !nan.isPositive && !nan.isNegative
#guard (-nan).isNaN
#guard posInfinity.isInfinite && posInfinity.isPositive
#guard (-posInfinity) == negInfinity
#guard negInfinity.isNegative
#guard (abs negInfinity) == posInfinity
#guard zero.isZero && zero.isFinite && !zero.isNormal
#guard !zero.isPositive && !zero.isNegative
#guard zero.sign? == none
#guard (-zero) == zero
#guard (abs zero) == zero
#guard (0 : AzFloat) == zero
#guard R zero == "0"
#guard R nan == "<none>"
#guard R posInfinity == "<none>"

#guard R one == "1"
#guard one.isNormal && one.isPositive
#guard one.precision? == some 1
#guard one.exponent? == E 1
#guard one.significand? == some (AzNat.pow2 63)   -- left-aligned
#guard R two == "2"
#guard two.exponent? == E 2
#guard R oneHalf == "1/2"
#guard oneHalf.exponent? == E 0
#guard R negOne == "-1"
#guard R (-two) == "-2"
#guard R (abs (-two)) == "2"
#guard R (powerOf2 (AzInt.ofInt (-10))) == "1/1024"
#guard (powerOf2 (AzInt.ofInt (-10))).exponent? == E (-9)

/-! ## Exact conversions -/

#guard R (ofAzNat (AzNat.ofNat 1000)) == "1000"
#guard (ofAzNat (AzNat.ofNat 1000)).precision? == some 10
#guard (ofAzNat (AzNat.ofNat 1000)).exponent? == E 10
#guard (ofAzNat (AzNat.ofNat 1000)).significand? == some (AzNat.ofNat (1000 * 2 ^ 54))
#guard (ofAzNat 0).isZero
#guard R (ofAzNat (AzNat.ofNat (2 ^ 64))) == "18446744073709551616"
#guard (ofAzNat (AzNat.ofNat (2 ^ 64))).precision? == some 65
#guard (ofAzNat (AzNat.ofNat (2 ^ 64))).significand?.map AzNat.size == some 128
#guard R (ofAzInt (AzInt.ofInt (-5))) == "-5"
#guard (ofAzInt (AzInt.ofInt (-5))).precision? == some 3
#guard (ofAzInt (AzInt.ofInt (-5))).exponent? == E 3
#guard (ofAzInt 0).isZero

/-! ## Rounding a rational -/

#guard R (F "1/3" 10).1 == "683/2048"
#guard (F "1/3" 10).2 == .gt
#guard (F "1/3" 10).1.precision? == some 10
#guard (F "1/3" 10).1.exponent? == E (-1)
#guard R (F "1/3" 10 .Floor).1 == "341/1024"
#guard (F "1/3" 10 .Floor).2 == .lt
#guard R (F "1/3" 10 .Down).1 == "341/1024"
#guard R (F "1/3" 10 .Ceiling).1 == "683/2048"
#guard R (F "1/3" 10 .Up).1 == "683/2048"
#guard R (F "-1/3" 10 .Floor).1 == "-683/2048"
#guard R (F "-1/3" 10 .Ceiling).1 == "-341/1024"
#guard R (F "-1/3" 10 .Down).1 == "-341/1024"
#guard R (F "-1/3" 10 .Up).1 == "-683/2048"
#guard R (F "1/3" 1).1 == "1/4"
#guard (F "1/3" 1).2 == .lt
#guard (F "1/3" 1).1.exponent? == E (-1)
#guard R (F "22/7" 10).1 == "805/256"
#guard (F "22/7" 10).2 == .gt
#guard (F "22/7" 10).1.exponent? == E 2
#guard R (F "22/7" 1).1 == "4"                     -- rounds up to a power of two
#guard (F "22/7" 1).2 == .gt
#guard (F "22/7" 1).1.exponent? == E 3
#guard (F "22/7" 1).1.precision? == some 1
#guard R (F "22/7" 1 .Floor).1 == "2"
#guard R (F "-22/7" 1 .Floor).1 == "-4"
#guard (F "-22/7" 1 .Floor).2 == .lt
#guard R (F "-22/7" 1 .Ceiling).1 == "-2"
#guard (F "-22/7" 1 .Ceiling).2 == .gt
#guard R (F "1" 1).1 == "1"
#guard R (F "1" 10).1 == "1"
#guard (F "1" 10).2 == .eq
#guard (F "1" 10).1.precision? == some 10
#guard (F "1" 10).1.exponent? == E 1
#guard R (F "1" 100).1 == "1"
#guard (F "1" 100).1.precision? == some 100
#guard (F "1" 100).1.significand?.map AzNat.size == some 128
#guard R (F "1/2" 1).1 == "1/2"
#guard (F "1/2" 1).1.exponent? == E 0
#guard R (F "7/8" 2).1 == "1"                      -- 0.111₂ to nearest 2 bits
#guard (F "7/8" 2).1.exponent? == E 1
#guard R (F "7/8" 2 .Down).1 == "3/4"
#guard R (F "1000000" 7).1 == "999424"             -- 11110100001001000000₂ to 7 bits
#guard R (F "1000000" 7 .Up).1 == "1007616"
#guard R (F "-1000000" 7).1 == "-999424"
#guard R (F "-1000000" 7 .Floor).1 == "-1007616"
#guard (F "0" 10).1.isZero
#guard (F "0" 10).2 == .eq
#guard (F "1" 0).1.isNaN
#guard R (ofAzRat (Q "1/10") 53) == "3602879701896397/36028797018963968"
#guard R (ofAzRat (Q "1/10") 24) == "13421773/134217728"
#guard (ofAzRat ((Q "1") <<< 1000) 5).exponent? == E 1001
#guard (ofAzRat ((Q "1") >>> 1000) 5).exponent? == E (-999)
#guard R (ofAzRat ((Q "1") >>> 1000) 5) == toString ((Q "1") >>> 1000)

/-! ## Shifts -/

#guard R (one <<< (10 : Nat)) == "1024"
#guard R (one >>> (10 : Nat)) == "1/1024"
#guard (one <<< (10 : Nat)).exponent? == E 11
#guard (one <<< (10 : Nat)).precision? == some 1
#guard R ((F "1/3" 10).1 <<< (11 : Nat)) == "683"
#guard R ((F "1/3" 10).1 >>> (3 : Nat)) == "683/16384"
#guard R ((F "-22/7" 10).1 <<< AzInt.ofInt (-8)) == "-805/65536"
#guard R ((F "-22/7" 10).1 >>> AzInt.ofInt (-8)) == "-805"
#guard ((F "1" 5).1 <<< (1000 : Nat)).exponent? == E 1001
#guard R ((F "1" 5).1 <<< (100 : Nat)) == toString ((Q "1") <<< 100)
#guard (nan <<< (3 : Nat)).isNaN
#guard (posInfinity <<< (3 : Nat)) == posInfinity
#guard (negInfinity >>> (3 : Nat)) == negInfinity
#guard (zero <<< (3 : Nat)) == zero
