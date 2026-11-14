/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.CosPi
import Azurite.AzFloat.CosRat
import Azurite.AzFloat.Sec
import Azurite.AzFloat.SecWithPeriod
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `secWithPeriod`, `secRatWithPeriod`, `secRat`, `secPi`, `secPiRat`

The special cases of the secant with a period: `u = 0` gives `NaN`; `x = 0` gives `1`; `x/u` an
even multiple of `1/2` gives exactly `1`, an odd multiple exactly `−1`; an odd multiple of `1/4`
is a pole and gives exactly `+∞` (for either sign of `x`); an odd multiple of `1/8` gives
`±√2`; the thirds and sixths give exactly `∓2`.  Every whole degree of two turns that is not a
pole, both signs, against the correctly rounded reciprocal of the cosine computed with 300
extra bits; other periods, modes and precisions; tiny and huge arguments.  The same for the
rational variant, `secRat` against the float `sec`, and `secPi`/`secPiRat`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def S (x : AzFloat) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  secWithPeriodPrecRound x u p m
private def R (q : String) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  secRatWithPeriodPrecRound (Q q) u p m
private def recip (c : AzFloat × Ordering) (p : Nat) (m : RoundingMode) : AzFloat × Ordering :=
  divPrecRound (F "1" 1) c.1 p m
private def agrees (x : AzFloat) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) : Bool :=
  S x u p m == recip (cosWithPeriodPrecRound x u (p + 300) .Nearest) p m
private def agreesRat (q : String) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :
    Bool :=
  R q u p m == recip (cosRatWithPeriodPrecRound (Q q) u (p + 300) .Nearest) p m

-- special values
#guard S (F "1" 53) 0 53 == (nan, .eq)
#guard S nan 360 53 == (nan, .eq)
#guard S (infinity true) 360 53 == (nan, .eq)
#guard S zero 360 53 == (F "1" 53, .eq)
#guard S zero 360 0 == (nan, .eq)
#guard S (F "1" 53) 360 0 == (nan, .eq)

-- multiples of `1/2`: exactly `±1`
#guard S (F "360" 53) 360 53 == (F "1" 53, .eq)
#guard S (F "180" 53) 360 53 == (F "-1" 53, .eq)
#guard S (F "-540" 53) 360 53 == (F "-1" 53, .eq)
#guard S (F "1" 53) 1 53 == (F "1" 53, .eq)
#guard S (F "3/2" 53) 1 53 == (F "-1" 53, .eq)

-- odd multiples of `1/4`: poles, exactly `+∞`
#guard S (F "90" 53) 360 53 == (infinity true, .eq)
#guard S (F "270" 53) 360 53 == (infinity true, .eq)
#guard S (F "-90" 53) 360 53 == (infinity true, .eq)
#guard S (F "-270" 53) 360 53 .Floor == (infinity true, .eq)
#guard S (F "1/4" 53) 1 53 == (infinity true, .eq)
#guard S (F "3/4" 53) 1 20 .Down == (infinity true, .eq)

-- odd multiples of `1/8`: `±√2`
#guard (toString (secWithPeriod (F "45" 200) 360)).startsWith
  "1.4142135623730950488016887242096980785696718753769480731766"
#guard (toString (secWithPeriod (F "135" 200) 360)).startsWith
  "-1.4142135623730950488016887242096980785696718753769480731766"
#guard S (F "225" 53) 360 53 == S (F "135" 53) 360 53
#guard S (F "-45" 53) 360 53 == S (F "45" 53) 360 53

-- thirds and sixths: exactly `∓2`
#guard S (F "60" 53) 360 53 == (F "2" 53, .eq)
#guard S (F "120" 53) 360 53 == (F "-2" 53, .eq)
#guard S (F "240" 53) 360 53 == (F "-2" 53, .eq)
#guard S (F "300" 53) 360 53 == (F "2" 53, .eq)
#guard S (F "60" 53) 360 1 == (F "2" 1, .eq)

-- a sweep against the reciprocal of the cosine (not at the poles)
#guard (List.range 721).all fun i => i % 180 == 90 || agrees (F s!"{i}" 53) 360 53
#guard (List.range 400).all fun i =>
  (i + 1) % 180 == 90 || agrees (F s!"-{i + 1}" 53) 360 53 .Floor
#guard (List.range 60).all fun i => agrees (F s!"{i + 1}/8" 53) 7 53 .Ceiling
#guard (List.range 60).all fun i => agrees (F s!"{2 * i + 1}/5" 30) 400 100 .Up
#guard agrees (F "1" 53) 360 1
#guard agrees (F "1" 53) 18446744073709551615 53
#guard agrees (F "12345678901234567890/1000000007" 100) 360 300
#guard agrees (F "1/3" 2000) 360 2000
#guard agrees (F "6333186975989759/70368744177664" 53) 360 53

-- tiny and huge arguments
private def tinyX : AzFloat := (F "1" 53) <<< AzInt.ofInt (-(2 ^ 30 : Int))
#guard S tinyX 360 53 == (F "1" 53, .lt)
#guard (S (-tinyX) 360 53 .Ceiling).2 == .gt
#guard S ((F "-1" 53) <<< AzInt.ofInt (-200)) 360 53 .Floor == (F "1" 53, .lt)
#guard (S ((F "-1" 53) <<< AzInt.ofInt (-200)) 360 53 .Ceiling).2 == .gt
#guard agrees ((F "3" 53) <<< AzInt.ofInt (2 ^ 20 : Int)) 7 53

-- the rational variant
#guard R "1/3" 0 53 == (nan, .eq)
#guard R "0" 360 53 == (F "1" 53, .eq)
#guard R "0" 360 0 == (nan, .eq)
#guard R "1/2" 1 53 == (F "-1" 53, .eq)
#guard R "1/4" 1 53 == (infinity true, .eq)
#guard R "-3/4" 1 53 == (infinity true, .eq)
#guard R "45/2" 90 53 == (infinity true, .eq)
#guard R "1/3" 1 53 == (F "-2" 53, .eq)
#guard R "-1/6" 1 53 == (F "2" 53, .eq)
#guard R "1/8" 1 53 == S (F "1/8" 53) 1 53
#guard (List.range 1081).all fun i => i % 540 == 270 || agreesRat s!"{i}/3" 360 53
#guard (List.range 200).all fun i => agreesRat s!"-{i + 1}/7" 360 53 .Floor
#guard agreesRat "12345678901234567890123456789/1000000007" 360 300
#guard agreesRat "1/1267650600228229401496703205376" 360 20

-- `secRat` against the float `sec` and the reciprocal of `cosRat`
#guard secRatPrecRound (Q "0") 53 .Nearest == (F "1" 53, .eq)
#guard secRatPrecRound (Q "1/3") 0 .Nearest == (nan, .eq)
#guard secRatPrecRound (Q "1/2") 53 .Nearest == secPrecRound (F "1/2" 53) 53 .Nearest
#guard secRatPrecRound (Q "-3") 53 .Floor == secPrecRound (F "-3" 53) 53 .Floor
#guard (List.range 26).all fun i =>
  secRatPrecRound (Q s!"{i + 1}/7") 53 .Nearest
    == recip (cosRatPrecRound (Q s!"{i + 1}/7") 353 .Nearest) 53 .Nearest
#guard secRatPrecRound (Q "11/7") 53 .Ceiling
  == recip (cosRatPrecRound (Q "11/7") 353 .Nearest) 53 .Ceiling
#guard secRatPrecRound (Q "1/1267650600228229401496703205376") 20 .Nearest == (F "1" 20, .lt)
#guard secRat (Q "1") 53 == sec (F "1" 53)

-- `secPi`, `secPiRat`
#guard secPiPrecRound (F "1" 53) 53 .Nearest == (F "-1" 53, .eq)
#guard secPiPrecRound (F "2" 53) 53 .Nearest == (F "1" 53, .eq)
#guard secPiPrecRound (F "1/2" 53) 53 .Nearest == (infinity true, .eq)
#guard secPiPrecRound (F "-3/2" 53) 53 .Nearest == (infinity true, .eq)
#guard secPiPrecRound (F "200000000000000000001/2" 80) 53 .Nearest == (infinity true, .eq)
#guard secPi (F "1/4" 53) == (S (F "45" 53) 360 53).1
#guard secPiRatPrecRound (Q "1/3") 53 .Nearest == (F "2" 53, .eq)
#guard secPiRatPrecRound (Q "2/3") 53 .Nearest == (F "-2" 53, .eq)
#guard secPiRatPrecRound (Q "7/2") 53 .Nearest == (infinity true, .eq)
#guard secPiRat (Q "1/4") 53 == secPi (F "1/4" 53)
#guard secPiPrecRound (F "1/3" 100) 80 .Floor
  == recip (cosPiPrecRound (F "1/3" 100) 380 .Nearest) 80 .Floor
