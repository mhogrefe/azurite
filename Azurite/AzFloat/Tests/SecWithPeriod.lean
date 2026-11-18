/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.CosPi
import Azurite.AzFloat.CosRat
import Azurite.AzFloat.OfString
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
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def S (x : AzFloat) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  secWithPeriodPrecRound x u p m
private def R (q : String) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  secRatWithPeriodPrecRound (Q q) u p m
private def recip (c : AzFloat × Ordering) (p : Nat) (m : RoundingMode) : AzFloat × Ordering :=
  divPrecRound (X "1" 1) c.1 p m
private def agrees (x : AzFloat) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) : Bool :=
  S x u p m == recip (cosWithPeriodPrecRound x u (p + 300) .Nearest) p m
private def agreesRat (q : String) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :
    Bool :=
  R q u p m == recip (cosRatWithPeriodPrecRound (Q q) u (p + 300) .Nearest) p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (S (X "1" 53) 0 53) == ("NaN", .eq)
#guard D (S nan 360 53) == ("NaN", .eq)
#guard D (S (infinity true) 360 53) == ("NaN", .eq)
#guard D (S zero 360 53) == ("1.0", .eq)
#guard D (S zero 360 0) == ("NaN", .eq)
#guard D (S (X "1" 53) 360 0) == ("NaN", .eq)

-- multiples of `1/2`: exactly `±1`
#guard D (S (X "360" 53) 360 53) == ("1.0", .eq)
#guard D (S (X "180" 53) 360 53) == ("-1.0", .eq)
#guard D (S (X "-540" 53) 360 53) == ("-1.0", .eq)
#guard D (S (X "1" 53) 1 53) == ("1.0", .eq)
#guard D (S (X "1.5" 53) 1 53) == ("-1.0", .eq)

-- odd multiples of `1/4`: poles, exactly `+∞`
#guard D (S (X "90" 53) 360 53) == ("Infinity", .eq)
#guard D (S (X "270" 53) 360 53) == ("Infinity", .eq)
#guard D (S (X "-90" 53) 360 53) == ("Infinity", .eq)
#guard D (S (X "-270" 53) 360 53 .Floor) == ("Infinity", .eq)
#guard D (S (X "0.25" 53) 1 53) == ("Infinity", .eq)
#guard D (S (X "0.75" 53) 1 20 .Down) == ("Infinity", .eq)

-- odd multiples of `1/8`: `±√2`
#guard toString (secWithPeriod (X "45" 200) 360) == "1.41421356237309504880168872420969807856967187\
  537694807317668"
#guard toString (secWithPeriod (X "135" 200) 360) == "-1.414213562373095048801688724209698078569671\
  87537694807317668"
#guard S (X "225" 53) 360 53 == S (X "135" 53) 360 53
#guard S (X "-45" 53) 360 53 == S (X "45" 53) 360 53

-- thirds and sixths: exactly `∓2`
#guard D (S (X "60" 53) 360 53) == ("2.0", .eq)
#guard D (S (X "120" 53) 360 53) == ("-2.0", .eq)
#guard D (S (X "240" 53) 360 53) == ("-2.0", .eq)
#guard D (S (X "300" 53) 360 53) == ("2.0", .eq)
#guard D (S (X "60" 53) 360 1) == ("2.0", .eq)

-- a sweep against the reciprocal of the cosine (not at the poles)
#guard (List.range 721).all fun i => i % 180 == 90 || agrees (F s!"{i}" 53) 360 53
#guard (List.range 400).all fun i =>
  (i + 1) % 180 == 90 || agrees (F s!"-{i + 1}" 53) 360 53 .Floor
#guard (List.range 60).all fun i => agrees (F s!"{i + 1}/8" 53) 7 53 .Ceiling
#guard (List.range 60).all fun i => agrees (F s!"{2 * i + 1}/5" 30) 400 100 .Up
#guard agrees (X "1" 53) 360 1
#guard agrees (X "1" 53) 18446744073709551615 53
#guard agrees (X "12345678814.81481618629628669593" 100) 360 300
#guard agrees (X "0.3333333333333333333333333333333333333333333333333333333333333333333333333333333\
  3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333\
  3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333\
  3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333\
  3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333\
  3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333\
  333333333333333333333333333333333333335" 2000) 360 2000
#guard agrees (X "89.99999999999999" 53) 360 53

-- tiny and huge arguments
private def tinyX : AzFloat := (X "1" 53) <<< AzInt.ofInt (-(2 ^ 30 : Int))
#guard S tinyX 360 53 == (X "1" 53, .lt)
#guard (S (-tinyX) 360 53 .Ceiling).2 == .gt
#guard D (S ((X "-1" 53) <<< AzInt.ofInt (-200)) 360 53 .Floor) == ("1.0", .lt)
#guard (S ((X "-1" 53) <<< AzInt.ofInt (-200)) 360 53 .Ceiling).2 == .gt
#guard agrees ((X "3" 53) <<< AzInt.ofInt (2 ^ 20 : Int)) 7 53

-- the rational variant
#guard D (R "1/3" 0 53) == ("NaN", .eq)
#guard D (R "0" 360 53) == ("1.0", .eq)
#guard D (R "0" 360 0) == ("NaN", .eq)
#guard D (R "1/2" 1 53) == ("-1.0", .eq)
#guard D (R "1/4" 1 53) == ("Infinity", .eq)
#guard D (R "-3/4" 1 53) == ("Infinity", .eq)
#guard D (R "45/2" 90 53) == ("Infinity", .eq)
#guard D (R "1/3" 1 53) == ("-2.0", .eq)
#guard D (R "-1/6" 1 53) == ("2.0", .eq)
#guard R "1/8" 1 53 == S (X "0.125" 53) 1 53
#guard (List.range 1081).all fun i => i % 540 == 270 || agreesRat s!"{i}/3" 360 53
#guard (List.range 200).all fun i => agreesRat s!"-{i + 1}/7" 360 53 .Floor
#guard agreesRat "12345678901234567890123456789/1000000007" 360 300
#guard agreesRat "1/1267650600228229401496703205376" 360 20

-- `secRat` against the float `sec` and the reciprocal of `cosRat`
#guard D (secRatPrecRound (Q "0") 53 .Nearest) == ("1.0", .eq)
#guard D (secRatPrecRound (Q "1/3") 0 .Nearest) == ("NaN", .eq)
#guard secRatPrecRound (Q "1/2") 53 .Nearest == secPrecRound (X "0.5" 53) 53 .Nearest
#guard secRatPrecRound (Q "-3") 53 .Floor == secPrecRound (X "-3" 53) 53 .Floor
#guard (List.range 26).all fun i =>
  secRatPrecRound (Q s!"{i + 1}/7") 53 .Nearest
    == recip (cosRatPrecRound (Q s!"{i + 1}/7") 353 .Nearest) 53 .Nearest
#guard secRatPrecRound (Q "11/7") 53 .Ceiling
  == recip (cosRatPrecRound (Q "11/7") 353 .Nearest) 53 .Ceiling
#guard D (secRatPrecRound (Q "1/1267650600228229401496703205376") 20 .Nearest) == ("1.0", .lt)
#guard secRat (Q "1") 53 == sec (X "1" 53)

-- `secPi`, `secPiRat`
#guard D (secPiPrecRound (X "1" 53) 53 .Nearest) == ("-1.0", .eq)
#guard D (secPiPrecRound (X "2" 53) 53 .Nearest) == ("1.0", .eq)
#guard D (secPiPrecRound (X "0.5" 53) 53 .Nearest) == ("Infinity", .eq)
#guard D (secPiPrecRound (X "-1.5" 53) 53 .Nearest) == ("Infinity", .eq)
#guard D (secPiPrecRound (X "100000000000000000000.5" 80) 53 .Nearest) == ("Infinity", .eq)
#guard secPi (X "0.25" 53) == (S (X "45" 53) 360 53).1
#guard D (secPiRatPrecRound (Q "1/3") 53 .Nearest) == ("2.0", .eq)
#guard D (secPiRatPrecRound (Q "2/3") 53 .Nearest) == ("-2.0", .eq)
#guard D (secPiRatPrecRound (Q "7/2") 53 .Nearest) == ("Infinity", .eq)
#guard secPiRat (Q "1/4") 53 == secPi (X "0.25" 53)
#guard secPiPrecRound (X "0.3333333333333333333333333333335" 100) 80 .Floor
  == recip (cosPiPrecRound (X "0.3333333333333333333333333333335" 100) 380 .Nearest) 80 .Floor
