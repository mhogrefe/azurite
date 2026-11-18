/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.Csc
import Azurite.AzFloat.OfString
import Azurite.AzFloat.Sin
import Azurite.AzFloat.SinPi
import Azurite.AzFloat.SinRat
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for the cosecant family

`csc`: the special values (`NaN`, `±∞`, `csc 0 = +∞` at every precision, `p = 0`), `csc 1` to
59 digits (reference: the Taylor series of `sin` in exact rational arithmetic), the float nearest
`π` (a large result), oddness and the directed modes, a sweep against the rounded reciprocal of
`sin x` computed with 300 extra bits, tiny arguments (`csc 2^(−2^30) = 2^(2^30)` rounded up from
just above), `2^1000`.  `cscRat` likewise.  With a period: `u = 0` gives `NaN`; `x = 0` gives
`+∞`; a multiple of `1/2` is a pole, `±∞` with the sign of `x`; the reduced denominator `4`
gives exactly `±1` and `12` exactly `±2`; every whole degree of two turns that is not a pole
against the reciprocal of the sine; `cscPi` at the integers and half-integers.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
/-- `0.3333333333…` at 2000 bits. -/
private def third2000 : AzFloat :=
  X "0.333333333333333333333333333333333333333333333333333333333333333333333333333333\
    33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333\
    33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333\
    33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333\
    33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333\
    33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333\
    33333333333333333333333333333333333333333333333333333333333333335" 2000
private def C (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := cscPrecRound x p m
private def recip (c : AzFloat × Ordering) (p : Nat) (m : RoundingMode) : AzFloat × Ordering :=
  divPrecRound (X "1" 1) c.1 p m
private def agrees (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) : Bool :=
  C x p m == recip (sinPrecRound x (p + 300) .Nearest) p m
private def W (x : AzFloat) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  cscWithPeriodPrecRound x u p m
private def agreesW (x : AzFloat) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) : Bool :=
  W x u p m == recip (sinWithPeriodPrecRound x u (p + 300) .Nearest) p m
private def R (q : String) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  cscRatWithPeriodPrecRound (Q q) u p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- `csc`: special values
#guard D (C nan 53) == ("NaN", .eq)
#guard D (C (infinity true) 53) == ("NaN", .eq)
#guard D (C (infinity false) 53) == ("NaN", .eq)
#guard D (C zero 53) == ("Infinity", .eq)
#guard D (C zero 0) == ("Infinity", .eq)
#guard D (C (X "1" 53) 0) == ("NaN", .eq)

-- `csc`: values
#guard toString (csc (X "1" 200)) == "1.18839510577812121626159945237455100352782983409796262526525\
  4"
#guard C (X "1" 53) 53 == recip (sinPrecRound (X "1" 53) 353 .Nearest) 53 .Nearest
#guard (C (X "-1" 53) 53 .Floor).1 == -(C (X "1" 53) 53 .Ceiling).1
#guard (C (X "1" 53) 53 .Floor).2 == .lt
#guard (C (X "1" 53) 53 .Ceiling).2 == .gt
#guard agrees (X "3.141592653589793" 53) 53
#guard (List.range 26).all fun i => agrees (F s!"{i + 1}/4" 53) 53
#guard (List.range 26).all fun i => agrees (F s!"-{i + 1}/4" 53) 53 .Floor
#guard (List.range 13).all fun i => agrees (F s!"{2 * i + 1}/7" 53) 53 .Ceiling
#guard (List.range 13).all fun i => agrees (F s!"{2 * i + 1}/5" 30) 100 .Up
#guard agrees (X "1" 53) 1
#guard agrees (X "-1000" 53) 53
#guard agrees (X "12345678814.81481618629628669593" 100) 300
#guard agrees third2000 2000
#guard agrees (X "9.094947017729282e-13" 53) 53
#guard agrees ((X "1" 53) <<< AzInt.ofInt 1000) 53

-- `csc`: tiny arguments (`csc x` is just above `1/x`)
private def tinyE : Int := -(2 ^ 30 : Int)
private def tinyX : AzFloat := (X "1" 53) <<< AzInt.ofInt tinyE
private def hugeY : AzFloat := (X "1" 53) <<< AzInt.ofInt (-tinyE)
#guard C tinyX 53 == (hugeY, .lt)
#guard C tinyX 53 .Floor == (hugeY, .lt)
#guard (C tinyX 53 .Ceiling).2 == .gt
#guard C (-tinyX) 53 == (-hugeY, .gt)
#guard C ((X "3" 53) <<< AzInt.ofInt (-200)) 53
  == recip (sinPrecRound ((X "3" 53) <<< AzInt.ofInt (-200)) 700 .Nearest) 53 .Nearest

-- `cscRat`
#guard D (cscRatPrecRound (Q "0") 53 .Nearest) == ("Infinity", .eq)
#guard D (cscRatPrecRound (Q "0") 0 .Nearest) == ("Infinity", .eq)
#guard D (cscRatPrecRound (Q "1/3") 0 .Nearest) == ("NaN", .eq)
#guard cscRatPrecRound (Q "1/2") 53 .Nearest == C (X "0.5" 53) 53
#guard cscRatPrecRound (Q "-3") 53 .Floor == C (X "-3" 53) 53 .Floor
#guard (List.range 26).all fun i =>
  cscRatPrecRound (Q s!"{i + 1}/7") 53 .Nearest
    == recip (sinRatPrecRound (Q s!"{i + 1}/7") 353 .Nearest) 53 .Nearest
#guard (List.range 12).all fun i =>
  cscRatPrecRound (Q s!"-{i + 1}/3") 40 .Ceiling
    == recip (sinRatPrecRound (Q s!"-{i + 1}/3") 340 .Nearest) 40 .Ceiling
#guard D (cscRatPrecRound (Q "1/1267650600228229401496703205376") 20 .Nearest) ==
  ("1.26765e30", .lt)
#guard D (cscRatPrecRound (Q "-1/1267650600228229401496703205376") 20 .Nearest) ==
  ("-1.26765e30", .gt)
#guard cscRat (Q "1") 53 == csc (X "1" 53)

-- with a period: special values and poles
#guard D (W (X "1" 53) 0 53) == ("NaN", .eq)
#guard D (W nan 360 53) == ("NaN", .eq)
#guard D (W (infinity true) 360 53) == ("NaN", .eq)
#guard D (W zero 360 53) == ("Infinity", .eq)
#guard D (W zero 360 0) == ("Infinity", .eq)
#guard D (W (X "1" 53) 360 0) == ("NaN", .eq)
#guard D (W (X "180" 53) 360 53) == ("Infinity", .eq)
#guard D (W (X "360" 53) 360 53) == ("Infinity", .eq)
#guard D (W (X "540" 53) 360 53 .Floor) == ("Infinity", .eq)
#guard D (W (X "-180" 53) 360 53) == ("-Infinity", .eq)
#guard D (W (X "-360" 53) 360 53) == ("-Infinity", .eq)
#guard D (W (X "0.5" 53) 1 53) == ("Infinity", .eq)
#guard D (W (X "-1.5" 53) 1 20 .Up) == ("-Infinity", .eq)

-- with a period: the denominators `4` (`±1`) and `12` (`±2`)
#guard D (W (X "90" 53) 360 53) == ("1.0", .eq)
#guard D (W (X "270" 53) 360 53) == ("-1.0", .eq)
#guard D (W (X "-90" 53) 360 53) == ("-1.0", .eq)
#guard D (W (X "-270" 53) 360 53) == ("1.0", .eq)
#guard D (W (X "30" 53) 360 53) == ("2.0", .eq)
#guard D (W (X "150" 53) 360 53) == ("2.0", .eq)
#guard D (W (X "210" 53) 360 53) == ("-2.0", .eq)
#guard D (W (X "330" 53) 360 53) == ("-2.0", .eq)
#guard D (W (X "-30" 53) 360 53) == ("-2.0", .eq)
#guard D (W (X "30" 53) 360 1) == ("2.0", .eq)

-- with a period: a sweep against the reciprocal of the sine (not at the poles)
#guard (List.range 721).all fun i => i % 180 == 0 || agreesW (X s!"{i}" 53) 360 53
#guard (List.range 400).all fun i =>
  (i + 1) % 180 == 0 || agreesW (X s!"-{i + 1}" 53) 360 53 .Floor
#guard (List.range 60).all fun i => agreesW (F s!"{i + 1}/8" 53) 7 53 .Ceiling
#guard (List.range 60).all fun i => agreesW (F s!"{2 * i + 1}/5" 30) 400 100 .Up
#guard agreesW (X "1" 53) 18446744073709551615 53
#guard agreesW third2000 360 2000
#guard agreesW ((X "3" 53) <<< AzInt.ofInt (2 ^ 20 : Int)) 7 53
#guard (W tinyX 360 53).2 == .lt || (W tinyX 360 53).2 == .gt
#guard W (-tinyX) 360 53 == (-(W tinyX 360 53).1, (W tinyX 360 53).2.swap)

-- the rational variant with a period
#guard D (R "1/3" 0 53) == ("NaN", .eq)
#guard D (R "0" 360 53) == ("Infinity", .eq)
#guard D (R "1/2" 1 53) == ("Infinity", .eq)
#guard D (R "-1/2" 1 53) == ("-Infinity", .eq)
#guard D (R "-7" 1 53) == ("-Infinity", .eq)
#guard D (R "45/2" 45 53) == ("Infinity", .eq)
#guard D (R "1/4" 1 53) == ("1.0", .eq)
#guard D (R "-1/4" 1 53) == ("-1.0", .eq)
#guard D (R "1/12" 1 53) == ("2.0", .eq)
#guard D (R "7/12" 1 53) == ("-2.0", .eq)
#guard D (R "-5/12" 1 53) == ("-2.0", .eq)
#guard R "1/8" 1 53 == W (X "0.125" 53) 1 53
#guard (List.range 1081).all fun i => i % 540 == 0 ||
  R s!"{i}/3" 360 53
    == recip (sinRatWithPeriodPrecRound (Q s!"{i}/3") 360 353 .Nearest) 53 .Nearest

-- `cscPi`, `cscPiRat`
#guard D (cscPiPrecRound (X "1" 53) 53 .Nearest) == ("Infinity", .eq)
#guard D (cscPiPrecRound (X "-2" 53) 53 .Nearest) == ("-Infinity", .eq)
#guard D (cscPiPrecRound zero 53 .Nearest) == ("Infinity", .eq)
#guard D (cscPiPrecRound (X "100000000000000000000" 80) 53 .Nearest) == ("Infinity", .eq)
#guard D (cscPiPrecRound (X "0.5" 53) 53 .Nearest) == ("1.0", .eq)
#guard D (cscPiPrecRound (X "1.5" 53) 53 .Nearest) == ("-1.0", .eq)
#guard D (cscPiPrecRound (X "-0.5" 53) 53 .Nearest) == ("-1.0", .eq)
#guard D (cscPiRatPrecRound (Q "1/6") 53 .Nearest) == ("2.0", .eq)
#guard D (cscPiRatPrecRound (Q "-7/6") 53 .Nearest) == ("2.0", .eq)
#guard D (cscPiRatPrecRound (Q "-3") 53 .Nearest) == ("-Infinity", .eq)
#guard cscPiRat (Q "1/4") 53 == cscPi (X "0.25" 53)
#guard cscPiPrecRound (X "0.3333333333333333333333333333335" 100) 80 .Floor
  == recip (sinPiPrecRound (X "0.3333333333333333333333333333335" 100) 380 .Nearest) 80 .Floor
