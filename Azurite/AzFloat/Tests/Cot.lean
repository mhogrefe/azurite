/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.Cot
import Azurite.AzFloat.SinCos
import Azurite.AzFloat.SinCosPi
import Azurite.AzFloat.SinCosRat
import Azurite.AzFloat.SinCosRatWithPeriod
import Azurite.AzFloat.SinCosWithPeriod
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse
import Azurite.AzFloat.OfString

/-!
# Tests for the cotangent family

`cot`: the special values (`NaN`, `±∞`, `cot 0 = +∞` at every precision, `p = 0`), `cot 1` to
57 digits (reference: the Taylor series of `sin` and `cos` in exact rational arithmetic), the
float nearest `π` (a large result), oddness and the directed modes, a sweep against the rounded
quotient `cos x / sin x` of `sinCos` computed with 300 extra bits, tiny arguments
(`cot 2^(−2^30) = 2^(2^30)` rounded down from just below), `2^1000`.  `cotRat` likewise.  With a
period: `u = 0` gives `NaN`; `x = 0` gives `+∞`; a multiple of `1/2` is a pole, the infinity
with the sign of `x` times the sign of the cosine; the reduced denominator `4` gives exactly `0`
and `8` exactly `±1`; every whole degree of two turns that is not a pole against the quotient;
`cotPi` at the integers, half-integers and quarter-integers.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def big1 : AzFloat := X "0.3333333333333333333333333333333333333333333333333333333333333333\
  3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333\
  3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333\
  3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333\
  3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333\
  3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333\
  333333333333333333333333333333333333333333333333333335" 2000
private def C (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := cotPrecRound x p m
private def quot (sc : (AzFloat × Ordering) × (AzFloat × Ordering)) (p : Nat)
    (m : RoundingMode) : AzFloat × Ordering :=
  divPrecRound sc.2.1 sc.1.1 p m
private def agrees (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) : Bool :=
  C x p m == quot (sinCosPrecRound x (p + 300) .Nearest) p m
private def W (x : AzFloat) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  cotWithPeriodPrecRound x u p m
private def agreesW (x : AzFloat) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) : Bool :=
  W x u p m == quot (sinCosWithPeriodPrecRound x u (p + 300) .Nearest) p m
private def R (q : String) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  cotRatWithPeriodPrecRound (Q q) u p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- `cot`: special values
#guard D (C nan 53) == ("NaN", .eq)
#guard D (C (infinity true) 53) == ("NaN", .eq)
#guard D (C (infinity false) 53) == ("NaN", .eq)
#guard D (C zero 53) == ("Infinity", .eq)
#guard D (C zero 0) == ("Infinity", .eq)
#guard D (C (X "1" 53) 0) == ("NaN", .eq)

-- `cot`: values
#guard toString (cot (X "1" 200))
  == "0.642092615934330703006419986594265620230278113918171379101162"
#guard agrees (X "1" 53) 53
#guard (C (X "-1" 53) 53 .Floor).1 == -(C (X "1" 53) 53 .Ceiling).1
#guard (C (X "1" 53) 53 .Floor).2 == .lt
#guard (C (X "1" 53) 53 .Ceiling).2 == .gt
#guard agrees (X "3.141592653589793" 53) 53
#guard agrees (X "1.5707963267948966" 53) 53
#guard (List.range 26).all fun i => agrees (F s!"{i + 1}/4" 53) 53
#guard (List.range 26).all fun i => agrees (F s!"-{i + 1}/4" 53) 53 .Floor
#guard (List.range 13).all fun i => agrees (F s!"{2 * i + 1}/7" 53) 53 .Ceiling
#guard (List.range 13).all fun i => agrees (F s!"{2 * i + 1}/5" 30) 100 .Up
#guard agrees (X "1" 53) 1
#guard agrees (X "-1000" 53) 53
#guard agrees (X "12345678814.81481618629628669593" 100) 300
#guard agrees big1 2000
#guard agrees (X "9.094947017729282e-13" 53) 53
#guard agrees ((X "1" 53) <<< AzInt.ofInt 1000) 53

-- `cot`: tiny arguments (`cot x` is just below `1/x`)
private def tinyE : Int := -(2 ^ 30 : Int)
private def tinyX : AzFloat := (X "1" 53) <<< AzInt.ofInt tinyE
private def hugeY : AzFloat := (X "1" 53) <<< AzInt.ofInt (-tinyE)
#guard C tinyX 53 == (hugeY, .gt)
#guard C tinyX 53 .Ceiling == (hugeY, .gt)
#guard (C tinyX 53 .Floor).2 == .lt
#guard C (-tinyX) 53 == (-hugeY, .lt)
#guard C ((X "3" 53) <<< AzInt.ofInt (-200)) 53
  == quot (sinCosPrecRound ((X "3" 53) <<< AzInt.ofInt (-200)) 1000 .Nearest) 53 .Nearest

-- `cotRat`
#guard D (cotRatPrecRound (Q "0") 53 .Nearest) == ("Infinity", .eq)
#guard D (cotRatPrecRound (Q "0") 0 .Nearest) == ("Infinity", .eq)
#guard D (cotRatPrecRound (Q "1/3") 0 .Nearest) == ("NaN", .eq)
#guard cotRatPrecRound (Q "1/2") 53 .Nearest == C (X "0.5" 53) 53
#guard cotRatPrecRound (Q "-3") 53 .Floor == C (X "-3" 53) 53 .Floor
#guard (List.range 26).all fun i =>
  cotRatPrecRound (Q s!"{i + 1}/7") 53 .Nearest
    == quot (sinCosRatPrecRound (Q s!"{i + 1}/7") 353 .Nearest) 53 .Nearest
#guard (List.range 12).all fun i =>
  cotRatPrecRound (Q s!"-{i + 1}/3") 40 .Ceiling
    == quot (sinCosRatPrecRound (Q s!"-{i + 1}/3") 340 .Nearest) 40 .Ceiling
#guard D (cotRatPrecRound (Q "1/1267650600228229401496703205376") 20 .Nearest)
  == ("1.26765e30", .gt)
#guard D (cotRatPrecRound (Q "-1/1267650600228229401496703205376") 20 .Nearest)
  == ("-1.26765e30", .lt)
#guard cotRat (Q "1") 53 == cot (X "1" 53)

-- with a period: special values and poles (sign of `x` times sign of the cosine)
#guard D (W (X "1" 53) 0 53) == ("NaN", .eq)
#guard D (W nan 360 53) == ("NaN", .eq)
#guard D (W (infinity true) 360 53) == ("NaN", .eq)
#guard D (W zero 360 53) == ("Infinity", .eq)
#guard D (W zero 360 0) == ("Infinity", .eq)
#guard D (W (X "1" 53) 360 0) == ("NaN", .eq)
#guard D (W (X "180" 53) 360 53) == ("-Infinity", .eq)
#guard D (W (X "360" 53) 360 53) == ("Infinity", .eq)
#guard D (W (X "540" 53) 360 53 .Floor) == ("-Infinity", .eq)
#guard D (W (X "-180" 53) 360 53) == ("Infinity", .eq)
#guard D (W (X "-360" 53) 360 53) == ("-Infinity", .eq)
#guard D (W (X "0.5" 53) 1 53) == ("-Infinity", .eq)
#guard D (W (X "-1.5" 53) 1 20 .Up) == ("Infinity", .eq)

-- with a period: the denominators `4` (`0`) and `8` (`±1`)
#guard D (W (X "90" 53) 360 53) == ("0.0", .eq)
#guard D (W (X "270" 53) 360 53) == ("0.0", .eq)
#guard D (W (X "-90" 53) 360 53 .Floor) == ("0.0", .eq)
#guard D (W (X "45" 53) 360 53) == ("1.0", .eq)
#guard D (W (X "135" 53) 360 53) == ("-1.0", .eq)
#guard D (W (X "225" 53) 360 53) == ("1.0", .eq)
#guard D (W (X "315" 53) 360 53) == ("-1.0", .eq)
#guard D (W (X "-45" 53) 360 53) == ("-1.0", .eq)
#guard D (W (X "-135" 53) 360 53) == ("1.0", .eq)
#guard D (W (X "45" 53) 360 1) == ("1.0", .eq)

-- with a period: a sweep against the quotient (not at the poles)
#guard (List.range 721).all fun i => i % 180 == 0 || agreesW (F s!"{i}" 53) 360 53
#guard (List.range 400).all fun i =>
  (i + 1) % 180 == 0 || agreesW (F s!"-{i + 1}" 53) 360 53 .Floor
#guard (List.range 60).all fun i => agreesW (F s!"{i + 1}/8" 53) 7 53 .Ceiling
#guard (List.range 60).all fun i => agreesW (F s!"{2 * i + 1}/5" 30) 400 100 .Up
#guard agreesW (X "1" 53) 18446744073709551615 53
#guard agreesW big1 360 2000
#guard agreesW ((X "3" 53) <<< AzInt.ofInt (2 ^ 20 : Int)) 7 53
#guard (W tinyX 360 53).2 == .lt || (W tinyX 360 53).2 == .gt
#guard W (-tinyX) 360 53 == (-(W tinyX 360 53).1, (W tinyX 360 53).2.swap)

-- the rational variant with a period
#guard D (R "1/3" 0 53) == ("NaN", .eq)
#guard D (R "0" 360 53) == ("Infinity", .eq)
#guard D (R "1/2" 1 53) == ("-Infinity", .eq)
#guard D (R "-1/2" 1 53) == ("Infinity", .eq)
#guard D (R "-7" 1 53) == ("-Infinity", .eq)
#guard D (R "7" 1 53) == ("Infinity", .eq)
#guard D (R "45/2" 45 53) == ("-Infinity", .eq)
#guard D (R "1/4" 1 53) == ("0.0", .eq)
#guard D (R "-3/4" 1 53) == ("0.0", .eq)
#guard D (R "1/8" 1 53) == ("1.0", .eq)
#guard D (R "3/8" 1 53) == ("-1.0", .eq)
#guard D (R "5/8" 1 53) == ("1.0", .eq)
#guard D (R "-5/8" 1 53) == ("-1.0", .eq)
#guard R "1/12" 1 53 == W (X "30" 53) 360 53
#guard (List.range 1081).all fun i => i % 540 == 0 ||
  R s!"{i}/3" 360 53
    == quot (sinCosRatWithPeriodPrecRound (Q s!"{i}/3") 360 353 .Nearest) 53 .Nearest

-- `cotPi`, `cotPiRat`
#guard D (cotPiPrecRound (X "1" 53) 53 .Nearest) == ("-Infinity", .eq)
#guard D (cotPiPrecRound (X "2" 53) 53 .Nearest) == ("Infinity", .eq)
#guard D (cotPiPrecRound (X "-1" 53) 53 .Nearest) == ("Infinity", .eq)
#guard D (cotPiPrecRound (X "-2" 53) 53 .Nearest) == ("-Infinity", .eq)
#guard D (cotPiPrecRound zero 53 .Nearest) == ("Infinity", .eq)
#guard D (cotPiPrecRound (X "100000000000000000000" 80) 53 .Nearest) == ("Infinity", .eq)
#guard D (cotPiPrecRound (X "0.5" 53) 53 .Nearest) == ("0.0", .eq)
#guard D (cotPiPrecRound (X "0.25" 53) 53 .Nearest) == ("1.0", .eq)
#guard D (cotPiPrecRound (X "0.75" 53) 53 .Nearest) == ("-1.0", .eq)
#guard D (cotPiPrecRound (X "-0.25" 53) 53 .Nearest) == ("-1.0", .eq)
#guard D (cotPiRatPrecRound (Q "5/4") 53 .Nearest) == ("1.0", .eq)
#guard D (cotPiRatPrecRound (Q "-3") 53 .Nearest) == ("Infinity", .eq)
#guard cotPiRat (Q "1/8") 53 == cotPi (X "0.125" 53)
#guard cotPiPrecRound (X "0.3333333333333333333333333333335" 100) 80 .Floor
  == quot (sinCosPiPrecRound (X "0.3333333333333333333333333333335" 100) 380 .Nearest) 80 .Floor
