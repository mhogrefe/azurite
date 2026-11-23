/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LnBarnesG
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `ln |G|` and `ln G` of the Barnes `G`-function

`ln G(1/2) = −0.50543305448969538279768498980834495172139910146661993278…`; the zeros
(`−∞`), the integers (`0` at `1, 2, 3`, `ln 2` at `4`, `ln 34560` at `7`, `65` through the
loop), the signs at negative arguments, `NaN` of `ln G` where `G < 0`, large arguments,
arguments that are not finite, `p = 0`, and rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- The float nearest to a rational at 53 bits. -/
private def F (s : String) : AzFloat := ofAzRat (Q s) 53
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)
private def DL (r : (AzFloat × Ordering) × Bool) : String × Ordering × Bool :=
  (toString r.1.1, r.1.2, r.2)
private def LA (x : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  DL (lnAbsBarnesGPrecRound (F x) p m)
private def L (x : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  D (lnBarnesGPrecRound (F x) p m)
private def LAR (x : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  DL (lnAbsBarnesGRatPrecRound (Q x) p m)
private def LR (x : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  D (lnBarnesGRatPrecRound (Q x) p m)

-- not finite, `p = 0`
#guard DL (lnAbsBarnesGPrecRound nan 53 .Nearest) == ("NaN", .eq, true)
#guard DL (lnAbsBarnesGPrecRound (infinity true) 53 .Nearest) == ("Infinity", .eq, true)
#guard DL (lnAbsBarnesGPrecRound (infinity false) 53 .Nearest) == ("NaN", .eq, true)
#guard LA "1/2" 0 == ("NaN", .eq, true)
#guard LA "0" 0 == ("-Infinity", .eq, true)

-- the zeros and the integers
#guard LA "0" 53 == ("-Infinity", .eq, true)
#guard LA "-3" 53 == ("-Infinity", .eq, true)
#guard LA "1" 53 == ("0.0", .eq, true)
#guard LA "2" 53 == ("0.0", .eq, true)
#guard LA "3" 53 == ("0.0", .eq, true)
#guard LA "4" 53 == ("0.6931471805599453", .lt, true)
#guard LA "7" 53 == ("10.450452222917992", .lt, true)
#guard LA "64" 53 == ("5302.683308695252", .gt, true)
#guard LA "65" 53 == ("5503.6926250945335", .gt, true)

-- values and signs
#guard LA "1/2" 53 == ("-0.5054330544896953", .gt, true)
#guard LA "1/2" 53 .Floor == ("-0.5054330544896954", .lt, true)
#guard LA "1/2" 200
  == ("-0.5054330544896953827976849898083449517213991014666199327898276", .gt, true)
#guard LA "3/2" 53 == ("0.06693188843500471", .gt, true)
#guard LA "-1/2" 53 == ("-1.7709451779743408", .lt, false)
#guard LA "-5/2" 53 == ("-2.5747484768531477", .gt, true)
#guard LA "201/2" 53 == ("15437.05347433899", .lt, true)
#guard LA "-41/2" 53 == ("357.1406193200218", .lt, false)
#guard LA "1000000" 53 == ("6157743382414.784", .lt, true)
#guard (toString (lnAbsBarnesG (F "1/2")).1, (lnAbsBarnesG (F "1/2")).2)
  == ("-0.5054330544896953", true)

-- `ln G`
#guard L "1/2" 53 == ("-0.5054330544896953", .gt)
#guard L "-1/2" 53 == ("NaN", .eq)
#guard L "-5/2" 53 == ("-2.5747484768531477", .gt)
#guard L "0" 53 == ("-Infinity", .eq)
#guard L "7" 53 == ("10.450452222917992", .lt)
#guard toString (lnBarnesG (F "1/2")) == "-0.5054330544896953"

-- rationals
#guard LAR "1/2" 53 == ("-0.5054330544896953", .gt, true)
#guard LAR "1/3" 53 == ("-0.9160944434130751", .lt, true)
#guard LAR "-1/3" 53 == ("-1.6542713519195547", .lt, false)
#guard LAR "-22/7" 53 == ("-5.193471805586307", .lt, true)
#guard LAR "7" 53 == ("10.450452222917992", .lt, true)
#guard LAR "0" 53 == ("-Infinity", .eq, true)
#guard LAR "-3" 53 == ("-Infinity", .eq, true)
#guard LAR "65" 53 == ("5503.6926250945335", .gt, true)
#guard LAR "301/3" 53 == ("15377.261726673827", .lt, true)
#guard LR "1/3" 53 == ("-0.9160944434130751", .lt)
#guard LR "-1/3" 53 == ("NaN", .eq)
#guard LR "1/3" 100 == ("-0.916094443413075069489569917361", .gt)
#guard toString (lnAbsBarnesGRat (Q "1/3") 53).1 == "-0.9160944434130751"
#guard toString (lnBarnesGRat (Q "1/3") 53) == "-0.9160944434130751"
