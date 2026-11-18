/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Sinh
import Azurite.AzFloat.Exp
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse
import Azurite.AzFloat.OfString

/-!
# Tests for `sinh x`

The special values (`NaN`, `±∞`, `0`, `p = 0`), the correctly rounded 53-bit values from
`2^(−200)` to `700` in three modes, 1-, 2-, 20-, 113-, 120- and 200-bit results, a 200-bit
string, oddness, tiny arguments `±2^(−1000)`, `±2^(−2^30)`, `±3·2^(−2^30)` (the value is just
outside `x`, at no cost), an argument more precise than the result, and large arguments
(`±2^20`, where `sinh x` rounds like `±exp |x| / 2`).  References: an independent 6000-bit
fixed-point evaluation of `(e^x − e^(−x))/2` rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def big1 : AzFloat := X "0.3333333333333333333333333333333333333333333333333333333333334\
  " 200
private def A (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := sinhPrecRound x p m
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (A nan 53) == ("NaN", .eq)
#guard D (A (infinity true) 53) == ("Infinity", .eq)
#guard D (A (infinity false) 53) == ("-Infinity", .eq)
#guard D (A (infinity false) 0) == ("-Infinity", .eq)
#guard D (A zero 53) == ("0.0", .eq)
#guard D (A zero 0) == ("0.0", .eq)
#guard D (A (X "2" 53) 0) == ("NaN", .eq)

-- correctly rounded values
#guard D (A (X "1" 53) 53) == ("1.1752011936438014", .lt)
#guard D (A (X "-1" 53) 53) == ("-1.1752011936438014", .gt)
#guard D (A (X "2" 53) 53) == ("3.6268604078470186", .lt)
#guard D (A (X "0.5" 53) 53) == ("0.5210953054937474", .gt)
#guard D (A (X "-0.3333333333333333" 53) 53) == ("-0.3395405572561501", .lt)
#guard D (A (X "1.5" 53) 53) == ("2.1292794550948173", .lt)
#guard D (A (X "-1.4" 53) 53) == ("-1.9043015014515339", .lt)
#guard D (A (X "3.142857142857143" 53) 53) == ("11.563406494500514", .gt)
#guard D (A (X "10" 53) 53) == ("11013.232874703393", .gt)
#guard D (A (X "-100" 53) 53) == ("-1.3440585709080678e43", .lt)
#guard D (A (X "0.001" 53) 53) == ("0.001000000166666675", .gt)
#guard D (A (X "-0.000000000001" 53) 53) == ("-1.0e-12", .gt)
#guard D (A (X "8.881784197001252e-16" 53) 53) == ("8.881784197001252e-16", .lt)
#guard D (A (X "7.888609052210118e-31" 53) 53) == ("7.888609052210118e-31", .lt)
#guard D (A (X "-1.8669045833583425e-60" 53) 53)
  == ("-1.8669045833583425e-60", .gt)
#guard D (A (X "30" 53) 53) == ("5343237290762.231", .gt)
#guard D (A (X "-37" 53) 53) == ("-5859571186401306.0", .lt)
#guard D (A (X "700" 53) 53) == ("5.0711602736750225e303", .lt)
#guard D (A (X "1" 53) 53 .Floor) == ("1.1752011936438014", .lt)
#guard D (A (X "-1" 53) 53 .Floor) == ("-1.1752011936438016", .lt)
#guard D (A (X "1.5" 53) 53 .Floor) == ("2.1292794550948173", .lt)
#guard D (A (X "-1.4" 53) 53 .Floor) == ("-1.9043015014515339", .lt)
#guard D (A (X "0.001" 53) 53 .Floor) == ("0.0010000001666666748", .lt)
#guard D (A (X "-100" 53) 53 .Floor) == ("-1.3440585709080678e43", .lt)
#guard D (A (X "7.888609052210118e-31" 53) 53 .Floor) == ("7.888609052210118e-31", .lt)
#guard D (A (X "1" 53) 53 .Ceiling) == ("1.1752011936438016", .gt)
#guard D (A (X "-1" 53) 53 .Ceiling) == ("-1.1752011936438014", .gt)
#guard D (A (X "1.5" 53) 53 .Ceiling) == ("2.1292794550948178", .gt)
#guard D (A (X "-1.4" 53) 53 .Ceiling) == ("-1.9043015014515337", .gt)
#guard D (A (X "0.001" 53) 53 .Ceiling) == ("0.001000000166666675", .gt)
#guard D (A (X "-100" 53) 53 .Ceiling) == ("-1.3440585709080676e43", .gt)
#guard D (A (X "7.888609052210118e-31" 53) 53 .Ceiling) == ("7.88860905221012e-31", .gt)
#guard D (A (X "1" 53) 20) == ("1.175201", .gt)
#guard D (A (X "1" 53) 1) == ("1.0", .lt)
#guard D (A (X "-1.5" 53) 2) == ("-2.0", .gt)
#guard D (A (X "1.5" 53) 113) == ("2.1292794550948174968343874946776316", .lt)
#guard D (A big1 200)
  == ("0.3395405572561501391012606113386035850723972276889639127383233", .lt)
#guard D (A big1 10 .Floor) == ("0.3394", .lt)
#guard D (A (X "10" 53) 120) == ("11013.2328747033933772365245548463644", .lt)
#guard sinh (X "1.5" 53) == (A (X "1.5" 53) 53).1
#guard toString (sinhPrecRound (X "1" 200) 200 .Nearest).1
  == "1.175201193643801456882381850595600815155717981334095870229566"
#guard toString (sinhPrecRound (X "-1.5" 200) 200 .Nearest).1
  == "-2.129279455094817496834387494677631648831789119504293864014407"

-- oddness: `f(−x, m) = −f(x, −m)`
private def odd (x : AzFloat) (p : Nat) (m : RoundingMode) : Bool :=
  let r := A x p (-m)
  A (-x) p m == (-r.1, r.2.swap)
#guard odd (X "1.5" 53) 53 .Nearest && odd (X "1.5" 53) 53 .Floor && odd (X "100" 53) 20 .Ceiling
#guard odd (X "0.001" 53) 113 .Floor && odd (h (X "1" 53) (-1000)) 53 .Ceiling

-- tiny arguments: just outside `x`
private def up : AzFloat := X "1.0000000000000002" 53
private def tinyOk (k : Int) : Bool :=
  let x := h (X "1" 53) (-k)
  A x 53 == (x, .lt) && A x 53 .Floor == (x, .lt) && A x 53 .Ceiling == (h up (-k), .gt)
    && A (-x) 53 == (-x, .gt) && A (-x) 53 .Ceiling == (-x, .gt)
    && A (-x) 53 .Floor == (-(h up (-k)), .lt)
#guard tinyOk 200
#guard tinyOk 1000
#guard tinyOk 1073741824
private def t3 : AzFloat := h (X "3" 53) (-1073741824)
#guard A t3 53 == (t3, .lt)
#guard A t3 2 .Ceiling == (h (X "4" 2) (-1073741824), .gt)
#guard A t3 1 == (h (X "4" 1) (-1073741824), .gt)
#guard A (-t3) 1 .Ceiling == (-(h (X "2" 1) (-1073741824)), .gt)
-- an argument more precise than the result
private def fine : AzFloat := h (X "1267650600228229401496703205377" 101) (-300)
#guard D (A fine 53) == ("6.223015277861142e-61", .lt)
#guard D (A fine 53 .Ceiling) == ("6.223015277861143e-61", .gt)
#guard A fine 101 == (fine, .lt)

-- large arguments: `sinh x` rounds like `exp |x| / 2`
private def big (x : AzFloat) (p : Nat) (m : RoundingMode) : Bool :=
  let r := expPrecRound x p m
  A x p m == (h r.1 (-1), r.2)
#guard big (X "1048576" 53) 53 .Nearest && big (X "1048576" 53) 53 .Floor
#guard big (X "15432098.625" 53) 20 .Ceiling && big (X "1000" 53) 113 .Nearest
#guard odd (X "1048576" 53) 53 .Floor
