/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcscWithPeriod
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `arccsc (x) u / (2π)`

The special values (`NaN`; `|x| < 1` gives `NaN`, including `0` and for `u = 0`; `0` at `±∞`;
`u = 0`; `±u/4` at `±1`; `±u/12` at `±2` — exact for `u = 360`, the correctly rounded rationals
for `u = 7`, `1` in several modes; `p = 0`), the correctly rounded 53-bit values in degrees,
other periods (`1`, `7`, `400`, `2^64 − 1`), oddness, the directed modes, 1-, 20- and 113-bit
results, a 200-bit string, the neighbours `±(1 + 2^(−52))` of `±1`, and huge arguments
`±2^1000`, `±2^(2^30)`, `±3·2^(2^30)`: the value is `u/(2πx)` up to a relative `2^(−2e)`, at no
extra cost.  References: an independent 1400-bit fixed-point evaluation rounded with exact
rationals.
-/

open Azurite Azurite.AzFloat

/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def W (x : AzFloat) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  acscWithPeriodPrecRound x u p m
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (W nan 360 53) == ("NaN", .eq)
#guard D (W zero 360 53) == ("NaN", .eq)
#guard D (W zero 0 53) == ("NaN", .eq)
#guard D (W (X "0.5" 53) 360 53) == ("NaN", .eq)
#guard D (W (X "-0.75" 53) 0 53) == ("NaN", .eq)
#guard D (W (infinity true) 360 53) == ("0.0", .eq)
#guard D (W (infinity false) 360 53) == ("0.0", .eq)
#guard D (W (infinity false) 0 0) == ("0.0", .eq)
#guard D (W (X "3" 53) 0 53) == ("0.0", .eq)
#guard D (W (X "-1" 53) 0 53) == ("0.0", .eq)
#guard D (W (X "3" 53) 360 0) == ("NaN", .eq)
#guard D (W (X "1" 53) 360 53) == ("9.0e1", .eq)
#guard D (W (X "-1" 200) 360 53) == ("-9.0e1", .eq)
#guard D (W (X "1" 53) 7 1) == ("2.0", .gt)
#guard D (W (X "-1" 53) 7 1) == ("-2.0", .lt)
-- a twelfth of a turn
#guard D (W (X "2" 53) 360 53) == ("3.0e1", .eq)
#guard D (W (X "-2" 200) 360 53) == ("-3.0e1", .eq)
#guard D (W (X "2" 53) 3 53) == ("0.25", .eq)
#guard D (W (X "2" 53) 7 53) == ("0.5833333333333334", .gt)
#guard D (W (X "2" 53) 7 53 .Floor) == ("0.5833333333333333", .lt)
#guard D (W (X "-2" 53) 7 53) == ("-0.5833333333333334", .lt)
#guard D (W (X "2" 53) 1 53) == ("0.08333333333333333", .lt)
#guard D (W (X "-2" 53) 1 53 .Floor) == ("-0.08333333333333334", .lt)

-- correctly rounded values
#guard D (W (X "3" 53) 360 53) == ("19.47122063449069", .gt)
#guard D (W (X "-3" 53) 360 53) == ("-19.47122063449069", .lt)
#guard D (W (X "1.5" 53) 360 53) == ("41.810314895778596", .lt)
#guard D (W (X "-1.4" 53) 360 53) == ("-45.58469140280703", .lt)
#guard D (W (X "1.25" 53) 360 53) == ("53.13010235415598", .gt)
#guard D (W (X "100" 53) 360 53) == ("0.5729673448571526", .lt)
#guard D (W (X "-1000" 53) 360 53) == ("-0.0572957890623832", .gt)
#guard D (W (X "1.000001" 53) 360 53) == ("89.91897156531104", .gt)
#guard D (W (X "-1.000001" 53) 360 53) == ("-89.91897156531104", .lt)
#guard D (W (X "3.142857142857143" 53) 360 53) == ("18.55300453502066", .lt)
#guard D (W (X "1125899906842624" 53) 360 53) == ("5.088887490341627e-14", .gt)
#guard D (W (X "1.5" 53) 1 53) == ("0.11613976359938499", .lt)
#guard D (W (X "-4" 53) 1 53) == ("-0.04021531162758312", .gt)
#guard D (W (X "1.5" 53) 7 53) == ("0.812978345195695", .gt)
#guard D (W (X "-4" 53) 7 53) == ("-0.28150718139308184", .gt)
#guard D (W (X "1.5" 53) 400 53) == ("46.455905439754", .gt)
#guard D (W (X "-4" 53) 400 53) == ("-16.08612465103325", .gt)
#guard W (X "1.5" 53) 18446744073709551615 53 == (X "2142400495898983424" 53, .lt)
#guard W (X "-4" 53) 18446744073709551615 53 == (X "-741841561438501760" 53, .gt)
#guard D (W (X "1.5" 53) 360 53 .Floor) == ("41.810314895778596", .lt)
#guard D (W (X "-4" 53) 360 53 .Floor) == ("-14.477512185929925", .lt)
#guard D (W (X "1.5" 53) 360 53 .Ceiling) == ("41.8103148957786", .gt)
#guard D (W (X "-4" 53) 360 53 .Ceiling) == ("-14.477512185929923", .gt)
#guard D (W (X "1.5" 53) 360 20) == ("41.8103", .lt)
#guard D (W (X "-4" 53) 360 1) == ("-2.0e1", .lt)
#guard D (W (X "1.5" 53) 360 113) == ("41.81031489577859806585791673057826", .lt)
#guard acscWithPeriod (X "1.5" 53) 360 == (W (X "1.5" 53) 360 53).1
#guard toString (acscWithPeriodPrecRound (X "1.5" 200) 360 200 .Nearest).1
  == "41.81031489577859806585791673057825953101411953590134775337278"

-- oddness: `f(−x, u, m) = −f(x, u, −m)`
private def odd (x : AzFloat) (u : UInt64) (p : Nat) (m : RoundingMode) : Bool :=
  let r := W x u p (-m)
  W (-x) u p m == (-r.1, r.2.swap)
#guard odd (X "1.5" 53) 360 53 .Nearest && odd (X "1.5" 53) 7 53 .Floor
#guard odd (X "1.000001" 53) 400 20 .Ceiling && odd (X "2" 53) 7 53 .Floor

-- next to `±1`
#guard D (W (X "1.0000000000000002" 53) 360 53) == ("89.99999879258174", .gt)
#guard D (W (X "-1.0000000000000002" 53) 360 53) == ("-89.99999879258174", .lt)
#guard D (W (X "-1.0000000000000002" 53) 360 53 .Ceiling)
  == ("-89.99999879258172", .gt)

-- huge arguments: `360/(2π) / x`
private def cN : AzFloat := X "57.29577951308232" 53
private def cF : AzFloat := X "57.295779513082316" 53
private def pw (k : Int) : AzFloat := powerOf2 (AzInt.ofInt k)
private def hugeOk (k : Int) : Bool :=
  W (pw k) 360 53 == (h cN (-k), .gt) && W (pw k) 360 53 .Floor == (h cF (-k), .lt)
    && W (pw k) 360 53 .Ceiling == (h cN (-k), .gt)
    && W (-(pw k)) 360 53 == (-(h cN (-k)), .lt)
    && W (-(pw k)) 360 53 .Ceiling == (-(h cF (-k)), .gt)
#guard hugeOk 1000
#guard hugeOk 1073741824
#guard hugeOk 60
private def big3 : AzFloat := h (X "3" 53) 1073741824
#guard W big3 360 53 == (h (X "19.09859317102744" 53) (-1073741824), .lt)
#guard W big3 360 53 .Ceiling
  == (h (X "19.098593171027442" 53) (-1073741824), .gt)
#guard W (-big3) 360 53 .Ceiling
  == (-(h (X "19.09859317102744" 53) (-1073741824)), .gt)
