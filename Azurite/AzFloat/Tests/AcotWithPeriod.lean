/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcotWithPeriod
import Azurite.AzFloat.ToString
import Azurite.AzFloat.OfString
import Azurite.AzRat.Parse

/-!
# Tests for `arccot (x) u / (2π)`

The special values (`NaN`; `0` at `±∞`; `u = 0`; `u/4` at `0`; `±u/8` at `±1` — exact or
correctly rounded; `p = 0`), the correctly rounded 53-bit values in degrees on both sides of
`1`, other periods (`1`, `7`, `400`, `2^64 − 1`), oddness, the directed modes, 1-, 20- and
113-bit results, a 200-bit string, the neighbours `±(1 + 2^(−52))` of `±1`, tiny arguments
`±2^(−60)`, `±2^(−2^30)` (the value is next to the quarter turn `±u/4`, at no extra cost), and
huge arguments `±2^1000`, `±2^(2^30)`, `±3·2^(2^30)` (the value is `u/(2πx)` up to a relative
`2^(−2e)`, at no extra cost).  References: an independent 1400-bit fixed-point evaluation
rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def W (x : AzFloat) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  acotWithPeriodPrecRound x u p m
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k

-- special values
#guard D (W nan 360 53) == ("NaN", .eq)
#guard D (W nan 0 53) == ("NaN", .eq)
#guard D (W (infinity true) 360 53) == ("0.0", .eq)
#guard D (W (infinity false) 360 53) == ("0.0", .eq)
#guard D (W (infinity false) 0 0) == ("0.0", .eq)
#guard D (W zero 360 53) == ("9.0e1", .eq)
#guard D (W zero 0 53) == ("0.0", .eq)
#guard D (W zero 7 53) == ("1.75", .eq)
#guard D (W zero 7 1) == ("2.0", .gt)
#guard D (W zero 7 1 .Floor) == ("1.0", .lt)
#guard D (W (X "3" 53) 0 53) == ("0.0", .eq)
#guard D (W (X "-0.3333333333333333" 53) 0 53) == ("0.0", .eq)
#guard D (W (X "-1" 53) 0 53) == ("0.0", .eq)
#guard D (W (X "3" 53) 360 0) == ("NaN", .eq)
#guard D (W (X "1" 53) 360 53) == ("45.0", .eq)
#guard D (W (X "-1" 200) 360 53) == ("-45.0", .eq)
#guard D (W (X "1" 53) 7 53) == ("0.875", .eq)
#guard D (W (X "1" 53) 7 1) == ("1.0", .gt)
#guard D (W (X "-1" 53) 7 1) == ("-1.0", .lt)
#guard D (W (X "-1" 53) 7 1 .Ceiling) == ("-0.5", .gt)

-- correctly rounded values
#guard D (W (X "3" 53) 360 53) == ("18.43494882292201", .lt)
#guard D (W (X "-3" 53) 360 53) == ("-18.43494882292201", .gt)
#guard D (W (X "1.5" 53) 360 53) == ("33.690067525979785", .lt)
#guard D (W (X "-1.4" 53) 360 53) == ("-35.53767779197438", .gt)
#guard D (W (X "0.25" 53) 360 53) == ("75.96375653207352", .lt)
#guard D (W (X "100" 53) 360 53) == ("0.5729386976834859", .gt)
#guard D (W (X "-1000" 53) 360 53) == ("-0.05729576041450061", .gt)
#guard D (W (X "0.001" 53) 360 53) == ("89.9427042395855", .lt)
#guard D (W (X "-0.0029296875" 53) 360 53) == ("-89.83214175120297", .gt)
#guard D (W (X "3.142857142857143" 53) 360 53) == ("17.650124219930124", .gt)
#guard D (W (X "1125899906842624" 53) 360 53) == ("5.088887490341627e-14", .gt)
#guard D (W (X "2" 53) 360 53) == ("26.56505117707799", .gt)
#guard D (W (X "-0.5" 53) 360 53) == ("-63.43494882292201", .gt)
#guard D (W (X "1.5" 53) 1 53) == ("0.09358352090549941", .gt)
#guard D (W (X "-4" 53) 1 53) == ("-0.03898956518868466", .gt)
#guard D (W (X "1.5" 53) 7 53) == ("0.6550846463384958", .lt)
#guard D (W (X "-4" 53) 7 53) == ("-0.2729269563207926", .gt)
#guard D (W (X "1.5" 53) 400 53) == ("37.43340836219976", .gt)
#guard D (W (X "-4" 53) 400 53) == ("-15.595826075473864", .gt)
#guard D (W (X "1.5" 53) 18446744073709551615 53) == ("1.7263112596603953e18", .gt)
#guard D (W (X "-4" 53) 18446744073709551615 53) == ("-7.19230530580881e17", .gt)
#guard D (W (X "1.5" 53) 360 53 .Floor) == ("33.690067525979785", .lt)
#guard D (W (X "-4" 53) 360 53 .Floor) == ("-14.036243467926479", .lt)
#guard D (W (X "1.5" 53) 360 53 .Ceiling) == ("33.69006752597979", .gt)
#guard D (W (X "-4" 53) 360 53 .Ceiling) == ("-14.036243467926477", .gt)
#guard D (W (X "1.5" 53) 360 20) == ("33.69006", .lt)
#guard D (W (X "-4" 53) 360 1) == ("-2.0e1", .lt)
#guard D (W (X "1.5" 53) 360 113) == ("33.69006752597978691352549456166014", .lt)
#guard acotWithPeriod (X "1.5" 53) 360 == (W (X "1.5" 53) 360 53).1
#guard toString ((acotWithPeriodPrecRound (X "1.5" 200) 360 200 .Nearest).1)
  == "33.6900675259797869135254945616601394202563635159059448556286"

-- oddness: `f(−x, u, m) = −f(x, u, −m)`
private def odd (x : AzFloat) (u : UInt64) (p : Nat) (m : RoundingMode) : Bool :=
  let r := W x u p (-m)
  W (-x) u p m == (-r.1, r.2.swap)
#guard odd (X "1.5" 53) 360 53 .Nearest && odd (X "1.5" 53) 7 53 .Floor
#guard odd (X "0.001" 53) 400 20 .Ceiling && odd (X "1" 53) 7 2 .Floor

-- next to `±1`
#guard D (W (X "1.0000000000000002" 53) 360 53) == ("44.99999999999999", .lt)
#guard D (W (X "-1.0000000000000002" 53) 360 53) == ("-44.99999999999999", .gt)

private def pw (k : Int) : AzFloat := powerOf2 (AzInt.ofInt k)

-- tiny arguments: just inside the quarter turn
private def b90 : AzFloat := X "89.99999999999999" 53
private def tinyOk (k : Int) : Bool :=
  W (pw (-k)) 360 53 == (X "90" 53, .gt) && W (pw (-k)) 360 53 .Floor == (b90, .lt)
    && W (pw (-k)) 360 53 .Ceiling == (X "90" 53, .gt)
    && W (-(pw (-k))) 360 53 == (X "-90" 53, .lt)
    && W (-(pw (-k))) 360 53 .Floor == (X "-90" 53, .lt)
    && W (-(pw (-k))) 360 53 .Ceiling == (-b90, .gt)
    && W (h (X "3" 53) (-k)) 7 53 == (X "1.75" 53, .gt)
    && W (h (X "3" 53) (-k)) 7 53 .Floor == (X "1.7499999999999998" 53, .lt)
#guard tinyOk 60
#guard tinyOk 200
#guard tinyOk 1073741824

-- huge arguments: `360/(2π) / x`
private def cN : AzFloat := X "57.29577951308232" 53
private def cF : AzFloat := X "57.295779513082316" 53
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
