/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Acsc
import Azurite.AzFloat.Asin
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `arccsc x`

The special values (`NaN`; `|x| < 1` gives `NaN`, including `0` and tiny arguments;
`arccsc (±∞) = 0`; `arccsc (±1) = ±π/2`, correctly rounded; `p = 0`), the correctly rounded
53-bit values at `±2` (`±π/6`), `3/2`, `5/4`, the float nearest `−7/5`, `100`, `−1000`, `10¹²`,
`±(1 + 10⁻⁶)`, `22/7`, the powers of two `2^50`, `±2^70` and `3·2^50`, and the neighbours
`±(1 + 2^(−52))` of `±1`; agreement with `asin` of an exactly representable reciprocal; oddness
(`f(−x, m) = −f(x, −m)`); the directed modes; 1-, 2-, 20- and 113-bit results; `arccsc 1024` at
120 and 200 bits (the value is `2^(−10) (1 + 2^(−20)/6 + …)`); 200-bit strings; and huge
arguments: `±2^1000`, `±2^(2^30)` (exponentially close to the float `1/x`: the three modes and
both signs) and `±3·2^300`, `±3·2^(2^30)` (the correctly rounded reciprocal), at no extra cost.
References: an independent 1400-bit fixed-point evaluation of `arcsin (1/x)` rounded with exact
rationals.
-/

open Azurite Azurite.AzFloat

/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def A (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := acscPrecRound x p m
private def piN : AzFloat := X "3.141592653589793" 53
private def piC : AzFloat := X "3.1415926535897936" 53
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (A nan 53) == ("NaN", .eq)
#guard D (A zero 53) == ("NaN", .eq)
#guard D (A (X "0.5" 53) 53) == ("NaN", .eq)
#guard D (A (X "-0.9999999999999999" 53) 53) == ("NaN", .eq)
#guard A (powerOf2 (AzInt.ofInt (-1073741824))) 53 == (nan, .eq)
#guard D (A (infinity true) 53) == ("0.0", .eq)
#guard D (A (infinity false) 53) == ("0.0", .eq)
#guard D (A (infinity true) 0) == ("0.0", .eq)
#guard D (A (X "1" 53) 53) == ("1.5707963267948966", .lt)
#guard D (A (X "1" 53) 53 .Ceiling) == ("1.5707963267948968", .gt)
#guard D (A (X "-1" 53) 53) == ("-1.5707963267948966", .gt)
#guard D (A (X "-1" 53) 53 .Floor) == ("-1.5707963267948968", .lt)
#guard D (A (X "-1" 53) 53 .Ceiling) == ("-1.5707963267948966", .gt)
#guard D (A (X "2" 53) 0) == ("NaN", .eq)

-- correctly rounded values
#guard D (A (X "2" 53) 53) == ("0.5235987755982989", .gt)
#guard D (A (X "-2" 53) 53) == ("-0.5235987755982989", .lt)
#guard D (A (X "1.5" 53) 53) == ("0.7297276562269663", .lt)
#guard D (A (X "1.25" 53) 53) == ("0.9272952180016122", .lt)
#guard D (A (X "-1.4" 53) 53) == ("-0.7956029534845354", .gt)
#guard D (A (X "100" 53) 53) == ("0.010000166674167112", .lt)
#guard D (A (X "-1000" 53) 53) == ("-0.0010000001666667416", .gt)
#guard D (A (X "1000000000000" 53) 53) == ("1.0e-12", .lt)
#guard D (A (X "1.000001" 53) 53) == ("1.569382113821837", .lt)
#guard D (A (X "-1.000001" 53) 53) == ("-1.569382113821837", .gt)
#guard D (A (X "3.142857142857143" 53) 53) == ("0.3238110152735501", .gt)
#guard D (A (X "1125899906842624" 53) 53) == ("8.881784197001252e-16", .lt)
#guard D (A (X "3377699720527872" 53) 53) == ("2.9605947323337506e-16", .lt)
#guard D (A (X "1180591620717411303424" 53) 53) == ("8.470329472543003e-22", .lt)
#guard D (A (X "-1180591620717411303424" 53) 53) == ("-8.470329472543003e-22", .gt)
#guard D (A (X "2" 53) 53 .Floor) == ("0.5235987755982988", .lt)
#guard D (A (X "-1.5" 53) 53 .Floor) == ("-0.7297276562269664", .lt)
#guard D (A (X "1125899906842624" 53) 53 .Floor) == ("8.881784197001252e-16", .lt)
#guard D (A (X "-1180591620717411303424" 53) 53 .Floor) == ("-8.470329472543005e-22", .lt)
#guard D (A (X "2" 53) 53 .Ceiling) == ("0.5235987755982989", .gt)
#guard D (A (X "-1.5" 53) 53 .Ceiling) == ("-0.7297276562269663", .gt)
#guard D (A (X "1125899906842624" 53) 53 .Ceiling) == ("8.881784197001254e-16", .gt)
#guard D (A (X "-1180591620717411303424" 53) 53 .Ceiling) == ("-8.470329472543003e-22", .gt)
#guard D (A (X "2" 53) 20) == ("0.523599", .lt)
#guard D (A (X "2" 53) 1) == ("0.5", .lt)
#guard D (A (X "1.5" 53) 113) == ("0.7297276562269663634547966598133207", .gt)
#guard D (A (X "-1.5" 53) 2) == ("-0.8", .lt)
#guard A (X "1024" 53) 200 == asinPrecRound (X "0.0009765625" 53) 200 .Nearest
#guard D (A (X "1024" 53) 120) == ("0.000976562655220495715999044108961015572", .lt)
#guard A (X "2" 53) 53 == asinPrecRound (X "0.5" 53) 53 .Nearest
#guard A (X "-4" 53) 53 .Floor == asinPrecRound (X "-0.25" 53) 53 .Floor
#guard acsc (X "2" 53) == (A (X "2" 53) 53).1

-- oddness: `f(−x, m) = −f(x, −m)`
private def odd (x : AzFloat) (p : Nat) (m : RoundingMode) : Bool :=
  let r := A x p (-m)
  A (-x) p m == (-r.1, r.2.swap)
#guard odd (X "1.5" 53) 53 .Nearest && odd (X "1.5" 53) 53 .Floor && odd (X "1.5" 53) 53 .Ceiling
#guard odd (X "1.000001" 53) 20 .Floor && odd (X "1024" 53) 113 .Ceiling

-- next to `±1`
#guard D (A (X "1.0000000000000002" 53) 53) == ("1.5707963057214724", .gt)
#guard D (A (X "-1.0000000000000002" 53) 53 .Floor) == ("-1.5707963057214724", .lt)

-- 200-bit strings
#guard toString (A (X "2" 200) 200).1 == "0.5235987755982988730771072305465838140328615665625176368\
  291576"
#guard toString (A (X "-1.5" 200) 200).1 == "-0.729727656226966363454796659813320695396505914047713\
  6907089496"

-- huge powers of two: exponentially close to the float `1/x`
private def succ1 : AzFloat := X "1.0000000000000002" 53
private def pw (k : Int) : AzFloat := powerOf2 (AzInt.ofInt k)
private def tiny (k : Int) : AzFloat := h (X "1" 53) (-k)
private def pow2ok (k : Int) : Bool :=
  A (pw k) 53 == (tiny k, .lt) && A (pw k) 53 .Floor == (tiny k, .lt)
    && A (pw k) 53 .Ceiling == (h succ1 (-k), .gt)
    && A (-(pw k)) 53 == (-(tiny k), .gt) && A (-(pw k)) 53 .Ceiling == (-(tiny k), .gt)
    && A (-(pw k)) 53 .Floor == (-(h succ1 (-k)), .lt)
#guard pow2ok 1000
#guard pow2ok 1073741824
#guard pow2ok 60
#guard pow2ok 100

-- huge arguments that are not powers of two: the correctly rounded reciprocal
private def recipOk (x : AzFloat) (p : Nat) : Bool :=
  A x p == divPrecRound one x p .Nearest && A x p .Floor == divPrecRound one x p .Floor
    && A x p .Ceiling == divPrecRound one x p .Ceiling
#guard recipOk (h (X "3" 53) 300) 53
#guard recipOk (h (X "-3" 53) 300) 53
#guard recipOk (h (X "3" 53) 1073741824) 53
#guard recipOk (h (X "-3.1415926535897936" 53) 1073741824) 200
#guard D (A (h (X "3" 53) 300) 53) == ("1.6363644884325754e-91", .lt)
