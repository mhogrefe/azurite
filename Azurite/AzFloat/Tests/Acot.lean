/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Acot
import Azurite.AzFloat.Atan
import Azurite.AzFloat.ToString
import Azurite.AzFloat.OfString
import Azurite.AzRat.Parse

/-!
# Tests for `arccot x`

The special values (`NaN`; `arccot (±∞) = 0`; `arccot 0 = π/2`, correctly rounded; `p = 0`),
the correctly rounded 53-bit values at `±1` (`±π/4`), `±2`, `3/2`, `1/2`, the floats nearest
`−1/3`, `1/1000`, `−7/5`, `100`, `−1000`, `10^(±12)`, `22/7`, the powers of two `2^50`, `±2^70`,
`2^(−70)` and `3·2^50`; agreement with `atan` of an exactly representable reciprocal; oddness
(`f(−x, m) = −f(x, −m)`); the directed modes; 1-, 2-, 20-, 113- and 120-bit results; 200-bit
strings; huge arguments: `±2^1000`, `±2^(2^30)` (exponentially close to the float `1/x`, from
below: the three modes and both signs) and `±3·2^300`, `±3·2^(2^30)` (the correctly rounded
reciprocal); and tiny arguments `±2^(−1000)`, `±2^(−2^30)` (next to `±π/2`), all at no extra
cost.  References: an independent 1400-bit fixed-point evaluation of `arctan (1/x)` rounded with
exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def A (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := acotPrecRound x p m
private def piN : AzFloat := X "3.141592653589793" 53
private def piC : AzFloat := X "3.1415926535897936" 53
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k

-- special values
#guard D (A nan 53) == ("NaN", .eq)
#guard D (A (infinity true) 53) == ("0.0", .eq)
#guard D (A (infinity false) 53) == ("0.0", .eq)
#guard D (A (infinity true) 0) == ("0.0", .eq)
#guard D (A zero 53) == ("1.5707963267948966", .lt)
#guard D (A zero 53 .Ceiling) == ("1.5707963267948968", .gt)
#guard D (A (X "2" 53) 0) == ("NaN", .eq)
#guard D (A (X "1" 53) 53) == ("0.7853981633974483", .lt)
#guard D (A (X "-1" 53) 53 .Floor) == ("-0.7853981633974484", .lt)

-- correctly rounded values
#guard D (A (X "1" 53) 53) == ("0.7853981633974483", .lt)
#guard D (A (X "-1" 53) 53) == ("-0.7853981633974483", .gt)
#guard D (A (X "2" 53) 53) == ("0.4636476090008061", .lt)
#guard D (A (X "-2" 53) 53) == ("-0.4636476090008061", .gt)
#guard D (A (X "1.5" 53) 53) == ("0.5880026035475675", .lt)
#guard D (A (X "0.5" 53) 53) == ("1.1071487177940904", .lt)
#guard D (A (X "-0.3333333333333333" 53) 53) == ("-1.2490457723982544", .gt)
#guard D (A (X "0.001" 53) 53) == ("1.5697963271282298", .gt)
#guard D (A (X "-1.4" 53) 53) == ("-0.6202494859828215", .gt)
#guard D (A (X "100" 53) 53) == ("0.009999666686665238", .lt)
#guard D (A (X "-1000" 53) 53) == ("-0.0009999996666668666", .gt)
#guard D (A (X "1000000000000" 53) 53) == ("1.0e-12", .lt)
#guard D (A (X "0.000000000001" 53) 53) == ("1.5707963267938967", .gt)
#guard D (A (X "3.142857142857143" 53) 53) == ("0.3080527810237764", .gt)
#guard D (A (X "1125899906842624" 53) 53) == ("8.881784197001252e-16", .gt)
#guard D (A (X "3377699720527872" 53) 53) == ("2.9605947323337506e-16", .lt)
#guard D (A (X "1180591620717411303424" 53) 53) == ("8.470329472543003e-22", .gt)
#guard D (A (X "-1180591620717411303424" 53) 53) == ("-8.470329472543003e-22", .lt)
#guard D (A (X "8.470329472543003e-22" 53) 53) == ("1.5707963267948966", .lt)
#guard D (A (X "1" 53) 53 .Floor) == ("0.7853981633974483", .lt)
#guard D (A (X "-1" 53) 53 .Floor) == ("-0.7853981633974484", .lt)
#guard D (A (X "2" 53) 53 .Floor) == ("0.4636476090008061", .lt)
#guard D (A (X "-1.5" 53) 53 .Floor) == ("-0.5880026035475676", .lt)
#guard D (A (X "0.3333333333333333" 53) 53 .Floor) == ("1.2490457723982544", .lt)
#guard D (A (X "1125899906842624" 53) 53 .Floor) == ("8.881784197001251e-16", .lt)
#guard D (A (X "-1180591620717411303424" 53) 53 .Floor) == ("-8.470329472543003e-22", .lt)
#guard D (A (X "1" 53) 53 .Ceiling) == ("0.7853981633974484", .gt)
#guard D (A (X "-1" 53) 53 .Ceiling) == ("-0.7853981633974483", .gt)
#guard D (A (X "2" 53) 53 .Ceiling) == ("0.46364760900080615", .gt)
#guard D (A (X "-1.5" 53) 53 .Ceiling) == ("-0.5880026035475675", .gt)
#guard D (A (X "0.3333333333333333" 53) 53 .Ceiling) == ("1.2490457723982547", .gt)
#guard D (A (X "1125899906842624" 53) 53 .Ceiling) == ("8.881784197001252e-16", .gt)
#guard D (A (X "-1180591620717411303424" 53) 53 .Ceiling) == ("-8.470329472543002e-22", .gt)
#guard D (A (X "2" 53) 20) == ("0.463648", .gt)
#guard D (A (X "2" 53) 1) == ("0.5", .gt)
#guard D (A (X "1.5" 53) 113) == ("0.5880026035475675512456110806250855", .gt)
#guard D (A (X "-1.5" 53) 2) == ("-0.5", .gt)
#guard D (A (X "0.3333333333333333" 53) 2) == ("1.0", .lt)
#guard D (A (X "1024" 53) 120) == ("0.000976562189559319430403430199717290851", .lt)
#guard A (X "2" 53) 53 == atanPrecRound (X "0.5" 53) 53 .Nearest
#guard A (X "-4" 53) 53 .Floor == atanPrecRound (X "-0.25" 53) 53 .Floor
#guard A (X "0.125" 53) 113 .Ceiling == atanPrecRound (X "8" 53) 113 .Ceiling
#guard A (X "1024" 53) 200 == atanPrecRound (X "0.0009765625" 53) 200 .Nearest
#guard acot (X "2" 53) == (A (X "2" 53) 53).1

-- oddness: `f(−x, m) = −f(x, −m)`
private def odd (x : AzFloat) (p : Nat) (m : RoundingMode) : Bool :=
  let r := A x p (-m)
  A (-x) p m == (-r.1, r.2.swap)
#guard odd (X "1.5" 53) 53 .Nearest && odd (X "1.5" 53) 53 .Floor && odd (X "1.5" 53) 53 .Ceiling
#guard odd (X "0.001" 53) 20 .Floor && odd (X "1024" 53) 113 .Ceiling

-- 200-bit strings
#guard toString ((A (X "2" 200) 200).1)
  == "0.463647609000806116214256231461214402028537054286120263810933"
#guard toString ((A (X "-1.5" 200) 200).1)
  == "-0.588002603547567551245611080625085427601707246055924353726047"

-- huge powers of two: exponentially close to the float `1/x`, from below
private def pred1 : AzFloat := X "0.9999999999999999" 53
private def pw (k : Int) : AzFloat := powerOf2 (AzInt.ofInt k)
private def tiny (k : Int) : AzFloat := h (X "1" 53) (-k)
private def pow2ok (k : Int) : Bool :=
  A (pw k) 53 == (tiny k, .gt) && A (pw k) 53 .Ceiling == (tiny k, .gt)
    && A (pw k) 53 .Floor == (h pred1 (-k), .lt)
    && A (-(pw k)) 53 == (-(tiny k), .lt) && A (-(pw k)) 53 .Floor == (-(tiny k), .lt)
    && A (-(pw k)) 53 .Ceiling == (-(h pred1 (-k)), .gt)
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

-- tiny arguments: next to `±π/2`
private def tinyOk (k : Int) : Bool :=
  A (pw (-k)) 53 == (h piN (-1), .lt) && A (pw (-k)) 53 .Ceiling == (h piC (-1), .gt)
    && A (-(pw (-k))) 53 == (-(h piN (-1)), .gt)
    && A (-(pw (-k))) 53 .Floor == (-(h piC (-1)), .lt)
#guard tinyOk 1000
#guard tinyOk 1073741824
