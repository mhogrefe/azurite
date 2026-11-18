/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Asinh
import Azurite.AzFloat.Ln
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `asinh x`

The special values (`NaN`, `±∞`, `0`, `p = 0`), the correctly rounded 53-bit values from
`2^(−200)` to `700` in three modes, large arguments up to `2^100`, 1-, 2-, 20-, 113-, 120- and
200-bit results, 200-bit strings, oddness, tiny arguments `±2^(−1000)`, `±2^(−2^30)` (the value
is just inside `x`, at no cost), and huge arguments `±2^(2^30)` (where `asinh x` rounds like
`ln (2x)`).  References: an independent 6000-bit fixed-point evaluation of
`ln (x + √(x² + 1))` rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
private def dn : AzFloat := X "0.9999999999999999" 53
private def A (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := asinhPrecRound x p m
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
#guard D (A (X "1" 53) 53) == ("0.881373587019543", .gt)
#guard D (A (X "-1" 53) 53) == ("-0.881373587019543", .lt)
#guard D (A (X "2" 53) 53) == ("1.4436354751788103", .lt)
#guard D (A (X "0.5" 53) 53) == ("0.48121182505960347", .gt)
#guard D (A (X "-0.3333333333333333" 53) 53) == ("-0.32745015023725843", .lt)
#guard D (A (X "1.5" 53) 53) == ("1.1947632172871092", .lt)
#guard D (A (X "-1.4" 53) 53) == ("-1.1379820462933674", .lt)
#guard D (A (X "3.142857142857143" 53) 53) == ("1.86267921113461", .gt)
#guard D (A (X "10" 53) 53) == ("2.99822295029797", .gt)
#guard D (A (X "-100" 53) 53) == ("-5.298342365610589", .lt)
#guard D (A (X "0.001" 53) 53) == ("0.0009999998333334083", .lt)
#guard D (A (X "-0.000000000001" 53) 53) == ("-1.0e-12", .lt)
#guard D (A (X "8.881784197001252e-16" 53) 53) == ("8.881784197001252e-16", .gt)
#guard D (A (X "7.888609052210118e-31" 53) 53) == ("7.888609052210118e-31", .gt)
#guard D (A (X "-1.8669045833583425e-60" 53) 53)
  == ("-1.8669045833583425e-60", .lt)
#guard D (A (X "30" 53) 53) == ("4.09462222433053", .lt)
#guard D (A (X "-37" 53) 53) == ("-4.304247658249556", .lt)
#guard D (A (X "700" 53) 53) == ("7.2442280258070415", .gt)
#guard D (A (X "1" 53) 53 .Floor) == ("0.8813735870195429", .lt)
#guard D (A (X "-1" 53) 53 .Floor) == ("-0.881373587019543", .lt)
#guard D (A (X "1.5" 53) 53 .Floor) == ("1.1947632172871092", .lt)
#guard D (A (X "-1.4" 53) 53 .Floor) == ("-1.1379820462933674", .lt)
#guard D (A (X "0.001" 53) 53 .Floor) == ("0.0009999998333334083", .lt)
#guard D (A (X "-100" 53) 53 .Floor) == ("-5.298342365610589", .lt)
#guard D (A (X "7.888609052210118e-31" 53) 53 .Floor) == ("7.888609052210117e-31", .lt)
#guard D (A (X "1" 53) 53 .Ceiling) == ("0.881373587019543", .gt)
#guard D (A (X "-1" 53) 53 .Ceiling) == ("-0.8813735870195429", .gt)
#guard D (A (X "1.5" 53) 53 .Ceiling) == ("1.1947632172871094", .gt)
#guard D (A (X "-1.4" 53) 53 .Ceiling) == ("-1.1379820462933672", .gt)
#guard D (A (X "0.001" 53) 53 .Ceiling) == ("0.0009999998333334085", .gt)
#guard D (A (X "-100" 53) 53 .Ceiling) == ("-5.298342365610588", .gt)
#guard D (A (X "7.888609052210118e-31" 53) 53 .Ceiling) == ("7.888609052210118e-31\
  ", .gt)
#guard D (A (X "1" 53) 20) == ("0.881373", .lt)
#guard D (A (X "1" 53) 1) == ("1.0", .gt)
#guard D (A (X "-1.5" 53) 2) == ("-1.0", .gt)
#guard D (A (X "1.5" 53) 113) == ("1.1947632172871093041119308285190906", .gt)
#guard D (A (X "0.3333333333333333333333333333333333333333333333333333333333334" 200) 200) == ("0.3\
  274501502372584433225352599882581277005245289907674512756297\
  ", .gt)
#guard D (A (X "0.333333333333333333333333333333333333333333333333333333333333\
  4" 200) 10 .Floor) == ("0.327", .lt)
#guard D (A (X "10" 53) 120) == ("2.998222950297969738846595537596453477", .gt)
#guard D (A (X "1000000" 110) 53) == ("14.50865773852447", .gt)
#guard D (A (X "1000000" 110) 53 .Floor) == ("14.508657738524468", .lt)
#guard D (A (X "-123456789012345678901234567890" 110) 53) == ("-67.67883589970292", .gt)
#guard D (A (X "-123456789012345678901234567890" 110) 53 .Floor) == ("-67.67883589970293", .lt)
#guard D (A (X "1267650600228229401496703205376" 110) 53) == ("70.00786523655448", .gt)
#guard D (A (X "1267650600228229401496703205376" 110) 53 .Floor) == ("70.00786523655447", .lt)
#guard asinh (X "1.5" 53) == (A (X "1.5" 53) 53).1
#guard toString (asinhPrecRound (X "1" 200) 200 .Nearest).1 == "0.881373587019543025232609324979792\
  309028160328261635410753296"
#guard toString (asinhPrecRound (X "-1.5" 200) 200 .Nearest).1 == "-1.19476321728710930411193082851\
  9090523536162075153005429270681"

-- oddness: `f(−x, m) = −f(x, −m)`
private def odd (x : AzFloat) (p : Nat) (m : RoundingMode) : Bool :=
  let r := A x p (-m)
  A (-x) p m == (-r.1, r.2.swap)
#guard odd (X "1.5" 53) 53 .Nearest && odd (X "1.5" 53) 53 .Floor
#guard odd (X "100" 53) 20 .Ceiling && odd (X "0.001" 53) 113 .Floor
#guard odd (h (X "1" 53) (-1000)) 53 .Ceiling && odd (h (X "1" 53) 1000) 53 .Ceiling

-- tiny arguments: just inside `x`
private def tinyOk (k : Int) : Bool :=
  let x := h (X "1" 53) (-k)
  A x 53 == (x, .gt) && A x 53 .Ceiling == (x, .gt) && A x 53 .Floor == (h dn (-k), .lt)
    && A (-x) 53 == (-x, .lt) && A (-x) 53 .Floor == (-x, .lt)
    && A (-x) 53 .Ceiling == (-(h dn (-k)), .gt)
#guard tinyOk 200
#guard tinyOk 1000
#guard tinyOk 1073741824

-- huge arguments: `asinh x` rounds like `ln (2x)`
private def big (x : AzFloat) (p : Nat) (m : RoundingMode) : Bool :=
  A x p m == lnPrecRound (h x 1) p m
#guard big (h (X "1" 53) 1073741824) 53 .Nearest && big (h (X "3" 53) 1073741824) 53 .Floor
#guard big (h (X "5" 53) 100000) 113 .Ceiling && odd (h (X "3" 53) 1073741824) 53 .Floor
