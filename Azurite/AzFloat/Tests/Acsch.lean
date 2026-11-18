/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Acsch
import Azurite.AzFloat.Ln
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `acsch x`

The special values (`NaN`, `±∞ ↦ 0`, `acsch 0 = +∞`, `p = 0`), the correctly rounded 53-bit
values from `2^(−200)` to `2^101` in three modes — across the switch to the huge-argument
enclosure — 1-, 2-, 20-, 113-, 120- and 200-bit results, 200-bit strings, oddness, huge
arguments `±2^1000`, `±2^(2^30)`, `±3·2^(2^30)` (the value is just inside `1/x`, at no cost),
and tiny arguments `2^(−2^30)` (where `acsch x` rounds like `ln (2/x)`).  References: an
independent 6000-bit fixed-point evaluation of `ln (1/x + √(1/x² + 1))` rounded with exact
rationals.
-/

open Azurite Azurite.AzFloat

/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
/-- `0.3333333333…` at 200 bits. -/
private def third200 : AzFloat :=
  X "0.3333333333333333333333333333333333333333333333333333333333334" 200
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
private def dn : AzFloat := X "0.9999999999999999" 53
private def A (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := acschPrecRound x p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (A nan 53) == ("NaN", .eq)
#guard D (A (infinity true) 53) == ("0.0", .eq)
#guard D (A (infinity false) 53) == ("0.0", .eq)
#guard D (A (infinity false) 0) == ("0.0", .eq)
#guard D (A zero 53) == ("Infinity", .eq)
#guard D (A zero 0) == ("Infinity", .eq)
#guard D (A (X "2" 53) 0) == ("NaN", .eq)

-- correctly rounded values
#guard D (A (X "1" 53) 53) == ("0.881373587019543", .gt)
#guard D (A (X "-1" 53) 53) == ("-0.881373587019543", .lt)
#guard D (A (X "2" 53) 53) == ("0.48121182505960347", .gt)
#guard D (A (X "0.5" 53) 53) == ("1.4436354751788103", .lt)
#guard D (A (X "-0.3333333333333333" 53) 53) == ("-1.8184464592320668", .gt)
#guard D (A (X "1.5" 53) 53) == ("0.6251451172504167", .lt)
#guard D (A (X "-1.4" 53) 53) == ("-0.6643306045898852", .lt)
#guard D (A (X "3.142857142857143" 53) 53) == ("0.313043843408309", .lt)
#guard D (A (X "10" 53) 53) == ("0.09983407889920756", .lt)
#guard D (A (X "-100" 53) 53) == ("-0.009999833340832888", .lt)
#guard D (A (X "0.001" 53) 53) == ("7.600902709541988", .lt)
#guard D (A (X "-0.000000000001" 53) 53) == ("-28.324168296488494", .lt)
#guard D (A (X "8.881784197001252e-16" 53) 53) == ("35.35050620855721", .gt)
#guard D (A (X "7.888609052210118e-31" 53) 53) == ("70.00786523655448", .gt)
#guard D (A (X "-1.8669045833583425e-60" 53) 53) ==
  ("-138.2239710038809", .lt)
#guard D (A (X "30" 53) 53) == ("0.03332716357820717", .lt)
#guard D (A (X "-37" 53) 53) == ("-0.02702373774690619", .gt)
#guard D (A (X "700" 53) 53) == ("0.0014285709426632256", .lt)
#guard D (A (X "1" 53) 53 .Floor) == ("0.8813735870195429", .lt)
#guard D (A (X "-1" 53) 53 .Floor) == ("-0.881373587019543", .lt)
#guard D (A (X "1.5" 53) 53 .Floor) == ("0.6251451172504167", .lt)
#guard D (A (X "-1.4" 53) 53 .Floor) == ("-0.6643306045898852", .lt)
#guard D (A (X "0.001" 53) 53 .Floor) == ("7.600902709541988", .lt)
#guard D (A (X "-100" 53) 53 .Floor) == ("-0.009999833340832888", .lt)
#guard D (A (X "7.888609052210118e-31" 53) 53 .Floor) == ("70.00786523655447", .lt)
#guard D (A (X "1" 53) 53 .Ceiling) == ("0.881373587019543", .gt)
#guard D (A (X "-1" 53) 53 .Ceiling) == ("-0.8813735870195429", .gt)
#guard D (A (X "1.5" 53) 53 .Ceiling) == ("0.6251451172504168", .gt)
#guard D (A (X "-1.4" 53) 53 .Ceiling) == ("-0.6643306045898851", .gt)
#guard D (A (X "0.001" 53) 53 .Ceiling) == ("7.600902709541989", .gt)
#guard D (A (X "-100" 53) 53 .Ceiling) == ("-0.009999833340832886", .gt)
#guard D (A (X "7.888609052210118e-31" 53) 53 .Ceiling) == ("70.00786523655448", .gt)
#guard D (A (X "1" 53) 20) == ("0.881373", .lt)
#guard D (A (X "1" 53) 1) == ("1.0", .gt)
#guard D (A (X "-1.5" 53) 2) == ("-0.8", .lt)
#guard D (A (X "1.5" 53) 113) == ("0.6251451172504166876342516732261024", .lt)
#guard D (A third200 200) ==
  ("1.818446459232066823483698963560708993786253942768121617451744", .gt)
#guard D (A third200 10 .Floor) == ("1.818", .lt)
#guard D (A (X "10" 53) 120) == ("0.0998340788992075633273031247047694433", .gt)
#guard D (A (X "1000000" 110) 53) == ("9.999999999998333e-7", .lt)
#guard D (A (X "1000000" 110) 53 .Floor) == ("9.999999999998333e-7", .lt)
#guard D (A (X "1000000" 110) 53 .Ceiling) == ("9.999999999998335e-7", .gt)
#guard D (A (X "-123456789012345678901234567890" 110) 53) == ("-8.1000000729e-30", .gt)
#guard D (A (X "-123456789012345678901234567890" 110) 53 .Floor) == ("-8.100000072900002e-30", .lt)
#guard D (A (X "-123456789012345678901234567890" 110) 53 .Ceiling) == ("-8.1000000729e-30", .gt)
#guard D (A (X "1267650600228229401496703205376" 110) 53) == ("7.888609052210118e-31", .gt)
#guard D (A (X "1267650600228229401496703205376" 110) 53 .Floor) == ("7.888609052210117e-31", .lt)
#guard D (A (X "1267650600228229401496703205376" 110) 53 .Ceiling) == ("7.888609052210118e-31", .gt)
#guard D (A (X "3802951800684688204490109616128" 110) 53) == ("2.629536350736706e-31", .lt)
#guard D (A (X "3802951800684688204490109616128" 110) 53 .Floor) == ("2.629536350736706e-31", .lt)
#guard D (A (X "3802951800684688204490109616128" 110) 53 .Ceiling) ==
  ("2.6295363507367063e-31", .gt)
#guard D (A (X "1125899906842624" 110) 53) == ("8.881784197001252e-16", .gt)
#guard D (A (X "1125899906842624" 110) 53 .Floor) == ("8.881784197001251e-16", .lt)
#guard D (A (X "1125899906842624" 110) 53 .Ceiling) == ("8.881784197001252e-16", .gt)
#guard D (A (X "-35184372088832" 110) 53) == ("-2.842170943040401e-14", .lt)
#guard D (A (X "-35184372088832" 110) 53 .Floor) == ("-2.842170943040401e-14", .lt)
#guard D (A (X "-35184372088832" 110) 53 .Ceiling) == ("-2.8421709430404004e-14", .gt)
#guard acsch (X "1.5" 53) == (A (X "1.5" 53) 53).1
#guard toString (acschPrecRound (X "1" 200) 200 .Nearest).1 == "0.881373587019543025232609324979792\
  309028160328261635410753296"
#guard toString (acschPrecRound (X "-1.5" 200) 200 .Nearest).1 == "-0.62514511725041668763425167322\
  61024070341843889531710193515776"

-- oddness: `f(−x, m) = −f(x, −m)`
private def odd (x : AzFloat) (p : Nat) (m : RoundingMode) : Bool :=
  let r := A x p (-m)
  A (-x) p m == (-r.1, r.2.swap)
#guard odd (X "1.5" 53) 53 .Nearest && odd (X "1.5" 53) 53 .Floor
#guard odd (X "100" 53) 20 .Ceiling && odd (X "0.001" 53) 113 .Floor
#guard odd (h (X "1" 53) (-1000)) 53 .Ceiling && odd (h (X "1" 53) 1000) 53 .Ceiling

-- huge arguments: just inside `1/x`
private def hugeOk (k : Int) : Bool :=
  let x := h (X "1" 53) k
  let y := h (X "1" 53) (-k)
  A x 53 == (y, .gt) && A x 53 .Ceiling == (y, .gt) && A x 53 .Floor == (h dn (-k), .lt)
    && A (-x) 53 == (-y, .lt) && A (-x) 53 .Floor == (-y, .lt)
    && A (-x) 53 .Ceiling == (-(h dn (-k)), .gt)
#guard hugeOk 60
#guard hugeOk 100
#guard hugeOk 1000
#guard hugeOk 1073741824
private def big3 : AzFloat := h (X "3" 53) 1073741824
#guard A big3 53 == (h (X "0.3333333333333333" 53) (-1073741824), .lt)
#guard A big3 53 .Ceiling
  == (h (X "0.33333333333333337" 53) (-1073741824), .gt)
#guard A (-big3) 53 .Floor
  == (-(h (X "0.33333333333333337" 53) (-1073741824)), .lt)

-- tiny arguments: `acsch x` rounds like `ln (2/x)`
#guard A (h (X "1" 53) (-1073741824)) 53 == lnPrecRound (h (X "1" 53) 1073741825) 53 .Nearest
#guard A (h (X "1" 53) (-100000)) 113 .Floor == lnPrecRound (h (X "1" 53) 100001) 113 .Floor
