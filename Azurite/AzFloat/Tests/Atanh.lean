/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Atanh
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `atanh x`

The special values (`NaN`; `±∞ ↦ NaN`; `NaN` for `|x| > 1`; `atanh (±1) = ±∞`; `0`; `p = 0`),
the correctly rounded 53-bit values from `2^(−200)` to `1 − 2^(−53)` in three modes, 1-, 2-,
20-, 113-, 120- and 200-bit results, 200-bit strings, oddness, and tiny arguments
`±2^(−1000)`, `±2^(−2^30)` (the value is just outside `x`, at no cost).  References: an
independent 6000-bit fixed-point evaluation of `(1/2) ln ((1 + x)/(1 − x))` rounded with exact
rationals.
-/

open Azurite Azurite.AzFloat

/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
private def up : AzFloat := X "1.0000000000000002" 53
private def A (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := atanhPrecRound x p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (A nan 53) == ("NaN", .eq)
#guard D (A (infinity true) 53) == ("NaN", .eq)
#guard D (A (infinity false) 53) == ("NaN", .eq)
#guard D (A zero 53) == ("0.0", .eq)
#guard D (A zero 0) == ("0.0", .eq)
#guard D (A (X "1" 53) 53) == ("Infinity", .eq)
#guard D (A (X "-1" 200) 53) == ("-Infinity", .eq)
#guard D (A (X "1" 53) 0) == ("Infinity", .eq)
#guard D (A (X "2" 53) 53) == ("NaN", .eq)
#guard D (A (X "-1.5" 53) 53) == ("NaN", .eq)
#guard D (A (X "1.0000000000000002" 53) 53) == ("NaN", .eq)
#guard D (A (h (X "1" 53) 1000) 53) == ("NaN", .eq)
#guard D (A (X "0.5" 53) 0) == ("NaN", .eq)

-- correctly rounded values
#guard D (A (X "0.5" 53) 53) == ("0.5493061443340549", .gt)
#guard D (A (X "-0.5" 53) 53) == ("-0.5493061443340549", .lt)
#guard D (A (X "0.3333333333333333" 53) 53) == ("0.34657359027997264", .gt)
#guard D (A (X "-0.2857142857142857" 53) 53) == ("-0.2938933324510595", .gt)
#guard D (A (X "0.75" 53) 53) == ("0.9729550745276566", .lt)
#guard D (A (X "0.99" 53) 53) == ("2.6466524123622457", .lt)
#guard D (A (X "-0.999999" 53) 53) == ("-7.254328619247669", .gt)
#guard D (A (X "0.9999999999999999" 53) 53) == ("18.714973875118524", .gt)
#guard D (A (X "-0.9999999999999999" 53) 53) == ("-18.714973875118524", .lt)
#guard D (A (X "0.001" 53) 53) == ("0.0010000003333335333", .lt)
#guard D (A (X "-0.000000000001" 53) 53) == ("-1.0e-12", .gt)
#guard D (A (X "8.881784197001252e-16" 53) 53) == ("8.881784197001252e-16", .lt)
#guard D (A (X "7.888609052210118e-31" 53) 53) == ("7.888609052210118e-31", .lt)
#guard D (A (X "-1.8669045833583425e-60" 53) 53)
  == ("-1.8669045833583425e-60", .gt)
#guard D (A (X "0.5" 53) 53 .Floor) == ("0.5493061443340548", .lt)
#guard D (A (X "-0.5" 53) 53 .Floor) == ("-0.5493061443340549", .lt)
#guard D (A (X "0.99" 53) 53 .Floor) == ("2.6466524123622457", .lt)
#guard D (A (X "0.9999999999999999" 53) 53 .Floor) == ("18.71497387511852", .lt)
#guard D (A (X "0.001" 53) 53 .Floor) == ("0.0010000003333335333", .lt)
#guard D (A (X "7.888609052210118e-31" 53) 53 .Floor) == ("7.888609052210118e-31", .lt)
#guard D (A (X "0.5" 53) 53 .Ceiling) == ("0.5493061443340549", .gt)
#guard D (A (X "-0.5" 53) 53 .Ceiling) == ("-0.5493061443340548", .gt)
#guard D (A (X "0.99" 53) 53 .Ceiling) == ("2.646652412362246", .gt)
#guard D (A (X "0.9999999999999999" 53) 53 .Ceiling) == ("18.714973875118524", .gt)
#guard D (A (X "0.001" 53) 53 .Ceiling) == ("0.0010000003333335335", .gt)
#guard D (A (X "7.888609052210118e-31" 53) 53 .Ceiling) == ("7.88860905221012e-31", .gt)
#guard D (A (X "0.5" 53) 20) == ("0.549306", .lt)
#guard D (A (X "0.5" 53) 1) == ("0.5", .lt)
#guard D (A (X "-0.75" 53) 2) == ("-1.0", .lt)
#guard D (A (X "0.75" 53) 113) == ("0.9729550745276566525526763717215899", .gt)
#guard D (A (X "0.3333333333333333333333333333333333333333333333333333333333334" 200) 200) == ("0.3\
  4657359027997265470861606072908828403775006718012762706034\
  ", .lt)
#guard D (A (X "0.333333333333333333333333333333333333333333333333333333333333\
  4" 200) 10 .Floor) == ("0.346", .lt)
#guard D (A (X "0.875" 53) 120) == ("1.354025100551105032998002285074356673", .gt)
#guard atanh (X "0.5" 53) == (A (X "0.5" 53) 53).1
#guard toString (atanhPrecRound (X "0.5" 200) 200 .Nearest).1 == "0.5493061443340548456976226184612\
  62852323745278911374725867347"
#guard toString (atanhPrecRound (X "-0.75" 200) 200 .Nearest).1 ==
    "-0.97295507452765665255267637172\
  1589864818542364790930594229695"

-- oddness: `f(−x, m) = −f(x, −m)`
private def odd (x : AzFloat) (p : Nat) (m : RoundingMode) : Bool :=
  let r := A x p (-m)
  A (-x) p m == (-r.1, r.2.swap)
#guard odd (X "0.5" 53) 53 .Nearest && odd (X "0.5" 53) 53 .Floor
#guard odd (X "0.99" 53) 20 .Ceiling && odd (X "0.001" 53) 113 .Floor
#guard odd (h (X "1" 53) (-1000)) 53 .Ceiling

-- tiny arguments: just outside `x`
private def tinyOk (k : Int) : Bool :=
  let x := h (X "1" 53) (-k)
  A x 53 == (x, .lt) && A x 53 .Floor == (x, .lt) && A x 53 .Ceiling == (h up (-k), .gt)
    && A (-x) 53 == (-x, .gt) && A (-x) 53 .Ceiling == (-x, .gt)
    && A (-x) 53 .Floor == (-(h up (-k)), .lt)
#guard tinyOk 200
#guard tinyOk 1000
#guard tinyOk 1073741824
