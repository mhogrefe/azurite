/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Acoth
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `acoth x`

The special values (`NaN`; `±∞ ↦ 0`; `acoth (±1) = ±∞`; `NaN` for `|x| < 1`, including `0`;
`p = 0`), the correctly rounded 53-bit values from `1 + 2^(−52)` to `3·2^100` of both signs in
three modes — across the switch to the huge-argument enclosure — 1-, 2-, 20-, 113-, 120- and
200-bit results, 200-bit strings, oddness, and huge arguments `±2^1000`, `±2^(2^30)`,
`±3·2^(2^30)` (the value is just outside `1/x`, at no cost).  References: an independent
6000-bit fixed-point evaluation of `(1/2) ln ((x + 1)/(x − 1))` rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
/-- `-1.333333333…` at 200 bits. -/
private def negFourThirds200 : AzFloat :=
  X "-1.333333333333333333333333333333333333333333333333333333333334" 200
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
private def up : AzFloat := X "1.0000000000000002" 53
private def A (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := acothPrecRound x p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (A nan 53) == ("NaN", .eq)
#guard D (A (infinity true) 53) == ("0.0", .eq)
#guard D (A (infinity false) 53) == ("0.0", .eq)
#guard D (A (infinity false) 0) == ("0.0", .eq)
#guard D (A (X "1" 53) 53) == ("Infinity", .eq)
#guard D (A (X "-1" 200) 53) == ("-Infinity", .eq)
#guard D (A (X "1" 53) 0) == ("Infinity", .eq)
#guard D (A zero 53) == ("NaN", .eq)
#guard D (A (X "0.5" 53) 53) == ("NaN", .eq)
#guard D (A (X "-0.75" 53) 53) == ("NaN", .eq)
#guard D (A (X "0.9999999999999999" 53) 53) == ("NaN", .eq)
#guard D (A (h (X "-1" 53) (-1000)) 53) == ("NaN", .eq)
#guard D (A (X "2" 53) 0) == ("NaN", .eq)

-- correctly rounded values
#guard D (A (X "2" 53) 53) == ("0.5493061443340549", .gt)
#guard D (A (X "-2" 53) 53) == ("-0.5493061443340549", .lt)
#guard D (A (X "3" 53) 53) == ("0.34657359027997264", .lt)
#guard D (A (X "-3.5" 53) 53) == ("-0.29389333245105953", .lt)
#guard D (A (X "1.3333333333333333" 53) 53) == ("0.9729550745276567", .lt)
#guard D (A (X "1.01" 53) 53) == ("2.6516524540295374", .lt)
#guard D (A (X "-1.000001" 53) 53) == ("-7.254329119303181", .lt)
#guard D (A (X "1.0000000000000002" 53) 53) == ("18.36840028483855", .lt)
#guard D (A (X "-1.0000000000000002" 53) 53) == ("-18.36840028483855", .gt)
#guard D (A (X "1000" 53) 53) == ("0.0010000003333335333", .lt)
#guard D (A (X "-1000000000000" 53) 53) == ("-1.0e-12", .gt)
#guard D (A (X "1125899906842624" 53) 53) == ("8.881784197001252e-16", .lt)
#guard D (A (X "35184372088832" 53) 53) == ("2.842170943040401e-14", .lt)
#guard D (A (X "3377699720527872" 53) 53) == ("2.9605947323337506e-16", .lt)
#guard D (A (X "1267650600228229401496703205376" 53) 53) == ("7.888609052210118e-31", .lt)
#guard D (A (X "-3802951800684688204490109616128" 53) 53) == ("-2.629536350736706e-31", .gt)
#guard D (A (X "2" 53) 53 .Floor) == ("0.5493061443340548", .lt)
#guard D (A (X "-2" 53) 53 .Floor) == ("-0.5493061443340549", .lt)
#guard D (A (X "1.01" 53) 53 .Floor) == ("2.6516524540295374", .lt)
#guard D (A (X "1.0000000000000002" 53) 53 .Floor) == ("18.36840028483855", .lt)
#guard D (A (X "1000" 53) 53 .Floor) == ("0.0010000003333335333", .lt)
#guard D (A (X "35184372088832" 53) 53 .Floor) == ("2.842170943040401e-14", .lt)
#guard D (A (X "1125899906842624" 53) 53 .Floor) == ("8.881784197001252e-16", .lt)
#guard D (A (X "-3802951800684688204490109616128" 53) 53 .Floor) == ("-2.6295363507367063e-31", .lt)
#guard D (A (X "2" 53) 53 .Ceiling) == ("0.5493061443340549", .gt)
#guard D (A (X "-2" 53) 53 .Ceiling) == ("-0.5493061443340548", .gt)
#guard D (A (X "1.01" 53) 53 .Ceiling) == ("2.651652454029538", .gt)
#guard D (A (X "1.0000000000000002" 53) 53 .Ceiling) == ("18.368400284838554", .gt)
#guard D (A (X "1000" 53) 53 .Ceiling) == ("0.0010000003333335335", .gt)
#guard D (A (X "35184372088832" 53) 53 .Ceiling) == ("2.8421709430404014e-14", .gt)
#guard D (A (X "1125899906842624" 53) 53 .Ceiling) == ("8.881784197001254e-16", .gt)
#guard D (A (X "-3802951800684688204490109616128" 53) 53 .Ceiling) ==
  ("-2.629536350736706e-31", .gt)
#guard D (A (X "2" 53) 20) == ("0.549306", .lt)
#guard D (A (X "2" 53) 1) == ("0.5", .lt)
#guard D (A (X "-1.3333333333333333" 53) 2) == ("-1.0", .lt)
#guard D (A (X "1.3333333333333333" 53) 113) == ("0.972955074527656747714649911020734", .lt)
#guard D (A (X "3" 200) 200) ==
  ("0.34657359027997265470861606072908828403775006718012762706034", .lt)
#guard D (A (X "3" 200) 10 .Floor) == ("0.346", .lt)
#guard D (A (X "1.1428571428571428" 53) 120) == ("1.354025100551105240239633548436959968", .lt)
#guard acoth (X "1.5" 53) == (A (X "1.5" 53) 53).1
#guard toString (acothPrecRound (X "2" 200) 200 .Nearest).1 == "0.549306144334054845697622618461262\
  852323745278911374725867347"
#guard toString (acothPrecRound negFourThirds200 200 .Nearest).1 == "-0.972955074527656652552676371\
  7215898648185423647909305942296943"

-- oddness: `f(−x, m) = −f(x, −m)`
private def odd (x : AzFloat) (p : Nat) (m : RoundingMode) : Bool :=
  let r := A x p (-m)
  A (-x) p m == (-r.1, r.2.swap)
#guard odd (X "1.5" 53) 53 .Nearest && odd (X "1.5" 53) 53 .Floor
#guard odd (X "100" 53) 20 .Ceiling && odd (X "1.001" 53) 113 .Floor
#guard odd (h (X "1" 53) 1000) 53 .Ceiling && odd (h (X "3" 53) 1073741824) 53 .Floor

-- huge arguments: just outside `1/x`
private def hugeOk (k : Int) : Bool :=
  let x := h (X "1" 53) k
  let y := h (X "1" 53) (-k)
  A x 53 == (y, .lt) && A x 53 .Floor == (y, .lt) && A x 53 .Ceiling == (h up (-k), .gt)
    && A (-x) 53 == (-y, .gt) && A (-x) 53 .Ceiling == (-y, .gt)
    && A (-x) 53 .Floor == (-(h up (-k)), .lt)
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
