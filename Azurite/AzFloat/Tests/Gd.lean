/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Gd
import Azurite.AzFloat.ToString
import Azurite.AzFloat.OfString
import Azurite.AzRat.Parse

/-!
# Tests for the Gudermannian `gd x`

The special values (`NaN`, `±∞ ↦ ±π/2`, `0`, `p = 0`); the correctly rounded 53-bit values on
every path — the alternating series for a small argument (`1/1024`, `3/8`), the general path
(`3/4`, `1`, `5/4`), the alternating series of `e^(−x)` (`2`, `7/2`, `20`, `45`) and the huge
path (`200`, `100000`, `2^(2^30)`), where the value is `π/2` rounded with the comparison of a
number just below it; 200-, 300- and 1000-bit results; directed rounding; oddness; tiny
arguments (`±2^(−1000)`, `±2^(−2^30)`: the value is just inside `x`, at no cost); and the
agreement of the three paths of the bracket.  References: a 400-digit evaluation of
`2 arctan ((e^x − 1)/(e^x + 1))` (argument halving and the series) rounded with exact
rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
private def A (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := gdPrecRound x p m

-- special values
#guard D (A nan 53) == ("NaN", .eq)
#guard A (infinity true) 53 == piDiv2PrecRound 53 .Nearest
#guard A (infinity true) 53 .Floor == piDiv2PrecRound 53 .Floor
#guard (A (infinity false) 53 .Floor).1 == -(piDiv2PrecRound 53 .Ceiling).1
#guard (A (infinity false) 53 .Floor).2 == .lt
#guard D (A (infinity true) 0) == ("NaN", .eq)
#guard D (A zero 53) == ("0.0", .eq)
#guard D (A zero 0) == ("0.0", .eq)
#guard D (A (X "1" 53) 0) == ("NaN", .eq)

-- correctly rounded 53-bit values on every path
#guard D (A (X "0.0009765625" 53) 53) == ("0.0009765623447796079", .gt)
#guard D (A (X "0.375" 53) 53) == ("0.3665078410841438", .lt)
#guard D (A (X "0.75" 53) 53) == ("0.6882013509140213", .lt)
#guard D (A (X "1" 53) 53) == ("0.8657694832396586", .gt)
#guard D (A (X "1.25" 53) 53) == ("1.0127356143501303", .lt)
#guard D (A (X "-2" 53) 53) == ("-1.301760336046015", .gt)
#guard D (A (X "3.5" 53) 53) == ("1.5104199075457003", .gt)
#guard D (A (X "20" 53) 53) == ("1.5707963226725894", .gt)
#guard D (A (X "45" 53) 53) == ("1.5707963267948966", .lt)
#guard D (A (X "200" 53) 53) == ("1.5707963267948966", .lt)
#guard D (A (X "100000" 53) 53) == ("1.5707963267948966", .lt)

-- a huge argument: `π/2` rounded, with the comparison of a number just below `π/2`
private def huge : AzFloat := h (X "3" 53) (2 ^ 30)
#guard (A huge 53).1 == (piDiv2PrecRound 53 .Nearest).1
#guard (A huge 53 .Floor) == piDiv2PrecRound 53 .Floor
#guard (A huge 53 .Ceiling) == piDiv2PrecRound 53 .Ceiling
#guard (A (-huge) 53 .Ceiling).1 == -(piDiv2PrecRound 53 .Floor).1

-- directed rounding and oddness
#guard D (A (X "1" 53) 53 .Floor) == ("0.8657694832396585", .lt)
#guard D (A (X "1" 53) 53 .Ceiling) == ("0.8657694832396586", .gt)
#guard D (A (X "-0.75" 53) 53) == ("-0.6882013509140213", .gt)
#guard (A (X "-1" 53) 53 .Floor).1 == -(A (X "1" 53) 53 .Ceiling).1

-- other precisions
#guard D (A (X "1" 53) 200)
  == ("0.8657694832396586242896018461918444413796791992487600996118485", .gt)
#guard D (A (X "30" 53) 300)
  == ("1.570796326794709466771944888147653125454663393060919778395717652423602027940801327114648292\
  ", .lt)
#guard D (A (X "0.015625" 53) 300)
  == ("0.015624364255924751377535849394056700481621354788103466320193138194562693671816761111290758\
  75", .lt)
#guard D (A (X "0.75" 53) 1000)
  == ("0.688201350914021377304730291927588999244863232628271289908330258589690720569064135455916498\
  1558752238686312394994517283623222528492013501905411090517831033203777717978372948036981092864565\
  0272247084261125922446463696733136084022330874689899151239852450695895498893886690918525812824240\
  02929348637411843", .gt)
#guard toString (gd (X "1" 200))
  == "0.8657694832396586242896018461918444413796791992487600996118485"
#guard (A (X "1" 53) 1).1 == X "1" 1 && (A (X "1" 53) 2).1 == X "0.75" 2

-- tiny arguments: the value is just inside `x`
#guard D (A (h (X "1" 53) (-1000)) 53) == ("9.332636185032189e-302", .gt)
#guard D (A (h (X "-1" 53) (-1000)) 53) == ("-9.332636185032189e-302", .lt)
#guard A (h (X "1" 53) (-(2 ^ 30))) 53 .Floor
  == (h (X "0.9999999999999999" 53) (-(2 ^ 30)), .lt)

-- the paths of the bracket agree
private def overlap (a b : Encl) : Bool := le a.1 b.2 && le b.1 a.2
private def x3 : AzFloat := X "3" 53
private def e3 : AzInt := AzInt.ofInt 2
#guard (gdLargeSeries? x3 e3 117).isSome
#guard ((gdLargeSeries? x3 e3 117).map (overlap (gdCore x3 e3 117))) == some true
#guard (gdLargeSeries? x3 e3 1000).isNone
private def xs : AzFloat := X "0.375" 53
private def es : AzInt := AzInt.ofInt (-1)
#guard ((gdSmallSeries? xs es 117).map (overlap (gdCore xs es 117))) == some true
#guard (gdSmallSeries? (X "0.75" 53) (AzInt.ofInt 0) 117).isNone
#guard overlap (gdHuge 128 117) (gdCore (X "200" 53) (AzInt.ofInt 8) 117)
#guard (enclNarrow? (X "1" 8, X "1.25" 8) 2).isSome && (enclNarrow? (X "1" 8, X "1.25" 8) 3).isNone
