/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Beta
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString

/-!
# Tests for the Beta function

The special values (`NaN`, the infinities, `B(0, b) = +∞`, negative integers, `p = 0`),
positive arguments (`B(1/2, 1/2) = π` in the five modes, `B(2, 3) = 1/12`,
`B(3/2, 5/2) = π/16`, `B(1/4, 3/4) = π√2`, `B(10, 10) = 9!²/19!`, large and tiny arguments),
the exact divisions `B(a, 1) = 1/a`, the rational values `B(a, n)` for a small integer `n`
(`B(−1/2, 2) = −4` exactly; `n = 64` and `65` on either side of the bound of the exact path),
the exact zeros where `a + b` is a non-positive integer,
negative arguments through the reflection formula (`B(−3/2, 5/2) = π`), other precisions, 200-
and 1000-bit values, and the symmetry `B(a, b) = B(b, a)`.
-/

open Azurite Azurite.AzFloat

/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def B (a b : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  betaPrecRound (X a 53) (X b 53) p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (betaPrecRound nan (X "1" 53) 53 .Nearest) == ("NaN", .eq)
#guard D (betaPrecRound (X "1" 53) nan 53 .Nearest) == ("NaN", .eq)
#guard D (betaPrecRound (infinity true) (X "2" 53) 53 .Nearest) == ("0.0", .eq)
#guard D (betaPrecRound (X "0.5" 53) (infinity true) 53 .Nearest) == ("0.0", .eq)
#guard D (betaPrecRound (infinity true) (infinity true) 53 .Nearest) == ("0.0", .eq)
#guard D (betaPrecRound (infinity true) (X "-2.5" 53) 53 .Nearest) == ("NaN", .eq)
#guard D (betaPrecRound (infinity true) zero 53 .Nearest) == ("NaN", .eq)
#guard D (betaPrecRound (infinity false) (X "2" 53) 53 .Nearest) == ("NaN", .eq)
#guard D (betaPrecRound (X "2" 53) (infinity false) 53 .Nearest) == ("NaN", .eq)
#guard D (betaPrecRound (infinity true) (infinity false) 53 .Nearest) == ("NaN", .eq)
#guard D (B "0" "0.5" 53) == ("Infinity", .eq)
#guard D (B "0.5" "0" 53) == ("Infinity", .eq)
#guard D (B "0" "0" 53) == ("Infinity", .eq)
#guard D (B "0" "-0.5" 53) == ("Infinity", .eq)
#guard D (B "0" "0.5" 0) == ("Infinity", .eq)
#guard D (B "0" "-2" 53) == ("NaN", .eq)
#guard D (B "-1" "0.5" 53) == ("NaN", .eq)
#guard D (B "0.5" "-3" 53) == ("NaN", .eq)
#guard D (B "-1" "-2" 53) == ("NaN", .eq)
#guard D (B "-2" "1" 53) == ("NaN", .eq)
#guard D (B "0.5" "0.5" 0) == ("NaN", .eq)

-- positive arguments
#guard D (B "0.5" "0.5" 53) == ("3.141592653589793", .lt)
#guard D (B "0.5" "0.5" 53 .Floor) == ("3.141592653589793", .lt)
#guard D (B "0.5" "0.5" 53 .Ceiling) == ("3.1415926535897936", .gt)
#guard D (B "0.5" "0.5" 53 .Up) == ("3.1415926535897936", .gt)
#guard D (B "0.5" "0.5" 53 .Down) == ("3.141592653589793", .lt)
#guard D (B "2" "3" 53) == ("0.08333333333333333", .lt)
#guard D (B "2" "3" 53 .Ceiling) == ("0.08333333333333334", .gt)
#guard D (B "1.5" "2.5" 53) == ("0.19634954084936207", .lt)
#guard D (B "0.25" "0.75" 53) == ("4.442882938158366", .lt)
#guard D (B "3.5" "0.125" 53) == ("6.546806554546746", .gt)
#guard D (B "10" "10" 53) == ("1.0825088224469029e-6", .lt)
#guard D (B "100" "200" 53) == ("3.607285449794666e-84", .lt)
#guard D (B "100" "200" 53 .Floor) == ("3.607285449794666e-84", .lt)
#guard D (B "1e10" "0.5" 53) == ("0.000017724538509276716", .lt)
#guard D (B "1e-10" "3" 53) == ("9999999998.5", .gt)
#guard D (B "1e-10" "1e-10" 53) == ("2.0e10", .gt)
#guard D (B "1e-30" "0.5" 53) == ("9.999999999999999e29", .lt)

-- `B(a, 1) = 1/a`, `B(1, b) = 1/b`: exact divisions
#guard D (B "2.5" "1" 53) == ("0.4", .gt)
#guard D (B "2.5" "1" 53 .Floor) == ("0.39999999999999997", .lt)
#guard D (B "1" "0.25" 53) == ("4.0", .eq)
#guard D (B "1" "3" 53 .Ceiling) == ("0.33333333333333337", .gt)
#guard D (B "-0.5" "1" 53) == ("-2.0", .eq)
#guard D (B "1" "1" 53) == ("1.0", .eq)

-- `B(a, n)` for a small positive integer `n`: the rational `(n − 1)!/(a (a+1) ⋯ (a+n−1))`
#guard D (B "-0.5" "2" 53) == ("-4.0", .eq)
#guard D (B "0.5" "2" 53) == ("1.3333333333333333", .lt)
#guard D (B "0.5" "2" 53 .Floor) == ("1.3333333333333333", .lt)
#guard D (B "3" "0.5" 53) == ("1.0666666666666667", .lt)
#guard D (B "4" "4" 53) == ("0.007142857142857143", .lt)
#guard D (B "0.25" "2" 53 .Ceiling) == ("3.2", .gt)
#guard D (B "-2.5" "2" 53) == ("0.26666666666666666", .lt)
#guard D (B "-2.5" "64" 53) == ("-28897.532343278588", .lt)
#guard D (B "0.75" "64" 53) == ("0.05423556332562687", .gt)
#guard D (B "0.75" "65" 53) == ("0.05360735216741498", .gt)
#guard D (B "1e-30" "2" 53) == ("9.999999999999999e29", .lt)
#guard D (B "0.5" "3" 200)
  == ("1.066666666666666666666666666666666666666666666666666666666667", .gt)
#guard D (B "40" "50" 53) == ("7.516171211855382e-28", .lt)

-- `a + b` a non-positive integer: `B = 0` exactly
#guard D (B "0.5" "-0.5" 53) == ("0.0", .eq)
#guard D (B "-0.5" "-0.5" 53) == ("0.0", .eq)
#guard D (B "-1.5" "0.5" 53) == ("0.0", .eq)
#guard D (B "-2.25" "1.25" 53) == ("0.0", .eq)
#guard D (B "-2.5" "-0.5" 53) == ("0.0", .eq)
#guard D (B "0.5" "-1.5" 53) == ("0.0", .eq)
#guard D (B "0.5" "-0.5" 0) == ("NaN", .eq)
private def tinyA : AzFloat := (X "3" 53) <<< AzInt.ofInt (-(2 ^ 30))
#guard D (betaPrecRound tinyA (-tinyA) 53 .Nearest) == ("0.0", .eq)

-- negative arguments
#guard D (B "-0.3" "-0.4" 53) == ("-3.769309024532314", .lt)
#guard D (B "-0.3" "-0.4" 53 .Floor) == ("-3.769309024532314", .lt)
#guard D (B "-1.5" "0.25" 53) == ("2.1850479619101", .gt)
#guard D (B "-2.5" "3.75" 53) == ("-4.61283990373203", .gt)
#guard D (B "-1.5" "2.5" 53) == ("3.141592653589793", .lt)
#guard D (B "-0.75" "-0.75" 53) == ("9.88839827894065", .gt)
#guard D (B "-100.5" "0.25" 53) == ("0.8089464500302618", .lt)
#guard D (B "-0.999" "0.5" 53) == ("500.19161145071797", .lt)
#guard D (B "0.3" "-1.2999" 53) == ("-0.0009959429753572805", .lt)

-- other precisions
#guard D (B "0.5" "0.5" 1) == ("4.0", .gt)
#guard D (B "0.5" "0.5" 2) == ("3.0", .lt)
#guard D (B "0.5" "0.5" 20) == ("3.141594", .gt)
#guard D (B "-0.3" "-0.4" 24) == ("-3.769309", .lt)
#guard D (B "0.5" "0.5" 200)
  == ("3.141592653589793238462643383279502884197169399375105820974944", .lt)
#guard D (B "1.5" "2.5" 200 .Floor)
  == ("0.196349540849362077403915211454968930262323087460944113810934", .lt)
#guard D (B "-0.3" "-0.4" 200)
  == ("-3.769309024532314046958633727459700285710995815431801293830371", .gt)
#guard D (B "100" "200" 200)
  == ("3.607285449794666051516045441164841677759351642986769415643664e-84", .gt)
#guard D (B "0.25" "0.75" 1000) == ("4.44288293815836624701588099006069369861462168937569022308539\
  560695643479309947391057532693476476523736341021268522879136435959851834562749237534635967441502\
    3279278819755877533113453661101306522127653019477442548721075410317108452709481602849783931074\
    445101869334937037691250236766286896527845907233829", .lt)

-- symmetry
#guard B "0.3" "2.75" 53 == B "2.75" "0.3" 53
#guard B "-0.3" "-0.4" 100 .Floor == B "-0.4" "-0.3" 100 .Floor
#guard B "-2.5" "3.75" 53 .Ceiling == B "3.75" "-2.5" 53 .Ceiling

-- `beta`
#guard toString (beta (X "0.5" 53) (X "0.5" 53)) == "3.141592653589793"
#guard toString (beta (X "0.5" 24) (X "0.5" 53)) == "3.141592653589793"

-- the fuel as an argument; no fuel is needed where the value is known to be irrational
-- (`a + b` a positive integer, or quarter-integers)
#guard D (betaPrecRoundFuel 0 (X "0.25" 53) (X "0.75" 53) 53 .Nearest)
  == ("4.442882938158366", .lt)
#guard D (betaPrecRoundFuel 0 (X "0.25" 53) (X "0.25" 53) 53 .Nearest)
  == ("7.4162987092054875", .lt)
#guard D (betaPrecRoundFuel 0 (X "0.125" 53) (X "2.875" 53) 53 .Nearest)
  == ("6.734254753911765", .lt)
#guard D (betaPrecRoundFuel 0 (X "-0.75" 53) (X "0.5" 53) 53 .Nearest)
  == ("1.74803836952808", .gt)
#guard D (betaPrecRoundFuel 3 (X "0.3" 53) (X "0.7" 53) 53 .Nearest)
  == ("3.883222077450933", .lt)
#guard betaPrecRoundFuel (gammaFuel 53) (X "0.3" 53) (X "2.75" 53) 53 .Nearest
  == B "0.3" "2.75" 53

-- a huge negative sum: the integer next to it is found at enough bits
#guard D (betaPrecRound (X "-1180591620717411303424.5" 100) (X "-31.25" 53) 20 .Nearest)
  == ("-5.13135e624", .gt)
#guard D (betaPrecRound (X "-1180591620717411303424.5" 100) (X "-32.25" 53) 20 .Nearest)
  == ("-1.878458e644", .gt)
