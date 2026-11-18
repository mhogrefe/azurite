/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Atan2RatWithPeriod
import Azurite.AzFloat.AtanRatWithPeriod
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse
import Azurite.AzFloat.OfString

/-!
# Tests for `atan2 (y, x) u / (2π)` of rationals

The special values in degrees (`y = 0`; `x = 0`; the diagonals `|y| = |x|`, also for unreduced
inputs; `u = 0`; `p = 0`) with roundings of the rational values that do not fit; the correctly
rounded 53-bit values in all eight octants and at rationals that are not floats; other periods
(`1`, `7`, `400`, `2^64 − 1`); agreement with the float function at representable arguments
and with `atanRatWithPeriod` for `x = 1`; homogeneity; the directed modes; 1-, 20- and 113-bit
results; a 200-bit string; and extreme ratios (`2^(±5000)`) next to `0`, a quarter and a half
turn in every octant.  References: an independent 1400-bit fixed-point evaluation rounded with
exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def E (y x : String) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  atan2RatWithPeriodPrecRound (Q y) (Q x) u p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (E "0" "0" 360 53) == ("0.0", .eq)
#guard D (E "0" "3/7" 360 53) == ("0.0", .eq)
#guard D (E "0" "-3/7" 360 53) == ("1.8e2", .eq)
#guard D (E "2/3" "0" 360 53) == ("9.0e1", .eq)
#guard D (E "-2/3" "0" 360 53) == ("-9.0e1", .eq)
#guard D (E "3/7" "3/7" 360 53) == ("45.0", .eq)
#guard D (E "-3/7" "3/7" 360 53) == ("-45.0", .eq)
#guard D (E "3/7" "-3/7" 360 53) == ("135.0", .eq)
#guard D (E "-3/7" "-3/7" 360 53) == ("-135.0", .eq)
#guard D (E "6/14" "-9/21" 360 2) == ("1.3e2", .lt)
#guard D (E "3/7" "-3/7" 7 2) == ("3.0", .gt)
#guard D (E "3/7" "-3/7" 1 53) == ("0.375", .eq)
#guard D (E "1/3" "7/5" 0 53) == ("0.0", .eq)
#guard D (E "0" "-3/7" 0 53) == ("0.0", .eq)
#guard D (E "3/7" "-3/7" 0 53) == ("0.0", .eq)
#guard D (E "1/3" "7/5" 360 0) == ("NaN", .eq)

-- correctly rounded values
#guard D (E "1" "3" 360 53) == ("18.43494882292201", .lt)
#guard D (E "3" "1" 360 53) == ("71.56505117707799", .gt)
#guard D (E "1" "-3" 360 53) == ("161.56505117707798", .lt)
#guard D (E "3" "-1" 360 53) == ("108.43494882292201", .lt)
#guard D (E "-1" "3" 360 53) == ("-18.43494882292201", .gt)
#guard D (E "-3" "1" 360 53) == ("-71.56505117707799", .lt)
#guard D (E "-1" "-3" 360 53) == ("-161.56505117707798", .gt)
#guard D (E "-3" "-1" 360 53) == ("-108.43494882292201", .gt)
#guard D (E "1/3" "7/5" 360 53) == ("13.392497753751098", .lt)
#guard D (E "-7/5" "1/3" 360 53) == ("-76.6075022462489", .gt)
#guard D (E "22/7" "-1/1000" 360 53) == ("90.0182304746844", .lt)
#guard D (E "1/1000" "-22/7" 360 53) == ("179.9817695253156", .gt)
#guard D (E "355/113" "1000000007/3" 360 53) == ("5.400000420733862e-7", .lt)
#guard D (E "1" "3" 1 53) == ("0.05120819117478336", .lt)
#guard D (E "1" "-3" 400 53) == ("179.51672353008667", .gt)
#guard D (E "-3" "1" 7 53) == ("-1.3915426617765165", .lt)
#guard D (E "3" "-1" 18446744073709551615 53) == ("5.556310415506209e18", .gt)
#guard D (E "1" "3" 360 53 .Floor) == ("18.43494882292201", .lt)
#guard D (E "-3" "-1" 360 53 .Floor) == ("-108.43494882292202", .lt)
#guard D (E "1" "3" 360 53 .Ceiling) == ("18.434948822922014", .gt)
#guard D (E "-3" "-1" 360 53 .Ceiling) == ("-108.43494882292201", .gt)
#guard D (E "1" "3" 360 20) == ("18.43494", .lt)
#guard D (E "1" "-3" 360 1) == ("1.0e2", .lt)
#guard D (E "-3" "1" 360 113) == ("-71.5650511770779893515721937204533", .lt)

-- agreement with the float function, with `atanRatWithPeriod`, and homogeneity
#guard E "1/2" "-3" 360 53
  == atan2WithPeriodPrecRound (X "0.5" 53) (X "-3" 53) 360 53 .Nearest
#guard E "1/3" "1" 360 53 == atanRatWithPeriodPrecRound (Q "1/3") 360 53 .Nearest
#guard E "-22/7" "1" 7 53 .Floor == atanRatWithPeriodPrecRound (Q "-22/7") 7 53 .Floor
#guard E "2/21" "-2/5" 360 53 == E "5" "-21" 360 53
#guard atan2RatWithPeriod (Q "1") (Q "3") 360 53 == (E "1" "3" 360 53).1
#guard toString (atan2RatWithPeriod (Q "1") (Q "-2") 360 200)
  == "153.434948822922010648427806279546705328795785700354778972014"

-- extreme ratios: next to `0`, a quarter turn and a half turn
private def pw (k : Nat) : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 1) <<< k)
private def one' : AzRat := Q "1"
private def R (y x : AzRat) (m : RoundingMode := .Nearest) :=
  atan2RatWithPeriodPrecRound y x 360 53 m
#guard toString (R (pw 5000) one').1 == "4.0564330500725343e-1504"
#guard (R (pw 5000) one').2 == .gt
#guard D (R one' (pw 5000)) == ("9.0e1", .gt)
#guard D (R one' (pw 5000) .Floor) == ("89.99999999999999", .lt)
#guard D (R (-one') (pw 5000)) == ("-9.0e1", .lt)
#guard D (R one' (-(pw 5000))) == ("9.0e1", .lt)
#guard D (R (-one') (-(pw 5000))) == ("-9.0e1", .gt)
#guard D (R (pw 5000) (-one')) == ("1.8e2", .gt)
#guard D (R (pw 5000) (-one') .Floor) == ("179.99999999999997", .lt)
#guard D (R (-(pw 5000)) (-one')) == ("-1.8e2", .lt)
-- the rational arctangent with a period at a huge argument
#guard D (atanRatWithPeriodPrecRound (pw 5000)⁻¹ 360 53 .Nearest) == ("9.0e1", .gt)
#guard D (atanRatWithPeriodPrecRound (-(pw 5000)⁻¹) 360 53 .Ceiling) == ("-89.99999999999999", .gt)
