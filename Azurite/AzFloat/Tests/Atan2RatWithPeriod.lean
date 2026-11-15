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
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def E (y x : String) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  atan2RatWithPeriodPrecRound (Q y) (Q x) u p m

-- special values
#guard E "0" "0" 360 53 == (zero, .eq)
#guard E "0" "3/7" 360 53 == (zero, .eq)
#guard E "0" "-3/7" 360 53 == (F "180" 53, .eq)
#guard E "2/3" "0" 360 53 == (F "90" 53, .eq)
#guard E "-2/3" "0" 360 53 == (F "-90" 53, .eq)
#guard E "3/7" "3/7" 360 53 == (F "45" 53, .eq)
#guard E "-3/7" "3/7" 360 53 == (F "-45" 53, .eq)
#guard E "3/7" "-3/7" 360 53 == (F "135" 53, .eq)
#guard E "-3/7" "-3/7" 360 53 == (F "-135" 53, .eq)
#guard E "6/14" "-9/21" 360 2 == (F "128" 2, .lt)
#guard E "3/7" "-3/7" 7 2 == (F "3" 2, .gt)
#guard E "3/7" "-3/7" 1 53 == (F "3/8" 53, .eq)
#guard E "1/3" "7/5" 0 53 == (zero, .eq)
#guard E "0" "-3/7" 0 53 == (zero, .eq)
#guard E "3/7" "-3/7" 0 53 == (zero, .eq)
#guard E "1/3" "7/5" 360 0 == (nan, .eq)

-- correctly rounded values
#guard E "1" "3" 360 53 == (F "1297244197648527/70368744177664" 53, .lt)
#guard E "3" "1" 360 53 == (F "5035942778341233/70368744177664" 53, .gt)
#guard E "1" "-3" 360 53 == (F "710570609645687/4398046511104" 53, .lt)
#guard E "3" "-1" 360 53 == (F "7630431173638287/70368744177664" 53, .lt)
#guard E "-1" "3" 360 53 == (F "-1297244197648527/70368744177664" 53, .gt)
#guard E "-3" "1" 360 53 == (F "-5035942778341233/70368744177664" 53, .lt)
#guard E "-1" "-3" 360 53 == (F "-710570609645687/4398046511104" 53, .gt)
#guard E "-3" "-1" 360 53 == (F "-7630431173638287/70368744177664" 53, .gt)
#guard E "1/3" "7/5" 360 53 == (F "3769652993334603/281474976710656" 53, .lt)
#guard E "-7/5" "1/3" 360 53 == (F "-5390773727656109/70368744177664" 53, .gt)
#guard E "22/7" "-1/1000" 360 53 == (F "791808728949883/8796093022208" 53, .lt)
#guard E "1/1000" "-22/7" 360 53 == (F "1583136387046277/8796093022208" 53, .gt)
#guard E "355/113" "1000000007/3" 360 53 == (F "2550078099435557/4722366482869645213696" 53, .lt)
#guard E "1" "3" 1 53 == (F "7379878102178287/144115188075855872" 53, .lt)
#guard E "1" "-3" 400 53 == (F "789522899606319/4398046511104" 53, .gt)
#guard E "-3" "1" 7 53 == (F "-1566737753261717/1125899906842624" 53, .lt)
#guard E "3" "-1" 18446744073709551615 53 == (F "5556310415506208768" 53, .gt)
#guard E "1" "3" 360 53 .Floor == (F "1297244197648527/70368744177664" 53, .lt)
#guard E "-3" "-1" 360 53 .Floor == (F "-476901948352393/4398046511104" 53, .lt)
#guard E "1" "3" 360 53 .Ceiling == (F "5188976790594109/281474976710656" 53, .gt)
#guard E "-3" "-1" 360 53 .Ceiling == (F "-7630431173638287/70368744177664" 53, .gt)
#guard E "1" "3" 360 20 == (F "151019/8192" 20, .lt)
#guard E "1" "-3" 360 1 == (F "128" 1, .lt)
#guard E "-3" "1" 360 113
  == (F "-5806046725119159567778531012198059/81129638414606681695789005144064" 113, .lt)

-- agreement with the float function, with `atanRatWithPeriod`, and homogeneity
#guard E "1/2" "-3" 360 53
  == atan2WithPeriodPrecRound (F "1/2" 53) (F "-3" 53) 360 53 .Nearest
#guard E "1/3" "1" 360 53 == atanRatWithPeriodPrecRound (Q "1/3") 360 53 .Nearest
#guard E "-22/7" "1" 7 53 .Floor == atanRatWithPeriodPrecRound (Q "-22/7") 7 53 .Floor
#guard E "2/21" "-2/5" 360 53 == E "5" "-21" 360 53
#guard atan2RatWithPeriod (Q "1") (Q "3") 360 53 == (E "1" "3" 360 53).1
#guard (toString (atan2RatWithPeriod (Q "1") (Q "-2") 360 200)).startsWith
  "153.4349488229220106484278062795467053287957857003547789"

-- extreme ratios: next to `0`, a quarter turn and a half turn
private def pw (k : Nat) : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 1) <<< k)
private def one' : AzRat := Q "1"
private def R (y x : AzRat) (m : RoundingMode := .Nearest) :=
  atan2RatWithPeriodPrecRound y x 360 53 m
#guard (R (pw 5000) one').1
  == (F "1007958012753983/17592186044416" 53) <<< AzInt.ofInt (-5000)
#guard (R (pw 5000) one').2 == .gt
#guard R one' (pw 5000) == (F "90" 53, .gt)
#guard R one' (pw 5000) .Floor == (F "6333186975989759/70368744177664" 53, .lt)
#guard R (-one') (pw 5000) == (F "-90" 53, .lt)
#guard R one' (-(pw 5000)) == (F "90" 53, .lt)
#guard R (-one') (-(pw 5000)) == (F "-90" 53, .gt)
#guard R (pw 5000) (-one') == (F "180" 53, .gt)
#guard R (pw 5000) (-one') .Floor == (F "6333186975989759/35184372088832" 53, .lt)
#guard R (-(pw 5000)) (-one') == (F "-180" 53, .lt)
-- the rational arctangent with a period at a huge argument
#guard atanRatWithPeriodPrecRound (pw 5000)⁻¹ 360 53 .Nearest == (F "90" 53, .gt)
#guard atanRatWithPeriodPrecRound (-(pw 5000)⁻¹) 360 53 .Ceiling
  == (F "-6333186975989759/70368744177664" 53, .gt)
