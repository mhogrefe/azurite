/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Atan2WithPeriod
import Azurite.AzFloat.AtanWithPeriod
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `atan2 (y, x) u / (2π)`

The whole table of special values in degrees (`NaN`; `±45`, `±135`, `±90` for `y = ±∞`; `0` and
`±180` for `x = ±∞`; `y = 0`; `x = 0`; the diagonals `|y| = |x|`, also at unequal precisions;
`u = 0`; `p = 0`), with roundings of the rational values that do not fit; the correctly rounded
53-bit values in all eight octants, at inexact and very unequal arguments; other periods (`1`,
`7`, `400`, `2^64 − 1`); agreement with `atanWithPeriod` for `x = 1`; the directed modes; 1-,
20- and 113-bit results; a 200-bit string; and extreme ratios (`2⁻²⁰⁰`, `2^(±2^30)`).
References: an independent 1400-bit fixed-point evaluation rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def D (y x : AzFloat) (u : UInt64) (p : Nat) (m : RoundingMode := .Nearest) :=
  atan2WithPeriodPrecRound y x u p m
private def inf : AzFloat := infinity true
private def ninf : AzFloat := infinity false
private def one' : AzFloat := F "1" 53

-- `NaN`
#guard D nan one' 360 53 == (nan, .eq)
#guard D one' nan 360 53 == (nan, .eq)
#guard D inf nan 360 53 == (nan, .eq)
#guard D nan zero 0 53 == (nan, .eq)
-- `y = ±∞`
#guard D inf inf 360 53 == (F "45" 53, .eq)
#guard D ninf inf 360 53 == (F "-45" 53, .eq)
#guard D inf ninf 360 53 == (F "135" 53, .eq)
#guard D ninf ninf 360 53 == (F "-135" 53, .eq)
#guard D inf (F "5" 53) 360 53 == (F "90" 53, .eq)
#guard D ninf zero 360 53 == (F "-90" 53, .eq)
#guard D inf ninf 7 2 == (F "3" 2, .gt)
#guard D ninf ninf 7 2 .Ceiling == (F "-2" 2, .gt)
#guard D inf ninf 1 53 == (F "3/8" 53, .eq)
-- `x = ±∞`, finite `y`
#guard D (F "5" 53) inf 360 53 == (zero, .eq)
#guard D (F "-5" 53) inf 360 53 == (zero, .eq)
#guard D zero inf 360 53 == (zero, .eq)
#guard D (F "5" 53) ninf 360 53 == (F "180" 53, .eq)
#guard D (F "-5" 53) ninf 360 53 == (F "-180" 53, .eq)
#guard D zero ninf 360 53 == (F "180" 53, .eq)
-- `y = 0`, `x = 0`
#guard D zero zero 360 53 == (zero, .eq)
#guard D zero (F "3" 53) 360 53 == (zero, .eq)
#guard D zero (F "-3" 53) 360 53 == (F "180" 53, .eq)
#guard D (F "2" 53) zero 360 53 == (F "90" 53, .eq)
#guard D (F "-2" 53) zero 360 53 == (F "-90" 53, .eq)
#guard D (F "-2" 53) zero 1 53 == (F "-1/4" 53, .eq)
-- the diagonals
#guard D (F "3" 53) (F "3" 53) 360 53 == (F "45" 53, .eq)
#guard D (F "-3" 53) (F "3" 53) 360 53 == (F "-45" 53, .eq)
#guard D (F "3" 53) (F "-3" 53) 360 53 == (F "135" 53, .eq)
#guard D (F "-3" 53) (F "-3" 53) 360 53 == (F "-135" 53, .eq)
#guard D (F "1/3" 53) (F "1/3" 53) 360 53 == (F "45" 53, .eq)
#guard D (F "3" 200) (F "-3" 53) 360 2 == (F "128" 2, .lt)
#guard D (F "3" 53) (F "-3" 53) 360 2 .Ceiling == (F "192" 2, .gt)
-- `u = 0`, `p = 0`
#guard D one' (F "2" 53) 0 53 == (zero, .eq)
#guard D inf ninf 0 53 == (zero, .eq)
#guard D (F "-5" 53) ninf 0 53 == (zero, .eq)
#guard D (F "3" 53) (F "3" 53) 0 53 == (zero, .eq)
#guard D one' (F "2" 53) 360 0 == (nan, .eq)

-- correctly rounded values
#guard D (F "1" 53) (F "2" 53) 360 53 == (F "1869349290346353/70368744177664" 53, .gt)
#guard D (F "2" 53) (F "1" 53) 360 53 == (F "4463837685643407/70368744177664" 53, .lt)
#guard D (F "1" 53) (F "-2" 53) 360 53 == (F "674814041352073/4398046511104" 53, .gt)
#guard D (F "2" 53) (F "-1" 53) 360 53 == (F "8202536266336113/70368744177664" 53, .gt)
#guard D (F "-1" 53) (F "2" 53) 360 53 == (F "-1869349290346353/70368744177664" 53, .lt)
#guard D (F "-2" 53) (F "1" 53) 360 53 == (F "-4463837685643407/70368744177664" 53, .gt)
#guard D (F "-1" 53) (F "-2" 53) 360 53 == (F "-674814041352073/4398046511104" 53, .lt)
#guard D (F "-2" 53) (F "-1" 53) 360 53 == (F "-8202536266336113/70368744177664" 53, .lt)
#guard D (F "1/3" 53) (F "7/5" 53) 360 53 == (F "3769652993334603/281474976710656" 53, .lt)
#guard D (F "-7/5" 53) (F "1/3" 53) 360 53 == (F "-5390773727656109/70368744177664" 53, .gt)
#guard D (F "22/7" 53) (F "-1/1000" 53) 360 53 == (F "791808728949883/8796093022208" 53, .lt)
#guard D (F "1/1000" 53) (F "-22/7" 53) 360 53 == (F "1583136387046277/8796093022208" 53, .gt)
#guard D (F "1000000000000" 53) (F "3" 53) 360 53 == (F "6333186975977665/70368744177664" 53, .gt)
#guard D (F "3" 53) (F "-1000000000000" 53) 360 53 == (F "197912092999491/1099511627776" 53, .lt)
#guard D (F "1" 53) (F "2" 53) 1 53 == (F "664657525456481/9007199254740992" 53, .lt)
#guard D (F "1" 53) (F "-2" 53) 400 53 == (F "749793379280081/4398046511104" 53, .lt)
#guard D (F "-2" 53) (F "1" 53) 7 53 == (F "-1388749502200171/1125899906842624" 53, .gt)
#guard D (F "2" 53) (F "-1" 53) 18446744073709551615 53 == (F "5972904630562260992" 53, .lt)
#guard D (F "1" 53) (F "2" 53) 360 53 .Floor == (F "7477397161385411/281474976710656" 53, .lt)
#guard D (F "-2" 53) (F "-1" 53) 360 53 .Floor == (F "-8202536266336113/70368744177664" 53, .lt)
#guard D (F "2" 53) (F "-1" 53) 360 53 .Floor == (F "512658516646007/4398046511104" 53, .lt)
#guard D (F "1" 53) (F "2" 53) 360 53 .Ceiling == (F "1869349290346353/70368744177664" 53, .gt)
#guard D (F "-2" 53) (F "-1" 53) 360 53 .Ceiling == (F "-512658516646007/4398046511104" 53, .gt)
#guard D (F "2" 53) (F "-1" 53) 360 53 .Ceiling == (F "8202536266336113/70368744177664" 53, .gt)
#guard D (F "1" 53) (F "2" 53) 360 20 == (F "217621/8192" 20, .gt)
#guard D (F "1" 53) (F "-2" 53) 360 1 == (F "128" 1, .lt)
#guard D (F "-2" 53) (F "1" 53) 360 113
  == (F "-5146454460852742461152984682250581/81129638414606681695789005144064" 113, .gt)

-- agreement with `atanWithPeriod` for `x = 1`
#guard D (F "1/3" 53) one' 360 53 == atanWithPeriodPrecRound (F "1/3" 53) 360 53 .Nearest
#guard D (F "-22/7" 53) one' 7 53 .Floor == atanWithPeriodPrecRound (F "-22/7" 53) 7 53 .Floor
#guard atan2WithPeriod (F "1" 53) (F "2" 53) 360 == (D (F "1" 53) (F "2" 53) 360 53).1
#guard (toString (atan2WithPeriodPrecRound (F "1" 200) (F "-2" 200) 360 200 .Nearest).1).startsWith
  "153.4349488229220106484278062795467053287957857003547789"

-- extreme ratios
private def t : AzFloat := powerOf2 (AzInt.ofInt (-200))
#guard D t one' 360 53 == (F ("1007958012753983/"
  ++ "28269553036454149273332760011886696253239742350009903329945699220681916416") 53, .gt)
#guard D one' t 360 53 == (F "90" 53, .gt)
#guard D one' t 360 53 .Floor == (F "6333186975989759/70368744177664" 53, .lt)
#guard D t (-one') 360 53 == (F "180" 53, .gt)
#guard D t (-one') 360 53 .Floor == (F "6333186975989759/35184372088832" 53, .lt)
#guard D (-t) (-one') 360 53 == (F "-180" 53, .lt)
private def tiny : AzFloat := powerOf2 (AzInt.ofInt (-1073741824))
private def huge : AzFloat := powerOf2 (AzInt.ofInt 1073741824)
#guard (D tiny one' 360 53).1
  == (F "1007958012753983/17592186044416" 53) <<< AzInt.ofInt (-1073741824)
#guard (D tiny one' 360 53).2 == .gt
#guard (D (-tiny) huge 360 53 .Floor).2 == .lt
#guard D huge tiny 360 53 == (F "90" 53, .gt)
#guard D tiny (-huge) 360 53 == (F "180" 53, .gt)
#guard D (-huge) (-tiny) 360 53 == (F "-90" 53, .gt)
#guard D (-huge) tiny 360 53 == (F "-90" 53, .lt)
#guard (D huge tiny 360 53 .Floor).2 == .lt
