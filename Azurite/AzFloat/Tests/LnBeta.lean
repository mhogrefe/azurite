/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LnBeta
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString

/-!
# Tests for `ln B(a, b)` and `ln |B(a, b)|` with the sign of `B(a, b)`

The special values (`NaN` where `B` is, `+∞` at a zero argument, `−∞` where `B = 0`, `p = 0`),
positive arguments (`ln B(1/2, 1/2) = ln π`, `ln B(2, 3) = −ln 12`, and
`ln B(10¹⁰, 10¹⁰) ≈ −1.39·10¹⁰`, where `B` itself has an exponent of ten digits), the exact
case `ln |B(a, 1)| = −ln |a|` (`0` at `a = 1`), negative arguments with the sign, other
precisions, 200- and 1000-bit values, agreement with the logarithm of `betaPrecRound`, and
`lnBetaPrecRound` (`NaN` where `B < 0`).
-/

open Azurite Azurite.AzFloat

/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def L (a b : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  lnAbsBetaPrecRound (X a 53) (X b 53) p m
/-- A result as its decimal output, its comparison tag and the sign. -/
private def D (r : (AzFloat × Ordering) × Bool) : String × Ordering × Bool :=
  (toString r.1.1, r.1.2, r.2)

-- special values
#guard D (lnAbsBetaPrecRound nan (X "1" 53) 53 .Nearest) == ("NaN", .eq, true)
#guard D (lnAbsBetaPrecRound (X "1" 53) nan 53 .Nearest) == ("NaN", .eq, true)
#guard D (lnAbsBetaPrecRound (infinity true) (X "2" 53) 53 .Nearest) == ("-Infinity", .eq, true)
#guard D (lnAbsBetaPrecRound (X "0.5" 53) (infinity true) 53 .Nearest)
  == ("-Infinity", .eq, true)
#guard D (lnAbsBetaPrecRound (infinity true) (infinity true) 53 .Nearest)
  == ("-Infinity", .eq, true)
#guard D (lnAbsBetaPrecRound (infinity true) (X "-2.5" 53) 53 .Nearest) == ("NaN", .eq, true)
#guard D (lnAbsBetaPrecRound (infinity false) (X "2" 53) 53 .Nearest) == ("NaN", .eq, true)
#guard D (L "0" "0.5" 53) == ("Infinity", .eq, true)
#guard D (L "0" "-0.5" 0) == ("Infinity", .eq, true)
#guard D (L "0" "-2" 53) == ("NaN", .eq, true)
#guard D (L "-1" "0.5" 53) == ("NaN", .eq, true)
#guard D (L "0.5" "-0.5" 53) == ("-Infinity", .eq, true)
#guard D (L "-1.5" "0.5" 0) == ("-Infinity", .eq, true)
#guard D (L "0.5" "0.5" 0) == ("NaN", .eq, true)

-- positive arguments
#guard D (L "0.5" "0.5" 53) == ("1.1447298858494002", .lt, true)
#guard D (L "0.5" "0.5" 53 .Floor) == ("1.1447298858494002", .lt, true)
#guard D (L "0.5" "0.5" 53 .Ceiling) == ("1.1447298858494004", .gt, true)
#guard D (L "2" "3" 53) == ("-2.4849066497880004", .lt, true)
#guard D (L "1.5" "2.5" 53) == ("-1.627858836390381", .gt, true)
#guard D (L "0.25" "0.75" 53) == ("1.4913034761293729", .gt, true)
#guard D (L "10" "10" 53) == ("-13.736229227036555", .gt, true)
#guard D (L "100" "200" 53) == ("-192.13419227497894", .gt, true)
#guard D (L "1e10" "1e10" 53) == ("-13862943621.44632", .lt, true)
#guard D (L "1e10" "1e10" 53 .Ceiling) == ("-13862943621.446318", .gt, true)
#guard D (L "1e-10" "3" 53) == ("23.025850929790458", .gt, true)
#guard D (L "1e100" "1e-100" 53) == ("230.25850929940458", .gt, true)

-- `ln |B(a, 1)| = −ln |a|`
#guard D (L "0.25" "1" 53) == ("1.3862943611198906", .lt, true)
#guard D (L "1" "0.25" 53 .Floor) == ("1.3862943611198906", .lt, true)
#guard D (L "1" "1" 53) == ("0.0", .eq, true)
#guard D (L "-0.5" "1" 53) == ("0.6931471805599453", .lt, false)
#guard D (L "3" "1" 53) == ("-1.0986122886681098", .lt, true)

-- negative arguments, with the sign of `B`
#guard D (L "-0.3" "-0.4" 53) == ("1.3268917020441846", .gt, false)
#guard D (L "-0.3" "-0.4" 53 .Up) == ("1.3268917020441846", .gt, false)
#guard D (L "-1.5" "0.25" 53) == ("0.7816377788375822", .lt, true)
#guard D (L "-2.5" "3.75" 53) == ("1.5288436985175562", .gt, false)
#guard D (L "-1.5" "2.5" 53) == ("1.1447298858494002", .lt, true)
#guard D (L "-0.999" "0.5" 53) == ("6.2149912479124865", .gt, true)
#guard D (L "-100.5" "0.25" 53) == ("-0.21202255690773367", .lt, true)
#guard D (L "0.3" "-1.2999" 53) == ("-6.911820555676078", .lt, false)

-- other precisions
#guard D (L "2.5" "3.5" 1) == ("-4.0", .lt, true)
#guard D (L "2.5" "3.5" 20) == ("-3.301834", .gt, true)
#guard D (L "0.5" "0.5" 200)
  == ("1.144729885849400174143427351353058711647294812915311571513623", .gt, true)
#guard D (L "-0.3" "-0.4" 200 .Floor)
  == ("1.32689170204418455035347077140576862200656669340028504250852", .lt, false)
#guard D (L "100" "200" 200)
  == ("-192.1341922749789518930798544281427326161826842345995678903774", .gt, true)
#guard D (L "0.25" "0.75" 1000) == ("1.49130347612937282885204341208214699568504488009543919857396\
  307621883458086967343758655493377369905147301055273898333202589096564580252186579541645462782480\
    6241757699680531620497638292670815774524764794688507005771631476265803568167354159140940416893\
    4602547859215071477275888085909323428490039095268298", .gt, true)

-- agreement with the logarithm of `B` (300 bits of `B`, then 53 of its logarithm)
private def viaBeta (a b : String) (m : RoundingMode) : AzFloat × Ordering :=
  lnPrecRound (betaPrecRound (X a 53) (X b 53) 300 .Nearest).1.abs 53 m
#guard (L "0.3" "2.75" 53).1 == viaBeta "0.3" "2.75" .Nearest
#guard (L "-0.3" "-0.4" 53 .Floor).1 == viaBeta "-0.3" "-0.4" .Floor
#guard (L "-2.5" "3.75" 53 .Ceiling).1 == viaBeta "-2.5" "3.75" .Ceiling
#guard (L "40" "0.125" 53).1 == viaBeta "40" "0.125" .Nearest

-- `lnAbsBeta`
#guard (toString (lnAbsBeta (X "0.5" 53) (X "0.5" 53)).1, (lnAbsBeta (X "0.5" 53) (X "0.5" 53)).2)
  == ("1.1447298858494002", true)

-- `lnBetaPrecRound`: the same where `B ≥ 0`, `NaN` where `B < 0`
private def LB (a b : String) (p : Nat) (m : RoundingMode := .Nearest) : String × Ordering :=
  let r := lnBetaPrecRound (X a 53) (X b 53) p m
  (toString r.1, r.2)
#guard LB "0.5" "0.5" 53 == ("1.1447298858494002", .lt)
#guard LB "2" "3" 53 == ("-2.4849066497880004", .lt)
#guard LB "-1.5" "2.5" 53 == ("1.1447298858494002", .lt)
#guard LB "-1.5" "0.25" 53 == ("0.7816377788375822", .lt)
#guard LB "1" "1" 53 == ("0.0", .eq)
#guard LB "0.25" "1" 53 == ("1.3862943611198906", .lt)
#guard LB "-0.3" "-0.4" 53 == ("NaN", .eq)
#guard LB "-2.5" "3.75" 53 == ("NaN", .eq)
#guard LB "-0.5" "1" 53 == ("NaN", .eq)
#guard LB "0" "0.5" 53 == ("Infinity", .eq)
#guard LB "0.5" "-0.5" 53 == ("-Infinity", .eq)
#guard LB "-1" "0.5" 53 == ("NaN", .eq)
#guard LB "0.5" "0.5" 0 == ("NaN", .eq)
#guard toString (lnBeta (X "0.5" 53) (X "0.5" 53)) == "1.1447298858494002"
#guard toString (lnBeta (X "-0.3" 53) (X "-0.4" 53)) == "NaN"
