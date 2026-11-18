/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LnBetaRat
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `ln B(a, b)` and `ln |B(a, b)|` of two rationals

The special values, positive rationals (`ln B(1/3, 2/3) = ln (2π/√3)`), the exact case
`ln |B(a, 1)| = −ln |a|`, negative rationals with the sign, other precisions, and agreement
with the float function on exactly representable arguments.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def R (a b : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  lnAbsBetaRatPrecRound (Q a) (Q b) p m
/-- A result as its decimal output, its comparison tag and the sign. -/
private def D (r : (AzFloat × Ordering) × Bool) : String × Ordering × Bool :=
  (toString r.1.1, r.1.2, r.2)

-- special values
#guard D (R "0" "1/2" 53) == ("Infinity", .eq, true)
#guard D (R "0" "-1/2" 0) == ("Infinity", .eq, true)
#guard D (R "0" "-2" 53) == ("NaN", .eq, true)
#guard D (R "-1" "1/2" 53) == ("NaN", .eq, true)
#guard D (R "1/3" "-1/3" 53) == ("-Infinity", .eq, true)
#guard D (R "-7/3" "4/3" 0) == ("-Infinity", .eq, true)
#guard D (R "1/2" "1/2" 0) == ("NaN", .eq, true)

-- positive rationals
#guard D (R "1/2" "1/2" 53) == ("1.1447298858494002", .lt, true)
#guard D (R "1/3" "2/3" 53) == ("1.2885709220752906", .lt, true)
#guard D (R "1/3" "2/3" 53 .Floor) == ("1.2885709220752906", .lt, true)
#guard D (R "1/3" "1/3" 53) == ("1.6676910187080105", .lt, true)
#guard D (R "22/7" "1/10" 53) == ("2.1530963223090582", .gt, true)
#guard D (R "100" "200" 53) == ("-192.13419227497894", .gt, true)
#guard D (R "100000000000000000000" "1/3" 53) == ("-14.365146639699205", .lt, true)

-- `ln |B(a, 1)| = −ln |a|`
#guard D (R "1/3" "1" 53) == ("1.0986122886681098", .gt, true)
#guard D (R "1" "1/3" 53 .Ceiling) == ("1.0986122886681098", .gt, true)
#guard D (R "1" "1" 53) == ("0.0", .eq, true)
#guard D (R "-1/2" "1" 53) == ("0.6931471805599453", .lt, false)

-- negative rationals, with the sign of `B`
#guard D (R "-1/3" "-1/3" 53) == ("1.412639372595335", .lt, false)
#guard D (R "-7/3" "5/2" 53) == ("-1.1652679336286726", .lt, false)
#guard D (R "-3/2" "5/2" 53) == ("1.1447298858494002", .lt, true)
#guard D (R "-201/2" "1/3" 53) == ("-1.2455507441260134", .lt, true)

-- other precisions
#guard D (R "1/3" "2/3" 1) == ("1.0", .lt, true)
#guard D (R "1/3" "2/3" 20) == ("1.28857", .lt, true)
#guard D (R "1/3" "2/3" 200)
  == ("1.288570922075290637863036854349972427399049668364192099766955", .lt, true)
#guard D (R "-1/3" "-1/3" 200 .Floor)
  == ("1.412639372595335068977028956146762952314420539753731342685014", .lt, false)
#guard D (R "1/3" "1/3" 1000) == ("1.6676910187080105696984852565839117478076198207934654629373151\
  161214281114960650310884510751057224309327938933957083538523279074267923691030765819076464722705\
    7723903945463216865974449878858990315760095617804524500546804009282578308114004502241627762342\
    57364775000874008048517178574092308744728526284783", .lt, true)

-- agreement with the float function
#guard R "1/2" "1/2" 53 == lnAbsBetaPrecRound (X "0.5" 53) (X "0.5" 53) 53 .Nearest
#guard R "-9/4" "5/4" 53 == lnAbsBetaPrecRound (X "-2.25" 53) (X "1.25" 53) 53 .Nearest
#guard R "-5/2" "15/4" 100 .Floor
  == lnAbsBetaPrecRound (X "-2.5" 53) (X "3.75" 53) 100 .Floor
#guard R "1/4" "1" 53 .Ceiling == lnAbsBetaPrecRound (X "0.25" 53) (X "1" 53) 53 .Ceiling

-- `lnAbsBetaRat`
#guard (toString (lnAbsBetaRat (Q "1/3") (Q "2/3") 53).1, (lnAbsBetaRat (Q "-1/3") (Q "-1/3") 53).2)
  == ("1.2885709220752906", false)

-- `lnBetaRatPrecRound`: the same where `B ≥ 0`, `NaN` where `B < 0`
private def LB (a b : String) (p : Nat) (m : RoundingMode := .Nearest) : String × Ordering :=
  let r := lnBetaRatPrecRound (Q a) (Q b) p m
  (toString r.1, r.2)
#guard LB "1/3" "2/3" 53 == ("1.2885709220752906", .lt)
#guard LB "-3/2" "5/2" 53 == ("1.1447298858494002", .lt)
#guard LB "1/3" "1" 53 == ("1.0986122886681098", .gt)
#guard LB "1" "1" 53 == ("0.0", .eq)
#guard LB "-1/3" "-1/3" 53 == ("NaN", .eq)
#guard LB "-7/3" "5/2" 53 == ("NaN", .eq)
#guard LB "-1/2" "1" 53 == ("NaN", .eq)
#guard LB "0" "1/2" 53 == ("Infinity", .eq)
#guard LB "1/3" "-1/3" 53 == ("-Infinity", .eq)
#guard LB "-1" "1/2" 53 == ("NaN", .eq)
#guard toString (lnBetaRat (Q "1/3") (Q "2/3") 53) == "1.2885709220752906"
