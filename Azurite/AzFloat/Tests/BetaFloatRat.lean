/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.BetaFloatRat
import Azurite.AzFloat.LnBeta
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `B`, `ln |B|` and `ln B` of a float and a rational

Special values (a float that is not finite, zeros, negative integers, `p = 0`), the exact
values (`B(3, 1/3) = 27/14`, `B(1, 1/3) = 3`, `B(1/2, 1/2) = π`), the exact zeros
(`B(1/2, −3/2) = 0`), negative arguments with the sign, a tiny float, and agreement with the
float functions where the rational is a float and with the function of two rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- The float nearest to a rational at `p` bits. -/
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def B (a b : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  betaFloatRatPrecRound (F a 53) (Q b) p m
private def LA (a b : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  lnAbsBetaFloatRatPrecRound (F a 53) (Q b) p m
private def L (a b : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  lnBetaFloatRatPrecRound (F a 53) (Q b) p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)
private def DL (r : (AzFloat × Ordering) × Bool) : String × Ordering × Bool :=
  (toString r.1.1, r.1.2, r.2)

-- a float that is not finite
#guard D (betaFloatRatPrecRound nan (Q "1/3") 53 .Nearest) == ("NaN", .eq)
#guard D (betaFloatRatPrecRound (infinity true) (Q "1/3") 53 .Nearest) == ("0.0", .eq)
#guard D (betaFloatRatPrecRound (infinity true) (Q "-1/3") 53 .Nearest) == ("NaN", .eq)
#guard D (betaFloatRatPrecRound (infinity true) (Q "0") 53 .Nearest) == ("NaN", .eq)
#guard D (betaFloatRatPrecRound (infinity false) (Q "1/3") 53 .Nearest) == ("NaN", .eq)
#guard DL (lnAbsBetaFloatRatPrecRound (infinity true) (Q "1/3") 53 .Nearest)
  == ("-Infinity", .eq, true)
#guard DL (lnAbsBetaFloatRatPrecRound (infinity true) (Q "-1/3") 53 .Nearest)
  == ("NaN", .eq, true)
#guard D (lnBetaFloatRatPrecRound (infinity true) (Q "1/3") 53 .Nearest) == ("-Infinity", .eq)
#guard D (lnBetaFloatRatPrecRound nan (Q "1/3") 53 .Nearest) == ("NaN", .eq)

-- special values
#guard D (B "0" "1/3" 53) == ("Infinity", .eq)
#guard D (B "1/2" "0" 53) == ("Infinity", .eq)
#guard D (B "-2" "1/3" 53) == ("NaN", .eq)
#guard D (B "1/2" "-7" 53) == ("NaN", .eq)
#guard D (B "1/2" "1/3" 0) == ("NaN", .eq)
#guard D (B "1/2" "-3/2" 53) == ("0.0", .eq)
#guard DL (LA "1/2" "-3/2" 53) == ("-Infinity", .eq, true)
#guard DL (LA "0" "1/3" 53) == ("Infinity", .eq, true)

-- exact values
#guard D (B "1" "1/3" 53) == ("3.0", .eq)
#guard D (B "3" "1/3" 53) == ("1.9285714285714286", .gt)
#guard D (B "1/2" "1/2" 53) == ("3.141592653589793", .lt)

-- values
#guard D (B "5/2" "1/3" 53) == ("2.0650318278429416", .lt)
#guard D (B "1/2" "1/3" 53) == ("4.206546315976363", .lt)
#guard D (B "-5/2" "1/3" 53) == ("0.9451746043304914", .lt)
#guard D (B "1/3" "1/3" 53) == ("5.29991625085635", .gt)
#guard D (B "1/3" "1/3" 100 .Floor) == ("5.299916250856350049817018140705", .lt)
#guard toString (betaFloatRat (F "5/2" 10) (Q "1/3") 200)
  == "2.065031827842941730094119007328614999500087247988052250740754"
#guard DL (LA "5/2" "1/3" 53) == ("0.7251456392932203", .gt, true)
#guard DL (LA "-5/2" "1/3" 53) == ("-0.05638560206832697", .lt, true)
#guard DL (LA "1" "-1/3" 53) == ("1.0986122886681098", .gt, false)
#guard DL (LA "1000000000000" "1/3" 53) == ("-8.224919725048304", .gt, true)
#guard D (L "5/2" "1/3" 53) == ("0.7251456392932203", .gt)
#guard D (L "1" "-1/3" 53) == ("NaN", .eq)
#guard (toString (lnAbsBetaFloatRat (F "5/2" 10) (Q "1/3") 100).1,
    (lnAbsBetaFloatRat (F "5/2" 10) (Q "1/3") 100).2)
  == ("0.725145639293220288749107349007", true)
#guard toString (lnBetaFloatRat (F "5/2" 10) (Q "1/3") 100)
  == "0.725145639293220288749107349007"

-- a tiny float: `B(2^(−100), 1/3) ≈ 2^100`
#guard D (betaFloatRatPrecRound (one <<< AzInt.ofInt (-100)) (Q "1/3") 53 .Nearest)
  == ("1.2676506002282294e30", .lt)
#guard DL (lnAbsBetaFloatRatPrecRound (one <<< AzInt.ofInt (-100)) (Q "1/3") 53 .Nearest)
  == ("69.31471805599453", .gt, true)

-- where the rational is a float: the float functions
#guard [("5/2", "3/4"), ("-5/2", "3/8"), ("1/3", "7/2"), ("1000000", "1/2"),
    ("1/1048576", "-9/4"), ("-7/4", "3/4")].all fun (x, y) =>
  [53, 100].all fun p => [RoundingMode.Floor, .Nearest, .Up].all fun m =>
    D (B x y p m) == D (betaPrecRound (F x 53) (F y 53) p m)
      && DL (LA x y p m) == DL (lnAbsBetaPrecRound (F x 53) (F y 53) p m)
      && D (L x y p m) == D (lnBetaPrecRound (F x 53) (F y 53) p m)

-- where the float is short: the function of two rationals
#guard [("5/2", "1/3"), ("-5/2", "2/7"), ("3/4", "-10/3"), ("17", "5/6")].all fun (x, y) =>
  [53, 100].all fun p => [RoundingMode.Ceiling, .Nearest, .Down].all fun m =>
    D (B x y p m) == D (betaRatPrecRound (Q x) (Q y) p m)
      && DL (LA x y p m) == DL (lnAbsBetaRatPrecRound (Q x) (Q y) p m)
