/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.BarnesGRat
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for the Barnes `G`-function of a rational

The zeros, the exact integers, `p = 0`, half-integers (the values of the float function),
thirds and sevenths with their signs, 200 bits of `G(1/3)`, a small argument, large shifts.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)
private def G (x : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  D (barnesGRatPrecRound (Q x) p m)

-- zeros, integers, `p = 0`
#guard G "0" 53 == ("0.0", .eq)
#guard G "0" 0 == ("0.0", .eq)
#guard G "-3" 53 == ("0.0", .eq)
#guard G "1" 53 == ("1.0", .eq)
#guard G "7" 53 == ("3.456e4", .eq)
#guard G "64" 53 == ("8.435294445350786e2302", .lt)
#guard G "65" 53 == ("1.6723884910237353e2390", .gt)
#guard G "1/3" 0 == ("NaN", .eq)

-- half-integers: the values of the float function
#guard G "1/2" 53 == ("0.6032442812094462", .lt)
#guard G "1/2" 53 .Ceiling == ("0.6032442812094463", .gt)
#guard G "3/2" 53 == ("1.069222649266413", .gt)
#guard G "-1/2" 53 == ("-0.17017206989656153", .lt)
#guard G "-3/2" 53 == ("-0.07200698193480054", .lt)
#guard G "-5/2" 53 == ("0.07617297965686111", .lt)

-- other rationals
#guard G "1/3" 53 == ("0.4000785230907682", .lt)
#guard G "1/3" 200
  == ("0.4000785230907682022850145152603045579230386308284175985953328", .gt)
#guard G "-1/3" 53 == ("-0.19123134530542987", .gt)
#guard G "7/3" 100 == ("0.957082735559644511138702903607", .lt)
#guard G "22/7" 53 == ("1.0463301460108736", .gt)
#guard G "-22/7" 53 == ("0.0055526954326128725", .lt)
#guard G "1/1000" 53 == ("0.0010009950387946161", .lt)
#guard G "301/3" 53 == ("1.8193433869462661e6678", .lt)
#guard G "-61/3" 53 == ("-4.315738167996215e150", .lt)
#guard toString (barnesGRat (Q "1/3") 53) == "0.4000785230907682"

-- a large negative argument: exponent and sign
#guard (fun r : AzFloat × Ordering => (r.1.exponent?.map toString, r.1.isNegative, r.2))
    (barnesGRatPrecRound (Q "-2000/3") 53 .Nearest) == (some "1608669", false, .lt)
