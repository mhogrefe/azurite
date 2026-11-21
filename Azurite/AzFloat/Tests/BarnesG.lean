/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.BarnesG
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for the Barnes `G`-function

`G(1/2) = 0.60324428120944620619142922453470207988300342038945976538776…`
(`= 2^(1/24) e^(1/8) π^(−1/4) A^(−3/2)`), `G(3/2) = Γ(1/2) G(1/2)`, the signs at negative
arguments (`G(−1/2) < 0`, `G(−3/2) < 0`, `G(−5/2) > 0`), the zeros at `0, −1, −2, …`, the exact
integers `G(n) = (n − 2)! ⋯ 1!` (`G(7) = 34560`), integers beyond the exact bound, arguments
that are not finite, `p = 0`, tiny arguments (`G(x) ≈ x`), and a large shift.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- The float nearest to a rational at 53 bits. -/
private def F (s : String) : AzFloat := ofAzRat (Q s) 53
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)
private def G (x : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  D (barnesGPrecRound (F x) p m)

-- not finite, `p = 0`
#guard D (barnesGPrecRound nan 53 .Nearest) == ("NaN", .eq)
#guard D (barnesGPrecRound (infinity true) 53 .Nearest) == ("Infinity", .eq)
#guard D (barnesGPrecRound (infinity false) 53 .Nearest) == ("NaN", .eq)
#guard G "1/2" 0 == ("NaN", .eq)
#guard G "0" 0 == ("0.0", .eq)

-- the zeros and the integers
#guard G "0" 53 == ("0.0", .eq)
#guard G "-3" 53 == ("0.0", .eq)
#guard G "1" 53 == ("1.0", .eq)
#guard G "2" 53 == ("1.0", .eq)
#guard G "3" 53 == ("1.0", .eq)
#guard G "4" 53 == ("2.0", .eq)
#guard G "5" 53 == ("12.0", .eq)
#guard G "7" 53 == ("3.456e4", .eq)
#guard G "20" 53 == ("4.3061925649977154e120", .gt)
#guard G "64" 53 == ("8.435294445350786e2302", .lt)
#guard (List.range 7).map (fun n => toString (barnesGNat n))
  == ["1", "1", "1", "1", "2", "12", "288"]
#guard toString (barnesGNat 7) == "34560"
-- beyond the exact bound: the loop
#guard G "65" 53 == ("1.6723884910237353e2390", .gt)
#guard G "70" 53 == ("8.617184828782125e2853", .gt)

-- half-integers
#guard G "1/2" 53 == ("0.6032442812094462", .lt)
#guard G "1/2" 53 .Floor == ("0.6032442812094462", .lt)
#guard G "1/2" 53 .Ceiling == ("0.6032442812094463", .gt)
#guard G "1/2" 1 == ("0.5", .lt)
#guard G "1/2" 2 == ("0.5", .lt)
#guard G "1/2" 200
  == ("0.603244281209446206191429224534702079883003420389459765387769", .gt)
#guard G "3/2" 53 == ("1.069222649266413", .gt)
#guard G "5/2" 53 == ("0.9475739010838258", .lt)
#guard G "-1/2" 53 == ("-0.17017206989656153", .lt)
#guard G "-3/2" 53 == ("-0.07200698193480054", .lt)
#guard G "-5/2" 53 == ("0.07617297965686111", .lt)
#guard toString (barnesG (F "1/2")) == "0.6032442812094462"

-- other arguments
#guard G "1/3" 53 == ("0.4000785230907682", .gt)
#guard G "7/3" 100 == ("0.95708273555964449832548432553", .lt)
#guard G "1/1024" 53 == ("0.000977511467884145", .lt)
#guard G "-1/1024" 53 == ("-0.0009756114554296788", .gt)
#guard G "201/2" 53 == ("1.6870997102901254e6704", .lt)
#guard G "-41/2" 53 == ("-1.271160046436095e155", .gt)

-- a large negative argument (the shift is about `1000`): exponent and sign, not the decimals
#guard (fun r : AzFloat × Ordering => (r.1.exponent?.map toString, r.1.isNegative, r.2))
    (barnesGPrecRound (F "-2001/2") 53 .Nearest) == (some "3913340", true, .gt)
