/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.QBeta
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for the `q`-beta function

The six functions (the base a float or a rational; two floats, a float and a rational, or
two rationals): the bases that are not positive and finite, the base `1` (`B`), arguments
that are not finite (`0` at `+∞` for `q > 1`, `NaN` for `q < 1`), `0` and the poles, the
zeros (`a + b` a non-positive integer), `p = 0`, the exact values at positive integers
(`B_{1/2}(2, 3) = 32/105`, `B_{1/3}(2, 3) = 243/520`, `B_3(2, 3) = 1/520`), the algebraic
value `B_{1/2}(1, 1/2) = 1 + √2/2`, bases below and above `1`, negative arguments, 200 bits
of `B_{1/2}(1/2, 1/2) = 2.47128689094317937794831721945329266429779850995824964634042…`
and of `B_{1/3}(1/3, 2/3) = 2.48712150187951727147225523450178383498456905568700875082684…`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- The float nearest to a rational at 53 bits. -/
private def F (s : String) : AzFloat := ofAzRat (Q s) 53
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)
private def B (q a b : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  D (qBetaPrecRound (F q) (F a) (F b) p m)
private def BFFR (q a b : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  D (qBetaFloatFloatRatPrecRound (F q) (F a) (Q b) p m)
private def BFRR (q a b : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  D (qBetaFloatRatRatPrecRound (F q) (Q a) (Q b) p m)
private def BRFF (q a b : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  D (qBetaRatFloatFloatPrecRound (Q q) (F a) (F b) p m)
private def BRFR (q a b : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  D (qBetaRatFloatRatPrecRound (Q q) (F a) (Q b) p m)
private def BR (q a b : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  D (qBetaRatPrecRound (Q q) (Q a) (Q b) p m)

/-! ### Floats -/

-- bases and arguments that are not finite, bases `≤ 0`
#guard D (qBetaPrecRound nan (F "1/2") (F "1/2") 53 .Nearest) == ("NaN", .eq)
#guard D (qBetaPrecRound (F "1/2") nan (F "1/2") 53 .Nearest) == ("NaN", .eq)
#guard D (qBetaPrecRound (F "1/2") (F "1/2") nan 53 .Nearest) == ("NaN", .eq)
#guard D (qBetaPrecRound (infinity true) (F "1/2") (F "1/2") 53 .Nearest) == ("NaN", .eq)
#guard D (qBetaPrecRound (F "1/2") (infinity true) (F "1/2") 53 .Nearest) == ("NaN", .eq)
#guard D (qBetaPrecRound (F "2") (infinity true) (F "1/2") 53 .Nearest) == ("0.0", .eq)
#guard D (qBetaPrecRound (F "2") (F "1/2") (infinity true) 53 .Nearest) == ("0.0", .eq)
#guard D (qBetaPrecRound (F "2") (infinity true) (infinity true) 53 .Nearest) == ("0.0", .eq)
#guard D (qBetaPrecRound (F "2") (infinity true) (F "-1/2") 53 .Nearest) == ("NaN", .eq)
#guard D (qBetaPrecRound (F "2") (infinity false) (F "1/2") 53 .Nearest) == ("NaN", .eq)
#guard D (qBetaPrecRound (F "1") (infinity true) (F "1/2") 53 .Nearest) == ("0.0", .eq)
#guard B "0" "1/2" "1/2" 53 == ("NaN", .eq)
#guard B "-2" "1/2" "1/2" 53 == ("NaN", .eq)

-- `0`, the poles, the zeros, `p = 0`
#guard B "1/2" "0" "1/2" 53 == ("Infinity", .eq)
#guard B "1/2" "1/2" "0" 53 == ("Infinity", .eq)
#guard B "1/2" "-3" "1/2" 53 == ("NaN", .eq)
#guard B "1/2" "-3" "0" 53 == ("NaN", .eq)
#guard B "1/2" "1/2" "-1/2" 53 == ("0.0", .eq)
#guard B "1/2" "3/2" "-5/2" 53 == ("0.0", .eq)
#guard B "1/2" "1/2" "1/2" 0 == ("NaN", .eq)
#guard B "1/2" "1/2" "-1/2" 0 == ("NaN", .eq)
#guard B "1/2" "0" "1/2" 0 == ("Infinity", .eq)

-- the base `1`: `B`
#guard B "1" "1/2" "1/2" 53 == ("3.141592653589793", .lt)
#guard B "1" "2" "3" 53 == ("0.08333333333333333", .lt)

-- the exact values at positive integers
#guard B "1/2" "1" "1" 53 == ("1.0", .eq)
#guard B "1/2" "2" "3" 53 == ("0.3047619047619048", .gt)
#guard B "1/2" "3" "4" 53 == ("0.20972862263184844", .lt)
#guard B "3" "3" "4" 53 == ("2.2704568159113616e-6", .gt)

-- bases below and above `1`
#guard B "1/2" "1/2" "1/2" 53 == ("2.4712868909431793", .lt)
#guard B "1/2" "1/2" "1/2" 53 .Ceiling == ("2.4712868909431798", .gt)
#guard B "1/2" "1/2" "1/2" 200
  == ("2.47128689094317937794831721945329266429779850995824964634043", .gt)
#guard B "3/4" "1/4" "5/2" 53 == ("2.838385821123477", .gt)
#guard B "2" "1/2" "3/2" 53 == ("1.7215513325299312", .gt)
#guard B "1/2" "301/3" "1/2" 53 == ("1.111595000650682", .gt)
#guard B "1/2" "1" "1/2" 53 == ("1.7071067811865475", .lt)
#guard B "1/2" "5" "1/2" 53 == ("1.1325083821611077", .lt)

-- negative arguments
#guard B "1/2" "-1/2" "3/4" 53 == ("-0.7546849494664817", .gt)
#guard B "1/2" "-3/2" "-1/4" 53 == ("-3.515396747091872", .lt)
#guard B "2" "-5/2" "7/4" 53 == ("1.016632473765052", .lt)

-- to nearest at the precision of the arguments
#guard toString (qBeta (F "1/2") (F "1/2") (F "1/2")) == "2.4712868909431793"

/-! ### Rationals -/

#guard BR "1/3" "1/3" "2/3" 53 == ("2.487121501879517", .lt)
#guard BR "1/3" "1/3" "2/3" 200
  == ("2.487121501879517271472255234501783834984569055687008750826842", .gt)
#guard BR "1/3" "2" "3" 53 == ("0.4673076923076923", .gt)
#guard BR "3" "2" "3" 53 == ("0.0019230769230769232", .gt)
#guard BR "1/3" "-7/3" "1/2" 53 == ("-0.17362772762746512", .lt)
#guard BR "1/3" "-7/3" "1/3" 53 == ("0.0", .eq)
#guard BR "1" "1/2" "1/2" 53 == ("3.141592653589793", .lt)
#guard BR "1/3" "0" "1/2" 53 == ("Infinity", .eq)
#guard BR "1/3" "-2" "1/2" 53 == ("NaN", .eq)
#guard BR "-1/3" "1/2" "1/2" 53 == ("NaN", .eq)
#guard toString (qBetaRat (Q "1/3") (Q "1/3") (Q "2/3") 53) == "2.487121501879517"

/-! ### Mixed -/

#guard BFFR "1/2" "1/2" "1/3" 53 == ("3.2166058756952407", .lt)
#guard BFFR "1/2" "-3/2" "1/3" 53 == ("0.6475007461483164", .gt)
#guard BFFR "1/2" "1/2" "-1/2" 53 == ("0.0", .eq)
#guard D (qBetaFloatFloatRatPrecRound (F "2") (infinity true) (Q "1/3") 53 .Nearest)
  == ("0.0", .eq)
#guard D (qBetaFloatFloatRatPrecRound (F "1/2") (infinity true) (Q "1/3") 53 .Nearest)
  == ("NaN", .eq)
#guard D (qBetaFloatFloatRatPrecRound (F "2") nan (Q "1/3") 53 .Nearest) == ("NaN", .eq)
#guard BFRR "1/2" "1/3" "2/3" 53 == ("2.8262564180889997", .lt)
#guard BRFF "1/3" "1/2" "1/4" 53 == ("3.4138251612602697", .gt)
#guard BRFR "1/3" "1/2" "1/3" 53 == ("2.8012936722539235", .gt)
