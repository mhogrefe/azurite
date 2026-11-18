/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.OfString
import Azurite.AzFloat.Pow
import Azurite.AzFloat.RatPow
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `q^y` with a rational base

The special values (as for `x^y`: `q^0 = 1`, `1^y = 1` even for `NaN`, the infinite exponents
against `|q|`, `0^y`, negative bases), the exact powers (`(4/9)^(1/2) = 2/3` rounded,
`(1/4)^(−1/2) = 2`, `(9/4)^(3/2) = 27/8`, `(3/2)^10`, `(−2/3)^3`), the integer powers through the
bracket (`3^40`, `(1/3)^40` at 20 bits), the correctly rounded `(2/3)^(5/4)`, `(22/7)^(−7/8)`,
`(1/3)^(1/3)` (the last within `1/30` ulp of a rounding boundary at 53 bits), `10^(1/2)`
(references from an 80- and 100-digit evaluation of `exp (y ln q)` at the float exponent),
`(1/3)^(1/3)` at 200 bits, agreement with `pow` on float bases, `(2/3)^(10^9)` at 10 bits
through the bracket, and `(−1)^y` for `y = ±2^(2^30)` by the parity read off the exponent.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
/-- `0.3333333333…` at 200 bits. -/
private def third200 : AzFloat :=
  X "0.3333333333333333333333333333333333333333333333333333333333334" 200
private def P (q : String) (y : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) :=
  ratPowPrecRound (Q q) y p m
private def pinf : AzFloat := infinity true
private def ninf : AzFloat := infinity false
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (P "1/3" zero 53) == ("1.0", .eq)
#guard D (P "0" zero 53) == ("1.0", .eq)
#guard D (P "1" nan 53) == ("1.0", .eq)
#guard D (P "1" ninf 53) == ("1.0", .eq)
#guard D (P "1" (X "-3.5" 53) 53) == ("1.0", .eq)
#guard D (P "2/3" nan 53) == ("NaN", .eq)
#guard D (P "3/2" pinf 53) == ("Infinity", .eq)
#guard D (P "2/3" pinf 53) == ("0.0", .eq)
#guard D (P "3/2" ninf 53) == ("0.0", .eq)
#guard D (P "2/3" ninf 53) == ("Infinity", .eq)
#guard D (P "-5/2" pinf 53) == ("Infinity", .eq)
#guard D (P "-1" pinf 53) == ("1.0", .eq)
#guard D (P "-1" ninf 53) == ("1.0", .eq)
#guard D (P "0" pinf 53) == ("0.0", .eq)
#guard D (P "0" ninf 53) == ("Infinity", .eq)
#guard D (P "0" (X "0.5" 53) 53) == ("0.0", .eq)
#guard D (P "0" (X "-2" 53) 53) == ("Infinity", .eq)
#guard D (P "-1" (X "4" 53) 53) == ("1.0", .eq)
#guard D (P "-1" (X "3" 53) 53) == ("-1.0", .eq)
#guard D (P "-2/3" (X "1.5" 53) 53) == ("NaN", .eq)
#guard D (P "-1" (X "0.5" 53) 53) == ("NaN", .eq)
#guard D (P "2/3" (X "3" 53) 0) == ("NaN", .eq)
#guard D (P "0" (X "3" 53) 0) == ("0.0", .eq)

-- exact and rational powers
#guard D (P "4/9" (X "0.5" 53) 53) == ("0.6666666666666666", .lt)
#guard D (P "1/4" (X "-0.5" 53) 53) == ("2.0", .eq)
#guard D (P "9/4" (X "1.5" 53) 53) == ("3.375", .eq)
#guard D (P "16/81" (X "0.75" 53) 53) == ("0.2962962962962963", .lt)
#guard D (P "3/2" (X "10" 53) 53) == ("57.6650390625", .eq)
#guard D (P "-2/3" (X "3" 53) 53) == ("-0.2962962962962963", .gt)
#guard D (P "-2/3" (X "2" 53) 53) == ("0.4444444444444444", .lt)
#guard D (P "2" (X "100" 53) 1) == ("1.0e30", .eq)

-- integer powers through the bracket
#guard D (P "3" (X "40" 20) 20) == ("1.215766e19", .lt)
#guard D (P "1/3" (X "40" 20) 20) == ("8.22527e-20", .gt)
#guard P "3" (X "40" 20) 20 == powPrecRound (X "3" 20) (X "40" 20) 20 .Nearest
#guard P "-3" (X "41" 20) 20 == powPrecRound (X "-3" 20) (X "41" 20) 20 .Nearest
#guard (P "2/3" (X "1000000000" 53) 10).2 == .lt

-- correctly rounded irrational powers
#guard D (P "2/3" (X "1.25" 53) 53) == ("0.6024013357398965", .lt)
#guard D (P "2/3" (X "1.25" 53) 53 .Ceiling) == ("0.6024013357398966", .gt)
#guard D (P "22/7" (X "-0.875" 53) 53) == ("0.36714780768758454", .gt)
#guard D (P "22/7" (X "-0.875" 53) 53 .Floor) == ("0.3671478076875845", .lt)
#guard D (P "1/3" (X "0.3333333333333333" 53) 53) == ("0.6933612743506348", .gt)
#guard D (P "1/3" (X "0.3333333333333333" 53) 53 .Floor) == ("0.6933612743506347", .lt)
#guard D (P "10" (X "0.5" 53) 53) == ("3.1622776601683795", .gt)
#guard toString (ratPowFloat (Q "1/3") third200 200)
  == "0.693361274350634704843352274785961795445935113457754036565864"
#guard P "3" (X "1.75" 53) 53 == powPrecRound (X "3" 53) (X "1.75" 53) 53 .Nearest
#guard P "3/2" (X "1.25" 53) 53 .Floor == powPrecRound (X "1.5" 53) (X "1.25" 53) 53 .Floor
#guard P "3/2" (X "-2.75" 53) 53 == powPrecRound (X "1.5" 53) (X "-2.75" 53) 53 .Nearest

-- tiny arguments: the value is `1 ± tiny`, with the boundary `1` next to it; one test decides
-- the rounding at a cost independent of the exponent (the Ziv loop needed about `|e|` bits)
private def tinyE : AzInt := AzInt.ofInt (-(2 ^ 30 : Int))
private def tinyX : AzFloat := (X "1" 53) <<< tinyE
private def aboveOne : AzFloat := X "1.0000000000000002" 53
private def belowOne : AzFloat := X "0.9999999999999999" 53
#guard D (ratPowPrecRound (Q "7/3") tinyX 53 .Nearest) == ("1.0", .lt)
#guard D (ratPowPrecRound (Q "7/3") tinyX 53 .Floor) == ("1.0", .lt)
#guard D (ratPowPrecRound (Q "7/3") tinyX 53 .Ceiling) == ("1.0000000000000002", .gt)
#guard D (ratPowPrecRound (Q "7/3") (-tinyX) 53 .Nearest) == ("1.0", .gt)
#guard D (ratPowPrecRound (Q "7/3") (-tinyX) 53 .Floor) == ("0.9999999999999999", .lt)
#guard D (ratPowPrecRound (Q "7/3") (-tinyX) 53 .Ceiling) == ("1.0", .gt)
#guard D (ratPowPrecRound (Q "3/7") tinyX 53 .Nearest) == ("1.0", .gt)

-- `(−1)^y` for a huge integer `y`: the parity from the exponent, without converting `y`
#guard D (P "-1" ((X "1" 1) <<< AzInt.ofInt (2 ^ 30)) 10) == ("1.0", .eq)
#guard D (P "-1" ((X "-1" 1) <<< AzInt.ofInt (2 ^ 30)) 10) == ("1.0", .eq)
#guard D (P "-1" (X "-7" 3) 10 .Floor) == ("-1.0", .eq)

-- huge exponents: the starting precision of Ziv's loop is logarithmic in the exponent of `y`
-- (`ratPowW₀` is an `lnMulW₀`); references from 700-digit decimal arithmetic
-- (`q^y = sig · 2^shift` with the 53-bit significand rounded to nearest)
private def hugeY : AzFloat := (X "3" 53) <<< AzInt.ofInt 200
private def sh (s : String) : AzInt := AzInt.ofInt (Q s).num.toNat
#guard P "10/3" hugeY 53 == ((X "8246119072952368" 53)
  <<< sh "8373588284503795037406635919271801218184159433932621801778476", .lt)
#guard P "10/3" (-hugeY) 53 == ((X "4919261879246654" 53)
  <<< (-sh "8373588284503795037406635919271801218184159433932621801778581"), .gt)
#guard P "7/9" hugeY 53 == ((X "4925387357126637" 53)
  <<< (-sh "1747882962819869796934539938187438995071985308497036263957224"), .gt)
#guard (P "10/3" hugeY 53 .Ceiling).2 == .gt && (P "10/3" (-hugeY) 53 .Floor).2 == .lt
#guard ratPowW₀ (AzInt.ofInt 202) (Q "10/3") == lnMulW₀ 216
#guard ratPowW₀ (AzInt.ofInt (2 ^ 40)) (Q "10/3") == 356
#guard ratPowW₀ (AzInt.ofInt (-5)) (Q "10/3") == 102
