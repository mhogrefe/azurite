/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.LogBaseP1
import Azurite.AzFloat.LogBasePow2P1
import Azurite.AzFloat.LogBaseRatBaseP1
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse
import Azurite.AzFloat.OfString

/-!
# Tests for `log_b (1 + x)` with a rational base

Special values, exact cases (including bases with odd denominators), agreement with the natural,
power-of-two and float-base `log_b (1 + x)` and with `log_b` on the exact `1 + x`, and
`log₃ (1 + 6) = 1.7712437491614222600679283070824577180664713345942434793689925…`,
`log_{3/2} (1 + 1) = 1.7095112913514547769761902621740141406150037352361072230744539…`,
`log₁₀ (1 + 2^(−30)) = 4.0446825483908662596994682583423467366992942764363982162…·10^(−10)`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def K (n : Int) : AzInt := AzInt.ofInt n
private def L (x : AzFloat) (b : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  logBaseRatBaseP1PrecRound x (Q b) p m
private def pinf : AzFloat := infinity true
private def ninf : AzFloat := infinity false
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (L nan "2" 10) == ("NaN", .eq)
#guard D (L (X "1" 53) "-2" 10) == ("NaN", .eq)
#guard D (L ninf "2" 10) == ("NaN", .eq)
#guard D (L (X "-2" 53) "2" 10) == ("NaN", .eq) -- `1 + x < 0`
#guard D (L (X "-1.5" 53) "2/3" 10) == ("NaN", .eq)
#guard D (L (X "1" 53) "2" 0) == ("NaN", .eq) -- precision 0
-- base `0` and base `1`
#guard D (L (X "1" 53) "0" 10) == ("0.0", .eq)
#guard D (L pinf "0" 10) == ("NaN", .eq)
#guard D (L (X "-1" 53) "0" 10) == ("NaN", .eq)
#guard D (L (X "1" 53) "1" 10) == ("Infinity", .eq)
#guard D (L (X "-0.5" 53) "1" 10) == ("-Infinity", .eq)
#guard D (L zero "1" 10) == ("NaN", .eq)
#guard D (L pinf "1" 10) == ("Infinity", .eq)
-- `x = ∞`, `x = 0`, `x = −1`
#guard D (L pinf "2" 10) == ("Infinity", .eq)
#guard D (L pinf "2/3" 10) == ("-Infinity", .eq)
#guard D (L zero "2" 10) == ("0.0", .eq)
#guard D (L zero "2/3" 10) == ("0.0", .eq)
#guard D (L (X "-1" 53) "2" 10) == ("-Infinity", .eq)
#guard D (L (X "-1" 53) "2/3" 10) == ("Infinity", .eq)

-- exact cases
#guard D (L (X "7" 53) "4" 53) == ("1.5", .eq)
#guard D (L (X "7" 53) "1/2" 53) == ("-3.0", .eq)
#guard D (L (X "-0.875" 53) "1/4" 53) == ("1.5", .eq)
#guard D (L (X "26" 53) "9" 53) == ("1.5", .eq)
#guard D (L (X "26" 53) "1/3" 53) == ("-3.0", .eq) -- an odd denominator
#guard D (L (X "2" 53) "1/9" 53) == ("-0.5", .eq)
#guard D (L (X "1.25" 53) "3/2" 53) == ("2.0", .eq) -- `9/4`
#guard D (L (X "1.25" 53) "2/3" 53) == ("-2.0", .eq)
#guard D (L (X "2.375" 53) "2/3" 53) == ("-3.0", .eq) -- `27/8`
#guard D (L (X "0.5" 53) "4/9" 53) == ("-0.5", .eq) -- `3/2`
#guard D (L (X "-0.4375" 53) "3/4" 53) == ("2.0", .eq) -- `9/16`
#guard D (L (X "999" 53) "10" 53) == ("3.0", .eq)
#guard D (L (X "999" 53) "1/10" 53) == ("-3.0", .eq)
#guard D (L (X "9" 53) "1000" 53) == ("0.3333333333333333", .lt)
#guard D (L (X "9" 53) "1/1000" 53 .Floor) == ("-0.33333333333333337", .lt)
#guard D (L (X "999" 53) "10" 1) == ("4.0", .gt)
#guard (L (X "3" 53) "2/3" 53).2 != .eq                       -- `n, d > 1`: never exact
#guard (L (X "1" 53) "10" 53).2 != .eq
#guard (L (X "-0.5" 53) "3" 53).2 != .eq

-- agreement with the natural, power-of-two and float-base `log_b (1 + x)`, and with `log_b`
#guard L (X "1" 53) "10" 150 == logBaseP1PrecRound (X "1" 53) 10 150 .Nearest
#guard L (X "-0.5" 53) "10" 150 .Floor == logBaseP1PrecRound (X "-0.5" 53) 10 150 .Floor
#guard L (X "9" 53) "8" 150 == logBasePow2P1PrecRound (X "9" 53) (K 3) 150 .Nearest
#guard L (X "9" 53) "1/8" 150 .Up == logBasePow2P1PrecRound (X "9" 53) (K (-3)) 150 .Up
#guard L (X "9" 53) "3/2" 150 == logBaseFloatP1PrecRound (X "9" 53) (X "1.5" 53) 150 .Nearest
#guard L (X "9" 53) "3/2" 150 .Ceiling == logBaseRatBasePrecRound (X "10" 53) (Q "3/2") 150 .Ceiling
#guard L (X "-0.375" 53) "2/3" 150 == logBaseRatBasePrecRound (X "0.625" 53) (Q "2/3") 150 .Nearest

-- `log₃ (1 + 6)`
private def ref37 : AzRat :=
  Q ("177124374916142226006792830708245771806647133459424347936899257727988619870/1"
    ++ "".pushn '0' 74)
#guard toString (L (X "6" 53) "3" 150).1 == "1.771243749161422260067928307082457718066471335"
#guard toString (L (X "6" 53) "1/3" 150).1 == "-1.771243749161422260067928307082457718066471335"
#guard toString (L (X "6" 53) "3" 150 .Floor).1 == "1.771243749161422260067928307082457718066471333"
-- `log_{3/2} (1 + 1)`
private def ref32 : AzRat :=
  Q ("170951129135145477697619026217401414061500373523610722307445390628771857790/1"
    ++ "".pushn '0' 74)
#guard toString (L (X "1" 53) "3/2" 150).1 == "1.709511291351454776976190262174014140615003736"
#guard toString (L (X "1" 53) "2/3" 150).1 == "-1.709511291351454776976190262174014140615003736"
#guard toString (L (X "1" 53) "2/3" 150 .Ceiling).1
  == "-1.709511291351454776976190262174014140615003734"
-- a base close to `1`
private def refUp : AzRat :=
  Q ("726817844576360406377773066636953741043174573311973997963607615425599651834/1"
    ++ "".pushn '0' 69)
#guard toString (L (X "1" 53) "1048577/1048576" 100).1 == "726817.844576360406377773066637"
#guard toString (L (X "-0.5" 53) "1048577/1048576" 100).1 == "-726817.844576360406377773066637"
-- a tiny argument: `log₁₀ (1 + 2^(−30))`
private def refTiny : AzRat :=
  Q ("4044682548390866259699468258342346736699294276436398216273/1"
    ++ "".pushn '0' 67)
#guard toString (L (X "0.000000000931322574615478515625\
  " 53) "10" 100).1 == "4.044682548390866259699468258343e-10"
#guard toString (L (X "0.000000000931322574615478515625\
  " 53) "1/10" 100).1 == "-4.044682548390866259699468258343e-10"

-- default precision
#guard toString (logBaseRatBaseP1 (X "7" 10) (Q "4")) == "1.5"
#guard toString (logBaseRatBaseP1 (X "6" 53) (Q "3")) == "1.7712437491614224"
#guard logBaseRatBaseP1 (X "1" 53) (Q "10") == logBaseP1 (X "1" 53) 10

-- tiny arguments: the cost does not depend on the exponent (`2^(−2^30)` is immediate)
private def tinyE : AzInt := AzInt.ofInt (-(2 ^ 30 : Int))
private def tinyX : AzFloat := (X "1" 53) <<< tinyE
#guard L tinyX "10" 53 == logBaseP1PrecRound tinyX 10 53 .Nearest

-- a huge power of two, `x = 2^K` with `K = 2^30 − 98`: `log₂ (1 + x) = K + ε`, `ε ≈ 2^(−K)`;
-- the side of `K` is decided without `K` bits of working precision
private def bigX : AzFloat := (X "1" 52) <<< AzInt.ofInt (2 ^ 30 - 98)
#guard D (L bigX "2" 52) == ("1073741726.0", .lt)
#guard D (L bigX "1/2" 52) == ("-1073741726.0", .gt)
#guard D (L bigX "1/4" 52 .Ceiling) == ("-536870863.0", .gt)

-- huge integers with a base that is not a power of two
private def bigY : AzFloat := (X "3" 52) <<< AzInt.ofInt (2 ^ 30)
#guard L bigX "10" 52 == logBaseP1PrecRound bigX 10 52 .Nearest
#guard (L bigX "3/2" 52).2 == .lt
#guard (L bigY "1/10" 52).2 == .lt

-- exponents far beyond memory (`x = 3·2^(±2^60)`): `onePlusSkip` settles the exactness test
-- without building `1 + x`
private def vastX : AzFloat := (X "3" 53) <<< K (2 ^ 60)
private def weeX : AzFloat := (X "3" 53) <<< K (-(2 ^ 60))
#guard L vastX "10" 53 == logBaseP1PrecRound vastX 10 53 .Nearest
#guard L vastX "3" 53 == logBaseP1PrecRound vastX 3 53 .Nearest
#guard (L vastX "10/3" 53).2 != .eq
#guard (L vastX "1/3" 53).2 != .eq
#guard L weeX "10" 53 == logBaseP1PrecRound weeX 10 53 .Nearest
#guard L (-weeX) "3" 53 == logBaseP1PrecRound (-weeX) 3 53 .Nearest
#guard (L weeX "10/3" 53).2 != .eq
#guard (L weeX "1/2" 53).2 != .eq
#guard (L (-weeX) "1/4" 53).2 != .eq
#guard (L ((X "1" 53) <<< K (-(2 ^ 60))) "1/2" 53).2 != .eq
#guard (L (-weeX) "1/3" 53).2 != .eq
#guard (L weeX "3/4" 53).2 != .eq
-- exact values survive the cheap test: `1 + x = b^(±1)`, `b^(±2)` with `b = 1 + 2^(−64)`
private def bS : String := "18446744073709551617/18446744073709551616"
private def x₁ : AzFloat :=
  X "5.42101086242752217003726400434970855712890625e-20" 200
private def x₂ : AzFloat :=
  X "1.084202172485504434036840159640498899124999663430556141945467e-19" 200
#guard D (L x₁ bS 53) == ("1.0", .eq)
#guard D (L x₂ bS 53) == ("2.0", .eq)
#guard D (L x₁ "18446744073709551616/18446744073709551617" 53) == ("-1.0", .eq)
#guard D (L x₂ "18446744073709551616/18446744073709551617" 53) == ("-2.0", .eq)
#guard (L x₁ "18446744073709551615/18446744073709551616" 53).2 != .eq
