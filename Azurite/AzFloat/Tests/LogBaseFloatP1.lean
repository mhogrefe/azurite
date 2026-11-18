/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.LogBaseFloatP1
import Azurite.AzFloat.LogBaseP1
import Azurite.AzFloat.LogBasePow2P1
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `log_b (1 + x)` with a float base

Special values (the table of `log_b` at `1 + x`), exact cases, agreement with `log_b (1 + x)` for
natural and power-of-two bases and with `log_b` on the exact `1 + x`, and
`log₃ (1 + 6) = 1.7712437491614222600679283070824577180664713345942434793689925…`,
`log_{3/2} (1 + 1) = 1.7095112913514547769761902621740141406150037352361072230744539…`,
`log_{1 + 2^(−20)} (1 + 1) = 726817.84457636040637777306663695374104317457331197399796360…`,
`log₁₀ (1 + 2^(−30)) = 4.0446825483908662596994682583423467366992942764363982162…·10^(−10)`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def K (n : Int) : AzInt := AzInt.ofInt n
private def L (x b : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) :=
  logBaseFloatP1PrecRound x b p m
private def pinf : AzFloat := infinity true
private def ninf : AzFloat := infinity false
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (L nan (X "2" 53) 10) == ("NaN", .eq)
#guard D (L (X "1" 53) nan 10) == ("NaN", .eq)
#guard D (L ninf (X "2" 53) 10) == ("NaN", .eq)
#guard D (L (X "1" 53) ninf 10) == ("NaN", .eq)
#guard D (L (X "1" 53) (X "-2" 53) 10) == ("NaN", .eq)
#guard D (L (X "-2" 53) (X "2" 53) 10) == ("NaN", .eq) -- `1 + x < 0`
#guard D (L (X "-1.5" 53) (X "2" 53) 10) == ("NaN", .eq)
#guard D (L (X "1" 53) (X "2" 53) 0) == ("NaN", .eq) -- precision 0
-- `x = ∞`: `log_b ∞`
#guard D (L pinf (X "2" 53) 10) == ("Infinity", .eq)
#guard D (L pinf (X "0.5" 53) 10) == ("-Infinity", .eq)
#guard D (L pinf one 10) == ("Infinity", .eq)
#guard D (L pinf pinf 10) == ("NaN", .eq)
#guard D (L pinf zero 10) == ("NaN", .eq)
-- `x = 0`: `log_b 1`
#guard D (L zero (X "2" 53) 10) == ("0.0", .eq)
#guard D (L zero (X "0.5" 53) 10) == ("0.0", .eq)
#guard D (L zero pinf 10) == ("0.0", .eq)
#guard D (L zero zero 10) == ("0.0", .eq)
#guard D (L zero one 10) == ("NaN", .eq)
-- `x = −1`: `log_b 0`
#guard D (L (X "-1" 53) (X "2" 53) 10) == ("-Infinity", .eq)
#guard D (L (X "-1" 53) (X "0.5" 53) 10) == ("Infinity", .eq)
#guard D (L (X "-1" 53) one 10) == ("-Infinity", .eq)
#guard D (L (X "-1" 53) pinf 10) == ("NaN", .eq)
#guard D (L (X "-1" 53) zero 10) == ("NaN", .eq)
-- base `1`, `∞`, `0` with finite `1 + x ≠ 1`
#guard D (L (X "1" 53) one 10) == ("Infinity", .eq)
#guard D (L (X "-0.5" 53) one 10) == ("-Infinity", .eq)
#guard D (L (X "1" 53) pinf 10) == ("0.0", .eq)
#guard D (L (X "-0.5" 53) zero 10) == ("0.0", .eq)

-- exact cases: `1 + x` and `b` integer powers of a common rational
#guard D (L (X "7" 53) (X "4" 53) 53) == ("1.5", .eq)
#guard D (L (X "3" 53) (X "8" 53) 53) == ("0.6666666666666666", .lt)
#guard D (L (X "7" 53) (X "0.5" 53) 53) == ("-3.0", .eq)
#guard D (L (X "-0.875" 53) (X "0.25" 53) 53) == ("1.5", .eq)
#guard D (L (X "-0.875" 53) (X "4" 53) 53) == ("-1.5", .eq)
#guard D (L (X "26" 53) (X "9" 53) 53) == ("1.5", .eq) -- an odd integer base
#guard D (L (X "2" 53) (X "9" 53) 53) == ("0.5", .eq)
#guard D (L (X "242" 53) (X "3" 53) 53) == ("5.0", .eq)
#guard D (L (X "24" 53) (X "5" 53) 53) == ("2.0", .eq)
#guard D (L (X "1.25" 53) (X "1.5" 53) 53) == ("2.0", .eq) -- `9/4`
#guard D (L (X "2.375" 53) (X "1.5" 53) 53) == ("3.0", .eq) -- `27/8`
#guard D (L (X "0.5" 53) (X "2.25" 53) 53) == ("0.5", .eq) -- `3/2`
#guard D (L (X "-0.4375" 53) (X "0.75" 53) 53) == ("2.0", .eq) -- `9/16`
#guard D (L (X "143" 53) (X "12" 53) 53) == ("2.0", .eq)
#guard D (L (X "999" 53) (X "10" 53) 53) == ("3.0", .eq)
#guard D (L (X "9" 53) (X "1000" 53) 53) == ("0.3333333333333333", .lt)
#guard D (L (X "9" 53) (X "1000" 53) 53 .Up) == ("0.33333333333333337", .gt)
#guard D (L (X "999" 53) (X "10" 53) 1) == ("4.0", .gt)
#guard D (L (X "1" 53) (X "2" 53) 53) == ("1.0", .eq)
#guard (L (X "1" 53) (X "10" 53) 53).2 != .eq
#guard (L (X "0.5" 53) (X "10" 53) 53).2 != .eq
#guard (L (X "-0.5" 53) (X "3" 53) 53).2 != .eq

-- agreement with the natural and power-of-two bases, and with `log_b` on the exact `1 + x`
#guard L (X "1" 53) (X "10" 53) 150 == logBaseP1PrecRound (X "1" 53) 10 150 .Nearest
#guard L (X "-0.5" 53) (X "10" 53) 150 .Floor == logBaseP1PrecRound (X "-0.5" 53) 10 150 .Floor
#guard L (X "0.000000000931322574615478515625" 53) (X "10" 53) 100
  == logBaseP1PrecRound (X "0.000000000931322574615478515625" 53) 10 100 .Nearest
#guard L (X "9" 53) (X "8" 53) 150 == logBasePow2P1PrecRound (X "9" 53) (K 3) 150 .Nearest
#guard L (X "9" 53) (X "0.125" 53) 150 .Ceiling
  == logBasePow2P1PrecRound (X "9" 53) (K (-3)) 150 .Ceiling
#guard L (X "9" 53) (X "1.5" 53) 150 == logBaseFloatPrecRound (X "10" 53) (X "1.5" 53) 150 .Nearest
#guard L (X "-0.375" 53) (X "2.25" 53) 150 .Up
  == logBaseFloatPrecRound (X "0.625" 53) (X "2.25" 53) 150 .Up

-- `log₃ (1 + 6)`
private def ref37 : AzRat :=
  Q ("177124374916142226006792830708245771806647133459424347936899257727988619870/1"
    ++ "".pushn '0' 74)
#guard toString ((L (X "6" 53) (X "3" 53) 150).1) == "1.7712437491614222600679283070824577180664713\
  35"
#guard toString ((L (X "6" 53) (X "3" 53) 150 .Floor).1) == "1.771243749161422260067928307082457718\
  066471333"
-- `log_{3/2} (1 + 1)`
private def ref32 : AzRat :=
  Q ("170951129135145477697619026217401414061500373523610722307445390628771857790/1"
    ++ "".pushn '0' 74)
#guard toString ((L (X "1" 53) (X "1.5" 53) 150).1) == "1.70951129135145477697619026217401414061500\
  3736"
#guard toString ((L (X "1" 53) (X "1.5" 53) 150 .Ceiling).1) == "1.70951129135145477697619026217401\
  4140615003736"
-- a base close to `1`
private def refUp : AzRat :=
  Q ("726817844576360406377773066636953741043174573311973997963607615425599651834/1"
    ++ "".pushn '0' 69)
#guard toString ((L (X "1" 53) (X "1.00000095367431640625" 53) 100).1) ==
    "726817.844576360406377773066637"
#guard toString ((L (X "-0.5" 53) (X "1.00000095367431640625" 53) 100).1) ==
    "-726817.84457636040637777306\
  6637"
-- a tiny argument: `log₁₀ (1 + 2^(−30))`
private def refTiny : AzRat :=
  Q ("4044682548390866259699468258342346736699294276436398216273/1"
    ++ "".pushn '0' 67)
#guard toString ((L (X "0.000000000931322574615478515625" 53) (X "10" 53) 100).1) ==
    "4.044682548390866259699468258343e\
  -10"
#guard (L (X "-0.000000000931322574615478515625" 53) (X "10" 53) 60).2 != .eq

-- default precision
#guard toString (logBaseFloatP1 (X "7" 10) (X "4" 53)) == "1.5"
#guard toString (logBaseFloatP1 (X "6" 53) (X "3" 53)) == "1.7712437491614224"
#guard logBaseFloatP1 (X "1" 53) (X "10" 53) == logBaseP1 (X "1" 53) 10

-- tiny arguments: the cost does not depend on the exponent (`2^(−2^30)` is immediate)
private def tinyE : AzInt := AzInt.ofInt (-(2 ^ 30 : Int))
private def tinyX : AzFloat := (X "1" 53) <<< tinyE
#guard L tinyX (X "10" 53) 53 == logBaseP1PrecRound tinyX 10 53 .Nearest

-- a huge power of two, `x = 2^K` with `K = 2^30 − 98`: `log₂ (1 + x) = K + ε`, `ε ≈ 2^(−K)`;
-- the side of `K` is decided without `K` bits of working precision
private def bigX : AzFloat := (X "1" 52) <<< AzInt.ofInt (2 ^ 30 - 98)
#guard L bigX (X "2" 53) 52 == (X "1073741726" 52, .lt)
#guard L bigX (X "0.5" 53) 52 == (X "-1073741726" 52, .gt)
#guard L bigX (X "4" 53) 52 .Floor == (X "536870863" 52, .lt)

-- huge integers with a base that is not a power of two
private def bigY : AzFloat := (X "3" 52) <<< AzInt.ofInt (2 ^ 30)
#guard L bigX (X "10" 53) 52 == logBaseP1PrecRound bigX 10 52 .Nearest
#guard (L bigX (X "6" 53) 52).2 == .lt
#guard (L bigY (X "0.75" 53) 52).2 == .lt

-- exponents far beyond memory (`x = 3·2^(±2^60)`): `onePlusSkip` settles the exactness test
-- without building `1 + x`; the work does not depend on the exponent
private def vastX : AzFloat := (X "3" 53) <<< K (2 ^ 60)
private def weeX : AzFloat := (X "3" 53) <<< K (-(2 ^ 60))
#guard L vastX (X "10" 53) 53 == logBaseP1PrecRound vastX 10 53 .Nearest
#guard L vastX (X "3" 53) 53 == logBaseP1PrecRound vastX 3 53 .Nearest
#guard (L vastX ((X "5" 53) <<< K (2 ^ 57)) 53).2 != .eq
#guard L weeX (X "10" 53) 53 == logBaseP1PrecRound weeX 10 53 .Nearest
#guard L weeX (X "3" 53) 53 == logBaseP1PrecRound weeX 3 53 .Nearest
#guard L (-weeX) (X "10" 53) 53 == logBaseP1PrecRound (-weeX) 10 53 .Nearest
#guard (L weeX ((X "5" 53) <<< K (-(2 ^ 57))) 53).2 != .eq
#guard (L (-weeX) (X "0.75" 53) 53).2 != .eq
-- a tiny `x` and a power-of-two base below `1` (the exponent quotient is positive, the odd
-- root of the base is `1`): no exact value, and `1 + x` is not built
#guard (L weeX (X "0.5" 53) 53).2 != .eq
#guard (L weeX (X "0.25" 53) 53).2 != .eq
#guard (L (-weeX) (X "0.5" 53) 53).2 != .eq
#guard (L ((X "1" 53) <<< K (-(2 ^ 60))) (X "0.5" 53) 53).2 != .eq
#guard (L ((X "1" 53) <<< K (-(2 ^ 60))) (X "2" 53) 53).2 != .eq
#guard L ((X "1" 1) <<< K (1 - 2 ^ 30)) (X "0.5" 1) 17 ==
  ((X "-189096" 17) <<< K (-16 - 2 ^ 30), .gt)
-- the cheap test does not hide exact values: `1 + x = b`, `b²`, `b³` with
-- `b = 1 ± 2^(−64)`, where the residues modulo `2^64` agree
private def bP : AzFloat := X "1.00000000000000000005" 65
private def bM : AzFloat := X "0.99999999999999999995" 64
private def p1 : AzFloat :=
  F ("1/18446744073709551616") 200
private def n1 : AzFloat :=
  F ("-1/18446744073709551616") 200
private def p2 : AzFloat :=
  F ("36893488147419103233/340282366920938463463374607431768211456") 200
private def n2 : AzFloat :=
  F ("-36893488147419103231/340282366920938463463374607431768211456") 200
private def n3 : AzFloat :=
  F ("-1020847100762815390334783590074175979521/62771017353866807638357894232076664161"
    ++ "02355444464034512896") 200
private def bp2 : AzFloat :=
  F ("340282366920938463500268095579187314689/340282366920938463463374607431768211456") 200
private def bn2 : AzFloat :=
  F ("340282366920938463426481119284349108225/340282366920938463463374607431768211456") 200
#guard D (L p1 bP 53) == ("1.0", .eq)
#guard D (L n1 bM 53) == ("1.0", .eq)
#guard D (L p2 bP 53) == ("2.0", .eq)
#guard D (L n2 bM 53) == ("2.0", .eq)
#guard D (L p1 bp2 53) == ("0.5", .eq)
#guard D (L n3 bn2 53) == ("1.5", .eq)
#guard (L p1 bM 53).2 != .eq
#guard (L p2 (X "3" 53) 53).2 != .eq

-- the pieces
#guard upow64 3 0 == 1
#guard upow64 3 40 == 12157665459056928801
#guard upow64 3 41 == (3 ^ 41 % 2 ^ 64 : Nat).toUInt64
#guard upow64 18446744073709551615 (2 ^ 60 + 1) == 18446744073709551615
#guard onePlusSkip true (K (2 ^ 60)) 3 (K 1) 5
#guard onePlusSkip true (K (2 ^ 60)) 3 (K 0) 3
#guard !onePlusSkip true (K 4) 5 (K 0) 3
#guard onePlusSkip true (K (-(2 ^ 60))) 3 (K 0) 3
#guard onePlusSkip false (K (-(2 ^ 60))) 3 (K (-2)) 3
#guard onePlusSkip true (K (-(2 ^ 60))) 3 (K 2) 3
#guard onePlusSkip true (K (-(2 ^ 60))) 1 (K (-1)) 1
#guard onePlusSkip false (K (-(2 ^ 60))) 3 (K (-2)) 1
#guard !onePlusSkip true (K (-64)) 1 (K (-64)) (AzNat.ofNat (2 ^ 64 + 1))
#guard !onePlusSkip true (K (-10)) 1 (K (-2)) 3
