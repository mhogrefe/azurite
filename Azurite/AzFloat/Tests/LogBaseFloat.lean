/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.Log2
import Azurite.AzFloat.LogBase
import Azurite.AzFloat.LogBaseFloat
import Azurite.AzFloat.LogBasePow2
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `log_b x` with a float base

The special-case table, exact cases (`x` and `b` integer powers of a common rational, including
odd integer bases and bases below `1`), agreement with the natural and power-of-two bases, and
`log₃ 7 = 1.77124374916142226006792830708245771806647133459424347936899257727988619870…`,
`log_{3/2} 2 = 1.70951129135145477697619026217401414061500373523610722307445390628771857790…`,
`log_{1 + 2^(−20)} 2 = 726817.84457636040637777306663695374104317457331197399796360761542…`,
`log_{1 − 2^(−20)} 2 = −726817.15142917984637992917538246799022410763591572310682221831516…`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def K (n : Int) : AzInt := AzInt.ofInt n
private def L (x b : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) :=
  logBaseFloatPrecRound x b p m
private def pinf : AzFloat := infinity true
private def ninf : AzFloat := infinity false
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values: `NaN`
#guard D (L nan (X "2" 53) 10) == ("NaN", .eq)
#guard D (L (X "2" 53) nan 10) == ("NaN", .eq)
#guard D (L (X "-2" 53) (X "2" 53) 10) == ("NaN", .eq)
#guard D (L (X "2" 53) (X "-2" 53) 10) == ("NaN", .eq)
#guard D (L ninf (X "2" 53) 10) == ("NaN", .eq)
#guard D (L (X "2" 53) ninf 10) == ("NaN", .eq)
#guard D (L pinf pinf 10) == ("NaN", .eq)
#guard D (L pinf zero 10) == ("NaN", .eq)
#guard D (L zero pinf 10) == ("NaN", .eq)
#guard D (L zero zero 10) == ("NaN", .eq)
#guard D (L one one 10) == ("NaN", .eq)
#guard D (L (X "8" 53) (X "2" 53) 0) == ("NaN", .eq) -- precision 0
-- `0` results
#guard D (L (X "2" 53) pinf 10) == ("0.0", .eq)
#guard D (L (X "2" 53) zero 10) == ("0.0", .eq)
#guard D (L one (X "10" 53) 10) == ("0.0", .eq)
#guard D (L one (X "0.1" 53) 10) == ("0.0", .eq)
#guard D (L one pinf 10) == ("0.0", .eq)
-- base `1`
#guard D (L (X "2" 53) one 10) == ("Infinity", .eq)
#guard D (L pinf one 10) == ("Infinity", .eq)
#guard D (L (X "0.5" 53) one 10) == ("-Infinity", .eq)
#guard D (L zero one 10) == ("-Infinity", .eq)
-- `x = ∞` and `x = 0`
#guard D (L pinf (X "2" 53) 10) == ("Infinity", .eq)
#guard D (L pinf (X "0.5" 53) 10) == ("-Infinity", .eq)
#guard D (L zero (X "2" 53) 10) == ("-Infinity", .eq)
#guard D (L zero (X "0.5" 53) 10) == ("Infinity", .eq)
#guard D (L zero (X "1.5" 53) 10) == ("-Infinity", .eq)

-- exact cases: a common rational root
#guard D (L (X "8" 53) (X "4" 53) 53) == ("1.5", .eq)
#guard D (L (X "4" 53) (X "8" 53) 53) == ("0.6666666666666666", .lt)
#guard D (L (X "4" 53) (X "8" 53) 53 .Floor) == ("0.6666666666666666", .lt)
#guard D (L (X "8" 53) (X "0.5" 53) 53) == ("-3.0", .eq)
#guard D (L (X "0.125" 53) (X "0.25" 53) 53) == ("1.5", .eq)
#guard D (L (X "0.125" 53) (X "4" 53) 53) == ("-1.5", .eq)
#guard D (L (X "27" 53) (X "9" 53) 53) == ("1.5", .eq) -- an odd integer base
#guard D (L (X "3" 53) (X "9" 53) 53) == ("0.5", .eq)
#guard D (L (X "243" 53) (X "3" 53) 53) == ("5.0", .eq)
#guard D (L (X "25" 53) (X "5" 53) 53) == ("2.0", .eq)
#guard D (L (X "9" 53) (X "27" 53) 53) == ("0.6666666666666666", .lt)
#guard D (L (X "2.25" 53) (X "1.5" 53) 53) == ("2.0", .eq)
#guard D (L (X "3.375" 53) (X "1.5" 53) 53) == ("3.0", .eq)
#guard D (L (X "1.5" 53) (X "2.25" 53) 53) == ("0.5", .eq)
#guard D (L (X "0.5625" 53) (X "0.75" 53) 53) == ("2.0", .eq)
#guard D (L (X "144" 53) (X "12" 53) 53) == ("2.0", .eq)
#guard D (L (X "12" 53) (X "144" 53) 53) == ("0.5", .eq)
#guard D (L (X "36" 53) (X "6" 53) 53) == ("2.0", .eq)
#guard D (L (X "1000" 53) (X "10" 53) 53) == ("3.0", .eq)
#guard D (L (X "10" 53) (X "1000" 53) 53) == ("0.3333333333333333", .lt)
#guard D (L (X "10" 53) (X "1000" 53) 53 .Up) == ("0.33333333333333337", .gt)
#guard D (L (X "1000" 53) (X "10" 53) 1) == ("4.0", .gt)
#guard D (L (X "1000" 53) (X "10" 53) 1 .Floor) == ("2.0", .lt)
#guard (L (X "0.001" 53) (X "10" 53) 53).2 != .eq            -- `1/1000` rounded is not exact
#guard toString ((L (X "0.001" 53) (X "10" 53) 20).1) == "-3.0"
#guard (L (X "2" 53) (X "10" 53) 53).2 != .eq
#guard (L (X "3" 53) (X "7" 53) 53).2 != .eq
#guard (L (X "27" 53) (X "1.5" 53) 53).2 != .eq

-- agreement with the natural and power-of-two bases
#guard L (X "2" 53) (X "10" 53) 150 == logBasePrecRound (X "2" 53) 10 150 .Nearest
#guard L (X "1.75" 53) (X "3" 53) 150 .Floor == logBasePrecRound (X "1.75" 53) 3 150 .Floor
#guard L (X "10" 53) (X "8" 53) 150 == logBasePow2PrecRound (X "10" 53) (K 3) 150 .Nearest
#guard L (X "10" 53) (X "0.125" 53) 150 == logBasePow2PrecRound (X "10" 53) (K (-3)) 150 .Nearest
#guard L (X "10" 53) (X "2" 53) 150 == log2PrecRound (X "10" 53) 150 .Nearest
#guard L (X "10" 53) (X "0.5" 53) 150 .Ceiling
  == logBasePow2PrecRound (X "10" 53) (K (-1)) 150 .Ceiling

-- `log₃ 7`
private def ref37 : AzRat :=
  Q ("177124374916142226006792830708245771806647133459424347936899257727988619870/1"
    ++ "".pushn '0' 74)
#guard toString ((L (X "7" 53) (X "3" 53) 150).1) == "1.7712437491614222600679283070824577180664713\
  35"
#guard toString ((L (X "7" 53) (X "3" 53) 150 .Floor).1) == "1.771243749161422260067928307082457718\
  066471333"
#guard toString ((L (X "7" 53) (X "3" 53) 150 .Ceiling).1) == "1.7712437491614222600679283070824577\
  18066471335"
-- `log_{3/2} 2`
private def ref32 : AzRat :=
  Q ("170951129135145477697619026217401414061500373523610722307445390628771857790/1"
    ++ "".pushn '0' 74)
#guard toString ((L (X "2" 53) (X "1.5" 53) 150).1) == "1.70951129135145477697619026217401414061500\
  3736"
#guard (L (X "2" 53) (X "0.6666666666666666" 53) 150).2 != .eq  -- `2/3` rounded, not exact
-- bases close to `1`: `ln b` is tiny, positive and negative
private def refUp : AzRat :=
  Q ("726817844576360406377773066636953741043174573311973997963607615425599651834/1"
    ++ "".pushn '0' 69)
private def refDown : AzRat :=
  Q ("-726817151429179846379929175382467990224107635915723106822218315163703350352/1"
    ++ "".pushn '0' 69)
#guard toString ((L (X "2" 53) (X "1.00000095367431640625" 53) 100).1) ==
    "726817.844576360406377773066637"
#guard toString ((L (X "2" 53) (X "0.99999904632568359375" 53) 100).1) ==
    "-726817.15142917984637992917538\
  3"
#guard toString ((L (X "2" 53) (X "1.00000095367431640625" 53) 100 .Floor).1) ==
    "726817.84457636040637777\
  3066637"
#guard toString ((L (X "0.5" 53) (X "1.00000095367431640625" 53) 100).1) ==
    "-726817.844576360406377773066\
  637"

-- default precision
#guard toString (logBaseFloat (X "8" 10) (X "4" 53)) == "1.5"
#guard toString (logBaseFloat (X "7" 53) (X "3" 53)) == "1.7712437491614224"
#guard logBaseFloat (X "2" 53) (X "10" 53) == logBase (X "2" 53) 10

-- exponents far beyond memory (`2^(±2^60)`): the exactness test asks whether the odd part is a
-- perfect `2^60`-th power, and `AzNat.rootInt` answers without computing `2^(2^60 − 1)`;
-- the work does not depend on the exponent
private def sh (r : AzFloat × Ordering) (k : Int) : AzFloat × Ordering := (r.1 <<< K k, r.2)
private def neg (r : AzFloat × Ordering) : AzFloat × Ordering := (-r.1, r.2.swap)
#guard L ((X "1" 53) <<< K (2 ^ 60)) (X "10" 53) 53 == sh (L (X "2" 53) (X "10" 53) 53) 60
#guard L ((X "1" 53) <<< K (-(2 ^ 60))) (X "10" 53) 53
  == neg (sh (L (X "2" 53) (X "10" 53) 53) 60)
#guard (L ((X "3" 53) <<< K (2 ^ 60)) (X "10" 53) 53).2 != .eq
#guard (L ((X "3" 53) <<< K (-(2 ^ 60))) (X "1.25" 53) 53).2 != .eq
#guard (L ((X "3" 53) <<< K (2 ^ 60)) ((X "5" 53) <<< K (2 ^ 57)) 53).2 != .eq
-- still exact with huge exponents: `log_{2^(2^57)} 2^(2^60) = 8`,
-- `log_{3·2^(2^57)} (9·2^(2^58)) = 2`
#guard L ((X "1" 53) <<< K (2 ^ 60)) ((X "1" 53) <<< K (2 ^ 57)) 53 == (X "8" 53, .eq)
#guard L ((X "9" 53) <<< K (2 ^ 58)) ((X "3" 53) <<< K (2 ^ 57)) 53 == (X "2" 53, .eq)

-- odd integers of many bits: multiplicative dependence by `mulDepExps` (divisions only, no
-- search for a primitive root over every exponent up to the bit length)
private def P (b e : Nat) : AzFloat := ofAzRat (AzNat.ofNat (b ^ e)).toAzRat 2000
#guard D (L (P 3 200) (P 3 300) 53) == ("0.6666666666666666", .lt)
#guard D (L (P 3 1000) (P 3 1) 53) == ("1.0e3", .eq)
#guard D (L (P 3 1) (P 3 1000) 53) == ("0.001", .gt)
#guard D (L (P 15 77) (P 15 121) 53) == ("0.6363636363636364", .lt)
#guard L (P 12345678901234567 30) (P 12345678901234567 18) 53
  == ofAzRatRound (Q "5/3") 53 .Nearest
#guard (L (ofAzRat (AzNat.ofNat (3 ^ 200 + 2)).toAzRat 2000) (P 3 300) 53).2 != .eq
#guard (L (P 3 200) (P 5 300) 53).2 != .eq
#guard mulDepExps 100 (AzNat.ofNat (3 ^ 20)) (AzNat.ofNat (3 ^ 12)) == some (5, 3)
#guard mulDepExps 100 (AzNat.ofNat (3 ^ 12)) (AzNat.ofNat (3 ^ 20)) == some (3, 5)
#guard mulDepExps 100 (AzNat.ofNat 1) (AzNat.ofNat 7) == some (0, 1)
#guard mulDepExps 100 (AzNat.ofNat 7) (AzNat.ofNat 7) == some (1, 1)
#guard mulDepExps 100 (AzNat.ofNat (6 ^ 9)) (AzNat.ofNat (6 ^ 4)) == some (9, 4)
#guard mulDepExps 100 (AzNat.ofNat (3 ^ 20)) (AzNat.ofNat (9 ^ 6 * 5)) == none
#guard mulDepExps 100 (AzNat.ofNat 12) (AzNat.ofNat 18) == none
