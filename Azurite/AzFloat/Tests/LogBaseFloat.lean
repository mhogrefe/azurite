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
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def K (n : Int) : AzInt := AzInt.ofInt n
private def L (x b : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) :=
  logBaseFloatPrecRound x b p m
private def pinf : AzFloat := infinity true
private def ninf : AzFloat := infinity false

-- special values: `NaN`
#guard L nan (F "2" 53) 10 == (nan, .eq)
#guard L (F "2" 53) nan 10 == (nan, .eq)
#guard L (F "-2" 53) (F "2" 53) 10 == (nan, .eq)
#guard L (F "2" 53) (F "-2" 53) 10 == (nan, .eq)
#guard L ninf (F "2" 53) 10 == (nan, .eq)
#guard L (F "2" 53) ninf 10 == (nan, .eq)
#guard L pinf pinf 10 == (nan, .eq)
#guard L pinf zero 10 == (nan, .eq)
#guard L zero pinf 10 == (nan, .eq)
#guard L zero zero 10 == (nan, .eq)
#guard L one one 10 == (nan, .eq)
#guard L (F "8" 53) (F "2" 53) 0 == (nan, .eq)               -- precision 0
-- `0` results
#guard L (F "2" 53) pinf 10 == (zero, .eq)
#guard L (F "2" 53) zero 10 == (zero, .eq)
#guard L one (F "10" 53) 10 == (zero, .eq)
#guard L one (F "1/10" 53) 10 == (zero, .eq)
#guard L one pinf 10 == (zero, .eq)
-- base `1`
#guard L (F "2" 53) one 10 == (infinity true, .eq)
#guard L pinf one 10 == (infinity true, .eq)
#guard L (F "1/2" 53) one 10 == (infinity false, .eq)
#guard L zero one 10 == (infinity false, .eq)
-- `x = ∞` and `x = 0`
#guard L pinf (F "2" 53) 10 == (infinity true, .eq)
#guard L pinf (F "1/2" 53) 10 == (infinity false, .eq)
#guard L zero (F "2" 53) 10 == (infinity false, .eq)
#guard L zero (F "1/2" 53) 10 == (infinity true, .eq)
#guard L zero (F "3/2" 53) 10 == (infinity false, .eq)

-- exact cases: a common rational root
#guard L (F "8" 53) (F "4" 53) 53 == (F "3/2" 53, .eq)
#guard L (F "4" 53) (F "8" 53) 53 == ofAzRatRound (Q "2/3") 53 .Nearest
#guard L (F "4" 53) (F "8" 53) 53 .Floor == ofAzRatRound (Q "2/3") 53 .Floor
#guard L (F "8" 53) (F "1/2" 53) 53 == (F "-3" 53, .eq)
#guard L (F "1/8" 53) (F "1/4" 53) 53 == (F "3/2" 53, .eq)
#guard L (F "1/8" 53) (F "4" 53) 53 == (F "-3/2" 53, .eq)
#guard L (F "27" 53) (F "9" 53) 53 == (F "3/2" 53, .eq)        -- an odd integer base
#guard L (F "3" 53) (F "9" 53) 53 == (F "1/2" 53, .eq)
#guard L (F "243" 53) (F "3" 53) 53 == (F "5" 53, .eq)
#guard L (F "25" 53) (F "5" 53) 53 == (F "2" 53, .eq)
#guard L (F "9" 53) (F "27" 53) 53 == ofAzRatRound (Q "2/3") 53 .Nearest
#guard L (F "9/4" 53) (F "3/2" 53) 53 == (F "2" 53, .eq)
#guard L (F "27/8" 53) (F "3/2" 53) 53 == (F "3" 53, .eq)
#guard L (F "3/2" 53) (F "9/4" 53) 53 == (F "1/2" 53, .eq)
#guard L (F "9/16" 53) (F "3/4" 53) 53 == (F "2" 53, .eq)
#guard L (F "144" 53) (F "12" 53) 53 == (F "2" 53, .eq)
#guard L (F "12" 53) (F "144" 53) 53 == (F "1/2" 53, .eq)
#guard L (F "36" 53) (F "6" 53) 53 == (F "2" 53, .eq)
#guard L (F "1000" 53) (F "10" 53) 53 == (F "3" 53, .eq)
#guard L (F "10" 53) (F "1000" 53) 53 == ofAzRatRound (Q "1/3") 53 .Nearest
#guard L (F "10" 53) (F "1000" 53) 53 .Up == ofAzRatRound (Q "1/3") 53 .Up
#guard L (F "1000" 53) (F "10" 53) 1 == (F "4" 1, .gt)
#guard L (F "1000" 53) (F "10" 53) 1 .Floor == (F "2" 1, .lt)
#guard (L (F "1/1000" 53) (F "10" 53) 53).2 != .eq            -- `1/1000` rounded is not exact
#guard (L (F "1/1000" 53) (F "10" 53) 20).1 == F "-3" 20
#guard (L (F "2" 53) (F "10" 53) 53).2 != .eq
#guard (L (F "3" 53) (F "7" 53) 53).2 != .eq
#guard (L (F "27" 53) (F "3/2" 53) 53).2 != .eq

-- agreement with the natural and power-of-two bases
#guard L (F "2" 53) (F "10" 53) 150 == logBasePrecRound (F "2" 53) 10 150 .Nearest
#guard L (F "7/4" 53) (F "3" 53) 150 .Floor == logBasePrecRound (F "7/4" 53) 3 150 .Floor
#guard L (F "10" 53) (F "8" 53) 150 == logBasePow2PrecRound (F "10" 53) (K 3) 150 .Nearest
#guard L (F "10" 53) (F "1/8" 53) 150 == logBasePow2PrecRound (F "10" 53) (K (-3)) 150 .Nearest
#guard L (F "10" 53) (F "2" 53) 150 == log2PrecRound (F "10" 53) 150 .Nearest
#guard L (F "10" 53) (F "1/2" 53) 150 .Ceiling
  == logBasePow2PrecRound (F "10" 53) (K (-1)) 150 .Ceiling

-- `log₃ 7`
private def ref37 : AzRat :=
  Q ("177124374916142226006792830708245771806647133459424347936899257727988619870/1"
    ++ "".pushn '0' 74)
#guard (L (F "7" 53) (F "3" 53) 150).1 == ofAzRat ref37 150
#guard (L (F "7" 53) (F "3" 53) 150 .Floor).1 == (ofAzRatRound ref37 150 .Floor).1
#guard (L (F "7" 53) (F "3" 53) 150 .Ceiling).1 == (ofAzRatRound ref37 150 .Ceiling).1
-- `log_{3/2} 2`
private def ref32 : AzRat :=
  Q ("170951129135145477697619026217401414061500373523610722307445390628771857790/1"
    ++ "".pushn '0' 74)
#guard (L (F "2" 53) (F "3/2" 53) 150).1 == ofAzRat ref32 150
#guard (L (F "2" 53) (F "2/3" 53) 150).2 != .eq               -- `2/3` rounded, not exact
-- bases close to `1`: `ln b` is tiny, positive and negative
private def refUp : AzRat :=
  Q ("726817844576360406377773066636953741043174573311973997963607615425599651834/1"
    ++ "".pushn '0' 69)
private def refDown : AzRat :=
  Q ("-726817151429179846379929175382467990224107635915723106822218315163703350352/1"
    ++ "".pushn '0' 69)
#guard (L (F "2" 53) (F "1048577/1048576" 53) 100).1 == ofAzRat refUp 100
#guard (L (F "2" 53) (F "1048575/1048576" 53) 100).1 == ofAzRat refDown 100
#guard (L (F "2" 53) (F "1048577/1048576" 53) 100 .Floor).1 == (ofAzRatRound refUp 100 .Floor).1
#guard (L (F "1/2" 53) (F "1048577/1048576" 53) 100).1 == ofAzRat (-refUp) 100

-- default precision
#guard logBaseFloat (F "8" 10) (F "4" 53) == F "3/2" 10
#guard logBaseFloat (F "7" 53) (F "3" 53) == ofAzRat ref37 53
#guard logBaseFloat (F "2" 53) (F "10" 53) == logBase (F "2" 53) 10
