/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Log2
import Azurite.AzFloat.Log2P1
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse
import Azurite.AzFloat.Ln
import Azurite.AzFloat.OfString

/-!
# Tests for `log₂ (1 + x)`

Exact cases `1 + x = 2^k` (`x = 1, 3, 7, −1/2, −3/4, −7/8`), then
`log₂ (1 + 2^(−30)) = 1.34361445924002321236225895697999546585367009927398877…·10^(−9)`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard toString (log2P1 nan) == "NaN"
#guard toString (log2P1 (infinity true)) == "Infinity"
#guard toString (log2P1 (infinity false)) == "NaN"
#guard toString (log2P1 zero) == "0.0"
#guard toString (log2P1 (X "-1" 53)) == "-Infinity"
#guard toString (log2P1 (X "-2" 53)) == "NaN"
#guard toString (log2P1 (X "-1.5" 53)) == "NaN"

-- exact powers of two
#guard D (log2P1PrecRound (X "1" 53) 53 .Nearest) == ("1.0", .eq)
#guard D (log2P1PrecRound (X "3" 53) 53 .Nearest) == ("2.0", .eq)
#guard D (log2P1PrecRound (X "7" 53) 53 .Floor) == ("3.0", .eq)
#guard D (log2P1PrecRound (X "-0.5" 53) 53 .Nearest) == ("-1.0", .eq)
#guard D (log2P1PrecRound (X "-0.75" 53) 53 .Ceiling) == ("-2.0", .eq)
#guard D (log2P1PrecRound (X "-0.875" 53) 53 .Nearest) == ("-3.0", .eq)
#guard D (log2P1PrecRound (X "1267650600228229401496703205375" 110) 110 .Nearest) == ("1.0e2", .eq)

-- agreement with `log2` on exactly representable sums
#guard log2P1 (X "9" 53) == log2 (X "10" 53)
#guard log2P1 (X "2" 53) == log2 (X "3" 53)
#guard log2P1 (X "-0.25" 53) == log2 (X "0.75" 53)
#guard log2P1PrecRound (X "9" 53) 53 .Floor == log2PrecRound (X "10" 53) 53 .Floor

-- small arguments
#guard toString (log2P1 (X "0.5" 53)) == "0.5849625007211562"
#guard toString (log2P1 (X "0.000000000931322574615478515625" 53)) == "1.3436144592400231e-9"
#guard (log2P1PrecRound (X "0.000000000931322574615478515625" 53) 53 .Floor).2 == .lt
#guard (log2P1PrecRound (X "0.000000000931322574615478515625" 53) 53 .Ceiling).2 == .gt

-- high precision, against 80-digit expansions rounded to 200 bits (`log₂ 3`, `log₂ 10`)
private def tenPow79 : String := "1".pushn '0' 79
private def ref10 : AzRat :=
  Q ("3321928094887362347870319429489390175864" ++ "8313930245806120547563958159347766086252/"
    ++ tenPow79)
private def ref3 : AzRat :=
  Q ("1584962500721156181453738943947816508759" ++ "8144076924810604557526545410982277943586/"
    ++ tenPow79)
#guard toString (log2P1 (X "2" 200))
  == "1.584962500721156181453738943947816508759814407692481060455753"
#guard toString (log2P1 (X "9" 200))
  == "3.321928094887362347870319429489390175864831393024580612054757"

-- precomputed constants: the same results
#guard log2P1With (LnConsts.forPrecision 53) (X "0.5" 53) == log2P1 (X "0.5" 53)
#guard log2P1With (LnConsts.forPrecision 53) (X "9" 53) == log2P1 (X "9" 53)
#guard log2P1With (LnConsts.forPrecision 53) (X "-0.5" 53) == log2P1 (X "-0.5" 53)
#guard log2P1With (LnConsts.forPrecision 53) (X "1" 53) == log2P1 (X "1" 53)
#guard log2P1PrecRoundWith (LnConsts.forPrecision 53) (X "0.5" 53) 53 .Ceiling
  == log2P1PrecRound (X "0.5" 53) 53 .Ceiling

-- tiny arguments: the cost does not depend on the exponent (`2^(−2^30)` is immediate)
private def tinyE : AzInt := AzInt.ofInt (-(2 ^ 30 : Int))
private def tinyX : AzFloat := (X "1" 53) <<< tinyE
-- `log₂ (1 + x) ≈ x / ln 2`
#guard log2P1PrecRound tinyX 53 .Nearest
  == ((X "1.4426950408889634" 53) <<< tinyE, .lt)
#guard log2P1PrecRoundWith (LnConsts.forPrecision 53) tinyX 53 .Nearest
  == log2P1PrecRound tinyX 53 .Nearest

-- a huge power of two, `x = 2^K` with `K = 2^30 − 98`: `log₂ (1 + x) = K + ε`, `ε ≈ 2^(−K)`;
-- the side of `K` is decided without `K` bits of working precision
private def bigX : AzFloat := (X "1" 52) <<< AzInt.ofInt (2 ^ 30 - 98)
#guard D (log2P1PrecRound bigX 52 .Nearest) == ("1073741726.0", .lt)
#guard D (log2P1PrecRound bigX 52 .Floor) == ("1073741726.0", .lt)
#guard D (log2P1PrecRound bigX 52 .Ceiling) == ("1073741726.0000002", .gt)
#guard toString (log2P1 bigX) == "1073741726.0"
#guard D (log2P1PrecRound ((X "1" 53) <<< AzInt.ofInt 70) 53 .Floor) == ("7.0e1", .lt)
#guard D (log2P1PrecRound ((X "1" 53) <<< AzInt.ofInt 70) 53 .Ceiling) == ("70.00000000000001", .gt)
#guard log2P1PrecRoundWith (LnConsts.forPrecision 53) bigX 52 .Nearest
  == log2P1PrecRound bigX 52 .Nearest
