/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Log2
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.ToString
import Azurite.AzFloat.OfString
import Azurite.AzRat.Parse
import Azurite.AzFloat.Ln

/-!
# Tests for `log₂`

Exact powers of two, then `log₂ 10 = 3.32192809488736234787031942948939017586483139302458061205…`,
`log₂ 3 = 1.58496250072115618145373894394781650875981440769248106045…`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!

-- special values
#guard toString (log2 nan) == "NaN"
#guard toString (log2 (infinity true)) == "Infinity"
#guard toString (log2 (infinity false)) == "NaN"
#guard toString (log2 zero) == "-Infinity"
#guard toString (log2 (X "-1" 53)) == "NaN"
#guard toString (log2 (X "-8" 53)) == "NaN"

-- exact powers of two
#guard D (log2PrecRound (X "1" 53) 53 .Nearest) == ("0.0", .eq)
#guard D (log2PrecRound (X "2" 53) 53 .Nearest) == ("1.0", .eq)
#guard D (log2PrecRound (X "8" 53) 53 .Nearest) == ("3.0", .eq)
#guard D (log2PrecRound (X "0.25" 53) 53 .Floor) == ("-2.0", .eq)
#guard D (log2PrecRound (X "0.000000000931322574615478515625" 53) 53 .Ceiling) == ("-3.0e1", .eq)
#guard D (log2PrecRound (X "1267650600228229401496703205376" 53) 53 .Nearest) == ("1.0e2", .eq)
#guard D (log2PrecRound (X "1267650600228229401496703205376" 3) 3 .Nearest) == ("1.0e2", .lt)
#guard D (log2PrecRound (X "1267650600228229401496703205376" 3) 3 .Ceiling) == ("1.1e2", .gt)

-- known values at 53 bits
#guard toString (log2 (X "10" 53)) == "3.321928094887362"
#guard toString (log2 (X "3" 53)) == "1.584962500721156"
-- `X "0.3333333333333333" 53` is the double `6004799503160661/2^54`, slightly below `1/3`
#guard toString (log2 (X "0.3333333333333333" 53)) == "-1.5849625007211563"
#guard toString (log2 (X "1.5" 53)) == "0.5849625007211562"
#guard toString (log2 (X "1000000" 53)) == "19.931568569324174"
#guard toString (log2 (X "5" 53)) == "2.321928094887362"

-- directed rounding brackets the exact value
#guard (log2PrecRound (X "10" 53) 53 .Floor).2 == .lt
#guard (log2PrecRound (X "10" 53) 53 .Ceiling).2 == .gt
#guard (log2PrecRound (X "10" 53) 53 .Floor).1 != (log2PrecRound (X "10" 53) 53 .Ceiling).1

-- high precision, against 80-digit expansions rounded to 200 bits
private def tenPow79 : String := "1".pushn '0' 79
private def ref10 : AzRat :=
  Q ("3321928094887362347870319429489390175864" ++ "8313930245806120547563958159347766086252/"
    ++ tenPow79)
private def ref3 : AzRat :=
  Q ("1584962500721156181453738943947816508759" ++ "8144076924810604557526545410982277943586/"
    ++ tenPow79)
#guard toString (log2 (X "10" 200))
  == "3.321928094887362347870319429489390175864831393024580612054757"
#guard toString (log2 (X "3" 200))
  == "1.584962500721156181453738943947816508759814407692481060455753"

-- precomputed constants: the same results
#guard log2With (LnConsts.forPrecision 53) (X "10" 53) == log2 (X "10" 53)
#guard log2With (LnConsts.forPrecision 53) (X "3" 53) == log2 (X "3" 53)
#guard log2With (LnConsts.forPrecision 200) (X "10" 200) == log2 (X "10" 200)
#guard log2PrecRoundWith (LnConsts.forPrecision 53) (X "10" 53) 53 .Floor
  == log2PrecRound (X "10" 53) 53 .Floor
#guard log2With (LnConsts.forPrecision 53) (X "8" 53) == log2 (X "8" 53)
#guard log2With (LnConsts.make 1) (X "10" 53) == log2 (X "10" 53)
