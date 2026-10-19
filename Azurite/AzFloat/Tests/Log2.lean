/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Log2
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `log₂`

Exact powers of two, then `log₂ 10 = 3.32192809488736234787031942948939017586483139302458061205…`,
`log₂ 3 = 1.58496250072115618145373894394781650875981440769248106045…`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p

-- special values
#guard log2 nan == nan
#guard log2 (infinity true) == infinity true
#guard log2 (infinity false) == nan
#guard log2 zero == infinity false
#guard log2 (F "-1" 53) == nan
#guard log2 (F "-8" 53) == nan

-- exact powers of two
#guard log2PrecRound (F "1" 53) 53 .Nearest == (zero, .eq)
#guard log2PrecRound (F "2" 53) 53 .Nearest == (F "1" 53, .eq)
#guard log2PrecRound (F "8" 53) 53 .Nearest == (F "3" 53, .eq)
#guard log2PrecRound (F "1/4" 53) 53 .Floor == (F "-2" 53, .eq)
#guard log2PrecRound (F "1/1073741824" 53) 53 .Ceiling == (F "-30" 53, .eq)
#guard log2PrecRound (F "1267650600228229401496703205376" 53) 53 .Nearest == (F "100" 53, .eq)
#guard log2PrecRound (F "1267650600228229401496703205376" 3) 3 .Nearest == (F "96" 3, .lt)
#guard log2PrecRound (F "1267650600228229401496703205376" 3) 3 .Ceiling == (F "112" 3, .gt)

-- known values at 53 bits
#guard toString (log2 (F "10" 53)) == "3.321928094887362"
#guard toString (log2 (F "3" 53)) == "1.584962500721156"
-- `F "1/3" 53` is the double `6004799503160661/2^54`, slightly below `1/3`
#guard toString (log2 (F "1/3" 53)) == "-1.5849625007211563"
#guard toString (log2 (F "3/2" 53)) == "0.5849625007211562"
#guard toString (log2 (F "1000000" 53)) == "19.931568569324174"
#guard toString (log2 (F "5" 53)) == "2.321928094887362"

-- directed rounding brackets the exact value
#guard (log2PrecRound (F "10" 53) 53 .Floor).2 == .lt
#guard (log2PrecRound (F "10" 53) 53 .Ceiling).2 == .gt
#guard (log2PrecRound (F "10" 53) 53 .Floor).1 != (log2PrecRound (F "10" 53) 53 .Ceiling).1

-- high precision, against 80-digit expansions rounded to 200 bits
private def tenPow79 : String := "1".pushn '0' 79
private def ref10 : AzRat :=
  Q ("3321928094887362347870319429489390175864" ++ "8313930245806120547563958159347766086252/"
    ++ tenPow79)
private def ref3 : AzRat :=
  Q ("1584962500721156181453738943947816508759" ++ "8144076924810604557526545410982277943586/"
    ++ tenPow79)
#guard log2 (F "10" 200) == ofAzRat ref10 200
#guard log2 (F "3" 200) == ofAzRat ref3 200
