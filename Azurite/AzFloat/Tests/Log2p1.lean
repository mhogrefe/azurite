/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Log2
import Azurite.AzFloat.Log2p1
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `log₂ (1 + x)`

Exact cases `1 + x = 2^k` (`x = 1, 3, 7, −1/2, −3/4, −7/8`), then
`log₂ (1 + 2^(−30)) = 1.34361445924002321236225895697999546585367009927398877…·10^(−9)`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p

-- special values
#guard log2p1 nan == nan
#guard log2p1 (infinity true) == infinity true
#guard log2p1 (infinity false) == nan
#guard log2p1 zero == zero
#guard log2p1 (F "-1" 53) == infinity false
#guard log2p1 (F "-2" 53) == nan
#guard log2p1 (F "-3/2" 53) == nan

-- exact powers of two
#guard log2p1PrecRound (F "1" 53) 53 .Nearest == (F "1" 53, .eq)
#guard log2p1PrecRound (F "3" 53) 53 .Nearest == (F "2" 53, .eq)
#guard log2p1PrecRound (F "7" 53) 53 .Floor == (F "3" 53, .eq)
#guard log2p1PrecRound (F "-1/2" 53) 53 .Nearest == (F "-1" 53, .eq)
#guard log2p1PrecRound (F "-3/4" 53) 53 .Ceiling == (F "-2" 53, .eq)
#guard log2p1PrecRound (F "-7/8" 53) 53 .Nearest == (F "-3" 53, .eq)
#guard log2p1PrecRound (F "1267650600228229401496703205375" 110) 110 .Nearest == (F "100" 110, .eq)

-- agreement with `log2` on exactly representable sums
#guard log2p1 (F "9" 53) == log2 (F "10" 53)
#guard log2p1 (F "2" 53) == log2 (F "3" 53)
#guard log2p1 (F "-1/4" 53) == log2 (F "3/4" 53)
#guard log2p1PrecRound (F "9" 53) 53 .Floor == log2PrecRound (F "10" 53) 53 .Floor

-- small arguments
#guard toString (log2p1 (F "1/2" 53)) == "0.5849625007211562"
#guard toString (log2p1 (F "1/1073741824" 53)) == "1.3436144592400231e-9"
#guard (log2p1PrecRound (F "1/1073741824" 53) 53 .Floor).2 == .lt
#guard (log2p1PrecRound (F "1/1073741824" 53) 53 .Ceiling).2 == .gt

-- high precision, against 80-digit expansions rounded to 200 bits (`log₂ 3`, `log₂ 10`)
private def tenPow79 : String := "1".pushn '0' 79
private def ref10 : AzRat :=
  Q ("3321928094887362347870319429489390175864" ++ "8313930245806120547563958159347766086252/"
    ++ tenPow79)
private def ref3 : AzRat :=
  Q ("1584962500721156181453738943947816508759" ++ "8144076924810604557526545410982277943586/"
    ++ tenPow79)
#guard log2p1 (F "2" 200) == ofAzRat ref3 200
#guard log2p1 (F "9" 200) == ofAzRat ref10 200
