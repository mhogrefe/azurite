/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Log2
import Azurite.AzFloat.Log2Rat
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `log₂` of a rational

`log₂ (22/7) = 1.65207669657969314875739372949396215006220489971562728763550992…`,
`log₂ (1/3) = −1.58496250072115618145373894394781650875981440769248106045575265…`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p

-- special values
#guard log2Rat (Q "0") 53 == infinity false
#guard log2Rat (Q "-2") 53 == nan
#guard log2Rat (Q "-1/8") 53 == nan

-- exact powers of two
#guard log2RatPrecRound (Q "1") 53 .Nearest == (zero, .eq)
#guard log2RatPrecRound (Q "8") 53 .Nearest == (F "3" 53, .eq)
#guard log2RatPrecRound (Q "1/8") 53 .Nearest == (F "-3" 53, .eq)
#guard log2RatPrecRound (Q "1/1267650600228229401496703205376") 53 .Floor == (F "-100" 53, .eq)
#guard log2RatPrecRound (Q "1267650600228229401496703205376") 3 .Nearest == (F "96" 3, .lt)

-- agreement with the float logarithm on exactly representable inputs
#guard log2Rat (Q "10") 53 == log2 (F "10" 53)
#guard log2Rat (Q "3") 200 == log2 (F "3" 200)
#guard log2RatPrecRound (Q "5" ) 53 .Ceiling == log2PrecRound (F "5" 53) 53 .Ceiling

-- known values at 53 bits (exact rationals, unlike `F "1/3" 53`)
#guard toString (log2Rat (Q "1/3") 53) == "-1.584962500721156"
#guard toString (log2Rat (Q "22/7") 53) == "1.6520766965796931"
#guard toString (log2Rat (Q "3/2") 53) == "0.5849625007211562"
#guard toString (log2Rat (Q "1000000/7") 53) == "17.12421364726657"

-- directed rounding brackets the exact value
#guard (log2RatPrecRound (Q "22/7") 53 .Floor).2 == .lt
#guard (log2RatPrecRound (Q "22/7") 53 .Ceiling).2 == .gt

-- high precision, against 80-digit expansions rounded to 200 bits
private def tenPow79 : String := "1".pushn '0' 79
private def ref10 : AzRat :=
  Q ("3321928094887362347870319429489390175864" ++ "8313930245806120547563958159347766086252/"
    ++ tenPow79)
private def ref3 : AzRat :=
  Q ("1584962500721156181453738943947816508759" ++ "8144076924810604557526545410982277943586/"
    ++ tenPow79)
#guard log2Rat (Q "10") 200 == ofAzRat ref10 200
#guard log2Rat (Q "1/3") 200 == ofAzRat (-ref3) 200
