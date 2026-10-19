/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Ln2
import Azurite.AzFloat.HexString
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `ln 2`

`ln 2 = 0.6931471805599453094172321214581765680755…`.  At `p` bits the candidates in `[1/2, 1)`
are `m/2^p`; `ln 2 · 2^53 = 6243314768165359.2088…` and
`ln 2 · 2^100 = 878668439483319573618263538048.2468…` (60-digit arithmetic), so rounding to
nearest goes down at both precisions.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p

#guard ln2PrecRound 1 .Nearest == (F "1/2" 1, .lt)
#guard ln2PrecRound 1 .Ceiling == (F "1" 1, .gt)
#guard ln2PrecRound 2 .Nearest == (F "3/4" 2, .gt)
#guard ln2PrecRound 2 .Floor == (F "1/2" 2, .lt)
#guard ln2PrecRound 3 .Nearest == (F "3/4" 3, .gt)
#guard ln2PrecRound 3 .Floor == (F "5/8" 3, .lt)
#guard ln2PrecRound 53 .Nearest == (F "6243314768165359/9007199254740992" 53, .lt)
#guard ln2PrecRound 53 .Floor == (F "6243314768165359/9007199254740992" 53, .lt)
#guard ln2PrecRound 53 .Ceiling == (F "6243314768165360/9007199254740992" 53, .gt)
#guard ln2PrecRound 100 .Nearest
  == (F "878668439483319573618263538048/1267650600228229401496703205376" 100, .lt)
#guard ln2PrecRound 100 .Up
  == (F "878668439483319573618263538049/1267650600228229401496703205376" 100, .gt)
#guard toString (ln2 53) == "0.6931471805599453"

/-! ## `log₂ e = 1/ln 2 = 1.4426950408889634073992468100189213742664595415298…`

`log₂ e · 2^52 = 6497320848556798.0916…`, `log₂ e · 2^99 = 914416617264592211221101407494.5696…`. -/

#guard log2EPrecRound 1 .Nearest == (F "1" 1, .lt)
#guard log2EPrecRound 1 .Ceiling == (F "2" 1, .gt)
#guard log2EPrecRound 2 .Nearest == (F "3/2" 2, .gt)
#guard log2EPrecRound 3 .Nearest == (F "3/2" 3, .gt)
#guard log2EPrecRound 3 .Floor == (F "5/4" 3, .lt)
#guard log2EPrecRound 53 .Nearest == (F "6497320848556798/4503599627370496" 53, .lt)
#guard log2EPrecRound 53 .Ceiling == (F "6497320848556799/4503599627370496" 53, .gt)
#guard log2EPrecRound 100 .Nearest
  == (F "914416617264592211221101407495/633825300114114700748351602688" 100, .gt)
#guard log2EPrecRound 100 .Floor
  == (F "914416617264592211221101407494/633825300114114700748351602688" 100, .lt)
#guard toString (log2E 53) == "1.4426950408889634"
