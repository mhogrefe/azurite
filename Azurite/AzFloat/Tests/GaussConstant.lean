/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.GaussConstant
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for Gauss's constant

`G = 0.8346268416740731862814297327990468089939930134903470024498…`; `G · 2^53 =
7517650266313539.9272…`, `G · 2^100 = 1058015216814730263581923557728.0829…`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p

#guard gaussConstantPrecRound 1 .Nearest == (F "1" 1, .gt)
#guard gaussConstantPrecRound 1 .Floor == (F "1/2" 1, .lt)
#guard gaussConstantPrecRound 2 .Nearest == (F "3/4" 2, .lt)
#guard gaussConstantPrecRound 2 .Ceiling == (F "1" 2, .gt)
#guard gaussConstantPrecRound 3 .Nearest == (F "7/8" 3, .gt)
#guard gaussConstantPrecRound 3 .Floor == (F "3/4" 3, .lt)
#guard gaussConstantPrecRound 53 .Nearest == (F "7517650266313540/9007199254740992" 53, .gt)
#guard gaussConstantPrecRound 53 .Floor == (F "7517650266313539/9007199254740992" 53, .lt)
#guard gaussConstantPrecRound 100 .Nearest
  == (F "1058015216814730263581923557728/1267650600228229401496703205376" 100, .lt)
#guard gaussConstantPrecRound 100 .Up
  == (F "1058015216814730263581923557729/1267650600228229401496703205376" 100, .gt)
#guard toString (gaussConstant 53) == "0.8346268416740732"
