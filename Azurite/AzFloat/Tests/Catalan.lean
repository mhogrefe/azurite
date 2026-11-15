/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Catalan
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for Catalan's constant

`G = 0.91596559417721901505460351493238411077414937428167213426649811962176301977625476947…`.
The correctly rounded values at 1, 2, 3, 53 and 100 bits in the nearest, floor and ceiling
modes (exact rationals from an independent evaluation to 2000 bits, in which Ramanujan's formula
and Broadhurst's BBP-type formula agree), precision `0`, and the decimal strings at 53, 200 and
400 bits.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p

#guard catalanConstantPrecRound 1 .Nearest == (F "1" 1, .gt)
#guard catalanConstantPrecRound 1 .Floor == (F "1/2" 1, .lt)
#guard catalanConstantPrecRound 1 .Ceiling == (F "1" 1, .gt)
#guard catalanConstantPrecRound 2 .Nearest == (F "1" 2, .gt)
#guard catalanConstantPrecRound 2 .Floor == (F "3/4" 2, .lt)
#guard catalanConstantPrecRound 2 .Ceiling == (F "1" 2, .gt)
#guard catalanConstantPrecRound 3 .Nearest == (F "7/8" 3, .lt)
#guard catalanConstantPrecRound 3 .Floor == (F "7/8" 3, .lt)
#guard catalanConstantPrecRound 3 .Ceiling == (F "1" 3, .gt)
#guard catalanConstantPrecRound 53 .Nearest == (F "8250284617241437/9007199254740992" 53, .lt)
#guard catalanConstantPrecRound 53 .Floor == (F "8250284617241437/9007199254740992" 53, .lt)
#guard catalanConstantPrecRound 53 .Ceiling == (F "4125142308620719/4503599627370496" 53, .gt)
#guard catalanConstantPrecRound 100 .Nearest
  == (F "145140541905894808764502001095/158456325028528675187087900672" 100, .gt)
#guard catalanConstantPrecRound 100 .Floor
  == (F "1161124335247158470116016008759/1267650600228229401496703205376" 100, .lt)
#guard catalanConstantPrecRound 100 .Ceiling
  == (F "145140541905894808764502001095/158456325028528675187087900672" 100, .gt)

#guard catalanConstantPrecRound 0 .Nearest == (nan, .eq)
#guard (catalanConstantPrecRound 200 .Floor).2 == .lt
#guard (catalanConstantPrecRound 200 .Ceiling).2 == .gt
#guard toString (AzFloat.catalanConstant 53) == "0.915965594177219"
#guard toString (AzFloat.catalanConstant 200)
  == "0.9159655941772190150546035149323841107741493742816721342664983"
#guard toString (AzFloat.catalanConstant 400)
  == "0.9159655941772190150546035149323841107741493742816721342664981196217630197762547694793"
    ++ "56512926115106248574422619196199579"
