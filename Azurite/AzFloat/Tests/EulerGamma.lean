/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.EulerGamma
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for Euler's constant

`γ = 0.57721566490153286060651209008240243104215933593992359880576723488486772677766467…`.
The correctly rounded values at 1, 2, 3, 53 and 100 bits in the nearest, floor and ceiling
modes (exact rationals from an independent 150-digit evaluation by the Brent–McMillan
formula), precision `0`, and the decimal strings at 53, 200 and 400 bits.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p

#guard eulerGammaPrecRound 1 .Nearest == (F "1/2" 1, .lt)
#guard eulerGammaPrecRound 1 .Floor == (F "1/2" 1, .lt)
#guard eulerGammaPrecRound 1 .Ceiling == (F "1" 1, .gt)
#guard eulerGammaPrecRound 2 .Nearest == (F "1/2" 2, .lt)
#guard eulerGammaPrecRound 2 .Floor == (F "1/2" 2, .lt)
#guard eulerGammaPrecRound 2 .Ceiling == (F "3/4" 2, .gt)
#guard eulerGammaPrecRound 3 .Nearest == (F "5/8" 3, .gt)
#guard eulerGammaPrecRound 3 .Floor == (F "1/2" 3, .lt)
#guard eulerGammaPrecRound 3 .Ceiling == (F "5/8" 3, .gt)
#guard eulerGammaPrecRound 53 .Nearest == (F "5199096506725913/9007199254740992" 53, .gt)
#guard eulerGammaPrecRound 53 .Floor == (F "649887063340739/1125899906842624" 53, .lt)
#guard eulerGammaPrecRound 53 .Ceiling == (F "5199096506725913/9007199254740992" 53, .gt)
#guard eulerGammaPrecRound 100 .Nearest
  == (F "45731736504597791087659990913/79228162514264337593543950336" 100, .lt)
#guard eulerGammaPrecRound 100 .Floor
  == (F "45731736504597791087659990913/79228162514264337593543950336" 100, .lt)
#guard eulerGammaPrecRound 100 .Ceiling
  == (F "731707784073564657402559854609/1267650600228229401496703205376" 100, .gt)

#guard eulerGammaPrecRound 0 .Nearest == (nan, .eq)
#guard (eulerGammaPrecRound 200 .Floor).2 == .lt
#guard (eulerGammaPrecRound 200 .Ceiling).2 == .gt
#guard toString (eulerGamma 53) == "0.5772156649015329"
#guard toString (eulerGamma 200)
  == "0.577215664901532860606512090082402431042159335939923598805767"
#guard toString (eulerGamma 400)
  == "0.5772156649015328606065120900824024310421593359399235988057672348848677267776646709369470"
    ++ "63291746749514631447249807082481"
