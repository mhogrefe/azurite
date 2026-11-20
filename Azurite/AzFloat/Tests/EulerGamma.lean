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
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

#guard D (eulerGammaPrecRound 1 .Nearest) == ("0.5", .lt)
#guard D (eulerGammaPrecRound 1 .Floor) == ("0.5", .lt)
#guard D (eulerGammaPrecRound 1 .Ceiling) == ("1.0", .gt)
#guard D (eulerGammaPrecRound 2 .Nearest) == ("0.5", .lt)
#guard D (eulerGammaPrecRound 2 .Floor) == ("0.5", .lt)
#guard D (eulerGammaPrecRound 2 .Ceiling) == ("0.8", .gt)
#guard D (eulerGammaPrecRound 3 .Nearest) == ("0.6", .gt)
#guard D (eulerGammaPrecRound 3 .Floor) == ("0.5", .lt)
#guard D (eulerGammaPrecRound 3 .Ceiling) == ("0.6", .gt)
#guard D (eulerGammaPrecRound 53 .Nearest) == ("0.5772156649015329", .gt)
#guard D (eulerGammaPrecRound 53 .Floor) == ("0.5772156649015328", .lt)
#guard D (eulerGammaPrecRound 53 .Ceiling) == ("0.5772156649015329", .gt)
#guard D (eulerGammaPrecRound 100 .Nearest) == ("0.577215664901532860606512090082", .lt)
#guard D (eulerGammaPrecRound 100 .Floor) == ("0.577215664901532860606512090082", .lt)
#guard D (eulerGammaPrecRound 100 .Ceiling) == ("0.577215664901532860606512090083", .gt)

#guard D (eulerGammaPrecRound 0 .Nearest) == ("NaN", .eq)
#guard (eulerGammaPrecRound 200 .Floor).2 == .lt
#guard (eulerGammaPrecRound 200 .Ceiling).2 == .gt
#guard toString (eulerGamma 53) == "0.5772156649015329"
#guard toString (eulerGamma 200)
  == "0.577215664901532860606512090082402431042159335939923598805767"
#guard toString (eulerGamma 400)
  == "0.5772156649015328606065120900824024310421593359399235988057672348848677267776646709369470"
    ++ "63291746749514631447249807082481"

-- the working parameters: the argument has no prime factor above `7`
#guard eulerGammaArg 69 == 54
#guard eulerGammaArg 129 == 96
#guard eulerGammaArg 216 == 160
#guard eulerGammaArg 1016 == 720
#guard (List.range 3000).all fun w => eulerGammaN w ≤ eulerGammaArg w
#guard (List.range 3000).all fun w => isSmooth (eulerGammaArg w)
#guard eulerGammaBlockBits 1023 == 0
#guard eulerGammaBlockBits 1024 == 256
#guard eulerGammaBlockBits 40301 == 2518
#guard eulerGammaBracket 100 == eulerGammaBracketAt 100 (eulerGammaArg 100)

-- brackets at different working precisions overlap and narrow: word blocks only (`w < 500`),
-- long blocks above
private def nested (w w' : Nat) : Bool :=
  let a := eulerGammaBracket w
  let b := eulerGammaBracket w'
  le a.1 b.2 && le b.1 a.2 && lt a.1 a.2 && lt b.1 b.2
private def narrowAt (w : Nat) : Bool :=
  let a := eulerGammaBracket w
  le (subPrecRound a.2 a.1 32 .Ceiling).1 (powerOf2 (-(AzNat.ofNat w).toAzInt))
#guard nested 64 69 && nested 69 129 && nested 129 216 && nested 216 316
#guard nested 316 337 && nested 337 700 && nested 700 1016 && nested 1016 2100
#guard [64, 65, 69, 100, 129, 193, 216, 316, 337, 700, 1016, 2100].all narrowAt

-- the long-block path agrees with the word-block path
#guard (setPrecRound (eulerGamma 2000) 400 .Nearest).1 == eulerGamma 400
#guard (setPrecRound (eulerGamma 700) 200 .Nearest).1 == eulerGamma 200
#guard (eulerGammaPrecRound 1000 .Floor).2 == .lt
#guard (eulerGammaPrecRound 1000 .Ceiling).2 == .gt

-- explicit fuel: the public function is the variant at `eulerGammaFuel p`
#guard eulerGammaPrecRound 53 .Nearest == eulerGammaPrecRoundFuel (eulerGammaFuel 53) 53 .Nearest
#guard eulerGammaPrecRoundFuel 0 53 .Nearest == eulerGammaPrecRound 53 .Nearest
