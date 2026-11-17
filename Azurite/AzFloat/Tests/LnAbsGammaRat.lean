/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LnAbsGammaRat
import Azurite.AzFloat.GammaRat
import Azurite.AzFloat.Ln
import Azurite.AzFloat.Conversion
import Azurite.AzRat.Parse

/-!
# Tests for `ln |Γ(q)|` and the sign of `Γ(q)` at a rational

* Special values: `0`, the poles, `1`, `2`, `p = 0`.
* `q > 0`: the value of `lnGammaRatPrecRound`, sign `true`.
* Dyadic arguments: the results of the float function at the same argument, in every mode.
* Non-dyadic `q < 0`: the 53-bit result against the logarithm of the 200-bit `|Γ(q)|`, in
  every mode; the signs between the poles; arguments next to a pole and next to `0`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def L (s : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  lnAbsGammaRatPrecRound (Q s) p m
private def pinf : AzFloat := infinity true
private def modes : List RoundingMode := [.Nearest, .Floor, .Ceiling, .Down, .Up]

-- special values
#guard L "0" 53 == ((pinf, .eq), true)
#guard L "0" 0 == ((pinf, .eq), true)
#guard L "-1" 53 == ((pinf, .eq), true)
#guard L "-7" 53 == ((pinf, .eq), true)
#guard L "-1267650600228229401496703205376" 0 == ((pinf, .eq), true)
#guard modes.all fun m => L "1" 53 m == ((zero, .eq), true)
#guard modes.all fun m => L "2" 53 m == ((zero, .eq), true)
#guard L "-1/3" 0 == ((nan, .eq), false)
#guard L "1/3" 0 == ((nan, .eq), true)

-- `q > 0`: `lnGammaRatPrecRound`
#guard ["1/3", "3/2", "7/3", "100", "1/1000000"].all fun s => modes.all fun m =>
  L s 53 m == (lnGammaRatPrecRound (Q s) 53 m, true)

-- dyadic arguments: the float function
#guard ["-1/2", "-3/2", "-5/2", "-7/4", "-201/2", "-1/1024", "-4097/4096"].all fun s =>
  modes.all fun m => L s 53 m == lnAbsGammaPrecRound (F s 64) 53 m
#guard L "-5/2" 200 == lnAbsGammaPrecRound (F "-5/2" 64) 200 .Nearest

/-- The 53-bit result is the rounding of `ln` of the 200-bit `|Γ(q)|`, with the sign of
`Γ(q)`. -/
private def viaGamma (s : String) (m : RoundingMode) : Bool :=
  let g := (gammaRatPrecRound (Q s) 200 .Nearest).1
  (L s 53 m).1.1 == (lnPrecRound g.abs 53 m).1 && (L s 53 m).2 == !g.isNegative
#guard ["-1/3", "-4/3", "-7/3", "-22/7", "-27/10", "-1000001/3", "-1/1000000007",
    "-10000001/10000000", "-9999999/10000000"].all fun s => modes.all fun m => viaGamma s m

-- signs between the poles
#guard (L "-1/3" 53).2 == false
#guard (L "-4/3" 53).2 == true
#guard (L "-7/3" 53).2 == false
#guard (L "-10/3" 53).2 == true
#guard (L "-3002/3" 53).2 == false
#guard (L "-3005/3" 53).2 == true
#guard gammaRatSign (Q "-4/3") && !gammaRatSign (Q "-1/3") && gammaRatSign (Q "-2")
  && gammaRatSign (Q "0") && gammaRatSign (Q "5/3")

-- the comparison tag agrees with the directed roundings
#guard (L "-1/3" 53 .Floor).1.2 == .lt && (L "-1/3" 53 .Ceiling).1.2 == .gt
  && lt (L "-1/3" 53 .Floor).1.1 (L "-1/3" 53 .Ceiling).1.1

-- nearest
#guard lnAbsGammaRat (Q "-1/3") 53 == ((L "-1/3" 53).1.1, false)
