/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LnAbsGamma
import Azurite.AzFloat.Gamma
import Azurite.AzFloat.Ln
import Azurite.AzFloat.Conversion
import Azurite.AzRat.Parse

/-!
# Tests for `ln |Γ(x)|` and the sign of `Γ(x)`

* Special values: `NaN`, `±∞`, `0`, the poles, `1`, `2`, `p = 0`.
* `x > 0`: the value of `lnGammaPrecRound`, sign `true`.
* `x < 0`: decimal brackets at `−1/2`, `−3/2`, `−5/2`; the 53-bit result against the logarithm
  of the 200-bit `|Γ(x)|`, in every mode; the signs between the poles; arguments next to a
  pole, tiny and large arguments, and an argument next to a zero of `ln |Γ|`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def L (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) :=
  lnAbsGammaPrecRound x p m
private def pinf : AzFloat := infinity true
private def modes : List RoundingMode := [.Nearest, .Floor, .Ceiling, .Down, .Up]

-- special values
#guard L nan 53 == ((nan, .eq), true)
#guard L pinf 53 == ((pinf, .eq), true)
#guard L (infinity false) 53 == ((pinf, .eq), true)
#guard L zero 53 == ((pinf, .eq), true)
#guard L zero 0 == ((pinf, .eq), true)
#guard L (F "-1" 53) 53 == ((pinf, .eq), true)
#guard L (F "-7" 53) 53 == ((pinf, .eq), true)
#guard L (F "-1267650600228229401496703205376" 53) 53 == ((pinf, .eq), true)
#guard modes.all fun m => L (F "1" 53) 53 m == ((zero, .eq), true)
#guard modes.all fun m => L (F "2" 53) 53 m == ((zero, .eq), true)
#guard L (F "1" 53) 0 == ((zero, .eq), true)
#guard L (F "-1/2" 53) 0 == ((nan, .eq), false)
#guard L (F "3" 53) 0 == ((nan, .eq), true)

-- `x > 0`: `lnGammaPrecRound`
#guard ["1/3", "3/2", "5/2", "100", "1/1000000"].all fun s => modes.all fun m =>
  L (F s 53) 53 m == (lnGammaPrecRound (F s 53) 53 m, true)

-- decimal brackets: `ln (2√π)`, `ln (4√π/3)`, `ln (8√π/15)`
private def between (r : AzFloat × Ordering) (lo hi : String) : Bool :=
  lt (F lo 80) r.1 && lt r.1 (F hi 80)
#guard modes.all fun m =>
  between (L (F "-1/2" 53) 53 m).1 "1265512123484644/1000000000000000"
    "1265512123484647/1000000000000000"
#guard modes.all fun m =>
  between (L (F "-3/2" 53) 53 m).1 "860047015376480/1000000000000000"
    "860047015376482/1000000000000000"
#guard modes.all fun m =>
  between (L (F "-5/2" 53) 53 m).1 "-56243716497675/1000000000000000"
    "-56243716497673/1000000000000000"

-- signs between the poles: `Γ < 0` on `(−1, 0)`, `> 0` on `(−2, −1)`, …
#guard (L (F "-1/2" 53) 53).2 == false
#guard (L (F "-3/2" 53) 53).2 == true
#guard (L (F "-5/2" 53) 53).2 == false
#guard (L (F "-7/2" 53) 53).2 == true
#guard (L (F "-1/1000000" 53) 53).2 == false
#guard (L (F "-999999/1000000" 53) 53).2 == false
#guard (L (F "-1000001/1000000" 53) 53).2 == true
#guard (L (F "-2001/2" 53) 53).2 == false
#guard (L (F "-2003/2" 53) 53).2 == true

/-- The 53-bit result is the rounding of `ln` of the 200-bit `|Γ(x)|` (the 200-bit value is
far from the 53-bit rounding boundaries in these cases), with the sign of `Γ(x)`. -/
private def viaGamma (x : AzFloat) (m : RoundingMode) : Bool :=
  let g := (gammaPrecRound x 200 .Nearest).1
  (L x 53 m).1.1 == (lnPrecRound g.abs 53 m).1 && (L x 53 m).2 == !g.isNegative
#guard ["-1/3", "-4/3", "-7/2", "-21/2", "-201/2", "-1/1024", "-10000001/10000000",
    "-27/10", "-1000001/3"].all fun s => modes.all fun m => viaGamma (F s 53) m

-- the comparison tag agrees with the directed roundings
#guard ["-1/3", "-27/10"].all fun s =>
  (L (F s 53) 53 .Floor).1.2 == .lt && (L (F s 53) 53 .Ceiling).1.2 == .gt
    && lt (L (F s 53) 53 .Floor).1.1 (L (F s 53) 53 .Ceiling).1.1

-- tiny arguments: `ln |Γ(x)| ≈ −ln |x|`
#guard between (L (-(one <<< AzInt.ofInt (-200))) 53).1 "138629436111989/1000000000000"
  "138629436111990/1000000000000"
#guard (L (-(one <<< AzInt.ofInt (-200))) 53).2 == false

-- next to a zero of `ln |Γ|` (`|Γ(x)| = 1` at `x ≈ −2.457024738…`): a small value, both signs
#guard lt zero (L (F "-2457/1000" 53) 53).1.1
#guard lt (L (F "-2458/1000" 53) 53).1.1 zero
#guard lt (L (F "-2457/1000" 53) 53).1.1 (F "1/1000" 53)

-- nearest at the precision of the argument
#guard lnAbsGamma (F "-1/2" 53) == ((L (F "-1/2" 53) 53).1.1, false)
