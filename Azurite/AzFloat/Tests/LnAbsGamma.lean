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
import Azurite.AzFloat.ToString
import Azurite.AzFloat.OfString

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
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def L (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) :=
  lnAbsGammaPrecRound x p m
private def pinf : AzFloat := infinity true
private def modes : List RoundingMode := [.Nearest, .Floor, .Ceiling, .Down, .Up]
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)
/-- A result with a flag, as decimal output. -/
private def Db (r : (AzFloat × Ordering) × Bool) : (String × Ordering) × Bool :=
  ((toString r.1.1, r.1.2), r.2)

-- special values
#guard Db (L nan 53) == (("NaN", .eq), true)
#guard Db (L pinf 53) == (("Infinity", .eq), true)
#guard Db (L (infinity false) 53) == (("Infinity", .eq), true)
#guard Db (L zero 53) == (("Infinity", .eq), true)
#guard Db (L zero 0) == (("Infinity", .eq), true)
#guard Db (L (X "-1" 53) 53) == (("Infinity", .eq), true)
#guard Db (L (X "-7" 53) 53) == (("Infinity", .eq), true)
#guard Db (L (X "-1267650600228229401496703205376" 53) 53) == (("Infinity", .eq), true)
#guard modes.all fun m => L (X "1" 53) 53 m == ((zero, .eq), true)
#guard modes.all fun m => L (X "2" 53) 53 m == ((zero, .eq), true)
#guard Db (L (X "1" 53) 0) == (("0.0", .eq), true)
#guard Db (L (X "-0.5" 53) 0) == (("NaN", .eq), false)
#guard Db (L (X "3" 53) 0) == (("NaN", .eq), true)

-- `x > 0`: `lnGammaPrecRound`
#guard ["1/3", "3/2", "5/2", "100", "1/1000000"].all fun s => modes.all fun m =>
  L (F s 53) 53 m == (lnGammaPrecRound (F s 53) 53 m, true)

-- decimal brackets: `ln (2√π)`, `ln (4√π/3)`, `ln (8√π/15)`
private def between (r : AzFloat × Ordering) (lo hi : String) : Bool :=
  lt (F lo 80) r.1 && lt r.1 (F hi 80)
#guard modes.all fun m =>
  between (L (X "-0.5" 53) 53 m).1 "1265512123484644/1000000000000000"
    "1265512123484647/1000000000000000"
#guard toString (L (X "-0.5" 53) 53).1.1 == "1.2655121234846454"
#guard modes.all fun m =>
  between (L (X "-1.5" 53) 53 m).1 "860047015376480/1000000000000000"
    "860047015376482/1000000000000000"
#guard toString (L (X "-1.5" 53) 53).1.1 == "0.860047015376481"
#guard modes.all fun m =>
  between (L (X "-2.5" 53) 53 m).1 "-56243716497675/1000000000000000"
    "-56243716497673/1000000000000000"
#guard toString (L (X "-2.5" 53) 53).1.1 == "-0.056243716497674054"

-- signs between the poles: `Γ < 0` on `(−1, 0)`, `> 0` on `(−2, −1)`, …
#guard (L (X "-0.5" 53) 53).2 == false
#guard (L (X "-1.5" 53) 53).2 == true
#guard (L (X "-2.5" 53) 53).2 == false
#guard (L (X "-3.5" 53) 53).2 == true
#guard (L (X "-0.000001" 53) 53).2 == false
#guard (L (X "-0.999999" 53) 53).2 == false
#guard (L (X "-1.000001" 53) 53).2 == true
#guard (L (X "-1000.5" 53) 53).2 == false
#guard (L (X "-1001.5" 53) 53).2 == true

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
#guard toString (L (-(one <<< AzInt.ofInt (-200))) 53).1.1 == "138.62943611198907"
#guard (L (-(one <<< AzInt.ofInt (-200))) 53).2 == false

-- next to a zero of `ln |Γ|` (`|Γ(x)| = 1` at `x ≈ −2.457024738…`): a small value, both signs
#guard lt zero (L (X "-2.457" 53) 53).1.1
#guard lt (L (X "-2.458" 53) 53).1.1 zero
#guard lt (L (X "-2.457" 53) 53).1.1 (X "0.001" 53)

-- nearest at the precision of the argument
#guard lnAbsGamma (X "-0.5" 53) == ((L (X "-0.5" 53) 53).1.1, false)
