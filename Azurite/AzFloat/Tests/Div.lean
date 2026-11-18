/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.Div
import Azurite.AzFloat.HexString
import Azurite.AzFloat.OfString
import Azurite.AzFloat.Shift
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for division and the rounding of unreduced fractions

Expected values computed by hand (the exact quotient, then rounding).  `H` is the exact
hexadecimal rendering.
-/

open Azurite Azurite.AzFloat

/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!

private def H (x : AzFloat) : String := toHexString x

private def D (x y : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) : AzFloat × Ordering :=
  divPrecRound x y p m
/-- A result as its decimal output and its comparison tag. -/
private def Dc (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

/-! ## Division -/

#guard Dc (D one one 1) == ("1.0", .eq)
#guard Dc (D (X "6" 3) (X "3" 2) 2) == ("2.0", .eq)
#guard Dc (D one (X "3" 2) 2) == ("0.4", .gt) -- 1/3 → 0.375
#guard Dc (D one (X "3" 2) 2 .Floor) == ("0.25", .lt)
#guard Dc (D one (X "3" 2) 53) == ("0.3333333333333333", .lt)
#guard Dc (D (X "0.3333333333333333" 53) (X "0.3333333333333333" 53) 53) == ("1.0", .eq)
#guard Dc (D two (X "3" 2) 1) == ("0.5", .lt) -- 2/3 → 1/2
#guard Dc (D (X "7" 3) (X "5" 3) 3) == ("1.5", .gt) -- 1.4 → 1.5
#guard Dc (D (X "5" 3) (X "7" 3) 3) == ("0.8", .gt) -- 0.714 → 0.75
#guard Dc (D (X "1" 100) (X "3" 2) 10) == ("0.3335", .gt) -- 683/2048
#guard Dc (D negOne (X "3" 2) 2) == ("-0.4", .lt)
#guard Dc (D negOne negOne 1) == ("1.0", .eq)
#guard Dc (D (one <<< 1000) (one <<< 999) 1) == ("2.0", .eq)
#guard Dc (D one (one <<< 1000) 1) == ("9.0e-302", .eq)
#guard Dc (D nan one 5) == ("NaN", .eq)
#guard Dc (D one nan 5) == ("NaN", .eq)
#guard Dc (D (infinity true) (infinity false) 5) == ("NaN", .eq)
#guard Dc (D (infinity false) one 5) == ("-Infinity", .eq)
#guard Dc (D (infinity false) negOne 5) == ("Infinity", .eq)
#guard Dc (D (infinity true) zero 5) == ("Infinity", .eq)
#guard Dc (D one zero 5) == ("Infinity", .eq)
#guard Dc (D negOne zero 5) == ("-Infinity", .eq)
#guard Dc (D zero zero 5) == ("NaN", .eq)
#guard Dc (D zero one 5) == ("0.0", .eq)
#guard Dc (D zero (infinity true) 5) == ("0.0", .eq)
#guard Dc (D one (infinity false) 5) == ("0.0", .eq)
#guard toString (one / X "3" 2) == "0.4"
#guard toString (X "1" 53 / X "3" 53) == "0.3333333333333333"
#guard toString (X "22" 53 / X "7" 53) == "3.142857142857143"

/-! ## Rounding an unreduced fraction -/

#guard toString ((ofFractionRound true (AzNat.ofNat 2) (AzNat.ofNat 6) 53 .Nearest).1)
  == "0.3333333333333333"
#guard toString ((ofFractionRound false (AzNat.ofNat 10) (AzNat.ofNat 30) 2 .Nearest).1) == "-0.4"
#guard Dc (ofFractionRound true (AzNat.ofNat 12) (AzNat.ofNat 4) 5 .Nearest) == ("3.0", .eq)
#guard Dc (ofFractionRound true (AzNat.ofNat 0) (AzNat.ofNat 4) 5 .Nearest) == ("0.0", .eq)
#guard toString ((ofFractionRound true (AzNat.ofNat 1) (AzNat.ofNat 10) 53 .Nearest).1) == "0.1"
#guard Dc (ofFractionRound true (AzNat.ofNat 7) (AzNat.ofNat 5) 3 .Floor) == ("1.2", .lt)
