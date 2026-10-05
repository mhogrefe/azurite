/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.HexString
import Azurite.AzFloat.Mul
import Azurite.AzFloat.Shift
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for multiplication and squaring

Expected values computed by hand (the exact product, then rounding).  `H` is the exact
hexadecimal rendering.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!

private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p

private def H (x : AzFloat) : String := toHexString x

private def M (x y : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) : AzFloat × Ordering :=
  mulPrecRound x y p m

private def Sq (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) : AzFloat × Ordering :=
  sqrPrecRound x p m

/-! ## Multiplication -/

#guard (M one one 1) == (one, .eq)
#guard (M two two 5) == (F "4" 5, .eq)
#guard (M (F "3" 2) (F "3" 2) 4) == (F "9" 4, .eq)
#guard (M (F "3" 2) (F "3" 2) 2) == (F "8" 2, .lt)                                 -- 9 → 8
#guard (M (F "3" 2) (F "5" 3) 3) == (F "16" 3, .gt)                                -- 15 tie → 16
#guard (M (F "3" 2) (F "5" 3) 3 .Floor) == (F "14" 3, .lt)
#guard (M (F "1/3" 53) (F "3" 2) 53) == (F "1" 53, .gt)  -- (2^54−1)/2^54 tie
#guard (M (F "1/3" 53) (F "3" 2) 53 .Floor) == (F "9007199254740991/9007199254740992" 53, .lt)
#guard (M negOne (F "3" 2) 2) == (F "-3" 2, .eq)
#guard (M negOne negOne 1) == (one, .eq)
#guard (M (one <<< 1000) (one >>> 999) 1) == (two, .eq)
#guard (M nan one 5) == (nan, .eq)
#guard (M one nan 5) == (nan, .eq)
#guard (M (infinity true) (infinity false) 5) == (infinity false, .eq)
#guard (M (infinity false) (infinity false) 5) == (infinity true, .eq)
#guard (M (infinity true) zero 5) == (nan, .eq)
#guard (M zero (infinity false) 5) == (nan, .eq)
#guard (M (infinity false) negOne 5) == (infinity true, .eq)
#guard (M (F "1/3" 53) (infinity false) 5) == (infinity false, .eq)
#guard (M zero (F "1/3" 53) 5) == (zero, .eq)
#guard (M (F "1/3" 53) zero 5) == (zero, .eq)
#guard (M zero zero 5) == (zero, .eq)

/-! ## Squaring -/

#guard (Sq (F "3" 2) 4) == (F "9" 4, .eq)
#guard (Sq (F "3" 2) 2) == (F "8" 2, .lt)
#guard (Sq (F "3" 2) 2 .Ceiling) == (F "12" 2, .gt)
#guard (Sq negOne 1) == (one, .eq)
#guard (Sq (F "-1/3" 53) 53) == (M (F "-1/3" 53) (F "-1/3" 53) 53)
#guard (Sq (one >>> 500) 1) == (one >>> 1000, .eq)
#guard (Sq (infinity false) 3) == (infinity true, .eq)
#guard (Sq zero 3) == (zero, .eq)
#guard (Sq nan 3) == (nan, .eq)

/-! ## Instances -/

#guard toString (two * two) == "4.0"
#guard toString ((F "3" 2) * (F "5" 3)) == "16.0"
#guard toString (F "1/10" 53 * F "1/10" 53) == "0.010000000000000002"
#guard toString (sqr (F "1/10" 53)) == "0.010000000000000002"
#guard sqr (F "-1/3" 53) == F "-1/3" 53 * F "-1/3" 53
