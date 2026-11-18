/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.HexString
import Azurite.AzFloat.Mul
import Azurite.AzFloat.OfString
import Azurite.AzFloat.Shift
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for multiplication and squaring

Expected values computed by hand (the exact product, then rounding), shown as the decimal output
of the result (`D`: the decimal and the comparison tag).  `H` is the exact hexadecimal rendering.
-/

open Azurite Azurite.AzFloat


/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!

private def H (x : AzFloat) : String := toHexString x

private def M (x y : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) : AzFloat × Ordering :=
  mulPrecRound x y p m

private def Sq (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) : AzFloat × Ordering :=
  sqrPrecRound x p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

/-! ## Multiplication -/

#guard D (M one one 1) == ("1.0", .eq)
#guard D (M two two 5) == ("4.0", .eq)
#guard D (M (X "3" 2) (X "3" 2) 4) == ("9.0", .eq)
#guard D (M (X "3" 2) (X "3" 2) 2) == ("8.0", .lt)  -- 9 → 8
#guard D (M (X "3" 2) (X "5" 3) 3) == ("16.0", .gt)  -- 15 tie → 16
#guard D (M (X "3" 2) (X "5" 3) 3 .Floor) == ("14.0", .lt)
#guard D (M (X "0.3333333333333333" 53) (X "3" 2) 53) == ("1.0", .gt)  -- (2^54−1)/2^54 tie
#guard D (M (X "0.3333333333333333" 53) (X "3" 2) 53 .Floor) == ("0.9999999999999999", .lt)
#guard D (M negOne (X "3" 2) 2) == ("-3.0", .eq)
#guard D (M negOne negOne 1) == ("1.0", .eq)
#guard D (M (one <<< 1000) (one >>> 999) 1) == ("2.0", .eq)
#guard D (M nan one 5) == ("NaN", .eq)
#guard D (M one nan 5) == ("NaN", .eq)
#guard D (M (infinity true) (infinity false) 5) == ("-Infinity", .eq)
#guard D (M (infinity false) (infinity false) 5) == ("Infinity", .eq)
#guard D (M (infinity true) zero 5) == ("NaN", .eq)
#guard D (M zero (infinity false) 5) == ("NaN", .eq)
#guard D (M (infinity false) negOne 5) == ("Infinity", .eq)
#guard D (M (X "0.3333333333333333" 53) (infinity false) 5) == ("-Infinity", .eq)
#guard D (M zero (X "0.3333333333333333" 53) 5) == ("0.0", .eq)
#guard D (M (X "0.3333333333333333" 53) zero 5) == ("0.0", .eq)
#guard D (M zero zero 5) == ("0.0", .eq)

/-! ## Squaring -/

#guard D (Sq (X "3" 2) 4) == ("9.0", .eq)
#guard D (Sq (X "3" 2) 2) == ("8.0", .lt)
#guard D (Sq (X "3" 2) 2 .Ceiling) == ("12.0", .gt)
#guard D (Sq negOne 1) == ("1.0", .eq)
#guard (Sq (X "-0.3333333333333333" 53) 53)
  == (M (X "-0.3333333333333333" 53) (X "-0.3333333333333333" 53) 53)
#guard D (Sq (one >>> 500) 1) == ("9.0e-302", .eq)
#guard D (Sq (infinity false) 3) == ("Infinity", .eq)
#guard D (Sq zero 3) == ("0.0", .eq)
#guard D (Sq nan 3) == ("NaN", .eq)

/-! ## Instances -/

#guard toString (two * two) == "4.0"
#guard toString ((X "3" 2) * (X "5" 3)) == "16.0"
#guard toString (X "0.1" 53 * X "0.1" 53) == "0.010000000000000002"
#guard toString (sqr (X "0.1" 53)) == "0.010000000000000002"
#guard toString (sqr (X "-0.3333333333333333" 53)) == "0.1111111111111111"
