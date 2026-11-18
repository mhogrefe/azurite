/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.RoundToInteger
import Azurite.AzFloat.Add
import Azurite.AzFloat.OfString
import Azurite.AzFloat.Shift
import Azurite.AzRat.Parse
import Azurite.AzFloat.ToString

/-!
# Tests for rounding to an integer
-/

open Azurite Azurite.AzFloat

/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def R (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) :=
  roundToIntegerPrecRound x p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)
/-- A result with its rounding direction and flag, as decimal output. -/
private def D3 (r : AzFloat × Ordering × Bool) : String × Ordering × Bool :=
  (toString r.1, r.2)

/-! ## Special values -/

#guard D3 (R nan 10) == ("NaN", .eq, false)
#guard D3 (R (infinity true) 10) == ("Infinity", .eq, false)
#guard D3 (R (infinity false) 10 .Floor) == ("-Infinity", .eq, false)
#guard D3 (R zero 10) == ("0.0", .eq, true)
#guard isInteger nan == false
#guard isInteger (infinity true) == false
#guard isInteger zero == true
#guard isInteger (X "7" 3) == true
#guard isInteger (X "6" 3) == true
#guard isInteger (X "3.5" 3) == false
#guard isInteger (X "0.25" 10) == false
#guard isInteger (X "1024" 3) == true
#guard isInteger (X "-5" 53) == true

/-! ## Integers that fit are unchanged -/

#guard D3 (R (X "7" 3) 3) == ("7.0", .eq, true)
#guard D3 (R (X "7" 3) 10) == ("7.0", .eq, true)
#guard D3 (R (X "-5" 53) 53 .Floor) == ("-5.0", .eq, true)
#guard D3 (R (X "1024" 3) 1) == ("1.0e3", .eq, true)

/-! ## Integers rounded to fit the precision: `(.lt, true)` / `(.gt, true)` -/

#guard D3 (R (X "10" 4) 2) == ("8.0", .lt, true)  -- tie between 8 and 12: even coordinate
#guard D3 (R (X "10" 4) 2 .Ceiling) == ("12.0", .gt, true)
#guard D3 (R (X "11" 4) 2) == ("12.0", .gt, true)
#guard D3 (R (X "123456789" 53) 10) == ("1.235e8", .gt, true)
#guard D3 (R (X "123456789" 53) 10 .Down) == ("1.233e8", .lt, true)
#guard D3 (R (X "-123456789" 53) 10 .Down) == ("-1.233e8", .gt, true)

/-! ## Non-integers: one rounding at the target precision -/

-- `10.5` to nearest at 2 bits is `12`, not `10` rounded again
#guard D3 (R (X "10.5" 5) 2) == ("12.0", .gt, false)
#guard D3 (R (X "10.5" 5) 2 .Floor) == ("8.0", .lt, false)
#guard D3 (R (X "10.5" 5) 2 .Down) == ("8.0", .lt, false)
#guard D3 (R (X "10.5" 5) 2 .Up) == ("12.0", .gt, false)
#guard D3 (R (X "-10.5" 5) 2) == ("-12.0", .lt, false)
#guard D3 (R (X "-10.5" 5) 2 .Down) == ("-8.0", .gt, false)
#guard D3 (R (X "10.5" 5) 5) == ("1.0e1", .lt, false)  -- ties to even: 10
#guard D3 (R (X "11.5" 5) 5) == ("12.0", .gt, false)
-- small values: the integer rounding
#guard D3 (R (X "2.5" 10) 10) == ("2.0", .lt, false)
#guard D3 (R (X "3.5" 10) 10) == ("4.0", .gt, false)
#guard D3 (R (X "-2.5" 10) 10) == ("-2.0", .gt, false)
#guard D3 (R (X "1.5" 10) 10) == ("2.0", .gt, false)
#guard D3 (R (X "0.5" 10) 10) == ("0.0", .lt, false)
#guard D3 (R (X "-0.5" 10) 10) == ("0.0", .gt, false)
#guard D3 (R (X "0.4" 10) 10) == ("0.0", .lt, false)
#guard D3 (R (X "0.6" 10) 10 .Floor) == ("0.0", .lt, false)
#guard D3 (R (X "0.6" 10) 10 .Ceiling) == ("1.0", .gt, false)
#guard D3 (R (X "-7.25" 10) 10 .Down) == ("-7.0", .gt, false)
#guard D3 (R (X "-7.25" 10) 10 .Up) == ("-8.0", .lt, false)
#guard D3 (R (X "-7.25" 10) 10 .Floor) == ("-8.0", .lt, false)
#guard D3 (R (X "-7.25" 10) 10 .Ceiling) == ("-7.0", .gt, false)
#guard D3 (R (X "-7.25" 10) 10) == ("-7.0", .gt, false)
-- rounding at the boundary `2^(p−1)`: `7.5` at 3 bits (`2^(p−1) = 4`) rounds to the 3-bit
-- integer `8`
#guard D3 (R (X "7.5" 10) 3) == ("8.0", .gt, false)
#guard D3 (R (X "7.5" 10) 3 .Floor) == ("7.0", .lt, false)
-- a huge integer plus a fraction
private def big : AzFloat := X "1" 200 <<< 100 + X "0.75" 200   -- 2^100 + 3/4, exact
#guard D3 (R big 200 .Floor) == ("1267650600228229401496703205376.0", .lt, false)
#guard D3 (R big 200 .Ceiling) == ("1267650600228229401496703205377.0", .gt, false)
#guard D3 (R big 200) == ("1267650600228229401496703205377.0", .gt, false)
#guard D3 (R big 5) == ("1.3e30", .lt, false)

/-! ## Wrappers -/

#guard toString (roundToIntegerPrec (X "10.5" 5) 2) == "12.0"
#guard toString (roundToIntegerRound (X "10.5" 5) .Floor) == "1.0e1"
#guard toString (roundToInteger (X "10.5" 5)) == "1.0e1"
#guard toString (roundToInteger (X "3.5" 5)) == "4.0"
#guard toString (roundToInteger (X "-0.33" 5)) == "0.0"
#guard toString (roundToInteger nan) == "NaN"
#guard toString (roundToInteger (infinity false)) == "-Infinity"

/-! ## Two roundings: `roundToIntegerThenPrecRound` -/

private def T (x : AzFloat) (irm : RoundingMode) (p : Nat) (rm : RoundingMode := .Nearest) :=
  roundToIntegerThenPrecRound x irm p rm

#guard D (T nan .Nearest 10) == ("NaN", .eq)
#guard D (T (infinity true) .Floor 10) == ("Infinity", .eq)
#guard D (T (infinity false) .Nearest 10 .Ceiling) == ("-Infinity", .eq)
#guard D (T zero .Nearest 10) == ("0.0", .eq)
-- `10.5` → `10` (nearest) → `8` at 2 bits: two roundings, where the single rounding gives `12`
#guard D (T (X "10.5" 5) .Nearest 2) == ("8.0", .lt)
#guard D3 (R (X "10.5" 5) 2) == ("12.0", .gt, false)
#guard D (T (X "10.5" 5) .Floor 2) == ("8.0", .lt)
#guard D (T (X "10.5" 5) .Ceiling 2) == ("12.0", .gt)
#guard D (T (X "10.5" 5) .Up 5) == ("11.0", .eq)
#guard D (T (X "10.5" 5) .Nearest 5) == ("1.0e1", .eq)
#guard D (T (X "10.5" 5) .Nearest 2 .Up) == ("12.0", .gt)
#guard D (T (X "-10.5" 5) .Nearest 2) == ("-8.0", .gt)
-- small values
#guard D (T (X "0.4" 10) .Nearest 10) == ("0.0", .eq)
#guard D (T (X "0.5" 10) .Nearest 10) == ("0.0", .eq)
#guard D (T (X "0.5" 10) .Ceiling 10) == ("1.0", .eq)
#guard D (T (X "1.5" 10) .Nearest 1) == ("2.0", .eq)
#guard D (T (X "2.5" 10) .Nearest 1) == ("2.0", .eq)
#guard D (T (X "3.5" 10) .Nearest 1) == ("4.0", .eq)
#guard D (T (X "-7.25" 10) .Down 2) == ("-8.0", .lt)
#guard D (T (X "-7.25" 10) .Down 3) == ("-7.0", .eq)
#guard D (T (X "-7.25" 10) .Up 3) == ("-8.0", .eq)
-- integers only pass through the final rounding
#guard D (T (X "123456789" 53) .Floor 10) == ("1.235e8", .gt)
#guard D (T (X "123456789" 53) .Nearest 53) == ("123456789.0", .eq)
#guard D (T big .Nearest 5) == ("1.3e30", .lt)
#guard D (T big .Nearest 200) == ("1267650600228229401496703205377.0", .eq)
#guard toString (roundToIntegerThenPrec (X "10.5" 5) .Nearest 2) == "8.0"

