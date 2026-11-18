/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Cbrt
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.Pow10
import Azurite.AzFloat.PowBaseRat
import Azurite.AzFloat.Shift
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse
import Azurite.AzFloat.OfString

/-!
# Tests for the cube root

Exact cubes (`∛8 = 2`, `∛(27/8) = 3/2`, `∛(−8) = −2`, `∛(2^300) = 2^100`), the correctly
rounded `∛2` (`1.2599210498948732` at 53 bits) and `∛(2^301)`, ties at precision `1`, agreement
with `10^(1/3)` and `7^(1/3)` from `pow10Rat`/`powBaseRat` at 150 bits, the symmetry
`∛(−x) = −∛x` with the modes `Floor`/`Ceiling` exchanged, the special values and precision `0`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def R (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) : AzFloat × Ordering :=
  cbrtPrecRound x p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- exact cubes
#guard D (R one 1) == ("1.0", .eq)
#guard D (R (X "8" 4) 2) == ("2.0", .eq)
#guard D (R (X "3.375" 5) 2) == ("1.5", .eq)
#guard D (R (X "-8" 4) 2) == ("-2.0", .eq)
#guard D (R (X "-3.375" 5) 2) == ("-1.5", .eq)
#guard D (R (X "0.125" 2) 1) == ("0.5", .eq)
#guard D (R (one <<< 300) 1) == ("1.0e30", .eq)
#guard D (R (one <<< 303) 1) == ("3.0e30", .eq)
#guard D (R (X "1000" 10) 53) == ("1.0e1", .eq)
#guard D (R (X "-1000000" 20) 53) == ("-1.0e2", .eq)
#guard R (X "0.001" 53) 53 != (X "0.1" 53, .eq)
#guard toString (cbrt (X "1000000000000000000000" 70)) == "1.0e7"

-- inexact roots
#guard D (R (X "2" 2) 2) == ("1.5", .gt)
#guard D (R (X "2" 3) 3) == ("1.2", .lt)
#guard D (R (X "2" 2) 2 .Ceiling) == ("1.5", .gt)
#guard D (R (X "2" 2) 2 .Floor) == ("1.0", .lt)
#guard D (R (one <<< 301) 1) == ("1.0e30", .lt)
#guard D (R (one <<< 301) 1 .Ceiling) == ("3.0e30", .gt)
#guard D (R (one <<< 302) 1) == ("3.0e30", .gt)
#guard toString (cbrt (X "2" 53)) == "1.2599210498948732"
#guard toString (cbrt (X "-2" 53)) == "-1.2599210498948732"
#guard toString (cbrt (X "10" 53)) == "2.154434690031884"

-- ties at precision `1`: `∛(27/8) = 3/2 → 2` (even), `∛(125/8) = 5/2 → 2`
#guard D (R (X "3.375" 5) 1) == ("2.0", .gt)
#guard D (R (X "15.625" 7) 1) == ("2.0", .lt)
#guard D (R (X "-3.375" 5) 1) == ("-2.0", .lt)

-- agreement with `10^(1/3)` and `7^(1/3)`
#guard R (X "10" 53) 150 == pow10RatPrecRound (Q "1/3") 150 .Nearest
#guard R (X "10" 53) 150 .Floor == pow10RatPrecRound (Q "1/3") 150 .Floor
#guard R (X "7" 53) 150 .Ceiling == powBaseRatPrecRound 7 (Q "1/3") 150 .Ceiling
#guard R (X "12345" 53) 100 == powBaseRatPrecRound 12345 (Q "1/3") 100 .Nearest

-- symmetry: `∛(−x) = −∛x` with `Floor` and `Ceiling` exchanged
#guard R (X "-2" 53) 53 == (-(R (X "2" 53) 53).1, (R (X "2" 53) 53).2.swap)
#guard R (X "-2" 53) 53 .Floor == (-(R (X "2" 53) 53 .Ceiling).1, .lt)
#guard R (X "-2" 53) 53 .Ceiling == (-(R (X "2" 53) 53 .Floor).1, .gt)
#guard R (X "-10" 53) 150 .Down == (-(R (X "10" 53) 150 .Down).1, .gt)
#guard R (X "-10" 53) 150 .Up == (-(R (X "10" 53) 150 .Up).1, .lt)

-- special values
#guard D (R nan 3) == ("NaN", .eq)
#guard D (R (infinity true) 3) == ("Infinity", .eq)
#guard D (R (infinity false) 3) == ("-Infinity", .eq)
#guard D (R zero 3) == ("0.0", .eq)
#guard D (R (X "2" 2) 0) == ("NaN", .eq)
#guard toString (cbrt nan) == "NaN"
#guard toString (cbrt (infinity false)) == "-Infinity"
#guard toString (cbrt zero) == "0.0"
