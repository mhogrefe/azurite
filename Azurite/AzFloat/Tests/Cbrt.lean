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

/-!
# Tests for the cube root

Exact cubes (`∛8 = 2`, `∛(27/8) = 3/2`, `∛(−8) = −2`, `∛(2^300) = 2^100`), the correctly
rounded `∛2` (`1.2599210498948732` at 53 bits) and `∛(2^301)`, ties at precision `1`, agreement
with `10^(1/3)` and `7^(1/3)` from `pow10Rat`/`powBaseRat` at 150 bits, the symmetry
`∛(−x) = −∛x` with the modes `Floor`/`Ceiling` exchanged, the special values and precision `0`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def R (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) : AzFloat × Ordering :=
  cbrtPrecRound x p m

-- exact cubes
#guard R one 1 == (one, .eq)
#guard R (F "8" 4) 2 == (F "2" 2, .eq)
#guard R (F "27/8" 5) 2 == (F "3/2" 2, .eq)
#guard R (F "-8" 4) 2 == (F "-2" 2, .eq)
#guard R (F "-27/8" 5) 2 == (F "-3/2" 2, .eq)
#guard R (F "1/8" 2) 1 == (F "1/2" 1, .eq)
#guard R (one <<< 300) 1 == (one <<< 100, .eq)
#guard R (one <<< 303) 1 == (one <<< 101, .eq)
#guard R (F "1000" 10) 53 == (F "10" 53, .eq)
#guard R (F "-1000000" 20) 53 == (F "-100" 53, .eq)
#guard R (F "1/1000" 53) 53 != (F "1/10" 53, .eq)
#guard cbrt (F "1000000000000000000000" 70) == F "10000000" 70

-- inexact roots
#guard R (F "2" 2) 2 == (F "3/2" 2, .gt)
#guard R (F "2" 3) 3 == (F "5/4" 3, .lt)
#guard R (F "2" 2) 2 .Ceiling == (F "3/2" 2, .gt)
#guard R (F "2" 2) 2 .Floor == (F "1" 2, .lt)
#guard R (one <<< 301) 1 == (one <<< 100, .lt)
#guard R (one <<< 301) 1 .Ceiling == (one <<< 101, .gt)
#guard R (one <<< 302) 1 == (one <<< 101, .gt)
#guard toString (cbrt (F "2" 53)) == "1.2599210498948732"
#guard toString (cbrt (F "-2" 53)) == "-1.2599210498948732"
#guard toString (cbrt (F "10" 53)) == "2.154434690031884"

-- ties at precision `1`: `∛(27/8) = 3/2 → 2` (even), `∛(125/8) = 5/2 → 2`
#guard R (F "27/8" 5) 1 == (F "2" 1, .gt)
#guard R (F "125/8" 7) 1 == (F "2" 1, .lt)
#guard R (F "-27/8" 5) 1 == (F "-2" 1, .lt)

-- agreement with `10^(1/3)` and `7^(1/3)`
#guard R (F "10" 53) 150 == pow10RatPrecRound (Q "1/3") 150 .Nearest
#guard R (F "10" 53) 150 .Floor == pow10RatPrecRound (Q "1/3") 150 .Floor
#guard R (F "7" 53) 150 .Ceiling == powBaseRatPrecRound 7 (Q "1/3") 150 .Ceiling
#guard R (F "12345" 53) 100 == powBaseRatPrecRound 12345 (Q "1/3") 100 .Nearest

-- symmetry: `∛(−x) = −∛x` with `Floor` and `Ceiling` exchanged
#guard R (F "-2" 53) 53 == (-(R (F "2" 53) 53).1, (R (F "2" 53) 53).2.swap)
#guard R (F "-2" 53) 53 .Floor == (-(R (F "2" 53) 53 .Ceiling).1, .lt)
#guard R (F "-2" 53) 53 .Ceiling == (-(R (F "2" 53) 53 .Floor).1, .gt)
#guard R (F "-10" 53) 150 .Down == (-(R (F "10" 53) 150 .Down).1, .gt)
#guard R (F "-10" 53) 150 .Up == (-(R (F "10" 53) 150 .Up).1, .lt)

-- special values
#guard R nan 3 == (nan, .eq)
#guard R (infinity true) 3 == (infinity true, .eq)
#guard R (infinity false) 3 == (infinity false, .eq)
#guard R zero 3 == (zero, .eq)
#guard R (F "2" 2) 0 == (nan, .eq)
#guard cbrt nan == nan
#guard cbrt (infinity false) == infinity false
#guard cbrt zero == zero
