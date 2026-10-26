/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Cbrt
import Azurite.AzFloat.CbrtRat
import Azurite.AzFloat.Conversion
import Azurite.AzFloat.Pow10
import Azurite.AzFloat.PowBaseRat
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for the cube root of a rational

Exact cubes (`∛(27/8) = 3/2`, `∛(−1/27) = −1/3`, `∛(1000/343) = 10/7` at a precision that holds
it, `∛(8/27) = 2/3` rounded), agreement with the float cube root on dyadics and with
`10^(1/3)`, `7^(1/3)` and `(22/7)^(1/3)` from the `powBaseRat` family, the correctly rounded
`∛2`, `∛(1/3)` and `∛(−1/3)` in all modes, ties, the symmetry `∛(−q) = −∛q` with `Floor` and
`Ceiling` exchanged, zero and precision `0`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def R (s : String) (p : Nat) (m : RoundingMode := .Nearest) : AzFloat × Ordering :=
  cbrtRatPrecRound (Q s) p m

-- exact cubes
#guard R "1" 1 == (one, .eq)
#guard R "8" 2 == (F "2" 2, .eq)
#guard R "27/8" 2 == (F "3/2" 2, .eq)
#guard R "-27/8" 2 == (F "-3/2" 2, .eq)
#guard R "-1/27" 53 == ofAzRatRound (Q "-1/3") 53 .Nearest
#guard R "-1/27" 53 .Floor == ofAzRatRound (Q "-1/3") 53 .Floor
#guard R "8/27" 53 == ofAzRatRound (Q "2/3") 53 .Nearest
#guard R "8/27" 53 .Ceiling == ofAzRatRound (Q "2/3") 53 .Ceiling
#guard R "1000/343" 100 == ofAzRatRound (Q "10/7") 100 .Nearest
#guard R "1000000000000000000000" 53 == (F "10000000" 53, .eq)
#guard R "1/1000000000000000000000" 53 == ofAzRatRound (Q "1/10000000") 53 .Nearest
#guard cbrtRat (Q "125/64") 10 == F "5/4" 10

-- agreement with the float cube root on dyadic rationals
#guard R "2" 53 == cbrtPrecRound (F "2" 53) 53 .Nearest
#guard R "2" 2 == cbrtPrecRound (F "2" 2) 2 .Nearest
#guard R "2" 3 .Floor == cbrtPrecRound (F "2" 3) 3 .Floor
#guard R "-2" 53 .Ceiling == cbrtPrecRound (F "-2" 53) 53 .Ceiling
#guard R "12345/4096" 150 == cbrtPrecRound (F "12345/4096" 53) 150 .Nearest
#guard R "-12345/4096" 150 .Down == cbrtPrecRound (F "-12345/4096" 53) 150 .Down
#guard toString (cbrtRat (Q "2") 53) == "1.2599210498948732"
#guard toString (cbrtRat (Q "-10") 53) == "-2.154434690031884"

-- agreement with `10^(1/3)`, `7^(1/3)` and `(22/7)^(1/3)`
#guard R "10" 150 == pow10RatPrecRound (Q "1/3") 150 .Nearest
#guard R "10" 150 .Floor == pow10RatPrecRound (Q "1/3") 150 .Floor
#guard R "7" 150 .Ceiling == powBaseRatPrecRound 7 (Q "1/3") 150 .Ceiling
#guard R "1/10" 150 == pow10RatPrecRound (Q "-1/3") 150 .Nearest
#guard R "1/7" 150 .Up == powBaseRatPrecRound 7 (Q "-1/3") 150 .Up

-- `∛(1/3)` and `∛(−1/3)` in the directed modes
#guard (R "1/3" 60 .Floor).2 == .lt
#guard (R "1/3" 60 .Ceiling).2 == .gt
#guard partialCompare (R "1/3" 60 .Floor).1 (R "1/3" 60 .Ceiling).1 == some .lt
#guard partialCompare (R "-1/3" 60 .Floor).1 (R "-1/3" 60 .Ceiling).1 == some .lt
#guard (R "-1/3" 60 .Floor).2 == .lt
#guard (R "-1/3" 60 .Ceiling).2 == .gt

-- ties at precision `1`: `∛(27/8) = 3/2 → 2` (even), `∛(125/8) = 5/2 → 2`
#guard R "27/8" 1 == (F "2" 1, .gt)
#guard R "125/8" 1 == (F "2" 1, .lt)
#guard R "-27/8" 1 == (F "-2" 1, .lt)

-- symmetry: `∛(−q) = −∛q` with `Floor` and `Ceiling` exchanged
#guard R "-2" 53 == (-(R "2" 53).1, (R "2" 53).2.swap)
#guard R "-2" 53 .Floor == (-(R "2" 53 .Ceiling).1, .lt)
#guard R "-2" 53 .Ceiling == (-(R "2" 53 .Floor).1, .gt)
#guard R "-22/7" 150 .Down == (-(R "22/7" 150 .Down).1, .gt)
#guard R "-22/7" 150 .Up == (-(R "22/7" 150 .Up).1, .lt)

-- zero and precision `0`
#guard R "0" 3 == (zero, .eq)
#guard R "0" 0 == (zero, .eq)
#guard R "2" 0 == (nan, .eq)
#guard R "-2" 0 == (nan, .eq)
#guard cbrtRat (Q "0") 53 == zero
