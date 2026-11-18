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
import Azurite.AzFloat.OfString

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
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def R (s : String) (p : Nat) (m : RoundingMode := .Nearest) : AzFloat × Ordering :=
  cbrtRatPrecRound (Q s) p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- exact cubes
#guard D (R "1" 1) == ("1.0", .eq)
#guard D (R "8" 2) == ("2.0", .eq)
#guard D (R "27/8" 2) == ("1.5", .eq)
#guard D (R "-27/8" 2) == ("-1.5", .eq)
#guard D (R "-1/27" 53) == ("-0.3333333333333333", .gt)
#guard D (R "-1/27" 53 .Floor) == ("-0.33333333333333337", .lt)
#guard D (R "8/27" 53) == ("0.6666666666666666", .lt)
#guard D (R "8/27" 53 .Ceiling) == ("0.6666666666666667", .gt)
#guard D (R "1000/343" 100) == ("1.42857142857142857142857142857", .lt)
#guard D (R "1000000000000000000000" 53) == ("1.0e7", .eq)
#guard D (R "1/1000000000000000000000" 53) == ("1.0e-7", .lt)
#guard toString (cbrtRat (Q "125/64") 10) == "1.25"

-- agreement with the float cube root on dyadic rationals
#guard R "2" 53 == cbrtPrecRound (X "2" 53) 53 .Nearest
#guard R "2" 2 == cbrtPrecRound (X "2" 2) 2 .Nearest
#guard R "2" 3 .Floor == cbrtPrecRound (X "2" 3) 3 .Floor
#guard R "-2" 53 .Ceiling == cbrtPrecRound (X "-2" 53) 53 .Ceiling
#guard R "12345/4096" 150 == cbrtPrecRound (X "3.013916015625" 53) 150 .Nearest
#guard R "-12345/4096" 150 .Down == cbrtPrecRound (X "-3.013916015625" 53) 150 .Down
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
#guard D (R "27/8" 1) == ("2.0", .gt)
#guard D (R "125/8" 1) == ("2.0", .lt)
#guard D (R "-27/8" 1) == ("-2.0", .lt)

-- symmetry: `∛(−q) = −∛q` with `Floor` and `Ceiling` exchanged
#guard R "-2" 53 == (-(R "2" 53).1, (R "2" 53).2.swap)
#guard R "-2" 53 .Floor == (-(R "2" 53 .Ceiling).1, .lt)
#guard R "-2" 53 .Ceiling == (-(R "2" 53 .Floor).1, .gt)
#guard R "-22/7" 150 .Down == (-(R "22/7" 150 .Down).1, .gt)
#guard R "-22/7" 150 .Up == (-(R "22/7" 150 .Up).1, .lt)

-- zero and precision `0`
#guard D (R "0" 3) == ("0.0", .eq)
#guard D (R "0" 0) == ("0.0", .eq)
#guard D (R "2" 0) == ("NaN", .eq)
#guard D (R "-2" 0) == ("NaN", .eq)
#guard toString (cbrtRat (Q "0") 53) == "0.0"
