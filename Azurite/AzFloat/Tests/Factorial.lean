/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Factorial
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString

/-!
# Tests for the factorial as a float

Small arguments through the exact factorial (`0! = 1! = 1`, `20!` exact at 53 bits, `25!` in
three modes, `170!`, `1000!`), `n = 2472` and `2473` on either side of `gammaIntBound 53`,
larger `n` through the `Γ` loop against the exact factorial rounded directly, other
precisions, `p = 0`, and `n = 10¹⁸`.
-/

open Azurite Azurite.AzFloat

private def N (s : String) : AzNat := (AzNat.parse s).get!
private def F (n : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  factorialPrecRound (N n) p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)
/-- The exact factorial rounded directly. -/
private def ex (n p : Nat) (m : RoundingMode) : AzFloat × Ordering :=
  setPrecRound (ofAzNat (AzNat.factorial n)) p m

-- small arguments: the exact factorial
#guard D (F "0" 53) == ("1.0", .eq)
#guard D (F "1" 53) == ("1.0", .eq)
#guard D (F "5" 53) == ("1.2e2", .eq)
#guard D (F "20" 53) == ("2.43290200817664e18", .eq)
#guard D (F "25" 53) == ("1.5511210043330986e25", .gt)
#guard D (F "25" 53 .Floor) == ("1.5511210043330984e25", .lt)
#guard D (F "25" 53 .Ceiling) == ("1.5511210043330986e25", .gt)
#guard D (F "170" 53) == ("7.257415615307999e306", .gt)
#guard D (F "1000" 53) == ("4.023872600770938e2567", .gt)

-- either side of `gammaIntBound 53 = 2472`
#guard D (F "2472" 53) == ("1.3660875245862886e7316", .gt)
#guard D (F "2473" 53) == ("3.3783344483018916e7319", .gt)
#guard D (F "2473" 53 .Floor) == ("3.3783344483018912e7319", .lt)

-- the `Γ` loop against the exact factorial
#guard F "2473" 53 == ex 2473 53 .Nearest
#guard F "5000" 53 .Floor == ex 5000 53 .Floor
#guard F "20000" 53 .Up == ex 20000 53 .Up
#guard F "20000" 100 == ex 20000 100 .Nearest
#guard F "3000" 1 == ex 3000 1 .Nearest

-- other precisions
#guard D (F "5" 0) == ("NaN", .eq)
#guard D (F "5" 2) == ("1.3e2", .gt)
#guard D (F "5" 2 .Floor) == ("1.0e2", .lt)
#guard D (F "30" 200) == ("2.6525285981219105863630848e32", .eq)
#guard D (F "5000" 200)
  == ("4.228577926605543522201064200233584405390786674626646748849783e16325", .gt)

-- `10¹⁸!`: binary exponent and scaled value
#guard
  let r := F "1000000000000000000" 53
  (toString (expOf r.1), D (r.1 <<< (-(expOf r.1)), r.2))
    == ("58352010667083558886", ("0.7214273226507162", .gt))

-- `factorial`
#guard toString (factorial (N "20") 53) == "2.43290200817664e18"
