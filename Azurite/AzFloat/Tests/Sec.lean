/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.Cos
import Azurite.AzFloat.Sec
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `sec`

The special values (`NaN`, `±∞`, `sec 0 = 1`, `p = 0`), `sec 1` to 59 digits (reference: the
Taylor series of `cos` in exact rational arithmetic), the 53-bit float nearest `π/2`
(`sec ≈ 1.6331239353195370·10¹⁶`: the loop resolves the pole) and nearest `π` (`sec ≈ −1`),
evenness, the directed modes, and a sweep over all the octants, both signs, several modes and
precisions against the correctly rounded reciprocal of `cos x` computed with 300 extra bits.
Extreme arguments: `2⁻⁴⁰` (the ordinary path), `±2^(−2^30)` (the tiny path, independent of the
exponent), `2^1000`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def S (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := secPrecRound x p m
/-- The reference: the reciprocal of `cos x` at `p + 300` bits, rounded to `p`. -/
private def ref (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) : AzFloat × Ordering :=
  divPrecRound (F "1" 1) (cosPrecRound x (p + 300) .Nearest).1 p m
private def agrees (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) : Bool :=
  S x p m == ref x p m

-- special values
#guard S nan 53 == (nan, .eq)
#guard S (infinity true) 53 == (nan, .eq)
#guard S (infinity false) 53 == (nan, .eq)
#guard S zero 53 == (F "1" 53, .eq)
#guard S zero 0 == (nan, .eq)
#guard S (F "1" 53) 0 == (nan, .eq)

-- values
#guard (toString (sec (F "1" 200))).startsWith
  "1.8508157176809256179117532413986501934703966550940092988351"
#guard S (F "1" 53) 53 == ref (F "1" 53) 53
#guard S (F "-1" 53) 53 == S (F "1" 53) 53
#guard (S (F "1" 53) 53 .Floor).2 == .lt
#guard (S (F "1" 53) 53 .Ceiling).2 == .gt
#guard (S (F "3" 53) 20).1 == (ref (F "3" 53) 20).1
#guard (S (F "3" 53) 53).1.isNegative

-- next to a pole: the 53-bit float nearest `π/2`; next to `π`
private def halfPi53 : AzFloat := F "884279719003555/562949953421312" 53
#guard S halfPi53 53 == (F "16331239353195370" 53, .gt)
#guard S (-halfPi53) 53 == (F "16331239353195370" 53, .gt)
#guard agrees halfPi53 200
#guard agrees halfPi53 53 .Floor
#guard agrees (F "884279719003555/281474976710656" 53) 53

-- a sweep against the reciprocal of `cos`
#guard (List.range 26).all fun i => agrees (F s!"{i + 1}/4" 53) 53
#guard (List.range 26).all fun i => agrees (F s!"-{i + 1}/4" 53) 53 .Floor
#guard (List.range 13).all fun i => agrees (F s!"{2 * i + 1}/7" 53) 53 .Ceiling
#guard (List.range 13).all fun i => agrees (F s!"-{2 * i + 1}/3" 64) 40 .Down
#guard (List.range 13).all fun i => agrees (F s!"{2 * i + 1}/5" 30) 100 .Up
#guard agrees (F "1" 53) 1
#guard agrees (F "100" 53) 53
#guard agrees (F "-1000" 53) 53
#guard agrees (F "1000000000000" 53) 53
#guard agrees (F "12345678901234567890/1000000007" 100) 300
#guard agrees (F "1/3" 2000) 2000

-- small arguments on the ordinary path
#guard S (F "1/1099511627776" 53) 53 == (F "1" 53, .lt)
#guard (S (F "1/1099511627776" 53) 53 .Ceiling).2 == .gt

-- tiny arguments: one test, at a cost independent of the exponent
private def tinyX : AzFloat := (F "1" 53) <<< AzInt.ofInt (-(2 ^ 30 : Int))
#guard S tinyX 53 == (F "1" 53, .lt)
#guard S tinyX 53 .Floor == (F "1" 53, .lt)
#guard (S tinyX 53 .Ceiling).2 == .gt
#guard (S tinyX 53 .Ceiling).1 != F "1" 53
#guard S (-tinyX) 53 == (F "1" 53, .lt)
#guard sec tinyX == F "1" 53

-- a huge argument
#guard agrees ((F "1" 53) <<< AzInt.ofInt 1000) 53
