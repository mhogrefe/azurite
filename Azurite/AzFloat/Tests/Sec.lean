/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.Cos
import Azurite.AzFloat.OfString
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
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def S (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := secPrecRound x p m
/-- The reference: the reciprocal of `cos x` at `p + 300` bits, rounded to `p`. -/
private def ref (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) : AzFloat × Ordering :=
  divPrecRound (X "1" 1) (cosPrecRound x (p + 300) .Nearest).1 p m
private def agrees (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) : Bool :=
  S x p m == ref x p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (S nan 53) == ("NaN", .eq)
#guard D (S (infinity true) 53) == ("NaN", .eq)
#guard D (S (infinity false) 53) == ("NaN", .eq)
#guard D (S zero 53) == ("1.0", .eq)
#guard D (S zero 0) == ("NaN", .eq)
#guard D (S (X "1" 53) 0) == ("NaN", .eq)

-- values
#guard toString (sec (X "1" 200)) == "1.85081571768092561791175324139865019347039665509400929883515\
  8"
#guard S (X "1" 53) 53 == ref (X "1" 53) 53
#guard S (X "-1" 53) 53 == S (X "1" 53) 53
#guard (S (X "1" 53) 53 .Floor).2 == .lt
#guard (S (X "1" 53) 53 .Ceiling).2 == .gt
#guard (S (X "3" 53) 20).1 == (ref (X "3" 53) 20).1
#guard (S (X "3" 53) 53).1.isNegative

-- next to a pole: the 53-bit float nearest `π/2`; next to `π`
private def halfPi53 : AzFloat := X "1.5707963267948966" 53
#guard D (S halfPi53 53) == ("1.633123935319537e16", .gt)
#guard D (S (-halfPi53) 53) == ("1.633123935319537e16", .gt)
#guard agrees halfPi53 200
#guard agrees halfPi53 53 .Floor
#guard agrees (X "3.141592653589793" 53) 53

-- a sweep against the reciprocal of `cos`
#guard (List.range 26).all fun i => agrees (F s!"{i + 1}/4" 53) 53
#guard (List.range 26).all fun i => agrees (F s!"-{i + 1}/4" 53) 53 .Floor
#guard (List.range 13).all fun i => agrees (F s!"{2 * i + 1}/7" 53) 53 .Ceiling
#guard (List.range 13).all fun i => agrees (F s!"-{2 * i + 1}/3" 64) 40 .Down
#guard (List.range 13).all fun i => agrees (F s!"{2 * i + 1}/5" 30) 100 .Up
#guard agrees (X "1" 53) 1
#guard agrees (X "100" 53) 53
#guard agrees (X "-1000" 53) 53
#guard agrees (X "1000000000000" 53) 53
#guard agrees (X "12345678814.81481618629628669593" 100) 300
#guard agrees (X "0.3333333333333333333333333333333333333333333333333333333333333333333333333333333\
  3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333\
  3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333\
  3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333\
  3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333\
  3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333\
  333333333333333333333333333333333333335" 2000) 2000

-- small arguments on the ordinary path
#guard D (S (X "9.094947017729282e-13" 53) 53) == ("1.0", .lt)
#guard (S (X "9.094947017729282e-13" 53) 53 .Ceiling).2 == .gt

-- tiny arguments: one test, at a cost independent of the exponent
private def tinyX : AzFloat := (X "1" 53) <<< AzInt.ofInt (-(2 ^ 30 : Int))
#guard S tinyX 53 == (X "1" 53, .lt)
#guard S tinyX 53 .Floor == (X "1" 53, .lt)
#guard (S tinyX 53 .Ceiling).2 == .gt
#guard (S tinyX 53 .Ceiling).1 != X "1" 53
#guard S (-tinyX) 53 == (X "1" 53, .lt)
#guard sec tinyX == X "1" 53

-- a huge argument
#guard agrees ((X "1" 53) <<< AzInt.ofInt 1000) 53
