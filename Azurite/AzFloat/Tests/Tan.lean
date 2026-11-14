/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.SinCos
import Azurite.AzFloat.Tan
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `tan`

The special values (`NaN`, `±∞`, `tan 0 = 0` at every precision, `p = 0`), `tan 1` to 60
digits, the 53-bit float nearest `π/2` (`tan ≈ 1.6331239353195370·10¹⁶`, the classical example:
the loop resolves the pole) and its negative, the float nearest `π` (`tan ≈ −1.2·10⁻¹⁶`),
oddness and the directed modes, and a sweep over all the octants, both signs, several modes and
precisions against the correctly rounded quotient of `sin x` and `cos x` computed with 300
extra bits.  Extreme arguments: `2⁻⁴⁰` (the ordinary path next to the argument), `±2^(−2^30)`
and `(3/2)·2^(−2^30)` (the tiny path, independent of the exponent), `2^1000`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def T (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) := tanPrecRound x p m
/-- The reference: the quotient of `sin x` and `cos x` at `p + 300` bits, rounded to `p`. -/
private def ref (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) : AzFloat × Ordering :=
  let sc := sinCosPrecRound x (p + 300) .Nearest
  divPrecRound sc.1.1 sc.2.1 p m
private def agrees (x : AzFloat) (p : Nat) (m : RoundingMode := .Nearest) : Bool :=
  T x p m == ref x p m

-- special values
#guard T nan 53 == (nan, .eq)
#guard T (infinity true) 53 == (nan, .eq)
#guard T (infinity false) 53 == (nan, .eq)
#guard T zero 53 == (zero, .eq)
#guard T zero 0 == (zero, .eq)
#guard T (F "1" 53) 0 == (nan, .eq)

-- values
#guard (toString (tan (F "1" 200))).startsWith
  "1.55740772465490223050697480745836017308725077238152003838394"
#guard (toString (tan (F "-1" 200))).startsWith
  "-1.55740772465490223050697480745836017308725077238152003838394"
#guard T (F "1" 53) 53 == ref (F "1" 53) 53
#guard (T (F "1" 53) 53 .Floor).2 == .lt
#guard (T (F "1" 53) 53 .Ceiling).2 == .gt
#guard (T (F "-1" 53) 53 .Floor).1 == -(T (F "1" 53) 53 .Ceiling).1
#guard (T (F "3" 53) 20).1 == (ref (F "3" 53) 20).1

-- next to a pole: the 53-bit float nearest `π/2`
private def halfPi53 : AzFloat := F "884279719003555/562949953421312" 53
#guard T halfPi53 53 == (F "16331239353195370" 53, .gt)
#guard T (-halfPi53) 53 == (F "-16331239353195370" 53, .lt)
#guard agrees halfPi53 200
#guard agrees halfPi53 53 .Floor

-- next to a zero: the 53-bit float nearest `π`
private def pi53 : AzFloat := F "884279719003555/281474976710656" 53
#guard agrees pi53 53
#guard (T pi53 53).1.isNegative

-- a sweep against the quotient of `sin` and `cos`
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
#guard T (F "1/1099511627776" 53) 53 == (F "1/1099511627776" 53, .lt)
#guard (T (F "1/1099511627776" 53) 53 .Ceiling).2 == .gt

-- tiny arguments: one test, at a cost independent of the exponent
private def tinyE : AzInt := AzInt.ofInt (-(2 ^ 30 : Int))
private def tinyX : AzFloat := (F "1" 53) <<< tinyE
#guard T tinyX 53 == (tinyX, .lt)
#guard T tinyX 53 .Floor == (tinyX, .lt)
#guard (T tinyX 53 .Ceiling).2 == .gt
#guard (T tinyX 53 .Ceiling).1 != tinyX
#guard T (-tinyX) 53 == (-tinyX, .gt)
#guard T (-tinyX) 53 .Ceiling == (-tinyX, .gt)
#guard (T (-tinyX) 53 .Floor).2 == .lt
#guard T ((F "3/2" 100) <<< tinyE) 53 == ((F "3/2" 53) <<< tinyE, .lt)
#guard tan tinyX == tinyX
-- the tiny path and the loop agree where both apply (`2^(−200)` at 53 and at 150 bits)
#guard T ((F "1" 53) <<< AzInt.ofInt (-200)) 53 .Ceiling
  == ((T ((F "1" 53) <<< AzInt.ofInt (-200)) 150 .Ceiling).1 |> fun y =>
    (setPrecRound y 53 .Ceiling))

-- a huge argument
#guard agrees ((F "1" 53) <<< AzInt.ofInt 1000) 53
