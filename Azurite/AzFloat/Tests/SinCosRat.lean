/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.SinCosRat
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `sinCosRat`

The special values (`q = 0`, `p = 0`), the correctly rounded 53-bit pairs `(sin q, cos q)` at
`1/3`, `1/10`, `±22/7`, `−7/5`, `355/113`, `−1/1000`, `10³⁰` (reference values of
`Tests/SinRat.lean` and `Tests/CosRat.lean`), the directed modes, a 20-bit result, 200-bit
values, the agreement with `sinRatPrecRound` and `cosRatPrecRound` on a sweep of rationals over
all the octants, both signs and several modes and precisions, a rational with a huge
denominator, and a tiny rational (delegated).
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def SC (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  sinCosRatPrecRound (Q q) p m
private def agrees (q : String) (p : Nat) (m : RoundingMode := .Nearest) : Bool :=
  sinCosRatPrecRound (Q q) p m == (sinRatPrecRound (Q q) p m, cosRatPrecRound (Q q) p m)

-- special values
#guard SC "0" 53 == ((zero, .eq), (F "1" 53, .eq))
#guard SC "0" 0 == ((zero, .eq), (nan, .eq))
#guard SC "1/3" 0 == ((nan, .eq), (nan, .eq))

-- correctly rounded values at exact rationals
#guard SC "1/3" 53 == ((F "5894215658275015/18014398509481984" 53, .gt),
  (F "8511415502608429/9007199254740992" 53, .gt))
#guard SC "1/10" 53 == ((F "1798438952039115/18014398509481984" 53, .gt),
  (F "8962200775956417/9007199254740992" 53, .gt))
#guard SC "22/7" 53 == ((F "-5831425920677443/4611686018427387904" 53, .gt),
  (F "-4503596026893703/4503599627370496" 53, .lt))
#guard SC "-22/7" 53 == ((F "5831425920677443/4611686018427387904" 53, .lt),
  (F "-4503596026893703/4503599627370496" 53, .lt))
#guard SC "-7/5" 53 == ((F "-4438071036768385/4503599627370496" 53, .gt),
  (F "6123711691446023/36028797018963968" 53, .lt))
#guard SC "355/113" 53 == ((F "-2519516530516539/9444732965739290427392" 53, .lt),
  (F "-140737488355323/140737488355328" 53, .lt))
#guard SC "-1/1000" 53 == ((F "-2305842624906545/2305843009213693952" 53, .lt),
  (F "2251798687785435/2251799813685248" 53, .gt))
#guard SC "1000000000000000000000000000000" 53
  == ((F "-811700891742577/9007199254740992" 53, .lt),
    (F "-4485275356010793/4503599627370496" 53, .gt))

-- directed modes and other precisions
#guard (SC "1/3" 53 .Floor).1 == (F "2947107829137507/9007199254740992" 53, .lt)
#guard (SC "22/7" 53 .Ceiling).1 == (F "-5831425920677443/4611686018427387904" 53, .gt)
#guard (SC "1/3" 20).1 == (F "686177/2097152" 20, .lt)
#guard sinCosRat (Q "1/3") 53 == (F "5894215658275015/18014398509481984" 53,
  F "8511415502608429/9007199254740992" 53)
#guard toString (sinCosRat (Q "1/3") 200).1
  == "0.3271946967961522441733440852676206060643014068937597915900562"
#guard toString (sinCosRat (Q "355/113") 200).1
  == "-2.667641890624191484063745288734688868221054266212710251192494e-7"

-- agreement with the separate functions: all the octants, both signs, several modes
#guard (List.range 26).all fun i => agrees s!"{i + 1}/4" 53
#guard (List.range 26).all fun i => agrees s!"-{i + 1}/4" 53 .Floor
#guard (List.range 13).all fun i => agrees s!"{2 * i + 1}/7" 53 .Ceiling
#guard (List.range 13).all fun i => agrees s!"-{2 * i + 1}/3" 40 .Down
#guard (List.range 13).all fun i => agrees s!"{2 * i + 1}/5" 100 .Up
#guard agrees "1/3" 1
#guard agrees "12345678901234567890/1000000007" 300
#guard agrees "1/3" 2000
#guard agrees ("314159265358979323846264338327950288419716939937510/"
  ++ "100000000000000000000000000000000000000000000000001") 64

-- a tiny rational (delegated to the tiny-argument paths) and a small one on the ordinary path
#guard agrees "1/1267650600228229401496703205376" 20
#guard agrees "-1/1267650600228229401496703205376" 20 .Floor
#guard agrees "1/1099511627776" 53
