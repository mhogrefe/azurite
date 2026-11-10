/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.Sin
import Azurite.AzFloat.SinRat
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `sin q` of a rational

The special values (`sin 0 = 0` at every precision, `p = 0`), the correctly rounded 53-bit
values of `sin q` at the exact rationals `1/3`, `1/10`, `±22/7` (which differs from `sin` of the
53-bit float nearest `22/7` from the fourth significant digit on, the argument being near `π`),
`−7/5`, `355/113` (`sin ≈ −2.7·10⁻⁷`), `−1/1000`, `10³⁰`, agreement with the float `sin` at
exactly representable arguments (`1/2`, `−3`, `10¹²`, `1/1024`), the directed modes, a 20-bit
result, 200-bit values, and the tiny path at `±1/(3·2^1000)` (`sin q` rounds like a value just
inside `q`).  References: a 300-digit evaluation rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def S (q : String) (p : Nat) (m : RoundingMode := .Nearest) := sinRatPrecRound (Q q) p m

-- special values
#guard S "0" 53 == (zero, .eq)
#guard S "0" 0 == (zero, .eq)
#guard S "1/3" 0 == (nan, .eq)

-- correctly rounded values at exact rationals
#guard S "1/3" 53 == (F "5894215658275015/18014398509481984" 53, .gt)
#guard S "1/10" 53 == (F "1798438952039115/18014398509481984" 53, .gt)
#guard S "22/7" 53 == (F "-5831425920677443/4611686018427387904" 53, .gt)
#guard sinPrecRound (F "22/7" 53) 53 .Nearest
  == (F "-5831425920677151/4611686018427387904" 53, .lt)
#guard S "-22/7" 53 == (F "5831425920677443/4611686018427387904" 53, .lt)
#guard S "-7/5" 53 == (F "-4438071036768385/4503599627370496" 53, .gt)
#guard S "355/113" 53 == (F "-2519516530516539/9444732965739290427392" 53, .lt)
#guard S "-1/1000" 53 == (F "-2305842624906545/2305843009213693952" 53, .lt)
#guard S "1000000000000000000000000000000" 53 == (F "-811700891742577/9007199254740992" 53, .lt)

-- agreement with the float `sin` at representable arguments
#guard S "1/2" 53 == sinPrecRound (F "1/2" 53) 53 .Nearest
#guard S "-3" 53 == sinPrecRound (F "-3" 53) 53 .Nearest
#guard S "1000000000000" 53 == sinPrecRound (F "1000000000000" 53) 53 .Nearest
#guard S "1/1024" 53 == sinPrecRound (F "1/1024" 53) 53 .Nearest

-- directed modes and other precisions
#guard S "1/3" 53 .Floor == (F "2947107829137507/9007199254740992" 53, .lt)
#guard S "1/3" 53 .Ceiling == (F "5894215658275015/18014398509481984" 53, .gt)
#guard S "22/7" 53 .Floor == (F "-1457856480169361/1152921504606846976" 53, .lt)
#guard S "22/7" 53 .Ceiling == (F "-5831425920677443/4611686018427387904" 53, .gt)
#guard S "-22/7" 53 .Floor == (F "5831425920677443/4611686018427387904" 53, .lt)
#guard S "-22/7" 53 .Ceiling == (F "1457856480169361/1152921504606846976" 53, .gt)
#guard S "1/3" 20 == (F "686177/2097152" 20, .lt)
#guard sinRat (Q "1/3") 53 == F "5894215658275015/18014398509481984" 53
#guard toString (sinRat (Q "1/3") 200)
  == "0.3271946967961522441733440852676206060643014068937597915900562"
#guard toString (sinRat (Q "355/113") 200)
  == "-2.667641890624191484063745288734688868221054266212710251192494e-7"

-- tiny arguments (`±1/(3·2^1000)`): `q − q³/6 < sin q < q`, rounded without a series
private def tinyQ : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 3) <<< (1000 : Nat))
private def tinyLo : AzFloat := (ofAzRatRound tinyQ 53 .Floor).1
private def tinyHi : AzFloat := (ofAzRatRound tinyQ 53 .Ceiling).1
#guard sinRatPrecRound tinyQ 53 .Nearest == (tinyLo, .lt)
#guard sinRatPrecRound tinyQ 53 .Floor == (tinyLo, .lt)
#guard sinRatPrecRound tinyQ 53 .Ceiling == (tinyHi, .gt)
#guard sinRatPrecRound (-tinyQ) 53 .Nearest == (-tinyLo, .gt)
#guard sinRatPrecRound (-tinyQ) 53 .Floor == (-tinyHi, .lt)
#guard sinRatPrecRound (-tinyQ) 53 .Ceiling == (-tinyLo, .gt)
#guard (sinTinyRat? tinyQ 53 .Nearest).isSome
#guard (sinTinyRat? (Q "1/1000") 53 .Nearest).isNone
