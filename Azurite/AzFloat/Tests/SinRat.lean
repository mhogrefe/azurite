/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.OfString
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
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def S (q : String) (p : Nat) (m : RoundingMode := .Nearest) := sinRatPrecRound (Q q) p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (S "0" 53) == ("0.0", .eq)
#guard D (S "0" 0) == ("0.0", .eq)
#guard D (S "1/3" 0) == ("NaN", .eq)

-- correctly rounded values at exact rationals
#guard D (S "1/3" 53) == ("0.32719469679615226", .gt)
#guard D (S "1/10" 53) == ("0.09983341664682815", .gt)
#guard D (S "22/7" 53) == ("-0.0012644889303773533", .gt)
#guard D (sinPrecRound (X "3.142857142857143" 53) 53 .Nearest) == ("-0.00126448893037729", .lt)
#guard D (S "-22/7" 53) == ("0.0012644889303773533", .lt)
#guard D (S "-7/5" 53) == ("-0.9854497299884601", .gt)
#guard D (S "355/113" 53) == ("-2.6676418906241917e-7", .lt)
#guard D (S "-1/1000" 53) == ("-0.0009999998333333417", .lt)
#guard D (S "1000000000000000000000000000000" 53) == ("-0.09011690191213806", .lt)

-- agreement with the float `sin` at representable arguments
#guard S "1/2" 53 == sinPrecRound (X "0.5" 53) 53 .Nearest
#guard S "-3" 53 == sinPrecRound (X "-3" 53) 53 .Nearest
#guard S "1000000000000" 53 == sinPrecRound (X "1000000000000" 53) 53 .Nearest
#guard S "1/1024" 53 == sinPrecRound (X "0.0009765625" 53) 53 .Nearest

-- directed modes and other precisions
#guard D (S "1/3" 53 .Floor) == ("0.3271946967961522", .lt)
#guard D (S "1/3" 53 .Ceiling) == ("0.32719469679615226", .gt)
#guard D (S "22/7" 53 .Floor) == ("-0.0012644889303773535", .lt)
#guard D (S "22/7" 53 .Ceiling) == ("-0.0012644889303773533", .gt)
#guard D (S "-22/7" 53 .Floor) == ("0.0012644889303773533", .lt)
#guard D (S "-22/7" 53 .Ceiling) == ("0.0012644889303773535", .gt)
#guard D (S "1/3" 20) == ("0.3271947", .lt)
#guard toString (sinRat (Q "1/3") 53) == "0.32719469679615226"
#guard toString (sinRat (Q "1/3") 200)
  == "0.3271946967961522441733440852676206060643014068937597915900562"
#guard toString (sinRat (Q "355/113") 200)
  == "-2.667641890624191484063745288734688868221054266212710251192494e-7"

-- tiny arguments (`±1/(3·2^1000)`): `q − q³/6 < sin q < q`, rounded without a series
private def tinyQ : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 3) <<< (1000 : Nat))
private def tinyLo : AzFloat := (ofAzRatRound tinyQ 53 .Floor).1
private def tinyHi : AzFloat := (ofAzRatRound tinyQ 53 .Ceiling).1
#guard D (sinRatPrecRound tinyQ 53 .Nearest) == ("3.110878728344063e-302", .lt)
#guard D (sinRatPrecRound tinyQ 53 .Floor) == ("3.110878728344063e-302", .lt)
#guard D (sinRatPrecRound tinyQ 53 .Ceiling) == ("3.1108787283440633e-302", .gt)
#guard D (sinRatPrecRound (-tinyQ) 53 .Nearest) == ("-3.110878728344063e-302", .gt)
#guard D (sinRatPrecRound (-tinyQ) 53 .Floor) == ("-3.1108787283440633e-302", .lt)
#guard D (sinRatPrecRound (-tinyQ) 53 .Ceiling) == ("-3.110878728344063e-302", .gt)
#guard (sinTinyRat? tinyQ 53 .Nearest).isSome
#guard (sinTinyRat? (Q "1/1000") 53 .Nearest).isNone
