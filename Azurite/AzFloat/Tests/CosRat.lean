/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Conversion
import Azurite.AzFloat.Cos
import Azurite.AzFloat.CosRat
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `cos q` of a rational

The special values (`cos 0 = 1`, `p = 0`), the correctly rounded 53-bit values of `cos q` at the
exact rationals `1/3`, `1/10`, `22/7`, `−7/5` (which differs in the last place from `cos` of the
53-bit float nearest `−7/5`), `355/113` (`cos ≈ −1 + 3.6·10⁻¹⁴`), `−1/1000`, `10³⁰`, `2⁻¹⁰⁰`,
agreement with the float `cos` at exactly representable arguments (`1/2`, `3`, `10¹²`,
`1/1024`), the directed modes, a 20-bit result, and 200-bit values of `cos (1/3)` and
`cos (355/113)`.  References: a 240-digit evaluation rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def C (q : String) (p : Nat) (m : RoundingMode := .Nearest) := cosRatPrecRound (Q q) p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (C "0" 53) == ("1.0", .eq)
#guard D (C "0" 0) == ("NaN", .eq)
#guard D (C "1/3" 0) == ("NaN", .eq)

-- correctly rounded values at exact rationals
#guard D (C "1/3" 53) == ("0.9449569463147377", .gt)
#guard D (C "1/10" 53) == ("0.9950041652780258", .gt)
#guard D (C "22/7" 53) == ("-0.999999200533553", .lt)
#guard D (C "-7/5" 53) == ("0.16996714290024093", .lt)
#guard D (cosPrecRound (X "-1.4" 53) 53 .Nearest) == ("0.16996714290024104", .gt)
#guard D (C "355/113" 53) == ("-0.9999999999999645", .lt)
#guard D (C "-1/1000" 53) == ("0.9999995000000417", .gt)
#guard D (C "1000000000000000000000000000000" 53) == ("-0.9959311944053957", .gt)
#guard D (C "1/1267650600228229401496703205376" 53) == ("1.0", .gt)

-- agreement with the float `cos` at representable arguments
#guard C "1/2" 53 == cosPrecRound (X "0.5" 53) 53 .Nearest
#guard C "3" 53 == cosPrecRound (X "3" 53) 53 .Nearest
#guard C "1000000000000" 53 == cosPrecRound (X "1000000000000" 53) 53 .Nearest
#guard C "1/1024" 53 == cosPrecRound (X "0.0009765625" 53) 53 .Nearest

-- directed modes and other precisions
#guard D (C "1/3" 53 .Floor) == ("0.9449569463147376", .lt)
#guard D (C "1/3" 53 .Ceiling) == ("0.9449569463147377", .gt)
#guard D (C "22/7" 53 .Floor) == ("-0.999999200533553", .lt)
#guard D (C "22/7" 53 .Ceiling) == ("-0.9999992005335528", .gt)
#guard D (C "1/3" 20) == ("0.944957", .lt)
#guard toString (cosRat (Q "1/3") 53) == "0.9449569463147377"
#guard toString (cosRat (Q "1/3") 200)
  == "0.944956946314737664388284007675880607845852699565140737677646"
#guard toString (cosRat (Q "355/113") 200)
  == "-0.9999999999999644184337169343129714252032324580791768112016077"

-- tiny arguments (`1/(3·2^1000)`): rounded without touching the argument
private def belowOne : AzFloat := X "0.9999999999999999" 53
private def tinyQ : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 3) <<< (1000 : Nat))
#guard D (cosRatPrecRound tinyQ 53 .Nearest) == ("1.0", .gt)
#guard D (cosRatPrecRound tinyQ 53 .Floor) == ("0.9999999999999999", .lt)
#guard D (cosRatPrecRound (-tinyQ) 53 .Ceiling) == ("1.0", .gt)
