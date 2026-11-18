/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.GdInv
import Azurite.AzFloat.GdInvRat
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse
import Azurite.AzFloat.OfString

/-!
# Tests for the inverse Gudermannian of a rational

`gd⁻¹ 0 = 0`, `p = 0`; the domain test on either side of `π/2` (`157/100`, `1570796/10^6`
inside; `1570797/10^6`, `355/226`, `11/7`, `2`, `−100` outside); the correctly rounded 53-bit
values from `1/1000` to `1570796/10^6`; 200- and 300-bit results; directed rounding and
oddness; a tiny argument; agreement with the float function on dyadic arguments.  References:
a 500-digit evaluation of `ln ((1 + sin q)/cos q)` rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def A (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  gdInvRatPrecRound (Q q) p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (A "0" 53) == ("0.0", .eq)
#guard D (A "0" 0) == ("0.0", .eq)
#guard D (A "1/3" 0) == ("NaN", .eq)

-- the domain `|q| < π/2`
#guard gdInvRatInDomain (Q "1/3") && gdInvRatInDomain (Q "-1") && gdInvRatInDomain (Q "3/2")
#guard gdInvRatInDomain (Q "157/100") && gdInvRatInDomain (Q "-1570796/1000000")
#guard !gdInvRatInDomain (Q "1570797/1000000") && !gdInvRatInDomain (Q "355/226")
#guard !gdInvRatInDomain (Q "-11/7") && !gdInvRatInDomain (Q "2") && !gdInvRatInDomain (Q "5")
#guard D (A "1570797/1000000" 53) == ("NaN", .eq)
#guard D (A "355/226" 53) == ("NaN", .eq)
#guard D (A "11/7" 53) == ("NaN", .eq)
#guard D (A "-11/7" 53) == ("NaN", .eq)
#guard D (A "2" 53) == ("NaN", .eq)
#guard D (A "-100" 53) == ("NaN", .eq)
#guard D (A "100000000000000000000000000000000000000000000000000/3" 53) == ("NaN", .eq)

-- correctly rounded 53-bit values
#guard D (A "1/1000" 53) == ("0.0010000001666667082", .lt)
#guard D (A "1/3" 53) == ("0.33968337608418653", .gt)
#guard D (A "-2/3" 53) == ("-0.7223612791553695", .gt)
#guard D (A "7/5" 53) == ("2.457995590372979", .lt)
#guard D (A "157/100" 53) == ("7.8286480377336956", .lt)
#guard D (A "-157/100" 53) == ("-7.8286480377336956", .gt)
#guard D (A "1570796/1000000" 53) == ("15.627080270862656", .lt)

-- other precisions, directed rounding, oddness
#guard D (A "1/3" 200) == ("0.3396833760841865123938864145882995892568868578520601800068325", .gt)
#guard D (A "157/100" 300)
  == ("7.8286480377336959586311215099644445159596123712331239942727805177049941347517518914842979\
    1", .gt)
#guard D (A "1/3" 53 .Floor) == ("0.3396833760841865", .lt)
#guard (A "-7/5" 53 .Ceiling).1 == -(A "7/5" 53 .Floor).1

-- a tiny argument: the value is just outside `q`
private def tinyQ : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 3) <<< (1000 : Nat))
#guard D (gdInvRatPrecRound tinyQ 53 .Floor) == ("3.110878728344063e-302", .lt)
#guard (gdInvRatPrecRound tinyQ 53 .Ceiling).2 == .gt

-- agreement with the float function on dyadic arguments
#guard A "3/8" 53 == gdInvPrecRound (X "0.375" 53) 53 .Nearest
#guard A "1" 53 == gdInvPrecRound (X "1" 53) 53 .Nearest
#guard A "-5/4" 53 .Floor == gdInvPrecRound (X "-1.25" 53) 53 .Floor
#guard A "3/2" 100 == gdInvPrecRound (X "1.5" 53) 100 .Nearest
#guard A "201/128" 53 .Ceiling == gdInvPrecRound (X "1.5703125" 53) 53 .Ceiling
