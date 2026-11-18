/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Atan
import Azurite.AzFloat.AtanRat
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `arctan q` of a rational

The special values (`arctan 0 = 0` at every precision, `p = 0`), the correctly rounded 53-bit
values of `arctan q` at the exact rationals `1/3` (same significand as `arctan` of the 53-bit
float nearest `1/3`, but on the other side of the exact value), `1/10`, `±22/7`, `−7/5`,
`355/113`, `−1/1000`, `10³⁰`, the neighbours `1 ± 10⁻⁶` of `1`, `1/(10⁹ + 7)`, `123456.789`,
agreement with the float `atan` at exactly representable arguments (`1/2`, `−3`, `10¹²`,
`1/1024`, `1`), the directed modes, 1-, 20-, 113- and 400-bit results, 200-bit strings, and the
tiny path at `±1/(3·2^1000)` (`arctan q` rounds like a value just inside `q`).  References: an
independent 1400-bit fixed-point evaluation rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def T (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  atanRatPrecRound (Q q) p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (T "0" 53) == ("0.0", .eq)
#guard D (T "0" 0) == ("0.0", .eq)
#guard D (T "1/3" 0) == ("NaN", .eq)

-- correctly rounded values at exact rationals
#guard D (T "1/3" 53) == ("0.3217505543966422", .lt)
#guard D (T "1/10" 53) == ("0.09966865249116202", .lt)
#guard D (T "22/7" 53) == ("1.2627435457711202", .gt)
#guard D (T "-22/7" 53) == ("-1.2627435457711202", .lt)
#guard D (T "-7/5" 53) == ("-0.9505468408120752", .lt)
#guard D (T "355/113" 53) == ("1.2626272802211267", .lt)
#guard D (T "-1/1000" 53) == ("-0.0009999996666668666", .gt)
#guard D (T "1000000000000000000000000000000" 53) == ("1.5707963267948966", .lt)
#guard D (T "1000001/1000000" 53) == ("0.7853986633971983", .gt)
#guard D (T "999999/1000000" 53) == ("0.7853976633971983", .lt)
#guard D (T "1/1000000007" 53) == ("9.99999993e-10", .gt)
#guard D (T "123456789/1000" 53) == ("1.570788226794823", .lt)
#guard D (atanPrecRound (X "0.3333333333333333" 53) 53 .Nearest) == ("0.3217505543966422", .gt)

-- agreement with the float `atan` at representable arguments
#guard T "1/2" 53 == atanPrecRound (X "0.5" 53) 53 .Nearest
#guard T "-3" 53 == atanPrecRound (X "-3" 53) 53 .Nearest
#guard T "1000000000000" 53 == atanPrecRound (X "1000000000000" 53) 53 .Nearest
#guard T "1/1024" 53 == atanPrecRound (X "0.0009765625" 53) 53 .Nearest
#guard T "1" 53 == atanPrecRound (X "1" 53) 53 .Nearest
#guard T "-1" 200 .Floor == atanPrecRound (X "-1" 53) 200 .Floor

-- directed modes and other precisions
#guard D (T "1/3" 53 .Floor) == ("0.3217505543966422", .lt)
#guard D (T "1/3" 53 .Ceiling) == ("0.32175055439664224", .gt)
#guard D (T "22/7" 53 .Floor) == ("1.26274354577112", .lt)
#guard D (T "22/7" 53 .Ceiling) == ("1.2627435457711202", .gt)
#guard D (T "-22/7" 53 .Floor) == ("-1.2627435457711202", .lt)
#guard D (T "-22/7" 53 .Ceiling) == ("-1.26274354577112", .gt)
#guard D (T "1/3" 20) == ("0.3217506", .gt)
#guard D (T "1/3" 1) == ("0.2", .lt)
#guard D (T "1/3" 113) == ("0.3217505543966421934014046143586613", .lt)
#guard D (T "-7/5" 113) == ("-0.9505468408120751478947891354638191", .gt)
#guard D (T "1/3" 400) == ("0.321750554396642193401404614358661319020755295557656191432803059356756\
  2374058105443564084223506413744390071693771297391482", .lt)
#guard toString (atanRat (Q "1/3") 53) == "0.3217505543966422"
#guard toString (atanRat (Q "1/3") 200) == "0.32175055439664219340140461435866131902075529555765619\
  1432803"
#guard toString (atanRat (Q "355/113") 200) == "1.2626272802211267126987321884110788752799549704226\
  6931780194"

-- tiny arguments (`±1/(3·2^1000)`): `q − q³/3 < arctan q < q`, rounded without the iteration
private def tinyQ : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 3) <<< (1000 : Nat))
private def tinyLo : AzFloat := (ofAzRatRound tinyQ 53 .Floor).1
private def tinyHi : AzFloat := (ofAzRatRound tinyQ 53 .Ceiling).1
#guard D (atanRatPrecRound tinyQ 53 .Nearest) == ("3.110878728344063e-302", .lt)
#guard D (atanRatPrecRound tinyQ 53 .Floor) == ("3.110878728344063e-302", .lt)
#guard D (atanRatPrecRound tinyQ 53 .Ceiling) == ("3.1108787283440633e-302", .gt)
#guard D (atanRatPrecRound (-tinyQ) 53 .Nearest) == ("-3.110878728344063e-302", .gt)
#guard D (atanRatPrecRound (-tinyQ) 53 .Floor) == ("-3.1108787283440633e-302", .lt)
#guard D (atanRatPrecRound (-tinyQ) 53 .Ceiling) == ("-3.110878728344063e-302", .gt)
#guard (atanTinyRat? tinyQ 53 .Nearest).isSome
#guard (atanTinyRat? (Q "1/1000") 53 .Nearest).isNone
