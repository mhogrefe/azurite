/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AsinhRat
import Azurite.AzFloat.Asinh
import Azurite.AzFloat.LnRat
import Azurite.AzFloat.ToString
import Azurite.AzFloat.OfString
import Azurite.AzRat.Parse

/-!
# Tests for `asinh q` of a rational

The special values (`0`, `p = 0`), the correctly rounded 53-bit values at exact rationals from
`10^(−30)/3` to `700/3` in three modes, 1-, 2-, 20-, 113- and 200-bit results, agreement with
the float `asinh` at representable arguments, oddness, 200-bit strings, tiny rationals
`±2^(−5000)`, `±1/(3·2^5000)` (just inside `q`, at no cost), and a huge rational (where
`asinh q` rounds like `ln (2q)`).  References: an independent 6000-bit fixed-point evaluation
of `ln (q + √(q² + 1))` rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
private def dn : AzFloat := X "0.9999999999999999" 53
private def T (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  asinhRatPrecRound (Q q) p m

-- special values
#guard D (T "0" 53) == ("0.0", .eq)
#guard D (T "0" 0) == ("0.0", .eq)
#guard D (T "1/3" 0) == ("NaN", .eq)

-- correctly rounded values at exact rationals
#guard D (T "1" 53) == ("0.881373587019543", .gt)
#guard D (T "-1" 53) == ("-0.881373587019543", .lt)
#guard D (T "1/3" 53) == ("0.32745015023725843", .lt)
#guard D (T "-2/7" 53) == ("-0.2819632391899829", .gt)
#guard D (T "22/7" 53) == ("1.86267921113461", .gt)
#guard D (T "355/113" 53) == ("1.862295824224284", .lt)
#guard D (T "-7/5" 53) == ("-1.1379820462933674", .lt)
#guard D (T "10" 53) == ("2.99822295029797", .gt)
#guard D (T "-100/3" 53) == ("-4.199930001980373", .lt)
#guard D (T "1/1000" 53) == ("0.0009999998333334083", .lt)
#guard D (T "-1/1000000007" 53) == ("-9.99999993e-10", .lt)
#guard D (T "3/1125899906842624" 53) == ("2.6645352591003757e-15", .gt)
#guard D (T "1/3000000000000000000000000000000" 53) == ("3.3333333333333333e-31", .lt)
#guard D (T "700/3" 53) == ("6.1456198187403475", .lt)
#guard D (T "1/3" 53 .Floor) == ("0.32745015023725843", .lt)
#guard D (T "-2/7" 53 .Floor) == ("-0.28196323918998295", .lt)
#guard D (T "22/7" 53 .Floor) == ("1.8626792111346098", .lt)
#guard D (T "-100/3" 53 .Floor) == ("-4.199930001980373", .lt)
#guard D (T "1/1000000007" 53 .Floor) == ("9.999999929999998e-10", .lt)
#guard D (T "1/3" 53 .Ceiling) == ("0.3274501502372585", .gt)
#guard D (T "-2/7" 53 .Ceiling) == ("-0.2819632391899829", .gt)
#guard D (T "22/7" 53 .Ceiling) == ("1.86267921113461", .gt)
#guard D (T "-100/3" 53 .Ceiling) == ("-4.1999300019803725", .gt)
#guard D (T "1/1000000007" 53 .Ceiling) == ("9.99999993e-10", .gt)
#guard D (T "1/3" 20) == ("0.3274503", .gt)
#guard D (T "1/3" 1) == ("0.2", .lt)
#guard D (T "-22/7" 2) == ("-2.0", .lt)
#guard D (T "1/3" 113) == ("0.3274501502372584433225352599882581", .lt)
#guard D (T "-7/5" 200) == ("-1.137982046293367397387547910702065720248638169144822891324286", .lt)

-- agreement with the float `asinh` at representable arguments, oddness
#guard T "3/2" 53 == asinhPrecRound (X "1.5" 53) 53 .Nearest
#guard T "-5/1024" 53 .Floor == asinhPrecRound (X "-0.0048828125" 53) 53 .Floor
#guard T "100" 20 .Ceiling == asinhPrecRound (X "100" 53) 20 .Ceiling
#guard asinhRat (Q "1/3") 53 == (T "1/3" 53).1
private def odd (q : AzRat) (p : Nat) (m : RoundingMode) : Bool :=
  let r := asinhRatPrecRound q p (-m)
  asinhRatPrecRound (-q) p m == (-r.1, r.2.swap)
#guard odd (Q "1/3") 53 .Nearest && odd (Q "22/7") 53 .Floor
#guard odd (Q "1/1000000007") 20 .Ceiling && odd (Q "1000000/3") 53 .Floor
#guard toString (asinhRat (Q "1/3") 200)
  == "0.3274501502372584433225352599882581277005245289907674512756294"
#guard toString (asinhRat (Q "-22/7") 200)
  == "-1.862679211134609985019001482949627540444162658920310431618422"

-- tiny rationals: just inside `q`
private def pw (k : Nat) : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 1) <<< k)
#guard D (asinhRatPrecRound (pw 5000) 53 .Nearest) == ("7.079811261048173e-1506", .gt)
#guard D (asinhRatPrecRound (pw 5000) 53 .Ceiling) == ("7.079811261048173e-1506", .gt)
#guard D (asinhRatPrecRound (pw 5000) 53 .Floor) == ("7.079811261048172e-1506", .lt)
#guard D (asinhRatPrecRound (-(pw 5000)) 53 .Nearest) == ("-7.079811261048173e-1506", .lt)
#guard D (asinhRatPrecRound (-(pw 5000)) 53 .Ceiling) == ("-7.079811261048172e-1506", .gt)
#guard D (asinhRatPrecRound (Q "1/3" * pw 5000) 53 .Nearest) == ("2.3599370870160575e-1506", .lt)
#guard D (asinhRatPrecRound (Q "1/3" * pw 5000) 53 .Ceiling) == ("2.359937087016058e-1506", .gt)

-- a huge rational: `asinh q` rounds like `ln (2q)`
private def bigq : AzRat := Q "2/3" * (pw 5000)⁻¹
#guard asinhRatPrecRound (Q "1/3" * (pw 5000)⁻¹) 53 .Nearest == lnRatPrecRound bigq 53 .Nearest
#guard asinhRatPrecRound (Q "1/3" * (pw 5000)⁻¹) 53 .Floor == lnRatPrecRound bigq 53 .Floor
