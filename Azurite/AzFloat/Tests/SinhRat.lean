/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.SinhRat
import Azurite.AzFloat.Sinh
import Azurite.AzFloat.ExpRat
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse
import Azurite.AzFloat.OfString

/-!
# Tests for `sinh q` of a rational

The special values (`0`, `p = 0`), the correctly rounded 53-bit values at exact rationals from
`10^(−30)/3` to `700/3` in three modes, 1-, 2-, 20-, 113- and 200-bit results, agreement with
the float `sinh` at representable arguments, oddness, 200-bit strings, tiny rationals
`±2^(−5000)`, `±1/(3·2^5000)` (the value is just outside `q`, at no cost), and a large rational
(where `sinh q` rounds like `exp q / 2`).  References: an independent 6000-bit fixed-point
evaluation of `(e^q − e^(−q))/2` rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def T (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  sinhRatPrecRound (Q q) p m
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (T "0" 53) == ("0.0", .eq)
#guard D (T "0" 0) == ("0.0", .eq)
#guard D (T "1/3" 0) == ("NaN", .eq)

-- correctly rounded values at exact rationals
#guard D (T "1" 53) == ("1.1752011936438014", .lt)
#guard D (T "-1" 53) == ("-1.1752011936438014", .gt)
#guard D (T "1/3" 53) == ("0.3395405572561501", .lt)
#guard D (T "-2/7" 53) == ("-0.289617452186032", .lt)
#guard D (T "22/7" 53) == ("11.563406494500514", .gt)
#guard D (T "355/113" 53) == ("11.548742449576174", .lt)
#guard D (T "-7/5" 53) == ("-1.904301501451534", .lt)
#guard D (T "10" 53) == ("11013.232874703393", .gt)
#guard D (T "-100/3" 53) == ("-149779623457090.94", .lt)
#guard D (T "1/1000" 53) == ("0.001000000166666675", .gt)
#guard D (T "-1/1000000007" 53) == ("-9.99999993e-10", .lt)
#guard D (T "3/1125899906842624" 53) == ("2.6645352591003757e-15", .lt)
#guard D (T "1/3000000000000000000000000000000" 53) == ("3.3333333333333333e-31", .lt)
#guard D (T "700/3" 53) == ("1.0823036301006912e101", .lt)
#guard D (T "1/3" 53 .Floor) == ("0.3395405572561501", .lt)
#guard D (T "-2/7" 53 .Floor) == ("-0.289617452186032", .lt)
#guard D (T "22/7" 53 .Floor) == ("11.563406494500512", .lt)
#guard D (T "-100/3" 53 .Floor) == ("-149779623457090.94", .lt)
#guard D (T "1/1000000007" 53 .Floor) == ("9.999999929999998e-10", .lt)
#guard D (T "1/3" 53 .Ceiling) == ("0.3395405572561502", .gt)
#guard D (T "-2/7" 53 .Ceiling) == ("-0.28961745218603197", .gt)
#guard D (T "22/7" 53 .Ceiling) == ("11.563406494500514", .gt)
#guard D (T "-100/3" 53 .Ceiling) == ("-149779623457090.9", .gt)
#guard D (T "1/1000000007" 53 .Ceiling) == ("9.99999993e-10", .gt)
#guard D (T "1/3" 20) == ("0.3395405", .lt)
#guard D (T "1/3" 1) == ("0.2", .lt)
#guard D (T "-22/7" 2) == ("-12.0", .lt)
#guard D (T "1/3" 113) == ("0.33954055725615013910126061133860357", .lt)
#guard D (T "-7/5" 200) == ("-1.904301501451534055142123827697426309551638683721294791202832", .gt)

-- agreement with the float `sinh` at representable arguments, oddness
#guard T "3/2" 53 == sinhPrecRound (X "1.5" 53) 53 .Nearest
#guard T "-5/1024" 53 .Floor == sinhPrecRound (X "-0.0048828125" 53) 53 .Floor
#guard T "100" 20 .Ceiling == sinhPrecRound (X "100" 53) 20 .Ceiling
#guard sinhRat (Q "1/3") 53 == (T "1/3" 53).1
private def odd (q : String) (p : Nat) (m : RoundingMode) : Bool :=
  let r := T q p (-m)
  sinhRatPrecRound (-(Q q)) p m == (-r.1, r.2.swap)
#guard odd "1/3" 53 .Nearest && odd "22/7" 53 .Floor && odd "1/1000000007" 20 .Ceiling
#guard toString (sinhRat (Q "1/3") 200)
  == "0.3395405572561501391012606113386035850723972276889639127383233"
#guard toString (sinhRat (Q "-22/7") 200)
  == "-11.56340649450051381641646085061672691915107789969396925396816"

-- tiny rationals: just outside `q`
private def pw (k : Nat) : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 1) <<< k)
private def up : AzFloat := X "1.0000000000000002" 53
#guard D (sinhRatPrecRound (pw 5000) 53 .Nearest) == ("7.079811261048173e-1506", .lt)
#guard D (sinhRatPrecRound (pw 5000) 53 .Floor) == ("7.079811261048173e-1506", .lt)
#guard D (sinhRatPrecRound (pw 5000) 53 .Ceiling) == ("7.079811261048174e-1506", .gt)
#guard D (sinhRatPrecRound (-(pw 5000)) 53 .Nearest) == ("-7.079811261048173e-1506", .gt)
#guard D (sinhRatPrecRound (-(pw 5000)) 53 .Floor) == ("-7.079811261048174e-1506", .lt)
#guard D (sinhRatPrecRound (Q "1/3" * pw 5000) 53 .Nearest) == ("2.3599370870160575e-1506", .lt)
#guard D (sinhRatPrecRound (Q "1/3" * pw 5000) 53 .Ceiling) == ("2.359937087016058e-1506", .gt)
#guard D (sinhRatPrecRound (Q "-1/3" * pw 5000) 53 .Floor) == ("-2.359937087016058e-1506", .lt)

-- a large rational: `sinh q` rounds like `exp q / 2`
private def big (q : String) (p : Nat) (m : RoundingMode) : Bool :=
  let r := expRatPrecRound (Q q) p m
  T q p m == (h r.1 (-1), r.2)
#guard big "1000000/3" 53 .Nearest && big "1000000/3" 53 .Floor && big "12345/7" 113 .Ceiling
#guard odd "1000000/3" 53 .Floor
