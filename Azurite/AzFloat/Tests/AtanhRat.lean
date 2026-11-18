/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AtanhRat
import Azurite.AzFloat.Atanh
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `atanh q` of a rational

The special values (`0`; `atanh (±1) = ±∞`; `NaN` for `|q| > 1`; `p = 0`), the correctly
rounded 53-bit values at exact rationals from `10^(−30)/3` to `1 − 10^(−30)/3` in three modes,
1-, 2-, 20-, 113- and 200-bit results, agreement with the float `atanh` at representable
arguments, oddness, 200-bit strings, tiny rationals `±2^(−5000)`, `±1/(3·2^5000)` (just outside
`q`, at no cost), and `±(1 − 2^(−5000))` (value `≈ 2500.5 ln 2`).  References: an independent
6000-bit fixed-point evaluation of `(1/2) ln ((1 + q)/(1 − q))` rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
private def up : AzFloat := X "1.0000000000000002" 53
private def T (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  atanhRatPrecRound (Q q) p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (T "0" 53) == ("0.0", .eq)
#guard D (T "0" 0) == ("0.0", .eq)
#guard D (T "1" 53) == ("Infinity", .eq)
#guard D (T "-3/3" 53) == ("-Infinity", .eq)
#guard D (T "1" 0) == ("Infinity", .eq)
#guard D (T "2" 53) == ("NaN", .eq)
#guard D (T "-1000001/1000000" 53) == ("NaN", .eq)
#guard D (T "1/3" 0) == ("NaN", .eq)

-- correctly rounded values at exact rationals
#guard D (T "1/2" 53) == ("0.5493061443340549", .gt)
#guard D (T "-1/2" 53) == ("-0.5493061443340549", .lt)
#guard D (T "1/3" 53) == ("0.34657359027997264", .lt)
#guard D (T "-2/7" 53) == ("-0.29389333245105953", .lt)
#guard D (T "7/22" 53) == ("0.329622814442132", .gt)
#guard D (T "113/355" 53) == ("0.3297652848804802", .gt)
#guard D (T "99/100" 53) == ("2.646652412362246", .lt)
#guard D (T "-999999999/1000000000" 53) == ("-10.708206508503178", .gt)
#guard D (T "1/1000" 53) == ("0.0010000003333335333", .lt)
#guard D (T "-1/1000000007" 53) == ("-9.99999993e-10", .lt)
#guard D (T "3/1125899906842624" 53) == ("2.6645352591003757e-15", .lt)
#guard D (T "1/3000000000000000000000000000000" 53) == ("3.3333333333333333e-31", .lt)
#guard D (T "2999999999999999999999999999999/3000000000000000000000000000000" 53)
  == ("35.43465612952471", .lt)
#guard D (T "1/3" 53 .Floor) == ("0.34657359027997264", .lt)
#guard D (T "-2/7" 53 .Floor) == ("-0.29389333245105953", .lt)
#guard D (T "99/100" 53 .Floor) == ("2.646652412362246", .lt)
#guard D (T "1/1000000007" 53 .Floor) == ("9.999999929999998e-10", .lt)
#guard D (T "1/3" 53 .Ceiling) == ("0.3465735902799727", .gt)
#guard D (T "-2/7" 53 .Ceiling) == ("-0.2938933324510595", .gt)
#guard D (T "99/100" 53 .Ceiling) == ("2.6466524123622466", .gt)
#guard D (T "1/1000000007" 53 .Ceiling) == ("9.99999993e-10", .gt)
#guard D (T "1/3" 20) == ("0.3465734", .lt)
#guard D (T "1/3" 1) == ("0.2", .lt)
#guard D (T "-7/22" 2) == ("-0.4", .lt)
#guard D (T "1/3" 113) == ("0.3465735902799726547086160607290883", .gt)
#guard D (T "-5/7" 200) == ("-0.895879734614027500406238679190351136361495346091502352927687", .lt)

-- agreement with the float `atanh` at representable arguments, oddness
#guard T "3/4" 53 == atanhPrecRound (X "0.75" 53) 53 .Nearest
#guard T "-5/1024" 53 .Floor == atanhPrecRound (X "-0.0048828125" 53) 53 .Floor
#guard T "1023/1024" 20 .Ceiling == atanhPrecRound (X "0.9990234375" 53) 20 .Ceiling
#guard atanhRat (Q "1/3") 53 == (T "1/3" 53).1
private def odd (q : AzRat) (p : Nat) (m : RoundingMode) : Bool :=
  let r := atanhRatPrecRound q p (-m)
  atanhRatPrecRound (-q) p m == (-r.1, r.2.swap)
#guard odd (Q "1/3") 53 .Nearest && odd (Q "7/22") 53 .Floor
#guard odd (Q "1/1000000007") 20 .Ceiling && odd (Q "999999/1000000") 53 .Floor
#guard toString (atanhRat (Q "1/3") 200) == "0.3465735902799726547086160607290882840377500671801276\
  2706034"
#guard toString (atanhRat (Q "-7/22") 200) == "-0.3296228144421319805936337311065991306607105009157\
  38452637164"

-- tiny rationals: just outside `q`
private def pw (k : Nat) : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 1) <<< k)
#guard D (atanhRatPrecRound (pw 5000) 53 .Nearest) == ("7.079811261048173e-1506", .lt)
#guard D (atanhRatPrecRound (pw 5000) 53 .Floor) == ("7.079811261048173e-1506", .lt)
#guard D (atanhRatPrecRound (pw 5000) 53 .Ceiling) == ("7.079811261048174e-1506", .gt)
#guard D (atanhRatPrecRound (-(pw 5000)) 53 .Nearest) == ("-7.079811261048173e-1506", .gt)
#guard D (atanhRatPrecRound (-(pw 5000)) 53 .Floor) == ("-7.079811261048174e-1506", .lt)
#guard D (atanhRatPrecRound (Q "1/3" * pw 5000) 53 .Nearest) == ("2.3599370870160575e-1506", .lt)
#guard D (atanhRatPrecRound (Q "1/3" * pw 5000) 53 .Ceiling) == ("2.359937087016058e-1506", .gt)

-- next to `±1`
#guard D (atanhRatPrecRound (1 - pw 5000) 53 .Nearest) == ("1733.2145249901432", .lt)
#guard D (atanhRatPrecRound (1 - pw 5000) 53 .Floor) == ("1733.2145249901432", .lt)
#guard D (atanhRatPrecRound (1 - pw 5000) 53 .Ceiling) == ("1733.2145249901434", .gt)
#guard odd (1 - pw 5000) 53 .Floor
