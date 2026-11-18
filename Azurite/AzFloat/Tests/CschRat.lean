/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.CschRat
import Azurite.AzFloat.Csch
import Azurite.AzFloat.ExpRat
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `csch q` of a rational

The special values (`csch 0 = +∞`, `p = 0`), the correctly rounded 53-bit values at exact
rationals from `10^(−30)/3` to `700/3` in three modes, 1-, 2-, 20-, 113- and 200-bit results,
agreement with the float `csch` at representable arguments, oddness, 200-bit strings, tiny
rationals `±2^(−5000)`, `±1/(3·2^5000)` (the value is just inside `1/q`, at no cost), and a
large rational (where `csch q` rounds like `2 exp (−q)`).  References: an independent 6000-bit
fixed-point evaluation of `2/(e^q − e^(−q))` rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
private def dn : AzFloat := X "0.9999999999999999" 53
private def T (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  cschRatPrecRound (Q q) p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (T "0" 53) == ("Infinity", .eq)
#guard D (T "0" 0) == ("Infinity", .eq)
#guard D (T "1/3" 0) == ("NaN", .eq)

-- correctly rounded values at exact rationals
#guard D (T "1" 53) == ("0.8509181282393216", .gt)
#guard D (T "-1" 53) == ("-0.8509181282393216", .lt)
#guard D (T "1/3" 53) == ("2.9451562666948146", .gt)
#guard D (T "-2/7" 53) == ("-3.4528305958498073", .lt)
#guard D (T "22/7" 53) == ("0.08647970651862788", .gt)
#guard D (T "355/113" 53) == ("0.08658951434462883", .gt)
#guard D (T "-7/5" 53) == ("-0.525126929342733", .lt)
#guard D (T "10" 53) == ("0.00009079985971212217", .gt)
#guard D (T "-100/3" 53) == ("-6.676475590730013e-15", .lt)
#guard D (T "1/1000" 53) == ("999.9998333333527", .lt)
#guard D (T "-1/1000000007" 53) == ("-1000000007.0", .lt)
#guard D (T "3/1125899906842624" 53) == ("375299968947541.3", .lt)
#guard D (T "1/3000000000000000000000000000000" 53) == ("3.0e30", .lt)
#guard D (T "700/3" 53) == ("9.239551380853872e-102", .gt)
#guard D (T "1/3" 53 .Floor) == ("2.945156266694814", .lt)
#guard D (T "-2/7" 53 .Floor) == ("-3.4528305958498073", .lt)
#guard D (T "22/7" 53 .Floor) == ("0.08647970651862787", .lt)
#guard D (T "-100/3" 53 .Floor) == ("-6.676475590730013e-15", .lt)
#guard D (T "1/1000000007" 53 .Floor) == ("1000000006.9999999", .lt)
#guard D (T "1/3" 53 .Ceiling) == ("2.9451562666948146", .gt)
#guard D (T "-2/7" 53 .Ceiling) == ("-3.452830595849807", .gt)
#guard D (T "22/7" 53 .Ceiling) == ("0.08647970651862788", .gt)
#guard D (T "-100/3" 53 .Ceiling) == ("-6.676475590730012e-15", .gt)
#guard D (T "1/1000000007" 53 .Ceiling) == ("1000000007.0", .gt)
#guard D (T "1/3" 20) == ("2.945156", .lt)
#guard D (T "1/3" 1) == ("2.0", .lt)
#guard D (T "-22/7" 2) == ("-0.09", .lt)
#guard D (T "1/3" 113) == ("2.9451562666948143476455860034951655", .lt)
#guard D (T "-7/5" 200) == ("-0.525126929342732954202268548850834127169282092516329226087083", .gt)

-- agreement with the float `csch` at representable arguments, oddness
#guard T "3/2" 53 == cschPrecRound (X "1.5" 53) 53 .Nearest
#guard T "-5/1024" 53 .Floor == cschPrecRound (X "-0.0048828125" 53) 53 .Floor
#guard T "100" 20 .Ceiling == cschPrecRound (X "100" 53) 20 .Ceiling
#guard cschRat (Q "1/3") 53 == (T "1/3" 53).1
private def odd (q : AzRat) (p : Nat) (m : RoundingMode) : Bool :=
  let r := cschRatPrecRound q p (-m)
  cschRatPrecRound (-q) p m == (-r.1, r.2.swap)
#guard odd (Q "1/3") 53 .Nearest && odd (Q "22/7") 53 .Floor
#guard odd (Q "1/1000000007") 20 .Ceiling && odd (Q "1000000/3") 53 .Floor
#guard toString (cschRat (Q "1/3") 200) == "2.94515626669481434764558600349516567646085056088849014\
  7110879"
#guard toString (cschRat (Q "-22/7") 200) == "-0.08647970651862787589103205270541728290508559867817\
  66266852968"

-- tiny rationals: just inside `1/q`
private def pw (k : Nat) : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 1) <<< k)
#guard D (cschRatPrecRound (pw 5000) 53 .Nearest) == ("1.412467032139426e1505", .gt)
#guard D (cschRatPrecRound (pw 5000) 53 .Ceiling) == ("1.412467032139426e1505", .gt)
#guard D (cschRatPrecRound (pw 5000) 53 .Floor) == ("1.4124670321394259e1505", .lt)
#guard D (cschRatPrecRound (-(pw 5000)) 53 .Nearest) == ("-1.412467032139426e1505", .lt)
#guard D (cschRatPrecRound (-(pw 5000)) 53 .Ceiling) == ("-1.4124670321394259e1505", .gt)
#guard D (cschRatPrecRound (Q "1/3" * pw 5000) 53 .Nearest) == ("4.237401096418278e1505", .gt)
#guard D (cschRatPrecRound (Q "1/3" * pw 5000) 53 .Floor) == ("4.2374010964182775e1505", .lt)
#guard D (cschRatPrecRound (Q "3" * pw 5000) 53 .Nearest) == ("4.708223440464753e1504", .lt)

-- a large rational: `csch q` rounds like `2 exp (−q)`
private def big (q : String) (p : Nat) (m : RoundingMode) : Bool :=
  let r := expRatPrecRound (-(Q q)) p m
  T q p m == (h r.1 1, r.2)
#guard big "1000000/3" 53 .Nearest && big "1000000/3" 53 .Floor && big "12345/7" 113 .Ceiling
