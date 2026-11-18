/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.SechRat
import Azurite.AzFloat.Sech
import Azurite.AzFloat.ExpRat
import Azurite.AzFloat.ToString
import Azurite.AzFloat.OfString
import Azurite.AzRat.Parse

/-!
# Tests for `sech q` of a rational

The special values (`sech 0 = 1`, `p = 0`), the correctly rounded 53-bit values at exact
rationals from `10^(−30)/3` to `700/3` in three modes, 1-, 2-, 20-, 113- and 200-bit results,
agreement with the float `sech` at representable arguments, evenness, 200-bit strings, tiny
rationals `±2^(−5000)`, `±1/(3·2^5000)` (the value is just below `1`, at no cost), and a large
rational (where `sech q` rounds like `2 exp (−|q|)`).  References: an independent 6000-bit
fixed-point evaluation of `2/(e^q + e^(−q))` rounded with exact rationals.
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
  sechRatPrecRound (Q q) p m

-- special values
#guard D (T "0" 53) == ("1.0", .eq)
#guard D (T "0" 1 .Ceiling) == ("1.0", .eq)
#guard D (T "0" 0) == ("NaN", .eq)
#guard D (T "1/3" 0) == ("NaN", .eq)

-- correctly rounded values at exact rationals
#guard D (T "1" 53) == ("0.6480542736638853", .lt)
#guard D (T "-1" 53) == ("0.6480542736638853", .lt)
#guard D (T "1/3" 53) == ("0.9469052537634979", .lt)
#guard D (T "-2/7" 53) == ("0.960527372318066", .lt)
#guard D (T "22/7" 53) == ("0.08615812953697949", .lt)
#guard D (T "355/113" 53) == ("0.08626671540697119", .lt)
#guard D (T "-7/5" 53) == ("0.4649219924089817", .gt)
#guard D (T "10" 53) == ("0.00009079985933781725", .gt)
#guard D (T "-100/3" 53) == ("6.676475590730013e-15", .gt)
#guard D (T "1/1000" 53) == ("0.9999995000002083", .lt)
#guard D (T "-1/1000000007" 53) == ("1.0", .gt)
#guard D (T "3/1125899906842624" 53) == ("1.0", .gt)
#guard D (T "1/3000000000000000000000000000000" 53) == ("1.0", .gt)
#guard D (T "700/3" 53) == ("9.239551380853872e-102", .gt)
#guard D (T "1/3" 53 .Floor) == ("0.9469052537634979", .lt)
#guard D (T "-2/7" 53 .Floor) == ("0.960527372318066", .lt)
#guard D (T "22/7" 53 .Floor) == ("0.08615812953697949", .lt)
#guard D (T "-100/3" 53 .Floor) == ("6.676475590730012e-15", .lt)
#guard D (T "1/1000000007" 53 .Floor) == ("0.9999999999999999", .lt)
#guard D (T "1/3" 53 .Ceiling) == ("0.946905253763498", .gt)
#guard D (T "-2/7" 53 .Ceiling) == ("0.9605273723180661", .gt)
#guard D (T "22/7" 53 .Ceiling) == ("0.0861581295369795", .gt)
#guard D (T "-100/3" 53 .Ceiling) == ("6.676475590730013e-15", .gt)
#guard D (T "1/1000000007" 53 .Ceiling) == ("1.0", .gt)
#guard D (T "1/3" 20) == ("0.946905", .lt)
#guard D (T "1/3" 1) == ("1.0", .gt)
#guard D (T "-22/7" 2) == ("0.09", .gt)
#guard D (T "1/3" 113) == ("0.9469052537634979265589522801398116", .lt)
#guard D (T "-7/5" 200) == ("0.4649219924089816673553283347446582448917855928175257061037488", .gt)

-- agreement with the float `sech` at representable arguments, evenness
#guard T "3/2" 53 == sechPrecRound (X "1.5" 53) 53 .Nearest
#guard T "-5/1024" 53 .Floor == sechPrecRound (X "-0.0048828125" 53) 53 .Floor
#guard T "100" 20 .Ceiling == sechPrecRound (X "100" 53) 20 .Ceiling
#guard sechRat (Q "1/3") 53 == (T "1/3" 53).1
#guard T "-22/7" 53 .Floor == T "22/7" 53 .Floor
#guard T "-1/1000000007" 20 .Ceiling == T "1/1000000007" 20 .Ceiling
#guard toString (sechRat (Q "1/3") 200)
  == "0.946905253763497926558952280139811647196865554127211019972439"
#guard toString (sechRat (Q "-22/7") 200)
  == "0.0861581295369794922761966168709947894310375872224657495364406"

-- tiny rationals: just below `1`
private def pw (k : Nat) : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 1) <<< k)
private def tinyOk (q : AzRat) : Bool :=
  sechRatPrecRound q 53 .Nearest == (X "1" 53, .gt)
    && sechRatPrecRound q 53 .Ceiling == (X "1" 53, .gt)
    && sechRatPrecRound q 53 .Floor == (dn, .lt)
    && sechRatPrecRound (-q) 53 .Floor == (dn, .lt)
#guard tinyOk (pw 5000)
#guard tinyOk (Q "1/3" * pw 5000)
#guard tinyOk (pw 100)

-- a large rational: `sech q` rounds like `2 exp (−|q|)`
private def big (q : String) (p : Nat) (m : RoundingMode) : Bool :=
  let r := expRatPrecRound (-(Q q)) p m
  T q p m == (h r.1 1, r.2) && sechRatPrecRound (-(Q q)) p m == (h r.1 1, r.2)
#guard big "1000000/3" 53 .Nearest && big "1000000/3" 53 .Floor && big "12345/7" 113 .Ceiling
