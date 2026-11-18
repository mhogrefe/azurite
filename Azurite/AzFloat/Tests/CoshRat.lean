/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.CoshRat
import Azurite.AzFloat.Cosh
import Azurite.AzFloat.ExpRat
import Azurite.AzFloat.OfString
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `cosh q` of a rational

The special values (`cosh 0 = 1`, `p = 0`), the correctly rounded 53-bit values at exact
rationals from `10^(−30)/3` to `700/3` in three modes, 1-, 2-, 20-, 113- and 200-bit results,
agreement with the float `cosh` at representable arguments, evenness, 200-bit strings, tiny
rationals `±2^(−5000)`, `±1/(3·2^5000)` (the value is just above `1`, at no cost), and a large
rational (where `cosh q` rounds like `exp |q| / 2`).  References: an independent 6000-bit
fixed-point evaluation of `(e^q + e^(−q))/2` rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
private def up : AzFloat := X "1.0000000000000002" 53
private def T (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  coshRatPrecRound (Q q) p m
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)

-- special values
#guard D (T "0" 53) == ("1.0", .eq)
#guard D (T "0" 1 .Ceiling) == ("1.0", .eq)
#guard D (T "0" 0) == ("NaN", .eq)
#guard D (T "1/3" 0) == ("NaN", .eq)

-- correctly rounded values at exact rationals
#guard D (T "1" 53) == ("1.5430806348152437", .lt)
#guard D (T "-1" 53) == ("1.5430806348152437", .lt)
#guard D (T "1/3" 53) == ("1.0560718678299394", .gt)
#guard D (T "-2/7" 53) == ("1.041094745261318", .lt)
#guard D (T "22/7" 53) == ("11.606565803761967", .gt)
#guard D (T "355/113" 53) == ("11.591956356312023", .gt)
#guard D (T "-7/5" 53) == ("2.1508984653931407", .gt)
#guard D (T "10" 53) == ("11013.232920103323", .lt)
#guard D (T "-100/3" 53) == ("149779623457090.94", .gt)
#guard D (T "1/1000" 53) == ("1.0000005000000416", .lt)
#guard D (T "-1/1000000007" 53) == ("1.0", .lt)
#guard D (T "3/1125899906842624" 53) == ("1.0", .lt)
#guard D (T "1/3000000000000000000000000000000" 53) == ("1.0", .lt)
#guard D (T "700/3" 53) == ("1.0823036301006912e101", .lt)
#guard D (T "1/3" 53 .Floor) == ("1.0560718678299392", .lt)
#guard D (T "-2/7" 53 .Floor) == ("1.041094745261318", .lt)
#guard D (T "22/7" 53 .Floor) == ("11.606565803761965", .lt)
#guard D (T "-100/3" 53 .Floor) == ("149779623457090.9", .lt)
#guard D (T "1/1000000007" 53 .Floor) == ("1.0", .lt)
#guard D (T "1/3" 53 .Ceiling) == ("1.0560718678299394", .gt)
#guard D (T "-2/7" 53 .Ceiling) == ("1.0410947452613182", .gt)
#guard D (T "22/7" 53 .Ceiling) == ("11.606565803761967", .gt)
#guard D (T "-100/3" 53 .Ceiling) == ("149779623457090.94", .gt)
#guard D (T "1/1000000007" 53 .Ceiling) == ("1.0000000000000002", .gt)
#guard D (T "1/3" 20) == ("1.056072", .gt)
#guard D (T "1/3" 1) == ("1.0", .lt)
#guard D (T "-22/7" 2) == ("12.0", .gt)
#guard D (T "1/3" 113) == ("1.0560718678299393895268647082639832", .lt)
#guard D (T "-7/5" 200) == ("2.1508984653931405320819850675311939426159224579627462804494", .lt)

-- agreement with the float `cosh` at representable arguments, evenness
#guard T "3/2" 53 == coshPrecRound (X "1.5" 53) 53 .Nearest
#guard T "-5/1024" 53 .Floor == coshPrecRound (X "-0.0048828125" 53) 53 .Floor
#guard T "100" 20 .Ceiling == coshPrecRound (X "100" 53) 20 .Ceiling
#guard coshRat (Q "1/3") 53 == (T "1/3" 53).1
#guard T "-22/7" 53 .Floor == T "22/7" 53 .Floor
#guard T "-1/1000000007" 20 .Ceiling == T "1/1000000007" 20 .Ceiling
#guard toString (coshRat (Q "1/3") 200) == "1.05607186782993938952686470826398325252550928751044306\
  9879193"
#guard toString (coshRat (Q "-22/7") 200) == "11.60656580376196641440105294515190289031076068876957\
  925687642"

-- tiny rationals: just above `1`
private def pw (k : Nat) : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 1) <<< k)
private def tinyOk (q : AzRat) : Bool :=
  coshRatPrecRound q 53 .Nearest == (X "1" 53, .lt)
    && coshRatPrecRound q 53 .Floor == (X "1" 53, .lt)
    && coshRatPrecRound q 53 .Ceiling == (up, .gt)
    && coshRatPrecRound (-q) 53 .Ceiling == (up, .gt)
#guard tinyOk (pw 5000)
#guard tinyOk (Q "1/3" * pw 5000)
#guard tinyOk (pw 100)

-- a large rational: `cosh q` rounds like `exp |q| / 2`
private def big (q : String) (p : Nat) (m : RoundingMode) : Bool :=
  let r := expRatPrecRound (Q q) p m
  T q p m == (h r.1 (-1), r.2) && coshRatPrecRound (-(Q q)) p m == (h r.1 (-1), r.2)
#guard big "1000000/3" 53 .Nearest && big "1000000/3" 53 .Floor && big "12345/7" 113 .Ceiling
