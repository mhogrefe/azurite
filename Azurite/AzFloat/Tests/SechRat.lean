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
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
private def dn : AzFloat := F "9007199254740991/9007199254740992" 53
private def T (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  sechRatPrecRound (Q q) p m

-- special values
#guard T "0" 53 == (F "1" 53, .eq)
#guard T "0" 1 .Ceiling == (F "1" 1, .eq)
#guard T "0" 0 == (nan, .eq)
#guard T "1/3" 0 == (nan, .eq)

-- correctly rounded values at exact rationals
#guard T "1" 53 == (F "5837153970777063/9007199254740992" 53, .lt)
#guard T "-1" 53 == (F "5837153970777063/9007199254740992" 53, .lt)
#guard T "1/3" 53 == (F "2132241074002227/2251799813685248" 53, .lt)
#guard T "-2/7" 53 == (F "8651661432101607/9007199254740992" 53, .lt)
#guard T "22/7" 53 == (F "1552086880310719/18014398509481984" 53, .lt)
#guard T "355/113" 53 == (F "6216171957780993/72057594037927936" 53, .lt)
#guard T "-7/5" 53 == (F "4187645023538877/9007199254740992" 53, .gt)
#guard T "10" 53 == (F "6699847068534165/73786976294838206464" 53, .gt)
#guard T "-100/3" 53 == (F "8463438289998023/1267650600228229401496703205376" 53, .gt)
#guard T "1/1000" 53 == (F "9007194751143241/9007199254740992" 53, .lt)
#guard T "-1/1000000007" 53 == (F "1" 53, .gt)
#guard T "3/1125899906842624" 53 == (F "1" 53, .gt)
#guard T "1/3000000000000000000000000000000" 53 == (F "1" 53, .gt)
#guard T "700/3" 53
  == (h (F "5824909772164951" 53) (-388), .gt)
#guard T "1/3" 53 .Floor == (F "2132241074002227/2251799813685248" 53, .lt)
#guard T "-2/7" 53 .Floor == (F "8651661432101607/9007199254740992" 53, .lt)
#guard T "22/7" 53 .Floor == (F "1552086880310719/18014398509481984" 53, .lt)
#guard T "-100/3" 53 .Floor == (F "4231719144999011/633825300114114700748351602688" 53, .lt)
#guard T "1/1000000007" 53 .Floor == (F "9007199254740991/9007199254740992" 53, .lt)
#guard T "1/3" 53 .Ceiling == (F "8528964296008909/9007199254740992" 53, .gt)
#guard T "-2/7" 53 .Ceiling == (F "1081457679012701/1125899906842624" 53, .gt)
#guard T "22/7" 53 .Ceiling == (F "6208347521242877/72057594037927936" 53, .gt)
#guard T "-100/3" 53 .Ceiling == (F "8463438289998023/1267650600228229401496703205376" 53, .gt)
#guard T "1/1000000007" 53 .Ceiling == (F "1" 53, .gt)
#guard T "1/3" 20 == (F "496451/524288" 20, .lt)
#guard T "1/3" 1 == (F "1" 1, .gt)
#guard T "-22/7" 2 == (F "3/32" 2, .gt)
#guard T "1/3" 113
  == (F "9833226348892668100949924212454163/10384593717069655257060992658440192" 113, .lt)
#guard T "-7/5" 200
  == (h (F "1494201674429364246982700274984134377110575935153761511780431" 200) (-201), .gt)

-- agreement with the float `sech` at representable arguments, evenness
#guard T "3/2" 53 == sechPrecRound (F "3/2" 53) 53 .Nearest
#guard T "-5/1024" 53 .Floor == sechPrecRound (F "-5/1024" 53) 53 .Floor
#guard T "100" 20 .Ceiling == sechPrecRound (F "100" 53) 20 .Ceiling
#guard sechRat (Q "1/3") 53 == (T "1/3" 53).1
#guard T "-22/7" 53 .Floor == T "22/7" 53 .Floor
#guard T "-1/1000000007" 20 .Ceiling == T "1/1000000007" 20 .Ceiling
#guard (toString (sechRat (Q "1/3") 200)).startsWith
  "0.946905253763497926558952280139811647196865554127211019"
#guard (toString (sechRat (Q "-22/7") 200)).startsWith
  "0.086158129536979492276196616870994789431037587222465749"

-- tiny rationals: just below `1`
private def pw (k : Nat) : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 1) <<< k)
private def tinyOk (q : AzRat) : Bool :=
  sechRatPrecRound q 53 .Nearest == (F "1" 53, .gt)
    && sechRatPrecRound q 53 .Ceiling == (F "1" 53, .gt)
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
