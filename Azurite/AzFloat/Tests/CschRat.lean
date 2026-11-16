/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.CschRat
import Azurite.AzFloat.Csch
import Azurite.AzFloat.ExpRat
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
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
private def dn : AzFloat := F "9007199254740991/9007199254740992" 53
private def T (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  cschRatPrecRound (Q q) p m

-- special values
#guard T "0" 53 == (infinity true, .eq)
#guard T "0" 0 == (infinity true, .eq)
#guard T "1/3" 0 == (nan, .eq)

-- correctly rounded values at exact rationals
#guard T "1" 53 == (F "7664389130522817/9007199254740992" 53, .gt)
#guard T "-1" 53 == (F "-7664389130522817/9007199254740992" 53, .lt)
#guard T "1/3" 53 == (F "1657975583154331/562949953421312" 53, .gt)
#guard T "-2/7" 53 == (F "-971885411552665/281474976710656" 53, .lt)
#guard T "22/7" 53 == (F "3115759792419219/36028797018963968" 53, .gt)
#guard T "355/113" 53 == (F "3119716036293301/36028797018963968" 53, .gt)
#guard T "-7/5" 53 == (F "-2364961443310145/4503599627370496" 53, .lt)
#guard T "10" 53 == (F "6699847096152993/73786976294838206464" 53, .gt)
#guard T "-100/3" 53 == (F "-8463438289998023/1267650600228229401496703205376" 53, .lt)
#guard T "1/1000" 53 == (F "8796091556192667/8796093022208" 53, .lt)
#guard T "-1/1000000007" 53 == (F "-1000000007" 53, .lt)
#guard T "3/1125899906842624" 53 == (F "6004799503160661/16" 53, .lt)
#guard T "1/3000000000000000000000000000000" 53 == (F "2999999999999999778178897805312" 53, .lt)
#guard T "700/3" 53
  == (h (F "5824909772164951" 53) (-388), .gt)
#guard T "1/3" 53 .Floor == (F "6631902332617323/2251799813685248" 53, .lt)
#guard T "-2/7" 53 .Floor == (F "-971885411552665/281474976710656" 53, .lt)
#guard T "22/7" 53 .Floor == (F "6231519584838437/72057594037927936" 53, .lt)
#guard T "-100/3" 53 .Floor == (F "-8463438289998023/1267650600228229401496703205376" 53, .lt)
#guard T "1/1000000007" 53 .Floor == (F "8388608058720255/8388608" 53, .lt)
#guard T "1/3" 53 .Ceiling == (F "1657975583154331/562949953421312" 53, .gt)
#guard T "-2/7" 53 .Ceiling == (F "-7775083292421319/2251799813685248" 53, .gt)
#guard T "22/7" 53 .Ceiling == (F "3115759792419219/36028797018963968" 53, .gt)
#guard T "-100/3" 53 .Ceiling == (F "-4231719144999011/633825300114114700748351602688" 53, .gt)
#guard T "1/1000000007" 53 .Ceiling == (F "1000000007" 53, .gt)
#guard T "1/3" 20 == (F "772055/262144" 20, .lt)
#guard T "1/3" 1 == (F "2" 1, .lt)
#guard T "-22/7" 2 == (F "-3/32" 2, .lt)
#guard T "1/3" 113
  == (F "7646062815726822761970806724714771/2596148429267413814265248164610048" 113, .lt)
#guard T "-7/5" 200
  == (h (F "-843846440825740267165113868684763183898443320153909766653623" 200) (-200), .gt)

-- agreement with the float `csch` at representable arguments, oddness
#guard T "3/2" 53 == cschPrecRound (F "3/2" 53) 53 .Nearest
#guard T "-5/1024" 53 .Floor == cschPrecRound (F "-5/1024" 53) 53 .Floor
#guard T "100" 20 .Ceiling == cschPrecRound (F "100" 53) 20 .Ceiling
#guard cschRat (Q "1/3") 53 == (T "1/3" 53).1
private def odd (q : AzRat) (p : Nat) (m : RoundingMode) : Bool :=
  let r := cschRatPrecRound q p (-m)
  cschRatPrecRound (-q) p m == (-r.1, r.2.swap)
#guard odd (Q "1/3") 53 .Nearest && odd (Q "22/7") 53 .Floor
#guard odd (Q "1/1000000007") 20 .Ceiling && odd (Q "1000000/3") 53 .Floor
#guard (toString (cschRat (Q "1/3") 200)).startsWith
  "2.945156266694814347645586003495165676460850560888490147"
#guard (toString (cschRat (Q "-22/7") 200)).startsWith
  "-0.08647970651862787589103205270541728290508559867817662"

-- tiny rationals: just inside `1/q`
private def pw (k : Nat) : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 1) <<< k)
#guard cschRatPrecRound (pw 5000) 53 .Nearest == (h (F "1" 53) 5000, .gt)
#guard cschRatPrecRound (pw 5000) 53 .Ceiling == (h (F "1" 53) 5000, .gt)
#guard cschRatPrecRound (pw 5000) 53 .Floor == (h dn 5000, .lt)
#guard cschRatPrecRound (-(pw 5000)) 53 .Nearest == (-(h (F "1" 53) 5000), .lt)
#guard cschRatPrecRound (-(pw 5000)) 53 .Ceiling == (-(h dn 5000), .gt)
#guard cschRatPrecRound (Q "1/3" * pw 5000) 53 .Nearest == (h (F "3" 53) 5000, .gt)
#guard cschRatPrecRound (Q "1/3" * pw 5000) 53 .Floor
  == (h (F "6755399441055743/2251799813685248" 53) 5000, .lt)
#guard cschRatPrecRound (Q "3" * pw 5000) 53 .Nearest
  == (h (F "6004799503160661/18014398509481984" 53) 5000, .lt)

-- a large rational: `csch q` rounds like `2 exp (−q)`
private def big (q : String) (p : Nat) (m : RoundingMode) : Bool :=
  let r := expRatPrecRound (-(Q q)) p m
  T q p m == (h r.1 1, r.2)
#guard big "1000000/3" 53 .Nearest && big "1000000/3" 53 .Floor && big "12345/7" 113 .Ceiling
