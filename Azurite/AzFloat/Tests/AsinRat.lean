/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Asin
import Azurite.AzFloat.AsinRat
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `arcsin q` of a rational

The special values (`0`; `±1` give `±π/2` in every mode; `|q| > 1` gives `NaN`; `p = 0`), the
correctly rounded 53-bit values at the exact rationals `1/3`, `1/10`, `−7/10`, `3/4`, `−22/23`,
`1 − 10⁻⁶`, `1/(10⁹ + 7)`, `5/7`, `−1/1000`, `355/452`, agreement with the float `asin` at
representable arguments, the directed modes, 1-, 20- and 113-bit results, a 200-bit string, the
rational `±(1 − 2^(−200))` next to `±1` (not representable at the target precision), and the
tiny paths at `±1/(3·2^1000)` and at the exactly representable `±2^(−5000)`.  References: an
independent 1400-bit fixed-point evaluation of `arctan (q/√(1 − q²))` rounded with exact
rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def T (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  asinRatPrecRound (Q q) p m
private def piN : AzFloat := F "884279719003555/562949953421312" 53
private def piC : AzFloat := F "7074237752028441/4503599627370496" 53

-- special values
#guard T "0" 53 == (zero, .eq)
#guard T "0" 0 == (zero, .eq)
#guard T "1/3" 0 == (nan, .eq)
#guard T "1" 53 == (piN, .lt)
#guard T "1" 53 .Ceiling == (piC, .gt)
#guard T "-1" 53 == (-piN, .gt)
#guard T "-1" 53 .Floor == (-piC, .lt)
#guard T "3/2" 53 == (nan, .eq)
#guard T "-22/7" 53 == (nan, .eq)
#guard T "1000001/1000000" 53 == (nan, .eq)

-- correctly rounded values at exact rationals
#guard T "1/3" 53 == (F "3060978757568649/9007199254740992" 53, .lt)
#guard T "1/10" 53 == (F "1804455842471457/18014398509481984" 53, .gt)
#guard T "-7/10" 53 == (F "-3492079876800203/4503599627370496" 53, .lt)
#guard T "3/4" 53 == (F "1909666031444023/2251799813685248" 53, .lt)
#guard T "-22/23" 53 == (F "-22427106441627/17592186044416" 53, .gt)
#guard T "999999/1000000" 53 == (F "883483587478145/562949953421312" 53, .lt)
#guard T "1/1000000007" 53 == (F "2417851622304297/2417851639229258349412352" 53, .gt)
#guard T "5/7" 53 == (F "7166154329695639/9007199254740992" 53, .gt)
#guard T "-1/1000" 53 == (F "-2305843393521035/2305843009213693952" 53, .gt)
#guard T "355/452" 53 == (F "2034139083931083/2251799813685248" 53, .lt)
#guard T "1/3" 53 .Floor == (F "3060978757568649/9007199254740992" 53, .lt)
#guard T "-3/4" 53 .Floor == (F "-7638664125776093/9007199254740992" 53, .lt)
#guard T "1/3" 53 .Ceiling == (F "6121957515137299/18014398509481984" 53, .gt)
#guard T "-3/4" 53 .Ceiling == (F "-1909666031444023/2251799813685248" 53, .gt)
#guard T "1/3" 20 == (F "356345/1048576" 20, .gt)
#guard T "1/3" 1 == (F "1/4" 1, .lt)
#guard T "3/4" 113
  == (F "4403390068538058708848283552344817/5192296858534827628530496329220096" 113, .gt)

-- agreement with the float `asin` at representable arguments
#guard T "1/2" 53 == asinPrecRound (F "1/2" 53) 53 .Nearest
#guard T "-3/4" 53 .Floor == asinPrecRound (F "-3/4" 53) 53 .Floor
#guard T "1/1024" 53 == asinPrecRound (F "1/1024" 53) 53 .Nearest
#guard asinRat (Q "1/3") 53 == (T "1/3" 53).1
#guard (toString (asinRat (Q "1/3") 200)).startsWith
  "0.33983690945412193709639251339176406638824469033245807"

-- a rational next to `±1`
private def pw (k : Nat) : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 1) <<< k)
private def near1 : AzRat := 1 - pw 200
#guard asinRatPrecRound near1 53 .Nearest == (piN, .lt)
#guard asinRatPrecRound near1 53 .Ceiling == (piC, .gt)
#guard asinRatPrecRound (-near1) 53 .Floor == (-piC, .lt)

-- tiny arguments
private def same (r : AzFloat × Ordering) (v : AzFloat) (o : Ordering) : Bool :=
  eqIEEE r.1 v && r.2 == o && r.1.precision? == some 53
private def tinyQ : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 3) <<< (1000 : Nat))
private def tinyLo : AzFloat := (ofAzRatRound tinyQ 53 .Floor).1
private def tinyHi : AzFloat := (ofAzRatRound tinyQ 53 .Ceiling).1
#guard asinRatPrecRound tinyQ 53 .Nearest == (tinyLo, .lt)
#guard asinRatPrecRound tinyQ 53 .Floor == (tinyLo, .lt)
#guard asinRatPrecRound tinyQ 53 .Ceiling == (tinyHi, .gt)
#guard asinRatPrecRound (-tinyQ) 53 .Floor == (-tinyHi, .lt)
#guard asinRatPrecRound (-tinyQ) 53 .Ceiling == (-tinyLo, .gt)
#guard same (asinRatPrecRound (pw 5000) 53 .Nearest) (powerOf2 (AzInt.ofInt (-5000))) .lt
#guard (asinRatPrecRound (pw 5000) 53 .Ceiling).2 == .gt
#guard same (asinRatPrecRound (-(pw 5000)) 53 .Nearest) (-(powerOf2 (AzInt.ofInt (-5000)))) .gt
#guard (asinTinyRat? tinyQ 53 .Nearest).isSome
#guard (asinTinyRat? (Q "1/1000") 53 .Nearest).isNone
