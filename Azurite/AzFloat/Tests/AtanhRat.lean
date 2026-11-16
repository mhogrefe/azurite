/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AtanhRat
import Azurite.AzFloat.Atanh
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
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
private def up : AzFloat := F "4503599627370497/4503599627370496" 53
private def T (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  atanhRatPrecRound (Q q) p m

-- special values
#guard T "0" 53 == (zero, .eq)
#guard T "0" 0 == (zero, .eq)
#guard T "1" 53 == (infinity true, .eq)
#guard T "-3/3" 53 == (infinity false, .eq)
#guard T "1" 0 == (infinity true, .eq)
#guard T "2" 53 == (nan, .eq)
#guard T "-1000001/1000000" 53 == (nan, .eq)
#guard T "1/3" 0 == (nan, .eq)

-- correctly rounded values at exact rationals
#guard T "1/2" 53 == (F "4947709893870347/9007199254740992" 53, .gt)
#guard T "-1/2" 53 == (F "-4947709893870347/9007199254740992" 53, .lt)
#guard T "1/3" 53 == (F "6243314768165359/18014398509481984" 53, .lt)
#guard T "-2/7" 53 == (F "-1323577902513265/4503599627370496" 53, .lt)
#guard T "7/22" 53 == (F "5937956737177599/18014398509481984" 53, .gt)
#guard T "113/355" 53 == (F "23205168970429/70368744177664" 53, .gt)
#guard T "99/100" 53 == (F "2979865704523459/1125899906842624" 53, .lt)
#guard T "-999999999/1000000000" 53 == (F "-3014092177593827/281474976710656" 53, .gt)
#guard T "1/1000" 53 == (F "4611687555656983/4611686018427387904" 53, .lt)
#guard T "-1/1000000007" 53 == (F "-2417851622304297/2417851639229258349412352" 53, .lt)
#guard T "3/1125899906842624" 53 == (F "3/1125899906842624" 53, .lt)
#guard T "1/3000000000000000000000000000000" 53
  == (F "3805993847215893/11417981541647679048466287755595961091061972992" 53, .lt)
#guard T "2999999999999999999999999999999/3000000000000000000000000000000" 53
  == (F "1246746126101009/35184372088832" 53, .lt)
#guard T "1/3" 53 .Floor == (F "6243314768165359/18014398509481984" 53, .lt)
#guard T "-2/7" 53 .Floor == (F "-1323577902513265/4503599627370496" 53, .lt)
#guard T "99/100" 53 .Floor == (F "2979865704523459/1125899906842624" 53, .lt)
#guard T "1/1000000007" 53 .Floor == (F "4835703244608593/4835703278458516698824704" 53, .lt)
#guard T "1/3" 53 .Ceiling == (F "390207173010335/1125899906842624" 53, .gt)
#guard T "-2/7" 53 .Ceiling == (F "-5294311610053059/18014398509481984" 53, .gt)
#guard T "99/100" 53 .Ceiling == (F "5959731409046919/2251799813685248" 53, .gt)
#guard T "1/1000000007" 53 .Ceiling == (F "2417851622304297/2417851639229258349412352" 53, .gt)
#guard T "1/3" 20 == (F "726817/2097152" 20, .lt)
#guard T "1/3" 1 == (F "1/4" 1, .lt)
#guard T "-7/22" 2 == (F "-3/8" 2, .lt)
#guard T "1/3" 113
  == (F "3599025928123676973540407451845619/10384593717069655257060992658440192" 113, .gt)
#guard T "-5/7" 200
  == (h (F "-359905807157982146446289311295131136112645639541113781519289" 200) (-198), .lt)

-- agreement with the float `atanh` at representable arguments, oddness
#guard T "3/4" 53 == atanhPrecRound (F "3/4" 53) 53 .Nearest
#guard T "-5/1024" 53 .Floor == atanhPrecRound (F "-5/1024" 53) 53 .Floor
#guard T "1023/1024" 20 .Ceiling == atanhPrecRound (F "1023/1024" 53) 20 .Ceiling
#guard atanhRat (Q "1/3") 53 == (T "1/3" 53).1
private def odd (q : AzRat) (p : Nat) (m : RoundingMode) : Bool :=
  let r := atanhRatPrecRound q p (-m)
  atanhRatPrecRound (-q) p m == (-r.1, r.2.swap)
#guard odd (Q "1/3") 53 .Nearest && odd (Q "7/22") 53 .Floor
#guard odd (Q "1/1000000007") 20 .Ceiling && odd (Q "999999/1000000") 53 .Floor
#guard (toString (atanhRat (Q "1/3") 200)).startsWith
  "0.346573590279972654708616060729088284037750067180127627"
#guard (toString (atanhRat (Q "-7/22") 200)).startsWith
  "-0.32962281444213198059363373110659913066071050091573845"

-- tiny rationals: just outside `q`
private def pw (k : Nat) : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 1) <<< k)
#guard atanhRatPrecRound (pw 5000) 53 .Nearest == (h (F "1" 53) (-5000), .lt)
#guard atanhRatPrecRound (pw 5000) 53 .Floor == (h (F "1" 53) (-5000), .lt)
#guard atanhRatPrecRound (pw 5000) 53 .Ceiling == (h up (-5000), .gt)
#guard atanhRatPrecRound (-(pw 5000)) 53 .Nearest == (-(h (F "1" 53) (-5000)), .gt)
#guard atanhRatPrecRound (-(pw 5000)) 53 .Floor == (-(h up (-5000)), .lt)
#guard atanhRatPrecRound (Q "1/3" * pw 5000) 53 .Nearest
  == (h (F "6004799503160661/18014398509481984" 53) (-5000), .lt)
#guard atanhRatPrecRound (Q "1/3" * pw 5000) 53 .Ceiling
  == (h (F "3002399751580331/9007199254740992" 53) (-5000), .gt)

-- next to `±1`
#guard atanhRatPrecRound (1 - pw 5000) 53 .Nearest == (F "1905689523656919/1099511627776" 53, .lt)
#guard atanhRatPrecRound (1 - pw 5000) 53 .Floor == (F "1905689523656919/1099511627776" 53, .lt)
#guard atanhRatPrecRound (1 - pw 5000) 53 .Ceiling == (F "7622758094627677/4398046511104" 53, .gt)
#guard odd (1 - pw 5000) 53 .Floor
