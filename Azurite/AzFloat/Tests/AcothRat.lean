/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcothRat
import Azurite.AzFloat.Acoth
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `acoth q` of a rational

The special values (`acoth (±1) = ±∞`; `NaN` for `|q| < 1`, including `0`; `p = 0`), the
correctly rounded 53-bit values at exact rationals from `1 + 10^(−30)/3` to `3·10^30` in three
modes, 1-, 2-, 20-, 113- and 200-bit results, agreement with the float `acoth` at
representable arguments, oddness, 200-bit strings, huge rationals `±2^5000`, `±3·2^5000` (just
outside `1/q`, at no cost), and `1 + 2^(−5000)` (value `≈ 2500.5 ln 2`).  References: an
independent 6000-bit fixed-point evaluation of `(1/2) ln ((q + 1)/(q − 1))` rounded with exact
rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
private def up : AzFloat := F "4503599627370497/4503599627370496" 53
private def T (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  acothRatPrecRound (Q q) p m

-- special values
#guard T "1" 53 == (infinity true, .eq)
#guard T "-3/3" 53 == (infinity false, .eq)
#guard T "1" 0 == (infinity true, .eq)
#guard T "0" 53 == (nan, .eq)
#guard T "1/2" 53 == (nan, .eq)
#guard T "-999999/1000000" 53 == (nan, .eq)
#guard T "3" 0 == (nan, .eq)

-- correctly rounded values at exact rationals
#guard T "2" 53 == (F "4947709893870347/9007199254740992" 53, .gt)
#guard T "-2" 53 == (F "-4947709893870347/9007199254740992" 53, .lt)
#guard T "3" 53 == (F "6243314768165359/18014398509481984" 53, .lt)
#guard T "-7/2" 53 == (F "-1323577902513265/4503599627370496" 53, .lt)
#guard T "22/7" 53 == (F "5937956737177599/18014398509481984" 53, .gt)
#guard T "355/113" 53 == (F "23205168970429/70368744177664" 53, .gt)
#guard T "100/99" 53 == (F "2979865704523459/1125899906842624" 53, .lt)
#guard T "-1000000000/999999999" 53 == (F "-3014092177593827/281474976710656" 53, .gt)
#guard T "1000" 53 == (F "4611687555656983/4611686018427387904" 53, .lt)
#guard T "-1000000007" 53 == (F "-2417851622304297/2417851639229258349412352" 53, .lt)
#guard T "1125899906842624/3" 53 == (F "3/1125899906842624" 53, .lt)
#guard T "3000000000000000000000000000000" 53
  == (F "3805993847215893/11417981541647679048466287755595961091061972992" 53, .lt)
#guard T "3000000000000000000000000000000/2999999999999999999999999999999" 53
  == (F "1246746126101009/35184372088832" 53, .lt)
#guard T "3" 53 .Floor == (F "6243314768165359/18014398509481984" 53, .lt)
#guard T "-7/2" 53 .Floor == (F "-1323577902513265/4503599627370496" 53, .lt)
#guard T "100/99" 53 .Floor == (F "2979865704523459/1125899906842624" 53, .lt)
#guard T "1000000007" 53 .Floor == (F "4835703244608593/4835703278458516698824704" 53, .lt)
#guard T "3" 53 .Ceiling == (F "390207173010335/1125899906842624" 53, .gt)
#guard T "-7/2" 53 .Ceiling == (F "-5294311610053059/18014398509481984" 53, .gt)
#guard T "100/99" 53 .Ceiling == (F "5959731409046919/2251799813685248" 53, .gt)
#guard T "1000000007" 53 .Ceiling == (F "2417851622304297/2417851639229258349412352" 53, .gt)
#guard T "3" 20 == (F "726817/2097152" 20, .lt)
#guard T "3" 1 == (F "1/4" 1, .lt)
#guard T "-22/7" 2 == (F "-3/8" 2, .lt)
#guard T "3" 113
  == (F "3599025928123676973540407451845619/10384593717069655257060992658440192" 113, .gt)
#guard T "-7/5" 200
  == (h (F "-359905807157982146446289311295131136112645639541113781519289" 200) (-198), .lt)

-- agreement with the float `acoth` at representable arguments, oddness
#guard T "3/2" 53 == acothPrecRound (F "3/2" 53) 53 .Nearest
#guard T "-1025/1024" 53 .Floor == acothPrecRound (F "-1025/1024" 53) 53 .Floor
#guard T "100" 20 .Ceiling == acothPrecRound (F "100" 53) 20 .Ceiling
#guard acothRat (Q "3") 53 == (T "3" 53).1
private def odd (q : AzRat) (p : Nat) (m : RoundingMode) : Bool :=
  let r := acothRatPrecRound q p (-m)
  acothRatPrecRound (-q) p m == (-r.1, r.2.swap)
#guard odd (Q "3") 53 .Nearest && odd (Q "22/7") 53 .Floor
#guard odd (Q "1000000007") 20 .Ceiling && odd (Q "1000001/1000000") 53 .Floor
#guard (toString (acothRat (Q "3") 200)).startsWith
  "0.346573590279972654708616060729088284037750067180127627"
#guard (toString (acothRat (Q "-22/7") 200)).startsWith
  "-0.32962281444213198059363373110659913066071050091573845"

-- huge rationals: just outside `1/q`
private def pw (k : Nat) : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 1) <<< k)
#guard acothRatPrecRound (pw 5000)⁻¹ 53 .Nearest == (h (F "1" 53) (-5000), .lt)
#guard acothRatPrecRound (pw 5000)⁻¹ 53 .Floor == (h (F "1" 53) (-5000), .lt)
#guard acothRatPrecRound (pw 5000)⁻¹ 53 .Ceiling == (h up (-5000), .gt)
#guard acothRatPrecRound (-(pw 5000)⁻¹) 53 .Nearest == (-(h (F "1" 53) (-5000)), .gt)
#guard acothRatPrecRound (Q "3" * (pw 5000)⁻¹) 53 .Nearest
  == (h (F "6004799503160661/18014398509481984" 53) (-5000), .lt)
#guard acothRatPrecRound (Q "3" * (pw 5000)⁻¹) 53 .Ceiling
  == (h (F "3002399751580331/9007199254740992" 53) (-5000), .gt)

-- next to `±1`
#guard acothRatPrecRound (1 + pw 5000) 53 .Nearest == (F "1905689523656919/1099511627776" 53, .lt)
#guard acothRatPrecRound (1 + pw 5000) 53 .Floor == (F "1905689523656919/1099511627776" 53, .lt)
#guard acothRatPrecRound (1 + pw 5000) 53 .Ceiling == (F "7622758094627677/4398046511104" 53, .gt)
#guard odd (1 + pw 5000) 53 .Floor
