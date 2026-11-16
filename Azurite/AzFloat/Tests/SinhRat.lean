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
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def T (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  sinhRatPrecRound (Q q) p m
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k

-- special values
#guard T "0" 53 == (zero, .eq)
#guard T "0" 0 == (zero, .eq)
#guard T "1/3" 0 == (nan, .eq)

-- correctly rounded values at exact rationals
#guard T "1" 53 == (F "2646317828889793/2251799813685248" 53, .lt)
#guard T "-1" 53 == (F "-2646317828889793/2251799813685248" 53, .gt)
#guard T "1/3" 53 == (F "6116618908543873/18014398509481984" 53, .lt)
#guard T "-2/7" 53 == (F "-5217284198980025/18014398509481984" 53, .lt)
#guard T "22/7" 53 == (F "6509619147470761/562949953421312" 53, .gt)
#guard T "355/113" 53 == (F "1625341006015909/140737488355328" 53, .lt)
#guard T "-7/5" 53 == (F "-8576211532338205/4503599627370496" 53, .lt)
#guard T "10" 53 == (F "3027294401285321/274877906944" 53, .gt)
#guard T "-100/3" 53 == (F "-2396473975313455/16" 53, .lt)
#guard T "1/1000" 53 == (F "4611686787041763/4611686018427387904" 53, .gt)
#guard T "-1/1000000007" 53 == (F "-2417851622304297/2417851639229258349412352" 53, .lt)
#guard T "3/1125899906842624" 53 == (F "3/1125899906842624" 53, .lt)
#guard T "1/3000000000000000000000000000000" 53
  == (F "3805993847215893/11417981541647679048466287755595961091061972992" 53, .lt)
#guard T "700/3" 53
  == (h (F "3482012665771007" 53) (284), .lt)
#guard T "1/3" 53 .Floor == (F "6116618908543873/18014398509481984" 53, .lt)
#guard T "-2/7" 53 .Floor == (F "-5217284198980025/18014398509481984" 53, .lt)
#guard T "22/7" 53 .Floor == (F "813702393433845/70368744177664" 53, .lt)
#guard T "-100/3" 53 .Floor == (F "-2396473975313455/16" 53, .lt)
#guard T "1/1000000007" 53 .Floor == (F "4835703244608593/4835703278458516698824704" 53, .lt)
#guard T "1/3" 53 .Ceiling == (F "3058309454271937/9007199254740992" 53, .gt)
#guard T "-2/7" 53 .Ceiling == (F "-652160524872503/2251799813685248" 53, .gt)
#guard T "22/7" 53 .Ceiling == (F "6509619147470761/562949953421312" 53, .gt)
#guard T "-100/3" 53 .Ceiling == (F "-4792947950626909/32" 53, .gt)
#guard T "1/1000000007" 53 .Ceiling == (F "2417851622304297/2417851639229258349412352" 53, .gt)
#guard T "1/3" 20 == (F "178017/524288" 20, .lt)
#guard T "1/3" 1 == (F "1/4" 1, .lt)
#guard T "-22/7" 2 == (F "-12" 2, .lt)
#guard T "1/3" 113
  == (F "7051981475145092557835873610582885/20769187434139310514121985316880384" 113, .lt)
#guard T "-7/5" 200
  == (h (F "-765023632605496716486344383993527490320167676841436943137735" 200) (-198), .gt)

-- agreement with the float `sinh` at representable arguments, oddness
#guard T "3/2" 53 == sinhPrecRound (F "3/2" 53) 53 .Nearest
#guard T "-5/1024" 53 .Floor == sinhPrecRound (F "-5/1024" 53) 53 .Floor
#guard T "100" 20 .Ceiling == sinhPrecRound (F "100" 53) 20 .Ceiling
#guard sinhRat (Q "1/3") 53 == (T "1/3" 53).1
private def odd (q : String) (p : Nat) (m : RoundingMode) : Bool :=
  let r := T q p (-m)
  sinhRatPrecRound (-(Q q)) p m == (-r.1, r.2.swap)
#guard odd "1/3" 53 .Nearest && odd "22/7" 53 .Floor && odd "1/1000000007" 20 .Ceiling
#guard (toString (sinhRat (Q "1/3") 200)).startsWith
  "0.339540557256150139101260611338603585072397227688963912"
#guard (toString (sinhRat (Q "-22/7") 200)).startsWith
  "-11.5634064945005138164164608506167269191510778996939692"

-- tiny rationals: just outside `q`
private def pw (k : Nat) : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 1) <<< k)
private def up : AzFloat := F "4503599627370497/4503599627370496" 53
#guard sinhRatPrecRound (pw 5000) 53 .Nearest == (h (F "1" 53) (-5000), .lt)
#guard sinhRatPrecRound (pw 5000) 53 .Floor == (h (F "1" 53) (-5000), .lt)
#guard sinhRatPrecRound (pw 5000) 53 .Ceiling == (h up (-5000), .gt)
#guard sinhRatPrecRound (-(pw 5000)) 53 .Nearest == (-(h (F "1" 53) (-5000)), .gt)
#guard sinhRatPrecRound (-(pw 5000)) 53 .Floor == (-(h up (-5000)), .lt)
#guard sinhRatPrecRound (Q "1/3" * pw 5000) 53 .Nearest
  == (h (F "6004799503160661/18014398509481984" 53) (-5000), .lt)
#guard sinhRatPrecRound (Q "1/3" * pw 5000) 53 .Ceiling
  == (h (F "3002399751580331/9007199254740992" 53) (-5000), .gt)
#guard sinhRatPrecRound (Q "-1/3" * pw 5000) 53 .Floor
  == (-(h (F "3002399751580331/9007199254740992" 53) (-5000)), .lt)

-- a large rational: `sinh q` rounds like `exp q / 2`
private def big (q : String) (p : Nat) (m : RoundingMode) : Bool :=
  let r := expRatPrecRound (Q q) p m
  T q p m == (h r.1 (-1), r.2)
#guard big "1000000/3" 53 .Nearest && big "1000000/3" 53 .Floor && big "12345/7" 113 .Ceiling
#guard odd "1000000/3" 53 .Floor
