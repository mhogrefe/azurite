/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.TanhRat
import Azurite.AzFloat.Tanh
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `tanh q` of a rational

The special values (`0`, `p = 0`), the correctly rounded 53-bit values at exact rationals from
`10^(−30)/3` to `700/3` in three modes, the transition to `±1`, 1-, 2-, 20-, 113- and 200-bit
results, agreement with the float `tanh` at representable arguments, oddness, 200-bit strings,
tiny rationals `±2^(−5000)`, `±1/(3·2^5000)` (just inside `q`, at no cost), and large rationals
`±10^6/3`, `±2^5000/3` (just inside `±1`, at no cost).  References: an independent 6000-bit
fixed-point evaluation of `(e^(2q) − 1)/(e^(2q) + 1)` rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
private def dn : AzFloat := F "9007199254740991/9007199254740992" 53
private def T (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  tanhRatPrecRound (Q q) p m

-- special values
#guard T "0" 53 == (zero, .eq)
#guard T "0" 0 == (zero, .eq)
#guard T "1/3" 0 == (nan, .eq)

-- correctly rounded values at exact rationals
#guard T "1" 53 == (F "1714957578484965/2251799813685248" 53, .lt)
#guard T "-1" 53 == (F "-1714957578484965/2251799813685248" 53, .gt)
#guard T "1/3" 53 == (F "2895929289884673/9007199254740992" 53, .lt)
#guard T "-2/7" 53 == (F "-5011344282282849/18014398509481984" 53, .lt)
#guard T "22/7" 53 == (F "8973705755907005/9007199254740992" 53, .lt)
#guard T "355/113" 53 == (F "8973621120336299/9007199254740992" 53, .lt)
#guard T "-7/5" 53 == (F "-996817338233891/1125899906842624" 53, .lt)
#guard T "10" 53 == (F "9007199217610549/9007199254740992" 53, .lt)
#guard T "-100/3" 53 == (F "-1" 53, .lt)
#guard T "1/1000" 53 == (F "2305842240599665/2305843009213693952" 53, .gt)
#guard T "-1/1000000007" 53 == (F "-2417851622304297/2417851639229258349412352" 53, .lt)
#guard T "3/1125899906842624" 53 == (F "3/1125899906842624" 53, .gt)
#guard T "1/3000000000000000000000000000000" 53
  == (F "3805993847215893/11417981541647679048466287755595961091061972992" 53, .lt)
#guard T "700/3" 53 == (F "1" 53, .gt)
#guard T "1/3" 53 .Floor == (F "2895929289884673/9007199254740992" 53, .lt)
#guard T "-2/7" 53 .Floor == (F "-5011344282282849/18014398509481984" 53, .lt)
#guard T "22/7" 53 .Floor == (F "8973705755907005/9007199254740992" 53, .lt)
#guard T "-100/3" 53 .Floor == (F "-1" 53, .lt)
#guard T "1/1000000007" 53 .Floor == (F "4835703244608593/4835703278458516698824704" 53, .lt)
#guard T "1/3" 53 .Ceiling == (F "5791858579769347/18014398509481984" 53, .gt)
#guard T "-2/7" 53 .Ceiling == (F "-156604508821339/562949953421312" 53, .gt)
#guard T "22/7" 53 .Ceiling == (F "4486852877953503/4503599627370496" 53, .gt)
#guard T "-100/3" 53 .Ceiling == (F "-9007199254740991/9007199254740992" 53, .gt)
#guard T "1/1000000007" 53 .Ceiling == (F "2417851622304297/2417851639229258349412352" 53, .gt)
#guard T "1/3" 20 == (F "674261/2097152" 20, .lt)
#guard T "1/3" 1 == (F "1/4" 1, .lt)
#guard T "-22/7" 2 == (F "-1" 2, .lt)
#guard T "1/3" 113
  == (F "6677558308257750314591414875726797/20769187434139310514121985316880384" 113, .gt)
#guard T "-7/5" 200
  == (h (F "-1422705246043617297630066582759662431505938125505099992081429" 200) (-200), .gt)

-- the transition to `±1`
#guard T "55/3" 53 == (F "4503599627370495/4503599627370496" 53, .gt)
#guard T "55/3" 53 .Floor == (F "9007199254740989/9007199254740992" 53, .lt)
#guard T "55/3" 53 .Ceiling == (F "4503599627370495/4503599627370496" 53, .gt)
#guard T "-58/3" 53 == (F "-1" 53, .lt)
#guard T "-58/3" 53 .Floor == (F "-1" 53, .lt)
#guard T "-58/3" 53 .Ceiling == (F "-9007199254740991/9007199254740992" 53, .gt)
#guard T "61/3" 53 == (F "1" 53, .gt)
#guard T "61/3" 53 .Floor == (F "9007199254740991/9007199254740992" 53, .lt)
#guard T "61/3" 53 .Ceiling == (F "1" 53, .gt)

-- agreement with the float `tanh` at representable arguments, oddness
#guard T "3/2" 53 == tanhPrecRound (F "3/2" 53) 53 .Nearest
#guard T "-5/1024" 53 .Floor == tanhPrecRound (F "-5/1024" 53) 53 .Floor
#guard T "100" 20 .Ceiling == tanhPrecRound (F "100" 53) 20 .Ceiling
#guard tanhRat (Q "1/3") 53 == (T "1/3" 53).1
private def odd (q : AzRat) (p : Nat) (m : RoundingMode) : Bool :=
  let r := tanhRatPrecRound q p (-m)
  tanhRatPrecRound (-q) p m == (-r.1, r.2.swap)
#guard odd (Q "1/3") 53 .Nearest && odd (Q "22/7") 53 .Floor
#guard odd (Q "1/1000000007") 20 .Ceiling && odd (Q "1000000/3") 53 .Floor
#guard (toString (tanhRat (Q "1/3") 200)).startsWith
  "0.321512737531634344719406222425206466005292002502083511"
#guard (toString (tanhRat (Q "-22/7") 200)).startsWith
  "-0.99628147464192520836125220785430942659848830893950662"

-- tiny rationals: just inside `q`
private def pw (k : Nat) : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 1) <<< k)
#guard tanhRatPrecRound (pw 5000) 53 .Nearest == (h (F "1" 53) (-5000), .gt)
#guard tanhRatPrecRound (pw 5000) 53 .Ceiling == (h (F "1" 53) (-5000), .gt)
#guard tanhRatPrecRound (pw 5000) 53 .Floor == (h dn (-5000), .lt)
#guard tanhRatPrecRound (-(pw 5000)) 53 .Nearest == (-(h (F "1" 53) (-5000)), .lt)
#guard tanhRatPrecRound (-(pw 5000)) 53 .Ceiling == (-(h dn (-5000)), .gt)
#guard tanhRatPrecRound (Q "1/3" * pw 5000) 53 .Nearest
  == (h (F "6004799503160661/18014398509481984" 53) (-5000), .lt)
#guard tanhRatPrecRound (Q "1/3" * pw 5000) 53 .Ceiling
  == (h (F "3002399751580331/9007199254740992" 53) (-5000), .gt)

-- large rationals: just inside `±1`
private def bigOk (q : AzRat) : Bool :=
  tanhRatPrecRound q 53 .Nearest == (F "1" 53, .gt)
    && tanhRatPrecRound q 53 .Ceiling == (F "1" 53, .gt)
    && tanhRatPrecRound q 53 .Floor == (dn, .lt)
    && tanhRatPrecRound (-q) 53 .Nearest == (F "-1" 53, .lt)
    && tanhRatPrecRound (-q) 53 .Ceiling == (-dn, .gt)
    && tanhRatPrecRound q 200 .Nearest == (F "1" 200, .gt)
#guard bigOk (Q "1000000/3")
#guard bigOk (Q "1/3" * (pw 5000)⁻¹)
#guard bigOk (Q "700/3")
