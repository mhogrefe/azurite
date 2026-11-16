/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.CothRat
import Azurite.AzFloat.Coth
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `coth q` of a rational

The special values (`coth 0 = +∞`, `p = 0`), the correctly rounded 53-bit values at exact
rationals from `10^(−30)/3` to `700/3` in three modes, the transition to `±1`, 1-, 2-, 20-,
113- and 200-bit results, agreement with the float `coth` at representable arguments, oddness,
200-bit strings, tiny rationals `±2^(−5000)`, `±1/(3·2^5000)` (just outside `1/q`, at no
cost), and large rationals `±10^6/3`, `±2^5000/3` (just outside `±1`, at no cost).  References:
an independent 6000-bit fixed-point evaluation of `(e^(2q) + 1)/(e^(2q) − 1)` rounded with
exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
private def up : AzFloat := F "4503599627370497/4503599627370496" 53
private def T (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  cothRatPrecRound (Q q) p m

-- special values
#guard T "0" 53 == (infinity true, .eq)
#guard T "0" 0 == (infinity true, .eq)
#guard T "1/3" 0 == (nan, .eq)

-- correctly rounded values at exact rationals
#guard T "1" 53 == (F "5913385222499101/4503599627370496" 53, .lt)
#guard T "-1" 53 == (F "-5913385222499101/4503599627370496" 53, .gt)
#guard T "1/3" 53 == (F "7003765483672909/2251799813685248" 53, .gt)
#guard T "-2/7" 53 == (F "-8094598359708903/2251799813685248" 53, .gt)
#guard T "22/7" 53 == (F "2260204441214337/2251799813685248" 53, .gt)
#guard T "355/113" 53 == (F "2260225758549917/2251799813685248" 53, .lt)
#guard T "-7/5" 53 == (F "-5086791939129737/4503599627370496" 53, .gt)
#guard T "10" 53 == (F "4503599645935717/4503599627370496" 53, .lt)
#guard T "-100/3" 53 == (F "-1" 53, .gt)
#guard T "1/1000" 53 == (F "2199023988559703/2199023255552" 53, .gt)
#guard T "-1/1000000007" 53 == (F "-1000000007" 53, .gt)
#guard T "3/1125899906842624" 53 == (F "6004799503160661/16" 53, .lt)
#guard T "1/3000000000000000000000000000000" 53 == (F "2999999999999999778178897805312" 53, .lt)
#guard T "700/3" 53 == (F "1" 53, .lt)
#guard T "1/3" 53 .Floor == (F "1750941370918227/562949953421312" 53, .lt)
#guard T "-2/7" 53 .Floor == (F "-1011824794963613/281474976710656" 53, .lt)
#guard T "22/7" 53 .Floor == (F "4520408882428673/4503599627370496" 53, .lt)
#guard T "-100/3" 53 .Floor == (F "-4503599627370497/4503599627370496" 53, .lt)
#guard T "1/1000000007" 53 .Floor == (F "1000000007" 53, .lt)
#guard T "1/3" 53 .Ceiling == (F "7003765483672909/2251799813685248" 53, .gt)
#guard T "-2/7" 53 .Ceiling == (F "-8094598359708903/2251799813685248" 53, .gt)
#guard T "22/7" 53 .Ceiling == (F "2260204441214337/2251799813685248" 53, .gt)
#guard T "-100/3" 53 .Ceiling == (F "-1" 53, .gt)
#guard T "1/1000000007" 53 .Ceiling == (F "8388608058720257/8388608" 53, .gt)
#guard T "1/3" 20 == (F "407673/131072" 20, .gt)
#guard T "1/3" 1 == (F "4" 1, .gt)
#guard T "-22/7" 2 == (F "-1" 2, .gt)
#guard T "1/3" 113
  == (F "4037395919674835690890492993011515/1298074214633706907132624082305024" 113, .lt)
#guard T "-7/5" 200
  == (h (F "-907514007299774155937927088534219834151874416883610255184569" 200) (-199), .lt)

-- the transition to `±1`
#guard T "55/3" 53 == (F "4503599627370497/4503599627370496" 53, .lt)
#guard T "55/3" 53 .Floor == (F "4503599627370497/4503599627370496" 53, .lt)
#guard T "55/3" 53 .Ceiling == (F "2251799813685249/2251799813685248" 53, .gt)
#guard T "-58/3" 53 == (F "-1" 53, .gt)
#guard T "-58/3" 53 .Floor == (F "-4503599627370497/4503599627370496" 53, .lt)
#guard T "-58/3" 53 .Ceiling == (F "-1" 53, .gt)
#guard T "61/3" 53 == (F "1" 53, .lt)
#guard T "61/3" 53 .Floor == (F "1" 53, .lt)
#guard T "61/3" 53 .Ceiling == (F "4503599627370497/4503599627370496" 53, .gt)

-- agreement with the float `coth` at representable arguments, oddness
#guard T "3/2" 53 == cothPrecRound (F "3/2" 53) 53 .Nearest
#guard T "-5/1024" 53 .Floor == cothPrecRound (F "-5/1024" 53) 53 .Floor
#guard T "100" 20 .Ceiling == cothPrecRound (F "100" 53) 20 .Ceiling
#guard cothRat (Q "1/3") 53 == (T "1/3" 53).1
private def odd (q : AzRat) (p : Nat) (m : RoundingMode) : Bool :=
  let r := cothRatPrecRound q p (-m)
  cothRatPrecRound (-q) p m == (-r.1, r.2.swap)
#guard odd (Q "1/3") 53 .Nearest && odd (Q "22/7") 53 .Floor
#guard odd (Q "1/1000000007") 20 .Ceiling && odd (Q "1000000/3") 53 .Floor
#guard (toString (cothRat (Q "1/3") 200)).startsWith
  "3.110296679619443701378375231417624794566543581787011086"
#guard (toString (cothRat (Q "-22/7") 200)).startsWith
  "-1.00373240439847711869383502509588454092894762000635019"

-- tiny rationals: just outside `1/q`
private def pw (k : Nat) : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 1) <<< k)
#guard cothRatPrecRound (pw 5000) 53 .Nearest == (h (F "1" 53) 5000, .lt)
#guard cothRatPrecRound (pw 5000) 53 .Floor == (h (F "1" 53) 5000, .lt)
#guard cothRatPrecRound (pw 5000) 53 .Ceiling == (h up 5000, .gt)
#guard cothRatPrecRound (-(pw 5000)) 53 .Nearest == (-(h (F "1" 53) 5000), .gt)
#guard cothRatPrecRound (-(pw 5000)) 53 .Floor == (-(h up 5000), .lt)
#guard cothRatPrecRound (Q "1/3" * pw 5000) 53 .Nearest == (h (F "3" 53) 5000, .lt)
#guard cothRatPrecRound (Q "1/3" * pw 5000) 53 .Ceiling
  == (h (F "6755399441055745/2251799813685248" 53) 5000, .gt)
#guard cothRatPrecRound (Q "3" * pw 5000) 53 .Nearest
  == (h (F "6004799503160661/18014398509481984" 53) 5000, .lt)

-- large rationals: just outside `±1`
private def bigOk (q : AzRat) : Bool :=
  cothRatPrecRound q 53 .Nearest == (F "1" 53, .lt)
    && cothRatPrecRound q 53 .Floor == (F "1" 53, .lt)
    && cothRatPrecRound q 53 .Ceiling == (up, .gt)
    && cothRatPrecRound (-q) 53 .Nearest == (F "-1" 53, .gt)
    && cothRatPrecRound (-q) 53 .Floor == (-up, .lt)
    && cothRatPrecRound q 200 .Nearest == (F "1" 200, .lt)
#guard bigOk (Q "1000000/3")
#guard bigOk (Q "1/3" * (pw 5000)⁻¹)
#guard bigOk (Q "700/3")
