/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AsinhRat
import Azurite.AzFloat.Asinh
import Azurite.AzFloat.LnRat
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `asinh q` of a rational

The special values (`0`, `p = 0`), the correctly rounded 53-bit values at exact rationals from
`10^(−30)/3` to `700/3` in three modes, 1-, 2-, 20-, 113- and 200-bit results, agreement with
the float `asinh` at representable arguments, oddness, 200-bit strings, tiny rationals
`±2^(−5000)`, `±1/(3·2^5000)` (just inside `q`, at no cost), and a huge rational (where
`asinh q` rounds like `ln (2q)`).  References: an independent 6000-bit fixed-point evaluation
of `ln (q + √(q² + 1))` rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
private def dn : AzFloat := F "9007199254740991/9007199254740992" 53
private def T (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  asinhRatPrecRound (Q q) p m

-- special values
#guard T "0" 53 == (zero, .eq)
#guard T "0" 0 == (zero, .eq)
#guard T "1/3" 0 == (nan, .eq)

-- correctly rounded values at exact rationals
#guard T "1" 53 == (F "7938707516150823/9007199254740992" 53, .gt)
#guard T "-1" 53 == (F "-7938707516150823/9007199254740992" 53, .lt)
#guard T "1/3" 53 == (F "737352187295465/2251799813685248" 53, .lt)
#guard T "-2/7" 53 == (F "-1269849538948185/4503599627370496" 53, .gt)
#guard T "22/7" 53 == (F "8388761401176599/4503599627370496" 53, .gt)
#guard T "355/113" 53 == (F "2096758695007529/1125899906842624" 53, .lt)
#guard T "-7/5" 53 == (F "-1281253879910281/1125899906842624" 53, .lt)
#guard T "10" 53 == (F "6751397880867803/2251799813685248" 53, .gt)
#guard T "-100/3" 53 == (F "-1182175199493811/281474976710656" 53, .lt)
#guard T "1/1000" 53 == (F "4611685249813397/4611686018427387904" 53, .lt)
#guard T "-1/1000000007" 53 == (F "-2417851622304297/2417851639229258349412352" 53, .lt)
#guard T "3/1125899906842624" 53 == (F "3/1125899906842624" 53, .gt)
#guard T "1/3000000000000000000000000000000" 53
  == (F "3805993847215893/11417981541647679048466287755595961091061972992" 53, .lt)
#guard T "700/3" 53 == (F "6919352781409941/1125899906842624" 53, .lt)
#guard T "1/3" 53 .Floor == (F "737352187295465/2251799813685248" 53, .lt)
#guard T "-2/7" 53 .Floor == (F "-5079398155792741/18014398509481984" 53, .lt)
#guard T "22/7" 53 .Floor == (F "4194380700588299/2251799813685248" 53, .lt)
#guard T "-100/3" 53 .Floor == (F "-1182175199493811/281474976710656" 53, .lt)
#guard T "1/1000000007" 53 .Floor == (F "4835703244608593/4835703278458516698824704" 53, .lt)
#guard T "1/3" 53 .Ceiling == (F "5898817498363721/18014398509481984" 53, .gt)
#guard T "-2/7" 53 .Ceiling == (F "-1269849538948185/4503599627370496" 53, .gt)
#guard T "22/7" 53 .Ceiling == (F "8388761401176599/4503599627370496" 53, .gt)
#guard T "-100/3" 53 .Ceiling == (F "-4728700797975243/1125899906842624" 53, .gt)
#guard T "1/1000000007" 53 .Ceiling == (F "2417851622304297/2417851639229258349412352" 53, .gt)
#guard T "1/3" 20 == (F "686713/2097152" 20, .gt)
#guard T "1/3" 1 == (F "1/4" 1, .lt)
#guard T "-22/7" 2 == (F "-2" 2, .lt)
#guard T "1/3" 113
  == (F "6800873545614697428443674336799377/20769187434139310514121985316880384" 113, .lt)
#guard T "-7/5" 200
  == (h (F "-914333321936253769731321016680565313586969682829540247550025" 200) (-199), .lt)

-- agreement with the float `asinh` at representable arguments, oddness
#guard T "3/2" 53 == asinhPrecRound (F "3/2" 53) 53 .Nearest
#guard T "-5/1024" 53 .Floor == asinhPrecRound (F "-5/1024" 53) 53 .Floor
#guard T "100" 20 .Ceiling == asinhPrecRound (F "100" 53) 20 .Ceiling
#guard asinhRat (Q "1/3") 53 == (T "1/3" 53).1
private def odd (q : AzRat) (p : Nat) (m : RoundingMode) : Bool :=
  let r := asinhRatPrecRound q p (-m)
  asinhRatPrecRound (-q) p m == (-r.1, r.2.swap)
#guard odd (Q "1/3") 53 .Nearest && odd (Q "22/7") 53 .Floor
#guard odd (Q "1/1000000007") 20 .Ceiling && odd (Q "1000000/3") 53 .Floor
#guard (toString (asinhRat (Q "1/3") 200)).startsWith
  "0.327450150237258443322535259988258127700524528990767451"
#guard (toString (asinhRat (Q "-22/7") 200)).startsWith
  "-1.86267921113460998501900148294962754044416265892031043"

-- tiny rationals: just inside `q`
private def pw (k : Nat) : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 1) <<< k)
#guard asinhRatPrecRound (pw 5000) 53 .Nearest == (h (F "1" 53) (-5000), .gt)
#guard asinhRatPrecRound (pw 5000) 53 .Ceiling == (h (F "1" 53) (-5000), .gt)
#guard asinhRatPrecRound (pw 5000) 53 .Floor == (h dn (-5000), .lt)
#guard asinhRatPrecRound (-(pw 5000)) 53 .Nearest == (-(h (F "1" 53) (-5000)), .lt)
#guard asinhRatPrecRound (-(pw 5000)) 53 .Ceiling == (-(h dn (-5000)), .gt)
#guard asinhRatPrecRound (Q "1/3" * pw 5000) 53 .Nearest
  == (h (F "6004799503160661/18014398509481984" 53) (-5000), .lt)
#guard asinhRatPrecRound (Q "1/3" * pw 5000) 53 .Ceiling
  == (h (F "3002399751580331/9007199254740992" 53) (-5000), .gt)

-- a huge rational: `asinh q` rounds like `ln (2q)`
private def bigq : AzRat := Q "2/3" * (pw 5000)⁻¹
#guard asinhRatPrecRound (Q "1/3" * (pw 5000)⁻¹) 53 .Nearest == lnRatPrecRound bigq 53 .Nearest
#guard asinhRatPrecRound (Q "1/3" * (pw 5000)⁻¹) 53 .Floor == lnRatPrecRound bigq 53 .Floor
