/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AcschRat
import Azurite.AzFloat.Acsch
import Azurite.AzFloat.LnRat
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `acsch q` of a rational

The special values (`acsch 0 = +∞`, `p = 0`), the correctly rounded 53-bit values at exact
rationals from `10^(−30)/3` to `700/3` in three modes, 1-, 2-, 20-, 113- and 200-bit results,
agreement with the float `acsch` at representable arguments, oddness, 200-bit strings, huge
rationals `±2^5000`, `±3·2^5000` (just inside `1/q`, at no cost), and a tiny rational (where
`acsch q` rounds like `ln (2/q)`).  References: an independent 6000-bit fixed-point evaluation
of `ln (1/q + √(1/q² + 1))` rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
private def dn : AzFloat := F "9007199254740991/9007199254740992" 53
private def T (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  acschRatPrecRound (Q q) p m

-- special values
#guard T "0" 53 == (infinity true, .eq)
#guard T "0" 0 == (infinity true, .eq)
#guard T "1/3" 0 == (nan, .eq)

-- correctly rounded values at exact rationals
#guard T "1" 53 == (F "7938707516150823/9007199254740992" 53, .gt)
#guard T "-1" 53 == (F "-7938707516150823/9007199254740992" 53, .lt)
#guard T "1/3" 53 == (F "4094777398095367/2251799813685248" 53, .gt)
#guard T "-2/7" 53 == (F "-4426408991817963/2251799813685248" 53, .gt)
#guard T "22/7" 53 == (F "5639296546097153/18014398509481984" 53, .gt)
#guard T "355/113" 53 == (F "5641494506044077/18014398509481984" 53, .lt)
#guard T "-7/5" 53 == (F "-2991879063281823/4503599627370496" 53, .gt)
#guard T "10" 53 == (F "3596901764234783/36028797018963968" 53, .lt)
#guard T "-100/3" 53 == (F "-2161403693219323/72057594037927936" 53, .lt)
#guard T "1/1000" 53 == (F "8557855652593173/1125899906842624" 53, .lt)
#guard T "-1/1000000007" 53 == (F "-6028184357298717/281474976710656" 53, .lt)
#guard T "3/1125899906842624" 53 == (F "2410262760849161/70368744177664" 53, .lt)
#guard T "1/3000000000000000000000000000000" 53 == (F "1246746126101009/17592186044416" 53, .lt)
#guard T "700/3" 53 == (F "308817314808341/72057594037927936" 53, .lt)
#guard T "1/3" 53 .Floor == (F "8189554796190733/4503599627370496" 53, .lt)
#guard T "-2/7" 53 .Floor == (F "-8852817983635927/4503599627370496" 53, .lt)
#guard T "22/7" 53 .Floor == (F "2753562766649/8796093022208" 53, .lt)
#guard T "-100/3" 53 .Floor == (F "-2161403693219323/72057594037927936" 53, .lt)
#guard T "1/1000000007" 53 .Floor == (F "1507046089324679/70368744177664" 53, .lt)
#guard T "1/3" 53 .Ceiling == (F "4094777398095367/2251799813685248" 53, .gt)
#guard T "-2/7" 53 .Ceiling == (F "-4426408991817963/2251799813685248" 53, .gt)
#guard T "22/7" 53 .Ceiling == (F "5639296546097153/18014398509481984" 53, .gt)
#guard T "-100/3" 53 .Ceiling == (F "-8645614772877291/288230376151711744" 53, .gt)
#guard T "1/1000000007" 53 .Ceiling == (F "6028184357298717/281474976710656" 53, .gt)
#guard T "1/3" 20 == (F "476695/262144" 20, .gt)
#guard T "1/3" 1 == (F "2" 1, .gt)
#guard T "-22/7" 2 == (F "-3/8" 2, .lt)
#guard T "1/3" 113
  == (F "2360478459421110266955303728740325/1298074214633706907132624082305024" 113, .gt)
#guard T "-7/5" 200
  == (h (F "-1067538122481062680359814346884023283735224879941423943881701" 200) (-200), .lt)

-- agreement with the float `acsch` at representable arguments, oddness
#guard T "3/2" 53 == acschPrecRound (F "3/2" 53) 53 .Nearest
#guard T "-5/1024" 53 .Floor == acschPrecRound (F "-5/1024" 53) 53 .Floor
#guard T "100" 20 .Ceiling == acschPrecRound (F "100" 53) 20 .Ceiling
#guard acschRat (Q "1/3") 53 == (T "1/3" 53).1
private def odd (q : AzRat) (p : Nat) (m : RoundingMode) : Bool :=
  let r := acschRatPrecRound q p (-m)
  acschRatPrecRound (-q) p m == (-r.1, r.2.swap)
#guard odd (Q "1/3") 53 .Nearest && odd (Q "22/7") 53 .Floor
#guard odd (Q "1/1000000007") 20 .Ceiling && odd (Q "1000000/3") 53 .Floor
#guard (toString (acschRat (Q "1/3") 200)).startsWith
  "1.818446459232066823483698963560708993786253942768121617"
#guard (toString (acschRat (Q "-22/7") 200)).startsWith
  "-0.31304384340830898212066562005248191202452777320872829"

-- huge rationals: just inside `1/q`
private def pw (k : Nat) : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 1) <<< k)
#guard acschRatPrecRound (pw 5000)⁻¹ 53 .Nearest == (h (F "1" 53) (-5000), .gt)
#guard acschRatPrecRound (pw 5000)⁻¹ 53 .Ceiling == (h (F "1" 53) (-5000), .gt)
#guard acschRatPrecRound (pw 5000)⁻¹ 53 .Floor == (h dn (-5000), .lt)
#guard acschRatPrecRound (-(pw 5000)⁻¹) 53 .Nearest == (-(h (F "1" 53) (-5000)), .lt)
#guard acschRatPrecRound (Q "3" * (pw 5000)⁻¹) 53 .Nearest
  == (h (F "6004799503160661/18014398509481984" 53) (-5000), .lt)
#guard acschRatPrecRound (Q "3" * (pw 5000)⁻¹) 53 .Ceiling
  == (h (F "3002399751580331/9007199254740992" 53) (-5000), .gt)

-- a tiny rational: `acsch q` rounds like `ln (2/q)`
private def bigq : AzRat := Q "6" * (pw 5000)⁻¹
#guard acschRatPrecRound (Q "1/3" * pw 5000) 53 .Nearest == lnRatPrecRound bigq 53 .Nearest
#guard acschRatPrecRound (Q "1/3" * pw 5000) 53 .Floor == lnRatPrecRound bigq 53 .Floor
