/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AsechRat
import Azurite.AzFloat.Asech
import Azurite.AzFloat.LnRat
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `asech q` of a rational

The special values (`asech 0 = +∞`; `asech 1 = 0`; `NaN` for `q < 0` and `q > 1`; `p = 0`),
the correctly rounded 53-bit values at exact rationals from `10^(−30)/3` to `1 − 10^(−30)/3`
in three modes, 1-, 2-, 20-, 113- and 200-bit results, agreement with the float `asech` at
representable arguments, 200-bit strings, and a tiny rational (where `asech q` rounds like
`ln (2/q)`).  References: an independent 6000-bit fixed-point evaluation of
`ln (1/q + √(1/q² − 1))` rounded with exact rationals.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
private def T (q : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  asechRatPrecRound (Q q) p m

-- special values
#guard T "0" 53 == (infinity true, .eq)
#guard T "0" 0 == (infinity true, .eq)
#guard T "1" 53 == (zero, .eq)
#guard T "3/3" 0 == (zero, .eq)
#guard T "2" 53 == (nan, .eq)
#guard T "1000001/1000000" 53 == (nan, .eq)
#guard T "-1/2" 53 == (nan, .eq)
#guard T "-1" 53 == (nan, .eq)
#guard T "-3" 53 == (nan, .eq)
#guard T "1/3" 0 == (nan, .eq)

-- correctly rounded values at exact rationals
#guard T "1/2" 53 == (F "5931051093853237/4503599627370496" 53, .gt)
#guard T "1/3" 53 == (F "7938707516150823/4503599627370496" 53, .gt)
#guard T "2/7" 53 == (F "4334370792049413/2251799813685248" 53, .gt)
#guard T "7/22" 53 == (F "8160300771249005/4503599627370496" 53, .gt)
#guard T "113/355" 53 == (F "4079194724512939/2251799813685248" 53, .gt)
#guard T "99/100" 53 == (F "5116609459402097/36028797018963968" 53, .gt)
#guard T "999999999/1000000000" 53 == (F "3299853898363415/73786976294838206464" 53, .lt)
#guard T "1/1000" 53 == (F "2139463772410805/281474976710656" 53, .gt)
#guard T "1/1000000007" 53 == (F "6028184357298717/281474976710656" 53, .gt)
#guard T "3/1125899906842624" 53 == (F "2410262760849161/70368744177664" 53, .lt)
#guard T "1/3000000000000000000000000000000" 53 == (F "1246746126101009/17592186044416" 53, .lt)
#guard T "2999999999999999999999999999999/3000000000000000000000000000000" 53
  == (F "1035032380897329/1267650600228229401496703205376" 53, .gt)
#guard T "1/3" 53 .Floor == (F "3969353758075411/2251799813685248" 53, .lt)
#guard T "2/7" 53 .Floor == (F "8668741584098825/4503599627370496" 53, .lt)
#guard T "99/100" 53 .Floor == (F "319788091212631/2251799813685248" 53, .lt)
#guard T "1/1000000007" 53 .Floor == (F "1507046089324679/70368744177664" 53, .lt)
#guard T "1/3" 53 .Ceiling == (F "7938707516150823/4503599627370496" 53, .gt)
#guard T "2/7" 53 .Ceiling == (F "4334370792049413/2251799813685248" 53, .gt)
#guard T "99/100" 53 .Ceiling == (F "5116609459402097/36028797018963968" 53, .gt)
#guard T "1/1000000007" 53 .Ceiling == (F "6028184357298717/281474976710656" 53, .gt)
#guard T "1/3" 20 == (F "924187/524288" 20, .lt)
#guard T "1/3" 1 == (F "2" 1, .gt)
#guard T "7/22" 2 == (F "2" 2, .gt)
#guard T "1/3" 113
  == (F "9152706614154291559812342711297187/5192296858534827628530496329220096" 113, .lt)
#guard T "5/7" 200
  == (h (F "696619474465246027754818035546008576481904682180959016208361" 200) (-199), .gt)

-- agreement with the float `asech` at representable arguments
#guard T "3/4" 53 == asechPrecRound (F "3/4" 53) 53 .Nearest
#guard T "5/1024" 53 .Floor == asechPrecRound (F "5/1024" 53) 53 .Floor
#guard T "1023/1024" 20 .Ceiling == asechPrecRound (F "1023/1024" 53) 20 .Ceiling
#guard asechRat (Q "1/3") 53 == (T "1/3" 53).1
#guard (toString (asechRat (Q "1/3") 200)).startsWith
  "1.762747174039086050465218649959584618056320656523270821"
#guard (toString (asechRat (Q "7/22") 200)).startsWith
  "1.811950760821413556235972813109322036695962129898042791"

-- a tiny rational: `asech q` rounds like `ln (2/q)`
private def pw (k : Nat) : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 1) <<< k)
private def bigq : AzRat := Q "6" * (pw 5000)⁻¹
#guard asechRatPrecRound (Q "1/3" * pw 5000) 53 .Nearest == lnRatPrecRound bigq 53 .Nearest
#guard asechRatPrecRound (Q "1/3" * pw 5000) 53 .Floor == lnRatPrecRound bigq 53 .Floor
