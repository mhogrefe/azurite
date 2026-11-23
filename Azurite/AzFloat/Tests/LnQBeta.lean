/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LnQBeta
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `ln |B_q|` and `ln B_q`

The twelve functions: the bases that are not positive and finite, the base `1` (`ln |B|`,
`ln B`), arguments that are not finite (`−∞` at `+∞` for `q > 1`, `NaN` for `q < 1`), `+∞`
at `a = 0`, `NaN` at the poles, `−∞` at the zeros, `p = 0`, the logarithms of the exact
values (`0` at `(1, 1)`, `ln (32/105)`, `ln (243/520)`), bases below and above `1`, the signs
at negative arguments and `NaN` of `ln B_q` where `B_q < 0`, 200 bits of
`ln B_{1/2}(1/2, 1/2) = 0.90473902344111235541578766764502971298869854267660556694391529…`
and of
`ln B_{1/3}(1/3, 2/3) = 0.91112601842466090713046783835925831398192601018261083911187087…`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
/-- The float nearest to a rational at 53 bits. -/
private def F (s : String) : AzFloat := ofAzRat (Q s) 53
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)
private def DL (r : (AzFloat × Ordering) × Bool) : String × Ordering × Bool :=
  (toString r.1.1, r.1.2, r.2)
private def LA (q a b : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  DL (lnAbsQBetaPrecRound (F q) (F a) (F b) p m)
private def L (q a b : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  D (lnQBetaPrecRound (F q) (F a) (F b) p m)
private def LAR (q a b : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  DL (lnAbsQBetaRatPrecRound (Q q) (Q a) (Q b) p m)
private def LR (q a b : String) (p : Nat) (m : RoundingMode := .Nearest) :=
  D (lnQBetaRatPrecRound (Q q) (Q a) (Q b) p m)

/-! ### Floats -/

-- bases and arguments that are not finite, bases `≤ 0`, `p = 0`
#guard DL (lnAbsQBetaPrecRound nan (F "1/2") (F "1/2") 53 .Nearest) == ("NaN", .eq, true)
#guard DL (lnAbsQBetaPrecRound (F "1/2") nan (F "1/2") 53 .Nearest) == ("NaN", .eq, true)
#guard DL (lnAbsQBetaPrecRound (F "1/2") (infinity true) (F "1/2") 53 .Nearest)
  == ("NaN", .eq, true)
#guard DL (lnAbsQBetaPrecRound (F "2") (infinity true) (F "1/2") 53 .Nearest)
  == ("-Infinity", .eq, true)
#guard DL (lnAbsQBetaPrecRound (F "2") (F "1/2") (infinity true) 53 .Nearest)
  == ("-Infinity", .eq, true)
#guard DL (lnAbsQBetaPrecRound (F "2") (infinity true) (F "-1/2") 53 .Nearest)
  == ("NaN", .eq, true)
#guard DL (lnAbsQBetaPrecRound (F "2") (infinity false) (F "1/2") 53 .Nearest)
  == ("NaN", .eq, true)
#guard D (lnQBetaPrecRound (F "2") (infinity true) (F "1/2") 53 .Nearest)
  == ("-Infinity", .eq)
#guard DL (lnAbsQBetaPrecRound (F "1") (infinity true) (F "1/2") 53 .Nearest)
  == ("-Infinity", .eq, true)
#guard LA "0" "1/2" "1/2" 53 == ("NaN", .eq, true)
#guard LA "1/2" "1/2" "1/2" 0 == ("NaN", .eq, true)

-- `0`, the poles, the zeros
#guard LA "1/2" "0" "1/2" 53 == ("Infinity", .eq, true)
#guard LA "1/2" "-3" "1/2" 53 == ("NaN", .eq, true)
#guard LA "1/2" "1/2" "-1/2" 53 == ("-Infinity", .eq, true)
#guard L "1/2" "1/2" "-1/2" 53 == ("-Infinity", .eq)
#guard L "1/2" "0" "1/2" 53 == ("Infinity", .eq)

-- the base `1`: `ln |B|`, `ln B`
#guard LA "1" "1/2" "1/2" 53 == ("1.1447298858494002", .lt, true)
#guard L "1" "1/2" "1/2" 53 == ("1.1447298858494002", .lt)
#guard LA "1" "-1/2" "3/4" 53 == ("0.1807705502178633", .gt, false)
#guard L "1" "-1/2" "3/4" 53 == ("NaN", .eq)

-- the logarithms of the exact values
#guard LA "1/2" "1" "1" 53 == ("0.0", .eq, true)
#guard LA "1/2" "2" "3" 53 == ("-1.1882244473577968", .gt, true)
#guard LA "3" "3" "4" 53 == ("-12.995529506227527", .gt, true)

-- bases below and above `1`
#guard LA "1/2" "1/2" "1/2" 53 == ("0.9047390234411123", .lt, true)
#guard LA "1/2" "1/2" "1/2" 53 .Ceiling == ("0.9047390234411125", .gt, true)
#guard LA "1/2" "1/2" "1/2" 200
  == ("0.904739023441112355415787667645029712988698542676605566943915", .lt, true)
#guard LA "3/4" "1/4" "5/2" 53 == ("1.0432355177441937", .lt, true)
#guard LA "2" "1/2" "3/2" 53 == ("0.5432258218415283", .gt, true)
#guard L "1/2" "1/2" "1/2" 53 == ("0.9047390234411123", .lt)

-- negative arguments: the sign, and `NaN` of `ln B_q` where `B_q < 0`
#guard LA "1/2" "-1/2" "3/4" 53 == ("-0.28145490229578257", .gt, false)
#guard LA "1/2" "-3/2" "-1/4" 53 == ("1.2571523914653662", .lt, false)
#guard LA "2" "-5/2" "7/4" 53 == ("0.016495669023386176", .lt, true)
#guard L "1/2" "-1/2" "3/4" 53 == ("NaN", .eq)
#guard L "2" "-5/2" "7/4" 53 == ("0.016495669023386176", .lt)

-- to nearest at the precision of the arguments
#guard toString (lnAbsQBeta (F "1/2") (F "1/2") (F "1/2")).1 == "0.9047390234411123"
#guard (lnAbsQBeta (F "1/2") (F "-1/2") (F "3/4")).2 == false
#guard toString (lnQBeta (F "1/2") (F "1/2") (F "1/2")) == "0.9047390234411123"

/-! ### Rationals -/

#guard LAR "1/3" "1/3" "2/3" 53 == ("0.9111260184246609", .lt, true)
#guard LAR "1/3" "1/3" "2/3" 200
  == ("0.911126018424660907130467838359258313981926010182610839111871", .gt, true)
#guard LAR "1/3" "2" "3" 53 == ("-0.7607673682349246", .lt, true)
#guard LAR "1/3" "-7/3" "1/2" 53 == ("-1.7508417681536192", .lt, false)
#guard LAR "1/3" "-7/3" "1/3" 53 == ("-Infinity", .eq, true)
#guard LAR "1" "1/2" "1/2" 53 == ("1.1447298858494002", .lt, true)
#guard LAR "-1/3" "1/2" "1/2" 53 == ("NaN", .eq, true)
#guard LR "1/3" "1/3" "2/3" 53 == ("0.9111260184246609", .lt)
#guard LR "1/3" "-7/3" "1/2" 53 == ("NaN", .eq)
#guard toString (lnQBetaRat (Q "1/3") (Q "1/3") (Q "2/3") 53) == "0.9111260184246609"

/-! ### Mixed -/

#guard DL (lnAbsQBetaFloatFloatRatPrecRound (F "1/2") (F "1/2") (Q "1/3") 53 .Nearest)
  == ("1.1683267277566078", .gt, true)
#guard DL (lnAbsQBetaFloatFloatRatPrecRound (F "2") (infinity true) (Q "1/3") 53 .Nearest)
  == ("-Infinity", .eq, true)
#guard DL (lnAbsQBetaFloatFloatRatPrecRound (F "1/2") (infinity true) (Q "1/3") 53 .Nearest)
  == ("NaN", .eq, true)
#guard D (lnQBetaFloatFloatRatPrecRound (F "1/2") (F "-3/2") (Q "1/3") 53 .Nearest)
  == ("-0.43463533305649604", .lt)
#guard DL (lnAbsQBetaFloatRatRatPrecRound (F "1/2") (Q "1/3") (Q "2/3") 53 .Nearest)
  == ("1.038953015492559", .lt, true)
#guard D (lnQBetaFloatRatRatPrecRound (F "1/2") (Q "1/3") (Q "2/3") 53 .Nearest)
  == ("1.038953015492559", .lt)
#guard DL (lnAbsQBetaRatFloatFloatPrecRound (Q "1/3") (F "1/2") (F "1/4") 53 .Nearest)
  == ("1.227833410776224", .gt, true)
#guard D (lnQBetaRatFloatFloatPrecRound (Q "1/3") (F "1/2") (F "1/4") 53 .Nearest)
  == ("1.227833410776224", .gt)
#guard DL (lnAbsQBetaRatFloatRatPrecRound (Q "1/3") (F "1/2") (Q "1/3") 53 .Nearest)
  == ("1.0300813362850731", .lt, true)
#guard D (lnQBetaRatFloatRatPrecRound (Q "1/3") (F "1/2") (Q "1/3") 53 .Nearest)
  == ("1.0300813362850731", .lt)
