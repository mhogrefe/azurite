/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.SinhCoshRat
import Azurite.AzFloat.SinhCosh
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `sinhCoshRat`

The joint rational computation against the two separate ones (themselves tested against an
independent reference in `Tests/SinhRat.lean` and `Tests/CoshRat.lean`): the special values
(`0`, `p = 0`), exact rationals from `10^(−30)/3` to `10^6/3` of both signs in the three modes
and at several precisions, tiny rationals where one or both tiny-argument tests answer,
agreement with the float `sinhCosh` at representable arguments, and `sinhCoshRat`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def ok (q : AzRat) (p : Nat) (m : RoundingMode) : Bool :=
  sinhCoshRatPrecRound q p m == (sinhRatPrecRound q p m, coshRatPrecRound q p m)
private def ok3 (q : AzRat) (p : Nat) : Bool :=
  ok q p .Nearest && ok q p .Floor && ok q p .Ceiling && ok (-q) p .Nearest && ok (-q) p .Floor

-- special values
#guard sinhCoshRatPrecRound (Q "0") 53 .Nearest == ((zero, .eq), (F "1" 53, .eq))
#guard sinhCoshRatPrecRound (Q "0") 0 .Nearest == ((zero, .eq), (nan, .eq))
#guard sinhCoshRatPrecRound (Q "1/3") 0 .Nearest == ((nan, .eq), (nan, .eq))

-- against the separate computations
#guard ok3 (Q "1") 53 && ok3 (Q "1/3") 53 && ok3 (Q "22/7") 53 && ok3 (Q "355/113") 53
#guard ok3 (Q "7/5") 53 && ok3 (Q "100/3") 53 && ok3 (Q "700/3") 53 && ok3 (Q "1000000/3") 53
#guard ok3 (Q "1/1000") 53 && ok3 (Q "1/1000000007") 53
#guard ok3 (Q "1/3000000000000000000000000000000") 53
#guard ok3 (Q "1/3") 1 && ok3 (Q "1/3") 2 && ok3 (Q "1/3") 20 && ok3 (Q "22/7") 113
#guard ok3 (Q "7/5") 200 && ok3 (Q "12345/7") 113
-- tiny rationals
private def pw (k : Nat) : AzRat := AzRat.ofAzNats (AzNat.ofNat 1) ((AzNat.ofNat 1) <<< k)
#guard ok3 (pw 5000) 53 && ok3 (Q "1/3" * pw 5000) 53 && ok3 (pw 200) 53 && ok3 (pw 100) 53
#guard ok3 (Q "1/3" * pw 70) 53 && ok3 (Q "1/3" * pw 60) 53 && ok3 (Q "5/7" * pw 30) 53

-- agreement with the float version, and `sinhCoshRat`
#guard sinhCoshRatPrecRound (Q "3/2") 53 .Nearest == sinhCoshPrecRound (F "3/2" 53) 53 .Nearest
#guard sinhCoshRatPrecRound (Q "-5/1024") 53 .Floor
  == sinhCoshPrecRound (F "-5/1024" 53) 53 .Floor
#guard sinhCoshRat (Q "1/3") 53 == (sinhRat (Q "1/3") 53, coshRat (Q "1/3") 53)
