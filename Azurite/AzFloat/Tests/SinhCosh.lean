/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.SinhCosh
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse

/-!
# Tests for `sinhCosh`

The joint computation against the two separate ones (themselves tested against an independent
reference in `Tests/Sinh.lean` and `Tests/Cosh.lean`): the special values (`NaN`, `±∞`, `0`,
`p = 0`), arguments from `2^(−200)` to `2^20` of both signs in the three modes and at several
precisions, tiny arguments where one or both tiny-argument tests answer, a few literal values,
and `sinhCosh`.
-/

open Azurite Azurite.AzFloat

private def Q (s : String) : AzRat := (AzRat.parse s).get!
private def F (s : String) (p : Nat) : AzFloat := ofAzRat (Q s) p
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
private def ok (x : AzFloat) (p : Nat) (m : RoundingMode) : Bool :=
  sinhCoshPrecRound x p m == (sinhPrecRound x p m, coshPrecRound x p m)
private def ok3 (x : AzFloat) (p : Nat) : Bool :=
  ok x p .Nearest && ok x p .Floor && ok x p .Ceiling && ok (-x) p .Nearest && ok (-x) p .Floor

-- special values
#guard sinhCoshPrecRound nan 53 .Nearest == ((nan, .eq), (nan, .eq))
#guard sinhCoshPrecRound (infinity true) 53 .Nearest
  == ((infinity true, .eq), (infinity true, .eq))
#guard sinhCoshPrecRound (infinity false) 53 .Nearest
  == ((infinity false, .eq), (infinity true, .eq))
#guard sinhCoshPrecRound zero 53 .Nearest == ((zero, .eq), (F "1" 53, .eq))
#guard sinhCoshPrecRound zero 0 .Nearest == ((zero, .eq), (nan, .eq))
#guard sinhCoshPrecRound (F "2" 53) 0 .Nearest == ((nan, .eq), (nan, .eq))

-- literal values
#guard sinhCoshPrecRound (F "1" 53) 53 .Nearest
  == ((F "2646317828889793/2251799813685248" 53, .lt),
    (F "434338585747285/281474976710656" 53, .lt))
#guard (toString (sinhCosh (F "1" 200)).1).startsWith
  "1.175201193643801456882381850595600815155717981334095870"
#guard (toString (sinhCosh (F "1" 200)).2).startsWith
  "1.543080634815243778477905620757061682601529112365863704"

-- against the separate computations
#guard ok3 (F "1" 53) 53 && ok3 (F "3/2" 53) 53 && ok3 (F "1/3" 53) 53 && ok3 (F "22/7" 53) 53
#guard ok3 (F "10" 53) 53 && ok3 (F "100" 53) 53 && ok3 (F "700" 53) 53
#guard ok3 (F "1/1000" 53) 53 && ok3 (F "1/1000000000000" 53) 53
#guard ok3 (F "1" 53) 1 && ok3 (F "1" 53) 2 && ok3 (F "3/2" 53) 20 && ok3 (F "3/2" 53) 113
#guard ok3 (F "1/3" 200) 200 && ok3 (F "1/3" 200) 10 && ok3 (F "10" 53) 300
#guard ok3 (F "1048576" 53) 53 && ok3 (F "123456789/8" 53) 20
-- tiny arguments: both tests answer, or the one of `cosh` only, or none
#guard ok3 (h (F "1" 53) (-1000)) 53 && ok3 (h (F "3" 53) (-1073741824)) 53
#guard ok3 (h (F "1" 53) (-200)) 53 && ok3 (h (F "1" 53) (-100)) 53
#guard ok3 (h (F "1" 53) (-70)) 53 && ok3 (h (F "1" 53) (-60)) 53 && ok3 (h (F "1" 53) (-40)) 53
#guard ok3 (h (F "1" 53) (-26)) 53 && ok3 (h (F "1" 53) (-27)) 53 && ok3 (h (F "5" 53) (-30)) 53
#guard sinhCosh (F "3/2" 53) == (sinh (F "3/2" 53), cosh (F "3/2" 53))
