/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.OfString
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

/-- A float input from its decimal spelling, rounded to nearest at `p` bits. -/
private def X (s : String) (p : Nat) : AzFloat := (ofDecimalString s p).get!
/-- `0.3333333333…` at 200 bits. -/
private def third200 : AzFloat :=
  X "0.3333333333333333333333333333333333333333333333333333333333334" 200
private def h (x : AzFloat) (k : Int) : AzFloat := x <<< AzInt.ofInt k
private def ok (x : AzFloat) (p : Nat) (m : RoundingMode) : Bool :=
  sinhCoshPrecRound x p m == (sinhPrecRound x p m, coshPrecRound x p m)
private def ok3 (x : AzFloat) (p : Nat) : Bool :=
  ok x p .Nearest && ok x p .Floor && ok x p .Ceiling && ok (-x) p .Nearest && ok (-x) p .Floor
/-- A result as its decimal output and its comparison tag. -/
private def D (r : AzFloat × Ordering) : String × Ordering := (toString r.1, r.2)
/-- A pair of results as decimal output. -/
private def D2 (r : (AzFloat × Ordering) × (AzFloat × Ordering)) :
    (String × Ordering) × (String × Ordering) := (D r.1, D r.2)

-- special values
#guard D2 (sinhCoshPrecRound nan 53 .Nearest) == (("NaN", .eq), ("NaN", .eq))
#guard D2 (sinhCoshPrecRound (infinity true) 53 .Nearest) == (("Infinity", .eq), ("Infinity", .eq))
#guard D2 (sinhCoshPrecRound (infinity false) 53 .Nearest) ==
  (("-Infinity", .eq), ("Infinity", .eq))
#guard D2 (sinhCoshPrecRound zero 53 .Nearest) == (("0.0", .eq), ("1.0", .eq))
#guard D2 (sinhCoshPrecRound zero 0 .Nearest) == (("0.0", .eq), ("NaN", .eq))
#guard D2 (sinhCoshPrecRound (X "2" 53) 0 .Nearest) == (("NaN", .eq), ("NaN", .eq))

-- literal values
#guard D2 (sinhCoshPrecRound (X "1" 53) 53 .Nearest) ==
  (("1.1752011936438014", .lt), ("1.5430806348152437", .lt))
#guard toString (sinhCosh (X "1" 200)).1 == "1.1752011936438014568823818505956008151557179813340958\
  70229566"
#guard toString (sinhCosh (X "1" 200)).2 == "1.5430806348152437784779056207570616826015291123658637\
  04737402"

-- against the separate computations
#guard ok3 (X "1" 53) 53 && ok3 (X "1.5" 53) 53 && ok3 (X "0.3333333333333333" 53) 53
  && ok3 (X "3.142857142857143" 53) 53
#guard ok3 (X "10" 53) 53 && ok3 (X "100" 53) 53 && ok3 (X "700" 53) 53
#guard ok3 (X "0.001" 53) 53 && ok3 (X "0.000000000001" 53) 53
#guard ok3 (X "1" 53) 1 && ok3 (X "1" 53) 2 && ok3 (X "1.5" 53) 20 && ok3 (X "1.5" 53) 113
#guard ok3 third200 200 && ok3 third200 10 && ok3 (X "10" 53) 300
#guard ok3 (X "1048576" 53) 53 && ok3 (X "15432098.625" 53) 20
-- tiny arguments: both tests answer, or the one of `cosh` only, or none
#guard ok3 (h (X "1" 53) (-1000)) 53 && ok3 (h (X "3" 53) (-1073741824)) 53
#guard ok3 (h (X "1" 53) (-200)) 53 && ok3 (h (X "1" 53) (-100)) 53
#guard ok3 (h (X "1" 53) (-70)) 53 && ok3 (h (X "1" 53) (-60)) 53 && ok3 (h (X "1" 53) (-40)) 53
#guard ok3 (h (X "1" 53) (-26)) 53 && ok3 (h (X "1" 53) (-27)) 53 && ok3 (h (X "5" 53) (-30)) 53
#guard sinhCosh (X "1.5" 53) == (sinh (X "1.5" 53), cosh (X "1.5" 53))
