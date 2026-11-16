/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Atan2Bracket
import Azurite.AzFloat.LnBracket
import Azurite.AzFloat.Sqrt
import Azurite.AzRat.Add
import Azurite.AzRat.Sub

/-!
## The brackets of `acosh x` and `acosh q`

`acosh x = ln (x + √(x² − 1))` for `x > 1`.  Next to `1` the difference `x² − 1` would cancel,
so it is computed as the product `(x − 1)(x + 1)` of two differences known with *relative*
accuracy: for a float `x` the rounded `x − 1` and `x + 1`, for a rational `q` the roundings of
the exact rationals `q − 1` and `q + 1`.  `acoshArg xl dl sl W` is the float
`⌊xl + ⌊√⌊dl · sl⌋⌋⌋` just below `V = x + √(x² − 1)` from floats `xl`, `dl`, `sl` just below
`x`, `x − 1`, `x + 1` (`y ≤ V ≤ y (1 + 8·2^(−W))`), and the brackets are `lnFloorBracket y w`
(`AzFloat/LnBracket.lean`) at `W = w + 8`.

The logarithm has absolute accuracy, and `acosh x ≈ √(2 (x − 1))` next to `1`, so the Ziv loops
of `AzFloat/Acosh.lean` start with `acoshExtra` more bits: half the leading zero bits of
`x − 1`.

The proofs are in `Equiv/AcoshBracket.lean`.
-/

namespace Azurite.AzFloat

/-- A float just below `x + √(x² − 1)` from floats `xl`, `dl`, `sl` just below `x`, `x − 1`,
`x + 1`, every operation rounded down at precision `W`. -/
def acoshArg (xl dl sl : AzFloat) (W : Nat) : AzFloat :=
  let m := (mulPrecRound dl sl W .Floor).1
  let r := (sqrtPrecRound m W .Floor).1
  (addPrecRound xl r W .Floor).1

/-- The bracket of `acosh x` at Ziv level `w` for a finite float `x > 1`. -/
def acoshBracket (x : AzFloat) (w : Nat) : Encl :=
  let W := w + 8
  lnFloorBracket
    (acoshArg x (subPrecRound x one W .Floor).1 (addPrecRound x one W .Floor).1 W) w

/-- The bracket of `acosh x` as a pair of `Roundable`s. -/
def acoshApprox (x : AzFloat) (w : Nat) : Roundable × Roundable :=
  enclApprox false (acoshBracket x w)

/-- The bracket of `acosh q` at Ziv level `w` for a rational `q > 1`. -/
def acoshRatBracket (q : AzRat) (w : Nat) : Encl :=
  let W := w + 8
  lnFloorBracket
    (acoshArg (ofAzRatRound q W .Floor).1 (ofAzRatRound (q - 1) W .Floor).1
      (ofAzRatRound (q + 1) W .Floor).1 W) w

/-- The bracket of `acosh q` as a pair of `Roundable`s. -/
def acoshRatApprox (q : AzRat) (w : Nat) : Roundable × Roundable :=
  enclApprox false (acoshRatBracket q w)

/-- The extra starting bits of the Ziv loop from a float `d ≈ x − 1`: half its leading zero
bits (the result is `≈ √(2 (x − 1))`). -/
def acoshExtra (d : AzFloat) : Nat :=
  match d.exponent? with
  | some ed => if ed.sign then 0 else ed.abs.toNat / 2 + 1
  | none => 0

end Azurite.AzFloat
