/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzInt.SweeneyHorner
import Azurite.AzNat.Compare

/-!
# Tests for the truncated backward recurrence of Sweeney's series

Small partial sums `∑_{k<N} (−1)^k n^(k+1) / ((k+1) (k+1)!)` against their exact fractions
(by cross multiplication); for the sizes the constant uses, enclosures computed with different
working sizes and block sizes must overlap, and the width `(c − a) / d` must be below `2^(−g)`
for `V = g + ⌈1.5 n⌉ + 16`.  Both loops (word blocks only, `Lb = 0`, and long blocks) and block
sizes around the limb boundaries are covered.
-/

namespace Azurite.AzInt

/-- `a / d ≤ t / q ≤ c / d` for the enclosure of the partial sum. -/
private def encloses (n N V Lb t q : Nat) : Bool :=
  let e := sweeneyHornerEncl n N V Lb
  let T := AzNat.ofNat t
  let Q := AzNat.ofNat q
  compare (e.1 * Q) (T * e.2.2) != .gt && compare (T * e.2.2) (e.2.1 * Q) != .gt

/-- Two enclosures of the same sum overlap. -/
private def overlap (n N V Lb V' Lb' : Nat) : Bool :=
  let e := sweeneyHornerEncl n N V Lb
  let f := sweeneyHornerEncl n N V' Lb'
  compare (e.1 * f.2.2) (f.2.1 * e.2.2) != .gt && compare (f.1 * e.2.2) (e.2.1 * f.2.2) != .gt

/-- The width of the enclosure is at most `2^(−g)`. -/
private def narrow (n N V Lb g : Nat) : Bool :=
  let e := sweeneyHornerEncl n N V Lb
  compare ((e.2.1 - e.1) <<< g) e.2.2 != .gt

private def terms (n : Nat) : Nat := 37 * ((n + 9) / 10) - 1

/-- Narrow at the working size, and consistent with a much larger one. -/
private def ok (n g Lb : Nat) : Bool :=
  let V := g + 3 * n / 2 + 16
  narrow n (terms n) V Lb g && overlap n (terms n) V Lb (2 * V) 0

-- exact partial sums: `1`, `3/4`, `13/9`, `4347/2400`, and thirteen terms at `n = 7`
#guard encloses 1 1 8 0 1 1 && encloses 1 1 8 64 1 1
#guard encloses 1 2 8 0 3 4 && encloses 1 2 80 0 3 4
#guard encloses 2 3 8 0 13 9 && encloses 2 3 80 64 13 9
#guard encloses 3 5 16 0 4347 2400 && encloses 3 5 200 0 4347 2400
#guard encloses 7 13 32 0 112765420830799860480 38775788043632640000
#guard encloses 7 13 32 64 112765420830799860480 38775788043632640000
#guard encloses 7 13 300 0 112765420830799860480 38775788043632640000
#guard narrow 7 13 300 0 250
#guard encloses 3 0 8 0 0 1
-- the sizes of the constant at 53, 113 and 200 bits, both arguments tried by `eulerGammaArg`
#guard ok 52 73 0
#guard ok 64 73 0
#guard ok 86 121 0
#guard ok 128 121 0
#guard ok 155 221 0
#guard ok 256 221 0
-- long blocks of several sizes (limb boundaries)
#guard ok 155 221 1
#guard ok 155 221 63
#guard ok 155 221 64
#guard ok 155 221 65
#guard ok 155 221 128
#guard ok 155 221 300
#guard ok 256 300 256
#guard ok 400 600 0
#guard ok 400 600 192
-- a block larger than everything: one application at the end
#guard ok 86 121 100000
-- far too few bits: still an enclosure (the radius says how wide)
#guard overlap 86 332 1 0 400 0
#guard overlap 86 332 40 0 400 0
#guard overlap 86 332 40 64 400 0
#guard overlap 155 591 100 128 700 0
-- arguments at and above the word limit of the blocks (an odd number of terms: a positive sum)
#guard overlap 70000 101 400 0 400 64
#guard narrow 70000 101 1400 0 20
#guard overlap 5000000000 21 400 0 400 64
#guard narrow 5000000000 21 2000 64 20

-- the pieces
#guard ((AzNat.ofNat 5).mulNat 7).toNat == 35
#guard ((AzNat.ofNat 5).mulNat (2 ^ 70)).toNat == 5 * 2 ^ 70
#guard ((AzNat.ofNat 5).mulNat (2 ^ 63 - 1)).toNat == 5 * (2 ^ 63 - 1)
#guard ((AzNat.ofNat 5).mulNat (2 ^ 63)).toNat == 5 * 2 ^ 63
#guard sweeneyFits 100 10 100 1 0 0 1
#guard !sweeneyFits (2 ^ 40) 10 100 (2 ^ 30) 0 0 1

end Azurite.AzInt
