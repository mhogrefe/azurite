/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Basic

/-!
## Comparison with a doubled operand

`cmpDouble x y` compares `x` with `2 y` without allocating `2 y`: the limbs of `2 y` are formed
on the fly from those of `y` (each is the low word of `2 yᵢ` plus the top bit of `yᵢ₋₁`) and
compared with those of `x` from the most significant position down, over
`max x.size (y.size + 1)` positions since `2 y` has at most one limb more than `y`.  When the
limb counts differ the loop decides at its first or second step.
-/

namespace Azurite.AzNat

/-- Limb `i` of `2 y`, from the limbs of `y` (limbs beyond the array read as zero): the low word
of `2 yᵢ` plus the top bit of `yᵢ₋₁`.  The sum never carries, since the first summand is even. -/
@[inline] def doubleLimb (y : Array UInt64) (i : Nat) : UInt64 :=
  (y.getD i 0 <<< 1) + (if i = 0 then (0 : UInt64) else y.getD (i - 1) 0 >>> 63)

/-- Compare the low `k` limbs of `x` with the low `k` limbs of `2 y`, most significant first. -/
def cmpDouble.go (x y : Array UInt64) : Nat → Ordering
  | 0 => .eq
  | i + 1 =>
    match Ord.compare (x.getD i 0) (doubleLimb y i) with
    | .eq => cmpDouble.go x y i
    | o => o

/-- **Compare `x` with `2 y`** without computing `2 y`. -/
def cmpDouble (x y : AzNat) : Ordering :=
  cmpDouble.go x.limbs y.limbs (max x.limbs.size (y.limbs.size + 1))

end Azurite.AzNat
