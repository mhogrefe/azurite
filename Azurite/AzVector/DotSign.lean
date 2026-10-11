/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzVector.Dot
import Azurite.AzNat.Basic
import Azurite.AzNat.Conversion
import Azurite.AzNat.Add
import Azurite.AzNat.Mul

/-!
## The sign of a dot product

`AzNat.dotSign v w` is the sign of `v ⬝ w` for two vectors of natural numbers, as the ordering
of the dot product against `0`: `.gt` when some coordinate is nonzero in both vectors, `.eq`
otherwise.  Every term `vᵢ wᵢ` is nonnegative, so the sign needs no multiplication and no
addition — one pass over the coordinates testing for zero.  (The signed and rational versions,
where terms of both signs may cancel, are the point of `compareProduct`/`compareProducts`.)

Correctness: `Equiv/DotSign.lean` (`dotSign_eq`, `dotSign_eq_compare_dot`).
-/

namespace Azurite.AzNat

open Azurite (AzVector)

variable {n : Nat}

/-- **The sign of `v ⬝ w`** for natural vectors, as its ordering against `0`. -/
def dotSign (v w : AzVector AzNat n) : Ordering :=
  if (v.zip (fun a b => decide (a ≠ 0) && decide (b ≠ 0)) w).data.any id then .gt else .eq

end Azurite.AzNat

/-! ### Tests -/

section Tests

open Azurite Azurite.AzNat

private def V (l : List Nat) (h : l.length = n := by decide) : AzVector AzNat n :=
  AzVector.ofList (l.map ofNat) (by simpa using h)

#guard dotSign (V (n := 0) []) (V []) == .eq
#guard dotSign (V (n := 3) [0, 0, 0]) (V [1, 2, 3]) == .eq
#guard dotSign (V (n := 3) [1, 0, 3]) (V [0, 5, 0]) == .eq          -- disjoint supports
#guard dotSign (V (n := 3) [1, 0, 3]) (V [0, 5, 7]) == .gt
#guard dotSign (V (n := 4) [0, 0, 0, 2]) (V [0, 0, 0, 2]) == .gt
#guard dotSign (V (n := 2) [18446744073709551616, 0]) (V [0, 18446744073709551616]) == .eq
#guard dotSign (V (n := 2) [18446744073709551616, 0]) (V [1, 18446744073709551616]) == .gt
-- agreement with the dot product
#guard
  let vs : List (AzVector AzNat 3) :=
    [V [0, 0, 0], V [1, 0, 0], V [0, 2, 0], V [0, 0, 3], V [1, 1, 0], V [5, 0, 7], V [1, 2, 3]]
  vs.all fun v => vs.all fun w =>
    dotSign v w == (if v.dot w = 0 then Ordering.eq else Ordering.gt)

end Tests
