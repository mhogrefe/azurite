/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LnBracket
import Azurite.AzFloat.Interval

/-!
## The logarithm of an enclosure

`lnOfEncl [lo, hi] w` encloses `ln v` for every `v ∈ [lo, hi]` with one evaluation of the
logarithm: `ln lo` by `lnBracket`, and `ln hi ≤ ln lo + (hi − lo)/lo`.  Used where the argument
of a logarithm is itself only known through an enclosure (the inverse Gudermannian, `ln Γ`).
The proofs are in `Azurite/AzFloat/Equiv/LnEncl.lean`.
-/

namespace Azurite.AzFloat

/-- The logarithm of an enclosure `[lo, hi]` with a positive lower end, at Ziv level `w`:
`lnBracket` at `lo`, the upper end raised by `⌈(hi − lo)/lo⌉`; the dummy bracket `[−1, 1]` when
`lo` is not a positive float. -/
def lnOfEncl (y : Encl) (w : Nat) : Encl :=
  match y.1 with
  | finite true e q m hv =>
    let L := lnBracket (finite true e q m hv) e w
    let d := (divPrecRound (subPrecRound y.2 (finite true e q m hv) w .Ceiling).1
      (finite true e q m hv) w .Ceiling).1
    (L.1, (addPrecRound L.2 d w .Ceiling).1)
  | _ => (-one, one)

end Azurite.AzFloat
