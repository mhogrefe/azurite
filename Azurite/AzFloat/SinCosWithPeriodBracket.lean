/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.CosWithPeriodBracket
import Azurite.AzFloat.SinWithPeriodBracket

/-!
## The joint bracket of `sin (2πr)` and `cos (2πr)` for a rational `r ∈ [0, 1)`

`sinCosPeriodBracket r w` encloses `sin (2πr)` and `cos (2πr)` together at Ziv level `w`: one
evaluation of `sinCosBracket t 3 w` at the float `t = ⌊2 ⌊r⌋_W · lo⌋_W` of `sinPeriodBracket` and
`cosPeriodBracket`, both components widened by `2^(6−W)`.  Its components are
`sinPeriodBracket r w` and `cosPeriodBracket r w` (by `rfl`), so their specifications apply.
`sinCosPeriodApprox neg` is the pair of pairs of `Roundable`s for the joint Ziv loop
(`AzFloat/SinCosWithPeriod.lean`); its components are `sinPeriodApprox neg r w` and
`cosPeriodApprox r w`.
-/

namespace Azurite.AzFloat

/-- The joint bracket `([sin (2πr)], [cos (2πr)])` at Ziv level `w` for a rational
`r ∈ [0, 1)`. -/
def sinCosPeriodBracket (r : AzRat) (w : Nat) : Encl × Encl :=
  let W := cosWork (AzInt.ofInt 3) w
  let P := piBracket W
  let a := (ofAzRatRound r W .Floor).1
  let t := (mulPrecRound (a <<< AzInt.ofInt 1) P.1 W .Floor).1
  let E := one <<< AzInt.ofInt (6 - W)
  let b := sinCosBracket t (AzInt.ofInt 3) w
  (Encl.widen W b.1 (Encl.exact E), Encl.widen W b.2 (Encl.exact E))

theorem sinCosPeriodBracket_fst (r : AzRat) (w : Nat) :
    (sinCosPeriodBracket r w).1 = sinPeriodBracket r w := rfl

theorem sinCosPeriodBracket_snd (r : AzRat) (w : Nat) :
    (sinCosPeriodBracket r w).2 = cosPeriodBracket r w := rfl

/-- `sinCosPeriodBracket` as `Roundable`s for the joint Ziv loop: the bracket of
`± sin (2πr)` (negated and swapped for `neg`) and the bracket of `cos (2πr)`. -/
def sinCosPeriodApprox (neg : Bool) (r : AzRat) (w : Nat) :
    (Roundable × Roundable) × (Roundable × Roundable) :=
  let b := sinCosPeriodBracket r w
  (if neg then
      (fun p mode => setPrecRound (-b.1.2) p mode, fun p mode => setPrecRound (-b.1.1) p mode)
    else (fun p mode => setPrecRound b.1.1 p mode, fun p mode => setPrecRound b.1.2 p mode),
    (fun p mode => setPrecRound b.2.1 p mode, fun p mode => setPrecRound b.2.2 p mode))

theorem sinCosPeriodApprox_fst (neg : Bool) (r : AzRat) (w : Nat) :
    (sinCosPeriodApprox neg r w).1 = sinPeriodApprox neg r w := rfl

theorem sinCosPeriodApprox_snd (neg : Bool) (r : AzRat) (w : Nat) :
    (sinCosPeriodApprox neg r w).2 = cosPeriodApprox r w := rfl

end Azurite.AzFloat
