/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Div.Classic
import Azurite.AzNat.Div.Newton

/-!
## Division: the dispatcher

`divModWith threshold U V` chooses between the classical dispatcher (`divModClassic`: one- and
two-limb divisors, schoolbook, and the divide-and-conquer division of MCA Algorithm 1.8) and
Newton–Barrett division (`divModNewton`: an approximate reciprocal of the divisor by Newton's
iteration, MCA Algorithm 3.5, then Barrett's quotient step, MCA Algorithm 2.5, block by block),
which is asymptotically faster — `O(M(n))` instead of `O(M(n) log n)` — and pays off in the
FFT range.  `divWith`/`modWith` are the quotient-only and remainder-only variants, and
`divMod`/`div`/`mod` fix the default threshold.
-/

namespace Azurite.AzNat

/-- Divisor limb count from which Newton–Barrett division is considered.  Measured 2026-10-19
(`az_nat_div_newton`, exact sizes, µs per division, Newton as % of the classical path): with a
2× dividend Newton is slower at every size (212 % at 1024 limbs, 149 % at 8192, 116 % at 32768,
107 % at 65536); the gain comes from amortizing the reciprocal over the blocks of a long
dividend: 8192 limbs ×5 94 %, ×8 86 %; 16384 ×4 82 %, ×6 72 %; 32768 ×3 87 %; 4096 ×12 only
94 %.  Cost model at these sizes: one Barrett block ≈ 0.8 and the reciprocal ≈ 0.7 of a
classical `2n/n` division (full products; the wrap-around trick and cached transforms of MCA
§2.4.1/§3.4.1 would cut the block cost to ≈ M(n)). -/
def divNewtonThreshold : Nat := 8192

/-- Quotient limbs (dividend minus divisor limbs) from which the Newton path is taken, together
with `divNewtonThreshold` and a quotient of at least twice the divisor.  Measured as above. -/
def divNewtonQuotientLimbs : Nat := 49152

/-- Below this many limbs the approximate reciprocal is computed exactly by the classical
division (`reciprocalBase`).  128 and 512 were indistinguishable (the top levels of the
recursion dominate). -/
def reciprocalBaseThreshold : Nat := 512

/-- Newton–Barrett division is used for divisors of at least `divNewtonThreshold` limbs when the
quotient has at least `divNewtonQuotientLimbs` limbs and at least twice the divisor's. -/
def useNewtonDiv (U V : AzNat) : Bool :=
  divNewtonThreshold ≤ V.limbs.size &&
    V.limbs.size + divNewtonQuotientLimbs ≤ U.limbs.size &&
    3 * V.limbs.size ≤ U.limbs.size

/-- Divide `U` by `V`, returning `(quotient, remainder)`; `divModWith t U 0 = (0, U)`. -/
def divModWith (threshold : Nat) (U V : AzNat) : AzNat × AzNat :=
  if useNewtonDiv U V then divModNewton reciprocalBaseThreshold U V
  else divModClassic threshold U V

/-- The quotient only. -/
def divWith (threshold : Nat) (U V : AzNat) : AzNat :=
  if useNewtonDiv U V then (divModNewton reciprocalBaseThreshold U V).1
  else divClassic threshold U V

/-- The remainder only. -/
def modWith (threshold : Nat) (U V : AzNat) : AzNat :=
  if useNewtonDiv U V then (divModNewton reciprocalBaseThreshold U V).2
  else modClassic threshold U V

/-- `divModWith` at the default threshold. -/
def divMod (U V : AzNat) : AzNat × AzNat := divModWith divDispatchThreshold U V

/-- `divWith` at the default threshold. -/
def div (U V : AzNat) : AzNat := divWith divDispatchThreshold U V

/-- `modWith` at the default threshold. -/
def mod (U V : AzNat) : AzNat := modWith divDispatchThreshold U V

instance : Div AzNat := ⟨div⟩
instance : Mod AzNat := ⟨mod⟩

end Azurite.AzNat
