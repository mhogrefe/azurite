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

/-- Divisor limb count from which Newton–Barrett division is considered (with the FFT-range
tricks, see `useNewtonDiv`).  Measured 2026-10-19 with `az_nat_div_newton` (exact sizes, Newton
as % of the classical time; dividend = ratio × divisor): 4096 limbs ×2 157 %, ×4 89 %; 8192 ×2
118 %, ×3 82 %, ×8 56 %; 16384 ×2 96 %, ×3 66 %; 32768 ×2 83 %; 65536 ×2 75 %.  Without the FFT
tricks (full products everywhere) the figures were 8192 ×8 86 %, 16384 ×6 72 %, 32768 ×2 117 %.
Below the FFT range, Barrett's step with Mulders' short products (`shortProductBase`): 1024 ×8
91 %, 2048 ×8 90 %, 4096 ×8 86 %, ×4 100–107 %, ×2 147–154 % (full products: 4096 ×8 96 %,
×2 160 %). -/
def divNewtonThreshold : Nat := 1024

/-- Divisor limb count from which the Newton path uses the FFT-range tricks (wrap-around
product in the reciprocal, cached transforms and modular remainder in Barrett's step).
Measured 2026-10-19: 2048, 4096 and 8192 are indistinguishable at 8192–32768 divisor limbs (the
lower levels of the reciprocal recursion cost little), and forcing the tricks at every level
loses at 2048-limb divisors. -/
def newtonFFTThreshold : Nat := 4096

/-- Below this many limbs the approximate reciprocal is computed exactly by the classical
division (`reciprocalBase`).  128 and 512 were indistinguishable (the top levels of the
recursion dominate). -/
def reciprocalBaseThreshold : Nat := 512

/-- The base-case size of the short products in Barrett's step (`Mul/ShortProduct`): below this
many limbs the full product is truncated.  Measured 2026-10-19: 8 to 128 are indistinguishable
at 2048 and 4096 divisor limbs. -/
def shortProductBase : Nat := 32

/-- Newton–Barrett division is used when the quotient is long enough for the reciprocal to pay
off: divisor `≥ 32768` limbs and dividend `≥ 2×`, divisor `≥ 8192` and dividend `≥ 3×`, divisor
`≥ 4096` and dividend `≥ 4×`, or divisor `≥ 1024` and dividend `≥ 8×` (measurements under
`divNewtonThreshold`). -/
def useNewtonDiv (U V : AzNat) : Bool :=
  let n := V.limbs.size
  let m := U.limbs.size
  (32768 ≤ n && 2 * n ≤ m) || (8192 ≤ n && 3 * n ≤ m) || (4096 ≤ n && 4 * n ≤ m) ||
    (divNewtonThreshold ≤ n && 8 * n ≤ m)

/-- Divide `U` by `V`, returning `(quotient, remainder)`; `divModWith t U 0 = (0, U)`. -/
def divModWith (threshold : Nat) (U V : AzNat) : AzNat × AzNat :=
  if useNewtonDiv U V then divModNewton reciprocalBaseThreshold newtonFFTThreshold shortProductBase U V
  else divModClassic threshold U V

/-- The quotient only. -/
def divWith (threshold : Nat) (U V : AzNat) : AzNat :=
  if useNewtonDiv U V then (divModNewton reciprocalBaseThreshold newtonFFTThreshold shortProductBase U V).1
  else divClassic threshold U V

/-- The remainder only. -/
def modWith (threshold : Nat) (U V : AzNat) : AzNat :=
  if useNewtonDiv U V then (divModNewton reciprocalBaseThreshold newtonFFTThreshold shortProductBase U V).2
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
