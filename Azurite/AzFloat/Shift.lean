/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Basic
import Azurite.AzInt.Conversion
import Azurite.AzInt.Equiv.Basic
import Azurite.AzInt.Sub

/-!
# Shifting an `AzFloat`

Multiplying by `2^k` only moves the exponent, and with an unbounded exponent this is always
exact: no rounding, no change of precision, and the special values are fixed.  `shiftLeft x k`
multiplies by `2^k` for `k : AzInt`; `shiftRight x k` divides.  The `<<<`/`>>>` notations take
an `AzInt` or a `Nat`.  `Equiv/Shift.lean` proves `toVal_shiftLeft` and that the shift is the
exact lift of `v ↦ v · 2^k` at the float's own precision.
-/

namespace Azurite.AzFloat

/-- `x · 2^k`, exactly. -/
def shiftLeft (x : AzFloat) (k : AzInt) : AzFloat :=
  match x with
  | finite s e p m h => finite s (e + k) p m h
  | x => x

/-- `x / 2^k`, exactly. -/
def shiftRight (x : AzFloat) (k : AzInt) : AzFloat := shiftLeft x (-k)

instance : HShiftLeft AzFloat AzInt AzFloat := ⟨shiftLeft⟩
instance : HShiftRight AzFloat AzInt AzFloat := ⟨shiftRight⟩
instance : HShiftLeft AzFloat Nat AzFloat := ⟨fun x k => shiftLeft x (AzNat.ofNat k).toAzInt⟩
instance : HShiftRight AzFloat Nat AzFloat := ⟨fun x k => shiftRight x (AzNat.ofNat k).toAzInt⟩

end Azurite.AzFloat
