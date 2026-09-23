/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzZMod.Instances
import Mathlib.Algebra.Ring.Equiv

/-!
# Bundled ring equivalence `AzZMod m ≃+* ZMod m.toNat`

`toZMod`/`ofZMod` upgraded from the bare bijection `equivZMod` to a `RingEquiv`,
so Mathlib's generic `map_*` lemmas (`map_add`, `map_mul`, `map_pow`, `map_neg`,
`map_natCast`, …) apply to `toZMod` directly.  The component homomorphism facts
(`toZMod_add`, `toZMod_mul`) are proven in the sibling `Equiv` files and the
`CommRing` structure in `Instances`; this file only packages them.  Mirrors
`AzZModPow2/Equiv/RingEquiv.lean`, with `NeZero m.toNat` an explicit hypothesis.
-/

namespace Azurite.AzZMod

variable {m : AzNat}

/-- `toZMod` bundled as a ring equivalence `AzZMod m ≃+* ZMod m.toNat`. -/
def ringEquivZMod [NeZero m.toNat] : AzZMod m ≃+* ZMod m.toNat :=
  { equivZMod with
    map_add' := toZMod_add
    map_mul' := toZMod_mul }

@[simp] theorem ringEquivZMod_apply [NeZero m.toNat] (a : AzZMod m) :
    ringEquivZMod a = toZMod a := rfl

@[simp] theorem ringEquivZMod_symm_apply [NeZero m.toNat] (z : ZMod m.toNat) :
    ringEquivZMod.symm z = ofZMod z := rfl

/-- `toZMod` bundled as a ring homomorphism `AzZMod m →+* ZMod m.toNat`. -/
def toZModRingHom [NeZero m.toNat] : AzZMod m →+* ZMod m.toNat := ringEquivZMod.toRingHom

@[simp] theorem toZModRingHom_apply [NeZero m.toNat] (a : AzZMod m) :
    toZModRingHom a = toZMod a := rfl

end Azurite.AzZMod
