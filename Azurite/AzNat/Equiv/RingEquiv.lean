/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Equiv.Add
import Azurite.AzNat.Equiv.Compare
import Azurite.AzNat.Equiv.Mul.ToomCook3
import Azurite.AzNat.Instances
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Order.Hom.Basic

/-!
# Bundled equivalences between `AzNat` and `ℕ`

`toNat`/`ofNat` upgraded from the bare bijection `equivNat : AzNat ≃ ℕ` to

* `ringEquivNat : AzNat ≃+* ℕ` — a `RingEquiv`, so Mathlib's generic
  `map_*` lemmas (`map_add`, `map_mul`, `map_pow`, `map_sum`, …) apply to
  `toNat` directly;
* `toNatRingHom : AzNat →+* ℕ` — the underlying ring homomorphism;
* `orderIsoNat : AzNat ≃o ℕ` — an `OrderIso`, giving monotonicity and
  order-reflection of `toNat` for free.

The component facts (`toNat_add`, `toNat_mul`, `le_iff_toNat_le`, …) are
proven in the sibling `Equiv` files; this file only packages them.
-/

namespace Azurite.AzNat

/-- `toNat` bundled as a ring equivalence `AzNat ≃+* ℕ`. -/
def ringEquivNat : AzNat ≃+* Nat :=
  { equivNat with
    map_add' := toNat_add
    map_mul' := toNat_mul }

@[simp] theorem ringEquivNat_apply (a : AzNat) : ringEquivNat a = a.toNat := rfl

@[simp] theorem ringEquivNat_symm_apply (n : Nat) : ringEquivNat.symm n = ofNat n := rfl

/-- `toNat` bundled as a ring homomorphism `AzNat →+* ℕ`. -/
def toNatRingHom : AzNat →+* Nat := ringEquivNat.toRingHom

@[simp] theorem toNatRingHom_apply (a : AzNat) : toNatRingHom a = a.toNat := rfl

/-- `toNat` bundled as an order isomorphism `AzNat ≃o ℕ`. -/
def orderIsoNat : AzNat ≃o Nat :=
  { equivNat with
    map_rel_iff' := fun {a b} => (le_iff_toNat_le a b).symm }

@[simp] theorem orderIsoNat_apply (a : AzNat) : orderIsoNat a = a.toNat := rfl

@[simp] theorem orderIsoNat_symm_apply (n : Nat) : orderIsoNat.symm n = ofNat n := rfl

end Azurite.AzNat
