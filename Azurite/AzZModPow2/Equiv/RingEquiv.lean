import Azurite.AzZModPow2.Instances
import Mathlib.Algebra.Ring.Equiv

/-!
# Bundled ring equivalence `AzZModPow2 k ≃+* ZMod (2^k)`

`toZMod`/`ofZMod` upgraded from the bare bijection `equivZMod` to a `RingEquiv`,
so Mathlib's generic `map_*` lemmas (`map_add`, `map_mul`, `map_pow`, `map_neg`,
`map_natCast`, …) apply to `toZMod` directly.  The component homomorphism facts
(`toZMod_add`, `toZMod_mul`) are proven in the sibling `Equiv` files and the
`CommRing` structure in `Instances`; this file only packages them.
-/

namespace Azurite.AzZModPow2

variable {k : Nat}

/-- `toZMod` bundled as a ring equivalence `AzZModPow2 k ≃+* ZMod (2^k)`. -/
def ringEquivZMod : AzZModPow2 k ≃+* ZMod (2 ^ k) :=
  { equivZMod with
    map_add' := toZMod_add
    map_mul' := toZMod_mul }

@[simp] theorem ringEquivZMod_apply (a : AzZModPow2 k) : ringEquivZMod a = toZMod a := rfl

@[simp] theorem ringEquivZMod_symm_apply (z : ZMod (2 ^ k)) : ringEquivZMod.symm z = ofZMod z := rfl

/-- `toZMod` bundled as a ring homomorphism `AzZModPow2 k →+* ZMod (2^k)`. -/
def toZModRingHom : AzZModPow2 k →+* ZMod (2 ^ k) := ringEquivZMod.toRingHom

@[simp] theorem toZModRingHom_apply (a : AzZModPow2 k) : toZModRingHom a = toZMod a := rfl

end Azurite.AzZModPow2
