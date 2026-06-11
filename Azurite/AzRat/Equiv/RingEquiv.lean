import Azurite.AzRat.Instances
import Mathlib.Algebra.Order.Hom.Ring
import Mathlib.Algebra.Ring.Equiv

/-!
# Bundled ring equivalence between `AzRat` and `ℚ`

`toRat`/`ofRat` upgraded from the bare bijection `equivRat : AzRat ≃ ℚ` to

* `ringEquivRat : AzRat ≃+* ℚ` — a `RingEquiv`, so Mathlib's generic
  `map_*` lemmas (`map_add`, `map_mul`, `map_neg`, `map_sub`, `map_pow`,
  and — since both sides are fields — `map_inv₀`, `map_div₀`, …) apply to
  `toRat` directly;
* `toRatRingHom : AzRat →+* ℚ` — the underlying ring homomorphism;
* `orderRingIsoRat : AzRat ≃+*o ℚ` — an `OrderRingIso`, merging the ring
  equivalence with the order isomorphism `orderIsoRat : AzRat ≃o ℚ`
  (`Azurite/AzRat/Equiv/Order.lean`) in one package.

There is no separate "field equivalence" to bundle: a field's `⁻¹` and `/`
are determined by its ring structure, so a `RingEquiv` between fields
already preserves them (via `map_inv₀`/`map_div₀`); the ordered-ring
isomorphism is the strongest bundled form. This file packages the ring
side (mirroring `ringEquivNat` and `ringEquivInt`). The component facts
(`toRat_add`, `toRat_mul`, …) are proven in the sibling `Equiv` files.
-/

namespace Azurite.AzRat

/-- `toRat` bundled as a ring equivalence `AzRat ≃+* ℚ`. -/
def ringEquivRat : AzRat ≃+* ℚ :=
  { equivRat with
    map_add' := toRat_add
    map_mul' := toRat_mul }

@[simp] theorem ringEquivRat_apply (q : AzRat) : ringEquivRat q = q.toRat := rfl

@[simp] theorem ringEquivRat_symm_apply (r : ℚ) : ringEquivRat.symm r = ofRat r := rfl

/-- `toRat` bundled as a ring homomorphism `AzRat →+* ℚ`. -/
def toRatRingHom : AzRat →+* ℚ := ringEquivRat.toRingHom

@[simp] theorem toRatRingHom_apply (q : AzRat) : toRatRingHom q = q.toRat := rfl

/-- `toRat` bundled as an ordered-ring isomorphism `AzRat ≃+*o ℚ` —
`ringEquivRat` and `orderIsoRat` in a single package, the strongest bundled
form available for a linearly ordered field. -/
def orderRingIsoRat : AzRat ≃+*o ℚ :=
  { ringEquivRat with
    map_le_map_iff' := fun {a b} => (le_iff_toRat_le a b).symm }

@[simp] theorem orderRingIsoRat_apply (q : AzRat) : orderRingIsoRat q = q.toRat := rfl

@[simp] theorem orderRingIsoRat_symm_apply (r : ℚ) :
    (orderRingIsoRat.symm : ℚ ≃+*o AzRat) r = ofRat r := rfl

end Azurite.AzRat
