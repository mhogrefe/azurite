import Azurite.AzZMod.Basic
import Mathlib.Data.ZMod.Basic

/-!
## `AzZMod m ≃ ZMod m.toNat`

The bridge to Mathlib: `toZMod` sends the canonical residue to `ZMod m.toNat`, and
`equivZMod` packages it as a bijection (the ring-isomorphism structure will follow
once the division-based ring operations are in place).  Mirrors
`AzZModPow2/Equiv/Basic.lean`; the proofs are identical in shape, with the
`NeZero` of the modulus now an explicit hypothesis rather than `positivity`.
-/

namespace Azurite.AzZMod

variable {m : AzNat}

/-- The canonical residue of `a` as an element of `ZMod m.toNat`. -/
def toZMod (a : AzZMod m) : ZMod m.toNat := (a.val.toNat : ZMod m.toNat)

/-- Reduce an element of `ZMod m.toNat` to its canonical `AzZMod m` residue. -/
def ofZMod [NeZero m.toNat] (z : ZMod m.toNat) : AzZMod m := ofAzNat m (AzNat.ofNat z.val)

@[simp] theorem toZMod_ofAzNat [NeZero m.toNat] (n : AzNat) :
    toZMod (ofAzNat m n) = (n.toNat : ZMod m.toNat) := by
  show (((n % m).toNat : ℕ) : ZMod m.toNat) = (n.toNat : ZMod m.toNat)
  rw [AzNat.toNat_mod, ZMod.natCast_mod]

@[simp] theorem toZMod_zero [NeZero m.toNat] : toZMod (0 : AzZMod m) = 0 := by
  show ((0 : AzNat).toNat : ZMod m.toNat) = 0
  rw [AzNat.toNat_zero, Nat.cast_zero]

@[simp] theorem toZMod_one [NeZero m.toNat] : toZMod (1 : AzZMod m) = 1 := by
  show toZMod (ofAzNat m 1) = 1
  rw [toZMod_ofAzNat]
  show ((1 : AzNat).toNat : ZMod m.toNat) = 1
  rw [AzNat.toNat_one, Nat.cast_one]

theorem toZMod_ofZMod [NeZero m.toNat] (z : ZMod m.toNat) : toZMod (ofZMod z) = z := by
  rw [ofZMod, toZMod_ofAzNat, AzNat.toNat_ofNat, ZMod.natCast_zmod_val]

theorem ofZMod_toZMod [NeZero m.toNat] (a : AzZMod m) : ofZMod (toZMod a) = a := by
  have hv : (toZMod a).val = a.val.toNat := by
    show ((a.val.toNat : ZMod m.toNat).val) = a.val.toNat
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt a.isLt]
  apply ext
  apply AzNat.toNat_injective
  show ((AzNat.ofNat (toZMod a).val) % m).toNat = a.val.toNat
  rw [AzNat.toNat_mod, AzNat.toNat_ofNat, hv, Nat.mod_eq_of_lt a.isLt]

/-- **`AzZMod m` is equivalent to `ZMod m.toNat`.**  The ring-isomorphism upgrade
awaits the division-based ring operations. -/
def equivZMod [NeZero m.toNat] : AzZMod m ≃ ZMod m.toNat where
  toFun := toZMod
  invFun := ofZMod
  left_inv := ofZMod_toZMod
  right_inv := toZMod_ofZMod

@[simp] theorem equivZMod_apply [NeZero m.toNat] (a : AzZMod m) : equivZMod a = toZMod a := rfl
@[simp] theorem equivZMod_symm_apply [NeZero m.toNat] (z : ZMod m.toNat) :
    equivZMod.symm z = ofZMod z := rfl

theorem toZMod_injective [NeZero m.toNat] : Function.Injective (toZMod (m := m)) :=
  equivZMod.injective

end Azurite.AzZMod
