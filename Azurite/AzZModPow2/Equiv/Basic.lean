import Azurite.AzZModPow2.Basic
import Mathlib.Data.ZMod.Basic

/-!
## `AzZModPow2 k ≃ ZMod (2^k)`

The bridge to Mathlib: `toZMod` sends the canonical residue to `ZMod (2^k)`, and
`equivZMod` packages it as a bijection (the ring-isomorphism structure will follow
once the masking-based ring operations are in place).
-/

namespace Azurite.AzZModPow2

variable {k : Nat}

instance instNeZeroTwoPow : NeZero ((2 : ℕ) ^ k) := ⟨by positivity⟩

/-- The canonical residue of `a` as an element of `ZMod (2^k)`. -/
def toZMod (a : AzZModPow2 k) : ZMod (2 ^ k) := (a.val.toNat : ZMod (2 ^ k))

/-- Reduce an element of `ZMod (2^k)` to its canonical `AzZModPow2 k` residue. -/
def ofZMod (z : ZMod (2 ^ k)) : AzZModPow2 k := ofAzNat k (AzNat.ofNat z.val)

@[simp] theorem toZMod_ofAzNat (n : AzNat) :
    toZMod (ofAzNat k n) = (n.toNat : ZMod (2 ^ k)) := by
  show (((n.modPow2 k).toNat : ℕ) : ZMod (2 ^ k)) = (n.toNat : ZMod (2 ^ k))
  rw [AzNat.toNat_modPow2, ZMod.natCast_mod]

@[simp] theorem toZMod_zero : toZMod (0 : AzZModPow2 k) = 0 := by
  show ((0 : AzNat).toNat : ZMod (2 ^ k)) = 0
  rw [AzNat.toNat_zero, Nat.cast_zero]

@[simp] theorem toZMod_one : toZMod (1 : AzZModPow2 k) = 1 := by
  show toZMod (ofAzNat k 1) = 1
  rw [toZMod_ofAzNat]
  show ((1 : AzNat).toNat : ZMod (2 ^ k)) = 1
  rw [AzNat.toNat_one, Nat.cast_one]

theorem toZMod_ofZMod (z : ZMod (2 ^ k)) : toZMod (ofZMod z) = z := by
  rw [ofZMod, toZMod_ofAzNat, AzNat.toNat_ofNat, ZMod.natCast_zmod_val]

theorem ofZMod_toZMod (a : AzZModPow2 k) : ofZMod (toZMod a) = a := by
  have hv : (toZMod a).val = a.val.toNat := by
    show ((a.val.toNat : ZMod (2 ^ k)).val) = a.val.toNat
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt a.isLt]
  apply ext
  apply AzNat.toNat_injective
  show ((AzNat.ofNat (toZMod a).val).modPow2 k).toNat = a.val.toNat
  rw [AzNat.toNat_modPow2, AzNat.toNat_ofNat, hv, Nat.mod_eq_of_lt a.isLt]

/-- **`AzZModPow2 k` is equivalent to `ZMod (2^k)`.**  The ring-isomorphism upgrade
awaits the masking-based ring operations. -/
def equivZMod : AzZModPow2 k ≃ ZMod (2 ^ k) where
  toFun := toZMod
  invFun := ofZMod
  left_inv := ofZMod_toZMod
  right_inv := toZMod_ofZMod

@[simp] theorem equivZMod_apply (a : AzZModPow2 k) : equivZMod a = toZMod a := rfl
@[simp] theorem equivZMod_symm_apply (z : ZMod (2 ^ k)) : equivZMod.symm z = ofZMod z := rfl

theorem toZMod_injective : Function.Injective (toZMod (k := k)) := equivZMod.injective

end Azurite.AzZModPow2
