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

/-- **Negation agrees with `ZMod`.**  The limb-level two's-complement `neg`
realizes negation in `ZMod (2^k)`. -/
@[simp] theorem toZMod_neg (a : AzZModPow2 k) : toZMod (-a) = -(toZMod a) := by
  show toZMod (neg a) = -(toZMod a)
  unfold neg
  by_cases h : a.val.limbs.size = 0
  · rw [dite_eq_left h]
    have hz : toZMod a = 0 := by
      show ((a.val.toNat : ℕ) : ZMod (2 ^ k)) = 0
      rw [(AzNat.toNat_eq_zero_iff a.val).mpr h, Nat.cast_zero]
    rw [toZMod_zero, hz, neg_zero]
  · rw [dite_eq_right h]
    show ((AzNat.lowMask k - a.val + 1).toNat : ZMod (2 ^ k)) = -(toZMod a)
    rw [AzNat.toNat_add, AzNat.toNat_one, AzNat.toNat_sub, AzNat.toNat_lowMask]
    have h2 : a.val.toNat ≤ 2 ^ k := le_of_lt a.isLt
    have hval : 2 ^ k - 1 - a.val.toNat + 1 = 2 ^ k - a.val.toNat := by
      have hlt : a.val.toNat < 2 ^ k := a.isLt
      omega
    rw [hval, Nat.cast_sub h2, ZMod.natCast_self, zero_sub]
    rfl

/-- `ofZMod`-phrased companion of `toZMod_neg`: reducing a negated
`ZMod (2^k)` element agrees with negating its residue. -/
@[simp] theorem ofZMod_neg (z : ZMod (2 ^ k)) : ofZMod (-z) = -(ofZMod z) := by
  apply toZMod_injective
  rw [toZMod_ofZMod, toZMod_neg, toZMod_ofZMod]

/-- **Addition agrees with `ZMod`.**  The wrapping `add` realizes addition in
`ZMod (2^k)`. -/
@[simp] theorem toZMod_add (a b : AzZModPow2 k) : toZMod (a + b) = toZMod a + toZMod b := by
  show (((AzNat.addModPow2 a.val b.val k).toNat : ℕ) : ZMod (2 ^ k)) = toZMod a + toZMod b
  rw [AzNat.toNat_addModPow2, ZMod.natCast_mod, Nat.cast_add]
  rfl

/-- `ofZMod`-phrased companion of `toZMod_add`. -/
@[simp] theorem ofZMod_add (x y : ZMod (2 ^ k)) : ofZMod (x + y) = ofZMod x + ofZMod y := by
  apply toZMod_injective
  rw [toZMod_add, toZMod_ofZMod, toZMod_ofZMod, toZMod_ofZMod]

/-- **Subtraction agrees with `ZMod`.**  The wrapping `sub` realizes subtraction
in `ZMod (2^k)`. -/
@[simp] theorem toZMod_sub (a b : AzZModPow2 k) : toZMod (a - b) = toZMod a - toZMod b := by
  show (((AzNat.subModPow2 a.val b.val k).toNat : ℕ) : ZMod (2 ^ k)) = toZMod a - toZMod b
  -- `(subModPow2 a b k).toNat + b.toNat ≡ a.toNat [MOD 2^k]`, cast to `ZMod`.
  have hmod := AzNat.subModPow2_modEq a.val b.val k
  have hcast : (((AzNat.subModPow2 a.val b.val k).toNat + b.val.toNat : ℕ) : ZMod (2 ^ k))
      = ((a.val.toNat : ℕ) : ZMod (2 ^ k)) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
  rw [Nat.cast_add] at hcast
  -- `toZMod a = (a.val.toNat : ZMod)`, `toZMod b = (b.val.toNat : ZMod)`.
  show (((AzNat.subModPow2 a.val b.val k).toNat : ℕ) : ZMod (2 ^ k))
      = ((a.val.toNat : ℕ) : ZMod (2 ^ k)) - ((b.val.toNat : ℕ) : ZMod (2 ^ k))
  rw [eq_sub_iff_add_eq, hcast]

/-- `ofZMod`-phrased companion of `toZMod_sub`. -/
@[simp] theorem ofZMod_sub (x y : ZMod (2 ^ k)) : ofZMod (x - y) = ofZMod x - ofZMod y := by
  apply toZMod_injective
  rw [toZMod_sub, toZMod_ofZMod, toZMod_ofZMod, toZMod_ofZMod]

/-- **Multiplication agrees with `ZMod`.**  The size-dispatched low product `mul`
realizes multiplication in `ZMod (2^k)`. -/
@[simp] theorem toZMod_mul (a b : AzZModPow2 k) : toZMod (a * b) = toZMod a * toZMod b := by
  show (((AzNat.mulDispatchModPow2 a.val b.val k).toNat : ℕ) : ZMod (2 ^ k)) = toZMod a * toZMod b
  rw [AzNat.toNat_mulDispatchModPow2, ZMod.natCast_mod, Nat.cast_mul]
  rfl

/-- `ofZMod`-phrased companion of `toZMod_mul`. -/
@[simp] theorem ofZMod_mul (x y : ZMod (2 ^ k)) : ofZMod (x * y) = ofZMod x * ofZMod y := by
  apply toZMod_injective
  rw [toZMod_mul, toZMod_ofZMod, toZMod_ofZMod, toZMod_ofZMod]

end Azurite.AzZModPow2
