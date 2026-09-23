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

/-- **Negation agrees with `ZMod`.**  The truncating `m - a.val` realizes
negation in `ZMod m.toNat`. -/
@[simp] theorem toZMod_neg [NeZero m.toNat] (a : AzZMod m) : toZMod (-a) = -(toZMod a) := by
  show toZMod (neg a) = -(toZMod a)
  unfold neg
  by_cases h : a.val.limbs.size = 0
  · rw [dite_eq_left h]
    have hz : toZMod a = 0 := by
      show ((a.val.toNat : ℕ) : ZMod m.toNat) = 0
      rw [(AzNat.toNat_eq_zero_iff a.val).mpr h, Nat.cast_zero]
    rw [toZMod_zero, hz, neg_zero]
  · rw [dite_eq_right h]
    show ((m - a.val).toNat : ZMod m.toNat) = -(toZMod a)
    rw [AzNat.toNat_sub, Nat.cast_sub (le_of_lt a.isLt), ZMod.natCast_self, zero_sub]
    rfl

/-- `ofZMod`-phrased companion of `toZMod_neg`. -/
@[simp] theorem ofZMod_neg [NeZero m.toNat] (z : ZMod m.toNat) : ofZMod (-z) = -(ofZMod z) := by
  apply toZMod_injective
  rw [toZMod_ofZMod, toZMod_neg, toZMod_ofZMod]

/-- **Addition agrees with `ZMod`.**  The add-then-conditionally-subtract `add`
realizes addition in `ZMod m.toNat`. -/
@[simp] theorem toZMod_add [NeZero m.toNat] (a b : AzZMod m) :
    toZMod (a + b) = toZMod a + toZMod b := by
  show toZMod (add a b) = toZMod a + toZMod b
  have key : toZMod (add a b) = ((a.val.toNat + b.val.toNat : ℕ) : ZMod m.toNat) := by
    simp only [add]
    split
    · rename_i h
      have hms : m.toNat ≤ a.val.toNat + b.val.toNat := by
        have := (AzNat.le_iff_toNat_le m (a.val + b.val)).mp h
        rwa [AzNat.toNat_add] at this
      show (((a.val + b.val - m).toNat : ℕ) : ZMod m.toNat) = _
      rw [AzNat.toNat_sub, AzNat.toNat_add, Nat.cast_sub hms, ZMod.natCast_self, sub_zero]
    · show (((a.val + b.val).toNat : ℕ) : ZMod m.toNat) = _
      rw [AzNat.toNat_add]
  rw [key, Nat.cast_add]
  rfl

/-- `ofZMod`-phrased companion of `toZMod_add`. -/
@[simp] theorem ofZMod_add [NeZero m.toNat] (x y : ZMod m.toNat) :
    ofZMod (x + y) = ofZMod x + ofZMod y := by
  apply toZMod_injective
  rw [toZMod_add, toZMod_ofZMod, toZMod_ofZMod, toZMod_ofZMod]

/-- **Subtraction agrees with `ZMod`.**  The borrow-or-add-`m` `sub` realizes
subtraction in `ZMod m.toNat`. -/
@[simp] theorem toZMod_sub [NeZero m.toNat] (a b : AzZMod m) :
    toZMod (a - b) = toZMod a - toZMod b := by
  show toZMod (sub a b) = toZMod a - toZMod b
  have key : toZMod (sub a b) = (a.val.toNat : ZMod m.toNat) - (b.val.toNat : ZMod m.toNat) := by
    simp only [sub]
    split
    · rename_i h
      have hba : b.val.toNat ≤ a.val.toNat := (AzNat.le_iff_toNat_le b.val a.val).mp h
      show (((a.val - b.val).toNat : ℕ) : ZMod m.toNat) = _
      rw [AzNat.toNat_sub, Nat.cast_sub hba]
    · rename_i h
      have hbam : b.val.toNat ≤ a.val.toNat + m.toNat := by
        have hb : b.val.toNat < m.toNat := b.isLt
        omega
      show (((a.val + m - b.val).toNat : ℕ) : ZMod m.toNat) = _
      rw [AzNat.toNat_sub, AzNat.toNat_add, Nat.cast_sub hbam, Nat.cast_add, ZMod.natCast_self,
        add_zero]
  rw [key]
  rfl

/-- `ofZMod`-phrased companion of `toZMod_sub`. -/
@[simp] theorem ofZMod_sub [NeZero m.toNat] (x y : ZMod m.toNat) :
    ofZMod (x - y) = ofZMod x - ofZMod y := by
  apply toZMod_injective
  rw [toZMod_sub, toZMod_ofZMod, toZMod_ofZMod, toZMod_ofZMod]

/-- **Multiplication agrees with `ZMod`.**  The reduce-the-product `mul` realizes
multiplication in `ZMod m.toNat`. -/
@[simp] theorem toZMod_mul [NeZero m.toNat] (a b : AzZMod m) :
    toZMod (a * b) = toZMod a * toZMod b := by
  show toZMod (ofAzNat m (a.val * b.val)) = toZMod a * toZMod b
  rw [toZMod_ofAzNat, AzNat.toNat_mul, Nat.cast_mul]
  rfl

/-- `ofZMod`-phrased companion of `toZMod_mul`. -/
@[simp] theorem ofZMod_mul [NeZero m.toNat] (x y : ZMod m.toNat) :
    ofZMod (x * y) = ofZMod x * ofZMod y := by
  apply toZMod_injective
  rw [toZMod_mul, toZMod_ofZMod, toZMod_ofZMod, toZMod_ofZMod]

/-- **Squaring agrees with `ZMod`.**  `Square.square` realizes squaring in
`ZMod m.toNat` (it equals `a * a`). -/
@[simp] theorem toZMod_square [NeZero m.toNat] (a : AzZMod m) :
    toZMod (Azurite.Square.square a) = toZMod a * toZMod a := by
  rw [Azurite.Square.square_eq, toZMod_mul]

end Azurite.AzZMod
