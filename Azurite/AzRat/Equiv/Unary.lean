import Azurite.AzRat.Unary
import Azurite.AzRat.Equiv.Basic
import Azurite.AzRat.Equiv.Construct
import Mathlib.Algebra.Order.Field.Basic

/-!
# Correctness of the `AzRat` unary operations

The three operations agree with their `ℚ` counterparts, in both directions:

* `toRat_neg` / `toRat_abs` / `toRat_inv`: `toRat` commutes with the operation;
* `ofRat_neg` / `ofRat_abs` / `ofRat_inv`: so does `ofRat` (by `toRat_injective`).

The `toRat` proofs work in the `Rat.divInt` normal form (`toRat_eq_divInt`) where the
core lemmas `Rat.neg_divInt` / `Rat.inv_divInt` / `Rat.divInt_nonneg` apply directly.
-/

namespace Azurite.AzRat

/-- `toRat` in `divInt` normal form. -/
private lemma toRat_eq_divInt (q : AzRat) :
    toRat q = Rat.divInt
      (if q.sign then (q.num.toNat : ℤ) else -(q.num.toNat : ℤ)) (q.den.toNat : ℤ) := by
  rw [toRat, Rat.mk_eq_divInt]

private lemma toRat_of_num_zero (q : AzRat) (h : q.num = 0) : toRat q = 0 := by
  rw [toRat_eq_divInt, q.zero_sign h, if_pos rfl, h, AzNat.toNat_zero]
  simp

@[simp] theorem toRat_neg (q : AzRat) : toRat (-q) = -(toRat q) := by
  show toRat q.neg = -(toRat q)
  by_cases hn : q.num = 0
  · rw [toRat_of_num_zero q hn, toRat_of_num_zero q.neg hn, neg_zero]
  · rw [toRat_eq_divInt q.neg, toRat_eq_divInt q]
    simp only [neg]
    rw [if_neg hn, Rat.neg_divInt]
    cases q.sign <;> simp

@[simp] theorem toRat_abs (q : AzRat) : toRat q.abs = |toRat q| := by
  have habs : toRat q.abs = Rat.divInt (q.num.toNat : ℤ) (q.den.toNat : ℤ) := by
    rw [toRat_eq_divInt]
    simp only [abs]
    rw [if_pos trivial]
  have hnn : (0 : ℚ) ≤ Rat.divInt (q.num.toNat : ℤ) (q.den.toNat : ℤ) :=
    Rat.divInt_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  by_cases hs : q.sign
  · rw [habs, toRat_eq_divInt, if_pos hs, abs_of_nonneg hnn]
  · rw [habs, toRat_eq_divInt, if_neg hs, ← Rat.neg_divInt, abs_neg, abs_of_nonneg hnn]

@[simp] theorem toRat_inv (q : AzRat) : toRat q⁻¹ = (toRat q)⁻¹ := by
  show toRat q.inv = (toRat q)⁻¹
  by_cases hn : q.num = 0
  · rw [inv, dif_pos hn, toRat_zero, toRat_of_num_zero q hn, inv_zero]
  · rw [inv, dif_neg hn, toRat_eq_divInt, toRat_eq_divInt q]
    dsimp only
    cases hs : q.sign with
    | true => rw [if_pos rfl, if_pos rfl, Rat.inv_divInt]
    | false =>
      rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true,
          ← Rat.neg_divInt, ← Rat.neg_divInt, inv_neg, Rat.inv_divInt]

@[simp] theorem ofRat_neg (r : ℚ) : ofRat (-r) = -(ofRat r) :=
  toRat_injective (by rw [toRat_ofRat, toRat_neg, toRat_ofRat])

@[simp] theorem ofRat_abs (r : ℚ) : ofRat |r| = (ofRat r).abs :=
  toRat_injective (by rw [toRat_ofRat, toRat_abs, toRat_ofRat])

@[simp] theorem ofRat_inv (r : ℚ) : ofRat r⁻¹ = (ofRat r)⁻¹ :=
  toRat_injective (by rw [toRat_ofRat, toRat_inv, toRat_ofRat])

end Azurite.AzRat
