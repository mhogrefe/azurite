/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzRat.Compare
import Azurite.AzRat.Unary
import Azurite.AzRat.Equiv.Compare
import Azurite.AzRat.Equiv.Unary

/-!
# The linear order on `AzRat`

`AzRat`'s `≤`/`<` are decided by the staged limb-level comparison `cmp`
(`Azurite/AzRat/Compare.lean`); here the order laws are transferred from `ℚ`
through `cmp_eq_compare`, giving the `LinearOrder AzRat` instance — with
`compare := cmp`, so Mathlib's `compare` on `AzRat` *is* the fast comparison.
Mirrors the `AzInt` construction.

Also provides the bundled `orderIsoRat : AzRat ≃o ℚ` and the order-level
descriptions of the operations defined so far: `toRat_max`/`toRat_min`, and
`abs_eq_max_neg` (through which `abs_eq` in `Azurite/AzRat/Instances.lean`
identifies `AzRat.abs` with the lattice absolute value `|·|`).
-/

namespace Azurite.AzRat

lemma le_iff_toRat_le (q r : AzRat) : q ≤ r ↔ toRat q ≤ toRat r := by
  change cmp q r ≠ Ordering.gt ↔ toRat q ≤ toRat r
  rw [cmp_eq_compare]
  exact compare_le_iff_le

lemma lt_iff_toRat_lt (q r : AzRat) : q < r ↔ toRat q < toRat r := by
  change cmp q r = Ordering.lt ↔ toRat q < toRat r
  rw [cmp_eq_compare]
  exact compare_lt_iff_lt

lemma le_refl (q : AzRat) : q ≤ q := by
  rw [le_iff_toRat_le]

lemma le_trans (q r s : AzRat) (h1 : q ≤ r) (h2 : r ≤ s) : q ≤ s := by
  rw [le_iff_toRat_le] at *
  exact _root_.le_trans h1 h2

lemma le_antisymm (q r : AzRat) (h1 : q ≤ r) (h2 : r ≤ q) : q = r := by
  rw [le_iff_toRat_le] at *
  exact toRat_injective (_root_.le_antisymm h1 h2)

lemma le_total (q r : AzRat) : q ≤ r ∨ r ≤ q := by
  rw [le_iff_toRat_le, le_iff_toRat_le]
  exact _root_.le_total (toRat q) (toRat r)

lemma lt_iff_le_not_ge (q r : AzRat) : q < r ↔ q ≤ r ∧ ¬ r ≤ q := by
  rw [lt_iff_toRat_lt, le_iff_toRat_le, le_iff_toRat_le]
  exact _root_.lt_iff_le_not_ge

lemma compare_eq_compareOfLessAndEq (q r : AzRat) :
    cmp q r = compareOfLessAndEq q r := by
  change cmp q r = (if q < r then Ordering.lt else if q = r then Ordering.eq else Ordering.gt)
  rw [cmp_eq_compare]
  rcases lt_trichotomy (toRat q) (toRat r) with h | h | h
  · rw [ite_eq_left ((lt_iff_toRat_lt q r).mpr h)]
    exact compare_lt_iff_lt.mpr h
  · rw [ite_eq_right (by rw [lt_iff_toRat_lt, h]; exact lt_irrefl _),
        ite_eq_left (toRat_injective h)]
    exact compare_eq_iff_eq.mpr h
  · rw [ite_eq_right (by rw [lt_iff_toRat_lt]; exact not_lt_of_gt h),
        ite_eq_right (fun he => absurd (congrArg toRat he) (by simpa using ne_of_gt h))]
    exact compare_gt_iff_gt.mpr h

/-- The verified linear order on `AzRat`: `≤`, `<`, `min`, `max`, and
`compare` are all decided by the staged limb-level `cmp`, with the order
laws transferred from `ℚ`. -/
instance instLinearOrderAzRat : LinearOrder AzRat where
  le_refl := le_refl
  le_trans := le_trans
  lt_iff_le_not_ge := lt_iff_le_not_ge
  le_antisymm := le_antisymm
  le_total := le_total
  toDecidableLE := inferInstance
  toDecidableEq := inferInstance
  toDecidableLT := inferInstance
  min_def := fun _ _ => rfl
  max_def := fun _ _ => rfl
  compare := cmp
  compare_eq_compareOfLessAndEq := compare_eq_compareOfLessAndEq

/-- `toRat` bundled as an order isomorphism `AzRat ≃o ℚ` (mirroring
`orderIsoNat : AzNat ≃o ℕ` and `orderIsoInt : AzInt ≃o ℤ`). -/
def orderIsoRat : AzRat ≃o ℚ :=
  { equivRat with
    map_rel_iff' := fun {q r} => (le_iff_toRat_le q r).symm }

@[simp] theorem orderIsoRat_apply (q : AzRat) : orderIsoRat q = toRat q := rfl

@[simp] theorem orderIsoRat_symm_apply (r : ℚ) : orderIsoRat.symm r = ofRat r := rfl

@[simp] theorem toRat_max (q r : AzRat) :
    toRat (max q r) = max (toRat q) (toRat r) :=
  orderIsoRat.monotone.map_max

@[simp] theorem toRat_min (q r : AzRat) :
    toRat (min q r) = min (toRat q) (toRat r) :=
  orderIsoRat.monotone.map_min

/-- `AzRat.abs` is the order-theoretic absolute value, `max q (-q)` — the
defining equation of Mathlib's `|·|`. (The `|·|` notation itself requires an
`AddGroup`, which `AzRat` acquires in `Azurite/AzRat/Instances.lean`; the
lemma `abs_eq` there uses this equation to prove `|q| = q.abs`.) -/
theorem abs_eq_max_neg (q : AzRat) : q.abs = max q (-q) := by
  apply toRat_injective
  rw [toRat_abs, toRat_max, toRat_neg]
  exact _root_.abs_eq_max_neg

end Azurite.AzRat

namespace Azurite

-- The order computes (string-anchored via `AzRat.parse`/`AzRat.toString`).

#guard ((fun a b => decide (a < b)) <$> AzRat.parse "1/3" <*> AzRat.parse "1/2") == some true
#guard ((fun a b => decide (a ≤ b)) <$> AzRat.parse "-1/2" <*> AzRat.parse "-2/3") == some false
#guard ((fun a b => decide (a ≤ b)) <$> AzRat.parse "2/4" <*> AzRat.parse "1/2") == some true
#guard ((fun a b => AzRat.toString (max a b)) <$> AzRat.parse "2/3" <*> AzRat.parse "3/4") == some "3/4"
#guard ((fun a b => AzRat.toString (min a b)) <$> AzRat.parse "-2/3" <*> AzRat.parse "-3/4") == some "-3/4"

end Azurite
