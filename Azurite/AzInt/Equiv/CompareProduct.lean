/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzInt.CompareProduct
import Azurite.AzInt.Equiv.Basic
import Azurite.AzNat.Equiv.CompareProduct

/-!
## Correctness of `AzInt.compareProduct`

`compareProduct_eq : compareProduct a b c = compare (a.toInt * b.toInt) c.toInt`.  The product
of two signed magnitudes is the signed product of the magnitudes, and the sign cases reduce to
the comparison of two natural numbers (`compare_signed`).
-/

namespace Azurite.AzInt

open Azurite.AzNat (compare_Nat_lt_iff compare_Nat_eq_iff compare_Nat_gt_iff)

private theorem compare_natCast (x y : ℕ) : Ord.compare (x : ℤ) (y : ℤ) = Ord.compare x y := by
  rcases h : Ord.compare x y with _ | _ | _
  · rw [compare_Nat_lt_iff] at h; exact compare_lt_iff_lt.mpr (by exact_mod_cast h)
  · rw [compare_Nat_eq_iff] at h; exact compare_eq_iff_eq.mpr (by exact_mod_cast h)
  · rw [compare_Nat_gt_iff] at h; exact compare_gt_iff_gt.mpr (by exact_mod_cast h)

private theorem compare_neg_neg (X Y : ℤ) : Ord.compare (-X) (-Y) = (Ord.compare X Y).swap := by
  rcases h : Ord.compare X Y with _ | _ | _
  · rw [compare_lt_iff_lt] at h; exact compare_gt_iff_gt.mpr (by omega)
  · rw [compare_eq_iff_eq] at h; exact compare_eq_iff_eq.mpr (by omega)
  · rw [compare_gt_iff_gt] at h; exact compare_lt_iff_lt.mpr (by omega)

/-- The comparison of two signed magnitudes, in the shape of `compareProduct`. -/
theorem compare_signed (sP cs : Bool) (P cn : ℕ) :
    Ord.compare (if sP then (P : ℤ) else -(P : ℤ)) (if cs then (cn : ℤ) else -(cn : ℤ))
      = if P = 0 then (if cn = 0 then .eq else if cs then .lt else .gt)
        else if cn = 0 then (if sP then .gt else .lt)
        else if sP then (if cs then Ord.compare P cn else .gt)
        else if cs then .lt else (Ord.compare P cn).swap := by
  by_cases hP : P = 0 <;> by_cases hc : cn = 0 <;> cases sP <;> cases cs <;>
    simp only [hP, hc, Nat.cast_zero, neg_zero, Bool.false_eq_true, ↓reduceIte,
      compare_natCast, compare_neg_neg]
  all_goals first
    | exact compare_eq_iff_eq.mpr rfl
    | exact compare_lt_iff_lt.mpr (by omega)
    | exact compare_gt_iff_gt.mpr (by omega)

/-- **Correctness of `compareProduct`.** -/
theorem compareProduct_eq (a b c : AzInt) :
    compareProduct a b c = Ord.compare (a.toInt * b.toInt) c.toInt := by
  rcases a with ⟨as, aa, _⟩
  rcases b with ⟨bs, ba, _⟩
  rcases c with ⟨cs, ca, _⟩
  unfold compareProduct toInt
  dsimp only
  have hP : (if as then (aa.toNat : ℤ) else -(aa.toNat : ℤ))
        * (if bs then (ba.toNat : ℤ) else -(ba.toNat : ℤ))
      = if (as == bs) then ((aa.toNat * ba.toNat : ℕ) : ℤ)
        else -((aa.toNat * ba.toNat : ℕ) : ℤ) := by
    cases as <;> cases bs <;> simp [Nat.cast_mul]
  rw [hP, compare_signed]
  simp only [AzNat.eq_zero_iff_toNat, AzNat.compareProduct_eq, Nat.mul_eq_zero]

end Azurite.AzInt
