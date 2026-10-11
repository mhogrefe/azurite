/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzVector.DotSign
import Azurite.AzVector.Equiv.Dot
import Azurite.AzNat.Equiv.RingEquiv
import Azurite.AzNat.Equiv.CompareProducts

/-!
## Correctness of `AzNat.dotSign`

`dotSign_eq : dotSign v w = compare (∑ i, vᵢ wᵢ) 0` over the values, and
`dotSign_eq_compare_dot : dotSign v w = compare (v.dot w).toNat 0`.  A sum of natural numbers
vanishes exactly when every term does, and a product of two exactly when a factor does.
-/

namespace Azurite.AzNat

open Azurite (AzVector)

variable {n : Nat}

/-- **Correctness of `dotSign`**: the ordering of `∑ i, vᵢ wᵢ` against `0`. -/
theorem dotSign_eq (v w : AzVector AzNat n) :
    dotSign v w = Ord.compare (∑ i, (v.toFn i).toNat * (w.toFn i).toNat) 0 := by
  unfold dotSign
  have hany : (v.zip (fun a b => decide (a ≠ 0) && decide (b ≠ 0)) w).data.any id = true ↔
      ∃ i : Fin n, (v.toFn i).toNat ≠ 0 ∧ (w.toFn i).toNat ≠ 0 := by
    rw [Vector.any_iff_exists]
    constructor
    · rintro ⟨i, hi, h⟩
      refine ⟨⟨i, hi⟩, ?_⟩
      have := AzVector.toFn_zip (fun a b => decide (a ≠ 0) && decide (b ≠ 0)) v w ⟨i, hi⟩
      change (v.zip _ w).data[i] = _ at this
      rw [this] at h
      simpa [eq_zero_iff_toNat] using h
    · rintro ⟨i, h⟩
      refine ⟨i, i.isLt, ?_⟩
      have := AzVector.toFn_zip (fun a b => decide (a ≠ 0) && decide (b ≠ 0)) v w i
      change (v.zip _ w).data[i.val] = _ at this
      rw [this]
      simpa [eq_zero_iff_toNat] using h
  split_ifs with h
  · obtain ⟨i, hv, hw⟩ := hany.mp h
    symm; rw [compare_Nat_gt_iff]
    exact lt_of_lt_of_le (Nat.mul_pos (Nat.pos_of_ne_zero hv) (Nat.pos_of_ne_zero hw))
      (Finset.single_le_sum (f := fun i => (v.toFn i).toNat * (w.toFn i).toNat)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  · symm; rw [compare_Nat_eq_iff]
    apply Finset.sum_eq_zero
    intro i _
    rw [Nat.mul_eq_zero]
    by_contra hne
    rw [not_or] at hne
    exact h (hany.mpr ⟨i, hne.1, hne.2⟩)

/-- **`dotSign` is the sign of the dot product.** -/
theorem dotSign_eq_compare_dot (v w : AzVector AzNat n) :
    dotSign v w = Ord.compare (v.dot w).toNat 0 := by
  rw [dotSign_eq, AzVector.dot_eq_dotProduct, dotProduct, ← toNatRingHom_apply, map_sum]
  congr 2
  funext i
  rw [map_mul, toNatRingHom_apply, toNatRingHom_apply]

end Azurite.AzNat
