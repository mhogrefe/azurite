/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter8.Section8_3.Proposition_8_27_Uniqueness
import Azurite.BasuPollackRoy.Chapter4.Section4_2.Notation_4_27

/-!
# BPR Lemma 8.28: row operations on the polynomial determinant

* Adding to one row a linear combination of the *other* rows leaves `pdet`
  unchanged (multilinearity + alternation).
* Reversing the rows multiplies `pdet` by `ε_m = (-1)^{m(m-1)/2}` (Notation 4.27),
  the sign of the reversal permutation (`AlternatingMap.map_perm`).
-/

namespace Azurite.BPR.Chapter8

open Polynomial

variable {K : Type*} [Field K] {m n : ℕ}

/-- **BPR Lemma 8.28 (first part).** Adding to row `j` a linear combination of the
    other rows leaves `pdet` unchanged. -/
theorem pdet_update_add_combination (P : Fin m → degreeLT K n) (j : Fin m) (lam : Fin m → K) :
    pdet (Function.update P j (P j + ∑ i ∈ Finset.univ.erase j, lam i • P i)) = pdet P := by
  set M : MultilinearMap K (fun _ : Fin m => degreeLT K n) (degreeLT K (n - m + 1)) :=
    toMLM pdet isMultilinear_pdet with hMdef
  show M (Function.update P j (P j + ∑ i ∈ Finset.univ.erase j, lam i • P i)) = M P
  rw [M.map_update_add, M.map_update_sum, Function.update_eq_self]
  have hsum : ∑ i ∈ Finset.univ.erase j, M (Function.update P j (lam i • P i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    rw [M.map_update_smul]
    have hz : M (Function.update P j (P i)) = 0 := by
      apply isAlternating_pdet (Function.update P j (P i)) i j hij
      rw [Function.update_of_ne hij, Function.update_self]
    rw [hz, smul_zero]
  rw [hsum, add_zero]

/-- **BPR Lemma 8.28 (second part).** Reversing the rows multiplies `pdet` by
    `ε_m = (-1)^{m(m-1)/2}`. -/
theorem pdet_reverse (P : Fin m → degreeLT K n) :
    pdet (P ∘ ⇑(Fin.revPerm)) = (Azurite.BPR.Chapter4.ε m) • pdet P := by
  have h := (toALT pdet isMultilinear_pdet isAlternating_pdet).map_perm P Fin.revPerm
  simp only [toALT_apply] at h
  rw [h, Units.smul_def, Azurite.BPR.Chapter4.sign_revPerm]

end Azurite.BPR.Chapter8
