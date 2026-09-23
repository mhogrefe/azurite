/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter4.Section4_2.Notation_4_13
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Data.Fin.SuccPred

/-!
# Bridge: `Res` agrees with `Polynomial.resultant`

Our BPR-faithful `Syl P Q` (descending power basis, P-shifts then
Q-shifts as rows) is related to Mathlib's `Polynomial.sylvester P Q
P.natDegree Q.natDegree` (ascending power basis, Q-shifts then P-shifts
as columns) by transposition and reindexing both axes by `Fin.rev`.
Since `det` is invariant under transpose and under reindexing by the
same equivalence, our `Res P Q` equals
`Polynomial.resultant P Q P.natDegree Q.natDegree`.

This bridge lets downstream files leverage Mathlib's well-developed
machinery for `Polynomial.resultant` (`resultant_map_map`,
`resultant_add_mul_left`, `resultant_comm`, etc.) for proving theorems
about our `Res`.
-/

namespace Azurite.BPR.Chapter4

open Polynomial

variable {D : Type*} [CommRing D]

/-- Entry-wise: our `Syl` is the transpose of Mathlib's
    `Polynomial.sylvester P Q P.natDegree Q.natDegree`, reindexed by
    `Fin.rev` on both axes. -/
private theorem Syl_eq_sylvester_T_submatrix_rev (P Q : D[X]) :
    Syl P Q =
      ((Polynomial.sylvester P Q P.natDegree Q.natDegree).transpose).submatrix
        Fin.rev Fin.rev := by
  ext i j
  rw [Matrix.submatrix_apply, Matrix.transpose_apply]
  unfold Syl
  rw [Matrix.of_apply]
  unfold Polynomial.sylvester
  rw [Matrix.of_apply]
  have hij : i.val < P.natDegree + Q.natDegree := i.isLt
  have hjj : j.val < P.natDegree + Q.natDegree := j.isLt
  have h_revi_val :
      (Fin.rev i).val = P.natDegree + Q.natDegree - 1 - i.val := by
    rw [Fin.val_rev]; omega
  have h_revj_val :
      (Fin.rev j).val = P.natDegree + Q.natDegree - 1 - j.val := by
    rw [Fin.val_rev]; omega
  by_cases hi : i.val < Q.natDegree
  · rw [ite_eq_left hi, Polynomial.coeff_X_pow_mul']
    have h_natAdd :
        Fin.rev i = Fin.natAdd P.natDegree
          ⟨Q.natDegree - 1 - i.val, by omega⟩ := by
      apply Fin.ext
      rw [h_revi_val]
      show P.natDegree + Q.natDegree - 1 - i.val =
        P.natDegree + (Q.natDegree - 1 - i.val)
      omega
    conv_rhs => rw [h_natAdd]
    rw [Fin.addCases_right]
    simp only [Set.mem_Icc, h_revj_val]
    split_ifs with h1 h2 h2
    · rfl
    · apply Polynomial.coeff_eq_zero_of_natDegree_lt
      push Not at h2
      have := h2 h1
      omega
    · exfalso; omega
    · rfl
  · push Not at hi
    rw [ite_eq_right (not_lt.mpr hi), Polynomial.coeff_X_pow_mul']
    have h_revi_lt : P.natDegree + Q.natDegree - 1 - i.val < P.natDegree := by
      omega
    have h_castAdd :
        Fin.rev i = Fin.castAdd Q.natDegree
          ⟨P.natDegree + Q.natDegree - 1 - i.val, h_revi_lt⟩ := by
      apply Fin.ext
      rw [h_revi_val]
      rfl
    conv_rhs => rw [h_castAdd]
    rw [Fin.addCases_left]
    simp only [Set.mem_Icc, h_revj_val]
    split_ifs with h1 h2 h2
    · rfl
    · apply Polynomial.coeff_eq_zero_of_natDegree_lt
      push Not at h2
      have := h2 h1
      omega
    · exfalso; omega
    · rfl

/-- **Bridge.** Our `Res` agrees with Mathlib's `Polynomial.resultant`
    evaluated at the polynomials' natural degrees. -/
theorem Res_eq_resultant (P Q : D[X]) :
    Res P Q = Polynomial.resultant P Q P.natDegree Q.natDegree := by
  unfold Res Polynomial.resultant
  rw [Syl_eq_sylvester_T_submatrix_rev P Q]
  rw [show ((Polynomial.sylvester P Q P.natDegree Q.natDegree).transpose).submatrix
        (Fin.rev : Fin (P.natDegree + Q.natDegree) → _)
        (Fin.rev : Fin (P.natDegree + Q.natDegree) → _)
      = ((Polynomial.sylvester P Q P.natDegree Q.natDegree).transpose).submatrix
          (Fin.revPerm : Equiv.Perm (Fin (P.natDegree + Q.natDegree)))
          (Fin.revPerm : Equiv.Perm (Fin (P.natDegree + Q.natDegree)))
      from rfl]
  rw [Matrix.det_submatrix_equiv_self Fin.revPerm]
  exact Matrix.det_transpose _

end Azurite.BPR.Chapter4
