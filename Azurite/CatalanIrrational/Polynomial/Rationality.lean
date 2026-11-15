/-
Copyright © 2026 Mikhail Hogrefe

Uses code adopted from the OpenAI mathematics repository (<https://github.com/openai/math>,
commit 4eaee87,
`lean/OAI/NumberTheory/Catalan/Polynomial/Rationality.lean`),
licensed under the Apache License, Version 2.0.

     Copyright © 2026 OpenAI

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.CatalanIrrational.Determinants.RowMomentExpansion
import Azurite.CatalanIrrational.Determinants.TwoAdicSmoothedMinor
import Azurite.CatalanIrrational.Estimates.MomentEvaluation

namespace OAI


noncomputable section

open Polynomial
open scoped BigOperators

namespace InternalCatalan

theorem row_contact_real {N r j : ℕ} (hN : 0 < N)
    (hr : r < n N) (hj : j < L N) :
    (∑ i ∈ Finset.range (H N),
      ((rowP N r).coeff i : ℝ) *
        (centralCoeffKernel ((j : ℤ) - i - 1) : ℝ)) =
      ((rowD N r).coeff j : ℝ) := by
  exact_mod_cast row_contact hN hr hj

theorem mixedMoment_rowP_evaluation {N r j : ℕ} (hN : 0 < N)
    (hr : r < n N) (hj : j < L N) :
    mixedMoment (realPoly (rowP N r)) (X ^ j) =
      (∑ i ∈ Finset.range (H N), ((rowP N r).coeff i : ℝ) *
        ((momentRat i j : ℝ) +
          4 * catalan * (centralCoeffKernel ((i : ℤ) - j) : ℝ))) +
      (3 / 2 : ℝ) * zetaSeries 0 0 * ((rowD N r).coeff j : ℝ) := by
  rw [mixedMoment_rowP_X_pow_eq_sum_range hN r j]
  simp_rw [mixedMoment_X_pow_evaluation]
  calc
    _ = ∑ i ∈ Finset.range (H N),
        ((((rowP N r).coeff i : ℝ) *
          ((momentRat i j : ℝ) +
            4 * catalan * (centralCoeffKernel ((i : ℤ) - j) : ℝ))) +
        ((3 / 2 : ℝ) * zetaSeries 0 0) *
          (((rowP N r).coeff i : ℝ) *
            (centralCoeffKernel ((j : ℤ) - i - 1) : ℝ))) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, row_contact_real hN hr hj]

theorem zetaMoment_rowD_evaluation {N r j : ℕ} (hN : 0 < N)
    (hj : j < L N) :
    zetaMoment (realPoly (rowD N r)) (X ^ j) =
      (∑ i ∈ Finset.range (H N),
        ((rowD N r).coeff i : ℝ) * (zetaRat i j : ℝ)) +
      ((rowD N r).coeff j : ℝ) * zetaSeries 0 0 := by
  have hjH : j < H N := by
    unfold L H at *
    omega
  rw [zetaMoment_rowD_X_pow_eq_sum_range hN r j]
  have hterms :
      (∑ i ∈ Finset.range (H N), ((rowD N r).coeff i : ℝ) * zetaSeries i j) =
        ∑ i ∈ Finset.range (H N), ((rowD N r).coeff i : ℝ) *
          ((zetaRat i j : ℝ) + if i = j then zetaSeries 0 0 else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [zetaSeries_eq_zetaRat_add i j]
  rw [hterms]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single j]
  · simp
  · intro i hi hij
    simp [hij]
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr hjH))

theorem rawEntryRat_cast {z : ℚ} {N r j : ℕ} (hz : (z : ℝ) = catalan)
    (hN : 0 < N) (hr : r < n N) (hj : j < L N) :
    (rawEntryRat z N r j : ℝ) =
      mixedMoment (realPoly (rowP N r)) (X ^ j) -
        (3 / 2 : ℝ) * zetaMoment (realPoly (rowD N r)) (X ^ j) := by
  rw [mixedMoment_rowP_evaluation hN hr hj, zetaMoment_rowD_evaluation hN hj]
  unfold rawEntryRat
  push_cast
  rw [hz]
  ring

theorem filteredEntryRat_cast {z : ℚ} {N r k : ℕ} (hz : (z : ℝ) = catalan)
    (hN : 0 < N) (hr : r < n N) (hk : k < n N) :
    (filteredEntryRat z N r k : ℝ) = determinantEntry N r k := by
  unfold filteredEntryRat determinantEntry
  push_cast
  rw [mixedMoment_filteredColumn, zetaMoment_filteredColumn,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  have hvq : v ≤ q N := by
    have hv' := Finset.mem_range.mp hv
    omega
  rw [rawEntryRat_cast hz hN hr (rawColumn_lt_L hk hvq)]
  ring

theorem determinantRat_cast {z : ℚ} {N : ℕ} (hz : (z : ℝ) = catalan)
    (hN : 0 < N) : (determinantRat z N : ℝ) = determinant N := by
  let Rmat : Matrix (Fin (n N)) (Fin (n N)) ℚ :=
    fun r k => filteredEntryRat z N r.val k.val
  let Amat : Matrix (Fin (n N)) (Fin (n N)) ℝ :=
    fun r k => determinantEntry N r.val k.val
  have hm : Rmat.map (fun x : ℚ => (x : ℝ)) = Amat := by
    ext r k
    exact filteredEntryRat_cast hz hN r.isLt k.isLt
  change (Rmat.det : ℝ) = Amat.det
  exact (Rat.cast_det (F := ℝ) Rmat).trans (congrArg Matrix.det hm)

theorem determinantRat_ne_zero_iff {z : ℚ} {N : ℕ}
    (hz : (z : ℝ) = catalan) (hN : 0 < N) :
    determinantRat z N ≠ 0 ↔ determinant N ≠ 0 := by
  rw [← determinantRat_cast hz hN]
  norm_cast

end InternalCatalan

end

end OAI
