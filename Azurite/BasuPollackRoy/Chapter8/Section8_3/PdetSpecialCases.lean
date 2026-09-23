/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter8.Section8_3.PolynomialDeterminant
import Azurite.BasuPollackRoy.Chapter8.Section8_3.PolynomialDeterminants

/-!
# BPR Proposition 8.27: the `m = n` and `m = 1` special cases

* When `m = n`, `pdet_{n,n}(𝒫) = det(Mat(𝒫))` (the polynomial determinant is the
  ordinary determinant, as a constant in `𝓕_1`).
* When `m = 1`, `pdet_{1,n}(P) = P` (the polynomial determinant is the identity).

Both are stated at the `K[X]` level to avoid the `n - m + 1` type arithmetic.
-/

namespace Azurite.BPR.Chapter8

open Polynomial

variable {K : Type*} [Field K] {m n : ℕ}

/-- `pdet` as an honest polynomial: `Σ_{i ≤ n-m} m_i X^i`. -/
theorem pdet_coe (P : Fin m → degreeLT K n) :
    ((pdet P : degreeLT K (n - m + 1)) : K[X])
      = ∑ i : Fin (n - m + 1), pdetMinor P (i : ℕ) • X ^ (i : ℕ) := by
  rw [pdet, Submodule.coe_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Submodule.coe_smul]
  rfl

/-- **`pdet_{n,n}(𝒫) = det(Mat(𝒫))`.** -/
theorem pdet_eq_det (P : Fin n → degreeLT K n) :
    ((pdet P : degreeLT K (n - n + 1)) : K[X])
      = C (Mat n (fun r => (P r : K[X]))).det := by
  rw [pdet_coe, Finset.sum_eq_single ⟨0, by omega⟩]
  · have hmat : pdetMinorMat P ((⟨0, by omega⟩ : Fin (n - n + 1)) : ℕ)
        = Mat n (fun r => (P r : K[X])) := by
      ext r c
      rw [pdetMinorMat, Mat]
      congr 1
      have := c.isLt
      simp only [pdetColIdx]
      split <;> omega
    rw [pdetMinor, hmat]
    simp [smul_eq_C_mul]
  · intro b _ hb
    exact absurd (Fin.ext (by have := b.isLt; omega)) hb
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **`pdet_{1,n}(P) = P`.** -/
theorem pdet_eq_self (hn : 1 ≤ n) (v : Fin 1 → degreeLT K n) :
    ((pdet v : degreeLT K (n - 1 + 1)) : K[X]) = (v 0 : K[X]) := by
  rw [pdet_coe]
  have hminor : ∀ i : Fin (n - 1 + 1), pdetMinor v (i : ℕ) = (v 0 : K[X]).coeff (i : ℕ) := by
    intro i
    rw [pdetMinor, Matrix.det_fin_one, pdetMinorMat]
    congr 1
  simp only [hminor]
  have hdeg : (v 0 : K[X]).natDegree < n - 1 + 1 := by
    have h2 := (v 0).2
    rw [mem_degreeLT] at h2
    rcases eq_or_ne (v 0 : K[X]) 0 with hz | hz
    · rw [hz, natDegree_zero]; omega
    · have := (natDegree_lt_iff_degree_lt hz).mpr h2; omega
  conv_rhs => rw [as_sum_range' (v 0 : K[X]) (n - 1 + 1) hdeg]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_eq_C_mul, C_mul_X_pow_eq_monomial]

end Azurite.BPR.Chapter8
