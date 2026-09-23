/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter8.Section8_3.Multilinear
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# BPR Proposition 8.27: the polynomial determinant `pdet_{m,n}`

> Source: Basu, Pollack, Roy, *Algorithms in Real Algebraic Geometry*,
> Springer 2006, §8.3.2.1.

The `(m,n)`-polynomial determinant is the unique multilinear alternating mapping
`(𝓕_n)^m → 𝓕_{n-m+1}` normalized on the top monomials (Proposition 8.27). It is
constructed by equation (8.11):

`pdet(𝒫) = Σ_{i ≤ n-m} m_i X^i`,

where `m_i` is the `m × m` minor of `Mat(𝒫)` on columns `1, …, m-1, n-i` (the
top `m-1` monomial columns together with the `X^i` column).

This file builds `pdet` and proves it is **multilinear** and **alternating**
(the structural half of existence): each minor `m_i` is a determinant whose row
`r` depends `K`-linearly only on `P r`, so `m_i` is multilinear and alternating
in the rows, and `pdet` is a `K`-linear combination of the `m_i`.
-/

namespace Azurite.BPR.Chapter8

open Polynomial

variable {K : Type*} [Field K] {m n : ℕ}

/-- Coefficient index of column `c` in the `i`-th minor: the first `m-1` columns
    are the top monomials `X^{n-1}, …, X^{n-m+1}` (index `n-1-c`); the last column
    is `X^i` (index `i`). -/
def pdetColIdx (n : ℕ) {m : ℕ} (i : ℕ) (c : Fin m) : ℕ :=
  if (c : ℕ) + 1 < m then n - 1 - (c : ℕ) else i

/-- The `m × m` submatrix of `Mat(𝒫)` on columns `1, …, m-1, n-i`. -/
noncomputable def pdetMinorMat (P : Fin m → degreeLT K n) (i : ℕ) :
    Matrix (Fin m) (Fin m) K :=
  fun r c => ((P r : K[X])).coeff (pdetColIdx n i c)

/-- The minor `m_i` of `Mat(𝒫)` (the determinant of `pdetMinorMat`). -/
noncomputable def pdetMinor (P : Fin m → degreeLT K n) (i : ℕ) : K :=
  (pdetMinorMat P i).det

/-- `X^i` as an element of `𝓕_d = degreeLT K d` (`i < d`). -/
noncomputable def pdetMono {d : ℕ} (i : Fin d) : degreeLT K d :=
  ⟨X ^ (i : ℕ), by rw [mem_degreeLT, degree_X_pow]; exact_mod_cast i.isLt⟩

/-- **BPR Proposition 8.27 / equation (8.11).** The `(m,n)`-polynomial determinant
    mapping `pdet_{m,n}(𝒫) = Σ_{i ≤ n-m} m_i X^i`. -/
noncomputable def pdet (P : Fin m → degreeLT K n) : degreeLT K (n - m + 1) :=
  ∑ i : Fin (n - m + 1), pdetMinor P (i : ℕ) • pdetMono i

/-- Updating one polynomial updates the corresponding row of every minor matrix. -/
private theorem pdetMinorMat_update (v : Fin m → degreeLT K n) (k : Fin m)
    (Q : degreeLT K n) (i : ℕ) :
    pdetMinorMat (Function.update v k Q) i
      = Matrix.updateRow (pdetMinorMat v i) k
          (fun c : Fin m => ((Q : K[X])).coeff (pdetColIdx n i c)) := by
  ext r c
  rcases eq_or_ne r k with rfl | hrk
  · rw [pdetMinorMat, Matrix.updateRow_self, Function.update_self]
  · rw [pdetMinorMat, Matrix.updateRow_ne hrk, Function.update_of_ne hrk, pdetMinorMat]

/-- Each minor is multilinear in the rows. -/
private theorem pdetMinor_update (v : Fin m → degreeLT K n) (k : Fin m) (a b : K)
    (A B : degreeLT K n) (i : ℕ) :
    pdetMinor (Function.update v k (a • A + b • B)) i
      = a * pdetMinor (Function.update v k A) i + b * pdetMinor (Function.update v k B) i := by
  have hcomb : (fun c : Fin m => ((a • A + b • B : degreeLT K n) : K[X]).coeff (pdetColIdx n i c))
      = a • (fun c : Fin m => ((A : K[X])).coeff (pdetColIdx n i c))
        + b • (fun c : Fin m => ((B : K[X])).coeff (pdetColIdx n i c)) := by
    funext c
    simp only [Submodule.coe_add, Submodule.coe_smul, Polynomial.coeff_add, Polynomial.coeff_smul,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  unfold pdetMinor
  rw [pdetMinorMat_update, pdetMinorMat_update, pdetMinorMat_update, hcomb,
    Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.det_updateRow_smul]

/-- **`pdet` is multilinear** (BPR Proposition 8.27, existence). -/
theorem isMultilinear_pdet :
    IsMultilinear (pdet : (Fin m → degreeLT K n) → degreeLT K (n - m + 1)) := by
  intro v k a b A B
  unfold pdet
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [pdetMinor_update, add_smul, mul_smul, mul_smul]

/-- **`pdet` is alternating** (BPR Proposition 8.27, existence). -/
theorem isAlternating_pdet :
    IsAlternating (pdet : (Fin m → degreeLT K n) → degreeLT K (n - m + 1)) := by
  intro v k l hkl hvkl
  have hzero : ∀ i : ℕ, pdetMinor v i = 0 := by
    intro i
    apply Matrix.det_zero_of_row_eq hkl
    funext c
    show ((v k : K[X])).coeff (pdetColIdx n i c) = ((v l : K[X])).coeff (pdetColIdx n i c)
    rw [hvkl]
  unfold pdet
  apply Finset.sum_eq_zero
  intro i _
  rw [hzero, zero_smul]

end Azurite.BPR.Chapter8
