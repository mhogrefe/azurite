/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section9Shanks
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# DLMF §3.9(iv), Example: Table 3.9.1, certified

* 3.9.12 (`s391`, `dlmf_3_9_12`): `sₙ = ∑_{j=1}^{n} (−1)^{j+1}/j²`, `s_∞ = π²/12
  = 0.82246 70334 24…` (from `ζ(2) = π²/6` by splitting even and odd terms).
* Table 3.9.1 (`dlmf_table_3_9_1`): the transforms `t_{n,2k}` (3.9.9) for `k = 1, …, 5`,
  `n = 0, …, 10`, computed exactly in `ℚ` by Laplace expansion (`lapDet`, `lapDet_eq`) and checked
  by `decide +kernel`. All entries are correctly rounded except one. **Erratum**:
  `t_{9,10} = 0.82246 70334 24507…`, so the printed `0.82246 70334 24` should be
  `0.82246 70334 25`.
-/

open Filter Topology Finset Matrix

namespace Azurite.DLMF

/-! ### Laplace expansion in `ℚ` -/

/-- Determinant by Laplace expansion along the first row. -/
def lapDet : (m : ℕ) → (Fin m → Fin m → ℚ) → ℚ
  | 0, _ => 1
  | m + 1, A => ∑ j : Fin (m + 1), (-1) ^ (j : ℕ) * A 0 j *
      lapDet m (fun i k => A i.succ (j.succAbove k))

theorem lapDet_eq (m : ℕ) (A : Fin m → Fin m → ℚ) : lapDet m A = (Matrix.of A).det := by
  induction m with
  | zero => simp [lapDet]
  | succ m ih =>
    rw [lapDet, det_succ_row_zero]
    refine sum_congr rfl fun j _ => ?_
    rw [ih]
    rfl

/-! ### The sequence -/

/-- **DLMF 3.9.12**: `sₙ = ∑_{j=1}^{n} (−1)^{j+1}/j²`. -/
noncomputable def s391 (n : ℕ) : ℝ := ∑ j ∈ Icc 1 n, (-1) ^ (j + 1) / (j : ℝ) ^ 2

/-- The same partial sums in `ℚ`. -/
def sQ391 (n : ℕ) : ℚ := ∑ j ∈ range n, (-1) ^ j / ((j : ℚ) + 1) ^ 2

theorem s391_eq (n : ℕ) : s391 n = (sQ391 n : ℝ) := by
  induction n with
  | zero => simp [s391, sQ391]
  | succ n ih =>
    rw [s391, sum_Icc_succ_top (by omega), ← s391, ih, sQ391, sQ391, sum_range_succ]
    push_cast
    ring

def sTab391 : List ℚ :=
  [0 / 1,
   1 / 1,
   3 / 4,
   31 / 36,
   115 / 144,
   3019 / 3600,
   973 / 1200,
   48877 / 58800,
   191833 / 235200,
   5257891 / 6350400,
   5194387 / 6350400,
   634871227 / 768398400,
   629535127 / 768398400,
   107159834863 / 129859329600,
   106497287263 / 129859329600,
   107074439839 / 129859329600,
   426268707331 / 519437318400,
   123711093737059 / 150117385017600,
   41082589491553 / 50039128339200,
   14880853934789833 / 18064125330451200,
   2967138724292741 / 3612825066090240]

/-- `sₙ` from the table (`n ≤ 20`). -/
def sT391 (n : ℕ) : ℚ := sTab391.getD n 0

theorem sT391_eq : ∀ n < 21, sT391 n = sQ391 n := by decide +kernel

/-- `Δ²sₙ` from the table. -/
def d2T391 (n : ℕ) : ℚ := sT391 (n + 2) - 2 * sT391 (n + 1) + sT391 n

/-- `t_{n,2k}` (3.9.9) by Laplace expansion. -/
def tQ391 (k n : ℕ) : ℚ :=
  lapDet (k + 1) (fun i j => sT391 (n + i + j)) / lapDet k (fun i j => d2T391 (n + i + j))

def tab391 : ℕ → ℕ → ℚ
  | 1, 0 => 800000000000 / 10 ^ 12
  | 2, 0 => 821826280624 / 10 ^ 12
  | 3, 0 => 822448450147 / 10 ^ 12
  | 4, 0 => 822466490960 / 10 ^ 12
  | 5, 0 => 822467017541 / 10 ^ 12
  | 1, 1 => 826923076923 / 10 ^ 12
  | 2, 1 => 822590201765 / 10 ^ 12
  | 3, 1 => 822470534657 / 10 ^ 12
  | 4, 1 => 822467134206 / 10 ^ 12
  | 5, 1 => 822467036345 / 10 ^ 12
  | 1, 2 => 821111111111 / 10 ^ 12
  | 2, 2 => 822434478514 / 10 ^ 12
  | 3, 2 => 822466182145 / 10 ^ 12
  | 4, 2 => 822467010248 / 10 ^ 12
  | 5, 2 => 822467032779 / 10 ^ 12
  | 1, 3 => 823001355014 / 10 ^ 12
  | 2, 3 => 822477811835 / 10 ^ 12
  | 3, 3 => 822467285183 / 10 ^ 12
  | 4, 3 => 822467039756 / 10 ^ 12
  | 5, 3 => 822467033590 / 10 ^ 12
  | 1, 4 => 822217668488 / 10 ^ 12
  | 2, 4 => 822462831441 / 10 ^ 12
  | 3, 4 => 822466946793 / 10 ^ 12
  | 4, 4 => 822467031436 / 10 ^ 12
  | 5, 4 => 822467033375 / 10 ^ 12
  | 1, 5 => 822598039216 / 10 ^ 12
  | 2, 5 => 822468885722 / 10 ^ 12
  | 3, 5 => 822467067021 / 10 ^ 12
  | 4, 5 => 822467034124 / 10 ^ 12
  | 5, 5 => 822467033440 / 10 ^ 12
  | 1, 6 => 822391939077 / 10 ^ 12
  | 2, 6 => 822466135237 / 10 ^ 12
  | 3, 6 => 822467019076 / 10 ^ 12
  | 4, 6 => 822467033154 / 10 ^ 12
  | 5, 6 => 822467033418 / 10 ^ 12
  | 1, 7 => 822513048323 / 10 ^ 12
  | 2, 7 => 822467503313 / 10 ^ 12
  | 3, 7 => 822467040056 / 10 ^ 12
  | 4, 7 => 822467033537 / 10 ^ 12
  | 5, 7 => 822467033426 / 10 ^ 12
  | 1, 8 => 822437313733 / 10 ^ 12
  | 2, 8 => 822466771932 / 10 ^ 12
  | 3, 8 => 822467030149 / 10 ^ 12
  | 4, 8 => 822467033373 / 10 ^ 12
  | 5, 8 => 822467033423 / 10 ^ 12
  | 1, 9 => 822487062489 / 10 ^ 12
  | 2, 9 => 822467186591 / 10 ^ 12
  | 3, 9 => 822467035134 / 10 ^ 12
  | 4, 9 => 822467033448 / 10 ^ 12
  | 5, 9 => 822467033424 / 10 ^ 12
  | 1, 10 => 822453053515 / 10 ^ 12
  | 2, 10 => 822466939757 / 10 ^ 12
  | 3, 10 => 822467032488 / 10 ^ 12
  | 4, 10 => 822467033412 / 10 ^ 12
  | 5, 10 => 822467033424 / 10 ^ 12
  | _, _ => 0

/-- The correctly rounded `t_{9,10}`. -/
def tab391c : ℚ := 822467033425 / 10 ^ 12

theorem tab391_check :
    (∀ k < 5, ∀ n < 11, (k, n) ≠ (4, 9) →
      |tQ391 (k + 1) n - tab391 (k + 1) n| < 5 / 10 ^ 13) ∧
    5 / 10 ^ 13 < |tQ391 5 9 - tab391 5 9| ∧ |tQ391 5 9 - tab391c| < 5 / 10 ^ 13 := by
  decide +kernel

end Azurite.DLMF
