/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section9ShanksTable

/-!
# DLMF §3.9(iv), Example: `sₙ = ∑ (−1)^{j+1}/j²` and Table 3.9.1

* `dlmf_3_9_12`: `sₙ → s_∞ = π²/12`, and `0.82246 70334 240 < π²/12 < 0.82246 70334 250`.
* `shanks_s391`: the transforms `t_{n,2k}` (3.9.9) of `sₙ` are the rationals `tQ391 k n`.
* `dlmf_table_3_9_1`: Table 3.9.1. All entries are correctly rounded to 12 decimals except
  `t_{9,10}` (**erratum**: `0.82246 70334 24` should be `0.82246 70334 25`).
-/

open Filter Topology Finset Matrix

namespace Azurite.DLMF

/-! ### Transferring Hankel determinants from `ℚ` to `ℝ` -/

theorem hankel_ratCast (u : ℕ → ℚ) (m n : ℕ) :
    hankel (fun i => (u i : ℝ)) m n = ((hankel u m n : ℚ) : ℝ) := by
  rw [hankel, hankel, ← Rat.coe_castHom, RingHom.map_det]
  congr 1

theorem fwdDiff_ratCast (u : ℕ → ℚ) :
    fwdDiff 1 (fun i => (u i : ℝ)) = fun i => ((fwdDiff 1 u i : ℚ) : ℝ) := by
  funext i
  simp [fwdDiff]

theorem hankel_congr {𝕜 : Type*} [Field 𝕜] {u v : ℕ → 𝕜} {m n : ℕ}
    (h : ∀ i j : Fin m, u (n + i + j) = v (n + i + j)) : hankel u m n = hankel v m n := by
  rw [hankel, hankel]
  congr 1
  ext i j
  exact h i j

/-- The transforms of 3.9.12 are `tQ391 k n` (`n ≤ 10`, `k ≤ 5`). -/
theorem shanks_s391 {k n : ℕ} (hk : k ≤ 5) (hn : n ≤ 10) :
    shanks k s391 n = (tQ391 k n : ℝ) := by
  have hs : s391 = fun m => ((sQ391 m : ℚ) : ℝ) := funext s391_eq
  have h1 : hankel sQ391 (k + 1) n = hankel sT391 (k + 1) n :=
    hankel_congr fun i j => (sT391_eq _ (by have := i.isLt; have := j.isLt; omega)).symm
  have h2 : hankel (fwdDiff 1 (fwdDiff 1 sQ391)) k n = hankel d2T391 k n :=
    hankel_congr fun i j => by
      have hi := i.isLt; have hj := j.isLt
      simp only [fwdDiff, d2T391]
      rw [sT391_eq _ (by omega), sT391_eq _ (by omega), sT391_eq _ (by omega)]
      ring_nf
  rw [shanks, hs, fwdDiff_ratCast, fwdDiff_ratCast, hankel_ratCast, hankel_ratCast, h1, h2,
    tQ391, lapDet_eq, lapDet_eq, Rat.cast_div]
  rfl

/-! ### `s_∞ = π²/12` -/

/-- **DLMF 3.9.12**: `sₙ → s_∞ = π²/12 = 0.82246 70334 24…`. -/
theorem dlmf_3_9_12 :
    Tendsto s391 atTop (𝓝 (Real.pi ^ 2 / 12)) ∧
      (0.8224670334240 : ℝ) < Real.pi ^ 2 / 12 ∧ Real.pi ^ 2 / 12 < 0.8224670334250 := by
  set f : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) ^ 2
  have hf : HasSum f (Real.pi ^ 2 / 6) := by
    have := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    simpa [f] using this
  have ho : HasSum (fun i : ℕ => f (2 * i + 1)) (Real.pi ^ 2 / 24) := by
    have := hf.mul_left (1 / 4)
    convert this using 1
    · funext i
      simp only [f]
      push_cast
      field_simp
      ring
    · ring
  have hes : Summable fun i : ℕ => f (2 * i) :=
    hf.summable.comp_injective (fun a b h => by simpa using h)
  have he : HasSum (fun i : ℕ => f (2 * i)) (Real.pi ^ 2 / 8) := by
    have h := hes.hasSum.even_add_odd ho
    have := h.unique hf
    convert hes.hasSum using 1
    linarith
  set g : ℕ → ℝ := fun j => (-1) ^ j / ((j : ℝ) + 1) ^ 2
  have hg : HasSum g (Real.pi ^ 2 / 12) := by
    have he' : HasSum (fun i : ℕ => g (2 * i)) (Real.pi ^ 2 / 8) :=
      he.congr_fun fun i => by simp [g, f, pow_mul]
    have ho' : HasSum (fun i : ℕ => g (2 * i + 1)) (-(Real.pi ^ 2 / 24)) :=
      ho.neg.congr_fun fun i => by simp [g, f, pow_succ, pow_mul, neg_div]
    convert he'.even_add_odd ho' using 1
    ring
  refine ⟨?_, ?_, ?_⟩
  · have := hg.tendsto_sum_nat
    refine this.congr fun n => ?_
    rw [s391_eq, sQ391]
    push_cast
    rfl
  · have := Real.pi_gt_d20
    nlinarith
  · have := Real.pi_lt_d20
    have := Real.pi_pos
    nlinarith

/-! ### Table 3.9.1 -/

/-- **Table 3.9.1**: Shanks' transformation `t_{n,2k}` of `sₙ = ∑_{j=1}^{n} (−1)^{j+1}/j²`,
`k = 1, …, 5`, `n = 0, …, 10`. All printed values are correctly rounded to 12 decimals except
`t_{9,10}`. **Erratum**: `t_{9,10} = 0.82246 70334 24507…`, printed `0.82246 70334 24`; the
correctly rounded value is `0.82246 70334 25`. -/
theorem dlmf_table_3_9_1 :
    (∀ k < 5, ∀ n < 11, (k, n) ≠ (4, 9) →
      |shanks (k + 1) s391 n - tab391 (k + 1) n| < 5 / 10 ^ 13) ∧
    5 / 10 ^ 13 < |shanks 5 s391 9 - tab391 5 9| ∧
      |shanks 5 s391 9 - tab391c| < 5 / 10 ^ 13 := by
  obtain ⟨h1, h2, h3⟩ := tab391_check
  have c : ∀ x y : ℚ, (|(x : ℝ) - y| : ℝ) = ((|x - y| : ℚ) : ℝ) := fun x y => by push_cast; rfl
  have b : ((5 / 10 ^ 13 : ℚ) : ℝ) = 5 / 10 ^ 13 := by norm_num
  refine ⟨fun k hk n hn hkn => ?_, ?_, ?_⟩
  · rw [shanks_s391 (by omega) (by omega), ← b, c]
    exact_mod_cast h1 k hk n hn hkn
  · rw [shanks_s391 (by omega) (by omega), ← b, c]
    exact_mod_cast h2
  · rw [shanks_s391 (by omega) (by omega), ← b, c]
    exact_mod_cast h3

end Azurite.DLMF
