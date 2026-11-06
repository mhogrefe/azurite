/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section11Lebesgue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.ZetaValues

/-!
# DLMF §3.11(ii): `L₁₀₀₀ = 4.07…`

`dlmf_3_11_ii_lebesgue_1000`: `4.07 ≤ L₁₀₀₀ < 4.08` (numerically `L₁₀₀₀ = 4.0701636…`).

From Szegő's series (`dlmf_3_11_ii_szego`) with `N = 2001`:

* `H′_M = H_{2M} − ½H_M` (`hprime_eq_harmonic`) and the second-order bounds
  `1/(2m) − 1/(12m²) ≤ H_m − ln m − γ ≤ 1/(2m)` (`harmonic_sub_log_bounds`, from the monotonicity of
  `H_m − ln m − 1/(2m)` and `H_m − ln m − 1/(2m) + 1/(12m²)`, i.e. the trapezoidal bounds
  `log_one_add_inv_le_trap`, `log_one_add_inv_ge_trap` from the series of `ln(1 + 1/a)`) give
  `H′_M = ½ ln M + ln 2 + ½γ + O(M⁻²)` (`hprime_bounds`);
* hence `Lₙ = (8/π²)(S + ½ ln N + ln 2 + ½γ) + O(N⁻²)`, `S = ∑_{k ≥ 2} ln k/(4k² − 1)`;
* `S = ½ ∑_{k ≥ 1} ln(1 + 1/k)/(2k + 1)` by summation by parts (`hasSum_log_div`), and
  `∑_{k ≥ 1} 1/(2k + 1)² = π²/8 − 1` (`hasSum_inv_odd_sq`), leaving a rapidly convergent remainder
  bounded in exact rational arithmetic (`dLoQ`, `dHiQ`, checked by the kernel);
* `γ` from `H₁₂₈` (kernel-checked) and `ln 2` (Mathlib's 9-digit bounds), `ln 2001 = 11 ln 2 −
  ln(1 + 47/2001)`.
-/

open Real Finset MeasureTheory Filter Topology Set

namespace Azurite.DLMF

/-! ### Logarithm bounds from `ln(1 + 1/a) = 2 ∑ y^{2j+1}/(2j + 1)`, `y = 1/(2a + 1)` -/

theorem log_one_add_inv_sum_le {a : ℝ} (ha : 0 < a) (J : ℕ) :
    ∑ j ∈ range J, 2 * (1 / (2 * (j : ℝ) + 1)) * (1 / (2 * a + 1)) ^ (2 * j + 1) ≤
      log (1 + a⁻¹) :=
  sum_le_hasSum (range J) (fun j _ => by positivity) (Real.hasSum_log_one_add_inv ha)

theorem log_one_add_inv_le_sum {a : ℝ} (ha : 0 < a) (J : ℕ) :
    log (1 + a⁻¹) ≤ ∑ j ∈ range J, 2 * (1 / (2 * (j : ℝ) + 1)) * (1 / (2 * a + 1)) ^ (2 * j + 1) +
      2 * (1 / (2 * (J : ℝ) + 1)) * (1 / (2 * a + 1)) ^ (2 * J + 1) *
        (1 - (1 / (2 * a + 1)) ^ 2)⁻¹ := by
  set y := 1 / (2 * a + 1) with hy
  have hy0 : 0 < y := by positivity
  have hy1 : y < 1 := by rw [hy, div_lt_one (by positivity)]; linarith
  have hy2 : y ^ 2 < 1 := by nlinarith
  have htail := (hasSum_nat_add_iff' J).mpr (Real.hasSum_log_one_add_inv ha)
  have hgeo := (hasSum_geometric_of_lt_one (sq_nonneg y) hy2).mul_left
    (2 * (1 / (2 * (J : ℝ) + 1)) * y ^ (2 * J + 1))
  have hle := hasSum_le (fun j => ?_) htail hgeo
  · linarith
  · rw [show 2 * (j + J) + 1 = (2 * J + 1) + 2 * j by ring, pow_add, pow_mul]
    have h1 : 1 / (2 * ((j + J : ℕ) : ℝ) + 1) ≤ 1 / (2 * (J : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      push_cast; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    have h2 : 0 ≤ y ^ (2 * J + 1) * (y ^ 2) ^ j := by positivity
    calc 2 * (1 / (2 * ((j + J : ℕ) : ℝ) + 1)) * (y ^ (2 * J + 1) * (y ^ 2) ^ j)
        ≤ 2 * (1 / (2 * (J : ℝ) + 1)) * (y ^ (2 * J + 1) * (y ^ 2) ^ j) := by gcongr
      _ = _ := by ring

/-- `ln(1 + 1/m) ≤ 1/(2m) + 1/(2(m + 1))`. -/
theorem log_one_add_inv_le_trap {m : ℝ} (hm : 0 < m) :
    log (1 + m⁻¹) ≤ 1 / (2 * m) + 1 / (2 * (m + 1)) := by
  have hm1 : 0 < 2 * m + 1 := by linarith
  have hm1' : 2 * m + 1 ≠ 0 := hm1.ne'
  have hm0 : m ≠ 0 := hm.ne'
  have hm2 : m + 1 ≠ 0 := by positivity
  have hden : 1 - (1 / (2 * m + 1)) ^ 2 ≠ 0 := by
    rw [show 1 - (1 / (2 * m + 1)) ^ 2 = 4 * m * (m + 1) / (2 * m + 1) ^ 2 by field_simp; ring]
    positivity
  calc log (1 + m⁻¹) ≤ _ := log_one_add_inv_le_sum hm 1
    _ = 2 / (2 * m + 1) + 1 / (6 * m * (m + 1) * (2 * m + 1)) := by
        simp only [range_one, sum_singleton, Nat.cast_zero, mul_zero, zero_add, Nat.cast_one,
          Nat.reduceMul, Nat.reduceAdd, div_pow, one_pow]
        rw [show 1 - 1 / (2 * m + 1) ^ 2 = 4 * m * (m + 1) / (2 * m + 1) ^ 2 by
          field_simp; ring]
        field_simp
        ring
    _ ≤ 1 / (2 * m) + 1 / (2 * (m + 1)) := by
        rw [← sub_nonneg]
        have e : 1 / (2 * m) + 1 / (2 * (m + 1)) -
            (2 / (2 * m + 1) + 1 / (6 * m * (m + 1) * (2 * m + 1))) =
            1 / (3 * m * (m + 1) * (2 * m + 1)) := by
          field_simp; ring
        rw [e]; positivity

/-- `ln(1 + 1/m) ≥ 1/(2m) + 1/(2(m + 1)) − 1/(12m²) + 1/(12(m + 1)²)`. -/
theorem log_one_add_inv_ge_trap {m : ℝ} (hm : 0 < m) :
    1 / (2 * m) + 1 / (2 * (m + 1)) - 1 / (12 * m ^ 2) + 1 / (12 * (m + 1) ^ 2) ≤
      log (1 + m⁻¹) := by
  have hm1 : 0 < 2 * m + 1 := by linarith
  have hm1' : 2 * m + 1 ≠ 0 := hm1.ne'
  calc 1 / (2 * m) + 1 / (2 * (m + 1)) - 1 / (12 * m ^ 2) + 1 / (12 * (m + 1) ^ 2)
      ≤ 2 / (2 * m + 1) + 2 / (3 * (2 * m + 1) ^ 3) := by
        rw [← sub_nonneg]
        have e : 2 / (2 * m + 1) + 2 / (3 * (2 * m + 1) ^ 3) -
            (1 / (2 * m) + 1 / (2 * (m + 1)) - 1 / (12 * m ^ 2) + 1 / (12 * (m + 1) ^ 2)) =
            ((2 * m + 1) ^ 2 + 1) / (24 * m ^ 2 * (m + 1) ^ 2 * (2 * m + 1) ^ 3) := by
          field_simp; ring
        rw [e]; positivity
    _ = ∑ j ∈ range 2, 2 * (1 / (2 * (j : ℝ) + 1)) * (1 / (2 * m + 1)) ^ (2 * j + 1) := by
        simp only [sum_range_succ, range_zero, sum_empty, Nat.cast_zero, Nat.cast_one,
          Nat.reduceMul, Nat.reduceAdd, div_pow, one_pow]
        field_simp
        ring
    _ ≤ log (1 + m⁻¹) := log_one_add_inv_sum_le hm 2

/-! ### Second-order bounds for `H_m − ln m − γ` -/

theorem log_succ_sub_log (m : ℝ) (hm : 0 < m) : log (m + 1) - log m = log (1 + m⁻¹) := by
  rw [← Real.log_div (by linarith) hm.ne']
  congr 1
  field_simp

theorem harmonic_succ_real (k : ℕ) :
    (harmonic (k + 1) : ℝ) = harmonic k + 1 / ((k : ℝ) + 1) := by
  rw [harmonic_succ]; push_cast; ring

/-- `1/(2m) − 1/(12m²) ≤ H_m − ln m − γ ≤ 1/(2m)` for `m ≥ 1`. -/
theorem harmonic_sub_log_bounds {m : ℕ} (hm : 1 ≤ m) :
    1 / (2 * (m : ℝ)) - 1 / (12 * (m : ℝ) ^ 2) ≤
        (harmonic m : ℝ) - log m - eulerMascheroniConstant ∧
      (harmonic m : ℝ) - log m - eulerMascheroniConstant ≤ 1 / (2 * (m : ℝ)) := by
  set u : ℕ → ℝ := fun k => (harmonic (k + 1) : ℝ) - log ((k : ℝ) + 1) - 1 / (2 * ((k : ℝ) + 1))
  set w : ℕ → ℝ := fun k => u k + 1 / (12 * ((k : ℝ) + 1) ^ 2)
  have hstep : ∀ k : ℕ, u (k + 1) - u k =
      1 / (2 * ((k : ℝ) + 1)) + 1 / (2 * ((k : ℝ) + 1 + 1)) - log (1 + ((k : ℝ) + 1)⁻¹) := by
    intro k
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hl := log_succ_sub_log ((k : ℝ) + 1) hk
    simp only [u]
    rw [harmonic_succ_real (k + 1)]
    push_cast
    have : (1 : ℝ) / ((k : ℝ) + 1 + 1) = 2 * (1 / (2 * ((k : ℝ) + 1 + 1))) := by
      field_simp
    linarith
  have hu : Monotone u := monotone_nat_of_le_succ fun k => by
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have := log_one_add_inv_le_trap hk
    have := hstep k
    linarith
  have hw : Antitone w := antitone_nat_of_succ_le fun k => by
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have := log_one_add_inv_ge_trap hk
    have := hstep k
    simp only [w]
    push_cast
    linarith
  have hlim0 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hlimH : Tendsto (fun k : ℕ => (harmonic (k + 1) : ℝ) - log ((k : ℝ) + 1)) atTop
      (𝓝 eulerMascheroniConstant) := by
    have := tendsto_harmonic_sub_log.comp (tendsto_add_atTop_nat 1)
    convert this using 2 with k
    simp
  have hlimu : Tendsto u atTop (𝓝 eulerMascheroniConstant) := by
    have := hlimH.sub (hlim0.div_const 2)
    simp only [zero_div, sub_zero] at this
    convert this using 2 with k
    simp only [u]
    rw [div_div, mul_comm ((k : ℝ) + 1) 2]
  have hlimw : Tendsto w atTop (𝓝 eulerMascheroniConstant) := by
    have h2 : Tendsto (fun k : ℕ => 1 / (12 * ((k : ℝ) + 1) ^ 2)) atTop (𝓝 0) := by
      have := (hlim0.pow 2).div_const 12
      simp only [zero_pow two_ne_zero, zero_div] at this
      convert this using 2 with k
      rw [div_pow, one_pow, div_div, mul_comm]
    have := hlimu.add h2
    rw [add_zero] at this
    exact this
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have h1 := hu.ge_of_tendsto hlimu k
  have h2 := hw.le_of_tendsto hlimw k
  simp only [u, w] at h1 h2
  push_cast
  constructor <;> linarith

/-! ### `H′_M` -/

theorem hprime_eq_harmonic (M : ℕ) : hprime M = (harmonic (2 * M) : ℝ) - (harmonic M : ℝ) / 2 := by
  induction M with
  | zero => simp [hprime]
  | succ M ih =>
    rw [hprime, sum_range_succ, ← hprime, ih, show 2 * (M + 1) = 2 * M + 1 + 1 by ring,
      harmonic_succ_real, harmonic_succ_real, harmonic_succ_real]
    push_cast
    field_simp
    ring

/-- `H′_M = ½ ln M + ln 2 + ½γ + ε`, `−1/(48M²) ≤ ε ≤ 1/(24M²)`. -/
theorem hprime_bounds {M : ℕ} (hM : 1 ≤ M) :
    -(1 / (48 * (M : ℝ) ^ 2)) ≤ hprime M - log M / 2 - log 2 - eulerMascheroniConstant / 2 ∧
      hprime M - log M / 2 - log 2 - eulerMascheroniConstant / 2 ≤ 1 / (24 * (M : ℝ) ^ 2) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  obtain ⟨a1, a2⟩ := harmonic_sub_log_bounds hM
  obtain ⟨b1, b2⟩ := harmonic_sub_log_bounds (m := 2 * M) (by omega)
  have hlog : log ((2 * M : ℕ) : ℝ) = log 2 + log M := by
    push_cast; exact Real.log_mul two_ne_zero hM'.ne'
  rw [hlog] at b1 b2
  rw [hprime_eq_harmonic]
  have e1 : 1 / (2 * ((2 * M : ℕ) : ℝ)) = 1 / (4 * (M : ℝ)) := by push_cast; ring
  have e2 : 1 / (12 * ((2 * M : ℕ) : ℝ) ^ 2) = 1 / (48 * (M : ℝ) ^ 2) := by push_cast; ring
  have e3 : 1 / (2 * (M : ℝ)) = 2 * (1 / (4 * (M : ℝ))) := by field_simp; ring
  have e4 : 1 / (12 * (M : ℝ) ^ 2) = 2 * (1 / (24 * (M : ℝ) ^ 2)) := by field_simp; ring
  have e5 : 1 / (24 * (M : ℝ) ^ 2) = 2 * (1 / (48 * (M : ℝ) ^ 2)) := by field_simp; ring
  rw [e1, e2] at b1
  rw [e1] at b2
  rw [e3, e4] at a1
  rw [e3] at a2
  constructor <;> linarith

/-! ### `∑_{k ≥ 1} 1/(2k + 1)² = π²/8 − 1` -/

theorem hasSum_inv_odd_sq : HasSum (fun k : ℕ => 1 / (2 * (k : ℝ) + 3) ^ 2) (π ^ 2 / 8 - 1) := by
  set f : ℕ → ℝ := fun n => 1 / (n : ℝ) ^ 2
  have hf : HasSum f (π ^ 2 / 6) := hasSum_zeta_two
  have he : HasSum (fun k => f (2 * k)) (π ^ 2 / 24) := by
    convert hasSum_zeta_two.mul_left (1 / 4) using 1
    · funext k; simp only [f]; push_cast
      rcases eq_or_ne (k : ℝ) 0 with h | h
      · simp [h]
      · field_simp; ring
    · ring
  have hs : Summable fun k => f (2 * k + 1) :=
    hf.summable.comp_injective (fun a b h => by simpa using h)
  have hsum := he.even_add_odd hs.hasSum
  have hval : ∑' k, f (2 * k + 1) = π ^ 2 / 8 := by
    have := hsum.unique hf
    linarith
  have h1 := (hasSum_nat_add_iff' 1).mpr (hval ▸ hs.hasSum)
  simp only [range_one, sum_singleton, f] at h1
  convert h1 using 1
  · funext k; push_cast; ring_nf
  · norm_num

/-! ### `S = ∑_{k ≥ 2} ln k/(4k² − 1)` by summation by parts -/

/-- The terms `T_k = ½ ln(1 + 1/(k + 1))/(2k + 3)` of the rearranged series. -/
noncomputable def lebT (k : ℕ) : ℝ := log (1 + ((k : ℝ) + 1)⁻¹) / 2 / (2 * (k : ℝ) + 3)

theorem lebT_nonneg (k : ℕ) : 0 ≤ lebT k := by
  unfold lebT
  have : 0 ≤ log (1 + ((k : ℝ) + 1)⁻¹) := Real.log_nonneg (by
    have : 0 ≤ ((k : ℝ) + 1)⁻¹ := by positivity
    linarith)
  positivity

theorem lebT_le (k : ℕ) : lebT k ≤ 1 / ((k : ℝ) + 1) ^ 2 := by
  unfold lebT
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hl : log (1 + ((k : ℝ) + 1)⁻¹) ≤ ((k : ℝ) + 1)⁻¹ := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + ((k : ℝ) + 1)⁻¹ by positivity)
    linarith
  rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have : ((k : ℝ) + 1)⁻¹ * ((k : ℝ) + 1) = 1 := inv_mul_cancel₀ hk.ne'
  nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ 1 + ((k : ℝ) + 1)⁻¹ by
    have : 0 ≤ ((k : ℝ) + 1)⁻¹ := by positivity
    linarith)]

theorem summable_lebT : Summable lebT :=
  Summable.of_nonneg_of_le lebT_nonneg lebT_le
    ((summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two) |>.congr
      fun k => by push_cast; rfl)

/-- Summation by parts: `∑_{k ≥ 1} ln(k)/(4k² − 1) = ∑_k T_k`. -/
theorem hasSum_log_div :
    HasSum (fun k : ℕ => log ((k : ℝ) + 1) / (4 * ((k : ℝ) + 1) ^ 2 - 1)) (∑' k, lebT k) := by
  have hpos : ∀ k : ℕ, 0 < 4 * ((k : ℝ) + 1) ^ 2 - 1 := fun k => by
    have : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    nlinarith
  have hnn : ∀ k : ℕ, 0 ≤ log ((k : ℝ) + 1) / (4 * ((k : ℝ) + 1) ^ 2 - 1) := fun k =>
    div_nonneg (Real.log_nonneg (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]))
      (hpos k).le
  -- `A_K = B_K − ½ ln(K + 1)/(2K + 1)`
  have hpart : ∀ K : ℕ, ∑ k ∈ range K, log ((k : ℝ) + 1) / (4 * ((k : ℝ) + 1) ^ 2 - 1) =
      ∑ k ∈ range K, lebT k - log ((K : ℝ) + 1) / 2 / (2 * (K : ℝ) + 1) := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [sum_range_succ, sum_range_succ, ih]
      have hK : (0 : ℝ) < (K : ℝ) + 1 := by positivity
      have hl := log_succ_sub_log ((K : ℝ) + 1) hK
      have h4 : 4 * ((K : ℝ) + 1) ^ 2 - 1 = (2 * K + 1) * (2 * K + 3) := by ring
      unfold lebT
      rw [← hl, h4]
      push_cast
      field_simp
      ring_nf
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  simp only [hpart]
  have hB := summable_lebT.hasSum.tendsto_sum_nat
  have hε : Tendsto (fun K : ℕ => log ((K : ℝ) + 1) / 2 / (2 * (K : ℝ) + 1)) atTop (𝓝 0) := by
    have h := Real.tendsto_pow_log_div_mul_add_atTop 2 (-1) 1 two_ne_zero
    have h2 := (h.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)).div_const 2
    simp only [zero_div] at h2
    convert h2 using 2 with K
    simp only [Function.comp, pow_one]
    ring_nf
  simpa using hB.sub hε

/-! ### Rational bounds -/

/-- Lower bounds `y⁴/3 + y⁶/5 + y⁸/7` for `T_k − y²`, `y = 1/(2k + 3)`. -/
def dLoQ (K : ℕ) : ℚ := ∑ k ∈ range K,
  (((1 : ℚ) / (2 * k + 3)) ^ 4 / 3 + ((1 : ℚ) / (2 * k + 3)) ^ 6 / 5 +
    ((1 : ℚ) / (2 * k + 3)) ^ 8 / 7)

/-- Upper bounds: `dLoQ` plus `y¹⁰/(9(1 − y²))`. -/
def dHiQ (K : ℕ) : ℚ := ∑ k ∈ range K,
  (((1 : ℚ) / (2 * k + 3)) ^ 4 / 3 + ((1 : ℚ) / (2 * k + 3)) ^ 6 / 5 +
    ((1 : ℚ) / (2 * k + 3)) ^ 8 / 7 +
      ((1 : ℚ) / (2 * k + 3)) ^ 10 / (9 * (1 - ((1 : ℚ) / (2 * k + 3)) ^ 2)))

theorem dLoQ_40 : (5204160 / 1000000000 : ℚ) ≤ dLoQ 40 := by decide +kernel

theorem dHiQ_40 : dHiQ 40 ≤ (5206290 / 1000000000 : ℚ) := by decide +kernel

theorem harmonic_128_bounds :
    (54331470925 / 10000000000 : ℚ) ≤ harmonic 128 ∧
      harmonic 128 ≤ (54331470926 / 10000000000 : ℚ) := by
  constructor <;> decide +kernel

/-- `T_k − y² ∈ [y⁴/3 + y⁶/5 + y⁸/7, … + y¹⁰/(9(1 − y²))]`. -/
theorem lebT_sub_bounds (k : ℕ) :
    (((1 : ℝ) / (2 * k + 3)) ^ 4 / 3 + ((1 : ℝ) / (2 * k + 3)) ^ 6 / 5 +
        ((1 : ℝ) / (2 * k + 3)) ^ 8 / 7) ≤ lebT k - 1 / (2 * (k : ℝ) + 3) ^ 2 ∧
      lebT k - 1 / (2 * (k : ℝ) + 3) ^ 2 ≤
        ((1 : ℝ) / (2 * k + 3)) ^ 4 / 3 + ((1 : ℝ) / (2 * k + 3)) ^ 6 / 5 +
          ((1 : ℝ) / (2 * k + 3)) ^ 8 / 7 +
            ((1 : ℝ) / (2 * k + 3)) ^ 10 / (9 * (1 - ((1 : ℝ) / (2 * k + 3)) ^ 2)) := by
  have ha : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hy : 1 / (2 * ((k : ℝ) + 1) + 1) = 1 / (2 * (k : ℝ) + 3) := by ring_nf
  have hlo := log_one_add_inv_sum_le ha 4
  have hhi := log_one_add_inv_le_sum ha 4
  rw [hy] at hlo hhi
  simp only [sum_range_succ, range_zero, sum_empty, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat] at hlo hhi
  have hk3 : (0 : ℝ) < 2 * (k : ℝ) + 3 := by positivity
  have hy2 : 1 - ((1 : ℝ) / (2 * k + 3)) ^ 2 > 0 := by
    have : (1 : ℝ) / (2 * k + 3) ≤ 1 / 3 := by
      apply one_div_le_one_div_of_le (by norm_num); linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have : 0 < (1 : ℝ) / (2 * k + 3) := by positivity
    nlinarith
  unfold lebT
  set y := (1 : ℝ) / (2 * k + 3) with hydef
  have hyk : 1 / (2 * (k : ℝ) + 3) ^ 2 = y ^ 2 := by rw [hydef, div_pow, one_pow]
  have hdiv : ∀ z : ℝ, z / 2 / (2 * (k : ℝ) + 3) = z * y / 2 := fun z => by rw [hydef]; ring
  rw [hyk, hdiv]
  have hy0 : 0 < y := by positivity
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right hlo hy0.le]
  · have := mul_le_mul_of_nonneg_right hhi hy0.le
    have e : 2 * (1 / (2 * (4 : ℝ) + 1)) * y ^ (2 * 4 + 1) * (1 - y ^ 2)⁻¹ * y / 2 =
        y ^ 10 / (9 * (1 - y ^ 2)) := by
      field_simp; ring
    nlinarith [e]

/-- `1/(2k + 3)⁴ ≤ (1/(2K + 3)²) · 1/(4(k + 1)² − 1)` for `k ≥ K`. -/
theorem inv_pow_four_le {K k : ℕ} (hk : K ≤ k) :
    (1 / (2 * (k : ℝ) + 3)) ^ 4 ≤
      1 / (2 * (K : ℝ) + 3) ^ 2 * (1 / (4 * ((k : ℝ) + 1) ^ 2 - 1)) := by
  have hk' : (K : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : (1 / (2 * (k : ℝ) + 3)) ^ 2 ≤ 1 / (2 * (K : ℝ) + 3) ^ 2 := by
    rw [div_pow, one_pow]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
  have h2 : (1 / (2 * (k : ℝ) + 3)) ^ 2 ≤ 1 / (4 * ((k : ℝ) + 1) ^ 2 - 1) := by
    rw [div_pow, one_pow]
    apply one_div_le_one_div_of_le (by nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
    nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  calc (1 / (2 * (k : ℝ) + 3)) ^ 4 = (1 / (2 * (k : ℝ) + 3)) ^ 2 * (1 / (2 * (k : ℝ) + 3)) ^ 2 :=
        by ring
    _ ≤ _ := mul_le_mul h1 h2 (by positivity) (by positivity)

theorem sum_range_inv_four_sq_sub_one (K : ℕ) :
    ∑ k ∈ range K, 1 / (4 * ((k : ℝ) + 1) ^ 2 - 1) = 1 / 2 * (1 - 1 / (2 * (K : ℝ) + 1)) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_range_succ, ih]
    have h1 : 0 < 4 * ((K : ℝ) + 1) ^ 2 - 1 := by
      have : (1 : ℝ) ≤ (K : ℝ) + 1 := by linarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
      nlinarith
    have h2 : (0 : ℝ) < 2 * K + 1 := by positivity
    push_cast
    field_simp
    ring

/-- The tail of `∑ 1/(4k² − 1)`. -/
theorem hasSum_inv_four_sq_sub_one_tail (K : ℕ) :
    HasSum (fun k : ℕ => 1 / (4 * (((k + K : ℕ) : ℝ) + 1) ^ 2 - 1))
      (1 / (2 * (2 * (K : ℝ) + 1))) := by
  have h := (hasSum_nat_add_iff' K).mpr hasSum_inv_four_sq_sub_one
  have hpart := sum_range_inv_four_sq_sub_one K
  rw [hpart] at h
  convert h using 1
  have : (0 : ℝ) < 2 * K + 1 := by positivity
  field_simp
  ring

/-- `S − (π²/8 − 1) ∈ [dLoQ 40, dHiQ 40 + tail]`. -/
theorem lebT_sum_bounds :
    (5204160 / 1000000000 : ℝ) ≤ (∑' k, lebT k) - (π ^ 2 / 8 - 1) ∧
      (∑' k, lebT k) - (π ^ 2 / 8 - 1) ≤ 5206290 / 1000000000 + 3 / 8 / 83 ^ 2 / 162 := by
  set D : ℕ → ℝ := fun k => lebT k - 1 / (2 * (k : ℝ) + 3) ^ 2
  have hD : HasSum D ((∑' k, lebT k) - (π ^ 2 / 8 - 1)) :=
    summable_lebT.hasSum.sub hasSum_inv_odd_sq
  have hDnn : ∀ k, 0 ≤ D k := fun k => le_trans (by positivity) (lebT_sub_bounds k).1
  have hlo : ((dLoQ 40 : ℚ) : ℝ) ≤ ∑ k ∈ range 40, D k := by
    rw [dLoQ]
    push_cast
    exact sum_le_sum fun k _ => (lebT_sub_bounds k).1
  have hhi : ∑ k ∈ range 40, D k ≤ ((dHiQ 40 : ℚ) : ℝ) := by
    rw [dHiQ]
    push_cast
    exact sum_le_sum fun k _ => (lebT_sub_bounds k).2
  have hLo : ((5204160 / 1000000000 : ℚ) : ℝ) ≤ ((dLoQ 40 : ℚ) : ℝ) := by exact_mod_cast dLoQ_40
  have hHi : ((dHiQ 40 : ℚ) : ℝ) ≤ ((5206290 / 1000000000 : ℚ) : ℝ) := by exact_mod_cast dHiQ_40
  push_cast at hLo hHi
  constructor
  · exact hLo.trans (hlo.trans (sum_le_hasSum (range 40) (fun k _ => hDnn k) hD))
  · -- tail bound
    have htail := (hasSum_nat_add_iff' 40).mpr hD
    have hT := (hasSum_inv_four_sq_sub_one_tail 40).mul_left (3 / 8 * (1 / (2 * (40 : ℝ) + 3) ^ 2))
    have hle := hasSum_le (fun k => ?_) htail hT
    · have : 3 / 8 * (1 / (2 * (40 : ℝ) + 3) ^ 2) * (1 / (2 * (2 * (40 : ℝ) + 1))) =
          3 / 8 / 83 ^ 2 / 162 := by norm_num
      linarith
    · have hb := (lebT_sub_bounds (k + 40)).2
      set y := (1 : ℝ) / (2 * ((k + 40 : ℕ) : ℝ) + 3) with hydef
      have hy0 : 0 < y := by positivity
      have hy1 : y ≤ 1 / 83 := by
        rw [hydef]; apply one_div_le_one_div_of_le (by norm_num); push_cast
        linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      have hy2 : 0 < 1 - y ^ 2 := by nlinarith
      -- `y⁴/3 + y⁶/5 + y⁸/7 + y¹⁰/(9(1 − y²)) ≤ (3/8) y⁴`
      have hsmall : y ^ 4 / 3 + y ^ 6 / 5 + y ^ 8 / 7 + y ^ 10 / (9 * (1 - y ^ 2)) ≤
          3 / 8 * y ^ 4 := by
        have hq : y ^ 2 ≤ 1 / 6889 := by
          have := pow_le_pow_left₀ hy0.le hy1 2
          norm_num at this ⊢; linarith
        have hy4 : 0 ≤ y ^ 4 := by positivity
        have h9 : y ^ 10 / (9 * (1 - y ^ 2)) ≤ y ^ 10 / 8 := by
          apply div_le_div_of_nonneg_left (by positivity) (by norm_num); nlinarith
        have b6 : y ^ 6 ≤ y ^ 4 / 6889 := by
          have := mul_le_mul_of_nonneg_left hq hy4
          nlinarith [this]
        have b8 : y ^ 8 ≤ y ^ 4 / 6889 := by
          have h1 := mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ y ^ 6)
          nlinarith [h1]
        have b10 : y ^ 10 ≤ y ^ 4 / 6889 := by
          have h1 := mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ y ^ 8)
          nlinarith [h1]
        linarith
      have h4 := inv_pow_four_le (K := 40) (k := k + 40) (by omega)
      simp only [D]
      calc lebT (k + 40) - 1 / (2 * ((k + 40 : ℕ) : ℝ) + 3) ^ 2 ≤ 3 / 8 * y ^ 4 :=
            hb.trans hsmall
        _ ≤ 3 / 8 * (1 / (2 * ((40 : ℕ) : ℝ) + 3) ^ 2 *
            (1 / (4 * (((k + 40 : ℕ) : ℝ) + 1) ^ 2 - 1))) := by gcongr
        _ = _ := by push_cast; ring

/-! ### The constants -/

theorem euler_bounds :
    (5772105769 / 10000000000 : ℝ) ≤ eulerMascheroniConstant ∧
      eulerMascheroniConstant ≤ 5772156668 / 10000000000 := by
  obtain ⟨h1, h2⟩ := harmonic_sub_log_bounds (m := 128) (by norm_num)
  obtain ⟨hH1, hH2⟩ := harmonic_128_bounds
  have hH1' : ((54331470925 / 10000000000 : ℚ) : ℝ) ≤ (harmonic 128 : ℝ) := by exact_mod_cast hH1
  have hH2' : (harmonic 128 : ℝ) ≤ ((54331470926 / 10000000000 : ℚ) : ℝ) := by exact_mod_cast hH2
  push_cast at hH1' hH2'
  have hlog : log ((128 : ℕ) : ℝ) = 7 * log 2 := by
    rw [show ((128 : ℕ) : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]; norm_num
  rw [hlog] at h1 h2
  have := Real.log_two_gt_d9
  have := Real.log_two_lt_d9
  norm_num at h1 h2
  constructor <;> linarith

theorem log_2001_bounds :
    (7601402331 / 1000000000 : ℝ) ≤ log 2001 ∧ log 2001 ≤ 7601403381 / 1000000000 := by
  have ha : (0 : ℝ) < 2001 / 47 := by norm_num
  have hlo := log_one_add_inv_sum_le ha 1
  have hhi := log_one_add_inv_le_sum ha 1
  simp only [range_one, sum_singleton, Nat.cast_zero, mul_zero, zero_add, Nat.cast_one,
    mul_one] at hlo hhi
  have h1 : (1 : ℝ) + (2001 / 47)⁻¹ = 2048 / 2001 := by norm_num
  have h2 : log ((2048 : ℝ) / 2001) = 11 * log 2 - log 2001 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (2048 : ℝ) = 2 ^ 11 by norm_num,
      Real.log_pow]
    norm_num
  rw [h1, h2] at hlo hhi
  have := Real.log_two_gt_d9
  have := Real.log_two_lt_d9
  norm_num at hlo hhi
  constructor <;> linarith

/-! ### `L₁₀₀₀` -/

/-- **DLMF §3.11(ii)**: `L₁₀₀₀ = 4.07…`, i.e. `4.07 ≤ L₁₀₀₀ < 4.08`. -/
theorem dlmf_3_11_ii_lebesgue_1000 : 4.07 ≤ lebesgueConst 1000 ∧ lebesgueConst 1000 < 4.08 := by
  have hπ := Real.pi_pos
  have hpos : ∀ k : ℕ, 0 < 4 * ((k : ℝ) + 1) ^ 2 - 1 := fun k => by
    have : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    nlinarith
  -- termwise bounds on `H′_{2001(k+1)}`
  have hterm : ∀ k : ℕ,
      log ((k : ℝ) + 1) / 2 + (log 2001 / 2 + log 2 + eulerMascheroniConstant / 2) -
          1 / (48 * 2001 ^ 2) ≤ hprime ((k + 1) * (2 * 1000 + 1)) ∧
        hprime ((k + 1) * (2 * 1000 + 1)) ≤ log ((k : ℝ) + 1) / 2 +
          (log 2001 / 2 + log 2 + eulerMascheroniConstant / 2) + 1 / (24 * 2001 ^ 2) := by
    intro k
    have hM : 1 ≤ (k + 1) * (2 * 1000 + 1) := by omega
    obtain ⟨h1, h2⟩ := hprime_bounds hM
    have hlog : log (((k + 1) * (2 * 1000 + 1) : ℕ) : ℝ) = log ((k : ℝ) + 1) + log 2001 := by
      push_cast
      rw [Real.log_mul (by positivity) (by norm_num)]
    rw [hlog] at h1 h2
    have hM2 : (2001 : ℝ) ^ 2 ≤ (((k + 1) * (2 * 1000 + 1) : ℕ) : ℝ) ^ 2 := by
      push_cast
      have : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      nlinarith
    have hd1 : 1 / (48 * (((k + 1) * (2 * 1000 + 1) : ℕ) : ℝ) ^ 2) ≤ 1 / (48 * 2001 ^ 2) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    have hd2 : 1 / (24 * (((k + 1) * (2 * 1000 + 1) : ℕ) : ℝ) ^ 2) ≤ 1 / (24 * 2001 ^ 2) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    constructor <;> linarith
  have hL := dlmf_3_11_ii_szego 1000
  have hS := hasSum_log_div
  have hinv := hasSum_inv_four_sq_sub_one
  obtain ⟨hS1, hS2⟩ := lebT_sum_bounds
  obtain ⟨hγ1, hγ2⟩ := euler_bounds
  obtain ⟨hN1, hN2⟩ := log_2001_bounds
  have h2a := Real.log_two_gt_d9
  have h2b := Real.log_two_lt_d9
  have hπ1 := Real.pi_gt_d6
  have hπ2 := Real.pi_lt_d6
  generalize eulerMascheroniConstant = γ at hterm hγ1 hγ2
  generalize (∑' k, lebT k) = S at hS hS1 hS2
  generalize hC : log 2001 / 2 + log 2 + γ / 2 = C at hterm
  have hlo : HasSum (fun k : ℕ => 16 / π ^ 2 * (log ((k : ℝ) + 1) / 2 + C - 1 / (48 * 2001 ^ 2)) /
      (4 * ((k : ℝ) + 1) ^ 2 - 1)) (8 / π ^ 2 * (S + C - 1 / (48 * 2001 ^ 2))) := by
    convert (hS.mul_left (8 / π ^ 2)).add
      (hinv.mul_left (16 / π ^ 2 * (C - 1 / (48 * 2001 ^ 2)))) using 1
    · funext k; have := hpos k; field_simp; ring
    · ring
  have hhi : HasSum (fun k : ℕ => 16 / π ^ 2 * (log ((k : ℝ) + 1) / 2 + C + 1 / (24 * 2001 ^ 2)) /
      (4 * ((k : ℝ) + 1) ^ 2 - 1)) (8 / π ^ 2 * (S + C + 1 / (24 * 2001 ^ 2))) := by
    convert (hS.mul_left (8 / π ^ 2)).add
      (hinv.mul_left (16 / π ^ 2 * (C + 1 / (24 * 2001 ^ 2)))) using 1
    · funext k; have := hpos k; field_simp; ring
    · ring
  have hle1 := hasSum_le (fun k => div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hterm k).1 (by positivity)) (hpos k).le) hlo hL
  have hle2 := hasSum_le (fun k => div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hterm k).2 (by positivity)) (hpos k).le) hL hhi
  have hπsq1 : π ^ 2 < 3.141593 ^ 2 := by nlinarith
  have hπsq2 : 3.141592 ^ 2 < π ^ 2 := by nlinarith
  constructor
  · have key : 4.07 * π ^ 2 ≤ 8 * (S + C - 1 / (48 * 2001 ^ 2)) := by
      norm_num at hS1 hγ1 hN1 hπsq1 ⊢
      linarith
    have : (4.07 : ℝ) ≤ 8 / π ^ 2 * (S + C - 1 / (48 * 2001 ^ 2)) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      linarith
    linarith
  · have key : 8 * (S + C + 1 / (24 * 2001 ^ 2)) < 4.08 * π ^ 2 := by
      norm_num at hS2 hγ2 hN2 hπsq2 ⊢
      linarith
    have : 8 / π ^ 2 * (S + C + 1 / (24 * 2001 ^ 2)) < 4.08 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      linarith
    linarith

end Azurite.DLMF
