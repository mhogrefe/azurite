/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.NumberTheory.ZetaValues
import Azurite.DLMF.Chapter4.Section14
import Azurite.DLMF.Chapter3.Section5Romberg

/-!
# DLMF §4.19 Maclaurin Series and Laurent Series (sine, cosine, cotangent, tangent, cosecant)

* 4.19.1–4.19.2: `dlmf_4_19_1`, `dlmf_4_19_2`.
* 4.19.6 (`0 < |z| < π`): `dlmf_4_19_6`. It is proved from the Mittag-Leffler expansion of `cot`
  (Mathlib's `cot_series_rep'`), expanding each term geometrically and summing over `n` by
  `ζ(2k)` with its Bernoulli value (`hasSum_zeta_nat`). The double series is reordered by
  `hasSum_swap_of_summable_norm`.
* 4.19.3 (`|z| < π/2`): `dlmf_4_19_3`, from `tan z = cot z − 2 cot 2z`.
* 4.19.4 (`0 < |z| < π`): `dlmf_4_19_4`, from `csc z = cot(z/2) − cot z`.
* The displayed first terms: `cotCoeff_values`, `tanCoeff_values`, `cscCoeff_values`
  (with `bernoulli'_six`, `bernoulli'_eight` from §3.5).

The general term with index `n ≥ 1` of DLMF is written with `n = m + 1`, `m ≥ 0`. `B_n` is
Mathlib's `bernoulli n` (`B₁ = −1/2`, the DLMF convention).
-/

open Set Filter Topology Complex
open scoped Real Nat

namespace Azurite.DLMF

/-- **DLMF 4.19.1**: `sin z = z − z³/3! + z⁵/5! − ⋯`. -/
theorem dlmf_4_19_1 (z : ℂ) :
    HasSum (fun n : ℕ => (-1) ^ n * z ^ (2 * n + 1) / (2 * n + 1)!) (sin z) :=
  Complex.hasSum_sin z

/-- **DLMF 4.19.2**: `cos z = 1 − z²/2! + z⁴/4! − ⋯`. -/
theorem dlmf_4_19_2 (z : ℂ) : HasSum (fun n : ℕ => (-1) ^ n * z ^ (2 * n) / (2 * n)!) (cos z) :=
  Complex.hasSum_cos z

/-! ### Tools -/

/-- Reordering an absolutely convergent double series. -/
theorem hasSum_swap_of_summable_norm {f : ℕ → ℕ → ℂ} {g h : ℕ → ℂ} {a : ℂ}
    (hs : Summable fun p : ℕ × ℕ => ‖f p.1 p.2‖) (hg : ∀ n, HasSum (f n) (g n))
    (hh : ∀ m, HasSum (fun n => f n m) (h m)) (ha : HasSum g a) : HasSum h a := by
  have hF : Summable fun p : ℕ × ℕ => f p.1 p.2 := hs.of_norm
  have h1 := hF.hasSum.prod_fiberwise fun n => hg n
  rw [ha.unique h1]
  have h2 : HasSum ((fun p : ℕ × ℕ => f p.1 p.2) ∘ Equiv.prodComm ℕ ℕ)
      (∑' p : ℕ × ℕ, f p.1 p.2) := (Equiv.hasSum_iff _).mpr hF.hasSum
  exact h2.prod_fiberwise fun m => hh m

/-- `ζ(2k) = ∑_{n ≥ 1} n^{−2k}` (with its Bernoulli value), as a complex series over `n + 1`. -/
theorem hasSum_zeta_succ {k : ℕ} (hk : k ≠ 0) :
    HasSum (fun n : ℕ => (1 : ℂ) / ((n : ℂ) + 1) ^ (2 * k))
      (((-1 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (2 * k - 1) * π ^ (2 * k) * bernoulli (2 * k) /
        (2 * k)! : ℝ) : ℂ) := by
  have h := (hasSum_nat_add_iff' 1).mpr (hasSum_zeta_nat hk)
  have h0 : (2 * k) ≠ 0 := by omega
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_pow h0, div_zero,
    sub_zero, Nat.cast_add, Nat.cast_one] at h
  have := Complex.ofRealCLM.hasSum h
  convert this using 1
  · funext n; simp
  · simp

theorem mem_integerComplement_of_norm_lt_one {x : ℂ} (h0 : x ≠ 0) (h1 : ‖x‖ < 1) :
    x ∈ integerComplement := by
  rintro ⟨n, rfl⟩
  rw [Complex.norm_intCast] at h1
  have : n = 0 := by
    have : |n| < 1 := by exact_mod_cast h1
    exact Int.abs_lt_one_iff.mp this
  exact h0 (by rw [this]; simp)

theorem norm_pi_mul_int (k : ℤ) : ‖(k : ℂ) * π‖ = |(k : ℝ)| * π := by
  rw [norm_mul, Complex.norm_intCast, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]

theorem sin_ne_zero_of_norm_lt_pi {z : ℂ} (h0 : z ≠ 0) (h1 : ‖z‖ < π) : sin z ≠ 0 := by
  intro h
  obtain ⟨k, rfl⟩ := Complex.sin_eq_zero_iff.mp h
  rw [norm_pi_mul_int] at h1
  have hk : |(k : ℝ)| < 1 := by
    have := Real.pi_pos
    by_contra hc; push Not at hc; nlinarith
  have : k = 0 := Int.abs_lt_one_iff.mp (by exact_mod_cast hk)
  exact h0 (by rw [this]; simp)

theorem cos_ne_zero_of_norm_lt_pi_div_two {z : ℂ} (h1 : ‖z‖ < π / 2) : cos z ≠ 0 := by
  intro h
  obtain ⟨k, rfl⟩ := Complex.cos_eq_zero_iff.mp h
  have hn : ‖(2 * (k : ℂ) + 1) * π / 2‖ = |((2 * k + 1 : ℤ) : ℝ)| * π / 2 := by
    rw [show (2 * (k : ℂ) + 1) = ((2 * k + 1 : ℤ) : ℂ) by push_cast; ring, norm_div, norm_mul,
      Complex.norm_ofNat, Complex.norm_intCast, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
  rw [hn] at h1
  have h2 : |((2 * k + 1 : ℤ) : ℝ)| < 1 := by
    have := Real.pi_pos
    by_contra hc; push Not at hc; nlinarith
  have h3 : |2 * k + 1| < 1 := by exact_mod_cast h2
  rw [abs_lt] at h3
  omega

/-! ### Cotangent (DLMF 4.19.6) -/

/-- The coefficient of `z^{2m+1}` in 4.19.6 (`n = m + 1`):
`−(−1)^{n−1} 2^{2n} B_{2n}/(2n)!`. -/
def cotCoeff (m : ℕ) : ℚ :=
  -((-1) ^ m * 2 ^ (2 * m + 2) * bernoulli (2 * m + 2) / (2 * m + 2)!)

/-- **DLMF 4.19.6**:
`cot z = 1/z − z/3 − z³/45 − ⋯ − ((−1)^{n−1} 2^{2n} B_{2n}/(2n)!) z^{2n−1} − ⋯`,
`0 < |z| < π`. -/
theorem dlmf_4_19_6 {z : ℂ} (h0 : z ≠ 0) (h1 : ‖z‖ < π) :
    HasSum (fun m : ℕ => (cotCoeff m : ℂ) * z ^ (2 * m + 1)) (cot z - 1 / z) := by
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  obtain ⟨x, hxdef⟩ : ∃ x : ℂ, x = z / π := ⟨_, rfl⟩
  have hxn : ‖x‖ = ‖z‖ / π := by
    rw [hxdef, norm_div, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  have hx1 : ‖x‖ < 1 := by rw [hxn, div_lt_one Real.pi_pos]; exact h1
  have hx0 : x ≠ 0 := by rw [hxdef]; exact div_ne_zero h0 hπ
  have hxZ := mem_integerComplement_of_norm_lt_one hx0 hx1
  have hN : ∀ n : ℕ, (1 : ℝ) ≤ ‖((n : ℂ) + 1)‖ := fun n => by
    rw [show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
    exact_mod_cast Nat.succ_pos n
  have hN0 : ∀ n : ℕ, ((n : ℂ) + 1) ≠ 0 := fun n h => by
    have := hN n; rw [h, norm_zero] at this; linarith
  -- the Mittag-Leffler series
  have hML : HasSum (cotTerm x) (π * cot (π * x) - 1 / x) := by
    rw [cot_series_rep' hxZ]; exact (summable_cotTerm hxZ).hasSum
  set f : ℕ → ℕ → ℂ := fun n m => -2 * x ^ (2 * m + 1) / ((n : ℂ) + 1) ^ (2 * m + 2) with hf
  have hg : ∀ n, HasSum (f n) (cotTerm x n) := by
    intro n
    obtain ⟨N, hNdef⟩ : ∃ N : ℂ, N = (n : ℂ) + 1 := ⟨_, rfl⟩
    have hN1 : 1 ≤ ‖N‖ := hNdef ▸ hN n
    have hNz : N ≠ 0 := hNdef ▸ hN0 n
    have hq : ‖x ^ 2 / N ^ 2‖ < 1 := by
      rw [norm_div, norm_pow, norm_pow, div_lt_one (by positivity)]
      have : ‖x‖ ^ 2 < 1 := by nlinarith [norm_nonneg x]
      nlinarith
    have hgeo := (hasSum_geometric_of_norm_lt_one hq).mul_left (-2 * x / N ^ 2)
    have hxN : x - N ≠ 0 := fun h => by
      have : ‖x‖ = ‖N‖ := by rw [sub_eq_zero.mp h]
      linarith
    have hxN' : x + N ≠ 0 := fun h => by
      have : ‖x‖ = ‖N‖ := by rw [eq_neg_of_add_eq_zero_left h, norm_neg]
      linarith
    have hNN : N ^ 2 - x ^ 2 ≠ 0 := by
      rw [show N ^ 2 - x ^ 2 = -((x - N) * (x + N)) by ring]
      exact neg_ne_zero.mpr (mul_ne_zero hxN hxN')
    convert hgeo using 1
    · funext m
      simp only [hf]
      rw [← hNdef, div_pow, ← pow_mul, ← pow_mul]
      field_simp
      ring
    · simp only [cotTerm]
      rw [← hNdef]
      have h1q : 1 - x ^ 2 / N ^ 2 ≠ 0 := by
        rw [show 1 - x ^ 2 / N ^ 2 = (N ^ 2 - x ^ 2) / N ^ 2 by field_simp]
        exact div_ne_zero hNN (pow_ne_zero 2 hNz)
      field_simp
      ring
  set ζc : ℕ → ℂ := fun m => (((-1 : ℝ) ^ (m + 1 + 1) * (2 : ℝ) ^ (2 * (m + 1) - 1) *
    π ^ (2 * (m + 1)) * bernoulli (2 * (m + 1)) / (2 * (m + 1))! : ℝ) : ℂ) with hζc
  have hh : ∀ m, HasSum (fun n => f n m) (-2 * x ^ (2 * m + 1) * ζc m) := by
    intro m
    have := (hasSum_zeta_succ (k := m + 1) (by omega)).mul_left (-2 * x ^ (2 * m + 1))
    convert this using 1
    funext n
    simp only [hf]
    rw [show 2 * (m + 1) = 2 * m + 2 by ring]
    ring
  have hs : Summable fun p : ℕ × ℕ => ‖f p.1 p.2‖ := by
    have hA : Summable fun n : ℕ => 2 / ((n : ℝ) + 1) ^ 2 := by
      have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
      simpa [div_eq_mul_inv] using this.mul_left 2
    have hB : Summable fun m : ℕ => ‖x‖ ^ (2 * m + 1) := by
      have := (summable_geometric_of_lt_one (by positivity : 0 ≤ ‖x‖ ^ 2)
        (by nlinarith [norm_nonneg x])).mul_left ‖x‖
      convert this using 1
      funext m
      ring
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_)
      (hA.mul_of_nonneg hB (fun _ => by positivity) (fun _ => by positivity))
    simp only [hf, norm_div, norm_mul, norm_neg, norm_pow, Complex.norm_ofNat]
    have h1N := hN p.1
    have hpow : ‖((p.1 : ℂ) + 1)‖ ^ 2 ≤ ‖((p.1 : ℂ) + 1)‖ ^ (2 * p.2 + 2) :=
      pow_le_pow_right₀ h1N (by omega)
    have hnn : ‖((p.1 : ℂ) + 1)‖ = (p.1 : ℝ) + 1 := by
      rw [show ((p.1 : ℂ) + 1) = ((p.1 + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
      push_cast; ring
    rw [hnn] at hpow ⊢
    rw [div_mul_eq_mul_div, mul_comm (2 : ℝ)]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity) hpow
  have hsw := hasSum_swap_of_summable_norm hs hg hh hML
  have hfin := hsw.mul_left (1 / (π : ℂ))
  have hlhs : 1 / (π : ℂ) * (π * cot (π * x) - 1 / x) = cot z - 1 / z := by
    have : (π : ℂ) * x = z := by rw [hxdef]; field_simp
    rw [this, hxdef]
    field_simp
  rw [hlhs] at hfin
  convert hfin using 1
  funext m
  simp only [hζc, cotCoeff, hxdef]
  rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega, show 2 * (m + 1) = 2 * m + 2 by ring]
  push_cast
  rw [div_pow, show (π : ℂ) ^ (2 * m + 2) = π * π ^ (2 * m + 1) by ring,
    show (2 : ℂ) ^ (2 * m + 2) = 2 * 2 ^ (2 * m + 1) by ring]
  have hπm : (π : ℂ) ^ (2 * m + 1) ≠ 0 := pow_ne_zero _ hπ
  field_simp
  ring

/-! ### Values of Bernoulli numbers and the displayed coefficients -/

theorem bernoulli_values : bernoulli 2 = 1 / 6 ∧ bernoulli 4 = -1 / 30 ∧ bernoulli 6 = 1 / 42 ∧
    bernoulli 8 = -1 / 30 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num)]
  · exact bernoulli'_two
  · exact bernoulli'_four
  · exact bernoulli'_six
  · exact bernoulli'_eight

/-- **DLMF 4.19.6**, the displayed terms: `−z/3 − z³/45 − 2z⁵/945`. -/
theorem cotCoeff_values : cotCoeff 0 = -1 / 3 ∧ cotCoeff 1 = -1 / 45 ∧ cotCoeff 2 = -2 / 945 := by
  obtain ⟨b2, b4, b6, -⟩ := bernoulli_values
  refine ⟨?_, ?_, ?_⟩ <;> simp [cotCoeff, b2, b4, b6, Nat.factorial] <;> norm_num

/-! ### Tangent (DLMF 4.19.3) and cosecant (DLMF 4.19.4) -/

/-- The coefficient of `z^{2m+1}` in 4.19.3 (`n = m + 1`):
`(−1)^{n−1} 2^{2n} (2^{2n} − 1) B_{2n}/(2n)!`. -/
def tanCoeff (m : ℕ) : ℚ :=
  (-1) ^ m * 2 ^ (2 * m + 2) * (2 ^ (2 * m + 2) - 1) * bernoulli (2 * m + 2) / (2 * m + 2)!

/-- The coefficient of `z^{2m+1}` in 4.19.4 (`n = m + 1`):
`(−1)^{n−1} 2 (2^{2n−1} − 1) B_{2n}/(2n)!`. -/
def cscCoeff (m : ℕ) : ℚ :=
  (-1) ^ m * 2 * (2 ^ (2 * m + 1) - 1) * bernoulli (2 * m + 2) / (2 * m + 2)!

/-- **DLMF 4.19.3**: `tan z = z + z³/3 + 2z⁵/15 + 17z⁷/315 + ⋯`, `|z| < π/2`. -/
theorem dlmf_4_19_3 {z : ℂ} (h1 : ‖z‖ < π / 2) :
    HasSum (fun m : ℕ => (tanCoeff m : ℂ) * z ^ (2 * m + 1)) (tan z) := by
  rcases eq_or_ne z 0 with rfl | h0
  · simp
  have h2 : ‖2 * z‖ < π := by rw [norm_mul, Complex.norm_ofNat]; linarith
  have h20 : 2 * z ≠ 0 := mul_ne_zero two_ne_zero h0
  have hA := dlmf_4_19_6 h0 (by linarith [Real.pi_pos])
  have hB := (dlmf_4_19_6 h20 h2).mul_left 2
  have hs := sin_ne_zero_of_norm_lt_pi h0 (by linarith [Real.pi_pos])
  have hc := cos_ne_zero_of_norm_lt_pi_div_two h1
  have hid : tan z = (cot z - 1 / z) - 2 * (cot (2 * z) - 1 / (2 * z)) := by
    rw [tan_eq_sin_div_cos, cot_eq_cos_div_sin, cot_eq_cos_div_sin, sin_two_mul, cos_two_mul]
    field_simp
    linear_combination z * sin_sq_add_cos_sq z
  rw [hid]
  convert hA.sub hB using 1
  funext m
  simp only [tanCoeff, cotCoeff]
  push_cast
  rw [mul_pow, show (2 : ℂ) ^ (2 * m + 1) = 2 ^ (2 * m + 2) / 2 by
    rw [pow_succ _ (2 * m + 1)]; ring]
  field_simp
  ring

/-- **DLMF 4.19.3**, the displayed terms `z + z³/3 + 2z⁵/15 + 17z⁷/315`. -/
theorem tanCoeff_values : tanCoeff 0 = 1 ∧ tanCoeff 1 = 1 / 3 ∧ tanCoeff 2 = 2 / 15 ∧
    tanCoeff 3 = 17 / 315 := by
  obtain ⟨b2, b4, b6, b8⟩ := bernoulli_values
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [tanCoeff, b2, b4, b6, b8, Nat.factorial] <;> norm_num

/-- **DLMF 4.19.4**: `csc z = 1/z + z/6 + 7z³/360 + 31z⁵/15120 + ⋯`, `0 < |z| < π`. -/
theorem dlmf_4_19_4 {z : ℂ} (h0 : z ≠ 0) (h1 : ‖z‖ < π) :
    HasSum (fun m : ℕ => (cscCoeff m : ℂ) * z ^ (2 * m + 1)) (cscC z - 1 / z) := by
  have h2 : ‖z / 2‖ < π := by rw [norm_div, Complex.norm_ofNat]; linarith [Real.pi_pos]
  have h20 : z / 2 ≠ 0 := div_ne_zero h0 two_ne_zero
  have hA := dlmf_4_19_6 h20 h2
  have hB := dlmf_4_19_6 h0 h1
  have hs := sin_ne_zero_of_norm_lt_pi h0 h1
  have hs2 : sin (z / 2) ≠ 0 := sin_ne_zero_of_norm_lt_pi h20 h2
  have hc2 : cos (z / 2) ≠ 0 := cos_ne_zero_of_norm_lt_pi_div_two (by
    rw [norm_div, Complex.norm_ofNat]; linarith)
  have hid : cscC z - 1 / z = (cot (z / 2) - 1 / (z / 2)) - (cot z - 1 / z) := by
    have hz : z = 2 * (z / 2) := by ring
    rw [cscC, cot_eq_cos_div_sin, cot_eq_cos_div_sin, hz, sin_two_mul, cos_two_mul]
    rw [← hz]
    field_simp
    ring
  rw [hid]
  convert hA.sub hB using 1
  funext m
  simp only [cscCoeff, cotCoeff]
  push_cast
  rw [div_pow, show (2 : ℂ) ^ (2 * m + 2) = 2 ^ (2 * m + 1) * 2 by rw [pow_succ]]
  field_simp
  ring

/-- **DLMF 4.19.4**, the displayed terms `z/6 + 7z³/360 + 31z⁵/15120`. -/
theorem cscCoeff_values : cscCoeff 0 = 1 / 6 ∧ cscCoeff 1 = 7 / 360 ∧ cscCoeff 2 = 31 / 15120 := by
  obtain ⟨b2, b4, b6, -⟩ := bernoulli_values
  refine ⟨?_, ?_, ?_⟩ <;> simp [cscCoeff, b2, b4, b6, Nat.factorial] <;> norm_num

end Azurite.DLMF
