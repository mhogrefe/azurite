/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section11Euler
import Azurite.Rounding.IntNearest

/-!
# DLMF §3.1(i): floating-point arithmetic

* **3.1.1–3.1.2** (`machineNum`): the machine numbers `ℝ_fl`, given as `0` and
  `(−1)^s 2^E ∑_{j<p} b_j 2^{−j}` with `b₀ = 1`.
  * `mem_machineNum_iff`: equivalently `±M·2^E/2^{p−1}` with `2^{p−1} ≤ M < 2^p`, by binary digits
    `binDigit`.
  * A nonzero machine number with exponent `E` lies in `[2^E, 2^{E+1})` (`machine_abs_bounds`).
* The machine epsilon `ε_M = 2^{1−p}` (`machineEps`) is the distance from `1` to the next larger
  machine number (`machineEps_isLeast`, `p ≥ 2`). The machine precision is `½ε_M = 2^{−p}`
  (`machineEps_half`).
* **3.1.3** (`dlmf_3_1_3`): `N_min = 2^{E_min} ≤ |x| ≤ 2^{E_max+1}(1 − 2^{−p}) = N_max` for nonzero
  machine numbers, both attained (`machineNmin_mem`).
* **The IEEE binary interchange formats** (`binary32`, `binary64`, `binary128`).
  * Figure 3.1.1 (`dlmf_figure_3_1_1`): 8, 11, 15 exponent bits, `E_max = 2^{N−p−1} − 1`,
    `E_min = 1 − E_max`.
  * The machine precisions `0.596 × 10^{−7}`, `0.111 × 10^{−15}`, `0.963 × 10^{−34}`, rendered by
    `AzRat.toSci` in the kernel (`dlmf_3_1_ii_precision_decimals`, `dlmf_3_1_ii_precisions`).
* **Rounding, 3.1.4–3.1.5**: `x₋` (`roundChop`) and `x₊ = x₋ + ε_M 2^E` (`roundChopUp`).
  * Both are machine numbers in range (`roundChop_mem`).
  * They are bridged to Azurite's rounding library: rounding down to `precisionSet 2 p` is chopping
    (`roundFloor_eq_roundChop`). Rounding to nearest (ties to even) gives `x₋` or `x₊`, whichever is
    nearer (`roundNearest_spec`), and negative numbers round like `−x` (`roundNearest_neg`).
* **The relative errors**.
  * Chopping: `< ε_M/(1 + ε_M) < ε_M` (`roundChop_rel_err`, `roundChop_rel_err_lt`); the supremum
    `ε_M/(1 + ε_M)` is not attained (`roundChop_rel_err_sharp`).
  * Rounding to nearest: `≤ 2^{−p}/(1 + 2^{−p}) < 2^{−p}` (`roundNearest_rel_err`), attained at
    `x = 1 + 2^{−p}` (`roundNearest_rel_err_attained`).
  * DLMF's "maximum relative error `ε_M`" and "maximum relative error equal to the machine precision
    `2^{−p}`" are therefore bounds, not maxima (`docs/dlmf_errata.md`).
-/

open Finset

namespace Azurite.DLMF

/-! ### §3.1(i) Machine numbers -/

/-- **DLMF 3.1.2**: the machine numbers `ℝ_fl` with `p` significant bits and exponents in
`[E_min, E_max]`: `0` and the numbers `(−1)^s 2^E ∑_{j<p} b_j 2^{−j}` with `b_0 = 1`,
`b_j ∈ {0, 1}`. -/
def machineNum (p : ℕ) (Emin Emax : ℤ) : Set ℝ :=
  {0} ∪ {x | ∃ (s : ℕ) (E : ℤ) (b : ℕ → ℕ), s ≤ 1 ∧ Emin ≤ E ∧ E ≤ Emax ∧ b 0 = 1 ∧
    (∀ j, b j ≤ 1) ∧ x = (-1) ^ s * 2 ^ E * ∑ j ∈ range p, (b j : ℝ) * 2 ^ (-(j : ℤ))}

/-- The binary digits of `m` (most significant first, `p` of them): `b_j = ⌊m/2^{p−1−j}⌋ mod 2`. -/
def binDigit (p m j : ℕ) : ℕ := if j < p then m / 2 ^ (p - 1 - j) % 2 else 0

theorem sum_digit_mul_pow (m : ℕ) : ∀ p : ℕ,
    ∑ i ∈ range p, (m / 2 ^ i % 2) * 2 ^ i = m % 2 ^ p
  | 0 => by simp [Nat.mod_one]
  | p + 1 => by rw [sum_range_succ, sum_digit_mul_pow m p, Nat.mod_pow_succ]; ring

theorem sum_two_pow (p : ℕ) : ∑ i ∈ range p, 2 ^ i + 1 = 2 ^ p := by
  induction p with
  | zero => simp
  | succ p ih => rw [sum_range_succ, pow_succ]; omega

/-- The integer significand `M = ∑_{j<p} b_j 2^{p−1−j}` of the bits `b`. -/
def bitsVal (p : ℕ) (b : ℕ → ℕ) : ℕ := ∑ j ∈ range p, b j * 2 ^ (p - 1 - j)

theorem bitsVal_binDigit {p m : ℕ} (hm : m < 2 ^ p) : bitsVal p (binDigit p m) = m := by
  unfold bitsVal
  rw [show ∑ j ∈ range p, binDigit p m j * 2 ^ (p - 1 - j) =
      ∑ j ∈ range p, (fun i => m / 2 ^ i % 2 * 2 ^ i) (p - 1 - j) from
      sum_congr rfl fun j hj => by simp only [binDigit, mem_range.mp hj, ↓reduceIte],
    sum_range_reflect (fun i => m / 2 ^ i % 2 * 2 ^ i) p, sum_digit_mul_pow, Nat.mod_eq_of_lt hm]

theorem binDigit_le (p m j : ℕ) : binDigit p m j ≤ 1 := by
  unfold binDigit; split_ifs <;> omega

theorem binDigit_zero {p m : ℕ} (hp : 1 ≤ p) (h1 : 2 ^ (p - 1) ≤ m) (h2 : m < 2 ^ p) :
    binDigit p m 0 = 1 := by
  have hpow : 2 ^ p = 2 * 2 ^ (p - 1) := by rw [← pow_succ']; congr 1; omega
  simp only [binDigit, show 0 < p by omega, ↓reduceIte, Nat.sub_zero]
  rw [Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)]

theorem bitsVal_bounds {p : ℕ} (hp : 1 ≤ p) {b : ℕ → ℕ} (h0 : b 0 = 1) (hb : ∀ j, b j ≤ 1) :
    2 ^ (p - 1) ≤ bitsVal p b ∧ bitsVal p b < 2 ^ p := by
  unfold bitsVal
  constructor
  · obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    rw [sum_range_succ', h0]
    simp
  · calc ∑ j ∈ range p, b j * 2 ^ (p - 1 - j) ≤ ∑ j ∈ range p, 2 ^ (p - 1 - j) :=
          sum_le_sum fun j _ => by nlinarith [hb j, Nat.one_le_two_pow (n := p - 1 - j)]
      _ = ∑ j ∈ range p, 2 ^ j := sum_range_reflect (fun i => 2 ^ i) p
      _ < 2 ^ p := by have := sum_two_pow p; omega

theorem sum_bits_eq (p : ℕ) (b : ℕ → ℕ) :
    ∑ j ∈ range p, (b j : ℝ) * 2 ^ (-(j : ℤ)) = (bitsVal p b : ℝ) / 2 ^ (p - 1) := by
  unfold bitsVal
  push_cast
  rw [sum_div]
  refine sum_congr rfl fun j hj => ?_
  have hj := mem_range.mp hj
  rw [mul_div_assoc]
  congr 1
  have e : (2 : ℝ) ^ (p - 1) = 2 ^ (p - 1 - j) * 2 ^ j := by
    rw [← pow_add]; congr 1; omega
  rw [e, zpow_neg, zpow_natCast]
  field_simp

/-- **Machine numbers by integer significands**: `x ≠ 0` is a machine number iff
`x = ±M 2^E/2^{p−1}` with `2^{p−1} ≤ M < 2^p` and `E_min ≤ E ≤ E_max` (3.1.1). -/
theorem mem_machineNum_iff {p : ℕ} (hp : 1 ≤ p) {Emin Emax : ℤ} {x : ℝ} (hx : x ≠ 0) :
    x ∈ machineNum p Emin Emax ↔ ∃ (s : ℕ) (E : ℤ) (M : ℕ), s ≤ 1 ∧ Emin ≤ E ∧ E ≤ Emax ∧
      2 ^ (p - 1) ≤ M ∧ M < 2 ^ p ∧ x = (-1) ^ s * M * 2 ^ E / 2 ^ (p - 1) := by
  constructor
  · rintro (h | ⟨s, E, b, hs, h1, h2, h0, hb, rfl⟩)
    · exact absurd h hx
    obtain ⟨l, u⟩ := bitsVal_bounds hp h0 hb
    refine ⟨s, E, bitsVal p b, hs, h1, h2, l, u, ?_⟩
    rw [sum_bits_eq]; ring
  · rintro ⟨s, E, M, hs, h1, h2, l, u, rfl⟩
    refine Or.inr ⟨s, E, binDigit p M, hs, h1, h2, binDigit_zero hp l u, binDigit_le p M, ?_⟩
    rw [sum_bits_eq, bitsVal_binDigit u]; ring

theorem abs_of_machine (s : ℕ) (M : ℕ) (E : ℤ) (p : ℕ) :
    |(-1 : ℝ) ^ s * M * 2 ^ E / 2 ^ (p - 1)| = M * 2 ^ E / 2 ^ (p - 1) := by
  rw [abs_div, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast,
    abs_of_pos (by positivity), abs_of_pos (by positivity)]

/-- A nonzero machine number with exponent `E` satisfies `2^E ≤ |x| < 2^{E+1}`. -/
theorem machine_abs_bounds {p M : ℕ} (hp : 1 ≤ p) (l : 2 ^ (p - 1) ≤ M) (u : M < 2 ^ p) (E : ℤ) :
    (2 : ℝ) ^ E ≤ M * 2 ^ E / 2 ^ (p - 1) ∧ (M : ℝ) * 2 ^ E / 2 ^ (p - 1) < 2 ^ (E + 1) := by
  have hpow : (2 : ℝ) ^ p = 2 * 2 ^ (p - 1) := by rw [← pow_succ']; congr 1; omega
  have l' : (2 : ℝ) ^ (p - 1) ≤ M := by exact_mod_cast l
  have u' : (M : ℝ) < 2 ^ p := by exact_mod_cast u
  have hE : (0 : ℝ) < 2 ^ E := by positivity
  constructor
  · rw [le_div_iff₀ (by positivity)]; nlinarith
  · rw [div_lt_iff₀ (by positivity), zpow_add_one₀ two_ne_zero]; nlinarith

/-- The machine epsilon `ε_M = 2^{1−p}`. -/
noncomputable def machineEps (p : ℕ) : ℝ := 2 ^ (1 - (p : ℤ))

/-- The machine precision `ε_M/2 = 2^{−p}`. -/
theorem machineEps_half (p : ℕ) : machineEps p / 2 = 2 ^ (-(p : ℤ)) := by
  rw [machineEps, div_eq_mul_inv, ← zpow_neg_one, ← zpow_add₀ two_ne_zero]; ring_nf

theorem machineEps_eq {p : ℕ} (hp : 1 ≤ p) : machineEps p = 1 / 2 ^ (p - 1) := by
  rw [machineEps, show (1 : ℤ) - p = -((p - 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast,
    one_div]

/-- **The machine epsilon**: `1 + ε_M` is the least machine number exceeding `1`
(`p ≥ 2`, `E_min ≤ 0 ≤ E_max`). -/
theorem machineEps_isLeast {p : ℕ} (hp : 2 ≤ p) {Emin Emax : ℤ} (h1 : Emin ≤ 0) (h2 : 0 ≤ Emax) :
    IsLeast {y | y ∈ machineNum p Emin Emax ∧ 1 < y} (1 + machineEps p) := by
  have hp1 : 1 ≤ p := by omega
  have hP : (0 : ℝ) < 2 ^ (p - 1) := by positivity
  have hpow : (2 : ℕ) ^ p = 2 * 2 ^ (p - 1) := by rw [← pow_succ']; congr 1; omega
  have hge : 2 ≤ 2 ^ (p - 1) := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ (p - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [machineEps_eq hp1]
  constructor
  · refine ⟨(mem_machineNum_iff hp1 (by positivity)).mpr ⟨0, 0, 2 ^ (p - 1) + 1, by norm_num, h1,
      h2, by omega, by omega, ?_⟩, ?_⟩
    · push_cast; field_simp
    · have : (0 : ℝ) < 1 / 2 ^ (p - 1) := by positivity
      linarith
  · rintro y ⟨hy, hy1⟩
    obtain ⟨s, E, M, hs, -, -, l, u, rfl⟩ := (mem_machineNum_iff hp1 (by linarith)).mp hy
    obtain ⟨b1, b2⟩ := machine_abs_bounds hp1 l u E
    have hs0 : s = 0 := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hs with h | h
      · exact h
      · exfalso; rw [h] at hy1
        have : (0 : ℝ) ≤ M * 2 ^ E / 2 ^ (p - 1) := by positivity
        have e : (-1 : ℝ) ^ 1 * M * 2 ^ E / 2 ^ (p - 1) = -(M * 2 ^ E / 2 ^ (p - 1)) := by ring
        linarith
    subst hs0
    simp only [pow_zero, one_mul] at hy1 ⊢
    rcases lt_trichotomy E 0 with hE | rfl | hE
    · exfalso
      have : (2 : ℝ) ^ (E + 1) ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
      linarith
    · simp only [zpow_zero, mul_one] at hy1 ⊢
      rw [one_lt_div hP] at hy1
      have hM : 2 ^ (p - 1) + 1 ≤ M := by exact_mod_cast hy1
      rw [show (1 : ℝ) + 1 / 2 ^ (p - 1) = (2 ^ (p - 1) + 1) / 2 ^ (p - 1) by field_simp]
      gcongr
      exact_mod_cast hM
    · have h2E : (2 : ℝ) ≤ 2 ^ E := by
        calc (2 : ℝ) = 2 ^ (1 : ℤ) := by norm_num
          _ ≤ 2 ^ E := zpow_le_zpow_right₀ (by norm_num) hE
      have : 1 / (2 : ℝ) ^ (p - 1) ≤ 1 := by
        rw [div_le_one hP]; exact one_le_pow₀ (by norm_num)
      linarith

/-- `N_min = 2^{E_min}`. -/
noncomputable def machineNmin (Emin : ℤ) : ℝ := 2 ^ Emin

/-- `N_max = 2^{E_max+1}(1 − 2^{−p})`. -/
noncomputable def machineNmax (p : ℕ) (Emax : ℤ) : ℝ := 2 ^ (Emax + 1) * (1 - 1 / 2 ^ p)

/-- **DLMF 3.1.3**: `N_min ≤ |x| ≤ N_max` for every nonzero machine number. -/
theorem dlmf_3_1_3 {p : ℕ} (hp : 1 ≤ p) {Emin Emax : ℤ} {x : ℝ} (hx : x ∈ machineNum p Emin Emax)
    (hx0 : x ≠ 0) : machineNmin Emin ≤ |x| ∧ |x| ≤ machineNmax p Emax := by
  obtain ⟨s, E, M, hs, h1, h2, l, u, rfl⟩ := (mem_machineNum_iff hp hx0).mp hx
  rw [abs_of_machine s]
  obtain ⟨b1, -⟩ := machine_abs_bounds hp l u E
  have hpow : (2 : ℝ) ^ p = 2 * 2 ^ (p - 1) := by rw [← pow_succ']; congr 1; omega
  constructor
  · exact (zpow_le_zpow_right₀ (by norm_num) h1).trans b1
  · have hM : (M : ℝ) ≤ 2 ^ p - 1 := by
      have : M + 1 ≤ 2 ^ p := u
      have : (M : ℝ) + 1 ≤ 2 ^ p := by exact_mod_cast this
      linarith
    have hE : (2 : ℝ) ^ E ≤ 2 ^ Emax := zpow_le_zpow_right₀ (by norm_num) h2
    rw [machineNmax, zpow_add_one₀ two_ne_zero, div_le_iff₀ (by positivity)]
    have e : 2 ^ Emax * 2 * (1 - 1 / (2 : ℝ) ^ p) * 2 ^ (p - 1) = (2 ^ p - 1) * 2 ^ Emax := by
      rw [hpow]; field_simp
    rw [e]
    have hp0 : (0 : ℝ) ≤ 2 ^ p - 1 := by linarith [one_le_pow₀ (n := p) (by norm_num : (1 : ℝ) ≤ 2)]
    calc (M : ℝ) * 2 ^ E ≤ (2 ^ p - 1) * 2 ^ E := by gcongr
      _ ≤ (2 ^ p - 1) * 2 ^ Emax := by gcongr

/-- `N_min` and `N_max` are machine numbers (so the bounds of 3.1.3 are attained). -/
theorem machineNmin_mem {p : ℕ} (hp : 1 ≤ p) {Emin Emax : ℤ} (h : Emin ≤ Emax) :
    machineNmin Emin ∈ machineNum p Emin Emax ∧ machineNmax p Emax ∈ machineNum p Emin Emax := by
  have hpow : (2 : ℕ) ^ p = 2 * 2 ^ (p - 1) := by rw [← pow_succ']; congr 1; omega
  have hge : 1 ≤ 2 ^ (p - 1) := Nat.one_le_two_pow
  constructor
  · refine (mem_machineNum_iff hp (by unfold machineNmin; positivity)).mpr
      ⟨0, Emin, 2 ^ (p - 1), by norm_num, le_rfl, h, le_rfl, by omega, ?_⟩
    rw [machineNmin]; push_cast; field_simp
  · have hpowR : (2 : ℝ) ^ p = 2 * 2 ^ (p - 1) := by exact_mod_cast hpow
    have hne : machineNmax p Emax ≠ 0 := by
      unfold machineNmax
      have : 1 / (2 : ℝ) ^ p < 1 := by
        rw [div_lt_one (by positivity), hpowR]
        have : (1 : ℝ) ≤ 2 ^ (p - 1) := one_le_pow₀ (by norm_num)
        linarith
      have : (0 : ℝ) < 2 ^ (Emax + 1) := by positivity
      nlinarith
    refine (mem_machineNum_iff hp hne).mpr ⟨0, Emax, 2 ^ p - 1, by norm_num, h, le_rfl, by omega,
      by omega, ?_⟩
    rw [machineNmax, Nat.cast_sub (Nat.one_le_two_pow), zpow_add_one₀ two_ne_zero]
    push_cast
    rw [hpowR]
    field_simp

/-! ### §3.1(ii) The IEEE binary interchange formats -/

/-- A binary interchange format: width `N` in bits, precision `p`, exponent range. -/
structure BinaryFormat where
  /-- The format width in bits. -/
  N : ℕ
  /-- The number of significant bits. -/
  p : ℕ
  /-- The least exponent. -/
  Emin : ℤ
  /-- The greatest exponent. -/
  Emax : ℤ
  deriving DecidableEq

/-- binary32 (previously single precision). -/
def binary32 : BinaryFormat := ⟨32, 24, -126, 127⟩
/-- binary64 (previously double precision). -/
def binary64 : BinaryFormat := ⟨64, 53, -1022, 1023⟩
/-- binary128 (previously quad precision). -/
def binary128 : BinaryFormat := ⟨128, 113, -16382, 16383⟩

/-- **Figure 3.1.1**: one sign bit, `p − 1` fraction bits and `N − p` exponent bits (8, 11, 15),
with `E_max = 2^{N−p−1} − 1` and `E_min = 1 − E_max` (the biased exponent codes `1, …, 2^{N−p} − 2`;
the two extreme codes are reserved). -/
theorem dlmf_figure_3_1_1 :
    (binary32.N - binary32.p, binary64.N - binary64.p, binary128.N - binary128.p) = (8, 11, 15) ∧
      ∀ f ∈ [binary32, binary64, binary128], 1 + (f.p - 1) + (f.N - f.p) = f.N ∧
        f.Emax = 2 ^ (f.N - f.p - 1) - 1 ∧ f.Emin = 1 - f.Emax := by
  decide

set_option maxRecDepth 100000 in
/-- **"The respective machine precisions are `0.596 × 10^{−7}`, `0.111 × 10^{−15}` and
`0.963 × 10^{−34}`"**: `2^{−24}`, `2^{−53}`, `2^{−113}` rendered exactly by `AzRat.toSci`. -/
theorem dlmf_3_1_ii_precision_decimals :
    (ratDecimalPlaces (1 / 2 ^ binary32.p) 10, ratDecimalPlaces (1 / 2 ^ binary64.p) 18,
        ratDecimalPlaces (1 / 2 ^ binary128.p) 37) =
      (some "0.0000000596", some "0.000000000000000111",
        some "0.0000000000000000000000000000000000963") := by
  decide +kernel

/-- The machine precisions to three significant figures. -/
theorem dlmf_3_1_ii_precisions :
    |machineEps binary32.p / 2 - 0.596e-7| < 0.0005e-7 ∧
      |machineEps binary64.p / 2 - 0.111e-15| < 0.0005e-15 ∧
      |machineEps binary128.p / 2 - 0.963e-34| < 0.0005e-34 := by
  simp only [machineEps_half, binary32, binary64, binary128]
  norm_num [abs_lt]

/-! ### §3.1(iii) Rounding -/

open RoundingTarget

theorem precScale_two_pos (p : ℕ) (x : ℝ) : 0 < precScale 2 p x := by
  unfold precScale; positivity

/-- The local scale `2^{E−p+1} = ε_M 2^E`, `E = ⌊log₂ x⌋`, of the machine numbers near `x > 0`. -/
theorem precScale_eq {p : ℕ} {x : ℝ} (hx : 0 < x) :
    precScale 2 p x = machineEps p * 2 ^ Int.log 2 x := by
  rw [precScale, abs_of_pos hx, machineEps, ← zpow_add₀ two_ne_zero]
  push_cast
  ring_nf

/-- **3.1.5**, `x₋`: chopping, `(1.b₁ ⋯ b_{p−1}) 2^E`. -/
noncomputable def roundChop (p : ℕ) (x : ℝ) : ℝ := ⌊x / precScale 2 p x⌋ * precScale 2 p x

/-- **3.1.5**, `x₊ = x₋ + ε_M 2^E`. -/
noncomputable def roundChopUp (p : ℕ) (x : ℝ) : ℝ := roundChop p x + precScale 2 p x

/-- The lattice facts behind 3.1.4–3.1.5 for `x > 0` with `E = ⌊log₂ x⌋`, `u = ε_M 2^E`:
`2^E = 2^{p−1}u` and `2^{p−1} ≤ x/u < 2^p`. -/
theorem chop_lattice {p : ℕ} (hp : 1 ≤ p) {x : ℝ} (hx : 0 < x) :
    (2 : ℝ) ^ Int.log 2 x = 2 ^ (p - 1) * precScale 2 p x ∧
      (2 : ℝ) ^ (p - 1) ≤ x / precScale 2 p x ∧ x / precScale 2 p x < 2 ^ p := by
  have h1 := Int.zpow_log_le_self (b := 2) (by norm_num) hx
  have h2 := Int.lt_zpow_succ_log_self (b := 2) (by norm_num) x
  push_cast at h1 h2
  have hu : 0 < precScale 2 p x := precScale_two_pos p x
  have e : (2 : ℝ) ^ Int.log 2 x = 2 ^ (p - 1) * precScale 2 p x := by
    rw [precScale_eq hx, machineEps_eq hp]; field_simp
  refine ⟨e, ?_, ?_⟩
  · rw [le_div_iff₀ hu, ← e]; exact h1
  · rw [div_lt_iff₀ hu, show (2 : ℝ) ^ p = 2 * 2 ^ (p - 1) by
      rw [← pow_succ']; congr 1; omega, mul_assoc, ← e, ← zpow_one_add₀ two_ne_zero, add_comm]
    exact h2

/-- Rounding down to the `p`-bit numbers (Azurite's `precisionSet 2 p`) is chopping. -/
theorem roundFloor_eq_roundChop (p : ℕ) [NeZero p] {x : ℝ} (hx : 0 < x) :
    (RoundingTarget.round (precisionSet 2 p) .Floor x).val = ((roundChop p x : ℝ) : EReal) := by
  rw [val_round_precisionSet .Floor x hx.ne', roundChop]
  have h := toInt_eq_of_val (val_roundFloor_intSet (x / precScale 2 p x)).symm
  rw [show RoundingTarget.round intSet .Floor (x / precScale 2 p x) =
      roundFloor intSet (x / precScale 2 p x)
    from rfl, h]

/-- `2^E ≤ x₋ ≤ x < x₊` for `x > 0`. -/
theorem roundChop_bounds {p : ℕ} (hp : 1 ≤ p) {x : ℝ} (hx : 0 < x) :
    (2 : ℝ) ^ Int.log 2 x ≤ roundChop p x ∧ roundChop p x ≤ x ∧ x < roundChopUp p x := by
  obtain ⟨e, l, -⟩ := chop_lattice hp hx
  have hu : 0 < precScale 2 p x := precScale_two_pos p x
  set u := precScale 2 p x
  have hfl : (2 : ℝ) ^ (p - 1) ≤ ⌊x / u⌋ := by
    have : ((2 ^ (p - 1) : ℕ) : ℤ) ≤ ⌊x / u⌋ := Int.le_floor.mpr (by push_cast; exact l)
    exact_mod_cast this
  refine ⟨?_, ?_, ?_⟩
  · rw [e, roundChop]; exact mul_le_mul_of_nonneg_right hfl hu.le
  · rw [roundChop, ← le_div_iff₀ hu]; exact Int.floor_le _
  · rw [roundChopUp, roundChop, ← add_one_mul, ← div_lt_iff₀ hu]; exact Int.lt_floor_add_one _

/-- **Chopping**: the relative error is less than `ε_M/(1 + ε_M)`, hence less than `ε_M`. -/
theorem roundChop_rel_err {p : ℕ} (hp : 1 ≤ p) {x : ℝ} (hx : 0 < x) :
    0 ≤ (x - roundChop p x) / x ∧
      (x - roundChop p x) / x < machineEps p / (1 + machineEps p) := by
  obtain ⟨b1, b2, b3⟩ := roundChop_bounds hp hx
  have hu := precScale_eq (p := p) hx
  have hE : (0 : ℝ) < 2 ^ Int.log 2 x := by positivity
  have hε : 0 < machineEps p := by unfold machineEps; positivity
  rw [roundChopUp, hu] at b3
  constructor
  · exact div_nonneg (by linarith) hx.le
  · rw [div_lt_div_iff₀ hx (by linarith)]
    -- `(x − X)(1 + ε) < ε x` ⟸ `x − X < εE ≤ εX`
    nlinarith [mul_le_mul_of_nonneg_left b1 hε.le]

theorem roundChop_rel_err_lt {p : ℕ} (hp : 1 ≤ p) {x : ℝ} (hx : 0 < x) :
    (x - roundChop p x) / x < machineEps p := by
  have hε : 0 < machineEps p := by unfold machineEps; positivity
  refine (roundChop_rel_err hp hx).2.trans ?_
  rw [div_lt_iff₀ (by linarith)]; nlinarith

/-- **Rounding to nearest** (Azurite's `RoundingTarget.round (precisionSet 2 p) .Nearest`, ties to
even) gives `x₋` or `x₊`, whichever is nearer to `x`. -/
theorem roundNearest_spec (p : ℕ) [NeZero p] {x : ℝ} (hx : 0 < x) :
    ∃ r : ℝ, (RoundingTarget.round (precisionSet 2 p) .Nearest x).val = (r : EReal) ∧
      (r = roundChop p x ∨ r = roundChopUp p x) ∧
      |x - r| ≤ x - roundChop p x ∧ |x - r| ≤ roundChopUp p x - x ∧
      |x - r| ≤ precScale 2 p x / 2 ∧ ∀ m : ℤ, |x - r| ≤ |x - m * precScale 2 p x| := by
  have hu : 0 < precScale 2 p x := precScale_two_pos p x
  set u := precScale 2 p x
  set y := x / u
  set n := toInt (RoundingTarget.round intSet .Nearest y)
  refine ⟨n * u, val_round_precisionSet .Nearest x hx.ne', ?_⟩
  have hxy : x = y * u := by simp only [y]; field_simp
  have key : ∀ m : ℤ, |x - m * u| = |y - m| * u := fun m => by
    rw [hxy, ← sub_mul, abs_mul, abs_of_pos hu]
  have hn := abs_toInt_round_nearest_sub_le y
  have hhalf := abs_sub_toInt_round_nearest_le y
  have hf1 := Int.floor_le y
  have hf2 := Int.lt_floor_add_one y
  have hn1 : ⌊y⌋ - 1 < n := by
    have : (⌊y⌋ : ℝ) - 1 < n := by rw [abs_le] at hhalf; linarith
    exact_mod_cast this
  have hn2 : n < ⌊y⌋ + 2 := by
    have : (n : ℝ) < ⌊y⌋ + 2 := by rw [abs_le] at hhalf; linarith
    exact_mod_cast this
  refine ⟨?_, ?_, ?_, ?_, fun m => ?_⟩
  · rcases (by omega : n = ⌊y⌋ ∨ n = ⌊y⌋ + 1) with h | h
    · left; rw [h]; rfl
    · right; rw [h, roundChopUp, roundChop]; push_cast; ring
  · have e1 : x - roundChop p x = (y - ⌊y⌋) * u := by
      rw [roundChop]; change x - ⌊y⌋ * u = _; rw [hxy]; ring
    rw [key, e1]
    have := hn ⌊y⌋
    rw [abs_of_nonneg (by linarith : 0 ≤ y - ⌊y⌋)] at this
    exact mul_le_mul_of_nonneg_right this hu.le
  · have e1 : roundChopUp p x - x = ((⌊y⌋ : ℝ) + 1 - y) * u := by
      rw [roundChopUp, roundChop]; change ⌊y⌋ * u + u - x = _; rw [hxy]; ring
    rw [key, e1]
    have := hn (⌊y⌋ + 1)
    rw [show |y - ((⌊y⌋ + 1 : ℤ) : ℝ)| = (⌊y⌋ : ℝ) + 1 - y by
      rw [abs_of_neg (by push_cast; linarith)]; push_cast; ring] at this
    exact mul_le_mul_of_nonneg_right this hu.le
  · rw [key]; nlinarith
  · rw [key, key]; exact mul_le_mul_of_nonneg_right (hn m) hu.le

/-- **Rounding to nearest**: the relative error is at most `2^{−p}/(1 + 2^{−p})`, hence at most
the machine precision `½ε_M = 2^{−p}`. -/
theorem roundNearest_rel_err {p : ℕ} [NeZero p] (hp : 1 ≤ p) {x r : ℝ} (hx : 0 < x)
    (hr : (RoundingTarget.round (precisionSet 2 p) .Nearest x).val = (r : EReal)) :
    |x - r| / x ≤ machineEps p / 2 / (1 + machineEps p / 2) := by
  obtain ⟨r', hr', -, -, -, hhalf, hall⟩ := roundNearest_spec p hx
  have e : r = r' := EReal.coe_injective (hr.symm.trans hr')
  subst e
  obtain ⟨e2, -, -⟩ := chop_lattice hp hx
  have hu : 0 < precScale 2 p x := precScale_two_pos p x
  have hlat := hall (2 ^ (p - 1))
  push_cast at hlat
  rw [← e2] at hlat
  have h1 := Int.zpow_log_le_self (b := 2) (by norm_num) hx
  push_cast at h1
  rw [abs_of_nonneg (show (0 : ℝ) ≤ x - 2 ^ Int.log 2 x by linarith)] at hlat
  have hus := precScale_eq (p := p) hx
  set u := precScale 2 p x
  set E := (2 : ℝ) ^ Int.log 2 x
  have hE : 0 < E := by positivity
  have hε : 0 < machineEps p := by unfold machineEps; positivity
  have hc : machineEps p / 2 / (1 + machineEps p / 2) = (u / 2) / (E + u / 2) := by
    rw [hus]; field_simp
  rw [hc, div_le_div_iff₀ hx (by positivity)]
  have hpos : 0 ≤ E + u / 2 := by positivity
  rcases le_total (E + u / 2) x with h | h
  · nlinarith [mul_le_mul_of_nonneg_right hhalf hpos, mul_le_mul_of_nonneg_left h hu.le]
  · nlinarith [mul_le_mul_of_nonneg_right hlat hpos, mul_le_mul_of_nonneg_left h hE.le]

/-- `x₋ = 1` and `x₊ = 1 + ε_M` for `1 ≤ x < 1 + ε_M`. -/
theorem roundChop_near_one {p : ℕ} (hp : 1 ≤ p) {x : ℝ} (h1 : 1 ≤ x)
    (h2 : x < 1 + machineEps p) :
    precScale 2 p x = machineEps p ∧ roundChop p x = 1 ∧ roundChopUp p x = 1 + machineEps p := by
  have hε : 0 < machineEps p := by unfold machineEps; positivity
  have hε1 : machineEps p ≤ 1 := by
    rw [machineEps_eq hp, div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
  have hlog : Int.log 2 x = 0 := by
    rw [Int.log_of_one_le_right 2 h1,
      (Nat.floor_eq_iff (n := 1) (by linarith)).mpr ⟨by push_cast; linarith,
        by push_cast; linarith⟩]
    simp
  have hus : precScale 2 p x = machineEps p := by rw [precScale_eq (by linarith), hlog]; simp
  have hinv : 1 / machineEps p = 2 ^ (p - 1) := by rw [machineEps_eq hp]; field_simp
  have hfl : ⌊x / machineEps p⌋ = 2 ^ (p - 1) := by
    rw [Int.floor_eq_iff]
    have hy : x / machineEps p = 2 ^ (p - 1) + (x - 1) / machineEps p := by
      rw [← hinv]; field_simp; ring
    rw [hy]
    push_cast
    constructor
    · have : 0 ≤ (x - 1) / machineEps p := div_nonneg (by linarith) hε.le
      linarith
    · have : (x - 1) / machineEps p < 1 := by rw [div_lt_one hε]; linarith
      linarith
  have hchop : roundChop p x = 1 := by
    rw [roundChop, hus, hfl]; push_cast; rw [machineEps_eq hp]; field_simp
  exact ⟨hus, hchop, by rw [roundChopUp, hchop, hus]⟩

/-- The bound is attained at `x = 1 + 2^{−p}` (a tie): the maximum relative error of rounding to
nearest is exactly `2^{−p}/(1 + 2^{−p})`, slightly less than DLMF's `2^{−p}`. -/
theorem roundNearest_rel_err_attained {p : ℕ} [NeZero p] (hp : 1 ≤ p) {r : ℝ}
    (hr : (RoundingTarget.round (precisionSet 2 p) .Nearest (1 + machineEps p / 2)).val =
      (r : EReal)) :
    |(1 + machineEps p / 2) - r| / (1 + machineEps p / 2) =
      machineEps p / 2 / (1 + machineEps p / 2) := by
  have hε : 0 < machineEps p := by unfold machineEps; positivity
  set x := 1 + machineEps p / 2
  have hx : 0 < x := by positivity
  obtain ⟨r', hr', hor, -⟩ := roundNearest_spec p hx
  have e : r = r' := EReal.coe_injective (hr.symm.trans hr')
  subst e
  obtain ⟨-, hc, hu⟩ := roundChop_near_one hp (x := x) (by simp only [x]; linarith)
    (by simp only [x]; linarith)
  congr 1
  rcases hor with h | h
  · rw [h, hc, abs_of_pos (by simp only [x]; linarith)]; simp only [x]; ring
  · rw [h, hu, abs_of_neg (by simp only [x]; linarith)]; simp only [x]; ring

/-- The chopping bound is sharp: every `η < ε_M/(1 + ε_M)` is exceeded by the relative error at
some `x ∈ (1, 1 + ε_M)` (so the supremum is `ε_M/(1 + ε_M)`, not attained). -/
theorem roundChop_rel_err_sharp {p : ℕ} (hp : 1 ≤ p) {η : ℝ}
    (hη : η < machineEps p / (1 + machineEps p)) :
    ∃ x : ℝ, 0 < x ∧ η < (x - roundChop p x) / x := by
  have hε : 0 < machineEps p := by unfold machineEps; positivity
  have hη1 : η < 1 := hη.trans (by rw [div_lt_one (by linarith)]; linarith)
  set τ := max 0 (η / (1 - η))
  have hτ0 : 0 ≤ τ := le_max_left _ _
  have hτ : τ < machineEps p := by
    rcases le_total η 0 with h | h
    · rw [show τ = 0 from max_eq_left (div_nonpos_of_nonpos_of_nonneg h (by linarith))]
      exact hε
    · refine max_lt hε ?_
      rw [div_lt_iff₀ (by linarith)]
      rw [lt_div_iff₀ (by linarith)] at hη
      linarith
  set t := (τ + machineEps p) / 2
  have ht0 : 0 < t := by simp only [t]; linarith
  refine ⟨1 + t, by linarith, ?_⟩
  obtain ⟨-, hc, -⟩ := roundChop_near_one hp (x := 1 + t) (by linarith) (by simp only [t]; linarith)
  rw [hc, add_sub_cancel_left, lt_div_iff₀ (by positivity)]
  have ht : η / (1 - η) < t := (le_max_right 0 (η / (1 - η))).trans_lt (by simp only [t]; linarith)
  rw [div_lt_iff₀ (by linarith)] at ht
  linarith

/-- "Negative numbers `x` are rounded in the same way as `−x`". -/
theorem roundNearest_neg (p : ℕ) [NeZero p] (x : ℝ) :
    (RoundingTarget.round (precisionSet 2 p) .Nearest (-x)).val =
      -(RoundingTarget.round (precisionSet 2 p) .Nearest x).val :=
  round_neg (precisionSet 2 p) .Nearest x

theorem machineNmax_eq {p : ℕ} (hp : 1 ≤ p) (Emax : ℤ) :
    machineNmax p Emax = ((2 ^ p - 1 : ℕ) : ℝ) * 2 ^ Emax / 2 ^ (p - 1) := by
  have hpowR : (2 : ℝ) ^ p = 2 * 2 ^ (p - 1) := by rw [← pow_succ']; congr 1; omega
  rw [machineNmax, Nat.cast_sub Nat.one_le_two_pow, zpow_add_one₀ two_ne_zero]
  push_cast
  rw [hpowR]
  field_simp

/-- For `N_min ≤ x ≤ N_max`, `x₋` is a machine number, and so is `x₊` when `x < N_max`. -/
theorem roundChop_mem {p : ℕ} (hp : 1 ≤ p) {Emin Emax : ℤ} {x : ℝ}
    (hlo : machineNmin Emin ≤ x) (hhi : x ≤ machineNmax p Emax) :
    roundChop p x ∈ machineNum p Emin Emax ∧
      (x < machineNmax p Emax → roundChopUp p x ∈ machineNum p Emin Emax) := by
  have hx : 0 < x := lt_of_lt_of_le (by unfold machineNmin; positivity) hlo
  have hpowR : (2 : ℝ) ^ p = 2 * 2 ^ (p - 1) := by rw [← pow_succ']; congr 1; omega
  set E := Int.log 2 x
  have hE1 : Emin ≤ E := (Int.zpow_le_iff_le_log (b := 2) (by norm_num) hx).mp
    (by push_cast; exact hlo)
  have hNmax : machineNmax p Emax < 2 ^ (Emax + 1) := by
    unfold machineNmax
    have : (0 : ℝ) < 1 / 2 ^ p := by positivity
    have : (0 : ℝ) < 2 ^ (Emax + 1) := by positivity
    nlinarith
  have hE2 : E ≤ Emax := by
    have := (Int.lt_zpow_iff_log_lt (b := 2) (by norm_num) hx).mp
      (by push_cast; exact hhi.trans_lt hNmax)
    omega
  obtain ⟨e, l, u⟩ := chop_lattice hp hx
  have hu : 0 < precScale 2 p x := precScale_two_pos p x
  set U := precScale 2 p x
  set n := ⌊x / U⌋
  have hn1 : (2 : ℤ) ^ (p - 1) ≤ n := Int.le_floor.mpr (by push_cast; exact l)
  have hn2 : n < 2 ^ p := Int.floor_lt.mpr (by push_cast; exact u)
  have hn0 : 0 ≤ n := le_trans (by positivity) hn1
  have hU : U = 2 ^ E / 2 ^ (p - 1) := by rw [e]; field_simp
  have hchop : roundChop p x = (n.toNat : ℝ) * 2 ^ E / 2 ^ (p - 1) := by
    rw [show roundChop p x = (n : ℝ) * U from rfl, hU]
    have : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hn0
    rw [this]; ring
  have hn1' : ((2 ^ (p - 1) : ℕ) : ℤ) ≤ n := by exact_mod_cast hn1
  have hn2' : n < ((2 ^ p : ℕ) : ℤ) := by exact_mod_cast hn2
  have hM1 : 2 ^ (p - 1) ≤ n.toNat := by omega
  have hM2 : n.toNat < 2 ^ p := by omega
  have hMpos : (0 : ℝ) < n.toNat := by exact_mod_cast lt_of_lt_of_le (Nat.two_pow_pos _) hM1
  have hpos : roundChop p x ≠ 0 := by rw [hchop]; positivity
  refine ⟨(mem_machineNum_iff hp hpos).mpr ⟨0, E, n.toNat, by norm_num, hE1, hE2, hM1, hM2,
    by rw [hchop]; ring⟩, fun hlt => ?_⟩
  have hup : roundChopUp p x = ((n.toNat + 1 : ℕ) : ℝ) * 2 ^ E / 2 ^ (p - 1) := by
    rw [show roundChopUp p x = roundChop p x + U from rfl, hchop, hU]; push_cast; ring
  have hpos' : roundChopUp p x ≠ 0 := by rw [hup]; positivity
  rcases (by omega : n.toNat + 1 < 2 ^ p ∨ n.toNat + 1 = 2 ^ p) with h | h
  · exact (mem_machineNum_iff hp hpos').mpr ⟨0, E, n.toNat + 1, by norm_num, hE1, hE2,
      by omega, h, by rw [hup]; ring⟩
  · -- `x₊ = 2^{E+1}`, and `E < E_max` since otherwise `x ≥ x₋ = N_max`
    have hE3 : E < Emax := by
      rcases lt_or_eq_of_le hE2 with h' | h'
      · exact h'
      · exfalso
        have hb := (roundChop_bounds hp hx).2.1
        rw [hchop, show n.toNat = 2 ^ p - 1 by omega, h', ← machineNmax_eq hp] at hb
        linarith
    refine (mem_machineNum_iff hp hpos').mpr ⟨0, E + 1, 2 ^ (p - 1), by norm_num, by omega,
      by omega, le_rfl, by omega, ?_⟩
    rw [hup, h, zpow_add_one₀ two_ne_zero]
    push_cast
    rw [hpowR]
    ring

end Azurite.DLMF
