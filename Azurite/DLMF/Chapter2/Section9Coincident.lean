/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section9Formal

/-!
# DLMF §2.9(ii): Coincident Characteristic Values — the case `2g₁ = f₀f₁`, 2.9.11–2.9.12

The roots of 2.9.5 coincide (`f₀² = 4g₀`, `ρ = −f₀/2`) and `2g₁ = f₀f₁`. Then the table
`T(s, j)` of §2.9(i) (`diffT`) has `T(s, 0) = T(s, 1) = 0` (`coinc_T_one`) and
`T(s, 2) = P(α − s)/2` (`coinc_T_two`), `P` the polynomial of 2.9.11 (`coincPoly`).

* 2.9.11 (`dlmf_2_9_11`): `P(α) = 2g₀α² − (f₀f₁ + 2g₀)α + 2g₂ − f₀f₂ = 2g₀(α − α₁)(α − α₂)`.
* 2.9.12 (`dlmf_2_9_12`): for a root `α` of 2.9.11 with `P(α − m) ≠ 0` for `m ≥ 1`, the
  coefficients `a₀ = 1`, `P(α − m)/2 · a_m = −∑_{s<m} aₛ T(s, m+2−s)` (`coincCoeff`) make
  `ρⁿ n^α ∑ aₛ/nˢ` a formal solution of 2.9.1 (residual `ρⁿ n^α O(n^{−N−2})`); these coefficients
  satisfy 2.9.7 (`dlmf_2_9_12_coeff`). When `α₂ − α₁` is not an integer this applies to both
  roots (`dlmf_2_9_12_pair`); when `α₂ − α₁ = 0, 1, 2, …` it applies to `α₁`
  (`dlmf_2_9_12_first`).
* The parenthetical remark of DLMF (`dlmf_2_9_ii_coeff`): in 2.9.7 the coefficient
  `ρ(f₀ + 2ρ)s` of `aₛ` vanishes, but the coefficient of `a_{s−1}` is `P(α − s + 1)/2`, nonzero for
  `s ≥ 2`; 2.9.7 at `s` determines `a_{s−1}` (see `docs/dlmf_errata.md`).

Not formalized: 2.9.13 (logarithmic solutions when `α₂ − α₁ ∈ ℕ`, cf. the deferred 2.7.6); the
existence of the solutions `w_j` (Wong and Li 1992b); 2.9.14 (Wong and Li 1992a).
-/

open Filter Topology Asymptotics Finset Complex

namespace Azurite.DLMF

theorem choose_two_eq (b : ℂ) : Ring.choose b 2 = b * (b - 1) / 2 := by
  rw [Ring.choose_eq_smul]
  simp [descPochhammer_succ_right, Polynomial.smeval_mul, Polynomial.smeval_X,
    Polynomial.smeval_sub]
  ring

/-- A complex quadratic factors. -/
theorem quadratic_factor (A B C : ℂ) (hA : A ≠ 0) :
    ∃ r₁ r₂ : ℂ, ∀ x, A * x ^ 2 + B * x + C = A * (x - r₁) * (x - r₂) := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self (B ^ 2 - 4 * A * C)
  refine ⟨(-B + s) / (2 * A), (-B - s) / (2 * A), fun x => ?_⟩
  field_simp
  linear_combination -hs

/-- **DLMF 2.9.11**: `2g₀α² − (f₀f₁ + 2g₀)α + 2g₂ − f₀f₂`. -/
def coincPoly (fc gc : ℕ → ℂ) (α : ℂ) : ℂ :=
  2 * gc 0 * α ^ 2 - (fc 0 * fc 1 + 2 * gc 0) * α + 2 * gc 2 - fc 0 * fc 2

/-- **DLMF 2.9.11**: the indices `α₁, α₂` are the roots of `P`. -/
theorem dlmf_2_9_11 (fc gc : ℕ → ℂ) (hg0 : gc 0 ≠ 0) :
    ∃ α₁ α₂ : ℂ, ∀ α, coincPoly fc gc α = 2 * gc 0 * (α - α₁) * (α - α₂) := by
  obtain ⟨r₁, r₂, h⟩ := quadratic_factor (2 * gc 0) (-(fc 0 * fc 1 + 2 * gc 0))
    (2 * gc 2 - fc 0 * fc 2) (mul_ne_zero two_ne_zero hg0)
  refine ⟨r₁, r₂, fun α => ?_⟩
  rw [coincPoly, ← h]
  ring

variable {fc gc : ℕ → ℂ} {ρ : ℂ}

section Coincident

variable (hρ : ρ ^ 2 + fc 0 * ρ + gc 0 = 0) (hdouble : fc 0 ^ 2 = 4 * gc 0)
  (h21 : 2 * gc 1 = fc 0 * fc 1)
include hρ hdouble

theorem coinc_fr : fc 0 + 2 * ρ = 0 := (dlmf_2_9_construction_fails hρ).mpr hdouble

include h21 in
/-- `T(s, 1) = 0` when `ρ` is a double root and `2g₁ = f₀f₁`. -/
theorem coinc_T_one (α : ℂ) (s : ℕ) : diffT fc gc ρ α s 1 = 0 := by
  have hfr := coinc_fr hρ hdouble
  simp only [diffT, sum_range_succ, sum_range_zero, Ring.choose_one_right,
    Ring.choose_zero_right, Nat.sub_zero, Nat.sub_self, zero_add, pow_one]
  linear_combination (ρ * (α - s) + fc 1 / 2) * hfr + (1 / 2 : ℂ) * h21

/-- `T(s, 2) = P(α − s)/2` when `ρ` is a double root. -/
theorem coinc_T_two (α : ℂ) (s : ℕ) : diffT fc gc ρ α s 2 = coincPoly fc gc (α - s) / 2 := by
  have hfr := coinc_fr hρ hdouble
  simp only [diffT, coincPoly, sum_range_succ, sum_range_zero, zero_add, Nat.sub_zero,
    Nat.sub_self, choose_two_eq, Ring.choose_one_right, Ring.choose_zero_right,
    show (2 : ℕ) - 1 = 1 from rfl]
  set β : ℂ := α - s
  linear_combination (ρ * β * (β - 1) / 2 + fc 1 * β / 2 + fc 2 / 2 - ρ * (β - β ^ 2)) * hfr +
    (β - β ^ 2) * hρ

end Coincident

/-- **DLMF 2.9.12**: `a₀ = 1`, `P(α − m)/2 · a_m = −∑_{s<m} aₛ T(s, m+2−s)` for `m ≥ 1`. -/
noncomputable def coincCoeff (fc gc : ℕ → ℂ) (ρ α : ℂ) : ℕ → ℂ
  | 0 => 1
  | m + 1 => -2 * (∑ i : Fin (m + 1), coincCoeff fc gc ρ α i * diffT fc gc ρ α i (m + 3 - i)) /
      coincPoly fc gc (α - (m + 1 : ℕ))

theorem coincCoeff_zero (fc gc : ℕ → ℂ) (ρ α : ℂ) : coincCoeff fc gc ρ α 0 = 1 := by
  rw [coincCoeff]

theorem coincCoeff_succ (fc gc : ℕ → ℂ) (ρ α : ℂ) {m : ℕ}
    (hP : coincPoly fc gc (α - (m + 1 : ℕ)) ≠ 0) :
    coincPoly fc gc (α - (m + 1 : ℕ)) / 2 * coincCoeff fc gc ρ α (m + 1) +
      ∑ i ∈ range (m + 1), coincCoeff fc gc ρ α i * diffT fc gc ρ α i (m + 3 - i) = 0 := by
  rw [coincCoeff, ← Finset.sum_range (fun i => coincCoeff fc gc ρ α i *
    diffT fc gc ρ α i (m + 3 - i))]
  field_simp
  ring

section Coincident

variable (hρ : ρ ^ 2 + fc 0 * ρ + gc 0 = 0) (hdouble : fc 0 ^ 2 = 4 * gc 0)
  (h21 : 2 * gc 1 = fc 0 * fc 1) {α : ℂ} (hα : coincPoly fc gc α = 0)
  (hP : ∀ m : ℕ, 1 ≤ m → coincPoly fc gc (α - m) ≠ 0)
include hρ hdouble h21

include hα hP in
/-- The coefficient identities `∑_{s≤d} aₛ T(s, d−s) = 0` for every `d`. -/
theorem coincCoeff_vanish (d : ℕ) :
    ∑ s ∈ range (d + 1), coincCoeff fc gc ρ α s * diffT fc gc ρ α s (d - s) = 0 := by
  rcases d with _ | _ | m
  · rw [sum_range_one, Nat.sub_self, diffT_zero, hρ, mul_zero]
  · rw [sum_range_succ, sum_range_one, Nat.sub_self, diffT_zero, hρ, mul_zero, add_zero,
      show 0 + 1 - 0 = 1 from rfl, coinc_T_one hρ hdouble h21, mul_zero]
  · rw [sum_range_succ, Nat.sub_self, diffT_zero, hρ, mul_zero, add_zero]
    rw [sum_range_succ, show m + 1 + 1 - (m + 1) = 1 by omega, coinc_T_one hρ hdouble h21,
      mul_zero, add_zero]
    rw [sum_range_succ, show m + 1 + 1 - m = 2 by omega, coinc_T_two hρ hdouble]
    rcases m with _ | k
    · simp [hα]
    · have hs := coincCoeff_succ fc gc ρ α (m := k) (hP (k + 1) (by omega))
      have e : ∑ s ∈ range (k + 1), coincCoeff fc gc ρ α s *
          diffT fc gc ρ α s (k + 1 + 1 + 1 - s) =
          ∑ i ∈ range (k + 1), coincCoeff fc gc ρ α i * diffT fc gc ρ α i (k + 3 - i) := rfl
      rw [e]
      linear_combination hs

include hα hP in
/-- **DLMF 2.9.12** (formal solutions): for `f`, `g` as in 2.9.3, a double root `ρ` of 2.9.5,
`2g₁ = f₀f₁`, a root `α` of 2.9.11 with `P(α − m) ≠ 0` for `m ≥ 1`, and `aₛ = coincCoeff`, each
truncation `w_N(n) = ρⁿ n^α ∑_{s≤N} aₛ/nˢ` satisfies
`w_N(n+2) + f(n) w_N(n+1) + g(n) w_N(n) = ρⁿ n^α B_N(n)`, `B_N(n) = O(n^{−N−2})`. -/
theorem dlmf_2_9_12 {f g : ℕ → ℂ} (hf : IsAsympSeqDLMF f fc) (hg : IsAsympSeqDLMF g gc)
    (N : ℕ) :
    ∃ B : ℕ → ℂ, IsBigODLMF atTop B (fun n => ((n : ℂ) ^ (N + 2))⁻¹) ∧
      ∀ n, 1 ≤ n → formalTrunc ρ α (coincCoeff fc gc ρ α) N (n + 2) +
        f n * formalTrunc ρ α (coincCoeff fc gc ρ α) N (n + 1) +
        g n * formalTrunc ρ α (coincCoeff fc gc ρ α) N n = ρ ^ n * (n : ℂ) ^ α * B n :=
  formalTrunc_isBigO hf hg hρ N fun d _ => coincCoeff_vanish hρ hdouble h21 hα hP d

include hα hP in
/-- **DLMF 2.9.12**: the coefficients `coincCoeff` satisfy 2.9.7 (whose left side vanishes). -/
theorem dlmf_2_9_12_coeff {s : ℕ} (hs : 1 ≤ s) :
    ρ * (fc 0 + 2 * ρ) * (s : ℂ) * coincCoeff fc gc ρ α s =
      ∑ r ∈ Icc 1 s, (ρ ^ 2 * 2 ^ (r + 1) * Ring.choose (α + r - s) (r + 1) +
        ρ * ∑ q ∈ range (r + 1 + 1), Ring.choose (α + r - s) (r + 1 - q) * fc q + gc (r + 1)) *
          coincCoeff fc gc ρ α (s - r) := by
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by omega⟩
  rw [sum_Icc_dlmf_2_9_7, coinc_fr hρ hdouble, mul_zero, zero_mul, zero_mul]
  have hv := coincCoeff_vanish hρ hdouble h21 hα hP (m + 1 + 1)
  rw [sum_range_succ, Nat.sub_self, diffT_zero, hρ, mul_zero, add_zero, sum_range_succ,
    show m + 1 + 1 - (m + 1) = 1 by omega, coinc_T_one hρ hdouble h21, mul_zero,
    add_zero] at hv
  exact hv.symm

end Coincident

/-- **DLMF §2.9(ii)**, the parenthetical remark on 2.9.7: when `ρ` is a double root, `2g₁ = f₀f₁`
and `α` is a root of 2.9.11 with `P(α − m) ≠ 0` for `m ≥ 1`, the coefficient `ρ(f₀ + 2ρ)s` of `aₛ`
in 2.9.7 vanishes, while for `s ≥ 2` the coefficient of `a_{s−1}` (the term `r = 1`, which is
`T(s−1, 2)` by `sum_Icc_dlmf_2_9_7`) equals `P(α − (s − 1))/2 ≠ 0`. -/
theorem dlmf_2_9_ii_coeff (hρ : ρ ^ 2 + fc 0 * ρ + gc 0 = 0) (hdouble : fc 0 ^ 2 = 4 * gc 0)
    {α : ℂ} (hP : ∀ m : ℕ, 1 ≤ m → coincPoly fc gc (α - m) ≠ 0) {s : ℕ} (hs : 2 ≤ s) :
    ρ * (fc 0 + 2 * ρ) * (s : ℂ) = 0 ∧
      diffT fc gc ρ α (s - 1) 2 = coincPoly fc gc (α - (s - 1 : ℕ)) / 2 ∧
      diffT fc gc ρ α (s - 1) 2 ≠ 0 := by
  refine ⟨by rw [coinc_fr hρ hdouble, mul_zero, zero_mul], coinc_T_two hρ hdouble α (s - 1), ?_⟩
  rw [coinc_T_two hρ hdouble α (s - 1)]
  exact div_ne_zero (hP (s - 1) (by omega)) two_ne_zero

/-- The roots `α₁`, `α₂` of 2.9.11 and the nonvanishing conditions of `dlmf_2_9_12`. -/
theorem coincPoly_roots {α₁ α₂ : ℂ}
    (hfac : ∀ α, coincPoly fc gc α = 2 * gc 0 * (α - α₁) * (α - α₂)) :
    coincPoly fc gc α₁ = 0 ∧ coincPoly fc gc α₂ = 0 := by
  constructor <;> rw [hfac] <;> ring

theorem coincPoly_sub_ne_zero_of_not_int {α₁ α₂ : ℂ} (hg0 : gc 0 ≠ 0)
    (hfac : ∀ α, coincPoly fc gc α = 2 * gc 0 * (α - α₁) * (α - α₂))
    (hnot : ∀ m : ℤ, α₂ - α₁ ≠ m) (m : ℕ) (hm : 1 ≤ m) :
    coincPoly fc gc (α₁ - m) ≠ 0 ∧ coincPoly fc gc (α₂ - m) ≠ 0 := by
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h2 : (2 : ℂ) * gc 0 ≠ 0 := mul_ne_zero two_ne_zero hg0
  constructor
  · rw [hfac]
    refine mul_ne_zero (mul_ne_zero h2 (by rw [sub_sub_cancel_left]; exact neg_ne_zero.mpr hm0))
      fun h => hnot (-(m : ℤ)) ?_
    push_cast
    linear_combination -h
  · rw [hfac]
    refine mul_ne_zero (mul_ne_zero h2 fun h => hnot m ?_) (by
      rw [sub_sub_cancel_left]; exact neg_ne_zero.mpr hm0)
    push_cast
    linear_combination h

theorem coincPoly_sub_ne_zero_of_nat {α₁ α₂ : ℂ} (hg0 : gc 0 ≠ 0)
    (hfac : ∀ α, coincPoly fc gc α = 2 * gc 0 * (α - α₁) * (α - α₂)) {k : ℕ}
    (hk : α₂ - α₁ = k) (m : ℕ) (hm : 1 ≤ m) : coincPoly fc gc (α₁ - m) ≠ 0 := by
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hmk : ((m + k : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [hfac]
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hg0)
    (by rw [sub_sub_cancel_left]; exact neg_ne_zero.mpr hm0)) fun h => hmk ?_
  push_cast
  linear_combination -h - hk

/-- **DLMF 2.9.12**: if `α₂ − α₁` is not an integer, both indices give formal solutions. -/
theorem dlmf_2_9_12_pair {f g : ℕ → ℂ} (hf : IsAsympSeqDLMF f fc) (hg : IsAsympSeqDLMF g gc)
    (hρ : ρ ^ 2 + fc 0 * ρ + gc 0 = 0) (hdouble : fc 0 ^ 2 = 4 * gc 0)
    (h21 : 2 * gc 1 = fc 0 * fc 1) (hg0 : gc 0 ≠ 0) {α₁ α₂ : ℂ}
    (hfac : ∀ α, coincPoly fc gc α = 2 * gc 0 * (α - α₁) * (α - α₂))
    (hnot : ∀ m : ℤ, α₂ - α₁ ≠ m) (N : ℕ) :
    ∀ α ∈ ({α₁, α₂} : Set ℂ), ∃ B : ℕ → ℂ,
      IsBigODLMF atTop B (fun n => ((n : ℂ) ^ (N + 2))⁻¹) ∧
      ∀ n, 1 ≤ n → formalTrunc ρ α (coincCoeff fc gc ρ α) N (n + 2) +
        f n * formalTrunc ρ α (coincCoeff fc gc ρ α) N (n + 1) +
        g n * formalTrunc ρ α (coincCoeff fc gc ρ α) N n = ρ ^ n * (n : ℂ) ^ α * B n := by
  intro α hα
  rcases hα with rfl | hα
  · exact dlmf_2_9_12 hρ hdouble h21 (coincPoly_roots hfac).1
      (fun m hm => (coincPoly_sub_ne_zero_of_not_int hg0 hfac hnot m hm).1) hf hg N
  · rw [Set.mem_singleton_iff] at hα
    subst hα
    exact dlmf_2_9_12 hρ hdouble h21 (coincPoly_roots hfac).2
      (fun m hm => (coincPoly_sub_ne_zero_of_not_int hg0 hfac hnot m hm).2) hf hg N

/-- **DLMF §2.9(ii)**: if `α₂ − α₁ = 0, 1, 2, …`, 2.9.12 applies for `j = 1`. -/
theorem dlmf_2_9_12_first {f g : ℕ → ℂ} (hf : IsAsympSeqDLMF f fc) (hg : IsAsympSeqDLMF g gc)
    (hρ : ρ ^ 2 + fc 0 * ρ + gc 0 = 0) (hdouble : fc 0 ^ 2 = 4 * gc 0)
    (h21 : 2 * gc 1 = fc 0 * fc 1) (hg0 : gc 0 ≠ 0) {α₁ α₂ : ℂ}
    (hfac : ∀ α, coincPoly fc gc α = 2 * gc 0 * (α - α₁) * (α - α₂)) {k : ℕ}
    (hk : α₂ - α₁ = k) (N : ℕ) :
    ∃ B : ℕ → ℂ, IsBigODLMF atTop B (fun n => ((n : ℂ) ^ (N + 2))⁻¹) ∧
      ∀ n, 1 ≤ n → formalTrunc ρ α₁ (coincCoeff fc gc ρ α₁) N (n + 2) +
        f n * formalTrunc ρ α₁ (coincCoeff fc gc ρ α₁) N (n + 1) +
        g n * formalTrunc ρ α₁ (coincCoeff fc gc ρ α₁) N n = ρ ^ n * (n : ℂ) ^ α₁ * B n :=
  dlmf_2_9_12 hρ hdouble h21 (coincPoly_roots hfac).1
    (fun m hm => coincPoly_sub_ne_zero_of_nat hg0 hfac hk m hm) hf hg N

end Azurite.DLMF
