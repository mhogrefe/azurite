/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section9
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# DLMF §2.9(i): Distinct Characteristic Values — formal solutions 2.9.4–2.9.7

For 2.9.1 with `f`, `g` expanded as in 2.9.3 (`IsAsympSeqDLMF`), `g₀ ≠ 0`:

* 2.9.5 (`dlmf_2_9_5`): the characteristic equation `ρ² + f₀ρ + g₀ = 0` has roots `ρ₁, ρ₂`,
  equal iff `f₀² = 4g₀`; for a root, `f₀ + 2ρ = 0 ↔ f₀² = 4g₀` (`dlmf_2_9_construction_fails`: "the
  construction fails if `ρ₁ = ρ₂`").
* 2.9.6 (`diffAlpha`): `α = (f₁ρ + g₁)/(f₀ρ + 2g₀)`.
* 2.9.7 (`diffCoeff`, `dlmf_2_9_7`): `a₀ = 1` and
  `ρ(f₀ + 2ρ) s aₛ = ∑_{r=1}^{s} (ρ² 2^{r+1} binom(α+r−s, r+1)
    + ρ ∑_{q=0}^{r+1} binom(α+r−s, r+1−q) f_q + g_{r+1}) a_{s−r}`.
* 2.9.4 (`dlmf_2_9_4`): `ρⁿ n^α ∑ aₛ/nˢ` is a *formal solution* of 2.9.1: every truncation
  `w_N(n) = ρⁿ n^α ∑_{s≤N} aₛ/nˢ` (`diffTrunc`) satisfies
  `w_N(n+2) + f(n) w_N(n+1) + g(n) w_N(n) = ρⁿ n^α B_N(n)` with `B_N(n) = O(n^{−N−2})`.

The proof writes `B_N(n) = ∑_{s≤N} aₛ n^{−s} (ρ²(1 + 2/n)^{α−s} + ρ f(n)(1 + 1/n)^{α−s} + g(n))`
(`formalTrunc_residual`), expands it with the binomial series (`diffBracket_series`, coefficient
`diffT s j`), and shows that the coefficient of `n^{−d}` is `∑_{s≤d} aₛ T(s, d−s) = 0`
(`diffCoeff_vanish`): `T(s, 0)` is 2.9.5, `T(s, 1) = −sρ(f₀ + 2ρ)` is 2.9.6, the rest is 2.9.7.
-/

open Filter Topology Asymptotics Finset Complex

namespace Azurite.DLMF

/-! ### 2.9.5: the characteristic equation -/

/-- **DLMF 2.9.5**: `ρ² + f₀ρ + g₀ = (ρ − ρ₁)(ρ − ρ₂)`, and `ρ₁ = ρ₂ ↔ f₀² = 4g₀`. -/
theorem dlmf_2_9_5 (f₀ g₀ : ℂ) : ∃ ρ₁ ρ₂ : ℂ,
    (∀ ρ, ρ ^ 2 + f₀ * ρ + g₀ = (ρ - ρ₁) * (ρ - ρ₂)) ∧ (ρ₁ = ρ₂ ↔ f₀ ^ 2 = 4 * g₀) := by
  obtain ⟨s, hs⟩ := IsAlgClosed.isSquare (f₀ ^ 2 - 4 * g₀)
  refine ⟨(-f₀ + s) / 2, (-f₀ - s) / 2, fun ρ => by linear_combination (-1 / 4 : ℂ) * hs, ?_⟩
  constructor
  · intro h
    have hs0 : s = 0 := by linear_combination h
    linear_combination hs + s * hs0
  · intro h
    have hss : s * s = 0 := by linear_combination -hs + h
    rw [mul_self_eq_zero.mp hss]
    ring

variable {fc gc : ℕ → ℂ} {ρ : ℂ}

theorem charRoot_ne_zero (hρ : ρ ^ 2 + fc 0 * ρ + gc 0 = 0) (hg0 : gc 0 ≠ 0) : ρ ≠ 0 := by
  rintro rfl
  exact hg0 (by simpa using hρ)

/-- "The construction fails if `ρ₁ = ρ₂`, that is, when `f₀² = 4g₀`": for a root `ρ` of 2.9.5, the
denominator `f₀ + 2ρ` of 2.9.7 vanishes iff `f₀² = 4g₀`. -/
theorem dlmf_2_9_construction_fails (hρ : ρ ^ 2 + fc 0 * ρ + gc 0 = 0) :
    fc 0 + 2 * ρ = 0 ↔ fc 0 ^ 2 = 4 * gc 0 := by
  constructor
  · intro h
    linear_combination (fc 0 + 2 * ρ) * h - 4 * hρ
  · intro h
    have : (fc 0 + 2 * ρ) ^ 2 = 0 := by linear_combination 4 * hρ + h
    exact (pow_eq_zero_iff two_ne_zero).mp this

theorem diffDen_ne (hρ : ρ ^ 2 + fc 0 * ρ + gc 0 = 0) (hg0 : gc 0 ≠ 0)
    (hdist : fc 0 ^ 2 ≠ 4 * gc 0) : ρ * (fc 0 + 2 * ρ) ≠ 0 :=
  mul_ne_zero (charRoot_ne_zero hρ hg0) fun h => hdist ((dlmf_2_9_construction_fails hρ).mp h)

theorem alphaDen_ne (hρ : ρ ^ 2 + fc 0 * ρ + gc 0 = 0) (hg0 : gc 0 ≠ 0)
    (hdist : fc 0 ^ 2 ≠ 4 * gc 0) : fc 0 * ρ + 2 * gc 0 ≠ 0 := by
  have e : fc 0 * ρ + 2 * gc 0 = -(ρ * (fc 0 + 2 * ρ)) := by linear_combination 2 * hρ
  rw [e]
  exact neg_ne_zero.mpr (diffDen_ne hρ hg0 hdist)

/-! ### 2.9.6–2.9.7: the coefficients -/

/-- **DLMF 2.9.6**: `α = (f₁ρ + g₁)/(f₀ρ + 2g₀)`. -/
noncomputable def diffAlpha (fc gc : ℕ → ℂ) (ρ : ℂ) : ℂ :=
  (fc 1 * ρ + gc 1) / (fc 0 * ρ + 2 * gc 0)

/-- The coefficient of `n^{−j}` in `ρ²(1 + 2/n)^{α−s} + ρ f(n)(1 + 1/n)^{α−s} + g(n)`:
`T(s, j) = ρ² 2ʲ binom(α−s, j) + ρ ∑_{q≤j} binom(α−s, j−q) f_q + gⱼ`. -/
noncomputable def diffT (fc gc : ℕ → ℂ) (ρ α : ℂ) (s j : ℕ) : ℂ :=
  ρ ^ 2 * 2 ^ j * Ring.choose (α - s) j +
    ρ * ∑ q ∈ range (j + 1), Ring.choose (α - s) (j - q) * fc q + gc j

/-- **DLMF 2.9.7**: `a₀ = 1` and `ρ(f₀ + 2ρ)(m+1) a_{m+1} = ∑_{i ≤ m} aᵢ T(i, m+2−i)`
(2.9.7 with `i = s − r`). -/
noncomputable def diffCoeff (fc gc : ℕ → ℂ) (ρ α : ℂ) : ℕ → ℂ
  | 0 => 1
  | m + 1 => (∑ i : Fin (m + 1), diffCoeff fc gc ρ α i * diffT fc gc ρ α i (m + 2 - i)) /
      (ρ * (fc 0 + 2 * ρ) * ((m + 1 : ℕ) : ℂ))

theorem diffCoeff_zero (fc gc : ℕ → ℂ) (ρ α : ℂ) : diffCoeff fc gc ρ α 0 = 1 := by
  rw [diffCoeff]

theorem diffCoeff_succ (fc gc : ℕ → ℂ) (ρ α : ℂ) (hne : ρ * (fc 0 + 2 * ρ) ≠ 0) (m : ℕ) :
    ρ * (fc 0 + 2 * ρ) * ((m + 1 : ℕ) : ℂ) * diffCoeff fc gc ρ α (m + 1) =
      ∑ i ∈ range (m + 1), diffCoeff fc gc ρ α i * diffT fc gc ρ α i (m + 2 - i) := by
  have hd : ρ * (fc 0 + 2 * ρ) * ((m + 1 : ℕ) : ℂ) ≠ 0 :=
    mul_ne_zero hne (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m))
  rw [diffCoeff, Finset.sum_range, mul_div_assoc', mul_div_cancel_left₀ _ hd]

/-- The right side of 2.9.7 at `s = m + 1`, reindexed by `i = s − r`: for any sequence `a`,
`∑_{r=1}^{m+1} (⋯) a_{m+1−r} = ∑_{i ≤ m} aᵢ T(i, m+2−i)`. -/
theorem sum_Icc_dlmf_2_9_7 (fc gc : ℕ → ℂ) (ρ α : ℂ) (a : ℕ → ℂ) (m : ℕ) :
    ∑ r ∈ Icc 1 (m + 1), (ρ ^ 2 * 2 ^ (r + 1) * Ring.choose (α + r - (m + 1 : ℕ)) (r + 1) +
        ρ * ∑ q ∈ range (r + 1 + 1), Ring.choose (α + r - (m + 1 : ℕ)) (r + 1 - q) * fc q +
          gc (r + 1)) * a (m + 1 - r) =
      ∑ i ∈ range (m + 1), a i * diffT fc gc ρ α i (m + 2 - i) := by
  rw [sum_Icc_one_eq_sum_range]
  conv_rhs => rw [← sum_range_reflect]
  refine sum_congr rfl fun j hj => ?_
  have hj : j < m + 1 := mem_range.mp hj
  rw [show m + 1 - 1 - j = m - j by omega, show m + 2 - (m - j) = j + 1 + 1 by omega,
    show m + 1 - (j + 1) = m - j by omega]
  have hc : α - ((m - j : ℕ) : ℂ) = α + ((j + 1 : ℕ) : ℂ) - ((m + 1 : ℕ) : ℂ) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  simp only [diffT, hc]
  ring

/-- **DLMF 2.9.7** in DLMF's form. -/
theorem dlmf_2_9_7 (fc gc : ℕ → ℂ) (ρ α : ℂ) (hne : ρ * (fc 0 + 2 * ρ) ≠ 0) {s : ℕ}
    (hs : 1 ≤ s) :
    ρ * (fc 0 + 2 * ρ) * (s : ℂ) * diffCoeff fc gc ρ α s =
      ∑ r ∈ Icc 1 s, (ρ ^ 2 * 2 ^ (r + 1) * Ring.choose (α + r - s) (r + 1) +
        ρ * ∑ q ∈ range (r + 1 + 1), Ring.choose (α + r - s) (r + 1 - q) * fc q + gc (r + 1)) *
          diffCoeff fc gc ρ α (s - r) := by
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by omega⟩
  rw [diffCoeff_succ fc gc ρ α hne, sum_Icc_dlmf_2_9_7]

/-- `T(s, 0) = ρ² + f₀ρ + g₀`. -/
theorem diffT_zero (fc gc : ℕ → ℂ) (ρ α : ℂ) (s : ℕ) :
    diffT fc gc ρ α s 0 = ρ ^ 2 + fc 0 * ρ + gc 0 := by
  simp [diffT]
  ring

/-- `T(s, 1) = −sρ(f₀ + 2ρ)` for `α` from 2.9.6. -/
theorem diffT_one (hρ : ρ ^ 2 + fc 0 * ρ + gc 0 = 0) (hden : fc 0 * ρ + 2 * gc 0 ≠ 0) (s : ℕ) :
    diffT fc gc ρ (diffAlpha fc gc ρ) s 1 = -((s : ℂ) * ρ * (fc 0 + 2 * ρ)) := by
  have hα : diffAlpha fc gc ρ * (fc 0 * ρ + 2 * gc 0) = fc 1 * ρ + gc 1 :=
    div_mul_cancel₀ _ hden
  simp only [diffT, sum_range_succ, sum_range_zero, Ring.choose_one_right,
    Ring.choose_zero_right, Nat.sub_zero, Nat.sub_self, zero_add, pow_one]
  linear_combination 2 * diffAlpha fc gc ρ * hρ - hα

/-- The coefficient identities: `∑_{s≤d} aₛ T(s, d−s) = 0` for every `d`. -/
theorem diffCoeff_vanish (hρ : ρ ^ 2 + fc 0 * ρ + gc 0 = 0) (hg0 : gc 0 ≠ 0)
    (hdist : fc 0 ^ 2 ≠ 4 * gc 0) (d : ℕ) :
    ∑ s ∈ range (d + 1), diffCoeff fc gc ρ (diffAlpha fc gc ρ) s *
      diffT fc gc ρ (diffAlpha fc gc ρ) s (d - s) = 0 := by
  rcases d with _ | m
  · rw [sum_range_one, Nat.sub_self, diffT_zero, hρ, mul_zero]
  · rw [sum_range_succ, Nat.sub_self, diffT_zero, hρ, mul_zero, add_zero, sum_range_succ,
      show m + 1 - m = 1 by omega, diffT_one hρ (alphaDen_ne hρ hg0 hdist)]
    rcases m with _ | k
    · simp
    · have hs := diffCoeff_succ fc gc ρ (diffAlpha fc gc ρ) (diffDen_ne hρ hg0 hdist) k
      have e : ∑ s ∈ range (k + 1), diffCoeff fc gc ρ (diffAlpha fc gc ρ) s *
          diffT fc gc ρ (diffAlpha fc gc ρ) s (k + 1 + 1 - s) =
          ∑ i ∈ range (k + 1), diffCoeff fc gc ρ (diffAlpha fc gc ρ) i *
            diffT fc gc ρ (diffAlpha fc gc ρ) i (k + 2 - i) := rfl
      rw [e]
      linear_combination -hs

/-! ### 2.9.4: the formal solutions -/

/-- `ρⁿ n^α ∑_{s≤N} aₛ/nˢ` (principal branch of `n^α`). -/
noncomputable def formalTrunc (ρ α : ℂ) (a : ℕ → ℂ) (N n : ℕ) : ℂ :=
  ρ ^ n * (n : ℂ) ^ α * ∑ s ∈ range (N + 1), a s / (n : ℂ) ^ s

/-- The truncation `w_N` of the formal solution 2.9.4. -/
noncomputable def diffTrunc (fc gc : ℕ → ℂ) (ρ : ℂ) (N : ℕ) : ℕ → ℂ :=
  formalTrunc ρ (diffAlpha fc gc ρ) (diffCoeff fc gc ρ (diffAlpha fc gc ρ)) N

/-- `(n + k)^β/(n + k)ˢ = n^β n^{−s} (1 + k/n)^{β−s}`. -/
theorem natCast_add_cpow_div (β : ℂ) {n : ℕ} (hn : 1 ≤ n) (k s : ℕ) :
    ((n + k : ℕ) : ℂ) ^ β / ((n + k : ℕ) : ℂ) ^ s =
      (n : ℂ) ^ β * ((n : ℂ)⁻¹) ^ s * (1 + (k : ℂ) * (n : ℂ)⁻¹) ^ (β - s) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hy0 : (0 : ℝ) < 1 + k / n := by positivity
  have hcast : ((n + k : ℕ) : ℂ) = ((n : ℝ) : ℂ) * (((1 + k / n : ℝ)) : ℂ) := by
    push_cast
    field_simp
  have hy : (1 + (k : ℂ) * (n : ℂ)⁻¹) = (((1 + k / n : ℝ)) : ℂ) := by
    push_cast
    ring
  have hyC : (((1 + k / n : ℝ)) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy0.ne'
  rw [hcast, hy, mul_cpow_ofReal_nonneg hn0.le hy0.le, cpow_sub _ _ hyC, cpow_natCast, mul_pow,
    ofReal_natCast]
  have hys : (((1 + k / n : ℝ)) : ℂ) ^ s ≠ 0 := pow_ne_zero _ hyC
  rw [inv_pow]
  field_simp

section Residual

variable {ρ α : ℂ} {a : ℕ → ℂ} {N : ℕ}

theorem formalTrunc_eq (n : ℕ) :
    formalTrunc ρ α a N n = ρ ^ n * (n : ℂ) ^ α * ∑ s ∈ range (N + 1), a s * ((n : ℂ)⁻¹) ^ s := by
  simp only [formalTrunc, div_eq_mul_inv, inv_pow]

theorem formalTrunc_add {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    formalTrunc ρ α a N (n + k) = ρ ^ n * (n : ℂ) ^ α * (ρ ^ k *
      ∑ s ∈ range (N + 1), a s * (((n : ℂ)⁻¹) ^ s * (1 + (k : ℂ) * (n : ℂ)⁻¹) ^ (α - s))) := by
  simp only [formalTrunc, mul_sum]
  refine sum_congr rfl fun s _ => ?_
  rw [show ρ ^ (n + k) * ((n + k : ℕ) : ℂ) ^ α * (a s / ((n + k : ℕ) : ℂ) ^ s) =
    ρ ^ n * ρ ^ k * a s * (((n + k : ℕ) : ℂ) ^ α / ((n + k : ℕ) : ℂ) ^ s) by ring,
    natCast_add_cpow_div α hn k s]
  ring

/-- `ρ²(1 + 2/n)^{α−s} + ρ f(n)(1 + 1/n)^{α−s} + g(n)`. -/
noncomputable def diffBracket (f g : ℕ → ℂ) (ρ α : ℂ) (s n : ℕ) : ℂ :=
  ρ ^ 2 * (1 + 2 * (n : ℂ)⁻¹) ^ (α - s) + ρ * f n * (1 + (n : ℂ)⁻¹) ^ (α - s) + g n

/-- The residual of a truncation: `w(n+2) + f(n) w(n+1) + g(n) w(n)
  = ρⁿ n^α ∑_{s≤N} aₛ n^{−s} (ρ²(1 + 2/n)^{α−s} + ρ f(n)(1 + 1/n)^{α−s} + g(n))`. -/
theorem formalTrunc_residual (f g : ℕ → ℂ) {n : ℕ} (hn : 1 ≤ n) :
    formalTrunc ρ α a N (n + 2) + f n * formalTrunc ρ α a N (n + 1) +
        g n * formalTrunc ρ α a N n =
      ρ ^ n * (n : ℂ) ^ α *
        ∑ s ∈ range (N + 1), a s * (((n : ℂ)⁻¹) ^ s * diffBracket f g ρ α s n) := by
  rw [formalTrunc_add hn 2, formalTrunc_add hn 1, formalTrunc_eq n]
  simp only [Nat.cast_ofNat, Nat.cast_one, one_mul, pow_one, mul_sum, diffBracket,
    ← sum_add_distrib]
  refine sum_congr rfl fun s _ => ?_
  ring

end Residual

/-- The bracket of `formalTrunc_residual` has the asymptotic series `∑ⱼ T(s, j) n^{−j}`. -/
theorem diffBracket_series {f g : ℕ → ℂ} (hf : IsAsympSeqDLMF f fc) (hg : IsAsympSeqDLMF g gc)
    (ρ α : ℂ) (s : ℕ) :
    HasAsympSeries atTop (fun n : ℕ => (n : ℂ)⁻¹) (diffBracket f g ρ α s)
      (diffT fc gc ρ α s) := by
  have hf' := (isAsympSeqDLMF_iff f fc).mp hf
  have hg' := (isAsympSeqDLMF_iff g gc).mp hg
  have h2 := hasAsympSeries_one_add_cpow tendsto_natInv 2 (α - s)
  have h1 := hasAsympSeries_one_add_cpow tendsto_natInv 1 (α - s)
  have h := ((h2.const_mul (ρ ^ 2)).add ((hf'.mul tendsto_natInv h1).const_mul ρ)).add hg'
  refine (h.congr_fun (Eventually.of_forall fun n => ?_)).congr_coeff fun j => ?_
  · simp only [diffBracket, one_mul]
    ring
  · have hre : ∑ i ∈ range (j + 1), fc (j - i) * (Ring.choose (α - s) i * 1 ^ i) =
        ∑ q ∈ range (j + 1), Ring.choose (α - s) (j - q) * fc q := by
      rw [← sum_range_reflect]
      refine sum_congr rfl fun i hi => ?_
      have := mem_range.mp hi
      rw [show j + 1 - 1 - i = j - i by omega, show j - (j - i) = i by omega, one_pow, mul_one,
        mul_comm]
    simp only [seqConv, diffT, hre]
    ring

/-- The formal-solution theorem for any `ρ`, `α`, `a` whose coefficient identities
`∑_{s≤d} aₛ T(s, d−s) = 0` hold for `d ≤ N + 1`: the truncation satisfies 2.9.1 up to
`ρⁿ n^α O(n^{−N−2})`. -/
theorem formalTrunc_isBigO {f g : ℕ → ℂ} (hf : IsAsympSeqDLMF f fc) (hg : IsAsympSeqDLMF g gc)
    {α : ℂ} {a : ℕ → ℂ} (hρ : ρ ^ 2 + fc 0 * ρ + gc 0 = 0) (N : ℕ)
    (hv : ∀ d ≤ N + 1, ∑ s ∈ range (d + 1), a s * diffT fc gc ρ α s (d - s) = 0) :
    ∃ B : ℕ → ℂ, IsBigODLMF atTop B (fun n => ((n : ℂ) ^ (N + 2))⁻¹) ∧
      ∀ n, 1 ≤ n → formalTrunc ρ α a N (n + 2) + f n * formalTrunc ρ α a N (n + 1) +
        g n * formalTrunc ρ α a N n = ρ ^ n * (n : ℂ) ^ α * B n := by
  set B : ℕ → ℂ := fun n => ∑ s ∈ range (N + 1), a s * (((n : ℂ)⁻¹) ^ s * diffBracket f g ρ α s n)
    with hB
  refine ⟨B, ?_, fun n hn => formalTrunc_residual f g hn⟩
  -- the asymptotic series of `B`
  have hser : HasAsympSeries atTop (fun n : ℕ => (n : ℂ)⁻¹) B
      (fun d => ∑ s ∈ range (N + 1), a s * if s ≤ d then diffT fc gc ρ α s (d - s) else 0) :=
    HasAsympSeries.sum _ fun s _ =>
      (((diffBracket_series hf hg ρ α s).pow_mul tendsto_natInv s).const_mul (a s))
  have hzero : ∀ d < N + 2,
      ∑ s ∈ range (N + 1), a s * (if s ≤ d then diffT fc gc ρ α s (d - s) else 0) = 0 := by
    intro d hd
    have hv := hv d (by omega)
    rcases Nat.lt_or_ge d (N + 1) with hdN | hdN
    · rw [← sum_range_add_sum_Ico _ (show d + 1 ≤ N + 1 by omega)]
      have h1 : ∑ s ∈ range (d + 1), a s * (if s ≤ d then diffT fc gc ρ α s (d - s) else 0) =
          0 := by
        rw [← hv]
        refine sum_congr rfl fun s hs => ?_
        simp only [show s ≤ d from Nat.lt_succ_iff.mp (mem_range.mp hs), ↓reduceIte]
      have h2 : ∑ s ∈ Ico (d + 1) (N + 1),
          a s * (if s ≤ d then diffT fc gc ρ α s (d - s) else 0) = 0 := by
        refine sum_eq_zero fun s hs => ?_
        simp only [show ¬s ≤ d by have := (mem_Ico.mp hs).1; omega, ↓reduceIte, mul_zero]
      rw [h1, h2, add_zero]
    · obtain rfl : d = N + 1 := by omega
      rw [sum_range_succ, Nat.sub_self, diffT_zero, hρ, mul_zero, add_zero] at hv
      rw [← hv]
      refine sum_congr rfl fun s hs => ?_
      simp only [show s ≤ N + 1 by have := mem_range.mp hs; omega, ↓reduceIte]
  have hO : B =O[atTop] fun n : ℕ => ((n : ℂ)⁻¹) ^ (N + 2) := by
    refine (hser (N + 2)).congr_left fun n => ?_
    rw [sum_eq_zero fun d hd => by simp only [hzero d (mem_range.mp hd), zero_mul], sub_zero]
  refine (dlmf_2_1_3 (eventually_natPow_inv_ne_zero (N + 2))).mpr ?_
  simpa only [inv_pow] using hO

/-- **DLMF 2.9.4**: for `f`, `g` as in 2.9.3 with `g₀ ≠ 0` and `f₀² ≠ 4g₀` (`ρ₁ ≠ ρ₂`), a root `ρ`
of 2.9.5, `α` from 2.9.6 and `aₛ` from 2.9.7, `ρⁿ n^α ∑ aₛ/nˢ` is a formal solution of 2.9.1: each
truncation `w_N = diffTrunc` satisfies `w_N(n+2) + f(n) w_N(n+1) + g(n) w_N(n) = ρⁿ n^α B_N(n)`
for `n ≥ 1`, with `B_N(n) = O(n^{−N−2})` as `n → ∞`. -/
theorem dlmf_2_9_4 {f g : ℕ → ℂ} (hf : IsAsympSeqDLMF f fc) (hg : IsAsympSeqDLMF g gc)
    (hρ : ρ ^ 2 + fc 0 * ρ + gc 0 = 0) (hg0 : gc 0 ≠ 0) (hdist : fc 0 ^ 2 ≠ 4 * gc 0) (N : ℕ) :
    ∃ B : ℕ → ℂ, IsBigODLMF atTop B (fun n => ((n : ℂ) ^ (N + 2))⁻¹) ∧
      ∀ n, 1 ≤ n → diffTrunc fc gc ρ N (n + 2) + f n * diffTrunc fc gc ρ N (n + 1) +
        g n * diffTrunc fc gc ρ N n = ρ ^ n * (n : ℂ) ^ diffAlpha fc gc ρ * B n :=
  formalTrunc_isBigO hf hg hρ N fun d _ => diffCoeff_vanish hρ hg0 hdist d

end Azurite.DLMF
