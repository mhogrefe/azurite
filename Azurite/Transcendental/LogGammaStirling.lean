/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section11Bounds
import Azurite.BrentZimmermann.Chapter4.TangentNumbers

/-!
# Stirling's series for `ln Γ` with its remainder, in tangent numbers

For `x > 0` (DLMF 5.11.1 and §5.11(ii), `Azurite/DLMF/Chapter5/Section11Bounds.lean`),

  `ln Γ(x) = (x − ½) ln x − x + ½ ln (2π) + ∑_{k=1}^{n−1} B_{2k} / (2k (2k−1) x^(2k−1)) + r`,

where the remainder `r` has the sign of the first neglected term and is at most that term in
magnitude.  With the tangent numbers `T_k` (`B_{2k} = (−1)^(k−1) 2k T_k / (4^(2k) − 2^(2k))`,
Brent–Zimmermann (4.62)) the coefficients are

  `B_{2k} / (2k (2k−1)) = (−1)^(k+1) a_k`,   `a_k = T_k / ((2k−1) (4^(2k) − 2^(2k))) > 0`

(`stirlingCoeffT`, `bernoulli_div_eq_stirlingCoeffT`): a positive integer over a positive
integer, with the sign explicit — the form the enclosure arithmetic of
`AzFloat/LnGammaBracket.lean` consumes.  `stirlingMu_eq_sum_add` is the statement used there:
`μ(x) = ln Γ(x) − (x − ½) ln x + x − ½ ln (2π) = ∑_{i<n−1} t_{i+1}(x) + r` with
`0 ≤ (−1)^(n+1) r ≤ a_n / x^(2n−1)`, for every `n ≥ 1`.
-/

namespace Azurite

open Finset

/-- The positive coefficient `a_k = T_k / ((2k−1) (4^(2k) − 2^(2k)))` of Stirling's series. -/
noncomputable def stirlingCoeffT (k : ℕ) : ℝ :=
  (BZ.tangentNumber k : ℝ) / ((2 * k - 1) * ((4 : ℝ) ^ (2 * k) - 2 ^ (2 * k)))

theorem four_pow_sub_two_pow_pos {k : ℕ} (hk : 1 ≤ k) :
    (0 : ℝ) < (4 : ℝ) ^ (2 * k) - 2 ^ (2 * k) := by
  have h : (2 : ℝ) ^ (2 * k) < 4 ^ (2 * k) :=
    pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
  linarith

theorem stirlingCoeffT_pos {k : ℕ} (hk : 1 ≤ k) : 0 < stirlingCoeffT k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hT : (0 : ℝ) < (BZ.tangentNumber (j + 1) : ℝ) := by exact_mod_cast BZ.tangentNumber_pos j
  have h1 : (0 : ℝ) < 2 * ((j + 1 : ℕ) : ℝ) - 1 := by
    push_cast; linarith [Nat.cast_nonneg (α := ℝ) j]
  exact div_pos hT (mul_pos h1 (four_pow_sub_two_pow_pos hk))

/-- `B_{2k} / (2k (2k−1)) = (−1)^(k+1) a_k` for `k ≥ 1`. -/
theorem bernoulli_div_eq_stirlingCoeffT {k : ℕ} (hk : 1 ≤ k) :
    (bernoulli (2 * k) : ℝ) / (2 * k * (2 * k - 1)) = (-1) ^ (k + 1) * stirlingCoeffT k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h := congrArg (Rat.cast : ℚ → ℝ) (BZ.bernoulli_two_mul_eq_tangentNumber j)
  push_cast at h
  have hd := four_pow_sub_two_pow_pos (k := j + 1) (by omega)
  have h1 : (0 : ℝ) < 2 * ((j + 1 : ℕ) : ℝ) - 1 := by
    push_cast; linarith [Nat.cast_nonneg (α := ℝ) j]
  have h2 : (0 : ℝ) < 2 * ((j + 1 : ℕ) : ℝ) := by positivity
  rw [h, stirlingCoeffT, show (-1 : ℝ) ^ (j + 1 + 1) = (-1) ^ j by rw [pow_succ, pow_succ]; ring]
  push_cast at hd h1 h2 ⊢
  field_simp

/-- The term of index `k ≥ 1` of Stirling's series, `(−1)^(k+1) a_k / x^(2k−1)`. -/
noncomputable def stirlingTermT (k : ℕ) (x : ℝ) : ℝ :=
  (-1) ^ (k + 1) * stirlingCoeffT k / x ^ (2 * k - 1)

/-- The remainder of DLMF's series after the terms `k = 1, …, n − 1`, for a real argument. -/
theorem stirlingSeriesRem_eq_stirlingMu_sub {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    DLMF.stirlingSeriesRem n x
      = ((DLMF.stirlingMu x - ∑ i ∈ range (n - 1), stirlingTermT (i + 1) x : ℝ) : ℂ) := by
  induction n, hn using Nat.le_induction with
  | base =>
    simp [DLMF.stirlingSeriesRem, DLMF.stirlingSeriesCoeff, DLMF.stirlingJ_ofReal,
      DLMF.stirlingJR_eq_stirlingMu hx]
  | succ n hn ih =>
    have hs := DLMF.stirlingSeriesRem_succ hn (x : ℂ)
    rw [ih, DLMF.stirlingFirst_ofReal hn] at hs
    have e : DLMF.stirlingSeriesRem (n + 1) x
        = ((DLMF.stirlingMu x - ∑ i ∈ range (n - 1), stirlingTermT (i + 1) x : ℝ) : ℂ)
          - (((bernoulli (2 * n) : ℝ) / (2 * n * (2 * n - 1) * x ^ (2 * n - 1)) : ℝ) : ℂ) := by
      rw [hs]; ring
    rw [e, ← Complex.ofReal_sub, show n + 1 - 1 = (n - 1) + 1 by omega, sum_range_succ,
      show n - 1 + 1 = n by omega]
    congr 1
    have hb := bernoulli_div_eq_stirlingCoeffT hn
    rw [stirlingTermT, ← hb]
    have hx' : x ^ (2 * n - 1) ≠ 0 := (pow_pos hx _).ne'
    field_simp
    ring

/-- **Stirling's series with its remainder**: for `x > 0` and `n ≥ 1`,
`μ(x) = ∑_{i<n−1} t_{i+1}(x) + r` with `0 ≤ (−1)^(n+1) r` and `|r| ≤ a_n / x^(2n−1)`. -/
theorem stirlingMu_eq_sum_add {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    ∃ r : ℝ, DLMF.stirlingMu x = ∑ i ∈ range (n - 1), stirlingTermT (i + 1) x + r ∧
      0 ≤ (-1) ^ (n + 1) * r ∧ |r| ≤ stirlingCoeffT n / x ^ (2 * n - 1) := by
  obtain ⟨r, τ, hr, hτ, habs, hsign⟩ := DLMF.dlmf_5_11_ii_real hn hx
  rw [stirlingSeriesRem_eq_stirlingMu_sub hn hx, Complex.ofReal_inj] at hr
  rw [DLMF.stirlingFirst_ofReal hn, Complex.ofReal_inj] at hτ
  have hxp : 0 < x ^ (2 * n - 1) := pow_pos hx _
  have hc := stirlingCoeffT_pos hn
  have hτ' : τ = (-1) ^ (n + 1) * (stirlingCoeffT n / x ^ (2 * n - 1)) := by
    rw [← hτ, ← mul_div_assoc, ← bernoulli_div_eq_stirlingCoeffT hn]
    field_simp
  have hq : 0 < stirlingCoeffT n / x ^ (2 * n - 1) := div_pos hc hxp
  have hsq : ((-1 : ℝ) ^ (n + 1)) * ((-1 : ℝ) ^ (n + 1)) = 1 := by
    rw [← mul_pow]; norm_num
  refine ⟨r, by rw [← hr]; ring, ?_, ?_⟩
  · rw [hτ'] at hsign
    have : 0 ≤ ((-1 : ℝ) ^ (n + 1) * r) * (stirlingCoeffT n / x ^ (2 * n - 1)) := by
      nlinarith [hsign]
    exact nonneg_of_mul_nonneg_left this hq
  · rw [hτ', abs_mul, abs_of_pos hq] at habs
    rcases neg_one_pow_eq_or ℝ (n + 1) with h | h <;> rw [h] at habs <;> simpa using habs

end Azurite
