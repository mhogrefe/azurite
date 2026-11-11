/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section11Stirling
import Azurite.DLMF.Chapter2.Section3LaplaceSeries

/-!
# DLMF §5.11(i): the coefficients of 5.11.8

Formal power-series side of <https://dlmf.nist.gov/5.11#E8>. With `w = 1/z`,
`1/(z + h) = w (1 + hw)^{−1}` (`shiftV`), and the coefficients of
`Ln Γ(z + h) − (z + h − ½) ln z + z − ½ ln(2π)` are those of Stirling's series composed with
`w (1 + hw)^{−1}` plus those of `(1/w + h − ½) ln(1 + hw) − h`. Their sum is
`(−1)ᵏ Bₖ(h)/(k(k − 1))` (`lnGammaShiftCoeff`), by
`Bₙ(h) = ∑ C(n, i) Bᵢ h^{n−i}` and `(k + 2)(k + 1) C(k, d) = C(k + 2, d + 2)(d + 2)(d + 1)`
(`coeff_lnGammaShift_series`).
-/

open Filter Topology Set PowerSeries
open scoped Real

namespace Azurite.DLMF

/-- `(1 + hX)^{−1} = ∑ (−h)ʲ Xʲ`. -/
noncomputable def shiftV (h : ℂ) : ℂ⟦X⟧ := mk fun j => (-h) ^ j

theorem shiftV_eq (h : ℂ) : shiftV h = rescale (-h) (mk 1) := by
  rw [rescale_mk]; ext j; simp [shiftV]

theorem shiftV_mul (h : ℂ) : shiftV h * (1 + C h * X) = 1 := by
  have e : (1 : ℂ⟦X⟧) + C h * X = rescale (-h) (1 - X) := by
    rw [map_sub, map_one, rescale_X, map_neg, neg_mul, sub_neg_eq_add]
  rw [shiftV_eq, e, ← map_mul, mk_one_mul_one_sub_eq_one, map_one]

theorem shiftV_eq_inv (h : ℂ) : shiftV h = (1 + C h * X)⁻¹ :=
  (PowerSeries.eq_inv_iff_mul_eq_one (by simp)).mpr (shiftV_mul h)

theorem coeff_shiftV_pow (h : ℂ) (d j : ℕ) :
    coeff j (shiftV h ^ (d + 1)) = (-h) ^ j * ((d + j).choose d : ℂ) := by
  rw [shiftV_eq, ← map_pow, mk_one_pow_eq_mk_choose_add, coeff_rescale, coeff_mk]

theorem coeff_shiftU_pow (h : ℂ) {d n : ℕ} (hd : d < n) :
    coeff n ((X * shiftV h) ^ (d + 1)) = (-h) ^ (n - 1 - d) * ((n - 1).choose d : ℂ) := by
  have hd' : d + 1 ≤ n := hd
  rw [mul_pow, coeff_X_pow_mul']
  simp only [hd', ↓reduceIte]
  rw [coeff_shiftV_pow, show d + (n - (d + 1)) = n - 1 by omega,
    show n - (d + 1) = n - 1 - d by omega]

theorem algebraMap_eq_C' (c : ℂ) : algebraMap ℂ ℂ⟦X⟧ c = C c := by
  ext; simp [coeff_C]

/-- The coefficients of `S(w (1 + hw)^{−1})` as finite sums. -/
theorem coeff_subst_shiftU (S : ℂ⟦X⟧) (h : ℂ) (n : ℕ) :
    coeff n (S.subst (X * shiftV h)) =
      ∑ m ∈ Finset.range (n + 1), coeff m S * coeff n ((X * shiftV h) ^ m) := by
  have hU0 : constantCoeff (X * shiftV h) = 0 := by simp
  have e := congrArg (fun p : Polynomial ℂ => p.coeff n) (trunc_aeval_trunc hU0 S (n + 1))
  simp only [coeff_trunc, lt_add_one n, ↓reduceIte] at e
  rw [← e, Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range' _ (natDegree_trunc_lt S n),
    map_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [coeff_trunc, ite_eq_left (Finset.mem_range.mp hm), algebraMap_eq_C', coeff_C_mul]

/-- `Bₙ(h) = ∑ C(n, i) Bᵢ h^{n−i}`. -/
theorem aeval_bernoulli_eq (N : ℕ) (h : ℂ) :
    Polynomial.aeval h (Polynomial.bernoulli N) =
      ∑ i ∈ Finset.range (N + 1), (bernoulli i : ℂ) * (N.choose i : ℂ) * h ^ (N - i) := by
  rw [Polynomial.bernoulli_def, map_sum, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  rw [Polynomial.aeval_monomial, show N + 1 - 1 - i = N - i by omega,
    Nat.sub_sub_self (by omega), Nat.choose_symm (by omega)]
  simp

/-- The `ℓⱼ = (−1)^{j+1} hʲ/j` of `ln(1 + hw) = ∑ ℓⱼ wʲ`. -/
noncomputable def logShiftCoeff (h : ℂ) (j : ℕ) : ℂ := (-1) ^ (j + 1) * h ^ j / j

theorem choose_identity (k d : ℕ) :
    ((k + 2 : ℕ) : ℂ) * ((k + 1 : ℕ) : ℂ) * (k.choose d : ℂ) =
      ((k + 2).choose (d + 2) : ℂ) * ((d + 2 : ℕ) : ℂ) * ((d + 1 : ℕ) : ℂ) := by
  have h1 := Nat.add_one_mul_choose_eq k d
  have h2 := Nat.add_one_mul_choose_eq (k + 1) (d + 1)
  have : (k + 2) * (k + 1) * k.choose d = (k + 2).choose (d + 2) * (d + 2) * (d + 1) := by
    rw [mul_assoc, h1, ← mul_assoc, h2]
  exact_mod_cast this

theorem stirlingSeriesCoeff_term (h : ℂ) {k d : ℕ} (hd : d ≤ k) :
    stirlingSeriesCoeff (d + 1) * ((-h) ^ (k - d) * (k.choose d : ℂ)) =
      (-1) ^ k * ((bernoulli (d + 2) : ℂ) * ((k + 2).choose (d + 2) : ℂ) * h ^ (k + 2 - (d + 2))) /
        (((k + 2 : ℕ) : ℂ) * ((k + 1 : ℕ) : ℂ)) := by
  simp only [stirlingSeriesCoeff, Nat.add_one_ne_zero, ↓reduceIte]
  rw [show k + 2 - (d + 2) = k - d by omega, show d + 1 + 1 = d + 2 by omega]
  rcases Nat.even_or_odd d with he | ho
  · have hs : (-1 : ℂ) ^ k = (-1) ^ (k - d) * (-1) ^ d := by
      rw [← pow_add, Nat.sub_add_cancel hd]
    rw [he.neg_one_pow, mul_one] at hs
    rw [neg_pow, hs]
    have hc := choose_identity k d
    push_cast at hc ⊢
    rw [show (d : ℂ) + 1 + 1 = d + 2 by ring]
    have h1 : (d : ℂ) + 2 ≠ 0 := by norm_cast
    have h2 : (d : ℂ) + 1 ≠ 0 := by norm_cast
    have h3 : (k : ℂ) + 2 ≠ 0 := by norm_cast
    have h4 : (k : ℂ) + 1 ≠ 0 := by norm_cast
    field_simp
    linear_combination h ^ (k - d) * (bernoulli (d + 2) : ℂ) * hc
  · have hB : bernoulli (d + 2) = 0 :=
      bernoulli_eq_zero_of_odd (ho.add_even even_two) (by omega)
    simp [hB]

/-- The coefficient identity behind 5.11.8 (index `k + 1`). -/
theorem lnGammaShift_key (h : ℂ) (k : ℕ) :
    ∑ d ∈ Finset.range (k + 1), stirlingSeriesCoeff (d + 1) * ((-h) ^ (k - d) * (k.choose d : ℂ)) +
        logShiftCoeff h (k + 2) + (h - 1 / 2) * logShiftCoeff h (k + 1) =
      (-1) ^ k * Polynomial.aeval h (Polynomial.bernoulli (k + 2)) /
        (((k + 2 : ℕ) : ℂ) * ((k + 1 : ℕ) : ℂ)) := by
  have hB := aeval_bernoulli_eq (k + 2) h
  rw [Finset.sum_range_succ', Finset.sum_range_succ'] at hB
  rw [Finset.sum_congr rfl fun d hd => stirlingSeriesCoeff_term h
      (by have := Finset.mem_range.mp hd; omega), hB]
  simp only [← Finset.sum_div, ← Finset.mul_sum]
  generalize ∑ i ∈ Finset.range (k + 1), (bernoulli (i + 2) : ℂ) * ((k + 2).choose (i + 2) : ℂ) *
    h ^ (k + 2 - (i + 2)) = T
  simp only [logShiftCoeff, bernoulli_zero, Nat.choose_one_right,
    Nat.choose_zero_right, show k + 2 - (0 + 1) = k + 1 by omega, Nat.sub_zero, zero_add]
  have h3 : ((k + 2 : ℕ) : ℂ) ≠ 0 := by norm_cast
  have h4 : ((k + 1 : ℕ) : ℂ) ≠ 0 := by norm_cast
  push_cast at h3 h4 ⊢
  rw [show (bernoulli 1 : ℂ) = -1 / 2 by norm_num [bernoulli_one]]
  field_simp
  ring

/-- The coefficients `(−1)^{n+1} B_{n+1}(h)/((n + 1)n)` of 5.11.8 (`n = k − 1`; `0` for `n = 0`). -/
noncomputable def lnGammaShiftCoeff (h : ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else
    (-1) ^ (n + 1) * Polynomial.aeval h (Polynomial.bernoulli (n + 1)) / (((n : ℂ) + 1) * n)

/-- `ln(1 + hw)` as a power series in `w`. -/
noncomputable def logShiftSeries (h : ℂ) : ℂ⟦X⟧ := mk (logShiftCoeff h)

/-- The series of `J(z + h) + (1/w + h − ½) ln(1 + hw) − h`, `w = 1/z`. -/
noncomputable def lnGammaShiftSeries (h : ℂ) : ℂ⟦X⟧ :=
  (mk stirlingSeriesCoeff).subst (X * shiftV h) + mk (fun j => coeff (j + 1) (logShiftSeries h)) +
    C (h - 1 / 2) * logShiftSeries h - C h

theorem lnGammaShiftSeries_eq (h : ℂ) : lnGammaShiftSeries h = mk (lnGammaShiftCoeff h) := by
  ext n
  rw [lnGammaShiftSeries, map_sub, map_add, map_add, coeff_C_mul, coeff_C, coeff_mk,
    coeff_subst_shiftU, logShiftSeries, coeff_mk, coeff_mk, coeff_mk]
  cases n with
  | zero => simp [stirlingSeriesCoeff, logShiftCoeff, lnGammaShiftCoeff]
  | succ k =>
    rw [Finset.sum_range_succ']
    simp only [coeff_mk]
    have hs : ∀ d ∈ Finset.range (k + 1), stirlingSeriesCoeff (d + 1) *
        coeff (k + 1) ((X * shiftV h) ^ (d + 1)) =
        stirlingSeriesCoeff (d + 1) * ((-h) ^ (k - d) * (k.choose d : ℂ)) := fun d hd => by
      rw [coeff_shiftU_pow h (by have := Finset.mem_range.mp hd; omega),
        show k + 1 - 1 - d = k - d by omega, Nat.add_sub_cancel]
    rw [Finset.sum_congr rfl hs]
    have hk := lnGammaShift_key h k
    have h0 : stirlingSeriesCoeff 0 = 0 := by simp [stirlingSeriesCoeff]
    simp only [h0, zero_mul, add_zero, Nat.add_one_ne_zero, ↓reduceIte, sub_zero,
      lnGammaShiftCoeff] at hk ⊢
    rw [show k + 1 + 1 = k + 2 from rfl]
    push_cast at hk ⊢
    linear_combination hk

end Azurite.DLMF
