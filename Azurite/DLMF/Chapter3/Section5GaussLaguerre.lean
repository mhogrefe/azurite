/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section5GaussJacobi
import Mathlib.Algebra.Group.ForwardDiff

/-!
# DLMF §3.5(v): the Gauss–Laguerre formula

Formula 3.5.27, for every `α > −1` ("generalized Gauss–Laguerre formula" when `α ≠ 0`).

* The weight `lagW α x = x^α e^{−x}` on `(0, ∞)`: `isGaussWeight_lagW`, moments
  `wInt_lagW_X_pow` (`∫ x^k w = Γ(k + α + 1)`).
* The monic Laguerre polynomials `lagMonic α n` (coefficients
  `(−1)^{n−j} C(n, j) Γ(n + α + 1)/Γ(j + α + 1)`), `lagMonic_monic`, `natDegree_lagMonic`,
  and `lagMonic_eq_lagL`: `p_n = (−1)^n n! L_n^{(α)}` with `lagL` the explicit sum 18.5.12
  ("the `p_n` are the monic Laguerre polynomials").
* Orthogonality via forward differences of `lagQ` (`sum_alt_choose_eq_fwdDiff`,
  `wInt_lagMonic_mul_X_pow`), `isOrthMonic_lagMonic`.
* 3.5.27: `dlmf_3_5_27` (`γ_n = n! Γ(n + α + 1)`).
* For `α = 0`: `eval_lagL_zero` and `christoffel_laguerre` (`w_k = 1/∑_{j<n} L_j(x_k)²`), used
  for Tables 3.5.6–3.5.9 in `Section5GaussLaguerreTables`.
-/

open Polynomial Finset Set MeasureTheory Real

namespace Azurite.DLMF

/-! ### The weight `x^α e^{−x}` on `(0, ∞)` -/

/-- The Laguerre weight `w(x) = x^α e^{−x}`. -/
noncomputable def lagW (α x : ℝ) : ℝ := x ^ α * exp (-x)

theorem lagW_pow_eq {α : ℝ} (k : ℕ) {x : ℝ} (hx : 0 < x) :
    x ^ k * lagW α x = exp (-x) * x ^ ((k + α + 1) - 1) := by
  rw [lagW, show (k : ℝ) + α + 1 - 1 = k + α by ring, rpow_add hx, rpow_natCast]; ring

/-- `x^α e^{−x}` is a Gauss weight on `(0, ∞)` for `α > −1`. -/
theorem isGaussWeight_lagW {α : ℝ} (hα : -1 < α) : IsGaussWeight (Ioi 0) (lagW α) where
  isOpen := isOpen_Ioi
  ordConnected := ordConnected_Ioi
  nonempty := ⟨1, by norm_num⟩
  pos := fun x hx => mul_pos (rpow_pos_of_pos hx _) (exp_pos _)
  integrableOn := fun k => by
    have hk : (0 : ℝ) ≤ k := k.cast_nonneg
    refine (GammaIntegral_convergent (s := k + α + 1) (by linarith)).congr_fun
      (fun x hx => (lagW_pow_eq k hx).symm) measurableSet_Ioi

/-- The moments `∫₀^∞ x^k x^α e^{−x} dx = Γ(k + α + 1)`. -/
theorem wInt_lagW_X_pow {α : ℝ} (hα : -1 < α) (k : ℕ) :
    wInt (Ioi 0) (lagW α) (X ^ k) = Gamma (k + α + 1) := by
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  rw [Gamma_eq_integral (by linarith), wInt]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  simp only [eval_pow, eval_X]
  exact lagW_pow_eq k hx

/-! ### The monic Laguerre polynomials -/

/-- The coefficients `(−1)^{n−j} C(n, j) Γ(n + α + 1)/Γ(j + α + 1)` of the monic Laguerre
polynomial. -/
noncomputable def laguerreCoeff (α : ℝ) (n j : ℕ) : ℝ :=
  (-1) ^ (n - j) * n.choose j * (Gamma (n + α + 1) / Gamma (j + α + 1))

/-- The monic Laguerre polynomial `p_n = (−1)ⁿ n! L_n^{(α)}`. -/
noncomputable def lagMonic (α : ℝ) (n : ℕ) : ℝ[X] :=
  ∑ j ∈ range (n + 1), C (laguerreCoeff α n j) * X ^ j

/-- The Laguerre polynomial `L_n^{(α)}(x) = ∑_ℓ Γ(n+α+1)/(Γ(ℓ+α+1) (n−ℓ)! ℓ!) (−x)^ℓ` (18.5.12). -/
noncomputable def lagL (α : ℝ) (n : ℕ) : ℝ[X] :=
  ∑ j ∈ range (n + 1), C ((-1) ^ j * (Gamma (n + α + 1) /
    (Gamma (j + α + 1) * (n - j).factorial * j.factorial))) * X ^ j

theorem coeff_lagMonic (α : ℝ) (n j : ℕ) :
    (lagMonic α n).coeff j = if j ≤ n then laguerreCoeff α n j else 0 := by
  simp only [lagMonic, finsetSum_coeff, coeff_C_mul_X_pow]
  split_ifs with h
  · rw [sum_eq_single_of_mem j (mem_range.mpr (by omega)) fun i _ hij => by
      simp [Ne.symm hij]]
    simp
  · exact sum_eq_zero fun i hi => by
      have := mem_range.mp hi
      simp [show j ≠ i by omega]

theorem lagMonic_monic {α : ℝ} (hα : -1 < α) (n : ℕ) : (lagMonic α n).Monic := by
  have hle : (lagMonic α n).natDegree ≤ n := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro j hj
    simp [coeff_lagMonic, show ¬ j ≤ n by omega]
  have hn : (lagMonic α n).coeff n = 1 := by
    simp only [coeff_lagMonic, le_refl, ↓reduceIte]
    rw [laguerreCoeff, Nat.sub_self, pow_zero, Nat.choose_self,
      div_self (Gamma_pos_of_pos (by linarith)).ne']
    simp
  rw [Monic, leadingCoeff, le_antisymm hle (le_natDegree_of_ne_zero (by rw [hn]; norm_num)), hn]

theorem natDegree_lagMonic {α : ℝ} (hα : -1 < α) (n : ℕ) : (lagMonic α n).natDegree = n := by
  apply le_antisymm
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro j hj
    simp [coeff_lagMonic, show ¬ j ≤ n by omega]
  · apply le_natDegree_of_ne_zero
    simp only [coeff_lagMonic, le_refl, ↓reduceIte]
    rw [laguerreCoeff, Nat.sub_self, pow_zero, Nat.choose_self,
      div_self (Gamma_pos_of_pos (by linarith)).ne']
    norm_num

/-- "The `p_n(x)` are the monic Laguerre polynomials": `p_n = (−1)ⁿ n! L_n^{(α)}`. -/
theorem lagMonic_eq_lagL {α : ℝ} (hα : -1 < α) (n : ℕ) :
    lagMonic α n = C ((-1 : ℝ) ^ n * n.factorial) * lagL α n := by
  rw [lagMonic, lagL, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  have hj := mem_range.mp hj
  rw [← mul_assoc, ← C_mul, laguerreCoeff]
  congr 2
  have hG := (Gamma_pos_of_pos (show (0 : ℝ) < j + α + 1 by linarith)).ne'
  rw [Nat.choose_eq_factorial_div_factorial (by omega), Nat.cast_div
    (Nat.factorial_mul_factorial_dvd_factorial (by omega)) (by positivity)]
  push_cast
  have hpow : (-1 : ℝ) ^ n = (-1) ^ (n - j) * (-1) ^ j := by
    rw [← pow_add, Nat.sub_add_cancel (by omega)]
  rw [show (-1 : ℝ) ^ (n - j) = (-1) ^ n * (-1) ^ j by
    rw [hpow, mul_assoc, ← pow_add, ← two_mul, pow_mul]; norm_num]
  have : ((j.factorial : ℝ)) ≠ 0 := by positivity
  have : (((n - j).factorial : ℝ)) ≠ 0 := by positivity
  field_simp

/-! ### Orthogonality and `γ_n` by finite differences -/

/-- `Q_m(t) = ∏_{i<m} (t + α + 1 + i)`, so that `Γ(t + m + α + 1) = Γ(t + α + 1) Q_m(t)`. -/
noncomputable def lagQ (α : ℝ) (m : ℕ) : ℝ[X] := ∏ i ∈ range m, (X + C (α + 1 + i))

theorem lagQ_monic (α : ℝ) (m : ℕ) : (lagQ α m).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_add_C _

theorem natDegree_lagQ (α : ℝ) (m : ℕ) : (lagQ α m).natDegree = m := by
  rw [lagQ, natDegree_prod_of_monic _ _ fun _ _ => monic_X_add_C _]
  simp only [natDegree_X_add_C, sum_const, card_range, smul_eq_mul, mul_one]

/-- `∑_{j≤n} (−1)^{n−j} C(n, j) Q(j)` is the `n`-th forward difference of `Q` at `0`. -/
theorem sum_alt_choose_eq_fwdDiff (Q : ℝ[X]) (n : ℕ) :
    ∑ j ∈ range (n + 1), (-1 : ℝ) ^ (n - j) * n.choose j * Q.eval (j : ℝ) =
      (fwdDiff 1)^[n] (fun t => Q.eval t) 0 := by
  rw [fwdDiff_iter_eq_sum_shift]
  refine sum_congr rfl fun j _ => ?_
  simp [zsmul_eq_mul]

theorem wInt_lagMonic_mul_X_pow {α : ℝ} (hα : -1 < α) (n m : ℕ) :
    wInt (Ioi 0) (lagW α) (lagMonic α n * X ^ m) =
      Gamma (n + α + 1) * (fwdDiff 1)^[n] (fun t => (lagQ α m).eval t) 0 := by
  have hw := isGaussWeight_lagW hα
  rw [← sum_alt_choose_eq_fwdDiff, lagMonic, sum_mul, wInt_sum hw, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  have hs : (0 : ℝ) < j + α + 1 := by have : (0 : ℝ) ≤ j := j.cast_nonneg; linarith
  rw [mul_assoc, ← pow_add, wInt_C_mul, wInt_lagW_X_pow hα, laguerreCoeff,
    show ((j + m : ℕ) : ℝ) + α + 1 = (j + α + 1) + m by push_cast; ring,
    jacGamma_add_nat hs m, lagQ, eval_prod]
  simp only [eval_add, eval_X, eval_C]
  have hG := (Gamma_pos_of_pos hs).ne'
  field_simp
  exact congrArg _ (prod_congr rfl fun i _ => by ring)

/-- **DLMF 3.5.27** (orthogonality): the monic Laguerre polynomials are the monic orthogonal
polynomials of `x^α e^{−x}` on `(0, ∞)`. -/
theorem isOrthMonic_lagMonic {α : ℝ} (hα : -1 < α) (n : ℕ) :
    IsOrthMonic (Ioi 0) (lagW α) n (lagMonic α n) := by
  have hw := isGaussWeight_lagW hα
  refine ⟨lagMonic_monic hα n, natDegree_lagMonic hα n, fun q hq => ?_⟩
  by_cases hq0 : q = 0
  · rw [hq0, mul_zero, wInt_zero]
  rw [as_sum_range' q n ((natDegree_lt_iff_degree_lt hq0).mpr hq), mul_sum, wInt_sum hw]
  refine sum_eq_zero fun m hm => ?_
  rw [← C_mul_X_pow_eq_monomial, mul_left_comm, wInt_C_mul, wInt_lagMonic_mul_X_pow hα,
    Polynomial.fwdDiff_iter_eq_zero_of_degree_lt (by rw [natDegree_lagQ]; exact mem_range.mp hm)]
  simp

/-- **DLMF 3.5.27**: `γ_n = n! Γ(n + α + 1)`. -/
theorem dlmf_3_5_27 {α : ℝ} (hα : -1 < α) (n : ℕ) :
    gaussGamma (Ioi 0) (lagW α) (lagMonic α n) = n.factorial * Gamma (n + α + 1) := by
  have hw := isGaussWeight_lagW hα
  have hp := lagMonic_monic hα n
  have hdeg : (lagMonic α n - X ^ n).degree < (n : WithBot ℕ) := by
    have h := degree_sub_lt_left (p := lagMonic α n) (q := X ^ n)
      (by rw [degree_eq_natDegree hp.ne_zero, natDegree_lagMonic hα, degree_X_pow])
      hp.ne_zero (by rw [hp.leadingCoeff, (monic_X_pow n).leadingCoeff])
    rwa [degree_eq_natDegree hp.ne_zero, natDegree_lagMonic hα] at h
  rw [gaussGamma, show lagMonic α n * lagMonic α n = lagMonic α n * (lagMonic α n - X ^ n) +
      lagMonic α n * X ^ n by ring, wInt_add hw, (isOrthMonic_lagMonic hα n).wInt_mul_eq_zero hdeg,
    zero_add, wInt_lagMonic_mul_X_pow hα]
  have h := (lagQ α n).fwdDiff_iter_degree_eq_factorial
  rw [natDegree_lagQ, (lagQ_monic α n).leadingCoeff] at h
  rw [h]
  simp [mul_comm]

/-! ### The weights for `α = 0` -/

/-- `L_j(x) = ∑_i (−1)^i C(j, i) x^i/i!` (`α = 0`). -/
theorem eval_lagL_zero (j : ℕ) (x : ℝ) :
    (lagL 0 j).eval x = ∑ i ∈ range (j + 1), (-1) ^ i * j.choose i / i.factorial * x ^ i := by
  rw [lagL, eval_finsetSum]
  refine sum_congr rfl fun i hi => ?_
  have hi := mem_range.mp hi
  simp only [eval_mul, eval_C, eval_pow, eval_X, add_zero]
  rw [show (j : ℝ) + 1 = ((j : ℕ) : ℝ) + 1 from rfl, Gamma_nat_eq_factorial,
    Gamma_nat_eq_factorial, Nat.choose_eq_factorial_div_factorial (by omega),
    Nat.cast_div (Nat.factorial_mul_factorial_dvd_factorial (by omega)) (by positivity)]
  push_cast
  have : (i.factorial : ℝ) ≠ 0 := by positivity
  have : ((j - i).factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- The Gauss–Laguerre weights (`α = 0`): `w_k = 1/∑_{j<n} L_j(x_k)²`. -/
theorem christoffel_laguerre (n : ℕ) {xk : ℝ} (hk : xk ∈ (lagMonic 0 n).roots.toFinset) :
    christoffel (Ioi 0) (lagW 0) (lagMonic 0 n) xk =
      1 / ∑ j ∈ range n, (lagL 0 j).eval xk ^ 2 := by
  have h := christoffel_mul_sum (isGaussWeight_lagW (by norm_num : (-1 : ℝ) < 0))
    (isOrthMonic_lagMonic (by norm_num)) n hk
  have hterm : ∀ j, (lagMonic 0 j).eval xk ^ 2 / gaussGamma (Ioi 0) (lagW 0) (lagMonic 0 j) =
      (lagL 0 j).eval xk ^ 2 := fun j => by
    rw [dlmf_3_5_27 (by norm_num), lagMonic_eq_lagL (by norm_num), eval_mul, eval_C, add_zero,
      Gamma_nat_eq_factorial]
    have : (j.factorial : ℝ) ≠ 0 := by positivity
    rw [mul_pow, mul_pow, ← pow_mul, mul_comm j 2, pow_mul]
    norm_num
    field_simp
  simp only [hterm] at h
  have hS : ∑ j ∈ range n, (lagL 0 j).eval xk ^ 2 ≠ 0 := by
    intro h0; rw [h0, mul_zero] at h; exact zero_ne_one h
  field_simp
  linarith

end Azurite.DLMF
