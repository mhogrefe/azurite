/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section5GaussLegendre
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# DLMF §3.5(v): the Gauss–Hermite formula

Formula 3.5.28.

* The weight `hermW x = e^{−x²}` on `(−∞, ∞)`: `isGaussWeight_hermW`, `wInt_hermW_one`
  (`∫ e^{−x²} = √π`), and integration by parts `wInt_hermW_derivative` (`∫ p′ w = 2 ∫ x p w`).
* The Hermite polynomials `hermiteH` (`H_{n+1} = 2x H_n − H_n′`), Rodrigues' formula 18.5.5
  (`hermiteH_rodrigues`), 18.9.25 (`derivative_hermiteH_succ`), the recurrence 18.9.1
  (`hermiteH_succ_succ`), parity (`eval_neg_hermiteH`).
* The monic Hermite polynomials `hermMonic` with `2ⁿ p_n = H_n` (`hermMonic_eq`, "the `p_n` are the
  monic Hermite polynomials"), `hermMonic_spec`.
* Orthogonality via `∫ p_n q w = 2⁻ⁿ ∫ q⁽ⁿ⁾ w` (`wInt_hermMonic_mul`): `isOrthMonic_hermMonic`.
* 3.5.28: `dlmf_3_5_28` (`γ_n = √π n!/2ⁿ`).
* The weights `w_k = √π/∑_{j<n} H_j(x_k)²/(2^j j!)` (`christoffel_hermite`), used for
  Tables 3.5.10–3.5.13 in `Section5GaussHermiteTables`.
-/

open Polynomial Finset Set MeasureTheory Real

namespace Azurite.DLMF

/-! ### The weight `e^{−x²}` on `(−∞, ∞)` -/

/-- The Hermite weight `w(x) = e^{−x²}`. -/
noncomputable def hermW (x : ℝ) : ℝ := exp (-x ^ 2)

/-- `e^{−x²}` is a Gauss weight on `(−∞, ∞)`. -/
theorem isGaussWeight_hermW : IsGaussWeight univ hermW where
  isOpen := isOpen_univ
  ordConnected := ordConnected_univ
  nonempty := univ_nonempty
  pos := fun x _ => exp_pos _
  integrableOn := fun k => by
    rw [integrableOn_univ]
    have hk : (-1 : ℝ) < k := by have : (0 : ℝ) ≤ k := k.cast_nonneg; linarith
    refine (integrable_rpow_mul_exp_neg_mul_sq one_pos hk).congr (ae_of_all _ fun x => ?_)
    simp [hermW, rpow_natCast]

theorem hasDerivAt_hermW (x : ℝ) : HasDerivAt hermW (-2 * x * hermW x) x := by
  have h := ((hasDerivAt_pow 2 x).neg).exp
  unfold hermW
  convert h using 1
  simp
  ring

/-- Integration by parts against `e^{−x²}`: `∫ p′ w = 2 ∫ x p w`. -/
theorem wInt_hermW_derivative (p : ℝ[X]) :
    wInt univ hermW (derivative p) = 2 * wInt univ hermW (X * p) := by
  have hw := isGaussWeight_hermW
  have hi : ∀ q : ℝ[X], Integrable fun x => q.eval x * hermW x := fun q => by
    simpa [integrableOn_univ] using hw.integrableOn_eval q
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable (u := fun x => p.eval x)
    (u' := fun x => (derivative p).eval x) (v := hermW) (v' := fun x => -2 * x * hermW x)
    (fun x _ => p.hasDerivAt x) (fun x _ => hasDerivAt_hermW x)
    (by
      refine (hi (C (-2) * X * p)).congr (ae_of_all _ fun x => ?_)
      simp only [eval_mul, eval_C, eval_X, Pi.mul_apply]; ring)
    (hi (derivative p)) (hi p)
  have e1 : ∫ x, p.eval x * (-2 * x * hermW x) = -2 * wInt univ hermW (X * p) := by
    rw [wInt, Measure.restrict_univ, ← integral_const_mul]
    congr 1; ext x; simp only [eval_mul, eval_X]; ring
  rw [e1] at h
  rw [wInt, Measure.restrict_univ]
  linarith

/-- `∫ e^{−x²} = √π`. -/
theorem wInt_hermW_one : wInt univ hermW 1 = √π := by
  rw [wInt, Measure.restrict_univ]
  have h := integral_gaussian 1
  rw [div_one] at h
  rw [← h]
  congr 1; ext x; simp [hermW]

/-! ### Hermite polynomials -/

/-- The Hermite polynomials `H_n` (§18.3), by `H_0 = 1`, `H_{n+1} = 2x H_n − H_n′` (Rodrigues'
formula `hermiteH_rodrigues` identifies them with 18.5.5). -/
noncomputable def hermiteH : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => C 2 * X * hermiteH n - derivative (hermiteH n)

theorem hermiteH_succ (n : ℕ) :
    hermiteH (n + 1) = C 2 * X * hermiteH n - derivative (hermiteH n) := rfl

/-- 18.9.25: `H_{n+1}′ = 2(n + 1) H_n`. -/
theorem derivative_hermiteH_succ (n : ℕ) :
    derivative (hermiteH (n + 1)) = C (2 * ((n : ℝ) + 1)) * hermiteH n := by
  induction n with
  | zero => simp [hermiteH]
  | succ n ih =>
    rw [hermiteH_succ (n + 1), derivative_sub, derivative_mul, derivative_mul, ih,
      derivative_mul, derivative_C, derivative_X, derivative_C, hermiteH_succ n]
    simp only [zero_mul, zero_add, mul_one, map_mul, map_add, map_natCast, map_ofNat,
      Nat.cast_add, Nat.cast_one, map_one]
    ring

/-- The three-term recurrence 18.9.1: `H_{n+2} = 2x H_{n+1} − 2(n + 1) H_n`. -/
theorem hermiteH_succ_succ (n : ℕ) :
    hermiteH (n + 2) = C 2 * X * hermiteH (n + 1) - C (2 * ((n : ℝ) + 1)) * hermiteH n := by
  rw [hermiteH_succ (n + 1), derivative_hermiteH_succ]

theorem eval_hermiteH_succ_succ (n : ℕ) (x : ℝ) :
    (hermiteH (n + 2)).eval x =
      2 * x * (hermiteH (n + 1)).eval x - 2 * (n + 1) * (hermiteH n).eval x := by
  rw [hermiteH_succ_succ]; simp

theorem eval_hermiteH_zero (x : ℝ) : (hermiteH 0).eval x = 1 := by simp [hermiteH]

theorem eval_hermiteH_one (x : ℝ) : (hermiteH 1).eval x = 2 * x := by simp [hermiteH]

/-- Parity: `H_n(−x) = (−1)ⁿ H_n(x)`. -/
theorem eval_neg_hermiteH (n : ℕ) (x : ℝ) :
    (hermiteH n).eval (-x) = (-1) ^ n * (hermiteH n).eval x := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp [eval_hermiteH_zero]
    | 1, _ => simp [eval_hermiteH_one]
    | n + 2, ih =>
      rw [eval_hermiteH_succ_succ, eval_hermiteH_succ_succ, ih n (by omega),
        ih (n + 1) (by omega)]
      ring

/-- **Rodrigues' formula** 18.5.5 (`w = e^{−x²}`, `κ_n = (−1)ⁿ`):
`dⁿ/dxⁿ e^{−x²} = (−1)ⁿ H_n(x) e^{−x²}`. -/
theorem hermiteH_rodrigues (n : ℕ) :
    iteratedDeriv n hermW = fun x => (-1) ^ n * (hermiteH n).eval x * hermW x := by
  induction n with
  | zero => ext x; simp [hermiteH]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    ext x
    have h : HasDerivAt (fun y => (-1) ^ n * ((hermiteH n).eval y * hermW y))
        ((-1) ^ n * ((derivative (hermiteH n)).eval x * hermW x +
          (hermiteH n).eval x * (-2 * x * hermW x))) x :=
      (((hermiteH n).hasDerivAt x).mul (hasDerivAt_hermW x)).const_mul _
    rw [show (fun x => (-1) ^ n * (hermiteH n).eval x * hermW x) =
      fun x => (-1) ^ n * ((hermiteH n).eval x * hermW x) by ext; ring, h.deriv, hermiteH_succ]
    simp only [eval_sub, eval_mul, eval_C, eval_X]
    ring

/-! ### The monic Hermite polynomials -/

/-- The monic Hermite polynomials: `p_0 = 1`, `p_{n+1} = x p_n − p_n′/2`. -/
noncomputable def hermMonic : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => X * hermMonic n - C (1 / 2) * derivative (hermMonic n)

/-- "The `p_n` are the monic Hermite polynomials": `2ⁿ p_n = H_n`. -/
theorem hermMonic_eq (n : ℕ) : C ((2 : ℝ) ^ n) * hermMonic n = hermiteH n := by
  induction n with
  | zero => simp [hermMonic, hermiteH]
  | succ n ih =>
    rw [hermiteH_succ, ← ih, hermMonic, derivative_mul, derivative_C, zero_mul, zero_add,
      pow_succ, C_mul]
    have h2 : C (1 / 2 : ℝ) * C 2 = 1 := by rw [← C_mul]; norm_num
    linear_combination (-(C ((2 : ℝ) ^ n) * derivative (hermMonic n))) * h2

theorem hermMonic_spec (n : ℕ) : (hermMonic n).Monic ∧ (hermMonic n).natDegree = n := by
  induction n with
  | zero => simp [hermMonic]
  | succ n ih =>
    obtain ⟨hm, hd⟩ := ih
    have hX : (X * hermMonic n).Monic := monic_X.mul hm
    have hXd : (X * hermMonic n).natDegree = n + 1 := by
      rw [natDegree_mul X_ne_zero hm.ne_zero, natDegree_X, hd, add_comm]
    have hlt : (C (1 / 2 : ℝ) * derivative (hermMonic n)).degree < (X * hermMonic n).degree := by
      rw [degree_C_mul (by norm_num), degree_eq_natDegree hX.ne_zero, hXd]
      refine (degree_derivative_lt hm.ne_zero).trans_le ?_
      rw [degree_eq_natDegree hm.ne_zero, hd]
      exact_mod_cast Nat.le_succ n
    refine ⟨hX.sub_of_left hlt, ?_⟩
    rw [hermMonic, natDegree_eq_of_degree_eq (degree_sub_eq_left_of_degree_lt hlt), hXd]

/-! ### Orthogonality and 3.5.28 -/

/-- `∫ p_{n+1} q w = ½ ∫ p_n q′ w` (from `∫ (p_n q)′ w = 2 ∫ x p_n q w`). -/
theorem wInt_hermMonic_succ_mul (n : ℕ) (q : ℝ[X]) :
    wInt univ hermW (hermMonic (n + 1) * q) =
      1 / 2 * wInt univ hermW (hermMonic n * derivative q) := by
  have hw := isGaussWeight_hermW
  have h := wInt_hermW_derivative (hermMonic n * q)
  rw [derivative_mul, wInt_add hw] at h
  rw [hermMonic, sub_mul, wInt_sub hw, mul_assoc, mul_assoc, wInt_C_mul]
  linarith

/-- `∫ p_n q w = 2⁻ⁿ ∫ q⁽ⁿ⁾ w`. -/
theorem wInt_hermMonic_mul (n : ℕ) (q : ℝ[X]) :
    wInt univ hermW (hermMonic n * q) = (1 / 2) ^ n * wInt univ hermW (derivative^[n] q) := by
  induction n generalizing q with
  | zero => simp [hermMonic]
  | succ n ih =>
    rw [wInt_hermMonic_succ_mul, ih, Function.iterate_succ_apply, pow_succ]
    ring

/-- **DLMF 3.5.28** (orthogonality): the monic Hermite polynomials are the monic orthogonal
polynomials of `e^{−x²}` on `(−∞, ∞)`. -/
theorem isOrthMonic_hermMonic (n : ℕ) : IsOrthMonic univ hermW n (hermMonic n) := by
  refine ⟨(hermMonic_spec n).1, (hermMonic_spec n).2, fun q hq => ?_⟩
  rw [wInt_hermMonic_mul]
  by_cases hq0 : q = 0
  · simp [hq0, wInt_zero]
  rw [iterate_derivative_eq_zero ((natDegree_lt_iff_degree_lt hq0).mpr hq), wInt_zero, mul_zero]

/-- **DLMF 3.5.28**: `γ_n = √π n!/2ⁿ`. -/
theorem dlmf_3_5_28 (n : ℕ) :
    gaussGamma univ hermW (hermMonic n) = √π * n.factorial / 2 ^ n := by
  obtain ⟨hm, hd⟩ := hermMonic_spec n
  have hD : derivative^[n] (hermMonic n) = C (n.factorial : ℝ) := by
    rw [eq_C_of_natDegree_le_zero ((natDegree_iterate_derivative _ n).trans (by omega)),
      coeff_iterate_derivative, zero_add, Nat.descFactorial_self]
    conv_lhs => rw [show (hermMonic n).coeff n = 1 by have := hm.coeff_natDegree; rwa [hd] at this]
    rw [nsmul_eq_mul, mul_one]
  rw [gaussGamma, wInt_hermMonic_mul, hD, ← mul_one (C _), wInt_C_mul, wInt_hermW_one]
  field_simp
  rw [← mul_pow]; norm_num

/-! ### Parity and the weights -/

theorem eval_neg_hermMonic (n : ℕ) (x : ℝ) :
    (hermMonic n).eval (-x) = (-1) ^ n * (hermMonic n).eval x := by
  have h := eval_neg_hermiteH n x
  rw [← hermMonic_eq] at h
  simp only [eval_mul, eval_C] at h
  have : (2 : ℝ) ^ n ≠ 0 := by positivity
  field_simp at h
  linear_combination h

/-- The Gauss–Hermite weights: `w_k = √π / ∑_{j<n} H_j(x_k)²/(2^j j!)`. -/
theorem christoffel_hermite (n : ℕ) {xk : ℝ} (hk : xk ∈ (hermMonic n).roots.toFinset) :
    christoffel univ hermW (hermMonic n) xk =
      √π / ∑ j ∈ range n, (hermiteH j).eval xk ^ 2 / (2 ^ j * j.factorial) := by
  have h := christoffel_mul_sum isGaussWeight_hermW isOrthMonic_hermMonic n hk
  have hπ : 0 < √π := sqrt_pos.mpr pi_pos
  have hterm : ∀ j, (hermMonic j).eval xk ^ 2 / gaussGamma univ hermW (hermMonic j) =
      (hermiteH j).eval xk ^ 2 / (2 ^ j * j.factorial) / √π := fun j => by
    rw [dlmf_3_5_28, ← hermMonic_eq, eval_mul, eval_C]
    have : (j.factorial : ℝ) ≠ 0 := by positivity
    field_simp
  simp only [hterm, ← sum_div] at h
  have hS : ∑ j ∈ range n, (hermiteH j).eval xk ^ 2 / (2 ^ j * j.factorial) ≠ 0 := by
    intro h0; rw [h0, zero_div, mul_zero] at h; exact zero_ne_one h
  field_simp at h ⊢
  linarith

end Azurite.DLMF
