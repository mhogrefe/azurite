/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section5GaussLegendre
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# DLMF §3.5(v): the Gauss formula for a logarithmic weight function

Formula 3.5.29: `[a, b] = [0, 1]`, `w(x) = ln(1/x)`.

* `logW`, `isGaussWeight_logW`, and the moments `integral_pow_mul_logW`/`wInt_logW_X_pow`
  (`∫₀¹ xᵏ ln(1/x) dx = 1/(k + 1)²`, by the fundamental theorem of calculus with the primitive
  `−x^{k+1} ln x/(k+1) + x^{k+1}/(k+1)²`).
* The orthogonal polynomials of this weight have no classical closed form, but their coefficients
  are rational: `qPoly` (rational coefficient lists), `logMom` (exact moments against `xʲ`), and
  the kernel-checkable certificate `logOK` with `isOrthMonic_of_logOK` and `gaussGamma_of_logOK`.
* `logMonic` (the monic orthogonal polynomials, `isOrthMonic_logMonic`), `logMonic_eq`
  (identification with a certified `qPoly`), and the weights `christoffel_log`
  (`w_k = 1/∑_{j<n} p_j(x_k)²/γ_j`), used for Tables 3.5.14–3.5.17 in `Section5GaussLogTables`.
-/

open Polynomial Finset Set MeasureTheory Real

namespace Azurite.DLMF

/-! ### The weight `ln(1/x)` on `(0, 1)` -/

/-- The logarithmic weight `w(x) = ln(1/x)`. -/
noncomputable def logW (x : ℝ) : ℝ := log (1 / x)

theorem logW_eq (x : ℝ) : logW x = -log x := by rw [logW, one_div, log_inv]

theorem intervalIntegrable_pow_mul_logW (k : ℕ) :
    IntervalIntegrable (fun x => x ^ k * logW x) volume 0 1 := by
  simp_rw [logW_eq]
  exact (intervalIntegral.intervalIntegrable_log'.neg).continuousOn_mul (continuous_pow k).continuousOn

/-- `∫₀¹ xᵏ ln(1/x) dx = 1/(k + 1)²`. -/
theorem integral_pow_mul_logW (k : ℕ) :
    ∫ x in (0 : ℝ)..1, x ^ k * logW x = 1 / (k + 1) ^ 2 := by
  have hk : (0 : ℝ) < k + 1 := by positivity
  set F : ℝ → ℝ := fun x => -(x ^ k * (x * log x)) / (k + 1) + x ^ (k + 1) / (k + 1) ^ 2
  have hF : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt F (x ^ k * logW x) x := by
    intro x hx
    have hx0 : x ≠ 0 := hx.1.ne'
    have h1 := ((hasDerivAt_pow k x).mul (hasDerivAt_mul_log hx0))
    have h2 := hasDerivAt_pow (k + 1) x
    convert (h1.neg.div_const (k + 1)).add (h2.div_const ((k + 1) ^ 2)) using 1
    rw [logW_eq]
    push_cast
    field_simp
    rcases k with _ | k
    · simp
    · simp only [Nat.add_sub_cancel]
      push_cast
      ring
  have hc : ContinuousOn F (Icc 0 1) :=
    ((((continuous_pow k).mul continuous_mul_log).neg.div_const _).add
      ((continuous_pow _).div_const _)).continuousOn
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hc hF
    (intervalIntegrable_pow_mul_logW k)]
  simp [F]

/-- `ln(1/x)` is a Gauss weight on `(0, 1)`. -/
theorem isGaussWeight_logW : IsGaussWeight (Ioo 0 1) logW where
  isOpen := isOpen_Ioo
  ordConnected := ordConnected_Ioo
  nonempty := ⟨1 / 2, by norm_num, by norm_num⟩
  pos := fun x hx => log_pos (by rw [one_div]; exact one_lt_inv_iff₀.mpr ⟨hx.1, hx.2⟩)
  integrableOn := fun k =>
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (intervalIntegrable_pow_mul_logW k)).mono_set Ioo_subset_Ioc_self

theorem wInt_logW_X_pow (k : ℕ) : wInt (Ioo 0 1) logW (X ^ k) = 1 / (k + 1) ^ 2 := by
  rw [wInt, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    ← integral_pow_mul_logW]
  simp

/-! ### Polynomials with rational coefficients -/

/-- `∑ᵢ cᵢ X^{k+i}` for the list `c`. -/
noncomputable def qPolyAux : List ℚ → ℕ → ℝ[X]
  | [], _ => 0
  | c :: l, k => C (c : ℝ) * X ^ k + qPolyAux l (k + 1)

/-- The polynomial `∑ᵢ cᵢ Xⁱ` with rational coefficients `c`. -/
noncomputable def qPoly (l : List ℚ) : ℝ[X] := qPolyAux l 0

theorem coeff_qPolyAux (l : List ℚ) (k i : ℕ) :
    (qPolyAux l k).coeff i = if k ≤ i then ((l.getD (i - k) 0 : ℚ) : ℝ) else 0 := by
  induction l generalizing k with
  | nil => simp [qPolyAux]
  | cons c l ih =>
    rw [qPolyAux, coeff_add, coeff_C_mul_X_pow, ih]
    rcases lt_trichotomy i k with h | rfl | h
    · simp [h.ne, show ¬ k ≤ i by omega, show ¬ k + 1 ≤ i by omega]
    · simp
    · simp only [show i ≠ k from h.ne', show k + 1 ≤ i from h, show k ≤ i from h.le,
        ↓reduceIte, zero_add]
      rw [show i - k = (i - (k + 1)) + 1 by omega]
      simp

theorem coeff_qPoly (l : List ℚ) (i : ℕ) : (qPoly l).coeff i = ((l.getD i 0 : ℚ) : ℝ) := by
  simp [qPoly, coeff_qPolyAux]

/-- Horner evaluation in `ℚ`. -/
def qEval : List ℚ → ℚ → ℚ
  | [], _ => 0
  | c :: l, x => c + x * qEval l x

/-- The real Horner evaluation. -/
noncomputable def qEvalR : List ℚ → ℝ → ℝ
  | [], _ => 0
  | c :: l, x => c + x * qEvalR l x

theorem eval_qPolyAux (l : List ℚ) (k : ℕ) (x : ℝ) :
    (qPolyAux l k).eval x = x ^ k * qEvalR l x := by
  induction l generalizing k with
  | nil => simp [qPolyAux, qEvalR]
  | cons c l ih =>
    simp only [qPolyAux, qEvalR, eval_add, eval_mul, eval_C, eval_pow, eval_X, ih]
    ring

theorem eval_qPoly (l : List ℚ) (x : ℝ) : (qPoly l).eval x = qEvalR l x := by
  rw [qPoly, eval_qPolyAux, pow_zero, one_mul]

theorem qEvalR_cast (l : List ℚ) (x : ℚ) : qEvalR l x = (qEval l x : ℝ) := by
  induction l with
  | nil => simp [qEvalR, qEval]
  | cons c l ih => simp [qEvalR, qEval, ih]

/-- `∑ᵢ cᵢ/(i + k + 1)²`: the integral of `∑ᵢ cᵢ x^{i+k} ln(1/x)` over `(0, 1)`. -/
def logMom : List ℚ → ℕ → ℚ
  | [], _ => 0
  | c :: l, k => c / ((k : ℚ) + 1) ^ 2 + logMom l (k + 1)

theorem wInt_qPolyAux_mul_X_pow (l : List ℚ) (k j : ℕ) :
    wInt (Ioo 0 1) logW (qPolyAux l k * X ^ j) = (logMom l (k + j) : ℝ) := by
  have hw := isGaussWeight_logW
  induction l generalizing k with
  | nil => simp [qPolyAux, logMom, wInt_zero]
  | cons c l ih =>
    rw [qPolyAux, add_mul, wInt_add hw, mul_assoc, wInt_C_mul, ← pow_add, wInt_logW_X_pow,
      ih (k + 1), logMom, show k + 1 + j = k + j + 1 by ring]
    push_cast
    ring

theorem wInt_qPoly_mul_X_pow (l : List ℚ) (j : ℕ) :
    wInt (Ioo 0 1) logW (qPoly l * X ^ j) = (logMom l j : ℝ) := by
  rw [qPoly, wInt_qPolyAux_mul_X_pow, zero_add]

/-- The exact check that `∑ᵢ cᵢ Xⁱ` is the monic orthogonal polynomial of degree `m` for
`ln(1/x)` on `(0, 1)`, with `γ_m > 0`. -/
def logOK (m : ℕ) (l : List ℚ) : Bool :=
  decide (l.length = m + 1) && decide (l.getD m 0 = 1) &&
    (List.range m).all (fun j => decide (logMom l j = 0)) && decide (0 < logMom l m)

theorem logOK_spec {m : ℕ} {l : List ℚ} (h : logOK m l = true) :
    (qPoly l).Monic ∧ (qPoly l).natDegree = m := by
  simp only [logOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hlen, hm⟩, -⟩, -⟩ := h
  have hcm : (qPoly l).coeff m = 1 := by rw [coeff_qPoly, hm, Rat.cast_one]
  have hle : (qPoly l).natDegree ≤ m := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro i hi
    rw [coeff_qPoly, List.getD_eq_default _ _ (by rw [hlen]; exact_mod_cast hi), Rat.cast_zero]
  have hd : (qPoly l).natDegree = m :=
    le_antisymm hle (le_natDegree_of_ne_zero (by rw [hcm]; exact one_ne_zero))
  exact ⟨by rw [Monic, leadingCoeff, hd, hcm], hd⟩

/-- `logOK` certifies the monic orthogonal polynomial. -/
theorem isOrthMonic_of_logOK {m : ℕ} {l : List ℚ} (h : logOK m l = true) :
    IsOrthMonic (Ioo 0 1) logW m (qPoly l) := by
  have hw := isGaussWeight_logW
  obtain ⟨hmon, hdeg⟩ := logOK_spec h
  simp only [logOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨-, hz⟩, -⟩ := h
  refine ⟨hmon, hdeg, fun q hq => ?_⟩
  by_cases hq0 : q = 0
  · rw [hq0, mul_zero, wInt_zero]
  rw [as_sum_range' q m ((natDegree_lt_iff_degree_lt hq0).mpr hq), mul_sum, wInt_sum hw]
  refine sum_eq_zero fun j hj => ?_
  rw [← C_mul_X_pow_eq_monomial, mul_left_comm, wInt_C_mul, wInt_qPoly_mul_X_pow,
    hz j (mem_range.mp hj), Rat.cast_zero, mul_zero]

/-- `γ_m = ∫ p_m xᵐ ln(1/x) dx`, computed exactly. -/
theorem gaussGamma_of_logOK {m : ℕ} {l : List ℚ} (h : logOK m l = true) :
    gaussGamma (Ioo 0 1) logW (qPoly l) = (logMom l m : ℝ) := by
  have hw := isGaussWeight_logW
  have hp := isOrthMonic_of_logOK h
  obtain ⟨hmon, hdeg⟩ := logOK_spec h
  have hlt : (qPoly l - X ^ m).degree < (m : WithBot ℕ) := by
    have h' := degree_sub_lt_left (p := qPoly l) (q := X ^ m)
      (by rw [degree_eq_natDegree hmon.ne_zero, hdeg, degree_X_pow])
      hmon.ne_zero (by rw [hmon.leadingCoeff, (monic_X_pow m).leadingCoeff])
    rwa [degree_eq_natDegree hmon.ne_zero, hdeg] at h'
  rw [gaussGamma, show qPoly l * qPoly l = qPoly l * (qPoly l - X ^ m) + qPoly l * X ^ m by ring,
    wInt_add hw, hp.wInt_mul_eq_zero hlt, zero_add, wInt_qPoly_mul_X_pow]

/-! ### The monic orthogonal polynomials and the weights -/

/-- The monic orthogonal polynomials `p_m` of `ln(1/x)` on `(0, 1)`. -/
noncomputable def logMonic (m : ℕ) : ℝ[X] :=
  Classical.choose (exists_isOrthMonic isGaussWeight_logW m)

theorem isOrthMonic_logMonic (m : ℕ) : IsOrthMonic (Ioo 0 1) logW m (logMonic m) :=
  Classical.choose_spec (exists_isOrthMonic isGaussWeight_logW m)

theorem logMonic_eq {m : ℕ} {l : List ℚ} (h : logOK m l = true) : logMonic m = qPoly l :=
  (isOrthMonic_logMonic m).unique isGaussWeight_logW (isOrthMonic_of_logOK h)

/-- The weights: `w_k = 1/∑_{j<n} p_j(x_k)²/γ_j` (3.5.20_2). -/
theorem christoffel_log (n : ℕ) {xk : ℝ} (hk : xk ∈ (logMonic n).roots.toFinset) :
    christoffel (Ioo 0 1) logW (logMonic n) xk =
      1 / ∑ j ∈ range n, (logMonic j).eval xk ^ 2 / gaussGamma (Ioo 0 1) logW (logMonic j) := by
  have h := christoffel_mul_sum isGaussWeight_logW isOrthMonic_logMonic n hk
  have hS : ∑ j ∈ range n, (logMonic j).eval xk ^ 2 / gaussGamma (Ioo 0 1) logW (logMonic j) ≠ 0 :=
    fun h0 => by rw [h0, mul_zero] at h; exact zero_ne_one h
  field_simp
  linarith

end Azurite.DLMF
