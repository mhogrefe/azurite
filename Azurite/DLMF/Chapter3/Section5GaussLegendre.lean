/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section5Gauss

/-!
# DLMF §3.5(v): the Gauss–Legendre formula

3.5.21 and the theory behind Tables 3.5.1–3.5.5.

* The monic Legendre polynomials by Rodrigues' formula: `rodrigues` (`Dⁿ (x² − 1)ⁿ`), `legendrePoly`
  (`P_n`), `legendreMonic` (`p_n`); `legendreP_eq` (`P_n = k_n p_n`, `legendreLead`: "the
  `p_n(x)` are the monic Legendre polynomials").
* `w = 1` on `(−1, 1)`: `isGaussWeight_legendre`, `wInt_Ioo_one`; orthogonality by repeated
  integration by parts (`integral_eval_mul_derivative`, `eval_iterate_derivative_X_sq_sub_one_pow`,
  `integral_mul_rodrigues`), `isOrthMonic_legendreMonic`.
* 3.5.21: `dlmf_3_5_21` (`γ_n = 2^{2n+1}/(2n+1) · (n!)⁴/((2n)!)²`, via `wallisI_eq`,
  `∫₋₁¹ (1 − x²)ⁿ = 2^{2n+1} (n!)²/(2n + 1)!`).
* Parity (`rodrigues_comp_neg_X`, `eval_neg_legendreP`), the three-term recurrence
  `legendreMonic_succ_succ` (from orthogonality: `gaussGamma_legendre_succ`,
  `intervalIntegral_odd_eq_zero`), Bonnet's recurrence `eval_legendreP_succ_succ` (18.9.1).
* The Christoffel numbers as reciprocals of the Christoffel function: `christoffel_mul_sum`
  (general weights: the matrix `(p_j(xₖ) √(wₖ/γ_j))` is orthogonal by 3.5.20_2) and
  `christoffel_legendre` (`wₖ = 2/∑_{j<n} (2j + 1) P_j(xₖ)²`).
-/

open Polynomial Finset Set MeasureTheory intervalIntegral

namespace Azurite.DLMF

/-- `D^n (x² − 1)^n`, the Rodrigues form of the Legendre polynomials (up to `2ⁿ n!`). -/
noncomputable def rodrigues (n : ℕ) : ℝ[X] := derivative^[n] ((X ^ 2 - 1) ^ n)

/-- The Legendre polynomial `P_n = (2ⁿ n!)⁻¹ Dⁿ (x² − 1)ⁿ` (§18.3, Rodrigues' formula 18.5.5). -/
noncomputable def legendrePoly (n : ℕ) : ℝ[X] := C (1 / (2 ^ n * n.factorial : ℝ)) * rodrigues n

/-- The monic Legendre polynomial `p_n = (n!/(2n)!) Dⁿ (x² − 1)ⁿ`. -/
noncomputable def legendreMonic (n : ℕ) : ℝ[X] :=
  C ((n.factorial : ℝ) / (2 * n).factorial) * rodrigues n

/-- Integration by parts for polynomials on `[−1, 1]`. -/
theorem integral_eval_mul_derivative (f g : ℝ[X]) :
    ∫ x in (-1 : ℝ)..1, f.eval x * (derivative g).eval x =
      f.eval 1 * g.eval 1 - f.eval (-1) * g.eval (-1) -
        ∫ x in (-1 : ℝ)..1, (derivative f).eval x * g.eval x :=
  integral_mul_deriv_eq_deriv_mul (fun x _ => f.hasDerivAt x) (fun x _ => g.hasDerivAt x)
    ((derivative f).continuous.intervalIntegrable _ _)
    ((derivative g).continuous.intervalIntegrable _ _)

theorem X_sq_sub_one_pow_ne_zero (n : ℕ) : ((X ^ 2 - 1) ^ n : ℝ[X]) ≠ 0 :=
  pow_ne_zero _ (X_pow_sub_C_ne_zero (by norm_num) 1)

/-- `Dⁱ (x² − 1)ⁿ` vanishes at `±1` for `i < n`. -/
theorem eval_iterate_derivative_X_sq_sub_one_pow {n i : ℕ} (hi : i < n) {a : ℝ}
    (ha : a = 1 ∨ a = -1) : (derivative^[i] ((X ^ 2 - 1) ^ n : ℝ[X])).eval a = 0 := by
  have hdvd : (X - C a) ^ n ∣ ((X ^ 2 - 1) ^ n : ℝ[X]) := by
    apply pow_dvd_pow_of_dvd
    rcases ha with rfl | rfl
    · exact ⟨X + 1, by rw [C_1]; ring⟩
    · exact ⟨X - 1, by rw [C_neg, C_1]; ring⟩
  have hm : n ≤ rootMultiplicity a ((X ^ 2 - 1) ^ n : ℝ[X]) :=
    (le_rootMultiplicity_iff (X_sq_sub_one_pow_ne_zero n)).mpr hdvd
  exact isRoot_iterate_derivative_of_lt_rootMultiplicity (hi.trans_le hm)

/-- Repeated integration by parts:
`∫₋₁¹ q Dⁿ u = (−1)ʲ ∫₋₁¹ Dʲ q D^{n−j} u`, `u = (x² − 1)ⁿ`, `j ≤ n`. -/
theorem integral_mul_rodrigues (n : ℕ) (q : ℝ[X]) :
    ∀ j ≤ n, ∫ x in (-1 : ℝ)..1, q.eval x * (rodrigues n).eval x =
      (-1) ^ j * ∫ x in (-1 : ℝ)..1, (derivative^[j] q).eval x *
        (derivative^[n - j] ((X ^ 2 - 1) ^ n : ℝ[X])).eval x := by
  intro j
  induction j with
  | zero => intro _; simp [rodrigues]
  | succ j ih =>
    intro hj
    rw [ih (by omega)]
    have hnj : n - j = (n - (j + 1)) + 1 := by omega
    rw [hnj, Function.iterate_succ_apply', integral_eval_mul_derivative,
      eval_iterate_derivative_X_sq_sub_one_pow (by omega) (Or.inl rfl),
      eval_iterate_derivative_X_sq_sub_one_pow (by omega) (Or.inr rfl),
      ← Function.iterate_succ_apply' derivative]
    ring

/-- `∫₋₁¹ q Dⁿ(x² − 1)ⁿ = 0` for `deg q < n`. -/
theorem integral_mul_rodrigues_eq_zero {n : ℕ} {q : ℝ[X]} (hq : q.degree < n) :
    ∫ x in (-1 : ℝ)..1, q.eval x * (rodrigues n).eval x = 0 := by
  rw [integral_mul_rodrigues n q n le_rfl, iterate_derivative_eq_zero_of_degree_lt hq]
  simp

/-- On `(−1, 1)` with `w = 1`, `∫_I p w` is the interval integral `∫₋₁¹ p`. -/
theorem wInt_Ioo_one (p : ℝ[X]) :
    wInt (Ioo (-1) 1) (fun _ => 1) p = ∫ x in (-1 : ℝ)..1, p.eval x := by
  rw [wInt, integral_of_le (by norm_num), integral_Ioc_eq_integral_Ioo]
  simp

/-- `w = 1` on `(−1, 1)` is a Gauss weight. -/
theorem isGaussWeight_legendre : IsGaussWeight (Ioo (-1 : ℝ) 1) (fun _ => 1) where
  isOpen := isOpen_Ioo
  ordConnected := ordConnected_Ioo
  nonempty := ⟨0, by norm_num, by norm_num⟩
  pos := fun _ _ => one_pos
  integrableOn := fun k =>
    ((continuous_pow k).mul continuous_const).integrableOn_Icc.mono_set Ioo_subset_Icc_self

theorem natDegree_X_sq_sub_one_pow (n : ℕ) : ((X ^ 2 - 1) ^ n : ℝ[X]).natDegree = 2 * n := by
  rw [natDegree_pow, show (X ^ 2 - 1 : ℝ[X]) = X ^ 2 - C 1 by rw [C_1], natDegree_X_pow_sub_C]
  ring

theorem monic_X_sq_sub_one_pow (n : ℕ) : ((X ^ 2 - 1) ^ n : ℝ[X]).Monic :=
  (monic_X_pow_sub_C 1 (by norm_num)).pow n

theorem coeff_rodrigues_n (n : ℕ) :
    (rodrigues n).coeff n = ((2 * n).descFactorial n : ℝ) := by
  rw [rodrigues, coeff_iterate_derivative, show n + n = 2 * n by ring, nsmul_eq_mul]
  have := (monic_X_sq_sub_one_pow n).coeff_natDegree
  rw [natDegree_X_sq_sub_one_pow] at this
  rw [this, mul_one]

theorem natDegree_rodrigues (n : ℕ) : (rodrigues n).natDegree = n := by
  apply le_antisymm
  · have := natDegree_iterate_derivative ((X ^ 2 - 1) ^ n : ℝ[X]) n
    rw [natDegree_X_sq_sub_one_pow] at this
    rw [rodrigues]; omega
  · apply le_natDegree_of_ne_zero
    rw [coeff_rodrigues_n]
    exact_mod_cast (Nat.descFactorial_pos.mpr (by omega)).ne'

theorem descFactorial_two_mul (n : ℕ) :
    ((2 * n).descFactorial n : ℝ) = (2 * n).factorial / n.factorial := by
  have h := Nat.factorial_mul_descFactorial (show n ≤ 2 * n by omega)
  rw [show 2 * n - n = n by omega] at h
  rw [eq_div_iff (by positivity)]
  exact_mod_cast (by rw [mul_comm]; exact h)

theorem legendreMonic_monic (n : ℕ) : (legendreMonic n).Monic := by
  have hc : ((n.factorial : ℝ) / (2 * n).factorial) ≠ 0 := by positivity
  rw [Monic, leadingCoeff, legendreMonic, natDegree_C_mul hc, natDegree_rodrigues, coeff_C_mul,
    coeff_rodrigues_n, descFactorial_two_mul]
  field_simp

theorem natDegree_legendreMonic (n : ℕ) : (legendreMonic n).natDegree = n := by
  rw [legendreMonic, natDegree_C_mul (by positivity), natDegree_rodrigues]

/-- The monic Legendre polynomials are the monic orthogonal polynomials of the weight `w = 1` on
`(−1, 1)`. -/
theorem isOrthMonic_legendreMonic (n : ℕ) :
    IsOrthMonic (Ioo (-1) 1) (fun _ => 1) n (legendreMonic n) := by
  refine ⟨legendreMonic_monic n, natDegree_legendreMonic n, fun q hq => ?_⟩
  rw [wInt_Ioo_one]
  simp only [legendreMonic, eval_mul, eval_C]
  rw [show (fun x => (n.factorial : ℝ) / (2 * n).factorial * (rodrigues n).eval x * q.eval x) =
    fun x => (n.factorial : ℝ) / (2 * n).factorial * (q.eval x * (rodrigues n).eval x) by
      ext; ring, intervalIntegral.integral_const_mul, integral_mul_rodrigues_eq_zero hq, mul_zero]

/-! ### `γ_n` (3.5.21) -/

/-- `Iₙ = ∫₋₁¹ (1 − x²)ⁿ dx`. -/
noncomputable def wallisI (n : ℕ) : ℝ := ∫ x in (-1 : ℝ)..1, ((1 - X ^ 2) ^ n : ℝ[X]).eval x

theorem wallisI_succ (n : ℕ) : (2 * n + 3) * wallisI (n + 1) = (2 * n + 2) * wallisI n := by
  have h := integral_eval_mul_derivative ((1 - X ^ 2) ^ (n + 1) : ℝ[X]) X
  simp only [derivative_X, eval_one, mul_one, eval_X] at h
  have hd : ∀ x : ℝ, (derivative ((1 - X ^ 2) ^ (n + 1) : ℝ[X])).eval x * x =
      (2 * n + 2) * (((1 - X ^ 2) ^ (n + 1) : ℝ[X]).eval x - ((1 - X ^ 2) ^ n : ℝ[X]).eval x) := by
    intro x
    simp only [derivative_pow, derivative_sub, derivative_one, eval_mul,
      eval_pow, eval_sub, eval_one, eval_X, eval_C, zero_sub, eval_neg, derivative_X]
    push_cast
    ring
  simp_rw [hd] at h
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
    ((Polynomial.continuous _).intervalIntegrable _ _)
    ((Polynomial.continuous _).intervalIntegrable _ _)] at h
  simp only [eval_pow, eval_sub, eval_one, eval_X] at h
  norm_num at h
  unfold wallisI
  simp only [eval_pow, eval_sub, eval_one, eval_X]
  linarith

theorem wallisI_eq (n : ℕ) :
    wallisI n = 2 ^ (2 * n + 1) * (n.factorial : ℝ) ^ 2 / (2 * n + 1).factorial := by
  induction n with
  | zero => simp [wallisI]; norm_num
  | succ n ih =>
    have h := wallisI_succ n
    rw [ih] at h
    have hpos : (0 : ℝ) < 2 * n + 3 := by positivity
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 by ring]
    simp only [Nat.factorial_succ] at h ⊢
    push_cast at h ⊢
    have hf : ((2 * n + 1).factorial : ℝ) ≠ 0 := by positivity
    field_simp at h ⊢
    rw [show (2 : ℝ) ^ (2 * n + 1 + 1 + 1) = 2 ^ (2 * n + 1) * 4 by ring]
    linear_combination (2 * (n : ℝ) + 2) * h

theorem legendreMonic_sub_X_pow_degree (n : ℕ) :
    (legendreMonic n - X ^ n).degree < (n : WithBot ℕ) := by
  have hp := legendreMonic_monic n
  have h := degree_sub_lt_left (p := legendreMonic n) (q := X ^ n)
    (by rw [degree_eq_natDegree hp.ne_zero, natDegree_legendreMonic, degree_X_pow])
    hp.ne_zero (by rw [hp.leadingCoeff, (monic_X_pow n).leadingCoeff])
  rwa [degree_eq_natDegree hp.ne_zero, natDegree_legendreMonic] at h

/-- **DLMF 3.5.21**: for Gauss–Legendre, `γ_n = 2^{2n+1}/(2n + 1) · (n!)⁴/((2n)!)²`. -/
theorem dlmf_3_5_21 (n : ℕ) :
    gaussGamma (Ioo (-1) 1) (fun _ => 1) (legendreMonic n) =
      2 ^ (2 * n + 1) / (2 * n + 1) * (n.factorial : ℝ) ^ 4 / ((2 * n).factorial : ℝ) ^ 2 := by
  have hw := isGaussWeight_legendre
  have horth := isOrthMonic_legendreMonic n
  set p := legendreMonic n
  have h1 : gaussGamma (Ioo (-1) 1) (fun _ => 1) p =
      wInt (Ioo (-1) 1) (fun _ => 1) (X ^ n * p) := by
    rw [gaussGamma, show p * p = p * (p - X ^ n) + X ^ n * p by ring, wInt_add hw,
      horth.wInt_mul_eq_zero (legendreMonic_sub_X_pow_degree n), zero_add]
  rw [h1, wInt_Ioo_one]
  simp only [p, legendreMonic, eval_mul, eval_C]
  rw [show (fun x => (X ^ n : ℝ[X]).eval x * ((n.factorial : ℝ) / (2 * n).factorial *
      (rodrigues n).eval x)) = fun x => (n.factorial : ℝ) / (2 * n).factorial *
        ((X ^ n : ℝ[X]).eval x * (rodrigues n).eval x) by ext; ring,
    intervalIntegral.integral_const_mul, integral_mul_rodrigues n (X ^ n) n le_rfl,
    iterate_derivative_X_pow_eq_C_mul, Nat.descFactorial_self, Nat.sub_self,
    Function.iterate_zero, id]
  have hev : ∀ x : ℝ, (C (n.factorial : ℝ) * X ^ 0 : ℝ[X]).eval x * ((X ^ 2 - 1) ^ n : ℝ[X]).eval x
      = (-1) ^ n * (n.factorial : ℝ) * ((1 - X ^ 2) ^ n : ℝ[X]).eval x := by
    intro x
    simp only [eval_C, eval_pow, eval_X, pow_zero, mul_one, eval_sub, eval_one]
    rw [show x ^ 2 - 1 = (-1) * (1 - x ^ 2) by ring, mul_pow]
    ring
  simp_rw [hev]
  rw [intervalIntegral.integral_const_mul, show (∫ x in (-1 : ℝ)..1,
    ((1 - X ^ 2) ^ n : ℝ[X]).eval x) = wallisI n from rfl, wallisI_eq]
  have h2 : ((2 * n + 1).factorial : ℝ) = (2 * n + 1) * (2 * n).factorial := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [h2]
  have hf : ((2 * n).factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring_nf
  rw [mul_comm, pow_mul, neg_one_sq, one_pow]

/-! ### Parity and the three-term recurrence -/

theorem iterate_derivative_comp_neg_X (p : ℝ[X]) :
    ∀ i : ℕ, (derivative^[i] p).comp (-X) = C ((-1 : ℝ) ^ i) * derivative^[i] (p.comp (-X)) := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    have hd : ∀ q : ℝ[X], (derivative q).comp (-X) = -derivative (q.comp (-X)) := fun q => by
      rw [derivative_comp, derivative_neg, derivative_X]; ring
    rw [Function.iterate_succ_apply', hd, ih, derivative_C_mul, Function.iterate_succ_apply',
      pow_succ, C_mul, C_neg, C_1]
    ring

/-- `P_n(−x) = (−1)ⁿ P_n(x)` (for the Rodrigues form, hence for `p_n` and `P_n`). -/
theorem rodrigues_comp_neg_X (n : ℕ) :
    (rodrigues n).comp (-X) = C ((-1 : ℝ) ^ n) * rodrigues n := by
  rw [rodrigues, iterate_derivative_comp_neg_X]
  congr 2
  simp [sub_comp, pow_comp]

theorem eval_neg_rodrigues (n : ℕ) (x : ℝ) :
    (rodrigues n).eval (-x) = (-1) ^ n * (rodrigues n).eval x := by
  have h := congrArg (eval x) (rodrigues_comp_neg_X n)
  simpa [eval_comp] using h

theorem eval_neg_legendreMonic (n : ℕ) (x : ℝ) :
    (legendreMonic n).eval (-x) = (-1) ^ n * (legendreMonic n).eval x := by
  simp only [legendreMonic, eval_mul, eval_C, eval_neg_rodrigues]; ring

theorem eval_neg_legendreP (n : ℕ) (x : ℝ) :
    (legendrePoly n).eval (-x) = (-1) ^ n * (legendrePoly n).eval x := by
  simp only [legendrePoly, eval_mul, eval_C, eval_neg_rodrigues]; ring

/-- An odd integrand integrates to `0` over `[−1, 1]`. -/
theorem intervalIntegral_odd_eq_zero {g : ℝ → ℝ} (hg : ∀ x, g (-x) = -g x) :
    ∫ x in (-1 : ℝ)..1, g x = 0 := by
  have h := intervalIntegral.integral_comp_neg (a := -1) (b := 1) g
  rw [neg_neg] at h
  simp only [hg, intervalIntegral.integral_neg] at h
  linarith

theorem degree_sub_C_coeff_mul_lt {f g : ℝ[X]} {m : ℕ} (hf : f.degree < (m + 1 : ℕ))
    (hg : g.Monic) (hgd : g.natDegree = m) :
    (f - C (f.coeff m) * g).degree < (m : WithBot ℕ) := by
  rw [degree_lt_iff_coeff_zero]
  intro i hi
  rw [coeff_sub, coeff_C_mul]
  rcases hi.lt_or_eq with hi | rfl
  · rw [coeff_eq_zero_of_degree_lt (hf.trans_le (by exact_mod_cast hi)),
      coeff_eq_zero_of_natDegree_lt (p := g) (by rw [hgd]; exact hi)]
    ring
  · rw [← hgd, hg.coeff_natDegree]; ring

/-- `γ_{k+2} = (k + 1)²/(4(k + 1)² − 1) · γ_{k+1}` (from 3.5.21). -/
theorem gaussGamma_legendre_succ (k : ℕ) :
    gaussGamma (Ioo (-1) 1) (fun _ => 1) (legendreMonic (k + 1)) =
      ((k + 1 : ℝ) ^ 2) / (4 * (k + 1) ^ 2 - 1) *
        gaussGamma (Ioo (-1) 1) (fun _ => 1) (legendreMonic k) := by
  rw [dlmf_3_5_21, dlmf_3_5_21, show 2 * (k + 1) = 2 * k + 1 + 1 by ring]
  simp only [Nat.factorial_succ]
  push_cast
  have h1 : (4 * ((k : ℝ) + 1) ^ 2 - 1) = (2 * k + 1) * (2 * k + 3) := by ring
  rw [h1]
  have : ((2 * k).factorial : ℝ) ≠ 0 := by positivity
  have : (k.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- The three-term recurrence of the monic Legendre polynomials:
`p_{k+2} = x p_{k+1} − (k + 1)²/(4(k + 1)² − 1) p_k`. -/
theorem legendreMonic_succ_succ (k : ℕ) :
    legendreMonic (k + 2) = X * legendreMonic (k + 1) -
      C (((k + 1 : ℝ) ^ 2) / (4 * (k + 1) ^ 2 - 1)) * legendreMonic k := by
  have hw := isGaussWeight_legendre
  set p := legendreMonic
  set β : ℝ := ((k + 1 : ℝ) ^ 2) / (4 * (k + 1) ^ 2 - 1)
  set r := X * p (k + 1) - p (k + 2) - C β * p k with hr_def
  have hmon : ∀ j, (p j).Monic := legendreMonic_monic
  have hdeg : ∀ j, (p j).natDegree = j := natDegree_legendreMonic
  have horth : ∀ j, IsOrthMonic (Ioo (-1) 1) (fun _ => 1) j (p j) := isOrthMonic_legendreMonic
  have hdegX : ∀ j, (X * p j).natDegree = j + 1 := fun j => by
    rw [natDegree_mul X_ne_zero (hmon j).ne_zero, natDegree_X, hdeg]; ring
  have hdegp : ∀ j, (p j).degree = (j : WithBot ℕ) := fun j => by
    rw [degree_eq_natDegree (hmon j).ne_zero, hdeg]
  have hlt : ∀ {a b : ℕ}, a < b → (a : WithBot ℕ) < (b : WithBot ℕ) := fun h => by exact_mod_cast h
  -- `deg r < k + 2`
  have hr1 : (X * p (k + 1) - p (k + 2)).degree < ((k + 2 : ℕ) : WithBot ℕ) := by
    have hX0 : X * p (k + 1) ≠ 0 := mul_ne_zero X_ne_zero (hmon _).ne_zero
    have := degree_sub_lt_left (p := X * p (k + 1)) (q := p (k + 2))
      (by rw [degree_eq_natDegree hX0, hdegp, hdegX]) hX0
      (by rw [((monic_X).mul (hmon _)).leadingCoeff, (hmon _).leadingCoeff])
    rwa [degree_eq_natDegree hX0, hdegX] at this
  have hr2 : (C β * p k).degree < ((k + 2 : ℕ) : WithBot ℕ) :=
    degree_le_natDegree.trans_lt (hlt (((natDegree_C_mul_le _ _).trans (hdeg k).le).trans_lt
      (by omega)))
  have hr : r.degree < ((k + 2 : ℕ) : WithBot ℕ) := (degree_sub_le _ _).trans_lt (max_lt hr1 hr2)
  -- `r ⊥` polynomials of degree `< k`
  have hlow : ∀ q : ℝ[X], q.degree < (k : WithBot ℕ) →
      wInt (Ioo (-1) 1) (fun _ => 1) (r * q) = 0 := by
    intro q hq
    have hXq : (X * q).degree < ((k + 1 : ℕ) : WithBot ℕ) := by
      rcases eq_or_ne q 0 with rfl | hq0
      · simp
      · rw [degree_eq_natDegree (mul_ne_zero X_ne_zero hq0), natDegree_mul X_ne_zero hq0,
          natDegree_X]
        rw [degree_eq_natDegree hq0] at hq
        have : q.natDegree < k := by exact_mod_cast hq
        exact hlt (by omega)
    rw [show r * q = p (k + 1) * (X * q) - p (k + 2) * q - C β * (p k * q) by
      simp only [hr_def]; ring, wInt_sub hw, wInt_sub hw, wInt_C_mul,
      (horth _).wInt_mul_eq_zero hXq,
      (horth _).wInt_mul_eq_zero (hq.trans (hlt (by omega))),
      (horth _).wInt_mul_eq_zero hq]
    ring
  -- `r ⊥ p_k`
  have hk : wInt (Ioo (-1) 1) (fun _ => 1) (r * p k) = 0 := by
    have hXpk : (X * p k - p (k + 1)).degree < ((k + 1 : ℕ) : WithBot ℕ) := by
      have hX0 : X * p k ≠ 0 := mul_ne_zero X_ne_zero (hmon _).ne_zero
      have := degree_sub_lt_left (p := X * p k) (q := p (k + 1))
        (by rw [degree_eq_natDegree hX0, hdegp, hdegX]) hX0
        (by rw [((monic_X).mul (hmon _)).leadingCoeff, (hmon _).leadingCoeff])
      rwa [degree_eq_natDegree hX0, hdegX] at this
    rw [show r * p k = p (k + 1) * p (k + 1) + p (k + 1) * (X * p k - p (k + 1)) -
        p (k + 2) * p k - C β * (p k * p k) by simp only [hr_def]; ring,
      wInt_sub hw, wInt_sub hw, wInt_add hw, wInt_C_mul, (horth (k + 1)).wInt_mul_eq_zero hXpk,
      (horth (k + 2)).wInt_mul_eq_zero (by rw [hdegp]; exact hlt (by omega))]
    have := gaussGamma_legendre_succ k
    simp only [gaussGamma] at this
    rw [this]
    ring
  -- `r ⊥ p_{k+1}` (parity)
  have hk1 : wInt (Ioo (-1) 1) (fun _ => 1) (r * p (k + 1)) = 0 := by
    rw [show r * p (k + 1) = X * (p (k + 1) * p (k + 1)) - p (k + 2) * p (k + 1) -
        C β * (p (k + 1) * p k) by simp only [hr_def]; ring,
      wInt_sub hw, wInt_sub hw, wInt_C_mul,
      (horth (k + 2)).wInt_mul_eq_zero (by rw [hdegp]; exact hlt (by omega)),
      (horth (k + 1)).wInt_mul_eq_zero (by rw [hdegp]; exact hlt (by omega)), wInt_Ioo_one]
    rw [intervalIntegral_odd_eq_zero fun x => by
      simp only [eval_mul, eval_X, p, eval_neg_legendreMonic]
      have hsq : ((-1 : ℝ) ^ (k + 1)) * (-1) ^ (k + 1) = 1 := by rw [← mul_pow]; norm_num
      linear_combination (-x * (legendreMonic (k + 1)).eval x *
        (legendreMonic (k + 1)).eval x) * hsq]
    ring
  -- `r = 0`
  set c1 := r.coeff (k + 1)
  set r1 := r - C c1 * p (k + 1)
  have hr1d : r1.degree < ((k + 1 : ℕ) : WithBot ℕ) :=
    degree_sub_C_coeff_mul_lt hr (hmon _) (hdeg _)
  set c0 := r1.coeff k
  set r2 := r1 - C c0 * p k
  have hr2d : r2.degree < (k : WithBot ℕ) := degree_sub_C_coeff_mul_lt hr1d (hmon _) (hdeg _)
  have hrr : wInt (Ioo (-1) 1) (fun _ => 1) (r * r) = 0 := by
    rw [show r * r = C c1 * (r * p (k + 1)) + C c0 * (r * p k) + r * r2 by
      simp only [r2, r1]; ring, wInt_add hw, wInt_add hw, wInt_C_mul, wInt_C_mul, hk, hk1,
      hlow r2 hr2d]
    ring
  have hr0 : r = 0 := by
    by_contra h
    exact (wInt_mul_self_pos hw h).ne' hrr
  rw [hr_def] at hr0
  linear_combination -hr0

/-! ### The Legendre polynomials `P_n` -/

/-- The leading coefficient `k_n = (2n)!/(2ⁿ (n!)²)` of `P_n`. -/
noncomputable def legendreLead (n : ℕ) : ℝ := (2 * n).factorial / (2 ^ n * (n.factorial : ℝ) ^ 2)

/-- "The `p_n(x)` are the monic Legendre polynomials": `P_n = k_n p_n`. -/
theorem legendreP_eq (n : ℕ) : legendrePoly n = C (legendreLead n) * legendreMonic n := by
  rw [legendrePoly, legendreMonic, ← mul_assoc, ← C_mul, legendreLead]
  congr 2
  have : ((2 * n).factorial : ℝ) ≠ 0 := by positivity
  field_simp

theorem legendreLead_pos (n : ℕ) : 0 < legendreLead n := by unfold legendreLead; positivity

theorem legendreLead_succ (k : ℕ) :
    legendreLead (k + 1) = (2 * k + 1) / (k + 1) * legendreLead k := by
  unfold legendreLead
  rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring]
  simp only [Nat.factorial_succ]
  push_cast
  have : ((2 * k).factorial : ℝ) ≠ 0 := by positivity
  have : (k.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem eval_legendreP_zero (x : ℝ) : (legendrePoly 0).eval x = 1 := by
  simp [legendrePoly, rodrigues]

theorem eval_legendreP_one (x : ℝ) : (legendrePoly 1).eval x = x := by
  simp [legendrePoly, rodrigues]
  ring

/-- **Bonnet's recurrence** (18.9.1):
`(k + 2) P_{k+2}(x) = (2k + 3) x P_{k+1}(x) − (k + 1) P_k(x)`. -/
theorem eval_legendreP_succ_succ (k : ℕ) (x : ℝ) :
    (k + 2) * (legendrePoly (k + 2)).eval x =
      (2 * k + 3) * x * (legendrePoly (k + 1)).eval x - (k + 1) * (legendrePoly k).eval x := by
  have h := congrArg (eval x) (legendreMonic_succ_succ k)
  simp only [eval_sub, eval_mul, eval_X, eval_C] at h
  simp only [legendreP_eq, eval_mul, eval_C]
  have h1 := legendreLead_succ (k + 1)
  have h2 := legendreLead_succ k
  push_cast at h1 h2
  rw [h, h1, h2]
  have : (4 * ((k : ℝ) + 1) ^ 2 - 1) = (2 * k + 1) * (2 * k + 3) := by ring
  rw [this]
  field_simp
  ring

/-! ### The Christoffel numbers via the Christoffel function -/

/-- The Christoffel numbers are the reciprocals of the Christoffel function:
`wₖ ∑_{j<n} p_j(xₖ)²/γ_j = 1` (the matrix `(p_j(xₖ) √(wₖ/γ_j))` is orthogonal by 3.5.20_2). -/
theorem christoffel_mul_sum {I : Set ℝ} {w : ℝ → ℝ} (hw : IsGaussWeight I w) {P : ℕ → ℝ[X]}
    (hP : ∀ m, IsOrthMonic I w m (P m)) (n : ℕ) {xk : ℝ} (hk : xk ∈ (P n).roots.toFinset) :
    christoffel I w (P n) xk *
      ∑ j ∈ range n, (P j).eval xk ^ 2 / gaussGamma I w (P j) = 1 := by
  classical
  set s := (P n).roots.toFinset
  obtain ⟨hnodup, hcard, -⟩ := (hP n).roots_spec hw
  have hs : #s = n := by rw [Multiset.toFinset_card_of_nodup hnodup, hcard]
  set c := christoffel I w (P n)
  have hγ : ∀ j, 0 < gaussGamma I w (P j) := fun j => wInt_mul_self_pos hw (hP j).1.ne_zero
  have hc : ∀ y : s, 0 < c y := fun y => christoffel_pos hw (hP n) y.2
  let A : Matrix (Fin n) s ℝ := fun j y =>
    (P j).eval (y : ℝ) * (Real.sqrt (gaussGamma I w (P j)))⁻¹ * Real.sqrt (c y)
  have hAA : A * A.transpose = 1 := by
    ext j l
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.transpose_apply]
    simp only [A]
    have hsum : ∑ y : s, (P j).eval (y : ℝ) * (Real.sqrt (gaussGamma I w (P j)))⁻¹ *
        Real.sqrt (c y) * ((P l).eval (y : ℝ) * (Real.sqrt (gaussGamma I w (P l)))⁻¹ *
          Real.sqrt (c y)) =
        (Real.sqrt (gaussGamma I w (P j)))⁻¹ * (Real.sqrt (gaussGamma I w (P l)))⁻¹ *
          ∑ y ∈ s, (P j).eval y * (P l).eval y * c y := by
      rw [mul_sum, ← Finset.sum_coe_sort s]
      refine sum_congr rfl fun y _ => ?_
      have := Real.mul_self_sqrt (hc y).le
      linear_combination ((P j).eval (y : ℝ) * (P l).eval (y : ℝ) *
        (Real.sqrt (gaussGamma I w (P j)))⁻¹ * (Real.sqrt (gaussGamma I w (P l)))⁻¹) * this
    rw [hsum, dlmf_3_5_20_2 hw hP n j.2 l.2]
    by_cases hjl : j = l
    · subst hjl
      simp only [↓reduceIte]
      have e : wInt I w (P j * P j) = gaussGamma I w (P j) := rfl
      rw [e, ← mul_inv, Real.mul_self_sqrt (hγ j).le, inv_mul_cancel₀ (hγ j).ne']
    · have : (j : ℕ) ≠ l := fun h => hjl (Fin.ext h)
      simp [this, hjl]
  have hAA' := (Matrix.mul_eq_one_comm_of_card_eq (m := Fin n) (n := s) (R := ℝ) (A := A)
    (B := A.transpose) (by simp [hs])).mp hAA
  have hkk := congrFun (congrFun hAA' ⟨xk, hk⟩) ⟨xk, hk⟩
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at hkk
  simp only [Matrix.transpose_apply] at hkk
  simp only [A] at hkk
  rw [← hkk, mul_sum, ← Fin.sum_univ_eq_sum_range (fun j => c xk * ((P j).eval xk ^ 2 /
    gaussGamma I w (P j)))]
  refine sum_congr rfl fun j _ => ?_
  have h1 := Real.mul_self_sqrt (hγ j).le
  have h2 := (Real.sqrt_pos.mpr (hγ j)).ne'
  have h3 := Real.mul_self_sqrt (hc ⟨xk, hk⟩).le
  simp only at h3
  rw [show ∀ a b d : ℝ, a * b⁻¹ * d * (a * b⁻¹ * d) = a ^ 2 * (b * b)⁻¹ * (d * d) from
    fun a b d => by ring, h1, h3]
  ring

theorem legendreLead_sq_mul_gamma (j : ℕ) :
    legendreLead j ^ 2 * gaussGamma (Ioo (-1) 1) (fun _ => 1) (legendreMonic j) =
      2 / (2 * j + 1) := by
  rw [dlmf_3_5_21, legendreLead]
  have : ((2 * j).factorial : ℝ) ≠ 0 := by positivity
  have : (j.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- The Gauss–Legendre weights: `wₖ = 2/∑_{j<n} (2j + 1) P_j(xₖ)²`. -/
theorem christoffel_legendre (n : ℕ) {xk : ℝ} (hk : xk ∈ (legendreMonic n).roots.toFinset) :
    christoffel (Ioo (-1) 1) (fun _ => 1) (legendreMonic n) xk =
      2 / ∑ j ∈ range n, (2 * j + 1) * (legendrePoly j).eval xk ^ 2 := by
  have h := christoffel_mul_sum isGaussWeight_legendre isOrthMonic_legendreMonic n hk
  have hterm : ∀ j, (legendreMonic j).eval xk ^ 2 /
      gaussGamma (Ioo (-1) 1) (fun _ => 1) (legendreMonic j) =
      (2 * j + 1) * (legendrePoly j).eval xk ^ 2 / 2 := fun j => by
    have hl := legendreLead_sq_mul_gamma j
    have hL := (legendreLead_pos j).ne'
    rw [legendreP_eq, eval_mul, eval_C]
    rw [gaussGamma] at hl
    have hγ' : wInt (Ioo (-1) 1) (fun _ => 1) (legendreMonic j * legendreMonic j) =
        2 / (2 * j + 1) / legendreLead j ^ 2 := by
      rw [← hl]; field_simp
    rw [gaussGamma, hγ']
    field_simp
  simp only [hterm, ← sum_div] at h
  have hS : ∑ j ∈ range n, (2 * j + 1) * (legendrePoly j).eval xk ^ 2 ≠ 0 := by
    intro h0; rw [h0, zero_div, mul_zero] at h; exact zero_ne_one h
  field_simp at h ⊢
  linarith

end Azurite.DLMF
