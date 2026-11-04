/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section5GaussChebyshev
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# DLMF §3.5(v): the Gauss–Jacobi formula

Formula 3.5.26.

* The weight `jacW α β = (1 − x)^α (1 + x)^β`, `intervalIntegrable_jac`, `isGaussWeight_jacW`
  (`α, β > −1`).
* Rodrigues: `jacR`, `jacF` (`Dᵏ[(1 − x)ᵃ (1 + x)ᵇ] = (1 − x)^{a−k} (1 + x)^{b−k} R_k`,
  `hasDerivAt_jacF`, `iteratedDeriv_jac`), `jacobiP` and `jacobiP_rodrigues` (18.5.5).
* Orthogonality by integration by parts with vanishing boundary terms (`continuousOn_jacF`,
  `jacF_one`, `jacF_neg_one`, `integral_mul_jacF_succ`, `integral_mul_jacF`); the leading
  coefficient `jacLead` (`jacR_degree`); `jacMonic`, `isOrthMonic_jacMonic`, `jacMonic_eq_jacobiP`
  ("the `p_n(x)` are the monic Jacobi polynomials").
* 3.5.26: `dlmf_3_5_26` (`n ≥ 1`), via the real Beta integral `integral_rpow_mul_one_sub_rpow`
  (from Mathlib's complex `betaIntegral`), `integral_jac_beta` and `jacGamma_add_nat`.
-/

open Polynomial Finset Set MeasureTheory intervalIntegral Real

namespace Azurite.DLMF

/-! ### The Jacobi weight -/

/-- The Jacobi weight `w(x) = (1 − x)^α (1 + x)^β`. -/
noncomputable def jacW (α β x : ℝ) : ℝ := (1 - x) ^ α * (1 + x) ^ β

/-- `g(x) (1 − x)^a (1 + x)^b` is integrable on `[−1, 1]` for continuous `g` and `a, b > −1`. -/
theorem intervalIntegrable_jac {a b : ℝ} (ha : -1 < a) (hb : -1 < b) {g : ℝ → ℝ}
    (hg : Continuous g) :
    IntervalIntegrable (fun x => g x * ((1 - x) ^ a * (1 + x) ^ b)) volume (-1) 1 := by
  have e : (fun x => g x * ((1 - x) ^ a * (1 + x) ^ b)) =
      fun x => (g x * (1 - x) ^ a) * (1 + x) ^ b := by funext x; ring
  have e' : (fun x => g x * ((1 - x) ^ a * (1 + x) ^ b)) =
      fun x => (g x * (1 + x) ^ b) * (1 - x) ^ a := by funext x; ring
  have h1 : IntervalIntegrable (fun x => g x * ((1 - x) ^ a * (1 + x) ^ b)) volume (-1) 0 := by
    have hβ : IntervalIntegrable (fun x => (1 + x) ^ b) volume (-1) 0 := by
      have := (intervalIntegral.intervalIntegrable_rpow' hb (a := 0) (b := 1)).comp_add_right 1
      simpa [add_comm] using this
    have hc : ContinuousOn (fun x => g x * (1 - x) ^ a) (uIcc (-1) 0) := by
      refine hg.continuousOn.mul (ContinuousOn.rpow_const (by fun_prop) fun x hx => Or.inl ?_)
      rw [Set.uIcc_of_le (by norm_num)] at hx
      linarith [hx.2]
    rw [e]; exact hβ.continuousOn_mul hc
  have h2 : IntervalIntegrable (fun x => g x * ((1 - x) ^ a * (1 + x) ^ b)) volume 0 1 := by
    have hα : IntervalIntegrable (fun x => (1 - x) ^ a) volume 0 1 := by
      have := (intervalIntegral.intervalIntegrable_rpow' ha (a := 1) (b := 0)).comp_sub_left 1
      simpa using this
    have hc : ContinuousOn (fun x => g x * (1 + x) ^ b) (uIcc 0 1) := by
      refine hg.continuousOn.mul (ContinuousOn.rpow_const (by fun_prop) fun x hx => Or.inl ?_)
      rw [Set.uIcc_of_le (by norm_num)] at hx
      linarith [hx.1]
    rw [e']; exact hα.continuousOn_mul hc
  exact h1.trans h2

/-- The Jacobi weight is a Gauss weight on `(−1, 1)` for `α, β > −1`. -/
theorem isGaussWeight_jacW {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) :
    IsGaussWeight (Ioo (-1) 1) (jacW α β) where
  isOpen := isOpen_Ioo
  ordConnected := ordConnected_Ioo
  nonempty := ⟨0, by norm_num, by norm_num⟩
  pos := fun x hx => mul_pos (rpow_pos_of_pos (by linarith [hx.2]) _)
    (rpow_pos_of_pos (by linarith [hx.1]) _)
  integrableOn := fun k => by
    have h := intervalIntegrable_jac hα hβ (continuous_pow k)
    rw [intervalIntegrable_iff, Set.uIoc_of_le (by norm_num)] at h
    exact h.mono_set Ioo_subset_Ioc_self

theorem wInt_jacW (α β : ℝ) (p : ℝ[X]) :
    wInt (Ioo (-1) 1) (jacW α β) p = ∫ x in (-1 : ℝ)..1, p.eval x * jacW α β x := by
  rw [wInt, integral_of_le (by norm_num), integral_Ioc_eq_integral_Ioo]

/-! ### Rodrigues' formula: `Dᵏ[(1 − x)ᵃ (1 + x)ᵇ] = (1 − x)^{a−k} (1 + x)^{b−k} R_k(x)` -/

/-- The polynomial factors `R_k` of the derivatives of `(1 − x)ᵃ (1 + x)ᵇ`. -/
noncomputable def jacR (a b : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | k + 1 => (C (-(a - k)) * (1 + X) + C (b - k) * (1 - X)) * jacR a b k +
      (1 - X ^ 2) * derivative (jacR a b k)

/-- `F_k(x) = (1 − x)^{a−k} (1 + x)^{b−k} R_k(x)`. -/
noncomputable def jacF (a b : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  (1 - x) ^ (a - k) * (1 + x) ^ (b - k) * (jacR a b k).eval x

theorem hasDerivAt_jacF (a b : ℝ) (k : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (jacF a b k) (jacF a b (k + 1) x) x := by
  have h1x : (1 - x) ≠ 0 := by linarith [hx.2]
  have h2x : (1 + x) ≠ 0 := by linarith [hx.1]
  have d1 : HasDerivAt (fun x : ℝ => (1 - x) ^ (a - k))
      ((a - k) * (1 - x) ^ (a - k - 1) * (0 - 1)) x :=
    (hasDerivAt_rpow_const (Or.inl h1x)).comp x ((hasDerivAt_const x 1).sub (hasDerivAt_id x))
  have d2 : HasDerivAt (fun x : ℝ => (1 + x) ^ (b - k))
      ((b - k) * (1 + x) ^ (b - k - 1) * (0 + 1)) x :=
    (hasDerivAt_rpow_const (Or.inl h2x)).comp x ((hasDerivAt_const x 1).add (hasDerivAt_id x))
  have d := (d1.mul d2).mul ((jacR a b k).hasDerivAt x)
  refine d.congr_deriv ?_
  have eA : (1 - x) ^ (a - k) = (1 - x) ^ (a - ((k + 1 : ℕ) : ℝ)) * (1 - x) := by
    rw [← rpow_add_one h1x]; congr 1; push_cast; ring
  have eA' : (1 - x) ^ (a - k - 1) = (1 - x) ^ (a - ((k + 1 : ℕ) : ℝ)) := by
    congr 1; push_cast; ring
  have eB : (1 + x) ^ (b - k) = (1 + x) ^ (b - ((k + 1 : ℕ) : ℝ)) * (1 + x) := by
    rw [← rpow_add_one h2x]; congr 1; push_cast; ring
  have eB' : (1 + x) ^ (b - k - 1) = (1 + x) ^ (b - ((k + 1 : ℕ) : ℝ)) := by
    congr 1; push_cast; ring
  simp only [Pi.mul_apply]
  rw [jacF, jacR, eA, eA', eB, eB']
  simp only [eval_add, eval_mul, eval_C, eval_sub, eval_one, eval_X, eval_pow]
  ring

/-! ### Integration by parts and orthogonality -/

section Rodrigues

variable {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ)
include hα hβ

omit hα hβ in
theorem jacF_eq_mul (k : ℕ) (x : ℝ) :
    jacF (n + α) (n + β) k x = (jacR (n + α) (n + β) k).eval x *
      ((1 - x) ^ ((n - k : ℝ) + α) * (1 + x) ^ ((n - k : ℝ) + β)) := by
  rw [jacF]; ring_nf

theorem intervalIntegrable_jacF {k : ℕ} (hk : k ≤ n) (q : ℝ[X]) :
    IntervalIntegrable (fun x => q.eval x * jacF (n + α) (n + β) k x) volume (-1) 1 := by
  have hk' : (0 : ℝ) ≤ n - k := by rw [sub_nonneg]; exact_mod_cast hk
  have h := intervalIntegrable_jac (a := (n - k : ℝ) + α) (b := (n - k : ℝ) + β) (by linarith)
    (by linarith) (g := fun x => q.eval x * (jacR (n + α) (n + β) k).eval x) (by fun_prop)
  refine h.congr fun x _ => ?_
  simp only [jacF_eq_mul]; ring

theorem continuousOn_jacF {k : ℕ} (hk : k < n) :
    ContinuousOn (jacF (n + α) (n + β) k) (Icc (-1) 1) := by
  have hk' : (1 : ℝ) ≤ n - k := by
    have : ((k + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hk
    push_cast at this; linarith
  unfold jacF
  refine ((ContinuousOn.rpow_const (by fun_prop) fun x _ => Or.inr (by linarith)).mul
    (ContinuousOn.rpow_const (by fun_prop) fun x _ => Or.inr (by linarith))).mul
    (jacR _ _ k).continuous.continuousOn

omit hβ in
theorem jacF_one {k : ℕ} (hk : k < n) : jacF (n + α) (n + β) k 1 = 0 := by
  have hk' : (1 : ℝ) ≤ n - k := by
    have : ((k + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hk
    push_cast at this; linarith
  rw [jacF, sub_self, zero_rpow (by linarith), zero_mul, zero_mul]

omit hα in
theorem jacF_neg_one {k : ℕ} (hk : k < n) : jacF (n + α) (n + β) k (-1) = 0 := by
  have hk' : (1 : ℝ) ≤ n - k := by
    have : ((k + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hk
    push_cast at this; linarith
  rw [jacF, show (1 : ℝ) + -1 = 0 by ring, zero_rpow (by linarith), mul_zero, zero_mul]

/-- One integration by parts: `∫ q F_{k+1} = −∫ q′ F_k` for `k < n`. -/
theorem integral_mul_jacF_succ {k : ℕ} (hk : k < n) (q : ℝ[X]) :
    ∫ x in (-1 : ℝ)..1, q.eval x * jacF (n + α) (n + β) (k + 1) x =
      -∫ x in (-1 : ℝ)..1, (derivative q).eval x * jacF (n + α) (n + β) k x := by
  have h := integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (-1 : ℝ) ≤ 1)
    (f := fun x => q.eval x * jacF (n + α) (n + β) k x)
    (f' := fun x => (derivative q).eval x * jacF (n + α) (n + β) k x +
      q.eval x * jacF (n + α) (n + β) (k + 1) x)
    (q.continuous.continuousOn.mul (continuousOn_jacF hα hβ n hk))
    (fun x hx => (q.hasDerivAt x).mul (hasDerivAt_jacF _ _ k hx))
    ((intervalIntegrable_jacF hα hβ n hk.le _).add (intervalIntegrable_jacF hα hβ n hk _))
  rw [jacF_one hα n hk, jacF_neg_one hβ n hk, mul_zero, mul_zero, sub_zero,
    intervalIntegral.integral_add (intervalIntegrable_jacF hα hβ n hk.le _)
      (intervalIntegrable_jacF hα hβ n hk _)] at h
  linarith

/-- Repeated integration by parts: `∫ q F_n = (−1)ʲ ∫ Dʲq F_{n−j}`. -/
theorem integral_mul_jacF (q : ℝ[X]) : ∀ j ≤ n,
    ∫ x in (-1 : ℝ)..1, q.eval x * jacF (n + α) (n + β) n x =
      (-1) ^ j * ∫ x in (-1 : ℝ)..1,
        (derivative^[j] q).eval x * jacF (n + α) (n + β) (n - j) x := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    rw [ih (by omega), show n - j = (n - (j + 1)) + 1 by omega,
      integral_mul_jacF_succ hα hβ n (by omega), Function.iterate_succ_apply']
    ring

end Rodrigues

/-! ### The leading coefficient of `R_k` -/

theorem jacR_succ_eq (a b : ℝ) (k : ℕ) :
    jacR a b (k + 1) = C (-(a - k) + (b - k)) * jacR a b k +
      C (-(a - k) - (b - k)) * (X * jacR a b k) + derivative (jacR a b k) -
        X ^ 2 * derivative (jacR a b k) := by
  rw [jacR]; simp only [map_add, map_sub, map_neg]; ring

theorem jacR_degree (a b : ℝ) (k : ℕ) :
    (jacR a b k).natDegree ≤ k ∧
      (jacR a b k).coeff k = ∏ j ∈ range k, (-(a + b - j)) := by
  induction k with
  | zero => simp [jacR]
  | succ k ih =>
    obtain ⟨hd, hc⟩ := ih
    set R := jacR a b k
    have hR' : (derivative R).natDegree ≤ k - 1 := (natDegree_derivative_le R).trans (by omega)
    constructor
    · rw [jacR_succ_eq]
      have h1 : (C (-(a - k) + (b - k)) * R).natDegree ≤ k + 1 :=
        (natDegree_C_mul_le _ _).trans (hd.trans (by omega))
      have h2 : (C (-(a - k) - (b - k)) * (X * R)).natDegree ≤ k + 1 :=
        (natDegree_C_mul_le _ _).trans ((natDegree_mul_le (p := X) (q := R)).trans
          (by rw [natDegree_X]; omega))
      have h3 : (derivative R).natDegree ≤ k + 1 := hR'.trans (by omega)
      have h4 : (X ^ 2 * derivative R).natDegree ≤ k + 1 := by
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · rw [eq_C_of_natDegree_le_zero hd, derivative_C, mul_zero, natDegree_zero]; omega
        · refine (natDegree_mul_le (p := X ^ 2) (q := derivative R)).trans ?_
          rw [natDegree_X_pow]; omega
      exact (natDegree_sub_le_of_le (natDegree_add_le_of_degree_le
        (natDegree_add_le_of_degree_le h1 h2) h3) h4).trans (max_self _).le
    · rw [jacR_succ_eq, coeff_sub, coeff_add, coeff_add, coeff_C_mul, coeff_C_mul, coeff_X_mul,
        coeff_eq_zero_of_natDegree_lt (by omega : R.natDegree < k + 1),
        coeff_eq_zero_of_natDegree_lt (by omega : (derivative R).natDegree < k + 1),
        coeff_X_pow_mul', hc, prod_range_succ]
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp; ring
      · simp only [show 2 ≤ k + 1 from by omega, ↓reduceIte]
        rw [show k + 1 - 2 = k - 1 by omega, coeff_derivative,
          show k - 1 + 1 = k by omega, hc]
        push_cast [show (1 : ℕ) ≤ k from hk]
        ring

/-! ### Beta and Gamma -/

/-- The real Beta integral `∫₀¹ t^{u−1} (1 − t)^{v−1} dt = Γ(u)Γ(v)/Γ(u + v)`. -/
theorem integral_rpow_mul_one_sub_rpow {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    ∫ t in (0 : ℝ)..1, t ^ (u - 1) * (1 - t) ^ (v - 1) = Gamma u * Gamma v / Gamma (u + v) := by
  have h := Complex.betaIntegral_eq_Gamma_mul_div (u : ℂ) (v : ℂ) (by simpa) (by simpa)
  rw [Complex.betaIntegral] at h
  have hc : (∫ t in (0 : ℝ)..1, (t : ℂ) ^ ((u : ℂ) - 1) * (1 - (t : ℂ)) ^ ((v : ℂ) - 1)) =
      ((∫ t in (0 : ℝ)..1, t ^ (u - 1) * (1 - t) ^ (v - 1) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le zero_le_one] at ht
    push_cast
    rw [Complex.ofReal_cpow ht.1, Complex.ofReal_cpow (by linarith [ht.2])]
    push_cast; ring_nf
  rw [hc, ← Complex.ofReal_add, Complex.Gamma_ofReal, Complex.Gamma_ofReal,
    Complex.Gamma_ofReal] at h
  exact_mod_cast h

/-- `∫₋₁¹ (1 − x)^A (1 + x)^B dx = 2^{A+B+1} Γ(A + 1)Γ(B + 1)/Γ(A + B + 2)`, `A, B > −1`. -/
theorem integral_jac_beta {A B : ℝ} (hA : -1 < A) (hB : -1 < B) :
    ∫ x in (-1 : ℝ)..1, (1 - x) ^ A * (1 + x) ^ B =
      2 ^ (A + B + 1) * (Gamma (A + 1) * Gamma (B + 1) / Gamma (A + B + 2)) := by
  have h := intervalIntegral.integral_comp_mul_sub (fun x => (1 - x) ^ A * (1 + x) ^ B)
    (two_ne_zero) 1 (a := 0) (b := 1)
  norm_num at h
  have hβ := integral_rpow_mul_one_sub_rpow (u := B + 1) (v := A + 1) (by linarith) (by linarith)
  simp only [add_sub_cancel_right] at hβ
  have e : (∫ x in (0 : ℝ)..1, (1 - (2 * x - 1)) ^ A * (2 * x) ^ B) =
      2 ^ (A + B) * ∫ t in (0 : ℝ)..1, t ^ B * (1 - t) ^ A := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le zero_le_one] at ht
    rw [show 1 - (2 * t - 1) = 2 * (1 - t) by ring,
      mul_rpow (by norm_num) (by linarith [ht.2]), mul_rpow (by norm_num) ht.1,
      rpow_add (by norm_num)]
    ring
  rw [e, hβ] at h
  rw [show A + B + 2 = B + 1 + (A + 1) by ring, rpow_add_one (by norm_num)]
  linear_combination -2 * h

theorem jacGamma_add_nat {s : ℝ} (hs : 0 < s) (n : ℕ) :
    Gamma (s + n) = Gamma s * ∏ i ∈ range n, (s + i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ, ← mul_assoc, ← ih, Nat.cast_succ, ← add_assoc,
      Gamma_add_one (by positivity : s + n ≠ 0)]
    ring

/-! ### The monic Jacobi polynomials and `γ_n` -/

/-- The leading coefficient `∏_{j<n} (−(2n + α + β − j))` of `R_n = Dⁿ`-factor. -/
noncomputable def jacLead (α β : ℝ) (n : ℕ) : ℝ := ∏ j ∈ range n, (-((n + α) + (n + β) - j))

/-- The Jacobi polynomial by Rodrigues' formula (18.5.5):
`(1 − x)^α (1 + x)^β P_n^{(α,β)}(x) = ((−1)ⁿ/(2ⁿ n!)) Dⁿ[(1 − x)^{n+α} (1 + x)^{n+β}]`. -/
noncomputable def jacobiP (α β : ℝ) (n : ℕ) : ℝ[X] :=
  C ((-1 : ℝ) ^ n / (2 ^ n * n.factorial)) * jacR (n + α) (n + β) n

/-- The monic Jacobi polynomial `p_n`. -/
noncomputable def jacMonic (α β : ℝ) (n : ℕ) : ℝ[X] := C (jacLead α β n)⁻¹ * jacR (n + α) (n + β) n

section Monic

variable {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ)
include hα hβ

theorem jacLead_ne_zero : jacLead α β n ≠ 0 :=
  prod_ne_zero_iff.mpr fun j hj => by
    have : (j : ℝ) + 1 ≤ n := by exact_mod_cast mem_range.mp hj
    exact neg_ne_zero.mpr (by linarith)

theorem natDegree_jacR : (jacR (n + α) (n + β) n).natDegree = n := by
  refine le_antisymm (jacR_degree _ _ n).1 (le_natDegree_of_ne_zero ?_)
  rw [(jacR_degree _ _ n).2]
  exact jacLead_ne_zero hα hβ n

theorem jacMonic_monic : (jacMonic α β n).Monic := by
  rw [Monic, jacMonic, leadingCoeff_mul, leadingCoeff_C, leadingCoeff, natDegree_jacR hα hβ,
    (jacR_degree _ _ n).2]
  exact inv_mul_cancel₀ (jacLead_ne_zero hα hβ n)

theorem natDegree_jacMonic : (jacMonic α β n).natDegree = n := by
  rw [jacMonic, natDegree_C_mul (inv_ne_zero (jacLead_ne_zero hα hβ n)), natDegree_jacR hα hβ]

omit hα hβ in
theorem jacF_n_eq (x : ℝ) :
    jacF (n + α) (n + β) n x = (jacR (n + α) (n + β) n).eval x * jacW α β x := by
  rw [jacF, jacW, add_sub_cancel_left, add_sub_cancel_left]; ring

theorem wInt_jacMonic_mul (q : ℝ[X]) :
    wInt (Ioo (-1) 1) (jacW α β) (jacMonic α β n * q) = (jacLead α β n)⁻¹ * (-1) ^ n *
      ∫ x in (-1 : ℝ)..1, (derivative^[n] q).eval x * jacF (n + α) (n + β) 0 x := by
  rw [wInt_jacW, show (fun x => (jacMonic α β n * q).eval x * jacW α β x) =
      fun x => (jacLead α β n)⁻¹ * (q.eval x * jacF (n + α) (n + β) n x) by
    funext x; rw [jacF_n_eq, jacMonic, eval_mul, eval_mul, eval_C]; ring,
    intervalIntegral.integral_const_mul, integral_mul_jacF hα hβ n q n le_rfl, Nat.sub_self]
  ring

/-- The monic Jacobi polynomials are the monic orthogonal polynomials of the weight
`(1 − x)^α (1 + x)^β`. -/
theorem isOrthMonic_jacMonic : IsOrthMonic (Ioo (-1) 1) (jacW α β) n (jacMonic α β n) := by
  refine ⟨jacMonic_monic hα hβ n, natDegree_jacMonic hα hβ n, fun q hq => ?_⟩
  rw [wInt_jacMonic_mul hα hβ, iterate_derivative_eq_zero_of_degree_lt hq]
  simp

omit hα hβ in
/-- "The `p_n(x)` are the monic Jacobi polynomials `P_n^{(α,β)}(x)`": `p_n = P_n/k_n`. -/
theorem jacMonic_eq_jacobiP :
    jacMonic α β n =
      C ((-1 : ℝ) ^ n / (2 ^ n * n.factorial) * jacLead α β n)⁻¹ * jacobiP α β n := by
  rw [jacMonic, jacobiP, ← mul_assoc, ← C_mul]
  congr 2
  have : ((-1 : ℝ) ^ n / (2 ^ n * n.factorial)) ≠ 0 := by
    apply div_ne_zero (pow_ne_zero _ (by norm_num)); positivity
  rw [mul_inv]
  field_simp

end Monic

/-- **DLMF 3.5.26**: for the Jacobi weight `(1 − x)^α (1 + x)^β`, `α, β > −1`, `n ≥ 1`,
`γ_n = Γ(n+α+1)Γ(n+β+1)Γ(n+α+β+1)/((2n+α+β+1) Γ(2n+α+β+1)²) · 2^{2n+α+β+1} n!`. -/
theorem dlmf_3_5_26 {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) {n : ℕ} (hn : 1 ≤ n) :
    gaussGamma (Ioo (-1) 1) (jacW α β) (jacMonic α β n) =
      Gamma (n + α + 1) * Gamma (n + β + 1) * Gamma (n + α + β + 1) /
        ((2 * n + α + β + 1) * Gamma (2 * n + α + β + 1) ^ 2) *
          2 ^ (2 * n + α + β + 1) * n.factorial := by
  have hw := isGaussWeight_jacW hα hβ
  have horth := isOrthMonic_jacMonic hα hβ n
  set p := jacMonic α β n
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  -- `γ_n = ∫ xⁿ p_n w`
  have hdeg : (p - X ^ n).degree < (n : WithBot ℕ) := by
    have hp := jacMonic_monic hα hβ n
    have h := degree_sub_lt_left (p := p) (q := X ^ n)
      (by rw [degree_eq_natDegree hp.ne_zero, natDegree_jacMonic hα hβ, degree_X_pow])
      hp.ne_zero (by rw [hp.leadingCoeff, (monic_X_pow n).leadingCoeff])
    rwa [degree_eq_natDegree hp.ne_zero, natDegree_jacMonic hα hβ] at h
  rw [gaussGamma, show p * p = p * (p - X ^ n) + p * X ^ n by ring, wInt_add hw,
    horth.wInt_mul_eq_zero hdeg, zero_add, wInt_jacMonic_mul hα hβ,
    iterate_derivative_X_pow_eq_C_mul, Nat.descFactorial_self, Nat.sub_self, pow_zero, mul_one]
  simp only [eval_C]
  rw [intervalIntegral.integral_const_mul]
  -- the Beta integral
  have hF0 : (fun x => jacF (n + α) (n + β) 0 x) = fun x => (1 - x) ^ ((n : ℝ) + α) *
      (1 + x) ^ ((n : ℝ) + β) := by
    funext x; simp [jacF, jacR]
  rw [hF0, integral_jac_beta (by linarith) (by linarith)]
  -- the leading coefficient as a ratio of Gamma functions
  have hs : 0 < (n : ℝ) + α + β + 1 := by linarith
  have hprod : ∏ j ∈ range n, ((n + α) + (n + β) - (j : ℝ)) =
      Gamma (2 * n + α + β + 1) / Gamma (n + α + β + 1) := by
    rw [eq_div_iff (Gamma_pos_of_pos hs).ne', mul_comm, show (2 * n + α + β + 1 : ℝ) =
      (n + α + β + 1) + n by ring, jacGamma_add_nat hs n]
    congr 1
    rw [← prod_range_reflect (fun i : ℕ => (n : ℝ) + α + β + 1 + i) n]
    refine prod_congr rfl fun j hj => ?_
    have := mem_range.mp hj
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  have hlead : jacLead α β n = (-1) ^ n * (Gamma (2 * n + α + β + 1) / Gamma (n + α + β + 1)) := by
    rw [jacLead, ← hprod, prod_congr rfl fun j _ => (neg_one_mul _).symm, prod_mul_distrib,
      prod_const, card_range]
  have hG2 : Gamma (2 * n + α + β + 2) = (2 * n + α + β + 1) * Gamma (2 * n + α + β + 1) := by
    rw [show (2 * n + α + β + 2 : ℝ) = (2 * n + α + β + 1) + 1 by ring,
      Gamma_add_one (by linarith)]
  rw [hlead, show (n : ℝ) + α + ((n : ℝ) + β) + 1 = 2 * n + α + β + 1 by ring,
    show (n : ℝ) + α + ((n : ℝ) + β) + 2 = 2 * n + α + β + 2 by ring, hG2]
  have h1 := (Gamma_pos_of_pos hs).ne'
  have h2 := (Gamma_pos_of_pos (by linarith : (0 : ℝ) < 2 * n + α + β + 1)).ne'
  have h3 : (2 * (n : ℝ) + α + β + 1) ≠ 0 := by linarith
  have h4 : ((-1 : ℝ) ^ n) ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

/-! ### Rodrigues' formula (18.5.5) -/

theorem iteratedDeriv_jac (a b : ℝ) :
    ∀ k : ℕ, ∀ x ∈ Ioo (-1 : ℝ) 1,
      iteratedDeriv k (fun x => (1 - x) ^ a * (1 + x) ^ b) x = jacF a b k x := by
  intro k
  induction k with
  | zero => intro x _; simp [jacF, jacR]
  | succ k ih =>
    intro x hx
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv k (fun x => (1 - x) ^ a * (1 + x) ^ b) =ᶠ[nhds x] jacF a b k :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hx) ih
    rw [hev.deriv_eq, (hasDerivAt_jacF a b k hx).deriv]

/-- Rodrigues' formula (18.5.5):
`(1 − x)^α (1 + x)^β P_n^{(α,β)}(x) = ((−1)ⁿ/(2ⁿ n!)) Dⁿ[(1 − x)^{n+α} (1 + x)^{n+β}]`
on `(−1, 1)`. -/
theorem jacobiP_rodrigues (α β : ℝ) (n : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    jacW α β x * (jacobiP α β n).eval x = (-1) ^ n / (2 ^ n * n.factorial) *
      iteratedDeriv n (fun x => (1 - x) ^ ((n : ℝ) + α) * (1 + x) ^ ((n : ℝ) + β)) x := by
  rw [iteratedDeriv_jac _ _ n x hx, jacF_n_eq, jacobiP, eval_mul, eval_C]; ring

end Azurite.DLMF
