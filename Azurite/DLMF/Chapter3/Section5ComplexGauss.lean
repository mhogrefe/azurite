/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter2.Section4Inverse
import Azurite.DLMF.Chapter3.Section5GaussLaguerre
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# DLMF §3.5(viii): complex Gauss quadrature

* 3.5.35: the Bromwich integral `cgI` (`bromwich` of §2.4(ii) at `t = 1`); its moments
  `(2πi)^{−1} ∫ e^ζ ζ^{−s−k} dζ = 1/Γ(s + k)` (`tendsto_cgI_pow`, from `bromwich_Gamma_cpow`), so
  for `f(ζ) = q(1/ζ)` polynomial, `I(f) = L(q)` with `L(q) = ∑ q_k/Γ(s + k)` (`cgL`, `cgI_poly`).
* 3.5.37: the complex orthogonal polynomials, explicitly
  `p_n(u) = ∑ⱼ (−1)ʲ C(n, j)(s + n − 1)_j uʲ = ₂F₀(−n, s + n − 1; ; u)` (`cgP`, `cgc`),
  orthogonal by forward differences (`sum_cgc_mu`, `cgL_cgP_mul`, `dlmf_3_5_37`); "related to
  Bessel polynomials": `p_n(u) = y_n(−2u; s)` with `y_n` of 18.34.1 (`besselYGen`,
  `cgP_eq_besselYGen`).
* The zeros of `p_n` are simple and nonzero (`cgP_derivative_ne_zero`, via the differential equation
  `cgP_ode`, `cgP_ode_iter`; `nodup_roots_cgP`, `card_cgNodesU`); the nodes are `ζ_k = 1/u_k`
  (`cgNodes`, `mem_cgNodes`) and the weights `w_k = L(ℓ_k)` (`cgWeight`), explicitly
  `w_k = A(u_k)/p_n′(u_k)` (`cgA`, `cgWeight_eq`).
* 3.5.36: `E_n(f) = 0` for `f(ζ)` a polynomial of degree `≤ 2n − 1` in `1/ζ` (`cgE`,
  `dlmf_3_5_36`, from `cgL_eq_sum`).
* "The complex Gauss nodes have positive real part for all `s > 0`": proved for the tabulated case
  `n = 5`, `s = 1` (`cgNodes_one_five_re_pos` in `Section5ComplexGaussTable`); the general
  statement is deferred.
-/

open Polynomial Finset Set Filter Topology MeasureTheory

namespace Azurite.DLMF

/-! ### The Bromwich integral 3.5.35 and its moments -/

/-- The moments `1/Γ(s + k)`. -/
noncomputable def cgMu (s : ℝ) (k : ℕ) : ℝ := (Real.Gamma (s + k))⁻¹

/-- **DLMF 3.5.35**: `I(f) = (2πi)^{−1} ∫_{c−i∞}^{c+i∞} e^ζ ζ^{−s} f(ζ) dζ` (`ζ = c + iy`, the limit
of the symmetric integrals `∫_{−η}^{η}`, `bromwich` of §2.4(ii) with `t = 1`). -/
noncomputable def cgI (s c : ℝ) (f : ℂ → ℂ) : ℂ := bromwich (fun z => z ^ (-(s : ℂ)) * f z) c 1

theorem line_ne_zero {c : ℝ} (hc : 0 < c) (y : ℝ) : (c : ℂ) + y * Complex.I ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

theorem line_mem_slitPlane {c : ℝ} (hc : 0 < c) (y : ℝ) :
    (c : ℂ) + y * Complex.I ∈ Complex.slitPlane := Or.inl (by simpa using hc)

theorem bromwichPartial_const_mul (a : ℂ) (Q : ℂ → ℂ) (σ t η : ℝ) :
    bromwichPartial (fun z => a * Q z) σ t η = a * bromwichPartial Q σ t η := by
  unfold bromwichPartial
  rw [show (fun y : ℝ => Complex.exp (((σ : ℂ) + y * Complex.I) * t) *
      (a * Q ((σ : ℂ) + y * Complex.I))) = fun y : ℝ => a * (Complex.exp (((σ : ℂ) + y *
        Complex.I) * t) * Q ((σ : ℂ) + y * Complex.I)) by ext; ring,
    intervalIntegral.integral_const_mul]
  ring

theorem bromwichPartial_add {Q₁ Q₂ : ℂ → ℂ} {σ t : ℝ}
    (h₁ : Continuous fun y : ℝ => Q₁ ((σ : ℂ) + y * Complex.I))
    (h₂ : Continuous fun y : ℝ => Q₂ ((σ : ℂ) + y * Complex.I)) (η : ℝ) :
    bromwichPartial (fun z => Q₁ z + Q₂ z) σ t η =
      bromwichPartial Q₁ σ t η + bromwichPartial Q₂ σ t η := by
  unfold bromwichPartial
  rw [← mul_add, ← intervalIntegral.integral_add]
  · congr 1
    refine intervalIntegral.integral_congr fun y _ => ?_
    simp only
    ring
  · exact (by fun_prop : Continuous fun y : ℝ => Complex.exp (((σ : ℂ) + y * Complex.I) * t)).mul
      h₁ |>.intervalIntegrable _ _
  · exact (by fun_prop : Continuous fun y : ℝ => Complex.exp (((σ : ℂ) + y * Complex.I) * t)).mul
      h₂ |>.intervalIntegrable _ _

/-- The integrand `ζ^{−s} q(1/ζ)` is continuous on the line `ℜζ = c > 0`. -/
theorem continuous_line_cpow_poly {s c : ℝ} (hc : 0 < c) (q : ℂ[X]) :
    Continuous fun y : ℝ => ((c : ℂ) + y * Complex.I) ^ (-(s : ℂ)) *
      q.eval ((c : ℂ) + y * Complex.I)⁻¹ := by
  refine Continuous.mul ?_ ?_
  · exact Continuous.cpow (by fun_prop) continuous_const fun y => line_mem_slitPlane hc y
  · exact q.continuous.comp (Continuous.inv₀ (by fun_prop) fun y => line_ne_zero hc y)

/-- The moments: `(2πi)^{−1} ∫ e^ζ ζ^{−s} ζ^{−k} dζ = 1/Γ(s + k)`. -/
theorem tendsto_cgI_pow {s c : ℝ} (hs : 0 < s) (hc : 0 < c) (k : ℕ) :
    Tendsto (bromwichPartial (fun z => z ^ (-(s : ℂ)) * z⁻¹ ^ k) c 1) atTop
      (𝓝 (cgMu s k : ℂ)) := by
  set α : ℂ := ((s + k : ℝ) : ℂ)
  have hα : 0 < α.re := by simp [α]; positivity
  have h := bromwich_Gamma_cpow hα hc one_pos
  rw [Complex.ofReal_one, Complex.one_cpow] at h
  have hG : Complex.Gamma α ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hα
  have e : ∀ η, bromwichPartial (fun z => z ^ (-(s : ℂ)) * z⁻¹ ^ k) c 1 η =
      (Complex.Gamma α)⁻¹ * bromwichPartial (fun z => Complex.Gamma α * z ^ (-α)) c 1 η := by
    intro η
    rw [bromwichPartial_const_mul, ← mul_assoc, inv_mul_cancel₀ hG, one_mul]
    unfold bromwichPartial
    congr 1
    refine intervalIntegral.integral_congr fun y _ => ?_
    simp only
    have hz := line_ne_zero hc y
    set z := (c : ℂ) + y * Complex.I
    have hk : z ^ (-(k : ℂ)) = z⁻¹ ^ k := by
      rw [Complex.cpow_neg, Complex.cpow_natCast, inv_pow]
    rw [show -α = -(s : ℂ) + -(k : ℂ) by simp [α]; ring, Complex.cpow_add _ _ hz, hk]
  have h2 := h.const_mul (Complex.Gamma α)⁻¹
  rw [mul_one] at h2
  convert h2.congr fun η => (e η).symm using 2
  rw [cgMu, Complex.ofReal_inv, ← Complex.Gamma_ofReal]

/-- The linear functional `L(q) = ∑ q_k/Γ(s + k)` on polynomials in `u = 1/ζ`. -/
noncomputable def cgL (s : ℝ) : ℂ[X] →ₗ[ℂ] ℂ :=
  Polynomial.lsum fun k => LinearMap.mulRight ℂ (cgMu s k : ℂ)

theorem cgL_monomial (s : ℝ) (k : ℕ) (a : ℂ) : cgL s (monomial k a) = a * cgMu s k := by
  rw [cgL, lsum_apply, sum_monomial_index]
  · rfl
  · simp

theorem cgL_C_mul_X_pow (s : ℝ) (k : ℕ) (a : ℂ) : cgL s (C a * X ^ k) = a * cgMu s k := by
  rw [C_mul_X_pow_eq_monomial, cgL_monomial]

/-- For a polynomial `q` in `1/ζ`, the Bromwich integral is `L(q)`. -/
theorem tendsto_cgI_poly {s c : ℝ} (hs : 0 < s) (hc : 0 < c) (q : ℂ[X]) :
    Tendsto (bromwichPartial (fun z => z ^ (-(s : ℂ)) * q.eval z⁻¹) c 1) atTop
      (𝓝 (cgL s q)) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    have e : ∀ η, bromwichPartial (fun z => z ^ (-(s : ℂ)) * (p + q).eval z⁻¹) c 1 η =
        bromwichPartial (fun z => z ^ (-(s : ℂ)) * p.eval z⁻¹) c 1 η +
          bromwichPartial (fun z => z ^ (-(s : ℂ)) * q.eval z⁻¹) c 1 η := fun η => by
      rw [← bromwichPartial_add (continuous_line_cpow_poly hc p)
        (continuous_line_cpow_poly hc q)]
      simp only [eval_add, mul_add]
    rw [map_add]
    exact (hp.add hq).congr fun η => (e η).symm
  | monomial k a =>
    have e : ∀ η, bromwichPartial (fun z => z ^ (-(s : ℂ)) * (monomial k a).eval z⁻¹) c 1 η =
        a * bromwichPartial (fun z => z ^ (-(s : ℂ)) * z⁻¹ ^ k) c 1 η := fun η => by
      rw [← bromwichPartial_const_mul]
      simp only [eval_monomial]
      unfold bromwichPartial
      congr 1
      refine intervalIntegral.integral_congr fun y _ => ?_
      simp only
      ring
    rw [cgL_monomial]
    exact ((tendsto_cgI_pow hs hc k).const_mul a).congr fun η => (e η).symm

theorem cgI_poly {s c : ℝ} (hs : 0 < s) (hc : 0 < c) (q : ℂ[X]) :
    cgI s c (fun ζ => q.eval ζ⁻¹) = cgL s q :=
  bromwich_eq_of_tendsto (tendsto_cgI_poly hs hc q)

/-! ### The complex orthogonal polynomials 3.5.37 -/

/-- The coefficients `(−1)ʲ C(n, j) (s + n − 1)_j` of `p_n(u) = ₂F₀(−n, s + n − 1; ; u)`. -/
noncomputable def cgc (s : ℝ) (n j : ℕ) : ℝ :=
  (-1) ^ j * n.choose j * ∏ i ∈ range j, (s + n - 1 + i)

/-- The complex orthogonal polynomials `p_n(u)`, `u = 1/ζ`, of 3.5.37. -/
noncomputable def cgP (s : ℝ) (n : ℕ) : ℂ[X] := ∑ j ∈ range (n + 1), C (cgc s n j : ℂ) * X ^ j

theorem cgc_eq_zero {s : ℝ} {n j : ℕ} (h : n < j) : cgc s n j = 0 := by
  simp [cgc, Nat.choose_eq_zero_of_lt h]

theorem coeff_cgP (s : ℝ) (n j : ℕ) : (cgP s n).coeff j = cgc s n j := by
  simp only [cgP, finsetSum_coeff, coeff_C_mul_X_pow]
  by_cases h : j ≤ n
  · rw [sum_eq_single_of_mem j (mem_range.mpr (by omega)) fun i _ hij => by simp [Ne.symm hij]]
    simp
  · rw [sum_eq_zero fun i hi => by simp at hi; simp [show j ≠ i by omega], cgc_eq_zero (by omega)]
    simp

/-- `∑ⱼ (−1)ʲ C(n, j) (s+n−1)_j/Γ(s + j + m) = 0` for `m < n`. -/
theorem sum_cgc_mu {s : ℝ} (hs : 0 < s) {n m : ℕ} (hmn : m < n) :
    ∑ j ∈ range (n + 1), cgc s n j * cgMu s (j + m) = 0 := by
  set K := n - 1 - m
  set a : ℝ := s + n - 1
  have ha : 0 < a := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    simp only [a]; linarith
  have hGa := (Real.Gamma_pos_of_pos ha).ne'
  have hterm : ∀ j ∈ range (n + 1), cgc s n j * cgMu s (j + m) =
      (Real.Gamma a)⁻¹ * ((-1) ^ n * ((-1 : ℝ) ^ (n - j) * n.choose j *
        (lagQ (s + m - 1) K).eval (j : ℝ))) := fun j hj => by
    have hj := mem_range.mp hj
    have hsj : 0 < s + (j + m : ℕ) := by positivity
    have e1 := jacGamma_add_nat hsj K
    have e2 := jacGamma_add_nat ha j
    have hK : (K : ℝ) = n - 1 - m := by
      simp only [K]; rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
    rw [show s + ((j + m : ℕ) : ℝ) + (K : ℝ) = a + j by
      rw [hK]; simp only [a]; push_cast; ring] at e1
    have hG := (Real.Gamma_pos_of_pos hsj).ne'
    have hQ : (lagQ (s + m - 1) K).eval (j : ℝ) = ∏ i ∈ range K, (s + (j + m : ℕ) + i) := by
      simp only [lagQ, eval_prod, eval_add, eval_X, eval_C]
      refine prod_congr rfl fun i _ => ?_
      push_cast; ring
    rw [hQ, cgc, cgMu, show ∏ i ∈ range j, (s + n - 1 + i) = ∏ i ∈ range j, (a + i) by rfl]
    have hpow : (-1 : ℝ) ^ j = (-1) ^ n * (-1) ^ (n - j) := by
      rw [← pow_add, show n + (n - j) = j + 2 * (n - j) by omega, pow_add, pow_mul]; norm_num
    rw [hpow]
    have hprod : ∏ i ∈ range j, (a + i) = Real.Gamma (a + j) / Real.Gamma a := by
      rw [e2]; field_simp
    rw [hprod, e1]
    field_simp
  rw [sum_congr rfl hterm, ← mul_sum, ← mul_sum, sum_alt_choose_eq_fwdDiff,
    Polynomial.fwdDiff_iter_eq_zero_of_degree_lt (by rw [natDegree_lagQ]; omega)]
  simp

/-- `L(p_n u^m) = 0` for `m < n`. -/
theorem cgL_cgP_mul_X_pow {s : ℝ} (hs : 0 < s) {n m : ℕ} (hmn : m < n) :
    cgL s (cgP s n * X ^ m) = 0 := by
  rw [cgP, sum_mul, map_sum]
  simp only [mul_assoc, ← pow_add, cgL_C_mul_X_pow]
  have h := congrArg (fun x : ℝ => (x : ℂ)) (sum_cgc_mu hs hmn)
  push_cast at h
  exact h

/-- `L(p_n q) = 0` for `deg q < n`. -/
theorem cgL_cgP_mul {s : ℝ} (hs : 0 < s) {n : ℕ} {q : ℂ[X]} (hq : q.natDegree < n) :
    cgL s (cgP s n * q) = 0 := by
  rw [as_sum_range' q n hq, mul_sum, map_sum]
  refine sum_eq_zero fun i hi => ?_
  rw [← C_mul_X_pow_eq_monomial, mul_left_comm, ← smul_eq_C_mul, map_smul,
    cgL_cgP_mul_X_pow hs (mem_range.mp hi), smul_zero]

/-- **DLMF 3.5.37**: `(2πi)^{−1} ∫_{c−i∞}^{c+i∞} e^ζ ζ^{−s} p_k(1/ζ) p_ℓ(1/ζ) dζ = 0`
for `k ≠ ℓ`. -/
theorem dlmf_3_5_37 {s c : ℝ} (hs : 0 < s) (hc : 0 < c) {k l : ℕ} (hkl : k ≠ l) :
    cgI s c (fun ζ => (cgP s k).eval ζ⁻¹ * (cgP s l).eval ζ⁻¹) = 0 := by
  have h := cgI_poly hs hc (cgP s k * cgP s l)
  simp only [eval_mul] at h
  rw [h]
  have hdeg : ∀ m, (cgP s m).natDegree ≤ m := fun m =>
    (natDegree_sum_le_of_forall_le _ _ fun j hj =>
      (natDegree_C_mul_X_pow_le _ _).trans (by have := mem_range.mp hj; omega))
  rcases Nat.lt_or_gt_of_ne hkl with h1 | h1
  · rw [mul_comm]; exact cgL_cgP_mul hs ((hdeg k).trans_lt h1)
  · exact cgL_cgP_mul hs ((hdeg l).trans_lt h1)

/-! ### The relation to the generalized Bessel polynomials (§18.34) -/

/-- The generalized Bessel polynomial 18.34.1:
`y_n(x; a) = ₂F₀(−n, n + a − 1; ; −x/2) = ∑_ℓ (−n)_ℓ (n + a − 1)_ℓ (−x/2)^ℓ/ℓ!`. -/
noncomputable def besselYGen (n : ℕ) (a : ℝ) (x : ℂ) : ℂ :=
  ∑ l ∈ range (n + 1), ((∏ i ∈ range l, (-(n : ℝ) + i)) * (∏ i ∈ range l, ((n : ℝ) + a - 1 + i)) /
    l.factorial : ℝ) * (-x / 2) ^ l

theorem prod_neg_add_eq (n l : ℕ) :
    ∏ i ∈ range l, (-(n : ℝ) + i) = (-1) ^ l * n.choose l * l.factorial := by
  have h : ∀ l, ∏ i ∈ range l, ((n : ℝ) - i) = (n.descFactorial l : ℝ) := fun l => by
    induction l with
    | zero => simp
    | succ l ih =>
      rw [prod_range_succ, ih, Nat.descFactorial_succ]
      rcases le_or_gt l n with hl | hl
      · push_cast [hl]; ring
      · rw [Nat.descFactorial_eq_zero_iff_lt.mpr hl]; simp
  rw [show ∏ i ∈ range l, (-(n : ℝ) + i) = ∏ i ∈ range l, ((-1) * ((n : ℝ) - i)) from
    prod_congr rfl fun i _ => by ring, prod_mul_distrib, prod_const, card_range, h,
    Nat.descFactorial_eq_factorial_mul_choose]
  push_cast; ring

/-- "Related to Bessel polynomials": `p_n(u) = y_n(−2u; s)`. -/
theorem cgP_eq_besselYGen (s : ℝ) (n : ℕ) (u : ℂ) :
    (cgP s n).eval u = besselYGen n s (-2 * u) := by
  simp only [cgP, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, besselYGen]
  refine sum_congr rfl fun l _ => ?_
  rw [prod_neg_add_eq, cgc]
  have : (l.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero l)
  push_cast
  field_simp
  ring_nf

/-! ### Simple, nonzero zeros -/

theorem cgc_succ (s : ℝ) (n j : ℕ) :
    (j + 1 : ℝ) * cgc s n (j + 1) = (j - n) * (j + s + n - 1) * cgc s n j := by
  rcases le_or_gt n j with h | h
  · rw [cgc_eq_zero (by omega)]
    rcases eq_or_lt_of_le h with rfl | h'
    · ring
    · rw [cgc_eq_zero h']; ring
  · have hc := Nat.choose_succ_right_eq n j
    have hc' : ((n.choose (j + 1) : ℕ) : ℝ) * (j + 1) = n.choose j * (n - j) := by
      have := congrArg (fun x : ℕ => (x : ℝ)) hc
      push_cast [show j ≤ n by omega] at this
      exact this
    simp only [cgc, pow_succ, prod_range_succ]
    linear_combination (-((-1) ^ j * (∏ i ∈ range j, (s + n - 1 + i)) * (s + n - 1 + j))) * hc'

theorem cgc_zero (s : ℝ) (n : ℕ) : cgc s n 0 = 1 := by simp [cgc]

theorem cgc_self_ne_zero {s : ℝ} (hs : 0 < s) (n : ℕ) : cgc s n n ≠ 0 := by
  rw [cgc, Nat.choose_self, Nat.cast_one, mul_one]
  refine mul_ne_zero (pow_ne_zero _ (by norm_num)) (prod_ne_zero_iff.mpr fun i hi => ?_)
  have hi := mem_range.mp hi
  have : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have : (0 : ℝ) ≤ i := i.cast_nonneg
  linarith

theorem natDegree_cgP {s : ℝ} (hs : 0 < s) (n : ℕ) : (cgP s n).natDegree = n := by
  refine le_antisymm ?_ (le_natDegree_of_ne_zero ?_)
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro j hj
    rw [coeff_cgP, cgc_eq_zero (by exact_mod_cast hj)]
    simp
  · rw [coeff_cgP]; exact_mod_cast cgc_self_ne_zero hs n

theorem cgP_ne_zero {s : ℝ} (hs : 0 < s) (n : ℕ) : cgP s n ≠ 0 := by
  intro h
  have := coeff_cgP s n n
  rw [h, coeff_zero] at this
  exact cgc_self_ne_zero hs n (by exact_mod_cast this.symm)

theorem eval_zero_cgP (s : ℝ) (n : ℕ) : (cgP s n).eval 0 = 1 := by
  rw [← coeff_zero_eq_eval_zero, coeff_cgP, cgc_zero]; simp

/-- The differential equation of `₂F₀(−n, s + n − 1; ; u)`:
`u² p″ + (su − 1) p′ − n(s + n − 1) p = 0`. -/
theorem cgP_ode (s : ℝ) (n : ℕ) :
    X ^ 2 * derivative (derivative (cgP s n)) + (C (s : ℂ) * X - 1) * derivative (cgP s n) -
      C ((n : ℂ) * (s + n - 1)) * cgP s n = 0 := by
  have key : ∀ j : ℕ, ((j + 1 : ℂ)) * (cgc s n (j + 1) : ℂ) =
      ((j : ℂ) - n) * (j + s + n - 1) * (cgc s n j : ℂ) := fun j => by
    have := congrArg (fun x : ℝ => (x : ℂ)) (cgc_succ s n j); push_cast at this; exact this
  rw [show X ^ 2 * derivative (derivative (cgP s n)) + (C (s : ℂ) * X - 1) *
      derivative (cgP s n) - C ((n : ℂ) * (s + n - 1)) * cgP s n =
      X ^ 2 * derivative (derivative (cgP s n)) + C (s : ℂ) * (X * derivative (cgP s n)) -
        derivative (cgP s n) - C ((n : ℂ) * (s + n - 1)) * cgP s n by ring]
  ext j
  rcases j with _ | _ | k
  · have k0 := key 0
    simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow_mul', coeff_X_mul_zero,
      coeff_derivative, coeff_cgP, coeff_zero, show ¬ (2 ≤ 0) by omega, ↓reduceIte]
    push_cast at k0 ⊢
    linear_combination -k0
  · have k1 := key 1
    simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow_mul', coeff_X_mul,
      coeff_derivative, coeff_cgP, coeff_zero, show ¬ (2 ≤ 0 + 1) by omega, ↓reduceIte]
    push_cast at k1 ⊢
    linear_combination -k1
  · have k2 := key (k + 2)
    simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow_mul', coeff_X_mul,
      coeff_derivative, coeff_cgP, coeff_zero, show 2 ≤ k + 1 + 1 by omega, ↓reduceIte,
      show k + 1 + 1 - 2 = k by omega]
    push_cast at k2 ⊢
    linear_combination -k2

/-- The `k`-times differentiated equation. -/
theorem cgP_ode_iter (s : ℝ) (n k : ℕ) :
    X ^ 2 * derivative^[k + 2] (cgP s n) +
      ((2 : ℂ[X]) * (k : ℂ[X]) * X + C (s : ℂ) * X - 1) * derivative^[k + 1] (cgP s n) +
      ((k : ℂ[X]) * ((k : ℂ[X]) - 1) + (k : ℂ[X]) * C (s : ℂ) - C ((n : ℂ) * (s + n - 1))) *
        derivative^[k] (cgP s n) = 0 := by
  induction k with
  | zero =>
    have h := cgP_ode s n
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq,
      Nat.cast_zero, mul_zero, zero_mul, zero_add, zero_sub] at h ⊢
    linear_combination h
  | succ k ih =>
    have h := congrArg derivative ih
    simp only [derivative_add, derivative_sub, derivative_mul, derivative_X_pow, derivative_X,
      derivative_C, derivative_natCast, derivative_one, derivative_zero, derivative_ofNat,
      Function.iterate_succ_apply', Nat.cast_ofNat, map_ofNat, show 2 - 1 = 1 from rfl,
      pow_one] at h
    simp only [Function.iterate_succ_apply']
    push_cast
    linear_combination h

theorem cgP_iter_eval_eq_zero {s : ℝ} {n : ℕ} {u : ℂ} (hu : u ≠ 0)
    (h0 : (cgP s n).eval u = 0) (h1 : (derivative (cgP s n)).eval u = 0) :
    ∀ k, (derivative^[k] (cgP s n)).eval u = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => simpa using h0
    | 1, _ => simpa using h1
    | k + 2, ih =>
      have h := congrArg (eval u) (cgP_ode_iter s n k)
      simp only [eval_add, eval_mul, eval_pow, eval_X, eval_zero, ih k (by omega),
        ih (k + 1) (by omega), mul_zero, add_zero] at h
      exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 2 hu)

/-- The zeros of `p_n` are simple. -/
theorem cgP_derivative_ne_zero {s : ℝ} (hs : 0 < s) {n : ℕ} {u : ℂ} (hu : (cgP s n).IsRoot u) :
    (derivative (cgP s n)).eval u ≠ 0 := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [IsRoot.def, eval_zero_cgP] at hu
    exact one_ne_zero hu
  intro h1
  have hall := cgP_iter_eval_eq_zero hu0 hu h1 n
  have hD : derivative^[n] (cgP s n) = C ((n.factorial : ℂ) * cgc s n n) := by
    rw [eq_C_of_natDegree_le_zero ((natDegree_iterate_derivative _ n).trans
      (by rw [natDegree_cgP hs]; simp)), coeff_iterate_derivative, zero_add,
      Nat.descFactorial_self, coeff_cgP, nsmul_eq_mul]
  rw [hD, eval_C] at hall
  exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
    (by exact_mod_cast cgc_self_ne_zero hs n) hall

theorem nodup_roots_cgP {s : ℝ} (hs : 0 < s) (n : ℕ) : (cgP s n).roots.Nodup := by
  rw [Multiset.nodup_iff_count_le_one]
  intro t
  rw [count_roots]
  by_contra h
  push Not at h
  have := (lt_rootMultiplicity_iff_isRoot_iterate_derivative_of_mem_nonZeroDivisors'
    (cgP_ne_zero hs n) (n := 1) fun m _ hm0 =>
      mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hm0)).mp h
  have r0 := this 0 (by omega)
  have r1 := this 1 le_rfl
  simp only [Function.iterate_zero, id_eq, Function.iterate_one] at r0 r1
  exact cgP_derivative_ne_zero hs r0 r1

/-! ### Nodes, weights and the quadrature rule 3.5.36 -/

/-- The zeros `u_k` of `p_n(u)`. -/
noncomputable def cgNodesU (s : ℝ) (n : ℕ) : Finset ℂ := (cgP s n).roots.toFinset

/-- The complex Gauss nodes `ζ_k = 1/u_k`. -/
noncomputable def cgNodes (s : ℝ) (n : ℕ) : Finset ℂ := (cgNodesU s n).image fun u => u⁻¹

/-- The weights `w_k = L(ℓ_k)`, `ℓ_k` the Lagrange basis polynomial (in `u = 1/ζ`) of `1/ζ_k`. -/
noncomputable def cgWeight (s : ℝ) (n : ℕ) (ζ : ℂ) : ℂ :=
  cgL s (Lagrange.basis (cgNodesU s n) id ζ⁻¹)

theorem card_cgNodesU {s : ℝ} (hs : 0 < s) (n : ℕ) : #(cgNodesU s n) = n := by
  rw [cgNodesU, Multiset.toFinset_card_of_nodup (nodup_roots_cgP hs n),
    IsAlgClosed.card_roots_eq_natDegree (k := ℂ), natDegree_cgP hs]

theorem mem_cgNodesU {s : ℝ} (hs : 0 < s) {n : ℕ} {u : ℂ} :
    u ∈ cgNodesU s n ↔ (cgP s n).eval u = 0 := by
  rw [cgNodesU, Multiset.mem_toFinset, mem_roots (cgP_ne_zero hs n), IsRoot.def]

theorem ne_zero_of_mem_cgNodesU {s : ℝ} (hs : 0 < s) {n : ℕ} {u : ℂ} (hu : u ∈ cgNodesU s n) :
    u ≠ 0 := by
  rintro rfl
  rw [mem_cgNodesU hs, eval_zero_cgP] at hu
  exact one_ne_zero hu

/-- The nodes are the reciprocals of the zeros of `p_n(1/ζ)`. -/
theorem mem_cgNodes {s : ℝ} (hs : 0 < s) {n : ℕ} {ζ : ℂ} :
    ζ ∈ cgNodes s n ↔ ζ ≠ 0 ∧ (cgP s n).eval ζ⁻¹ = 0 := by
  rw [cgNodes, Finset.mem_image]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨inv_ne_zero (ne_zero_of_mem_cgNodesU hs hu), by rwa [inv_inv, ← mem_cgNodesU hs]⟩
  · rintro ⟨h0, h⟩
    exact ⟨ζ⁻¹, (mem_cgNodesU hs).mpr h, inv_inv ζ⟩

/-- Gauss exactness in `u = 1/ζ`: `L(q) = ∑ₖ L(ℓₖ) q(uₖ)` for `deg q ≤ 2n − 1`. -/
theorem cgL_eq_sum {s : ℝ} (hs : 0 < s) {n : ℕ} (hn : 1 ≤ n) {q : ℂ[X]} (hq : q.natDegree < 2 * n) :
    cgL s q = ∑ u ∈ cgNodesU s n, cgL s (Lagrange.basis (cgNodesU s n) id u) * q.eval u := by
  set P := cgP s n
  have hP0 := cgP_ne_zero hs n
  set Pm := C P.leadingCoeff⁻¹ * P
  have hPm : Pm.Monic := monic_C_mul_of_mul_leadingCoeff_eq_one
    (inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr hP0))
  have hPmdeg : Pm.natDegree = n := by
    rw [natDegree_C_mul (inv_ne_zero (leadingCoeff_ne_zero.mpr hP0)), natDegree_cgP hs]
  have hdecomp := (modByMonic_add_div q Pm).symm
  set r := q %ₘ Pm
  set a := q /ₘ Pm
  have ha : a.natDegree < n := by
    rw [natDegree_divByMonic q hPm, hPmdeg]; omega
  have hPa : cgL s (Pm * a) = 0 := by
    rw [mul_assoc, ← smul_eq_C_mul, map_smul, cgL_cgP_mul hs ha, smul_zero]
  have hr : r.degree < #(cgNodesU s n) := by
    rw [card_cgNodesU hs]
    have := degree_modByMonic_lt q hPm
    rwa [degree_eq_natDegree hPm.ne_zero, hPmdeg] at this
  have hinterp := Lagrange.eq_interpolate (s := cgNodesU s n) (v := id) (Set.injOn_id _) hr
  have hev : ∀ u ∈ cgNodesU s n, r.eval u = q.eval u := fun u hu => by
    have h := congrArg (eval u) hdecomp
    have hPu : Pm.eval u = 0 := by
      rw [eval_mul, eval_C, (mem_cgNodesU hs).mp hu, mul_zero]
    rw [eval_add, eval_mul, hPu, zero_mul, add_zero] at h
    exact h.symm
  conv_lhs => rw [hdecomp, map_add, hPa, add_zero, hinterp, Lagrange.interpolate_apply, map_sum]
  refine sum_congr rfl fun u hu => ?_
  rw [← smul_eq_C_mul, map_smul, smul_eq_mul, id, hev u hu, mul_comm]

/-- The error term of 3.5.36: `E_n(f) = I(f) − ∑ₖ wₖ f(ζₖ)`. -/
noncomputable def cgE (s c : ℝ) (n : ℕ) (f : ℂ → ℂ) : ℂ :=
  cgI s c f - ∑ ζ ∈ cgNodes s n, cgWeight s n ζ * f ζ

/-- **DLMF 3.5.36**: `I(f) = ∑ₖ wₖ f(ζₖ) + Eₙ(f)` with `Eₙ(f) = 0` when `f(ζ)` is a polynomial
of degree `≤ 2n − 1` in `1/ζ`. -/
theorem dlmf_3_5_36 {s c : ℝ} (hs : 0 < s) (hc : 0 < c) {n : ℕ} (hn : 1 ≤ n) {q : ℂ[X]}
    (hq : q.natDegree ≤ 2 * n - 1) : cgE s c n (fun ζ => q.eval ζ⁻¹) = 0 := by
  rw [cgE, cgI_poly hs hc, cgL_eq_sum hs hn (by omega), cgNodes,
    sum_image fun x _ y _ h => inv_injective h, sub_eq_zero]
  refine sum_congr rfl fun u _ => ?_
  rw [cgWeight, inv_inv]

/-! ### The weights as a function of the node -/

/-- `p_n(X) − p_n(u) = (X − u) Q_u(X)` with `Q_u = ∑ᵢ cᵢ ∑_{j<i} u^{i−1−j} Xʲ`. -/
noncomputable def cgQ (s : ℝ) (n : ℕ) (u : ℂ) : ℂ[X] :=
  ∑ i ∈ range (n + 1), C (cgc s n i : ℂ) * ∑ j ∈ range i, C (u ^ (i - 1 - j)) * X ^ j

theorem cgP_sub_eq (s : ℝ) (n : ℕ) (u : ℂ) :
    cgP s n - C ((cgP s n).eval u) = (X - C u) * cgQ s n u := by
  have hgeom : ∀ i : ℕ, (X - C u) * ∑ j ∈ range i, C (u ^ (i - 1 - j)) * X ^ j =
      X ^ i - C (u ^ i) := fun i => by
    have := Commute.geom_sum₂_mul (Commute.all (X : ℂ[X]) (C u)) i
    rw [map_pow, ← this, mul_comm]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    rw [map_pow]; ring
  simp only [cgP, cgQ, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, map_sum]
  rw [← sum_sub_distrib, Finset.mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_left_comm, hgeom, mul_sub, map_mul]

/-- The numerator `A(u) = L(Q_u) = ∑ᵢ cᵢ ∑_{j<i} u^{i−1−j}/Γ(s + j)`. -/
noncomputable def cgA (s : ℝ) (n : ℕ) (u : ℂ) : ℂ :=
  ∑ i ∈ range (n + 1), (cgc s n i : ℂ) * ∑ j ∈ range i, u ^ (i - 1 - j) * cgMu s j

theorem cgL_cgQ (s : ℝ) (n : ℕ) (u : ℂ) : cgL s (cgQ s n u) = cgA s n u := by
  simp only [cgQ, cgA, map_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [← smul_eq_C_mul, map_smul, map_sum, smul_eq_mul]
  congr 1
  refine sum_congr rfl fun j _ => ?_
  rw [cgL_C_mul_X_pow]

/-- The complex Gauss weights: `w_k = A(u_k)/p_n′(u_k)`, `u_k = 1/ζ_k`. -/
theorem cgL_basis_eq {s : ℝ} (hs : 0 < s) {n : ℕ} {u : ℂ} (hu : u ∈ cgNodesU s n) :
    cgL s (Lagrange.basis (cgNodesU s n) id u) =
      cgA s n u / (derivative (cgP s n)).eval u := by
  classical
  set P := cgP s n
  have hP0 := cgP_ne_zero hs n
  have hlc : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP0
  set Pm := C P.leadingCoeff⁻¹ * P
  have hPm : Pm.Monic := monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ hlc)
  have hnodal : Lagrange.nodal (cgNodesU s n) id = Pm := by
    have hroots : Pm.roots = P.roots := roots_C_mul _ (inv_ne_zero hlc)
    have hcard : Multiset.card Pm.roots = Pm.natDegree := IsAlgClosed.card_roots_eq_natDegree
    rw [Lagrange.nodal_eq, Finset.prod_eq_multiset_prod, cgNodesU, Multiset.toFinset_val,
      Multiset.dedup_eq_self.mpr (nodup_roots_cgP hs n), ← hroots]
    exact prod_multiset_X_sub_C_of_monic_of_roots_card_eq hPm hcard
  have hPu : P.eval u = 0 := (mem_cgNodesU hs).mp hu
  have hfac : Pm = (X - C u) * (C P.leadingCoeff⁻¹ * cgQ s n u) := by
    have : P - C (P.eval u) = (X - C u) * cgQ s n u := cgP_sub_eq s n u
    rw [hPu, map_zero, sub_zero] at this
    simp only [Pm]; rw [this]; ring
  have hdiv : Pm / (X - C u) = C P.leadingCoeff⁻¹ * cgQ s n u := by
    rw [hfac, mul_div_cancel_left₀ _ (X_sub_C_ne_zero u)]
  have hder : (derivative Pm).eval u = P.leadingCoeff⁻¹ * (derivative P).eval u := by
    simp [Pm]
  rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div hu, Lagrange.nodalWeight_eq_eval_derivative_nodal
    hu, hnodal, id, hdiv, hder, ← mul_assoc, ← C_mul, ← smul_eq_C_mul, map_smul, cgL_cgQ,
    smul_eq_mul]
  field_simp

/-- The weight at a node `ζ`: `w = A(1/ζ)/p_n′(1/ζ)`. -/
theorem cgWeight_eq {s : ℝ} (hs : 0 < s) {n : ℕ} {ζ : ℂ} (hζ : ζ ∈ cgNodes s n) :
    cgWeight s n ζ = cgA s n ζ⁻¹ / (derivative (cgP s n)).eval ζ⁻¹ := by
  obtain ⟨-, h⟩ := (mem_cgNodes hs).mp hζ
  exact cgL_basis_eq hs ((mem_cgNodesU hs).mpr h)

end Azurite.DLMF
