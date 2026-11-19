/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Feldman.ExpPoly

/-!
# The auxiliary function of Fel'dman's Theorem 3

For integers `y(k, l, τ)`, `k < q₀`, `l < q`, `τ < n`, and a complex number `ξ`:

  `C_{k,l} = ∑_τ y(k,l,τ) ξ^τ` (`coefC`),   `P_l = ∑_k C_{k,l} X^k` (`auxP`),
  `f(z) = ∑_l e^{lz} P_l(z)` (`auxF`),
  `V(s, x, w) = ∑_l (−1)^{lx} ((D + l)^s P_l)(i x w)` (`auxV`),   `x ∈ ℕ`.

`V(s, x, π) = f⁽ˢ⁾(πix)` (`auxV_pi`), while `V(s, x, ξ)` is "`f⁽ˢ⁾(πix)` with `π` replaced by
`ξ`", a polynomial in `ξ` with Gaussian integer coefficients (`auxV_eq_aeval`).  With `|y| ≤ C`
and `|ξ| ≤ 5` everything is bounded through `‖P_l‖₁ ≤ q₀ n C 5ⁿ` (`l1_auxP_le`):
`norm_auxV_le`, `norm_auxV_sub_le` (the change from `π` to `ξ`), `norm_auxF_le`.
`auxV_eq_sum` displays `V` as a linear form in `y`, for Dirichlet's principle.
-/

namespace Azurite.Feldman

open Polynomial Finset

/-- The index set of the unknowns `y(k, l, τ)`. -/
def idxJ (q₀ q n : ℕ) : Finset (ℕ × ℕ × ℕ) := range q₀ ×ˢ range q ×ˢ range n

theorem card_idxJ (q₀ q n : ℕ) : (idxJ q₀ q n).card = q₀ * (q * n) := by
  simp [idxJ]

/-- `C_{k,l} = ∑_{τ<n} y(k, l, τ) ξ^τ`. -/
noncomputable def coefC (n : ℕ) (y : ℕ × ℕ × ℕ → ℤ) (ξ : ℂ) (k l : ℕ) : ℂ :=
  ∑ τ ∈ range n, (y (k, l, τ) : ℂ) * ξ ^ τ

/-- `P_l = ∑_{k<q₀} C_{k,l} X^k`. -/
noncomputable def auxP (q₀ n : ℕ) (y : ℕ × ℕ × ℕ → ℤ) (ξ : ℂ) (l : ℕ) : ℂ[X] :=
  ∑ k ∈ range q₀, C (coefC n y ξ k l) * X ^ k

/-- `f(z) = ∑_{l<q} e^{lz} P_l(z)`. -/
noncomputable def auxF (q₀ q n : ℕ) (y : ℕ × ℕ × ℕ → ℤ) (ξ : ℂ) (z : ℂ) : ℂ :=
  ∑ l ∈ range q, Complex.exp (l * z) * (auxP q₀ n y ξ l).eval z

/-- `V(s, x, w) = ∑_{l<q} (−1)^{lx} ((D + l)^s P_l)(i x w)`. -/
noncomputable def auxV (q₀ q n : ℕ) (y : ℕ × ℕ × ℕ → ℤ) (ξ : ℂ) (s x : ℕ) (w : ℂ) : ℂ :=
  ∑ l ∈ range q, (-1 : ℂ) ^ (l * x)
    * (((shiftD (l : ℂ)) ^ s) (auxP q₀ n y ξ l)).eval (Complex.I * x * w)

variable {q₀ q n : ℕ} {y : ℕ × ℕ × ℕ → ℤ} {ξ : ℂ}

/-- `V(s, x, π) = f⁽ˢ⁾(πix)`. -/
theorem auxV_pi (q₀ q n : ℕ) (y : ℕ × ℕ × ℕ → ℤ) (ξ : ℂ) (s x : ℕ) :
    auxV q₀ q n y ξ s x Real.pi
      = iteratedDeriv s (auxF q₀ q n y ξ) (Complex.I * x * Real.pi) := by
  unfold auxF
  rw [iteratedDeriv_expPoly]
  unfold auxV
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  have h : (l : ℂ) * (Complex.I * x * Real.pi) = ((l * x : ℕ) : ℂ) * (Real.pi * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_nat_mul, Complex.exp_pi_mul_I]

theorem differentiable_auxF (q₀ q n : ℕ) (y : ℕ × ℕ × ℕ → ℤ) (ξ : ℂ) :
    Differentiable ℂ (auxF q₀ q n y ξ) := by
  unfold auxF
  fun_prop

/-! ### Bounds -/

theorem natDegree_auxP_le (q₀ n : ℕ) (y : ℕ × ℕ × ℕ → ℤ) (ξ : ℂ) (l : ℕ) :
    (auxP q₀ n y ξ l).natDegree ≤ q₀ - 1 := by
  unfold auxP
  refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
  have := mem_range.mp hk
  exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)

theorem norm_coefC_le {Cb : ℝ} (hy : ∀ j, |(y j : ℝ)| ≤ Cb) (hξ : ‖ξ‖ ≤ 5) (k l : ℕ) :
    ‖coefC n y ξ k l‖ ≤ n * (Cb * 5 ^ n) := by
  unfold coefC
  have hCb : 0 ≤ Cb := (abs_nonneg _).trans (hy (0, 0, 0))
  calc ‖∑ τ ∈ range n, (y (k, l, τ) : ℂ) * ξ ^ τ‖ ≤ ∑ _τ ∈ range n, Cb * 5 ^ n := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun τ hτ => ?_)
        rw [norm_mul, Complex.norm_intCast, norm_pow]
        have hτ' := (mem_range.mp hτ).le
        exact mul_le_mul (hy _) ((pow_le_pow_left₀ (norm_nonneg _) hξ τ).trans
          (pow_le_pow_right₀ (by norm_num) hτ')) (by positivity) hCb
    _ = n * (Cb * 5 ^ n) := by rw [Finset.sum_const, card_range, nsmul_eq_mul]

theorem l1_X_pow (k : ℕ) : l1 (X ^ k : ℂ[X]) = 1 := by
  have := l1_X_pow_mul k (1 : ℂ[X])
  rwa [mul_one, l1_one] at this

/-- `‖P_l‖₁ ≤ q₀ n C 5ⁿ`. -/
theorem l1_auxP_le {Cb : ℝ} (hy : ∀ j, |(y j : ℝ)| ≤ Cb) (hξ : ‖ξ‖ ≤ 5) (l : ℕ) :
    l1 (auxP q₀ n y ξ l) ≤ q₀ * (n * (Cb * 5 ^ n)) := by
  unfold auxP
  refine (l1_sum_le _ _).trans ?_
  calc ∑ k ∈ range q₀, l1 (C (coefC n y ξ k l) * X ^ k)
      ≤ ∑ _k ∈ range q₀, (n * (Cb * 5 ^ n) : ℝ) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [l1_C_mul, l1_X_pow, mul_one]
        exact norm_coefC_le hy hξ k l
    _ = q₀ * (n * (Cb * 5 ^ n)) := by rw [Finset.sum_const, card_range, nsmul_eq_mul]

/-- The polynomials `(D + l)^s P_l`, `l < q`: degree `< q₀` and `‖·‖₁ ≤ (q₀ + q)^s ‖P_l‖₁`. -/
theorem l1_shift_auxP_le {Cb : ℝ} (hy : ∀ j, |(y j : ℝ)| ≤ Cb) (hξ : ‖ξ‖ ≤ 5) {l : ℕ}
    (hl : l < q) (s : ℕ) :
    l1 (((shiftD (l : ℂ)) ^ s) (auxP q₀ n y ξ l))
      ≤ ((q₀ : ℝ) + q) ^ s * (q₀ * (n * (Cb * 5 ^ n))) := by
  have hCb : 0 ≤ Cb := (abs_nonneg _).trans (hy (0, 0, 0))
  refine (l1_shiftD_pow_le (natDegree_auxP_le q₀ n y ξ l) (l : ℂ) s).trans ?_
  have h1 : (((q₀ - 1 : ℕ) : ℝ) + ‖(l : ℂ)‖) ≤ (q₀ : ℝ) + q := by
    rw [Complex.norm_natCast]
    have : ((q₀ - 1 : ℕ) : ℝ) ≤ q₀ := by exact_mod_cast Nat.sub_le q₀ 1
    have : (l : ℝ) ≤ q := by exact_mod_cast hl.le
    linarith
  exact mul_le_mul (pow_le_pow_left₀ (by positivity) h1 s) (l1_auxP_le hy hξ l)
    (l1_nonneg _) (by positivity)

/-- `|V(s, x, w)| ≤ q (q₀ + q)^s q₀ n C 5ⁿ R^{q₀}` for `|x w| ≤ R`. -/
theorem norm_auxV_le {Cb : ℝ} (hy : ∀ j, |(y j : ℝ)| ≤ Cb) (hξ : ‖ξ‖ ≤ 5) (s x : ℕ) {w : ℂ}
    {R : ℝ} (hR : 1 ≤ R) (hw : x * ‖w‖ ≤ R) :
    ‖auxV q₀ q n y ξ s x w‖
      ≤ q * (((q₀ : ℝ) + q) ^ s * (q₀ * (n * (Cb * 5 ^ n))) * R ^ q₀) := by
  have hCb : 0 ≤ Cb := (abs_nonneg _).trans (hy (0, 0, 0))
  have hR0 : 0 ≤ R := by linarith
  unfold auxV
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum (g := fun _ =>
    ((q₀ : ℝ) + q) ^ s * (q₀ * (n * (Cb * 5 ^ n))) * R ^ q₀) fun l hl => ?_).trans
    (le_of_eq (by rw [Finset.sum_const, card_range, nsmul_eq_mul]))
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have hz : ‖Complex.I * x * w‖ ≤ R := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_natCast]
    exact hw
  refine (norm_eval_le_l1 (natDegree_shiftD_pow_le _ (natDegree_auxP_le q₀ n y ξ l) s) hR
    hz).trans ?_
  exact mul_le_mul (l1_shift_auxP_le hy hξ (mem_range.mp hl) s)
    (pow_le_pow_right₀ hR (Nat.sub_le _ _)) (by positivity) (by positivity)

/-- The change of `V` between two points `w₁`, `w₂`. -/
theorem norm_auxV_sub_le {Cb : ℝ} (hy : ∀ j, |(y j : ℝ)| ≤ Cb) (hξ : ‖ξ‖ ≤ 5) (s x : ℕ)
    {w₁ w₂ : ℂ} {R : ℝ} (hR : 1 ≤ R) (hw₁ : x * ‖w₁‖ ≤ R) (hw₂ : x * ‖w₂‖ ≤ R) :
    ‖auxV q₀ q n y ξ s x w₁ - auxV q₀ q n y ξ s x w₂‖
      ≤ ‖w₁ - w₂‖ * (x * (q * (q₀ * (((q₀ : ℝ) + q) ^ s * (q₀ * (n * (Cb * 5 ^ n)))
        * R ^ q₀)))) := by
  have hCb : 0 ≤ Cb := (abs_nonneg _).trans (hy (0, 0, 0))
  have hR0 : 0 ≤ R := by linarith
  unfold auxV
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ l ∈ range q,
      ‖(-1 : ℂ) ^ (l * x) * (((shiftD (l : ℂ)) ^ s) (auxP q₀ n y ξ l)).eval (Complex.I * x * w₁)
        - (-1 : ℂ) ^ (l * x)
          * (((shiftD (l : ℂ)) ^ s) (auxP q₀ n y ξ l)).eval (Complex.I * x * w₂)‖
      ≤ ‖w₁ - w₂‖ * (x * (q₀ * (((q₀ : ℝ) + q) ^ s * (q₀ * (n * (Cb * 5 ^ n))) * R ^ q₀))) := by
    intro l hl
    rw [← mul_sub, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    have hz : ∀ w : ℂ, x * ‖w‖ ≤ R → ‖Complex.I * x * w‖ ≤ R := fun w hw => by
      rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_natCast]
      exact hw
    have hd := natDegree_shiftD_pow_le (l : ℂ) (natDegree_auxP_le q₀ n y ξ l) s
    refine (norm_eval_sub_le hd hR (hz w₁ hw₁) (hz w₂ hw₂)).trans ?_
    have hdiff : ‖Complex.I * x * w₁ - Complex.I * x * w₂‖ = ‖w₁ - w₂‖ * x := by
      rw [← mul_sub, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_natCast, mul_comm]
    rw [hdiff, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    refine mul_le_mul (by exact_mod_cast Nat.sub_le q₀ 1) ?_
      (mul_nonneg (l1_nonneg _) (pow_nonneg hR0 _)) (Nat.cast_nonneg _)
    exact mul_le_mul (l1_shift_auxP_le hy hξ (mem_range.mp hl) s)
      (pow_le_pow_right₀ hR (Nat.sub_le _ _)) (by positivity) (by positivity)
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [Finset.sum_const, card_range, nsmul_eq_mul]
  ring

/-- `|f(z)| ≤ q e^{q|z|} q₀ n C 5ⁿ R^{q₀}` for `|z| ≤ R`. -/
theorem norm_auxF_le {Cb : ℝ} (hy : ∀ j, |(y j : ℝ)| ≤ Cb) (hξ : ‖ξ‖ ≤ 5) {z : ℂ} {R : ℝ}
    (hR : 1 ≤ R) (hz : ‖z‖ ≤ R) :
    ‖auxF q₀ q n y ξ z‖ ≤ q * (Real.exp (q * R) * (q₀ * (n * (Cb * 5 ^ n)) * R ^ q₀)) := by
  have hCb : 0 ≤ Cb := (abs_nonneg _).trans (hy (0, 0, 0))
  have hR0 : 0 ≤ R := by linarith
  unfold auxF
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum (g := fun _ =>
    Real.exp (q * R) * (q₀ * (n * (Cb * 5 ^ n)) * R ^ q₀)) fun l hl => ?_).trans
    (le_of_eq (by rw [Finset.sum_const, card_range, nsmul_eq_mul]))
  rw [norm_mul]
  have hl' : (l : ℝ) ≤ q := by exact_mod_cast (mem_range.mp hl).le
  have h1 : ‖Complex.exp (l * z)‖ ≤ Real.exp (q * R) := by
    refine (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
    rw [norm_mul, Complex.norm_natCast]
    exact mul_le_mul hl' hz (norm_nonneg _) (Nat.cast_nonneg _)
  have h2 : ‖(auxP q₀ n y ξ l).eval z‖ ≤ q₀ * (n * (Cb * 5 ^ n)) * R ^ q₀ :=
    (norm_eval_le_l1 (natDegree_auxP_le q₀ n y ξ l) hR hz).trans
      (mul_le_mul (l1_auxP_le hy hξ l) (pow_le_pow_right₀ hR (Nat.sub_le _ _))
        (by positivity) (by positivity))
  exact mul_le_mul h1 h2 (norm_nonneg _) (Real.exp_nonneg _)

/-! ### `V` as a linear form in `y` -/

/-- The coefficient of `y(k, l, τ)` in `V(s, x, w)`. -/
noncomputable def auxBeta (ξ : ℂ) (s x : ℕ) (w : ℂ) (j : ℕ × ℕ × ℕ) : ℂ :=
  ξ ^ j.2.2 * ((-1 : ℂ) ^ (j.2.1 * x)
    * (((shiftD (j.2.1 : ℂ)) ^ s) (X ^ j.1)).eval (Complex.I * x * w))

theorem auxV_eq_sum (q₀ q n : ℕ) (y : ℕ × ℕ × ℕ → ℤ) (ξ : ℂ) (s x : ℕ) (w : ℂ) :
    auxV q₀ q n y ξ s x w = ∑ j ∈ idxJ q₀ q n, (y j : ℂ) * auxBeta ξ s x w j := by
  unfold auxV auxP idxJ
  simp only [map_sum, ← smul_eq_C_mul, map_smul, eval_finsetSum, eval_smul, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_product]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun l _ => ?_
  unfold coefC auxBeta
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  ring

/-! ### Integrality: `V(s, x, ξ)` as a Gaussian integer polynomial in `ξ` -/

/-- `(D + l)^s X^k` as an integer polynomial. -/
noncomputable def auxE (s l k : ℕ) : ℤ[X] := ((shiftDZ (l : ℤ)) ^ s) (X ^ k)

theorem toC_auxE (s l k : ℕ) : toC (auxE s l k) = ((shiftD (l : ℂ)) ^ s) (X ^ k) := by
  unfold auxE
  rw [toC_shiftDZ_pow]
  simp [toC]

theorem natDegree_auxE_le (s l k : ℕ) : (auxE s l k).natDegree ≤ k := by
  rw [← natDegree_toC, toC_auxE]
  exact natDegree_shiftD_pow_le _ (natDegree_X_pow_le k) s

theorem sum_abs_coeff_auxE {q₀ : ℕ} (s l : ℕ) {k : ℕ} (hk : k < q₀) :
    ∑ j ∈ range q₀, |((auxE s l k).coeff j : ℝ)| ≤ ((k : ℝ) + l) ^ s := by
  have hdeg : (toC (auxE s l k)).natDegree < q₀ := by
    rw [natDegree_toC]
    exact (natDegree_auxE_le s l k).trans_lt hk
  have h1 : ∑ j ∈ range q₀, |((auxE s l k).coeff j : ℝ)| = l1 (toC (auxE s l k)) := by
    rw [l1_eq_sum_range hdeg]
    exact Finset.sum_congr rfl fun j _ => (norm_coeff_toC _ j).symm
  rw [h1, toC_auxE]
  have := l1_shiftD_pow_le (natDegree_X_pow_le (R := ℂ) k) (l : ℂ) s
  rwa [l1_X_pow, mul_one, Complex.norm_natCast] at this

/-- The integer polynomials `Q₁` (`part = reI`) and `Q₂` (`part = imI`) with
`V(s, x, ξ) = Q₁(ξ) + i Q₂(ξ)`. -/
noncomputable def auxQ (part : ℕ → ℤ) (q₀ q n : ℕ) (y : ℕ × ℕ × ℕ → ℤ) (s x : ℕ) : ℤ[X] :=
  ∑ jj ∈ idxJ q₀ q n, ∑ j ∈ range q₀,
    C (y jj * (-1) ^ (jj.2.1 * x) * (auxE s jj.2.1 jj.1).coeff j * (x : ℤ) ^ j * part j)
      * X ^ (jj.2.2 + j)

theorem auxV_eq_aeval (q₀ q n : ℕ) (y : ℕ × ℕ × ℕ → ℤ) (ξ : ℂ) (s x : ℕ) :
    auxV q₀ q n y ξ s x ξ
      = aeval ξ (auxQ reI q₀ q n y s x) + Complex.I * aeval ξ (auxQ imI q₀ q n y s x) := by
  rw [auxV_eq_sum]
  unfold auxQ
  simp only [map_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun jj hjj => ?_
  rw [← Finset.sum_add_distrib]
  have hk : jj.1 < q₀ := by
    have := hjj
    simp only [idxJ, mem_product, mem_range] at this
    exact this.1
  unfold auxBeta
  rw [← toC_auxE, ← aeval_eq_eval_toC,
    aeval_eq_sum_range' ((natDegree_auxE_le s jj.2.1 jj.1).trans_lt hk), Finset.mul_sum,
    Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [map_mul, map_pow, aeval_X, eq_intCast, zsmul_eq_mul, map_intCast, map_natCast,
    map_neg, map_one]
  rw [mul_pow, mul_pow, I_pow_eq j]
  ring

theorem natDegree_auxQ_le (part : ℕ → ℤ) (q₀ q n : ℕ) (y : ℕ × ℕ × ℕ → ℤ) (s x : ℕ) :
    (auxQ part q₀ q n y s x).natDegree ≤ (n - 1) + (q₀ - 1) := by
  unfold auxQ
  refine natDegree_sum_le_of_forall_le _ _ fun jj hjj => ?_
  refine natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
  simp only [idxJ, mem_product, mem_range] at hjj
  have := mem_range.mp hj
  exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)

/-- The heights of `Q₁`, `Q₂`. -/
theorem abs_coeff_auxQ_le {part : ℕ → ℤ} (hpart : ∀ j, |part j| ≤ 1) {Cb : ℝ}
    (hy : ∀ j, |(y j : ℝ)| ≤ Cb) (s x m : ℕ) :
    |((auxQ part q₀ q n y s x).coeff m : ℝ)|
      ≤ q₀ * (q * n) * (Cb * (((q₀ : ℝ) + q) ^ s * (max 1 x : ℝ) ^ q₀)) := by
  have hCb : 0 ≤ Cb := (abs_nonneg _).trans (hy (0, 0, 0))
  unfold auxQ
  rw [finsetSum_coeff]
  push_cast
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum (g := fun _ =>
    Cb * (((q₀ : ℝ) + q) ^ s * (max 1 x : ℝ) ^ q₀)) fun jj hjj => ?_).trans
    (le_of_eq (by rw [Finset.sum_const, card_idxJ, nsmul_eq_mul]; push_cast; ring))
  simp only [idxJ, mem_product, mem_range] at hjj
  obtain ⟨hk, hl, -⟩ := hjj
  rw [finsetSum_coeff]
  push_cast
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ j ∈ range q₀,
      |((C (y jj * (-1) ^ (jj.2.1 * x) * (auxE s jj.2.1 jj.1).coeff j * (x : ℤ) ^ j * part j)
        * X ^ (jj.2.2 + j) : ℤ[X]).coeff m : ℝ)|
      ≤ Cb * (max 1 x : ℝ) ^ q₀ * |((auxE s jj.2.1 jj.1).coeff j : ℝ)| := by
    intro j hj
    have hj' := (mem_range.mp hj).le
    rw [coeff_C_mul_X_pow]
    split_ifs
    · push_cast
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one,
        abs_pow, Nat.abs_cast]
      have h1 : (x : ℝ) ^ j ≤ (max 1 x : ℝ) ^ q₀ :=
        (pow_le_pow_left₀ (Nat.cast_nonneg _) (le_max_right _ _) j).trans
          (pow_le_pow_right₀ (le_max_left _ _) hj')
      have h2 : |(part j : ℝ)| ≤ 1 := by exact_mod_cast hpart j
      have h3 := hy jj
      have h4 : 0 ≤ |((auxE s jj.2.1 jj.1).coeff j : ℝ)| := abs_nonneg _
      have h5 : (0 : ℝ) ≤ (x : ℝ) ^ j := by positivity
      calc |(y jj : ℝ)| * |((auxE s jj.2.1 jj.1).coeff j : ℝ)| * (x : ℝ) ^ j * |(part j : ℝ)|
          ≤ Cb * |((auxE s jj.2.1 jj.1).coeff j : ℝ)| * (max 1 x : ℝ) ^ q₀ * 1 := by
            gcongr
        _ = Cb * (max 1 x : ℝ) ^ q₀ * |((auxE s jj.2.1 jj.1).coeff j : ℝ)| := by ring
    · simp only [Int.cast_zero, abs_zero]
      positivity
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have hE := sum_abs_coeff_auxE s jj.2.1 hk
  have hE' : ((jj.1 : ℝ) + jj.2.1) ^ s ≤ ((q₀ : ℝ) + q) ^ s := by
    refine pow_le_pow_left₀ (by positivity) ?_ s
    have h1 : (jj.1 : ℝ) ≤ q₀ := by exact_mod_cast hk.le
    have h2 : (jj.2.1 : ℝ) ≤ q := by exact_mod_cast hl.le
    linarith
  calc Cb * (max 1 x : ℝ) ^ q₀ * ∑ j ∈ range q₀, |((auxE s jj.2.1 jj.1).coeff j : ℝ)|
      ≤ Cb * (max 1 x : ℝ) ^ q₀ * ((q₀ : ℝ) + q) ^ s :=
        mul_le_mul_of_nonneg_left (hE.trans hE') (by positivity)
    _ = Cb * (((q₀ : ℝ) + q) ^ s * (max 1 x : ℝ) ^ q₀) := by ring

end Azurite.Feldman
