/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter4.Section4_7.HomotopyIFT
import Azurite.BasuPollackRoy.Chapter4.Section4_7.JacobianRank
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# BPR §4.7: discharging the determinant hypothesis of the homotopy IFT

`HomotopyIFT.lean` proves `homotopy_local_ift`, the projective implicit function theorem instantiated
for the homotopy system, taking the transversality hypothesis `hdet` (invertibility of the `y`-block
real Jacobian) as an explicit input.  This file *derives* `hdet` from the intrinsic non-singularity
of the projective zero, and packages the result as `homotopy_local_ift'`.

The mathematics is Cauchy–Riemann at the polynomial level: the `2k × 2k` real `y`-block Jacobian is
the realification (`realifyMatrix`) of the `k × k` complex affine Jacobian of the chart-`j₀`
dehomogenized system.  Its invertibility follows from `isUnit_det_realifyMatrix` together with the
rank-`k` non-singularity condition (via `rank_eq_iff_det_submatrix_succAbove_ne_zero` and the Euler
relation `projJacobian_col_mem_span_of_common_zero`).
-/

namespace Azurite.BPR.Chapter4

open Azurite.BPR (IsSFunction IsSemialgContinuousOn HasPartialDerivAtIn)

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] {k : ℕ}

/-! ### Cauchy–Riemann at the polynomial level -/

set_option linter.unusedSectionVars false in
/-- **The polynomial-level Cauchy–Riemann lemma.** For a complex polynomial `ψ` in `m` variables, the
real/imaginary parts of `z ↦ aeval (realEquiv.symm z) ψ` are real polynomials `Qre, Qim` (as in
`exists_reL_imL_aeval`) whose partial derivatives with respect to the real (`castAdd`) and imaginary
(`natAdd`) coordinate of the `b`-th complex variable realize the complex derivative `pderiv b ψ`:
`∂Qre/∂(Re y_b) = Re(∂ψ/∂y_b)`, `∂Qim/∂(Re y_b) = Im(∂ψ/∂y_b)`,
`∂Qre/∂(Im y_b) = −Im(∂ψ/∂y_b)`, `∂Qim/∂(Im y_b) = Re(∂ψ/∂y_b)`. -/
theorem exists_reL_imL_aeval_cauchyRiemann {m : ℕ} (ψ : MvPolynomial (Fin m) (Ri R)) :
    ∃ Qre Qim : MvPolynomial (Fin (m + m)) R,
      (∀ w : Fin (m + m) → R,
        Ri.reL (aeval (realEquiv.symm w) ψ) = eval w Qre ∧
        Ri.imL (aeval (realEquiv.symm w) ψ) = eval w Qim) ∧
      (∀ (b : Fin m) (w : Fin (m + m) → R),
        eval w (pderiv (Fin.castAdd m b) Qre)
            = Ri.reL (aeval (realEquiv.symm w) (pderiv b ψ)) ∧
        eval w (pderiv (Fin.castAdd m b) Qim)
            = Ri.imL (aeval (realEquiv.symm w) (pderiv b ψ)) ∧
        eval w (pderiv (Fin.natAdd m b) Qre)
            = -Ri.imL (aeval (realEquiv.symm w) (pderiv b ψ)) ∧
        eval w (pderiv (Fin.natAdd m b) Qim)
            = Ri.reL (aeval (realEquiv.symm w) (pderiv b ψ))) := by
  classical
  induction ψ using MvPolynomial.induction_on with
  | C a =>
    refine ⟨C (Ri.reL a), C (Ri.imL a), fun w => ?_, fun b w => ?_⟩
    · rw [aeval_C, Algebra.algebraMap_self_apply, eval_C, eval_C]; exact ⟨rfl, rfl⟩
    · simp only [pderiv_C, map_zero, neg_zero, and_self]
  | add P' P'' ihP' ihP'' =>
    obtain ⟨Qre', Qim', hev', hdv'⟩ := ihP'
    obtain ⟨Qre'', Qim'', hev'', hdv''⟩ := ihP''
    refine ⟨Qre' + Qre'', Qim' + Qim'', fun w => ?_, fun b w => ?_⟩
    · obtain ⟨hre', him'⟩ := hev' w
      obtain ⟨hre'', him''⟩ := hev'' w
      rw [map_add, eval_add, eval_add, map_add, map_add]
      exact ⟨by rw [hre', hre''], by rw [him', him'']⟩
    · obtain ⟨h1', h2', h3', h4'⟩ := hdv' b w
      obtain ⟨h1'', h2'', h3'', h4''⟩ := hdv'' b w
      simp only [map_add]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [h1', h1'']
      · rw [h2', h2'']
      · rw [h3', h3'']; ring
      · rw [h4', h4'']
  | mul_X P' c ihP' =>
    obtain ⟨Qre', Qim', hev', hdv'⟩ := ihP'
    refine ⟨Qre' * X (Fin.castAdd m c) - Qim' * X (Fin.natAdd m c),
            Qre' * X (Fin.natAdd m c) + Qim' * X (Fin.castAdd m c), fun w => ?_, fun b w => ?_⟩
    · -- evaluation part (same as `exists_reL_imL_aeval`)
      obtain ⟨hre', him'⟩ := hev' w
      rw [map_mul, aeval_X]
      constructor
      · rw [reL_mul, reL_symm_apply, imL_symm_apply, hre', him',
          eval_sub, eval_mul, eval_mul, eval_X, eval_X]
      · rw [imL_mul, reL_symm_apply, imL_symm_apply, hre', him',
          eval_add, eval_mul, eval_mul, eval_X, eval_X]
    · -- derivative part: Cauchy–Riemann commutation through `* X c`
      obtain ⟨h1', h2', h3', h4'⟩ := hdv' b w
      obtain ⟨hre', him'⟩ := hev' w
      -- index distinctness facts
      have hcn : (Fin.castAdd m c : Fin (m + m)) ≠ Fin.natAdd m c := by
        intro h; have := congrArg Fin.val h
        simp only [Fin.val_castAdd, Fin.val_natAdd] at this; omega
      have hnc : (Fin.natAdd m c : Fin (m + m)) ≠ Fin.castAdd m c := hcn.symm
      have hcbcn : (Fin.castAdd m b : Fin (m + m)) ≠ Fin.natAdd m c := by
        intro h; have := congrArg Fin.val h
        simp only [Fin.val_castAdd, Fin.val_natAdd] at this; omega
      have hnbcc : (Fin.natAdd m b : Fin (m + m)) ≠ Fin.castAdd m c := by
        intro h; have := congrArg Fin.val h
        simp only [Fin.val_castAdd, Fin.val_natAdd] at this; omega
      have hccb : b ≠ c → (Fin.castAdd m c : Fin (m + m)) ≠ Fin.castAdd m b :=
        fun hbc h => hbc (Fin.castAdd_injective _ _ h).symm
      have hnnb : b ≠ c → (Fin.natAdd m c : Fin (m + m)) ≠ Fin.natAdd m b :=
        fun hbc h => hbc (Fin.natAdd_injective _ _ h).symm
      -- the complex value/derivative at `w`
      set Y : Ri R := realEquiv.symm w c with hY
      have hYre : Ri.reL Y = w (Fin.castAdd m c) := by rw [hY, reL_symm_apply]
      have hYim : Ri.imL Y = w (Fin.natAdd m c) := by rw [hY, imL_symm_apply]
      -- RHS unfolding: `pderiv b (P' * X c) = pderiv b P' * X c + P' * (δ b c)`
      have hRHS : aeval (realEquiv.symm w) (pderiv b (P' * X c))
          = aeval (realEquiv.symm w) (pderiv b P') * Y
            + (if b = c then aeval (realEquiv.symm w) P' else 0) := by
        rw [pderiv_mul, map_add, map_mul, aeval_X, ← hY, map_mul]
        by_cases hbc : b = c
        · subst hbc; rw [pderiv_X_self, ite_eq_left rfl, map_one, mul_one]
        · rw [pderiv_X_of_ne (fun h => hbc h.symm), map_zero, mul_zero, add_zero,
            ite_eq_right hbc, add_zero]
      -- the four LHS partial-derivative evaluations, expanded via `pderiv_mul`
      have eL1 : (eval w) (pderiv (Fin.castAdd m b)
            (Qre' * X (Fin.castAdd m c) - Qim' * X (Fin.natAdd m c)))
          = Ri.reL (aeval (realEquiv.symm w) (pderiv b P')) * w (Fin.castAdd m c)
            - Ri.imL (aeval (realEquiv.symm w) (pderiv b P')) * w (Fin.natAdd m c)
            + (if b = c then eval w Qre' else 0) := by
        rw [map_sub, pderiv_mul, pderiv_mul, pderiv_X_of_ne hcbcn.symm, mul_zero, add_zero,
          eval_sub, eval_add, eval_mul, eval_mul, eval_mul, eval_X, eval_X, h1', h2']
        by_cases hbc : b = c
        · subst hbc; rw [pderiv_X_self, map_one, ite_eq_left rfl]; ring
        · rw [pderiv_X_of_ne (hccb hbc), map_zero, mul_zero,
            add_zero, ite_eq_right hbc]; ring
      have eL2 : (eval w) (pderiv (Fin.castAdd m b)
            (Qre' * X (Fin.natAdd m c) + Qim' * X (Fin.castAdd m c)))
          = Ri.reL (aeval (realEquiv.symm w) (pderiv b P')) * w (Fin.natAdd m c)
            + Ri.imL (aeval (realEquiv.symm w) (pderiv b P')) * w (Fin.castAdd m c)
            + (if b = c then eval w Qim' else 0) := by
        rw [map_add, pderiv_mul, pderiv_mul, pderiv_X_of_ne hcbcn.symm, mul_zero, add_zero,
          eval_add, eval_add, eval_mul, eval_mul, eval_mul, eval_X, eval_X, h1', h2']
        by_cases hbc : b = c
        · subst hbc; rw [pderiv_X_self, map_one, ite_eq_left rfl]; ring
        · rw [pderiv_X_of_ne (hccb hbc), map_zero, mul_zero,
            add_zero, ite_eq_right hbc]; ring
      have eL3 : (eval w) (pderiv (Fin.natAdd m b)
            (Qre' * X (Fin.castAdd m c) - Qim' * X (Fin.natAdd m c)))
          = -Ri.imL (aeval (realEquiv.symm w) (pderiv b P')) * w (Fin.castAdd m c)
            - Ri.reL (aeval (realEquiv.symm w) (pderiv b P')) * w (Fin.natAdd m c)
            - (if b = c then eval w Qim' else 0) := by
        rw [map_sub, pderiv_mul, pderiv_mul, pderiv_X_of_ne hnbcc.symm, mul_zero, add_zero,
          eval_sub, eval_add, eval_mul, eval_mul, eval_mul, eval_X, eval_X, h3', h4']
        by_cases hbc : b = c
        · subst hbc; rw [pderiv_X_self, map_one, ite_eq_left rfl]; ring
        · rw [pderiv_X_of_ne (hnnb hbc), map_zero, mul_zero,
            add_zero, ite_eq_right hbc]; ring
      have eL4 : (eval w) (pderiv (Fin.natAdd m b)
            (Qre' * X (Fin.natAdd m c) + Qim' * X (Fin.castAdd m c)))
          = -Ri.imL (aeval (realEquiv.symm w) (pderiv b P')) * w (Fin.natAdd m c)
            + Ri.reL (aeval (realEquiv.symm w) (pderiv b P')) * w (Fin.castAdd m c)
            + (if b = c then eval w Qre' else 0) := by
        rw [map_add, pderiv_mul, pderiv_mul, pderiv_X_of_ne hnbcc.symm, mul_zero, add_zero,
          eval_add, eval_add, eval_mul, eval_mul, eval_mul, eval_X, eval_X, h3', h4']
        by_cases hbc : b = c
        · subst hbc; rw [pderiv_X_self, map_one, ite_eq_left rfl]; ring
        · rw [pderiv_X_of_ne (hnnb hbc), map_zero, mul_zero,
            add_zero, ite_eq_right hbc]; ring
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [eL1, hRHS, map_add, reL_mul, hYre, hYim]
        split_ifs with hbc
        · linear_combination -hre'
        · rw [map_zero]
      · rw [eL2, hRHS, map_add, imL_mul, hYre, hYim]
        split_ifs with hbc
        · linear_combination -him'
        · rw [map_zero]
      · rw [eL3, hRHS, map_add, imL_mul, hYre, hYim]
        split_ifs with hbc
        · linear_combination him'
        · rw [map_zero]; ring
      · rw [eL4, hRHS, map_add, reL_mul, hYre, hYim]
        split_ifs with hbc
        · linear_combination -hre'
        · rw [map_zero]; ring

/-! ### Chart-`j₀` chain rule and the affine Jacobian -/

set_option linter.unusedSectionVars false in
/-- **Chain rule for the chart-`j₀` dehomogenizing substitution.** Differentiating the chart-`j₀`
dehomogenization (substitute `1` at `j₀`, the other variables as the affine coordinates via
`succAbove`) in the affine variable `a` equals dehomogenizing the partial derivative in
`X_{j₀.succAbove a}`. -/
theorem pderiv_dehomAt (j₀ : Fin (k + 1)) (p : MvPolynomial (Fin (k + 1)) (Ri R)) (a : Fin k) :
    pderiv a (dehomAt j₀ p)
      = dehomAt j₀ (pderiv (j₀.succAbove a) p) := by
  classical
  unfold dehomAt
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j h =>
    simp only [map_mul, Derivation.leibniz, pderiv_X, smul_eq_mul, map_add, aeval_X, h]
    refine Fin.succAboveCases j₀ ?_ (fun b => ?_) j
    · simp [Fin.insertNth_apply_same, (Fin.succAbove_ne j₀ a).symm]
    · simp only [Fin.insertNth_apply_succAbove, pderiv_X]
      by_cases hab : a = b <;> simp [hab, (Fin.succAbove_right_injective (p := j₀)).eq_iff]

set_option linter.unusedSectionVars false in
/-- Evaluating the chart-`j₀` dehomogenization at `v` equals evaluating the original at
`insertNth j₀ 1 v`. -/
theorem aeval_dehomAt (j₀ : Fin (k + 1)) (p : MvPolynomial (Fin (k + 1)) (Ri R)) (v : Fin k → Ri R) :
    aeval v (dehomAt j₀ p) = aeval (Fin.insertNth j₀ (1 : Ri R) v) p :=
  (aeval_insertNth_one j₀ p v).symm

set_option linter.unusedSectionVars false in
/-- **The affine Jacobian determinant is a unit at a non-singular projective zero (any chart `j₀`).**
The `k × k` complex Jacobian of the chart-`j₀` dehomogenized system `Pᵢ(…, 1, …)` at the affine
coordinates `chartInv j₀ x₀` has unit determinant whenever `x₀` is a non-singular projective zero of
the homogeneous `P₁, …, P_k` lying in the chart `𝒰_{j₀}`. -/
theorem isUnit_det_jacobian_dehomAt
    (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (hP : ∀ i, (P i).IsHomogeneous (d i)) (j₀ : Fin (k + 1))
    (x₀ : complexProjectiveSpace R k) (hx₀ : x₀ ∈ chartSet j₀)
    (hns : IsNonsingularProjectiveZero P x₀) :
    IsUnit (jacobian (fun i => dehomAt j₀ (P i)) (chartInv j₀ x₀)).det := by
  classical
  obtain ⟨hzero, hrank⟩ := hns
  have hxj : x₀.rep j₀ ≠ 0 := by rw [chartSet_eq] at hx₀; exact hx₀
  -- the submatrix dropping column `j₀` of the projective Jacobian has nonzero determinant
  have hcol := projJacobian_col_mem_span_of_common_zero hP hzero j₀ hxj
  have hdetne : ((projJacobian P x₀).submatrix id j₀.succAbove).det ≠ 0 :=
    (rank_eq_iff_det_submatrix_succAbove_ne_zero (projJacobian P x₀) j₀ hcol).mp hrank
  -- `x₀.rep = c • insertNth j₀ 1 (chartInv j₀ x₀)` with `c ≠ 0`
  obtain ⟨c, hc, hrep⟩ :
      ∃ c : Ri R, c ≠ 0 ∧ x₀.rep = c • Fin.insertNth j₀ (1 : Ri R) (chartInv j₀ x₀) := by
    have h1 : mkLine x₀.rep x₀.rep_nonzero
        = mkLine (Fin.insertNth j₀ (1 : Ri R) (chartInv j₀ x₀)) (insertNth_one_ne_zero j₀ _) := by
      rw [mkLine_rep]
      conv_lhs => rw [← chartMap_chartInv j₀ x₀ hxj]
      rw [chartMap]
    exact (mkLine_eq_mkLine_iff _ _ _ _).mp h1
  set v : Fin (k + 1) → Ri R := Fin.insertNth j₀ (1 : Ri R) (chartInv j₀ x₀) with hv
  -- the affine Jacobian equals the column-dropped projective Jacobian at `v`, up to row scaling
  -- `Jaff i a = aeval v (pderiv (j₀.succAbove a) (P i))`
  have hJaff : jacobian (fun i => dehomAt j₀ (P i)) (chartInv j₀ x₀)
      = Matrix.of fun i a => aeval v (pderiv (j₀.succAbove a) (P i)) := by
    ext i a
    rw [jacobian, Matrix.of_apply, Matrix.of_apply, pderiv_dehomAt, aeval_dehomAt, hv]
  -- the column-dropped projective Jacobian at `x₀.rep` is rows of `Jaff` scaled by `c ^ (dᵢ - 1)`
  have hproj : (projJacobian P x₀).submatrix id j₀.succAbove
      = Matrix.diagonal (fun i => c ^ (d i - 1))
          * Matrix.of fun i a => aeval v (pderiv (j₀.succAbove a) (P i)) := by
    ext i a
    rw [Matrix.diagonal_mul, Matrix.submatrix_apply, id_eq, projJacobian, Matrix.of_apply,
      Matrix.of_apply, hrep, aeval_smul_isHomogeneous ((hP i).pderiv)]
  rw [hJaff]
  -- transfer non-vanishing of the determinant through the diagonal row-scaling
  rw [hproj, Matrix.det_mul, Matrix.det_diagonal] at hdetne
  exact isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul hdetne)

/-! ### Point-block Cauchy–Riemann for the real homotopy equations -/

/-- A complex-valued function `f` of the full real coordinate vector *has point-block re/im
polynomials with complex gradient `df`* if its real/imaginary parts are real polynomials whose
partial derivatives with respect to the real (`castAdd`) and imaginary (`natAdd`) coordinate of the
`b`-th *point* variable (the `natAdd (1+1)` block) realize `df b` according to Cauchy–Riemann.  This
is the engine that identifies the `y`-block real Jacobian of the realified homotopy system with the
realification of the complex affine Jacobian. -/
def HasPtReImCR (f : (Fin ((1 + 1) + (k + k)) → R) → Ri R)
    (df : Fin k → (Fin ((1 + 1) + (k + k)) → R) → Ri R) : Prop :=
  ∃ Qre Qim : MvPolynomial (Fin ((1 + 1) + (k + k))) R,
    (∀ z, Ri.reL (f z) = eval z Qre ∧ Ri.imL (f z) = eval z Qim) ∧
    (∀ (b : Fin k) (z : Fin ((1 + 1) + (k + k)) → R),
      eval z (pderiv (Fin.natAdd (1 + 1) (Fin.castAdd k b)) Qre) = Ri.reL (df b z) ∧
      eval z (pderiv (Fin.natAdd (1 + 1) (Fin.castAdd k b)) Qim) = Ri.imL (df b z) ∧
      eval z (pderiv (Fin.natAdd (1 + 1) (Fin.natAdd k b)) Qre) = -Ri.imL (df b z) ∧
      eval z (pderiv (Fin.natAdd (1 + 1) (Fin.natAdd k b)) Qim) = Ri.reL (df b z))

set_option linter.unusedSectionVars false in
/-- A complex constant has point-block re/im polynomials with zero gradient. -/
theorem hasPtReImCR_const (c : Ri R) :
    HasPtReImCR (fun _ : Fin ((1 + 1) + (k + k)) → R => c) (fun _ _ => 0) := by
  refine ⟨C (Ri.reL c), C (Ri.imL c), fun _ => ⟨by rw [eval_C], by rw [eval_C]⟩, fun b z => ?_⟩
  simp only [pderiv_C, map_zero, neg_zero, and_self]

set_option linter.unusedSectionVars false in
/-- Point-block re/im polynomials are closed under addition (gradients add). -/
theorem HasPtReImCR.add {f g : (Fin ((1 + 1) + (k + k)) → R) → Ri R} {df dg}
    (hf : HasPtReImCR f df) (hg : HasPtReImCR g dg) :
    HasPtReImCR (fun z => f z + g z) (fun b z => df b z + dg b z) := by
  obtain ⟨fre, fim, hfev, hfdv⟩ := hf
  obtain ⟨gre, gim, hgev, hgdv⟩ := hg
  refine ⟨fre + gre, fim + gim, fun z => ?_, fun b z => ?_⟩
  · simp only [map_add, (hfev z).1, (hfev z).2, (hgev z).1, (hgev z).2, and_self]
  · obtain ⟨e1, e2, e3, e4⟩ := hfdv b z
    obtain ⟨f1, f2, f3, f4⟩ := hgdv b z
    simp only [map_add]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [e1, f1]
    · rw [e2, f2]
    · rw [e3, f3]; ring
    · rw [e4, f4]

set_option linter.unusedSectionVars false in
/-- Point-block re/im polynomials are closed under multiplication (Leibniz rule for gradients). -/
theorem HasPtReImCR.mul {f g : (Fin ((1 + 1) + (k + k)) → R) → Ri R} {df dg}
    (hf : HasPtReImCR f df) (hg : HasPtReImCR g dg) :
    HasPtReImCR (fun z => f z * g z) (fun b z => df b z * g z + f z * dg b z) := by
  obtain ⟨fre, fim, hfev, hfdv⟩ := hf
  obtain ⟨gre, gim, hgev, hgdv⟩ := hg
  refine ⟨fre * gre - fim * gim, fre * gim + fim * gre, fun z => ?_, fun b z => ?_⟩
  · obtain ⟨hfre, hfim⟩ := hfev z
    obtain ⟨hgre, hgim⟩ := hgev z
    refine ⟨show Ri.reL (f z * g z) = _ from ?_, show Ri.imL (f z * g z) = _ from ?_⟩
    · rw [reL_mul, eval_sub, eval_mul, eval_mul, hfre, hfim, hgre, hgim]
    · rw [imL_mul, eval_add, eval_mul, eval_mul, hfre, hfim, hgre, hgim]
  · obtain ⟨hfre, hfim⟩ := hfev z
    obtain ⟨hgre, hgim⟩ := hgev z
    obtain ⟨e1, e2, e3, e4⟩ := hfdv b z
    obtain ⟨g1, g2, g3, g4⟩ := hgdv b z
    have hRre : Ri.reL (df b z * g z + f z * dg b z)
        = Ri.reL (df b z) * Ri.reL (g z) - Ri.imL (df b z) * Ri.imL (g z)
          + (Ri.reL (f z) * Ri.reL (dg b z) - Ri.imL (f z) * Ri.imL (dg b z)) := by
      rw [map_add, reL_mul, reL_mul]
    have hRim : Ri.imL (df b z * g z + f z * dg b z)
        = Ri.reL (df b z) * Ri.imL (g z) + Ri.imL (df b z) * Ri.reL (g z)
          + (Ri.reL (f z) * Ri.imL (dg b z) + Ri.imL (f z) * Ri.reL (dg b z)) := by
      rw [map_add, imL_mul, imL_mul]
    refine ⟨show _ = Ri.reL (df b z * g z + f z * dg b z) from ?_,
            show _ = Ri.imL (df b z * g z + f z * dg b z) from ?_,
            show _ = -Ri.imL (df b z * g z + f z * dg b z) from ?_,
            show _ = Ri.reL (df b z * g z + f z * dg b z) from ?_⟩
    · rw [hRre, map_sub, pderiv_mul, pderiv_mul, eval_sub, eval_add, eval_add,
        eval_mul, eval_mul, eval_mul, eval_mul, e1, e2, g1, g2, ← hfre, ← hfim, ← hgre, ← hgim]
      ring
    · rw [hRim, map_add, pderiv_mul, pderiv_mul, eval_add, eval_add, eval_add,
        eval_mul, eval_mul, eval_mul, eval_mul, e1, e2, g1, g2, ← hfre, ← hfim, ← hgre, ← hgim]
      ring
    · rw [hRim, map_sub, pderiv_mul, pderiv_mul, eval_sub, eval_add, eval_add,
        eval_mul, eval_mul, eval_mul, eval_mul, e3, e4, g3, g4, ← hfre, ← hfim, ← hgre, ← hgim]
      ring
    · rw [hRre, map_add, pderiv_mul, pderiv_mul, eval_add, eval_add, eval_add,
        eval_mul, eval_mul, eval_mul, eval_mul, e3, e4, g3, g4, ← hfre, ← hfim, ← hgre, ← hgim]
      ring

set_option linter.unusedSectionVars false in
/-- **Base case: a complex polynomial of the point block.** For a fixed complex polynomial `φ` in the
`k + 1` homogeneous variables, `z ↦ aeval (xcoordsR j₀ z) φ` has point-block re/im polynomials whose
complex gradient in the `b`-th point variable is `aeval (xcoordsR j₀ z) (pderiv (j₀.succAbove b) φ)`
— i.e. the dehomogenized complex derivative. -/
theorem hasPtReImCR_aeval_xcoordsR (j₀ : Fin (k + 1)) (φ : MvPolynomial (Fin (k + 1)) (Ri R)) :
    HasPtReImCR (fun z : Fin ((1 + 1) + (k + k)) → R => aeval (xcoordsR j₀ z) φ)
      (fun b z => aeval (xcoordsR j₀ z) (pderiv (j₀.succAbove b) φ)) := by
  obtain ⟨Qre, Qim, hev, hdv⟩ := exists_reL_imL_aeval_cauchyRiemann (dehomAt j₀ φ)
  refine ⟨rename (Fin.natAdd (1 + 1)) Qre, rename (Fin.natAdd (1 + 1)) Qim, fun z => ?_,
    fun b z => ?_⟩
  · -- evaluation: reduce through `xcoordsR = insertNth j₀ 1 (realEquiv.symm (point block))`
    have hxc : aeval (xcoordsR j₀ z) φ
        = aeval (realEquiv.symm (z ∘ Fin.natAdd (1 + 1))) (dehomAt j₀ φ) := by
      rw [xcoordsR, aeval_insertNth_one]
    show Ri.reL (aeval (xcoordsR j₀ z) φ) = _ ∧ Ri.imL (aeval (xcoordsR j₀ z) φ) = _
    rw [hxc, eval_rename, eval_rename]
    exact hev (z ∘ Fin.natAdd (1 + 1))
  · -- gradient: `pderiv` through the rename, plus the chain rule `pderiv_dehomAt`
    have hxc : aeval (xcoordsR j₀ z) (pderiv (j₀.succAbove b) φ)
        = aeval (realEquiv.symm (z ∘ Fin.natAdd (1 + 1))) (pderiv b (dehomAt j₀ φ)) := by
      rw [pderiv_dehomAt, xcoordsR, aeval_insertNth_one]
    obtain ⟨d1, d2, d3, d4⟩ := hdv b (z ∘ Fin.natAdd (1 + 1))
    have hg : (fun b z => aeval (xcoordsR j₀ z) (pderiv (j₀.succAbove b) φ)) b z
        = aeval (realEquiv.symm (z ∘ Fin.natAdd (1 + 1))) (pderiv b (dehomAt j₀ φ)) := hxc
    rw [hg]
    have hinj : Function.Injective (Fin.natAdd (1 + 1) : Fin (k + k) → Fin ((1 + 1) + (k + k))) :=
      Fin.natAdd_injective (k + k) (1 + 1)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [pderiv_rename hinj, eval_rename]; exact d1
    · rw [pderiv_rename hinj, eval_rename]; exact d2
    · rw [pderiv_rename hinj, eval_rename]; exact d3
    · rw [pderiv_rename hinj, eval_rename]; exact d4

set_option linter.unusedSectionVars false in
/-- **Base case: a parameter coordinate.** `pcoordsR i₀ z a` depends only on the parameter block of
`z` (the `castAdd (k + k)` block), hence has zero gradient in the point variables. -/
theorem hasPtReImCR_pcoordsR (i₀ : Fin 2) (a : Fin 2) :
    HasPtReImCR (fun z : Fin ((1 + 1) + (k + k)) → R => pcoordsR i₀ z a) (fun _ _ => 0) := by
  classical
  -- index distinctness: `castAdd (k+k) c ≠ natAdd (1+1) (castAdd/natAdd b)` (parameter vs point)
  have hpd1 : ∀ (c : Fin (1 + 1)) (b : Fin k),
      (Fin.natAdd (1 + 1) (Fin.castAdd k b) : Fin ((1 + 1) + (k + k)))
        ≠ Fin.castAdd (k + k) c := by
    intro c b h; have := congrArg Fin.val h
    simp only [Fin.val_natAdd, Fin.val_castAdd] at this; omega
  have hpd2 : ∀ (c : Fin (1 + 1)) (b : Fin k),
      (Fin.natAdd (1 + 1) (Fin.natAdd k b) : Fin ((1 + 1) + (k + k)))
        ≠ Fin.castAdd (k + k) c := by
    intro c b h; have := congrArg Fin.val h
    simp only [Fin.val_natAdd, Fin.val_castAdd] at this; omega
  by_cases ha : a = i₀
  · subst ha
    have hconst : (fun z : Fin ((1 + 1) + (k + k)) → R => pcoordsR a z a)
        = fun _ => (1 : Ri R) := by
      funext z; rw [pcoordsR, Fin.insertNth_apply_same]
    rw [hconst]; exact hasPtReImCR_const 1
  · obtain ⟨c0, hc0⟩ : ∃ c : Fin 1, i₀.succAbove c = a := Fin.exists_succAbove_eq ha
    refine ⟨X (Fin.castAdd (k + k) (Fin.castAdd 1 c0)),
            X (Fin.castAdd (k + k) (Fin.natAdd 1 c0)), fun z => ?_, fun b z => ?_⟩
    · have hval : pcoordsR i₀ z a = (realEquiv.symm (z ∘ Fin.castAdd (k + k))) c0 := by
        rw [pcoordsR, ← hc0, Fin.insertNth_apply_succAbove]
      refine ⟨show Ri.reL (pcoordsR i₀ z a) = _ from ?_, show Ri.imL (pcoordsR i₀ z a) = _ from ?_⟩
      · rw [hval, reL_symm_apply, eval_X, Function.comp_apply]
      · rw [hval, imL_symm_apply, eval_X, Function.comp_apply]
    · have z1 : ∀ c : Fin (1 + 1), pderiv (Fin.natAdd (1 + 1) (Fin.castAdd k b))
          (X (Fin.castAdd (k + k) c) : MvPolynomial (Fin ((1 + 1) + (k + k))) R) = 0 :=
        fun c => pderiv_X_of_ne (hpd1 c b).symm
      have z2 : ∀ c : Fin (1 + 1), pderiv (Fin.natAdd (1 + 1) (Fin.natAdd k b))
          (X (Fin.castAdd (k + k) c) : MvPolynomial (Fin ((1 + 1) + (k + k))) R) = 0 :=
        fun c => pderiv_X_of_ne (hpd2 c b).symm
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [z1 (Fin.castAdd 1 c0), map_zero, map_zero]
      · rw [z1 (Fin.natAdd 1 c0), map_zero, map_zero]
      · rw [z2 (Fin.castAdd 1 c0), map_zero, map_zero, neg_zero]
      · rw [z2 (Fin.natAdd 1 c0), map_zero, map_zero]

set_option linter.unusedSectionVars false in
/-- **The complex homotopy equation has point-block re/im polynomials.** Its complex gradient in the
`b`-th point variable is the dehomogenized complex derivative `aeval (xcoordsR j₀ z) (pderiv
(j₀.succAbove b) (homotopyPoly …))`. -/
theorem hasPtReImCR_cEq (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (i₀ : Fin 2) (j₀ : Fin (k + 1)) (i : Fin k) :
    HasPtReImCR (fun z => cEq P d i₀ j₀ i z)
      (fun b z => aeval (xcoordsR j₀ z)
        (pderiv (j₀.succAbove b)
          (homotopyPoly P d (pcoordsR i₀ z 0) (pcoordsR i₀ z 1) i))) := by
  -- `cEq i = pcoords 0 · aeval (P i) + pcoords 1 · aeval (diagFactor i)` (linear in the parameter)
  have hsplit : (fun z => cEq P d i₀ j₀ i z)
      = fun z => pcoordsR i₀ z 0 * aeval (xcoordsR j₀ z) (P i)
          + pcoordsR i₀ z 1 * aeval (xcoordsR j₀ z) (diagFactor (R := R) (d i) i) := by
    funext z
    show aeval (xcoordsR j₀ z) (homotopyPoly P d (pcoordsR i₀ z 0) (pcoordsR i₀ z 1) i) = _
    rw [homotopyPoly, map_add, map_mul, map_mul, aeval_C, aeval_C,
      Algebra.algebraMap_self_apply, Algebra.algebraMap_self_apply]
  have hcr := (((hasPtReImCR_pcoordsR i₀ 0).mul (hasPtReImCR_aeval_xcoordsR j₀ (P i))).add
    ((hasPtReImCR_pcoordsR i₀ 1).mul
      (hasPtReImCR_aeval_xcoordsR j₀ (diagFactor (R := R) (d i) i))))
  -- the assembled gradient simplifies to the dehomogenized derivative of `homotopyPoly`
  have hgrad : (fun b z => (0 : Ri R) * aeval (xcoordsR j₀ z) (P i)
        + pcoordsR i₀ z 0 * aeval (xcoordsR j₀ z) (pderiv (j₀.succAbove b) (P i))
      + ((0 : Ri R) * aeval (xcoordsR j₀ z) (diagFactor (R := R) (d i) i)
        + pcoordsR i₀ z 1 *
          aeval (xcoordsR j₀ z) (pderiv (j₀.succAbove b) (diagFactor (R := R) (d i) i))))
      = fun b z => aeval (xcoordsR j₀ z)
          (pderiv (j₀.succAbove b)
            (homotopyPoly P d (pcoordsR i₀ z 0) (pcoordsR i₀ z 1) i)) := by
    funext b z
    rw [homotopyPoly, map_add, pderiv_C_mul, pderiv_C_mul, map_add, map_mul, map_mul, aeval_C,
      aeval_C, Algebra.algebraMap_self_apply, Algebra.algebraMap_self_apply]
    ring
  rw [hsplit, ← hgrad]
  exact hcr

/-! ### The `hdet` matrix is the realification of the complex affine Jacobian -/

set_option linter.unusedSectionVars false in
/-- The chosen representing polynomial `homotopyQ` coincides with the point-block re/im polynomial of
the homotopy equation (they agree at every point, hence are equal over the infinite field `R`). -/
theorem homotopyQ_eq_of_hasPtReImCR (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (i₀ : Fin 2) (j₀ : Fin (k + 1)) (l' : Fin k) {Qre Qim : MvPolynomial (Fin ((1 + 1) + (k + k))) R}
    (h : ∀ z, Ri.reL (cEq P d i₀ j₀ l' z) = eval z Qre ∧ Ri.imL (cEq P d i₀ j₀ l' z) = eval z Qim) :
    homotopyQ P d i₀ j₀ (Fin.castAdd k l') = Qre ∧
      homotopyQ P d i₀ j₀ (Fin.natAdd k l') = Qim := by
  constructor
  · refine MvPolynomial.funext fun z => ?_
    rw [← homotopyF_eq_eval_homotopyQ, homotopyF, Fin.addCases_left, (h z).1]
  · refine MvPolynomial.funext fun z => ?_
    rw [← homotopyF_eq_eval_homotopyQ, homotopyF, Fin.addCases_right, (h z).2]

set_option linter.unusedSectionVars false in
/-- **The `y`-block real Jacobian is the realification of the complex affine Jacobian.** The matrix
of point-block partial derivatives `homotopyG … l (natAdd (1+1) j) basepoint` (the `hdet` matrix of
`homotopy_local_ift`) equals `realifyMatrix J`, where `J` is the `k × k` complex Jacobian of the
chart-`j₀` dehomogenized homotopy system at `chartInv j₀ x₀` (with parameters `pcoordsR i₀
basepoint`). -/
theorem homotopyG_matrix_eq_realifyMatrix
    (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (i₀ : Fin 2) (j₀ : Fin (k + 1)) (p₀ : complexProjectiveSpace R 1)
    (x₀ : complexProjectiveSpace R k) :
    (Matrix.of fun l j : Fin (k + k) =>
        homotopyG P d i₀ j₀ l (Fin.natAdd (1 + 1) j)
          (Fin.append (realEquiv (chartInv i₀ p₀)) (realEquiv (chartInv j₀ x₀))))
      = realifyMatrix (Matrix.of fun l' b : Fin k => aeval
          (xcoordsR j₀ (Fin.append (realEquiv (chartInv i₀ p₀)) (realEquiv (chartInv j₀ x₀))))
          (pderiv (j₀.succAbove b)
            (homotopyPoly P d
              (pcoordsR i₀ (Fin.append (realEquiv (chartInv i₀ p₀)) (realEquiv (chartInv j₀ x₀))) 0)
              (pcoordsR i₀ (Fin.append (realEquiv (chartInv i₀ p₀)) (realEquiv (chartInv j₀ x₀))) 1)
              l'))) := by
  classical
  set z₀ : Fin ((1 + 1) + (k + k)) → R :=
    Fin.append (realEquiv (chartInv i₀ p₀)) (realEquiv (chartInv j₀ x₀)) with hz₀
  ext l j
  simp only [Matrix.of_apply, realifyMatrix]
  -- decompose the row `l` and column `j` into re/im blocks
  refine Fin.addCases (fun l' => ?_) (fun l' => ?_) l <;>
    refine Fin.addCases (fun b => ?_) (fun b => ?_) j <;>
    · obtain ⟨Qre, Qim, hev, hdv⟩ := hasPtReImCR_cEq P d i₀ j₀ l'
      obtain ⟨hQre, hQim⟩ := homotopyQ_eq_of_hasPtReImCR P d i₀ j₀ l' hev
      obtain ⟨c1, c2, c3, c4⟩ := hdv b z₀
      simp only [homotopyG, Fin.addCases_left, Fin.addCases_right, hQre, hQim]
      first | rw [c1] | rw [c2] | rw [c3] | rw [c4]

set_option linter.unusedSectionVars false in
/-- Scaling every polynomial of a square system by a fixed nonzero constant `s` preserves the
property of being a non-singular projective zero (the common zero set and the projective Jacobian
rank are both unchanged). -/
theorem isNonsingularProjectiveZero_C_smul
    {Q : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)} {s : Ri R} (hs : s ≠ 0)
    {x : complexProjectiveSpace R k} (h : IsNonsingularProjectiveZero Q x) :
    IsNonsingularProjectiveZero (fun i => C s * Q i) x := by
  obtain ⟨hzero, hrank⟩ := h
  refine ⟨fun i => ?_, ?_⟩
  · rw [map_mul, aeval_C, Algebra.algebraMap_self_apply, hzero i, mul_zero]
  · -- `projJacobian (C s • Q) = C s • projJacobian Q`, so the rank is preserved
    have hjac : projJacobian (fun i => C s * Q i) x
        = Matrix.of fun i j => s * aeval x.rep (pderiv j (Q i)) := by
      ext i j
      rw [projJacobian, Matrix.of_apply, Matrix.of_apply, pderiv_C_mul, map_mul, aeval_C,
        Algebra.algebraMap_self_apply]
    have hsmul : projJacobian (fun i => C s * Q i) x
        = (Matrix.diagonal fun _ : Fin k => s) * projJacobian Q x := by
      rw [hjac]; ext i j
      rw [Matrix.diagonal_mul, projJacobian, Matrix.of_apply, Matrix.of_apply]
    rw [hsmul, Matrix.rank_mul_eq_right_of_isUnit_det, hrank]
    rw [Matrix.det_diagonal]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun _ _ => hs)

/-- **Local implicit function theorem for the homotopy pencil, from non-singularity.** This is
`homotopy_local_ift` with the determinant (transversality) hypothesis `hdet` *derived* from the
intrinsic non-singularity of the projective zero `x₀`.  The realification of the complex affine
Jacobian (`homotopyG_matrix_eq_realifyMatrix`) is invertible by `isUnit_det_realifyMatrix` together
with `isUnit_det_jacobian_dehomAt` (rank-`k` non-singularity, up to the parameter rescaling that
relates `pcoordsR` to `p₀.rep`). -/
theorem homotopy_local_ift' (m : ℕ) (P : Fin k → MvPolynomial (Fin (k + 1)) (Ri R)) (d : Fin k → ℕ)
    (hP : ∀ i, (P i).IsHomogeneous (d i))
    (p₀ : complexProjectiveSpace R 1) (x₀ : complexProjectiveSpace R k)
    (i₀ : Fin 2) (j₀ : Fin (k + 1)) (hp₀ : p₀ ∈ chartSet i₀) (hx₀ : x₀ ∈ chartSet j₀)
    (hzero : ∀ i, aeval x₀.rep (homotopyPoly P d (p₀.rep 0) (p₀.rep 1) i) = 0)
    (hns : IsNonsingularProjectiveZero (homotopyPoly P d (p₀.rep 0) (p₀.rep 1)) x₀) :
    ∃ (U : Set (complexProjectiveSpace R 1)) (V : Set (complexProjectiveSpace R k))
      (ϕ : complexProjectiveSpace R 1 → complexProjectiveSpace R k),
      IsOpen U ∧ p₀ ∈ U ∧ IsOpen V ∧ x₀ ∈ V ∧ ϕ p₀ = x₀ ∧
      IsSClassMapP m U V ϕ ∧
      (∀ p ∈ U, ∀ x ∈ V,
        ((∀ l, homotopyF P d i₀ j₀ l
            (Fin.append (realEquiv (chartInv i₀ p)) (realEquiv (chartInv j₀ x))) = 0)
          ↔ x = ϕ p)) := by
  classical
  set z₀ : Fin ((1 + 1) + (k + k)) → R :=
    Fin.append (realEquiv (chartInv i₀ p₀)) (realEquiv (chartInv j₀ x₀)) with hz₀
  -- the parameter coordinates at the basepoint reconstruct `insertNth i₀ 1 (chartInv i₀ p₀)`
  have hpi : p₀.rep i₀ ≠ 0 := by rw [chartSet_eq] at hp₀; exact hp₀
  have hzparam : z₀ ∘ Fin.castAdd (k + k) = realEquiv (chartInv i₀ p₀) := by
    funext mm; rw [hz₀, Function.comp_apply, Fin.append_left]
  have hpc : pcoordsR i₀ z₀ = Fin.insertNth i₀ (1 : Ri R) (chartInv i₀ p₀) := by
    rw [pcoordsR, hzparam, Equiv.symm_apply_apply]
  -- `p₀.rep = cp • insertNth i₀ 1 (chartInv i₀ p₀)` with `cp ≠ 0`
  obtain ⟨cp, hcp, hprep⟩ :
      ∃ c : Ri R, c ≠ 0 ∧ p₀.rep = c • Fin.insertNth i₀ (1 : Ri R) (chartInv i₀ p₀) := by
    have h1 : mkLine p₀.rep p₀.rep_nonzero
        = mkLine (Fin.insertNth i₀ (1 : Ri R) (chartInv i₀ p₀)) (insertNth_one_ne_zero i₀ _) := by
      rw [mkLine_rep]
      conv_lhs => rw [← chartMap_chartInv i₀ p₀ hpi]
      rw [chartMap]
    exact (mkLine_eq_mkLine_iff _ _ _ _).mp h1
  -- hence the basepoint parameters are `cp⁻¹ • p₀.rep`
  have hparam0 : pcoordsR i₀ z₀ 0 = cp⁻¹ * p₀.rep 0 := by
    rw [hpc, hprep, Pi.smul_apply, smul_eq_mul]; field_simp
  have hparam1 : pcoordsR i₀ z₀ 1 = cp⁻¹ * p₀.rep 1 := by
    rw [hpc, hprep, Pi.smul_apply, smul_eq_mul]; field_simp
  -- the homotopy system at the basepoint parameters equals `C cp⁻¹ •` the original
  have hsys : ∀ l', homotopyPoly P d (pcoordsR i₀ z₀ 0) (pcoordsR i₀ z₀ 1) l'
      = C cp⁻¹ * homotopyPoly P d (p₀.rep 0) (p₀.rep 1) l' := by
    intro l'; rw [hparam0, hparam1, homotopyPoly_smul]
  -- non-singularity transports through the scaling
  have hns' : IsNonsingularProjectiveZero
      (fun l' => homotopyPoly P d (pcoordsR i₀ z₀ 0) (pcoordsR i₀ z₀ 1) l') x₀ := by
    have hscale : (fun l' => homotopyPoly P d (pcoordsR i₀ z₀ 0) (pcoordsR i₀ z₀ 1) l')
        = fun l' => C cp⁻¹ * homotopyPoly P d (p₀.rep 0) (p₀.rep 1) l' := funext hsys
    rw [hscale]
    exact isNonsingularProjectiveZero_C_smul (inv_ne_zero hcp) hns
  -- the affine Jacobian determinant is a unit, hence so is its realification
  have hP' : ∀ l', (homotopyPoly P d (pcoordsR i₀ z₀ 0) (pcoordsR i₀ z₀ 1) l').IsHomogeneous (d l') :=
    fun l' => homotopyPoly_isHomogeneous P d hP _ _ l'
  have hJ := isUnit_det_jacobian_dehomAt
    (fun l' => homotopyPoly P d (pcoordsR i₀ z₀ 0) (pcoordsR i₀ z₀ 1) l') d hP' j₀ x₀ hx₀ hns'
  have hdetReal := isUnit_det_realifyMatrix _ hJ
  -- identify the realified Jacobian with the `hdet` matrix and conclude
  have hmatrix := homotopyG_matrix_eq_realifyMatrix P d i₀ j₀ p₀ x₀
  have hJaff : (jacobian (fun l' => dehomAt j₀ (homotopyPoly P d (pcoordsR i₀ z₀ 0)
        (pcoordsR i₀ z₀ 1) l')) (chartInv j₀ x₀))
      = Matrix.of fun l' b : Fin k => aeval (xcoordsR j₀ z₀)
          (pderiv (j₀.succAbove b)
            (homotopyPoly P d (pcoordsR i₀ z₀ 0) (pcoordsR i₀ z₀ 1) l')) := by
    ext l' b
    have hxc : aeval (xcoordsR j₀ z₀) (pderiv (j₀.succAbove b)
          (homotopyPoly P d (pcoordsR i₀ z₀ 0) (pcoordsR i₀ z₀ 1) l'))
        = aeval (chartInv j₀ x₀) (pderiv b (dehomAt j₀
            (homotopyPoly P d (pcoordsR i₀ z₀ 0) (pcoordsR i₀ z₀ 1) l'))) := by
      rw [pderiv_dehomAt]
      have hzpt : z₀ ∘ Fin.natAdd (1 + 1) = realEquiv (chartInv j₀ x₀) := by
        funext mm; rw [hz₀, Function.comp_apply, Fin.append_right]
      rw [xcoordsR, hzpt, Equiv.symm_apply_apply, aeval_insertNth_one, aeval_dehomAt]
    rw [jacobian, Matrix.of_apply, Matrix.of_apply, hxc]
  rw [hJaff] at hJ
  have hdet : IsUnit (Matrix.of fun l j : Fin (k + k) =>
      homotopyG P d i₀ j₀ l (Fin.natAdd (1 + 1) j) z₀).det := by
    rw [hz₀, hmatrix]; exact isUnit_det_realifyMatrix _ hJ
  exact homotopy_local_ift m P d hP p₀ x₀ i₀ j₀ hp₀ hx₀ hzero hdet

end Azurite.BPR.Chapter4
