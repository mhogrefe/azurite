/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section3Contour

/-!
# DLMF §3.3(iii): divided differences

Mathlib has no divided differences; `divDiff n z f` is defined here by DLMF's recursion.

* 3.3.34: `divDiff`, `divDiff_succ_seq` (the general step for a sequence `z₀, z₁, …`),
  `dlmf_3_3_34` (the three displayed cases).
* 3.3.35: `dlmf_3_3_35`. Proof: `divDiff_eq_coeff` (`[z₀, …, z_n] f` is the `zⁿ` coefficient of
  the interpolation polynomial `P_n`), by induction with Neville's identity
  `interpolate_neville` and uniqueness of `P_n`; the coefficient is `∑ ω̃_k f_k`
  (`coeff_interpolate`, since `ℓ_k = ω̃_k ∏'_j (z − z_j)`, `coeff_basis_eq_nodalWeight`).
* 3.3.36: `dlmf_3_3_36`, for `f` that is `n` times differentiable on an open set containing the
  smallest closed interval containing the nodes (continuity of `f^{(n)}` is not needed): the
  generalized Rolle theorem for `f − P_n`, whose `n`-th derivative is
  `f^{(n)} − n! [x₀, …, x_n] f` (`iterate_derivative_of_natDegree_le`).
* 3.3.37: `dlmf_3_3_37`, on a positively oriented Jordan contour enclosing the nodes, with `f`
  continuous within and on `C` and analytic within: the partial fractions
  `1/ω_{n+1}(ζ) = ∑ ω̃_k/(ζ − z_k)` (3.3.3_2) and Cauchy's integral formula at each node, then
  3.3.35.
-/

open Polynomial Finset Lagrange
open scoped Real

namespace Azurite.DLMF

/-! ### The definition 3.3.34 -/

section Field

variable {F : Type*} [Field F]

/-- **DLMF 3.3.34**: the divided difference `[z₀, z₁, …, z_n] f`, by
`[z₀] f = f₀` and `[z₀, …, z_{n+1}] f = ([z₁, …, z_{n+1}] f − [z₀, …, z_n] f)/(z_{n+1} − z₀)`. -/
def divDiff : (n : ℕ) → (Fin (n + 1) → F) → (F → F) → F
  | 0, z, f => f (z 0)
  | n + 1, z, f => (divDiff n (fun i => z i.succ) f - divDiff n (fun i => z i.castSucc) f) /
      (z (Fin.last (n + 1)) - z 0)

/-- **DLMF 3.3.34**, the general step, for a sequence `z₀, z₁, z₂, …`. -/
theorem divDiff_succ_seq (n : ℕ) (z : ℕ → F) (f : F → F) :
    divDiff (n + 1) (fun i => z i) f =
      (divDiff n (fun i => z (i + 1)) f - divDiff n (fun i => z i) f) / (z (n + 1) - z 0) := by
  rw [divDiff]
  simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_last, Fin.val_zero]

/-- **DLMF 3.3.34**: `[z₀] f = f₀`, `[z₀, z₁] f = ([z₁] f − [z₀] f)/(z₁ − z₀)`,
`[z₀, z₁, z₂] f = ([z₁, z₂] f − [z₀, z₁] f)/(z₂ − z₀)`. -/
theorem dlmf_3_3_34 (z : ℕ → F) (f : F → F) :
    divDiff 0 (fun i => z i) f = f (z 0) ∧
      divDiff 1 (fun i => z i) f =
        (divDiff 0 (fun i => z (i + 1)) f - divDiff 0 (fun i => z i) f) / (z 1 - z 0) ∧
      divDiff 2 (fun i => z i) f =
        (divDiff 1 (fun i => z (i + 1)) f - divDiff 1 (fun i => z i) f) / (z 2 - z 0) :=
  ⟨rfl, divDiff_succ_seq 0 z f, divDiff_succ_seq 1 z f⟩

/-! ### The explicit form 3.3.35 -/

/-- The `zⁿ` coefficient of `ℓ_k` is `ω̃_k`. -/
theorem coeff_basis_eq_nodalWeight {n : ℕ} (z : Fin (n + 1) → F) (k : Fin (n + 1)) :
    (Lagrange.basis univ z k).coeff n = nodalWeight univ z k := by
  rw [basis_eq_prod_sub_inv_mul_nodal_div (mem_univ k), ← nodal_erase_eq_nodal_div (mem_univ k),
    coeff_C_mul]
  have hd : (nodal (univ.erase k) z).natDegree = n := by
    rw [natDegree_nodal, card_erase_of_mem (mem_univ k), card_univ, Fintype.card_fin,
      Nat.add_sub_cancel]
  have hm := (nodal_monic (s := univ.erase k) (v := z)).coeff_natDegree
  rw [hd] at hm
  rw [hm, mul_one]

/-- The leading (`zⁿ`) coefficient of `P_n` is `∑ ω̃_k f_k`. -/
theorem coeff_interpolate {n : ℕ} (z : Fin (n + 1) → F) (r : Fin (n + 1) → F) :
    (interpolate univ z r).coeff n = ∑ k, r k * nodalWeight univ z k := by
  rw [interpolate_apply, finsetSum_coeff]
  exact sum_congr rfl fun k _ => by rw [coeff_C_mul, coeff_basis_eq_nodalWeight]

/-- Neville's identity:
`P_{z₀…z_{n+1}} = ((x − z₀) P_{z₁…z_{n+1}} − (x − z_{n+1}) P_{z₀…z_n})/(z_{n+1} − z₀)`. -/
theorem interpolate_neville {n : ℕ} (z : Fin (n + 2) → F) (hz : Function.Injective z)
    (f : F → F) :
    interpolate univ z (fun k => f (z k)) =
      C (1 / (z (Fin.last (n + 1)) - z 0)) *
        ((X - C (z 0)) *
            interpolate univ (fun i : Fin (n + 1) => z i.succ) (fun k => f (z k.succ)) -
          (X - C (z (Fin.last (n + 1)))) *
            interpolate univ (fun i : Fin (n + 1) => z i.castSucc)
      (fun k => f (z k.castSucc))) := by
  obtain ⟨hd1, hev1, -⟩ := lagrange_unique (fun i : Fin (n + 1) => z i.succ)
    (fun i j h => Fin.succ_injective _ (hz h)) (fun k => f (z k.succ))
  obtain ⟨hd0, hev0, -⟩ := lagrange_unique (fun i : Fin (n + 1) => z i.castSucc)
    (fun i j h => Fin.castSucc_injective _ (hz h)) (fun k => f (z k.castSucc))
  set Q1 := interpolate univ (fun i : Fin (n + 1) => z i.succ) (fun k => f (z k.succ))
  set Q0 := interpolate univ (fun i : Fin (n + 1) => z i.castSucc)
      (fun k => f (z k.castSucc))
  obtain ⟨-, -, huniq⟩ := lagrange_unique z hz (fun k => f (z k))
  have hne : z (Fin.last (n + 1)) - z 0 ≠ 0 := sub_ne_zero.mpr fun h => by
    have := congrArg Fin.val (hz h); simp at this
  refine (huniq _ ?_ fun k => ?_).symm
  · refine (natDegree_C_mul_le _ _).trans ((natDegree_sub_le _ _).trans (max_le ?_ ?_)) <;>
      refine natDegree_mul_le.trans ?_ <;> rw [natDegree_X_sub_C] <;> omega
  · simp only [eval_mul, eval_C, eval_sub, eval_X]
    induction k using Fin.cases with
    | zero =>
      have h0 := hev0 0
      simp only [Fin.castSucc_zero] at h0
      rw [h0, sub_self, zero_mul, zero_sub]
      field_simp
      ring
    | succ j =>
      rw [hev1 j]
      induction j using Fin.lastCases with
      | last =>
        rw [Fin.succ_last, sub_self, zero_mul, sub_zero]
        field_simp
      | cast j =>
        have h0 := hev0 j.succ
        rw [← Fin.succ_castSucc] at h0
        rw [h0]
        field_simp
        ring

/-- The divided difference is the leading coefficient of the interpolation polynomial. -/
theorem divDiff_eq_coeff : ∀ {n : ℕ} (z : Fin (n + 1) → F), Function.Injective z →
    ∀ f : F → F, divDiff n z f = (interpolate univ z (fun k => f (z k))).coeff n
  | 0, z, hz, f => by
    obtain ⟨-, -, huniq⟩ := lagrange_unique z hz (fun k => f (z k))
    rw [← huniq (C (f (z 0))) (by simp) fun k => by rw [Subsingleton.elim (α := Fin 1) k 0, eval_C]]
    simp [divDiff]
  | n + 1, z, hz, f => by
    rw [divDiff, divDiff_eq_coeff _ (fun i j h => Fin.succ_injective _ (hz h)),
      divDiff_eq_coeff _ (fun i j h => Fin.castSucc_injective _ (hz h)),
      interpolate_neville z hz f, coeff_C_mul, coeff_sub, coeff_X_sub_C_mul, coeff_X_sub_C_mul]
    obtain ⟨hd1, -, -⟩ := lagrange_unique (fun i : Fin (n + 1) => z i.succ)
      (fun i j h => Fin.succ_injective _ (hz h)) (fun k => f (z k.succ))
    obtain ⟨hd0, -, -⟩ := lagrange_unique (fun i : Fin (n + 1) => z i.castSucc)
      (fun i j h => Fin.castSucc_injective _ (hz h)) (fun k => f (z k.castSucc))
    rw [coeff_eq_zero_of_natDegree_lt (by omega : _ < n + 1),
      coeff_eq_zero_of_natDegree_lt (by omega : _ < n + 1)]
    ring

/-- **DLMF 3.3.35**: `[z₀, …, z_n] f = ∑_k f(z_k) / ∏_{j ≠ k} (z_k − z_j)`. -/
theorem dlmf_3_3_35 {n : ℕ} (z : Fin (n + 1) → F) (hz : Function.Injective z) (f : F → F) :
    divDiff n z f = ∑ k, f (z k) / ∏ j ∈ univ.erase k, (z k - z j) := by
  rw [divDiff_eq_coeff z hz, coeff_interpolate]
  exact sum_congr rfl fun k _ => by rw [nodalWeight, prod_inv_distrib, div_eq_mul_inv]

end Field

/-! ### The mean-value form 3.3.36 -/

theorem iterate_derivative_of_natDegree_le {p : ℝ[X]} {n : ℕ} (hp : p.natDegree ≤ n) :
    derivative^[n] p = C ((n.factorial : ℝ) * p.coeff n) := by
  have hdeg : (derivative^[n] p).natDegree = 0 := by
    have := natDegree_iterate_derivative p n
    omega
  rw [eq_C_of_natDegree_eq_zero hdeg, coeff_iterate_derivative, zero_add, Nat.descFactorial_self,
    nsmul_eq_mul]

/-- **DLMF 3.3.36**: for real distinct nodes and `f` that is `n` times differentiable on an open
set containing the smallest closed interval `I` containing the nodes,
`[x₀, …, x_n] f = f^{(n)}(ξ)/n!` for some `ξ ∈ I`. -/
theorem dlmf_3_3_36 {n : ℕ} (x : Fin (n + 1) → ℝ) (hx : Function.Injective x) (f : ℝ → ℝ)
    {U : Set ℝ} (hU : IsOpen U) (hd : ∀ k < n, DifferentiableOn ℝ (iteratedDeriv k f) U)
    (hI : Set.Icc ((univ.image x).min' (univ_nonempty.image x))
      ((univ.image x).max' (univ_nonempty.image x)) ⊆ U) :
    ∃ ξ ∈ Set.Icc ((univ.image x).min' (univ_nonempty.image x))
      ((univ.image x).max' (univ_nonempty.image x)),
      divDiff n x f = iteratedDeriv n f ξ / n.factorial := by
  set s := univ.image x
  obtain ⟨hPdeg, hPev, -⟩ := lagrange_unique x hx (fun k => f (x k))
  set P := interpolate univ x (fun k => f (x k))
  have hcard : s.card = n + 1 := by
    rw [card_image_of_injective _ hx, card_univ, Fintype.card_fin]
  set e := s.orderEmbOfFin hcard
  have he0 : e 0 = s.min' (univ_nonempty.image x) := by
    rw [show (0 : Fin (n + 1)) = ⟨0, by omega⟩ from rfl, orderEmbOfFin_zero hcard (by omega)]
  have hel : e (Fin.last n) = s.max' (univ_nonempty.image x) := by
    rw [show Fin.last n = ⟨n + 1 - 1, by omega⟩ from Fin.ext (by simp),
      orderEmbOfFin_last hcard (by omega)]
  have hEq := iteratedDeriv_sub_poly_eqOn hU P n hd
  have hdg : ∀ k < n, DifferentiableOn ℝ (iteratedDeriv k fun u => f u - P.eval u) U :=
    fun k hk => ((hd k hk).sub (Polynomial.differentiable _).differentiableOn).congr
      (hEq k hk.le)
  have hzero : ∀ i, f (e i) - P.eval (e i) = 0 := fun i => by
    obtain ⟨j, -, hj⟩ := mem_image.mp (orderEmbOfFin_mem s hcard i)
    rw [← hj, hPev j, sub_self]
  obtain ⟨ξ, hξ, hξ0⟩ := exists_iteratedDeriv_eq_zero n (fun u => f u - P.eval u) U hdg e
    e.strictMono (by rw [he0, hel]; exact hI) hzero
  rw [he0, hel] at hξ
  refine ⟨ξ, hξ, ?_⟩
  have h1 := hEq n le_rfl (hI hξ)
  rw [hξ0, iterate_derivative_of_natDegree_le hPdeg] at h1
  simp only [eval_C] at h1
  rw [divDiff_eq_coeff x hx]
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  linarith

/-! ### The contour integral 3.3.37 -/

variable {c : ℝ → ℂ} {a b : ℝ}

open Azurite.JordanCurve Complex in
/-- **DLMF 3.3.37**: if `f` is continuous within and on a positively oriented simple closed
contour `C` and analytic within `C`, and `C` encloses `z₀, …, z_n`, then
`[z₀, …, z_n] f = (1/(2πi)) ∮_C f(ζ)/ω_{n+1}(ζ) dζ`. -/
theorem dlmf_3_3_37 {n : ℕ} (z : Fin (n + 1) → ℂ) (hz : Function.Injective z)
    (P : ClosedPiecewiseC1 c a b) (hJ : IsJordanCurve c a b) (hpos : P.IsPositivelyOriented)
    {f : ℂ → ℂ} (hfc : ContinuousOn f (jordanInterior c a b ∪ c '' Set.Icc a b))
    (hfd : DifferentiableOn ℂ f (jordanInterior c a b))
    (hnodes : ∀ k, z k ∈ jordanInterior c a b) :
    divDiff n z f =
      1 / (2 * π * I) * contourIntegral (fun ζ => f ζ / (nodal univ z).eval ζ) c a b := by
  have hfC : ContinuousOn f P.curve := hfc.mono Set.subset_union_right
  have hcont : ∀ p ∈ jordanInterior c a b, ContinuousOn (fun ζ => f ζ / (ζ - p)) P.curve :=
    fun p hp => hfC.div (continuousOn_id.sub continuousOn_const)
      fun _ hζ => P.sub_ne_zero_of_mem_curve hp.1 hζ
  have hint : ∀ p ∈ jordanInterior c a b,
      P.contourIntegral (fun ζ => f ζ / (ζ - p)) = 2 * π * I * f p := fun p hp => by
    rw [P.contourIntegral_eq (hcont p hp), dlmf_1_9_30_jordan P hJ hpos hfc hfd hp, ← mul_assoc,
      one_div, mul_inv_cancel₀ two_pi_I_ne_zero, one_mul]
  have hωC : ∀ ζ ∈ P.curve, (nodal univ z).eval ζ ≠ 0 := fun ζ hζ => by
    rw [eval_nodal]
    exact prod_ne_zero_iff.mpr fun k _ => P.sub_ne_zero_of_mem_curve (hnodes k).1 hζ
  have hg : ContinuousOn (fun ζ => f ζ / (nodal univ z).eval ζ) P.curve :=
    hfC.div (Polynomial.differentiable _).continuous.continuousOn hωC
  -- partial fractions `1/ω = ∑ ω̃_k/(ζ − z_k)` on the contour
  have hpf : Set.EqOn (fun ζ => f ζ / (nodal univ z).eval ζ)
      (fun ζ => ∑ k, nodalWeight univ z k * (f ζ / (ζ - z k))) P.curve := fun ζ hζ => by
    have hζn : ∀ k, ζ ≠ z k := fun k =>
      sub_ne_zero.mp (P.sub_ne_zero_of_mem_curve (hnodes k).1 hζ)
    have h1 := (dlmf_3_3_3_2 z hz ζ).2 hζn
    simp only
    rw [div_eq_iff (hωC ζ hζ), sum_mul, eq_comm]
    calc ∑ k, nodalWeight univ z k * (f ζ / (ζ - z k)) * (nodal univ z).eval ζ
        = f ζ * ((nodal univ z).eval ζ * ∑ k, nodalWeight univ z k / (ζ - z k)) := by
          rw [mul_sum, mul_sum]; exact sum_congr rfl fun k _ => by ring
      _ = f ζ := by rw [← h1, mul_one]
  have h2 : ∀ k ∈ Finset.univ, ContinuousOn
      (fun ζ => nodalWeight univ z k * (f ζ / (ζ - z k))) P.curve :=
    fun k _ => continuousOn_const.mul (hcont _ (hnodes k))
  rw [← P.contourIntegral_eq hg, P.contourIntegral_congr hpf, P.contourIntegral_finsetSum _ h2]
  simp only [P.contourIntegral_const_mul, fun k => hint _ (hnodes k)]
  rw [divDiff_eq_coeff z hz, coeff_interpolate, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  field_simp [two_pi_I_ne_zero]

end Azurite.DLMF
