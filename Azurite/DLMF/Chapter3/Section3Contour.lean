/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section9CauchyJordan
import Azurite.DLMF.Chapter3.Section3

/-!
# DLMF §3.3(i): the contour-integral form of the Lagrange remainder

* 3.3.6: `dlmf_3_3_6`, with `C` a positively oriented simple closed piecewise-`C¹` contour,
  `f` continuous within and on `C` and analytic within `C` (DLMF: `f` analytic on a
  simply-connected domain containing `C`), and `C` enclosing `z` and **all** the nodes
  `z₀, …, z_n` (DLMF omits `z₀`; see `docs/dlmf_errata.md`).

Proof: the partial-fraction expansion `nodal_partialFraction`,
`1/((ζ − z) ω(ζ)) = (1/ω(z))/(ζ − z) + ∑ (ω̃_k/(z_k − z))/(ζ − z_k)` (from the interpolant of
`1/(u − z)`, which is `(ω(z) − ω(u))/(ω(z)(z − u))`), linearity of the contour integral
(`ClosedPiecewiseC1.contourIntegral_finsetSum`) and Cauchy's integral formula at each pole
(`dlmf_1_9_30_jordan`), then the second form of 3.3.1.
-/

open Complex Polynomial Finset Lagrange Set
open scoped Real

namespace Azurite.JordanCurve.ClosedPiecewiseC1

variable {c : ℝ → ℂ} {a b : ℝ} (P : ClosedPiecewiseC1 c a b)

theorem contourIntegral_finsetSum {ι : Type*} (s : Finset ι) {g : ι → ℂ → ℂ}
    (hg : ∀ i ∈ s, ContinuousOn (g i) P.curve) :
    P.contourIntegral (fun z => ∑ i ∈ s, g i z) = ∑ i ∈ s, P.contourIntegral (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [sum_empty]
    have := P.contourIntegral_const_mul 0 (fun _ => 0)
    simpa using this
  | insert i s hi ih =>
    simp only [sum_insert hi]
    rw [P.contourIntegral_add (hg i (mem_insert_self _ _))
      (continuousOn_finsetSum _ fun j hj => hg j (mem_insert_of_mem hj)),
      ih fun j hj => hg j (mem_insert_of_mem hj)]

end Azurite.JordanCurve.ClosedPiecewiseC1

namespace Azurite.DLMF

open Azurite.JordanCurve

/-- The partial-fraction expansion behind 3.3.6: for `ζ` different from `w` and the nodes
`z_k`, with `w` not a node,
`1/((ζ − w) ω_{n+1}(ζ)) = (1/ω_{n+1}(w))/(ζ − w) + ∑ (ω̃_k/(z_k − w))/(ζ − z_k)`. -/
theorem nodal_partialFraction {n : ℕ} (z : Fin (n + 1) → ℂ) (hz : Function.Injective z)
    {w ζ : ℂ} (hw : ∀ k, w ≠ z k) (hζw : ζ ≠ w) (hζ : ∀ k, ζ ≠ z k) :
    1 / ((ζ - w) * (nodal univ z).eval ζ) = 1 / (nodal univ z).eval w * (1 / (ζ - w)) +
      ∑ k, nodalWeight univ z k / (z k - w) * (1 / (ζ - z k)) := by
  set ω := nodal univ z
  have hωw : ω.eval w ≠ 0 := by
    rw [eval_nodal]; exact prod_ne_zero_iff.mpr fun k _ => sub_ne_zero.mpr (hw k)
  have hωζ : ω.eval ζ ≠ 0 := by
    rw [eval_nodal]; exact prod_ne_zero_iff.mpr fun k _ => sub_ne_zero.mpr (hζ k)
  -- `D = (ω(w) − ω)/(X − w)`, a polynomial of degree `≤ n`
  set p := C (ω.eval w) - ω
  have hroot : p.IsRoot w := by simp [p]
  set D := p /ₘ (X - C w)
  have hD : (X - C w) * D = p := mul_divByMonic_eq_iff_isRoot.mpr hroot
  have hDeval : ∀ u, (u - w) * D.eval u = ω.eval w - ω.eval u := fun u => by
    have := congrArg (eval u) hD
    simpa [p] using this
  have hωdeg : ω.natDegree = n + 1 := by
    rw [natDegree_nodal, card_univ, Fintype.card_fin]
  have hDdeg : D.natDegree ≤ n := by
    rw [natDegree_divByMonic _ (monic_X_sub_C w), natDegree_X_sub_C]
    have h := natDegree_sub_le (C (ω.eval w)) ω
    rw [natDegree_C, hωdeg] at h
    change p.natDegree ≤ _ at h
    omega
  set Q := C (1 / ω.eval w) * D
  have hQdeg : Q.natDegree ≤ n := (natDegree_C_mul_le _ _).trans hDdeg
  have hQnode : ∀ k, Q.eval (z k) = 1 / (z k - w) := fun k => by
    have h1 := hDeval (z k)
    rw [eval_nodal_at_node (mem_univ k), sub_zero] at h1
    have hk : z k - w ≠ 0 := sub_ne_zero.mpr (hw k).symm
    simp only [Q, eval_mul, eval_C]
    field_simp
    linear_combination h1
  obtain ⟨-, -, huniq⟩ := lagrange_unique z hz (fun k => 1 / (z k - w))
  have hQ := huniq Q hQdeg hQnode
  have h3 := dlmf_3_3_1_nodal z (fun k => 1 / (z k - w)) hζ
  rw [← hQ] at h3
  have hsum : ∑ k, nodalWeight univ z k / (z k - w) * (1 / (ζ - z k)) =
      ∑ k, nodalWeight univ z k * (1 / (z k - w)) / (ζ - z k) :=
    sum_congr rfl fun k _ => by ring
  have hs2 : ∑ k, nodalWeight univ z k * (1 / (z k - w)) / (ζ - z k) = Q.eval ζ / ω.eval ζ :=
    eq_div_of_mul_eq hωζ (by rw [mul_comm]; exact h3.symm)
  rw [hsum, hs2]
  have hQζ : Q.eval ζ = D.eval ζ / ω.eval w := by simp only [Q, eval_mul, eval_C]; ring
  have h1 := hDeval ζ
  have hζw' : ζ - w ≠ 0 := sub_ne_zero.mpr hζw
  rw [hQζ]
  field_simp
  linear_combination (-1 : ℂ) * h1

variable {c : ℝ → ℂ} {a b : ℝ}

/-- **DLMF 3.3.6**: if `f` is continuous within and on a positively oriented simple closed
contour `C` and analytic within `C`, and `C` encloses `z` and all the nodes `z₀, …, z_n`, then
`R_n(z) = ω_{n+1}(z)/(2πi) ∮_C f(ζ)/((ζ − z) ω_{n+1}(ζ)) dζ`. -/
theorem dlmf_3_3_6 {n : ℕ} (z : Fin (n + 1) → ℂ) (hz : Function.Injective z)
    (P : ClosedPiecewiseC1 c a b) (hJ : IsJordanCurve c a b) (hpos : P.IsPositivelyOriented)
    {f : ℂ → ℂ} (hfc : ContinuousOn f (jordanInterior c a b ∪ c '' Icc a b))
    (hfd : DifferentiableOn ℂ f (jordanInterior c a b)) (hnodes : ∀ k, z k ∈ jordanInterior c a b)
    {w : ℂ} (hw : w ∈ jordanInterior c a b) :
    lagrangeRem z f w = (nodal univ z).eval w / (2 * π * I) *
      contourIntegral (fun ζ => f ζ / ((ζ - w) * (nodal univ z).eval ζ)) c a b := by
  set ω := nodal univ z
  obtain ⟨-, hPev, -⟩ := lagrange_unique z hz (fun k => f (z k))
  by_cases hnode : ∃ j, w = z j
  · obtain ⟨j, rfl⟩ := hnode
    rw [lagrangeRem, hPev j, sub_self, eval_nodal_at_node (mem_univ j), zero_div, zero_mul]
  push Not at hnode
  have hfC : ContinuousOn f P.curve := hfc.mono subset_union_right
  have hcont : ∀ p ∈ jordanInterior c a b, ContinuousOn (fun ζ => f ζ / (ζ - p)) P.curve :=
    fun p hp => hfC.div (continuousOn_id.sub continuousOn_const)
      fun _ hζ => P.sub_ne_zero_of_mem_curve hp.1 hζ
  -- Cauchy's integral formula at each pole
  have hint : ∀ p ∈ jordanInterior c a b,
      P.contourIntegral (fun ζ => f ζ / (ζ - p)) = 2 * π * I * f p := fun p hp => by
    rw [P.contourIntegral_eq (hcont p hp), dlmf_1_9_30_jordan P hJ hpos hfc hfd hp, ← mul_assoc,
      one_div, mul_inv_cancel₀ two_pi_I_ne_zero, one_mul]
  have hωC : ∀ ζ ∈ P.curve, ω.eval ζ ≠ 0 := fun ζ hζ => by
    rw [eval_nodal]
    exact prod_ne_zero_iff.mpr fun k _ => P.sub_ne_zero_of_mem_curve (hnodes k).1 hζ
  have hg : ContinuousOn (fun ζ => f ζ / ((ζ - w) * ω.eval ζ)) P.curve :=
    hfC.div ((continuousOn_id.sub continuousOn_const).mul
      (Polynomial.differentiable _).continuous.continuousOn)
      fun ζ hζ => mul_ne_zero (P.sub_ne_zero_of_mem_curve hw.1 hζ) (hωC ζ hζ)
  -- partial fractions on the contour
  have hpf : EqOn (fun ζ => f ζ / ((ζ - w) * ω.eval ζ))
      (fun ζ => 1 / ω.eval w * (f ζ / (ζ - w)) +
        ∑ k, nodalWeight univ z k / (z k - w) * (f ζ / (ζ - z k))) P.curve := fun ζ hζ => by
    have h := nodal_partialFraction z hz (w := w) (ζ := ζ) hnode
      (sub_ne_zero.mp (P.sub_ne_zero_of_mem_curve hw.1 hζ))
      fun k => sub_ne_zero.mp (P.sub_ne_zero_of_mem_curve (hnodes k).1 hζ)
    simp only
    rw [div_eq_mul_one_div (f ζ), h, mul_add, mul_sum]
    congr 1
    · ring
    · exact sum_congr rfl fun k _ => by ring
  have h1 : ContinuousOn (fun ζ => 1 / ω.eval w * (f ζ / (ζ - w))) P.curve :=
    continuousOn_const.mul (hcont w hw)
  have h2 : ∀ k ∈ Finset.univ, ContinuousOn
      (fun ζ => nodalWeight univ z k / (z k - w) * (f ζ / (ζ - z k))) P.curve :=
    fun k _ => continuousOn_const.mul (hcont _ (hnodes k))
  rw [← P.contourIntegral_eq hg, P.contourIntegral_congr hpf,
    P.contourIntegral_add h1 (continuousOn_finsetSum _ h2), P.contourIntegral_const_mul,
    P.contourIntegral_finsetSum _ h2]
  simp only [P.contourIntegral_const_mul, hint w hw, fun k => hint _ (hnodes k)]
  have hωw : ω.eval w ≠ 0 := by
    rw [eval_nodal]; exact prod_ne_zero_iff.mpr fun k _ => sub_ne_zero.mpr (hnode k)
  rw [lagrangeRem, dlmf_3_3_1_nodal z _ hnode]
  have hsum : ∑ k, nodalWeight univ z k / (z k - w) * (2 * π * I * f (z k)) =
      -(2 * π * I) * ∑ k, nodalWeight univ z k * f (z k) / (w - z k) := by
    rw [mul_sum]
    exact sum_congr rfl fun k _ => by rw [← neg_sub w (z k), div_neg]; ring
  rw [hsum]
  field_simp
  ring

end Azurite.DLMF
