/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section5
import Azurite.JordanCurve.Orientation
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# DLMF §1.6: Vectors and Vector-Valued Functions

Formalizations of <https://dlmf.nist.gov/1.6>, one theorem per equation, named `dlmf_1_6_N`;
statements made in the prose are named `dlmf_1_6_i_<topic>`.  Vectors of `ℝ³` are
`a : Fin 3 → ℝ` with components `a 0, a 1, a 2` (DLMF's `a₁, a₂, a₃`); the dot product is
Mathlib's `⬝ᵥ` and the cross product Mathlib's `⨯₃`.  Since the norm Lean puts on `Fin 3 → ℝ` is
the sup norm, the Euclidean magnitude 1.6.3 is `vnorm a = √(a ⬝ᵥ a)`, shown equal to the norm of
`a` in `EuclideanSpace ℝ (Fin 3)`; the angle between vectors is Mathlib's
`InnerProductGeometry.angle` there.

## §1.6(i) Vectors

* 1.6.1 `dlmf_1_6_1`; 1.6.2 `dlmf_1_6_2` (dot product).
* 1.6.3 `vnorm`, `dlmf_1_6_3`; 1.6.4 `vangle`, `dlmf_1_6_4`, `vangle_mem_Icc`.
* 1.6.5 `unitI`, `unitJ`, `unitK`; 1.6.6 `dlmf_1_6_6`.
* 1.6.7 `dlmf_1_6_7`, 1.6.8 `dlmf_1_6_8` (cross products of the unit vectors).
* 1.6.9 `dlmf_1_6_9_det` (the formal determinant, expanded along its first row),
  `dlmf_1_6_9` (components), `dot_cross_self_eq` (Lagrange's identity),
  `vnorm_cross` (`‖a × b‖ = ‖a‖ ‖b‖ sin θ`), `dlmf_1_6_9_normal` (`a × b = ‖a‖ ‖b‖ sin θ n` with
  `n` the unit normal given by the right-hand rule: `det [a, b, n] > 0`).
* `dlmf_1_6_i_area` (area of the parallelogram: base `‖a‖` times height = `‖a × b‖`),
  `dlmf_1_6_i_volume` (Lebesgue volume of the parallelepiped `= |a · (b × c)|`).
* 1.6.10 `dlmf_1_6_10`, 1.6.11 `dlmf_1_6_11` (triple vector products).

## §1.6(ii) Vectors: alternative notations

Einstein's summation convention is written with explicit sums over `Fin 3`.

* 1.6.12 `dlmf_1_6_12`; 1.6.13 `unitE`, `unitE_eq`, `dlmf_1_6_13` (`aⱼ eⱼ = a`).
* 1.6.14 `leviCivita`, `dlmf_1_6_14` (`ε` is the sign of the permutation, `0` otherwise);
  1.6.15 `dlmf_1_6_15`; 1.6.16 `dlmf_1_6_16` (the `εε = δδ − δδ` identity, by `decide`).
* 1.6.17 `dlmf_1_6_17`, 1.6.18 `dlmf_1_6_18` (cross products via `ε`),
  `sum_leviCivita_eq_triple`, `dlmf_1_6_ii_volume` (volume `= |ε_{jkℓ} aⱼ bₖ cℓ|`).

## §1.6(iii) Vector-valued functions

Points are `p : Fin 3 → ℝ`, scalar fields `f : (Fin 3 → ℝ) → ℝ`, vector fields
`F : (Fin 3 → ℝ) → (Fin 3 → ℝ)`; `pd i f p = Df(p) eᵢ` is `∂f/∂xᵢ`.

* 1.6.19 `pd`, `hasDerivAt_pd`, `dlmf_1_6_19` (`pd` is the coordinate partial derivative);
  1.6.20 `grad3`, `dlmf_1_6_20`; 1.6.21 `div3`, `dlmf_1_6_21`; 1.6.22 `curl3`, `dlmf_1_6_22`
  (the formal determinant via the Levi-Civita symbol).
* Product rules `pd_add`, `pd_sub`, `pd_mul`, `pd_div`, `pd_sum`, `pd_mul_fun`.
* First-order identities (differentiable at `p`): 1.6.23 `dlmf_1_6_23`, 1.6.24 `dlmf_1_6_24`,
  1.6.25 `dlmf_1_6_25`, 1.6.26 `dlmf_1_6_26`, 1.6.28 `dlmf_1_6_28`.
* Second-order identities (`C²` fields; `pd_comm` from Mathlib's symmetry of second
  derivatives, `pd_pd_eq`, `contDiff_pd`, `differentiable_pd`): 1.6.27 `dlmf_1_6_27`
  (`div curl = 0`), 1.6.29 `dlmf_1_6_29` (`curl grad = 0`), 1.6.30 `lap3`, `dlmf_1_6_30`,
  1.6.31 `dlmf_1_6_31`, 1.6.32 `dlmf_1_6_32`, 1.6.33 `dlmf_1_6_33`, 1.6.34 `vlap3`,
  `dlmf_1_6_34` (`curl curl F = ∇(∇ · F) − ∇²F`).

## §1.6(iv) Path and line integrals

* 1.6.35 `dlmf_1_6_35`; 1.6.36 `pathLength`, `dlmf_1_6_36` (the length is the total variation:
  supremum of inscribed polygon lengths, via `olver_11_02`); 1.6.37 `pathIntegral`,
  `dlmf_1_6_37`; 1.6.38 `lineIntegral`, `dlmf_1_6_38`.
* Reparametrization: `deriv_comp_reparam`, `lineIntegral_comp`, 1.6.39 `dlmf_1_6_39`, 1.6.40
  `dlmf_1_6_40`, 1.6.41 `dlmf_1_6_41`, `dlmf_1_6_41_antitone`; 1.6.42 `fderiv_apply_eq_grad`,
  `dlmf_1_6_42` (`∫_c ∇f · ds = f(c(b)) − f(c(a))`).
* `IsSimpleClosedPath`, `IsPiecewiseDifferentiablePath`.
* Green's theorem 1.6.43–1.6.44 for rectangles: `lineIntegral2`, `rectBoundaryIntegral`,
  `rectBoundaryIntegral_eq`, `dlmf_1_6_44_rect` (from Mathlib's divergence theorem on boxes),
  `dlmf_1_6_iv_area`.
* Green's theorem 1.6.44 for a region `{a ≤ x ≤ b, φ₁(x) ≤ y ≤ φ₂(x)}` between two `C¹` graphs:
  `lineIntegral2_graph`, `lineIntegral2_vertical`, `regionXBoundaryIntegral`,
  `dlmf_1_6_44_regionX` (Fubini + FTC for the `F₁ dx` part, Leibniz's rule 1.5.22 for the
  `F₂ dy` part), `dlmf_1_6_iv_area_regionX`.
* Green's theorem 1.6.44 for a general closed piecewise-`C¹` curve: `toComplexPath`,
  `IsSimpleClosedPlanePath`, `planeInterior` (the region `S`: union of the bounded components of
  the complement; `planeInterior_eq_image`, `preimage_planeInterior` relate it to
  `JordanCurve.jordanInterior` in `ℂ`), `fderiv_comp_equivRealProd`,
  `lineIntegral2_eq_mul_setIntegral` (winding number a constant `w` on `S`: the line integral is
  `w ∬_S`; from `JordanCurve.ClosedPiecewiseC1.lineIntegralRe_eq_mul_setIntegral_jordanInterior`,
  itself from the Cauchy–Pompeiu formula), `dlmf_1_6_44` (positively oriented, `C¹` fields).
* "Continuously differentiable on `S ∪ ∂S`" read as "on an open `U ⊇ S ∪ C`":
  `isCompact_closure_planeInterior_union`, `exists_contDiff_eqOn_nhds` (smooth cutoff),
  `lineIntegral2_eq_mul_setIntegral_of_contDiffOn`, `dlmf_1_6_44_nhds`.
* Simple closed curves, no orientation hypothesis (the winding number on `S` is `±1`,
  `JordanCurve/Orientation`): `dlmf_1_6_44_simple` (positively oriented and Green's formula, or
  negatively oriented and the formula with a minus sign), `lineIntegral2_reverse`,
  `planeInterior_reverse`, `dlmf_1_6_44_simple_or_reverse` (the curve or its reversal is positively
  oriented); `planeInterior_nonempty_isConnected`, `dlmf_1_6_iv_area_general`.
-/

namespace Azurite.DLMF

open Matrix MeasureTheory

/-- **DLMF 1.6.1**: a vector `a = (a₁, a₂, a₃)`. -/
theorem dlmf_1_6_1 (a : Fin 3 → ℝ) : a = ![a 0, a 1, a 2] := by
  ext i
  fin_cases i <;> rfl

/-- **DLMF 1.6.2**: the dot (scalar) product `a · b = a₁b₁ + a₂b₂ + a₃b₃`. -/
theorem dlmf_1_6_2 (a b : Fin 3 → ℝ) : a ⬝ᵥ b = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
  simp [dotProduct, Fin.sum_univ_three]

/-- **DLMF 1.6.3**: the magnitude `‖a‖ = √(a · a)`. -/
noncomputable def vnorm (a : Fin 3 → ℝ) : ℝ := √(a ⬝ᵥ a)

/-- **DLMF 1.6.3**: `vnorm` is the Euclidean norm. -/
theorem dlmf_1_6_3 (a : Fin 3 → ℝ) :
    vnorm a = ‖(WithLp.toLp 2 a : EuclideanSpace ℝ (Fin 3))‖ := by
  simp [vnorm, EuclideanSpace.norm_eq, dotProduct, sq]

theorem inner_toLp (a b : Fin 3 → ℝ) :
    inner ℝ (WithLp.toLp 2 a : EuclideanSpace ℝ (Fin 3)) (WithLp.toLp 2 b) = a ⬝ᵥ b := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

/-- **DLMF 1.6.4**: the angle `θ` between `a` and `b` (the unoriented angle in `ℝ³`). -/
noncomputable def vangle (a b : Fin 3 → ℝ) : ℝ :=
  InnerProductGeometry.angle (WithLp.toLp 2 a : EuclideanSpace ℝ (Fin 3)) (WithLp.toLp 2 b)

theorem vangle_mem_Icc (a b : Fin 3 → ℝ) : vangle a b ∈ Set.Icc 0 Real.pi :=
  ⟨InnerProductGeometry.angle_nonneg _ _, InnerProductGeometry.angle_le_pi _ _⟩

/-- **DLMF 1.6.4**: `cos θ = a · b / (‖a‖ ‖b‖)`. -/
theorem dlmf_1_6_4 (a b : Fin 3 → ℝ) :
    Real.cos (vangle a b) = a ⬝ᵥ b / (vnorm a * vnorm b) := by
  rw [vangle, InnerProductGeometry.cos_angle, inner_toLp, dlmf_1_6_3, dlmf_1_6_3]

/-- **DLMF 1.6.5**: the unit vectors `i`, `j`, `k`. -/
def unitI : Fin 3 → ℝ := ![1, 0, 0]

@[inherit_doc unitI]
def unitJ : Fin 3 → ℝ := ![0, 1, 0]

@[inherit_doc unitI]
def unitK : Fin 3 → ℝ := ![0, 0, 1]

/-- **DLMF 1.6.6**: `a = a₁ i + a₂ j + a₃ k`. -/
theorem dlmf_1_6_6 (a : Fin 3 → ℝ) : a = a 0 • unitI + a 1 • unitJ + a 2 • unitK := by
  ext i
  fin_cases i <;> simp [unitI, unitJ, unitK]

/-- **DLMF 1.6.7**: `i × j = k`, `j × k = i`, `k × i = j`. -/
theorem dlmf_1_6_7 : unitI ⨯₃ unitJ = unitK ∧ unitJ ⨯₃ unitK = unitI ∧ unitK ⨯₃ unitI = unitJ := by
  refine ⟨?_, ?_, ?_⟩ <;> ext i <;> fin_cases i <;> simp [cross_apply, unitI, unitJ, unitK]

/-- **DLMF 1.6.8**: `j × i = −k`, `k × j = −i`, `i × k = −j`. -/
theorem dlmf_1_6_8 :
    unitJ ⨯₃ unitI = -unitK ∧ unitK ⨯₃ unitJ = -unitI ∧ unitI ⨯₃ unitK = -unitJ := by
  refine ⟨?_, ?_, ?_⟩ <;> ext i <;> fin_cases i <;> simp [cross_apply, unitI, unitJ, unitK]

/-- **DLMF 1.6.9**, the formal determinant `|i j k; a₁ a₂ a₃; b₁ b₂ b₃|` expanded along its first
row: the coefficient of each unit vector `e` is `det [e; a; b]`. -/
theorem dlmf_1_6_9_det (a b : Fin 3 → ℝ) :
    a ⨯₃ b = det ![unitI, a, b] • unitI + det ![unitJ, a, b] • unitJ +
      det ![unitK, a, b] • unitK := by
  simp only [← triple_product_eq_det]
  ext i
  fin_cases i <;> simp [cross_apply, unitI, unitJ, unitK]

/-- **DLMF 1.6.9**: `a × b = (a₂b₃ − a₃b₂) i + (a₃b₁ − a₁b₃) j + (a₁b₂ − a₂b₁) k`. -/
theorem dlmf_1_6_9 (a b : Fin 3 → ℝ) :
    a ⨯₃ b = (a 1 * b 2 - a 2 * b 1) • unitI + (a 2 * b 0 - a 0 * b 2) • unitJ +
      (a 0 * b 1 - a 1 * b 0) • unitK := by
  ext i
  fin_cases i <;> simp [cross_apply, unitI, unitJ, unitK]

/-- Lagrange's identity `(a × b) · (a × b) = (a · a)(b · b) − (a · b)²`. -/
theorem dot_cross_self_eq (a b : Fin 3 → ℝ) :
    (a ⨯₃ b) ⬝ᵥ (a ⨯₃ b) = (a ⬝ᵥ a) * (b ⬝ᵥ b) - (a ⬝ᵥ b) ^ 2 := by
  simp only [dlmf_1_6_2, cross_apply, cons_val_zero, cons_val_one, cons_val_two, head_cons,
    tail_cons]
  ring

/-- `‖a × b‖ = ‖a‖ ‖b‖ sin θ`. -/
theorem vnorm_cross (a b : Fin 3 → ℝ) :
    vnorm (a ⨯₃ b) = vnorm a * vnorm b * Real.sin (vangle a b) := by
  have h := InnerProductGeometry.sin_angle_mul_norm_mul_norm
    (WithLp.toLp 2 a : EuclideanSpace ℝ (Fin 3)) (WithLp.toLp 2 b)
  rw [inner_toLp, inner_toLp, inner_toLp, ← dlmf_1_6_3, ← dlmf_1_6_3] at h
  rw [vangle, mul_comm, h, vnorm, dot_cross_self_eq, sq]

/-- **DLMF 1.6.9**: `a × b = ‖a‖ ‖b‖ (sin θ) n`, where (for `a × b ≠ 0`) `n` is the unit vector
normal to `a` and `b` whose direction is given by the right-hand rule (`det [a, b, n] > 0`). -/
theorem dlmf_1_6_9_normal {a b : Fin 3 → ℝ} (h : a ⨯₃ b ≠ 0) :
    vnorm ((vnorm (a ⨯₃ b))⁻¹ • (a ⨯₃ b)) = 1 ∧ a ⬝ᵥ ((vnorm (a ⨯₃ b))⁻¹ • (a ⨯₃ b)) = 0 ∧
      b ⬝ᵥ ((vnorm (a ⨯₃ b))⁻¹ • (a ⨯₃ b)) = 0 ∧
      0 < det ![a, b, (vnorm (a ⨯₃ b))⁻¹ • (a ⨯₃ b)] ∧
      a ⨯₃ b = (vnorm a * vnorm b * Real.sin (vangle a b)) •
        ((vnorm (a ⨯₃ b))⁻¹ • (a ⨯₃ b)) := by
  set c := a ⨯₃ b
  have hcc : 0 < c ⬝ᵥ c := by
    rw [dlmf_1_6_2]
    by_contra hle
    push Not at hle
    apply h
    ext i
    fin_cases i <;> simp <;> nlinarith [sq_nonneg (c 0), sq_nonneg (c 1), sq_nonneg (c 2)]
  have hn : 0 < vnorm c := Real.sqrt_pos.mpr hcc
  have hsq : vnorm c * vnorm c = c ⬝ᵥ c := Real.mul_self_sqrt hcc.le
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [vnorm, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← hsq]
    field_simp
    exact Real.sqrt_one
  · rw [dotProduct_smul, dot_self_cross, smul_zero]
  · rw [dotProduct_smul, dot_cross_self, smul_zero]
  · rw [← triple_product_eq_det, triple_product_permutation, triple_product_permutation,
      smul_dotProduct, smul_eq_mul, ← hsq]
    field_simp
    exact hn
  · rw [← vnorm_cross, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]

/-- **DLMF §1.6(i)**: the area of the parallelogram with sides `a`, `b` — base `‖a‖` times height
`‖b − ((a · b)/(a · a)) a‖` — is `‖a × b‖`. -/
theorem dlmf_1_6_i_area {a : Fin 3 → ℝ} (ha : a ≠ 0) (b : Fin 3 → ℝ) :
    vnorm a * vnorm (b - (a ⬝ᵥ b / a ⬝ᵥ a) • a) = vnorm (a ⨯₃ b) := by
  have haa : 0 < a ⬝ᵥ a := by
    rw [dlmf_1_6_2]
    by_contra hle
    push Not at hle
    apply ha
    ext i
    fin_cases i <;> simp <;> nlinarith [sq_nonneg (a 0), sq_nonneg (a 1), sq_nonneg (a 2)]
  rw [vnorm, vnorm, vnorm, ← Real.sqrt_mul haa.le, dot_cross_self_eq]
  congr 1
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    dotProduct_comm b a]
  field_simp
  ring

/-- **DLMF §1.6(i)**: the volume of the parallelepiped with edges `a`, `b`, `c` is
`|a · (b × c)|` (Lebesgue measure of `{s a + t b + u c : s, t, u ∈ [0, 1]}`). -/
theorem dlmf_1_6_i_volume (a b c : Fin 3 → ℝ) :
    volume (parallelepiped ![a, b, c]) = ENNReal.ofReal |a ⬝ᵥ (b ⨯₃ c)| := by
  have h : (Pi.basisFun ℝ (Fin 3)).addHaar = volume := by
    rw [Module.Basis.addHaar_def, Module.Basis.parallelepiped_basisFun,
      addHaarMeasure_eq_volume_pi]
  rw [← h, Measure.addHaar_parallelepiped, Module.Basis.det_apply, triple_product_eq_det]
  congr 2
  rw [← Matrix.det_transpose]
  congr 1

/-- **DLMF 1.6.10**: `a × (b × c) = b (a · c) − c (a · b)`. -/
theorem dlmf_1_6_10 (a b c : Fin 3 → ℝ) :
    a ⨯₃ (b ⨯₃ c) = (a ⬝ᵥ c) • b - (a ⬝ᵥ b) • c := by
  ext i
  fin_cases i <;> simp [cross_apply, dlmf_1_6_2] <;> ring

/-- **DLMF 1.6.11**: `(a × b) × c = b (a · c) − a (b · c)`. -/
theorem dlmf_1_6_11 (a b c : Fin 3 → ℝ) :
    (a ⨯₃ b) ⨯₃ c = (a ⬝ᵥ c) • b - (b ⬝ᵥ c) • a := by
  ext i
  fin_cases i <;> simp [cross_apply, dlmf_1_6_2] <;> ring

/-! ## §1.6(ii) Vectors: alternative notations

Einstein's summation convention is written with explicit sums `∑ j`; indices run over `Fin 3`
(DLMF's `1, 2, 3` are `0, 1, 2`). -/

/-- **DLMF 1.6.12**: `aⱼbⱼ = ∑_{j=1}^3 aⱼbⱼ = a · b`. -/
theorem dlmf_1_6_12 (a b : Fin 3 → ℝ) : ∑ j, a j * b j = a ⬝ᵥ b := rfl

/-- **DLMF 1.6.13**: the unit vectors `e₁, e₂, e₃`. -/
def unitE (j : Fin 3) : Fin 3 → ℝ := Pi.single j 1

theorem unitE_eq : unitE 0 = unitI ∧ unitE 1 = unitJ ∧ unitE 2 = unitK := by
  refine ⟨?_, ?_, ?_⟩ <;> ext i <;> fin_cases i <;> rfl

/-- **DLMF §1.6(ii)**: `aⱼ eⱼ = a`. -/
theorem dlmf_1_6_13 (a : Fin 3 → ℝ) : ∑ j, a j • unitE j = a := by
  ext i
  simp [unitE, Finset.sum_apply, Pi.single_apply]

/-- **DLMF 1.6.14**: the Levi-Civita symbol `ε_{jkℓ}`: `+1` for an even permutation of
`1, 2, 3`, `−1` for an odd one, `0` otherwise (see `dlmf_1_6_14`). -/
def leviCivita (j k l : Fin 3) : ℤ :=
  if j = k ∨ k = l ∨ j = l then 0 else if k - j = 1 then 1 else -1

/-- **DLMF 1.6.14**: `ε_{σ(1)σ(2)σ(3)} = sign σ` for every permutation `σ`, and `ε_{jkℓ} = 0`
when `j, k, ℓ` is not a permutation. -/
theorem dlmf_1_6_14 :
    (∀ σ : Equiv.Perm (Fin 3), leviCivita (σ 0) (σ 1) (σ 2) = (Equiv.Perm.sign σ : ℤ)) ∧
      ∀ j k l : Fin 3, ¬ Function.Injective ![j, k, l] → leviCivita j k l = 0 := by
  constructor <;> decide

/-- **DLMF 1.6.15**: `ε₁₂₃ = ε₃₁₂ = 1`, `ε₂₁₃ = ε₃₂₁ = −1`, `ε₂₂₁ = 0`. -/
theorem dlmf_1_6_15 :
    leviCivita 0 1 2 = 1 ∧ leviCivita 2 0 1 = 1 ∧ leviCivita 1 0 2 = -1 ∧
      leviCivita 2 1 0 = -1 ∧ leviCivita 1 1 0 = 0 := by
  decide

/-- **DLMF 1.6.16**: `ε_{jkℓ} ε_{ℓmn} = δ_{j,m} δ_{k,n} − δ_{j,n} δ_{k,m}` (summed over `ℓ`). -/
theorem dlmf_1_6_16 (j k m n : Fin 3) :
    ∑ l, leviCivita j k l * leviCivita l m n =
      (if j = m then 1 else 0) * (if k = n then 1 else 0) -
        (if j = n then 1 else 0) * (if k = m then 1 else 0) := by
  revert j k m n
  decide

/-- **DLMF 1.6.17**: `eⱼ × eₖ = ε_{jkℓ} eℓ` (summed over `ℓ`). -/
theorem dlmf_1_6_17 (j k : Fin 3) :
    unitE j ⨯₃ unitE k = ∑ l, (leviCivita j k l : ℝ) • unitE l := by
  ext i
  have h1 : ¬((-1 : Fin 3) = 1) := by decide
  have h2 : (-2 : Fin 3) = 1 := by decide
  fin_cases j <;> fin_cases k <;> fin_cases i <;>
    simp [cross_apply, unitE, leviCivita, Finset.sum_apply, Fin.sum_univ_three, h1, h2]

/-- **DLMF 1.6.18**: `aⱼ eⱼ × bₖ eₖ = ε_{jkℓ} aⱼ bₖ eℓ` (summed over `j, k, ℓ`). -/
theorem dlmf_1_6_18 (a b : Fin 3 → ℝ) :
    (∑ j, a j • unitE j) ⨯₃ (∑ k, b k • unitE k) =
      ∑ j, ∑ k, ∑ l, ((leviCivita j k l : ℝ) * a j * b k) • unitE l := by
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, dlmf_1_6_17,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => ?_
  congr 1
  ring

/-- `ε_{jkℓ} aⱼ bₖ cℓ = a · (b × c)`. -/
theorem sum_leviCivita_eq_triple (a b c : Fin 3 → ℝ) :
    ∑ j, ∑ k, ∑ l, (leviCivita j k l : ℝ) * a j * b k * c l = a ⬝ᵥ (b ⨯₃ c) := by
  have h1 : ¬((-1 : Fin 3) = 1) := by decide
  have h2 : (-2 : Fin 3) = 1 := by decide
  simp only [Fin.sum_univ_three, dlmf_1_6_2, cross_apply]
  simp [leviCivita, h1, h2]
  ring

/-- **DLMF §1.6(ii)**: the volume of the parallelepiped with edges `a`, `b`, `c` is
`|ε_{jkℓ} aⱼ bₖ cℓ|`. -/
theorem dlmf_1_6_ii_volume (a b c : Fin 3 → ℝ) :
    volume (parallelepiped ![a, b, c]) =
      ENNReal.ofReal |∑ j, ∑ k, ∑ l, (leviCivita j k l : ℝ) * a j * b k * c l| := by
  rw [sum_leviCivita_eq_triple, dlmf_1_6_i_volume]

/-! ## §1.6(iii) Vector-valued functions

Points of `ℝ³` are `p : Fin 3 → ℝ` (coordinates `x, y, z` = `p 0, p 1, p 2`), scalar fields are
`f : (Fin 3 → ℝ) → ℝ` and vector fields `F : (Fin 3 → ℝ) → (Fin 3 → ℝ)` with components
`F · k`.  The partial derivative `∂f/∂xᵢ` at `p` is `pd i f p = Df(p) eᵢ`. -/

section VectorFields

/-- The partial derivative `∂f/∂xᵢ`: the derivative of `f` at `p` in the direction `eᵢ`. -/
noncomputable def pd (i : Fin 3) (f : (Fin 3 → ℝ) → ℝ) (p : Fin 3 → ℝ) : ℝ :=
  fderiv ℝ f p (unitE i)

/-- `pd i f p` is the derivative of `t ↦ f(p + t eᵢ)` at `0`. -/
theorem hasDerivAt_pd {f : (Fin 3 → ℝ) → ℝ} {p : Fin 3 → ℝ} (hf : DifferentiableAt ℝ f p)
    (i : Fin 3) : HasDerivAt (fun t : ℝ => f (p + t • unitE i)) (pd i f p) 0 := by
  have hg : HasDerivAt (fun t : ℝ => p + t • unitE i) (unitE i) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (unitE i)).const_add p
  have hf' : HasFDerivAt f (fderiv ℝ f p) (p + (0 : ℝ) • unitE i) := by
    simpa using hf.hasFDerivAt
  exact hf'.comp_hasDerivAt 0 hg

/-- **DLMF 1.6.19**: `∂f/∂xᵢ = lim_{h→0} (f(p + h eᵢ) − f(p))/h`, the coordinate partial
derivative (for `f` differentiable at `p`). -/
theorem dlmf_1_6_19 {f : (Fin 3 → ℝ) → ℝ} {p : Fin 3 → ℝ} (hf : DifferentiableAt ℝ f p)
    (i : Fin 3) : pd i f p = deriv (fun t : ℝ => f (p + t • unitE i)) 0 :=
  (hasDerivAt_pd hf i).deriv.symm

theorem pd_add {f g : (Fin 3 → ℝ) → ℝ} {p : Fin 3 → ℝ} (hf : DifferentiableAt ℝ f p)
    (hg : DifferentiableAt ℝ g p) (i : Fin 3) :
    pd i (fun q => f q + g q) p = pd i f p + pd i g p := by
  simp only [pd]
  rw [show (fun q => f q + g q) = f + g from rfl, fderiv_add hf hg]
  rfl

theorem pd_sub {f g : (Fin 3 → ℝ) → ℝ} {p : Fin 3 → ℝ} (hf : DifferentiableAt ℝ f p)
    (hg : DifferentiableAt ℝ g p) (i : Fin 3) :
    pd i (fun q => f q - g q) p = pd i f p - pd i g p := by
  simp only [pd]
  rw [show (fun q => f q - g q) = f - g from rfl, fderiv_sub hf hg]
  rfl

theorem pd_mul {f g : (Fin 3 → ℝ) → ℝ} {p : Fin 3 → ℝ} (hf : DifferentiableAt ℝ f p)
    (hg : DifferentiableAt ℝ g p) (i : Fin 3) :
    pd i (fun q => f q * g q) p = f p * pd i g p + g p * pd i f p := by
  simp only [pd]
  rw [show (fun q => f q * g q) = f * g from rfl, fderiv_mul hf hg]
  rfl

theorem pd_div {f g : (Fin 3 → ℝ) → ℝ} {p : Fin 3 → ℝ} (hf : DifferentiableAt ℝ f p)
    (hg : DifferentiableAt ℝ g p) (hg0 : g p ≠ 0) (i : Fin 3) :
    pd i (fun q => f q / g q) p = (g p * pd i f p - f p * pd i g p) / g p ^ 2 := by
  have h := (hasDerivAt_pd hf i).div (hasDerivAt_pd hg i) (by simpa using hg0)
  simp only [zero_smul, add_zero] at h
  have hd : DifferentiableAt ℝ (fun q => f q / g q) p := by
    refine (hf.mul (hg.inv hg0)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => ?_)
    simp [div_eq_mul_inv]
  rw [(hasDerivAt_pd hd i).unique h]
  ring

/-- **DLMF 1.6.20**: `grad f = ∇f = (∂f/∂x) i + (∂f/∂y) j + (∂f/∂z) k`. -/
noncomputable def grad3 (f : (Fin 3 → ℝ) → ℝ) (p : Fin 3 → ℝ) : Fin 3 → ℝ := fun i => pd i f p

/-- **DLMF 1.6.19–1.6.20**: `∇ = i ∂/∂x + j ∂/∂y + k ∂/∂z` applied to `f`. -/
theorem dlmf_1_6_20 (f : (Fin 3 → ℝ) → ℝ) (p : Fin 3 → ℝ) :
    grad3 f p = pd 0 f p • unitI + pd 1 f p • unitJ + pd 2 f p • unitK := by
  ext i
  fin_cases i <;> simp [grad3, unitI, unitJ, unitK]

/-- **DLMF 1.6.21**: `div F = ∇ · F = ∂F₁/∂x + ∂F₂/∂y + ∂F₃/∂z`. -/
noncomputable def div3 (F : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (p : Fin 3 → ℝ) : ℝ :=
  ∑ i, pd i (fun q => F q i) p

theorem dlmf_1_6_21 (F : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (p : Fin 3 → ℝ) :
    div3 F p = pd 0 (fun q => F q 0) p + pd 1 (fun q => F q 1) p + pd 2 (fun q => F q 2) p := by
  simp [div3, Fin.sum_univ_three]

/-- **DLMF 1.6.22**: `curl F = ∇ × F = (∂F₃/∂y − ∂F₂/∂z) i + (∂F₁/∂z − ∂F₃/∂x) j +
(∂F₂/∂x − ∂F₁/∂y) k`. -/
noncomputable def curl3 (F : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (p : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![pd 1 (fun q => F q 2) p - pd 2 (fun q => F q 1) p,
    pd 2 (fun q => F q 0) p - pd 0 (fun q => F q 2) p,
    pd 0 (fun q => F q 1) p - pd 1 (fun q => F q 0) p]

/-- **DLMF 1.6.22**, the formal determinant `|i j k; ∂/∂x ∂/∂y ∂/∂z; F₁ F₂ F₃|` written with the
Levi-Civita symbol: `(∇ × F)ℓ = ε_{ℓjk} ∂ⱼ Fₖ`. -/
theorem dlmf_1_6_22 (F : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (p : Fin 3 → ℝ) (l : Fin 3) :
    curl3 F p l = ∑ j, ∑ k, (leviCivita l j k : ℝ) * pd j (fun q => F q k) p := by
  have h1 : ¬((-1 : Fin 3) = 1) := by decide
  have h2 : (-2 : Fin 3) = 1 := by decide
  fin_cases l <;> simp [curl3, Fin.sum_univ_three, leviCivita, h1, h2] <;> ring

/-- **DLMF 1.6.23**: `∇(fg) = f∇g + g∇f`. -/
theorem dlmf_1_6_23 {f g : (Fin 3 → ℝ) → ℝ} {p : Fin 3 → ℝ} (hf : DifferentiableAt ℝ f p)
    (hg : DifferentiableAt ℝ g p) :
    grad3 (fun q => f q * g q) p = f p • grad3 g p + g p • grad3 f p := by
  ext i
  simp [grad3, pd_mul hf hg]

/-- **DLMF 1.6.24**: `∇(f/g) = (g∇f − f∇g)/g²`. -/
theorem dlmf_1_6_24 {f g : (Fin 3 → ℝ) → ℝ} {p : Fin 3 → ℝ} (hf : DifferentiableAt ℝ f p)
    (hg : DifferentiableAt ℝ g p) (hg0 : g p ≠ 0) :
    grad3 (fun q => f q / g q) p = (g p ^ 2)⁻¹ • (g p • grad3 f p - f p • grad3 g p) := by
  ext i
  simp only [grad3, pd_div hf hg hg0, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-- **DLMF 1.6.25**: `∇ · (fF) = f(∇ · F) + F · ∇f`. -/
theorem dlmf_1_6_25 {f : (Fin 3 → ℝ) → ℝ} {F : (Fin 3 → ℝ) → (Fin 3 → ℝ)} {p : Fin 3 → ℝ}
    (hf : DifferentiableAt ℝ f p) (hF : DifferentiableAt ℝ F p) :
    div3 (fun q => f q • F q) p = f p * div3 F p + F p ⬝ᵥ grad3 f p := by
  have hc := differentiableAt_pi.mp hF
  simp only [div3, Pi.smul_apply, smul_eq_mul, pd_mul hf (hc _), Finset.sum_add_distrib,
    Finset.mul_sum, dotProduct, grad3]

/-- **DLMF 1.6.26**: `∇ · (F × G) = G · (∇ × F) − F · (∇ × G)`. -/
theorem dlmf_1_6_26 {F G : (Fin 3 → ℝ) → (Fin 3 → ℝ)} {p : Fin 3 → ℝ}
    (hF : DifferentiableAt ℝ F p) (hG : DifferentiableAt ℝ G p) :
    div3 (fun q => F q ⨯₃ G q) p = G p ⬝ᵥ curl3 F p - F p ⬝ᵥ curl3 G p := by
  have hf := differentiableAt_pi.mp hF
  have hg := differentiableAt_pi.mp hG
  simp only [div3, Fin.sum_univ_three, cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  have hm : ∀ a b, DifferentiableAt ℝ (fun q => F q a * G q b) p := fun a b =>
    (hf a).mul (hg b)
  rw [pd_sub (hm 1 2) (hm 2 1), pd_sub (hm 2 0) (hm 0 2), pd_sub (hm 0 1) (hm 1 0),
    pd_mul (hf 1) (hg 2), pd_mul (hf 2) (hg 1), pd_mul (hf 2) (hg 0), pd_mul (hf 0) (hg 2),
    pd_mul (hf 0) (hg 1), pd_mul (hf 1) (hg 0)]
  simp only [dlmf_1_6_2, curl3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

/-- **DLMF 1.6.28**: `∇ × (fF) = f(∇ × F) + (∇f) × F`. -/
theorem dlmf_1_6_28 {f : (Fin 3 → ℝ) → ℝ} {F : (Fin 3 → ℝ) → (Fin 3 → ℝ)} {p : Fin 3 → ℝ}
    (hf : DifferentiableAt ℝ f p) (hF : DifferentiableAt ℝ F p) :
    curl3 (fun q => f q • F q) p = f p • curl3 F p + grad3 f p ⨯₃ F p := by
  have hc := differentiableAt_pi.mp hF
  ext l
  fin_cases l <;>
  · simp only [curl3, Pi.smul_apply, smul_eq_mul, pd_mul hf (hc _), Pi.add_apply,
      cross_apply, grad3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    ring

/-! ### Second-order identities (for `C²` fields) -/

theorem contDiff_pd {f : (Fin 3 → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (j : Fin 3) :
    ContDiff ℝ 1 (pd j f) := by
  show ContDiff ℝ 1 fun p => fderiv ℝ f p (unitE j)
  exact (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

theorem differentiable_pd {f : (Fin 3 → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (j : Fin 3) :
    Differentiable ℝ (pd j f) :=
  (contDiff_pd hf j).differentiable one_ne_zero

/-- `∂ᵢ∂ⱼ f(p) = D²f(p)(eᵢ, eⱼ)`. -/
theorem pd_pd_eq {f : (Fin 3 → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (i j : Fin 3) (p : Fin 3 → ℝ) :
    pd i (pd j f) p = fderiv ℝ (fderiv ℝ f) p (unitE i) (unitE j) := by
  have hdd : DifferentiableAt ℝ (fderiv ℝ f) p :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero p
  have h := hdd.hasFDerivAt.clm_apply (hasFDerivAt_const (unitE j) p)
  show fderiv ℝ (fun q => fderiv ℝ f q (unitE j)) p (unitE i) = _
  rw [h.fderiv]
  simp

/-- Mixed partial derivatives of a `C²` function commute. -/
theorem pd_comm {f : (Fin 3 → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (i j : Fin 3) (p : Fin 3 → ℝ) :
    pd i (pd j f) p = pd j (pd i f) p := by
  rw [pd_pd_eq hf, pd_pd_eq hf]
  exact hf.contDiffAt.isSymmSndFDerivAt (by simp) _ _

theorem pd_sum {g : Fin 3 → (Fin 3 → ℝ) → ℝ} {p : Fin 3 → ℝ}
    (hg : ∀ i, DifferentiableAt ℝ (g i) p) (j : Fin 3) :
    pd j (fun q => ∑ i, g i q) p = ∑ i, pd j (g i) p := by
  simp only [pd]
  rw [fderiv_fun_sum fun i _ => hg i]
  simp

/-- **DLMF 1.6.27**: `∇ · (∇ × F) = div curl F = 0`. -/
theorem dlmf_1_6_27 {F : (Fin 3 → ℝ) → (Fin 3 → ℝ)} (hF : ContDiff ℝ 2 F) (p : Fin 3 → ℝ) :
    div3 (curl3 F) p = 0 := by
  have hc : ∀ k, ContDiff ℝ 2 fun q => F q k := contDiff_pi.mp hF
  have hd : ∀ k j, Differentiable ℝ (pd j fun q => F q k) := fun k j =>
    differentiable_pd (hc k) j
  simp only [div3, Fin.sum_univ_three, curl3, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  rw [pd_sub (hd 2 1 p) (hd 1 2 p), pd_sub (hd 0 2 p) (hd 2 0 p), pd_sub (hd 1 0 p) (hd 0 1 p)]
  linarith [pd_comm (hc 2) 0 1 p, pd_comm (hc 1) 0 2 p, pd_comm (hc 0) 1 2 p]

/-- **DLMF 1.6.29**: `∇ × (∇f) = curl grad f = 0`. -/
theorem dlmf_1_6_29 {f : (Fin 3 → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (p : Fin 3 → ℝ) :
    curl3 (grad3 f) p = 0 := by
  ext l
  fin_cases l <;> simp only [curl3, grad3, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Pi.zero_apply, Fin.zero_eta,
      Fin.mk_one, Fin.reduceFinMk]
  · rw [pd_comm hf 1 2, sub_self]
  · rw [pd_comm hf 2 0, sub_self]
  · rw [pd_comm hf 0 1, sub_self]

/-- **DLMF 1.6.30**: the Laplacian `∇²f = ∇ · (∇f)`. -/
noncomputable def lap3 (f : (Fin 3 → ℝ) → ℝ) (p : Fin 3 → ℝ) : ℝ := div3 (grad3 f) p

/-- **DLMF 1.6.30**: `∇²f = ∂²f/∂x² + ∂²f/∂y² + ∂²f/∂z²`. -/
theorem dlmf_1_6_30 (f : (Fin 3 → ℝ) → ℝ) (p : Fin 3 → ℝ) :
    lap3 f p = div3 (grad3 f) p ∧ lap3 f p = ∑ i, pd i (pd i f) p :=
  ⟨rfl, rfl⟩

/-- `∂ᵢ(fg) = f ∂ᵢg + g ∂ᵢf` as functions, for differentiable `f`, `g`. -/
theorem pd_mul_fun {f g : (Fin 3 → ℝ) → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (i : Fin 3) : pd i (fun q => f q * g q) = fun q => f q * pd i g q + g q * pd i f q :=
  funext fun q => pd_mul (hf q) (hg q) i

/-- **DLMF 1.6.31**: `∇²(fg) = f∇²g + g∇²f + 2(∇f · ∇g)`. -/
theorem dlmf_1_6_31 {f g : (Fin 3 → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (p : Fin 3 → ℝ) :
    lap3 (fun q => f q * g q) p = f p * lap3 g p + g p * lap3 f p +
      2 * (grad3 f p ⬝ᵥ grad3 g p) := by
  have hf1 : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hg1 : Differentiable ℝ g := hg.differentiable (by norm_num)
  have key : ∀ i, pd i (pd i fun q => f q * g q) p =
      f p * pd i (pd i g) p + pd i g p * pd i f p +
        (g p * pd i (pd i f) p + pd i f p * pd i g p) := fun i => by
    have hm1 : DifferentiableAt ℝ (fun q => f q * pd i g q) p :=
      (hf1 p).mul (differentiable_pd hg i p)
    have hm2 : DifferentiableAt ℝ (fun q => g q * pd i f q) p :=
      (hg1 p).mul (differentiable_pd hf i p)
    rw [pd_mul_fun hf1 hg1 i, pd_add hm1 hm2, pd_mul (hf1 p) (differentiable_pd hg i p),
      pd_mul (hg1 p) (differentiable_pd hf i p)]
  simp only [(dlmf_1_6_30 _ _).2, key, Fin.sum_univ_three, dotProduct, grad3]
  ring

/-- **DLMF 1.6.32**: `∇ · (∇f × ∇g) = 0`. -/
theorem dlmf_1_6_32 {f g : (Fin 3 → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (p : Fin 3 → ℝ) : div3 (fun q => grad3 f q ⨯₃ grad3 g q) p = 0 := by
  have hgf : DifferentiableAt ℝ (grad3 f) p :=
    differentiableAt_pi.mpr fun i => differentiable_pd hf i p
  have hgg : DifferentiableAt ℝ (grad3 g) p :=
    differentiableAt_pi.mpr fun i => differentiable_pd hg i p
  rw [dlmf_1_6_26 hgf hgg, dlmf_1_6_29 hf, dlmf_1_6_29 hg, dotProduct_zero, dotProduct_zero,
    sub_zero]

/-- **DLMF 1.6.33**: `∇ · (f∇g − g∇f) = f∇²g − g∇²f`. -/
theorem dlmf_1_6_33 {f g : (Fin 3 → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (p : Fin 3 → ℝ) :
    div3 (fun q => f q • grad3 g q - g q • grad3 f q) p = f p * lap3 g p - g p * lap3 f p := by
  have hf1 : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hg1 : Differentiable ℝ g := hg.differentiable (by norm_num)
  have key : ∀ i, pd i (fun q => (f q • grad3 g q - g q • grad3 f q) i) p =
      f p * pd i (pd i g) p + pd i g p * pd i f p -
        (g p * pd i (pd i f) p + pd i f p * pd i g p) := fun i => by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, grad3]
    have hm1 : DifferentiableAt ℝ (fun q => f q * pd i g q) p :=
      (hf1 p).mul (differentiable_pd hg i p)
    have hm2 : DifferentiableAt ℝ (fun q => g q * pd i f q) p :=
      (hg1 p).mul (differentiable_pd hf i p)
    rw [pd_sub hm1 hm2,
      pd_mul (hf1 p) (differentiable_pd hg i p), pd_mul (hg1 p) (differentiable_pd hf i p)]
  simp only [div3, key, (dlmf_1_6_30 _ _).2, Fin.sum_univ_three]
  ring

/-- The vector Laplacian `∇²F`, componentwise. -/
noncomputable def vlap3 (F : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (p : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => lap3 (fun q => F q i) p

/-- **DLMF 1.6.34**: `∇ × (∇ × F) = curl curl F = ∇(∇ · F) − ∇²F`. -/
theorem dlmf_1_6_34 {F : (Fin 3 → ℝ) → (Fin 3 → ℝ)} (hF : ContDiff ℝ 2 F) (p : Fin 3 → ℝ) :
    curl3 (curl3 F) p = grad3 (div3 F) p - vlap3 F p := by
  have hc : ∀ k, ContDiff ℝ 2 fun q => F q k := contDiff_pi.mp hF
  have hd : ∀ k j, Differentiable ℝ (pd j fun q => F q k) := fun k j =>
    differentiable_pd (hc k) j
  have hdiv : ∀ j, pd j (div3 F) p = ∑ i, pd j (pd i fun q => F q i) p := fun j =>
    pd_sum (g := fun i => pd i fun q => F q i) (fun i => hd i i p) j
  ext l
  simp only [Pi.sub_apply, grad3, hdiv, vlap3, (dlmf_1_6_30 _ _).2, Fin.sum_univ_three]
  fin_cases l <;> simp only [curl3, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk]
  · rw [pd_sub (hd 1 0 p) (hd 0 1 p), pd_sub (hd 0 2 p) (hd 2 0 p)]
    linarith [pd_comm (hc 1) 0 1 p, pd_comm (hc 2) 0 2 p]
  · rw [pd_sub (hd 2 1 p) (hd 1 2 p), pd_sub (hd 1 0 p) (hd 0 1 p)]
    linarith [pd_comm (hc 0) 1 0 p, pd_comm (hc 2) 1 2 p]
  · rw [pd_sub (hd 0 2 p) (hd 2 0 p), pd_sub (hd 2 1 p) (hd 1 2 p)]
    linarith [pd_comm (hc 0) 2 0 p, pd_comm (hc 1) 2 1 p]

end VectorFields

/-! ## §1.6(iv) Path and line integrals

A path is `c : ℝ → (Fin 3 → ℝ)`, `c(t) = (x(t), y(t), z(t))`, with velocity `deriv c`.  Green's
theorem is proven for rectangles; DLMF states it for any closed bounded region whose boundary is a
piecewise-differentiable simple closed curve, which needs the Jordan curve theorem (not in
Mathlib). -/

section Paths

/-- `‖v‖` is continuous. -/
theorem continuous_vnorm : Continuous vnorm := by
  show Continuous fun v : Fin 3 → ℝ => √(∑ i, v i * v i)
  exact Real.continuous_sqrt.comp
    (continuous_finsetSum _ fun i _ => (continuous_apply i).mul (continuous_apply i))

theorem vnorm_smul (r : ℝ) (v : Fin 3 → ℝ) : vnorm (r • v) = |r| * vnorm v := by
  simp only [vnorm, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [← mul_assoc, Real.sqrt_mul (mul_self_nonneg r), Real.sqrt_mul_self_eq_abs]

/-- **DLMF 1.6.35**: `c'(t) = (x'(t), y'(t), z'(t))`. -/
theorem dlmf_1_6_35 {c : ℝ → Fin 3 → ℝ} {t : ℝ} (hc : DifferentiableAt ℝ c t) :
    deriv c t = ![deriv (fun s => c s 0) t, deriv (fun s => c s 1) t,
      deriv (fun s => c s 2) t] := by
  rw [deriv_pi (differentiableAt_pi.mp hc)]
  ext i
  fin_cases i <;> rfl

/-- **DLMF 1.6.36**: the length `∫_a^b ‖c'(t)‖ dt` of a path. -/
noncomputable def pathLength (c : ℝ → Fin 3 → ℝ) (a b : ℝ) : ℝ :=
  ∫ t in a..b, vnorm (deriv c t)

/-- **DLMF 1.6.36**: for a path with continuous velocity, the length is the total variation of
`c` on `[a, b]` (the supremum of the lengths of inscribed polygons, `olver_11_02`). -/
theorem dlmf_1_6_36 {c : ℝ → Fin 3 → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hc : ∀ t ∈ Set.Icc a b, HasDerivAt c (deriv c t) t)
    (hc' : ContinuousOn (deriv c) (Set.Icc a b)) :
    ENNReal.ofReal (pathLength c a b) =
      eVariationOn (fun t => (WithLp.toLp 2 (c t) : EuclideanSpace ℝ (Fin 3))) (Set.Icc a b) := by
  set e := (EuclideanSpace.equiv (Fin 3) ℝ).symm
  have he : ∀ v, e v = WithLp.toLp 2 v := fun v => rfl
  have h := olver_11_02 hab (f := fun t => e (c t)) (f' := fun t => e (deriv c t))
    (fun t ht => e.hasFDerivAt.comp_hasDerivAt t (hc t ht)) (e.continuous.comp_continuousOn hc')
  simp only [he] at h
  rw [h, pathLength]
  congr 2
  funext t
  rw [dlmf_1_6_3]

/-- **DLMF 1.6.37**: the path integral `∫_c f ds = ∫_a^b f(c(t)) ‖c'(t)‖ dt`. -/
noncomputable def pathIntegral (f : (Fin 3 → ℝ) → ℝ) (c : ℝ → Fin 3 → ℝ) (a b : ℝ) : ℝ :=
  ∫ t in a..b, f (c t) * vnorm (deriv c t)

theorem dlmf_1_6_37 (f : (Fin 3 → ℝ) → ℝ) (c : ℝ → Fin 3 → ℝ) (a b : ℝ) :
    pathIntegral f c a b = ∫ t in a..b, f (c t) * vnorm (deriv c t) ∧
      pathLength c a b = pathIntegral (fun _ => 1) c a b := by
  simp [pathIntegral, pathLength]

/-- **DLMF 1.6.38**: the line integral `∫_c F · ds = ∫_a^b F(c(t)) · c'(t) dt`. -/
noncomputable def lineIntegral (F : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (c : ℝ → Fin 3 → ℝ)
    (a b : ℝ) : ℝ :=
  ∫ t in a..b, F (c t) ⬝ᵥ deriv c t

/-- **DLMF 1.6.38**: `∫_c F · ds = ∫_a^b (F₁ dx/dt + F₂ dy/dt + F₃ dz/dt) dt`. -/
theorem dlmf_1_6_38 (F : (Fin 3 → ℝ) → (Fin 3 → ℝ)) {c : ℝ → Fin 3 → ℝ}
    (hc : Differentiable ℝ c) (a b : ℝ) :
    lineIntegral F c a b = ∫ t in a..b, (F (c t) 0 * deriv (fun s => c s 0) t +
      F (c t) 1 * deriv (fun s => c s 1) t + F (c t) 2 * deriv (fun s => c s 2) t) := by
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [dlmf_1_6_2, dlmf_1_6_35 (hc t), Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

theorem deriv_comp_reparam {c : ℝ → Fin 3 → ℝ} {h h' : ℝ → ℝ} {t : ℝ}
    (hc : Differentiable ℝ c) (hh : HasDerivAt h (h' t) t) :
    deriv (c ∘ h) t = h' t • deriv c (h t) :=
  ((hc (h t)).hasDerivAt.scomp t hh).deriv

/-- Line integrals transform under a `C¹` reparametrization `t' = h(t)` by
`∫_{c ∘ h, [a, b]} F · ds = ∫_{c, [h(a), h(b)]} F · ds`. -/
theorem lineIntegral_comp {F : (Fin 3 → ℝ) → (Fin 3 → ℝ)} {c : ℝ → Fin 3 → ℝ} {h h' : ℝ → ℝ}
    {a b : ℝ} (hF : Continuous F) (hc : Differentiable ℝ c) (hc' : Continuous (deriv c))
    (hh : ∀ t ∈ Set.uIcc a b, HasDerivAt h (h' t) t) (hh' : ContinuousOn h' (Set.uIcc a b)) :
    lineIntegral F (c ∘ h) a b = lineIntegral F c (h a) (h b) := by
  have hg : Continuous fun u => F (c u) ⬝ᵥ deriv c u :=
    continuous_finsetSum _ fun i _ =>
      ((continuous_apply i).comp (hF.comp hc.continuous)).mul ((continuous_apply i).comp hc')
  rw [lineIntegral, lineIntegral, ← intervalIntegral.integral_comp_mul_deriv hh hh' hg]
  refine intervalIntegral.integral_congr fun t ht => ?_
  simp only [Function.comp_apply, deriv_comp_reparam hc (hh t ht), dotProduct_smul, smul_eq_mul]
  ring

/-- **DLMF 1.6.39**: for an orientation-preserving reparametrization `c₁ = c ∘ h` (`h(a) = a'`,
`h(b) = b'`), `∫_c F · ds = ∫_{c₁} F · ds`.  (Monotonicity of `h` is not needed here.) -/
theorem dlmf_1_6_39 {F : (Fin 3 → ℝ) → (Fin 3 → ℝ)} {c : ℝ → Fin 3 → ℝ} {h h' : ℝ → ℝ}
    {a b a' b' : ℝ} (hF : Continuous F) (hc : Differentiable ℝ c) (hc' : Continuous (deriv c))
    (hh : ∀ t ∈ Set.uIcc a b, HasDerivAt h (h' t) t) (hh' : ContinuousOn h' (Set.uIcc a b))
    (ha : h a = a') (hb : h b = b') :
    lineIntegral F c a' b' = lineIntegral F (c ∘ h) a b := by
  rw [lineIntegral_comp hF hc hc' hh hh', ha, hb]

/-- **DLMF 1.6.40**: for an orientation-reversing reparametrization (`h(a) = b'`, `h(b) = a'`),
`∫_c F · ds = −∫_{c₁} F · ds`. -/
theorem dlmf_1_6_40 {F : (Fin 3 → ℝ) → (Fin 3 → ℝ)} {c : ℝ → Fin 3 → ℝ} {h h' : ℝ → ℝ}
    {a b a' b' : ℝ} (hF : Continuous F) (hc : Differentiable ℝ c) (hc' : Continuous (deriv c))
    (hh : ∀ t ∈ Set.uIcc a b, HasDerivAt h (h' t) t) (hh' : ContinuousOn h' (Set.uIcc a b))
    (ha : h a = b') (hb : h b = a') :
    lineIntegral F c a' b' = -lineIntegral F (c ∘ h) a b := by
  rw [lineIntegral_comp hF hc hc' hh hh', ha, hb, lineIntegral, lineIntegral,
    intervalIntegral.integral_symm]

/-- **DLMF 1.6.41**: path integrals are unchanged by a monotonic `C¹` reparametrization
(orientation-preserving case). -/
theorem dlmf_1_6_41 {f : (Fin 3 → ℝ) → ℝ} {c : ℝ → Fin 3 → ℝ} {h h' : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : Continuous f) (hc : Differentiable ℝ c) (hc' : Continuous (deriv c))
    (hh : ∀ t ∈ Set.uIcc a b, HasDerivAt h (h' t) t) (hh' : ContinuousOn h' (Set.uIcc a b))
    (hmono : MonotoneOn h (Set.Icc a b)) :
    pathIntegral f c (h a) (h b) = pathIntegral f (c ∘ h) a b := by
  have hg : Continuous fun u => f (c u) * vnorm (deriv c u) :=
    (hf.comp hc.continuous).mul (continuous_vnorm.comp hc')
  have hpos : ∀ t ∈ Set.uIcc a b, 0 ≤ h' t := fun t ht => by
    rw [Set.uIcc_of_le hab.le] at ht
    exact (hh t (by rw [Set.uIcc_of_le hab.le]; exact ht)).hasDerivWithinAt.nonneg_of_monotoneOn
      (uniqueDiffWithinAt_iff_accPt.mp (uniqueDiffOn_Icc hab t ht)) hmono
  rw [pathIntegral, pathIntegral, ← intervalIntegral.integral_comp_mul_deriv hh hh' hg]
  refine intervalIntegral.integral_congr fun t ht => ?_
  simp only [Function.comp_apply, deriv_comp_reparam hc (hh t ht), vnorm_smul,
    abs_of_nonneg (hpos t ht)]
  ring

/-- **DLMF 1.6.41** (orientation-reversing case): for antitone `h`,
`∫_{c, [h(b), h(a)]} f ds = ∫_{c ∘ h, [a, b]} f ds`. -/
theorem dlmf_1_6_41_antitone {f : (Fin 3 → ℝ) → ℝ} {c : ℝ → Fin 3 → ℝ} {h h' : ℝ → ℝ}
    {a b : ℝ} (hab : a < b) (hf : Continuous f) (hc : Differentiable ℝ c)
    (hc' : Continuous (deriv c)) (hh : ∀ t ∈ Set.uIcc a b, HasDerivAt h (h' t) t)
    (hh' : ContinuousOn h' (Set.uIcc a b)) (hanti : AntitoneOn h (Set.Icc a b)) :
    pathIntegral f c (h b) (h a) = pathIntegral f (c ∘ h) a b := by
  have hg : Continuous fun u => f (c u) * vnorm (deriv c u) :=
    (hf.comp hc.continuous).mul (continuous_vnorm.comp hc')
  have hneg : ∀ t ∈ Set.uIcc a b, h' t ≤ 0 := fun t ht => by
    rw [Set.uIcc_of_le hab.le] at ht
    have := ((hh t (by rw [Set.uIcc_of_le hab.le]; exact ht)).neg).hasDerivWithinAt
      |>.nonneg_of_monotoneOn (uniqueDiffWithinAt_iff_accPt.mp (uniqueDiffOn_Icc hab t ht))
        (fun x hx y hy hxy => neg_le_neg (hanti hx hy hxy))
    linarith
  rw [pathIntegral, pathIntegral, intervalIntegral.integral_symm,
    ← intervalIntegral.integral_comp_mul_deriv hh hh' hg, ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun t ht => ?_
  simp only [Function.comp_apply, deriv_comp_reparam hc (hh t ht), vnorm_smul,
    abs_of_nonpos (hneg t ht)]
  ring

/-- `Df(p) v = ∇f(p) · v`. -/
theorem fderiv_apply_eq_grad (f : (Fin 3 → ℝ) → ℝ) (p v : Fin 3 → ℝ) :
    fderiv ℝ f p v = grad3 f p ⬝ᵥ v := by
  conv_lhs => rw [← dlmf_1_6_13 v]
  simp only [map_sum, map_smul, smul_eq_mul, dotProduct, grad3, pd]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- **DLMF 1.6.42**: for continuously differentiable `f`, `∫_c ∇f · ds = f(c(b)) − f(c(a))`. -/
theorem dlmf_1_6_42 {f : (Fin 3 → ℝ) → ℝ} {c : ℝ → Fin 3 → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : Differentiable ℝ c) (hc' : Continuous (deriv c)) (a b : ℝ) :
    lineIntegral (grad3 f) c a b = f (c b) - f (c a) := by
  have hgrad : Continuous (grad3 f) := continuous_pi fun i => by
    show Continuous fun p => fderiv ℝ f p (unitE i)
    exact (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hderiv : ∀ t, HasDerivAt (fun s => f (c s)) (grad3 f (c t) ⬝ᵥ deriv c t) t := fun t => by
    have := ((hf.differentiable one_ne_zero (c t)).hasFDerivAt).comp_hasDerivAt t
      (hc t).hasDerivAt
    rwa [fderiv_apply_eq_grad] at this
  have hcont : Continuous fun t => grad3 f (c t) ⬝ᵥ deriv c t :=
    continuous_finsetSum _ fun i _ =>
      ((continuous_apply i).comp (hgrad.comp hc.continuous)).mul ((continuous_apply i).comp hc')
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
    (hcont.intervalIntegrable a b)

/-- **DLMF §1.6(iv)**: the image of `c` on `[a, b]` is a simple closed curve if `c` is one-to-one
on `[a, b)` and `c(a) = c(b)`. -/
def IsSimpleClosedPath (c : ℝ → Fin 3 → ℝ) (a b : ℝ) : Prop :=
  Set.InjOn c (Set.Ico a b) ∧ c a = c b

/-- **DLMF §1.6(iv)**: `c` is piecewise differentiable on `[a, b]`: continuous, and differentiable
off finitely many points. -/
def IsPiecewiseDifferentiablePath (c : ℝ → Fin 3 → ℝ) (a b : ℝ) : Prop :=
  ContinuousOn c (Set.Icc a b) ∧
    ∃ s : Finset ℝ, ∀ t ∈ Set.Ioo a b, t ∉ s → DifferentiableAt ℝ c t

/-! ### Green's theorem (rectangles) -/

/-- The line integral `∫_c F₁ dx + F₂ dy` of the planar field `F = F₁ i + F₂ j` (DLMF 1.6.43)
along a plane path `c(t) = (x(t), y(t))`. -/
noncomputable def lineIntegral2 (F₁ F₂ : ℝ → ℝ → ℝ) (c : ℝ → ℝ × ℝ) (a b : ℝ) : ℝ :=
  ∫ t in a..b, (F₁ (c t).1 (c t).2 * deriv (fun s => (c s).1) t +
    F₂ (c t).1 (c t).2 * deriv (fun s => (c s).2) t)

/-- The line integral around the boundary of the rectangle `[x₀, x₁] × [y₀, y₁]`, traversed
anticlockwise (bottom, right, top, left). -/
noncomputable def rectBoundaryIntegral (F₁ F₂ : ℝ → ℝ → ℝ) (x₀ x₁ y₀ y₁ : ℝ) : ℝ :=
  lineIntegral2 F₁ F₂ (fun t => (t, y₀)) x₀ x₁ + lineIntegral2 F₁ F₂ (fun t => (x₁, t)) y₀ y₁ +
    lineIntegral2 F₁ F₂ (fun t => (t, y₁)) x₁ x₀ + lineIntegral2 F₁ F₂ (fun t => (x₀, t)) y₁ y₀

theorem rectBoundaryIntegral_eq (F₁ F₂ : ℝ → ℝ → ℝ) (x₀ x₁ y₀ y₁ : ℝ) :
    rectBoundaryIntegral F₁ F₂ x₀ x₁ y₀ y₁ =
      (∫ x in x₀..x₁, F₁ x y₀) + (∫ y in y₀..y₁, F₂ x₁ y) - (∫ x in x₀..x₁, F₁ x y₁) -
        ∫ y in y₀..y₁, F₂ x₀ y := by
  simp only [rectBoundaryIntegral, lineIntegral2, deriv_id'', deriv_const, mul_one, mul_zero,
    add_zero, zero_add]
  rw [intervalIntegral.integral_symm x₀ x₁, intervalIntegral.integral_symm y₀ y₁]
  ring

/-- **DLMF 1.6.43–1.6.44** (Green's theorem) for a rectangle `S = [x₀, x₁] × [y₀, y₁]` with
boundary `C` oriented anticlockwise and `F₁`, `F₂` continuously differentiable:
`∬_S (∂F₂/∂x − ∂F₁/∂y) dA = ∫_C F · ds = ∫_C F₁ dx + F₂ dy`. -/
theorem dlmf_1_6_44_rect {F₁ F₂ : ℝ → ℝ → ℝ} (hF₁ : ContDiff ℝ 1 (Function.uncurry F₁))
    (hF₂ : ContDiff ℝ 1 (Function.uncurry F₂)) (x₀ x₁ y₀ y₁ : ℝ) :
    ∫ x in x₀..x₁, ∫ y in y₀..y₁, (partialX F₂ x y - partialY F₁ x y) =
      rectBoundaryIntegral F₁ F₂ x₀ x₁ y₀ y₁ := by
  have hd₁ := hF₁.differentiable one_ne_zero
  have hd₂ := hF₂.differentiable one_ne_zero
  have key := MeasureTheory.integral2_divergence_prod_of_hasFDerivAt
    (Function.uncurry F₂) (fun p => -Function.uncurry F₁ p) (fderiv ℝ (Function.uncurry F₂))
    (fun p => -fderiv ℝ (Function.uncurry F₁) p) x₀ y₀ x₁ y₁
    hF₂.continuous.continuousOn hF₁.continuous.neg.continuousOn
    (fun p _ => (hd₂ p).hasFDerivAt) (fun p _ => (hd₁ p).hasFDerivAt.neg)
    (ContinuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)
      (((hF₂.continuous_fderiv one_ne_zero).clm_apply continuous_const).add
        (((hF₁.continuous_fderiv one_ne_zero).neg).clm_apply continuous_const)).continuousOn)
  have hint : ∀ x y, partialX F₂ x y - partialY F₁ x y =
      fderiv ℝ (Function.uncurry F₂) (x, y) (1, 0) +
        (-fderiv ℝ (Function.uncurry F₁) (x, y)) (0, 1) := fun x y => by
    rw [partialX_of_hasFDerivAt (hd₂ (x, y)).hasFDerivAt,
      partialY_of_hasFDerivAt (hd₁ (x, y)).hasFDerivAt, _root_.neg_apply,
      sub_eq_add_neg]
  simp_rw [hint]
  rw [key, rectBoundaryIntegral_eq]
  simp only [Function.uncurry_apply_pair, intervalIntegral.integral_neg]
  ring

/-- **DLMF §1.6(iv)**: the area of `S` from 1.6.44 with `F = −y i`, `x j` or `−½y i + ½x j`
(for a rectangle). -/
theorem dlmf_1_6_iv_area (x₀ x₁ y₀ y₁ : ℝ) :
    (x₁ - x₀) * (y₁ - y₀) = rectBoundaryIntegral (fun _ y => -y) (fun _ _ => 0) x₀ x₁ y₀ y₁ ∧
      (x₁ - x₀) * (y₁ - y₀) = rectBoundaryIntegral (fun _ _ => 0) (fun x _ => x) x₀ x₁ y₀ y₁ ∧
      (x₁ - x₀) * (y₁ - y₀) =
        rectBoundaryIntegral (fun _ y => -y / 2) (fun x _ => x / 2) x₀ x₁ y₀ y₁ := by
  have area : ∀ {F₁ F₂ : ℝ → ℝ → ℝ}, ContDiff ℝ 1 (Function.uncurry F₁) →
      ContDiff ℝ 1 (Function.uncurry F₂) → (∀ x y, partialX F₂ x y - partialY F₁ x y = 1) →
      (x₁ - x₀) * (y₁ - y₀) = rectBoundaryIntegral F₁ F₂ x₀ x₁ y₀ y₁ := fun h₁ h₂ h => by
    rw [← dlmf_1_6_44_rect h₁ h₂]
    simp [h]
    ring
  refine ⟨area ?_ ?_ ?_, area ?_ ?_ ?_, area ?_ ?_ ?_⟩
  · exact (contDiff_snd.neg : ContDiff ℝ 1 fun p : ℝ × ℝ => -p.2)
  · exact (contDiff_const : ContDiff ℝ 1 fun _ : ℝ × ℝ => (0 : ℝ))
  · intro x y
    simp [partialX, partialY]
  · exact (contDiff_const : ContDiff ℝ 1 fun _ : ℝ × ℝ => (0 : ℝ))
  · exact (contDiff_fst : ContDiff ℝ 1 fun p : ℝ × ℝ => p.1)
  · intro x y
    simp [partialX, partialY]
  · exact (contDiff_snd.neg.div_const 2 : ContDiff ℝ 1 fun p : ℝ × ℝ => -p.2 / 2)
  · exact (contDiff_fst.div_const 2 : ContDiff ℝ 1 fun p : ℝ × ℝ => p.1 / 2)
  · intro x y
    rw [show partialX (fun x (_ : ℝ) => x / 2) x y = 1 / 2 from
        ((hasDerivAt_id x).div_const 2).deriv,
      show partialY (fun (_ : ℝ) y => -y / 2) x y = -1 / 2 from
        ((hasDerivAt_id y).neg.div_const 2).deriv]
    norm_num

/-! ### Green's theorem (regions between two graphs) -/

theorem lineIntegral2_graph (F₁ F₂ : ℝ → ℝ → ℝ) (φ : ℝ → ℝ) (a b : ℝ) :
    lineIntegral2 F₁ F₂ (fun t => (t, φ t)) a b =
      ∫ t in a..b, (F₁ t (φ t) + F₂ t (φ t) * deriv φ t) := by
  simp [lineIntegral2]

theorem lineIntegral2_vertical (F₁ F₂ : ℝ → ℝ → ℝ) (x₀ c d : ℝ) :
    lineIntegral2 F₁ F₂ (fun t => (x₀, t)) c d = ∫ t in c..d, F₂ x₀ t := by
  simp [lineIntegral2]

/-- The line integral around the boundary of `D = {a ≤ x ≤ b, φ₁(x) ≤ y ≤ φ₂(x)}`, traversed
anticlockwise: along `y = φ₁(x)` from `a` to `b`, up `x = b`, back along `y = φ₂(x)`, down
`x = a`. -/
noncomputable def regionXBoundaryIntegral (F₁ F₂ : ℝ → ℝ → ℝ) (a b : ℝ) (φ₁ φ₂ : ℝ → ℝ) : ℝ :=
  lineIntegral2 F₁ F₂ (fun t => (t, φ₁ t)) a b +
    lineIntegral2 F₁ F₂ (fun t => (b, t)) (φ₁ b) (φ₂ b) +
    lineIntegral2 F₁ F₂ (fun t => (t, φ₂ t)) b a +
    lineIntegral2 F₁ F₂ (fun t => (a, t)) (φ₂ a) (φ₁ a)

/-- **DLMF 1.6.44** (Green's theorem) for a region `S = {a ≤ x ≤ b, φ₁(x) ≤ y ≤ φ₂(x)}` between
two `C¹` graphs, with boundary `C` oriented anticlockwise and `F₁`, `F₂` continuously
differentiable: `∬_S (∂F₂/∂x − ∂F₁/∂y) dA = ∫_C F₁ dx + F₂ dy`.  The `F₁` part is Fubini and
the fundamental theorem of calculus in `y`; the `F₂` part is Leibniz's rule 1.5.22 for
`H(x) = ∫_{φ₁(x)}^{φ₂(x)} F₂(x, y) dy`. -/
theorem dlmf_1_6_44_regionX {F₁ F₂ : ℝ → ℝ → ℝ} (hF₁ : ContDiff ℝ 1 (Function.uncurry F₁))
    (hF₂ : ContDiff ℝ 1 (Function.uncurry F₂)) {a b : ℝ} (hab : a ≤ b) {φ₁ φ₂ : ℝ → ℝ}
    (hφ₁ : ContDiff ℝ 1 φ₁) (hφ₂ : ContDiff ℝ 1 φ₂) (hle : ∀ x ∈ Set.Icc a b, φ₁ x ≤ φ₂ x) :
    ∫ p in regionX a b φ₁ φ₂, (partialX F₂ p.1 p.2 - partialY F₁ p.1 p.2) =
      regionXBoundaryIntegral F₁ F₂ a b φ₁ φ₂ := by
  obtain ⟨hc₁, -, hdy₁, -, hcY₁⟩ := (isContinuouslyDifferentiable_iff F₁).mpr hF₁
  obtain ⟨hc₂, hdx₂, -, hcX₂, -⟩ := (isContinuouslyDifferentiable_iff F₂).mpr hF₂
  have hφ₁c := hφ₁.continuous
  have hφ₂c := hφ₂.continuous
  have hdφ₁ : Continuous (deriv φ₁) := hφ₁.continuous_deriv le_rfl
  have hdφ₂ : Continuous (deriv φ₂) := hφ₂.continuous_deriv le_rfl
  -- continuity of compositions `(x, φ(x))`
  have hcomp : ∀ {G : ℝ → ℝ → ℝ}, Continuous (Function.uncurry G) → ∀ {φ : ℝ → ℝ},
      Continuous φ → Continuous fun x => G x (φ x) := fun hG _ hφ =>
    hG.comp (continuous_id.prodMk hφ)
  have hslice : ∀ {G : ℝ → ℝ → ℝ}, Continuous (Function.uncurry G) → ∀ x,
      Continuous (G x) := fun hG x => hG.comp (continuous_const.prodMk continuous_id)
  -- the double integral as a repeated integral
  have hcont : ContinuousOn (Function.uncurry fun x y => partialX F₂ x y - partialY F₁ x y)
      (regionX a b φ₁ φ₂) := (hcX₂.sub hcY₁).continuousOn
  rw [dlmf_1_5_31 (f := fun x y => partialX F₂ x y - partialY F₁ x y) hab hφ₁c hφ₂c hle hcont]
  -- inner integral of `∂F₁/∂y` by the fundamental theorem of calculus
  have hinner : ∀ x, ∫ y in φ₁ x..φ₂ x, (partialX F₂ x y - partialY F₁ x y) =
      (∫ y in φ₁ x..φ₂ x, partialX F₂ x y) - (F₁ x (φ₂ x) - F₁ x (φ₁ x)) := fun x => by
    have hft : ∫ y in φ₁ x..φ₂ x, partialY F₁ x y = F₁ x (φ₂ x) - F₁ x (φ₁ x) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => (hdy₁ x y).hasDerivAt)
        ((hslice hcY₁ x).intervalIntegrable _ _)
    rw [intervalIntegral.integral_sub ((hslice hcX₂ x).intervalIntegrable _ _)
      ((hslice hcY₁ x).intervalIntegrable _ _), hft]
  simp_rw [hinner]
  -- Leibniz's rule for `H(x) = ∫_{φ₁(x)}^{φ₂(x)} F₂(x, y) dy`
  set I : ℝ → ℝ := fun x => ∫ y in φ₁ x..φ₂ x, partialX F₂ x y with hI
  have hIc : Continuous I := by
    have hf : Continuous (Function.uncurry fun (x : ℝ) (y : ℝ) => partialX F₂ x y) := hcX₂
    have e : I = fun x => (∫ y in (0 : ℝ)..φ₂ x, partialX F₂ x y) -
        ∫ y in (0 : ℝ)..φ₁ x, partialX F₂ x y := by
      funext x
      rw [hI, intervalIntegral.integral_interval_sub_left
        ((hslice hcX₂ x).intervalIntegrable _ _) ((hslice hcX₂ x).intervalIntegrable _ _)]
    rw [e]
    exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hf hφ₂c).sub
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hf hφ₁c)
  have hH : ∀ x, HasDerivAt (fun x => ∫ y in φ₁ x..φ₂ x, F₂ x y)
      (F₂ x (φ₂ x) * deriv φ₂ x - F₂ x (φ₁ x) * deriv φ₁ x + I x) x := fun x =>
    hasDerivAt_integral_variable hc₂ hcX₂ isOpen_univ (fun x _ y => (hdx₂ x y).hasDerivAt)
      (Set.mem_univ x) ((hφ₁.differentiable one_ne_zero) x).hasDerivAt
      ((hφ₂.differentiable one_ne_zero) x).hasDerivAt
  have hP : Continuous fun x => F₂ x (φ₂ x) * deriv φ₂ x := (hcomp hc₂ hφ₂c).mul hdφ₂
  have hQ : Continuous fun x => F₂ x (φ₁ x) * deriv φ₁ x := (hcomp hc₂ hφ₁c).mul hdφ₁
  have hsum : Continuous fun x =>
      F₂ x (φ₂ x) * deriv φ₂ x - F₂ x (φ₁ x) * deriv φ₁ x + I x := (hP.sub hQ).add hIc
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := b)
    (fun x _ => hH x) (hsum.intervalIntegrable a b)
  have hPQ : Continuous fun x => F₂ x (φ₂ x) * deriv φ₂ x - F₂ x (φ₁ x) * deriv φ₁ x :=
    hP.sub hQ
  rw [intervalIntegral.integral_add (hPQ.intervalIntegrable _ _) (hIc.intervalIntegrable _ _),
    intervalIntegral.integral_sub (hP.intervalIntegrable _ _) (hQ.intervalIntegrable _ _)] at hFTC
  -- the boundary integral
  have hR₁ : Continuous fun x => F₁ x (φ₂ x) := hcomp hc₁ hφ₂c
  have hR₂ : Continuous fun x => F₁ x (φ₁ x) := hcomp hc₁ hφ₁c
  have hR₁₂ : Continuous fun x => F₁ x (φ₂ x) - F₁ x (φ₁ x) := hR₁.sub hR₂
  rw [regionXBoundaryIntegral, lineIntegral2_graph, lineIntegral2_graph, lineIntegral2_vertical,
    lineIntegral2_vertical, intervalIntegral.integral_add (hR₂.intervalIntegrable _ _)
      (hQ.intervalIntegrable _ _),
    intervalIntegral.integral_add (hR₁.intervalIntegrable _ _) (hP.intervalIntegrable _ _),
    intervalIntegral.integral_symm a b, intervalIntegral.integral_symm a b,
    intervalIntegral.integral_symm (φ₁ a) (φ₂ a),
    intervalIntegral.integral_sub (hIc.intervalIntegrable _ _) (hR₁₂.intervalIntegrable _ _),
    intervalIntegral.integral_sub (hR₁.intervalIntegrable _ _) (hR₂.intervalIntegrable _ _)]
  linarith

/-- **DLMF §1.6(iv)**: the area of a region between two `C¹` graphs from 1.6.44 with
`F = −y i`, `x j` or `−½y i + ½x j`. -/
theorem dlmf_1_6_iv_area_regionX {a b : ℝ} (hab : a ≤ b) {φ₁ φ₂ : ℝ → ℝ}
    (hφ₁ : ContDiff ℝ 1 φ₁) (hφ₂ : ContDiff ℝ 1 φ₂) (hle : ∀ x ∈ Set.Icc a b, φ₁ x ≤ φ₂ x) :
    MeasureTheory.volume.real (regionX a b φ₁ φ₂) =
        regionXBoundaryIntegral (fun _ y => -y) (fun _ _ => 0) a b φ₁ φ₂ ∧
      MeasureTheory.volume.real (regionX a b φ₁ φ₂) =
        regionXBoundaryIntegral (fun _ _ => 0) (fun x _ => x) a b φ₁ φ₂ ∧
      MeasureTheory.volume.real (regionX a b φ₁ φ₂) =
        regionXBoundaryIntegral (fun _ y => -y / 2) (fun x _ => x / 2) a b φ₁ φ₂ := by
  have area : ∀ {F₁ F₂ : ℝ → ℝ → ℝ}, ContDiff ℝ 1 (Function.uncurry F₁) →
      ContDiff ℝ 1 (Function.uncurry F₂) → (∀ x y, partialX F₂ x y - partialY F₁ x y = 1) →
      MeasureTheory.volume.real (regionX a b φ₁ φ₂) =
        regionXBoundaryIntegral F₁ F₂ a b φ₁ φ₂ := fun h₁ h₂ h => by
    rw [← dlmf_1_6_44_regionX h₁ h₂ hab hφ₁ hφ₂ hle]
    simp [h]
  refine ⟨area ?_ ?_ ?_, area ?_ ?_ ?_, area ?_ ?_ ?_⟩
  · exact (contDiff_snd.neg : ContDiff ℝ 1 fun p : ℝ × ℝ => -p.2)
  · exact (contDiff_const : ContDiff ℝ 1 fun _ : ℝ × ℝ => (0 : ℝ))
  · intro x y
    simp [partialX, partialY]
  · exact (contDiff_const : ContDiff ℝ 1 fun _ : ℝ × ℝ => (0 : ℝ))
  · exact (contDiff_fst : ContDiff ℝ 1 fun p : ℝ × ℝ => p.1)
  · intro x y
    simp [partialX, partialY]
  · exact (contDiff_snd.neg.div_const 2 : ContDiff ℝ 1 fun p : ℝ × ℝ => -p.2 / 2)
  · exact (contDiff_fst.div_const 2 : ContDiff ℝ 1 fun p : ℝ × ℝ => p.1 / 2)
  · intro x y
    rw [show partialX (fun x (_ : ℝ) => x / 2) x y = 1 / 2 from
        ((hasDerivAt_id x).div_const 2).deriv,
      show partialY (fun (_ : ℝ) y => -y / 2) x y = -1 / 2 from
        ((hasDerivAt_id y).neg.div_const 2).deriv]
    norm_num

end Paths

/-! ### Green's theorem (general closed curves) -/

/-- A plane path `c : ℝ → ℝ × ℝ` viewed as a path in `ℂ`. -/
def toComplexPath (c : ℝ → ℝ × ℝ) : ℝ → ℂ := fun t => ⟨(c t).1, (c t).2⟩

/-- **DLMF §1.6(iv)**: a simple closed plane curve (`c` one-to-one on `[a, b)`, `c(a) = c(b)`). -/
def IsSimpleClosedPlanePath (c : ℝ → ℝ × ℝ) (a b : ℝ) : Prop :=
  Set.InjOn c (Set.Ico a b) ∧ c a = c b

/-- The region `S` bounded by a closed plane curve: the union of the bounded connected
components of the complement of its image (for a simple closed curve, the unique bounded
component, by the Jordan curve theorem `JordanCurve.IsJordanCurve.jordanInterior_eq`). -/
def planeInterior (c : ℝ → ℝ × ℝ) (a b : ℝ) : Set (ℝ × ℝ) :=
  {q | q ∉ c '' Set.Icc a b ∧ Bornology.IsBounded (connectedComponentIn (c '' Set.Icc a b)ᶜ q)}

theorem equivRealProdCLM_toComplexPath (c : ℝ → ℝ × ℝ) (t : ℝ) :
    Complex.equivRealProdCLM (toComplexPath c t) = c t := rfl

theorem image_equivRealProdCLM_toComplexPath (c : ℝ → ℝ × ℝ) (a b : ℝ) :
    Complex.equivRealProdCLM '' (toComplexPath c '' Set.Icc a b) = c '' Set.Icc a b := by
  rw [Set.image_image]
  rfl

theorem isBounded_image_equivRealProdCLM_iff (S : Set ℂ) :
    Bornology.IsBounded (Complex.equivRealProdCLM '' S) ↔ Bornology.IsBounded S := by
  constructor
  · intro hS
    have := (Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ).lipschitzWith.isBounded_image hS
    rw [Set.image_image] at this
    have heq : (fun x => (Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ)
        (Complex.equivRealProdCLM x)) '' S = S := by
      rw [show (fun x => (Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ)
        (Complex.equivRealProdCLM x)) = fun x => x from
        funext fun x => Complex.equivRealProdCLM.symm_apply_apply x, Set.image_id']
    rwa [heq] at this
  · exact fun hS => (Complex.equivRealProdCLM : ℂ →L[ℝ] ℝ × ℝ).lipschitzWith.isBounded_image hS

/-- Boundedness of complementary components is preserved by `ℂ ≃ ℝ × ℝ`. -/
theorem isBounded_connectedComponentIn_iff {c : ℝ → ℝ × ℝ} {a b : ℝ} {p : ℂ}
    (hp : p ∉ toComplexPath c '' Set.Icc a b) :
    Bornology.IsBounded (connectedComponentIn (c '' Set.Icc a b)ᶜ (Complex.equivRealProdCLM p)) ↔
      Bornology.IsBounded (connectedComponentIn (toComplexPath c '' Set.Icc a b)ᶜ p) := by
  have := Complex.equivRealProdCLM.toHomeomorph.image_connectedComponentIn
    (s := (toComplexPath c '' Set.Icc a b)ᶜ) hp
  rw [ContinuousLinearEquiv.coe_toHomeomorph, Set.image_compl_eq Complex.equivRealProdCLM.bijective,
    image_equivRealProdCLM_toComplexPath] at this
  rw [← this, isBounded_image_equivRealProdCLM_iff]

/-- The region bounded by `c` corresponds to the interior of the complex path. -/
theorem preimage_planeInterior (c : ℝ → ℝ × ℝ) (a b : ℝ) :
    Complex.measurableEquivRealProd ⁻¹' planeInterior c a b =
      JordanCurve.jordanInterior (toComplexPath c) a b := by
  ext p
  have hmem : Complex.measurableEquivRealProd p ∉ c '' Set.Icc a b ↔
      p ∉ toComplexPath c '' Set.Icc a b := by
    rw [← image_equivRealProdCLM_toComplexPath,
      show Complex.measurableEquivRealProd p = Complex.equivRealProdCLM p from rfl]
    exact not_congr Complex.equivRealProdCLM.injective.mem_set_image
  constructor
  · rintro ⟨h1, h2⟩
    have h1' := hmem.mp h1
    exact ⟨h1', (isBounded_connectedComponentIn_iff h1').mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨hmem.mpr h1, (isBounded_connectedComponentIn_iff h1).mpr h2⟩

theorem planeInterior_eq_image (c : ℝ → ℝ × ℝ) (a b : ℝ) :
    planeInterior c a b =
      Complex.equivRealProdCLM '' JordanCurve.jordanInterior (toComplexPath c) a b := by
  rw [← preimage_planeInterior]
  exact (Set.image_preimage_eq _ Complex.equivRealProdCLM.surjective).symm

/-- The partial derivatives of `F` are the real derivatives of `z ↦ F (Re z) (Im z)` in the
directions `1` and `i`. -/
theorem fderiv_comp_equivRealProd {F : ℝ → ℝ → ℝ} (hF : ContDiff ℝ 1 (Function.uncurry F))
    (p : ℂ) :
    fderiv ℝ (fun z : ℂ => F z.re z.im) p 1 = partialX F p.re p.im ∧
      fderiv ℝ (fun z : ℂ => F z.re z.im) p Complex.I = partialY F p.re p.im := by
  have hd := (hF.differentiable one_ne_zero (p.re, p.im)).hasFDerivAt
  have h : HasFDerivAt (fun z : ℂ => F z.re z.im)
      ((fderiv ℝ (Function.uncurry F) (p.re, p.im)).comp
        (Complex.equivRealProdCLM : ℂ →L[ℝ] ℝ × ℝ)) p := by
    have h0 := hd.comp p Complex.equivRealProdCLM.hasFDerivAt
    exact h0
  rw [h.fderiv, partialX_of_hasFDerivAt hd, partialY_of_hasFDerivAt hd]
  constructor
  · show fderiv ℝ (Function.uncurry F) (p.re, p.im) ((1 : ℂ).re, (1 : ℂ).im) = _
    rw [Complex.one_re, Complex.one_im]
  · show fderiv ℝ (Function.uncurry F) (p.re, p.im) (Complex.I.re, Complex.I.im) = _
    rw [Complex.I_re, Complex.I_im]

/-- Green's theorem for a closed piecewise-`C¹` plane curve whose winding number is a constant
`w` on the region `S` it bounds (`F₁`, `F₂` globally `C¹`):
`∫_C F₁ dx + F₂ dy = w ∬_S (∂F₂/∂x − ∂F₁/∂y) dA`. -/
theorem lineIntegral2_eq_mul_setIntegral {c : ℝ → ℝ × ℝ} {a b : ℝ}
    (P : JordanCurve.ClosedPiecewiseC1 (toComplexPath c) a b) {w : ℤ}
    (hw : ∀ p ∈ JordanCurve.jordanInterior (toComplexPath c) a b, P.windingNumber p = w)
    {F₁ F₂ : ℝ → ℝ → ℝ} (hF₁ : ContDiff ℝ 1 (Function.uncurry F₁))
    (hF₂ : ContDiff ℝ 1 (Function.uncurry F₂)) :
    lineIntegral2 F₁ F₂ c a b =
      (w : ℝ) * ∫ q in planeInterior c a b, (partialX F₂ q.1 q.2 - partialY F₁ q.1 q.2) := by
  have hu : ContDiff ℝ 1 fun z : ℂ => F₁ z.re z.im := hF₁.comp Complex.equivRealProdCLM.contDiff
  have hv : ContDiff ℝ 1 fun z : ℂ => F₂ z.re z.im := hF₂.comp Complex.equivRealProdCLM.contDiff
  have hL : lineIntegral2 F₁ F₂ c a b = JordanCurve.lineIntegralRe (fun z : ℂ => F₁ z.re z.im)
    (fun z : ℂ => F₂ z.re z.im) (toComplexPath c) a b := rfl
  rw [hL, P.lineIntegralRe_eq_mul_setIntegral_jordanInterior hw hu hv, ← preimage_planeInterior,
    ← Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
      Complex.measurableEquivRealProd.measurableEmbedding]
  congr 1
  refine setIntegral_congr_fun ?_ fun p _ => ?_
  · rw [preimage_planeInterior]
    exact (JordanCurve.isOpen_jordanInterior P.continuousOn).measurableSet
  · rw [(fderiv_comp_equivRealProd hF₂ p).1, (fderiv_comp_equivRealProd hF₁ p).2]
    rfl

/-- **DLMF 1.6.43–1.6.44** (Green's theorem) for a positively oriented closed piecewise-`C¹`
plane curve `C` (parametrized by `c` on `[a, b]`, winding number `1` on the region
`S = planeInterior c a b` it bounds) and `F₁`, `F₂` continuously differentiable:
`∫_C F · ds = ∫_C F₁ dx + F₂ dy = ∬_S (∂F₂/∂x − ∂F₁/∂y) dA`.  Proof: Cauchy–Pompeiu and Fubini
give `∮ (u − i v) dz = 2i ∫ ∂̄(u − i v) · W dA` for the winding number `W`
(`JordanCurve.ClosedPiecewiseC1.contourIntegral_eq_integral_dbar`); `W = 1` on `S`, `W = 0` on the
unbounded components and the curve is null.  See `dlmf_1_6_44_nhds` for fields that are only
`C¹` near `S ∪ C`, and `dlmf_1_6_44_simple` for simple closed curves without an orientation
hypothesis. -/
theorem dlmf_1_6_44 {c : ℝ → ℝ × ℝ} {a b : ℝ}
    (P : JordanCurve.ClosedPiecewiseC1 (toComplexPath c) a b) (hpos : P.IsPositivelyOriented)
    {F₁ F₂ : ℝ → ℝ → ℝ} (hF₁ : ContDiff ℝ 1 (Function.uncurry F₁))
    (hF₂ : ContDiff ℝ 1 (Function.uncurry F₂)) :
    lineIntegral2 F₁ F₂ c a b =
      ∫ q in planeInterior c a b, (partialX F₂ q.1 q.2 - partialY F₁ q.1 q.2) := by
  rw [lineIntegral2_eq_mul_setIntegral P (w := 1) hpos hF₁ hF₂, Int.cast_one, one_mul]

theorem isOpen_planeInterior {c : ℝ → ℝ × ℝ} {a b : ℝ}
    (P : JordanCurve.ClosedPiecewiseC1 (toComplexPath c) a b) : IsOpen (planeInterior c a b) := by
  rw [planeInterior_eq_image, ← ContinuousLinearEquiv.coe_toHomeomorph]
  exact Complex.equivRealProdCLM.toHomeomorph.isOpenMap _
    (JordanCurve.isOpen_jordanInterior P.continuousOn)

/-- `S ∪ ∂S` is compact, and the closure of `S` lies in `S ∪ C`. -/
theorem isCompact_closure_planeInterior_union {c : ℝ → ℝ × ℝ} {a b : ℝ}
    (P : JordanCurve.ClosedPiecewiseC1 (toComplexPath c) a b) :
    IsCompact (closure (planeInterior c a b) ∪ c '' Set.Icc a b) ∧
      closure (planeInterior c a b) ⊆ planeInterior c a b ∪ c '' Set.Icc a b := by
  set e := Complex.equivRealProdCLM.toHomeomorph with he
  have hS : planeInterior c a b = e '' JordanCurve.jordanInterior (toComplexPath c) a b := by
    rw [planeInterior_eq_image, he, ContinuousLinearEquiv.coe_toHomeomorph]
  have hC : c '' Set.Icc a b = e '' P.curve := by
    rw [← image_equivRealProdCLM_toComplexPath, he, ContinuousLinearEquiv.coe_toHomeomorph]
    rfl
  obtain ⟨R', hR'⟩ := P.isCompact_curve.isBounded.subset_closedBall 0
  set R := max R' 0
  have hsub : P.curve ⊆ Metric.closedBall 0 R :=
    hR'.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  have hbd := JordanCurve.jordanInterior_subset_closedBall (le_max_right R' 0) hsub
  have hcomp : IsCompact (closure (JordanCurve.jordanInterior (toComplexPath c) a b)) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure
      (Metric.isBounded_closedBall.subset hbd).closure
  rw [hS, hC, ← e.image_closure, ← Set.image_union]
  refine ⟨(hcomp.union P.isCompact_curve).image e.continuous, ?_⟩
  rw [← Set.image_union]
  exact Set.image_mono (JordanCurve.closure_jordanInterior_subset P.continuousOn)

/-- A function `C¹` on an open set `U ⊇ K` (`K` compact) agrees near `K` with a globally `C¹`
function (multiply by a smooth cutoff). -/
theorem exists_contDiff_eqOn_nhds {F : ℝ → ℝ → ℝ} {U K : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U) (hF : ContDiffOn ℝ 1 (Function.uncurry F) U) :
    ∃ F' : ℝ → ℝ → ℝ, ContDiff ℝ 1 (Function.uncurry F') ∧
      ∃ V : Set (ℝ × ℝ), IsOpen V ∧ K ⊆ V ∧ ∀ q ∈ V, F' q.1 q.2 = F q.1 q.2 := by
  obtain ⟨V₂, hV₂o, hKV₂, hV₂U, -⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨V₁, hV₁o, hKV₁, hV₁V₂, -⟩ := exists_open_between_and_isCompact_closure hK hV₂o hKV₂
  obtain ⟨χ, hχ, -, hχs, hχ1⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := 1) hV₂o isClosed_closure hV₁V₂
  refine ⟨fun x y => χ (x, y) * F x y, ?_, V₁, hV₁o, hKV₁, fun q hq => ?_⟩
  · have heq : Function.uncurry (fun x y => χ (x, y) * F x y) =
        fun q => χ q * Function.uncurry F q := rfl
    rw [heq, contDiff_iff_contDiffAt]
    intro q
    by_cases hq : q ∈ U
    · exact hχ.contDiffAt.mul (hF.contDiffAt (hU.mem_nhds hq))
    · have hqs : q ∉ tsupport χ := by
        show q ∉ closure (Function.support χ)
        rw [hχs]
        exact fun h => hq (hV₂U h)
      have h0 : χ =ᶠ[nhds q] 0 := notMem_tsupport_iff_eventuallyEq.mp hqs
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [h0] with r hr
      simp [hr]
  · have : χ q = 1 := (hχ1 q).mp (subset_closure hq)
    simp [this]

/-- **DLMF 1.6.44** with an arbitrary constant winding number `w` on `S`, for fields that are
continuously differentiable on an open set `U ⊇ S ∪ C`. -/
theorem lineIntegral2_eq_mul_setIntegral_of_contDiffOn {c : ℝ → ℝ × ℝ} {a b : ℝ}
    (P : JordanCurve.ClosedPiecewiseC1 (toComplexPath c) a b) {w : ℤ}
    (hw : ∀ p ∈ JordanCurve.jordanInterior (toComplexPath c) a b, P.windingNumber p = w)
    {F₁ F₂ : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hSU : planeInterior c a b ∪ c '' Set.Icc a b ⊆ U)
    (hF₁ : ContDiffOn ℝ 1 (Function.uncurry F₁) U)
    (hF₂ : ContDiffOn ℝ 1 (Function.uncurry F₂) U) :
    lineIntegral2 F₁ F₂ c a b =
      (w : ℝ) * ∫ q in planeInterior c a b, (partialX F₂ q.1 q.2 - partialY F₁ q.1 q.2) := by
  obtain ⟨hK, hcl⟩ := isCompact_closure_planeInterior_union P
  set K := closure (planeInterior c a b) ∪ c '' Set.Icc a b with hKdef
  have hKU : K ⊆ U := fun q hq => hSU (hq.elim (fun h => hcl h) fun h => Or.inr h)
  obtain ⟨G₁, hG₁, V₁, hV₁, hKV₁, hGF₁⟩ := exists_contDiff_eqOn_nhds hU hK hKU hF₁
  obtain ⟨G₂, hG₂, V₂, hV₂, hKV₂, hGF₂⟩ := exists_contDiff_eqOn_nhds hU hK hKU hF₂
  have hline : lineIntegral2 F₁ F₂ c a b = lineIntegral2 G₁ G₂ c a b := by
    unfold lineIntegral2
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le P.a_le_b] at ht
    have hct : c t ∈ K := Or.inr ⟨t, ht, rfl⟩
    rw [← hGF₁ (c t) (hKV₁ hct), ← hGF₂ (c t) (hKV₂ hct)]
  rw [hline, lineIntegral2_eq_mul_setIntegral P hw hG₁ hG₂]
  congr 1
  refine setIntegral_congr_fun (isOpen_planeInterior P).measurableSet fun q hq => ?_
  have hqK : q ∈ K := Or.inl (subset_closure hq)
  have hx : partialX G₂ q.1 q.2 = partialX F₂ q.1 q.2 := by
    unfold partialX
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [(Continuous.tendsto (f := fun t : ℝ => (t, q.2)) (by fun_prop) q.1).eventually
      (hV₂.mem_nhds (hKV₂ hqK))] with t ht
    exact hGF₂ _ ht
  have hy : partialY G₁ q.1 q.2 = partialY F₁ q.1 q.2 := by
    unfold partialY
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [(Continuous.tendsto (f := fun t : ℝ => (q.1, t)) (by fun_prop) q.2).eventually
      (hV₁.mem_nhds (hKV₁ hqK))] with t ht
    exact hGF₁ _ ht
  rw [hx, hy]

/-- **DLMF 1.6.43–1.6.44** (Green's theorem) as stated: `C` positively oriented closed
piecewise-`C¹`, `F₁`, `F₂` continuously differentiable on an open set `U` containing `S ∪ ∂S`
(the open-neighbourhood reading of "continuously differentiable on `S ∪ ∂S`"). -/
theorem dlmf_1_6_44_nhds {c : ℝ → ℝ × ℝ} {a b : ℝ}
    (P : JordanCurve.ClosedPiecewiseC1 (toComplexPath c) a b) (hpos : P.IsPositivelyOriented)
    {F₁ F₂ : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hSU : planeInterior c a b ∪ c '' Set.Icc a b ⊆ U)
    (hF₁ : ContDiffOn ℝ 1 (Function.uncurry F₁) U)
    (hF₂ : ContDiffOn ℝ 1 (Function.uncurry F₂) U) :
    lineIntegral2 F₁ F₂ c a b =
      ∫ q in planeInterior c a b, (partialX F₂ q.1 q.2 - partialY F₁ q.1 q.2) := by
  rw [lineIntegral2_eq_mul_setIntegral_of_contDiffOn P (w := 1) hpos hU hSU hF₁ hF₂,
    Int.cast_one, one_mul]

theorem injOn_toComplexPath {c : ℝ → ℝ × ℝ} {a b : ℝ} (hc : IsSimpleClosedPlanePath c a b) :
    Set.InjOn (toComplexPath c) (Set.Ico a b) := fun _ hs _ ht hst =>
  hc.1 hs ht (Prod.ext (congrArg Complex.re hst) (congrArg Complex.im hst))

theorem isJordanCurve_toComplexPath {c : ℝ → ℝ × ℝ} {a b : ℝ} (hab : a < b)
    (hc : IsSimpleClosedPlanePath c a b) (P : JordanCurve.ClosedPiecewiseC1 (toComplexPath c) a b) :
    JordanCurve.IsJordanCurve (toComplexPath c) a b :=
  P.isJordanCurve hab (injOn_toComplexPath hc)

/-- For a simple closed curve the region `S` is nonempty and connected (Jordan curve theorem). -/
theorem planeInterior_nonempty_isConnected {c : ℝ → ℝ × ℝ} {a b : ℝ} (hab : a < b)
    (hc : IsSimpleClosedPlanePath c a b) (P : JordanCurve.ClosedPiecewiseC1 (toComplexPath c) a b) :
    (planeInterior c a b).Nonempty ∧ IsConnected (planeInterior c a b) := by
  have h := isJordanCurve_toComplexPath hab hc P
  rw [planeInterior_eq_image]
  obtain ⟨p, hp⟩ := h.exists_mem_jordanInterior
  exact ⟨⟨_, p, hp, rfl⟩,
    h.isConnected_jordanInterior.image _ Complex.equivRealProdCLM.continuous.continuousOn⟩

/-- **DLMF 1.6.44** for a simple closed piecewise-`C¹` curve, with no orientation hypothesis:
the winding number on `S` is `1` (positive orientation, and Green's formula holds) or `−1`
(negative orientation, and the formula holds with a minus sign).  Fields are `C¹` on an open
`U ⊇ S ∪ C`. -/
theorem dlmf_1_6_44_simple {c : ℝ → ℝ × ℝ} {a b : ℝ} (hab : a < b)
    (hc : IsSimpleClosedPlanePath c a b) (P : JordanCurve.ClosedPiecewiseC1 (toComplexPath c) a b)
    {F₁ F₂ : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hSU : planeInterior c a b ∪ c '' Set.Icc a b ⊆ U)
    (hF₁ : ContDiffOn ℝ 1 (Function.uncurry F₁) U)
    (hF₂ : ContDiffOn ℝ 1 (Function.uncurry F₂) U) :
    (P.IsPositivelyOriented ∧ lineIntegral2 F₁ F₂ c a b =
        ∫ q in planeInterior c a b, (partialX F₂ q.1 q.2 - partialY F₁ q.1 q.2)) ∨
      (P.IsNegativelyOriented ∧ lineIntegral2 F₁ F₂ c a b =
        -∫ q in planeInterior c a b, (partialX F₂ q.1 q.2 - partialY F₁ q.1 q.2)) := by
  rcases P.isPositivelyOriented_or_isNegativelyOriented (isJordanCurve_toComplexPath hab hc P)
    with hpos | hneg
  · refine Or.inl ⟨hpos, ?_⟩
    rw [lineIntegral2_eq_mul_setIntegral_of_contDiffOn P (w := 1) hpos hU hSU hF₁ hF₂,
      Int.cast_one, one_mul]
  · refine Or.inr ⟨hneg, ?_⟩
    rw [lineIntegral2_eq_mul_setIntegral_of_contDiffOn P (w := -1) hneg hU hSU hF₁ hF₂]
    push_cast
    ring

/-- `d/dx f(d − x) = −f'(d − x)`, with no differentiability hypothesis. -/
theorem deriv_comp_const_sub_eq (f : ℝ → ℝ) (d x : ℝ) :
    deriv (fun s => f (d - s)) x = -deriv f (d - x) := by
  have h : (fun s => f (d - s)) = fun s => (fun y => f (d + y)) (-s) := by
    funext s
    rw [sub_eq_add_neg]
  rw [h, deriv_comp_neg (fun y => f (d + y)), deriv_comp_const_add, ← sub_eq_add_neg]

/-- Traversing the curve backwards (`t ↦ c(a + b − t)`) negates the line integral. -/
theorem lineIntegral2_reverse (F₁ F₂ : ℝ → ℝ → ℝ) (c : ℝ → ℝ × ℝ) (a b : ℝ) :
    lineIntegral2 F₁ F₂ (fun t => c (a + b - t)) a b = -lineIntegral2 F₁ F₂ c a b := by
  unfold lineIntegral2
  have h1 : ∀ t, deriv (fun s => (c (a + b - s)).1) t = -deriv (fun s => (c s).1) (a + b - t) :=
    fun t => deriv_comp_const_sub_eq (fun s => (c s).1) (a + b) t
  have h2 : ∀ t, deriv (fun s => (c (a + b - s)).2) t = -deriv (fun s => (c s).2) (a + b - t) :=
    fun t => deriv_comp_const_sub_eq (fun s => (c s).2) (a + b) t
  simp only [h1, h2, mul_neg, ← neg_add, intervalIntegral.integral_neg]
  have hsub := intervalIntegral.integral_comp_sub_left (a := a) (b := b)
    (fun t => F₁ (c t).1 (c t).2 * deriv (fun s => (c s).1) t +
      F₂ (c t).1 (c t).2 * deriv (fun s => (c s).2) t) (a + b)
  rw [hsub, add_sub_cancel_right, add_sub_cancel_left]

/-- The reversed curve bounds the same region. -/
theorem planeInterior_reverse (c : ℝ → ℝ × ℝ) (a b : ℝ) :
    planeInterior (fun t => c (a + b - t)) a b = planeInterior c a b := by
  have h : (fun t => c (a + b - t)) '' Set.Icc a b = c '' Set.Icc a b := by
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨a + b - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨a + b - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, by simp⟩
  simp only [planeInterior, h]

/-- **DLMF 1.6.44** for every simple closed piecewise-`C¹` curve, traversed in its positive
direction: either `c` itself or its reversal `t ↦ c(a + b − t)` satisfies Green's formula over
the region `S` both bound. -/
theorem dlmf_1_6_44_simple_or_reverse {c : ℝ → ℝ × ℝ} {a b : ℝ} (hab : a < b)
    (hc : IsSimpleClosedPlanePath c a b) (P : JordanCurve.ClosedPiecewiseC1 (toComplexPath c) a b)
    {F₁ F₂ : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hSU : planeInterior c a b ∪ c '' Set.Icc a b ⊆ U)
    (hF₁ : ContDiffOn ℝ 1 (Function.uncurry F₁) U)
    (hF₂ : ContDiffOn ℝ 1 (Function.uncurry F₂) U) :
    lineIntegral2 F₁ F₂ c a b =
        ∫ q in planeInterior c a b, (partialX F₂ q.1 q.2 - partialY F₁ q.1 q.2) ∨
      lineIntegral2 F₁ F₂ (fun t => c (a + b - t)) a b =
        ∫ q in planeInterior (fun t => c (a + b - t)) a b,
          (partialX F₂ q.1 q.2 - partialY F₁ q.1 q.2) := by
  rcases dlmf_1_6_44_simple hab hc P hU hSU hF₁ hF₂ with ⟨-, h⟩ | ⟨-, h⟩
  · exact Or.inl h
  · refine Or.inr ?_
    rw [lineIntegral2_reverse, h, planeInterior_reverse, neg_neg]

/-- **DLMF §1.6(iv)**: the area of the region bounded by a positively oriented closed
piecewise-`C¹` curve, from 1.6.44 with `F = −y i`, `x j` or `−½y i + ½x j`. -/
theorem dlmf_1_6_iv_area_general {c : ℝ → ℝ × ℝ} {a b : ℝ}
    (P : JordanCurve.ClosedPiecewiseC1 (toComplexPath c) a b) (hpos : P.IsPositivelyOriented) :
    MeasureTheory.volume.real (planeInterior c a b) =
        lineIntegral2 (fun _ y => -y) (fun _ _ => 0) c a b ∧
      MeasureTheory.volume.real (planeInterior c a b) =
        lineIntegral2 (fun _ _ => 0) (fun x _ => x) c a b ∧
      MeasureTheory.volume.real (planeInterior c a b) =
        lineIntegral2 (fun _ y => -y / 2) (fun x _ => x / 2) c a b := by
  have area : ∀ {F₁ F₂ : ℝ → ℝ → ℝ}, ContDiff ℝ 1 (Function.uncurry F₁) →
      ContDiff ℝ 1 (Function.uncurry F₂) → (∀ x y, partialX F₂ x y - partialY F₁ x y = 1) →
      MeasureTheory.volume.real (planeInterior c a b) = lineIntegral2 F₁ F₂ c a b :=
    fun h₁ h₂ h => by
      rw [dlmf_1_6_44 P hpos h₁ h₂]
      simp [h]
  refine ⟨area ?_ ?_ ?_, area ?_ ?_ ?_, area ?_ ?_ ?_⟩
  · exact (contDiff_snd.neg : ContDiff ℝ 1 fun p : ℝ × ℝ => -p.2)
  · exact (contDiff_const : ContDiff ℝ 1 fun _ : ℝ × ℝ => (0 : ℝ))
  · intro x y
    simp [partialX, partialY]
  · exact (contDiff_const : ContDiff ℝ 1 fun _ : ℝ × ℝ => (0 : ℝ))
  · exact (contDiff_fst : ContDiff ℝ 1 fun p : ℝ × ℝ => p.1)
  · intro x y
    simp [partialX, partialY]
  · exact (contDiff_snd.neg.div_const 2 : ContDiff ℝ 1 fun p : ℝ × ℝ => -p.2 / 2)
  · exact (contDiff_fst.div_const 2 : ContDiff ℝ 1 fun p : ℝ × ℝ => p.1 / 2)
  · intro x y
    simp [partialX, partialY]
    ring

end Azurite.DLMF
