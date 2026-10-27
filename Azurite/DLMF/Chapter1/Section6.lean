/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

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

end Azurite.DLMF
