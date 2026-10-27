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
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Inv

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

end Azurite.DLMF
