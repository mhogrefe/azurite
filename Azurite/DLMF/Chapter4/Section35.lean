/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section21
import Azurite.DLMF.Chapter4.Section28

/-!
# DLMF §4.35 Identities (hyperbolic functions)

## §4.35(i) Addition Formulas

* 4.35.1–4.35.4: `dlmf_4_35_1`, …, `dlmf_4_35_4` (each `±` as two conjuncts; `tanh`, `coth`
  where the needed `cosh`, `sinh` are nonzero; `coth` is `cothC` of §4.28).
* 4.35.5–4.35.10: `dlmf_4_35_5`, …, `dlmf_4_35_10`.

## §4.35(ii) Squares and Products

* 4.35.11–4.35.19: `dlmf_4_35_11`, …, `dlmf_4_35_19` (4.35.12, 4.35.13 where `cosh z`, `sinh z`
  are nonzero).

## §4.35(iii) Multiples of the Argument

* 4.35.20–4.35.22 ("the square roots assume their principal value on the positive real axis, and
  are determined by continuity elsewhere"): `dlmf_4_35_20`, `dlmf_4_35_21`, `dlmf_4_35_22`. Each
  states the squared identity for all `z`, the principal root on the positive real axis, and
  that a continuous branch of the root on a connected set avoiding the zeros of the radicand,
  principal at one positive point, is the left-hand side (`branch_eq_of_sq`).
* 4.35.23–4.35.33: `dlmf_4_35_23`, …, `dlmf_4_35_33` (`tanh` forms where `cosh z ≠ 0`).

## §4.35(iv) Real and Imaginary Parts; Moduli

* 4.35.34–4.35.40 (`z = x + iy`): `dlmf_4_35_34`, …, `dlmf_4_35_40`. The `tanh`, `coth` and
  modulus formulas come from 4.21.39–4.21.43 at `iz = −y + ix`; they hold everywhere in Lean's
  convention (at a pole both sides are `0`).
-/

open Complex
open scoped Real

namespace Azurite.DLMF

/-! ### §4.35(i) Addition Formulas -/

/-- **DLMF 4.35.1**: `sinh(u ± v) = sinh u cosh v ± cosh u sinh v`. -/
theorem dlmf_4_35_1 (u v : ℂ) :
    sinh (u + v) = sinh u * cosh v + cosh u * sinh v ∧
      sinh (u - v) = sinh u * cosh v - cosh u * sinh v :=
  ⟨sinh_add u v, sinh_sub u v⟩

/-- **DLMF 4.35.2**: `cosh(u ± v) = cosh u cosh v ± sinh u sinh v`. -/
theorem dlmf_4_35_2 (u v : ℂ) :
    cosh (u + v) = cosh u * cosh v + sinh u * sinh v ∧
      cosh (u - v) = cosh u * cosh v - sinh u * sinh v :=
  ⟨cosh_add u v, cosh_sub u v⟩

/-- **DLMF 4.35.3**: `tanh(u ± v) = (tanh u ± tanh v)/(1 ± tanh u tanh v)`
(`cosh u, cosh v ≠ 0`). -/
theorem dlmf_4_35_3 {u v : ℂ} (hu : cosh u ≠ 0) (hv : cosh v ≠ 0) :
    tanh (u + v) = (tanh u + tanh v) / (1 + tanh u * tanh v) ∧
      tanh (u - v) = (tanh u - tanh v) / (1 - tanh u * tanh v) := by
  have huv := mul_ne_zero hu hv
  simp only [tanh_eq_sinh_div_cosh, sinh_add, cosh_add, sinh_sub, cosh_sub]
  constructor
  · rw [show sinh u / cosh u + sinh v / cosh v =
        (sinh u * cosh v + cosh u * sinh v) / (cosh u * cosh v) by field_simp,
      show 1 + sinh u / cosh u * (sinh v / cosh v) = (cosh u * cosh v + sinh u * sinh v) /
        (cosh u * cosh v) by field_simp, div_div_div_cancel_right₀ huv]
  · rw [show sinh u / cosh u - sinh v / cosh v =
        (sinh u * cosh v - cosh u * sinh v) / (cosh u * cosh v) by field_simp,
      show 1 - sinh u / cosh u * (sinh v / cosh v) = (cosh u * cosh v - sinh u * sinh v) /
        (cosh u * cosh v) by field_simp, div_div_div_cancel_right₀ huv]

/-- **DLMF 4.35.4**: `coth(u ± v) = (±coth u coth v + 1)/(coth u ± coth v)`
(`sinh u, sinh v ≠ 0`). -/
theorem dlmf_4_35_4 {u v : ℂ} (hu : sinh u ≠ 0) (hv : sinh v ≠ 0) :
    cothC (u + v) = (cothC u * cothC v + 1) / (cothC u + cothC v) ∧
      cothC (u - v) = (-(cothC u * cothC v) + 1) / (cothC u - cothC v) := by
  have huv := mul_ne_zero hu hv
  simp only [cothC_eq_cosh_div_sinh, sinh_add, cosh_add, sinh_sub, cosh_sub]
  constructor
  · rw [show cosh u / sinh u * (cosh v / sinh v) + 1 = (cosh u * cosh v + sinh u * sinh v) /
        (sinh u * sinh v) by field_simp,
      show cosh u / sinh u + cosh v / sinh v = (sinh u * cosh v + cosh u * sinh v) /
        (sinh u * sinh v) by field_simp; ring, div_div_div_cancel_right₀ huv]
  · rw [show -(cosh u / sinh u * (cosh v / sinh v)) + 1 = -(cosh u * cosh v - sinh u * sinh v) /
        (sinh u * sinh v) by field_simp; ring,
      show cosh u / sinh u - cosh v / sinh v = -(sinh u * cosh v - cosh u * sinh v) /
        (sinh u * sinh v) by field_simp; ring, div_div_div_cancel_right₀ huv, neg_div_neg_eq]

/-- **DLMF 4.35.5**: `sinh u + sinh v = 2 sinh((u + v)/2) cosh((u − v)/2)`. -/
theorem dlmf_4_35_5 (u v : ℂ) :
    sinh u + sinh v = 2 * sinh ((u + v) / 2) * cosh ((u - v) / 2) := by
  conv_lhs => rw [(half_sum_diff u v).1, (half_sum_diff u v).2]
  rw [sinh_add, sinh_sub]; ring_nf

/-- **DLMF 4.35.6**: `sinh u − sinh v = 2 cosh((u + v)/2) sinh((u − v)/2)`. -/
theorem dlmf_4_35_6 (u v : ℂ) :
    sinh u - sinh v = 2 * cosh ((u + v) / 2) * sinh ((u - v) / 2) := by
  conv_lhs => rw [(half_sum_diff u v).1, (half_sum_diff u v).2]
  rw [sinh_add, sinh_sub]; ring_nf

/-- **DLMF 4.35.7**: `cosh u + cosh v = 2 cosh((u + v)/2) cosh((u − v)/2)`. -/
theorem dlmf_4_35_7 (u v : ℂ) :
    cosh u + cosh v = 2 * cosh ((u + v) / 2) * cosh ((u - v) / 2) := by
  conv_lhs => rw [(half_sum_diff u v).1, (half_sum_diff u v).2]
  rw [cosh_add, cosh_sub]; ring_nf

/-- **DLMF 4.35.8**: `cosh u − cosh v = 2 sinh((u + v)/2) sinh((u − v)/2)`. -/
theorem dlmf_4_35_8 (u v : ℂ) :
    cosh u - cosh v = 2 * sinh ((u + v) / 2) * sinh ((u - v) / 2) := by
  conv_lhs => rw [(half_sum_diff u v).1, (half_sum_diff u v).2]
  rw [cosh_add, cosh_sub]; ring_nf

/-- **DLMF 4.35.9**: `tanh u ± tanh v = sinh(u ± v)/(cosh u cosh v)` (`cosh u, cosh v ≠ 0`). -/
theorem dlmf_4_35_9 {u v : ℂ} (hu : cosh u ≠ 0) (hv : cosh v ≠ 0) :
    tanh u + tanh v = sinh (u + v) / (cosh u * cosh v) ∧
      tanh u - tanh v = sinh (u - v) / (cosh u * cosh v) := by
  simp only [tanh_eq_sinh_div_cosh, sinh_add, sinh_sub]
  constructor <;> field_simp

/-- **DLMF 4.35.10**: `coth u ± coth v = sinh(v ± u)/(sinh u sinh v)` (`sinh u, sinh v ≠ 0`). -/
theorem dlmf_4_35_10 {u v : ℂ} (hu : sinh u ≠ 0) (hv : sinh v ≠ 0) :
    cothC u + cothC v = sinh (v + u) / (sinh u * sinh v) ∧
      cothC u - cothC v = sinh (v - u) / (sinh u * sinh v) := by
  simp only [cothC_eq_cosh_div_sinh, sinh_add, sinh_sub]
  constructor <;> field_simp

/-! ### §4.35(ii) Squares and Products -/

/-- **DLMF 4.35.11**: `cosh² z − sinh² z = 1`. -/
theorem dlmf_4_35_11 (z : ℂ) : cosh z ^ 2 - sinh z ^ 2 = 1 := cosh_sq_sub_sinh_sq z

/-- **DLMF 4.35.12**: `sech² z = 1 − tanh² z` (`cosh z ≠ 0`). -/
theorem dlmf_4_35_12 {z : ℂ} (hz : cosh z ≠ 0) : sechC z ^ 2 = 1 - tanh z ^ 2 := by
  rw [sechC, tanh_eq_sinh_div_cosh]
  field_simp
  linear_combination -cosh_sq_sub_sinh_sq z

/-- **DLMF 4.35.13**: `csch² z = coth² z − 1` (`sinh z ≠ 0`). -/
theorem dlmf_4_35_13 {z : ℂ} (hz : sinh z ≠ 0) : cschC z ^ 2 = cothC z ^ 2 - 1 := by
  rw [cschC, cothC_eq_cosh_div_sinh]
  field_simp
  linear_combination -cosh_sq_sub_sinh_sq z

/-- **DLMF 4.35.14**: `2 sinh u sinh v = cosh(u + v) − cosh(u − v)`. -/
theorem dlmf_4_35_14 (u v : ℂ) : 2 * sinh u * sinh v = cosh (u + v) - cosh (u - v) := by
  rw [cosh_add, cosh_sub]; ring

/-- **DLMF 4.35.15**: `2 cosh u cosh v = cosh(u + v) + cosh(u − v)`. -/
theorem dlmf_4_35_15 (u v : ℂ) : 2 * cosh u * cosh v = cosh (u + v) + cosh (u - v) := by
  rw [cosh_add, cosh_sub]; ring

/-- **DLMF 4.35.16**: `2 sinh u cosh v = sinh(u + v) + sinh(u − v)`. -/
theorem dlmf_4_35_16 (u v : ℂ) : 2 * sinh u * cosh v = sinh (u + v) + sinh (u - v) := by
  rw [sinh_add, sinh_sub]; ring

/-- **DLMF 4.35.17**: `sinh² u − sinh² v = sinh(u + v) sinh(u − v)`. -/
theorem dlmf_4_35_17 (u v : ℂ) : sinh u ^ 2 - sinh v ^ 2 = sinh (u + v) * sinh (u - v) := by
  rw [sinh_add, sinh_sub]
  linear_combination sinh v ^ 2 * cosh_sq_sub_sinh_sq u - sinh u ^ 2 * cosh_sq_sub_sinh_sq v

/-- **DLMF 4.35.18**: `cosh² u − cosh² v = sinh(u + v) sinh(u − v)`. -/
theorem dlmf_4_35_18 (u v : ℂ) : cosh u ^ 2 - cosh v ^ 2 = sinh (u + v) * sinh (u - v) := by
  rw [sinh_add, sinh_sub]
  linear_combination (1 + sinh v ^ 2) * cosh_sq_sub_sinh_sq u -
    (1 + sinh u ^ 2) * cosh_sq_sub_sinh_sq v

/-- **DLMF 4.35.19**: `sinh² u + cosh² v = cosh(u + v) cosh(u − v)`. -/
theorem dlmf_4_35_19 (u v : ℂ) : sinh u ^ 2 + cosh v ^ 2 = cosh (u + v) * cosh (u - v) := by
  rw [cosh_add, cosh_sub]
  linear_combination -sinh u ^ 2 * cosh_sq_sub_sinh_sq v - cosh v ^ 2 * cosh_sq_sub_sinh_sq u

/-! ### §4.35(iii) Multiples of the Argument -/

/-- A continuous square root of `h²` on a preconnected set where `h ≠ 0`, agreeing with `h` at one
point, is `h`. -/
theorem branch_eq_of_sq {S : Set ℂ} (hS : IsPreconnected S) {f h : ℂ → ℂ}
    (hf : ContinuousOn f S) (hh : ContinuousOn h S) (hh0 : ∀ z ∈ S, h z ≠ 0)
    (hsq : ∀ z ∈ S, f z ^ 2 = h z ^ 2) {z₀ : ℂ} (hz₀ : z₀ ∈ S) (h0 : f z₀ = h z₀) :
    ∀ z ∈ S, f z = h z := by
  have hT : IsDiscrete ({1, -1} : Set ℂ) := DiscreteTopology.isDiscrete
  have hmaps : Set.MapsTo (fun z => f z / h z) S {1, -1} := fun z hz => by
    have h1 : (f z / h z - 1) * (f z / h z + 1) = 0 := by
      have := hh0 z hz
      field_simp
      linear_combination hsq z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases mul_eq_zero.mp h1 with h1 | h1
    · left; linear_combination h1
    · right; linear_combination h1
  intro z hz
  have := hS.constant_of_mapsTo hT (hf.div hh hh0) hmaps hz hz₀
  rw [Pi.div_apply, Pi.div_apply, h0, div_self (hh0 z₀ hz₀)] at this
  exact (div_eq_one_iff_eq (hh0 z hz)).mp this

theorem cosh_sub_one_eq (z : ℂ) : cosh z - 1 = 2 * sinh (z / 2) ^ 2 := by
  have h := cosh_two_mul (z / 2)
  rw [show 2 * (z / 2) = z by ring] at h
  linear_combination h + cosh_sq_sub_sinh_sq (z / 2)

theorem cosh_add_one_eq (z : ℂ) : cosh z + 1 = 2 * cosh (z / 2) ^ 2 := by
  have h := cosh_two_mul (z / 2)
  rw [show 2 * (z / 2) = z by ring] at h
  linear_combination h - cosh_sq_sub_sinh_sq (z / 2)

theorem sinh_eq_two_mul_half (z : ℂ) : sinh z = 2 * sinh (z / 2) * cosh (z / 2) := by
  rw [← sinh_two_mul, show 2 * (z / 2) = z by ring]

theorem ofReal_cpow_half_eq_sqrt {x : ℝ} (hx : 0 ≤ x) : (x : ℂ) ^ (1 / 2 : ℂ) = (√x : ℝ) := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hx,
    Real.sqrt_eq_rpow]

/-- **DLMF 4.35.20**: `sinh(z/2) = ((cosh z − 1)/2)^{1/2}`. The square holds for all `z`; on the
positive real axis the root is principal; and any continuous branch of the root on a connected
set avoiding `cosh z = 1` that is principal at one point of the positive real axis is
`sinh(z/2)` ("determined by continuity"). -/
theorem dlmf_4_35_20 :
    (∀ z : ℂ, sinh (z / 2) ^ 2 = (cosh z - 1) / 2) ∧
      (∀ x : ℝ, 0 ≤ x → sinh ((x : ℂ) / 2) = ((cosh (x : ℂ) - 1) / 2) ^ (1 / 2 : ℂ)) ∧
      ∀ {S : Set ℂ} {f : ℂ → ℂ}, IsPreconnected S → (∀ z ∈ S, cosh z ≠ 1) → ContinuousOn f S →
        (∀ z ∈ S, f z ^ 2 = (cosh z - 1) / 2) →
        ∀ {x₀ : ℝ}, 0 < x₀ → (x₀ : ℂ) ∈ S →
          f x₀ = ((cosh (x₀ : ℂ) - 1) / 2) ^ (1 / 2 : ℂ) → ∀ z ∈ S, f z = sinh (z / 2) := by
  have hsq : ∀ z : ℂ, sinh (z / 2) ^ 2 = (cosh z - 1) / 2 := fun z => by
    rw [cosh_sub_one_eq]; ring
  have hreal : ∀ x : ℝ, 0 ≤ x → sinh ((x : ℂ) / 2) = ((cosh (x : ℂ) - 1) / 2) ^ (1 / 2 : ℂ) := by
    intro x hx
    rw [← hsq, show (x : ℂ) / 2 = ((x / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_sinh,
      ← ofReal_pow, ofReal_cpow_half_eq_sqrt (sq_nonneg _),
      Real.sqrt_sq (Real.sinh_nonneg_iff.mpr (by linarith))]
  refine ⟨hsq, hreal, fun {S f} hS hS1 hf hfsq {x₀} hx₀ hx₀S hf0 => ?_⟩
  refine branch_eq_of_sq hS hf (Continuous.continuousOn (by fun_prop)) (fun z hz h0 => hS1 z hz ?_)
    (fun z hz => by rw [hfsq z hz, hsq]) hx₀S (by rw [hf0, hreal x₀ hx₀.le])
  have := cosh_sub_one_eq z
  rw [h0] at this
  linear_combination this

/-- **DLMF 4.35.21**: `cosh(z/2) = ((cosh z + 1)/2)^{1/2}`; the root is principal on the whole
real axis, and determined by continuity (on connected sets avoiding `cosh z = −1`). -/
theorem dlmf_4_35_21 :
    (∀ z : ℂ, cosh (z / 2) ^ 2 = (cosh z + 1) / 2) ∧
      (∀ x : ℝ, cosh ((x : ℂ) / 2) = ((cosh (x : ℂ) + 1) / 2) ^ (1 / 2 : ℂ)) ∧
      ∀ {S : Set ℂ} {f : ℂ → ℂ}, IsPreconnected S → (∀ z ∈ S, cosh z ≠ -1) → ContinuousOn f S →
        (∀ z ∈ S, f z ^ 2 = (cosh z + 1) / 2) →
        ∀ {x₀ : ℝ}, 0 < x₀ → (x₀ : ℂ) ∈ S →
          f x₀ = ((cosh (x₀ : ℂ) + 1) / 2) ^ (1 / 2 : ℂ) → ∀ z ∈ S, f z = cosh (z / 2) := by
  have hsq : ∀ z : ℂ, cosh (z / 2) ^ 2 = (cosh z + 1) / 2 := fun z => by
    rw [cosh_add_one_eq]; ring
  have hreal : ∀ x : ℝ, cosh ((x : ℂ) / 2) = ((cosh (x : ℂ) + 1) / 2) ^ (1 / 2 : ℂ) := by
    intro x
    rw [← hsq, show (x : ℂ) / 2 = ((x / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cosh,
      ← ofReal_pow, ofReal_cpow_half_eq_sqrt (sq_nonneg _),
      Real.sqrt_sq (Real.cosh_pos _).le]
  refine ⟨hsq, hreal, fun {S f} hS hS1 hf hfsq {x₀} hx₀ hx₀S hf0 => ?_⟩
  refine branch_eq_of_sq hS hf (Continuous.continuousOn (by fun_prop)) (fun z hz h0 => hS1 z hz ?_)
    (fun z hz => by rw [hfsq z hz, hsq]) hx₀S (by rw [hf0, hreal x₀])
  have := cosh_add_one_eq z
  rw [h0] at this
  linear_combination this

/-- **DLMF 4.35.22**: `tanh(z/2) = ((cosh z − 1)/(cosh z + 1))^{1/2} = (cosh z − 1)/sinh z
= sinh z/(cosh z + 1)`. The last two forms hold everywhere (Lean's `x/0 = 0` at the poles); the
root is principal on the positive real axis and determined by continuity (on connected sets
avoiding `cosh z = ±1`). -/
theorem dlmf_4_35_22 :
    (∀ z : ℂ, tanh (z / 2) ^ 2 = (cosh z - 1) / (cosh z + 1) ∧
      tanh (z / 2) = (cosh z - 1) / sinh z ∧ tanh (z / 2) = sinh z / (cosh z + 1)) ∧
      (∀ x : ℝ, 0 ≤ x →
        tanh ((x : ℂ) / 2) = ((cosh (x : ℂ) - 1) / (cosh (x : ℂ) + 1)) ^ (1 / 2 : ℂ)) ∧
      ∀ {S : Set ℂ} {f : ℂ → ℂ}, IsPreconnected S → (∀ z ∈ S, cosh z ≠ 1 ∧ cosh z ≠ -1) →
        ContinuousOn f S → (∀ z ∈ S, f z ^ 2 = (cosh z - 1) / (cosh z + 1)) →
        ∀ {x₀ : ℝ}, 0 < x₀ → (x₀ : ℂ) ∈ S →
          f x₀ = ((cosh (x₀ : ℂ) - 1) / (cosh (x₀ : ℂ) + 1)) ^ (1 / 2 : ℂ) →
          ∀ z ∈ S, f z = tanh (z / 2) := by
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  have hsq : ∀ z : ℂ, tanh (z / 2) ^ 2 = (cosh z - 1) / (cosh z + 1) := fun z => by
    rw [tanh_eq_sinh_div_cosh, cosh_sub_one_eq z, cosh_add_one_eq z, div_pow,
      mul_div_mul_left _ _ h2]
  have hforms : ∀ z : ℂ, tanh (z / 2) = (cosh z - 1) / sinh z ∧
      tanh (z / 2) = sinh z / (cosh z + 1) := fun z => by
    refine ⟨?_, ?_⟩
    · rw [tanh_eq_sinh_div_cosh, cosh_sub_one_eq z, sinh_eq_two_mul_half z]
      rcases eq_or_ne (sinh (z / 2)) 0 with hs | hs
      · simp [hs]
      · symm
        rw [show (2 : ℂ) * sinh (z / 2) ^ 2 = (2 * sinh (z / 2)) * sinh (z / 2) by ring]
        exact mul_div_mul_left _ _ (mul_ne_zero h2 hs)
    · rw [tanh_eq_sinh_div_cosh, cosh_add_one_eq z, sinh_eq_two_mul_half z]
      rcases eq_or_ne (cosh (z / 2)) 0 with hc | hc
      · simp [hc]
      · symm
        rw [show 2 * sinh (z / 2) * cosh (z / 2) = (2 * cosh (z / 2)) * sinh (z / 2) by ring,
          show 2 * cosh (z / 2) ^ 2 = (2 * cosh (z / 2)) * cosh (z / 2) by ring]
        exact mul_div_mul_left _ _ (mul_ne_zero h2 hc)
  have hreal : ∀ x : ℝ, 0 ≤ x →
      tanh ((x : ℂ) / 2) = ((cosh (x : ℂ) - 1) / (cosh (x : ℂ) + 1)) ^ (1 / 2 : ℂ) := by
    intro x hx
    rw [← hsq, show (x : ℂ) / 2 = ((x / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_tanh,
      ← ofReal_pow, ofReal_cpow_half_eq_sqrt (sq_nonneg _), Real.sqrt_sq]
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr (by linarith)) (Real.cosh_pos _).le
  refine ⟨fun z => ⟨hsq z, hforms z⟩, hreal, fun {S f} hS hS1 hf hfsq {x₀} hx₀ hx₀S hf0 => ?_⟩
  have hc0 : ∀ z ∈ S, cosh (z / 2) ≠ 0 := fun z hz h0 => (hS1 z hz).2 (by
    have := cosh_add_one_eq z; rw [h0] at this; linear_combination this)
  have hs0 : ∀ z ∈ S, sinh (z / 2) ≠ 0 := fun z hz h0 => (hS1 z hz).1 (by
    have := cosh_sub_one_eq z; rw [h0] at this; linear_combination this)
  have hcont : ContinuousOn (fun z => tanh (z / 2)) S := by
    have : ContinuousOn (fun z => sinh (z / 2) / cosh (z / 2)) S :=
      (Continuous.continuousOn (by fun_prop)).div (Continuous.continuousOn (by fun_prop)) hc0
    exact this.congr fun z _ => tanh_eq_sinh_div_cosh _
  refine branch_eq_of_sq hS hf hcont (fun z hz => ?_) (fun z hz => by rw [hfsq z hz, hsq])
    hx₀S (by rw [hf0, hreal x₀ hx₀.le])
  rw [tanh_eq_sinh_div_cosh]
  exact div_ne_zero (hs0 z hz) (hc0 z hz)

/-- **DLMF 4.35.23–4.35.25**: `sinh(−z) = −sinh z`, `cosh(−z) = cosh z`, `tanh(−z) = −tanh z`. -/
theorem dlmf_4_35_23 (z : ℂ) : sinh (-z) = -sinh z := sinh_neg z

theorem dlmf_4_35_24 (z : ℂ) : cosh (-z) = cosh z := cosh_neg z

theorem dlmf_4_35_25 (z : ℂ) : tanh (-z) = -tanh z := tanh_neg z

/-- **DLMF 4.35.26**: `sinh(2z) = 2 sinh z cosh z = 2 tanh z/(1 − tanh² z)` (the last form for
`cosh z ≠ 0`). -/
theorem dlmf_4_35_26 (z : ℂ) :
    sinh (2 * z) = 2 * sinh z * cosh z ∧
      (cosh z ≠ 0 → sinh (2 * z) = 2 * tanh z / (1 - tanh z ^ 2)) := by
  refine ⟨sinh_two_mul z, fun hz => ?_⟩
  have h1 : 1 - tanh z ^ 2 = 1 / cosh z ^ 2 := by
    rw [tanh_eq_sinh_div_cosh]
    field_simp
    linear_combination cosh_sq_sub_sinh_sq z
  rw [h1, sinh_two_mul, tanh_eq_sinh_div_cosh]
  field_simp

/-- **DLMF 4.35.27**: `cosh(2z) = 2cosh² z − 1 = 2sinh² z + 1 = cosh² z + sinh² z`. -/
theorem dlmf_4_35_27 (z : ℂ) :
    cosh (2 * z) = 2 * cosh z ^ 2 - 1 ∧ cosh (2 * z) = 2 * sinh z ^ 2 + 1 ∧
      cosh (2 * z) = cosh z ^ 2 + sinh z ^ 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [cosh_two_mul]
  · linear_combination -cosh_sq_sub_sinh_sq z
  · linear_combination cosh_sq_sub_sinh_sq z

/-- **DLMF 4.35.28**: `tanh(2z) = 2 tanh z/(1 + tanh² z)` (`cosh z ≠ 0`). -/
theorem dlmf_4_35_28 {z : ℂ} (hz : cosh z ≠ 0) : tanh (2 * z) = 2 * tanh z / (1 + tanh z ^ 2) := by
  rw [tanh_eq_sinh_div_cosh, sinh_two_mul, cosh_two_mul, tanh_eq_sinh_div_cosh,
    ← mul_div_mul_right (2 * (sinh z / cosh z)) (1 + (sinh z / cosh z) ^ 2) (pow_ne_zero 2 hz)]
  congr 1 <;> field_simp

/-- **DLMF 4.35.29**: `sinh(3z) = 3 sinh z + 4 sinh³ z`. -/
theorem dlmf_4_35_29 (z : ℂ) : sinh (3 * z) = 3 * sinh z + 4 * sinh z ^ 3 := by
  rw [sinh_three_mul]; ring

/-- **DLMF 4.35.30**: `cosh(3z) = −3 cosh z + 4 cosh³ z`. -/
theorem dlmf_4_35_30 (z : ℂ) : cosh (3 * z) = -3 * cosh z + 4 * cosh z ^ 3 := by
  rw [cosh_three_mul]; ring

/-- **DLMF 4.35.31**: `sinh(4z) = 4 sinh³ z cosh z + 4 cosh³ z sinh z`. -/
theorem dlmf_4_35_31 (z : ℂ) :
    sinh (4 * z) = 4 * sinh z ^ 3 * cosh z + 4 * cosh z ^ 3 * sinh z := by
  rw [show 4 * z = 2 * (2 * z) by ring, sinh_two_mul, sinh_two_mul, cosh_two_mul]
  ring

/-- **DLMF 4.35.32**: `cosh(4z) = cosh⁴ z + 6 sinh² z cosh² z + sinh⁴ z`. -/
theorem dlmf_4_35_32 (z : ℂ) :
    cosh (4 * z) = cosh z ^ 4 + 6 * sinh z ^ 2 * cosh z ^ 2 + sinh z ^ 4 := by
  rw [show 4 * z = 2 * (2 * z) by ring, cosh_two_mul, cosh_two_mul, sinh_two_mul]
  ring

/-- **DLMF 4.35.33**: `cosh(nz) ± sinh(nz) = (cosh z ± sinh z)ⁿ`, `n ∈ ℤ`. -/
theorem dlmf_4_35_33 (n : ℤ) (z : ℂ) :
    cosh (n * z) + sinh (n * z) = (cosh z + sinh z) ^ n ∧
      cosh (n * z) - sinh (n * z) = (cosh z - sinh z) ^ n := by
  rw [cosh_add_sinh, cosh_add_sinh, cosh_sub_sinh, cosh_sub_sinh, exp_int_mul,
    show -((n : ℂ) * z) = n * -z by ring, exp_int_mul]
  exact ⟨rfl, rfl⟩

/-! ### §4.35(iv) Real and Imaginary Parts; Moduli -/

theorem I_mul_add_mul_I (x y : ℝ) : I * ((x : ℂ) + y * I) = ((-y : ℝ) : ℂ) + (x : ℂ) * I := by
  push_cast; ring_nf; rw [I_sq]; ring

/-- **DLMF 4.35.34**: `sinh z = sinh x cos y + i cosh x sin y`. -/
theorem dlmf_4_35_34 (x y : ℝ) :
    sinh (x + y * I) = (Real.sinh x * Real.cos y : ℝ) + I * (Real.cosh x * Real.sin y : ℝ) := by
  rw [sinh_add, sinh_mul_I, cosh_mul_I]; push_cast; ring

/-- **DLMF 4.35.35**: `cosh z = cosh x cos y + i sinh x sin y`. -/
theorem dlmf_4_35_35 (x y : ℝ) :
    cosh (x + y * I) = (Real.cosh x * Real.cos y : ℝ) + I * (Real.sinh x * Real.sin y : ℝ) := by
  rw [cosh_add, sinh_mul_I, cosh_mul_I]; push_cast; ring

/-- **DLMF 4.35.36**: `tanh z = (sinh 2x + i sin 2y)/(cosh 2x + cos 2y)`. -/
theorem dlmf_4_35_36 (x y : ℝ) :
    tanh (x + y * I) =
      ((Real.sinh (2 * x) : ℝ) + I * (Real.sin (2 * y) : ℝ)) /
        ((Real.cosh (2 * x) + Real.cos (2 * y) : ℝ) : ℂ) := by
  rw [tanh_eq_neg_I_mul_tan, I_mul_add_mul_I, dlmf_4_21_39, mul_neg, Real.sin_neg, Real.cos_neg]
  push_cast
  rw [← mul_div_assoc]
  congr 1
  · linear_combination (-sinh (2 * (x : ℂ))) * I_sq
  · ring

/-- **DLMF 4.35.37**: `coth z = (sinh 2x − i sin 2y)/(cosh 2x − cos 2y)`. -/
theorem dlmf_4_35_37 (x y : ℝ) :
    cothC (x + y * I) =
      ((Real.sinh (2 * x) : ℝ) - I * (Real.sin (2 * y) : ℝ)) /
        ((Real.cosh (2 * x) - Real.cos (2 * y) : ℝ) : ℂ) := by
  have hc : cothC (x + y * I) = I * cot (I * (x + y * I)) := by
    rw [dlmf_4_28_13, ← mul_assoc, mul_neg, I_mul_I, neg_neg, one_mul]
  rw [hc, I_mul_add_mul_I, dlmf_4_21_40, mul_neg, Real.sin_neg, Real.cos_neg]
  push_cast
  rw [← mul_div_assoc]
  congr 1
  linear_combination (-sinh (2 * (x : ℂ))) * I_sq

theorem norm_sinh_eq_norm_sin (z : ℂ) : ‖sinh z‖ = ‖sin (I * z)‖ := by
  rw [dlmf_4_28_8, norm_mul, norm_I, one_mul]

/-- **DLMF 4.35.38**: `|sinh z| = (sinh² x + sin² y)^{1/2} = (½(cosh 2x − cos 2y))^{1/2}`. -/
theorem dlmf_4_35_38 (x y : ℝ) :
    ‖sinh (x + y * I)‖ = √(Real.sinh x ^ 2 + Real.sin y ^ 2) ∧
      √(Real.sinh x ^ 2 + Real.sin y ^ 2) = √((Real.cosh (2 * x) - Real.cos (2 * y)) / 2) := by
  obtain ⟨h1, h2⟩ := dlmf_4_21_41 (-y) x
  rw [Real.sin_neg, neg_sq, add_comm (Real.sin y ^ 2)] at h1
  rw [Real.sin_neg, neg_sq, mul_neg, Real.cos_neg, add_comm (Real.sin y ^ 2)] at h2
  rw [norm_sinh_eq_norm_sin, I_mul_add_mul_I]
  exact ⟨h1, h2⟩

/-- **DLMF 4.35.39**: `|cosh z| = (sinh² x + cos² y)^{1/2} = (½(cosh 2x + cos 2y))^{1/2}`. -/
theorem dlmf_4_35_39 (x y : ℝ) :
    ‖cosh (x + y * I)‖ = √(Real.sinh x ^ 2 + Real.cos y ^ 2) ∧
      √(Real.sinh x ^ 2 + Real.cos y ^ 2) = √((Real.cosh (2 * x) + Real.cos (2 * y)) / 2) := by
  obtain ⟨h1, h2⟩ := dlmf_4_21_42 (-y) x
  rw [Real.cos_neg, add_comm (Real.cos y ^ 2)] at h1
  rw [Real.cos_neg, mul_neg, Real.cos_neg, add_comm (Real.cos y ^ 2)] at h2
  rw [← dlmf_4_28_9, I_mul_add_mul_I]
  exact ⟨h1, h2⟩

/-- **DLMF 4.35.40**: `|tanh z| = ((cosh 2x − cos 2y)/(cosh 2x + cos 2y))^{1/2}`. -/
theorem dlmf_4_35_40 (x y : ℝ) :
    ‖tanh (x + y * I)‖ =
      √((Real.cosh (2 * x) - Real.cos (2 * y)) / (Real.cosh (2 * x) + Real.cos (2 * y))) := by
  have h := dlmf_4_21_43 (-y) x
  rw [mul_neg, Real.cos_neg] at h
  rw [tanh_eq_neg_I_mul_tan, norm_mul, norm_neg, norm_I, one_mul, I_mul_add_mul_I]
  exact h

end Azurite.DLMF
