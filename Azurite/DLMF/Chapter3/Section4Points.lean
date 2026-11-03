/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section3PointsSevenEight
import Azurite.DLMF.Chapter3.Section4

/-!
# DLMF §3.4(i): the two- through eight-point differentiation formulas

The cases `n = 1, …, 7` of 3.4.1 (`dlmf_3_4_1`).

* The coefficients: `lagCoeffD_eq` writes `B_k^n(t) = c ω_E′(t)`, `c = (−1)^{n₁+k}/((k − n₀)!
  (n₁ − k)!)`, `ω_E` the nodal polynomial of the nodes other than `k`; for explicit nodes the
  product rule expands `ω_E′` and `ring` compares with DLMF. `lagCoeffD_one` (3.4.5),
  `lagCoeffD_two` (3.4.6), `dlmf_3_4_8`, `dlmf_3_4_10`, `dlmf_3_4_12`, `dlmf_3_4_14`,
  `dlmf_3_4_16`: all 35 printed coefficients are correct.
* The formulas: `dlmf_3_4_5` (`h f′_t = −f₀ + f₁ + h R′_{1,t}`), `dlmf_3_4_6` (written out),
  `dlmf_3_4_7`, `dlmf_3_4_9`, `dlmf_3_4_11`, `dlmf_3_4_13`, `dlmf_3_4_15` (sums with the
  `B_k^n` above); all hold for every real `t` (DLMF's ranges of `t` matter only for the bounds).
* Remainder bounds (3.4.4, corrected) with the exact `c_n` of §3.3(ii): `dlmf_3_4_5_bound`
  (`c₁ = 1/8`), `dlmf_3_4_6_bound` (`c₂ = 1/(9√3)`). For `n ≥ 3` apply `dlmf_3_4_4` with the
  `t`-sets and the bounds on `c_n` from `Section3Points`, `Section3PointsFiveSix`,
  `Section3PointsSevenEight`.
-/

open Polynomial Finset Lagrange

namespace Azurite.DLMF

/-- `B_k^n(t) = c (d/dt) ∏_{m ≠ k} (t − m)` with `c = (−1)^{n₁+k}/((k − n₀)! (n₁ − k)!)`, the
derivative of the nodal polynomial of the other nodes. -/
theorem lagCoeffD_eq (n : ℕ) (k : ℤ) (t : ℝ) :
    lagCoeffD n k t = (-1 : ℝ) ^ (eqN1 n + k) /
        ((k - eqN0 n).toNat.factorial * (eqN1 n - k).toNat.factorial) *
      (derivative (nodal ((Icc (eqN0 n) (eqN1 n)).erase k) fun m : ℤ => (m : ℝ))).eval t := by
  have h : lagCoeff' n k = fun s => (-1 : ℝ) ^ (eqN1 n + k) /
      ((k - eqN0 n).toNat.factorial * (eqN1 n - k).toNat.factorial) *
      (nodal ((Icc (eqN0 n) (eqN1 n)).erase k) fun m : ℤ => (m : ℝ)).eval s :=
    funext fun s => by rw [lagCoeff', eval_nodal]
  rw [lagCoeffD, h, ((Polynomial.hasDerivAt _ t).const_mul _).deriv]

/-- `B_0^1 = −1`, `B_1^1 = 1` (the coefficients of 3.4.5). -/
theorem lagCoeffD_one (t : ℝ) :
    lagCoeffD 1 0 t = -1 ∧
      lagCoeffD 1 1 t = 1 := by
  simp only [lagCoeffD_eq, eqN0_one, eqN1_one]
  rw [show (Icc (0 : ℤ) 1).erase 0 = {1} by decide,
    show (Icc (0 : ℤ) 1).erase 1 = {0} by decide]
  refine ⟨?_, ?_⟩ <;>
    norm_num [nodal, prod_insert, prod_pair, Nat.factorial, derivative_mul]

/-- The coefficients of 3.4.6: `B_{−1}^2 = −½(1 − 2t)`, `B_0^2 = −2t`, `B_1^2 = ½(1 + 2t)`. -/
theorem lagCoeffD_two (t : ℝ) :
    lagCoeffD 2 (-1) t = -(1 / 2) * (1 - 2 * t) ∧
      lagCoeffD 2 0 t = -2 * t ∧
      lagCoeffD 2 1 t = 1 / 2 * (1 + 2 * t) := by
  simp only [lagCoeffD_eq, eqN0_two, eqN1_two]
  rw [show (Icc (-1 : ℤ) 1).erase (-1) = {0, 1} by decide,
    show (Icc (-1 : ℤ) 1).erase 0 = {-1, 1} by decide,
    show (Icc (-1 : ℤ) 1).erase 1 = {-1, 0} by decide]
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [nodal, prod_insert, prod_pair, Nat.factorial, derivative_mul] <;> ring

/-- **DLMF 3.4.8**: the coefficients `B_k^3`, `k = −1, …, 2`. -/
theorem dlmf_3_4_8 (t : ℝ) :
    lagCoeffD 3 (-1) t = -(1 / 6) * (2 - 6 * t + 3 * t ^ 2) ∧
      lagCoeffD 3 0 t = -(1 / 2) * (1 + 4 * t - 3 * t ^ 2) ∧
      lagCoeffD 3 1 t = 1 / 2 * (2 + 2 * t - 3 * t ^ 2) ∧
      lagCoeffD 3 2 t = -(1 / 6) * (1 - 3 * t ^ 2) := by
  simp only [lagCoeffD_eq, eqN0_three, eqN1_three]
  rw [show (Icc (-1 : ℤ) 2).erase (-1) = {0, 1, 2} by decide,
    show (Icc (-1 : ℤ) 2).erase 0 = {-1, 1, 2} by decide,
    show (Icc (-1 : ℤ) 2).erase 1 = {-1, 0, 2} by decide,
    show (Icc (-1 : ℤ) 2).erase 2 = {-1, 0, 1} by decide]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    norm_num [nodal, prod_insert, prod_pair, Nat.factorial, derivative_mul] <;> ring

/-- **DLMF 3.4.10**: the coefficients `B_k^4`, `k = −2, …, 2`. -/
theorem dlmf_3_4_10 (t : ℝ) :
    lagCoeffD 4 (-2) t = 1 / 12 * (1 - t - 3 * t ^ 2 + 2 * t ^ 3) ∧
      lagCoeffD 4 (-1) t = -(1 / 6) * (4 - 8 * t - 3 * t ^ 2 + 4 * t ^ 3) ∧
      lagCoeffD 4 0 t = -(1 / 2) * t * (5 - 2 * t ^ 2) ∧
      lagCoeffD 4 1 t = 1 / 6 * (4 + 8 * t - 3 * t ^ 2 - 4 * t ^ 3) ∧
      lagCoeffD 4 2 t = -(1 / 12) * (1 + t - 3 * t ^ 2 - 2 * t ^ 3) := by
  simp only [lagCoeffD_eq, eqN0_four, eqN1_four]
  rw [show (Icc (-2 : ℤ) 2).erase (-2) = {-1, 0, 1, 2} by decide,
    show (Icc (-2 : ℤ) 2).erase (-1) = {-2, 0, 1, 2} by decide,
    show (Icc (-2 : ℤ) 2).erase 0 = {-2, -1, 1, 2} by decide,
    show (Icc (-2 : ℤ) 2).erase 1 = {-2, -1, 0, 2} by decide,
    show (Icc (-2 : ℤ) 2).erase 2 = {-2, -1, 0, 1} by decide]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [nodal, prod_insert, prod_pair, Nat.factorial, derivative_mul] <;> ring

/-- **DLMF 3.4.12**: the coefficients `B_k^5`, `k = −2, …, 3`. -/
theorem dlmf_3_4_12 (t : ℝ) :
    lagCoeffD 5 (-2) t = 1 / 120 * (6 - 10 * t - 15 * t ^ 2 + 20 * t ^ 3 - 5 * t ^ 4) ∧
      lagCoeffD 5 (-1) t = -(1 / 24) * (12 - 32 * t + 3 * t ^ 2 + 16 * t ^ 3 - 5 * t ^ 4) ∧
      lagCoeffD 5 0 t = -(1 / 12) * (4 + 30 * t - 15 * t ^ 2 - 12 * t ^ 3 + 5 * t ^ 4) ∧
      lagCoeffD 5 1 t = 1 / 12 * (12 + 16 * t - 21 * t ^ 2 - 8 * t ^ 3 + 5 * t ^ 4) ∧
      lagCoeffD 5 2 t = -(1 / 24) * (6 + 2 * t - 21 * t ^ 2 - 4 * t ^ 3 + 5 * t ^ 4) ∧
      lagCoeffD 5 3 t = 1 / 120 * (4 - 15 * t ^ 2 + 5 * t ^ 4) := by
  simp only [lagCoeffD_eq, eqN0_five, eqN1_five]
  rw [show (Icc (-2 : ℤ) 3).erase (-2) = {-1, 0, 1, 2, 3} by decide,
    show (Icc (-2 : ℤ) 3).erase (-1) = {-2, 0, 1, 2, 3} by decide,
    show (Icc (-2 : ℤ) 3).erase 0 = {-2, -1, 1, 2, 3} by decide,
    show (Icc (-2 : ℤ) 3).erase 1 = {-2, -1, 0, 2, 3} by decide,
    show (Icc (-2 : ℤ) 3).erase 2 = {-2, -1, 0, 1, 3} by decide,
    show (Icc (-2 : ℤ) 3).erase 3 = {-2, -1, 0, 1, 2} by decide]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [nodal, prod_insert, prod_pair, Nat.factorial, derivative_mul] <;> ring

/-- **DLMF 3.4.14**: the coefficients `B_k^6`, `k = −3, …, 3`. -/
theorem dlmf_3_4_14 (t : ℝ) :
    lagCoeffD 6 (-3) t =
        -(1 / 720) * (12 - 8 * t - 45 * t ^ 2 + 20 * t ^ 3 + 15 * t ^ 4 - 6 * t ^ 5) ∧
      lagCoeffD 6 (-2) t = 1 / 60 * (9 - 9 * t - 30 * t ^ 2 + 20 * t ^ 3 + 5 * t ^ 4 - 3 * t ^ 5) ∧
      lagCoeffD 6 (-1) t =
          -(1 / 48) * (36 - 72 * t - 39 * t ^ 2 + 52 * t ^ 3 + 5 * t ^ 4 - 6 * t ^ 5) ∧
      lagCoeffD 6 0 t = -(1 / 18) * t * (49 - 28 * t ^ 2 + 3 * t ^ 4) ∧
      lagCoeffD 6 1 t = 1 / 48 * (36 + 72 * t - 39 * t ^ 2 - 52 * t ^ 3 + 5 * t ^ 4 + 6 * t ^ 5) ∧
      lagCoeffD 6 2 t = -(1 / 60) * (9 + 9 * t - 30 * t ^ 2 - 20 * t ^ 3 + 5 * t ^ 4 + 3 * t ^ 5) ∧
      lagCoeffD 6 3 t =
          1 / 720 * (12 + 8 * t - 45 * t ^ 2 - 20 * t ^ 3 + 15 * t ^ 4 + 6 * t ^ 5) := by
  simp only [lagCoeffD_eq, eqN0_six, eqN1_six]
  rw [show (Icc (-3 : ℤ) 3).erase (-3) = {-2, -1, 0, 1, 2, 3} by decide,
    show (Icc (-3 : ℤ) 3).erase (-2) = {-3, -1, 0, 1, 2, 3} by decide,
    show (Icc (-3 : ℤ) 3).erase (-1) = {-3, -2, 0, 1, 2, 3} by decide,
    show (Icc (-3 : ℤ) 3).erase 0 = {-3, -2, -1, 1, 2, 3} by decide,
    show (Icc (-3 : ℤ) 3).erase 1 = {-3, -2, -1, 0, 2, 3} by decide,
    show (Icc (-3 : ℤ) 3).erase 2 = {-3, -2, -1, 0, 1, 3} by decide,
    show (Icc (-3 : ℤ) 3).erase 3 = {-3, -2, -1, 0, 1, 2} by decide]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [nodal, prod_insert, prod_pair, Nat.factorial, derivative_mul] <;> ring

/-- **DLMF 3.4.16**: the coefficients `B_k^7`, `k = −3, …, 4`. -/
theorem dlmf_3_4_16 (t : ℝ) :
    lagCoeffD 7 (-3) t =
        -(1 / 5040) * (48 - 56 * t - 168 * t ^ 2 + 140 * t ^ 3 +
          35 * t ^ 4 - 42 * t ^ 5 + 7 * t ^ 6) ∧
      lagCoeffD 7 (-2) t =
          1 / 720 * (72 - 108 * t - 213 * t ^ 2 + 240 * t ^ 3 -
            10 * t ^ 4 - 36 * t ^ 5 + 7 * t ^ 6) ∧
      lagCoeffD 7 (-1) t =
          -(1 / 240) * (144 - 360 * t - 48 * t ^ 2 + 260 * t ^ 3 -
            45 * t ^ 4 - 30 * t ^ 5 + 7 * t ^ 6) ∧
      lagCoeffD 7 0 t =
          -(1 / 144) * (36 + 392 * t - 147 * t ^ 2 - 224 * t ^ 3 +
            70 * t ^ 4 + 24 * t ^ 5 - 7 * t ^ 6) ∧
      lagCoeffD 7 1 t =
          1 / 144 * (144 + 216 * t - 264 * t ^ 2 - 156 * t ^ 3 +
            85 * t ^ 4 + 18 * t ^ 5 - 7 * t ^ 6) ∧
      lagCoeffD 7 2 t =
          -(1 / 240) * (72 + 36 * t - 267 * t ^ 2 - 80 * t ^ 3 +
            90 * t ^ 4 + 12 * t ^ 5 - 7 * t ^ 6) ∧
      lagCoeffD 7 3 t =
          1 / 720 * (48 + 8 * t - 192 * t ^ 2 - 20 * t ^ 3 + 85 * t ^ 4 + 6 * t ^ 5 - 7 * t ^ 6) ∧
      lagCoeffD 7 4 t = -(1 / 5040) * (36 - 147 * t ^ 2 + 70 * t ^ 4 - 7 * t ^ 6) := by
  simp only [lagCoeffD_eq, eqN0_seven, eqN1_seven]
  rw [show (Icc (-3 : ℤ) 4).erase (-3) = {-2, -1, 0, 1, 2, 3, 4} by decide,
    show (Icc (-3 : ℤ) 4).erase (-2) = {-3, -1, 0, 1, 2, 3, 4} by decide,
    show (Icc (-3 : ℤ) 4).erase (-1) = {-3, -2, 0, 1, 2, 3, 4} by decide,
    show (Icc (-3 : ℤ) 4).erase 0 = {-3, -2, -1, 1, 2, 3, 4} by decide,
    show (Icc (-3 : ℤ) 4).erase 1 = {-3, -2, -1, 0, 2, 3, 4} by decide,
    show (Icc (-3 : ℤ) 4).erase 2 = {-3, -2, -1, 0, 1, 3, 4} by decide,
    show (Icc (-3 : ℤ) 4).erase 3 = {-3, -2, -1, 0, 1, 2, 4} by decide,
    show (Icc (-3 : ℤ) 4).erase 4 = {-3, -2, -1, 0, 1, 2, 3} by decide]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [nodal, prod_insert, prod_pair, Nat.factorial, derivative_mul] <;> ring

/-! ### The formulas 3.4.5–3.4.15 -/

/-- **DLMF 3.4.5** (two-point formula): `h f′_t = −f₀ + f₁ + h R′_{1,t}` (every real `t`; DLMF:
`0 < t < 1`). -/
theorem dlmf_3_4_5 {x₀ h : ℝ} (hh : h ≠ 0) (f : ℝ → ℝ) (t : ℝ)
    (hf : DifferentiableAt ℝ f (x₀ + t * h)) :
    h * deriv f (x₀ + t * h) = -f x₀ + f (x₀ + h) +
      h * deriv (lagrangeRem (eqNode x₀ h 1) f) (x₀ + t * h) := by
  rw [dlmf_3_4_1 hh 1 f t hf, eqN0_one, eqN1_one, Icc_zero_one, sum_pair (by norm_num)]
  obtain ⟨h0, h1⟩ := lagCoeffD_one t
  rw [h0, h1]
  push_cast
  ring_nf

/-- **DLMF 3.4.6** (three-point formula):
`h f′_t = −½(1 − 2t) f_{−1} − 2t f₀ + ½(1 + 2t) f₁ + h R′_{2,t}` (every real `t`; DLMF:
`|t| < 1`). -/
theorem dlmf_3_4_6 {x₀ h : ℝ} (hh : h ≠ 0) (f : ℝ → ℝ) (t : ℝ)
    (hf : DifferentiableAt ℝ f (x₀ + t * h)) :
    h * deriv f (x₀ + t * h) = -(1 / 2) * (1 - 2 * t) * f (x₀ - h) - 2 * t * f x₀ +
      1 / 2 * (1 + 2 * t) * f (x₀ + h) +
      h * deriv (lagrangeRem (eqNode x₀ h 2) f) (x₀ + t * h) := by
  rw [dlmf_3_4_1 hh 2 f t hf, Icc_eqN_two, sum_insert (by decide), sum_pair (by decide)]
  obtain ⟨h1, h2, h3⟩ := lagCoeffD_two t
  rw [h1, h2, h3]
  push_cast
  ring_nf

/-- **DLMF 3.4.7** (four-point formula): `h f′_t = ∑_{k=−1}^{2} B_k^3 f_k + h R′_{3,t}` (every real
`t`; DLMF: `−1 < t < 2`), with `B_k^3` as in 3.4.8 (`dlmf_3_4_8`). -/
theorem dlmf_3_4_7 {x₀ h : ℝ} (hh : h ≠ 0) (f : ℝ → ℝ) (t : ℝ)
    (hf : DifferentiableAt ℝ f (x₀ + t * h)) :
    h * deriv f (x₀ + t * h) = ∑ k ∈ Icc (-1 : ℤ) 2, lagCoeffD 3 k t * f (x₀ + k * h) +
      h * deriv (lagrangeRem (eqNode x₀ h 3) f) (x₀ + t * h) := by
  rw [dlmf_3_4_1 hh 3 f t hf, eqN0_three, eqN1_three]

/-- **DLMF 3.4.9** (five-point formula): `h f′_t = ∑_{k=−2}^{2} B_k^4 f_k + h R′_{4,t}` (every real
`t`; DLMF: `|t| < 2`), with `B_k^4` as in 3.4.10 (`dlmf_3_4_10`). -/
theorem dlmf_3_4_9 {x₀ h : ℝ} (hh : h ≠ 0) (f : ℝ → ℝ) (t : ℝ)
    (hf : DifferentiableAt ℝ f (x₀ + t * h)) :
    h * deriv f (x₀ + t * h) = ∑ k ∈ Icc (-2 : ℤ) 2, lagCoeffD 4 k t * f (x₀ + k * h) +
      h * deriv (lagrangeRem (eqNode x₀ h 4) f) (x₀ + t * h) := by
  rw [dlmf_3_4_1 hh 4 f t hf, eqN0_four, eqN1_four]

/-- **DLMF 3.4.11** (six-point formula): `h f′_t = ∑_{k=−2}^{3} B_k^5 f_k + h R′_{5,t}` (every real
`t`; DLMF: `−2 < t < 3`), with `B_k^5` as in 3.4.12 (`dlmf_3_4_12`). -/
theorem dlmf_3_4_11 {x₀ h : ℝ} (hh : h ≠ 0) (f : ℝ → ℝ) (t : ℝ)
    (hf : DifferentiableAt ℝ f (x₀ + t * h)) :
    h * deriv f (x₀ + t * h) = ∑ k ∈ Icc (-2 : ℤ) 3, lagCoeffD 5 k t * f (x₀ + k * h) +
      h * deriv (lagrangeRem (eqNode x₀ h 5) f) (x₀ + t * h) := by
  rw [dlmf_3_4_1 hh 5 f t hf, eqN0_five, eqN1_five]

/-- **DLMF 3.4.13** (seven-point formula): `h f′_t = ∑_{k=−3}^{3} B_k^6 f_k + h R′_{6,t}` (every
real `t`; DLMF: `|t| < 3`), with `B_k^6` as in 3.4.14 (`dlmf_3_4_14`). -/
theorem dlmf_3_4_13 {x₀ h : ℝ} (hh : h ≠ 0) (f : ℝ → ℝ) (t : ℝ)
    (hf : DifferentiableAt ℝ f (x₀ + t * h)) :
    h * deriv f (x₀ + t * h) = ∑ k ∈ Icc (-3 : ℤ) 3, lagCoeffD 6 k t * f (x₀ + k * h) +
      h * deriv (lagrangeRem (eqNode x₀ h 6) f) (x₀ + t * h) := by
  rw [dlmf_3_4_1 hh 6 f t hf, eqN0_six, eqN1_six]

/-- **DLMF 3.4.15** (eight-point formula): `h f′_t = ∑_{k=−3}^{4} B_k^7 f_k + h R′_{7,t}` (every
real `t`; DLMF: `−3 < t < 4`), with `B_k^7` as in 3.4.16 (`dlmf_3_4_16`). -/
theorem dlmf_3_4_15 {x₀ h : ℝ} (hh : h ≠ 0) (f : ℝ → ℝ) (t : ℝ)
    (hf : DifferentiableAt ℝ f (x₀ + t * h)) :
    h * deriv f (x₀ + t * h) = ∑ k ∈ Icc (-3 : ℤ) 4, lagCoeffD 7 k t * f (x₀ + k * h) +
      h * deriv (lagrangeRem (eqNode x₀ h 7) f) (x₀ + t * h) := by
  rw [dlmf_3_4_1 hh 7 f t hf, eqN0_seven, eqN1_seven]

/-! ### Remainder bounds: 3.4.4 with the `c_n` of §3.3(ii) -/

/-- 3.4.4 (corrected) for the two-point formula, `c₁ = 1/8` (3.3.15): for `0 < t < 1`,
`h |R′_{1,t}| ≤ h² (h |f‴(ξ₁)|/8 + |f″(ξ₀)|/2)`, `ξ₀, ξ₁ ∈ [x₀, x₀ + h]`. -/
theorem dlmf_3_4_5_bound {x₀ h : ℝ} (hh : 0 < h) (f : ℝ → ℝ) {U : Set ℝ} (hU : IsOpen U)
    (hd : ∀ k ≤ 2, DifferentiableOn ℝ (iteratedDeriv k f) U) (hI : Set.Icc x₀ (x₀ + h) ⊆ U)
    (hc : ContinuousOn (iteratedDeriv 3 f) (Set.Icc x₀ (x₀ + h))) {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ ξ₀ ∈ Set.Icc x₀ (x₀ + h), ∃ ξ₁ ∈ Set.Icc x₀ (x₀ + h),
      h * |deriv (lagrangeRem (eqNode x₀ h 1) f) (x₀ + t * h)| ≤
        h ^ 2 * (1 / 8 * h * |iteratedDeriv 3 f ξ₁| + 1 / 2 * |iteratedDeriv 2 f ξ₀|) := by
  have e0 : x₀ + (eqN0 1 : ℝ) * h = x₀ := by rw [eqN0_one]; push_cast; ring
  have e1 : x₀ + (eqN1 1 : ℝ) * h = x₀ + h := by rw [eqN1_one]; push_cast; ring
  have hJ : Set.Ioo (0 : ℝ) 1 ⊆ Set.Ioo (eqN0 1 : ℝ) (eqN1 1) := by
    rw [eqN0_one, eqN1_one]; push_cast; exact subset_rfl
  have := dlmf_3_4_4 hh 1 f hU hd (by rw [e0, e1]; exact hI) (by rw [e0, e1]; exact hc) hJ ht
  rw [e0, e1, dlmf_3_3_15] at this
  obtain ⟨ξ₀, h0, ξ₁, h1, hR⟩ := this
  exact ⟨ξ₀, h0, ξ₁, h1, by convert hR using 2; norm_num⟩

/-- 3.4.4 (corrected) for the three-point formula, `c₂ = 1/(9√3)` (3.3.18): for `|t| < 1`,
`h |R′_{2,t}| ≤ h³ (h |f⁗(ξ₁)|/(9√3) + |f‴(ξ₀)|/3)`, `ξ₀, ξ₁ ∈ [x₀ − h, x₀ + h]`. -/
theorem dlmf_3_4_6_bound {x₀ h : ℝ} (hh : 0 < h) (f : ℝ → ℝ) {U : Set ℝ} (hU : IsOpen U)
    (hd : ∀ k ≤ 3, DifferentiableOn ℝ (iteratedDeriv k f) U)
    (hI : Set.Icc (x₀ - h) (x₀ + h) ⊆ U)
    (hc : ContinuousOn (iteratedDeriv 4 f) (Set.Icc (x₀ - h) (x₀ + h))) {t : ℝ}
    (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    ∃ ξ₀ ∈ Set.Icc (x₀ - h) (x₀ + h), ∃ ξ₁ ∈ Set.Icc (x₀ - h) (x₀ + h),
      h * |deriv (lagrangeRem (eqNode x₀ h 2) f) (x₀ + t * h)| ≤
        h ^ 3 * (1 / (9 * √3) * h * |iteratedDeriv 4 f ξ₁| + 1 / 3 * |iteratedDeriv 3 f ξ₀|) := by
  have e0 : x₀ + (eqN0 2 : ℝ) * h = x₀ - h := by rw [eqN0_two]; push_cast; ring
  have e1 : x₀ + (eqN1 2 : ℝ) * h = x₀ + h := by rw [eqN1_two]; push_cast; ring
  have hJ : Set.Ioo (-1 : ℝ) 1 ⊆ Set.Ioo (eqN0 2 : ℝ) (eqN1 2) := by
    rw [eqN0_two, eqN1_two]; push_cast; exact subset_rfl
  have := dlmf_3_4_4 hh 2 f hU hd (by rw [e0, e1]; exact hI) (by rw [e0, e1]; exact hc) hJ ht
  rw [e0, e1, dlmf_3_3_18] at this
  obtain ⟨ξ₀, h0, ξ₁, h1, hR⟩ := this
  exact ⟨ξ₀, h0, ξ₁, h1, by convert hR using 2; norm_num⟩

end Azurite.DLMF
