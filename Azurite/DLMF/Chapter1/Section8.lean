/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.PSeries

/-!
# DLMF §1.8: Fourier Series

Formalizations of <https://dlmf.nist.gov/1.8>, one theorem per equation, named `dlmf_1_8_N`;
statements made in the prose are named `dlmf_1_8_i_<topic>`.  Functions are `f : ℝ → ℂ` (real
or complex valued); integrals over `[−π, π]` are interval integrals.

## §1.8(i) Definitions and Elementary Properties

* 1.8.2 `fourierA`, `fourierB`; 1.8.4 `fourierC` (`dlmf_1_8_2_a`, `dlmf_1_8_2_b`,
  `dlmf_1_8_4`).  `fourierC_eq_fourierCoeffOn` identifies `cₙ` with Mathlib's
  `fourierCoeffOn` on `[−π, π]`, and `fourierCoeff_lift_eq` with `fourierCoeff` of the lift of a
  `2π`-periodic function to `AddCircle (2π)`.
* Relations `cₙ = (aₙ − i bₙ)/2`, `c₋ₙ = (aₙ + i bₙ)/2` (`fourierC_natCast`,
  `fourierC_neg_natCast`, `fourierC_zero`); even functions have `bₙ = 0`
  (`dlmf_1_8_i_even`), odd functions `aₙ = 0` (`dlmf_1_8_i_odd`).
* 1.8.1, 1.8.3 (`dlmf_1_8_1`, `dlmf_1_8_3`): DLMF writes the series formally; here a continuous
  `2π`-periodic `f` with summable `cₙ` is shown to be the pointwise sum of both series.
* Parseval 1.8.5, 1.8.6, 1.8.6_1, 1.8.6_2 for square-integrable `f`, `g`
  (`dlmf_1_8_5`, `dlmf_1_8_6`, `dlmf_1_8_6_1`, `dlmf_1_8_6_2`): 1.8.6 is Mathlib's
  `hasSum_sq_fourierCoeffOn`; 1.8.6_2 by polarization (`four_mul_mul_conj`,
  `fourierC_add_mul`); the real forms by pairing `n` with `−n` (`fourier_pair_mul_conj`).
  The `HasSum` statements carry `½ a₀ ā'₀` to the other side.
* 1.8.7 `dlmf_1_8_7`: `aₙ, bₙ, cₙ, c₋ₙ = o(n⁻ᵐ)`.  "`f⁽ᵐ⁾` piecewise continuous" is modelled by a
  chain `F 0 = f, …, F m`: `F 0, …, F (m−1)` continuous and `2π`-periodic, each `F (k+1)` the
  right derivative of `F k`, and `F m` integrable.  Repeated integration by parts
  (`fourierC_eq_div_of_hasDerivWithinAt`, `fourierC_iterate`) and Riemann–Lebesgue.
* Uniqueness `dlmf_1_8_i_uniqueness` (`cₙ`), `dlmf_1_8_i_uniqueness_ab` (`aₙ`, `bₙ`): from
  Parseval, `∫ |f − g|² = 0`.
* 1.8.8 `lebesgueConst`, `dlmf_1_8_8`; 1.8.9 `dlmf_1_8_9` (`Lₙ ∼ (4/π²) ln n`): `Lₙ` is within
  `1` of `(2/π) ∫₀^{(n+½)π} |sin u|/u du` (`lebesgueConst_bounds`, using
  `0 ≤ 1/sin u − 1/u ≤ 1`, `inv_sin_sub_inv_le_one`), which is within `3π/2` of `(2/π) Hₙ`
  (`sincAbs_bounds`, one period at a time: `piece_lower`, `piece_upper`), and
  `Hₙ = ln n + O(1)`.
* 1.8.10 `dlmf_1_8_10` (Riemann–Lebesgue, `λ → +∞`; also `dlmf_1_8_10_atBot`): from Mathlib's
  `Real.tendsto_integral_exp_smul_cocompact`.  It holds for every `f`, since a non-integrable
  `f` has integral `0`.

## §1.8(ii) Convergence

* 1.8.11 `dlmf_1_8_11` (Dirichlet): for `f` `2π`-periodic and integrable on a period, the partial
  sums `fourierPartialSum f N x` tend to `½f(x−) + ½f(x+)` at every `x` where `f` has one-sided
  derivatives.  The derivatives are based at the one-sided limits `f(x±)`, as Dirichlet's theorem
  requires: DLMF's literal reference to (1.4.4), based at `f(x)`, would rule out jumps.  DLMF's
  "continuous except at finitely many points" is not needed.  Proof: the Dirichlet kernel
  (`halfDirichlet`, `two_mul_halfDirichlet_mul_sin`, `integral_halfDirichlet`), the partial sum
  folded onto `[0, π]` (`fourierPartialSum_eq_integral`, `fourierPartialSum_eq_fold`),
  integrability of the Dirichlet quotient (`intervalIntegrable_dirichlet_quotient`) and the
  Riemann–Lebesgue lemma (`tendsto_integral_mul_sin`).
* `dlmf_1_8_ii_nonuniform`: if the partial sums converge uniformly on a neighbourhood of `x` to a
  limit equal to `f` away from `x`, then `f(x−) = f(x+)`, so convergence is non-uniform at a jump.

## §1.8(iii) Integration and Differentiation

* 1.8.12 `dlmf_1_8_12`: `∫₀^x (f − ½a₀) = ∑ (aₙ sin(nx) + bₙ(1 − cos(nx)))/n` for every real `x`
  (DLMF: `0 ≤ x ≤ 2π`), for `f` `2π`-periodic and square-integrable on a period (piecewise
  continuous functions are).  Proof: Parseval 1.8.6_1 against the oriented indicator of
  `(0, x]` (`orientedIndicator`, `hasSum_integral_of_mem`), extended by periodicity.
* `dlmf_1_8_iii_deriv`: for a `2π`-periodic `f ∈ C²`, `f′(x) = ∑ n (bₙ cos(nx) − aₙ sin(nx))` at
  every `x`.  Integration by parts gives `cₙ(f′) = in cₙ(f)` (`fourierC_deriv`,
  `fourierA_deriv`, `fourierB_deriv`).  Applied twice, it makes the `cₙ(f′)` absolutely summable,
  since `|cₙ(f′)| ≤ (|cₙ(f″)|² + n⁻²)/2`.  Then 1.8.1 applies to `f′`.
-/

namespace Azurite.DLMF

open MeasureTheory Set Filter Topology Real
open scoped ComplexConjugate

/-! ### §1.8(i) Definitions -/

/-- **DLMF 1.8.2**: the Fourier cosine coefficients `aₙ = (1/π) ∫_{−π}^{π} f(x) cos(nx) dx`. -/
noncomputable def fourierA (f : ℝ → ℂ) (n : ℕ) : ℂ :=
  (1 / π : ℝ) • ∫ x in (-π)..π, f x * (Real.cos (n * x) : ℂ)

/-- **DLMF 1.8.2**: the Fourier sine coefficients `bₙ = (1/π) ∫_{−π}^{π} f(x) sin(nx) dx`. -/
noncomputable def fourierB (f : ℝ → ℂ) (n : ℕ) : ℂ :=
  (1 / π : ℝ) • ∫ x in (-π)..π, f x * (Real.sin (n * x) : ℂ)

/-- **DLMF 1.8.4**: the complex Fourier coefficients
`cₙ = (1/(2π)) ∫_{−π}^{π} f(x) e^{−inx} dx`. -/
noncomputable def fourierC (f : ℝ → ℂ) (n : ℤ) : ℂ :=
  (1 / (2 * π) : ℝ) • ∫ x in (-π)..π, f x * Complex.exp (-(n * x * Complex.I))

theorem dlmf_1_8_2_a (f : ℝ → ℂ) (n : ℕ) :
    fourierA f n = (1 / π : ℝ) • ∫ x in (-π)..π, f x * (Real.cos (n * x) : ℂ) := rfl

theorem dlmf_1_8_2_b (f : ℝ → ℂ) (n : ℕ) :
    fourierB f n = (1 / π : ℝ) • ∫ x in (-π)..π, f x * (Real.sin (n * x) : ℂ) := rfl

theorem dlmf_1_8_4 (f : ℝ → ℂ) (n : ℤ) :
    fourierC f n = (1 / (2 * π) : ℝ) • ∫ x in (-π)..π, f x * Complex.exp (-(n * x * Complex.I)) :=
  rfl

theorem neg_pi_lt_pi : -π < π := by linarith [Real.pi_pos]

/-- The coefficients `cₙ` are Mathlib's `fourierCoeffOn` on `[−π, π]`. -/
theorem fourierC_eq_fourierCoeffOn (f : ℝ → ℂ) (n : ℤ) :
    fourierC f n = fourierCoeffOn neg_pi_lt_pi f n := by
  rw [fourierCoeffOn_eq_integral, fourierC]
  congr 1
  · ring
  refine intervalIntegral.integral_congr fun x _ => ?_
  have hexp : fourier (-n) (x : AddCircle (π - -π)) = Complex.exp (-(n * x * Complex.I)) := by
    rw [fourier_coe_apply]
    congr 1
    push_cast
    field_simp
    ring
  simp only [hexp, smul_eq_mul]
  ring

instance fact_two_pi_pos : Fact (0 < 2 * π) := ⟨by positivity⟩

/-- For a `2π`-periodic `f`, the `cₙ` are the Fourier coefficients of `f` on `AddCircle (2π)`. -/
theorem fourierCoeff_lift_eq {f : ℝ → ℂ} (hper : Function.Periodic f (2 * π)) (n : ℤ) :
    fourierCoeff (T := 2 * π) hper.lift n = fourierC f n := by
  rw [fourierCoeff_eq_intervalIntegral _ _ (-π), show -π + 2 * π = π by ring, fourierC]
  congr 1
  refine intervalIntegral.integral_congr fun x _ => ?_
  have hexp : fourier (-n) (x : AddCircle (2 * π)) = Complex.exp (-(n * x * Complex.I)) := by
    rw [fourier_coe_apply]
    congr 1
    push_cast
    field_simp
  simp only [hexp, smul_eq_mul, Function.Periodic.lift_coe]
  ring

theorem intervalIntegrable_mul_cos {f : ℝ → ℂ} (hf : IntervalIntegrable f volume (-π) π)
    (c : ℝ) : IntervalIntegrable (fun x => f x * (Real.cos (c * x) : ℂ)) volume (-π) π :=
  hf.mul_continuousOn (Complex.continuous_ofReal.comp
    (Real.continuous_cos.comp (continuous_const.mul continuous_id))).continuousOn

theorem intervalIntegrable_mul_sin {f : ℝ → ℂ} (hf : IntervalIntegrable f volume (-π) π)
    (c : ℝ) : IntervalIntegrable (fun x => f x * (Real.sin (c * x) : ℂ)) volume (-π) π :=
  hf.mul_continuousOn (Complex.continuous_ofReal.comp
    (Real.continuous_sin.comp (continuous_const.mul continuous_id))).continuousOn

theorem exp_neg_mul_I_eq (n : ℝ) (x : ℝ) :
    Complex.exp (-(n * x * Complex.I)) =
      (Real.cos (n * x) : ℂ) - Complex.I * (Real.sin (n * x) : ℂ) := by
  rw [show -((n : ℂ) * x * Complex.I) = ((-(n * x) : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

theorem exp_mul_I_eq (n : ℝ) (x : ℝ) :
    Complex.exp (n * x * Complex.I) =
      (Real.cos (n * x) : ℂ) + Complex.I * (Real.sin (n * x) : ℂ) := by
  rw [show (n : ℂ) * x * Complex.I = ((n * x : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  ring

/-- **DLMF §1.8(i)**: `cₙ = (aₙ − i bₙ)/2` (for `n = 0`, `c₀ = a₀/2` since `b₀ = 0`). -/
theorem fourierC_natCast {f : ℝ → ℂ} (hf : IntervalIntegrable f volume (-π) π) (n : ℕ) :
    fourierC f n = (fourierA f n - Complex.I * fourierB f n) / 2 := by
  have e : ∀ x : ℝ, f x * Complex.exp (-(((n : ℤ) : ℂ) * x * Complex.I)) =
      f x * (Real.cos (n * x) : ℂ) - Complex.I * (f x * (Real.sin (n * x) : ℂ)) := fun x => by
    rw [show (((n : ℤ) : ℂ)) = ((n : ℝ) : ℂ) by push_cast; rfl, exp_neg_mul_I_eq]
    ring
  rw [fourierC, intervalIntegral.integral_congr fun x _ => e x,
    intervalIntegral.integral_sub (intervalIntegrable_mul_cos hf _)
      ((intervalIntegrable_mul_sin hf _).const_mul _),
    intervalIntegral.integral_const_mul, fourierA, fourierB]
  simp only [Complex.real_smul]
  push_cast
  field_simp

/-- **DLMF §1.8(i)**: `c₋ₙ = (aₙ + i bₙ)/2`. -/
theorem fourierC_neg_natCast {f : ℝ → ℂ} (hf : IntervalIntegrable f volume (-π) π) (n : ℕ) :
    fourierC f (-n) = (fourierA f n + Complex.I * fourierB f n) / 2 := by
  have e : ∀ x : ℝ, f x * Complex.exp (-(((-(n : ℤ) : ℤ) : ℂ) * x * Complex.I)) =
      f x * (Real.cos (n * x) : ℂ) + Complex.I * (f x * (Real.sin (n * x) : ℂ)) := fun x => by
    rw [show -(((-(n : ℤ) : ℤ) : ℂ) * x * Complex.I) = ((n : ℝ) : ℂ) * x * Complex.I by
      push_cast; ring, exp_mul_I_eq]
    ring
  rw [fourierC, intervalIntegral.integral_congr fun x _ => e x,
    intervalIntegral.integral_add (intervalIntegrable_mul_cos hf _)
      ((intervalIntegrable_mul_sin hf _).const_mul _),
    intervalIntegral.integral_const_mul, fourierA, fourierB]
  simp only [Complex.real_smul]
  push_cast
  field_simp

theorem fourierB_zero (f : ℝ → ℂ) : fourierB f 0 = 0 := by
  simp [fourierB]

/-- **DLMF §1.8(i)**: if `f(−x) = f(x)` then `bₙ = 0` for all `n`. -/
theorem dlmf_1_8_i_even {f : ℝ → ℂ} (heven : ∀ x, f (-x) = f x) (n : ℕ) : fourierB f n = 0 := by
  have h := intervalIntegral.integral_comp_neg (a := -π) (b := π)
    (fun x => f x * (Real.sin (n * x) : ℂ))
  simp only [neg_neg, heven, mul_neg, Real.sin_neg, Complex.ofReal_neg,
    intervalIntegral.integral_neg] at h
  rw [fourierB, show (∫ x in (-π)..π, f x * (Real.sin (n * x) : ℂ)) = 0 by
    linear_combination (-1 / 2 : ℂ) * h, smul_zero]

/-- **DLMF §1.8(i)**: if `f(−x) = −f(x)` then `aₙ = 0` for all `n`. -/
theorem dlmf_1_8_i_odd {f : ℝ → ℂ} (hodd : ∀ x, f (-x) = -f x) (n : ℕ) : fourierA f n = 0 := by
  have h := intervalIntegral.integral_comp_neg (a := -π) (b := π)
    (fun x => f x * (Real.cos (n * x) : ℂ))
  simp only [neg_neg, hodd, mul_neg, Real.cos_neg, neg_mul, intervalIntegral.integral_neg] at h
  rw [fourierA, show (∫ x in (-π)..π, f x * (Real.cos (n * x) : ℂ)) = 0 by
    linear_combination (-1 / 2 : ℂ) * h, smul_zero]

/-! ### The Fourier series -/

/-- **DLMF 1.8.3**: a continuous `2π`-periodic `f` with summable `cₙ` is the sum of its Fourier
series `∑ₙ cₙ e^{inx}` at every `x` (DLMF writes the series "formally"; see §1.8(ii) for
convergence). -/
theorem dlmf_1_8_3 {f : ℝ → ℂ} (hper : Function.Periodic f (2 * π)) (hc : Continuous f)
    (hs : Summable (fourierC f)) (x : ℝ) :
    HasSum (fun n : ℤ => fourierC f n * Complex.exp (n * x * Complex.I)) (f x) := by
  let F : C(AddCircle (2 * π), ℂ) := ⟨hper.lift, hc.quotient_liftOn' _⟩
  have hF : ∀ n, fourierCoeff F n = fourierC f n := fourierCoeff_lift_eq hper
  have h := has_pointwise_sum_fourier_series_of_summable (f := F)
    (by rw [show fourierCoeff ⇑F = fourierC f from funext hF]; exact hs) (x : AddCircle (2 * π))
  convert h using 1
  · funext n
    have hexp : fourier n (x : AddCircle (2 * π)) = Complex.exp (n * x * Complex.I) := by
      rw [fourier_coe_apply]
      congr 1
      push_cast
      field_simp
    rw [hF, smul_eq_mul, hexp]
  · rfl

/-- **DLMF 1.8.1**: a continuous `2π`-periodic `f` with summable `cₙ` satisfies
`f(x) = ½a₀ + ∑_{n ≥ 1} (aₙ cos(nx) + bₙ sin(nx))`. -/
theorem dlmf_1_8_1 {f : ℝ → ℂ} (hper : Function.Periodic f (2 * π)) (hc : Continuous f)
    (hs : Summable (fourierC f)) (x : ℝ) :
    HasSum (fun n : ℕ => fourierA f (n + 1) * (Real.cos ((n + 1 : ℕ) * x) : ℂ) +
      fourierB f (n + 1) * (Real.sin ((n + 1 : ℕ) * x) : ℂ)) (f x - fourierA f 0 / 2) := by
  have hf : IntervalIntegrable f volume (-π) π := hc.intervalIntegrable _ _
  have h := (dlmf_1_8_3 hper hc hs x).nat_add_neg
  have e : ∀ n : ℕ, fourierC f n * Complex.exp ((n : ℤ) * x * Complex.I) +
      fourierC f (-n) * Complex.exp (((-n : ℤ) : ℂ) * x * Complex.I) =
      fourierA f n * (Real.cos (n * x) : ℂ) + fourierB f n * (Real.sin (n * x) : ℂ) := by
    intro n
    rw [fourierC_natCast hf, fourierC_neg_natCast hf,
      show (((n : ℤ) : ℂ)) = ((n : ℝ) : ℂ) by push_cast; rfl,
      show ((((-n : ℤ)) : ℂ)) * x * Complex.I = -(((n : ℝ) : ℂ) * x * Complex.I) by
        push_cast; ring, exp_mul_I_eq, exp_neg_mul_I_eq]
    ring_nf
    rw [Complex.I_sq]
    ring
  simp only [e, Int.cast_zero, zero_mul, Complex.exp_zero, mul_one] at h
  rw [show fourierC f 0 = fourierA f 0 / 2 by
    simpa [fourierB_zero] using fourierC_natCast hf 0] at h
  have h1 := (hasSum_nat_add_iff' 1).mpr h
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_mul, Real.cos_zero,
    Real.sin_zero, Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, add_zero] at h1
  convert h1 using 1
  ring

/-! ### Parseval's formula -/

theorem intervalIntegrable_of_memLp {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc (-π) π))) : IntervalIntegrable f volume (-π) π :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le neg_pi_lt_pi.le).mpr (hf.integrable one_le_two)

theorem intervalIntegrable_sq_norm_of_memLp {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc (-π) π))) :
    IntervalIntegrable (fun x => ‖f x‖ ^ 2) volume (-π) π :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le neg_pi_lt_pi.le).mpr
    ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf)

/-- **DLMF 1.8.6** (Parseval's formula): for `f` square-integrable on `[−π, π]`,
`(1/(2π)) ∫_{−π}^{π} |f(x)|² dx = ∑_{n ∈ ℤ} |cₙ|²`. -/
theorem dlmf_1_8_6 {f : ℝ → ℂ} (hf : MemLp f 2 (volume.restrict (Ioc (-π) π))) :
    HasSum (fun n : ℤ => ‖fourierC f n‖ ^ 2) (1 / (2 * π) * ∫ x in (-π)..π, ‖f x‖ ^ 2) := by
  have h := hasSum_sq_fourierCoeffOn neg_pi_lt_pi hf
  simp only [← fourierC_eq_fourierCoeffOn, smul_eq_mul] at h
  convert h using 2
  ring

theorem fourierC_add_mul {f g : ℝ → ℂ} (hf : IntervalIntegrable f volume (-π) π)
    (hg : IntervalIntegrable g volume (-π) π) (z : ℂ) (n : ℤ) :
    fourierC (fun x => f x + z * g x) n = fourierC f n + z * fourierC g n := by
  have hc : ContinuousOn (fun x : ℝ => Complex.exp (-(n * x * Complex.I))) (uIcc (-π) π) :=
    (by fun_prop : Continuous fun x : ℝ => Complex.exp (-(n * x * Complex.I))).continuousOn
  have e : ∀ x : ℝ, (f x + z * g x) * Complex.exp (-(n * x * Complex.I)) =
      f x * Complex.exp (-(n * x * Complex.I)) + z * (g x * Complex.exp (-(n * x * Complex.I))) :=
    fun x => by ring
  rw [fourierC, intervalIntegral.integral_congr fun x _ => e x,
    intervalIntegral.integral_add (hf.mul_continuousOn hc) ((hg.mul_continuousOn hc).const_mul z),
    intervalIntegral.integral_const_mul, fourierC, fourierC]
  simp only [Complex.real_smul]
  ring

/-- Polarization: `4 u v̄ = |u + v|² − |u − v|² + i (|u + iv|² − |u − iv|²)`. -/
theorem four_mul_mul_conj (u v : ℂ) :
    4 * (u * conj v) = ((‖u + 1 * v‖ ^ 2 - ‖u + -1 * v‖ ^ 2 : ℝ) : ℂ) +
      Complex.I * ((‖u + Complex.I * v‖ ^ 2 - ‖u + -Complex.I * v‖ ^ 2 : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [Complex.sq_norm, Complex.normSq_apply] <;> ring

/-- **DLMF 1.8.6_2** (Parseval's formula, polarized): for `f`, `g` square-integrable on
`[−π, π]`, `(1/(2π)) ∫_{−π}^{π} f(x) ḡ(x) dx = ∑_{n ∈ ℤ} cₙ c̄'ₙ`. -/
theorem dlmf_1_8_6_2 {f g : ℝ → ℂ} (hf : MemLp f 2 (volume.restrict (Ioc (-π) π)))
    (hg : MemLp g 2 (volume.restrict (Ioc (-π) π))) :
    HasSum (fun n : ℤ => fourierC f n * conj (fourierC g n))
      (1 / (2 * π) * ∫ x in (-π)..π, f x * conj (g x)) := by
  have hfi := intervalIntegrable_of_memLp hf
  have hgi := intervalIntegrable_of_memLp hg
  have hm : ∀ z : ℂ, MemLp (fun x => f x + z * g x) 2 (volume.restrict (Ioc (-π) π)) :=
    fun z => hf.add (hg.const_mul z)
  have P : ∀ z : ℂ, HasSum (fun n => ‖fourierC f n + z * fourierC g n‖ ^ 2)
      (1 / (2 * π) * ∫ x in (-π)..π, ‖f x + z * g x‖ ^ 2) := fun z => by
    have := dlmf_1_8_6 (hm z)
    simpa only [fourierC_add_mul hfi hgi] using this
  have Q : ∀ z : ℂ, IntervalIntegrable (fun x => ‖f x + z * g x‖ ^ 2) volume (-π) π :=
    fun z => intervalIntegrable_sq_norm_of_memLp (hm z)
  have H := ((Complex.hasSum_ofReal.mpr ((P 1).sub (P (-1)))).add
    ((Complex.hasSum_ofReal.mpr ((P Complex.I).sub (P (-Complex.I)))).mul_left
      Complex.I)).div_const 4
  convert H using 1
  · funext n
    rw [← four_mul_mul_conj]
    ring
  · have hR : ∀ z w : ℂ, IntervalIntegrable
        (fun x => (((‖f x + z * g x‖ ^ 2 - ‖f x + w * g x‖ ^ 2 : ℝ)) : ℂ)) volume (-π) π :=
      fun z w => ⟨((Q z).sub (Q w)).1.ofReal, ((Q z).sub (Q w)).2.ofReal⟩
    have hint : ∫ x in (-π)..π, f x * conj (g x) =
        ((∫ x in (-π)..π, (((‖f x + 1 * g x‖ ^ 2 - ‖f x + -1 * g x‖ ^ 2 : ℝ)) : ℂ)) +
          Complex.I * ∫ x in (-π)..π,
            (((‖f x + Complex.I * g x‖ ^ 2 - ‖f x + -Complex.I * g x‖ ^ 2 : ℝ)) : ℂ)) / 4 := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add (hR 1 (-1))
        ((hR Complex.I (-Complex.I)).const_mul _), ← intervalIntegral.integral_div]
      refine intervalIntegral.integral_congr fun x _ => ?_
      rw [← four_mul_mul_conj]
      ring
    rw [hint, intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal,
      intervalIntegral.integral_sub (Q 1) (Q (-1)),
      intervalIntegral.integral_sub (Q Complex.I) (Q (-Complex.I))]
    push_cast
    ring

theorem fourier_pair_mul_conj {f g : ℝ → ℂ} (hf : IntervalIntegrable f volume (-π) π)
    (hg : IntervalIntegrable g volume (-π) π) (n : ℕ) :
    fourierC f n * conj (fourierC g n) + fourierC f (-n) * conj (fourierC g (-n)) =
      (fourierA f n * conj (fourierA g n) + fourierB f n * conj (fourierB g n)) / 2 := by
  rw [fourierC_natCast hf, fourierC_natCast hg, fourierC_neg_natCast hf, fourierC_neg_natCast hg]
  simp only [map_div₀, map_sub, map_add, map_mul, Complex.conj_I, map_ofNat]
  linear_combination (-(fourierB f n * conj (fourierB g n)) / 2) * Complex.I_sq

theorem fourierC_zero {f : ℝ → ℂ} (hf : IntervalIntegrable f volume (-π) π) :
    fourierC f 0 = fourierA f 0 / 2 := by
  simpa [fourierB_zero] using fourierC_natCast hf 0

/-- **DLMF 1.8.6_1** (Parseval's formula, polarized, real form): for `f`, `g` square-integrable
on `[−π, π]`, `(1/π) ∫_{−π}^{π} f ḡ = ½ a₀ ā'₀ + ∑_{n ≥ 1} (aₙ ā'ₙ + bₙ b̄'ₙ)`. -/
theorem dlmf_1_8_6_1 {f g : ℝ → ℂ} (hf : MemLp f 2 (volume.restrict (Ioc (-π) π)))
    (hg : MemLp g 2 (volume.restrict (Ioc (-π) π))) :
    HasSum (fun n : ℕ => fourierA f (n + 1) * conj (fourierA g (n + 1)) +
        fourierB f (n + 1) * conj (fourierB g (n + 1)))
      (1 / π * (∫ x in (-π)..π, f x * conj (g x)) -
        fourierA f 0 * conj (fourierA g 0) / 2) := by
  have hfi := intervalIntegrable_of_memLp hf
  have hgi := intervalIntegrable_of_memLp hg
  have h := (dlmf_1_8_6_2 hf hg).nat_add_neg
  simp only [fourier_pair_mul_conj hfi hgi] at h
  rw [fourierC_zero hfi, fourierC_zero hgi] at h
  have h1 := (hasSum_nat_add_iff' 1).mpr (h.mul_left 2)
  simp only [Finset.range_one, Finset.sum_singleton, fourierB_zero] at h1
  convert h1 using 1
  · funext n; ring
  · simp only [map_div₀, map_ofNat]; field_simp; ring

/-- **DLMF 1.8.5** (Parseval's formula, real form): for `f` square-integrable on `[−π, π]`,
`(1/π) ∫_{−π}^{π} |f(x)|² dx = ½|a₀|² + ∑_{n ≥ 1} (|aₙ|² + |bₙ|²)`. -/
theorem dlmf_1_8_5 {f : ℝ → ℂ} (hf : MemLp f 2 (volume.restrict (Ioc (-π) π))) :
    HasSum (fun n : ℕ => ‖fourierA f (n + 1)‖ ^ 2 + ‖fourierB f (n + 1)‖ ^ 2)
      (1 / π * (∫ x in (-π)..π, ‖f x‖ ^ 2) - ‖fourierA f 0‖ ^ 2 / 2) := by
  rw [← Complex.hasSum_ofReal]
  have h := dlmf_1_8_6_1 hf hf
  have hsq : ∀ z : ℂ, z * conj z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [hsq] at h
  rw [intervalIntegral.integral_ofReal] at h
  convert h using 1
  · funext n; push_cast; ring
  · push_cast; ring

/-! ### Uniqueness -/

theorem memLp_of_continuous {f : ℝ → ℂ} (hf : Continuous f) :
    MemLp f 2 (volume.restrict (Ioc (-π) π)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (-π) π) hf.continuousOn
  exact MemLp.of_bound hf.aestronglyMeasurable C
    (ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => hC x (Ioc_subset_Icc_self hx))

/-- A continuous `2π`-periodic function whose Fourier coefficients `cₙ` all vanish is zero. -/
theorem eq_zero_of_fourierC_eq_zero {h : ℝ → ℂ} (hper : Function.Periodic h (2 * π))
    (hc : Continuous h) (h0 : ∀ n, fourierC h n = 0) : h = 0 := by
  have hP := dlmf_1_8_6 (memLp_of_continuous hc)
  simp only [h0, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hP
  have hI : ∫ x in (-π)..π, ‖h x‖ ^ 2 = 0 := by
    have := hP.unique hasSum_zero
    have hπ : (0 : ℝ) < 2 * π := by positivity
    field_simp at this
    exact this.trans (mul_zero _)
  have hcont : Continuous fun x => ‖h x‖ ^ 2 := by fun_prop
  have hae := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae neg_pi_lt_pi.le
    (ae_of_all _ fun x => by positivity) (hcont.intervalIntegrable _ _)).mp hI
  have hIoo : EqOn (fun x => ‖h x‖ ^ 2) 0 (Ioo (-π) π) :=
    Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioc_self hae)
      isOpen_Ioo hcont.continuousOn continuousOn_const
  have hIcc : EqOn h 0 (Icc (-π) π) := by
    rw [← closure_Ioo neg_pi_lt_pi.ne]
    refine EqOn.closure (fun x hx => ?_) hc continuous_const
    have := hIoo hx
    simpa using this
  funext x
  have hmem := toIocMod_mem_Ioc (by positivity : (0 : ℝ) < 2 * π) (-π) x
  rw [← hper.sub_zsmul_eq (toIocDiv (by positivity : (0 : ℝ) < 2 * π) (-π) x),
    self_sub_toIocDiv_zsmul]
  exact hIcc ⟨hmem.1.le, by linarith [hmem.2]⟩

/-- **DLMF §1.8(i)** (uniqueness of Fourier series): continuous `2π`-periodic functions with the
same Fourier coefficients `cₙ` are equal. -/
theorem dlmf_1_8_i_uniqueness {f g : ℝ → ℂ} (hfp : Function.Periodic f (2 * π))
    (hgp : Function.Periodic g (2 * π)) (hf : Continuous f) (hg : Continuous g)
    (hc : ∀ n, fourierC f n = fourierC g n) : f = g := by
  have h := eq_zero_of_fourierC_eq_zero (h := fun x => f x + (-1) * g x)
    (fun x => by simp only [hfp x, hgp x]) (by fun_prop) fun n => by
      rw [fourierC_add_mul (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _), hc n]; ring
  funext x
  have := congrFun h x
  simp only [Pi.zero_apply] at this
  linear_combination this

/-- **DLMF §1.8(i)** (uniqueness of Fourier series), with the coefficients `aₙ`, `bₙ`. -/
theorem dlmf_1_8_i_uniqueness_ab {f g : ℝ → ℂ} (hfp : Function.Periodic f (2 * π))
    (hgp : Function.Periodic g (2 * π)) (hf : Continuous f) (hg : Continuous g)
    (ha : ∀ n, fourierA f n = fourierA g n) (hb : ∀ n, fourierB f n = fourierB g n) : f = g := by
  refine dlmf_1_8_i_uniqueness hfp hgp hf hg fun n => ?_
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [fourierC_natCast (hf.intervalIntegrable _ _), fourierC_natCast (hg.intervalIntegrable _ _),
      ha, hb]
  · rw [fourierC_neg_natCast (hf.intervalIntegrable _ _),
      fourierC_neg_natCast (hg.intervalIntegrable _ _), ha, hb]

/-! ### The Riemann–Lebesgue lemma -/

theorem tendsto_setIntegral_Ioc_mul_exp (f : ℝ → ℂ) (a b : ℝ) :
    Tendsto (fun l : ℝ => ∫ x in Ioc a b, f x * Complex.exp (l * x * Complex.I))
      (cocompact ℝ) (𝓝 0) := by
  have hRL := Real.tendsto_integral_exp_smul_cocompact ((Ioc a b).indicator f)
  have h2π : 0 < 2 * π := by positivity
  have hw : Tendsto (fun l : ℝ => -(l / (2 * π))) (cocompact ℝ) (cocompact ℝ) := by
    rw [cocompact_eq_atBot_atTop]
    refine Tendsto.sup ?_ ?_
    · exact (tendsto_neg_atBot_atTop.comp (tendsto_id.atBot_div_const h2π)).mono_right
        le_sup_right
    · exact (tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_div_const h2π)).mono_right
        le_sup_left
  refine (hRL.comp hw).congr fun l => ?_
  simp only [Function.comp_apply]
  rw [← integral_indicator measurableSet_Ioc]
  congr 1
  funext v
  by_cases hv : v ∈ Ioc a b
  · rw [indicator_of_mem hv, Circle.smul_def, Real.fourierChar_apply, indicator_of_mem hv,
      smul_eq_mul, mul_comm (f v)]
    congr 2
    push_cast
    field_simp
  · simp [indicator_of_notMem hv]

/-- The Riemann–Lebesgue lemma on an interval, as `|λ| → ∞`.  It holds for every `f`: when `f`
is not integrable the integral is `0`. -/
theorem tendsto_intervalIntegral_mul_exp_cocompact (f : ℝ → ℂ) (a b : ℝ) :
    Tendsto (fun l : ℝ => ∫ x in a..b, f x * Complex.exp (l * x * Complex.I))
      (cocompact ℝ) (𝓝 0) := by
  have := (tendsto_setIntegral_Ioc_mul_exp f a b).sub (tendsto_setIntegral_Ioc_mul_exp f b a)
  rw [sub_zero] at this
  exact this

/-- **DLMF 1.8.10** (Riemann–Lebesgue lemma): `∫_a^b f(x) e^{iλx} dx → 0` as `λ → ∞`. -/
theorem dlmf_1_8_10 (f : ℝ → ℂ) (a b : ℝ) :
    Tendsto (fun l : ℝ => ∫ x in a..b, f x * Complex.exp (l * x * Complex.I)) atTop (𝓝 0) :=
  (tendsto_intervalIntegral_mul_exp_cocompact f a b).mono_left atTop_le_cocompact

/-- **DLMF 1.8.10** as `λ → −∞`. -/
theorem dlmf_1_8_10_atBot (f : ℝ → ℂ) (a b : ℝ) :
    Tendsto (fun l : ℝ => ∫ x in a..b, f x * Complex.exp (l * x * Complex.I)) atBot (𝓝 0) :=
  (tendsto_intervalIntegral_mul_exp_cocompact f a b).mono_left atBot_le_cocompact

theorem tendsto_fourierC_atTop (f : ℝ → ℂ) :
    Tendsto (fun n : ℕ => fourierC f n) atTop (𝓝 0) := by
  have h := ((dlmf_1_8_10_atBot f (-π) π).comp
    (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)).const_smul (1 / (2 * π) : ℝ)
  rw [smul_zero] at h
  refine h.congr fun n => ?_
  simp only [Function.comp_apply, fourierC]
  congr 1
  refine intervalIntegral.integral_congr fun x _ => ?_
  push_cast
  ring_nf

theorem tendsto_fourierC_neg_atTop (f : ℝ → ℂ) :
    Tendsto (fun n : ℕ => fourierC f (-n)) atTop (𝓝 0) := by
  have h := ((dlmf_1_8_10 f (-π) π).comp tendsto_natCast_atTop_atTop).const_smul
    (1 / (2 * π) : ℝ)
  rw [smul_zero] at h
  refine h.congr fun n => ?_
  simp only [Function.comp_apply, fourierC]
  congr 1
  refine intervalIntegral.integral_congr fun x _ => ?_
  push_cast
  ring_nf

/-! ### Asymptotic estimates of coefficients -/

/-- Integration by parts: for a continuous `2π`-periodic `f` with right derivative `f'`
(integrable), `cₙ(f) = cₙ(f') / (in)` for `n ≠ 0`. -/
theorem fourierC_eq_div_of_hasDerivWithinAt {f f' : ℝ → ℂ} (hper : Function.Periodic f (2 * π))
    (hc : Continuous f) (hd : ∀ x, HasDerivWithinAt f (f' x) (Ioi x) x)
    (hi : IntervalIntegrable f' volume (-π) π) {n : ℤ} (hn : n ≠ 0) :
    fourierC f n = fourierC f' n / (n * Complex.I) := by
  rw [fourierC_eq_fourierCoeffOn, fourierC_eq_fourierCoeffOn,
    fourierCoeffOn_of_hasDeriv_right neg_pi_lt_pi hn hc.continuousOn (fun x _ => hd x) hi]
  have hper' : f π = f (-π) := by
    have := hper (-π)
    rwa [show -π + 2 * π = π by ring] at this
  rw [hper', sub_self, mul_zero, zero_sub]
  have hn' : (n : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp
  ring

/-- Repeated integration by parts: `cₙ(f) = cₙ(f⁽ᵐ⁾) / (in)ᵐ`. -/
theorem fourierC_iterate {m : ℕ} (F : ℕ → ℝ → ℂ)
    (hper : ∀ k < m, Function.Periodic (F k) (2 * π)) (hc : ∀ k < m, Continuous (F k))
    (hd : ∀ k < m, ∀ x, HasDerivWithinAt (F k) (F (k + 1) x) (Ioi x) x)
    (hi : IntervalIntegrable (F m) volume (-π) π) {n : ℤ} (hn : n ≠ 0) :
    fourierC (F 0) n = fourierC (F m) n / (n * Complex.I) ^ m := by
  have hint : ∀ k ≤ m, IntervalIntegrable (F k) volume (-π) π := fun k hk => by
    rcases hk.lt_or_eq with hk | rfl
    · exact (hc k hk).intervalIntegrable _ _
    · exact hi
  have key : ∀ k ≤ m, fourierC (F 0) n = fourierC (F k) n / (n * Complex.I) ^ k := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      rw [ih (by omega), fourierC_eq_div_of_hasDerivWithinAt (hper k (by omega)) (hc k (by omega))
        (hd k (by omega)) (hint (k + 1) hk) hn]
      ring
  exact key m le_rfl

theorem isLittleO_of_tendsto_pow_mul {m : ℕ} {u : ℕ → ℂ}
    (h : Tendsto (fun n : ℕ => (n : ℂ) ^ m * u n) atTop (𝓝 0)) :
    u =o[atTop] fun n => ((n : ℝ) ^ m)⁻¹ := by
  refine Asymptotics.isLittleO_iff.mpr fun c hc => ?_
  filter_upwards [(Metric.tendsto_nhds.mp h) c hc, eventually_ge_atTop 1] with n hn hn1
  rw [dist_zero_right, norm_mul, norm_pow, Complex.norm_natCast] at hn
  have hpos : (0 : ℝ) < (n : ℝ) ^ m := pow_pos (by exact_mod_cast hn1) m
  rw [norm_inv, norm_pow, Real.norm_natCast, ← div_eq_mul_inv, le_div_iff₀ hpos]
  linarith

/-- **DLMF 1.8.7**: if `f` is `2π`-periodic and `f⁽ᵐ⁾` is piecewise continuous, then
`aₙ, bₙ, cₙ = o(n⁻ᵐ)` as `n → ∞`.  Here `F k` plays `f⁽ᵏ⁾`: `F 0 = f`, …, `F (m−1)` are
continuous and `2π`-periodic, each `F (k+1)` is the right derivative of `F k`, and `F m` is
integrable on `[−π, π]` (this covers piecewise continuous `f⁽ᵐ⁾`, whose right-continuous version
is the right derivative of `f⁽ᵐ⁻¹⁾`).  The statement for `cₙ` is given for `n` and `−n`. -/
theorem dlmf_1_8_7 {m : ℕ} (F : ℕ → ℝ → ℂ)
    (hper : ∀ k < m, Function.Periodic (F k) (2 * π)) (hc : ∀ k < m, Continuous (F k))
    (hd : ∀ k < m, ∀ x, HasDerivWithinAt (F k) (F (k + 1) x) (Ioi x) x)
    (hi : IntervalIntegrable (F m) volume (-π) π) :
    (fun n : ℕ => fourierA (F 0) n) =o[atTop] (fun n => ((n : ℝ) ^ m)⁻¹) ∧
      (fun n : ℕ => fourierB (F 0) n) =o[atTop] (fun n => ((n : ℝ) ^ m)⁻¹) ∧
      (fun n : ℕ => fourierC (F 0) n) =o[atTop] (fun n => ((n : ℝ) ^ m)⁻¹) ∧
      (fun n : ℕ => fourierC (F 0) (-n)) =o[atTop] (fun n => ((n : ℝ) ^ m)⁻¹) := by
  have hF0 : IntervalIntegrable (F 0) volume (-π) π := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact hi
    · exact (hc 0 hm).intervalIntegrable _ _
  have hIm : Complex.I ^ m ≠ 0 := pow_ne_zero _ Complex.I_ne_zero
  have hpos : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  have hcp : Tendsto (fun n : ℕ => (n : ℂ) ^ m * fourierC (F 0) n) atTop (𝓝 0) := by
    have := (tendsto_fourierC_atTop (F m)).div_const (Complex.I ^ m)
    rw [zero_div] at this
    refine this.congr' (hpos.mono fun n hn => ?_)
    have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    show fourierC (F m) (n : ℤ) / Complex.I ^ m = (n : ℂ) ^ m * fourierC (F 0) (n : ℤ)
    rw [fourierC_iterate F hper hc hd hi hn0]
    push_cast
    rw [mul_pow]
    field_simp
  have hcn : Tendsto (fun n : ℕ => (n : ℂ) ^ m * fourierC (F 0) (-n)) atTop (𝓝 0) := by
    have := (tendsto_fourierC_neg_atTop (F m)).div_const ((-Complex.I) ^ m)
    rw [zero_div] at this
    refine this.congr' (hpos.mono fun n hn => ?_)
    have hn0 : (-(n : ℤ)) ≠ 0 := by
      have : (n : ℤ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      exact neg_ne_zero.mpr this
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    show fourierC (F m) (-(n : ℤ)) / (-Complex.I) ^ m = (n : ℂ) ^ m * fourierC (F 0) (-(n : ℤ))
    rw [fourierC_iterate F hper hc hd hi hn0]
    push_cast
    rw [show (-(n : ℂ) * Complex.I) = (n : ℂ) * -Complex.I by ring, mul_pow]
    field_simp
  have ha : ∀ n : ℕ, fourierA (F 0) n = fourierC (F 0) n + fourierC (F 0) (-n) := fun n => by
    rw [fourierC_natCast hF0, fourierC_neg_natCast hF0]; ring
  have hb : ∀ n : ℕ, fourierB (F 0) n =
      Complex.I * (fourierC (F 0) n - fourierC (F 0) (-n)) := fun n => by
    rw [fourierC_natCast hF0, fourierC_neg_natCast hF0]
    linear_combination (fourierB (F 0) n) * Complex.I_sq
  refine ⟨isLittleO_of_tendsto_pow_mul ?_, isLittleO_of_tendsto_pow_mul ?_,
    isLittleO_of_tendsto_pow_mul hcp, isLittleO_of_tendsto_pow_mul hcn⟩
  · simpa [ha, mul_add] using hcp.add hcn
  · have := (hcp.sub hcn).const_mul Complex.I
    rw [sub_zero, mul_zero] at this
    refine this.congr fun n => ?_
    rw [hb]; ring

/-! ### Lebesgue constants -/

/-- **DLMF 1.8.8**: the Lebesgue constants
`Lₙ = (1/π) ∫₀^π |sin((n + ½)t)| / sin(½t) dt`. -/
noncomputable def lebesgueConst (n : ℕ) : ℝ :=
  1 / π * ∫ t in (0 : ℝ)..π, |Real.sin ((n + 1 / 2) * t)| / Real.sin (t / 2)

theorem dlmf_1_8_8 (n : ℕ) :
    lebesgueConst n = 1 / π * ∫ t in (0 : ℝ)..π, |Real.sin ((n + 1 / 2) * t)| / Real.sin (t / 2) :=
  rfl

theorem intervalIntegrable_of_abs_le {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : Measurable f)
    (C : ℝ) (hC : ∀ x ∈ Ioc a b, |f x| ≤ C) : IntervalIntegrable f volume a b :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
    (IntegrableOn.of_bound measure_Ioc_lt_top hf.aestronglyMeasurable C
      (ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => by
        rw [Real.norm_eq_abs]; exact hC x hx))

/-- `0 ≤ 1/sin u − 1/u ≤ 1` on `(0, π/2]`. -/
theorem inv_sin_sub_inv_le_one {u : ℝ} (hu : 0 < u) (hu' : u ≤ π / 2) :
    1 / Real.sin u - 1 / u ≤ 1 := by
  have h1 := Real.sin_ge_sub_cube hu.le
  have h2 := Real.mul_le_sin hu.le hu'
  have hπ := Real.pi_pos
  have hπ4 := Real.pi_le_four
  have hs : 0 < Real.sin u := lt_of_lt_of_le (by positivity) h2
  rw [div_sub_div _ _ hs.ne' hu.ne', div_le_one (mul_pos hs hu)]
  have h3 : 2 / π * u * u ≤ Real.sin u * u := mul_le_mul_of_nonneg_right h2 hu.le
  have h5 : π * u ≤ 12 := by nlinarith
  have h4 : u ^ 3 / 6 ≤ 2 / π * u * u := by
    rw [show 2 / π * u * u = 2 * u ^ 2 / π by ring, le_div_iff₀ hπ]
    nlinarith [mul_le_mul_of_nonneg_left h5 (sq_nonneg u)]
  linarith

theorem measurable_abs_sin_div : Measurable fun u : ℝ => |Real.sin u| / u := by fun_prop

theorem abs_sin_div_le_one {u : ℝ} (hu : 0 < u) : |Real.sin u| / u ≤ 1 := by
  rw [div_le_one hu]
  exact Real.abs_sin_le_abs.trans (abs_of_pos hu).le

theorem intervalIntegrable_abs_sin_div {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun u => |Real.sin u| / u) volume a b :=
  intervalIntegrable_of_abs_le hab measurable_abs_sin_div 1 fun u hu => by
    have hu0 : 0 < u := ha.trans_lt hu.1
    rw [abs_of_nonneg (div_nonneg (abs_nonneg _) hu0.le)]
    exact abs_sin_div_le_one hu0

theorem integral_abs_sin_period (k : ℕ) :
    ∫ u in (k * π)..((k + 1) * π), |Real.sin u| = 2 := by
  have h := intervalIntegral.integral_comp_add_right (fun u => |Real.sin u|) (k * π)
    (a := 0) (b := π)
  rw [zero_add, show π + k * π = (k + 1) * π by ring] at h
  rw [← h, intervalIntegral.integral_congr (g := Real.sin) fun x hx => ?_, integral_sin,
    Real.cos_zero, Real.cos_pi]
  · norm_num
  · rw [Set.uIcc_of_le Real.pi_pos.le] at hx
    rw [Real.sin_add_nat_mul_pi, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hx.1 hx.2)]

theorem piece_lower (k : ℕ) :
    2 / ((k + 1) * π) ≤ ∫ u in (k * π)..((k + 1) * π), |Real.sin u| / u := by
  have hπ := Real.pi_pos
  have hle : (k : ℝ) * π ≤ (k + 1) * π := by nlinarith
  have hk0 : 0 ≤ (k : ℝ) * π := by positivity
  calc 2 / ((k + 1) * π) = ∫ u in (k * π)..((k + 1) * π), |Real.sin u| / ((k + 1) * π) := by
        rw [intervalIntegral.integral_div, integral_abs_sin_period]
    _ ≤ ∫ u in (k * π)..((k + 1) * π), |Real.sin u| / u := by
        refine intervalIntegral.integral_mono_on hle
          ((Real.continuous_sin.abs.div_const _).intervalIntegrable _ _)
          (intervalIntegrable_abs_sin_div hk0 hle) fun u hu => ?_
        rcases (hk0.trans hu.1).eq_or_lt with h0 | h0
        · rw [← h0]; simp
        · exact div_le_div_of_nonneg_left (abs_nonneg _) h0 hu.2

theorem piece_upper (k : ℕ) :
    ∫ u in ((k + 1) * π)..((k + 1 + 1) * π), |Real.sin u| / u ≤ 2 / ((k + 1) * π) := by
  have hπ := Real.pi_pos
  have hle : ((k : ℝ) + 1) * π ≤ (k + 1 + 1) * π := by nlinarith
  have hk0 : 0 < ((k : ℝ) + 1) * π := by positivity
  calc ∫ u in ((k + 1) * π)..((k + 1 + 1) * π), |Real.sin u| / u
      ≤ ∫ u in ((k + 1) * π)..((k + 1 + 1) * π), |Real.sin u| / ((k + 1) * π) := by
        refine intervalIntegral.integral_mono_on hle (intervalIntegrable_abs_sin_div hk0.le hle)
          ((Real.continuous_sin.abs.div_const _).intervalIntegrable _ _) fun u hu =>
            div_le_div_of_nonneg_left (abs_nonneg _) hk0 hu.1
    _ = 2 / ((k + 1) * π) := by
        rw [intervalIntegral.integral_div]
        have := integral_abs_sin_period (k + 1)
        push_cast at this
        rw [this]

theorem integral_abs_sin_div_le_length {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ u in a..b, |Real.sin u| / u ≤ b - a := by
  calc ∫ u in a..b, |Real.sin u| / u ≤ ∫ _ in a..b, (1 : ℝ) :=
        intervalIntegral.integral_mono_on hab (intervalIntegrable_abs_sin_div ha hab)
          intervalIntegrable_const fun _ hu => by
            rcases (ha.trans hu.1).eq_or_lt with h0 | h0
            · rw [← h0]; simp
            · exact abs_sin_div_le_one h0
    _ = b - a := by simp

theorem integral_abs_sin_div_nonneg {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    0 ≤ ∫ u in a..b, |Real.sin u| / u :=
  intervalIntegral.integral_nonneg hab fun _ hu =>
    div_nonneg (abs_nonneg _) (ha.trans hu.1)

/-- `∫₀^{(n+½)π} |sin u|/u du` lies within a constant of `(2/π) Hₙ`. -/
theorem sincAbs_bounds (n : ℕ) :
    2 / π * (harmonic n : ℝ) ≤ ∫ u in (0 : ℝ)..((n + 1 / 2) * π), |Real.sin u| / u ∧
      ∫ u in (0 : ℝ)..((n + 1 / 2) * π), |Real.sin u| / u ≤
        2 / π * (harmonic n : ℝ) + 3 / 2 * π := by
  have hπ := Real.pi_pos
  have hH : (harmonic n : ℝ) = ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1) := by
    simp [harmonic]
  have hint : ∀ k < n, IntervalIntegrable (fun u => |Real.sin u| / u) volume
      ((k : ℕ) * π) (((k + 1 : ℕ) : ℝ) * π) := fun k _ =>
    intervalIntegrable_abs_sin_div (by positivity) (by push_cast; nlinarith)
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals (a := fun k : ℕ => (k : ℝ) * π)
    hint
  simp only [Nat.cast_zero, zero_mul] at hsplit
  have htail_int : IntervalIntegrable (fun u => |Real.sin u| / u) volume ((n : ℝ) * π)
      ((n + 1 / 2) * π) := intervalIntegrable_abs_sin_div (by positivity) (by nlinarith)
  have hmain_int : IntervalIntegrable (fun u => |Real.sin u| / u) volume 0 ((n : ℝ) * π) :=
    intervalIntegrable_abs_sin_div le_rfl (by positivity)
  rw [← intervalIntegral.integral_add_adjacent_intervals hmain_int htail_int, ← hsplit]
  have htail0 := integral_abs_sin_div_nonneg (a := (n : ℝ) * π) (b := (n + 1 / 2) * π)
    (by positivity) (by nlinarith)
  have htail1 := integral_abs_sin_div_le_length (a := (n : ℝ) * π) (b := (n + 1 / 2) * π)
    (by positivity) (by nlinarith)
  have hlow : ∀ k ∈ Finset.range n, 2 / π * (1 / ((k : ℝ) + 1)) ≤
      ∫ u in ((k : ℕ) * π)..(((k + 1 : ℕ) : ℝ) * π), |Real.sin u| / u := fun k _ => by
    have := piece_lower k
    push_cast
    calc 2 / π * (1 / ((k : ℝ) + 1)) = 2 / ((k + 1) * π) := by field_simp
      _ ≤ _ := this
  constructor
  · rw [hH, Finset.mul_sum]
    have := Finset.sum_le_sum hlow
    linarith
  · -- peel off the first period
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp at htail1 ⊢
      nlinarith
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Finset.sum_range_succ']
    have h0 := integral_abs_sin_div_le_length (a := ((0 : ℕ) : ℝ) * π)
      (b := (((0 + 1 : ℕ)) : ℝ) * π) (by simp) (by push_cast; nlinarith)
    have hup : ∑ k ∈ Finset.range m,
        ∫ u in (((k + 1 : ℕ) : ℝ) * π)..(((k + 1 + 1 : ℕ) : ℝ) * π), |Real.sin u| / u ≤
        ∑ k ∈ Finset.range m, 2 / π * (1 / ((k : ℝ) + 1)) := Finset.sum_le_sum fun k _ => by
      have := piece_upper k
      push_cast
      calc _ ≤ 2 / ((k + 1) * π) := this
        _ = 2 / π * (1 / ((k : ℝ) + 1)) := by field_simp
    have hsub : ∑ k ∈ Finset.range m, 2 / π * (1 / ((k : ℝ) + 1)) ≤
        2 / π * (harmonic (m + 1) : ℝ) := by
      rw [hH, Finset.mul_sum, Finset.sum_range_succ]
      have : 0 ≤ 2 / π * (1 / ((m : ℝ) + 1)) := by positivity
      linarith
    rw [show ((0 + 1 : ℕ) : ℝ) * π - ((0 : ℕ) : ℝ) * π = π by push_cast; ring] at h0
    rw [show ((m + 1 : ℕ) + 1 / 2 : ℝ) * π - ((m + 1 : ℕ) : ℝ) * π = π / 2 by ring] at htail1
    linarith

/-- The Lebesgue constant is within `1` of `(2/π) ∫₀^{(n+½)π} |sin u|/u du`. -/
theorem lebesgueConst_bounds (n : ℕ) :
    2 / π * ∫ u in (0 : ℝ)..((n + 1 / 2) * π), |Real.sin u| / u ≤ lebesgueConst n ∧
      lebesgueConst n ≤ 2 / π * (∫ u in (0 : ℝ)..((n + 1 / 2) * π), |Real.sin u| / u) + 1 := by
  have hπ := Real.pi_pos
  set ν : ℝ := n + 1 / 2
  have hν : 0 < ν := by positivity
  -- the comparison integrand `|sin νt| · 2/t`
  have hJ : ∫ t in (0 : ℝ)..π, |Real.sin (ν * t)| * (2 / t) =
      2 * ∫ u in (0 : ℝ)..(ν * π), |Real.sin u| / u := by
    have e : ∀ t : ℝ, |Real.sin (ν * t)| * (2 / t) = 2 * ν * (|Real.sin (ν * t)| / (ν * t)) :=
      fun t => by
        rcases eq_or_ne t 0 with rfl | ht
        · simp
        · field_simp
    simp_rw [e]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left (fun u => |Real.sin u| / u) hν.ne', mul_zero,
      smul_eq_mul]
    field_simp
  have hmeasL : Measurable fun t : ℝ => |Real.sin (ν * t)| / Real.sin (t / 2) := by fun_prop
  have hmeasJ : Measurable fun t : ℝ => |Real.sin (ν * t)| * (2 / t) := by fun_prop
  have hsin_pos : ∀ t ∈ Ioc (0 : ℝ) π, 0 < Real.sin (t / 2) := fun t ht =>
    Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by linarith [ht.2])
  have hsin_ge : ∀ t ∈ Ioc (0 : ℝ) π, t / π ≤ Real.sin (t / 2) := fun t ht => by
    have := Real.mul_le_sin (x := t / 2) (by linarith [ht.1]) (by linarith [ht.2])
    calc t / π = 2 / π * (t / 2) := by field_simp
      _ ≤ _ := this
  have habs : ∀ t, 0 ≤ t → |Real.sin (ν * t)| ≤ ν * t := fun t ht =>
    Real.abs_sin_le_abs.trans (abs_of_nonneg (by positivity)).le
  have hLint : IntervalIntegrable (fun t => |Real.sin (ν * t)| / Real.sin (t / 2)) volume 0 π :=
    intervalIntegrable_of_abs_le hπ.le hmeasL (ν * π) fun t ht => by
      have hs := hsin_pos t ht
      rw [abs_of_nonneg (div_nonneg (abs_nonneg _) hs.le), div_le_iff₀ hs]
      calc |Real.sin (ν * t)| ≤ ν * t := habs t ht.1.le
        _ = ν * π * (t / π) := by field_simp
        _ ≤ ν * π * Real.sin (t / 2) := by
            gcongr
            exact hsin_ge t ht
  have hJint : IntervalIntegrable (fun t => |Real.sin (ν * t)| * (2 / t)) volume 0 π :=
    intervalIntegrable_of_abs_le hπ.le hmeasJ (2 * ν) fun t ht => by
      rw [abs_of_nonneg (mul_nonneg (abs_nonneg _) (div_nonneg zero_le_two ht.1.le))]
      calc |Real.sin (ν * t)| * (2 / t) ≤ ν * t * (2 / t) :=
            mul_le_mul_of_nonneg_right (habs t ht.1.le) (div_nonneg zero_le_two ht.1.le)
        _ = 2 * ν := by have := ht.1.ne'; field_simp
  have hlow : ∫ t in (0 : ℝ)..π, |Real.sin (ν * t)| * (2 / t) ≤
      ∫ t in (0 : ℝ)..π, |Real.sin (ν * t)| / Real.sin (t / 2) := by
    refine intervalIntegral.integral_mono_ae_restrict hπ.le hJint hLint ?_
    refine (ae_restrict_iff' measurableSet_Icc).mpr (ae_of_all _ fun t ht => ?_)
    rcases ht.1.eq_or_lt with rfl | ht0
    · simp
    have hs := hsin_pos t ⟨ht0, ht.2⟩
    show |Real.sin (ν * t)| * (2 / t) ≤ |Real.sin (ν * t)| / Real.sin (t / 2)
    rw [div_eq_mul_one_div _ (Real.sin (t / 2))]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [div_le_div_iff₀ ht0 hs]
    linarith [Real.sin_le (x := t / 2) (by linarith)]
  have hup : ∫ t in (0 : ℝ)..π, |Real.sin (ν * t)| / Real.sin (t / 2) ≤
      ∫ t in (0 : ℝ)..π, (|Real.sin (ν * t)| * (2 / t) + 1) := by
    refine intervalIntegral.integral_mono_ae_restrict hπ.le hLint
      (hJint.add intervalIntegrable_const) ?_
    refine (ae_restrict_iff' measurableSet_Icc).mpr (ae_of_all _ fun t ht => ?_)
    rcases ht.1.eq_or_lt with rfl | ht0
    · simp
    have hs := hsin_pos t ⟨ht0, ht.2⟩
    have hd := inv_sin_sub_inv_le_one (u := t / 2) (by linarith) (by linarith [ht.2])
    have hd0 : 0 ≤ 1 / Real.sin (t / 2) - 1 / (t / 2) := by
      rw [sub_nonneg]
      exact one_div_le_one_div_of_le hs (Real.sin_le (by linarith))
    have hsn : |Real.sin (ν * t)| ≤ 1 := Real.abs_sin_le_one _
    show |Real.sin (ν * t)| / Real.sin (t / 2) ≤ |Real.sin (ν * t)| * (2 / t) + 1
    have e : |Real.sin (ν * t)| / Real.sin (t / 2) = |Real.sin (ν * t)| * (2 / t) +
        |Real.sin (ν * t)| * (1 / Real.sin (t / 2) - 1 / (t / 2)) := by
      field_simp
      ring
    rw [e]
    nlinarith [abs_nonneg (Real.sin (ν * t))]
  rw [intervalIntegral.integral_add hJint intervalIntegrable_const, intervalIntegral.integral_const,
    sub_zero, smul_eq_mul, mul_one] at hup
  rw [hJ] at hlow hup
  unfold lebesgueConst
  constructor
  · calc 2 / π * ∫ u in (0 : ℝ)..(ν * π), |Real.sin u| / u
        = 1 / π * (2 * ∫ u in (0 : ℝ)..(ν * π), |Real.sin u| / u) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlow (by positivity)
  · calc 1 / π * ∫ t in (0 : ℝ)..π, |Real.sin (ν * t)| / Real.sin (t / 2)
        ≤ 1 / π * (2 * (∫ u in (0 : ℝ)..(ν * π), |Real.sin u| / u) + π) :=
          mul_le_mul_of_nonneg_left hup (by positivity)
      _ = 2 / π * (∫ u in (0 : ℝ)..(ν * π), |Real.sin u| / u) + 1 := by field_simp

/-- **DLMF 1.8.9**: `Lₙ ∼ (4/π²) ln n` as `n → ∞`. -/
theorem dlmf_1_8_9 :
    Asymptotics.IsEquivalent atTop (fun n : ℕ => lebesgueConst n)
      (fun n : ℕ => 4 / π ^ 2 * Real.log n) := by
  have hπ := Real.pi_pos
  have hO : (fun n : ℕ => lebesgueConst n - 4 / π ^ 2 * Real.log n) =O[atTop]
      (fun _ : ℕ => (1 : ℝ)) := by
    refine Asymptotics.IsBigO.of_bound (4 / π ^ 2 + 4) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    obtain ⟨hL1, hL2⟩ := lebesgueConst_bounds n
    obtain ⟨hK1, hK2⟩ := sincAbs_bounds n
    have hH1 := log_add_one_le_harmonic n
    have hH2 := harmonic_le_one_add_log n
    have hlog : Real.log n ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast hn) (by push_cast; linarith)
    have hc : 0 < 4 / π ^ 2 := by positivity
    have hA : 4 / π ^ 2 * Real.log n ≤ lebesgueConst n := by
      calc 4 / π ^ 2 * Real.log n ≤ 4 / π ^ 2 * (harmonic n : ℝ) :=
            mul_le_mul_of_nonneg_left (hlog.trans hH1) hc.le
        _ = 2 / π * (2 / π * (harmonic n : ℝ)) := by ring
        _ ≤ 2 / π * ∫ u in (0 : ℝ)..((n + 1 / 2) * π), |Real.sin u| / u :=
            mul_le_mul_of_nonneg_left hK1 (by positivity)
        _ ≤ lebesgueConst n := hL1
    have hB : lebesgueConst n ≤ 4 / π ^ 2 * Real.log n + (4 / π ^ 2 + 4) := by
      calc lebesgueConst n ≤ 2 / π * (2 / π * (harmonic n : ℝ) + 3 / 2 * π) + 1 :=
            hL2.trans (by gcongr)
        _ = 4 / π ^ 2 * (harmonic n : ℝ) + 4 := by field_simp; ring
        _ ≤ 4 / π ^ 2 * (1 + Real.log n) + 4 := by gcongr
        _ = 4 / π ^ 2 * Real.log n + (4 / π ^ 2 + 4) := by ring
    rw [Real.norm_eq_abs, norm_one, mul_one, abs_le]
    constructor <;> linarith
  have ho : (fun _ : ℕ => (1 : ℝ)) =o[atTop] (fun n : ℕ => 4 / π ^ 2 * Real.log n) :=
    (Real.isLittleO_const_log_atTop.comp_tendsto tendsto_natCast_atTop_atTop).const_mul_right
      (by positivity)
  exact hO.trans_isLittleO ho

/-! ### §1.8(iii) Integration and differentiation -/

theorem periodic_intervalIntegrable {f : ℝ → ℂ} (hper : Function.Periodic f (2 * π))
    (hf : IntervalIntegrable f volume (-π) π) (a b : ℝ) : IntervalIntegrable f volume a b :=
  hper.intervalIntegrable (by positivity) (by rwa [show -π + 2 * π = π by ring]) a b

/-- The oriented indicator of `(0, y]`: `1` on `(0, y]`, `−1` on `(y, 0]`. -/
noncomputable def orientedIndicator (y t : ℝ) : ℂ :=
  (Ioc 0 y).indicator (fun _ => (1 : ℂ)) t - (Ioc y 0).indicator (fun _ => (1 : ℂ)) t

theorem conj_orientedIndicator (y t : ℝ) :
    conj (orientedIndicator y t) = orientedIndicator y t := by
  unfold orientedIndicator
  by_cases h1 : t ∈ Ioc 0 y <;> by_cases h2 : t ∈ Ioc y 0 <;> simp [h1, h2]

theorem memLp_orientedIndicator (y : ℝ) :
    MemLp (orientedIndicator y) 2 (volume.restrict (Ioc (-π) π)) := by
  refine MemLp.of_bound ?_ 2 (ae_of_all _ fun t => ?_)
  · exact ((measurable_const.indicator measurableSet_Ioc).sub
      (measurable_const.indicator measurableSet_Ioc)).aestronglyMeasurable
  · unfold orientedIndicator
    by_cases h1 : t ∈ Ioc 0 y <;> by_cases h2 : t ∈ Ioc y 0 <;> norm_num [h1, h2]

theorem integral_mul_orientedIndicator {y : ℝ} (hy : y ∈ Icc (-π) π) {h : ℝ → ℂ}
    (hh : IntervalIntegrable h volume (-π) π) :
    ∫ t in (-π)..π, h t * orientedIndicator y t = ∫ t in (0 : ℝ)..y, h t := by
  have e : ∀ t, h t * orientedIndicator y t = (Ioc 0 y).indicator h t - (Ioc y 0).indicator h t :=
    fun t => by
      unfold orientedIndicator
      by_cases h1 : t ∈ Ioc 0 y <;> by_cases h2 : t ∈ Ioc y 0 <;> simp [h1, h2]
  have hI := (intervalIntegrable_iff_integrableOn_Ioc_of_le neg_pi_lt_pi.le).mp hh
  rw [intervalIntegral.integral_of_le neg_pi_lt_pi.le, setIntegral_congr_fun measurableSet_Ioc
    fun t _ => e t, integral_sub (hI.indicator measurableSet_Ioc) (hI.indicator measurableSet_Ioc),
    setIntegral_indicator measurableSet_Ioc, setIntegral_indicator measurableSet_Ioc,
    (inter_eq_right (s := Ioc (-π) π) (t := Ioc 0 y)).mpr fun t ht =>
      ⟨by linarith [ht.1, hy.1, Real.pi_pos], by linarith [ht.2, hy.2]⟩,
    (inter_eq_right (s := Ioc (-π) π) (t := Ioc y 0)).mpr fun t ht =>
      ⟨by linarith [ht.1, hy.1], by linarith [ht.2, Real.pi_pos]⟩]
  rfl

theorem integral_cos_mul_zero_to {c : ℝ} (hc : c ≠ 0) (y : ℝ) :
    ∫ t in (0 : ℝ)..y, Real.cos (c * t) = Real.sin (c * y) / c := by
  rw [intervalIntegral.integral_comp_mul_left (fun t => Real.cos t) hc, integral_cos, mul_zero,
    Real.sin_zero, sub_zero, smul_eq_mul]
  field_simp

theorem integral_sin_mul_zero_to {c : ℝ} (hc : c ≠ 0) (y : ℝ) :
    ∫ t in (0 : ℝ)..y, Real.sin (c * t) = (1 - Real.cos (c * y)) / c := by
  rw [intervalIntegral.integral_comp_mul_left (fun t => Real.sin t) hc, integral_sin, mul_zero,
    Real.cos_zero, smul_eq_mul]
  field_simp

theorem integral_orientedIndicator_mul {y : ℝ} (hy : y ∈ Icc (-π) π) {h : ℝ → ℂ}
    (hh : IntervalIntegrable h volume (-π) π) :
    ∫ t in (-π)..π, orientedIndicator y t * h t = ∫ t in (0 : ℝ)..y, h t := by
  simp_rw [mul_comm (orientedIndicator y _)]
  exact integral_mul_orientedIndicator hy hh

theorem fourierA_orientedIndicator {y : ℝ} (hy : y ∈ Icc (-π) π) (n : ℕ) :
    fourierA (orientedIndicator y) (n + 1) =
      ((Real.sin ((n + 1 : ℕ) * y) / ((n + 1 : ℕ) * π) : ℝ) : ℂ) := by
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [fourierA, integral_orientedIndicator_mul hy
    (h := fun t => (Real.cos (((n + 1 : ℕ) : ℝ) * t) : ℂ)) (Continuous.intervalIntegrable
      (by fun_prop) _ _),
    intervalIntegral.integral_ofReal, integral_cos_mul_zero_to hn, Complex.real_smul]
  push_cast
  field_simp

theorem fourierB_orientedIndicator {y : ℝ} (hy : y ∈ Icc (-π) π) (n : ℕ) :
    fourierB (orientedIndicator y) (n + 1) =
      (((1 - Real.cos ((n + 1 : ℕ) * y)) / ((n + 1 : ℕ) * π) : ℝ) : ℂ) := by
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [fourierB, integral_orientedIndicator_mul hy
    (h := fun t => (Real.sin (((n + 1 : ℕ) : ℝ) * t) : ℂ)) (Continuous.intervalIntegrable
      (by fun_prop) _ _),
    intervalIntegral.integral_ofReal, integral_sin_mul_zero_to hn, Complex.real_smul]
  push_cast
  field_simp

theorem fourierA_orientedIndicator_zero {y : ℝ} (hy : y ∈ Icc (-π) π) :
    fourierA (orientedIndicator y) 0 = ((y / π : ℝ) : ℂ) := by
  rw [fourierA, integral_orientedIndicator_mul hy
    (h := fun t => (Real.cos (((0 : ℕ) : ℝ) * t) : ℂ)) (Continuous.intervalIntegrable
      (by fun_prop) _ _)]
  simp [Complex.real_smul]
  ring

theorem integral_eq_pi_mul_fourierA_zero (f : ℝ → ℂ) :
    ∫ t in (-π)..π, f t = π * fourierA f 0 := by
  simp only [fourierA, Nat.cast_zero, zero_mul, Real.cos_zero, Complex.ofReal_one, mul_one,
    Complex.real_smul]
  push_cast
  field_simp

/-- 1.8.12 for `x ∈ [−π, π]`: Parseval 1.8.6_1 against the oriented indicator of `(0, x]`. -/
theorem hasSum_integral_of_mem {f : ℝ → ℂ} (hf : MemLp f 2 (volume.restrict (Ioc (-π) π)))
    {y : ℝ} (hy : y ∈ Icc (-π) π) :
    HasSum (fun n : ℕ => (fourierA f (n + 1) * (Real.sin ((n + 1 : ℕ) * y) : ℂ) +
        fourierB f (n + 1) * (1 - (Real.cos ((n + 1 : ℕ) * y) : ℂ))) / ((n + 1 : ℕ) : ℂ))
      (∫ t in (0 : ℝ)..y, (f t - fourierA f 0 / 2)) := by
  have hfi := intervalIntegrable_of_memLp hf
  have h := (dlmf_1_8_6_1 hf (memLp_orientedIndicator y)).mul_left (π : ℂ)
  simp only [fourierA_orientedIndicator hy, fourierB_orientedIndicator hy,
    fourierA_orientedIndicator_zero hy, Complex.conj_ofReal, conj_orientedIndicator] at h
  rw [integral_mul_orientedIndicator hy hfi] at h
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hfy : IntervalIntegrable f volume 0 y := hfi.mono_set (by
    rw [Set.uIcc_of_le neg_pi_lt_pi.le]
    exact Set.uIcc_subset_Icc ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ hy)
  convert h using 1
  · funext n
    push_cast
    field_simp
  · rw [intervalIntegral.integral_sub hfy intervalIntegrable_const, intervalIntegral.integral_const]
    simp only [Complex.real_smul, sub_zero]
    push_cast
    field_simp

/-- **DLMF 1.8.12**: for `f` square-integrable on a period (e.g. piecewise continuous) and
`2π`-periodic, `∫₀^x (f(t) − ½a₀) dt = ∑_{n ≥ 1} (aₙ sin(nx) + bₙ(1 − cos(nx)))/n`.  DLMF states
this for `0 ≤ x ≤ 2π`; it holds for every real `x`. -/
theorem dlmf_1_8_12 {f : ℝ → ℂ} (hper : Function.Periodic f (2 * π))
    (hf : MemLp f 2 (volume.restrict (Ioc (-π) π))) (x : ℝ) :
    HasSum (fun n : ℕ => (fourierA f (n + 1) * (Real.sin ((n + 1 : ℕ) * x) : ℂ) +
        fourierB f (n + 1) * (1 - (Real.cos ((n + 1 : ℕ) * x) : ℂ))) / ((n + 1 : ℕ) : ℂ))
      (∫ t in (0 : ℝ)..x, (f t - fourierA f 0 / 2)) := by
  have hp : (0 : ℝ) < 2 * π := by positivity
  have hfi := intervalIntegrable_of_memLp hf
  have hgi : ∀ a b, IntervalIntegrable (fun t => f t - fourierA f 0 / 2) volume a b :=
    fun a b => (periodic_intervalIntegrable hper hfi a b).sub intervalIntegrable_const
  have hper' : Function.Periodic (fun t => f t - fourierA f 0 / 2) (2 * π) := fun t => by
    simp only [hper t]
  have hL : Function.Periodic (fun x => ∫ t in (0 : ℝ)..x, (f t - fourierA f 0 / 2)) (2 * π) :=
    fun x => by
      simp only
      rw [← intervalIntegral.integral_add_adjacent_intervals (hgi 0 x) (hgi x (x + 2 * π)),
        hper'.intervalIntegral_add_eq x (-π), show -π + 2 * π = π by ring,
        intervalIntegral.integral_sub hfi intervalIntegrable_const, intervalIntegral.integral_const,
        integral_eq_pi_mul_fourierA_zero, Complex.real_smul]
      push_cast
      ring
  have hT : ∀ n : ℕ, Function.Periodic (fun x : ℝ => (fourierA f (n + 1) *
      (Real.sin ((n + 1 : ℕ) * x) : ℂ) + fourierB f (n + 1) *
        (1 - (Real.cos ((n + 1 : ℕ) * x) : ℂ))) / ((n + 1 : ℕ) : ℂ)) (2 * π) := fun n x => by
    simp only
    rw [show ((n + 1 : ℕ) : ℝ) * (x + 2 * π) = (n + 1 : ℕ) * x + (n + 1 : ℕ) * (2 * π) by ring,
      Real.sin_add_nat_mul_two_pi, Real.cos_add_nat_mul_two_pi]
  set y := toIocMod hp (-π) x
  have hmem := toIocMod_mem_Ioc hp (-π) x
  have hy : y ∈ Icc (-π) π := ⟨hmem.1.le, by linarith [hmem.2]⟩
  have hxy : y = x - toIocDiv hp (-π) x • (2 * π) := (self_sub_toIocDiv_zsmul hp (-π) x).symm
  have h := hasSum_integral_of_mem hf hy
  rw [hxy, hL.sub_zsmul_eq] at h
  convert h using 1
  funext n
  rw [(hT n).sub_zsmul_eq]

theorem periodic_deriv {f : ℝ → ℂ} {c : ℝ} (hper : Function.Periodic f c) :
    Function.Periodic (deriv f) c := fun x => by
  have : (fun y => f (y + c)) = f := funext hper
  rw [← deriv_comp_add_const, this]

theorem fourierA_eq_add {f : ℝ → ℂ} (hf : IntervalIntegrable f volume (-π) π) (n : ℕ) :
    fourierA f n = fourierC f n + fourierC f (-n) := by
  rw [fourierC_natCast hf, fourierC_neg_natCast hf]; ring

theorem fourierB_eq_sub {f : ℝ → ℂ} (hf : IntervalIntegrable f volume (-π) π) (n : ℕ) :
    fourierB f n = Complex.I * (fourierC f n - fourierC f (-n)) := by
  rw [fourierC_natCast hf, fourierC_neg_natCast hf]
  linear_combination (fourierB f n) * Complex.I_sq

/-- `cₙ(g′) = i n cₙ(g)` for a `C¹`, `2π`-periodic `g`. -/
theorem fourierC_deriv {g : ℝ → ℂ} (hper : Function.Periodic g (2 * π)) (hg : ContDiff ℝ 1 g)
    (n : ℤ) : fourierC (deriv g) n = n * Complex.I * fourierC g n := by
  have hd : ∀ x, HasDerivWithinAt g (deriv g x) (Ioi x) x := fun x =>
    (hg.differentiable one_ne_zero x).hasDerivAt.hasDerivWithinAt
  have hi : IntervalIntegrable (deriv g) volume (-π) π :=
    (hg.continuous_deriv le_rfl).intervalIntegrable _ _
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [fourierC, Int.cast_zero, zero_mul, neg_zero, Complex.exp_zero, mul_one]
    rw [intervalIntegral.integral_deriv_eq_sub (fun x _ => hg.differentiable one_ne_zero x) hi]
    have : g π = g (-π) := by
      have := hper (-π)
      rwa [show -π + 2 * π = π by ring] at this
    rw [this, sub_self, smul_zero]
  · rw [fourierC_eq_div_of_hasDerivWithinAt hper hg.continuous hd hi hn]
    have : (n : ℂ) * Complex.I ≠ 0 := mul_ne_zero (Int.cast_ne_zero.mpr hn) Complex.I_ne_zero
    field_simp

theorem fourierA_deriv {g : ℝ → ℂ} (hper : Function.Periodic g (2 * π)) (hg : ContDiff ℝ 1 g)
    (n : ℕ) : fourierA (deriv g) n = n * fourierB g n := by
  have hgi : IntervalIntegrable g volume (-π) π := hg.continuous.intervalIntegrable _ _
  rw [fourierA_eq_add ((hg.continuous_deriv le_rfl).intervalIntegrable _ _), fourierB_eq_sub hgi,
    fourierC_deriv hper hg, fourierC_deriv hper hg]
  push_cast
  ring

theorem fourierB_deriv {g : ℝ → ℂ} (hper : Function.Periodic g (2 * π)) (hg : ContDiff ℝ 1 g)
    (n : ℕ) : fourierB (deriv g) n = -(n * fourierA g n) := by
  have hgi : IntervalIntegrable g volume (-π) π := hg.continuous.intervalIntegrable _ _
  rw [fourierB_eq_sub ((hg.continuous_deriv le_rfl).intervalIntegrable _ _), fourierA_eq_add hgi,
    fourierC_deriv hper hg, fourierC_deriv hper hg]
  push_cast
  linear_combination (n * (fourierC g n + fourierC g (-n))) * Complex.I_sq

/-- **DLMF §1.8(iii)**: for a `2π`-periodic `f ∈ C²`, the term-by-term derivative of the Fourier
series converges at every point to `f′(x)`:
`f′(x) = ∑_{n ≥ 1} n (bₙ cos(nx) − aₙ sin(nx))`. -/
theorem dlmf_1_8_iii_deriv {f : ℝ → ℂ} (hper : Function.Periodic f (2 * π))
    (hf : ContDiff ℝ 2 f) (x : ℝ) :
    HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℂ) *
      (fourierB f (n + 1) * (Real.cos ((n + 1 : ℕ) * x) : ℂ) -
      fourierA f (n + 1) * (Real.sin ((n + 1 : ℕ) * x) : ℂ))) (deriv f x) := by
  have hf1 : ContDiff ℝ 1 (deriv f) := ContDiff.deriv' (n := 1) (by convert hf; norm_num)
  have hf0 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hper1 := periodic_deriv hper
  -- the coefficients of `f′` are summable: `|cₙ(f′)| = |cₙ(f″)|/|n|`
  have hP := (dlmf_1_8_6 (memLp_of_continuous (hf1.continuous_deriv le_rfl))).summable
  have hsq : Summable fun n : ℤ => 1 / (n : ℝ) ^ 2 := Real.summable_one_div_int_pow.mpr one_lt_two
  have hsum : Summable (fourierC (deriv f)) := by
    refine Summable.of_norm_bounded_eventually ((hP.add hsq).div_const 2) ?_
    filter_upwards [eventually_cofinite_ne 0] with n hn
    have h2 := fourierC_deriv hper1 hf1 n
    have hnI : (n : ℂ) * Complex.I ≠ 0 := mul_ne_zero (Int.cast_ne_zero.mpr hn) Complex.I_ne_zero
    have heq : fourierC (deriv f) n = fourierC (deriv (deriv f)) n / (n * Complex.I) := by
      rw [h2]; field_simp
    have hnr : (0 : ℝ) < |(n : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hn)
    rw [heq, norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_intCast]
    have := two_mul_le_add_sq ‖fourierC (deriv (deriv f)) n‖ (1 / |(n : ℝ)|)
    rw [div_pow, one_pow, sq_abs] at this
    rw [div_eq_mul_one_div]
    linarith
  have h := dlmf_1_8_1 hper1 hf1.continuous hsum x
  rw [fourierA_deriv hper hf0, Nat.cast_zero, zero_mul, zero_div, sub_zero] at h
  convert h using 1
  funext n
  rw [fourierA_deriv hper hf0, fourierB_deriv hper hf0]
  ring

/-! ### §1.8(ii) Convergence -/

/-- The partial sums of 1.8.1: `½a₀ + ∑_{n=1}^N (aₙ cos(nx) + bₙ sin(nx))`. -/
noncomputable def fourierPartialSum (f : ℝ → ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  fourierA f 0 / 2 + ∑ n ∈ Finset.range N, (fourierA f (n + 1) * (Real.cos ((n + 1 : ℕ) * x) : ℂ) +
    fourierB f (n + 1) * (Real.sin ((n + 1 : ℕ) * x) : ℂ))

/-- Half the Dirichlet kernel: `½ + ∑_{n=1}^N cos(ns)`. -/
noncomputable def halfDirichlet (N : ℕ) (s : ℝ) : ℝ :=
  1 / 2 + ∑ n ∈ Finset.range N, Real.cos ((n + 1 : ℕ) * s)

theorem continuous_halfDirichlet (N : ℕ) : Continuous (halfDirichlet N) := by
  unfold halfDirichlet; fun_prop

theorem halfDirichlet_neg (N : ℕ) (s : ℝ) : halfDirichlet N (-s) = halfDirichlet N s := by
  simp [halfDirichlet, mul_neg, Real.cos_neg]

theorem halfDirichlet_periodic (N : ℕ) : Function.Periodic (halfDirichlet N) (2 * π) := fun s => by
  simp only [halfDirichlet]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [show ((n + 1 : ℕ) : ℝ) * (s + 2 * π) = (n + 1 : ℕ) * s + (n + 1 : ℕ) * (2 * π) by ring,
    Real.cos_add_nat_mul_two_pi]

/-- `2 Dₙ(s) sin(s/2) = sin((N + ½)s)`. -/
theorem two_mul_halfDirichlet_mul_sin (N : ℕ) (s : ℝ) :
    2 * halfDirichlet N s * Real.sin (s / 2) = Real.sin ((N + 1 / 2) * s) := by
  induction N with
  | zero => simp [halfDirichlet]; ring_nf
  | succ N ih =>
    rw [halfDirichlet, Finset.sum_range_succ, ← add_assoc, ← halfDirichlet]
    have e1 : ((N : ℝ) + 1 / 2) * s = (N + 1 : ℕ) * s - s / 2 := by push_cast; ring
    have e2 : (((N + 1 : ℕ) : ℝ) + 1 / 2) * s = (N + 1 : ℕ) * s + s / 2 := by push_cast; ring
    rw [e1] at ih
    rw [e2, Real.sin_add, mul_add, add_mul, ih, Real.sin_sub]
    ring

theorem integral_halfDirichlet (N : ℕ) : ∫ s in (0 : ℝ)..π, halfDirichlet N s = π / 2 := by
  have hc : ∀ n : ℕ, IntervalIntegrable (fun s : ℝ => Real.cos ((n + 1 : ℕ) * s)) volume 0 π :=
    fun n => (by fun_prop : Continuous fun s : ℝ => Real.cos ((n + 1 : ℕ) * s)).intervalIntegrable
      _ _
  simp only [halfDirichlet]
  rw [intervalIntegral.integral_add intervalIntegrable_const
    ((by fun_prop : Continuous fun s : ℝ => ∑ n ∈ Finset.range N,
      Real.cos ((n + 1 : ℕ) * s)).intervalIntegrable _ _),
    intervalIntegral.integral_finsetSum fun n _ => hc n]
  have h0 : ∀ n : ℕ, ∫ s in (0 : ℝ)..π, Real.cos ((n + 1 : ℕ) * s) = 0 := fun n => by
    rw [integral_cos_mul_zero_to (by positivity), Real.sin_nat_mul_pi, zero_div]
  simp only [h0, Finset.sum_const_zero, add_zero, intervalIntegral.integral_const, sub_zero,
    smul_eq_mul]
  ring

theorem fourier_term_eq_integral {f : ℝ → ℂ} (hf : IntervalIntegrable f volume (-π) π) (k : ℕ)
    (x : ℝ) :
    fourierA f k * (Real.cos (k * x) : ℂ) + fourierB f k * (Real.sin (k * x) : ℂ) =
      (1 / π : ℝ) • ∫ t in (-π)..π, f t * (Real.cos (k * (t - x)) : ℂ) := by
  have e : ∀ t : ℝ, f t * (Real.cos (k * (t - x)) : ℂ) = f t * (Real.cos (k * t) : ℂ) *
      (Real.cos (k * x) : ℂ) + f t * (Real.sin (k * t) : ℂ) * (Real.sin (k * x) : ℂ) :=
    fun t => by rw [mul_sub, Real.cos_sub]; push_cast; ring
  rw [intervalIntegral.integral_congr fun t _ => e t,
    intervalIntegral.integral_add ((intervalIntegrable_mul_cos hf _).mul_const _)
      ((intervalIntegrable_mul_sin hf _).mul_const _),
    intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const, fourierA, fourierB]
  simp only [Complex.real_smul]
  ring

/-- The partial sum as an integral against the Dirichlet kernel. -/
theorem fourierPartialSum_eq_integral {f : ℝ → ℂ} (hf : IntervalIntegrable f volume (-π) π)
    (N : ℕ) (x : ℝ) :
    fourierPartialSum f N x =
      (1 / π : ℝ) • ∫ t in (-π)..π, f t * (halfDirichlet N (t - x) : ℂ) := by
  have hcos : ∀ n : ℕ, IntervalIntegrable
      (fun t => f t * (Real.cos ((n + 1 : ℕ) * (t - x)) : ℂ)) volume (-π) π := fun n =>
    hf.mul_continuousOn (by fun_prop : Continuous fun t : ℝ =>
      (Real.cos ((n + 1 : ℕ) * (t - x)) : ℂ)).continuousOn
  have e : ∀ t : ℝ, f t * (halfDirichlet N (t - x) : ℂ) = f t * (1 / 2 : ℂ) +
      ∑ n ∈ Finset.range N, f t * (Real.cos ((n + 1 : ℕ) * (t - x)) : ℂ) := fun t => by
    simp only [halfDirichlet]
    push_cast
    rw [mul_add, Finset.mul_sum]
  have hsum : IntervalIntegrable (fun t => ∑ n ∈ Finset.range N,
      f t * (Real.cos ((n + 1 : ℕ) * (t - x)) : ℂ)) volume (-π) π := by
    simp_rw [← Finset.mul_sum]
    exact hf.mul_continuousOn (by fun_prop : Continuous fun t : ℝ =>
      ∑ n ∈ Finset.range N, (Real.cos ((n + 1 : ℕ) * (t - x)) : ℂ)).continuousOn
  rw [intervalIntegral.integral_congr fun t _ => e t,
    intervalIntegral.integral_add (hf.mul_const _) hsum,
    intervalIntegral.integral_finsetSum fun n _ => hcos n, smul_add, Finset.smul_sum,
    fourierPartialSum]
  congr 1
  · rw [intervalIntegral.integral_mul_const, integral_eq_pi_mul_fourierA_zero, Complex.real_smul]
    have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    push_cast
    field_simp
  · exact Finset.sum_congr rfl fun n _ => fourier_term_eq_integral hf (n + 1) x

theorem periodic_intervalIntegrable_add {f : ℝ → ℂ} (hper : Function.Periodic f (2 * π))
    (hf : IntervalIntegrable f volume (-π) π) (x a b : ℝ) :
    IntervalIntegrable (fun s => f (x + s)) volume a b := by
  simpa using (periodic_intervalIntegrable hper hf (a + x) (b + x)).comp_add_left x

theorem periodic_intervalIntegrable_sub {f : ℝ → ℂ} (hper : Function.Periodic f (2 * π))
    (hf : IntervalIntegrable f volume (-π) π) (x a b : ℝ) :
    IntervalIntegrable (fun s => f (x - s)) volume a b := by
  simpa using (periodic_intervalIntegrable hper hf (x - a) (x - b)).comp_sub_left x

/-- The partial sum folded onto `[0, π]`:
`Sₙ(x) = (1/π) ∫₀^π (f(x + s) + f(x − s)) Dₙ(s) ds`. -/
theorem fourierPartialSum_eq_fold {f : ℝ → ℂ} (hper : Function.Periodic f (2 * π))
    (hf : IntervalIntegrable f volume (-π) π) (N : ℕ) (x : ℝ) :
    fourierPartialSum f N x = (1 / π : ℝ) •
      ∫ s in (0 : ℝ)..π, (f (x + s) + f (x - s)) * (halfDirichlet N s : ℂ) := by
  rw [fourierPartialSum_eq_integral hf]
  congr 1
  have hD : Continuous fun s => (halfDirichlet N s : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_halfDirichlet N)
  have hg : Function.Periodic (fun t => f t * (halfDirichlet N (t - x) : ℂ)) (2 * π) := fun t => by
    simp only
    rw [hper t, show t + 2 * π - x = t - x + 2 * π by ring, halfDirichlet_periodic]
  have hφ : ∀ a b, IntervalIntegrable (fun s => f (x + s) * (halfDirichlet N s : ℂ)) volume a b :=
    fun a b => (periodic_intervalIntegrable_add hper hf x a b).mul_continuousOn hD.continuousOn
  have h1 : ∫ t in (-π)..π, f t * (halfDirichlet N (t - x) : ℂ) =
      ∫ s in (-π)..π, f (x + s) * (halfDirichlet N s : ℂ) := by
    have e1 : ∫ t in (-π)..π, f t * (halfDirichlet N (t - x) : ℂ) =
        ∫ t in (-π + x)..(-π + x + 2 * π), f t * (halfDirichlet N (t - x) : ℂ) := by
      rw [hg.intervalIntegral_add_eq (-π + x) (-π), show -π + 2 * π = π by ring]
    rw [e1, show -π + x + 2 * π = π + x by ring,
      ← intervalIntegral.integral_comp_add_right (fun t => f t * (halfDirichlet N (t - x) : ℂ))]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [add_comm s x, add_sub_cancel_left]
  have h2 : ∫ s in (-π)..π, f (x + s) * (halfDirichlet N s : ℂ) =
      ∫ s in (0 : ℝ)..π, (f (x + s) + f (x - s)) * (halfDirichlet N s : ℂ) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hφ (-π) 0) (hφ 0 π), add_comm]
    have h3 : ∫ s in (-π)..0, f (x + s) * (halfDirichlet N s : ℂ) =
        ∫ s in (0 : ℝ)..π, f (x - s) * (halfDirichlet N s : ℂ) := by
      rw [← neg_zero, ← intervalIntegral.integral_comp_neg
        (fun s => f (x + s) * (halfDirichlet N s : ℂ)), neg_zero]
      refine intervalIntegral.integral_congr fun s _ => ?_
      simp only [halfDirichlet_neg, ← sub_eq_add_neg]
    rw [h3, ← intervalIntegral.integral_add (hφ 0 π)
      ((periodic_intervalIntegrable_sub hper hf x 0 π).mul_continuousOn hD.continuousOn)]
    refine intervalIntegral.integral_congr fun s _ => ?_
    ring
  rw [h1, h2]

/-- The Riemann–Lebesgue lemma for `sin((N + ½)s)`. -/
theorem tendsto_integral_mul_sin {h : ℝ → ℂ} (hh : IntervalIntegrable h volume 0 π) :
    Tendsto (fun N : ℕ => ∫ s in (0 : ℝ)..π, h s * (Real.sin (((N : ℝ) + 1 / 2) * s) : ℂ))
      atTop (𝓝 0) := by
  have hlam : Tendsto (fun N : ℕ => (N : ℝ) + 1 / 2) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have h1 := (dlmf_1_8_10 h 0 π).comp hlam
  have h2 := (dlmf_1_8_10_atBot h 0 π).comp (tendsto_neg_atTop_atBot.comp hlam)
  have := (h1.sub h2).div_const (2 * Complex.I)
  rw [sub_zero, zero_div] at this
  refine this.congr fun N => ?_
  have hc : ∀ l : ℝ, IntervalIntegrable (fun s => h s * Complex.exp (l * s * Complex.I)) volume
      0 π := fun l => hh.mul_continuousOn
    (by fun_prop : Continuous fun s : ℝ => Complex.exp (l * s * Complex.I)).continuousOn
  simp only [Function.comp_apply]
  rw [← intervalIntegral.integral_sub (hc _) (hc _), ← intervalIntegral.integral_div]
  refine intervalIntegral.integral_congr fun s _ => ?_
  rw [exp_mul_I_eq, exp_mul_I_eq, neg_mul, Real.cos_neg, Real.sin_neg]
  push_cast
  field_simp
  ring

/-- The Dirichlet quotient `(f(x + s) − f(x+) + f(x − s) − f(x−)) / sin(s/2)` is integrable on
`[0, π]` when `f` has one-sided derivatives at `x`. -/
theorem intervalIntegrable_dirichlet_quotient {f : ℝ → ℂ} (hper : Function.Periodic f (2 * π))
    (hf : IntervalIntegrable f volume (-π) π) {x : ℝ} {fL fR dL dR : ℂ}
    (hL : Tendsto (fun h : ℝ => (f (x + h) - fL) / h) (𝓝[<] 0) (𝓝 dL))
    (hR : Tendsto (fun h : ℝ => (f (x + h) - fR) / h) (𝓝[>] 0) (𝓝 dR)) :
    IntervalIntegrable (fun s : ℝ => ((f (x + s) - fR) + (f (x - s) - fL)) /
      (Real.sin (s / 2) : ℂ)) volume 0 π := by
  have hπ := Real.pi_pos
  set CR := ‖dR‖ + 1
  set CL := ‖dL‖ + 1
  obtain ⟨δR, hδR, hbR⟩ : ∃ δ > 0, ∀ s ∈ Ioo 0 δ, ‖f (x + s) - fR‖ ≤ CR * s := by
    have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), ‖(f (x + h) - fR) / h‖ < CR :=
      hR.norm.eventually (gt_mem_nhds (by simp [CR]))
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
    refine ⟨u, hu, fun s hs => ?_⟩
    have h := hsub hs
    simp only [Set.mem_ofPred_eq, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hs.1] at h
    rw [div_lt_iff₀ hs.1] at h
    exact h.le
  obtain ⟨δL, hδL, hbL⟩ : ∃ δ > 0, ∀ s ∈ Ioo 0 δ, ‖f (x - s) - fL‖ ≤ CL * s := by
    have hev : ∀ᶠ h in 𝓝[<] (0 : ℝ), ‖(f (x + h) - fL) / h‖ < CL :=
      hL.norm.eventually (gt_mem_nhds (by simp [CL]))
    obtain ⟨l, hl, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hev
    refine ⟨-l, neg_pos.mpr hl, fun s hs => ?_⟩
    have h := hsub (show -s ∈ Ioo l 0 from ⟨by linarith [hs.2], by linarith [hs.1]⟩)
    simp only [Set.mem_ofPred_eq, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_neg (neg_neg_of_pos hs.1), neg_neg, ← sub_eq_add_neg] at h
    rw [div_lt_iff₀ hs.1] at h
    exact h.le
  set δ := min (min δR δL) π
  have hδ : 0 < δ := lt_min (lt_min hδR hδL) hπ
  set ψ : ℝ → ℂ := fun s => (f (x + s) - fR) + (f (x - s) - fL)
  have hψ : IntervalIntegrable ψ volume 0 π :=
    ((periodic_intervalIntegrable_add hper hf x 0 π).sub intervalIntegrable_const).add
      ((periodic_intervalIntegrable_sub hper hf x 0 π).sub intervalIntegrable_const)
  have hψI := (intervalIntegrable_iff_integrableOn_Ioc_of_le hπ.le).mp hψ
  set G : ℝ → ℝ := fun s => (CR + CL) * π + ‖ψ s‖ * (π / δ)
  have hG : IntegrableOn G (Ioc 0 π) volume :=
    (integrableOn_const measure_Ioc_lt_top.ne).add (hψI.norm.mul_const _)
  refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hπ.le).mpr (Integrable.mono' hG ?_ ?_)
  · exact hψI.aestronglyMeasurable.mul (by fun_prop : Measurable fun s : ℝ =>
      ((Real.sin (s / 2) : ℂ))⁻¹).aestronglyMeasurable |>.congr (ae_of_all _ fun s => by
        simp only [Pi.mul_apply, div_eq_mul_inv, ψ])
  · refine ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => ?_
    have hsin : s / π ≤ Real.sin (s / 2) := by
      have := Real.mul_le_sin (x := s / 2) (by linarith [hs.1]) (by linarith [hs.2])
      calc s / π = 2 / π * (s / 2) := by field_simp
        _ ≤ _ := this
    have hspos : 0 < s / π := div_pos hs.1 hπ
    have hsinpos : 0 < Real.sin (s / 2) := hspos.trans_le hsin
    have hnorm : ‖ψ s / (Real.sin (s / 2) : ℂ)‖ = ‖ψ s‖ / Real.sin (s / 2) := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsinpos]
    show ‖ψ s / (Real.sin (s / 2) : ℂ)‖ ≤ (CR + CL) * π + ‖ψ s‖ * (π / δ)
    rw [hnorm, div_le_iff₀ hsinpos]
    have hGnn : 0 ≤ ‖ψ s‖ * (π / δ) := by positivity
    rcases lt_or_ge s δ with hsδ | hsδ
    · have h1 := hbR s ⟨hs.1, hsδ.trans_le ((min_le_left _ _).trans (min_le_left _ _))⟩
      have h2 := hbL s ⟨hs.1, hsδ.trans_le ((min_le_left _ _).trans (min_le_right _ _))⟩
      have hψs : ‖ψ s‖ ≤ (CR + CL) * s := (norm_add_le _ _).trans (by linarith)
      have : (CR + CL) * s = (CR + CL) * π * (s / π) := by field_simp
      nlinarith [mul_le_mul_of_nonneg_left hsin (by positivity : (0 : ℝ) ≤ (CR + CL) * π),
        mul_nonneg hGnn hsinpos.le]
    · have hδπ : δ / π ≤ Real.sin (s / 2) :=
        (div_le_div_of_nonneg_right hsδ hπ.le).trans hsin
      have : ‖ψ s‖ = ‖ψ s‖ * (π / δ) * (δ / π) := by field_simp
      nlinarith [mul_le_mul_of_nonneg_left hδπ hGnn, mul_nonneg (by positivity :
        (0 : ℝ) ≤ (CR + CL) * π) hsinpos.le]

/-- **DLMF 1.8.11** (Dirichlet's theorem): let `f` be `2π`-periodic and absolutely integrable on a
period.  At a point `x` where `f` has a right-hand derivative `lim_{h→0+} (f(x+h) − f(x+))/h` and a
left-hand derivative `lim_{h→0−} (f(x+h) − f(x−))/h` (generalized derivatives based at the one-sided
limits `f(x±)`, which these hypotheses force), the Fourier series 1.8.1 converges to
`½ f(x−) + ½ f(x+)`.  DLMF's "continuous except at finitely many points" is not needed. -/
theorem dlmf_1_8_11 {f : ℝ → ℂ} (hper : Function.Periodic f (2 * π))
    (hf : IntervalIntegrable f volume (-π) π) {x : ℝ} {fL fR dL dR : ℂ}
    (hL : Tendsto (fun h : ℝ => (f (x + h) - fL) / h) (𝓝[<] 0) (𝓝 dL))
    (hR : Tendsto (fun h : ℝ => (f (x + h) - fR) / h) (𝓝[>] 0) (𝓝 dR)) :
    Tendsto (fun N => fourierPartialSum f N x) atTop (𝓝 (fL / 2 + fR / 2)) := by
  have hπ := Real.pi_pos
  set ψ : ℝ → ℂ := fun s => (f (x + s) - fR) + (f (x - s) - fL)
  set h : ℝ → ℂ := fun s => ψ s / (Real.sin (s / 2) : ℂ)
  have hh : IntervalIntegrable h volume 0 π := intervalIntegrable_dirichlet_quotient hper hf hL hR
  have hD : ∀ N : ℕ, Continuous fun s => (halfDirichlet N s : ℂ) := fun N =>
    Complex.continuous_ofReal.comp (continuous_halfDirichlet N)
  have key : ∀ N : ℕ, fourierPartialSum f N x - (fL / 2 + fR / 2) = (1 / (2 * π) : ℝ) •
      ∫ s in (0 : ℝ)..π, h s * (Real.sin (((N : ℝ) + 1 / 2) * s) : ℂ) := fun N => by
    have hsum : IntervalIntegrable (fun s => (f (x + s) + f (x - s)) * (halfDirichlet N s : ℂ))
        volume 0 π := ((periodic_intervalIntegrable_add hper hf x 0 π).add
          (periodic_intervalIntegrable_sub hper hf x 0 π)).mul_continuousOn (hD N).continuousOn
    have hconst : ∫ s in (0 : ℝ)..π, (fR + fL) * (halfDirichlet N s : ℂ) = (fR + fL) * (π / 2) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
        integral_halfDirichlet]
      push_cast; ring
    have htarget : fL / 2 + fR / 2 = (1 / π : ℝ) •
        ∫ s in (0 : ℝ)..π, (fR + fL) * (halfDirichlet N s : ℂ) := by
      rw [hconst, Complex.real_smul]
      have : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      push_cast
      field_simp
      ring
    rw [fourierPartialSum_eq_fold hper hf, htarget, ← smul_sub,
      ← intervalIntegral.integral_sub hsum ((hD N).intervalIntegrable _ _ |>.const_mul _)]
    have hcongr : ∫ s in (0 : ℝ)..π, ((f (x + s) + f (x - s)) * (halfDirichlet N s : ℂ) -
        (fR + fL) * (halfDirichlet N s : ℂ)) =
        ∫ s in (0 : ℝ)..π, (1 / 2 : ℂ) * (h s * (Real.sin (((N : ℝ) + 1 / 2) * s) : ℂ)) := by
      refine intervalIntegral.integral_congr_ae (ae_of_all _ fun s hs => ?_)
      rw [Set.uIoc_of_le hπ.le] at hs
      have hsin : Real.sin (s / 2) ≠ 0 :=
        (Real.sin_pos_of_pos_of_lt_pi (by linarith [hs.1]) (by linarith [hs.2])).ne'
      have hk := two_mul_halfDirichlet_mul_sin N s
      have hk' : (Real.sin (((N : ℝ) + 1 / 2) * s) : ℂ) =
          2 * (halfDirichlet N s : ℂ) * (Real.sin (s / 2) : ℂ) := by
        rw [← hk]; push_cast; ring
      have hsC : (Real.sin (s / 2) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsin
      simp only [h, ψ]
      rw [hk']
      field_simp
      ring
    rw [hcongr, intervalIntegral.integral_const_mul, Complex.real_smul, Complex.real_smul]
    push_cast
    ring
  rw [← tendsto_sub_nhds_zero_iff]
  have := (tendsto_integral_mul_sin hh).const_smul (1 / (2 * π) : ℝ)
  rw [smul_zero] at this
  exact this.congr fun N => (key N).symm

/-- **DLMF §1.8(ii)**: the convergence in 1.8.11 is not uniform near a jump.  If the partial sums
converge uniformly on a neighbourhood `U` of `x` to a limit `F` that agrees with `f` on `U \ {x}`,
then `f(x−) = f(x+)`. -/
theorem dlmf_1_8_ii_nonuniform {f F : ℝ → ℂ} {x : ℝ} {U : Set ℝ} (hU : U ∈ 𝓝 x)
    (hunif : TendstoUniformlyOn (fun N y => fourierPartialSum f N y) F atTop U)
    (hpt : ∀ y ∈ U, y ≠ x → F y = f y) {fL fR : ℂ}
    (hL : Tendsto f (𝓝[<] x) (𝓝 fL)) (hR : Tendsto f (𝓝[>] x) (𝓝 fR)) : fL = fR := by
  have hcont : ContinuousOn F U := hunif.continuousOn (Frequently.of_forall fun N =>
    (by unfold fourierPartialSum; fun_prop :
      Continuous fun y => fourierPartialSum f N y).continuousOn)
  have hFx : ContinuousAt F x := hcont.continuousAt hU
  have hR' : Tendsto f (𝓝[>] x) (𝓝 (F x)) := by
    refine (hFx.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [nhdsWithin_le_nhds hU, self_mem_nhdsWithin] with y hy hyx
    exact hpt y hy (ne_of_gt hyx)
  have hL' : Tendsto f (𝓝[<] x) (𝓝 (F x)) := by
    refine (hFx.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [nhdsWithin_le_nhds hU, self_mem_nhdsWithin] with y hy hyx
    exact hpt y hy (ne_of_lt hyx)
  rw [tendsto_nhds_unique hL hL', tendsto_nhds_unique hR hR']

end Azurite.DLMF
