/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Order.Monotone.Basic
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Azurite.DLMF.Chapter1.SetPartitionCount
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue
import Mathlib.Topology.EMetricSpace.VariationOnFromTo
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# DLMF §1.4: Calculus of One Variable

Formalizations of the equations of the NIST Digital Library of Mathematical Functions,
<https://dlmf.nist.gov/1.4>, one theorem per equation, named `dlmf_1_4_N`; statements made in
the prose between equations are named `dlmf_1_4_i_<topic>`, `dlmf_1_4_ii_<topic>`, … after their
subsection.  Functions are real-valued functions of a real variable, `f : ℝ → ℝ`.  The ledger
`docs/dlmf_plan.md` maps every equation to its theorem.

## §1.4(i) Monotonicity

* `dlmf_1_4_i_nondecreasing`, `dlmf_1_4_i_increasing`, `dlmf_1_4_i_nonincreasing`,
  `dlmf_1_4_i_decreasing`: the four cases, as Mathlib's `MonotoneOn`, `StrictMonoOn`,
  `AntitoneOn`, `StrictAntiOn` (stated on any set `I`, not only intervals).
* `IsMonotonic`, `IsStrictlyMonotonic`; `isMonotonic_iff` (monotonic iff nondecreasing or
  nonincreasing), `IsStrictlyMonotonic.isMonotonic`.

## §1.4(ii) Continuity

* 1.4.1 `dlmf_1_4_1`, 1.4.2 `dlmf_1_4_2`: continuity on the right, `f(c+) = f(c)`, and its
  `ε`–`δ` form; 1.4.3 `dlmf_1_4_3`, `dlmf_1_4_3_eps`: continuity on the left.
* `dlmf_1_4_ii_continuousAt` (continuous iff continuous on both sides), `dlmf_1_4_ii_C_open`
  (`f ∈ C(a, b)`), `dlmf_1_4_ii_C_closed` (`f ∈ C[a, b]`).
* `HasRemovableSingularity` (`HasRemovableSingularity.continuousAt_update`: defining
  `f(c) = f(c±)` removes it), `dlmf_1_4_ii_sin_div_removable` (the example `(sin x)/x` at `0`).
* `HasSimpleDiscontinuity`, `IsPiecewiseContinuous` (`ContinuousOn.isPiecewiseContinuous`),
  `dlmf_1_4_ii_step_piecewiseContinuous` (the unit step, cf. Figure 1.4.1).

## §1.4(iii) Derivatives

* 1.4.4 `dlmf_1_4_4`, `dlmf_1_4_4_differentiable`: the derivative as the limit of difference
  quotients; 1.4.5–1.4.7 `dlmf_1_4_5`–`dlmf_1_4_7`: sum, product and quotient rules.
* 1.4.8–1.4.9 `dlmf_1_4_8`, `dlmf_1_4_9`: higher derivatives (`iteratedDeriv`);
  `dlmf_1_4_iii_Cn`, `dlmf_1_4_iii_Cinfty`: the classes `Cⁿ(I)`, `C^∞(I)` (`ContDiffOn`).
* 1.4.10 `dlmf_1_4_10`: the chain rule; `dlmf_1_4_iii_max`, `dlmf_1_4_iii_min`: `f'(c) = 0` at a
  local extremum.
* 1.4.11 `dlmf_1_4_11`: the mean value theorem; `dlmf_1_4_iii_monotone`, `dlmf_1_4_iii_antitone`,
  `dlmf_1_4_iii_const`: the sign of `f'` on `(a, b)`.
* 1.4.12 `dlmf_1_4_12`: Leibniz's formula (`iteratedDeriv_mul`).
* 1.4.13 Faà di Bruno: `dlmf_1_4_13` (DLMF's form, the sum over `m₁ + 2m₂ + ⋯ + nmₙ = n` with
  the solutions indexed by the partitions `Nat.Partition n`), `dlmf_1_4_13_tuples` (the same sum
  literally over the tuples `multiplicityVectors n`, through `multiplicities` and
  `partitionOfMultiplicities`), `dlmf_1_4_13_partitions` (Mathlib's form, a sum over ordered set
  partitions), `dlmf_1_4_13_two`, `dlmf_1_4_13_three` (`n = 2, 3`).  The passage from Mathlib's
  form to DLMF's is the count of set partitions by block sizes, `cnt_eq_bell` in
  `Azurite.DLMF.Chapter1.SetPartitionCount`.
* 1.4.14–1.4.15 L'Hôpital: `dlmf_1_4_15` (`0/0`, `deriv.lhopital_zero_nhdsNE`) and
  `dlmf_1_4_15_atTop` (`∞/∞`, proven here from Cauchy's mean value theorem:
  `lhopital_atTop_estimate`, `lhopital_atTop_right_on_Ioo`, `lhopital_atTop_left_on_Ioo`).

## §1.4(iv) Indefinite integrals

* `IsAntiderivOn` (`F' = f` on `I`), `IsAntiderivOn.add_const`, `dlmf_1_4_iv_antideriv`
  (`∫ f dx = F(x) + C`: on an open interval any two indefinite integrals differ by a constant).
* 1.4.16 `dlmf_1_4_16` (integration by parts for indefinite integrals) and
  `dlmf_1_4_16_definite` (`intervalIntegral.integral_mul_deriv_eq_deriv_mul`).
* 1.4.17 `dlmf_1_4_17` (`∫ xⁿ = xⁿ⁺¹/(n + 1)`, integer `n ≠ −1`), `dlmf_1_4_17_neg_one`
  (`∫ x⁻¹ = ln|x|`), `dlmf_1_4_17_rpow` (real `n ≠ −1`, `x > 0`).

## §1.4(v) Definite integrals

* Riemann integrals: `TaggedPartition` (`a = x₀ < ⋯ < xₙ = b`, tags `ξⱼ ∈ [xⱼ, xⱼ₊₁]`),
  `TaggedPartition.riemannSum`, `HasRiemannIntegral` (1.4.18 as `max(xⱼ₊₁ − xⱼ) → 0`),
  `RiemannIntegrable`, `HasRiemannIntegral.unique` (via `uniformPartition`).
* `hasRiemannIntegral_of_bounded`: a bounded function continuous on `[a, b]` off a finite set has
  Riemann integral `∫ x in a..b, f x`; hence 1.4.18 `dlmf_1_4_18` (continuous) and
  `dlmf_1_4_v_piecewise` (piecewise continuous, `IsPiecewiseContinuous.exists_bound`).
* 1.4.19 `dlmf_1_4_19` (and `HasRiemannIntegral.linear`), 1.4.20 `dlmf_1_4_20`, 1.4.21
  `dlmf_1_4_21`.
* Infinite integrals: `ConvergesAtTop`, `ConvergesAtBot` (1.4.22), `ConvergesLeft`,
  `ConvergesRight` (1.4.23); `dlmf_1_4_22`, `dlmf_1_4_22_Iic`, `dlmf_1_4_23`,
  `dlmf_1_4_23_right` (the limits equal the Lebesgue integrals); `dlmf_1_4_v_abs_atTop`,
  `dlmf_1_4_v_abs_left` (absolute convergence implies convergence).
* Stieltjes, Lebesgue, Lebesgue–Stieltjes integrals: `dlmf_1_4_v_stieltjes_measure` (Mathlib's
  `StieltjesFunction.measure`, `dα((c, d]) = α(d) − α(c)`), `dlmf_1_4_v_lebesgue` (Lebesgue
  measure is `dα` for `α(x) = x`), `TaggedPartition.stieltjesSum`, `HasStieltjesIntegral`,
  `hasStieltjesIntegral_of_deriv` (for `α` with continuous derivative `w`, the Stieltjes integral
  is `∫ f w`).
* Absolutely continuous Stieltjes measure: 1.4.23_1 `dlmf_1_4_23_1` (`α(d) − α(c) = ∫_c^d w` gives
  `dα = w dx`, `withDensity`), 1.4.23_2 `dlmf_1_4_23_2` (`∫ f dα = ∫ f w`),
  `dlmf_1_4_v_absCont_of_deriv`, `stieltjesOfDeriv`, `stieltjesOfDeriv_measure` (differentiable
  `α` with continuous `α' = w`).
* Stieltjes measure with `α` discontinuous: `heaviside` (`H(x − x₀)`), `heaviside_measure`
  (`dα = δ(x − x₀) dx`), `dlmf_1_4_v_heaviside` (`∫_a^b f dα = f(xₙ)` or `0`), 1.4.23_3
  `dlmf_1_4_23_3` (`∫ f dα = ∫ w f + ∑ wₙ f(xₙ)`; `measure_sum_smul`, `integral_sum_dirac`,
  `integrable_sum_dirac`).
* Cauchy principal values: `HasPrincipalValue` (1.4.24), `HasPrincipalValueInfty` (1.4.25);
  `dlmf_1_4_24`, `dlmf_1_4_25` (they equal the integral when it exists),
  `dlmf_1_4_24_inv` (`⨍_{−1}^1 dx/x = 0`), `dlmf_1_4_25_id` (`⨍ x dx = 0`).
* 1.4.26–1.4.27 `dlmf_1_4_26`, `dlmf_1_4_27`: the fundamental theorem of calculus.
* 1.4.28 `dlmf_1_4_28`, `dlmf_1_4_28_piecewise`: change of variables.
* 1.4.29 `dlmf_1_4_29`: the first mean value theorem; 1.4.30 `dlmf_1_4_30` (and
  `dlmf_1_4_30_monotone`, `intervalIntegrable_mul_of_monotoneOn`): the second mean value theorem.
* 1.4.31 `dlmf_1_4_31`: repeated integrals, `repeatedIntegral a n f b = (1/n!) ∫_a^b (b − x)^n f`
  (`primitive`, `integral_pow_mul_eq_succ_mul_primitive`: one integration by parts per step).
* 1.4.32 `l2NormSq`, `dlmf_1_4_32`: square-integrable functions (Mathlib's `MemLp f 2`).
* Functions of bounded variation (with Olver (1997b) §11.2–11.5, pp. 27–29): 1.4.33
  `dlmf_1_4_33` (`𝒱_{a,b}(f) = eVariationOn f s` is the supremum of `∑ |f(xⱼ) − f(xⱼ₋₁)|` over
  point sets `x₀ < ⋯ < xₙ` of the closure `s`), `dlmf_1_4_v_variation_closure`,
  `dlmf_1_4_v_boundedVariationOn_iff`, `dlmf_1_4_v_boundedVariationOn_iff_bdd`,
  `leftVariation` (`𝒱_{a,x}(f)`), `dlmf_1_4_v_jordan` (`g = 𝒱_{a,x}(f)` and `h = g − f`
  nondecreasing and bounded, `f = g − h`); `olver_11_3` (`𝒱 ≥ ‖f(b) − f(a)‖`), `olver_11_01`
  (monotonic `f`), `olver_11_3_subdivision` (subdivision at the extrema); 1.4.34 `olver_11_02`
  (`𝒱_{a,b}(f) = ∫_a^b ‖f'‖` for `f'` continuous on `[a, b]`, `E`-valued, via Riemann sums of
  `‖f'‖`), `eVariationOn_eq_integral_of_isOpen` (open interval, `[c, d]` exhaustion:
  `exists_Icc_exhaustion`), `dlmf_1_4_34` (`f` continuous on `[a, b]`, `f'` on `(a, b)`),
  `dlmf_1_4_34_Ioi`, `dlmf_1_4_34_Iio`, `dlmf_1_4_34_univ`, `dlmf_1_4_34_real`, `olver_11_5`
  (complex `f`), `variationIntegral` (DLMF's extension to arbitrary `a, b`); Olver Ex. 11.1
  `olver_ex_11_1_add`, `olver_ex_11_1_norm`, `olver_ex_11_1_abs`, `olver_ex_11_1_abs_eq`
  (equality for continuous real `f`); Ex. 11.2 (ii) `olver_ex_11_2_ii` (step function), (iii)
  `olver_ex_11_2_iii` (`𝒱(sech) = 2`, via `eVariationOn_Iic_of_monotoneOn`,
  `eVariationOn_Ici_of_antitoneOn`).  Not formalized: Ex. 11.2 (i), (iv), and the variation
  along a path in `ℂ` (Olver §11.5 second half, Ex. 11.3–11.4).
-/

namespace Azurite.DLMF

open Set Filter Topology

/-! ### §1.4(i) Monotonicity -/

/-- **DLMF §1.4(i)**: `f` is nondecreasing on `I` if `f(x₁) ≤ f(x₂)` whenever `x₁ < x₂` in `I`
(Mathlib's `MonotoneOn`). -/
theorem dlmf_1_4_i_nondecreasing (f : ℝ → ℝ) (I : Set ℝ) :
    MonotoneOn f I ↔ ∀ x₁ ∈ I, ∀ x₂ ∈ I, x₁ < x₂ → f x₁ ≤ f x₂ := by
  refine ⟨fun h x₁ h₁ x₂ h₂ hlt => h h₁ h₂ hlt.le, fun h x₁ h₁ x₂ h₂ hle => ?_⟩
  rcases hle.lt_or_eq with hlt | rfl
  · exact h x₁ h₁ x₂ h₂ hlt
  · exact le_rfl

/-- **DLMF §1.4(i)**: `f` is increasing (strictly increasing) on `I` if `f(x₁) < f(x₂)` whenever
`x₁ < x₂` in `I` (Mathlib's `StrictMonoOn`). -/
theorem dlmf_1_4_i_increasing (f : ℝ → ℝ) (I : Set ℝ) :
    StrictMonoOn f I ↔ ∀ x₁ ∈ I, ∀ x₂ ∈ I, x₁ < x₂ → f x₁ < f x₂ :=
  ⟨fun h _ h₁ _ h₂ hlt => h h₁ h₂ hlt, fun h _ h₁ _ h₂ hlt => h _ h₁ _ h₂ hlt⟩

/-- **DLMF §1.4(i)**: `f` is nonincreasing on `I` if `f(x₁) ≥ f(x₂)` whenever `x₁ < x₂` in `I`
(Mathlib's `AntitoneOn`). -/
theorem dlmf_1_4_i_nonincreasing (f : ℝ → ℝ) (I : Set ℝ) :
    AntitoneOn f I ↔ ∀ x₁ ∈ I, ∀ x₂ ∈ I, x₁ < x₂ → f x₂ ≤ f x₁ := by
  refine ⟨fun h x₁ h₁ x₂ h₂ hlt => h h₁ h₂ hlt.le, fun h x₁ h₁ x₂ h₂ hle => ?_⟩
  rcases hle.lt_or_eq with hlt | rfl
  · exact h x₁ h₁ x₂ h₂ hlt
  · exact le_rfl

/-- **DLMF §1.4(i)**: `f` is decreasing (strictly decreasing) on `I` if `f(x₁) > f(x₂)` whenever
`x₁ < x₂` in `I` (Mathlib's `StrictAntiOn`). -/
theorem dlmf_1_4_i_decreasing (f : ℝ → ℝ) (I : Set ℝ) :
    StrictAntiOn f I ↔ ∀ x₁ ∈ I, ∀ x₂ ∈ I, x₁ < x₂ → f x₂ < f x₁ :=
  ⟨fun h _ h₁ _ h₂ hlt => h h₁ h₂ hlt, fun h _ h₁ _ h₂ hlt => h _ h₁ _ h₂ hlt⟩

/-- **DLMF §1.4(i)**: each of the four cases is classified as monotonic. -/
def IsMonotonic (f : ℝ → ℝ) (I : Set ℝ) : Prop :=
  MonotoneOn f I ∨ StrictMonoOn f I ∨ AntitoneOn f I ∨ StrictAntiOn f I

/-- **DLMF §1.4(i)**: the strictly increasing or strictly decreasing cases are strictly
monotonic. -/
def IsStrictlyMonotonic (f : ℝ → ℝ) (I : Set ℝ) : Prop :=
  StrictMonoOn f I ∨ StrictAntiOn f I

/-- The strict cases are special cases of the non-strict ones, so a function is monotonic iff it
is nondecreasing or nonincreasing. -/
theorem isMonotonic_iff (f : ℝ → ℝ) (I : Set ℝ) :
    IsMonotonic f I ↔ MonotoneOn f I ∨ AntitoneOn f I := by
  unfold IsMonotonic
  constructor
  · rintro (h | h | h | h)
    · exact Or.inl h
    · exact Or.inl h.monotoneOn
    · exact Or.inr h
    · exact Or.inr h.antitoneOn
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))

theorem IsStrictlyMonotonic.isMonotonic {f : ℝ → ℝ} {I : Set ℝ} (h : IsStrictlyMonotonic f I) :
    IsMonotonic f I := by
  rcases h with h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr h))

/-! ### §1.4(ii) Continuity

The one-sided limits `f(c+)` and `f(c−)` are limits along `𝓝[>] c` and `𝓝[<] c`; continuity on the
right (left) at `c` is Mathlib's `ContinuousWithinAt f (Ici c) c`
(`ContinuousWithinAt f (Iic c) c`).
-/

/-- **DLMF 1.4.1**: `f` is continuous on the right at `c` iff `f(c+) = lim_{x→c+} f(x) = f(c)`
(`continuousWithinAt_Ioi_iff_Ici`). -/
theorem dlmf_1_4_1 (f : ℝ → ℝ) (c : ℝ) :
    ContinuousWithinAt f (Ici c) c ↔ Tendsto f (𝓝[>] c) (𝓝 (f c)) := by
  rw [← continuousWithinAt_Ioi_iff_Ici]
  rfl

/-- **DLMF 1.4.2**: continuity on the right at `c` in `ε`–`δ` form: for every `ε > 0` there is
`δ > 0` with `|f(c + α) − f(c)| < ε` for all `0 ≤ α < δ` (`Metric.continuousWithinAt_iff`). -/
theorem dlmf_1_4_2 (f : ℝ → ℝ) (c : ℝ) :
    ContinuousWithinAt f (Ici c) c ↔
      ∀ ε > 0, ∃ δ > 0, ∀ α, 0 ≤ α → α < δ → |f (c + α) - f c| < ε := by
  rw [Metric.continuousWithinAt_iff]
  refine forall₂_congr fun ε _ => exists_congr fun δ => and_congr_right fun _ => ?_
  constructor
  · intro h α hα hαδ
    have := @h (c + α) (by simp [hα]) (by rw [Real.dist_eq]; simpa [abs_of_nonneg hα])
    rwa [Real.dist_eq] at this
  · intro h x hx hxδ
    have hx' : (0 : ℝ) ≤ x - c := sub_nonneg.mpr hx
    rw [Real.dist_eq, abs_of_nonneg hx'] at hxδ
    have := h (x - c) hx' hxδ
    rwa [add_sub_cancel, ← Real.dist_eq] at this

/-- **DLMF 1.4.3**: `f` is continuous on the left at `c` iff `f(c−) = lim_{x→c−} f(x) = f(c)`
(`continuousWithinAt_Iio_iff_Iic`). -/
theorem dlmf_1_4_3 (f : ℝ → ℝ) (c : ℝ) :
    ContinuousWithinAt f (Iic c) c ↔ Tendsto f (𝓝[<] c) (𝓝 (f c)) := by
  rw [← continuousWithinAt_Iio_iff_Iic]
  rfl

/-- **DLMF 1.4.3**, the `ε`–`δ` form on the left: `|f(c − α) − f(c)| < ε` for all `0 ≤ α < δ`. -/
theorem dlmf_1_4_3_eps (f : ℝ → ℝ) (c : ℝ) :
    ContinuousWithinAt f (Iic c) c ↔
      ∀ ε > 0, ∃ δ > 0, ∀ α, 0 ≤ α → α < δ → |f (c - α) - f c| < ε := by
  rw [Metric.continuousWithinAt_iff]
  refine forall₂_congr fun ε _ => exists_congr fun δ => and_congr_right fun _ => ?_
  constructor
  · intro h α hα hαδ
    have := @h (c - α) (by simp [hα]) (by rw [Real.dist_eq]; simpa [abs_of_nonneg hα])
    rwa [Real.dist_eq] at this
  · intro h x hx hxδ
    have hx' : (0 : ℝ) ≤ c - x := sub_nonneg.mpr hx
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg hx'] at hxδ
    have := h (c - x) hx' hxδ
    rwa [sub_sub_cancel, ← Real.dist_eq] at this

/-- **DLMF §1.4(ii)**: `f` is continuous at `c` when both 1.4.1 and 1.4.3 apply
(`continuousAt_iff_continuous_left_right`). -/
theorem dlmf_1_4_ii_continuousAt (f : ℝ → ℝ) (c : ℝ) :
    ContinuousAt f c ↔ ContinuousWithinAt f (Ici c) c ∧ ContinuousWithinAt f (Iic c) c := by
  rw [continuousAt_iff_continuous_left_right, and_comm]

/-- **DLMF §1.4(ii)**: `f ∈ C(a, b)` iff `f` is continuous at each point of `(a, b)`
(`IsOpen.continuousOn_iff`). -/
theorem dlmf_1_4_ii_C_open (f : ℝ → ℝ) (a b : ℝ) :
    ContinuousOn f (Ioo a b) ↔ ∀ c ∈ Ioo a b, ContinuousAt f c :=
  isOpen_Ioo.continuousOn_iff

/-- **DLMF §1.4(ii)**: for `a < b`, `f ∈ C[a, b]` iff `f ∈ C(a, b)`, `f` is continuous on the right
at `a`, and continuous on the left at `b`. -/
theorem dlmf_1_4_ii_C_closed (f : ℝ → ℝ) {a b : ℝ} (hab : a < b) :
    ContinuousOn f (Icc a b) ↔ (∀ c ∈ Ioo a b, ContinuousAt f c) ∧
      ContinuousWithinAt f (Ici a) a ∧ ContinuousWithinAt f (Iic b) b := by
  constructor
  · intro h
    refine ⟨fun c hc => (h c (Ioo_subset_Icc_self hc)).continuousAt (Icc_mem_nhds hc.1 hc.2),
      ?_, ?_⟩
    · exact (h a (left_mem_Icc.mpr hab.le)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hab)
    · exact (h b (right_mem_Icc.mpr hab.le)).mono_of_mem_nhdsWithin (Icc_mem_nhdsLE hab)
  · rintro ⟨hint, ha, hb⟩ x hx
    rcases eq_or_lt_of_le hx.1 with rfl | hax
    · exact ha.mono Icc_subset_Ici_self
    rcases eq_or_lt_of_le hx.2 with rfl | hxb
    · exact hb.mono Icc_subset_Iic_self
    exact (hint x ⟨hax, hxb⟩).continuousWithinAt

/-- **DLMF §1.4(ii)**: `f` has a removable singularity at `c` when `f(c+) = f(c−)`; the value of
`f` at `c` plays no role (the DLMF leaves it undefined). -/
def HasRemovableSingularity (f : ℝ → ℝ) (c : ℝ) : Prop :=
  ∃ L, Tendsto f (𝓝[>] c) (𝓝 L) ∧ Tendsto f (𝓝[<] c) (𝓝 L)

/-- A removable singularity is removed by defining `f(c) = f(c+) = f(c−)`. -/
theorem HasRemovableSingularity.continuousAt_update {f : ℝ → ℝ} {c L : ℝ}
    (hr : Tendsto f (𝓝[>] c) (𝓝 L)) (hl : Tendsto f (𝓝[<] c) (𝓝 L)) :
    ContinuousAt (Function.update f c L) c := by
  rw [continuousAt_iff_continuous_left_right, ← continuousWithinAt_Iio_iff_Iic,
    ← continuousWithinAt_Ioi_iff_Ici]
  constructor
  · change Tendsto _ _ _
    rw [Function.update_self]
    refine hl.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [Function.update_of_ne (ne_of_lt hx)]
  · change Tendsto _ _ _
    rw [Function.update_self]
    refine hr.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [Function.update_of_ne (ne_of_gt hx)]

/-- **DLMF §1.4(ii)**, the example: `f(x) = (sin x)/x` has a removable singularity at `c = 0`, with
`f(0+) = f(0−) = 1` (`Real.continuous_sinc`). -/
theorem dlmf_1_4_ii_sin_div_removable :
    HasRemovableSingularity (fun x => Real.sin x / x) 0 := by
  have h : Tendsto Real.sinc (𝓝[≠] 0) (𝓝 1) := by
    rw [← Real.sinc_zero]
    exact Real.continuous_sinc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h' : Tendsto (fun x => Real.sin x / x) (𝓝[≠] 0) (𝓝 1) := by
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact Real.sinc_of_ne_zero hx
  exact ⟨1, h'.mono_left (nhdsWithin_mono _ fun x hx => ne_of_gt hx),
    h'.mono_left (nhdsWithin_mono _ fun x hx => ne_of_lt hx)⟩

/-- **DLMF §1.4(ii)**: `f` has a simple discontinuity at `c` when `f(c+)` and `f(c−)` exist but
`f(c+) ≠ f(c−)`. -/
def HasSimpleDiscontinuity (f : ℝ → ℝ) (c : ℝ) : Prop :=
  ∃ L R, Tendsto f (𝓝[>] c) (𝓝 R) ∧ Tendsto f (𝓝[<] c) (𝓝 L) ∧ R ≠ L

/-- **DLMF §1.4(ii)**: `f` is piecewise (sectionally) continuous on `I` if it is continuous on `I`
save for a finite number of simple discontinuities. -/
def IsPiecewiseContinuous (f : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∃ S : Finset ℝ, (∀ c ∈ I, c ∉ S → ContinuousWithinAt f I c) ∧
    ∀ c ∈ S, HasSimpleDiscontinuity f c

/-- Continuous functions are piecewise continuous (no discontinuities). -/
theorem ContinuousOn.isPiecewiseContinuous {f : ℝ → ℝ} {I : Set ℝ} (h : ContinuousOn f I) :
    IsPiecewiseContinuous f I :=
  ⟨∅, fun c hc _ => h c hc, fun c hc => absurd hc (Finset.notMem_empty c)⟩

/-- **DLMF §1.4(ii)**, an example of a piecewise continuous function (cf. Figure 1.4.1): the unit
step, `0` for `x < 0` and `1` for `x ≥ 0`, with a simple discontinuity at `0`. -/
theorem dlmf_1_4_ii_step_piecewiseContinuous :
    IsPiecewiseContinuous (fun x : ℝ => if 0 ≤ x then 1 else 0) univ := by
  set f : ℝ → ℝ := fun x => if 0 ≤ x then 1 else 0 with hf
  have hpos : ∀ᶠ x in 𝓝[>] (0 : ℝ), f x = 1 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp [hf, le_of_lt (mem_Ioi.mp hx)]
  have hneg : ∀ᶠ x in 𝓝[<] (0 : ℝ), f x = 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp [hf, not_le.mpr (mem_Iio.mp hx)]
  refine ⟨{0}, fun c _ hc => ?_, fun c hc => ?_⟩
  · have hc0 : c ≠ 0 := by simpa using hc
    refine ContinuousAt.continuousWithinAt ?_
    rcases lt_or_gt_of_ne hc0 with h | h
    · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
      filter_upwards [Iio_mem_nhds h] with x hx
      simp [hf, not_le.mpr (mem_Iio.mp hx)]
    · refine (continuousAt_const (y := (1 : ℝ))).congr ?_
      filter_upwards [Ioi_mem_nhds h] with x hx
      simp [hf, le_of_lt (mem_Ioi.mp hx)]
  · rw [Finset.mem_singleton] at hc
    subst hc
    exact ⟨0, 1, tendsto_const_nhds.congr' (hpos.mono fun x hx => hx.symm),
      tendsto_const_nhds.congr' (hneg.mono fun x hx => hx.symm), one_ne_zero⟩


/-! ### §1.4(iii) Derivatives -/

section Derivatives

open Finset
open scoped ContDiff

/-- **DLMF 1.4.4**: `f'(x) = lim_{h→0} (f(x + h) − f(x))/h`
(`hasDerivAt_iff_tendsto_slope_zero`). -/
theorem dlmf_1_4_4 (f : ℝ → ℝ) (x f' : ℝ) :
    HasDerivAt f f' x ↔ Tendsto (fun h => (f (x + h) - f x) / h) (𝓝[≠] 0) (𝓝 f') := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  simp only [smul_eq_mul, inv_mul_eq_div]

/-- **DLMF 1.4.4**: `f` is differentiable at `x` when this limit exists. -/
theorem dlmf_1_4_4_differentiable (f : ℝ → ℝ) (x : ℝ) :
    DifferentiableAt ℝ f x ↔ ∃ L, Tendsto (fun h => (f (x + h) - f x) / h) (𝓝[≠] 0) (𝓝 L) :=
  ⟨fun h => ⟨_, (dlmf_1_4_4 f x _).mp h.hasDerivAt⟩,
    fun ⟨L, h⟩ => ((dlmf_1_4_4 f x L).mpr h).differentiableAt⟩

/-- **DLMF 1.4.5**: `(f + g)' = f' + g'` (`deriv_add`). -/
theorem dlmf_1_4_5 {f g : ℝ → ℝ} {x : ℝ} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) : deriv (fun y => f y + g y) x = deriv f x + deriv g x :=
  deriv_add hf hg

/-- **DLMF 1.4.6**: `(fg)' = f'g + fg'` (`deriv_mul`). -/
theorem dlmf_1_4_6 {f g : ℝ → ℝ} {x : ℝ} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    deriv (fun y => f y * g y) x = deriv f x * g x + f x * deriv g x :=
  deriv_mul hf hg

/-- **DLMF 1.4.7**: `(f/g)' = (f'g − fg')/g²` where `g(x) ≠ 0` (`deriv_div`). -/
theorem dlmf_1_4_7 {f g : ℝ → ℝ} {x : ℝ} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (hx : g x ≠ 0) :
    deriv (fun y => f y / g y) x = (deriv f x * g x - f x * deriv g x) / g x ^ 2 :=
  deriv_div hf hg hx

/-- **DLMF 1.4.8**: `f⁽²⁾ = d/dx (df/dx)` (`iteratedDeriv_succ`, `iteratedDeriv_one`). -/
theorem dlmf_1_4_8 (f : ℝ → ℝ) : iteratedDeriv 2 f = deriv (deriv f) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]

/-- **DLMF 1.4.9**: `f⁽ⁿ⁾ = d/dx f⁽ⁿ⁻¹⁾` (`iteratedDeriv_succ`). -/
theorem dlmf_1_4_9 (f : ℝ → ℝ) (n : ℕ) : iteratedDeriv (n + 1) f = deriv (iteratedDeriv n f) :=
  iteratedDeriv_succ

/-- **DLMF §1.4(iii)**: `f ∈ Cⁿ(I)` (`ContDiffOn ℝ n f I`) iff `f, f', …, f⁽ⁿ⁾` exist and are
continuous on `I`, for an interval `I` with nonempty interior (more generally any set with unique
derivatives; `contDiffOn_nat_iff_continuousOn_differentiableOn_deriv`). -/
theorem dlmf_1_4_iii_Cn {f : ℝ → ℝ} {I : Set ℝ} (hI : UniqueDiffOn ℝ I) (n : ℕ) :
    ContDiffOn ℝ n f I ↔ (∀ m ≤ n, ContinuousOn (iteratedDerivWithin m f I) I) ∧
      ∀ m < n, DifferentiableOn ℝ (iteratedDerivWithin m f I) I :=
  contDiffOn_nat_iff_continuousOn_differentiableOn_deriv hI

/-- **DLMF §1.4(iii)**: `f ∈ C^∞(I)` iff `f ∈ Cⁿ(I)` for every `n` (`contDiffOn_infty`). -/
theorem dlmf_1_4_iii_Cinfty (f : ℝ → ℝ) (I : Set ℝ) :
    ContDiffOn ℝ ∞ f I ↔ ∀ n : ℕ, ContDiffOn ℝ n f I :=
  contDiffOn_infty

/-- **DLMF 1.4.10**, the chain rule: for `h(x) = f(g(x))`, `h'(x) = f'(g(x)) g'(x)`
(`deriv_comp`). -/
theorem dlmf_1_4_10 {f g : ℝ → ℝ} {x : ℝ} (hf : DifferentiableAt ℝ f (g x))
    (hg : DifferentiableAt ℝ g x) : deriv (fun y => f (g y)) x = deriv f (g x) * deriv g x :=
  deriv_comp x hf hg

/-- **DLMF §1.4(iii)**, maxima: if `f(x) ≤ f(c)` for `c − δ ≤ x ≤ c + δ` (`δ > 0`) then
`f'(c) = 0` (`IsLocalMax.deriv_eq_zero`; `f'(c) = 0` by convention if `f` is not
differentiable at `c`). -/
theorem dlmf_1_4_iii_max {f : ℝ → ℝ} {c δ : ℝ} (hδ : 0 < δ)
    (h : ∀ x ∈ Icc (c - δ) (c + δ), f x ≤ f c) : deriv f c = 0 :=
  IsLocalMax.deriv_eq_zero (Filter.mem_of_superset
    (Icc_mem_nhds (by linarith) (by linarith)) h)

/-- **DLMF §1.4(iii)**, minima: if `f(x) ≥ f(c)` for `c − δ ≤ x ≤ c + δ` then `f'(c) = 0`. -/
theorem dlmf_1_4_iii_min {f : ℝ → ℝ} {c δ : ℝ} (hδ : 0 < δ)
    (h : ∀ x ∈ Icc (c - δ) (c + δ), f c ≤ f x) : deriv f c = 0 :=
  IsLocalMin.deriv_eq_zero (Filter.mem_of_superset
    (Icc_mem_nhds (by linarith) (by linarith)) h)

/-- **DLMF 1.4.11**, the mean value theorem: if `f` is continuous on `[a, b]` and differentiable
on `(a, b)`, there is `c ∈ (a, b)` with `f(b) − f(a) = (b − a) f'(c)` (`exists_deriv_eq_slope`). -/
theorem dlmf_1_4_11 {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hfc : ContinuousOn f (Icc a b))
    (hfd : DifferentiableOn ℝ f (Ioo a b)) :
    ∃ c ∈ Ioo a b, f b - f a = (b - a) * deriv f c := by
  obtain ⟨c, hc, h⟩ := exists_deriv_eq_slope f hab hfc hfd
  refine ⟨c, hc, ?_⟩
  rw [h, mul_div_cancel₀ _ (sub_ne_zero.mpr hab.ne')]

/-- **DLMF §1.4(iii)**: if `f'(x) ≥ 0` on `(a, b)` then `f` is nondecreasing on `(a, b)`
(`monotoneOn_of_deriv_nonneg`). -/
theorem dlmf_1_4_iii_monotone {f : ℝ → ℝ} {a b : ℝ} (hf : DifferentiableOn ℝ f (Ioo a b))
    (h : ∀ x ∈ Ioo a b, 0 ≤ deriv f x) : MonotoneOn f (Ioo a b) :=
  monotoneOn_of_deriv_nonneg (convex_Ioo a b) hf.continuousOn (by rwa [interior_Ioo])
    (by rwa [interior_Ioo])

/-- **DLMF §1.4(iii)**: if `f'(x) ≤ 0` on `(a, b)` then `f` is nonincreasing on `(a, b)`
(`antitoneOn_of_deriv_nonpos`). -/
theorem dlmf_1_4_iii_antitone {f : ℝ → ℝ} {a b : ℝ} (hf : DifferentiableOn ℝ f (Ioo a b))
    (h : ∀ x ∈ Ioo a b, deriv f x ≤ 0) : AntitoneOn f (Ioo a b) :=
  antitoneOn_of_deriv_nonpos (convex_Ioo a b) hf.continuousOn (by rwa [interior_Ioo])
    (by rwa [interior_Ioo])

/-- **DLMF §1.4(iii)**: if `f'(x) = 0` on `(a, b)` then `f` is constant on `(a, b)`. -/
theorem dlmf_1_4_iii_const {f : ℝ → ℝ} {a b : ℝ} (hf : DifferentiableOn ℝ f (Ioo a b))
    (h : ∀ x ∈ Ioo a b, deriv f x = 0) : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo a b, f x = f y := by
  have hm := dlmf_1_4_iii_monotone hf fun x hx => (h x hx).ge
  have ha := dlmf_1_4_iii_antitone hf fun x hx => (h x hx).le
  intro x hx y hy
  rcases le_total x y with hxy | hxy
  · exact le_antisymm (hm hx hy hxy) (ha hx hy hxy)
  · exact le_antisymm (ha hy hx hxy) (hm hy hx hxy)

/-- **DLMF 1.4.12**, Leibniz's formula: `(fg)⁽ⁿ⁾ = ∑ₖ C(n, k) f⁽ⁿ⁻ᵏ⁾ g⁽ᵏ⁾` for `f, g` of class `Cⁿ`
near `x` (`iteratedDeriv_mul`). -/
theorem dlmf_1_4_12 {f g : ℝ → ℝ} {x : ℝ} {n : ℕ} (hf : ContDiffAt ℝ n f x)
    (hg : ContDiffAt ℝ n g x) :
    iteratedDeriv n (fun y => f y * g y) x =
      ∑ k ∈ range (n + 1), (n.choose k : ℝ) * iteratedDeriv (n - k) f x * iteratedDeriv k g x := by
  rw [show (fun y => f y * g y) = f * g from rfl, iteratedDeriv_mul hf hg,
    ← sum_range_reflect]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [show n - (n + 1 - 1 - k) = k by omega, show n + 1 - 1 - k = n - k by omega,
    Nat.choose_symm hk']

/-- **DLMF 1.4.13**, Faà di Bruno's formula:
`dⁿ/dxⁿ f(g(x)) = ∑ (n!/(m₁! m₂! ⋯ mₙ!)) f⁽ᵏ⁾(g(x)) (g'(x)/1!)^{m₁} (g''(x)/2!)^{m₂} ⋯
(g⁽ⁿ⁾(x)/n!)^{mₙ}`,
the sum over all nonnegative `m₁, …, mₙ` with `m₁ + 2m₂ + ⋯ + nmₙ = n` and `k = m₁ + ⋯ + mₙ`.
Here the solutions `(m₁, …, mₙ)` are indexed by the partitions `p` of `n` (`Nat.Partition n`),
with `mⱼ = count j p.parts` and `k = card p.parts`; for `f, g` of class `Cⁿ` near `x` and `g x`.
Proven by grouping Mathlib's sum over ordered set partitions
(`iteratedDeriv_comp_eq_sum_orderedFinpartition`) by block sizes, with the count
`cnt_eq_bell`. -/
theorem dlmf_1_4_13 {f g : ℝ → ℝ} {x : ℝ} {n : ℕ} (hf : ContDiffAt ℝ n f (g x))
    (hg : ContDiffAt ℝ n g x) :
    iteratedDeriv n (fun y => f (g y)) x = ∑ p : Nat.Partition n,
      ((n.factorial : ℝ) / ∏ j ∈ Finset.Icc 1 n, ((p.parts.count j).factorial : ℝ)) *
        iteratedDeriv (Multiset.card p.parts) f (g x) *
        ∏ j ∈ Finset.Icc 1 n, (iteratedDeriv j g x / (j.factorial : ℝ)) ^ p.parts.count j := by
  rw [show (fun y => f (g y)) = f ∘ g from rfl, iteratedDeriv_comp_eq_sum_partition hf hg]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hT := partition_toFinset_subset_Icc p
  have hzero : ∀ j ∈ Finset.Icc 1 n, j ∉ p.parts.toFinset → p.parts.count j = 0 :=
    fun j _ hj => Multiset.count_eq_zero.mpr fun h => hj (Multiset.mem_toFinset.mpr h)
  have h1 : ∏ j ∈ Finset.Icc 1 n, ((p.parts.count j).factorial : ℝ) =
      ∏ j ∈ p.parts.toFinset, ((p.parts.count j).factorial : ℝ) :=
    (Finset.prod_subset hT fun j hj hj' => by rw [hzero j hj hj']; simp).symm
  have h2 : ∏ j ∈ Finset.Icc 1 n, (iteratedDeriv j g x / (j.factorial : ℝ)) ^ p.parts.count j =
      ∏ j ∈ p.parts.toFinset, (iteratedDeriv j g x / (j.factorial : ℝ)) ^ p.parts.count j :=
    (Finset.prod_subset hT fun j hj hj' => by rw [hzero j hj hj', pow_zero]).symm
  rw [h1, h2, bell_cast_eq, fdbTerm, Finset.prod_multiset_map_count]
  simp_rw [div_pow]
  rw [Finset.prod_div_distrib]
  have hA : (∏ j ∈ p.parts.toFinset, (j.factorial : ℝ) ^ p.parts.count j) ≠ 0 := by positivity
  have hB : (∏ j ∈ p.parts.toFinset, ((p.parts.count j).factorial : ℝ)) ≠ 0 := by positivity
  field_simp

/-- The multiplicity vector `(m₁, …, mₙ)` of a partition of `n`, `mᵢ = count i p.parts`, indexed
by `Fin n` through `i ↦ i + 1`. -/
def multiplicities {n : ℕ} (p : Nat.Partition n) (i : Fin n) : ℕ := p.parts.count ((i : ℕ) + 1)

/-- The tuples `(m₁, …, mₙ)` of nonnegative integers with `m₁ + 2m₂ + ⋯ + nmₙ = n`. -/
def multiplicityVectors (n : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset fun _ : Fin n => range (n + 1)).filter
    fun m => ∑ i : Fin n, ((i : ℕ) + 1) * m i = n

theorem prod_Icc_one_eq_prod_fin {n : ℕ} {M : Type*} [CommMonoid M] (F : ℕ → M) :
    ∏ j ∈ Finset.Icc 1 n, F j = ∏ i : Fin n, F ((i : ℕ) + 1) := by
  have h : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [h, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel, ← Fin.prod_univ_eq_prod_range]
  exact Finset.prod_congr rfl fun i _ => by rw [add_comm]

theorem sum_Icc_one_eq_sum_fin {n : ℕ} {M : Type*} [AddCommMonoid M] (F : ℕ → M) :
    ∑ j ∈ Finset.Icc 1 n, F j = ∑ i : Fin n, F ((i : ℕ) + 1) := by
  have h : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [h, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel, ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun i _ => by rw [add_comm]

/-- `∑ᵢ (i + 1) mᵢ = n` for the multiplicities of a partition of `n`. -/
theorem sum_multiplicities {n : ℕ} (p : Nat.Partition n) :
    ∑ i : Fin n, ((i : ℕ) + 1) * multiplicities p i = n := by
  have hlt : ∀ j ∈ p.parts, j < n + 1 := fun j hj =>
    Nat.lt_succ_of_le (p.parts_sum ▸ Multiset.le_sum_of_mem hj)
  have h := sum_eq_sum_range_count hlt
  rw [p.parts_sum, Finset.sum_range_succ', zero_mul, add_zero, ← Fin.sum_univ_eq_sum_range] at h
  exact h.symm

theorem card_parts_eq_sum_multiplicities {n : ℕ} (p : Nat.Partition n) :
    Multiset.card p.parts = ∑ i : Fin n, multiplicities p i := by
  rw [← Multiset.toFinset_sum_count_eq]
  simp only [multiplicities]
  rw [← sum_Icc_one_eq_sum_fin fun j => p.parts.count j]
  refine Finset.sum_subset (partition_toFinset_subset_Icc p) fun j _ hj => ?_
  exact Multiset.count_eq_zero.mpr fun h => hj (Multiset.mem_toFinset.mpr h)

theorem count_sum_replicate {n : ℕ} (m : Fin n → ℕ) (i : Fin n) :
    (∑ j : Fin n, Multiset.replicate (m j) ((j : ℕ) + 1)).count ((i : ℕ) + 1) = m i := by
  rw [Multiset.count_sum']
  simp only [Multiset.count_replicate]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [ite_eq_right_iff]
    intro h
    exact absurd (Fin.ext (by omega)) hj
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem count_sum_replicate_of_notMem {n : ℕ} (m : Fin n → ℕ) {k : ℕ} (hk : k ∉ Finset.Icc 1 n) :
    (∑ j : Fin n, Multiset.replicate (m j) ((j : ℕ) + 1)).count k = 0 := by
  rw [Multiset.count_sum']
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Multiset.count_replicate, ite_eq_right_iff]
  intro h
  exact absurd (Finset.mem_Icc.mpr ⟨by omega, by have := j.isLt; omega⟩) hk

/-- The partition of `n` with multiplicity vector `m`. -/
def partitionOfMultiplicities {n : ℕ} (m : Fin n → ℕ) (hm : m ∈ multiplicityVectors n) :
    Nat.Partition n where
  parts := ∑ j : Fin n, Multiset.replicate (m j) ((j : ℕ) + 1)
  parts_pos := by
    intro i hi
    rw [Multiset.mem_sum] at hi
    obtain ⟨j, -, hj⟩ := hi
    rw [Multiset.eq_of_mem_replicate hj]
    exact Nat.succ_pos _
  parts_sum := by
    rw [Multiset.sum_sum]
    simp only [Multiset.sum_replicate, smul_eq_mul]
    have := (Finset.mem_filter.mp hm).2
    calc ∑ j : Fin n, m j * ((j : ℕ) + 1) = ∑ j : Fin n, ((j : ℕ) + 1) * m j :=
          Finset.sum_congr rfl fun j _ => mul_comm _ _
      _ = n := this

/-- **DLMF 1.4.13**, summed literally over the tuples `(m₁, …, mₙ)` with
`m₁ + 2m₂ + ⋯ + nmₙ = n` (`multiplicityVectors n`), with `k = m₁ + ⋯ + mₙ`; the bijection with
partitions is `multiplicities`/`partitionOfMultiplicities`. -/
theorem dlmf_1_4_13_tuples {f g : ℝ → ℝ} {x : ℝ} {n : ℕ} (hf : ContDiffAt ℝ n f (g x))
    (hg : ContDiffAt ℝ n g x) :
    iteratedDeriv n (fun y => f (g y)) x = ∑ m ∈ multiplicityVectors n,
      ((n.factorial : ℝ) / ∏ i : Fin n, ((m i).factorial : ℝ)) *
        iteratedDeriv (∑ i, m i) f (g x) *
        ∏ i : Fin n, (iteratedDeriv ((i : ℕ) + 1) g x / (((i : ℕ) + 1).factorial : ℝ)) ^ m i := by
  rw [dlmf_1_4_13 hf hg]
  refine Finset.sum_bij' (fun p _ => multiplicities p) (fun m hm => partitionOfMultiplicities m hm)
    ?_ ?_ ?_ ?_ ?_
  · intro p _
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun i => ?_, sum_multiplicities p⟩
    rw [Finset.mem_range]
    have h1 := sum_multiplicities p
    have h2 : ((i : ℕ) + 1) * multiplicities p i ≤
        ∑ i : Fin n, ((i : ℕ) + 1) * multiplicities p i :=
      Finset.single_le_sum (f := fun i : Fin n => ((i : ℕ) + 1) * multiplicities p i)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [h1] at h2
    nlinarith
  · intro m _
    exact Finset.mem_univ _
  · intro p _
    refine Nat.Partition.ext ?_
    simp only [partitionOfMultiplicities]
    ext k
    by_cases hk : k ∈ Finset.Icc 1 n
    · obtain ⟨i, rfl⟩ : ∃ i : Fin n, (i : ℕ) + 1 = k :=
        ⟨⟨k - 1, by have := Finset.mem_Icc.mp hk; omega⟩,
          by have := Finset.mem_Icc.mp hk; simp; omega⟩
      rw [count_sum_replicate]
      rfl
    · rw [count_sum_replicate_of_notMem _ hk]
      exact (Multiset.count_eq_zero.mpr fun h =>
        hk (partition_toFinset_subset_Icc p (Multiset.mem_toFinset.mpr h))).symm
  · intro m _
    funext i
    exact count_sum_replicate m i
  · intro p _
    rw [prod_Icc_one_eq_prod_fin, prod_Icc_one_eq_prod_fin, card_parts_eq_sum_multiplicities]
    rfl

/-- **DLMF 1.4.13**, Faà di Bruno's formula in Mathlib's form: the sum over the ordered
partitions `c` of `{0, …, n − 1}` of `f⁽ᵏ⁾(g(x)) ∏ⱼ g⁽|cⱼ|⁾(x)` with `k` the number of blocks
(`iteratedDeriv_comp_eq_sum_orderedFinpartition`). -/
theorem dlmf_1_4_13_partitions {f g : ℝ → ℝ} {x : ℝ} {n : ℕ} (hf : ContDiffAt ℝ n f (g x))
    (hg : ContDiffAt ℝ n g x) :
    iteratedDeriv n (fun y => f (g y)) x =
      ∑ c : OrderedFinpartition n,
        iteratedDeriv c.length f (g x) * ∏ j, iteratedDeriv (c.partSize j) g x :=
  iteratedDeriv_comp_eq_sum_orderedFinpartition hf hg le_rfl

/-- **DLMF 1.4.13** for `n = 2`: `(f ∘ g)⁽²⁾ = f⁽²⁾(g) g'² + f'(g) g⁽²⁾` (the terms `m = (2, 0)` and
`m = (0, 1)`; `iteratedDeriv_comp_two`). -/
theorem dlmf_1_4_13_two {f g : ℝ → ℝ} {x : ℝ} (hf : ContDiffAt ℝ 2 f (g x))
    (hg : ContDiffAt ℝ 2 g x) :
    iteratedDeriv 2 (fun y => f (g y)) x =
      iteratedDeriv 2 f (g x) * deriv g x ^ 2 + deriv f (g x) * iteratedDeriv 2 g x :=
  iteratedDeriv_comp_two hf hg

/-- **DLMF 1.4.13** for `n = 3`: `(f ∘ g)⁽³⁾ = f⁽³⁾(g) g'³ + 3 f⁽²⁾(g) g⁽²⁾ g' + f'(g) g⁽³⁾`
(`iteratedDeriv_comp_three`). -/
theorem dlmf_1_4_13_three {f g : ℝ → ℝ} {x : ℝ} (hf : ContDiffAt ℝ 3 f (g x))
    (hg : ContDiffAt ℝ 3 g x) :
    iteratedDeriv 3 (fun y => f (g y)) x =
      iteratedDeriv 3 f (g x) * deriv g x ^ 3 +
        3 * iteratedDeriv 2 f (g x) * iteratedDeriv 2 g x * deriv g x +
        deriv f (g x) * iteratedDeriv 3 g x :=
  iteratedDeriv_comp_three hf hg

/-- **DLMF 1.4.14–1.4.15**, L'Hôpital's rule (the `0/0` case): if `f(x), g(x) → 0` as `x → a`,
`g'(x) ≠ 0` near `a` (`x ≠ a`), and `f'(x)/g'(x)` has a limit, then `f(x)/g(x)` has the same limit
(`deriv.lhopital_zero_nhdsNE`). -/
theorem dlmf_1_4_15 {f g : ℝ → ℝ} {a : ℝ} {l : Filter ℝ}
    (hdf : ∀ᶠ x in 𝓝[≠] a, DifferentiableAt ℝ f x) (hg' : ∀ᶠ x in 𝓝[≠] a, deriv g x ≠ 0)
    (hfa : Tendsto f (𝓝[≠] a) (𝓝 0)) (hga : Tendsto g (𝓝[≠] a) (𝓝 0))
    (hdiv : Tendsto (fun x => deriv f x / deriv g x) (𝓝[≠] a) l) :
    Tendsto (fun x => f x / g x) (𝓝[≠] a) l :=
  deriv.lhopital_zero_nhdsNE hdf hg' hfa hga hdiv

/-- The algebra behind the `∞/∞` rule: with `Q = (f(x) − f(y))/(g(x) − g(y))`,
`f(x)/g(x) − L = (Q − L) + (f(y) − Q g(y))/g(x)`, so `|f(x)/g(x) − L| < ε` once `|Q − L| < ε/2` and
`g(x) > 2K/ε` with `K = |f(y)| + (|L| + ε/2)|g(y)|`. -/
theorem lhopital_atTop_estimate {fx fy gx gy L ε : ℝ} (hε : 0 < ε) (hgxy : gx - gy ≠ 0)
    (hQ : |(fx - fy) / (gx - gy) - L| < ε / 2)
    (hgx : 2 * (|fy| + (|L| + ε / 2) * |gy|) / ε < gx) :
    |fx / gx - L| < ε := by
  set Q := (fx - fy) / (gx - gy) with hQdef
  set K := |fy| + (|L| + ε / 2) * |gy| with hK
  have hK0 : 0 ≤ K := by positivity
  have hgx0 : 0 < gx := lt_of_le_of_lt (by positivity) hgx
  have hfx : fx = Q * (gx - gy) + fy := by rw [hQdef, div_mul_cancel₀ _ hgxy]; ring
  have hsplit : fx / gx - L = (Q - L) + (fy - Q * gy) / gx := by
    rw [hfx]; field_simp; ring
  have hQabs : |Q| ≤ |L| + ε / 2 := by
    have := abs_sub_abs_le_abs_sub Q L
    linarith
  have hnum : |fy - Q * gy| ≤ K := by
    calc |fy - Q * gy| ≤ |fy| + |Q * gy| := abs_sub _ _
      _ = |fy| + |Q| * |gy| := by rw [abs_mul]
      _ ≤ K := by rw [hK]; gcongr
  have htail : |(fy - Q * gy) / gx| < ε / 2 := by
    rw [abs_div, abs_of_pos hgx0, div_lt_iff₀ hgx0]
    have : 2 * K < ε * gx := by rw [div_lt_iff₀ hε] at hgx; linarith
    linarith
  rw [hsplit]
  calc |(Q - L) + (fy - Q * gy) / gx| ≤ |Q - L| + |(fy - Q * gy) / gx| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hQ htail
    _ = ε := add_halves ε

/-- L'Hôpital's rule, the `∞/∞` case, approaching `a` from the right: if `g → ∞`, `g' ≠ 0` and
`f'/g' → L` on `(a, b)`, then `f/g → L` (Cauchy's mean value theorem on `[x, y]`). -/
theorem lhopital_atTop_right_on_Ioo {f f' g g' : ℝ → ℝ} {a b L : ℝ} (hab : a < b)
    (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) (hgg' : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Ioo a b, g' x ≠ 0) (hga : Tendsto g (𝓝[>] a) atTop)
    (hdiv : Tendsto (fun x => f' x / g' x) (𝓝[>] a) (𝓝 L)) :
    Tendsto (fun x => f x / g x) (𝓝[>] a) (𝓝 L) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    (Metric.tendsto_nhds.mp hdiv (ε / 2) (half_pos hε))
  set c := min u b with hc
  have hac : a < c := lt_min hu hab
  set y := (a + c) / 2 with hy
  have hay : a < y := by rw [hy]; linarith
  have hyc : y < c := by rw [hy]; linarith
  have hyb : y < b := lt_of_lt_of_le hyc (min_le_right _ _)
  -- the Cauchy mean value theorem on `[x, y]`
  have key : ∀ x ∈ Ioo a y, g x - g y ≠ 0 ∧ |(f x - f y) / (g x - g y) - L| < ε / 2 := by
    intro x hx
    have hsubI : Icc x y ⊆ Ioo a b := fun z hz =>
      ⟨lt_of_lt_of_le hx.1 hz.1, lt_of_le_of_lt hz.2 hyb⟩
    have hsubO : Ioo x y ⊆ Ioo a b := Ioo_subset_Icc_self.trans hsubI
    have hfc : ContinuousOn f (Icc x y) := fun z hz =>
      (hff' z (hsubI hz)).continuousAt.continuousWithinAt
    have hgc : ContinuousOn g (Icc x y) := fun z hz =>
      (hgg' z (hsubI hz)).continuousAt.continuousWithinAt
    obtain ⟨z₁, hz₁, hgz⟩ := exists_hasDerivAt_eq_slope g g' hx.2 hgc
      fun z hz => hgg' z (hsubO hz)
    have hne : g x - g y ≠ 0 := by
      intro h0
      have : g y - g x = 0 := by linarith
      rw [this, zero_div] at hgz
      exact hg' z₁ (hsubO hz₁) hgz
    obtain ⟨z, hz, hcm⟩ := exists_ratio_hasDerivAt_eq_ratio_slope f f' hx.2 hfc
      (fun z hz => hff' z (hsubO hz)) g g' hgc fun z hz => hgg' z (hsubO hz)
    have hgz0 := hg' z (hsubO hz)
    have hQ : (f x - f y) / (g x - g y) = f' z / g' z := by
      rw [div_eq_div_iff hne hgz0]
      linarith
    have hzu : z ∈ Ioo a u := ⟨lt_trans hx.1 hz.1, lt_of_lt_of_le (lt_trans hz.2 hyc)
      (min_le_left _ _)⟩
    refine ⟨hne, ?_⟩
    rw [hQ, ← Real.dist_eq]
    exact hsub hzu
  filter_upwards [Ioo_mem_nhdsGT hay,
    hga.eventually_gt_atTop (2 * (|f y| + (|L| + ε / 2) * |g y|) / ε)] with x hx hgx
  obtain ⟨hne, hQ⟩ := key x hx
  rw [Real.dist_eq]
  exact lhopital_atTop_estimate hε hne hQ hgx

/-- L'Hôpital's rule, the `∞/∞` case, approaching `b` from the left (reflection `x ↦ −x` of
`lhopital_atTop_right_on_Ioo`). -/
theorem lhopital_atTop_left_on_Ioo {f f' g g' : ℝ → ℝ} {a b L : ℝ} (hab : a < b)
    (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) (hgg' : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Ioo a b, g' x ≠ 0) (hgb : Tendsto g (𝓝[<] b) atTop)
    (hdiv : Tendsto (fun x => f' x / g' x) (𝓝[<] b) (𝓝 L)) :
    Tendsto (fun x => f x / g x) (𝓝[<] b) (𝓝 L) := by
  have hdnf : ∀ x ∈ -Ioo a b, HasDerivAt (f ∘ Neg.neg) (f' (-x) * -1) x := fun x hx =>
    (hff' (-x) hx).comp x (hasDerivAt_neg x)
  have hdng : ∀ x ∈ -Ioo a b, HasDerivAt (g ∘ Neg.neg) (g' (-x) * -1) x := fun x hx =>
    (hgg' (-x) hx).comp x (hasDerivAt_neg x)
  rw [neg_Ioo] at hdnf hdng
  have := lhopital_atTop_right_on_Ioo (neg_lt_neg hab) hdnf hdng
    (fun x hx => mul_ne_zero (hg' (-x) ⟨by linarith [hx.2], by linarith [hx.1]⟩) (by norm_num))
    (hgb.comp tendsto_neg_nhdsGT_neg)
    (by
      simp only [neg_div_neg_eq, mul_one, mul_neg]
      exact hdiv.comp tendsto_neg_nhdsGT_neg)
  have := this.comp tendsto_neg_nhdsLT
  unfold Function.comp at this
  simpa only [neg_neg] using this

/-- **DLMF 1.4.14–1.4.15**, L'Hôpital's rule (the `∞/∞` case): if `g(x) → ∞` as `x → a`,
`g'(x) ≠ 0` near `a` (`x ≠ a`), `f` is differentiable near `a`, and `f'(x)/g'(x) → L`, then
`f(x)/g(x) → L`.  (Mathlib has only the `0/0` case; the behaviour of `f` is not needed.) -/
theorem dlmf_1_4_15_atTop {f g : ℝ → ℝ} {a L : ℝ}
    (hdf : ∀ᶠ x in 𝓝[≠] a, DifferentiableAt ℝ f x) (hg' : ∀ᶠ x in 𝓝[≠] a, deriv g x ≠ 0)
    (hga : Tendsto g (𝓝[≠] a) atTop)
    (hdiv : Tendsto (fun x => deriv f x / deriv g x) (𝓝[≠] a) (𝓝 L)) :
    Tendsto (fun x => f x / g x) (𝓝[≠] a) (𝓝 L) := by
  simp only [← Iio_union_Ioi, nhdsWithin_union, tendsto_sup, eventually_sup] at *
  have hdg : ∀ x, deriv g x ≠ 0 → DifferentiableAt ℝ g x := fun x hx =>
    differentiableAt_of_deriv_ne_zero hx
  constructor
  · obtain ⟨l, hl, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp (hdf.1.and hg'.1)
    exact lhopital_atTop_left_on_Ioo hl (fun x hx => (hsub hx).1.hasDerivAt)
      (fun x hx => (hdg x (hsub hx).2).hasDerivAt) (fun x hx => (hsub hx).2) hga.1 hdiv.1
  · obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hdf.2.and hg'.2)
    exact lhopital_atTop_right_on_Ioo hu (fun x hx => (hsub hx).1.hasDerivAt)
      (fun x hx => (hdg x (hsub hx).2).hasDerivAt) (fun x hx => (hsub hx).2) hga.2 hdiv.2

end Derivatives


/-! ### §1.4(iv) Indefinite integrals -/

/-- **DLMF §1.4(iv)**: `F` is an indefinite integral (antiderivative) of `f` on `I` if
`F'(x) = f(x)` there. -/
def IsAntiderivOn (F f : ℝ → ℝ) (I : Set ℝ) : Prop := ∀ x ∈ I, HasDerivAt F (f x) x

/-- **DLMF §1.4(iv)**: if `F' = f`, then `F + C` is again an indefinite integral of `f`. -/
theorem IsAntiderivOn.add_const {F f : ℝ → ℝ} {I : Set ℝ} (h : IsAntiderivOn F f I) (C : ℝ) :
    IsAntiderivOn (fun x => F x + C) f I := fun x hx => (h x hx).add_const C

/-- **DLMF §1.4(iv)**: `∫ f dx = F(x) + C`: on an open interval (more generally an open
preconnected set), every indefinite integral of `f` is `F + C` for a constant `C`
(`IsOpen.is_const_of_deriv_eq_zero`). -/
theorem dlmf_1_4_iv_antideriv {F G f : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I)
    (hI' : IsPreconnected I) (hF : IsAntiderivOn F f I) (hG : IsAntiderivOn G f I) :
    ∃ C, ∀ x ∈ I, G x = F x + C := by
  rcases I.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact ⟨0, fun x hx => absurd hx (Set.notMem_empty x)⟩
  have hd : ∀ x ∈ I, HasDerivAt (fun x => G x - F x) 0 x := fun x hx => by
    have := (hG x hx).sub (hF x hx)
    rwa [sub_self] at this
  refine ⟨G x₀ - F x₀, fun x hx => ?_⟩
  have := hI.is_const_of_deriv_eq_zero (f := fun x => G x - F x) hI'
    (fun y hy => (hd y hy).differentiableAt.differentiableWithinAt)
    (fun y hy => (hd y hy).deriv) hx hx₀
  linarith

/-- **DLMF 1.4.16**, integration by parts: if `F' = f` and `H' = F g'`, then `F g − H` is an
indefinite integral of `f g`: `∫ f g = (∫ f) g − ∫ (∫ f) g'`. -/
theorem dlmf_1_4_16 {F f g g' H : ℝ → ℝ} {I : Set ℝ} (hF : IsAntiderivOn F f I)
    (hg : ∀ x ∈ I, HasDerivAt g (g' x) x) (hH : IsAntiderivOn H (fun x => F x * g' x) I) :
    IsAntiderivOn (fun x => F x * g x - H x) (fun x => f x * g x) I := fun x hx => by
  have := ((hF x hx).mul (hg x hx)).sub (hH x hx)
  convert this using 1
  ring

/-- **DLMF 1.4.16**, definite form (`intervalIntegral.integral_mul_deriv_eq_deriv_mul`):
`∫_a^b F g' = F(b) g(b) − F(a) g(a) − ∫_a^b f g` for `F' = f`. -/
theorem dlmf_1_4_16_definite {F f g g' : ℝ → ℝ} {a b : ℝ}
    (hF : ∀ x ∈ uIcc a b, HasDerivAt F (f x) x) (hg : ∀ x ∈ uIcc a b, HasDerivAt g (g' x) x)
    (hf : IntervalIntegrable f MeasureTheory.volume a b)
    (hg' : IntervalIntegrable g' MeasureTheory.volume a b) :
    ∫ x in a..b, f x * g x = F b * g b - F a * g a - ∫ x in a..b, F x * g' x := by
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul hF hg hf hg']
  ring

/-- **DLMF 1.4.17**, `n ≠ −1`: `∫ xⁿ dx = xⁿ⁺¹/(n + 1) + C` for integer `n` (at `x ≠ 0` when
`n < 0`; `hasDerivAt_zpow`). -/
theorem dlmf_1_4_17 {n : ℤ} (hn : n ≠ -1) {x : ℝ} (hx : x ≠ 0 ∨ 0 ≤ n) :
    HasDerivAt (fun x : ℝ => x ^ (n + 1) / (n + 1)) (x ^ n) x := by
  have hn' : ((n : ℝ) + 1) ≠ 0 := by
    intro h
    apply hn
    exact_mod_cast (eq_neg_of_add_eq_zero_left h)
  have := (hasDerivAt_zpow (n + 1) x (hx.imp_right fun h => by omega)).div_const ((n : ℝ) + 1)
  convert this using 1
  push_cast
  rw [add_sub_cancel_right]
  field_simp

/-- **DLMF 1.4.17**, `n = −1`: `∫ x⁻¹ dx = ln|x| + C` (`Real.hasDerivAt_log`, `Real.log_abs`). -/
theorem dlmf_1_4_17_neg_one {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun x : ℝ => Real.log |x|) (x ^ (-1 : ℤ)) x := by
  simp only [Real.log_abs, zpow_neg_one]
  exact Real.hasDerivAt_log hx

/-- **DLMF 1.4.17** for real exponents `n ≠ −1` at `x > 0` (`Real.hasDerivAt_rpow_const`). -/
theorem dlmf_1_4_17_rpow {n x : ℝ} (hn : n ≠ -1) (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => x ^ (n + 1) / (n + 1)) (x ^ n) x := by
  have hn' : n + 1 ≠ 0 := fun h => hn (eq_neg_of_add_eq_zero_left h)
  have := (Real.hasDerivAt_rpow_const (p := n + 1) (Or.inl hx.ne')).div_const (n + 1)
  convert this using 1
  rw [add_sub_cancel_right]
  field_simp

/-! ### §1.4(v) Definite integrals

Mathlib's integral `∫ x in a..b, f x` is the Lebesgue integral; the DLMF's Riemann integral is the
limit 1.4.18 of Riemann sums over tagged partitions (`TaggedPartition`, `HasRiemannIntegral`),
proven here to exist and agree with Mathlib's integral for bounded functions continuous off a
finite set, in particular for continuous and for piecewise continuous functions. -/

section DefiniteIntegrals

open MeasureTheory Finset

/-! #### Riemann integrals -/

/-- **DLMF §1.4(v)**: a tagged partition `a = x₀ < x₁ < ⋯ < xₙ = b` of `[a, b]` with points
`ξⱼ ∈ [xⱼ, xⱼ₊₁]`, `j = 0, 1, …, n − 1`. -/
structure TaggedPartition (a b : ℝ) where
  /-- The number of subintervals. -/
  n : ℕ
  /-- The division points `x₀, …, xₙ`. -/
  x : ℕ → ℝ
  /-- The tags `ξ₀, …, ξₙ₋₁`. -/
  ξ : ℕ → ℝ
  lt : ∀ j < n, x j < x (j + 1)
  first : x 0 = a
  last : x n = b
  tag : ∀ j < n, ξ j ∈ Icc (x j) (x (j + 1))

namespace TaggedPartition

variable {a b : ℝ} (P : TaggedPartition a b)

/-- The Riemann sum `∑ⱼ f(ξⱼ)(xⱼ₊₁ − xⱼ)`. -/
def riemannSum (f : ℝ → ℝ) : ℝ := ∑ j ∈ range P.n, f (P.ξ j) * (P.x (j + 1) - P.x j)

theorem le_of_le : ∀ {i j : ℕ}, i ≤ j → j ≤ P.n → P.x i ≤ P.x j := by
  intro i j hij hjn
  induction j with
  | zero => rw [Nat.le_zero.mp hij]
  | succ j ih =>
    rcases Nat.of_le_succ hij with h | h
    · exact (ih h (by omega)).trans (P.lt j (by omega)).le
    · rw [h]

theorem mem_Icc {j : ℕ} (hj : j ≤ P.n) : P.x j ∈ Icc a b := by
  refine ⟨?_, ?_⟩
  · calc a = P.x 0 := P.first.symm
      _ ≤ P.x j := P.le_of_le (Nat.zero_le j) hj
  · calc P.x j ≤ P.x P.n := P.le_of_le hj le_rfl
      _ = b := P.last

theorem a_le_b {a b : ℝ} (P : TaggedPartition a b) : a ≤ b :=
  (P.mem_Icc (j := 0) (Nat.zero_le _)).1.trans (P.mem_Icc (j := 0) (Nat.zero_le _)).2

theorem sum_lengths : ∑ j ∈ range P.n, (P.x (j + 1) - P.x j) = b - a := by
  rw [Finset.sum_range_sub, P.first, P.last]

/-- Disjoint subintervals inside `[c, d]` have total length at most `d − c`. -/
theorem sum_lengths_le {T : Finset ℕ} (hT : T ⊆ range P.n) {c d : ℝ} (hcd : c ≤ d)
    (hsub : ∀ j ∈ T, Icc (P.x j) (P.x (j + 1)) ⊆ Icc c d) :
    ∑ j ∈ T, (P.x (j + 1) - P.x j) ≤ d - c := by
  have hdisj : (T : Set ℕ).PairwiseDisjoint fun j => Ioo (P.x j) (P.x (j + 1)) := by
    intro i hi j hj hij
    rcases lt_or_gt_of_ne hij with h | h
    · have hi' := mem_range.mp (hT hi)
      have hj' := mem_range.mp (hT hj)
      have : P.x (i + 1) ≤ P.x j := P.le_of_le h (by omega)
      exact Set.disjoint_left.mpr fun t ht1 ht2 => by linarith [ht1.2, ht2.1]
    · have hi' := mem_range.mp (hT hi)
      have hj' := mem_range.mp (hT hj)
      have : P.x (j + 1) ≤ P.x i := P.le_of_le h (by omega)
      exact Set.disjoint_left.mpr fun t ht1 ht2 => by linarith [ht1.1, ht2.2]
  have hmeas := measure_biUnion_finset (μ := volume) hdisj fun j _ => measurableSet_Ioo
  have hle : volume (⋃ j ∈ T, Ioo (P.x j) (P.x (j + 1))) ≤ volume (Icc c d) :=
    measure_mono (Set.iUnion₂_subset fun j hj => Ioo_subset_Icc_self.trans (hsub j hj))
  rw [hmeas, Real.volume_Icc] at hle
  simp only [Real.volume_Ioo] at hle
  have hnn : ∀ j ∈ T, 0 ≤ P.x (j + 1) - P.x j := fun j hj =>
    sub_nonneg.mpr (P.lt j (mem_range.mp (hT hj))).le
  rw [← ENNReal.ofReal_sum_of_nonneg hnn, ENNReal.ofReal_le_ofReal_iff (by linarith)] at hle
  exact hle

end TaggedPartition

open TaggedPartition

/-- **DLMF 1.4.18**: `I` is the limit of the Riemann sums `∑ f(ξⱼ)(xⱼ₊₁ − xⱼ)` as
`max (xⱼ₊₁ − xⱼ) → 0`. -/
def HasRiemannIntegral (f : ℝ → ℝ) (a b I : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ P : TaggedPartition a b, (∀ j < P.n, P.x (j + 1) - P.x j < δ) →
    |P.riemannSum f - I| < ε

/-- **DLMF §1.4(v)**: `f` is Riemann integrable on `[a, b]` if the limit 1.4.18 exists. -/
def RiemannIntegrable (f : ℝ → ℝ) (a b : ℝ) : Prop := ∃ I, HasRiemannIntegral f a b I

/-- The Riemann sum minus the integral, interval by interval. -/
theorem riemannSum_sub_integral {f : ℝ → ℝ} {a b : ℝ} (P : TaggedPartition a b)
    (hf : IntervalIntegrable f volume a b) :
    P.riemannSum f - ∫ x in a..b, f x =
      ∑ j ∈ range P.n, ∫ t in P.x j..P.x (j + 1), (f (P.ξ j) - f t) := by
  have hab : a ≤ b := P.a_le_b
  have hint : ∀ j < P.n, IntervalIntegrable f volume (P.x j) (P.x (j + 1)) := fun j hj =>
    hf.mono_set (by
      rw [uIcc_of_le hab, uIcc_of_le (P.lt j hj).le]
      exact Icc_subset_Icc (P.mem_Icc hj.le).1 (P.mem_Icc hj).2)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  rw [P.first, P.last] at hsum
  rw [← hsum, TaggedPartition.riemannSum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [intervalIntegral.integral_sub intervalIntegrable_const (hint j (mem_range.mp hj)),
    intervalIntegral.integral_const, smul_eq_mul, mul_comm]

/-- One term of the error: if `|f(ξ) − f(t)| ≤ C` on `[xⱼ, xⱼ₊₁]`, the term is at most
`C (xⱼ₊₁ − xⱼ)` (`intervalIntegral.norm_integral_le_of_norm_le_const`). -/
theorem abs_error_term_le {f : ℝ → ℝ} {u v ξ C : ℝ} (huv : u ≤ v)
    (h : ∀ t ∈ Icc u v, |f ξ - f t| ≤ C) :
    |∫ t in u..v, (f ξ - f t)| ≤ C * (v - u) := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := u) (b := v)
    (f := fun t => f ξ - f t) (C := C) fun t ht => by
      rw [uIoc_of_le huv] at ht
      exact h t (Ioc_subset_Icc_self ht)
  rwa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr huv)] at this

/-- A sum over a union of finsets is at most the sum of the sums, for nonnegative terms. -/
theorem sum_biUnion_le_of_nonneg {S : Finset ℝ} {T : ℝ → Finset ℕ} {g : ℕ → ℝ}
    (hg : ∀ j ∈ S.biUnion T, 0 ≤ g j) : ∑ j ∈ S.biUnion T, g j ≤ ∑ s ∈ S, ∑ j ∈ T s, g j := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.biUnion_insert] at hg ⊢
    rw [Finset.sum_insert ha]
    have ih' := ih fun j hj => hg j (Finset.mem_union_right _ hj)
    calc ∑ j ∈ T a ∪ S.biUnion T, g j
        ≤ ∑ j ∈ T a ∪ S.biUnion T, g j + ∑ j ∈ T a ∩ S.biUnion T, g j :=
          le_add_of_nonneg_right (Finset.sum_nonneg fun j hj =>
            hg j (Finset.mem_union_left _ (Finset.mem_inter.mp hj).1))
      _ = ∑ j ∈ T a, g j + ∑ j ∈ S.biUnion T, g j := Finset.sum_union_inter
      _ ≤ ∑ j ∈ T a, g j + ∑ s ∈ S, ∑ j ∈ T s, g j := by gcongr

/-- **Riemann integrability of bounded functions continuous off a finite set**: if `|f| ≤ M` on
`[a, b]` and `f` is continuous on `[a, b]` except at the points of a finite set `S`, the Riemann
sums converge to the integral.  Away from `η`-windows around `S`, `f` is uniformly continuous; the
subintervals meeting a window lie in a `2η`-window and have total length at most `4η` per point. -/
theorem hasRiemannIntegral_of_bounded {f : ℝ → ℝ} {a b M : ℝ} {S : Finset ℝ} (hab : a ≤ b)
    (hM : ∀ x ∈ Icc a b, |f x| ≤ M)
    (hcont : ∀ x ∈ Icc a b, x ∉ S → ContinuousWithinAt f (Icc a b) x)
    (hf : IntervalIntegrable f volume a b) :
    HasRiemannIntegral f a b (∫ x in a..b, f x) := by
  classical
  intro ε hε
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM a ⟨le_rfl, hab⟩)
  set k : ℝ := (S.card : ℝ) with hk
  have hk0 : 0 ≤ k := Nat.cast_nonneg _
  set η := ε / (16 * (M + 1) * (k + 1)) with hη
  have hη0 : 0 < η := by positivity
  set K := Icc a b \ ⋃ s ∈ S, Ioo (s - η) (s + η) with hK
  have hKc : IsCompact K :=
    isCompact_Icc.diff (isOpen_biUnion fun s _ => isOpen_Ioo)
  have hKcont : ContinuousOn f K := fun t ht =>
    (hcont t ht.1 fun hs => ht.2 (mem_iUnion₂.mpr ⟨t, hs, by constructor <;> linarith⟩)).mono
      sdiff_subset
  set ε' := ε / (2 * (b - a + 1)) with hε'
  have hε'0 : 0 < ε' := by
    have : 0 < b - a + 1 := by linarith
    positivity
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ :=
    Metric.uniformContinuousOn_iff.mp (hKc.uniformContinuousOn_of_continuous hKcont) ε' hε'0
  refine ⟨min δ₁ η, lt_min hδ₁ hη0, fun P hP => ?_⟩
  rw [riemannSum_sub_integral P hf]
  set Δ : ℕ → ℝ := fun j => P.x (j + 1) - P.x j with hΔ
  have hΔ0 : ∀ j ∈ range P.n, 0 ≤ Δ j := fun j hj =>
    sub_nonneg.mpr (P.lt j (mem_range.mp hj)).le
  set good : ℕ → Prop := fun j => Icc (P.x j) (P.x (j + 1)) ⊆ K with hgood
  -- the bound on each term
  have hterm : ∀ j ∈ range P.n, |∫ t in P.x j..P.x (j + 1), (f (P.ξ j) - f t)| ≤
      (if good j then ε' else 2 * M) * Δ j := by
    intro j hj
    have hjn := mem_range.mp hj
    have hlt := P.lt j hjn
    have htag := P.tag j hjn
    have hIcc : Icc (P.x j) (P.x (j + 1)) ⊆ Icc a b :=
      Icc_subset_Icc (P.mem_Icc hjn.le).1 (P.mem_Icc hjn).2
    refine abs_error_term_le hlt.le fun t ht => ?_
    split_ifs with hg
    · have h1 := hδ₁' (P.ξ j) (hg htag) t (hg ht)
      have hd : dist (P.ξ j) t < δ₁ := by
        rw [Real.dist_eq, abs_lt]
        have := hP j hjn
        have := min_le_left δ₁ η
        constructor <;> linarith [ht.1, ht.2, htag.1, htag.2]
      rw [Real.dist_eq] at h1
      exact (h1 hd).le
    · calc |f (P.ξ j) - f t| ≤ |f (P.ξ j)| + |f t| := abs_sub _ _
        _ ≤ M + M := add_le_add (hM _ (hIcc htag)) (hM _ (hIcc ht))
        _ = 2 * M := by ring
  -- the bad intervals lie in `2η`-windows around the points of `S`
  set T : ℝ → Finset ℕ := fun s => (range P.n).filter fun j =>
    Icc (P.x j) (P.x (j + 1)) ⊆ Icc (s - 2 * η) (s + 2 * η) with hT
  have hbad : (range P.n).filter (fun j => ¬ good j) ⊆ S.biUnion T := by
    intro j hj
    obtain ⟨hj, hng⟩ := Finset.mem_filter.mp hj
    have hjn := mem_range.mp hj
    obtain ⟨t, ht, htK⟩ := Set.not_subset.mp hng
    have htab : t ∈ Icc a b :=
      Icc_subset_Icc (P.mem_Icc hjn.le).1 (P.mem_Icc hjn).2 ht
    have : t ∈ ⋃ s ∈ S, Ioo (s - η) (s + η) := by
      by_contra hn
      exact htK ⟨htab, hn⟩
    obtain ⟨s, hs, hst⟩ := mem_iUnion₂.mp this
    have hδ := (hP j hjn).trans_le (min_le_right δ₁ η)
    refine Finset.mem_biUnion.mpr ⟨s, hs, Finset.mem_filter.mpr ⟨hj, ?_⟩⟩
    refine Icc_subset_Icc ?_ ?_ <;> linarith [ht.1, ht.2, hst.1, hst.2]
  have hT_le : ∀ s ∈ S, ∑ j ∈ T s, Δ j ≤ 4 * η := fun s _ => by
    have := P.sum_lengths_le (T := T s) (Finset.filter_subset _ _)
      (c := s - 2 * η) (d := s + 2 * η) (by linarith)
      fun j hj => (Finset.mem_filter.mp hj).2
    linarith
  have hbad_sum : ∑ j ∈ (range P.n).filter (fun j => ¬ good j), Δ j ≤ k * (4 * η) := by
    calc ∑ j ∈ (range P.n).filter (fun j => ¬ good j), Δ j
        ≤ ∑ j ∈ S.biUnion T, Δ j :=
          Finset.sum_le_sum_of_subset_of_nonneg hbad fun j hj _ => by
            obtain ⟨s, _, hjs⟩ := Finset.mem_biUnion.mp hj
            exact hΔ0 j (Finset.filter_subset _ _ hjs)
      _ ≤ ∑ s ∈ S, ∑ j ∈ T s, Δ j := sum_biUnion_le_of_nonneg fun j hj => by
          obtain ⟨s, _, hjs⟩ := Finset.mem_biUnion.mp hj
          exact hΔ0 j (Finset.filter_subset _ _ hjs)
      _ ≤ ∑ _s ∈ S, 4 * η := Finset.sum_le_sum hT_le
      _ = k * (4 * η) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hgood_sum : ∑ j ∈ (range P.n).filter (fun j => good j), Δ j ≤ b - a := by
    rw [← P.sum_lengths]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun j hj _ => hΔ0 j hj
  calc |∑ j ∈ range P.n, ∫ t in P.x j..P.x (j + 1), (f (P.ξ j) - f t)|
      ≤ ∑ j ∈ range P.n, |∫ t in P.x j..P.x (j + 1), (f (P.ξ j) - f t)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ range P.n, (if good j then ε' else 2 * M) * Δ j := Finset.sum_le_sum hterm
    _ = ε' * ∑ j ∈ (range P.n).filter (fun j => good j), Δ j +
        2 * M * ∑ j ∈ (range P.n).filter (fun j => ¬ good j), Δ j := by
        simp only [ite_mul]
        rw [Finset.sum_ite, Finset.mul_sum, Finset.mul_sum]
    _ ≤ ε' * (b - a) + 2 * M * (k * (4 * η)) := by
        gcongr
    _ < ε := by
        have h1 : ε' * (b - a) < ε / 2 := by
          rw [hε', div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
          nlinarith
        have h2 : 2 * M * (k * (4 * η)) < ε / 2 := by
          have hden : 0 < 16 * (M + 1) * (k + 1) := by positivity
          have : 2 * M * (k * (4 * η)) = ε * (8 * M * k) / (16 * (M + 1) * (k + 1)) := by
            rw [hη]; field_simp; ring
          rw [this, div_lt_iff₀ hden]
          nlinarith [mul_nonneg hM0 hk0]
        linarith

/-- A bounded function continuous on `[a, b]` off a finite set is integrable there. -/
theorem intervalIntegrable_of_bounded {f : ℝ → ℝ} {a b M : ℝ} {S : Finset ℝ} (hab : a ≤ b)
    (hM : ∀ x ∈ Icc a b, |f x| ≤ M)
    (hcont : ∀ x ∈ Icc a b, x ∉ S → ContinuousWithinAt f (Icc a b) x) :
    IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  have hc : ContinuousOn f (Icc a b \ (S : Set ℝ)) := fun x hx =>
    (hcont x hx.1 hx.2).mono sdiff_subset
  have hmeas : AEStronglyMeasurable f (volume.restrict (Icc a b)) := by
    have := hc.aestronglyMeasurable (μ := volume)
      (measurableSet_Icc.diff S.finite_toSet.measurableSet)
    rwa [Measure.restrict_congr_set (sdiff_null_ae_eq_self (S.finite_toSet.measure_zero _))]
      at this
  exact IntegrableOn.of_bound measure_Icc_lt_top hmeas M
    (ae_restrict_of_forall_mem measurableSet_Icc fun x hx => by
      rw [Real.norm_eq_abs]; exact hM x hx)

/-- A piecewise continuous function is bounded on `[a, b]`: it is locally bounded (by continuity,
or by its one-sided limits at the simple discontinuities) and `[a, b]` is compact. -/
theorem IsPiecewiseContinuous.exists_bound {f : ℝ → ℝ} {a b : ℝ}
    (h : IsPiecewiseContinuous f (Icc a b)) : ∃ M, ∀ x ∈ Icc a b, |f x| ≤ M := by
  obtain ⟨S, hcont, hdisc⟩ := h
  have hloc : ∀ y ∈ Icc a b, ∃ C, ∀ᶠ z in 𝓝 y, z ∈ Icc a b → |f z| ≤ C := by
    intro y hy
    by_cases hyS : y ∈ S
    · obtain ⟨L, R, hR, hL, -⟩ := hdisc y hyS
      have h1 : ∀ᶠ z in 𝓝[>] y, |f z| ≤ |R| + 1 := by
        filter_upwards [(Metric.tendsto_nhds.mp hR) 1 one_pos] with z hz
        rw [Real.dist_eq] at hz
        have := abs_sub_abs_le_abs_sub (f z) R
        linarith
      have h2 : ∀ᶠ z in 𝓝[<] y, |f z| ≤ |L| + 1 := by
        filter_upwards [(Metric.tendsto_nhds.mp hL) 1 one_pos] with z hz
        rw [Real.dist_eq] at hz
        have := abs_sub_abs_le_abs_sub (f z) L
        linarith
      have h3 : ∀ᶠ z in 𝓝[≠] y, |f z| ≤ |L| + |R| + 1 := by
        rw [← nhdsLT_sup_nhdsGT, eventually_sup]
        exact ⟨h2.mono fun z hz => by linarith [abs_nonneg R],
          h1.mono fun z hz => by linarith [abs_nonneg L]⟩
      refine ⟨|L| + |R| + 1 + |f y|, ?_⟩
      filter_upwards [eventually_nhdsWithin_iff.mp h3] with z hz _
      by_cases hzy : z = y
      · rw [hzy]; linarith [abs_nonneg L, abs_nonneg R]
      · linarith [hz hzy, abs_nonneg (f y)]
    · have hc := hcont y hy hyS
      have h1 : ∀ᶠ z in 𝓝[Icc a b] y, |f z| ≤ |f y| + 1 := by
        filter_upwards [(Metric.tendsto_nhds.mp hc) 1 one_pos] with z hz
        rw [Real.dist_eq] at hz
        have := abs_sub_abs_le_abs_sub (f z) (f y)
        linarith
      exact ⟨|f y| + 1, eventually_nhdsWithin_iff.mp h1⟩
  choose C hC using hloc
  obtain ⟨t, ht⟩ := isCompact_Icc.elim_nhds_subcover'
    (fun y hy => {z | z ∈ Icc a b → |f z| ≤ C y hy}) fun y hy => hC y hy
  refine ⟨∑ y ∈ t, |C y.1 y.2|, fun x hx => ?_⟩
  obtain ⟨y, hyt, hxy⟩ := mem_iUnion₂.mp (ht hx)
  calc |f x| ≤ C y.1 y.2 := hxy hx
    _ ≤ |C y.1 y.2| := le_abs_self _
    _ ≤ ∑ y ∈ t, |C y.1 y.2| :=
        Finset.single_le_sum (f := fun y : Icc a b => |C y.1 y.2|) (fun _ _ => abs_nonneg _) hyt

/-- **DLMF 1.4.18**: a continuous function on `[a, b]` is Riemann integrable, and its integral is
the limit of the Riemann sums. -/
theorem dlmf_1_4_18 {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) :
    HasRiemannIntegral f a b (∫ x in a..b, f x) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  have hM' : ∀ x ∈ Icc a b, |f x| ≤ M := fun x hx => by rw [← Real.norm_eq_abs]; exact hM x hx
  have hcont : ∀ x ∈ Icc a b, x ∉ (∅ : Finset ℝ) → ContinuousWithinAt f (Icc a b) x :=
    fun x hx _ => hf x hx
  exact hasRiemannIntegral_of_bounded hab hM' hcont (intervalIntegrable_of_bounded hab hM' hcont)

/-- **DLMF §1.4(v)**: piecewise continuity of `f` on `[a, b]` is sufficient for the limit 1.4.18 to
exist. -/
theorem dlmf_1_4_v_piecewise {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : IsPiecewiseContinuous f (Icc a b)) :
    HasRiemannIntegral f a b (∫ x in a..b, f x) := by
  obtain ⟨M, hM⟩ := hf.exists_bound
  obtain ⟨S, hcont, -⟩ := hf
  exact hasRiemannIntegral_of_bounded hab hM hcont (intervalIntegrable_of_bounded hab hM hcont)

/-- The uniform partition of `[a, b]` into `n` equal parts, tagged at the left endpoints. -/
noncomputable def uniformPartition {a b : ℝ} (hab : a < b) (n : ℕ) (hn : 0 < n) :
    TaggedPartition a b where
  n := n
  x j := a + j * ((b - a) / n)
  ξ j := a + j * ((b - a) / n)
  lt j _ := by
    have : 0 < (b - a) / n := div_pos (by linarith) (Nat.cast_pos.mpr hn)
    push_cast
    nlinarith
  first := by simp
  last := by
    have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    field_simp
    ring
  tag j _ := by
    have : 0 < (b - a) / n := div_pos (by linarith) (Nat.cast_pos.mpr hn)
    refine ⟨le_rfl, ?_⟩
    push_cast
    nlinarith

/-- **DLMF §1.4(v)**: the limit 1.4.18 is unique (for `a < b`), so the Riemann integral is well
defined. -/
theorem HasRiemannIntegral.unique {f : ℝ → ℝ} {a b I J : ℝ} (hab : a < b)
    (hI : HasRiemannIntegral f a b I) (hJ : HasRiemannIntegral f a b J) : I = J := by
  refine eq_of_abs_sub_nonpos (le_of_forall_pos_lt_add fun ε hε => ?_)
  obtain ⟨δ, hδ, hδ'⟩ := hI (ε / 2) (half_pos hε)
  obtain ⟨δ', hδ'0, hδ''⟩ := hJ (ε / 2) (half_pos hε)
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / min δ δ')
  have hmin : 0 < min δ δ' := lt_min hδ hδ'0
  have hn0 : 0 < n := by
    have : 0 < (b - a) / min δ δ' := div_pos (by linarith) hmin
    exact_mod_cast this.trans hn
  set P := uniformPartition hab n hn0
  have hstep : ∀ j < P.n, P.x (j + 1) - P.x j < min δ δ' := fun j _ => by
    simp only [P, uniformPartition]
    push_cast
    have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
    rw [show a + ((j : ℝ) + 1) * ((b - a) / n) - (a + j * ((b - a) / n)) = (b - a) / n by ring,
      div_lt_iff₀ hn']
    rw [div_lt_iff₀ hmin] at hn
    linarith
  have h1 := hδ' P fun j hj => (hstep j hj).trans_le (min_le_left _ _)
  have h2 := hδ'' P fun j hj => (hstep j hj).trans_le (min_le_right _ _)
  calc |I - J| ≤ |P.riemannSum f - I| + |P.riemannSum f - J| := by
        rw [abs_sub_comm (P.riemannSum f) I]
        exact abs_sub_le I (P.riemannSum f) J
    _ < ε / 2 + ε / 2 := add_lt_add h1 h2
    _ = 0 + ε := by ring

/-- **DLMF 1.4.19**: `∫(cf + dg) = c∫f + d∫g` for constants `c, d` (`intervalIntegral.integral_add`,
`intervalIntegral.integral_const_mul`). -/
theorem dlmf_1_4_19 {f g : ℝ → ℝ} {a b : ℝ} (c d : ℝ) (hf : IntervalIntegrable f volume a b)
    (hg : IntervalIntegrable g volume a b) :
    ∫ x in a..b, (c * f x + d * g x) = c * (∫ x in a..b, f x) + d * ∫ x in a..b, g x := by
  rw [intervalIntegral.integral_add (hf.const_mul c) (hg.const_mul d),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

/-- **DLMF 1.4.19** for the Riemann sums: the limits 1.4.18 are linear. -/
theorem HasRiemannIntegral.linear {f g : ℝ → ℝ} {a b I J : ℝ} (c d : ℝ)
    (hf : HasRiemannIntegral f a b I) (hg : HasRiemannIntegral g a b J) :
    HasRiemannIntegral (fun x => c * f x + d * g x) a b (c * I + d * J) := by
  intro ε hε
  have hc : 0 < 2 * (|c| + 1) := by positivity
  have hd : 0 < 2 * (|d| + 1) := by positivity
  obtain ⟨δ₁, hδ₁, h₁⟩ := hf (ε / (2 * (|c| + 1))) (div_pos hε hc)
  obtain ⟨δ₂, hδ₂, h₂⟩ := hg (ε / (2 * (|d| + 1))) (div_pos hε hd)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun P hP => ?_⟩
  have e1 := h₁ P fun j hj => (hP j hj).trans_le (min_le_left _ _)
  have e2 := h₂ P fun j hj => (hP j hj).trans_le (min_le_right _ _)
  have hsum : P.riemannSum (fun x => c * f x + d * g x) =
      c * P.riemannSum f + d * P.riemannSum g := by
    simp only [TaggedPartition.riemannSum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsum]
  have hc' : |c| * |P.riemannSum f - I| ≤ ε / 2 := by
    have h1 : |c| * |P.riemannSum f - I| ≤ (|c| + 1) * (ε / (2 * (|c| + 1))) :=
      mul_le_mul (by linarith) e1.le (abs_nonneg _) (by positivity)
    have h2 : (|c| + 1) * (ε / (2 * (|c| + 1))) = ε / 2 := by field_simp
    linarith
  have hd' : |d| * |P.riemannSum g - J| < ε / 2 := by
    have h1 : |d| * |P.riemannSum g - J| ≤ |d| * (ε / (2 * (|d| + 1))) :=
      mul_le_mul_of_nonneg_left e2.le (abs_nonneg _)
    have h2 : |d| * (ε / (2 * (|d| + 1))) < (|d| + 1) * (ε / (2 * (|d| + 1))) :=
      mul_lt_mul_of_pos_right (by linarith) (div_pos hε hd)
    have h3 : (|d| + 1) * (ε / (2 * (|d| + 1))) = ε / 2 := by field_simp
    linarith
  calc |c * P.riemannSum f + d * P.riemannSum g - (c * I + d * J)|
      = |c * (P.riemannSum f - I) + d * (P.riemannSum g - J)| := by ring_nf
    _ ≤ |c * (P.riemannSum f - I)| + |d * (P.riemannSum g - J)| := abs_add_le _ _
    _ = |c| * |P.riemannSum f - I| + |d| * |P.riemannSum g - J| := by rw [abs_mul, abs_mul]
    _ < ε := by linarith

/-- **DLMF 1.4.20**: `∫_a^b f = −∫_b^a f` (`intervalIntegral.integral_symm`). -/
theorem dlmf_1_4_20 (f : ℝ → ℝ) (a b : ℝ) : ∫ x in a..b, f x = -∫ x in b..a, f x :=
  intervalIntegral.integral_symm b a

/-- **DLMF 1.4.21**: `∫_a^b f = ∫_a^c f + ∫_c^b f`
(`intervalIntegral.integral_add_adjacent_intervals`). -/
theorem dlmf_1_4_21 {f : ℝ → ℝ} {a b c : ℝ} (hac : IntervalIntegrable f volume a c)
    (hcb : IntervalIntegrable f volume c b) :
    ∫ x in a..b, f x = (∫ x in a..c, f x) + ∫ x in c..b, f x :=
  (intervalIntegral.integral_add_adjacent_intervals hac hcb).symm

/-! #### Infinite integrals -/

/-- **DLMF 1.4.22**: `∫_a^∞ f = lim_{b→∞} ∫_a^b f`; the integral converges to `L`. -/
def ConvergesAtTop (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Tendsto (fun b => ∫ x in a..b, f x) atTop (𝓝 L)

/-- **DLMF 1.4.22**, similarly `∫_{−∞}^a f = lim_{b→−∞} ∫_b^a f`. -/
def ConvergesAtBot (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Tendsto (fun b => ∫ x in b..a, f x) atBot (𝓝 L)

/-- **DLMF 1.4.23**: for `f(b) = ±∞`, `∫_a^b f = lim_{c→b−} ∫_a^c f`. -/
def ConvergesLeft (f : ℝ → ℝ) (a b L : ℝ) : Prop :=
  Tendsto (fun c => ∫ x in a..c, f x) (𝓝[<] b) (𝓝 L)

/-- **DLMF 1.4.23**, similarly when `f(a) = ±∞`: `∫_a^b f = lim_{c→a+} ∫_c^b f`. -/
def ConvergesRight (f : ℝ → ℝ) (a b L : ℝ) : Prop :=
  Tendsto (fun c => ∫ x in c..b, f x) (𝓝[>] a) (𝓝 L)

/-- **DLMF 1.4.22**: for `f` (Lebesgue) integrable on `(a, ∞)`, the limit exists and equals
`∫_{(a,∞)} f` (`intervalIntegral_tendsto_integral_Ioi`). -/
theorem dlmf_1_4_22 {f : ℝ → ℝ} {a : ℝ} (hf : IntegrableOn f (Ioi a)) :
    ConvergesAtTop f a (∫ x in Ioi a, f x) :=
  intervalIntegral_tendsto_integral_Ioi a hf tendsto_id

/-- **DLMF 1.4.22** for `∫_{−∞}^a` (`intervalIntegral_tendsto_integral_Iic`). -/
theorem dlmf_1_4_22_Iic {f : ℝ → ℝ} {a : ℝ} (hf : IntegrableOn f (Iic a)) :
    ConvergesAtBot f a (∫ x in Iic a, f x) :=
  intervalIntegral_tendsto_integral_Iic a hf tendsto_id

/-- **DLMF 1.4.23**: for `f` integrable on `[a, b]`, `∫_a^c f → ∫_a^b f` as `c → b−`
(`intervalIntegral.continuousOn_primitive_interval`). -/
theorem dlmf_1_4_23 {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hf : IntervalIntegrable f volume a b) :
    ConvergesLeft f a b (∫ x in a..b, f x) := by
  have hc := intervalIntegral.continuousOn_primitive_interval (μ := volume)
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mp hf |>.mono_set
      (by rw [uIcc_of_le hab.le]))
  have hb : b ∈ uIcc a b := right_mem_uIcc
  have hmem : uIcc a b ∈ 𝓝[<] b := by
    rw [uIcc_of_le hab.le]
    exact Filter.mem_of_superset (Ioo_mem_nhdsLT hab) Ioo_subset_Icc_self
  exact ((hc b hb).mono_of_mem_nhdsWithin hmem).tendsto

/-- **DLMF 1.4.23** at the left endpoint: `∫_c^b f → ∫_a^b f` as `c → a+`. -/
theorem dlmf_1_4_23_right {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : IntervalIntegrable f volume a b) : ConvergesRight f a b (∫ x in a..b, f x) := by
  have hc := intervalIntegral.continuousOn_primitive_interval (μ := volume)
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mp hf |>.mono_set
      (by rw [uIcc_of_le hab.le]))
  have hmem : uIcc a b ∈ 𝓝[>] a := by
    rw [uIcc_of_le hab.le]
    exact Filter.mem_of_superset (Ioo_mem_nhdsGT hab) Ioo_subset_Icc_self
  have hlim := ((hc a left_mem_uIcc).mono_of_mem_nhdsWithin hmem).tendsto
  simp only [intervalIntegral.integral_same] at hlim
  have := (tendsto_const_nhds (x := ∫ x in a..b, f x)).sub hlim
  rw [sub_zero] at this
  refine this.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hab] with c hc'
  exact intervalIntegral.integral_interval_sub_left hf
    (hf.mono_set (by rw [uIcc_of_le hab.le, uIcc_of_le hc'.1.le]
                     exact Icc_subset_Icc le_rfl hc'.2.le))

/-- **DLMF §1.4(v)**: absolute convergence implies convergence (at `∞`): if `∫_a^b |f|` has a limit
as `b → ∞`, then `f` is integrable on `(a, ∞)` and `∫_a^b f` converges
(`integrableOn_Ioi_of_intervalIntegral_norm_tendsto`). -/
theorem dlmf_1_4_v_abs_atTop {f : ℝ → ℝ} {a L : ℝ}
    (hloc : ∀ b, IntervalIntegrable f volume a b) (habs : ConvergesAtTop (fun x => |f x|) a L) :
    IntegrableOn f (Ioi a) ∧ ConvergesAtTop f a (∫ x in Ioi a, f x) := by
  have hint : IntegrableOn f (Ioi a) :=
    integrableOn_Ioi_of_intervalIntegral_norm_tendsto L a (fun i => (hloc i).1) tendsto_id
      (by simp only [Real.norm_eq_abs]; exact habs)
  exact ⟨hint, dlmf_1_4_22 hint⟩

/-- **DLMF §1.4(v)**: absolute convergence implies convergence (at a singular endpoint `b`): if
`∫_a^c |f|` has a limit as `c → b−`, then `f` is integrable on `[a, b]` and `∫_a^c f` converges. -/
theorem dlmf_1_4_v_abs_left {f : ℝ → ℝ} {a b L : ℝ} (hab : a < b)
    (hloc : ∀ c < b, IntervalIntegrable f volume a c)
    (habs : ConvergesLeft (fun x => |f x|) a b L) :
    IntervalIntegrable f volume a b ∧ ConvergesLeft f a b (∫ x in a..b, f x) := by
  classical
  set b' : ℝ → ℝ := fun i => if i < b then i else a with hb'
  have hfi : ∀ i, IntegrableOn f (Ioc a (b' i)) := fun i => by
    by_cases hi : i < b
    · simp only [hb', ite_eq_left hi]
      exact (hloc i hi).1
    · simp only [hb', ite_eq_right hi, Set.Ioc_self]
      exact integrableOn_empty (f := f)
  have hb'lim : Tendsto b' (𝓝[<] b) (𝓝 b) := by
    refine (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with i hi
    simp [hb', mem_Iio.mp hi]
  have hbound : ∀ᶠ i in 𝓝[<] b, (∫ x in Ioc a (b' i), ‖f x‖) ≤ L + 1 := by
    filter_upwards [Ioo_mem_nhdsLT hab, (Metric.tendsto_nhds.mp habs) 1 one_pos] with i hi hL
    simp only [hb', ite_eq_left hi.2]
    rw [Real.dist_eq] at hL
    rw [← intervalIntegral.integral_of_le hi.1.le]
    simp only [Real.norm_eq_abs]
    linarith [le_abs_self ((∫ x in a..i, |f x|) - L)]
  have hint := integrableOn_Ioc_of_intervalIntegral_norm_bounded_right hfi hb'lim hbound
  have hii : IntervalIntegrable f volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).mpr hint
  exact ⟨hii, dlmf_1_4_23 hab hii⟩


open scoped ENNReal NNReal

/-! #### Stieltjes, Lebesgue, and Lebesgue–Stieltjes integrals -/

/-- **DLMF §1.4(v)**: the Stieltjes measure `dα` of a nondecreasing function `α` gives `(c, d]` the
mass `α(d) − α(c)` (`StieltjesFunction.measure_Ioc`; Mathlib's `StieltjesFunction` is a
nondecreasing right-continuous function, and `Monotone.stieltjesFunction` replaces a nondecreasing
function by its right limits, which does not change the Stieltjes integral of a continuous
function). -/
theorem dlmf_1_4_v_stieltjes_measure (α : StieltjesFunction ℝ) (c d : ℝ) :
    α.measure (Ioc c d) = ENNReal.ofReal (α d - α c) :=
  α.measure_Ioc c d

/-- **DLMF §1.4(v)**: Lebesgue measure is the Stieltjes measure of `α(x) = x`, so the Lebesgue
integral is the Lebesgue–Stieltjes integral for `α(x) = x` (`Real.volume_eq_stieltjes_id`). -/
theorem dlmf_1_4_v_lebesgue : (volume : Measure ℝ) = StieltjesFunction.id.measure :=
  Real.volume_eq_stieltjes_id

namespace TaggedPartition

variable {a b : ℝ}

/-- The Riemann–Stieltjes sum `∑ⱼ f(ξⱼ)(α(xⱼ₊₁) − α(xⱼ))`. -/
def stieltjesSum (P : TaggedPartition a b) (f α : ℝ → ℝ) : ℝ :=
  ∑ j ∈ range P.n, f (P.ξ j) * (α (P.x (j + 1)) - α (P.x j))

end TaggedPartition

/-- **DLMF §1.4(v)**: the Stieltjes integral `∫_a^b f dα` as the limit of Riemann–Stieltjes sums
(defined "similarly as Riemann integrability"). -/
def HasStieltjesIntegral (f α : ℝ → ℝ) (a b I : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ P : TaggedPartition a b, (∀ j < P.n, P.x (j + 1) - P.x j < δ) →
    |P.stieltjesSum f α - I| < ε

/-- **DLMF §1.4(v)**: for `α` differentiable on `[a, b]` with continuous derivative `w` and `f`
continuous, the Stieltjes integral exists and equals `∫_a^b f(x) w(x) dx`: by the mean value
theorem `α(xⱼ₊₁) − α(xⱼ) = w(cⱼ)(xⱼ₊₁ − xⱼ)`, so the Riemann–Stieltjes sums are within
`max |f| · osc w · (b − a)` of the Riemann sums of `f w`. -/
theorem hasStieltjesIntegral_of_deriv {f α w : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hα : ∀ x ∈ Icc a b, HasDerivAt α (w x) x) (hw : ContinuousOn w (Icc a b))
    (hf : ContinuousOn f (Icc a b)) :
    HasStieltjesIntegral f α a b (∫ x in a..b, f x * w x) := by
  intro ε hε
  obtain ⟨Mf, hMf⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  have hMf0 : 0 ≤ Mf := (norm_nonneg _).trans (hMf a ⟨le_rfl, hab⟩)
  obtain ⟨δ₁, hδ₁, h₁⟩ := dlmf_1_4_18 hab (hf.mul hw) (ε / 2) (half_pos hε)
  set ε' := ε / (2 * (Mf + 1) * (b - a + 1)) with hε'
  have hε'0 : 0 < ε' := by
    have : 0 < b - a + 1 := by linarith
    positivity
  obtain ⟨δ₂, hδ₂, h₂⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hw) ε' hε'0
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun P hP => ?_⟩
  have hR := h₁ P fun j hj => (hP j hj).trans_le (min_le_left _ _)
  have hdiff : |P.stieltjesSum f α - P.riemannSum (fun x => f x * w x)| ≤ Mf * ε' * (b - a) := by
    rw [TaggedPartition.stieltjesSum, TaggedPartition.riemannSum, ← Finset.sum_sub_distrib,
      ← P.sum_lengths, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
    have hjn := mem_range.mp hj
    have hlt := P.lt j hjn
    have hsub : Icc (P.x j) (P.x (j + 1)) ⊆ Icc a b :=
      Icc_subset_Icc (P.mem_Icc hjn.le).1 (P.mem_Icc hjn).2
    obtain ⟨c, hc, hcα⟩ := exists_hasDerivAt_eq_slope α w hlt
      (fun x hx => (hα x (hsub hx)).continuousAt.continuousWithinAt)
      fun x hx => hα x (hsub (Ioo_subset_Icc_self hx))
    have hΔ : α (P.x (j + 1)) - α (P.x j) = w c * (P.x (j + 1) - P.x j) := by
      rw [hcα, div_mul_cancel₀ _ (sub_ne_zero.mpr hlt.ne')]
    have htag := P.tag j hjn
    have hwc : |w c - w (P.ξ j)| ≤ ε' := by
      have hd : dist c (P.ξ j) < δ₂ := by
        rw [Real.dist_eq, abs_lt]
        have := (hP j hjn).trans_le (min_le_right _ _)
        constructor <;> linarith [hc.1, hc.2, htag.1, htag.2]
      have := h₂ c (hsub (Ioo_subset_Icc_self hc)) (P.ξ j) (hsub htag) hd
      rw [Real.dist_eq] at this
      exact this.le
    have hfξ : |f (P.ξ j)| ≤ Mf := by rw [← Real.norm_eq_abs]; exact hMf _ (hsub htag)
    rw [hΔ, show f (P.ξ j) * (w c * (P.x (j + 1) - P.x j)) - f (P.ξ j) * w (P.ξ j) *
        (P.x (j + 1) - P.x j) = f (P.ξ j) * (w c - w (P.ξ j)) * (P.x (j + 1) - P.x j) by ring,
      abs_mul, abs_mul, abs_of_pos (sub_pos.mpr hlt)]
    have : |f (P.ξ j)| * |w c - w (P.ξ j)| ≤ Mf * ε' :=
      mul_le_mul hfξ hwc (abs_nonneg _) hMf0
    nlinarith [sub_pos.mpr hlt]
  have hsmall : Mf * ε' * (b - a) < ε / 2 := by
    have hpos : 0 < 2 * (Mf + 1) * (b - a + 1) := by
      have : 0 < b - a + 1 := by linarith
      positivity
    rw [hε', mul_div_assoc', div_mul_eq_mul_div, div_lt_iff₀ hpos]
    have h1 : Mf * ε * (b - a) * 2 ≤ (Mf + 1) * ε * (b - a + 1) * 2 := by
      have : 0 ≤ b - a := by linarith
      gcongr <;> linarith
    nlinarith [mul_pos hε (show (0 : ℝ) < Mf + 1 by linarith)]
  calc |P.stieltjesSum f α - ∫ x in a..b, f x * w x|
      ≤ |P.stieltjesSum f α - P.riemannSum (fun x => f x * w x)| +
          |P.riemannSum (fun x => f x * w x) - ∫ x in a..b, f x * w x| := abs_sub_le _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt (hdiff.trans hsmall.le) hR
    _ = ε := add_halves ε

/-! #### Absolutely continuous Stieltjes measure -/

/-- **DLMF 1.4.23_1**: `dα` is absolutely continuous with weight function `w ≥ 0` when
`α(d) − α(c) = ∫_c^d w(x) dx` for `c ≤ d`; then `dα = w(x) dx`, i.e. the Stieltjes measure is
Lebesgue measure with density `w` (`Measure.ext_of_Ioc'`, `ofReal_integral_eq_lintegral_ofReal`). -/
theorem dlmf_1_4_23_1 {α : StieltjesFunction ℝ} {w : ℝ → ℝ} (hw0 : ∀ x, 0 ≤ w x)
    (hwi : LocallyIntegrable w volume) (hα : ∀ c d, c ≤ d → α d - α c = ∫ x in c..d, w x) :
    α.measure = volume.withDensity fun x => ENNReal.ofReal (w x) := by
  refine Measure.ext_of_Ioc' _ _ (fun c d _ => measure_Ioc_lt_top.ne) fun c d hcd => ?_
  rw [α.measure_Ioc, hα c d hcd.le, intervalIntegral.integral_of_le hcd.le,
    withDensity_apply _ measurableSet_Ioc,
    ofReal_integral_eq_lintegral_ofReal (hwi.integrableOn_isCompact isCompact_Icc |>.mono_set
      Ioc_subset_Icc_self) (ae_of_all _ fun x => hw0 x)]

/-- **DLMF 1.4.23_2**: then `∫_a^b f(x) dα(x) = ∫_a^b f(x) w(x) dx`
(`integral_withDensity_eq_integral_toReal_smul₀`). -/
theorem dlmf_1_4_23_2 {α : StieltjesFunction ℝ} {w : ℝ → ℝ} (hw0 : ∀ x, 0 ≤ w x)
    (hwi : LocallyIntegrable w volume) (hα : ∀ c d, c ≤ d → α d - α c = ∫ x in c..d, w x)
    (f : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) :
    ∫ x in Ioo a b, f x ∂α.measure = ∫ x in a..b, f x * w x := by
  rw [dlmf_1_4_23_1 hw0 hwi hα, restrict_withDensity measurableSet_Ioo,
    integral_withDensity_eq_integral_toReal_smul₀
      (hwi.aestronglyMeasurable.aemeasurable.ennreal_ofReal.restrict)
      (ae_of_all _ fun x => ENNReal.ofReal_lt_top),
    intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun x _ => ?_
  rw [ENNReal.toReal_ofReal (hw0 x), smul_eq_mul, mul_comm]

/-- The Stieltjes function `α` of a `C¹` function with nonnegative derivative. -/
def stieltjesOfDeriv {α w : ℝ → ℝ} (hα : ∀ x, HasDerivAt α (w x) x) (hw0 : ∀ x, 0 ≤ w x) :
    StieltjesFunction ℝ where
  toFun := α
  mono' := monotone_of_deriv_nonneg (fun x => (hα x).differentiableAt)
    fun x => (hα x).deriv ▸ hw0 x
  right_continuous' x := (hα x).continuousAt.continuousWithinAt

/-- **DLMF §1.4(v)**: in particular `dα` is absolutely continuous when `α` is differentiable with
`α' = w` continuous: `α(d) − α(c) = ∫_c^d w` (`intervalIntegral.integral_eq_sub_of_hasDerivAt`). -/
theorem dlmf_1_4_v_absCont_of_deriv {α w : ℝ → ℝ} (hα : ∀ x, HasDerivAt α (w x) x)
    (hw : Continuous w) (c d : ℝ) : α d - α c = ∫ x in c..d, w x :=
  (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hα x)
    (hw.intervalIntegrable c d)).symm

theorem stieltjesOfDeriv_measure {α w : ℝ → ℝ} (hα : ∀ x, HasDerivAt α (w x) x)
    (hw0 : ∀ x, 0 ≤ w x) (hw : Continuous w) :
    (stieltjesOfDeriv hα hw0).measure = volume.withDensity fun x => ENNReal.ofReal (w x) :=
  dlmf_1_4_23_1 hw0 hw.locallyIntegrable fun c d _ => dlmf_1_4_v_absCont_of_deriv hα hw c d

/-! #### Stieltjes measure with `α(x)` discontinuous -/

/-- The Heaviside step `H(x − x₀)` (`1` for `x ≥ x₀`, `0` for `x < x₀`; right-continuous, as a
Stieltjes function). -/
noncomputable def heaviside (x₀ : ℝ) : StieltjesFunction ℝ where
  toFun x := if x₀ ≤ x then 1 else 0
  mono' x y hxy := by
    by_cases hx : x₀ ≤ x
    · simp [hx, hx.trans hxy]
    · by_cases hy : x₀ ≤ y <;> simp [hx, hy]
  right_continuous' x := by
    by_cases hx : x₀ ≤ x
    · refine (continuousWithinAt_const (b := (1 : ℝ))).congr (fun y hy => ?_) (by simp [hx])
      simp [hx.trans (mem_Ici.mp hy)]
    · have : ∀ᶠ y in 𝓝[Ici x] x, (if x₀ ≤ y then (1 : ℝ) else 0) = 0 := by
        filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (not_le.mp hx))] with y hy
        simp [not_le.mpr (mem_Iio.mp hy)]
      exact (continuousWithinAt_const (b := (0 : ℝ))).congr_of_eventuallyEq this (by simp [hx])

theorem heaviside_apply (x₀ x : ℝ) : heaviside x₀ x = if x₀ ≤ x then 1 else 0 := rfl

/-- **DLMF §1.4(v)**: for `α(x) = H(x − xₙ)` the measure `dα` is the Dirac measure `δ(x − xₙ) dx`
at `xₙ`. -/
theorem heaviside_measure (x₀ : ℝ) : (heaviside x₀).measure = Measure.dirac x₀ := by
  refine Measure.ext_of_Ioc' _ _ (fun c d _ => measure_Ioc_lt_top.ne) fun c d hcd => ?_
  rw [StieltjesFunction.measure_Ioc, heaviside_apply, heaviside_apply,
    Measure.dirac_apply' _ measurableSet_Ioc]
  by_cases h1 : x₀ ≤ c
  · have h2 : x₀ ≤ d := h1.trans hcd.le
    simp [h1, h2, Set.indicator, not_lt.mpr h1]
  · by_cases h2 : x₀ ≤ d
    · simp [h1, h2, Set.indicator, not_le.mp h1]
    · simp [h1, h2, Set.indicator]

/-- **DLMF §1.4(v)**: `∫_a^b f(x) dα(x) = f(xₙ)` for `xₙ ∈ (a, b)` and `0` otherwise, when
`α(x) = H(x − xₙ)` (`setIntegral_dirac`). -/
theorem dlmf_1_4_v_heaviside (f : ℝ → ℝ) (x₀ a b : ℝ) :
    ∫ x in Ioo a b, f x ∂(heaviside x₀).measure = if x₀ ∈ Ioo a b then f x₀ else 0 := by
  classical
  rw [heaviside_measure, setIntegral_dirac]

/-- Every function is integrable against a finite nonnegative combination of Dirac measures. -/
theorem integrable_sum_dirac {ι : Type*} (T : Finset ι) (c : ι → ℝ≥0) (x : ι → ℝ) (f : ℝ → ℝ) :
    Integrable f (∑ n ∈ T, c n • Measure.dirac (x n)) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert m T hm ih =>
    rw [Finset.sum_insert hm]
    exact ((integrable_dirac (by simp)).smul_measure_nnreal).add_measure ih

/-- The integral against a finite nonnegative combination of Dirac measures at points of `s`. -/
theorem integral_sum_dirac {ι : Type*} (T : Finset ι) (c : ι → ℝ≥0) (x : ι → ℝ) (f : ℝ → ℝ)
    (s : Set ℝ) (hx : ∀ n ∈ T, x n ∈ s) :
    ∫ y in s, f y ∂(∑ n ∈ T, c n • Measure.dirac (x n)) = ∑ n ∈ T, (c n : ℝ) * f (x n) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert m T hm ih =>
    rw [Finset.sum_insert hm, Finset.sum_insert hm, Measure.restrict_add,
      integral_add_measure ((integrable_dirac (by simp)).smul_measure_nnreal.restrict)
        ((integrable_sum_dirac T c x f).restrict),
      Measure.restrict_smul, integral_smul_nnreal_measure, setIntegral_dirac,
      ite_eq_left (hx m (Finset.mem_insert_self m T)),
      ih fun n hn => hx n (Finset.mem_insert_of_mem hn), NNReal.smul_def, smul_eq_mul]

/-- The Stieltjes measure of a finite nonnegative combination of Stieltjes functions
(`StieltjesFunction.measure_add`, `StieltjesFunction.measure_smul`). -/
theorem measure_sum_smul {ι : Type*} (T : Finset ι) (c : ι → ℝ≥0) (g : ι → StieltjesFunction ℝ) :
    (∑ n ∈ T, c n • g n).measure = ∑ n ∈ T, c n • (g n).measure := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [StieltjesFunction.measure_zero]
  | insert m T hm ih =>
    rw [Finset.sum_insert hm, Finset.sum_insert hm, StieltjesFunction.measure_add,
      StieltjesFunction.measure_smul, ih]

/-- **DLMF 1.4.23_3**: for `dα(x) = w(x) dx + ∑ₙ wₙ δ(x − xₙ) dx` with `xₙ ∈ (a, b)`, i.e.
`α = α_w + ∑ₙ wₙ H(x − xₙ)` with `dα_w = w dx` absolutely continuous, and `f` continuous,
`∫_a^b f(x) dα(x) = ∫_a^b w(x) f(x) dx + ∑ₙ wₙ f(xₙ)`. -/
theorem dlmf_1_4_23_3 {αw : StieltjesFunction ℝ} {w : ℝ → ℝ} (hw0 : ∀ x, 0 ≤ w x)
    (hwi : LocallyIntegrable w volume) (hα : ∀ c d, c ≤ d → αw d - αw c = ∫ x in c..d, w x)
    {ι : Type*} (T : Finset ι) (wₙ : ι → ℝ≥0) (xₙ : ι → ℝ) {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hxₙ : ∀ n ∈ T, xₙ n ∈ Ioo a b) (hf : ContinuousOn f (Icc a b)) :
    ∫ x in Ioo a b, f x ∂(αw + ∑ n ∈ T, wₙ n • heaviside (xₙ n)).measure =
      (∫ x in a..b, w x * f x) + ∑ n ∈ T, (wₙ n : ℝ) * f (xₙ n) := by
  have hmeas : (αw + ∑ n ∈ T, wₙ n • heaviside (xₙ n)).measure =
      αw.measure + ∑ n ∈ T, wₙ n • Measure.dirac (xₙ n) := by
    rw [StieltjesFunction.measure_add, measure_sum_smul]
    simp only [heaviside_measure]
  have hint : IntegrableOn f (Ioo a b) αw.measure :=
    (hf.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  rw [hmeas, Measure.restrict_add, integral_add_measure hint
    ((integrable_sum_dirac T wₙ xₙ f).restrict), dlmf_1_4_23_2 hw0 hwi hα f hab,
    integral_sum_dirac T wₙ xₙ f _ hxₙ]
  congr 1
  exact intervalIntegral.integral_congr fun x _ => mul_comm (f x) (w x)


/-! #### Cauchy principal values -/

/-- **DLMF 1.4.24**: the Cauchy principal value
`⨍_a^b f = lim_{ε→0+} (∫_a^{c−ε} f + ∫_{c+ε}^b f)` is `L`. -/
def HasPrincipalValue (f : ℝ → ℝ) (a b c L : ℝ) : Prop :=
  Tendsto (fun ε => (∫ x in a..c - ε, f x) + ∫ x in c + ε..b, f x) (𝓝[>] 0) (𝓝 L)

/-- **DLMF 1.4.25**: `⨍_{−∞}^∞ f = lim_{b→∞} ∫_{−b}^b f` is `L`. -/
def HasPrincipalValueInfty (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Tendsto (fun b => ∫ x in -b..b, f x) atTop (𝓝 L)

theorem tendsto_sub_nhdsGT {a b c : ℝ} (hc : c ∈ Ioo a b) :
    Tendsto (fun ε => c - ε) (𝓝[>] 0) (𝓝[Icc a b] c) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have : Tendsto (fun ε : ℝ => c - ε) (𝓝 0) (𝓝 (c - 0)) := tendsto_const_nhds.sub tendsto_id
    rw [sub_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < c - a by linarith [hc.1])] with ε hε
    exact ⟨by linarith [hε.2], by linarith [hε.1, hc.2]⟩

theorem tendsto_add_nhdsGT {a b c : ℝ} (hc : c ∈ Ioo a b) :
    Tendsto (fun ε => c + ε) (𝓝[>] 0) (𝓝[Icc a b] c) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have : Tendsto (fun ε : ℝ => c + ε) (𝓝 0) (𝓝 (c + 0)) := tendsto_const_nhds.add tendsto_id
    rw [add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < b - c by linarith [hc.2])] with ε hε
    exact ⟨by linarith [hε.1, hc.1], by linarith [hε.2]⟩

/-- **DLMF 1.4.24**: when `∫_a^b f` exists, the principal value exists and equals it (continuity
of `x ↦ ∫_a^x f`, `intervalIntegral.continuousOn_primitive_interval`). -/
theorem dlmf_1_4_24 {f : ℝ → ℝ} {a b c : ℝ} (hc : c ∈ Ioo a b)
    (hf : IntervalIntegrable f volume a b) : HasPrincipalValue f a b c (∫ x in a..b, f x) := by
  have hab : a ≤ b := (hc.1.trans hc.2).le
  have hcont := intervalIntegral.continuousOn_primitive_interval (μ := volume)
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hf |>.mono_set
      (by rw [Set.uIcc_of_le hab]))
  rw [Set.uIcc_of_le hab] at hcont
  set F := fun x => ∫ t in a..x, f t with hF
  have hcF : ContinuousWithinAt F (Icc a b) c := hcont c (Ioo_subset_Icc_self hc)
  have h1 := hcF.tendsto.comp (tendsto_sub_nhdsGT hc)
  have h2 := hcF.tendsto.comp (tendsto_add_nhdsGT hc)
  have hlim := h1.add (tendsto_const_nhds (x := ∫ x in a..b, f x)) |>.sub h2
  rw [add_sub_cancel_left] at hlim
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < min (c - a) (b - c) by
    exact lt_min (by linarith [hc.1]) (by linarith [hc.2]))] with ε hε
  have hε1 : ε < c - a := hε.2.trans_le (min_le_left _ _)
  have hε2 : ε < b - c := hε.2.trans_le (min_le_right _ _)
  have hsub : IntervalIntegrable f volume a (c + ε) := hf.mono_set (by
    rw [Set.uIcc_of_le hab, Set.uIcc_of_le (by linarith [hε.1])]
    exact Icc_subset_Icc le_rfl (by linarith))
  simp only [Function.comp, hF]
  rw [← intervalIntegral.integral_interval_sub_left hf hsub]
  ring

/-- **DLMF §1.4(v)**: the principal value can exist when the integral does not: for `f(x) = 1/x`
on `(−1, 1)` with `c = 0`, `∫_{−1}^{−ε} dx/x + ∫_ε^1 dx/x = 0` (`integral_inv`). -/
theorem dlmf_1_4_24_inv : HasPrincipalValue (fun x => x⁻¹) (-1) 1 0 0 := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
  have h1 : (0 : ℝ) ∉ uIcc (-1) (0 - ε) := by
    rw [Set.uIcc_of_le (by linarith [hε.2])]
    intro h
    linarith [h.2, hε.1]
  have h2 : (0 : ℝ) ∉ uIcc (0 + ε) 1 := by
    rw [Set.uIcc_of_le (by linarith [hε.2])]
    intro h
    linarith [h.1, hε.1]
  rw [integral_inv h1, integral_inv h2, zero_sub, zero_add, neg_div_neg_eq, div_one,
    one_div, Real.log_inv, add_neg_cancel]

/-- **DLMF 1.4.25**: for `f` integrable on `ℝ`, the principal value exists and equals `∫ f`
(`intervalIntegral_tendsto_integral`). -/
theorem dlmf_1_4_25 {f : ℝ → ℝ} (hf : Integrable f) : HasPrincipalValueInfty f (∫ x, f x) :=
  intervalIntegral_tendsto_integral hf tendsto_neg_atTop_atBot tendsto_id

/-- **DLMF §1.4(v)**: `⨍_{−∞}^∞ x dx = 0` although `x` is not integrable (`integral_id`). -/
theorem dlmf_1_4_25_id : HasPrincipalValueInfty (fun x => x) 0 := by
  refine tendsto_const_nhds.congr fun b => ?_
  rw [integral_id]
  ring

/-! #### Fundamental theorem of calculus -/

/-- **DLMF 1.4.26**: for `F' = f` with `f` continuous, `∫_a^b f = F(b) − F(a)`
(`intervalIntegral.integral_eq_sub_of_hasDerivAt`). -/
theorem dlmf_1_4_26 {F f : ℝ → ℝ} {a b : ℝ} (hF : ∀ x ∈ uIcc a b, HasDerivAt F (f x) x)
    (hf : ContinuousOn f (uIcc a b)) : ∫ x in a..b, f x = F b - F a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt hF hf.intervalIntegrable

/-- **DLMF 1.4.27**: `d/dx ∫_a^x f(t) dt = f(x)` for continuous `f`
(`Continuous.integral_hasStrictDerivAt`). -/
theorem dlmf_1_4_27 {f : ℝ → ℝ} (hf : Continuous f) (a x : ℝ) :
    HasDerivAt (fun x => ∫ t in a..x, f t) (f x) x :=
  (hf.integral_hasStrictDerivAt a x).hasDerivAt

/-! #### Change of variables -/

/-- **DLMF 1.4.28**: `∫_a^b f(φ(x)) φ'(x) dx = ∫_{φ(a)}^{φ(b)} f(t) dt` for `φ'` continuous and `f`
continuous on `φ([a, b])` (`intervalIntegral.integral_comp_mul_deriv'`). -/
theorem dlmf_1_4_28 {f φ φ' : ℝ → ℝ} {a b : ℝ} (hφ : ∀ x ∈ uIcc a b, HasDerivAt φ (φ' x) x)
    (hφ' : ContinuousOn φ' (uIcc a b)) (hf : ContinuousOn f (φ '' uIcc a b)) :
    ∫ x in a..b, f (φ x) * φ' x = ∫ t in φ a..φ b, f t :=
  intervalIntegral.integral_comp_mul_deriv' hφ hφ' hf

/-- **DLMF 1.4.28** for piecewise continuous `φ'`: it suffices that `φ` be continuous with
right derivative `φ'` on `(a, b)` and the integrands be integrable
(`intervalIntegral.integral_comp_mul_deriv'''`). -/
theorem dlmf_1_4_28_piecewise {f φ φ' : ℝ → ℝ} {a b : ℝ} (hφ : ContinuousOn φ (uIcc a b))
    (hφ' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivWithinAt φ (φ' x) (Ioi x) x)
    (hf : ContinuousOn f (φ '' Ioo (min a b) (max a b))) (hf1 : IntegrableOn f (φ '' uIcc a b))
    (hf2 : IntegrableOn (fun x => f (φ x) * φ' x) (uIcc a b)) :
    ∫ x in a..b, f (φ x) * φ' x = ∫ t in φ a..φ b, f t :=
  intervalIntegral.integral_comp_mul_deriv''' hφ hφ' hf hf1 hf2

/-! #### Mean value theorems -/

/-- **DLMF 1.4.29**, the first mean value theorem: for `f` continuous and `φ ≥ 0` integrable on
`[a, b]`, `∫_a^b f φ = f(c) ∫_a^b φ` for some `c ∈ [a, b]`
(`exists_eq_const_mul_intervalIntegral_of_nonneg`). -/
theorem dlmf_1_4_29 {f φ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hφ : IntervalIntegrable φ volume a b) (hφ0 : ∀ x ∈ Icc a b, 0 ≤ φ x) :
    ∃ c ∈ Icc a b, ∫ x in a..b, f x * φ x = f c * ∫ x in a..b, φ x := by
  rw [← Set.uIcc_of_le hab] at hf ⊢
  exact exists_eq_const_mul_intervalIntegral_of_nonneg hf hφ fun x hx =>
    hφ0 x (by rw [← Set.uIcc_of_le hab]; exact uIoc_subset_uIcc hx)

/-- Integrability of `f φ` for `f` monotone and `φ` integrable on `[a, b]`. -/
theorem intervalIntegrable_mul_of_monotoneOn {f φ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : MonotoneOn f (Icc a b)) (hφ : IntervalIntegrable φ volume a b) :
    IntervalIntegrable (fun x => f x * φ x) volume a b := by
  have hfi : IntervalIntegrable f volume a b :=
    MonotoneOn.intervalIntegrable (by rwa [Set.uIcc_of_le hab])
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab] at hfi hφ ⊢
  refine hφ.bdd_mul hfi.aestronglyMeasurable (c := |f a| + |f b|) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => ?_
  have hx' : x ∈ Icc a b := Ioc_subset_Icc_self hx
  have h1 := hf ⟨le_rfl, hab⟩ hx' hx'.1
  have h2 := hf hx' ⟨hab, le_rfl⟩ hx'.2
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [neg_abs_le (f a), le_abs_self (f b), abs_nonneg (f a),
    abs_nonneg (f b)]

/-- **DLMF 1.4.30**, the second mean value theorem, `f` nondecreasing: `∫_a^b f φ =
f(a) ∫_a^c φ + f(b) ∫_c^b φ` for some `c ∈ [a, b]` (from Mathlib's nonnegative-weight form
`exists_eq_const_mul_intervalIntegral_of_nonneg_of_monotoneOn` applied to `f − f(a)`). -/
theorem dlmf_1_4_30_monotone {f φ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : MonotoneOn f (Icc a b))
    (hφ : IntervalIntegrable φ volume a b) :
    ∃ c ∈ Icc a b, ∫ x in a..b, f x * φ x =
      f a * (∫ x in a..c, φ x) + f b * ∫ x in c..b, φ x := by
  have hg : MonotoneOn (fun x => f x - f a) (Icc a b) := fun x hx y hy hxy =>
    sub_le_sub_right (hf hx hy hxy) _
  obtain ⟨c, hc, hcg⟩ := exists_eq_const_mul_intervalIntegral_of_nonneg_of_monotoneOn
    (f := fun x => f x - f a) hab (by simp) hg hφ
  refine ⟨c, hc, ?_⟩
  have hfφ := intervalIntegrable_mul_of_monotoneOn hab hf hφ
  have hsplit : ∫ x in a..b, (f x - f a) * φ x =
      (∫ x in a..b, f x * φ x) - f a * ∫ x in a..b, φ x := by
    simp only [sub_mul]
    rw [intervalIntegral.integral_sub hfφ (hφ.const_mul (f a)),
      intervalIntegral.integral_const_mul]
  have hca : IntervalIntegrable φ volume a c := hφ.mono_set (by
    rw [Set.uIcc_of_le hab, Set.uIcc_of_le hc.1]; exact Icc_subset_Icc le_rfl hc.2)
  have hcb : IntervalIntegrable φ volume c b := hφ.mono_set (by
    rw [Set.uIcc_of_le hab, Set.uIcc_of_le hc.2]; exact Icc_subset_Icc hc.1 le_rfl)
  have hadd := intervalIntegral.integral_add_adjacent_intervals hca hcb
  rw [hsplit, ← hadd] at hcg
  linarith

/-- **DLMF 1.4.30**, the second mean value theorem for `f` monotonic (nondecreasing or
nonincreasing; the nonincreasing case from the nondecreasing one applied to `−f`). -/
theorem dlmf_1_4_30 {f φ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : MonotoneOn f (Icc a b) ∨ AntitoneOn f (Icc a b))
    (hφ : IntervalIntegrable φ volume a b) :
    ∃ c ∈ Icc a b, ∫ x in a..b, f x * φ x =
      f a * (∫ x in a..c, φ x) + f b * ∫ x in c..b, φ x := by
  rcases hf with hf | hf
  · exact dlmf_1_4_30_monotone hab hf hφ
  · obtain ⟨c, hc, h⟩ := dlmf_1_4_30_monotone (f := fun x => -f x) hab hf.neg hφ
    refine ⟨c, hc, ?_⟩
    simp only [neg_mul, intervalIntegral.integral_neg] at h
    linarith

/-! #### Repeated integrals -/

/-- The primitive `P g (x) = ∫_a^x g`. -/
noncomputable def primitive (a : ℝ) (g : ℝ → ℝ) : ℝ → ℝ := fun x => ∫ t in a..x, g t

/-- The repeated integral `∫_a^b dxₙ ∫_a^{xₙ} dxₙ₋₁ ⋯ ∫_a^{x₂} dx₁ ∫_a^{x₁} f(x) dx` (`n + 1`
integrations), i.e. the `(n + 1)`-fold primitive of `f` at `b`. -/
noncomputable def repeatedIntegral (a : ℝ) (n : ℕ) (f : ℝ → ℝ) (b : ℝ) : ℝ :=
  (primitive a)^[n + 1] f b

theorem continuous_primitive' {g : ℝ → ℝ} (hg : Continuous g) (a : ℝ) :
    Continuous (primitive a g) :=
  intervalIntegral.continuous_primitive (fun _ _ => hg.intervalIntegrable _ _) a

/-- One integration by parts: `∫_a^b (b − x)^{n+1} f(x) dx = (n + 1) ∫_a^b (b − x)^n P f(x) dx`. -/
theorem integral_pow_mul_eq_succ_mul_primitive {f : ℝ → ℝ} (hf : Continuous f) (a b : ℝ)
    (n : ℕ) : ∫ x in a..b, (b - x) ^ (n + 1) * f x =
      (n + 1) * ∫ x in a..b, (b - x) ^ n * primitive a f x := by
  have hu : ∀ x ∈ uIcc a b, HasDerivAt (fun x => (b - x) ^ (n + 1))
      (-((n + 1 : ℕ) : ℝ) * (b - x) ^ n) x := fun x _ => by
    have := (hasDerivAt_pow (n + 1) (b - x)).comp x ((hasDerivAt_id x).const_sub b)
    convert this using 1
    · rfl
    · rw [Nat.add_sub_cancel]
      push_cast
      ring
  have hv : ∀ x ∈ uIcc a b, HasDerivAt (primitive a f) (f x) x := fun x _ =>
    (hf.integral_hasStrictDerivAt a x).hasDerivAt
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
    ((continuous_const.mul ((continuous_const.sub continuous_id).pow n)).intervalIntegrable a b)
    (hf.intervalIntegrable a b)
  rw [hparts]
  simp only [primitive, sub_self, intervalIntegral.integral_same, mul_zero,
    zero_pow (Nat.succ_ne_zero n), zero_mul, zero_sub]
  rw [← intervalIntegral.integral_neg, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun x _ => ?_
  push_cast
  ring

/-- **DLMF 1.4.31**, repeated integrals (Cauchy's formula): for `f` continuous,
`∫_a^b dxₙ ∫_a^{xₙ} ⋯ ∫_a^{x₁} f(x) dx = (1/n!) ∫_a^b (b − x)^n f(x) dx`; by induction on `n`
with one integration by parts per step. -/
theorem dlmf_1_4_31 {f : ℝ → ℝ} (hf : Continuous f) (a b : ℝ) (n : ℕ) :
    repeatedIntegral a n f b = 1 / n.factorial * ∫ x in a..b, (b - x) ^ n * f x := by
  induction n generalizing f with
  | zero => simp [repeatedIntegral, primitive]
  | succ n ih =>
    have h := ih (continuous_primitive' hf a)
    rw [repeatedIntegral] at h
    rw [repeatedIntegral, Function.iterate_succ_apply, h,
      integral_pow_mul_eq_succ_mul_primitive hf a b n, Nat.factorial_succ]
    push_cast
    field_simp

/-! #### Square-integrable functions -/

/-- **DLMF 1.4.32**: `‖f‖₂² = ∫_a^b |f(x)|² dx`. -/
noncomputable def l2NormSq (f : ℝ → ℝ) (a b : ℝ) : ℝ := ∫ x in a..b, |f x| ^ 2

/-- **DLMF 1.4.32**: a (measurable) `f` is square-integrable on `(a, b)`, i.e. in Mathlib's `L²`
(`MemLp f 2`), iff `|f|²` is integrable there (`memLp_two_iff_integrable_sq`). -/
theorem dlmf_1_4_32 {f : ℝ → ℝ} {a b : ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioc a b))) :
    MemLp f 2 (volume.restrict (Ioc a b)) ↔ IntegrableOn (fun x => |f x| ^ 2) (Ioc a b) := by
  rw [memLp_two_iff_integrable_sq hf]
  simp only [sq_abs]
  rfl


/-! ### Functions of bounded variation (DLMF 1.4.33–1.4.34, Olver (1997b) §11.2–11.5) -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Each Riemann–Stieltjes-type sum of `‖f(xⱼ₊₁) − f(xⱼ)‖` along a monotone sequence in `[a, b]`
is at most `∫_a^b ‖f'‖`, for `f` with continuous derivative `f'` on `[a, b]`
(`‖f(xⱼ₊₁) − f(xⱼ)‖ = ‖∫ f'‖ ≤ ∫ ‖f'‖`, Olver §11.4). -/
theorem sum_norm_sub_le_integral {f f' : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x) (hf' : ContinuousOn f' (Icc a b))
    {u : ℕ → ℝ} (hu : Monotone u) {n : ℕ} (hus : ∀ i ≤ n, u i ∈ Icc a b) :
    ∑ i ∈ range n, ‖f (u (i + 1)) - f (u i)‖ ≤ ∫ x in a..b, ‖f' x‖ := by
  have hnorm : ContinuousOn (fun x => ‖f' x‖) (Icc a b) := hf'.norm
  have hsub : ∀ i < n, uIcc (u i) (u (i + 1)) ⊆ Icc a b := fun i hi => by
    rw [uIcc_of_le (hu (Nat.le_succ i))]
    exact Icc_subset_Icc (hus i hi.le).1 (hus (i + 1) hi).2
  calc ∑ i ∈ range n, ‖f (u (i + 1)) - f (u i)‖
      = ∑ i ∈ range n, ‖∫ x in u i..u (i + 1), f' x‖ := by
        refine sum_congr rfl fun i hi => ?_
        have hi' := mem_range.mp hi
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hf x (hsub i hi' hx))
          ((hf'.mono (hsub i hi')).intervalIntegrable)]
    _ ≤ ∑ i ∈ range n, ∫ x in u i..u (i + 1), ‖f' x‖ :=
        sum_le_sum fun i _ => intervalIntegral.norm_integral_le_integral_norm (hu (Nat.le_succ i))
    _ = ∫ x in u 0..u n, ‖f' x‖ :=
        intervalIntegral.sum_integral_adjacent_intervals fun i hi =>
          (hnorm.mono (hsub i hi)).intervalIntegrable
    _ ≤ ∫ x in a..b, ‖f' x‖ :=
        intervalIntegral.integral_mono_interval (hus 0 (Nat.zero_le n)).1 (hu (Nat.zero_le n))
          (hus n le_rfl).2
          (ae_of_all _ fun x => norm_nonneg _) (hnorm.intervalIntegrable_of_Icc hab)

/-- **Olver (11.02)** (DLMF 1.4.34 on a compact interval): for `f` with continuous derivative
`f'` on `[a, b]`, `𝒱_{a,b}(f) = ∫_a^b ‖f'(x)‖ dx`.  The sums `∑ ‖f(xⱼ₊₁) − f(xⱼ)‖` are at most
the integral; conversely they are within `ε (b − a)` of the Riemann sums of `‖f'‖` once the mesh
is small, by uniform continuity of `f'`. -/
theorem olver_11_02 {f f' : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x) (hf' : ContinuousOn f' (Icc a b)) :
    eVariationOn f (Icc a b) = ENNReal.ofReal (∫ x in a..b, ‖f' x‖) := by
  have hnorm : ContinuousOn (fun x => ‖f' x‖) (Icc a b) := hf'.norm
  set I := ∫ x in a..b, ‖f' x‖ with hI
  -- the upper bound
  have hle : eVariationOn f (Icc a b) ≤ ENNReal.ofReal I := by
    refine iSup_le fun p => ?_
    obtain ⟨n, u, hu, hus⟩ := p
    calc ∑ i ∈ range n, edist (f (u (i + 1))) (f (u i))
        = ENNReal.ofReal (∑ i ∈ range n, ‖f (u (i + 1)) - f (u i)‖) := by
          rw [ENNReal.ofReal_sum_of_nonneg fun i _ => norm_nonneg _]
          exact sum_congr rfl fun i _ => by rw [edist_dist, dist_eq_norm]
      _ ≤ ENNReal.ofReal I :=
          ENNReal.ofReal_le_ofReal (sum_norm_sub_le_integral hab hf hf' hu fun i _ => hus i)
  refine le_antisymm hle ?_
  -- the lower bound: suppose `V < I`
  by_contra hlt
  rw [not_le] at hlt
  have hV : eVariationOn f (Icc a b) ≠ ⊤ := (hlt.trans ENNReal.ofReal_lt_top).ne
  have hVI : (eVariationOn f (Icc a b)).toReal < I := by
    have := ENNReal.toReal_strict_mono ENNReal.ofReal_ne_top hlt
    rwa [ENNReal.toReal_ofReal (intervalIntegral.integral_nonneg hab fun x _ => norm_nonneg _)]
      at this
  set V := (eVariationOn f (Icc a b)).toReal with hVdef
  set ε := (I - V) / (2 * (b - a + 1)) with hε
  have hε0 : 0 < ε := by
    have : 0 < b - a + 1 := by linarith
    have : 0 < I - V := by linarith
    positivity
  -- Riemann sums of `‖f'‖` approximate `I`, and `f'` is uniformly continuous
  obtain ⟨δ₁, hδ₁, hR⟩ := dlmf_1_4_18 hab hnorm ε hε0
  obtain ⟨δ₂, hδ₂, hU⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hf') ε hε0
  -- a fine uniform partition
  rcases eq_or_lt_of_le hab with rfl | hab'
  · -- `a = b`: the integral is `0`, contradiction with `V ≥ 0`
    simp only [hI, intervalIntegral.integral_same] at hVI
    exact absurd hVI (not_lt.mpr ENNReal.toReal_nonneg)
  obtain ⟨m, hm⟩ := exists_nat_gt ((b - a) / min δ₁ δ₂)
  have hmin : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
  have hm0 : 0 < m := by
    have : 0 < (b - a) / min δ₁ δ₂ := div_pos (by linarith) hmin
    exact_mod_cast this.trans hm
  set P := uniformPartition hab' m hm0
  have hstep : ∀ j < P.n, P.x (j + 1) - P.x j < min δ₁ δ₂ := fun j _ => by
    simp only [P, uniformPartition]
    push_cast
    have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm0
    rw [show a + ((j : ℝ) + 1) * ((b - a) / m) - (a + j * ((b - a) / m)) = (b - a) / m by ring,
      div_lt_iff₀ hm']
    rw [div_lt_iff₀ hmin] at hm
    linarith
  -- the sum over the partition bounds `V` from below
  have hsumV : ∑ j ∈ range P.n, ‖f (P.x (j + 1)) - f (P.x j)‖ ≤ V := by
    set u : ℕ → ℝ := fun j => P.x (min j P.n) with hu
    have humono : Monotone u := fun i j hij =>
      P.le_of_le (min_le_min_right _ hij) (min_le_right _ _)
    have hus : ∀ i, u i ∈ Icc a b := fun i => P.mem_Icc (min_le_right _ _)
    have h1 := eVariationOn.sum_le (f := f) humono hus (n := P.n)
    rw [hVdef, ← ENNReal.ofReal_le_iff_le_toReal hV, ENNReal.ofReal_sum_of_nonneg
      fun i _ => norm_nonneg _]
    refine le_trans (le_of_eq ?_) h1
    refine sum_congr rfl fun j hj => ?_
    have hjn := mem_range.mp hj
    rw [edist_dist, dist_eq_norm, hu]
    simp only [min_eq_left hjn.le, min_eq_left (Nat.succ_le_of_lt hjn)]
  -- each increment is close to `‖f'(ξⱼ)‖ Δⱼ`
  have hterm : ∀ j ∈ range P.n, ‖f' (P.ξ j)‖ * (P.x (j + 1) - P.x j) - ε * (P.x (j + 1) - P.x j) ≤
      ‖f (P.x (j + 1)) - f (P.x j)‖ := by
    intro j hj
    have hjn := mem_range.mp hj
    have hlt := P.lt j hjn
    have htag := P.tag j hjn
    have hsub : Icc (P.x j) (P.x (j + 1)) ⊆ Icc a b :=
      Icc_subset_Icc (P.mem_Icc hjn.le).1 (P.mem_Icc hjn).2
    have hsub' : uIcc (P.x j) (P.x (j + 1)) ⊆ Icc a b := by rw [uIcc_of_le hlt.le]; exact hsub
    have hint : ∫ x in P.x j..P.x (j + 1), f' x = f (P.x (j + 1)) - f (P.x j) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hf x (hsub' hx))
        ((hf'.mono hsub').intervalIntegrable)
    have hconst : ∫ x in P.x j..P.x (j + 1), f' (P.ξ j) = (P.x (j + 1) - P.x j) • f' (P.ξ j) :=
      intervalIntegral.integral_const _
    have hdiff : ‖∫ x in P.x j..P.x (j + 1), (f' x - f' (P.ξ j))‖ ≤ ε * (P.x (j + 1) - P.x j) := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := P.x j) (b := P.x (j + 1))
        (f := fun x => f' x - f' (P.ξ j)) (C := ε) fun x hx => by
          rw [uIoc_of_le hlt.le] at hx
          have hx' := Ioc_subset_Icc_self hx
          have hd : dist x (P.ξ j) < δ₂ := by
            rw [Real.dist_eq, abs_lt]
            have := (hstep j hjn).trans_le (min_le_right _ _)
            constructor <;> linarith [hx'.1, hx'.2, htag.1, htag.2]
          have := hU x (hsub hx') (P.ξ j) (hsub htag) hd
          rw [dist_eq_norm] at this
          exact this.le
      rwa [abs_of_nonneg (sub_nonneg.mpr hlt.le)] at this
    rw [intervalIntegral.integral_sub (hf'.mono hsub').intervalIntegrable intervalIntegrable_const,
      hint, hconst] at hdiff
    have h1 := abs_norm_sub_norm_le (f (P.x (j + 1)) - f (P.x j))
      ((P.x (j + 1) - P.x j) • f' (P.ξ j))
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hlt.le), abs_le] at h1
    linarith [h1.1]
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, P.sum_lengths] at hsum
  have hRS := hR P fun j hj => (hstep j hj).trans_le (min_le_left _ _)
  rw [abs_lt] at hRS
  have hRS' : I - ε < P.riemannSum fun x => ‖f' x‖ := by linarith [hRS.1]
  have hmain : P.riemannSum (fun x => ‖f' x‖) - ε * (b - a) ≤ V := by
    rw [TaggedPartition.riemannSum]
    linarith
  have : I - ε * (b - a + 1) ≤ V := by linarith
  rw [hε] at this
  have hden : 0 < 2 * (b - a + 1) := by linarith
  have : (I - V) / (2 * (b - a + 1)) * (b - a + 1) = (I - V) / 2 := by field_simp
  linarith

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- The variation is unchanged by negating the function. -/
theorem eVariationOn_neg (f : ℝ → E) (s : Set ℝ) : eVariationOn (-f) s = eVariationOn f s := by
  unfold eVariationOn
  exact iSup_congr fun p => sum_congr rfl fun i _ => by simp only [Pi.neg_apply, edist_neg_neg]

/-- **DLMF 1.4.33.** For real `f` on a set `s` (the closure of the interval `(a, b)`), the total
variation `𝒱_{a,b}(f) = eVariationOn f s` is the supremum of `∑ |f(x_j) − f(x_{j−1})|` over all
finite sets of points `x₀ < x₁ < ⋯ < xₙ` of `s`. -/
theorem dlmf_1_4_33 (f : ℝ → ℝ) (s : Set ℝ) :
    eVariationOn f s =
      ⨆ p : (n : ℕ) × {u : ℕ → ℝ // StrictMonoOn u (Set.Iic n) ∧ ∀ i ∈ Set.Iic n, u i ∈ s},
        ENNReal.ofReal (∑ j ∈ range p.1, |f (p.2.1 (j + 1)) - f (p.2.1 j)|) := by
  rw [eVariationOn.eVariationOn_eq_strictMonoOn]
  refine iSup_congr fun p => ?_
  rw [ENNReal.ofReal_sum_of_nonneg fun i _ => abs_nonneg _]
  exact sum_congr rfl fun i _ => by rw [edist_dist, Real.dist_eq]

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- DLMF §1.4(v): the closure of `(a, b)` is `(a, b)` with the finite endpoints added, so
`𝒱_{a,b}(f)` is the variation on `[a, b]`, `[a, ∞)`, `(−∞, b]` or `ℝ`. -/
theorem dlmf_1_4_v_variation_closure (f : ℝ → E) {a b : ℝ} (hab : a < b) :
    eVariationOn f (closure (Ioo a b)) = eVariationOn f (Icc a b) ∧
      eVariationOn f (closure (Ioi a)) = eVariationOn f (Ici a) ∧
      eVariationOn f (closure (Iio b)) = eVariationOn f (Iic b) := by
  rw [closure_Ioo hab.ne, closure_Ioi, closure_Iio]
  exact ⟨rfl, rfl, rfl⟩

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- DLMF §1.4(v): `f` is of bounded variation on `(a, b)` when `𝒱_{a,b}(f) < ∞`. -/
theorem dlmf_1_4_v_boundedVariationOn_iff (f : ℝ → E) (s : Set ℝ) :
    BoundedVariationOn f s ↔ eVariationOn f s < ⊤ :=
  lt_top_iff_ne_top.symm

/-- Bounded variation of real `f`, in terms of the sums of DLMF 1.4.33: they are bounded. -/
theorem dlmf_1_4_v_boundedVariationOn_iff_bdd (f : ℝ → ℝ) (s : Set ℝ) :
    BoundedVariationOn f s ↔ ∃ M : ℝ, ∀ (n : ℕ) (u : ℕ → ℝ), StrictMonoOn u (Set.Iic n) →
      (∀ i ∈ Set.Iic n, u i ∈ s) → ∑ j ∈ range n, |f (u (j + 1)) - f (u j)| ≤ M := by
  constructor
  · intro h
    refine ⟨(eVariationOn f s).toReal, fun n u hu hus => ?_⟩
    rw [← ENNReal.ofReal_le_iff_le_toReal h, dlmf_1_4_33]
    exact le_iSup (fun p : (n : ℕ) ×
      {u : ℕ → ℝ // StrictMonoOn u (Set.Iic n) ∧ ∀ i ∈ Set.Iic n, u i ∈ s} =>
        ENNReal.ofReal (∑ j ∈ range p.1, |f (p.2.1 (j + 1)) - f (p.2.1 j)|)) ⟨n, u, hu, hus⟩
  · rintro ⟨M, hM⟩
    show eVariationOn f s ≠ ⊤
    rw [dlmf_1_4_33]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (iSup_le fun p => ENNReal.ofReal_le_ofReal (hM p.1 p.2.1 p.2.2.1 p.2.2.2))

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- DLMF's `g(x) = 𝒱_{a,x}(f)`: the variation of `f` on the part of `s` at or to the left of `x`
(`a` being the left end of `s`, possibly `−∞`).  When `a` is the least element of `s` this is
Mathlib's `variationOnFromTo f s a x`. -/
noncomputable def leftVariation (f : ℝ → E) (s : Set ℝ) (x : ℝ) : ℝ :=
  (eVariationOn f (s ∩ Iic x)).toReal

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem leftVariation_eq_variationOnFromTo {f : ℝ → E} {s : Set ℝ} {a : ℝ} (ha : IsLeast s a)
    {x : ℝ} (hx : x ∈ s) : leftVariation f s x = variationOnFromTo f s a x := by
  rw [leftVariation, variationOnFromTo.eq_of_le f s (ha.2 hx)]
  congr 2
  ext y
  simp only [mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
  exact ⟨fun h => ⟨h.1, ha.2 h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩

/-- DLMF §1.4(v), the Jordan decomposition: if `f` is of bounded variation on `s`, then
`g(x) = 𝒱_{a,x}(f)` and `h(x) = 𝒱_{a,x}(f) − f(x)` are nondecreasing bounded functions on `s`,
and `f = g − h`. -/
theorem dlmf_1_4_v_jordan {f : ℝ → ℝ} {s : Set ℝ} (hf : BoundedVariationOn f s) :
    MonotoneOn (leftVariation f s) s ∧ MonotoneOn (leftVariation f s - f) s ∧
      (∃ C, ∀ x ∈ s, |leftVariation f s x| ≤ C) ∧
      (∃ C, ∀ x ∈ s, |(leftVariation f s - f) x| ≤ C) ∧
      ∀ x, f x = leftVariation f s x - (leftVariation f s - f) x := by
  have hfin : ∀ t ⊆ s, eVariationOn f t ≠ ⊤ := fun t ht =>
    ne_top_of_le_ne_top hf (eVariationOn.mono f ht)
  -- the variation up to `y` dominates the variation up to `x ∈ s` plus that on `[x, y]`
  have hsplit : ∀ x ∈ s, ∀ y, x ≤ y →
      leftVariation f s x + (eVariationOn f (s ∩ Icc x y)).toReal ≤ leftVariation f s y := by
    intro x hx y hxy
    have h1 := eVariationOn.add_le_union f (s := s ∩ Iic x) (t := s ∩ Icc x y)
      fun u hu v hv => hu.2.trans hv.2.1
    have hU : (s ∩ Iic x) ∪ (s ∩ Icc x y) ⊆ s ∩ Iic y := by
      rintro z (⟨hz, hzx⟩ | ⟨hz, hzxy⟩)
      · exact ⟨hz, hzx.trans hxy⟩
      · exact ⟨hz, hzxy.2⟩
    rw [leftVariation, leftVariation,
      ← ENNReal.toReal_add (hfin _ inter_subset_left) (hfin _ inter_subset_left)]
    exact ENNReal.toReal_mono (hfin _ inter_subset_left) (h1.trans (eVariationOn.mono f hU))
  have hbdd : ∀ x, |leftVariation f s x| ≤ (eVariationOn f s).toReal := fun x => by
    rw [leftVariation, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_mono hf (eVariationOn.mono f inter_subset_left)
  refine ⟨fun x hx y _ hxy =>
    le_trans (le_add_of_nonneg_right ENNReal.toReal_nonneg) (hsplit x hx y hxy), ?_,
    ⟨_, fun x _ => hbdd x⟩, ?_, fun x => by simp⟩
  · intro x hx y hy hxy
    have hd := eVariationOn.edist_le f (s := s ∩ Icc x y) ⟨hx, le_rfl, hxy⟩ ⟨hy, hxy, le_rfl⟩
    rw [edist_dist, Real.dist_eq] at hd
    have hd' : |f x - f y| ≤ (eVariationOn f (s ∩ Icc x y)).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal (hfin _ inter_subset_left)).mp hd
    have := hsplit x hx y hxy
    simp only [Pi.sub_apply]
    linarith [neg_abs_le (f x - f y)]
  · rcases s.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
    · exact ⟨0, fun x hx => hx.elim⟩
    refine ⟨2 * (eVariationOn f s).toReal + |f x₀|, fun x hx => ?_⟩
    have h2 := hf.dist_le hx hx₀
    rw [Real.dist_eq] at h2
    simp only [Pi.sub_apply]
    calc |leftVariation f s x - f x| ≤ |leftVariation f s x| + |f x| := abs_sub _ _
      _ ≤ _ := by linarith [hbdd x, abs_sub_abs_le_abs_sub (f x) (f x₀)]

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- **Olver §11.3**: the subdivision `x₀ = a`, `x₁ = b` gives `𝒱_{a,b}(f) ≥ ‖f(b) − f(a)‖`. -/
theorem olver_11_3 (f : ℝ → E) {a b : ℝ} (hab : a ≤ b) :
    ENNReal.ofReal ‖f b - f a‖ ≤ eVariationOn f (Icc a b) := by
  rw [← dist_eq_norm, ← edist_dist]
  exact eVariationOn.edist_le f (Set.right_mem_Icc.mpr hab) (Set.left_mem_Icc.mpr hab)

/-- **Olver (11.01)**: equality holds when `f` is monotonic on `[a, b]`. -/
theorem olver_11_01 {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : MonotoneOn f (Icc a b) ∨ AntitoneOn f (Icc a b)) :
    eVariationOn f (Icc a b) = ENNReal.ofReal |f b - f a| := by
  have ha := Set.left_mem_Icc.mpr hab
  have hb := Set.right_mem_Icc.mpr hab
  rcases hf with hf | hf
  · rw [abs_of_nonneg (sub_nonneg.mpr (hf ha hb hab))]
    have := hf.eVariationOn_eq ha hb
    rwa [Set.inter_self] at this
  · have hneg : MonotoneOn (-f) (Icc a b) := fun x hx y hy hxy => neg_le_neg (hf hx hy hxy)
    rw [← eVariationOn_neg, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (hf ha hb hab))]
    have := hneg.eVariationOn_eq ha hb
    rwa [Set.inter_self, Pi.neg_apply, Pi.neg_apply, neg_sub_neg] at this

/-- **Olver §11.3**: subdividing `[a, b]` at the maxima and minima of `f`, so that `f` is
monotonic on each subinterval `[x_j, x_{j+1}]`, gives `𝒱_{a,b}(f) = ∑ |f(x_{j+1}) − f(x_j)|`. -/
theorem olver_11_3_subdivision {f : ℝ → ℝ} {x : ℕ → ℝ} (hx : Monotone x) {n : ℕ}
    (hf : ∀ j < n, MonotoneOn f (Icc (x j) (x (j + 1))) ∨ AntitoneOn f (Icc (x j) (x (j + 1)))) :
    eVariationOn f (Icc (x 0) (x n)) =
      ENNReal.ofReal (∑ j ∈ range n, |f (x (j + 1)) - f (x j)|) := by
  have h := eVariationOn.sum f hx (s := Icc (x 0) (x n)) (n := n)
    fun i _ hin => ⟨hx (Nat.zero_le i), hx hin.le⟩
  rw [Set.inter_self] at h
  rw [← h, ENNReal.ofReal_sum_of_nonneg fun i _ => abs_nonneg _]
  refine sum_congr rfl fun j hj => ?_
  have hjn := mem_range.mp hj
  rw [inter_eq_right.mpr (Icc_subset_Icc (hx (Nat.zero_le j)) (hx hjn)),
    olver_11_01 (hx (Nat.le_succ j)) (hf j hjn)]

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- **Olver Ex. 11.1**: `𝒱(f + g) ≤ 𝒱(f) + 𝒱(g)`. -/
theorem olver_ex_11_1_add (f g : ℝ → E) (s : Set ℝ) :
    eVariationOn (f + g) s ≤ eVariationOn f s + eVariationOn g s := by
  refine iSup_le fun p => ?_
  obtain ⟨n, u, hu, hus⟩ := p
  calc ∑ i ∈ range n, edist ((f + g) (u (i + 1))) ((f + g) (u i))
      ≤ ∑ i ∈ range n, (edist (f (u (i + 1))) (f (u i)) + edist (g (u (i + 1))) (g (u i))) :=
        sum_le_sum fun i _ => edist_add_add_le _ _ _ _
    _ = ∑ i ∈ range n, edist (f (u (i + 1))) (f (u i)) +
          ∑ i ∈ range n, edist (g (u (i + 1))) (g (u i)) := sum_add_distrib
    _ ≤ _ := add_le_add (eVariationOn.sum_le hu hus) (eVariationOn.sum_le hu hus)

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- **Olver Ex. 11.1**: `𝒱(f) ≥ 𝒱(‖f‖)`, since the norm is `1`-Lipschitz. -/
theorem olver_ex_11_1_norm (f : ℝ → E) (s : Set ℝ) :
    eVariationOn (fun x => ‖f x‖) s ≤ eVariationOn f s := by
  have := (lipschitzWith_one_norm (E := E)).lipschitzOnWith (s := univ)
    |>.comp_eVariationOn_le (g := f) (s := s) (mapsTo_univ _ _)
  rw [ENNReal.coe_one, one_mul] at this
  exact this

/-- **Olver Ex. 11.1** for real `f`: `𝒱(|f|) ≤ 𝒱(f)`. -/
theorem olver_ex_11_1_abs (f : ℝ → ℝ) (s : Set ℝ) :
    eVariationOn (fun x => |f x|) s ≤ eVariationOn f s := by
  simpa only [Real.norm_eq_abs] using olver_ex_11_1_norm f s

/-- An open order-connected subset of `ℝ` (an open interval, possibly unbounded) is the increasing
union of compact intervals `[c n, d n]` it contains, built from an enumeration of its rational
points. -/
theorem exists_Icc_exhaustion {I : Set ℝ} (hI : IsOpen I) (hI' : I.OrdConnected)
    (hne : I.Nonempty) : ∃ c d : ℕ → ℝ, Antitone c ∧ Monotone d ∧ (∀ n, c n ≤ d n) ∧
      (∀ n, Icc (c n) (d n) ⊆ I) ∧ ⋃ n, Icc (c n) (d n) = I := by
  -- every point of `I` has rational points of `I` on both sides
  have hrat : ∀ x ∈ I, ∃ r₁ r₂ : ℚ, (r₁ : ℝ) ∈ I ∩ range ((↑) : ℚ → ℝ) ∧
      (r₂ : ℝ) ∈ I ∩ range ((↑) : ℚ → ℝ) ∧ (r₁ : ℝ) ≤ x ∧ x ≤ r₂ := by
    intro x hx
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hI.mem_nhds hx)
    obtain ⟨r₁, hr₁⟩ := exists_rat_btwn (show x - ε < x by linarith)
    obtain ⟨r₂, hr₂⟩ := exists_rat_btwn (show x < x + ε by linarith)
    refine ⟨r₁, r₂, ⟨hball ?_, r₁, rfl⟩, ⟨hball ?_, r₂, rfl⟩, hr₁.2.le, hr₂.1.le⟩ <;>
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] <;> constructor <;> linarith
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨r₀, -, hr₀, -, -, -⟩ := hrat x₀ hx₀
  obtain ⟨q, hq⟩ := ((countable_range _).mono (inter_subset_right (s := I))).exists_eq_range
    ⟨_, hr₀⟩
  have hqI : ∀ n, q n ∈ I := fun n => by
    have : q n ∈ I ∩ range ((↑) : ℚ → ℝ) := by rw [hq]; exact mem_range_self n
    exact this.1
  have hne' : ∀ n, (range (n + 1)).Nonempty := fun n => ⟨0, mem_range.mpr n.succ_pos⟩
  have hsub : ∀ n, Icc ((range (n + 1)).inf' (hne' n) q) ((range (n + 1)).sup' (hne' n) q) ⊆ I :=
    fun n => by
      obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' (hne' n) q
      obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup' (hne' n) q
      rw [hi, hj]
      exact hI'.out (hqI i) (hqI j)
  refine ⟨fun n => (range (n + 1)).inf' (hne' n) q, fun n => (range (n + 1)).sup' (hne' n) q,
    fun m n hmn => Finset.inf'_mono q (range_subset_range.mpr (by omega)) (hne' m),
    fun m n hmn => Finset.sup'_mono q (range_subset_range.mpr (by omega)) (hne' m),
    fun n => (Finset.inf'_le q (mem_range.mpr n.succ_pos)).trans
      (Finset.le_sup' q (mem_range.mpr n.succ_pos)), hsub,
    subset_antisymm (iUnion_subset hsub) fun x hx => ?_⟩
  obtain ⟨r₁, r₂, hr₁, hr₂, h₁, h₂⟩ := hrat x hx
  rw [hq] at hr₁ hr₂
  obtain ⟨i, hi⟩ := hr₁
  obtain ⟨j, hj⟩ := hr₂
  refine mem_iUnion.mpr ⟨max i j, ?_, ?_⟩
  · calc (range (max i j + 1)).inf' (hne' _) q ≤ q i :=
        Finset.inf'_le q (mem_range.mpr (by omega))
      _ ≤ x := hi ▸ h₁
  · calc x ≤ q j := hj ▸ h₂
      _ ≤ (range (max i j + 1)).sup' (hne' _) q := Finset.le_sup' q (mem_range.mpr (by omega))

/-- **DLMF 1.4.34, Olver §11.4** on an open interval `I` (bounded or not): if `f` has continuous
derivative `f'` on `I` and `‖f'‖` is integrable over `I`, then `𝒱_I(f) = ∫_I ‖f'(x)‖ dx`.  The
upper bound is Olver's `∑ ‖f(x_{s+1}) − f(x_s)‖ = ∑ ‖∫ f'‖ ≤ ∫ ‖f'‖`; the lower bound (11.03)
is `𝒱_I(f) ≥ 𝒱_{c,d}(f) = ∫_c^d ‖f'‖` for arbitrary `c ≤ d` in `I`, letting `[c, d]` exhaust
`I`. -/
theorem eVariationOn_eq_integral_of_isOpen {f f' : ℝ → E} {I : Set ℝ} (hI : IsOpen I)
    (hI' : I.OrdConnected) (hf : ∀ x ∈ I, HasDerivAt f (f' x) x) (hf' : ContinuousOn f' I)
    (hint : IntegrableOn (fun x => ‖f' x‖) I) :
    eVariationOn f I = ENNReal.ofReal (∫ x in I, ‖f' x‖) := by
  rcases I.eq_empty_or_nonempty with rfl | hne
  · simp
  apply le_antisymm
  · refine iSup_le fun p => ?_
    obtain ⟨n, u, hu, hus⟩ := p
    have hsub : Icc (u 0) (u n) ⊆ I := hI'.out (hus 0) (hus n)
    calc ∑ i ∈ range n, edist (f (u (i + 1))) (f (u i))
        = ENNReal.ofReal (∑ i ∈ range n, ‖f (u (i + 1)) - f (u i)‖) := by
          rw [ENNReal.ofReal_sum_of_nonneg fun i _ => norm_nonneg _]
          exact sum_congr rfl fun i _ => by rw [edist_dist, dist_eq_norm]
      _ ≤ ENNReal.ofReal (∫ x in u 0..u n, ‖f' x‖) :=
          ENNReal.ofReal_le_ofReal (sum_norm_sub_le_integral (hu (Nat.zero_le n))
            (fun x hx => hf x (hsub hx)) (hf'.mono hsub) hu
            fun i hi => ⟨hu (Nat.zero_le i), hu hi⟩)
      _ ≤ ENNReal.ofReal (∫ x in I, ‖f' x‖) := by
          rw [intervalIntegral.integral_of_le (hu (Nat.zero_le n))]
          exact ENNReal.ofReal_le_ofReal (setIntegral_mono_set hint
            (ae_of_all _ fun x => norm_nonneg _) (ae_of_all _ (Ioc_subset_Icc_self.trans hsub)))
  · obtain ⟨c, d, hc, hd, hcd, hsub, hU⟩ := exists_Icc_exhaustion hI hI' hne
    have hlim : Tendsto (fun n => ∫ x in Icc (c n) (d n), ‖f' x‖) atTop
        (𝓝 (∫ x in I, ‖f' x‖)) := by
      have := tendsto_setIntegral_of_monotone (μ := volume) (f := fun x => ‖f' x‖)
        (s := fun n => Icc (c n) (d n)) (fun n => measurableSet_Icc)
        (fun m n hmn => Icc_subset_Icc (hc hmn) (hd hmn)) (by rw [hU]; exact hint)
      rwa [hU] at this
    refine le_of_tendsto' (ENNReal.tendsto_ofReal hlim) fun n => ?_
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (hcd n),
      ← olver_11_02 (hcd n) (fun x hx => hf x (hsub n hx)) (hf'.mono (hsub n))]
    exact eVariationOn.mono f (hsub n)

/-- **DLMF 1.4.34** for a bounded interval: if `f` is continuous on `[a, b]`, `f'` is continuous
on `(a, b)` and `∫_a^b ‖f'‖` exists, then `𝒱_{a,b}(f) = ∫_a^b ‖f'(x)‖ dx`. -/
theorem dlmf_1_4_34 {f f' : ℝ → E} {a b : ℝ} (hab : a < b) (hfc : ContinuousOn f (Icc a b))
    (hf : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) (hf' : ContinuousOn f' (Ioo a b))
    (hint : IntegrableOn (fun x => ‖f' x‖) (Ioo a b)) :
    eVariationOn f (Icc a b) = ENNReal.ofReal (∫ x in a..b, ‖f' x‖) := by
  rw [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo,
    ← eVariationOn_eq_integral_of_isOpen isOpen_Ioo ordConnected_Ioo hf hf' hint]
  -- the variation is unchanged by adding the endpoints, by continuity of `f` there
  have hb : eVariationOn f (Ioo a b) = eVariationOn f (Ioc a b) := by
    have h := eVariationOn.eVariationOn_inter_Iio_eq_inter_Iic_of_continuousWithinAt (f := f)
      (s := Ioi a) (a := b) (by rw [Ioi_inter_Iio, nhdsWithin_Ioo_eq_nhdsLT hab]; infer_instance)
      (by
        rw [Ioi_inter_Iic]
        exact (hfc b (Set.right_mem_Icc.mpr hab.le)).mono Ioc_subset_Icc_self)
    rwa [Ioi_inter_Iio, Ioi_inter_Iic] at h
  have ha : eVariationOn f (Ioc a b) = eVariationOn f (Icc a b) :=
    eVariationOn.eVariationOn_Ioc_eq_Icc_of_continuousWithinAt
      ((hfc a (Set.left_mem_Icc.mpr hab.le)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hab))
  rw [← ha, ← hb]

/-- **DLMF 1.4.34** on `[a, ∞)`: `𝒱_{a,∞}(f) = ∫_a^∞ ‖f'(x)‖ dx`. -/
theorem dlmf_1_4_34_Ioi {f f' : ℝ → E} {a : ℝ} (hfc : ContinuousWithinAt f (Ici a) a)
    (hf : ∀ x ∈ Ioi a, HasDerivAt f (f' x) x) (hf' : ContinuousOn f' (Ioi a))
    (hint : IntegrableOn (fun x => ‖f' x‖) (Ioi a)) :
    eVariationOn f (Ici a) = ENNReal.ofReal (∫ x in Ioi a, ‖f' x‖) := by
  rw [← eVariationOn_eq_integral_of_isOpen isOpen_Ioi ordConnected_Ioi hf hf' hint]
  have h := eVariationOn.eVariationOn_inter_Ioi_eq_inter_Ici_of_continuousWithinAt (f := f)
    (s := univ) (a := a) (by rw [univ_inter]; infer_instance) (by rwa [univ_inter])
  rwa [univ_inter, univ_inter, eq_comm] at h

/-- **DLMF 1.4.34** on `(−∞, b]`: `𝒱_{−∞,b}(f) = ∫_{−∞}^b ‖f'(x)‖ dx`. -/
theorem dlmf_1_4_34_Iio {f f' : ℝ → E} {b : ℝ} (hfc : ContinuousWithinAt f (Iic b) b)
    (hf : ∀ x ∈ Iio b, HasDerivAt f (f' x) x) (hf' : ContinuousOn f' (Iio b))
    (hint : IntegrableOn (fun x => ‖f' x‖) (Iio b)) :
    eVariationOn f (Iic b) = ENNReal.ofReal (∫ x in Iio b, ‖f' x‖) := by
  rw [← eVariationOn_eq_integral_of_isOpen isOpen_Iio ordConnected_Iio hf hf' hint]
  have h := eVariationOn.eVariationOn_inter_Iio_eq_inter_Iic_of_continuousWithinAt (f := f)
    (s := univ) (a := b) (by rw [univ_inter]; infer_instance) (by rwa [univ_inter])
  rwa [univ_inter, univ_inter, eq_comm] at h

/-- **DLMF 1.4.34** on `(−∞, ∞)`: `𝒱_{−∞,∞}(f) = ∫_{−∞}^∞ ‖f'(x)‖ dx`. -/
theorem dlmf_1_4_34_univ {f f' : ℝ → E} (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f')
    (hint : Integrable fun x => ‖f' x‖) :
    eVariationOn f univ = ENNReal.ofReal (∫ x, ‖f' x‖) := by
  rw [← Measure.restrict_univ (μ := volume)]
  exact eVariationOn_eq_integral_of_isOpen isOpen_univ ordConnected_univ (fun x _ => hf x)
    hf'.continuousOn hint.integrableOn

/-- **DLMF 1.4.34** for real `f` on a compact interval, with `|f'|` in place of `‖f'‖`. -/
theorem dlmf_1_4_34_real {f f' : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hfc : ContinuousOn f (Icc a b))
    (hf : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) (hf' : ContinuousOn f' (Ioo a b))
    (hint : IntegrableOn (fun x => |f' x|) (Ioo a b)) :
    eVariationOn f (Icc a b) = ENNReal.ofReal (∫ x in a..b, |f' x|) := by
  simpa only [Real.norm_eq_abs] using
    dlmf_1_4_34 hab hfc hf hf' (by simpa only [Real.norm_eq_abs] using hint)

/-- **Olver §11.5, DLMF §1.4(v)**: for a complex function `f` of the real variable `x`, the
variation is given by (11.02) / (1.4.34): `𝒱_{a,b}(f) = ∫_a^b |f'(x)| dx`. -/
theorem olver_11_5 {f f' : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x) (hf' : ContinuousOn f' (Icc a b)) :
    eVariationOn f (Icc a b) = ENNReal.ofReal (∫ x in a..b, ‖f' x‖) :=
  olver_11_02 hab hf hf'

/-- DLMF's extension of `𝒱_{a,b}(f)` by (1.4.34) to arbitrary real `a, b` (not necessarily
`a < b`) and to complex (here `E`-valued) `f`: `𝒱_{a,b}(f) = ∫_a^b ‖f'(x)‖ dx`. -/
noncomputable def variationIntegral (f : ℝ → E) (a b : ℝ) : ℝ :=
  ∫ x in a..b, ‖deriv f x‖

omit [CompleteSpace E] in
/-- Reversing the endpoints negates the extended variation. -/
theorem variationIntegral_symm (f : ℝ → E) (a b : ℝ) :
    variationIntegral f b a = -variationIntegral f a b :=
  intervalIntegral.integral_symm a b

/-- For `a ≤ b` and continuously differentiable `f`, the extended variation is the total
variation of `f` on `[a, b]`. -/
theorem variationIntegral_eq_toReal {f : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, DifferentiableAt ℝ f x) (hf' : ContinuousOn (deriv f) (Icc a b)) :
    variationIntegral f a b = (eVariationOn f (Icc a b)).toReal := by
  rw [variationIntegral, olver_11_02 hab (fun x hx => (hf x hx).hasDerivAt) hf',
    ENNReal.toReal_ofReal (intervalIntegral.integral_nonneg hab fun x _ => norm_nonneg _)]

/-- Splitting a sum over `range (2n)` into consecutive pairs. -/
theorem sum_range_two_mul (g : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ range (2 * n), g k = ∑ i ∈ range n, (g (2 * i) + g (2 * i + 1)) := by
  induction n with
  | zero => simp
  | succ n ih => rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sum_range_succ, sum_range_succ,
      sum_range_succ, ih, add_assoc]

/-- **Olver Ex. 11.1**, the equality case: for real continuous `f` on an interval `s`,
`𝒱(|f|) = 𝒱(f)`.  Refining a subdivision by a zero of `f` (intermediate value theorem) between
any two consecutive points where `f` changes sign makes the `|f|`-sum equal the `f`-sum. -/
theorem olver_ex_11_1_abs_eq {f : ℝ → ℝ} {s : Set ℝ} (hs : s.OrdConnected)
    (hf : ContinuousOn f s) : eVariationOn (fun x => |f x|) s = eVariationOn f s := by
  refine le_antisymm (olver_ex_11_1_abs f s) (iSup_le fun p => ?_)
  obtain ⟨n, u, hu, hus⟩ := p
  -- a point `z i` of `[u i, u (i+1)]`: a zero of `f` when `f` changes sign, else `u i`
  have hz : ∀ i, ∃ z ∈ Icc (u i) (u (i + 1)),
      (f (u i) * f (u (i + 1)) ≤ 0 → f z = 0) ∧ (0 < f (u i) * f (u (i + 1)) → z = u i) := by
    intro i
    have hsub : Icc (u i) (u (i + 1)) ⊆ s := hs.out (hus i) (hus (i + 1))
    by_cases h : f (u i) * f (u (i + 1)) ≤ 0
    · rcases mul_nonpos_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · obtain ⟨z, hz, hfz⟩ := intermediate_value_Icc' (hu (Nat.le_succ i)) (hf.mono hsub) ⟨h2, h1⟩
        exact ⟨z, hz, fun _ => hfz, fun h' => absurd h' (not_lt.mpr h)⟩
      · obtain ⟨z, hz, hfz⟩ := intermediate_value_Icc (hu (Nat.le_succ i)) (hf.mono hsub) ⟨h1, h2⟩
        exact ⟨z, hz, fun _ => hfz, fun h' => absurd h' (not_lt.mpr h)⟩
    · exact ⟨u i, Set.left_mem_Icc.mpr (hu (Nat.le_succ i)), fun h' => absurd h' h, fun _ => rfl⟩
  choose z hzmem hz0 hz1 using hz
  -- the refined sequence `u 0, z 0, u 1, z 1, …`, kept opaque
  obtain ⟨v, hv0, hv1⟩ : ∃ v : ℕ → ℝ, (∀ m, v (2 * m) = u m) ∧ ∀ m, v (2 * m + 1) = z m :=
    ⟨fun k => if k % 2 = 0 then u (k / 2) else z (k / 2), fun m => by
      simp only [Nat.mul_mod_right, ↓reduceIte, Nat.mul_div_cancel_left _ two_pos], fun m => by
      have h1 : (2 * m + 1) % 2 = 1 := by omega
      have h2 : (2 * m + 1) / 2 = m := by omega
      simp only [h1, h2, one_ne_zero, ↓reduceIte]⟩
  have hv0' : ∀ m, v (2 * m + 1 + 1) = u (m + 1) := fun m => by
    rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring, hv0]
  have hvmono : Monotone v := by
    refine monotone_nat_of_le_succ fun k => ?_
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' k
    · rw [hv0, hv1]; exact (hzmem m).1
    · rw [hv1, hv0']; exact (hzmem m).2
  have hvs : ∀ k, v k ∈ s := fun k => by
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' k
    · rw [hv0]; exact hus m
    · rw [hv1]; exact hs.out (hus m) (hus (m + 1)) (hzmem m)
  -- each original increment is at most the two refined ones
  have hterm : ∀ i, |f (u (i + 1)) - f (u i)| ≤
      |(|f (z i)| - |f (u i)|)| + |(|f (u (i + 1))| - |f (z i)|)| := by
    intro i
    by_cases h : f (u i) * f (u (i + 1)) ≤ 0
    · rw [hz0 i h, abs_zero, zero_sub, sub_zero, abs_neg, abs_abs, abs_abs]
      rcases mul_nonpos_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        cases abs_cases (f (u (i + 1)) - f (u i)) <;> cases abs_cases (f (u i)) <;>
        cases abs_cases (f (u (i + 1))) <;> linarith
    · rw [hz1 i (not_le.mp h), sub_self, abs_zero, zero_add]
      rcases mul_pos_iff.mp (not_le.mp h) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        cases abs_cases (f (u (i + 1)) - f (u i)) <;> cases abs_cases (f (u i)) <;>
        cases abs_cases (f (u (i + 1))) <;> cases abs_cases (|f (u (i + 1))| - |f (u i)|) <;>
        linarith
  calc ∑ i ∈ range n, edist (f (u (i + 1))) (f (u i))
      = ENNReal.ofReal (∑ i ∈ range n, |f (u (i + 1)) - f (u i)|) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun i _ => abs_nonneg _]
        exact sum_congr rfl fun i _ => by rw [edist_dist, Real.dist_eq]
    _ ≤ ENNReal.ofReal (∑ k ∈ range (2 * n), |(|f (v (k + 1))| - |f (v k)|)|) := by
        rw [sum_range_two_mul]
        refine ENNReal.ofReal_le_ofReal (sum_le_sum fun i _ => ?_)
        rw [hv0, hv1, hv0']
        exact hterm i
    _ = ∑ k ∈ range (2 * n), edist |f (v (k + 1))| |f (v k)| := by
        rw [ENNReal.ofReal_sum_of_nonneg fun i _ => abs_nonneg _]
        exact sum_congr rfl fun i _ => by rw [edist_dist, Real.dist_eq]
    _ ≤ eVariationOn (fun x => |f x|) s := eVariationOn.sum_le (f := fun x => |f x|) hvmono hvs

/-- The variation of a nondecreasing function on `(−∞, b]` with limit `L` at `−∞` is
`f(b) − L`. -/
theorem eVariationOn_Iic_of_monotoneOn {f : ℝ → ℝ} {b L : ℝ} (hf : MonotoneOn f (Iic b))
    (hL : Tendsto f atBot (𝓝 L)) : eVariationOn f (Iic b) = ENNReal.ofReal (f b - L) := by
  have hLle : ∀ x ≤ b, L ≤ f x := by
    intro x hx
    have hg : Monotone fun y => f (min y b) := fun y z hyz =>
      hf (mem_Iic.mpr (min_le_right _ _)) (mem_Iic.mpr (min_le_right _ _)) (min_le_min_right _ hyz)
    have hg' : Tendsto (fun y => f (min y b)) atBot (𝓝 L) := by
      refine hL.congr' ?_
      filter_upwards [eventually_le_atBot b] with y hy
      rw [min_eq_left hy]
    have := hg.le_of_tendsto hg' x
    rwa [min_eq_left hx] at this
  apply le_antisymm
  · rw [eVariationOn.eq_biSup_inter_Icc]
    refine iSup₂_le fun p hp => ?_
    obtain ⟨h1, h2, _⟩ := hp
    rw [hf.eVariationOn_eq h1 h2]
    exact ENNReal.ofReal_le_ofReal (by linarith [hf h2 (mem_Iic.mpr le_rfl) h2, hLle _ h1])
  · have hV : ∀ c ≤ b, ENNReal.ofReal (f b - f c) ≤ eVariationOn f (Iic b) := fun c hc => by
      rw [← hf.eVariationOn_eq (mem_Iic.mpr hc) (mem_Iic.mpr le_rfl)]
      exact eVariationOn.mono f inter_subset_left
    exact le_of_tendsto (ENNReal.tendsto_ofReal (tendsto_const_nhds.sub hL))
      (by filter_upwards [eventually_le_atBot b] with c hc using hV c hc)

/-- The variation of a nonincreasing function on `[a, ∞)` with limit `L` at `∞` is `f(a) − L`. -/
theorem eVariationOn_Ici_of_antitoneOn {f : ℝ → ℝ} {a L : ℝ} (hf : AntitoneOn f (Ici a))
    (hL : Tendsto f atTop (𝓝 L)) : eVariationOn f (Ici a) = ENNReal.ofReal (f a - L) := by
  have hLle : ∀ x, a ≤ x → L ≤ f x := by
    intro x hx
    have hg : Antitone fun y => f (max y a) := fun y z hyz =>
      hf (mem_Ici.mpr (le_max_right _ _)) (mem_Ici.mpr (le_max_right _ _)) (max_le_max_right _ hyz)
    have hg' : Tendsto (fun y => f (max y a)) atTop (𝓝 L) := by
      refine hL.congr' ?_
      filter_upwards [eventually_ge_atTop a] with y hy
      rw [max_eq_left hy]
    have := hg.le_of_tendsto hg' x
    rwa [max_eq_left hx] at this
  have hneg : MonotoneOn (-f) (Ici a) := fun x hx y hy hxy => neg_le_neg (hf hx hy hxy)
  apply le_antisymm
  · rw [eVariationOn.eq_biSup_inter_Icc]
    refine iSup₂_le fun p hp => ?_
    obtain ⟨h1, h2, _⟩ := hp
    rw [← eVariationOn_neg, hneg.eVariationOn_eq h1 h2, Pi.neg_apply, Pi.neg_apply]
    exact ENNReal.ofReal_le_ofReal (by linarith [hf (mem_Ici.mpr le_rfl) h1 h1, hLle _ h2])
  · have hV : ∀ c, a ≤ c → ENNReal.ofReal (f a - f c) ≤ eVariationOn f (Ici a) := fun c hc => by
      rw [← eVariationOn_neg, ← neg_sub_neg (f c) (f a), ← Pi.neg_apply f, ← Pi.neg_apply f,
        ← hneg.eVariationOn_eq (mem_Ici.mpr le_rfl) (mem_Ici.mpr hc)]
      exact eVariationOn.mono _ inter_subset_left
    exact le_of_tendsto (ENNReal.tendsto_ofReal (tendsto_const_nhds.sub hL))
      (by filter_upwards [eventually_ge_atTop a] with c hc using hV c hc)

/-- **Olver Ex. 11.2 (ii)**: the step function `f = 0` (`x < 0`), `1/2` (`x = 0`), `1`
(`x > 0`) has `𝒱_{−1,1}(f) = 1`. -/
theorem olver_ex_11_2_ii :
    eVariationOn (fun x : ℝ => if x < 0 then (0 : ℝ) else if x = 0 then 1 / 2 else 1)
      (Icc (-1) 1) = 1 := by
  have hmono : MonotoneOn (fun x : ℝ => if x < 0 then (0 : ℝ) else if x = 0 then 1 / 2 else 1)
      (Icc (-1) 1) := by
    intro x _ y _ hxy
    simp only
    split_ifs <;> norm_num <;>
      first | linarith | exact ‹¬x = 0› (le_antisymm (by linarith) (not_lt.mp ‹¬x < 0›))
  rw [olver_11_01 (a := -1) (b := 1) (by norm_num) (Or.inl hmono)]
  norm_num

/-- **Olver Ex. 11.2 (iii)**: `𝒱_{−∞,∞}(sech x) = 2`.  `sech` increases from `0` to `1` on
`(−∞, 0]` and decreases from `1` to `0` on `[0, ∞)`. -/
theorem olver_ex_11_2_iii : eVariationOn (fun x => (Real.cosh x)⁻¹) univ = 2 := by
  have hcosh : ∀ x y : ℝ, |x| ≤ |y| → (Real.cosh y)⁻¹ ≤ (Real.cosh x)⁻¹ := fun x y h =>
    (inv_le_inv₀ (Real.cosh_pos y) (Real.cosh_pos x)).mpr (Real.cosh_le_cosh.mpr h)
  have hexp : ∀ x : ℝ, Real.exp (-x) / 2 ≤ Real.cosh x := fun x => by
    rw [Real.cosh_eq]; linarith [Real.exp_pos x]
  have hexp' : ∀ x : ℝ, Real.exp x / 2 ≤ Real.cosh x := fun x => by
    rw [Real.cosh_eq]; linarith [Real.exp_pos (-x)]
  have hbot : Tendsto (fun x => (Real.cosh x)⁻¹) atBot (𝓝 0) :=
    (tendsto_atTop_mono hexp ((Real.tendsto_exp_atTop.comp tendsto_neg_atBot_atTop).atTop_div_const
      two_pos)).inv_tendsto_atTop
  have htop : Tendsto (fun x => (Real.cosh x)⁻¹) atTop (𝓝 0) :=
    (tendsto_atTop_mono hexp' (Real.tendsto_exp_atTop.atTop_div_const two_pos)).inv_tendsto_atTop
  have hl := eVariationOn_Iic_of_monotoneOn (b := 0) (fun x hx y hy hxy =>
    hcosh y x (by rw [abs_of_nonpos (mem_Iic.mp hx), abs_of_nonpos (mem_Iic.mp hy)]; linarith))
    hbot
  have hr := eVariationOn_Ici_of_antitoneOn (a := 0) (fun x hx y hy hxy =>
    hcosh x y (by rw [abs_of_nonneg (mem_Ici.mp hx), abs_of_nonneg (mem_Ici.mp hy)]; exact hxy))
    htop
  rw [← Set.Iic_union_Ici (a := (0 : ℝ)), eVariationOn.union _ isGreatest_Iic isLeast_Ici, hl, hr,
    Real.cosh_zero, inv_one, sub_zero, ENNReal.ofReal_one, one_add_one_eq_two]

end DefiniteIntegrals

end Azurite.DLMF
