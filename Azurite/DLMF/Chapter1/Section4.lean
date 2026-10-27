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

end Azurite.DLMF
