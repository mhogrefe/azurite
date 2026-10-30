/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.JordanCurve.Orientation
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# DLMF §1.9(iii): Integration

Formalizations of <https://dlmf.nist.gov/1.9.iii>, built on the winding-number / Green machinery
of `Azurite.JordanCurve` (closed piecewise-`C¹` curves `ClosedPiecewiseC1`, integer winding
numbers, `∮ g dz = 2i ∫ ∂̄g · W dA`) and the vendored Jordan curve theorem.

* Arcs and contours: `IsArc` (restriction to `[a, b]` of a `C¹` map, i.e. `C¹` up to the
  endpoints), `IsContour` (continuous, `C¹` on the pieces of a subdivision — DLMF's "`x′`, `y′`
  piecewise continuous", read with one-sided limits at the corners), `IsSimpleContour`,
  `IsSimpleClosedContour`; `IsArc.isContour`, `IsContour.nonempty_closedPiecewiseC1`,
  `IsSimpleClosedContour.isJordanCurve`.
* 1.9.28: `contourIntegral f z a b = ∫ₐᵇ f(z(t)) z′(t) dt`; `dlmf_1_9_28` (the `x′ + i y′` form,
  `z` differentiable off a countable set); `ClosedPiecewiseC1.contourIntegral_eq` (the piecewise
  integral equals the single integral).  DLMF's remark on infinite integrands / infinite
  endpoints ("defined analogously to §1.4(v)"): `ContourConvergesAtTop`, `ContourConvergesAtBot`,
  `ContourConvergesLeft`, `ContourConvergesRight`, agreeing with the Lebesgue integral for
  integrable integrands (`contourConvergesAtTop_of_integrableOn`, `…AtBot…`,
  `contourConvergesLeft_of_intervalIntegrable`, `…Right…`); example
  `contourConvergesAtTop_exp_neg` (`∫_0^∞ e^{−z} dz = 1`).
* Contour-integral calculus on `ClosedPiecewiseC1`: `contourIntegral_congr`, `_add`,
  `_const_mul`, `contourIntegral_eq_zero_of_hasDerivAt` (closed curve, exact integrand),
  `contourIntegral_inv_pow_eq_zero` (`∮ dz/(z − p)^(n+2) = 0`).
* Jordan curve theorem: `dlmf_1_9_iii_jordan` (complement = interior ∪ exterior, disjoint, both
  open and connected, interior bounded, exterior unbounded, both with frontier `C`), via
  `frontier_connectedComponentIn_jordan` (Maehara's Lemma 1 transported from the plane).
* Cauchy's theorem in homology form: `windingSupport` (curve ∪ points with nonzero winding
  number, compact), `ClosedPiecewiseC1.contourIntegral_eq_zero` (`f` analytic on an open
  `U ⊇ windingSupport`; proof: smooth cutoff `exists_contDiff_eqOn_nhds_complex`, Green form,
  `dbar_eq_zero`, curve null).  `contourIntegral_div_sub` (`∮ f/(z − p) = 2πi W(p) f(p)`, via
  `dslope`), `contourIntegral_div_sub_pow` (`∮ f/(z − p)^(n+1) = 2πi W(p) f⁽ⁿ⁾(p)/n!`, induction
  with `iteratedDeriv_succ_eq_dslope`).
* 1.9.29–1.9.31: `dlmf_1_9_29`, `dlmf_1_9_30`, `dlmf_1_9_31` for any closed piecewise-`C¹` curve
  (simple or not), "within `C`" = `jordanInterior` (bounded components), positive orientation =
  `IsPositivelyOriented` (winding number `1` on the interior); 1.9.31 also holds for `n = 0`.
  Here `f` is analytic on an open set containing `C` and its interior; DLMF's hypotheses
  ("continuous within and on `C`, analytic within `C`", `C` simple) are handled in
  `Section9CauchyJordan` (`dlmf_1_9_29_jordan`, `dlmf_1_9_30_jordan`, `dlmf_1_9_31_jordan`).
* Liouville: `dlmf_1_9_iii_liouville`.
* 1.9.32: `dlmf_1_9_32` (`(2πi)⁻¹ ∮ dz/(z − z₀) = 𝒩(C, z₀) ∈ ℤ`), `dlmf_1_9_32_simple`
  (`1` inside, `0` outside for positive orientation), `dlmf_1_9_iii_orientation` (a simple
  closed contour is positively or negatively oriented).
* 1.9.33: `dlmf_1_9_33` (mean value property, Mathlib's `HarmonicOnNhd.circleAverage_eq`).
* 1.9.34: `poissonIntegral`, `dlmf_1_9_34` (DLMF's polar form of the integrand,
  `norm_sq_polar_sub`, `poissonKernel_polar`), `dlmf_1_9_34_harmonic` (real part of a
  Herglotz–Riesz integral, analytic by Mathlib), `dlmf_1_9_34_tendsto` (boundary values: kernel
  nonnegative with mean `1`, `integral_poissonKernel_circleMap`, and at most
  `4(R² − |z|²)/δ²` away from `w`).
-/

open Complex MeasureTheory Set Metric Filter Topology Bornology
open scoped Interval Real

namespace Azurite.DLMF

open Azurite.JordanCurve

/-! ### Arcs and contours -/

/-- An *arc* `z(t) = x(t) + i y(t)`, `a ≤ t ≤ b`, with `x`, `y` continuously differentiable on
`[a, b]` (one-sided at the endpoints): `z` is the restriction of a `C¹` function. -/
def IsArc (z : ℝ → ℂ) (a b : ℝ) : Prop :=
  a ≤ b ∧ ∃ g : ℝ → ℂ, ContDiff ℝ 1 g ∧ EqOn z g (Icc a b)

/-- A *contour*: `z` is continuous and `z′` is piecewise continuous, i.e. there is a subdivision
`a = t₀ < t₁ < ⋯ < tₙ = b` such that `z` is an arc on each `[tᵢ, tᵢ₊₁]`. -/
def IsContour (z : ℝ → ℂ) (a b : ℝ) : Prop :=
  ∃ (n : ℕ) (t : ℕ → ℝ) (g : ℕ → ℝ → ℂ), (∀ i < n, t i < t (i + 1)) ∧ t 0 = a ∧ t n = b ∧
    (∀ i < n, ContDiff ℝ 1 (g i)) ∧ ∀ i < n, EqOn z (g i) (Icc (t i) (t (i + 1)))

/-- A *simple* contour has no multiple points. -/
def IsSimpleContour (z : ℝ → ℂ) (a b : ℝ) : Prop := IsContour z a b ∧ InjOn z (Icc a b)

/-- A *simple closed* contour: simple except that `z(a) = z(b)`. -/
def IsSimpleClosedContour (z : ℝ → ℂ) (a b : ℝ) : Prop :=
  IsContour z a b ∧ a < b ∧ InjOn z (Ico a b) ∧ z a = z b

theorem IsArc.isContour {z : ℝ → ℂ} {a b : ℝ} (h : IsArc z a b) : IsContour z a b := by
  obtain ⟨hab, g, hg, hzg⟩ := h
  rcases hab.lt_or_eq with hlt | rfl
  · refine ⟨1, fun i => if i = 0 then a else b, fun _ => g, ?_, by simp, by simp,
      fun _ _ => hg, ?_⟩
    · intro i hi
      obtain rfl : i = 0 := by omega
      simpa using hlt
    · intro i hi
      obtain rfl : i = 0 := by omega
      simpa using hzg
  · exact ⟨0, fun _ => a, fun _ => g, fun _ h => absurd h (Nat.not_lt_zero _), rfl, rfl,
      fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩

/-- A closed contour is a `ClosedPiecewiseC1` curve. -/
theorem IsContour.nonempty_closedPiecewiseC1 {z : ℝ → ℂ} {a b : ℝ} (h : IsContour z a b)
    (hz : z a = z b) : Nonempty (ClosedPiecewiseC1 z a b) := by
  obtain ⟨n, t, g, hlt, h0, hn, hg, heq⟩ := h
  exact ⟨⟨n, t, g, hlt, h0, hn, hg, heq, hz⟩⟩

/-- A simple closed contour is a Jordan curve and a closed piecewise-`C¹` curve. -/
theorem IsSimpleClosedContour.isJordanCurve {z : ℝ → ℂ} {a b : ℝ}
    (h : IsSimpleClosedContour z a b) :
    IsJordanCurve z a b ∧ Nonempty (ClosedPiecewiseC1 z a b) := by
  obtain ⟨hc, hab, hinj, hz⟩ := h
  obtain ⟨P⟩ := hc.nonempty_closedPiecewiseC1 hz
  exact ⟨P.isJordanCurve hab hinj, ⟨P⟩⟩

/-! ### Equation 1.9.28 -/

/-- The contour integral `∫_C f(z) dz = ∫ₐᵇ f(z(t)) z′(t) dt`. -/
noncomputable def contourIntegral (f : ℂ → ℂ) (z : ℝ → ℂ) (a b : ℝ) : ℂ :=
  ∫ t in a..b, f (z t) * deriv z t

theorem deriv_eq_deriv_re_add_I_mul {z : ℝ → ℂ} {t : ℝ} (hz : DifferentiableAt ℝ z t) :
    deriv z t = deriv (fun s => (z s).re) t + I * deriv (fun s => (z s).im) t := by
  have h := hz.hasDerivAt
  have hre : HasDerivAt (fun s => (z s).re) (deriv z t).re t :=
    (reCLM.hasFDerivAt (x := z t)).comp_hasDerivAt t h
  have him : HasDerivAt (fun s => (z s).im) (deriv z t).im t :=
    (imCLM.hasFDerivAt (x := z t)).comp_hasDerivAt t h
  rw [hre.deriv, him.deriv, mul_comm]
  exact (re_add_im _).symm

/-- **DLMF 1.9.28**: `∫_C f(z) dz = ∫ₐᵇ f(z(t)) (x′(t) + i y′(t)) dt`, for `z` differentiable
away from a countable set (e.g. the corners of a contour). -/
theorem dlmf_1_9_28 (f : ℂ → ℂ) {z : ℝ → ℂ} {a b : ℝ} {s : Set ℝ} (hs : s.Countable)
    (hz : ∀ t ∈ Ioo (min a b) (max a b) \ s, DifferentiableAt ℝ z t) :
    contourIntegral f z a b = ∫ t in a..b,
      f (z t) * (deriv (fun s => (z s).re) t + I * deriv (fun s => (z s).im) t) := by
  refine intervalIntegral.integral_congr_ae ?_
  have hnull : volume (s ∪ {max a b}) = 0 :=
    (hs.union (countable_singleton _)).measure_zero volume
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with t ht htI
  have ht' : t ∉ s ∧ t ≠ max a b := by
    simp only [mem_union, mem_singleton_iff, not_or] at ht
    exact ht
  rw [uIoc] at htI
  rw [deriv_eq_deriv_re_add_I_mul (hz t ⟨⟨htI.1, lt_of_le_of_ne htI.2 ht'.2⟩, ht'.1⟩)]

/-! #### Infinite contour integrals (the remark after 1.9.28) -/

/-- DLMF §1.9(iii), "defined analogously to §1.4(v)" (1.4.22): the contour integral over the path
`z(t)`, `a ≤ t < ∞`, converges to `L`. -/
def ContourConvergesAtTop (f : ℂ → ℂ) (z : ℝ → ℂ) (a : ℝ) (L : ℂ) : Prop :=
  Tendsto (fun b => contourIntegral f z a b) atTop (𝓝 L)

/-- The contour integral over `z(t)`, `−∞ < t ≤ a`, converges to `L`. -/
def ContourConvergesAtBot (f : ℂ → ℂ) (z : ℝ → ℂ) (a : ℝ) (L : ℂ) : Prop :=
  Tendsto (fun b => contourIntegral f z b a) atBot (𝓝 L)

/-- (1.4.23) An integrand infinite at the end `t = b` of the path: `∫_a^b = lim_{c→b−} ∫_a^c`. -/
def ContourConvergesLeft (f : ℂ → ℂ) (z : ℝ → ℂ) (a b : ℝ) (L : ℂ) : Prop :=
  Tendsto (fun c => contourIntegral f z a c) (𝓝[<] b) (𝓝 L)

/-- (1.4.23) An integrand infinite at the start `t = a`: `∫_a^b = lim_{c→a+} ∫_c^b`. -/
def ContourConvergesRight (f : ℂ → ℂ) (z : ℝ → ℂ) (a b : ℝ) (L : ℂ) : Prop :=
  Tendsto (fun c => contourIntegral f z c b) (𝓝[>] a) (𝓝 L)

/-- When `f(z(t)) z′(t)` is integrable on `(a, ∞)`, the infinite contour integral converges to
the Lebesgue integral. -/
theorem contourConvergesAtTop_of_integrableOn {f : ℂ → ℂ} {z : ℝ → ℂ} {a : ℝ}
    (hf : IntegrableOn (fun t => f (z t) * deriv z t) (Ioi a)) :
    ContourConvergesAtTop f z a (∫ t in Ioi a, f (z t) * deriv z t) :=
  intervalIntegral_tendsto_integral_Ioi a hf tendsto_id

/-- When `f(z(t)) z′(t)` is integrable on `(−∞, a)`, the infinite contour integral converges to
the Lebesgue integral. -/
theorem contourConvergesAtBot_of_integrableOn {f : ℂ → ℂ} {z : ℝ → ℂ} {a : ℝ}
    (hf : IntegrableOn (fun t => f (z t) * deriv z t) (Iic a)) :
    ContourConvergesAtBot f z a (∫ t in Iic a, f (z t) * deriv z t) :=
  intervalIntegral_tendsto_integral_Iic a hf tendsto_id

/-- For an integrable integrand the limits at a finite end agree with the contour integral. -/
theorem contourConvergesLeft_of_intervalIntegrable {f : ℂ → ℂ} {z : ℝ → ℂ} {a b : ℝ}
    (hab : a < b) (hf : IntervalIntegrable (fun t => f (z t) * deriv z t) volume a b) :
    ContourConvergesLeft f z a b (contourIntegral f z a b) := by
  have hc := intervalIntegral.continuousOn_primitive_interval (μ := volume)
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mp hf |>.mono_set
      (by rw [uIcc_of_le hab.le]))
  have hmem : uIcc a b ∈ 𝓝[<] b := by
    rw [uIcc_of_le hab.le]
    exact Filter.mem_of_superset (Ioo_mem_nhdsLT hab) Ioo_subset_Icc_self
  exact ((hc b right_mem_uIcc).mono_of_mem_nhdsWithin hmem).tendsto

/-- At the start of the path. -/
theorem contourConvergesRight_of_intervalIntegrable {f : ℂ → ℂ} {z : ℝ → ℂ} {a b : ℝ}
    (hab : a < b) (hf : IntervalIntegrable (fun t => f (z t) * deriv z t) volume a b) :
    ContourConvergesRight f z a b (contourIntegral f z a b) := by
  have hc := intervalIntegral.continuousOn_primitive_interval_left (μ := volume)
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mp hf |>.mono_set
      (by rw [uIcc_of_le hab.le]))
  have hmem : uIcc a b ∈ 𝓝[>] a := by
    rw [uIcc_of_le hab.le]
    exact Filter.mem_of_superset (Ioo_mem_nhdsGT hab) Ioo_subset_Icc_self
  exact ((hc a left_mem_uIcc).mono_of_mem_nhdsWithin hmem).tendsto

/-- Example: along the positive real axis, `∫_0^∞ e^{−z} dz = 1`. -/
theorem contourConvergesAtTop_exp_neg :
    ContourConvergesAtTop (fun w => cexp (-w)) (fun t : ℝ => (t : ℂ)) 0 1 := by
  have hd : ∀ t : ℝ, deriv (fun t : ℝ => (t : ℂ)) t = 1 := fun t =>
    ((hasDerivAt_id t).ofReal_comp).deriv.trans (by simp)
  have he : ∀ b : ℝ, contourIntegral (fun w => cexp (-w)) (fun t : ℝ => (t : ℂ)) 0 b =
      ((1 - Real.exp (-b) : ℝ) : ℂ) := fun b => by
    simp only [contourIntegral, hd, mul_one]
    have : ∫ t in (0 : ℝ)..b, Real.exp (-t) = 1 - Real.exp (-b) := by
      rw [intervalIntegral.integral_comp_neg (fun t => Real.exp t), integral_exp]; simp
    rw [← this, ← intervalIntegral.integral_ofReal]
    congr 1; funext t; push_cast; rfl
  unfold ContourConvergesAtTop
  simp_rw [he]
  have : Tendsto (fun b : ℝ => 1 - Real.exp (-b)) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub Real.tendsto_exp_neg_atTop_nhds_zero
  rw [sub_zero] at this
  have h := (Complex.continuous_ofReal.tendsto _).comp this
  rwa [Complex.ofReal_one] at h

end Azurite.DLMF

namespace Azurite.JordanCurve.ClosedPiecewiseC1

variable {c : ℝ → ℂ} {a b : ℝ} (P : ClosedPiecewiseC1 c a b)

theorem continuousOn_piece {f : ℂ → ℂ} (hf : ContinuousOn f P.curve) {i : ℕ} (hi : i < P.n) :
    ContinuousOn (fun s => f (P.g i s) * deriv (P.g i) s) (Icc (P.t i) (P.t (i + 1))) :=
  (hf.comp (P.contDiff i hi).continuous.continuousOn fun _ hs =>
    P.mem_curve_of_mem_piece hi hs).mul ((P.contDiff i hi).continuous_deriv le_rfl).continuousOn

theorem intervalIntegrable_piece {f : ℂ → ℂ} (hf : ContinuousOn f P.curve) {i : ℕ}
    (hi : i < P.n) :
    IntervalIntegrable (fun s => f (P.g i s) * deriv (P.g i) s) volume (P.t i) (P.t (i + 1)) :=
  (P.continuousOn_piece hf hi).intervalIntegrable_of_Icc (P.lt i hi).le

/-- The piecewise contour integral equals DLMF's single integral `∫ₐᵇ f(c(t)) c′(t) dt`. -/
theorem contourIntegral_eq {f : ℂ → ℂ} (hf : ContinuousOn f P.curve) :
    P.contourIntegral f = Azurite.DLMF.contourIntegral f c a b := by
  have hpiece : ∀ i < P.n, ∀ᵐ s ∂volume, s ∈ Ι (P.t i) (P.t (i + 1)) →
      f (P.g i s) * deriv (P.g i) s = f (c s) * deriv c s := by
    intro i hi
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (measure_singleton (P.t (i + 1)))]
      with s hs hsI
    rw [uIoc_of_le (P.lt i hi).le] at hsI
    have hsIoo : s ∈ Ioo (P.t i) (P.t (i + 1)) :=
      ⟨hsI.1, lt_of_le_of_ne hsI.2 fun h => hs (by simp [h])⟩
    have hev : c =ᶠ[𝓝 s] P.g i := eventually_of_mem (Ioo_mem_nhds hsIoo.1 hsIoo.2)
      fun x hx => P.eqOn i hi (Ioo_subset_Icc_self hx)
    rw [hev.deriv_eq, P.eqOn i hi (Ioo_subset_Icc_self hsIoo)]
  unfold ClosedPiecewiseC1.contourIntegral Azurite.DLMF.contourIntegral
  rw [Finset.sum_congr rfl fun i hi =>
      intervalIntegral.integral_congr_ae (hpiece i (Finset.mem_range.mp hi)),
    intervalIntegral.sum_integral_adjacent_intervals, P.first, P.last]
  intro i hi
  exact (P.intervalIntegrable_piece hf hi).congr_ae (ae_restrict_of_ae_restrict_of_subset
    subset_rfl ((ae_restrict_iff' measurableSet_uIoc).mpr (hpiece i hi)))

theorem contourIntegral_congr {f₁ f₂ : ℂ → ℂ} (h : EqOn f₁ f₂ P.curve) :
    P.contourIntegral f₁ = P.contourIntegral f₂ := by
  unfold ClosedPiecewiseC1.contourIntegral
  refine Finset.sum_congr rfl fun i hi => intervalIntegral.integral_congr fun s hs => ?_
  have hi' := Finset.mem_range.mp hi
  rw [uIcc_of_le (P.lt i hi').le] at hs
  simp only [h (P.mem_curve_of_mem_piece hi' hs)]

theorem contourIntegral_add {f₁ f₂ : ℂ → ℂ} (h₁ : ContinuousOn f₁ P.curve)
    (h₂ : ContinuousOn f₂ P.curve) :
    P.contourIntegral (fun z => f₁ z + f₂ z) = P.contourIntegral f₁ + P.contourIntegral f₂ := by
  unfold ClosedPiecewiseC1.contourIntegral
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  rw [← intervalIntegral.integral_add (P.intervalIntegrable_piece h₁ hi')
    (P.intervalIntegrable_piece h₂ hi')]
  congr 1
  ext s
  ring

theorem contourIntegral_const_mul (w : ℂ) (f : ℂ → ℂ) :
    P.contourIntegral (fun z => w * f z) = w * P.contourIntegral f := by
  unfold ClosedPiecewiseC1.contourIntegral
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  ext s
  ring

/-- The contour integral of a derivative around a closed curve vanishes. -/
theorem contourIntegral_eq_zero_of_hasDerivAt {F F' : ℂ → ℂ}
    (hF : ∀ w ∈ P.curve, HasDerivAt F (F' w) w) (hF' : ContinuousOn F' P.curve) :
    P.contourIntegral F' = 0 := by
  unfold ClosedPiecewiseC1.contourIntegral
  have h : ∀ i < P.n, ∫ s in P.t i..P.t (i + 1), F' (P.g i s) * deriv (P.g i) s =
      F (c (P.t (i + 1))) - F (c (P.t i)) := by
    intro i hi
    have hle := (P.lt i hi).le
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => F (P.g i s)) ?_
      (P.intervalIntegrable_piece hF' hi), P.eqOn i hi ⟨hle, le_rfl⟩,
      P.eqOn i hi ⟨le_rfl, hle⟩]
    intro s hs
    rw [uIcc_of_le hle] at hs
    exact (hF _ (P.mem_curve_of_mem_piece hi hs)).comp s
      ((P.contDiff i hi).differentiable one_ne_zero s).hasDerivAt
  rw [Finset.sum_congr rfl fun i hi => h i (Finset.mem_range.mp hi),
    Finset.sum_range_sub (fun i => F (c (P.t i))), P.last, P.first, P.closed, sub_self]

theorem sub_ne_zero_of_mem_curve {p z : ℂ} (hp : p ∉ P.curve) (hz : z ∈ P.curve) : z - p ≠ 0 :=
  sub_ne_zero.mpr fun h => hp (h ▸ hz)

theorem continuousOn_inv_sub_pow {p : ℂ} (hp : p ∉ P.curve) (n : ℕ) :
    ContinuousOn (fun z => ((z - p) ^ n)⁻¹) P.curve :=
  continuousOn_of_forall_continuousAt fun _ hz =>
    ((continuous_sub_right p).pow n).continuousAt.inv₀
      (pow_ne_zero _ (P.sub_ne_zero_of_mem_curve hp hz))

/-- `∮ dz/(z − p)^(n+2) = 0` off the curve. -/
theorem contourIntegral_inv_pow_eq_zero {p : ℂ} (hp : p ∉ P.curve) (n : ℕ) :
    P.contourIntegral (fun z => ((z - p) ^ (n + 2))⁻¹) = 0 := by
  refine P.contourIntegral_eq_zero_of_hasDerivAt
    (F := fun z => -((n + 1 : ℂ))⁻¹ * ((z - p) ^ (n + 1))⁻¹) (fun w hw => ?_)
    (P.continuousOn_inv_sub_pow hp _)
  have hne := P.sub_ne_zero_of_mem_curve hp hw
  have h1 : HasDerivAt (fun z => (z - p) ^ (n + 1)) ((n + 1 : ℂ) * (w - p) ^ n) w := by
    simpa using ((hasDerivAt_id' w).sub_const p).fun_pow (n + 1)
  have h2 := (h1.inv (pow_ne_zero _ hne)).const_mul (-((n + 1 : ℂ))⁻¹)
  convert h2 using 1
  have hn : (n + 1 : ℂ) ≠ 0 := Nat.cast_add_one_ne_zero n
  field_simp
  ring

/-! ### Cauchy's theorem -/

/-- The curve together with the points it winds around. -/
def windingSupport : Set ℂ := P.curve ∪ {p | p ∉ P.curve ∧ P.windingNumber p ≠ 0}

theorem isCompact_windingSupport : IsCompact P.windingSupport := by
  obtain ⟨R, hR⟩ := P.exists_forall_windingNumber_eq_zero
  obtain ⟨M, hM⟩ := P.isCompact_curve.isBounded.subset_closedBall 0
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · rw [← isOpen_compl_iff]
    refine isOpen_iff_mem_nhds.mpr fun p hp => ?_
    have hpc : p ∉ P.curve := fun h => hp (Or.inl h)
    have hW : P.windingNumber p = 0 := by
      by_contra h
      exact hp (Or.inr ⟨hpc, h⟩)
    filter_upwards [P.isOpen_compl_curve.mem_nhds hpc, P.eventually_windingNumber_eq hpc]
      with q hq hqW
    rintro (h | h)
    · exact hq h
    · exact h.2 (hqW.trans hW)
  · refine (isBounded_closedBall (x := (0 : ℂ)) (r := max R M)).subset ?_
    rintro p (h | h)
    · exact closedBall_subset_closedBall (le_max_right _ _) (hM h)
    · rw [mem_closedBall_zero_iff]
      by_contra hlt
      push Not at hlt
      exact h.2 (hR p (lt_of_le_of_lt (le_max_left _ _) hlt))

theorem curve_subset_windingSupport : P.curve ⊆ P.windingSupport := subset_union_left

end Azurite.JordanCurve.ClosedPiecewiseC1

namespace Azurite.DLMF

open Azurite.JordanCurve

/-- A `C¹` function on an open `U ⊇ K` (`K` compact) agrees on a neighbourhood of `K` with a
globally `C¹` function. -/
theorem exists_contDiff_eqOn_nhds_complex {F : ℂ → ℂ} {U K : Set ℂ} (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U) (hF : ContDiffOn ℝ 1 F U) :
    ∃ F' : ℂ → ℂ, ContDiff ℝ 1 F' ∧ ∃ V : Set ℂ, IsOpen V ∧ K ⊆ V ∧ EqOn F' F V := by
  obtain ⟨V₂, hV₂o, hKV₂, hV₂U, -⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨V₁, hV₁o, hKV₁, hV₁V₂, -⟩ := exists_open_between_and_isCompact_closure hK hV₂o hKV₂
  obtain ⟨χ, hχ, -, hχs, hχ1⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := 1) hV₂o isClosed_closure hV₁V₂
  have hχt : tsupport χ = closure V₂ := by rw [tsupport, hχs]
  refine ⟨fun x => χ x • F x, ?_, V₁, hV₁o, hKV₁, fun q hq => ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro q
    by_cases hq : q ∈ U
    · exact hχ.contDiffAt.smul (hF.contDiffAt (hU.mem_nhds hq))
    · have hqs : q ∉ tsupport χ := by
        rw [hχt]
        exact fun h => hq (hV₂U h)
      have h0 : χ =ᶠ[𝓝 q] 0 := notMem_tsupport_iff_eventuallyEq.mp hqs
      refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
      filter_upwards [h0] with r hr
      simp [hr]
  · have : χ q = 1 := (hχ1 q).mp (subset_closure hq)
    simp [this]

/-- `∂̄g = 0` where `g` agrees with a complex-differentiable function. -/
theorem dbar_eq_zero {f g : ℂ → ℂ} {p : ℂ} (hf : DifferentiableAt ℂ f p)
    (hgf : g =ᶠ[𝓝 p] f) : dbar g p = 0 := by
  have h := hf.hasFDerivAt.restrictScalars ℝ
  rw [dbar, hgf.fderiv_eq, h.fderiv]
  simp only [ContinuousLinearMap.coe_restrictScalars']
  have : (fderiv ℂ f p) I = I * (fderiv ℂ f p) 1 := by
    rw [← smul_eq_mul, ← ContinuousLinearMap.map_smul, smul_eq_mul, mul_one]
  rw [this]
  linear_combination ((fderiv ℂ f p) 1 / 2) * I_sq

end Azurite.DLMF

namespace Azurite.JordanCurve.ClosedPiecewiseC1

variable {c : ℝ → ℂ} {a b : ℝ} (P : ClosedPiecewiseC1 c a b)

/-- **Cauchy's theorem** (homology form): `∮ f dz = 0` for `f` analytic on an open set containing
the curve and every point the curve winds around. -/
theorem contourIntegral_eq_zero {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hKU : P.windingSupport ⊆ U) : P.contourIntegral f = 0 := by
  have hF : ContDiffOn ℝ 1 f U := (hf.contDiffOn hU).restrict_scalars ℝ
  obtain ⟨g, hg, V, hV, hKV, hgf⟩ :=
    Azurite.DLMF.exists_contDiff_eqOn_nhds_complex hU P.isCompact_windingSupport hKU hF
  rw [P.contourIntegral_congr (f₁ := f) (f₂ := g) fun z hz =>
      (hgf (hKV (P.curve_subset_windingSupport hz))).symm,
    P.contourIntegral_eq_integral_dbar' hg]
  have : (fun p => dbar g p * (P.windingNumber p : ℂ)) =ᵐ[volume] 0 := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp P.volume_curve] with p hp
    by_cases hW : P.windingNumber p = 0
    · simp [hW]
    · have hpK : p ∈ P.windingSupport := Or.inr ⟨hp, hW⟩
      have hev : g =ᶠ[𝓝 p] f := eventually_of_mem ((hV.inter hU).mem_nhds ⟨hKV hpK, hKU hpK⟩)
        fun q hq => hgf hq.1
      simp [Azurite.DLMF.dbar_eq_zero (hf.differentiableAt (hU.mem_nhds (hKU hpK))) hev]
  rw [integral_congr_ae this]
  simp

/-- If the winding number at `p` vanishes, `p` may be removed from the domain. -/
theorem windingSupport_subset_sdiff {U : Set ℂ} (hKU : P.windingSupport ⊆ U) {p : ℂ}
    (hp : p ∉ P.curve) (hW : P.windingNumber p = 0) : P.windingSupport ⊆ U \ {p} := by
  intro q hq
  refine ⟨hKU hq, fun hqp => ?_⟩
  rw [mem_singleton_iff] at hqp
  subst hqp
  rcases hq with h | h
  · exact hp h
  · exact h.2 hW

/-- **Cauchy's integral formula** (homology form): `∮ f(z)/(z − p) dz = 2πi · W(p) · f(p)`. -/
theorem contourIntegral_div_sub {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hKU : P.windingSupport ⊆ U) {p : ℂ} (hp : p ∉ P.curve) :
    P.contourIntegral (fun z => f z / (z - p)) = 2 * π * I * P.windingNumber p * f p := by
  by_cases hW : P.windingNumber p = 0
  · rw [hW, Int.cast_zero, mul_zero, zero_mul]
    refine P.contourIntegral_eq_zero (hU.sdiff isClosed_singleton) ?_
      (P.windingSupport_subset_sdiff hKU hp hW)
    exact (hf.mono sdiff_subset).div (differentiableOn_id.sub_const p)
      fun z hz => sub_ne_zero.mpr hz.2
  · have hpU : p ∈ U := hKU (Or.inr ⟨hp, hW⟩)
    have hG : DifferentiableOn ℂ (dslope f p) U :=
      (differentiableOn_dslope (hU.mem_nhds hpU)).mpr hf
    have heq : EqOn (fun z => f z / (z - p)) (fun z => dslope f p z + f p * ((z - p) ^ 1)⁻¹)
        P.curve := by
      intro z hz
      have hzp : z ≠ p := fun h => hp (h ▸ hz)
      have hne := P.sub_ne_zero_of_mem_curve hp hz
      simp only [dslope_of_ne _ hzp, slope_def_field, pow_one]
      field_simp
      ring
    have hcont := P.continuousOn_inv_sub_pow hp 1
    rw [P.contourIntegral_congr heq, P.contourIntegral_add (f₁ := dslope f p)
        (f₂ := fun z => f p * ((z - p) ^ 1)⁻¹)
        (hG.continuousOn.mono (P.curve_subset_windingSupport.trans hKU))
        (continuousOn_const.mul hcont),
      P.contourIntegral_eq_zero hU hG hKU, P.contourIntegral_const_mul]
    simp only [pow_one]
    rw [P.contourIntegral_inv_eq hp]
    ring

end Azurite.JordanCurve.ClosedPiecewiseC1

namespace Azurite.DLMF

open Azurite.JordanCurve

theorem iteratedDeriv_sub_const_succ_succ (p : ℂ) (k : ℕ) :
    iteratedDeriv (k + 2) (fun z : ℂ => z - p) = 0 := by
  rw [iteratedDeriv_succ', iteratedDeriv_succ']
  have : deriv (fun z : ℂ => z - p) = fun _ => 1 := funext fun z => by simp
  rw [this]
  ext z
  simp

/-- `f^{(n+1)}(p) = (n + 1) · (dslope f p)^{(n)}(p)`. -/
theorem iteratedDeriv_succ_eq_dslope {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ} (hU : U ∈ 𝓝 p)
    (hf : DifferentiableOn ℂ f U) (n : ℕ) :
    iteratedDeriv (n + 1) f p = (n + 1) * iteratedDeriv n (dslope f p) p := by
  have hG : DifferentiableOn ℂ (dslope f p) U := (differentiableOn_dslope hU).mpr hf
  have hGa : ContDiffAt ℂ (n + 1) (dslope f p) p := (hG.analyticAt hU).contDiffAt
  have hfun : f = fun z => f p + (z - p) * dslope f p z := by
    funext z
    have := sub_smul_dslope f p z
    rw [smul_eq_mul] at this
    rw [this]
    ring
  conv_lhs => rw [hfun]
  have hl : ContDiffAt ℂ (n + 1) (fun z : ℂ => z - p) p := contDiffAt_id.sub contDiffAt_const
  rw [iteratedDeriv_const_add (by omega : 0 < n + 1), iteratedDeriv_fun_mul hl hGa,
    Finset.sum_range_succ', Finset.sum_range_succ']
  have hrest : ∑ i ∈ Finset.range n, ((n + 1).choose (i + 1 + 1) : ℂ) *
      iteratedDeriv (i + 1 + 1) (fun z => z - p) p *
      iteratedDeriv (n + 1 - (i + 1 + 1)) (dslope f p) p = 0 :=
    Finset.sum_eq_zero fun i _ => by
      rw [iteratedDeriv_sub_const_succ_succ]
      simp
  rw [hrest]
  simp [iteratedDeriv_one]

end Azurite.DLMF

namespace Azurite.JordanCurve.ClosedPiecewiseC1

variable {c : ℝ → ℂ} {a b : ℝ} (P : ClosedPiecewiseC1 c a b)

/-- **Cauchy's integral formula for derivatives** (homology form):
`∮ f(z)/(z − p)^(n+1) dz = 2πi · W(p) · f⁽ⁿ⁾(p)/n!`. -/
theorem contourIntegral_div_sub_pow {U : Set ℂ} (hU : IsOpen U) {p : ℂ} (hp : p ∉ P.curve)
    (n : ℕ) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hKU : P.windingSupport ⊆ U) :
    P.contourIntegral (fun z => f z / (z - p) ^ (n + 1)) =
      2 * π * I * P.windingNumber p * (iteratedDeriv n f p / n.factorial) := by
  by_cases hW : P.windingNumber p = 0
  · rw [hW, Int.cast_zero, mul_zero, zero_mul]
    refine P.contourIntegral_eq_zero (hU.sdiff isClosed_singleton) ?_
      (P.windingSupport_subset_sdiff hKU hp hW)
    exact (hf.mono sdiff_subset).div ((differentiableOn_id.sub_const p).pow _)
      fun z hz => pow_ne_zero _ (sub_ne_zero.mpr hz.2)
  have hpU : p ∈ U := hKU (Or.inr ⟨hp, hW⟩)
  induction n generalizing f with
  | zero => simpa using P.contourIntegral_div_sub hU hf hKU hp
  | succ n ih =>
    have hG : DifferentiableOn ℂ (dslope f p) U :=
      (differentiableOn_dslope (hU.mem_nhds hpU)).mpr hf
    have heq : EqOn (fun z => f z / (z - p) ^ (n + 1 + 1))
        (fun z => dslope f p z / (z - p) ^ (n + 1) + f p * ((z - p) ^ (n + 2))⁻¹)
        P.curve := by
      intro z hz
      have hzp : z ≠ p := fun h => hp (h ▸ hz)
      have hne := P.sub_ne_zero_of_mem_curve hp hz
      simp only [dslope_of_ne _ hzp, slope_def_field]
      field_simp
      ring
    have hc1 : ContinuousOn (fun z => dslope f p z / (z - p) ^ (n + 1)) P.curve :=
      (hG.continuousOn.mono (P.curve_subset_windingSupport.trans hKU)).div
        ((continuous_sub_right p).pow _).continuousOn
        fun z hz => pow_ne_zero _ (P.sub_ne_zero_of_mem_curve hp hz)
    rw [P.contourIntegral_congr heq, P.contourIntegral_add
        (f₂ := fun z => f p * ((z - p) ^ (n + 2))⁻¹) hc1
        (continuousOn_const.mul (P.continuousOn_inv_sub_pow hp _)),
      ih hG, P.contourIntegral_const_mul, P.contourIntegral_inv_pow_eq_zero hp,
      Azurite.DLMF.iteratedDeriv_succ_eq_dslope (hU.mem_nhds hpU) hf, Nat.factorial_succ]
    have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    have hn1 : (n + 1 : ℂ) ≠ 0 := Nat.cast_add_one_ne_zero n
    push_cast
    field_simp
    ring

/-- For a closed curve, the points it winds around lie in the bounded components of the
complement (the *interior*). -/
theorem windingSupport_subset {U : Set ℂ} (hU : jordanInterior c a b ∪ c '' Icc a b ⊆ U) :
    P.windingSupport ⊆ U := by
  rintro p (h | ⟨hp, hW⟩)
  · exact hU (Or.inr h)
  · refine hU (Or.inl ?_)
    rcases (compl_image_eq_union (c := c) (a := a) (b := b)).subset hp with h | h
    · exact h
    · exact absurd (P.windingNumber_eq_zero_of_mem_jordanExterior h) hW

end Azurite.JordanCurve.ClosedPiecewiseC1

namespace Azurite.DLMF

open Azurite.JordanCurve

variable {c : ℝ → ℂ} {a b : ℝ}

/-! ### Jordan curve theorem -/

/-- Every component of the complement of a Jordan curve (when there are at least two) has the
whole curve as its boundary. -/
theorem frontier_connectedComponentIn_jordan (h : IsJordanCurve c a b) {p q : ℂ}
    (hp : p ∉ c '' Icc a b) (hq : q ∉ c '' Icc a b)
    (hpq : connectedComponentIn (c '' Icc a b)ᶜ q ≠ connectedComponentIn (c '' Icc a b)ᶜ p) :
    frontier (connectedComponentIn (c '' Icc a b)ᶜ p) = c '' Icc a b := by
  obtain ⟨r, hrc, hri, hrr⟩ := h.exists_sphere_param
  have hmem : ∀ {z : ℂ}, z ∉ c '' Icc a b → Arcs.complexLIE z ∈ (range r)ᶜ := fun hz hm => by
    rw [hrr, mem_image_complexLIE_iff] at hm
    exact hz hm
  have hcomp : ∀ {z : ℂ}, z ∉ c '' Icc a b → connectedComponentIn (range r)ᶜ
      (Arcs.complexLIE z) = Arcs.complexLIE '' connectedComponentIn (c '' Icc a b)ᶜ z :=
    fun hz => by rw [hrr, image_connectedComponentIn_compl hz]
  have key := component_boundary_eq Brouwer.brouwerFPT hrc hri (hmem hp)
    ⟨_, hmem hq, by
      rw [hcomp hp, hcomp hq]
      exact fun he => hpq (image_injective.mpr Arcs.complexLIE.injective he)⟩
  have himg := Arcs.complexLIE.toHomeomorph.image_frontier
    (connectedComponentIn (c '' Icc a b)ᶜ p)
  simp only [LinearIsometryEquiv.coe_toHomeomorph] at himg
  rw [hcomp hp, ← himg, hrr] at key
  exact image_injective.mpr Arcs.complexLIE.injective key

/-- **Jordan curve theorem** (DLMF §1.9(iii)): a simple closed curve `C` divides `ℂ` into two
disjoint open domains, the bounded *interior* and the unbounded *exterior*, each with boundary
`C`.  Only continuity is needed. -/
theorem dlmf_1_9_iii_jordan (h : IsJordanCurve c a b) :
    (c '' Icc a b)ᶜ = jordanInterior c a b ∪ jordanExterior c a b ∧
    Disjoint (jordanInterior c a b) (jordanExterior c a b) ∧
    IsOpen (jordanInterior c a b) ∧ IsConnected (jordanInterior c a b) ∧
    IsOpen (jordanExterior c a b) ∧ IsConnected (jordanExterior c a b) ∧
    IsBounded (jordanInterior c a b) ∧ ¬ IsBounded (jordanExterior c a b) ∧
    frontier (jordanInterior c a b) = c '' Icc a b ∧
    frontier (jordanExterior c a b) = c '' Icc a b := by
  obtain ⟨p, hp⟩ := h.exists_mem_jordanInterior
  obtain ⟨q, hq⟩ := h.exists_mem_jordanExterior
  have hne : connectedComponentIn (c '' Icc a b)ᶜ q ≠ connectedComponentIn (c '' Icc a b)ᶜ p :=
    fun he => hq.2 (by rw [he]; exact hp.2)
  obtain ⟨M, hM⟩ :=
    (isCompact_Icc.image_of_continuousOn h.continuousOn).isBounded.subset_closedBall 0
  refine ⟨compl_image_eq_union, jordanInterior_disjoint_jordanExterior,
    isOpen_jordanInterior h.continuousOn, h.isConnected_jordanInterior,
    isOpen_jordanExterior h.continuousOn, h.isConnected_jordanExterior, ?_, ?_, ?_, ?_⟩
  · exact isBounded_closedBall.subset (jordanInterior_subset_closedBall (le_max_right M 0)
      (hM.trans (closedBall_subset_closedBall (le_max_left M 0))))
  · exact fun hb => hq.2 (hb.subset (connectedComponentIn_subset_jordanExterior hq))
  · rw [h.jordanInterior_eq hp]
    exact frontier_connectedComponentIn_jordan h hp.1 hq.1 hne
  · rw [h.jordanExterior_eq hq]
    exact frontier_connectedComponentIn_jordan h hq.1 hp.1 hne.symm

/-! ### Cauchy's theorem and Cauchy's integral formula -/

theorem two_pi_I_ne_zero : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]

/-- **DLMF 1.9.29** (Cauchy's theorem): `∫_C f(z) dz = 0` for `f` analytic on an open set
containing `C` and its interior.  Any closed piecewise-`C¹` curve is allowed (its interior is the
union of the bounded components of the complement). -/
theorem dlmf_1_9_29 (P : ClosedPiecewiseC1 c a b) {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hsub : jordanInterior c a b ∪ c '' Icc a b ⊆ U) (hf : DifferentiableOn ℂ f U) :
    contourIntegral f c a b = 0 := by
  rw [← P.contourIntegral_eq (hf.continuousOn.mono (subset_union_right.trans hsub))]
  exact P.contourIntegral_eq_zero hU hf (P.windingSupport_subset hsub)

theorem continuousOn_div_sub_pow (P : ClosedPiecewiseC1 c a b) {f : ℂ → ℂ} {U : Set ℂ}
    (hsub : c '' Icc a b ⊆ U) (hf : DifferentiableOn ℂ f U) {z₀ : ℂ}
    (hz₀ : z₀ ∉ c '' Icc a b) (n : ℕ) :
    ContinuousOn (fun z => f z / (z - z₀) ^ n) P.curve :=
  (hf.continuousOn.mono hsub).div ((continuous_sub_right z₀).pow _).continuousOn
    fun _ hz => pow_ne_zero _ (P.sub_ne_zero_of_mem_curve hz₀ hz)

/-- **DLMF 1.9.30** (Cauchy's integral formula), `C` positively oriented. -/
theorem dlmf_1_9_30 (P : ClosedPiecewiseC1 c a b) (hpos : P.IsPositivelyOriented) {f : ℂ → ℂ}
    {U : Set ℂ} (hU : IsOpen U) (hsub : jordanInterior c a b ∪ c '' Icc a b ⊆ U)
    (hf : DifferentiableOn ℂ f U) {z₀ : ℂ} (hz₀ : z₀ ∈ jordanInterior c a b) :
    f z₀ = 1 / (2 * π * I) * contourIntegral (fun z => f z / (z - z₀)) c a b := by
  have hc := continuousOn_div_sub_pow P (subset_union_right.trans hsub) hf hz₀.1 1
  simp only [pow_one] at hc
  rw [← P.contourIntegral_eq hc,
    P.contourIntegral_div_sub hU hf (P.windingSupport_subset hsub) hz₀.1, hpos z₀ hz₀,
    Int.cast_one, mul_one, one_div, inv_mul_cancel_left₀ two_pi_I_ne_zero]

/-- **DLMF 1.9.31** (Cauchy's integral formula for derivatives), `C` positively oriented; also
valid for `n = 0`, where it is 1.9.30. -/
theorem dlmf_1_9_31 (P : ClosedPiecewiseC1 c a b) (hpos : P.IsPositivelyOriented) {f : ℂ → ℂ}
    {U : Set ℂ} (hU : IsOpen U) (hsub : jordanInterior c a b ∪ c '' Icc a b ⊆ U)
    (hf : DifferentiableOn ℂ f U) {z₀ : ℂ} (hz₀ : z₀ ∈ jordanInterior c a b) (n : ℕ) :
    iteratedDeriv n f z₀ = n.factorial / (2 * π * I) *
      contourIntegral (fun z => f z / (z - z₀) ^ (n + 1)) c a b := by
  rw [← P.contourIntegral_eq (continuousOn_div_sub_pow P (subset_union_right.trans hsub) hf
      hz₀.1 _), P.contourIntegral_div_sub_pow hU hz₀.1 n hf (P.windingSupport_subset hsub),
    hpos z₀ hz₀, Int.cast_one, mul_one]
  have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have h2 := two_pi_I_ne_zero
  field_simp

/-! ### Liouville's theorem -/

/-- **Liouville's theorem** (DLMF §1.9(iii)): any bounded entire function is a constant. -/
theorem dlmf_1_9_iii_liouville {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hb : IsBounded (range f)) : ∃ w, ∀ z, f z = w :=
  hf.exists_const_forall_eq_of_bounded hb

/-! ### Winding number -/

/-- **DLMF 1.9.32**: for a closed contour `C` and `z₀ ∉ C`, `(2πi)⁻¹ ∫_C dz/(z − z₀)` is the
integer `𝒩(C, z₀)`. -/
theorem dlmf_1_9_32 (P : ClosedPiecewiseC1 c a b) {z₀ : ℂ} (hz₀ : z₀ ∉ c '' Icc a b) :
    1 / (2 * π * I) * contourIntegral (fun z => 1 / (z - z₀)) c a b = P.windingNumber z₀ := by
  have hc : ContinuousOn (fun z => 1 / (z - z₀)) P.curve :=
    continuousOn_const.div (continuousOn_id.sub continuousOn_const)
      fun _ hz => P.sub_ne_zero_of_mem_curve hz₀ hz
  rw [← P.contourIntegral_eq hc]
  simp only [one_div]
  rw [P.contourIntegral_inv_eq hz₀, inv_mul_cancel_left₀ two_pi_I_ne_zero]

/-- DLMF §1.9(iii): for a positively oriented simple closed contour, `𝒩(C, z₀)` is `1` inside
and `0` outside. -/
theorem dlmf_1_9_32_simple (P : ClosedPiecewiseC1 c a b) (hpos : P.IsPositivelyOriented) :
    (∀ z₀ ∈ jordanInterior c a b, P.windingNumber z₀ = 1) ∧
      ∀ z₀ ∈ jordanExterior c a b, P.windingNumber z₀ = 0 :=
  ⟨hpos, fun _ hz => P.windingNumber_eq_zero_of_mem_jordanExterior hz⟩

/-- A simple closed contour is described in the positive or the negative rotational sense:
its winding number is `1` throughout its interior, or `−1` throughout. -/
theorem dlmf_1_9_iii_orientation (P : ClosedPiecewiseC1 c a b) (h : IsJordanCurve c a b) :
    P.IsPositivelyOriented ∨ P.IsNegativelyOriented :=
  P.isPositivelyOriented_or_isNegativelyOriented h

/-! ### Mean value property -/

/-- **DLMF 1.9.33** (mean value property): for `u` harmonic on a neighbourhood of the closed disk
of radius `r` about `z`, `u(z) = (2π)⁻¹ ∫₀^{2π} u(z + r e^{iφ}) dφ`. -/
theorem dlmf_1_9_33 {u : ℂ → ℝ} {z : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hu : InnerProductSpace.HarmonicOnNhd u (closedBall z r)) :
    u z = 1 / (2 * π) * ∫ φ in (0 : ℝ)..2 * π, u (z + r * exp (φ * I)) := by
  have h := InnerProductSpace.HarmonicOnNhd.circleAverage_eq (R := r)
    (by rwa [abs_of_nonneg hr])
  rw [← h, Real.circleAverage_def, smul_eq_mul, one_div]
  rfl

/-! ### Poisson integral -/

/-- The Poisson integral `u(z) = (2π)⁻¹ ∫₀^{2π} P(z, R e^{iφ}) h(R e^{iφ}) dφ`. -/
noncomputable def poissonIntegral (h : ℂ → ℝ) (R : ℝ) (z : ℂ) : ℝ :=
  Real.circleAverage (poissonKernel 0 z • h) 0 R

theorem norm_sq_polar_sub (R r φ θ : ℝ) :
    ‖(R : ℂ) * exp (φ * I) - r * exp (θ * I)‖ ^ 2 =
      R ^ 2 - 2 * R * r * Real.cos (φ - θ) + r ^ 2 := by
  rw [← normSq_eq_norm_sq, normSq_apply]
  simp only [sub_re, sub_im, re_ofReal_mul, im_ofReal_mul, exp_ofReal_mul_I_re,
    exp_ofReal_mul_I_im, Real.cos_sub]
  linear_combination R ^ 2 * Real.sin_sq_add_cos_sq φ + r ^ 2 * Real.sin_sq_add_cos_sq θ

theorem poissonKernel_polar (R r φ θ : ℝ) :
    poissonKernel 0 (r * exp (θ * I)) (circleMap 0 R φ) =
      (R ^ 2 - r ^ 2) / (R ^ 2 - 2 * R * r * Real.cos (φ - θ) + r ^ 2) := by
  rw [poissonKernel_def]
  simp only [sub_zero, circleMap, zero_add]
  rw [norm_sq_polar_sub]
  simp only [norm_mul, norm_real, Real.norm_eq_abs, norm_exp_ofReal_mul_I, mul_one, sq_abs]

/-- **DLMF 1.9.34**: the Poisson integral in polar coordinates `z = r e^{iθ}`. -/
theorem dlmf_1_9_34 (h : ℂ → ℝ) (R r θ : ℝ) :
    poissonIntegral h R (r * exp (θ * I)) = 1 / (2 * π) * ∫ φ in (0 : ℝ)..2 * π,
      (R ^ 2 - r ^ 2) * h (R * exp (φ * I)) / (R ^ 2 - 2 * R * r * Real.cos (φ - θ) + r ^ 2) := by
  rw [poissonIntegral, Real.circleAverage_def, smul_eq_mul, one_div]
  congr 1
  refine intervalIntegral.integral_congr fun φ _ => ?_
  rw [Pi.smul_apply', poissonKernel_polar, smul_eq_mul]
  simp only [circleMap, zero_add]
  ring

theorem poissonIntegral_eq_re {h : ℂ → ℝ} {R : ℝ} (hR : 0 < R)
    (hh : ContinuousOn h (sphere 0 R)) {z : ℂ} (hz : z ∉ sphere (0 : ℂ) |R|) :
    poissonIntegral h R z =
      (Real.circleAverage (fun ζ => herglotzRieszKernel 0 z ζ • (h ζ : ℂ)) 0 R).re := by
  have hci : CircleIntegrable h 0 R := by
    apply ContinuousOn.circleIntegrable'
    rwa [abs_of_pos hR]
  rw [re_circleAverage_herglotzRieszKernel_smul hci hz, poissonIntegral,
    poissonKernel_eq_re_herglotzRieszKernel]

/-- DLMF §1.9(iii): the Poisson integral of a continuous `h` is harmonic in `|z| < R`. -/
theorem dlmf_1_9_34_harmonic {h : ℂ → ℝ} {R : ℝ} (hR : 0 < R)
    (hh : ContinuousOn h (sphere 0 R)) :
    InnerProductSpace.HarmonicOnNhd (poissonIntegral h R) (ball 0 R) := by
  intro z hz
  have hsph : ∀ w ∈ ball (0 : ℂ) R, w ∉ sphere (0 : ℂ) |R| := fun w hw hs => by
    rw [abs_of_pos hR, mem_sphere] at hs
    rw [mem_ball] at hw
    exact lt_irrefl _ (hs ▸ hw)
  have hci : CircleIntegrable (fun ζ => (h ζ : ℂ)) 0 R := by
    apply ContinuousOn.circleIntegrable'
    rw [abs_of_pos hR]
    exact continuous_ofReal.comp_continuousOn hh
  have hF := analyticOnNhd_circleAverage_herglotzRieszKernel_smul hci z (hsph z hz)
  have hev : poissonIntegral h R =ᶠ[𝓝 z] fun w =>
      (Real.circleAverage (fun ζ => herglotzRieszKernel 0 w ζ • (h ζ : ℂ)) 0 R).re :=
    eventually_of_mem (isOpen_ball.mem_nhds hz) fun w hw => poissonIntegral_eq_re hR hh (hsph w hw)
  exact (InnerProductSpace.harmonicAt_congr_nhds hev).mpr hF.harmonicAt_re

section PoissonBoundary

variable {h : ℂ → ℝ} {R : ℝ}

theorem norm_circleMap_zero_of_pos (hR : 0 < R) (φ : ℝ) : ‖circleMap 0 R φ‖ = R := by
  rw [norm_circleMap_zero, abs_of_pos hR]

theorem circleMap_sub_ne_zero (hR : 0 < R) {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) (φ : ℝ) :
    circleMap 0 R φ - z ≠ 0 := fun h0 => by
  have hzR : ‖z‖ < R := mem_ball_zero_iff.mp hz
  rw [sub_eq_zero] at h0
  rw [← h0, norm_circleMap_zero_of_pos hR] at hzR
  exact lt_irrefl _ hzR

theorem poissonKernel_circleMap (hR : 0 < R) (z : ℂ) (φ : ℝ) :
    poissonKernel 0 z (circleMap 0 R φ) = (R ^ 2 - ‖z‖ ^ 2) / ‖circleMap 0 R φ - z‖ ^ 2 := by
  rw [poissonKernel_def]
  simp [norm_circleMap_zero_of_pos hR]

theorem poissonKernel_circleMap_nonneg (hR : 0 < R) {z : ℂ} (hz : z ∈ ball (0 : ℂ) R)
    (φ : ℝ) : 0 ≤ poissonKernel 0 z (circleMap 0 R φ) := by
  have hzR : ‖z‖ < R := mem_ball_zero_iff.mp hz
  rw [poissonKernel_circleMap hR]
  exact div_nonneg (by nlinarith [norm_nonneg z]) (sq_nonneg _)

theorem continuous_poissonKernel_circleMap (hR : 0 < R) {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) :
    Continuous fun φ => poissonKernel 0 z (circleMap 0 R φ) := by
  simp_rw [poissonKernel_circleMap hR]
  exact continuous_const.div (((continuous_circleMap 0 R).sub continuous_const).norm.pow 2)
    fun φ => pow_ne_zero _ (norm_ne_zero_iff.mpr (circleMap_sub_ne_zero hR hz φ))

/-- `(2π)⁻¹ ∫₀^{2π} P(z, R e^{iφ}) dφ = 1` (the Poisson formula for `u = 1`). -/
theorem integral_poissonKernel_circleMap {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) :
    ∫ φ in (0 : ℝ)..2 * π, poissonKernel 0 z (circleMap 0 R φ) = 2 * π := by
  have h1 := InnerProductSpace.HarmonicOnNhd.circleAverage_poissonKernel_smul
    (f := fun _ => (1 : ℝ)) (c := 0) (R := R) (InnerProductSpace.harmonicOnNhd_const 1) hz
  rw [Real.circleAverage_def, smul_eq_mul] at h1
  simp only [Pi.smul_apply', smul_eq_mul, mul_one] at h1
  rw [inv_mul_eq_iff_eq_mul₀ (by positivity), mul_one] at h1
  exact h1

/-- DLMF §1.9(iii): the Poisson integral takes the boundary values `h`:
`u(z) → h(w)` as `z → w` within `|z| < R`, for `|w| = R`. -/
theorem dlmf_1_9_34_tendsto (hR : 0 < R) (hh : ContinuousOn h (sphere 0 R)) {w : ℂ}
    (hw : w ∈ sphere (0 : ℂ) R) :
    Tendsto (poissonIntegral h R) (𝓝[ball 0 R] w) (𝓝 (h w)) := by
  have hnormw : ‖w‖ = R := by simpa using hw
  have hhc : Continuous fun φ => h (circleMap 0 R φ) :=
    hh.comp_continuous (continuous_circleMap 0 R) fun φ => circleMap_mem_sphere 0 hR.le φ
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : ℂ) R).exists_bound_of_continuousOn hh
  set M' := max M 0 with hM'
  have hM'0 : 0 ≤ M' := le_max_right _ _
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδh⟩ := Metric.continuousWithinAt_iff.mp (hh w hw) (ε / 2) (half_pos hε)
  set η := ε * δ ^ 2 / (16 * (M' + 1)) with hηdef
  have hη : 0 < η := by positivity
  refine ⟨min (δ / 2) (η / (2 * R)), by positivity, ?_⟩
  intro z hz hzw
  have hzR : ‖z‖ < R := mem_ball_zero_iff.mp hz
  have hzw1 : dist z w < δ / 2 := lt_of_lt_of_le hzw (min_le_left _ _)
  have hzw2 : dist z w < η / (2 * R) := lt_of_lt_of_le hzw (min_le_right _ _)
  set g := R ^ 2 - ‖z‖ ^ 2 with hgdef
  have hg0 : 0 ≤ g := by nlinarith [norm_nonneg z]
  have hgap : g < η := by
    have h1 : R - ‖z‖ ≤ dist z w := by
      rw [dist_eq_norm, norm_sub_rev, ← hnormw]
      exact norm_sub_norm_le w z
    have h2 : (R - ‖z‖) * (R + ‖z‖) ≤ dist z w * (2 * R) :=
      mul_le_mul h1 (by linarith) (by linarith [norm_nonneg z]) dist_nonneg
    have h3 : dist z w * (2 * R) < η := (lt_div_iff₀ (by positivity)).mp hzw2
    have h4 : g = (R - ‖z‖) * (R + ‖z‖) := by rw [hgdef]; ring
    linarith
  set k := fun φ => poissonKernel 0 z (circleMap 0 R φ) with hkdef
  have hkc : Continuous k := continuous_poissonKernel_circleMap hR hz
  have hkint : ∫ φ in (0 : ℝ)..2 * π, k φ = 2 * π := integral_poissonKernel_circleMap hz
  set C := 8 * M' * g / δ ^ 2 with hCdef
  have hC0 : 0 ≤ C := by positivity
  have hrepr : poissonIntegral h R z - h w =
      (2 * π)⁻¹ * ∫ φ in (0 : ℝ)..2 * π, k φ * (h (circleMap 0 R φ) - h w) := by
    rw [poissonIntegral, Real.circleAverage_def, smul_eq_mul]
    simp only [Pi.smul_apply', smul_eq_mul]
    have hsplit : (fun φ => k φ * (h (circleMap 0 R φ) - h w)) =
        fun φ => k φ * h (circleMap 0 R φ) - k φ * h w := funext fun φ => by ring
    have i1 : IntervalIntegrable (fun φ => k φ * h (circleMap 0 R φ)) volume 0 (2 * π) :=
      (hkc.mul hhc).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun φ => k φ * h w) volume 0 (2 * π) :=
      (hkc.mul continuous_const).intervalIntegrable _ _
    show ((2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, k θ * h (circleMap 0 R θ)) - h w = _
    rw [hsplit, intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_mul_const, hkint]
    field_simp
  have hpt : ∀ φ, |k φ * (h (circleMap 0 R φ) - h w)| ≤ ε / 2 * k φ + C := by
    intro φ
    have hk0 : 0 ≤ k φ := poissonKernel_circleMap_nonneg hR hz φ
    rw [abs_mul, abs_of_nonneg hk0]
    by_cases hnear : dist (circleMap 0 R φ) w < δ
    · have h1 := hδh (circleMap_mem_sphere 0 hR.le φ) hnear
      rw [Real.dist_eq] at h1
      nlinarith
    · push Not at hnear
      have hfar : δ / 2 ≤ ‖circleMap 0 R φ - z‖ := by
        have := dist_triangle (circleMap 0 R φ) z w
        rw [dist_eq_norm (circleMap 0 R φ) z] at this
        linarith
      have hsq : δ ^ 2 ≤ 4 * ‖circleMap 0 R φ - z‖ ^ 2 := by nlinarith
      have hkle : k φ ≤ 4 * g / δ ^ 2 := by
        simp only [hkdef]
        rw [poissonKernel_circleMap hR, div_le_div_iff₀
          (pow_pos (norm_pos_iff.mpr (circleMap_sub_ne_zero hR hz φ)) 2) (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left hsq hg0]
      have hdiff : |h (circleMap 0 R φ) - h w| ≤ 2 * M' := by
        have h1 := hM _ (circleMap_mem_sphere 0 hR.le φ)
        have h2 := hM w hw
        rw [Real.norm_eq_abs] at h1 h2
        calc |h (circleMap 0 R φ) - h w| ≤ |h (circleMap 0 R φ)| + |h w| := abs_sub _ _
          _ ≤ 2 * M' := by linarith [le_max_left M 0]
      calc k φ * |h (circleMap 0 R φ) - h w| ≤ 4 * g / δ ^ 2 * (2 * M') :=
            mul_le_mul hkle hdiff (abs_nonneg _) (by positivity)
        _ = C := by rw [hCdef]; ring
        _ ≤ ε / 2 * k φ + C := le_add_of_nonneg_left (by positivity)
  have hint : |∫ φ in (0 : ℝ)..2 * π, k φ * (h (circleMap 0 R φ) - h w)| ≤
      ε / 2 * (2 * π) + C * (2 * π) := by
    refine (intervalIntegral.abs_integral_le_integral_abs (by positivity)).trans ?_
    have i1 : IntervalIntegrable (fun φ => |k φ * (h (circleMap 0 R φ) - h w)|) volume 0
        (2 * π) := (hkc.mul (hhc.sub continuous_const)).abs.intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun φ => ε / 2 * k φ) volume 0 (2 * π) :=
      (continuous_const.mul hkc).intervalIntegrable _ _
    have i3 : IntervalIntegrable (fun φ => ε / 2 * k φ + C) volume 0 (2 * π) :=
      i2.add intervalIntegrable_const
    refine (intervalIntegral.integral_mono_on (by positivity) i1 i3 fun φ _ => hpt φ).trans_eq ?_
    rw [intervalIntegral.integral_add i2 intervalIntegrable_const,
      intervalIntegral.integral_const_mul, hkint, intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hC : C < ε / 2 := by
    rw [hCdef, div_lt_iff₀ (by positivity)]
    have h1 : 8 * M' * g ≤ 8 * (M' + 1) * g := by nlinarith
    have h2 : 8 * (M' + 1) * g < 8 * (M' + 1) * η :=
      mul_lt_mul_of_pos_left hgap (by positivity)
    have h3 : 8 * (M' + 1) * η = ε / 2 * δ ^ 2 := by
      rw [hηdef]
      field_simp
      ring
    linarith
  rw [Real.dist_eq, hrepr, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹)]
  have hπ : (0 : ℝ) < 2 * π := by positivity
  calc (2 * π)⁻¹ * |∫ φ in (0 : ℝ)..2 * π, k φ * (h (circleMap 0 R φ) - h w)|
      ≤ (2 * π)⁻¹ * (ε / 2 * (2 * π) + C * (2 * π)) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = ε / 2 + C := by field_simp
    _ < ε := by linarith

end PoissonBoundary

end Azurite.DLMF
