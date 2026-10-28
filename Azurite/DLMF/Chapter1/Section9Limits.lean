/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section7
import Azurite.DLMF.Chapter1.Section9Integration
import Azurite.DLMF.Chapter1.Section9Series
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# DLMF §1.9(vii): Inversion of Limits

Formalizations of <https://dlmf.nist.gov/1.9.vii> (indices run over `ℕ`; DLMF's "positive
integers" for double sequences is an inessential shift).

* Double sequences: `DoubleSeqConverges` (1.9.64, `doubleSeqConverges_iff`: `atTop` on `ℕ × ℕ`),
  `dlmf_1_9_65`, `dlmf_1_9_65_swap` (if the inner limits exist, the repeated limits exist and
  equal the double limit).
* Double series: `doubleSeriesPartial` (1.9.66), `DoubleSeriesConvergesTo`,
  `DoubleSeriesConvergesAbsolutely`; `dlmf_1_9_67` (absolutely convergent ⇒ convergent, with
  sum equal to both repeated sums, each inner series convergent), via
  `summable_norm_of_doubleSeriesConvergesAbsolutely` (rectangle partial sums bound all finite
  sums) and `tendsto_range_product`.
* 1.9.68: `dlmf_1_9_68` (term-by-term integration along a finite contour `z : [a, b] → D`,
  continuous with integrable `z′`, for `∑ fₙ` converging uniformly on compact subsets of `D`).
* 1.9.69–1.9.71: `dlmf_1_9_69_iff_70` (the two conditions coincide, `lintegral_tsum`),
  `dlmf_1_9_71` (`(a, b)` finite or infinite as `eIoo` with `EReal` endpoints; via Mathlib's
  `integral_tsum`, the sum `∑' fₙ` agreeing a.e. with the uniform limit `g`).
-/

open Filter Topology Set Finset Metric Complex MeasureTheory

namespace Azurite.DLMF

/-! ### Double sequences -/

/-- **DLMF 1.9.64**: the double sequence `{z_{m,n}}` converges to `z`. -/
def DoubleSeqConverges {E : Type*} [SeminormedAddCommGroup E] (z : ℕ → ℕ → E) (L : E) : Prop :=
  ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n → ‖z m n - L‖ < ε

theorem doubleSeqConverges_iff {E : Type*} [SeminormedAddCommGroup E] {z : ℕ → ℕ → E} {L : E} :
    DoubleSeqConverges z L ↔ Tendsto (fun p : ℕ × ℕ => z p.1 p.2) atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  constructor
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    exact ⟨(N, N), fun p hp => by rw [dist_eq_norm]; exact hN _ _ hp.1 hp.2⟩
  · intro h ε hε
    obtain ⟨P, hP⟩ := h ε hε
    refine ⟨max P.1 P.2, fun m n hm hn => ?_⟩
    have := hP (m, n) ⟨le_of_max_le_left hm, le_of_max_le_right hn⟩
    rwa [dist_eq_norm] at this

/-- **DLMF 1.9.65**: if `z_{m,n} → z` and the inner limits `lim_n z_{m,n}` exist, the repeated
limit `lim_m lim_n z_{m,n}` exists and equals `z`. -/
theorem dlmf_1_9_65 {E : Type*} [SeminormedAddCommGroup E] {z : ℕ → ℕ → E} {L : E}
    (h : DoubleSeqConverges z L) {a : ℕ → E} (ha : ∀ m, Tendsto (z m) atTop (𝓝 (a m))) :
    Tendsto a atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := h (ε / 2) (half_pos hε)
  refine ⟨N, fun m hm => ?_⟩
  have hle : dist (a m) L ≤ ε / 2 := by
    refine le_of_tendsto ((ha m).dist tendsto_const_nhds) ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [dist_eq_norm]
    exact (hN m n hm hn).le
  linarith

/-- DLMF 1.9.65, the other repeated limit `lim_n lim_m z_{m,n}`. -/
theorem dlmf_1_9_65_swap {E : Type*} [SeminormedAddCommGroup E] {z : ℕ → ℕ → E} {L : E}
    (h : DoubleSeqConverges z L) {b : ℕ → E} (hb : ∀ n, Tendsto (fun m => z m n) atTop (𝓝 (b n))) :
    Tendsto b atTop (𝓝 L) :=
  dlmf_1_9_65 (z := fun n m => z m n) (fun ε hε => (h ε hε).imp fun _ hN m n hm hn =>
    hN n m hn hm) hb

/-! ### Double series -/

/-- **DLMF 1.9.66**: the partial sums `z_{p,q} = ∑_{m=0}^{p} ∑_{n=0}^{q} ζ_{m,n}`. -/
def doubleSeriesPartial {E : Type*} [AddCommMonoid E] (ζ : ℕ → ℕ → E) (p q : ℕ) : E :=
  ∑ m ∈ range (p + 1), ∑ n ∈ range (q + 1), ζ m n

/-- The double series converges (to `s`). -/
def DoubleSeriesConvergesTo {E : Type*} [SeminormedAddCommGroup E] (ζ : ℕ → ℕ → E) (s : E) :
    Prop :=
  DoubleSeqConverges (doubleSeriesPartial ζ) s

/-- The double series converges absolutely: it converges with `ζ_{m,n}` replaced by
`|ζ_{m,n}|`. -/
def DoubleSeriesConvergesAbsolutely {E : Type*} [SeminormedAddCommGroup E] (ζ : ℕ → ℕ → E) :
    Prop :=
  ∃ s : ℝ, DoubleSeriesConvergesTo (fun m n => ‖ζ m n‖) s

theorem doubleSeriesPartial_eq_sum_product {E : Type*} [AddCommMonoid E] (ζ : ℕ → ℕ → E)
    (p q : ℕ) :
    doubleSeriesPartial ζ p q = ∑ x ∈ range (p + 1) ×ˢ range (q + 1), ζ x.1 x.2 := by
  rw [doubleSeriesPartial, sum_product]

theorem tendsto_range_product :
    Tendsto (fun p : ℕ × ℕ => range (p.1 + 1) ×ˢ range (p.2 + 1)) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro s
  refine ⟨(s.sup fun x => max x.1 x.2, s.sup fun x => max x.1 x.2), fun p hp x hx => ?_⟩
  have h : max x.1 x.2 ≤ s.sup fun x => max x.1 x.2 :=
    Finset.le_sup (f := fun x : ℕ × ℕ => max x.1 x.2) hx
  have h1 : x.1 ≤ max x.1 x.2 := le_max_left _ _
  have h2 : x.2 ≤ max x.1 x.2 := le_max_right _ _
  have hp1 : (s.sup fun x => max x.1 x.2) ≤ p.1 := hp.1
  have hp2 : (s.sup fun x => max x.1 x.2) ≤ p.2 := hp.2
  simp only [Finset.mem_product, Finset.mem_range]
  constructor <;> omega

/-- An absolutely convergent double series is summable (over `ℕ × ℕ`) in norm. -/
theorem summable_norm_of_doubleSeriesConvergesAbsolutely {E : Type*} [SeminormedAddCommGroup E]
    {ζ : ℕ → ℕ → E} (h : DoubleSeriesConvergesAbsolutely ζ) :
    Summable fun x : ℕ × ℕ => ‖ζ x.1 x.2‖ := by
  obtain ⟨S, hS⟩ := h
  have hT := doubleSeqConverges_iff.mp hS
  have hle : ∀ p q, doubleSeriesPartial (fun m n => ‖ζ m n‖) p q ≤ S := by
    intro p q
    refine ge_of_tendsto hT ?_
    filter_upwards [eventually_ge_atTop (p, q)] with r hr
    have hr1 : p ≤ r.1 := hr.1
    have hr2 : q ≤ r.2 := hr.2
    rw [doubleSeriesPartial_eq_sum_product, doubleSeriesPartial_eq_sum_product]
    exact sum_le_sum_of_subset_of_nonneg
      (product_subset_product (range_subset_range.mpr (by omega))
        (range_subset_range.mpr (by omega))) fun _ _ _ => norm_nonneg _
  refine summable_of_sum_le (c := S) (fun _ => norm_nonneg _) fun u => ?_
  obtain ⟨p, hp⟩ := (tendsto_atTop_atTop.mp tendsto_range_product) u
  refine (sum_le_sum_of_subset_of_nonneg (hp p le_rfl) fun _ _ _ => norm_nonneg _).trans ?_
  rw [← doubleSeriesPartial_eq_sum_product (fun m n => ‖ζ m n‖)]
  exact hle p.1 p.2

/-- **DLMF 1.9.67**: an absolutely convergent double series is convergent, and its sum is given by
either repeated sum (each inner series converging, in DLMF's sense). -/
theorem dlmf_1_9_67 {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] {ζ : ℕ → ℕ → E}
    (h : DoubleSeriesConvergesAbsolutely ζ) :
    ∃ s, DoubleSeriesConvergesTo ζ s ∧
      (∀ m, SeriesConverges (ζ m) (∑' n, ζ m n)) ∧
      SeriesConverges (fun m => ∑' n, ζ m n) s ∧
      (∀ n, SeriesConverges (fun m => ζ m n) (∑' m, ζ m n)) ∧
      SeriesConverges (fun n => ∑' m, ζ m n) s := by
  have hsn := summable_norm_of_doubleSeriesConvergesAbsolutely h
  set f : ℕ × ℕ → E := fun x => ζ x.1 x.2 with hf
  have hs : Summable f := hsn.of_norm
  set s := ∑' x, f x
  have hfs : HasSum f s := hs.hasSum
  refine ⟨s, ?_, fun m => ?_, ?_, fun n => ?_, ?_⟩
  · rw [DoubleSeriesConvergesTo, doubleSeqConverges_iff]
    have := hfs.comp tendsto_range_product
    refine this.congr fun p => ?_
    rw [Function.comp_apply, doubleSeriesPartial_eq_sum_product]
  · exact seriesConverges_iff.mpr (hs.prod_factor m).hasSum.tendsto_sum_nat
  · exact seriesConverges_iff.mpr
      (hfs.prod_fiberwise fun m => (hs.prod_factor m).hasSum).tendsto_sum_nat
  · have hs' : Summable fun x : ℕ × ℕ => f (x.2, x.1) :=
      hs.comp_injective (fun x y hxy => by
        simp only [Prod.mk.injEq] at hxy
        exact Prod.ext hxy.2 hxy.1)
    exact seriesConverges_iff.mpr (hs'.prod_factor n).hasSum.tendsto_sum_nat
  · have hfs' : HasSum (fun x : ℕ × ℕ => f (x.2, x.1)) s :=
      (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hfs
    have hs' := hfs'.summable
    exact seriesConverges_iff.mpr
      (hfs'.prod_fiberwise fun n => (hs'.prod_factor n).hasSum).tendsto_sum_nat

/-! ### Term-by-term integration -/

/-- **DLMF 1.9.68** (term-by-term integration along a contour): if the `fₙ` are continuous on `D`
and `∑ fₙ` converges uniformly on every compact subset of `D` to `g`, then for a finite contour
`C ⊆ D` (`z` continuous on `[a, b]` with integrable `z′`), `∑ ∫_C fₙ = ∫_C g`. -/
theorem dlmf_1_9_68 {D : Set ℂ} {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ} (hf : ∀ n, ContinuousOn (f n) D)
    (hu : ∀ K ⊆ D, IsCompact K → SeriesConvergesUniformlyOn f g K) {z : ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b) (hz : ContinuousOn z (Set.Icc a b))
    (hz' : IntervalIntegrable (deriv z) volume a b)
    (hzD : z '' Set.Icc a b ⊆ D) :
    SeriesConverges (fun n => contourIntegral (f n) z a b) (contourIntegral g z a b) := by
  set K := z '' Set.Icc a b
  have hK : IsCompact K := isCompact_Icc.image_of_continuousOn hz
  have hKu := hu K hzD hK
  have hS : ∀ n, ContinuousOn (fun w => partialSum (fun k => f k w) n) D := fun n =>
    continuousOn_finsetSum _ fun k _ => hf k
  have hg : ContinuousOn g K :=
    hKu.continuousOn (Eventually.of_forall fun n => (hS n).mono hzD).frequently
  have huIcc : Set.uIcc a b = Set.Icc a b := uIcc_of_le hab
  have hmaps : MapsTo z (Set.Icc a b) K := fun t ht => ⟨t, ht, rfl⟩
  have hint : ∀ {φ : ℂ → ℂ}, ContinuousOn φ K →
      IntervalIntegrable (fun t => φ (z t) * deriv z t) volume a b := fun hφ =>
    hz'.continuousOn_mul (by rw [huIcc]; exact hφ.comp hz hmaps)
  have hpartial : ∀ n, partialSum (fun k => contourIntegral (f k) z a b) n =
      contourIntegral (fun w => partialSum (fun k => f k w) n) z a b := by
    intro n
    unfold partialSum contourIntegral
    simp only [Finset.sum_mul]
    rw [intervalIntegral.integral_finsetSum fun k _ => hint ((hf k).mono hzD)]
  have hL : 0 ≤ ∫ t in a..b, ‖deriv z t‖ :=
    intervalIntegral.integral_nonneg hab fun _ _ => norm_nonneg _
  unfold SeriesConverges
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ := ε / ((∫ t in a..b, ‖deriv z t‖) + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨N, hN⟩ := dlmf_1_9_47.mp hKu δ hδ0
  refine ⟨N, fun n hn => ?_⟩
  rw [hpartial, dist_eq_norm]
  unfold contourIntegral
  rw [← intervalIntegral.integral_sub (hint ((hS n).mono hzD)) (hint hg)]
  calc ‖∫ t in a..b, (partialSum (fun k => f k (z t)) n * deriv z t - g (z t) * deriv z t)‖
      ≤ ∫ t in a..b, δ * ‖deriv z t‖ := by
        refine intervalIntegral.norm_integral_le_of_norm_le hab (ae_of_all _ fun t ht => ?_)
          (hz'.norm.const_mul δ)
        rw [← sub_mul, norm_mul]
        exact mul_le_mul_of_nonneg_right
          (hN n hn (z t) (hmaps (Ioc_subset_Icc_self ht))).le (norm_nonneg _)
    _ = δ * ∫ t in a..b, ‖deriv z t‖ := intervalIntegral.integral_const_mul _ _
    _ < ε := by
        rw [hδ, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith

/-! ### Dominated convergence for series -/

/-- **DLMF 1.9.69 ⇔ 1.9.70**: for measurable terms the two conditions coincide
(`∫ ∑ |fₙ| = ∑ ∫ |fₙ|` in `[0, ∞]`). -/
theorem dlmf_1_9_69_iff_70 {a b : EReal} {f : ℕ → ℝ → ℂ}
    (hf : ∀ n, ContinuousOn (f n) (eIoo a b)) :
    (∫⁻ t in eIoo a b, ∑' n, ‖f n t‖ₑ) < ⊤ ↔ ∑' n, ∫⁻ t in eIoo a b, ‖f n t‖ₑ < ⊤ := by
  rw [lintegral_tsum fun n =>
    ((hf n).aestronglyMeasurable (isOpen_eIoo a b).measurableSet).enorm]

/-- **DLMF 1.9.71** (dominated convergence for series): if the `fₙ` are continuous on `(a, b)`,
`∑ fₙ` converges uniformly on compact subintervals to `g`, and 1.9.69 or 1.9.70 holds, then
`∑ ∫ₐᵇ fₙ = ∫ₐᵇ g`. -/
theorem dlmf_1_9_71 {a b : EReal} {f : ℕ → ℝ → ℂ} {g : ℝ → ℂ}
    (hf : ∀ n, ContinuousOn (f n) (eIoo a b))
    (hu : ∀ c d, Set.Icc c d ⊆ eIoo a b → SeriesConvergesUniformlyOn f g (Set.Icc c d))
    (hcond : (∫⁻ t in eIoo a b, ∑' n, ‖f n t‖ₑ) < ⊤ ∨ ∑' n, ∫⁻ t in eIoo a b, ‖f n t‖ₑ < ⊤) :
    SeriesConverges (fun n => ∫ t in eIoo a b, f n t) (∫ t in eIoo a b, g t) := by
  set I := eIoo a b
  have hIm : MeasurableSet I := (isOpen_eIoo a b).measurableSet
  have hmeas : ∀ n, AEStronglyMeasurable (f n) (volume.restrict I) := fun n =>
    (hf n).aestronglyMeasurable hIm
  have h70 : ∑' n, ∫⁻ t in I, ‖f n t‖ₑ ≠ ⊤ := by
    rcases hcond with h | h
    · exact ((dlmf_1_9_69_iff_70 hf).mp h).ne
    · exact h.ne
  have h69 : (∫⁻ t in I, ∑' n, ‖f n t‖ₑ) ≠ ⊤ := by
    rw [lintegral_tsum fun n => (hmeas n).enorm]
    exact h70
  -- `g = ∑' fₙ` almost everywhere on `(a, b)`
  have hae : ∀ᵐ t ∂(volume.restrict I), g t = ∑' n, f n t := by
    have hfin := ae_lt_top' (AEMeasurable.tsum fun n => (hmeas n).enorm) h69
    filter_upwards [hfin, ae_restrict_mem hIm] with t ht htI
    have hsum : Summable fun n => f n t := by
      refine Summable.of_nnnorm ?_
      exact ENNReal.tsum_coe_ne_top_iff_summable.mp ht.ne
    have hpt : Tendsto (fun n => partialSum (fun k => f k t) n) atTop (𝓝 (g t)) :=
      (hu t t (by rw [Set.Icc_self]; exact singleton_subset_iff.mpr htI)).tendsto_at
        (Set.left_mem_Icc.mpr le_rfl)
    exact tendsto_nhds_unique hpt (seriesConverges_iff.mpr hsum.hasSum.tendsto_sum_nat)
  have hint := integral_tsum hmeas h70
  rw [integral_congr_ae hae, hint]
  have hsum : Summable fun n => ∫ t in I, f n t := by
    refine Summable.of_norm_bounded (g := fun n => (∫⁻ t in I, ‖f n t‖ₑ).toReal)
      (ENNReal.summable_toReal h70) fun n => ?_
    have := norm_integral_le_lintegral_norm (μ := volume.restrict I) (f n)
    simpa only [ofReal_norm] using this
  exact seriesConverges_iff.mpr hsum.hasSum.tendsto_sum_nat

end Azurite.DLMF
