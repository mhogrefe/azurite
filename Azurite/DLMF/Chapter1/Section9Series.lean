/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# DLMF §1.9(v): Infinite Sequences and Series

Formalizations of <https://dlmf.nist.gov/1.9.v>.  DLMF's convergence of a series is convergence of
the partial sums `sₙ = ∑_{k=0}^{n} zₖ` (`SeriesConverges`), which differs from Mathlib's
unconditional `Summable`; absolute convergence (`SeriesConvergesAbsolutely`) is shown equivalent
to `Summable ‖zₙ‖`.

* Sequences: `dlmf_1_9_v_tendsto_iff`, `dlmf_1_9_v_converges_iff` (`zₙ` converges iff `xₙ` and
  `yₙ` do).
* Series: `partialSum`, `SeriesConverges`, `SeriesDiverges`, `SeriesConvergesAbsolutely`;
  `dlmf_1_9_v_absolutely` (absolutely convergent ⇒ convergent), `SeriesConverges.tendsto_zero`.
* Root and ratio tests: `dlmf_1_9_v_root_lt`, `dlmf_1_9_v_ratio_lt` (absolute convergence;
  the ratio test assumes `zₙ ≠ 0` eventually, implicit in DLMF since `z_{n+1}/zₙ` must make
  sense), `dlmf_1_9_v_root_gt`, `dlmf_1_9_v_ratio_gt` (divergence, absolute and outright).
* 1.9.46: `ConvergesPointwiseOn`, `dlmf_1_9_46_of_uniform`; 1.9.47: `dlmf_1_9_47` (Mathlib's
  `TendstoUniformlyOn` in DLMF's `ε`–`N` form); `SeriesConvergesUniformlyOn`.
* Weierstrass `M`-test: `dlmf_1_9_v_Mtest` (sum `∑' fₙ(z)`).
* Doubly-infinite series: `doublePartialSum` (`∑_{n=−M}^{N}`, `M`, `N → ∞` independently),
  `DoubleSeriesConverges`, `DoubleSeriesConvergesUniformlyOn`; `dlmf_1_9_v_doubly`,
  `dlmf_1_9_v_doubly_uniform` (convergent (uniformly) iff both halves are), via
  `doublePartialSum_eq` and `uniformCauchySeqOn_of_split`.
-/

open Filter Topology Set Finset Metric Complex

namespace Azurite.DLMF

/-! ### Sequences -/

/-- DLMF §1.9(v): `zₙ → z` iff `xₙ → ℜz` and `yₙ → ℑz`. -/
theorem dlmf_1_9_v_tendsto_iff {z : ℕ → ℂ} {w : ℂ} :
    Tendsto z atTop (𝓝 w) ↔
      Tendsto (fun n => (z n).re) atTop (𝓝 w.re) ∧ Tendsto (fun n => (z n).im) atTop (𝓝 w.im) := by
  refine ⟨fun h => ⟨(continuous_re.tendsto w).comp h, (continuous_im.tendsto w).comp h⟩,
    fun ⟨hx, hy⟩ => ?_⟩
  have := ((continuous_ofReal.tendsto _).comp hx).add
    (((continuous_ofReal.tendsto _).comp hy).mul_const I)
  simpa only [Function.comp_def, re_add_im] using this

/-- DLMF §1.9(v): `{zₙ}` converges iff `{xₙ}` and `{yₙ}` separately converge. -/
theorem dlmf_1_9_v_converges_iff {z : ℕ → ℂ} :
    (∃ w, Tendsto z atTop (𝓝 w)) ↔
      (∃ x, Tendsto (fun n => (z n).re) atTop (𝓝 x)) ∧
        ∃ y, Tendsto (fun n => (z n).im) atTop (𝓝 y) := by
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨hx, hy⟩ := dlmf_1_9_v_tendsto_iff.mp hw
    exact ⟨⟨_, hx⟩, ⟨_, hy⟩⟩
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    exact ⟨⟨x, y⟩, dlmf_1_9_v_tendsto_iff.mpr ⟨hx, hy⟩⟩

/-! ### Series -/

/-- The partial sum `sₙ = ∑_{k=0}^{n} zₖ`. -/
def partialSum {E : Type*} [AddCommMonoid E] (z : ℕ → E) (n : ℕ) : E :=
  ∑ k ∈ range (n + 1), z k

/-- `∑ zₙ` converges (to `s`): `sₙ → s`. -/
def SeriesConverges {E : Type*} [AddCommMonoid E] [TopologicalSpace E] (z : ℕ → E) (s : E) :
    Prop :=
  Tendsto (partialSum z) atTop (𝓝 s)

/-- `∑ zₙ` diverges: `sₙ` does not converge. -/
def SeriesDiverges {E : Type*} [AddCommMonoid E] [TopologicalSpace E] (z : ℕ → E) : Prop :=
  ¬ ∃ s, SeriesConverges z s

/-- `∑ zₙ` converges absolutely: `∑ |zₙ|` converges. -/
def SeriesConvergesAbsolutely {E : Type*} [SeminormedAddCommGroup E] (z : ℕ → E) : Prop :=
  ∃ s : ℝ, SeriesConverges (fun n => ‖z n‖) s

theorem seriesConverges_iff {E : Type*} [AddCommMonoid E] [TopologicalSpace E] {z : ℕ → E}
    {s : E} : SeriesConverges z s ↔ Tendsto (fun n => ∑ k ∈ range n, z k) atTop (𝓝 s) :=
  tendsto_add_atTop_iff_nat (f := fun n => ∑ k ∈ range n, z k) 1

theorem seriesConvergesAbsolutely_iff {E : Type*} [SeminormedAddCommGroup E] {z : ℕ → E} :
    SeriesConvergesAbsolutely z ↔ Summable fun n => ‖z n‖ := by
  constructor
  · rintro ⟨s, hs⟩
    exact ((hasSum_iff_tendsto_nat_of_nonneg (fun n => norm_nonneg _) s).mpr
      (seriesConverges_iff.mp hs)).summable
  · intro h
    exact ⟨_, seriesConverges_iff.mpr h.hasSum.tendsto_sum_nat⟩

/-- DLMF §1.9(v): absolutely convergent series are convergent. -/
theorem dlmf_1_9_v_absolutely {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {z : ℕ → E} (h : SeriesConvergesAbsolutely z) : ∃ s, SeriesConverges z s :=
  ⟨_, seriesConverges_iff.mpr
    (seriesConvergesAbsolutely_iff.mp h).of_norm.hasSum.tendsto_sum_nat⟩

/-- The terms of a convergent series tend to `0`. -/
theorem SeriesConverges.tendsto_zero {E : Type*} [NormedAddCommGroup E] {z : ℕ → E} {s : E}
    (h : SeriesConverges z s) : Tendsto z atTop (𝓝 0) := by
  have h1 : Tendsto (fun n => partialSum z (n + 1) - partialSum z n) atTop (𝓝 (s - s)) :=
    ((tendsto_add_atTop_iff_nat 1).mpr h).sub h
  rw [sub_self] at h1
  refine (tendsto_add_atTop_iff_nat 1).mp (h1.congr fun n => ?_)
  simp [partialSum, sum_range_succ]

theorem seriesDiverges_of_norm_ge {E : Type*} [NormedAddCommGroup E] {z : ℕ → E} {c : ℝ}
    (hc : 0 < c) (h : ∀ᶠ n in atTop, c ≤ ‖z n‖) : SeriesDiverges z := by
  rintro ⟨s, hs⟩
  have h0 := (tendsto_norm_zero.comp hs.tendsto_zero).eventually (gt_mem_nhds hc)
  obtain ⟨n, hn1, hn2⟩ := (h.and h0).exists
  exact absurd hn1 (not_le.mpr hn2)

theorem not_seriesConvergesAbsolutely_of_diverges {E : Type*} [NormedAddCommGroup E]
    [CompleteSpace E] {z : ℕ → E} (h : SeriesDiverges z) : ¬ SeriesConvergesAbsolutely z :=
  fun ha => h (dlmf_1_9_v_absolutely ha)

/-- DLMF §1.9(v) (root test): if `|zₙ|^{1/n} → l < 1`, the series converges absolutely. -/
theorem dlmf_1_9_v_root_lt {E : Type*} [NormedAddCommGroup E] {z : ℕ → E} {l : ℝ} (hl : l < 1)
    (h : Tendsto (fun n : ℕ => ‖z n‖ ^ ((1 : ℝ) / n)) atTop (𝓝 l)) :
    SeriesConvergesAbsolutely z := by
  have hl0 : 0 ≤ l := ge_of_tendsto' h fun n => by positivity
  obtain ⟨r, hlr, hr1⟩ := exists_between hl
  have hr0 : 0 < r := hl0.trans_lt hlr
  rw [seriesConvergesAbsolutely_iff]
  refine Summable.of_norm_bounded_eventually (g := fun n => r ^ n)
    (summable_geometric_of_lt_one hr0.le hr1) ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [h.eventually (gt_mem_nhds hlr), eventually_ge_atTop 1] with n hn hn1
  rw [norm_norm]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn1)
  calc ‖z n‖ = (‖z n‖ ^ ((1 : ℝ) / n)) ^ n := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), one_div_mul_cancel hn0,
          Real.rpow_one]
    _ ≤ r ^ n := pow_le_pow_left₀ (by positivity) hn.le n

/-- DLMF §1.9(v) (root test): if `|zₙ|^{1/n} → l > 1`, the series diverges (absolutely and
outright: the terms do not tend to `0`). -/
theorem dlmf_1_9_v_root_gt {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] {z : ℕ → E}
    {l : ℝ} (hl : 1 < l) (h : Tendsto (fun n : ℕ => ‖z n‖ ^ ((1 : ℝ) / n)) atTop (𝓝 l)) :
    SeriesDiverges z ∧ ¬ SeriesConvergesAbsolutely z := by
  have hd : SeriesDiverges z := by
    refine seriesDiverges_of_norm_ge one_pos ?_
    filter_upwards [h.eventually (lt_mem_nhds hl), eventually_ge_atTop 1] with n hn hn1
    by_contra hlt
    push Not at hlt
    have : ‖z n‖ ^ ((1 : ℝ) / n) ≤ 1 := Real.rpow_le_one (norm_nonneg _) hlt.le (by positivity)
    linarith
  exact ⟨hd, not_seriesConvergesAbsolutely_of_diverges hd⟩

/-- DLMF §1.9(v) (ratio test): if `|z_{n+1}/zₙ| → l < 1` (`zₙ ≠ 0` eventually), the series
converges absolutely. -/
theorem dlmf_1_9_v_ratio_lt {z : ℕ → ℂ} {l : ℝ} (hl : l < 1) (hz : ∀ᶠ n in atTop, z n ≠ 0)
    (h : Tendsto (fun n => ‖z (n + 1) / z n‖) atTop (𝓝 l)) : SeriesConvergesAbsolutely z := by
  rw [seriesConvergesAbsolutely_iff]
  refine summable_of_ratio_test_tendsto_lt_one hl ?_ ?_
  · filter_upwards [hz] with n hn
    exact norm_ne_zero_iff.mpr hn
  · simpa only [norm_norm, norm_div] using h

/-- DLMF §1.9(v) (ratio test): if `|z_{n+1}/zₙ| → l > 1`, the series diverges (absolutely and
outright). -/
theorem dlmf_1_9_v_ratio_gt {z : ℕ → ℂ} {l : ℝ} (hl : 1 < l)
    (h : Tendsto (fun n => ‖z (n + 1) / z n‖) atTop (𝓝 l)) :
    SeriesDiverges z ∧ ¬ SeriesConvergesAbsolutely z := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h.eventually (lt_mem_nhds hl))
  have hpos : ∀ n ≥ N, 0 < ‖z n‖ := fun n hn => by
    have := hN n hn
    by_contra h0
    have h0' : z n = 0 := norm_eq_zero.mp (le_antisymm (not_lt.mp h0) (norm_nonneg _))
    rw [h0', div_zero, norm_zero] at this
    linarith
  have hmono : ∀ n ≥ N, ‖z N‖ ≤ ‖z n‖ := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact le_rfl
    | succ n hn ih =>
      have h1 := hN n hn
      rw [norm_div, one_lt_div (hpos n hn)] at h1
      linarith
  have hd : SeriesDiverges z :=
    seriesDiverges_of_norm_ge (hpos N le_rfl) (eventually_atTop.mpr ⟨N, hmono⟩)
  exact ⟨hd, not_seriesConvergesAbsolutely_of_diverges hd⟩

/-! ### Sequences and series of functions -/

/-- **DLMF 1.9.46**: pointwise convergence on `S`. -/
def ConvergesPointwiseOn {α E : Type*} [TopologicalSpace E] (F : ℕ → α → E) (f : α → E)
    (S : Set α) : Prop :=
  ∀ z ∈ S, Tendsto (fun n => F n z) atTop (𝓝 (f z))

/-- **DLMF 1.9.47**: uniform convergence on `S` (Mathlib's `TendstoUniformlyOn`) in DLMF's
`ε`–`N` form. -/
theorem dlmf_1_9_47 {α E : Type*} [SeminormedAddCommGroup E] {F : ℕ → α → E} {f : α → E}
    {S : Set α} : TendstoUniformlyOn F f atTop S ↔
      ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ z ∈ S, ‖F n z - f z‖ < ε := by
  rw [Metric.tendstoUniformlyOn_iff]
  simp only [eventually_atTop, dist_eq_norm, norm_sub_rev]

/-- Uniform convergence implies pointwise convergence. -/
theorem dlmf_1_9_46_of_uniform {α E : Type*} [SeminormedAddCommGroup E] {F : ℕ → α → E}
    {f : α → E} {S : Set α} (h : TendstoUniformlyOn F f atTop S) : ConvergesPointwiseOn F f S :=
  fun _ hz => h.tendsto_at hz

/-- `∑ fₙ(z)` converges uniformly on `S` (to `g`): the partial sums converge uniformly. -/
def SeriesConvergesUniformlyOn {α E : Type*} [AddCommMonoid E] [UniformSpace E]
    (F : ℕ → α → E) (g : α → E) (S : Set α) : Prop :=
  TendstoUniformlyOn (fun n z => partialSum (fun k => F k z) n) g atTop S

theorem eventually_atTop_add_one_iff {p : ℕ → Prop} :
    (∀ᶠ n in atTop, p (n + 1)) ↔ ∀ᶠ n in atTop, p n := by
  simp only [eventually_atTop]
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨N + 1, fun n hn => ?_⟩
    have := hN (n - 1) (by omega)
    rwa [Nat.sub_add_cancel (by omega)] at this
  · rintro ⟨N, hN⟩
    exact ⟨N, fun n hn => hN _ (by omega)⟩

theorem tendstoUniformlyOn_add_one_iff {α E : Type*} [PseudoMetricSpace E] {F : ℕ → α → E}
    {f : α → E} {S : Set α} :
    TendstoUniformlyOn (fun n => F (n + 1)) f atTop S ↔ TendstoUniformlyOn F f atTop S := by
  rw [Metric.tendstoUniformlyOn_iff, Metric.tendstoUniformlyOn_iff]
  exact forall₂_congr fun ε _ => eventually_atTop_add_one_iff
    (p := fun n => ∀ x ∈ S, dist (f x) (F n x) < ε)

theorem seriesConvergesUniformlyOn_iff {α E : Type*} [SeminormedAddCommGroup E]
    {F : ℕ → α → E} {g : α → E} {S : Set α} : SeriesConvergesUniformlyOn F g S ↔
      TendstoUniformlyOn (fun n z => ∑ k ∈ range n, F k z) g atTop S :=
  tendstoUniformlyOn_add_one_iff (F := fun n z => ∑ k ∈ range n, F k z)

/-- **Weierstrass `M`-test** (DLMF §1.9(v)): if `∑ Mₙ` converges and `|fₙ(z)| ≤ Mₙ` on `S`, then
`∑ fₙ(z)` converges uniformly on `S`. -/
theorem dlmf_1_9_v_Mtest {α E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {F : ℕ → α → E} {M : ℕ → ℝ} {S : Set α} (hM : ∃ s, SeriesConverges M s)
    (hb : ∀ n, ∀ z ∈ S, ‖F n z‖ ≤ M n) :
    SeriesConvergesUniformlyOn F (fun z => ∑' n, F n z) S := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨z₀, hz₀⟩
  · exact tendstoUniformlyOn_empty
  have hM0 : ∀ n, 0 ≤ M n := fun n => (norm_nonneg _).trans (hb n z₀ hz₀)
  obtain ⟨s, hs⟩ := hM
  have hsum : Summable M :=
    ((hasSum_iff_tendsto_nat_of_nonneg hM0 s).mpr (seriesConverges_iff.mp hs)).summable
  exact seriesConvergesUniformlyOn_iff.mpr
    (tendstoUniformlyOn_tsum_nat hsum fun n z hz => hb n z hz)

/-! ### Doubly-infinite series -/

/-- `∑_{n=−M}^{N} fₙ`. -/
def doublePartialSum {E : Type*} [AddCommMonoid E] (f : ℤ → E) (p : ℕ × ℕ) : E :=
  ∑ n ∈ Icc (-(p.1 : ℤ)) p.2, f n

/-- `∑_{n=−∞}^{∞} fₙ` converges uniformly on `S`: `∑_{n=−M}^{N} fₙ(z) → g(z)` uniformly as `M`
and `N` tend to `∞` independently. -/
def DoubleSeriesConvergesUniformlyOn {α E : Type*} [AddCommMonoid E] [UniformSpace E]
    (F : ℤ → α → E) (g : α → E) (S : Set α) : Prop :=
  TendstoUniformlyOn (fun p z => doublePartialSum (fun n => F n z) p) g atTop S

/-- `∑_{n=−∞}^{∞} fₙ` converges to `s`. -/
def DoubleSeriesConverges {E : Type*} [AddCommMonoid E] [TopologicalSpace E] (f : ℤ → E)
    (s : E) : Prop :=
  Tendsto (doublePartialSum f) atTop (𝓝 s)

theorem sum_Icc_zero_eq {E : Type*} [AddCommMonoid E] (f : ℤ → E) (N : ℕ) :
    ∑ n ∈ Icc (0 : ℤ) N, f n = ∑ k ∈ range (N + 1), f k := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.cast_add, Nat.cast_one, ← insert_Icc_right_eq_Icc_add_one (by positivity),
      sum_insert (by simp), ih, sum_range_succ (fun k : ℕ => f k) (N + 1), add_comm, Nat.cast_add,
      Nat.cast_one]

theorem doublePartialSum_eq {E : Type*} [AddCommMonoid E] (f : ℤ → E) (M N : ℕ) :
    doublePartialSum f (M, N) =
      partialSum (fun k => f k) N + ∑ k ∈ range M, f (-((k + 1 : ℕ) : ℤ)) := by
  unfold doublePartialSum partialSum
  induction M with
  | zero => simp [sum_Icc_zero_eq]
  | succ M ih =>
    have hle : -((M + 1 : ℕ) : ℤ) ≤ N := by omega
    rw [← insert_Icc_add_one_left_eq_Icc hle, sum_insert (by simp),
      show -((M + 1 : ℕ) : ℤ) + 1 = -(M : ℤ) by push_cast; ring, ih,
      sum_range_succ (fun k : ℕ => f (-((k + 1 : ℕ) : ℤ))) M]
    abel

/-- A uniformly convergent "split" double sequence has uniformly Cauchy halves. -/
theorem uniformCauchySeqOn_of_split {α E : Type*} [NormedAddCommGroup E] {A B : ℕ → α → E}
    {g : α → E} {S : Set α}
    (h : TendstoUniformlyOn (fun p : ℕ × ℕ => fun z => A p.2 z + B p.1 z) g atTop S) :
    UniformCauchySeqOn A atTop S ∧ UniformCauchySeqOn B atTop S := by
  rw [Metric.tendstoUniformlyOn_iff] at h
  constructor
  all_goals
    intro u hu
    obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.mp hu
    obtain ⟨P, hP⟩ := eventually_atTop.mp (h (ε / 2) (half_pos hε))
  · filter_upwards [prod_mem_prod (Ici_mem_atTop P.2) (Ici_mem_atTop P.2)] with m hm z hz
    refine hεu ?_
    have h1 := hP (P.1, m.1) ⟨le_rfl, hm.1⟩ z hz
    have h2 := hP (P.1, m.2) ⟨le_rfl, hm.2⟩ z hz
    simp only at h1 h2
    rw [← dist_add_right (A m.1 z) (A m.2 z) (B P.1 z)]
    linarith [dist_triangle_left (A m.1 z + B P.1 z) (A m.2 z + B P.1 z) (g z)]
  · filter_upwards [prod_mem_prod (Ici_mem_atTop P.1) (Ici_mem_atTop P.1)] with m hm z hz
    refine hεu ?_
    have h1 := hP (m.1, P.2) ⟨hm.1, le_rfl⟩ z hz
    have h2 := hP (m.2, P.2) ⟨hm.2, le_rfl⟩ z hz
    simp only at h1 h2
    rw [← dist_add_left (A P.2 z) (B m.1 z) (B m.2 z)]
    linarith [dist_triangle_left (A P.2 z + B m.1 z) (A P.2 z + B m.2 z) (g z)]

theorem exists_tendstoUniformlyOn_of_uniformCauchySeqOn {α E : Type*} [NormedAddCommGroup E]
    [CompleteSpace E] {F : ℕ → α → E} {S : Set α} (h : UniformCauchySeqOn F atTop S) :
    ∃ g, TendstoUniformlyOn F g atTop S :=
  ⟨fun z => limUnder atTop fun n => F n z,
    h.tendstoUniformlyOn_of_tendsto fun _ hz => (h.cauchySeq hz).tendsto_limUnder⟩

/-- DLMF §1.9(v): `∑_{n=−∞}^{∞} fₙ(z)` converges uniformly on `S` iff `∑_{n=0}^{∞} fₙ(z)` and
`∑_{n=1}^{∞} f_{−n}(z)` both converge uniformly on `S`. -/
theorem dlmf_1_9_v_doubly_uniform {α E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {F : ℤ → α → E} {S : Set α} :
    (∃ g, DoubleSeriesConvergesUniformlyOn F g S) ↔
      (∃ g₁, SeriesConvergesUniformlyOn (fun n z => F n z) g₁ S) ∧
        ∃ g₂, SeriesConvergesUniformlyOn (fun n z => F (-((n + 1 : ℕ) : ℤ)) z) g₂ S := by
  have hsplit : ∀ (p : ℕ × ℕ) z, doublePartialSum (fun n => F n z) p =
      partialSum (fun k => F k z) p.2 + ∑ k ∈ range p.1, F (-((k + 1 : ℕ) : ℤ)) z :=
    fun p z => doublePartialSum_eq _ p.1 p.2
  constructor
  · rintro ⟨g, hg⟩
    have hg' : TendstoUniformlyOn (fun p : ℕ × ℕ => fun z => partialSum (fun k => F k z) p.2 +
        ∑ k ∈ range p.1, F (-((k + 1 : ℕ) : ℤ)) z) g atTop S :=
      hg.congr (Eventually.of_forall fun p ⦃z⦄ _ => hsplit p z)
    obtain ⟨hA, hB⟩ := uniformCauchySeqOn_of_split
      (A := fun n z => partialSum (fun k => F k z) n)
      (B := fun M z => ∑ k ∈ range M, F (-((k + 1 : ℕ) : ℤ)) z) hg'
    obtain ⟨g₁, hg₁⟩ := exists_tendstoUniformlyOn_of_uniformCauchySeqOn hA
    obtain ⟨g₂, hg₂⟩ := exists_tendstoUniformlyOn_of_uniformCauchySeqOn hB
    exact ⟨⟨g₁, hg₁⟩, ⟨g₂, seriesConvergesUniformlyOn_iff.mpr hg₂⟩⟩
  · rintro ⟨⟨g₁, hg₁⟩, ⟨g₂, hg₂⟩⟩
    have hg₂' := seriesConvergesUniformlyOn_iff.mp hg₂
    refine ⟨g₁ + g₂, ?_⟩
    unfold DoubleSeriesConvergesUniformlyOn
    unfold SeriesConvergesUniformlyOn at hg₁
    rw [Metric.tendstoUniformlyOn_iff] at hg₁ hg₂' ⊢
    intro ε hε
    rw [← prod_atTop_atTop_eq]
    filter_upwards [tendsto_snd.eventually (hg₁ (ε / 2) (half_pos hε)),
      tendsto_fst.eventually (hg₂' (ε / 2) (half_pos hε))] with p h1 h2 z hz
    rw [hsplit, Pi.add_apply]
    calc dist (g₁ z + g₂ z) (partialSum (fun k => F k z) p.2 +
          ∑ k ∈ range p.1, F (-((k + 1 : ℕ) : ℤ)) z)
        ≤ dist (g₁ z) (partialSum (fun k => F k z) p.2) +
          dist (g₂ z) (∑ k ∈ range p.1, F (-((k + 1 : ℕ) : ℤ)) z) := dist_add_add_le _ _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add (h1 z hz) (h2 z hz)
      _ = ε := add_halves ε

theorem exists_tendstoUniformlyOn_unit_iff {ι E : Type*} [PseudoMetricSpace E] {l : Filter ι}
    {F : ι → E} : (∃ g : Unit → E, TendstoUniformlyOn (fun i (_ : Unit) => F i) g l univ) ↔
      ∃ s, Tendsto F l (𝓝 s) := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g (), Metric.tendsto_nhds.mpr fun ε hε => ?_⟩
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hg ε hε] with i hi
    rw [dist_comm]
    exact hi () (mem_univ _)
  · rintro ⟨s, hs⟩
    refine ⟨fun _ => s, Metric.tendstoUniformlyOn_iff.mpr fun ε hε => ?_⟩
    filter_upwards [Metric.tendsto_nhds.mp hs ε hε] with i hi x _
    rw [dist_comm]
    exact hi

/-- DLMF §1.9(v): `∑_{n=−∞}^{∞} fₙ` converges iff `∑_{n=0}^{∞} fₙ` and `∑_{n=1}^{∞} f_{−n}` both
converge. -/
theorem dlmf_1_9_v_doubly {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] {f : ℤ → E} :
    (∃ s, DoubleSeriesConverges f s) ↔
      (∃ s₁, SeriesConverges (fun n => f n) s₁) ∧
        ∃ s₂, SeriesConverges (fun n => f (-((n + 1 : ℕ) : ℤ))) s₂ := by
  have h := dlmf_1_9_v_doubly_uniform (F := fun n (_ : Unit) => f n) (S := univ)
  simp only [DoubleSeriesConvergesUniformlyOn, SeriesConvergesUniformlyOn] at h
  rw [exists_tendstoUniformlyOn_unit_iff (F := doublePartialSum f),
    exists_tendstoUniformlyOn_unit_iff (F := partialSum fun k => f k),
    exists_tendstoUniformlyOn_unit_iff (F := partialSum fun k => f (-((k + 1 : ℕ) : ℤ)))] at h
  exact h

end Azurite.DLMF
