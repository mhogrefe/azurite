/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section9Series
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.PSeries
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.BigOperators.Field

/-!
# DLMF §1.15(i)–(ii): Summability methods

Formalizations of <https://dlmf.nist.gov/1.15#i> and <https://dlmf.nist.gov/1.15#ii>. Convergence
of a series means convergence of its partial sums (`SeriesConverges`, §1.9(v)).

**Definitions (§1.15(i)).** `AbelSum` (1.15.2–1.15.3), `CesaroSum` (1.15.4–1.15.5), `CesaroGenSum`
(1.15.6–1.15.7, written literally with `ascPochhammer`), `BorelSum` (1.15.8–1.15.9). The Abel and
Borel definitions require the defining power series to converge.
`cesaroSum_iff_cesaroGenSum_one`: `(C,1)` is `(C,α)` at `α = 1`.

**Regularity (§1.15(ii)).** `IsRegularMethod M`: `M` sums every convergent series to its sum.
* Abel (1.15.10–1.15.11, `dlmf_1_15_11`): Mathlib's Abel limit theorem.
* `(C,1)` (`dlmf_1_15_ii_cesaro`) and Borel (`dlmf_1_15_ii_borel`); `(C,α)` for `α ≥ 0`
  (`dlmf_1_15_ii_cesaroGen`, through `sum_cesaroCoeff_mul`, the summation by parts
  `∑ (α+1)ₖ/k! a_{n−k} = ∑ (α)_{n−j}/(n−j)! s_j`). All three use the positive Toeplitz lemma
  `tendsto_tsum_weights`.
* **DLMF discrepancy.** DLMF says all the methods are regular, including `(C,α)` for every
  `α > −1`. For `−1 < α < 0` this is false (`dlmf_1_15_ii_cesaroGen_not_regular`). There
  `(α+1)ₙ/n! → 0` (`tendsto_cesaroCoeff`), and a sparse convergent series with terms `2^{−j}` at
  rapidly increasing positions has unbounded `(C,α)` means. `dlmf_1_15_ii` collects the corrected
  statement.
-/

open Set Filter Topology Finset Complex
open scoped Nat

namespace Azurite.DLMF

/-! ### §1.15(i) Definitions -/

/-- **DLMF (1.15.1)**: `sₙ = ∑_{k=0}^{n} aₖ` (the partial sums `partialSum` of §1.9(v)). -/
theorem dlmf_1_15_1 (a : ℕ → ℂ) (n : ℕ) : partialSum a n = ∑ k ∈ range (n + 1), a k := rfl

/-- **DLMF (1.15.2)–(1.15.3)**, Abel summability: `∑ aₙ xⁿ` converges for `0 < x < 1` (here
`f(x)`) and `f(x) → s` as `x → 1−`. -/
def AbelSum (a : ℕ → ℂ) (s : ℂ) : Prop :=
  ∃ f : ℝ → ℂ, (∀ x ∈ Ioo (0 : ℝ) 1, SeriesConverges (fun n => a n * (x : ℂ) ^ n) (f x)) ∧
    Tendsto f (𝓝[<] 1) (𝓝 s)

/-- **DLMF (1.15.4)–(1.15.5)**, Cesàro summability `(C,1)`: `(s₀ + ⋯ + sₙ)/(n + 1) → s`. -/
def CesaroSum (a : ℕ → ℂ) (s : ℂ) : Prop :=
  Tendsto (fun n : ℕ => (∑ k ∈ range (n + 1), partialSum a k) / (n + 1)) atTop (𝓝 s)

/-- **DLMF (1.15.6)–(1.15.7)**, general Cesàro summability `(C,α)`, `α > −1`:
`n!/(α+1)ₙ ∑_{k=0}^{n} (α+1)ₖ/k! · a_{n−k} → s`. -/
def CesaroGenSum (α : ℝ) (a : ℕ → ℂ) (s : ℂ) : Prop :=
  Tendsto (fun n : ℕ => ((n ! / (ascPochhammer ℝ n).eval (α + 1) : ℝ) : ℂ) *
    ∑ k ∈ range (n + 1), (((ascPochhammer ℝ k).eval (α + 1) / k ! : ℝ) : ℂ) * a (n - k))
    atTop (𝓝 s)

/-- **DLMF (1.15.8)–(1.15.9)**, Borel summability: `∑ sₙ tⁿ/n!` converges for all `t` (here `F(t)`)
and `e^{−t} F(t) → s` as `t → ∞`. -/
def BorelSum (a : ℕ → ℂ) (s : ℂ) : Prop :=
  ∃ F : ℝ → ℂ, (∀ t : ℝ, SeriesConverges (fun n => partialSum a n * (t : ℂ) ^ n / n !) (F t)) ∧
    Tendsto (fun t : ℝ => (Real.exp (-t) : ℂ) * F t) atTop (𝓝 s)

/-! ### Tools -/

theorem seriesConverges_of_hasSum {z : ℕ → ℂ} {s : ℂ} (h : HasSum z s) : SeriesConverges z s :=
  (tendsto_add_atTop_iff_nat 1).mpr h.tendsto_sum_nat

theorem tendsto_range_of_seriesConverges {z : ℕ → ℂ} {s : ℂ} (h : SeriesConverges z s) :
    Tendsto (fun n => ∑ i ∈ range n, z i) atTop (𝓝 s) :=
  (tendsto_add_atTop_iff_nat 1).mp h

theorem bounded_of_tendsto {u : ℕ → ℂ} {s : ℂ} (h : Tendsto u atTop (𝓝 s)) :
    ∃ M, 0 ≤ M ∧ ∀ n, ‖u n‖ ≤ M := by
  have h' : Tendsto (fun n => ‖u n‖) cofinite (𝓝 ‖s‖) := by
    rw [Nat.cofinite_eq_atTop]; exact h.norm
  obtain ⟨M, hM⟩ := h'.bddAbove_range_of_cofinite
  exact ⟨max M 0, le_max_right _ _, fun n => (hM ⟨n, rfl⟩).trans (le_max_left _ _)⟩

/-- Positive Toeplitz weights: if `w_t(n) ≥ 0`, `∑ₙ w_t(n) = 1` and `w_t(n) → 0` for each `n`,
then `∑ₙ w_t(n) uₙ → lim uₙ`. -/
theorem tendsto_tsum_weights {ι : Type*} {l : Filter ι} {w : ι → ℕ → ℝ} {u : ℕ → ℂ} {s : ℂ}
    (hw0 : ∀ᶠ t in l, ∀ n, 0 ≤ w t n) (hws : ∀ᶠ t in l, HasSum (w t) 1)
    (hwn : ∀ n, Tendsto (fun t => w t n) l (𝓝 0)) (hu : Tendsto u atTop (𝓝 s)) :
    Tendsto (fun t => ∑' n, (w t n : ℂ) * u n) l (𝓝 s) := by
  obtain ⟨M, hM0, hM⟩ := bounded_of_tendsto (hu.sub_const s)
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hu (ε / 2) (by positivity)
  have hfin : Tendsto (fun t => ∑ n ∈ range N, w t n) l (𝓝 0) := by
    simpa using tendsto_finsetSum (range N) fun n _ => hwn n
  have hsmall := (tendsto_order.1 hfin).2 (ε / (2 * (M + 1))) (by positivity)
  filter_upwards [hw0, hws, hsmall] with t h0 h1 h2
  have hsw : Summable (w t) := h1.summable
  have hsd : Summable fun n => (w t n : ℂ) * (u n - s) :=
    Summable.of_norm_bounded (hsw.mul_right M) fun n => by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (h0 n)]
      exact mul_le_mul_of_nonneg_left (hM n) (h0 n)
  have hsn : Summable fun n => w t n * ‖u n - s‖ :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (h0 n) (norm_nonneg _))
      (fun n => mul_le_mul_of_nonneg_left (hM n) (h0 n)) (hsw.mul_right M)
  have hws' : HasSum (fun n => (w t n : ℂ) * s) s := by
    have := (Complex.hasSum_ofReal.mpr h1).mul_right s
    simpa using this
  have e : (∑' n, (w t n : ℂ) * u n) - s = ∑' n, (w t n : ℂ) * (u n - s) := by
    have hsu : Summable fun n => (w t n : ℂ) * u n :=
      (hsd.add hws'.summable).congr fun n => by ring
    conv_lhs => rw [← hws'.tsum_eq]
    rw [← hsu.tsum_sub hws'.summable]
    congr 1; funext n; ring
  have e2 : ∀ n, ‖(w t n : ℂ) * (u n - s)‖ = w t n * ‖u n - s‖ := fun n => by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (h0 n)]
  rw [dist_eq_norm, e]
  refine (norm_tsum_le_tsum_norm (hsn.congr fun n => (e2 n).symm)).trans_lt ?_
  simp_rw [e2]
  rw [← hsn.sum_add_tsum_nat_add N]
  have hA : ∑ n ∈ range N, w t n * ‖u n - s‖ ≤ M * ∑ n ∈ range N, w t n := by
    rw [mul_sum]; exact sum_le_sum fun n _ => by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_right (hM n) (h0 n)
  have hB : ∑' n, w t (n + N) * ‖u (n + N) - s‖ ≤ ε / 2 := by
    have hsN : Summable fun n => w t (n + N) := (summable_nat_add_iff N).mpr hsw
    calc ∑' n, w t (n + N) * ‖u (n + N) - s‖ ≤ ∑' n, w t (n + N) * (ε / 2) :=
          Summable.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left
            (by rw [← dist_eq_norm]; exact (hN (n + N) (by omega)).le) (h0 _))
            ((summable_nat_add_iff N).mpr hsn) (hsN.mul_right _)
      _ = (∑' n, w t (n + N)) * (ε / 2) := tsum_mul_right
      _ ≤ 1 * (ε / 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [← h1.tsum_eq, ← hsw.sum_add_tsum_nat_add N]
          exact le_add_of_nonneg_left (sum_nonneg fun n _ => h0 n)
      _ = ε / 2 := one_mul _
  have hC : M * ∑ n ∈ range N, w t n < ε / 2 := by
    calc M * ∑ n ∈ range N, w t n ≤ M * (ε / (2 * (M + 1))) :=
          mul_le_mul_of_nonneg_left h2.le hM0
      _ < ε / 2 := by
          rw [show M * (ε / (2 * (M + 1))) = ε / 2 * (M / (M + 1)) by field_simp]
          exact mul_lt_of_lt_one_right (by positivity) ((div_lt_one (by linarith)).mpr
            (by linarith))
  linarith

/-! ### §1.15(ii) Regularity -/

/-- A summation method is regular if it sums every convergent series to its sum. -/
def IsRegularMethod (M : (ℕ → ℂ) → ℂ → Prop) : Prop :=
  ∀ a s, SeriesConverges a s → M a s

/-- **DLMF (1.15.10)–(1.15.11)**: Abel summation is regular (Abel's limit theorem). -/
theorem dlmf_1_15_11 {a : ℕ → ℂ} {s : ℂ} (h : SeriesConverges a s) : AbelSum a s := by
  obtain ⟨M, hM0, hM⟩ := bounded_of_tendsto h.tendsto_zero
  refine ⟨fun x => ∑' n, a n * (x : ℂ) ^ n, fun x hx => ?_, ?_⟩
  · have hsum : Summable fun n => a n * (x : ℂ) ^ n := by
      refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hx.1.le hx.2).mul_left M)
        fun n => ?_
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hx.1.le]
      exact mul_le_mul_of_nonneg_right (hM n) (pow_nonneg hx.1.le n)
    exact seriesConverges_of_hasSum hsum.hasSum
  · exact tendsto_map'_iff.mp
      (Complex.tendsto_tsum_powerSeries_nhdsWithin_lt (tendsto_range_of_seriesConverges h))

theorem dlmf_1_15_ii_abel : IsRegularMethod AbelSum := fun _ _ h => dlmf_1_15_11 h

/-- **DLMF §1.15(ii)**: Cesàro `(C,1)` summation is regular. -/
theorem dlmf_1_15_ii_cesaro : IsRegularMethod CesaroSum := fun a s h => by
  have := (tendsto_add_atTop_iff_nat 1).mpr (Filter.Tendsto.cesaro_smul h)
  refine this.congr fun n => ?_
  rw [Complex.real_smul]
  push_cast
  field_simp

/-- **DLMF §1.15(ii)**: Borel summation is regular. -/
theorem dlmf_1_15_ii_borel : IsRegularMethod BorelSum := fun a s h => by
  obtain ⟨M, hM0, hM⟩ := bounded_of_tendsto h
  have hsum : ∀ t : ℝ, Summable fun n => partialSum a n * (t : ℂ) ^ n / n ! := fun t =>
    Summable.of_norm_bounded ((Real.summable_pow_div_factorial |t|).mul_left M) fun n => by
      rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast,
        mul_div_assoc]
      exact mul_le_mul (hM n) le_rfl (by positivity) hM0
  refine ⟨fun t => ∑' n, partialSum a n * (t : ℂ) ^ n / n !,
    fun t => seriesConverges_of_hasSum (hsum t).hasSum, ?_⟩
  have hT := tendsto_tsum_weights (l := atTop) (w := fun t n => Real.exp (-t) * (t ^ n / n !))
    (u := partialSum a)
    (eventually_ge_atTop 0 |>.mono fun t ht n => by positivity)
    (Eventually.of_forall fun t => by
      have := (NormedSpace.expSeries_div_hasSum_exp t).mul_left (Real.exp (-t))
      rwa [← Real.exp_eq_exp_ℝ, ← Real.exp_add, neg_add_cancel, Real.exp_zero] at this)
    (fun n => by
      have := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).div_const (n ! : ℝ)
      rw [zero_div] at this
      exact this.congr fun t => by ring)
    h
  refine hT.congr fun t => ?_
  rw [← tsum_mul_left]
  congr 1; funext n
  push_cast; ring

/-! ### General Cesàro means -/

/-- `(α + 1)ₖ/k!`, the weights of 1.15.7. -/
noncomputable def cesaroCoeff (α : ℝ) (k : ℕ) : ℝ := (ascPochhammer ℝ k).eval (α + 1) / k !

theorem cesaroCoeff_zero (α : ℝ) : cesaroCoeff α 0 = 1 := by simp [cesaroCoeff]

theorem cesaroCoeff_succ (α : ℝ) (k : ℕ) :
    cesaroCoeff α (k + 1) = cesaroCoeff α k * ((α + 1 + k) / (k + 1)) := by
  simp only [cesaroCoeff, ascPochhammer_succ_eval, Nat.factorial_succ, Nat.cast_mul]
  push_cast
  field_simp

theorem cesaroCoeff_sub_one_succ (α : ℝ) (k : ℕ) :
    cesaroCoeff (α - 1) (k + 1) = cesaroCoeff α k * (α / (k + 1)) := by
  simp only [cesaroCoeff, ascPochhammer_succ_left, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_one, Nat.factorial_succ,
    Nat.cast_mul, sub_add_cancel]
  push_cast
  field_simp

/-- Pascal: `(α+1)ₙ/n! = ∑_{i ≤ n} (α)ᵢ/i!`. -/
theorem cesaroCoeff_eq_sum (α : ℝ) (n : ℕ) :
    cesaroCoeff α n = ∑ i ∈ range (n + 1), cesaroCoeff (α - 1) i := by
  induction n with
  | zero => simp [cesaroCoeff_zero]
  | succ n ih =>
    rw [sum_range_succ, ← ih, cesaroCoeff_succ, cesaroCoeff_sub_one_succ]
    field_simp
    ring

theorem cesaroCoeff_pos {α : ℝ} (hα : -1 < α) (k : ℕ) : 0 < cesaroCoeff α k := by
  induction k with
  | zero => simp [cesaroCoeff_zero]
  | succ k ih =>
    rw [cesaroCoeff_succ]
    exact mul_pos ih (div_pos (by have := k.cast_nonneg (α := ℝ); linarith) (by positivity))

theorem cesaroCoeff_one (n : ℕ) : cesaroCoeff 1 n = n + 1 := by
  induction n with
  | zero => simp [cesaroCoeff_zero]
  | succ n ih => rw [cesaroCoeff_succ, ih]; push_cast; field_simp; ring

theorem cesaroCoeff_zero_param (n : ℕ) : cesaroCoeff 0 n = 1 := by
  induction n with
  | zero => simp [cesaroCoeff_zero]
  | succ n ih => rw [cesaroCoeff_succ, ih]; field_simp; ring

/-- The `(C,α)` mean `n!/(α+1)ₙ ∑ (α+1)ₖ/k! a_{n−k}` of 1.15.7. -/
theorem cesaroGen_eq (α : ℝ) (a : ℕ → ℂ) (n : ℕ) :
    ((n ! / (ascPochhammer ℝ n).eval (α + 1) : ℝ) : ℂ) *
      ∑ k ∈ range (n + 1), (((ascPochhammer ℝ k).eval (α + 1) / k ! : ℝ) : ℂ) * a (n - k) =
    ((cesaroCoeff α n)⁻¹ : ℂ) * ∑ k ∈ range (n + 1), (cesaroCoeff α k : ℂ) * a (n - k) := by
  simp only [cesaroCoeff]
  push_cast
  rw [inv_div]

/-- Summation by parts: `∑_{k ≤ n} (α+1)ₖ/k! a_{n−k} = ∑_{j ≤ n} (α)_{n−j}/(n−j)! s_j`. -/
theorem sum_cesaroCoeff_mul (α : ℝ) (a : ℕ → ℂ) (n : ℕ) :
    ∑ k ∈ range (n + 1), (cesaroCoeff α k : ℂ) * a (n - k) =
      ∑ j ∈ range (n + 1), (cesaroCoeff (α - 1) (n - j) : ℂ) * partialSum a j := by
  set PA := PowerSeries.mk fun k => (cesaroCoeff α k : ℂ)
  set PB := PowerSeries.mk fun k => (cesaroCoeff (α - 1) k : ℂ)
  set P1 := PowerSeries.mk fun _ : ℕ => (1 : ℂ)
  have h1 : PA = PB * P1 := by
    ext m
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [PA, PB, P1, PowerSeries.coeff_mk, mul_one]
    rw [cesaroCoeff_eq_sum]; push_cast; rfl
  have h2 : PowerSeries.mk (partialSum a) = P1 * PowerSeries.mk a := by
    ext m
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [P1, PowerSeries.coeff_mk, one_mul, partialSum]
    rw [← sum_range_reflect]
    refine sum_congr rfl fun k hk => ?_
    congr 1
  have h3 := congrArg (PowerSeries.coeff n) (show PA * PowerSeries.mk a =
    PB * PowerSeries.mk (partialSum a) by rw [h1, h2, mul_assoc])
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h3
  simp only [PA, PB, PowerSeries.coeff_mk] at h3
  rw [h3, ← sum_range_reflect]
  refine sum_congr rfl fun j hj => ?_
  have := mem_range.mp hj
  rw [show n - (n + 1 - 1 - j) = j by omega, show n + 1 - 1 - j = n - j by omega]

/-- `(C,1)` (1.15.5) is `(C,α)` (1.15.7) at `α = 1`. -/
theorem cesaroSum_iff_cesaroGenSum_one {a : ℕ → ℂ} {s : ℂ} :
    CesaroSum a s ↔ CesaroGenSum 1 a s := by
  unfold CesaroSum CesaroGenSum
  refine tendsto_congr fun n => ?_
  rw [cesaroGen_eq, sum_cesaroCoeff_mul, cesaroCoeff_one]
  simp only [show (1 : ℝ) - 1 = 0 by ring, cesaroCoeff_zero_param, ofReal_one, one_mul]
  push_cast
  rw [div_eq_inv_mul]

/-- **DLMF §1.15(ii)**: `(C,α)` summation is regular for `α ≥ 0` (positive Toeplitz weights
`(α)_{n−j}/(n−j)! · n!/(α+1)ₙ` on the partial sums). -/
theorem dlmf_1_15_ii_cesaroGen {α : ℝ} (hα : 0 ≤ α) : IsRegularMethod (CesaroGenSum α) :=
  fun a s h => by
  set A := cesaroCoeff α
  set B := cesaroCoeff (α - 1)
  have hA : ∀ k, 0 < A k := cesaroCoeff_pos (by linarith)
  have hB : ∀ k, 0 ≤ B k := fun k => by
    rcases k with _ | k
    · simp [B, cesaroCoeff_zero]
    · show 0 ≤ cesaroCoeff (α - 1) (k + 1)
      rw [cesaroCoeff_sub_one_succ]; exact mul_nonneg (hA k).le (by positivity)
  have hmono : Monotone A := monotone_nat_of_le_succ fun k => by
    simp only [A]; rw [cesaroCoeff_succ]
    refine le_mul_of_one_le_right (hA k).le ?_
    rw [one_le_div (by positivity)]; linarith
  set w : ℕ → ℕ → ℝ := fun n j => if j ≤ n then B (n - j) / A n else 0
  have hT := tendsto_tsum_weights (l := atTop) (w := w) (u := partialSum a)
    (Eventually.of_forall fun n j => by
      simp only [w]; split_ifs
      · exact div_nonneg (hB _) (hA n).le
      · exact le_rfl)
    (Eventually.of_forall fun n => by
      have hfin : ∀ j ∉ range (n + 1), w n j = 0 := fun j hj => by
        have : ¬ j ≤ n := by rw [Finset.mem_range] at hj; omega
        simp only [w, this, ite_false]
      have hsum : ∑ j ∈ range (n + 1), w n j = 1 := by
        rw [sum_congr rfl (g := fun j => B (n - j) / A n) fun j hj => by
          have : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          simp only [w, this, ite_true]]
        rw [← Finset.sum_div]
        have hr := Finset.sum_range_reflect (fun i => B i) (n + 1)
        simp only [Nat.add_sub_cancel] at hr
        rw [hr]
        simp only [B, A]
        rw [← cesaroCoeff_eq_sum, div_self (cesaroCoeff_pos (by linarith) n).ne']
      rw [← hsum]
      exact hasSum_sum_of_ne_finset_zero hfin)
    (fun j => by
      have hz := (tendsto_const_div_atTop_nhds_zero_nat α).comp (tendsto_sub_atTop_nat j)
      refine squeeze_zero' (Eventually.of_forall fun n => ?_) ?_ hz
      · simp only [w]; split_ifs
        · exact div_nonneg (hB _) (hA n).le
        · exact le_rfl
      · filter_upwards [eventually_gt_atTop j] with n hn
        simp only [w, hn.le, ite_true, Function.comp]
        obtain ⟨m, hm⟩ : ∃ m, n - j = m + 1 := ⟨n - j - 1, by omega⟩
        rw [hm, show B (m + 1) = A m * (α / (m + 1)) from cesaroCoeff_sub_one_succ α m]
        have hAm : A m ≤ A n := hmono (by omega)
        push_cast
        rw [div_le_div_iff₀ (hA n) (by positivity)]
        calc A m * (α / (m + 1)) * (m + 1) = A m * α := by field_simp
          _ ≤ A n * α := mul_le_mul_of_nonneg_right hAm hα
          _ = α * A n := mul_comm _ _)
    h
  unfold CesaroGenSum
  refine hT.congr fun n => ?_
  rw [cesaroGen_eq, sum_cesaroCoeff_mul, mul_sum, tsum_eq_sum (s := range (n + 1)) fun j hj => by
    have : ¬ j ≤ n := by rw [Finset.mem_range] at hj; omega
    simp [w, this]]
  refine sum_congr rfl fun j hj => ?_
  have : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  simp only [w, this, ite_true]
  push_cast; ring

/-! ### `(C,α)` is not regular for `−1 < α < 0` -/

theorem cesaroCoeff_le_exp {α : ℝ} (h1 : -1 < α) (n : ℕ) :
    cesaroCoeff α n ≤ Real.exp (α * ∑ i ∈ range n, 1 / ((i : ℝ) + 1)) := by
  induction n with
  | zero => simp [cesaroCoeff_zero]
  | succ n ih =>
    rw [cesaroCoeff_succ, sum_range_succ, mul_add, Real.exp_add]
    have hf : (α + 1 + n) / (n + 1) = α / (n + 1) + 1 := by field_simp; ring
    rw [hf]
    have h0 : 0 ≤ α / (n + 1) + 1 := by
      rw [← hf]; exact div_nonneg (by have := n.cast_nonneg (α := ℝ); linarith) (by positivity)
    have he := Real.add_one_le_exp (α / (n + 1))
    calc cesaroCoeff α n * (α / (n + 1) + 1) ≤
        Real.exp (α * ∑ i ∈ range n, 1 / ((i : ℝ) + 1)) * Real.exp (α / (n + 1)) :=
          mul_le_mul ih he h0 (Real.exp_pos _).le
      _ = _ := by rw [mul_one_div]

theorem tendsto_cesaroCoeff {α : ℝ} (h1 : -1 < α) (h2 : α < 0) :
    Tendsto (cesaroCoeff α) atTop (𝓝 0) := by
  have hH : Tendsto (fun n => α * ∑ i ∈ range n, 1 / ((i : ℝ) + 1)) atTop atBot :=
    Filter.Tendsto.const_mul_atTop_of_neg h2 Real.tendsto_sum_range_one_div_nat_succ_atTop
  refine squeeze_zero (fun n => (cesaroCoeff_pos h1 n).le) (cesaroCoeff_le_exp h1)
    (Real.tendsto_exp_atBot.comp hH)

/-- **DLMF §1.15(ii) fails for `−1 < α < 0`**: DLMF states that all methods of §1.15(i), including
`(C,α)` for every `α > −1`, are regular. For `−1 < α < 0` this is false. Since `(α+1)ₙ/n! → 0`, a
sparse convergent series with positive terms `2^{−j}` at rapidly increasing positions `n_j`
has `(C,α)` means at least `j + 1` at `n_j`, so they do not converge. -/
theorem dlmf_1_15_ii_cesaroGen_not_regular {α : ℝ} (h1 : -1 < α) (h2 : α < 0) :
    ¬ IsRegularMethod (CesaroGenSum α) := by
  intro hreg
  have hA0 := tendsto_cesaroCoeff h1 h2
  have hε : ∀ j : ℕ, ∃ m, ∀ k ≥ m, cesaroCoeff α k < (1 / 2) ^ j / (j + 1) := fun j =>
    eventually_atTop.mp ((tendsto_order.1 hA0).2 _ (by positivity))
  choose M hM using hε
  set nj : ℕ → ℕ := fun j => j + ∑ i ∈ range (j + 1), M i
  have hmono : StrictMono nj := strictMono_nat_of_lt_succ fun j => by
    simp only [nj, sum_range_succ]; omega
  have hge : ∀ j, M j ≤ nj j := fun j => by
    simp only [nj]
    have := single_le_sum (f := M) (fun _ _ => Nat.zero_le _) (self_mem_range_succ j)
    omega
  set b : ℕ → ℝ := fun j => (1 / 2) ^ j
  set a : ℕ → ℝ := Function.extend nj b 0
  have ha0 : ∀ m, 0 ≤ a m := fun m => by
    by_cases h : ∃ j, nj j = m
    · obtain ⟨j, rfl⟩ := h
      simp only [a, hmono.injective.extend_apply]; positivity
    · simp only [a, Function.extend_apply' _ _ _ h, Pi.zero_apply, le_refl]
  have haj : ∀ j, a (nj j) = b j := fun j => hmono.injective.extend_apply _ _ _
  have hconv : SeriesConverges (fun n => (a n : ℂ)) 2 := by
    refine seriesConverges_of_hasSum ?_
    have : HasSum a 2 := (hasSum_extend_zero hmono.injective).mpr hasSum_geometric_two
    exact Complex.hasSum_ofReal.mpr this
  have hlim := hreg _ _ hconv
  unfold CesaroGenSum at hlim
  obtain ⟨K, -, hK⟩ := bounded_of_tendsto hlim
  obtain ⟨j, hj⟩ := exists_nat_gt K
  have hn := hK (nj j)
  rw [cesaroGen_eq α (fun n => (a n : ℂ)) (nj j)] at hn
  set n := nj j
  have hreal : ((cesaroCoeff α n)⁻¹ : ℂ) * ∑ k ∈ range (n + 1), (cesaroCoeff α k : ℂ) *
      (a (n - k) : ℂ) = (((cesaroCoeff α n)⁻¹ * ∑ k ∈ range (n + 1), cesaroCoeff α k *
        a (n - k) : ℝ) : ℂ) := by push_cast; rfl
  rw [hreal, Complex.norm_real, Real.norm_eq_abs] at hn
  have hpos : ∀ k, 0 ≤ cesaroCoeff α k * a (n - k) := fun k =>
    mul_nonneg (cesaroCoeff_pos h1 k).le (ha0 _)
  have hS : b j ≤ ∑ k ∈ range (n + 1), cesaroCoeff α k * a (n - k) := by
    have := single_le_sum (fun k _ => hpos k) (mem_range.mpr (Nat.succ_pos n))
    simp only [cesaroCoeff_zero, one_mul, Nat.sub_zero] at this
    rw [show n = nj j from rfl, haj j] at this
    exact this
  have hAn : cesaroCoeff α n < b j / (j + 1) := hM j n (hge j)
  have hApos := cesaroCoeff_pos h1 n
  have hbig : (j : ℝ) + 1 ≤ (cesaroCoeff α n)⁻¹ * ∑ k ∈ range (n + 1),
      cesaroCoeff α k * a (n - k) := by
    rw [inv_mul_eq_div, le_div_iff₀ hApos]
    have hbj : 0 < b j := by positivity
    rw [lt_div_iff₀ (by positivity)] at hAn
    nlinarith
  have := (le_abs_self _).trans hn
  linarith

/-- **DLMF §1.15(ii)**, corrected: Abel, `(C,1)`, Borel and `(C,α)` for `α ≥ 0` are regular, while
`(C,α)` for `−1 < α < 0` is not. -/
theorem dlmf_1_15_ii :
    IsRegularMethod AbelSum ∧ IsRegularMethod CesaroSum ∧ IsRegularMethod BorelSum ∧
      (∀ α : ℝ, 0 ≤ α → IsRegularMethod (CesaroGenSum α)) ∧
      (∀ α : ℝ, -1 < α → α < 0 → ¬ IsRegularMethod (CesaroGenSum α)) :=
  ⟨dlmf_1_15_ii_abel, dlmf_1_15_ii_cesaro, dlmf_1_15_ii_borel, fun _ h => dlmf_1_15_ii_cesaroGen h,
    fun _ h1 h2 => dlmf_1_15_ii_cesaroGen_not_regular h1 h2⟩

end Azurite.DLMF
