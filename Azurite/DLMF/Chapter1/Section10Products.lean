/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# DLMF §1.10(ix): Infinite Products

Formalizations of <https://dlmf.nist.gov/1.10.ix>. Factors are indexed by `n ≥ 1`, and
`partialProd a k m = p_{k,m} = ∏_{n=k}^{m} (1 + aₙ)`.

* **Definitions.**
  * `InfProdConverges`: `p_{k,m} → p_k ≠ 0` for some `k ≥ 1`, allowing finitely many zero factors.
  * `InfProdConvergesAbsolutely`: `∏ (1 + |aₙ|)` converges.
  * `InfProdConvergesUniformlyOn`: the partial products converge uniformly.
* **The value.** `InfProdConverges.exists_tendsto`: `p_{1,m} → P`, and `P = 0` iff some factor
  `1 + aₙ` vanishes.
* **Series criteria.**
  * `dlmf_1_10_ix_log`: for `aₙ ≠ −1`, the product converges iff `∑ ln(1 + aₙ)` converges. The
    hard direction tracks the integers `(Sₘ − ln P − ln(pₘ/P))/(2πi)`, which are eventually
    constant.
  * `dlmf_1_10_ix_abs`: the product converges absolutely iff `∑ |aₙ|` converges.
  * `InfProdConvergesAbsolutely.infProdConverges`: absolute convergence implies convergence.
* **Analytic factors.**
  * `dlmf_1_10_20` covers 1.10.20–1.10.21. It assumes `1 + aₙ(z) ≠ 0` for `n ≥ N` explicitly,
    since Lean's `log 0 = 0`. The tail products `exp(∑ ln(1 + aₙ))` converge uniformly; the limit is
    analytic as a locally uniform limit, and it vanishes only at zeros of the factors.
  * `dlmf_1_10_ix_Mtest`: the M-test variant.
* **Weierstrass product.** `dlmf_1_10_22` shows `∏ (1 − z/zₙ) e^{z/zₙ}` is entire with zeros
  exactly at the `zₙ`. It uses `|(1 − w)eʷ − 1| ≤ 3|w|²` for `|w| ≤ 1`
  (`norm_weierstrassE_sub_one_le`).
-/

open Filter Topology Metric Complex Finset
open scoped Real

namespace Azurite.DLMF

/-! ### Convergence of infinite products -/

/-- The partial product `p_{k,m} = ∏_{n=k}^{m} (1 + aₙ)`. -/
def partialProd (a : ℕ → ℂ) (k m : ℕ) : ℂ := ∏ n ∈ Ico k (m + 1), (1 + a n)

/-- DLMF §1.10(ix): `∏_{n=1}^∞ (1 + aₙ)` converges if `p_{k,m} → p_k ≠ 0` as `m → ∞` for some
`k ≥ 1` (allowing finitely many zero factors). -/
def InfProdConverges (a : ℕ → ℂ) : Prop :=
  ∃ k ≥ 1, ∃ p ≠ 0, Tendsto (partialProd a k) atTop (𝓝 p)

/-- The convergence is absolute if `∏_{n=1}^∞ (1 + |aₙ|)` converges. -/
def InfProdConvergesAbsolutely (a : ℕ → ℂ) : Prop :=
  InfProdConverges fun n => (‖a n‖ : ℂ)

/-- For `aₙ = aₙ(z)`, the convergence is uniform on `S` if the partial products `p_{k,m}(z)`
converge uniformly. -/
def InfProdConvergesUniformlyOn (a : ℕ → ℂ → ℂ) (k : ℕ) (p : ℂ → ℂ) (S : Set ℂ) : Prop :=
  TendstoUniformlyOn (fun m z => partialProd (fun n => a n z) k m) p atTop S

theorem partialProd_split (a : ℕ → ℂ) {k m : ℕ} (hk : 1 ≤ k) (hm : k ≤ m + 1) :
    partialProd a 1 m = (∏ n ∈ Ico 1 k, (1 + a n)) * partialProd a k m :=
  (prod_Ico_consecutive _ hk hm).symm

theorem partialProd_succ (a : ℕ → ℂ) {k m : ℕ} (hk : k ≤ m + 1) :
    partialProd a k (m + 1) = partialProd a k m * (1 + a (m + 1)) :=
  prod_Ico_succ_top hk _

/-- If `p_{k,m} → p_k`, the full partial products `p_{1,m}` tend to `p_{1,k−1} p_k`. -/
theorem tendsto_partialProd_one {a : ℕ → ℂ} {k : ℕ} (hk : 1 ≤ k) {p : ℂ}
    (h : Tendsto (partialProd a k) atTop (𝓝 p)) :
    Tendsto (partialProd a 1) atTop (𝓝 ((∏ n ∈ Ico 1 k, (1 + a n)) * p)) := by
  refine (h.const_mul _).congr' ?_
  filter_upwards [eventually_ge_atTop k] with m hm
  exact (partialProd_split a hk (by omega)).symm

/-- DLMF §1.10(ix): the value `p_{1,k−1} p_k` of a convergent product vanishes iff some factor
`1 + aₙ` vanishes. -/
theorem head_mul_eq_zero_iff {a : ℕ → ℂ} {k : ℕ} {p : ℂ} (hp : p ≠ 0)
    (h : Tendsto (partialProd a k) atTop (𝓝 p)) :
    (∏ n ∈ Ico 1 k, (1 + a n)) * p = 0 ↔ ∃ n ≥ 1, 1 + a n = 0 := by
  rw [mul_eq_zero, or_iff_left hp, prod_eq_zero_iff]
  constructor
  · rintro ⟨n, hn, h0⟩
    exact ⟨n, (mem_Ico.mp hn).1, h0⟩
  · rintro ⟨n, hn1, h0⟩
    by_cases hnk : n < k
    · exact ⟨n, mem_Ico.mpr ⟨hn1, hnk⟩, h0⟩
    · exfalso
      refine hp (tendsto_nhds_unique h (tendsto_const_nhds.congr' ?_))
      filter_upwards [eventually_ge_atTop n] with m hm
      show (0 : ℂ) = ∏ n ∈ Ico k (m + 1), (1 + a n)
      exact (prod_eq_zero (Finset.mem_Ico.mpr ⟨by omega, by omega⟩ : n ∈ Ico k (m + 1)) h0).symm

/-- A convergent product: the partial products `∏_{n=1}^{m}` converge to `P`, and `P = 0` iff some
factor vanishes. -/
theorem InfProdConverges.exists_tendsto {a : ℕ → ℂ} (h : InfProdConverges a) :
    ∃ P, Tendsto (partialProd a 1) atTop (𝓝 P) ∧ (P = 0 ↔ ∃ n ≥ 1, 1 + a n = 0) := by
  obtain ⟨k, hk, p, hp, hlim⟩ := h
  exact ⟨_, tendsto_partialProd_one hk hlim, head_mul_eq_zero_iff hp hlim⟩

/-- DLMF §1.10(ix): for `aₙ ≠ −1`, `∏ (1 + aₙ)` converges iff `∑ ln(1 + aₙ)` converges. -/
theorem dlmf_1_10_ix_log {a : ℕ → ℂ} (ha : ∀ n ≥ 1, 1 + a n ≠ 0) :
    InfProdConverges a ↔
      ∃ s, Tendsto (fun m => ∑ n ∈ Ico 1 (m + 1), log (1 + a n)) atTop (𝓝 s) := by
  set S : ℕ → ℂ := fun m => ∑ n ∈ Ico 1 (m + 1), log (1 + a n) with hS
  have hexpS : ∀ m, exp (S m) = partialProd a 1 m := fun m => by
    rw [hS, exp_sum, partialProd]
    exact prod_congr rfl fun n hn => exp_log (ha n (mem_Ico.mp hn).1)
  have hP0 : ∀ m, partialProd a 1 m ≠ 0 := fun m => by
    rw [← hexpS]
    exact exp_ne_zero _
  constructor
  · intro h
    obtain ⟨P, hP, hPz⟩ := h.exists_tendsto
    have hPne : P ≠ 0 := fun h0 => by
      obtain ⟨n, hn, h0'⟩ := hPz.mp h0
      exact ha n hn h0'
    -- `1 + a(m+1) = p_{1,m+1} / p_{1,m} → 1`
    have h1a : Tendsto (fun m => 1 + a (m + 1)) atTop (𝓝 1) := by
      have := (hP.comp (tendsto_add_atTop_nat 1)).div hP hPne
      rw [div_self hPne] at this
      refine this.congr fun m => ?_
      show partialProd a 1 (m + 1) / partialProd a 1 m = _
      rw [partialProd_succ a (by omega), mul_div_cancel_left₀ _ (hP0 m)]
    have hlog1 : ContinuousAt log 1 := continuousAt_clog (by simp [mem_slitPlane_iff])
    have hla : Tendsto (fun m => log (1 + a (m + 1))) atTop (𝓝 0) := by
      have := hlog1.tendsto.comp h1a
      rw [log_one] at this
      exact this
    have hℓ : Tendsto (fun m => log (partialProd a 1 m / P)) atTop (𝓝 0) := by
      have h2 := hP.div_const P
      rw [div_self hPne] at h2
      have := hlog1.tendsto.comp h2
      rw [log_one] at this
      exact this
    -- `S m − log P − log(p_{1,m}/P)` is an integer multiple of `2πi`
    have hint : ∀ m, ∃ j : ℤ, S m - log P - log (partialProd a 1 m / P) = j * (2 * π * I) := by
      intro m
      apply exp_eq_one_iff.mp
      rw [exp_sub, exp_sub, hexpS m, exp_log hPne, exp_log (div_ne_zero (hP0 m) hPne)]
      have := hP0 m
      field_simp
    choose j hj using hint
    have hdiff : Tendsto (fun m => ((j (m + 1) : ℂ) - j m) * (2 * π * I)) atTop (𝓝 0) := by
      have : (fun m => ((j (m + 1) : ℂ) - j m) * (2 * π * I)) = fun m =>
          log (1 + a (m + 1)) - (log (partialProd a 1 (m + 1) / P) -
            log (partialProd a 1 m / P)) := by
        funext m
        rw [sub_mul, ← hj, ← hj, hS]
        simp only
        rw [sum_Ico_succ_top (by omega : 1 ≤ m + 1)]
        ring
      rw [this]
      simpa using hla.sub ((hℓ.comp (tendsto_add_atTop_nat 1)).sub hℓ)
    have hev : ∀ᶠ m in atTop, j (m + 1) = j m := by
      have h2 : Tendsto (fun m => ((j (m + 1) : ℂ) - j m)) atTop (𝓝 0) := by
        have := hdiff.mul_const (2 * π * I)⁻¹
        simp only [zero_mul] at this
        refine this.congr fun m => ?_
        field_simp
      filter_upwards [h2.eventually (ball_mem_nhds 0 one_pos)] with m hm
      rw [dist_zero_right] at hm
      have : |(j (m + 1) - j m : ℤ)| < 1 := by
        have h' : ‖((j (m + 1) - j m : ℤ) : ℂ)‖ < 1 := by push_cast; exact hm
        rwa [norm_intCast, ← Int.cast_abs, ← Int.cast_one, Int.cast_lt] at h'
      have := abs_lt.mp this
      omega
    obtain ⟨m₀, hm₀⟩ := eventually_atTop.mp hev
    have hconst : ∀ m ≥ m₀, j m = j m₀ := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => rfl
      | succ m hm ih => rw [hm₀ m hm, ih]
    refine ⟨log P + j m₀ * (2 * π * I), ?_⟩
    have : Tendsto (fun m => log P + j m₀ * (2 * π * I) + log (partialProd a 1 m / P)) atTop
        (𝓝 (log P + j m₀ * (2 * π * I))) := by simpa using tendsto_const_nhds.add hℓ
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop m₀] with m hm
    rw [← hconst m hm, ← hj m]
    ring
  · rintro ⟨s, hs⟩
    refine ⟨1, le_rfl, exp s, exp_ne_zero _, ?_⟩
    exact ((continuous_exp.tendsto s).comp hs).congr fun m => hexpS m

/-- DLMF §1.10(ix): `∏ (1 + aₙ)` converges absolutely iff `∑ |aₙ|` converges. -/
theorem dlmf_1_10_ix_abs (a : ℕ → ℂ) :
    InfProdConvergesAbsolutely a ↔
      ∃ s, Tendsto (fun m => ∑ n ∈ Ico 1 (m + 1), ‖a n‖) atTop (𝓝 s) := by
  set Q : ℕ → ℕ → ℝ := fun k m => ∏ n ∈ Ico k (m + 1), (1 + ‖a n‖) with hQ
  set S : ℕ → ℕ → ℝ := fun k m => ∑ n ∈ Ico k (m + 1), ‖a n‖ with hSdef
  have hcast : ∀ k m, partialProd (fun n => (‖a n‖ : ℂ)) k m = (Q k m : ℂ) := fun k m => by
    simp [partialProd, hQ]
  have hQmono : ∀ k, Monotone (Q k) := fun k => monotone_nat_of_le_succ fun m => by
    by_cases hkm : k ≤ m + 1
    · simp only [hQ]
      rw [prod_Ico_succ_top hkm]
      exact le_mul_of_one_le_right (prod_nonneg fun n _ => by positivity)
        (by linarith [norm_nonneg (a (m + 1))])
    · simp only [hQ]
      rw [Finset.Ico_eq_empty_of_le (by omega), Finset.Ico_eq_empty_of_le (by omega)]
  have hSmono : ∀ k, Monotone (S k) := fun k => monotone_nat_of_le_succ fun m => by
    by_cases hkm : k ≤ m + 1
    · simp only [hSdef]
      rw [sum_Ico_succ_top hkm]
      linarith [norm_nonneg (a (m + 1))]
    · simp only [hSdef]
      rw [Finset.Ico_eq_empty_of_le (by omega), Finset.Ico_eq_empty_of_le (by omega)]
  have hle_exp : ∀ k m, Q k m ≤ Real.exp (S k m) := fun k m => by
    simp only [hQ, hSdef]
    rw [Real.exp_sum]
    gcongr with n hn
    linarith [Real.add_one_le_exp ‖a n‖]
  have hge : ∀ k m, 1 + S k m ≤ Q k m := fun k m => by
    simp only [hQ, hSdef]
    induction Ico k (m + 1) using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [sum_insert hi, prod_insert hi]
      have h0 : 0 ≤ ∑ n ∈ s, ‖a n‖ := sum_nonneg fun n _ => norm_nonneg _
      nlinarith [mul_nonneg (norm_nonneg (a i)) h0, norm_nonneg (a i)]
  constructor
  · rintro ⟨k, hk, p, -, hp⟩
    have hre : Tendsto (Q k) atTop (𝓝 p.re) := by
      have := (continuous_re.tendsto p).comp hp
      refine this.congr fun m => ?_
      simp [hcast]
    have hbdd : ∀ m, S k m ≤ p.re := fun m =>
      (by linarith [hge k m] : S k m ≤ Q k m).trans ((hQmono k).ge_of_tendsto hre m)
    -- `S 1 m = S 1 (k − 1) + S k m` for `m ≥ k − 1`
    have hsplit : ∀ m, k ≤ m + 1 → S 1 m = S 1 (k - 1) + S k m := fun m hm => by
      simp only [hSdef]
      rw [Nat.sub_add_cancel hk, sum_Ico_consecutive _ hk hm]
    have hbdd1 : BddAbove (Set.range (S 1)) := ⟨S 1 (k - 1) + p.re, by
      rintro _ ⟨m, rfl⟩
      by_cases hm : k ≤ m + 1
      · rw [hsplit m hm]
        linarith [hbdd m]
      · have := hSmono 1 (show m ≤ k - 1 by omega)
        have h0 : 0 ≤ p.re := (le_trans (by
          simp only [hSdef]; exact sum_nonneg fun n _ => norm_nonneg _) (hbdd 0))
        linarith⟩
    exact ⟨_, tendsto_atTop_ciSup (hSmono 1) hbdd1⟩
  · rintro ⟨s, hs⟩
    have hbdd : BddAbove (Set.range (Q 1)) := ⟨Real.exp s, by
      rintro _ ⟨m, rfl⟩
      exact (hle_exp 1 m).trans (Real.exp_le_exp.mpr ((hSmono 1).ge_of_tendsto hs m))⟩
    have hlim := tendsto_atTop_ciSup (hQmono 1) hbdd
    refine ⟨1, le_rfl, ((⨆ m, Q 1 m : ℝ) : ℂ), ?_, ?_⟩
    · have : 1 ≤ ⨆ m, Q 1 m := le_trans (by
        have := hge 1 0
        have h0 : 0 ≤ S 1 0 := by simp only [hSdef]; exact sum_nonneg fun n _ => norm_nonneg _
        linarith) (le_ciSup hbdd 0)
      exact ofReal_ne_zero.mpr (by linarith)
    · exact ((continuous_ofReal.tendsto _).comp hlim).congr fun m => (hcast 1 m).symm

/-! ### Uniform convergence and analyticity -/

theorem tendstoUniformlyOn_cexp {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {S : Set ℂ} {B : ℝ}
    (h : TendstoUniformlyOn F f atTop S) (hF : ∀ m, ∀ z ∈ S, ‖F m z‖ ≤ B) :
    TendstoUniformlyOn (fun m z => exp (F m z)) (fun z => exp (f z)) atTop S := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  have hB : 0 < Real.exp B := Real.exp_pos B
  filter_upwards [h (min 1 (ε / (2 * Real.exp B))) (by positivity)] with m hm z hz
  have hd := hm z hz
  rw [dist_eq_norm] at hd ⊢
  have h1 : ‖f z - F m z‖ ≤ 1 := hd.le.trans (min_le_left _ _)
  calc ‖exp (f z) - exp (F m z)‖ = ‖exp (F m z)‖ * ‖exp (f z - F m z) - 1‖ := by
        rw [← norm_mul, mul_sub, mul_one, ← exp_add, add_sub_cancel]
    _ ≤ Real.exp B * (2 * ‖f z - F m z‖) :=
        mul_le_mul ((norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr (hF m z hz)))
          (norm_exp_sub_one_le h1) (norm_nonneg _) hB.le
    _ < Real.exp B * (2 * (ε / (2 * Real.exp B))) := by
        gcongr
        exact hd.trans_le (min_le_right _ _)
    _ = ε := by field_simp

theorem tendstoUniformlyOn_mul_of_bounded {F : ℕ → ℂ → ℂ} {f g : ℂ → ℂ} {S : Set ℂ}
    {H : ℝ} (h : TendstoUniformlyOn F f atTop S) (hg : ∀ z ∈ S, ‖g z‖ ≤ H) :
    TendstoUniformlyOn (fun m z => g z * F m z) (fun z => g z * f z) atTop S := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  have hH : 0 < |H| + 1 := by positivity
  filter_upwards [h (ε / (|H| + 1)) (by positivity)] with m hm z hz
  have hd := hm z hz
  rw [dist_eq_norm] at hd ⊢
  calc ‖g z * f z - g z * F m z‖ = ‖g z‖ * ‖f z - F m z‖ := by rw [← mul_sub, norm_mul]
    _ ≤ (|H| + 1) * ‖f z - F m z‖ :=
        mul_le_mul_of_nonneg_right (by linarith [hg z hz, le_abs_self H]) (norm_nonneg _)
    _ < (|H| + 1) * (ε / (|H| + 1)) := by gcongr
    _ = ε := by field_simp

/-- **DLMF 1.10.20–1.10.21**: let `aₙ(z)` be analytic in `D`. If there is an `N`, independent of
`z ∈ D`, with `|ln(1 + aₙ(z))| ≤ Mₙ` for `n ≥ N` (`1 + aₙ(z) ≠ 0`, so that the principal logarithm
is meant) and `∑ Mₙ < ∞`, then `∏ (1 + aₙ(z))` converges uniformly in `D` (the partial products
`p_{N,m}` converge uniformly to `p_N ≠ 0`) to an analytic function `p(z) = p_{1,N−1}(z) p_N(z)`,
and `p(z) = 0` only when at least one factor `1 + aₙ(z)` vanishes. -/
theorem dlmf_1_10_20 {a : ℕ → ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D)
    (ha : ∀ n, DifferentiableOn ℂ (a n) D) {N : ℕ} (hN : 1 ≤ N)
    (hne : ∀ n ≥ N, ∀ z ∈ D, 1 + a n z ≠ 0) {M : ℕ → ℝ}
    (hM : ∀ n ≥ N, ∀ z ∈ D, ‖log (1 + a n z)‖ ≤ M n) (hMs : Summable M) :
    ∃ p : ℂ → ℂ, InfProdConvergesUniformlyOn a N p D ∧ (∀ z ∈ D, p z ≠ 0) ∧
      AnalyticOnNhd ℂ (fun z => (∏ n ∈ Ico 1 N, (1 + a n z)) * p z) D ∧
      ∀ z ∈ D, InfProdConverges (fun n => a n z) ∧
        Tendsto (fun m => partialProd (fun n => a n z) 1 m) atTop
          (𝓝 ((∏ n ∈ Ico 1 N, (1 + a n z)) * p z)) ∧
        ((∏ n ∈ Ico 1 N, (1 + a n z)) * p z = 0 ↔ ∃ n ≥ 1, 1 + a n z = 0) := by
  set b : ℕ → ℂ → ℂ := fun n z => if N ≤ n then log (1 + a n z) else 0 with hbdef
  have hb : ∀ n z, z ∈ D → ‖b n z‖ ≤ ‖M n‖ := by
    intro n z hz
    by_cases h : N ≤ n
    · simp only [hbdef, h, ↓reduceIte, Real.norm_eq_abs]
      exact (hM n h z hz).trans (le_abs_self _)
    · simp only [hbdef, h, ↓reduceIte, norm_zero]
      exact norm_nonneg _
  have hu : Summable fun n => ‖M n‖ := hMs.norm
  have hsum := tendstoUniformlyOn_tsum_nat hu hb
  have hsum' : TendstoUniformlyOn (fun m z => ∑ n ∈ range (m + 1), b n z)
      (fun z => ∑' n, b n z) atTop D := by
    rw [Metric.tendstoUniformlyOn_iff] at hsum ⊢
    intro ε hε
    exact (tendsto_add_atTop_nat 1).eventually (hsum ε hε)
  have hbound : ∀ m, ∀ z ∈ D, ‖∑ n ∈ range (m + 1), b n z‖ ≤ ∑' n, ‖M n‖ := fun m z hz =>
    (norm_sum_le _ _).trans ((sum_le_sum fun n _ => hb n z hz).trans
      (hu.sum_le_tsum _ fun n _ => norm_nonneg _))
  have hrep : ∀ m, ∀ z ∈ D,
      exp (∑ n ∈ range (m + 1), b n z) = partialProd (fun n => a n z) N m := by
    intro m z hz
    have hfilt : (range (m + 1)).filter (fun n => N ≤ n) = Ico N (m + 1) := by
      ext n
      simp only [mem_filter, mem_range, Finset.mem_Ico]
      omega
    rw [hbdef]
    simp only
    rw [← sum_filter, hfilt, exp_sum, partialProd]
    exact prod_congr rfl fun n hn => exp_log (hne n (Finset.mem_Ico.mp hn).1 z hz)
  set p : ℂ → ℂ := fun z => exp (∑' n, b n z) with hp
  have hunif : InfProdConvergesUniformlyOn a N p D :=
    (tendstoUniformlyOn_cexp hsum' hbound).congr
      (Eventually.of_forall fun m z hz => hrep m z hz)
  have hpd : DifferentiableOn ℂ p D :=
    hunif.tendstoLocallyUniformlyOn.differentiableOn (Eventually.of_forall fun m =>
      DifferentiableOn.fun_finsetProd fun n _ => (differentiableOn_const 1).add (ha n)) hD
  have hhead : DifferentiableOn ℂ (fun z => ∏ n ∈ Ico 1 N, (1 + a n z)) D :=
    DifferentiableOn.fun_finsetProd fun n _ => (differentiableOn_const 1).add (ha n)
  refine ⟨p, hunif, fun z _ => exp_ne_zero _, (hhead.mul hpd).analyticOnNhd hD,
    fun z hz => ?_⟩
  have hlim : Tendsto (partialProd (fun n => a n z) N) atTop (𝓝 (p z)) := hunif.tendsto_at hz
  exact ⟨⟨N, hN, p z, exp_ne_zero _, hlim⟩, tendsto_partialProd_one hN hlim,
    head_mul_eq_zero_iff (exp_ne_zero _) hlim⟩

/-- **M-test** (DLMF §1.10(ix)): if `|aₙ(z)| ≤ Mₙ` for all `n` and `z ∈ D`, with `∑ Mₙ < ∞`, then
`∏_{n=1}^∞ (1 + aₙ(z))` converges uniformly in `D` to an analytic function `P`, vanishing only
where some factor does. -/
theorem dlmf_1_10_ix_Mtest {a : ℕ → ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D)
    (ha : ∀ n, DifferentiableOn ℂ (a n) D) {M : ℕ → ℝ} (hM : ∀ n ≥ 1, ∀ z ∈ D, ‖a n z‖ ≤ M n)
    (hMs : Summable M) :
    ∃ P : ℂ → ℂ, InfProdConvergesUniformlyOn a 1 P D ∧ AnalyticOnNhd ℂ P D ∧
      ∀ z ∈ D, InfProdConverges (fun n => a n z) ∧ (P z = 0 ↔ ∃ n ≥ 1, 1 + a n z = 0) := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    (hMs.tendsto_atTop_zero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  set N := max N₀ 1
  have hN : 1 ≤ N := le_max_right _ _
  have hsmall : ∀ n ≥ N, ∀ z ∈ D, ‖a n z‖ ≤ 1 / 2 := fun n hn z hz =>
    (hM n (hN.trans hn) z hz).trans (hN₀ n ((le_max_left _ _).trans hn)).le
  have hne : ∀ n ≥ N, ∀ z ∈ D, 1 + a n z ≠ 0 := fun n hn z hz h => by
    have : a n z = -1 := by linear_combination h
    have := hsmall n hn z hz
    rw [‹a n z = -1›, norm_neg, norm_one] at this
    norm_num at this
  obtain ⟨p, hunif, -, han, hpt⟩ := dlmf_1_10_20 hD ha hN hne (M := fun n => 3 / 2 * M n)
    (fun n hn z hz => (norm_log_one_add_half_le_self (hsmall n hn z hz)).trans
      (by linarith [hM n (hN.trans hn) z hz])) (hMs.mul_left _)
  refine ⟨fun z => (∏ n ∈ Ico 1 N, (1 + a n z)) * p z, ?_, han, fun z hz =>
    ⟨(hpt z hz).1, (hpt z hz).2.2⟩⟩
  have hH : ∀ z ∈ D, ‖∏ n ∈ Ico 1 N, (1 + a n z)‖ ≤ ∏ n ∈ Ico 1 N, (1 + ‖M n‖) := by
    intro z hz
    rw [norm_prod]
    gcongr with n hn
    calc ‖1 + a n z‖ ≤ ‖(1 : ℂ)‖ + ‖a n z‖ := norm_add_le _ _
      _ ≤ 1 + ‖M n‖ := by
          rw [norm_one, Real.norm_eq_abs]
          linarith [hM n (Finset.mem_Ico.mp hn).1 z hz, le_abs_self (M n)]
  refine (tendstoUniformlyOn_mul_of_bounded hunif hH).congr ?_
  filter_upwards [eventually_ge_atTop N] with m hm z _
  exact (partialProd_split (fun n => a n z) hN (by omega)).symm

/-- An absolutely convergent product converges. -/
theorem InfProdConvergesAbsolutely.infProdConverges {a : ℕ → ℂ}
    (h : InfProdConvergesAbsolutely a) : InfProdConverges a := by
  obtain ⟨s, hs⟩ := (dlmf_1_10_ix_abs a).mp h
  set M : ℕ → ℝ := fun n => if 1 ≤ n then ‖a n‖ else 0 with hMdef
  have hM0 : ∀ n, 0 ≤ M n := fun n => by
    simp only [hMdef]
    split_ifs
    · exact norm_nonneg _
    · exact le_rfl
  have hrange : ∀ m, ∑ n ∈ range (m + 1), M n = ∑ n ∈ Ico 1 (m + 1), ‖a n‖ := fun m => by
    have hfilt : (range (m + 1)).filter (fun n => 1 ≤ n) = Ico 1 (m + 1) := by
      ext n
      simp only [mem_filter, mem_range, Finset.mem_Ico]
      omega
    rw [hMdef]
    simp only
    rw [← sum_filter, hfilt]
  have hMs : Summable M := by
    refine ⟨s, (hasSum_iff_tendsto_nat_of_nonneg hM0 s).mpr ?_⟩
    refine (tendsto_add_atTop_iff_nat 1).mp ?_
    exact hs.congr fun m => (hrange m).symm
  obtain ⟨P, -, -, hP⟩ := dlmf_1_10_ix_Mtest (a := fun n _ => a n) (D := Set.univ) isOpen_univ
    (fun n => differentiableOn_const _) (M := M)
    (fun n hn _ _ => by simp only [hMdef, hn, ↓reduceIte]; exact le_rfl) hMs
  exact (hP 0 (Set.mem_univ _)).1

/-! ### Weierstrass product -/

/-- The Weierstrass primary factor `(1 − w) e^w`. -/
noncomputable def weierstrassE (w : ℂ) : ℂ := (1 - w) * exp w

theorem norm_weierstrassE_sub_one_le {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖weierstrassE w - 1‖ ≤ 3 * ‖w‖ ^ 2 := by
  have : weierstrassE w - 1 = (exp w - 1 - w) - w * (exp w - 1) := by
    unfold weierstrassE
    ring
  rw [this]
  calc ‖exp w - 1 - w - w * (exp w - 1)‖ ≤ ‖exp w - 1 - w‖ + ‖w * (exp w - 1)‖ := norm_sub_le _ _
    _ ≤ ‖w‖ ^ 2 + ‖w‖ * (2 * ‖w‖) := by
        rw [norm_mul]
        exact add_le_add (norm_exp_sub_one_sub_id_le hw)
          (mul_le_mul_of_nonneg_left (norm_exp_sub_one_le hw) (norm_nonneg _))
    _ = 3 * ‖w‖ ^ 2 := by ring

theorem weierstrassE_eq_zero_iff {w : ℂ} : weierstrassE w = 0 ↔ w = 1 := by
  rw [weierstrassE, mul_eq_zero, or_iff_left (exp_ne_zero _), sub_eq_zero, eq_comm]

/-- The Weierstrass product `P(z) = ∏_{n=1}^∞ (1 − z/zₙ) e^{z/zₙ}` (limit of partial products). -/
noncomputable def weierstrassProduct (zs : ℕ → ℂ) (z : ℂ) : ℂ :=
  limUnder atTop fun m => ∏ n ∈ Ico 1 (m + 1), weierstrassE (z / zs n)

/-- **DLMF 1.10.22**: if `∑ |zₙ^{−2}|` converges (`zₙ ≠ 0`), then
`P(z) = ∏_{n=1}^∞ (1 − z/zₙ) e^{z/zₙ}` converges for every `z` and is an entire function whose zeros
are exactly the `zₙ`. -/
theorem dlmf_1_10_22 {zs : ℕ → ℂ} (h0 : ∀ n ≥ 1, zs n ≠ 0)
    (hs : Summable fun n => ‖(zs n ^ 2)⁻¹‖) :
    Differentiable ℂ (weierstrassProduct zs) ∧
      (∀ z, Tendsto (fun m => ∏ n ∈ Ico 1 (m + 1), weierstrassE (z / zs n)) atTop
        (𝓝 (weierstrassProduct zs z))) ∧
      ∀ z, weierstrassProduct zs z = 0 ↔ ∃ n ≥ 1, z = zs n := by
  set a : ℕ → ℂ → ℂ := fun n z => weierstrassE (z / zs n) - 1 with hadef
  have hpp : ∀ z m, partialProd (fun n => a n z) 1 m =
      ∏ n ∈ Ico 1 (m + 1), weierstrassE (z / zs n) := fun z m => by
    simp [partialProd, hadef]
  have hzero : ∀ z, (∃ n ≥ 1, 1 + a n z = 0) ↔ ∃ n ≥ 1, z = zs n := fun z => by
    refine exists_congr fun n => and_congr_right fun hn => ?_
    rw [hadef]
    simp only [add_sub_cancel, weierstrassE_eq_zero_iff, div_eq_one_iff_eq (h0 n hn)]
  have hda : ∀ n, Differentiable ℂ (a n) := fun n => by
    simp only [hadef, weierstrassE]
    fun_prop
  -- on each disk `|z| < R` the product converges to an analytic function
  have key : ∀ R > 0, ∃ P : ℂ → ℂ, AnalyticOnNhd ℂ P (ball 0 R) ∧ ∀ z ∈ ball (0 : ℂ) R,
      Tendsto (fun m => ∏ n ∈ Ico 1 (m + 1), weierstrassE (z / zs n)) atTop (𝓝 (P z)) ∧
        (P z = 0 ↔ ∃ n ≥ 1, z = zs n) := by
    intro R hR
    have hc : 0 < 1 / (6 * R ^ 2) := by positivity
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hs.tendsto_atTop_zero.eventually (gt_mem_nhds hc))
    set N := max N₀ 1
    have hN : 1 ≤ N := le_max_right _ _
    have hw : ∀ n ≥ N, ∀ z ∈ ball (0 : ℂ) R, ‖z / zs n‖ ^ 2 ≤ R ^ 2 * ‖(zs n ^ 2)⁻¹‖ := by
      intro n hn z hz
      rw [norm_div, div_pow, norm_inv, norm_pow, div_eq_mul_inv]
      have : ‖z‖ ^ 2 ≤ R ^ 2 := by
        rw [mem_ball, dist_zero_right] at hz
        exact pow_le_pow_left₀ (norm_nonneg _) hz.le 2
      exact mul_le_mul_of_nonneg_right this (by positivity)
    have hsmall : ∀ n ≥ N, ‖(zs n ^ 2)⁻¹‖ < 1 / (6 * R ^ 2) := fun n hn =>
      hN₀ n ((le_max_left _ _).trans hn)
    have hw1 : ∀ n ≥ N, ∀ z ∈ ball (0 : ℂ) R, ‖z / zs n‖ ^ 2 ≤ 1 / 6 := fun n hn z hz => by
      have := hw n hn z hz
      have h2 := hsmall n hn
      have : R ^ 2 * ‖(zs n ^ 2)⁻¹‖ ≤ R ^ 2 * (1 / (6 * R ^ 2)) :=
        mul_le_mul_of_nonneg_left h2.le (by positivity)
      have h3 : R ^ 2 * (1 / (6 * R ^ 2)) = 1 / 6 := by field_simp
      linarith
    have hle1 : ∀ n ≥ N, ∀ z ∈ ball (0 : ℂ) R, ‖z / zs n‖ ≤ 1 := fun n hn z hz => by
      have := hw1 n hn z hz
      nlinarith [norm_nonneg (z / zs n)]
    have ha2 : ∀ n ≥ N, ∀ z ∈ ball (0 : ℂ) R, ‖a n z‖ ≤ 1 / 2 := fun n hn z hz => by
      have := norm_weierstrassE_sub_one_le (hle1 n hn z hz)
      have := hw1 n hn z hz
      simp only [hadef]
      linarith
    have hne : ∀ n ≥ N, ∀ z ∈ ball (0 : ℂ) R, 1 + a n z ≠ 0 := fun n hn z hz h => by
      have : a n z = -1 := by linear_combination h
      have := ha2 n hn z hz
      rw [‹a n z = -1›, norm_neg, norm_one] at this
      norm_num at this
    obtain ⟨p, -, -, han, hpt⟩ := dlmf_1_10_20 isOpen_ball (fun n => (hda n).differentiableOn)
      hN hne (M := fun n => 9 / 2 * R ^ 2 * ‖(zs n ^ 2)⁻¹‖) (fun n hn z hz => by
        have h1 := norm_log_one_add_half_le_self (ha2 n hn z hz)
        have h2 := norm_weierstrassE_sub_one_le (hle1 n hn z hz)
        have h3 := hw n hn z hz
        simp only [hadef] at h1 ⊢
        nlinarith [norm_nonneg (log (1 + (weierstrassE (z / zs n) - 1)))])
      (hs.mul_left _)
    refine ⟨_, han, fun z hz => ⟨?_, ?_⟩⟩
    · exact ((hpt z hz).2.1).congr fun m => hpp z m
    · rw [(hpt z hz).2.2, hzero]
  have hval : ∀ R > 0, ∀ P : ℂ → ℂ, (∀ z ∈ ball (0 : ℂ) R,
      Tendsto (fun m => ∏ n ∈ Ico 1 (m + 1), weierstrassE (z / zs n)) atTop (𝓝 (P z))) →
      ∀ z ∈ ball (0 : ℂ) R, weierstrassProduct zs z = P z := fun R _ P hP z hz =>
    (hP z hz).limUnder_eq
  have hRz : ∀ z : ℂ, z ∈ ball (0 : ℂ) (‖z‖ + 1) := fun z => by
    rw [mem_ball, dist_zero_right]
    linarith
  refine ⟨fun z => ?_, fun z => ?_, fun z => ?_⟩
  · obtain ⟨P, hPa, hP⟩ := key (‖z‖ + 1) (by positivity)
    have heq : weierstrassProduct zs =ᶠ[𝓝 z] P :=
      eventually_of_mem (isOpen_ball.mem_nhds (hRz z)) fun w hw =>
        hval _ (by positivity) P (fun w hw => (hP w hw).1) w hw
    exact ((hPa z (hRz z)).differentiableAt).congr_of_eventuallyEq heq
  · obtain ⟨P, -, hP⟩ := key (‖z‖ + 1) (by positivity)
    rw [hval _ (by positivity) P (fun w hw => (hP w hw).1) z (hRz z)]
    exact (hP z (hRz z)).1
  · obtain ⟨P, -, hP⟩ := key (‖z‖ + 1) (by positivity)
    rw [hval _ (by positivity) P (fun w hw => (hP w hw).1) z (hRz z)]
    exact (hP z (hRz z)).2

end Azurite.DLMF
