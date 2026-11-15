/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter6.Section9
import Mathlib.Analysis.Analytic.Binomial

/-!
# DLMF §6.10(i): inverse factorial series

Formalizations of <https://dlmf.nist.gov/6.10.i>, equations 6.10.1–6.10.3.

## Main results

* `e1c`, `dlmf_6_10_3`: the coefficients `c_k` by their recursion `c₀ = 1`,
  `c_k = −∑_{j<k} c_j/(k − j)`.
* `dlmf_6_10_2`: `c₀, …, c₄ = 1, −1, 1/2, −1/3, 1/6`.
* `dlmf_6_10_1`: the inverse factorial series
  `E₁(z) = e^{−z} ∑ k! c_k / (z(z+1)⋯(z+k))` converges to `E₁(z)` for `ℜz > 0`.

## Method

The coefficients are the integrals `c_k = ∫₀^∞ e^{−s} (−1)^k C(s, k) ds` (`e1c_eq_binGamma`,
by integration by parts against the recursion of `binq`). Writing `e^z E₁(z) = ∫₀^∞ e^{−zt}/(1+t)`
(`exp_mul_E1_eq_integral`), the partial sums `S_n(t) = ∑_{k<n} c_k (1 − e^{−t})^k` tend to
`∫₀^∞ e^{−s} e^{−st} ds = 1/(1+t)` by the binomial series `∑ (−1)^k C(s,k) u^k = (1 − u)^s`
(`tendsto_e1Sc`). The partial sums of the binomial series are bounded uniformly
(`abs_binq_partial_le`, from the sign pattern of the binomial tail), so `|S_n| ≤ K`
(`abs_e1Sc_le`) and dominated convergence applies; the Beta integral
`∫₀^∞ e^{−zt}(1 − e^{−t})^k dt = k!/(z(z+1)⋯(z+k))` (`betaJ_eq`) identifies the terms.
-/

open Complex Filter Topology Set MeasureTheory Polynomial
open scoped Real Nat

namespace Azurite.DLMF

/-! ### 6.10.2, 6.10.3: the coefficients -/

/-- **DLMF 6.10.3**: `c₀ = 1`, `c_k = −∑_{j<k} c_j/(k − j)`. -/
noncomputable def e1c : ℕ → ℝ
  | 0 => 1
  | k + 1 => -∑ j : Fin (k + 1), e1c j / ((k + 1 : ℕ) - (j : ℕ) : ℝ)
termination_by k => k
decreasing_by exact j.isLt

/-- **DLMF 6.10.3**. -/
theorem dlmf_6_10_3 {k : ℕ} (hk : 1 ≤ k) :
    e1c k = -∑ j ∈ Finset.range k, e1c j / (k - j : ℝ) := by
  obtain ⟨k, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [e1c, Finset.sum_range (fun j => e1c j / ((k + 1 : ℕ) - j : ℝ))]

/-- **DLMF 6.10.2**: `c₀ = 1`, `c₁ = −1`, `c₂ = 1/2`, `c₃ = −1/3`, `c₄ = 1/6`. -/
theorem dlmf_6_10_2 :
    e1c 0 = 1 ∧ e1c 1 = -1 ∧ e1c 2 = 1 / 2 ∧ e1c 3 = -1 / 3 ∧ e1c 4 = 1 / 6 := by
  have h0 : e1c 0 = 1 := by rw [e1c]
  have h1 : e1c 1 = -1 := by rw [dlmf_6_10_3 le_rfl]; simp [h0]
  have h2 : e1c 2 = 1 / 2 := by
    rw [dlmf_6_10_3 (by norm_num)]; simp [Finset.sum_range_succ, h0, h1]; norm_num
  have h3 : e1c 3 = -1 / 3 := by
    rw [dlmf_6_10_3 (by norm_num)]; simp [Finset.sum_range_succ, h0, h1, h2]; norm_num
  have h4 : e1c 4 = 1 / 6 := by
    rw [dlmf_6_10_3 (by norm_num)]; simp [Finset.sum_range_succ, h0, h1, h2, h3]; norm_num
  exact ⟨h0, h1, h2, h3, h4⟩

/-! ### The binomial coefficients `qₖ(s) = (−1)ᵏ C(s, k)` of `(1 − u)^s` -/

/-- `qₖ(s) = (−1)ᵏ s(s−1)⋯(s−k+1)/k!`, the coefficient of `uᵏ` in `(1 − u)^s`. -/
noncomputable def binq (k : ℕ) (s : ℝ) : ℝ := (-1) ^ k / k ! * (descPochhammer ℝ k).eval s

theorem binq_zero (s : ℝ) : binq 0 s = 1 := by simp [binq]

theorem binq_at_zero {k : ℕ} (hk : 1 ≤ k) : binq k 0 = 0 := by
  simp [binq, show k ≠ 0 by omega]

/-- `(k + 1) q_{k+1} = (k − s) qₖ`. -/
theorem binq_succ (k : ℕ) (s : ℝ) : (k + 1 : ℝ) * binq (k + 1) s = (k - s) * binq k s := by
  simp only [binq, descPochhammer_succ_eval, Nat.factorial_succ, pow_succ]
  have : (k ! : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem binq_eq_choose (k : ℕ) (s : ℝ) : binq k s = (-1) ^ k * Ring.choose s k := by
  rw [Ring.choose_eq_smul, smul_eq_mul, ← aeval_eq_smeval, aeval_def, ← eval_map,
    descPochhammer_map, binq]
  ring

theorem continuous_binq (k : ℕ) : Continuous (binq k) :=
  continuous_const.mul (Polynomial.continuous _)

/-- The derivative identity `qₖ′ = −∑_{j<k} q_j/(k − j)`. -/
noncomputable def binqDeriv (k : ℕ) (s : ℝ) : ℝ := -∑ j ∈ Finset.range k, binq j s / (k - j : ℝ)

theorem hasDerivAt_binq : ∀ (k : ℕ) (s : ℝ), HasDerivAt (binq k) (binqDeriv k s) s := by
  intro k
  induction k with
  | zero =>
    intro s
    have : binq 0 = fun _ => 1 := funext binq_zero
    rw [this]
    simpa [binqDeriv] using hasDerivAt_const s (1 : ℝ)
  | succ k ih =>
    intro s
    have hfun : binq (k + 1) = fun s => (k - s) * binq k s / (k + 1 : ℝ) := by
      funext s
      have := binq_succ k s
      field_simp
      linarith
    rw [hfun]
    have h1 := (((hasDerivAt_const s (k : ℝ)).sub (hasDerivAt_id s)).mul (ih s)).div_const
      ((k : ℝ) + 1)
    refine h1.congr_deriv ?_
    -- `(−q_k + (k − s) q_k′)/(k + 1) = q_{k+1}′`
    have hs : ∀ j : ℕ, s * binq j s = j * binq j s - (j + 1) * binq (j + 1) s := fun j => by
      have := binq_succ j s
      linarith
    simp only [binqDeriv, Pi.sub_apply, id, zero_sub, neg_one_mul]
    have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
    -- rewrite `(k − s) q_j = (k − j) q_j + (j + 1) q_{j+1}`
    have hsum : (k - s) * ∑ j ∈ Finset.range k, binq j s / (k - j : ℝ) =
        ∑ j ∈ Finset.range k, binq j s +
          ∑ j ∈ Finset.range k, (j + 1 : ℝ) * binq (j + 1) s / (k - j : ℝ) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjk : (k : ℝ) - j ≠ 0 := by
        have := Finset.mem_range.mp hj
        have : (j : ℝ) < k := by exact_mod_cast this
        linarith
      rw [show (k - s) * (binq j s / (k - j : ℝ)) = (k * binq j s - s * binq j s) / (k - j) by ring,
        hs j]
      field_simp
      ring
    have hsum2 : (k + 1 : ℝ) * ∑ j ∈ Finset.range (k + 1), binq j s / ((k + 1 : ℕ) - j : ℝ) =
        ∑ j ∈ Finset.range (k + 1), binq j s +
          ∑ j ∈ Finset.range k, (j + 1 : ℝ) * binq (j + 1) s / (k - j : ℝ) := by
      rw [Finset.mul_sum]
      have e : ∀ j ∈ Finset.range (k + 1), (k + 1 : ℝ) * (binq j s / ((k + 1 : ℕ) - j : ℝ)) =
          binq j s + j * binq j s / ((k + 1 : ℕ) - j : ℝ) := by
        intro j hj
        have hjk : ((k + 1 : ℕ) : ℝ) - j ≠ 0 := by
          have := Finset.mem_range.mp hj
          have : (j : ℝ) < k + 1 := by exact_mod_cast this
          push_cast; linarith
        field_simp
        push_cast
        ring
      rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_range_succ' (fun j =>
        (j : ℝ) * binq j s / ((k + 1 : ℕ) - j : ℝ))]
      simp only [Nat.cast_zero, zero_mul, zero_div, add_zero]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      push_cast
      ring_nf
    rw [div_eq_iff hk1]
    have e3 := Finset.sum_range_succ (fun j => binq j s) k
    push_cast at hsum2 ⊢
    linear_combination (-1 : ℝ) * hsum + hsum2 + e3

/-! ### `c_k = ∫_0^∞ e^{−s} qₖ(s) ds` -/

theorem integrableOn_pow_mul_exp_neg (i : ℕ) :
    IntegrableOn (fun s : ℝ => s ^ i * Real.exp (-s)) (Ioi 0) := by
  have h := Real.GammaIntegral_convergent (s := (i : ℝ) + 1) (by positivity)
  refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
  show Real.exp (-x) * x ^ ((i : ℝ) + 1 - 1) = x ^ i * Real.exp (-x)
  rw [show (i : ℝ) + 1 - 1 = ((i : ℕ) : ℝ) by ring, Real.rpow_natCast, mul_comm]

/-- `p(s) e^{−s}` is integrable on `(0, ∞)` and tends to `0` at `∞`, for a polynomial `p`. -/
theorem poly_mul_exp_neg (p : ℝ[X]) :
    IntegrableOn (fun s => p.eval s * Real.exp (-s)) (Ioi 0) ∧
      Tendsto (fun s => p.eval s * Real.exp (-s)) atTop (𝓝 0) := by
  have e : (fun s => p.eval s * Real.exp (-s)) =
      fun s => ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * (s ^ i * Real.exp (-s)) := by
    funext s
    rw [eval_eq_sum_range, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  refine ⟨integrable_finsetSum _ fun i _ => (integrableOn_pow_mul_exp_neg i).const_mul _, ?_⟩
  have := tendsto_finsetSum (Finset.range (p.natDegree + 1)) fun i _ =>
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero i).const_mul (p.coeff i)
  simpa using this

/-- `qₖ` as a polynomial. -/
theorem binq_eq_eval (k : ℕ) :
    binq k = fun s => (Polynomial.C ((-1) ^ k / k ! : ℝ) * descPochhammer ℝ k).eval s := by
  funext s; simp [binq]

theorem binq_mul_exp_neg (k : ℕ) :
    IntegrableOn (fun s => binq k s * Real.exp (-s)) (Ioi 0) ∧
      Tendsto (fun s => binq k s * Real.exp (-s)) atTop (𝓝 0) := by
  rw [binq_eq_eval]
  exact poly_mul_exp_neg _

/-- `γₖ = ∫_0^∞ e^{−s} qₖ(s) ds`. -/
noncomputable def binGamma (k : ℕ) : ℝ := ∫ s in Ioi (0 : ℝ), binq k s * Real.exp (-s)

theorem binGamma_rec {k : ℕ} (hk : 1 ≤ k) :
    binGamma k = -∑ j ∈ Finset.range k, binGamma j / (k - j : ℝ) := by
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul (a := 0) (a' := 0) (b' := 0)
    (u := binq k) (u' := binqDeriv k) (v := fun s => -Real.exp (-s)) (v' := fun s => Real.exp (-s))
    (fun s _ => hasDerivAt_binq k s)
    (fun s _ => ((Real.hasDerivAt_exp (-s)).comp s (hasDerivAt_neg s)).neg.congr_deriv (by simp))
    (binq_mul_exp_neg k).1 ?_ ?_ ?_
  · have hpt : ∀ x, binqDeriv k x * -Real.exp (-x) =
        ∑ j ∈ Finset.range k, binq j x * Real.exp (-x) / (k - j : ℝ) := fun x => by
      simp only [binqDeriv, neg_mul, mul_neg, neg_neg, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hint : ∀ j ∈ Finset.range k, Integrable
        (fun s => binq j s * Real.exp (-s) / (k - j : ℝ)) (volume.restrict (Ioi 0)) := fun j _ =>
      (binq_mul_exp_neg j).1.div_const _
    have hI : ∫ x in Ioi (0 : ℝ), binqDeriv k x * -Real.exp (-x) =
        ∑ j ∈ Finset.range k, binGamma j / (k - j : ℝ) := by
      rw [show (fun x => binqDeriv k x * -Real.exp (-x)) = fun x =>
        ∑ j ∈ Finset.range k, binq j x * Real.exp (-x) / (k - j : ℝ) from funext hpt,
        integral_finsetSum _ hint]
      exact Finset.sum_congr rfl fun j _ => by rw [integral_div]; rfl
    rw [binGamma, hibp, hI]
    ring
  · -- `u′ v` integrable
    have : (fun s => binqDeriv k s * -Real.exp (-s)) =
        fun s => ∑ j ∈ Finset.range k, binq j s * Real.exp (-s) / (k - j : ℝ) := by
      funext s
      simp only [binqDeriv, neg_mul, mul_neg, neg_neg, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [show (binqDeriv k * fun s => -Real.exp (-s)) =
      fun s => binqDeriv k s * -Real.exp (-s) from rfl, this]
    exact integrable_finsetSum _ fun j _ => (binq_mul_exp_neg j).1.div_const _
  · -- at `0+`
    have hc : Continuous fun s => binq k s * -Real.exp (-s) :=
      (continuous_binq k).mul (Real.continuous_exp.comp continuous_neg).neg
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    rw [binq_at_zero hk, zero_mul] at this
    exact this
  · -- at `∞`
    have := (binq_mul_exp_neg k).2.neg
    rw [neg_zero] at this
    exact this.congr fun s => by simp [mul_neg]

theorem binGamma_zero : binGamma 0 = 1 := by
  rw [binGamma]
  simp only [binq_zero, one_mul]
  exact integral_exp_neg_Ioi_zero

/-- **The coefficients are moments**: `c_k = ∫_0^∞ e^{−s} (−1)ᵏ C(s, k) ds`. -/
theorem e1c_eq_binGamma (k : ℕ) : e1c k = binGamma k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [binGamma_zero, e1c]
    · rw [dlmf_6_10_3 hk, binGamma_rec hk]
      congr 1
      exact Finset.sum_congr rfl fun j hj => by rw [ih j (Finset.mem_range.mp hj)]

/-! ### Uniform bounds on the binomial partial sums -/

/-- The binomial series `(1 − u)^s = ∑ qₖ(s) uᵏ`, `|u| < 1`. -/
theorem hasSum_binq (s : ℝ) {u : ℝ} (hu : |u| < 1) :
    HasSum (fun k => binq k s * u ^ k) ((1 - u) ^ s) := by
  have hball : -u ∈ Metric.eball (0 : ℝ) 1 := by
    rw [Metric.mem_eball, edist_zero_right, enorm_neg, Real.enorm_eq_ofReal_abs]
    exact (ENNReal.ofReal_lt_one).mpr hu
  have h := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := s)).hasSum hball
  simp only [binomialSeries_apply, List.ofFn_const, List.prod_replicate, smul_eq_mul,
    zero_add] at h
  rw [show (1 : ℝ) - u = 1 + -u by ring]
  refine h.congr_fun fun k => ?_
  rw [binq_eq_choose, neg_pow]
  ring

/-- `|qₖ(s)| ≤ C(m, k)` for `k ≤ m = ⌈s⌉`. -/
theorem abs_binq_le_choose {s : ℝ} (hs : 0 ≤ s) :
    ∀ k, k ≤ ⌈s⌉₊ → |binq k s| ≤ (⌈s⌉₊.choose k : ℝ) := by
  set m := ⌈s⌉₊
  have hm : (m : ℝ) < s + 1 := Nat.ceil_lt_add_one hs
  intro k
  induction k with
  | zero => intro _; simp [binq_zero]
  | succ k ih =>
    intro hk
    have hk' := ih (by omega)
    have hks : (k : ℝ) ≤ s := by
      have : (k : ℝ) + 1 ≤ m := by exact_mod_cast hk
      linarith
    have hrec := binq_succ k s
    have habs : |binq (k + 1) s| = (s - k) / (k + 1) * |binq k s| := by
      have hk1 : (0 : ℝ) < k + 1 := by positivity
      have : binq (k + 1) s = (k - s) / (k + 1) * binq k s := by field_simp; linarith
      rw [this, abs_mul, abs_div, abs_of_pos hk1, abs_of_nonpos (by linarith)]
      ring
    have hch : (m.choose (k + 1) : ℝ) * (k + 1) = (m.choose k : ℝ) * (m - k) := by
      have := Nat.choose_succ_right_eq m k
      rw [← Nat.cast_sub (by omega)]
      exact_mod_cast this
    rw [habs]
    have hk1 : (0 : ℝ) < k + 1 := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hk1, hch]
    have h1 : s - k ≤ m - k := by linarith [Nat.le_ceil s]
    have h2 : 0 ≤ s - k := by linarith
    calc (s - k) * |binq k s| ≤ (m - k) * (m.choose k : ℝ) :=
          mul_le_mul h1 hk' (abs_nonneg _) (by linarith)
      _ = (m.choose k : ℝ) * (m - k) := by ring

/-- **The partial sums of the binomial series of `(1 − u)^s`** are bounded by `2^{s+1} + 1` on
`0 ≤ u < 1`, `s ≥ 0` (the terms keep one sign from `k = ⌈s⌉` on). -/
theorem abs_binq_partial_le {s : ℝ} (hs : 0 ≤ s) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (n : ℕ) :
    |∑ k ∈ Finset.range n, binq k s * u ^ k| ≤ (2 : ℝ) ^ (s + 1) + 1 := by
  set m := ⌈s⌉₊ with hmdef
  have hm : (m : ℝ) < s + 1 := Nat.ceil_lt_add_one hs
  have h2m : (2 : ℝ) ^ m ≤ (2 : ℝ) ^ (s + 1) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hm.le
  -- the first `m` terms
  have hfirst : ∀ n, n ≤ m → |∑ k ∈ Finset.range n, binq k s * u ^ k| ≤ (2 : ℝ) ^ m := by
    intro n hn
    calc |∑ k ∈ Finset.range n, binq k s * u ^ k|
        ≤ ∑ k ∈ Finset.range n, |binq k s * u ^ k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) := by
          refine (Finset.sum_le_sum fun k hk => ?_).trans (Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_subset_range.mpr (by omega)) fun _ _ _ => by positivity)
          rw [abs_mul, abs_of_nonneg (pow_nonneg hu0 k)]
          have := abs_binq_le_choose hs k (by have := Finset.mem_range.mp hk; omega)
          calc |binq k s| * u ^ k ≤ |binq k s| * 1 :=
                mul_le_mul_of_nonneg_left (pow_le_one₀ hu0 hu1.le) (abs_nonneg _)
            _ ≤ _ := by rw [mul_one]; exact this
      _ = (2 : ℝ) ^ m := by exact_mod_cast Nat.sum_range_choose m
  rcases le_or_gt n m with hn | hn
  · exact (hfirst n hn).trans (by linarith)
  -- from `m` on the terms have the sign `σ` of `q_m`
  set σ : ℝ := if binq m s < 0 then -1 else 1 with hσ
  have hσ1 : |σ| = 1 := by rw [hσ]; split_ifs <;> simp
  have hsign : ∀ j, 0 ≤ σ * binq (m + j) s := by
    intro j
    induction j with
    | zero =>
      rw [add_zero, hσ]
      split_ifs with h
      · linarith
      · push Not at h; linarith
    | succ j ih =>
      have hrec := binq_succ (m + j) s
      have hk1 : (0 : ℝ) < (m + j : ℕ) + 1 := by positivity
      have hge : 0 ≤ ((m + j : ℕ) : ℝ) - s := by push_cast; linarith [Nat.le_ceil s]
      have : binq (m + j + 1) s = (((m + j : ℕ) : ℝ) - s) / ((m + j : ℕ) + 1) * binq (m + j) s := by
        field_simp; push_cast at hrec ⊢; linarith
      rw [show m + (j + 1) = m + j + 1 by ring, this,
        show σ * ((((m + j : ℕ) : ℝ) - s) / ((m + j : ℕ) + 1) * binq (m + j) s) =
          (((m + j : ℕ) : ℝ) - s) / ((m + j : ℕ) + 1) * (σ * binq (m + j) s) by ring]
      exact mul_nonneg (div_nonneg hge hk1.le) ih
  -- `g(j) = σ S_{m+j}` increases to `σ (1 − u)^s`
  set S : ℕ → ℝ := fun n => ∑ k ∈ Finset.range n, binq k s * u ^ k
  have hmono : Monotone fun j => σ * S (m + j) := by
    refine monotone_nat_of_le_succ fun j => ?_
    simp only [S, show m + (j + 1) = m + j + 1 by ring, Finset.sum_range_succ, mul_add]
    have := mul_nonneg (hsign j) (pow_nonneg hu0 (m + j))
    linarith [show σ * (binq (m + j) s * u ^ (m + j)) = σ * binq (m + j) s * u ^ (m + j) by ring]
  have hlim : Tendsto (fun j => σ * S (m + j)) atTop (𝓝 (σ * (1 - u) ^ s)) := by
    have h := (hasSum_binq s (by rw [abs_of_nonneg hu0]; exact hu1)).tendsto_sum_nat
    exact (h.comp (tendsto_atTop_mono (fun j => Nat.le_add_left j m) tendsto_id)).const_mul σ
  obtain ⟨j, rfl⟩ : ∃ j, n = m + j := ⟨n - m, by omega⟩
  have hup := hmono.ge_of_tendsto hlim j
  have hlow : σ * S m ≤ σ * S (m + j) := by simpa using hmono (Nat.zero_le j)
  have hpow0 : 0 ≤ (1 - u) ^ s := Real.rpow_nonneg (by linarith) s
  have hpow1 : (1 - u) ^ s ≤ 1 := Real.rpow_le_one (by linarith) (by linarith) hs
  have hSm := hfirst m le_rfl
  -- `|S| = |σ S|`, and `σ S` lies between `σ S_m` and `σ (1 − u)^s`
  have key : |σ * S (m + j)| ≤ |σ * S m| + 1 := by
    rw [abs_le]
    have h1 : |σ * S m| = |S m| := by rw [abs_mul, hσ1, one_mul]
    have h2 : |σ * (1 - u) ^ s| ≤ 1 := by
      rw [abs_mul, hσ1, one_mul, abs_of_nonneg hpow0]; exact hpow1
    constructor
    · linarith [neg_abs_le (σ * S m), abs_nonneg (σ * S m)]
    · linarith [le_abs_self (σ * (1 - u) ^ s), abs_nonneg (σ * S m)]
  rw [abs_mul, hσ1, one_mul, abs_mul, hσ1, one_mul] at key
  show |S (m + j)| ≤ _
  linarith

/-! ### The partial sums of `∑ c_k (1 − e^{−t})ᵏ` -/

theorem integrableOn_binBound :
    IntegrableOn (fun s : ℝ => ((2 : ℝ) ^ (s + 1) + 1) * Real.exp (-s)) (Ioi 0) := by
  have hl : 0 < 1 - Real.log 2 := by have := Real.log_two_lt_d9; linarith
  have h1 := (exp_neg_integrableOn_Ioi 0 hl).const_mul 2
  have h2 := exp_neg_integrableOn_Ioi 0 (b := 1) one_pos
  have h3 : IntegrableOn (fun x => 2 * Real.exp (-(1 - Real.log 2) * x) +
      Real.exp (-1 * x)) (Ioi 0) volume := h1.add h2
  refine h3.congr_fun (fun s _ => ?_) measurableSet_Ioi
  show 2 * Real.exp (-(1 - Real.log 2) * s) + Real.exp (-1 * s) =
    ((2 : ℝ) ^ (s + 1) + 1) * Real.exp (-s)
  rw [Real.rpow_def_of_pos two_pos, add_mul, ← Real.exp_add, one_mul, neg_one_mul]
  congr 1
  rw [show Real.log 2 * (s + 1) + -s = Real.log 2 + -(1 - Real.log 2) * s by ring, Real.exp_add,
    Real.exp_log two_pos]

/-- `K = ∫_0^∞ (2^{s+1} + 1) e^{−s} ds`. -/
noncomputable def binK : ℝ := ∫ s in Ioi (0 : ℝ), ((2 : ℝ) ^ (s + 1) + 1) * Real.exp (-s)

/-- `S_n(t) = ∑_{k<n} c_k (1 − e^{−t})ᵏ`. -/
noncomputable def e1Sc (n : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, e1c k * (1 - Real.exp (-t)) ^ k

theorem e1Sc_eq (n : ℕ) (t : ℝ) : e1Sc n t = ∫ s in Ioi (0 : ℝ),
    (∑ k ∈ Finset.range n, binq k s * (1 - Real.exp (-t)) ^ k) * Real.exp (-s) := by
  have hint : ∀ k ∈ Finset.range n, Integrable
      (fun s => binq k s * Real.exp (-s) * (1 - Real.exp (-t)) ^ k) (volume.restrict (Ioi 0)) :=
    fun k _ => (binq_mul_exp_neg k).1.mul_const _
  rw [e1Sc]
  symm
  calc ∫ s in Ioi (0 : ℝ), (∑ k ∈ Finset.range n, binq k s * (1 - Real.exp (-t)) ^ k) *
        Real.exp (-s)
      = ∫ s in Ioi (0 : ℝ), ∑ k ∈ Finset.range n,
          binq k s * Real.exp (-s) * (1 - Real.exp (-t)) ^ k := by
        congr 1; funext s; rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = ∑ k ∈ Finset.range n, ∫ s in Ioi (0 : ℝ),
          binq k s * Real.exp (-s) * (1 - Real.exp (-t)) ^ k := integral_finsetSum _ hint
    _ = ∑ k ∈ Finset.range n, e1c k * (1 - Real.exp (-t)) ^ k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [integral_mul_const, e1c_eq_binGamma, binGamma]

theorem e1Sc_u {t : ℝ} (ht : 0 ≤ t) : 0 ≤ 1 - Real.exp (-t) ∧ 1 - Real.exp (-t) < 1 := by
  have h1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  exact ⟨by linarith, by linarith [Real.exp_pos (-t)]⟩

/-- **The partial sums are bounded**: `|S_n(t)| ≤ K` for `t ≥ 0`. -/
theorem abs_e1Sc_le (n : ℕ) {t : ℝ} (ht : 0 ≤ t) : |e1Sc n t| ≤ binK := by
  obtain ⟨hu0, hu1⟩ := e1Sc_u ht
  rw [e1Sc_eq, binK, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le integrableOn_binBound
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun s (hs : 0 < s) => ?_))
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_right (abs_binq_partial_le hs.le hu0 hu1 n) (Real.exp_pos _).le

/-- `S_n(t) → 1/(1 + t)` for `t ≥ 0` (dominated convergence in `s`). -/
theorem tendsto_e1Sc {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n => e1Sc n t) atTop (𝓝 (1 / (1 + t))) := by
  obtain ⟨hu0, hu1⟩ := e1Sc_u ht
  set u := 1 - Real.exp (-t)
  have hlim : ∫ s in Ioi (0 : ℝ), (1 - u) ^ s * Real.exp (-s) = 1 / (1 + t) := by
    have e : ∀ s : ℝ, (1 - u) ^ s * Real.exp (-s) = Real.exp (-(1 + t) * s) := fun s => by
      rw [show 1 - u = Real.exp (-t) by simp [u], ← Real.exp_mul, ← Real.exp_add]
      ring_nf
    simp_rw [e]
    rw [integral_exp_mul_Ioi (by linarith) 0, mul_zero, Real.exp_zero, neg_div_neg_eq]
  simp_rw [e1Sc_eq]
  rw [← hlim]
  refine tendsto_integral_of_dominated_convergence
    (fun s => ((2 : ℝ) ^ (s + 1) + 1) * Real.exp (-s)) (fun n => ?_) integrableOn_binBound
    (fun n => (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun s (hs : 0 < s) => ?_))
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun s (hs : 0 < s) => ?_))
  · exact ((continuous_finsetSum _ fun k _ => (continuous_binq k).mul continuous_const).mul
      (Real.continuous_exp.comp continuous_neg)).aestronglyMeasurable
  · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (abs_binq_partial_le hs.le hu0 hu1 n) (Real.exp_pos _).le
  · exact ((hasSum_binq s (by rw [abs_of_nonneg hu0]; exact hu1)).tendsto_sum_nat).mul_const _

/-! ### `∫_0^∞ e^{−zt}(1 − e^{−t})ᵏ dt = k!/(z(z+1)⋯(z+k))` -/

theorem norm_exp_neg_mul_ofReal {z : ℂ} (t : ℝ) : ‖cexp (-(z * t))‖ = Real.exp (-(z.re * t)) := by
  rw [norm_exp]; simp

theorem integrableOn_exp_neg_mul_bounded {z : ℂ} (hz : 0 < z.re) {g : ℝ → ℂ}
    (hg : Continuous g) {C : ℝ} (hC : ∀ t, 0 ≤ t → ‖g t‖ ≤ C) :
    IntegrableOn (fun t : ℝ => cexp (-(z * t)) * g t) (Ioi 0) := by
  have h := (exp_neg_integrableOn_Ioi 0 hz).const_mul C
  refine Integrable.mono' h ((by fun_prop : Continuous fun t : ℝ => cexp (-(z * t))).mul hg
    |>.aestronglyMeasurable) ((ae_restrict_iff' measurableSet_Ioi).mpr
      (ae_of_all _ fun t (ht : 0 < t) => ?_))
  rw [norm_mul, norm_exp_neg_mul_ofReal, mul_comm, neg_mul]
  exact mul_le_mul_of_nonneg_right (hC t ht.le) (Real.exp_pos _).le

theorem norm_one_sub_exp_pow_le {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    ‖(((1 - Real.exp (-t)) ^ k : ℝ) : ℂ)‖ ≤ 1 := by
  obtain ⟨h0, h1⟩ := e1Sc_u ht
  rw [norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h0 k)]
  exact pow_le_one₀ h0 h1.le

/-- The Beta integral `Jₖ(z)`. -/
noncomputable def betaJ (k : ℕ) (z : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), cexp (-(z * t)) * (((1 - Real.exp (-t)) ^ k : ℝ) : ℂ)

theorem betaJ_eq : ∀ (k : ℕ) {z : ℂ}, 0 < z.re →
    betaJ k z = k ! / ∏ i ∈ Finset.range (k + 1), (z + i) := by
  intro k
  induction k with
  | zero =>
    intro z hz
    simp only [betaJ, pow_zero, ofReal_one, mul_one, Nat.factorial_zero, Nat.cast_one]
    have h := integral_exp_mul_complex_Ioi (a := -z) (by simpa using hz) 0
    simp only [ofReal_zero, mul_zero, exp_zero] at h
    rw [show (fun t : ℝ => cexp (-(z * t))) = fun t : ℝ => cexp (-z * t) by
      funext t; ring_nf, h]
    simp
  | succ k ih =>
    intro z hz
    have hz0 : z ≠ 0 := fun h => by simp [h] at hz
    have hz1 : 0 < (z + 1).re := by simp; linarith
    -- integration by parts with `u = (1 − e^{−t})^{k+1}`, `v = −e^{−zt}/z`
    set u : ℝ → ℂ := fun t => (((1 - Real.exp (-t)) ^ (k + 1) : ℝ) : ℂ)
    set u' : ℝ → ℂ := fun t =>
      ((((k + 1 : ℕ) : ℝ) * (1 - Real.exp (-t)) ^ k * Real.exp (-t) : ℝ) : ℂ)
    set v : ℝ → ℂ := fun t => -cexp (-(z * t)) / z
    set v' : ℝ → ℂ := fun t => cexp (-(z * t))
    have hu : ∀ t, HasDerivAt u (u' t) t := fun t => by
      have h1 : HasDerivAt (fun t => 1 - Real.exp (-t)) (Real.exp (-t)) t := by
        have := ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)).const_sub 1
        simpa using this
      have h2 := (h1.pow (k + 1)).ofReal_comp
      refine h2.congr_deriv ?_
      simp only [u']
      push_cast
      ring
    have hv : ∀ t, HasDerivAt v (v' t) t := fun t => by
      have h1 : HasDerivAt (fun w : ℂ => -cexp (-(z * w)) / z) (cexp (-(z * t))) (t : ℂ) := by
        have := ((((hasDerivAt_id (t : ℂ)).const_mul z).neg).cexp.neg).div_const z
        simp only [Pi.neg_apply, id, mul_one] at this
        refine this.congr_deriv ?_
        field_simp
      exact h1.comp_ofReal
    have hibp := integral_Ioi_mul_deriv_eq_deriv_mul (a := 0) (a' := 0) (b' := 0)
      (fun t _ => hu t) (fun t _ => hv t) ?_ ?_ ?_ ?_
    · -- `J_{k+1}(z) = (k+1)/z · J_k(z+1)`
      have hJ : betaJ (k + 1) z = (k + 1) / z * betaJ k (z + 1) := by
        have e1 : betaJ (k + 1) z = ∫ t in Ioi (0 : ℝ), u t * v' t := by
          rw [betaJ]
          refine setIntegral_congr_fun measurableSet_Ioi fun t _ => by simp [u, v']; ring
        rw [e1, hibp, betaJ, sub_self, zero_sub, ← integral_neg, ← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
        simp only [u', v]
        push_cast
        rw [show -((z + 1) * (t : ℂ)) = -(z * t) + -(t : ℂ) by ring, exp_add]
        field_simp
      rw [hJ, ih hz1, Finset.prod_range_succ' (fun i => z + i), Nat.factorial_succ]
      push_cast
      simp only [add_zero]
      have hp : ∏ i ∈ Finset.range (k + 1), (z + 1 + i) ≠ 0 := by
        refine Finset.prod_ne_zero_iff.mpr fun i _ h => ?_
        have := congrArg Complex.re h
        simp at this
        linarith [show (0 : ℝ) ≤ i from Nat.cast_nonneg i]
      rw [show ∏ i ∈ Finset.range (k + 1), (z + ((i : ℂ) + 1)) =
        ∏ i ∈ Finset.range (k + 1), (z + 1 + i) from
        Finset.prod_congr rfl fun i _ => by ring]
      field_simp
    · exact integrableOn_exp_neg_mul_bounded (g := fun t => u t) hz (by fun_prop)
        (fun t ht => norm_one_sub_exp_pow_le ht (k + 1)) |>.congr_fun
        (fun t _ => by simp [u, v']; ring) measurableSet_Ioi
    · -- `u′ v` integrable
      have hb : ∀ t, 0 ≤ t → ‖-((((k + 1 : ℕ) : ℝ) * (1 - Real.exp (-t)) ^ k * Real.exp (-t) : ℝ)
          : ℂ) / z‖ ≤ ((k + 1 : ℕ) : ℝ) / ‖z‖ := by
        intro t ht
        obtain ⟨h0, h1⟩ := e1Sc_u ht
        rw [norm_div, norm_neg, norm_real, Real.norm_eq_abs]
        refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
        rw [abs_of_nonneg (by positivity)]
        have hp : (1 - Real.exp (-t)) ^ k ≤ 1 := pow_le_one₀ h0 h1.le
        have he : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
        have : (1 - Real.exp (-t)) ^ k * Real.exp (-t) ≤ 1 := by
          have := mul_le_mul hp he (Real.exp_pos _).le zero_le_one
          linarith
        nlinarith [Real.exp_pos (-t), pow_nonneg h0 k,
          show (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) from Nat.cast_nonneg _]
      refine (integrableOn_exp_neg_mul_bounded hz (by fun_prop) hb).congr_fun
        (fun t _ => ?_) measurableSet_Ioi
      simp only [u', v, Pi.mul_apply]
      ring
    · -- `u v → 0` at `0+`
      have hc : Continuous (u * v) := by
        simp only [u, v]; fun_prop
      have h := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      simpa [u, v] using h
    · -- `u v → 0` at `∞`
      have hb : Tendsto (fun t : ℝ => Real.exp (-(z.re * t)) / ‖z‖) atTop (𝓝 0) := by
        have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
          (tendsto_id.const_mul_atTop hz)).div_const ‖z‖
        simpa [Function.comp_def] using this
      refine squeeze_zero_norm' ?_ hb
      filter_upwards [eventually_ge_atTop 0] with t ht
      simp only [Pi.mul_apply, u, v, norm_mul, norm_div, norm_neg, norm_exp_neg_mul_ofReal]
      have h1 := norm_one_sub_exp_pow_le ht (k + 1)
      have h2 : 0 ≤ Real.exp (-(z.re * t)) := (Real.exp_pos _).le
      rw [mul_div_assoc']
      refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
      have := mul_le_mul_of_nonneg_right h1 h2
      linarith

/-! ### 6.10.1 -/

/-- `eᶻ E₁(z) = ∫_0^∞ e^{−zt}/(1 + t) dt`, `ℜz > 0` (FTC along the line `z(1 + t)`). -/
theorem exp_mul_E1_eq_integral {z : ℂ} (hz : 0 < z.re) :
    ∫ t in Ioi (0 : ℝ), cexp (-(z * t)) / (t + 1) = cexp z * expIntE₁ z := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hline : ∀ t : ℝ, 0 ≤ t → z * t + z ∈ slitPlane := fun t ht =>
    mem_slitPlane_of_re_pos (by simp; nlinarith)
  have hlim : Tendsto (fun R : ℝ => expIntE₁ (z * R + z)) atTop (𝓝 0) := by
    have hre : Tendsto (fun R : ℝ => (z * R + z).re) atTop atTop := by
      simp only [add_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
      exact tendsto_atTop_add_const_right _ _ (tendsto_id.const_mul_atTop hz)
    refine tendsto_expIntE₁_zero ((eventually_ge_atTop 0).mono fun R hR => hline R hR)
      (r₀ := 0) ((eventually_ge_atTop 0).mono fun R hR => ?_)
      (tendsto_atTop_mono (fun R => le_max_right _ _) hre)
    simp; nlinarith
  have h := tendsto_integral_of_lineE1 z z 0 (f := fun t : ℝ => cexp (-(z * t)) / (t + 1))
    (fun t ht => by
      have hne : (t : ℂ) + 1 ≠ 0 := fun h0 => by
        have := congrArg Complex.re h0; simp at this; linarith
      rw [show z * (t : ℂ) + z = z * (t + 1) by ring, div_eq_of_line hz0 hne])
    hline hlim
  simp only [ofReal_zero, mul_zero, zero_add] at h
  refine integral_Ioi_eq_of_tendsto ?_ h
  refine (exp_neg_integrableOn_Ioi 0 hz).mono' (ContinuousOn.aestronglyMeasurable
    (fun t (ht : 0 < t) => ?_) measurableSet_Ioi)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t (ht : 0 < t) => ?_))
  · have hne : (t : ℂ) + 1 ≠ 0 := fun h0 => by
      have := congrArg Complex.re h0; simp at this; linarith
    exact ((by fun_prop : Continuous fun t : ℝ => cexp (-(z * t))).continuousAt.div
      (by fun_prop : Continuous fun t : ℝ => (t : ℂ) + 1).continuousAt hne).continuousWithinAt
  · rw [norm_div, norm_exp_neg_mul_ofReal, neg_mul]
    have : 1 ≤ ‖(t : ℂ) + 1‖ := by
      have := re_le_norm ((t : ℂ) + 1); simp at this; linarith
    exact div_le_self (Real.exp_pos _).le this

/-- **DLMF 6.10.1**: `E₁(z) = e^{−z} ∑_{k≥0} k! c_k/(z(z+1)⋯(z+k))`, `ℜz > 0` (the partial sums
converge; `c_k` by 6.10.3). -/
theorem dlmf_6_10_1 {z : ℂ} (hz : 0 < z.re) :
    Tendsto (fun n => ∑ k ∈ Finset.range n,
        cexp (-z) * (k ! * e1c k / ∏ i ∈ Finset.range (k + 1), (z + i))) atTop
      (𝓝 (expIntE₁ z)) := by
  -- the partial sums are integrals of `e^{−zt} S_n(t)`
  have hpart : ∀ n, ∑ k ∈ Finset.range n, (k ! * e1c k / ∏ i ∈ Finset.range (k + 1), (z + i))
      = ∫ t in Ioi (0 : ℝ), cexp (-(z * t)) * (e1Sc n t : ℂ) := by
    intro n
    have hint : ∀ k ∈ Finset.range n, Integrable (fun t : ℝ => (e1c k : ℂ) *
        (cexp (-(z * t)) * (((1 - Real.exp (-t)) ^ k : ℝ) : ℂ))) (volume.restrict (Ioi 0)) :=
      fun k _ => (integrableOn_exp_neg_mul_bounded hz (by fun_prop)
        (fun t ht => norm_one_sub_exp_pow_le ht k)).const_mul _
    rw [show (fun t : ℝ => cexp (-(z * t)) * (e1Sc n t : ℂ)) = fun t : ℝ =>
        ∑ k ∈ Finset.range n, (e1c k : ℂ) * (cexp (-(z * t)) *
          (((1 - Real.exp (-t)) ^ k : ℝ) : ℂ)) by
      funext t; simp only [e1Sc]; push_cast; rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring,
      integral_finsetSum _ hint]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul, show (∫ t in Ioi (0 : ℝ), cexp (-(z * t)) *
      (((1 - Real.exp (-t)) ^ k : ℝ) : ℂ)) = betaJ k z from rfl, betaJ_eq k hz]
    ring
  -- dominated convergence
  have hlim : Tendsto (fun n => ∫ t in Ioi (0 : ℝ), cexp (-(z * t)) * (e1Sc n t : ℂ)) atTop
      (𝓝 (cexp z * expIntE₁ z)) := by
    rw [← exp_mul_E1_eq_integral hz]
    refine tendsto_integral_of_dominated_convergence (fun t => binK * Real.exp (-(z.re * t)))
      (fun n => ?_) (by
        have hb : IntegrableOn (fun t => binK * Real.exp (-z.re * t)) (Ioi 0) :=
          (exp_neg_integrableOn_Ioi 0 hz).const_mul binK
        exact hb.congr_fun (fun t _ => by simp [neg_mul]) measurableSet_Ioi)
      (fun n => (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t (ht : 0 < t) => ?_))
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t (ht : 0 < t) => ?_))
    · exact ((by fun_prop : Continuous fun t : ℝ => cexp (-(z * t))).mul
        (continuous_ofReal.comp (continuous_finsetSum _ fun k _ =>
          continuous_const.mul (by fun_prop)))).aestronglyMeasurable
    · rw [norm_mul, norm_exp_neg_mul_ofReal, norm_real, Real.norm_eq_abs, mul_comm]
      exact mul_le_mul_of_nonneg_right (abs_e1Sc_le n ht.le) (Real.exp_pos _).le
    · have := ((continuous_ofReal.tendsto _).comp (tendsto_e1Sc ht.le)).const_mul
        (cexp (-(z * t)))
      have e : cexp (-(z * t)) * (((1 / (1 + t)) : ℝ) : ℂ) = cexp (-(z * t)) / (t + 1) := by
        rw [div_eq_mul_inv]
        congr 1
        push_cast
        rw [add_comm, one_mul]
      rw [e] at this
      exact this
  have h := hlim.const_mul (cexp (-z))
  have hee : cexp (-z) * (cexp z * expIntE₁ z) = expIntE₁ z := by
    rw [← mul_assoc, ← exp_add, neg_add_cancel, exp_zero, one_mul]
  rw [hee] at h
  refine h.congr fun n => ?_
  rw [← hpart, Finset.mul_sum]

end Azurite.DLMF
