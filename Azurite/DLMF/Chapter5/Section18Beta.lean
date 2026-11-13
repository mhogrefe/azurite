/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section18Gamma

/-!
# DLMF §5.18(iii): the `q`-Beta function

Formalization of <https://dlmf.nist.gov/5.18>, subsection (iii). Throughout `0 < q < 1`.

* 5.18.11: `B_q(a, b) = Γ_q(a) Γ_q(b) / Γ_q(a + b)` (`qBeta`, definition).
* 5.18.12: for `ℜa > 0`, `ℜb > 0`,
  `B_q(a, b) = ∫₀¹ t^{a−1} (tq; q)_∞ / (tq^b; q)_∞ d_q t` (`dlmf_5_18_12`), with Jackson's
  `q`-integral `∫₀^c f(t) d_q t = c(1 − q) ∑_{n≥0} f(cqⁿ) qⁿ` (`jacksonIntegral`); the series
  converges (`hasSum_dlmf_5_18_12`).

The proof evaluates the Jackson sum by the `q`-binomial theorem
`∑ₙ (α; q)ₙ/(q; q)ₙ xⁿ = (αx; q)_∞ / (x; q)_∞` for `|x| < 1` (`hasSum_qBinomial`), proved from
the functional equation `(1 − x) S(x) = (1 − αx) S(qx)` iterated to
`(x; q)_N S(x) = (αx; q)_N S(q^N x)` and `S(q^N x) → S(0) = 1`.
-/

open Complex Filter Topology Finset

namespace Azurite.DLMF

/-- Jackson's `q`-integral `∫₀^c f(t) d_q t = c(1 − q) ∑_{n≥0} f(cqⁿ) qⁿ`. -/
noncomputable def jacksonIntegral (q c : ℝ) (f : ℝ → ℂ) : ℂ :=
  c * (1 - q) * ∑' n : ℕ, f (c * q ^ n) * q ^ n

/-- DLMF 5.18.11: `B_q(a, b) = Γ_q(a) Γ_q(b) / Γ_q(a + b)`. -/
noncomputable def qBeta (q : ℝ) (a b : ℂ) : ℂ := qGamma q a * qGamma q b / qGamma q (a + b)

theorem dlmf_5_18_11 (q : ℝ) (a b : ℂ) :
    qBeta q a b = qGamma q a * qGamma q b / qGamma q (a + b) := rfl

/-- The integrand `t^{a−1} (tq; q)_∞ / (tq^b; q)_∞` of 5.18.12. -/
noncomputable def qBetaIntegrand (q : ℝ) (a b : ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (a - 1) * qPochhammerInf (t * q) q / qPochhammerInf (t * (q : ℂ) ^ b) q

/-- `(a; q)_∞ = (a; q)ₙ (aqⁿ; q)_∞`. -/
theorem qPochhammerInf_eq_mul {a q : ℂ} (hq : ‖q‖ < 1) (n : ℕ) :
    qPochhammerInf a q = qPochhammer a q n * qPochhammerInf (a * q ^ n) q := by
  have hm : Multipliable fun i : ℕ => 1 - a * q ^ (i + n) := by
    refine (multipliable_qPochhammer (a := a * q ^ n) hq).congr fun i => ?_
    rw [pow_add]; ring
  have h := Multipliable.prod_mul_tprod_nat_mul' (f := fun i : ℕ => 1 - a * q ^ i) (k := n) hm
  rw [qPochhammerInf, ← h, qPochhammer, qPochhammerInf]
  refine congrArg _ (tprod_congr fun i => ?_)
  rw [pow_add]; ring

/-- The `q`-binomial coefficient `(α; q)ₙ / (q; q)ₙ`. -/
noncomputable def qBinomCoeff (α : ℂ) (q : ℝ) (n : ℕ) : ℂ := qPochhammer α q n / qPochhammer q q n

section QBinomial

variable {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
include hq0 hq1

theorem norm_one_sub_mul_pow (k : ℕ) : ‖(1 : ℂ) - q * (q : ℂ) ^ k‖ = 1 - q ^ (k + 1) := by
  have e : (1 : ℂ) - q * (q : ℂ) ^ k = ((1 - q ^ (k + 1) : ℝ) : ℂ) := by push_cast; ring
  rw [e, Complex.norm_real, Real.norm_of_nonneg]
  exact sub_nonneg.2 (pow_le_one₀ hq0.le hq1.le)

theorem qPochhammer_self_ne_zero (n : ℕ) : qPochhammer q q n ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun k _ h => ?_
  have := norm_one_sub_mul_pow hq0 hq1 k
  rw [h, norm_zero] at this
  have : q ^ (k + 1) < 1 := pow_lt_one₀ hq0.le hq1 (by omega)
  linarith

theorem qBinomCoeff_succ (α : ℂ) (n : ℕ) :
    qBinomCoeff α q (n + 1) * (1 - (q : ℂ) ^ (n + 1)) = qBinomCoeff α q n * (1 - α * q ^ n) := by
  have h1 := qPochhammer_self_ne_zero hq0 hq1 n
  have h2 : (1 : ℂ) - (q : ℂ) ^ (n + 1) ≠ 0 := by
    have := qPochhammer_self_ne_zero hq0 hq1 (n + 1)
    rw [qPochhammer_succ] at this
    rw [pow_succ']; exact right_ne_zero_of_mul this
  rw [qBinomCoeff, qBinomCoeff, qPochhammer_succ, qPochhammer_succ, ← pow_succ']
  field_simp

/-- A uniform bound `‖(α; q)ₙ/(q; q)ₙ‖ ≤ M`. -/
theorem exists_norm_qBinomCoeff_le (α : ℂ) : ∃ M, 0 ≤ M ∧ ∀ n, ‖qBinomCoeff α q n‖ ≤ M := by
  -- lower bound for `(q; q)ₙ`
  have hpos : ∀ k : ℕ, 0 < 1 - q ^ (k + 1) := fun k =>
    sub_pos.2 (pow_lt_one₀ hq0.le hq1 (by omega))
  have hP := Real.hasProd_of_hasSum_log hpos (summable_log_one_sub_pow_succ hq0 hq1).hasSum
  set L := Real.exp (∑' k : ℕ, Real.log (1 - q ^ (k + 1))) with hL
  have hL0 : 0 < L := Real.exp_pos _
  have hanti : Antitone fun n => ∏ k ∈ range n, (1 - q ^ (k + 1)) := by
    refine antitone_nat_of_succ_le fun n => ?_
    rw [Finset.prod_range_succ]
    refine mul_le_of_le_one_right (Finset.prod_nonneg fun k _ => (hpos k).le) ?_
    have := pow_pos hq0 (n + 1); linarith
  have hlow : ∀ n, L ≤ ∏ k ∈ range n, (1 - q ^ (k + 1)) := hanti.le_of_tendsto hP.tendsto_prod_nat
  -- upper bound for `(α; q)ₙ`
  set U := Real.exp (‖α‖ / (1 - q)) with hU
  have hup : ∀ n, ‖qPochhammer α q n‖ ≤ U := by
    intro n
    calc ‖qPochhammer α q n‖ ≤ ∏ k ∈ range n, ‖(1 : ℂ) - α * (q : ℂ) ^ k‖ :=
          Finset.norm_prod_le _ _
      _ ≤ ∏ k ∈ range n, Real.exp (‖α‖ * q ^ k) := by
          refine Finset.prod_le_prod₀ (fun k _ => norm_nonneg _) fun k _ => ?_
          refine (norm_sub_le _ _).trans ?_
          rw [norm_one, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hq0.le,
            add_comm]
          exact Real.add_one_le_exp _
      _ = Real.exp (‖α‖ * ∑ k ∈ range n, q ^ k) := by
          rw [← Real.exp_sum, Finset.mul_sum]
      _ ≤ U := by
          rw [hU]
          refine Real.exp_le_exp.2 ?_
          rw [div_eq_mul_inv]
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          rw [← tsum_geometric_of_lt_one hq0.le hq1]
          exact (summable_geometric_of_lt_one hq0.le hq1).sum_le_tsum _
            (fun k _ => (pow_pos hq0 k).le)
  refine ⟨U / L, by positivity, fun n => ?_⟩
  have hden : ‖qPochhammer (q : ℂ) q n‖ = ∏ k ∈ range n, (1 - q ^ (k + 1)) := by
    rw [qPochhammer, norm_prod]
    exact Finset.prod_congr rfl fun k _ => norm_one_sub_mul_pow hq0 hq1 k
  rw [qBinomCoeff, norm_div, hden]
  have hd0 : 0 < ∏ k ∈ range n, (1 - q ^ (k + 1)) := Finset.prod_pos fun k _ => hpos k
  rw [div_le_div_iff₀ hd0 hL0]
  calc ‖qPochhammer α q n‖ * L ≤ U * L := by gcongr; exact hup n
    _ ≤ U * ∏ k ∈ range n, (1 - q ^ (k + 1)) := by gcongr; exact hlow n

theorem summable_qBinom (α : ℂ) {x : ℂ} (hx : ‖x‖ < 1) :
    Summable fun n => qBinomCoeff α q n * x ^ n := by
  obtain ⟨M, hM0, hM⟩ := exists_norm_qBinomCoeff_le hq0 hq1 α
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one (norm_nonneg x) hx).mul_left M)
    fun n => ?_
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_right (hM n) (by positivity)

theorem norm_ofReal_mul_lt {x : ℂ} (hx : ‖x‖ < 1) : ‖(q : ℂ) * x‖ < 1 := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hq0.le]
  nlinarith [norm_nonneg x]

/-- The functional equation `(1 − x) S(x) = (1 − αx) S(qx)`. -/
theorem qBinom_functional (α : ℂ) {x : ℂ} (hx : ‖x‖ < 1) :
    (1 - x) * ∑' n, qBinomCoeff α q n * x ^ n =
      (1 - α * x) * ∑' n, qBinomCoeff α q n * ((q : ℂ) * x) ^ n := by
  set c := qBinomCoeff α q
  have hs1 := summable_qBinom hq0 hq1 α hx
  have hs2 := summable_qBinom hq0 hq1 α (norm_ofReal_mul_lt hq0 hq1 hx)
  set g : ℕ → ℂ := fun n => c n * x ^ n - c n * ((q : ℂ) * x) ^ n with hg
  have hgs : Summable g := hs1.sub hs2
  have hg' : ∀ n, g (n + 1) = x * (c n * x ^ n) - α * x * (c n * ((q : ℂ) * x) ^ n) := by
    intro n
    have h := qBinomCoeff_succ hq0 hq1 α n
    simp only [hg, mul_pow]
    linear_combination x ^ (n + 1) * h
  have e1 : ∑' n, g n = (∑' n, c n * x ^ n) - ∑' n, c n * ((q : ℂ) * x) ^ n := hs1.tsum_sub hs2
  have e2 : ∑' n, g n = g 0 + ∑' n, g (n + 1) := hgs.tsum_eq_zero_add
  have e3 : ∑' n, g (n + 1) =
      x * (∑' n, c n * x ^ n) - α * x * ∑' n, c n * ((q : ℂ) * x) ^ n := by
    simp_rw [hg']
    rw [(hs1.mul_left x).tsum_sub (hs2.mul_left (α * x)), tsum_mul_left, tsum_mul_left]
  have e0 : g 0 = 0 := by simp [hg]
  rw [e2, e0, zero_add, e3] at e1
  linear_combination -e1

/-- `‖S(y) − 1‖ ≤ M‖y‖/(1 − ‖x‖)` for `‖y‖ ≤ ‖x‖ < 1`. -/
theorem tendsto_qBinom_zero (α : ℂ) {x : ℂ} (hx : ‖x‖ < 1) :
    Tendsto (fun N : ℕ => ∑' n, qBinomCoeff α q n * ((q : ℂ) ^ N * x) ^ n) atTop (𝓝 1) := by
  obtain ⟨M, hM0, hM⟩ := exists_norm_qBinomCoeff_le hq0 hq1 α
  set c := qBinomCoeff α q
  have hy : ∀ N : ℕ, ‖(q : ℂ) ^ N * x‖ ≤ ‖x‖ := by
    intro N
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hq0.le]
    exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hq0.le hq1.le)
  have hb : ∀ N : ℕ, ‖(∑' n, c n * ((q : ℂ) ^ N * x) ^ n) - 1‖ ≤
      M / (1 - ‖x‖) * ‖(q : ℂ) ^ N * x‖ := by
    intro N
    set y := (q : ℂ) ^ N * x
    have hy1 : ‖y‖ < 1 := (hy N).trans_lt hx
    have hs := summable_qBinom hq0 hq1 α hy1
    have hc0 : qBinomCoeff α q 0 = 1 := by simp [qBinomCoeff]
    have h1 : HasSum (fun n => c (n + 1) * y ^ (n + 1)) ((∑' n, c n * y ^ n) - 1) := by
      rw [hs.tsum_eq_zero_add, hc0, pow_zero, mul_one, add_sub_cancel_left]
      exact ((summable_nat_add_iff 1).2 hs).hasSum
    have h2 : HasSum (fun n : ℕ => M * ‖y‖ * ‖y‖ ^ n) (M * ‖y‖ * (1 - ‖y‖)⁻¹) :=
      (hasSum_geometric_of_lt_one (norm_nonneg _) hy1).mul_left _
    refine (h1.norm_le_of_bounded h2 fun n => ?_).trans ?_
    · rw [norm_mul, norm_pow, pow_succ]
      calc ‖c (n + 1)‖ * (‖y‖ ^ n * ‖y‖) ≤ M * (‖y‖ ^ n * ‖y‖) := by gcongr; exact hM _
        _ = M * ‖y‖ * ‖y‖ ^ n := by ring
    · have h3 : 0 < 1 - ‖x‖ := by linarith
      have h4 : 1 - ‖x‖ ≤ 1 - ‖y‖ := by linarith [hy N]
      rw [div_mul_eq_mul_div, ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_left (by positivity) h3 h4
  have hz : Tendsto (fun N : ℕ => M / (1 - ‖x‖) * ‖(q : ℂ) ^ N * x‖) atTop (𝓝 0) := by
    have : Tendsto (fun N : ℕ => (q : ℂ) ^ N * x) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one
        (norm_ofReal_lt_one_of_pos hq0 hq1)).mul_const x
    simpa using this.norm.const_mul (M / (1 - ‖x‖))
  exact tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _) hb hz)

/-- `(x; q)_N S(x) = (αx; q)_N S(q^N x)`. -/
theorem qBinom_iterate (α : ℂ) {x : ℂ} (hx : ‖x‖ < 1) (N : ℕ) :
    qPochhammer x q N * ∑' n, qBinomCoeff α q n * x ^ n =
      qPochhammer (α * x) q N * ∑' n, qBinomCoeff α q n * ((q : ℂ) ^ N * x) ^ n := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hxN : ‖(q : ℂ) ^ N * x‖ < 1 := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hq0.le]
      exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hq0.le hq1.le)).trans_lt hx
    have hf := qBinom_functional hq0 hq1 α hxN
    rw [show (q : ℂ) * ((q : ℂ) ^ N * x) = (q : ℂ) ^ (N + 1) * x by ring] at hf
    rw [qPochhammer_succ, qPochhammer_succ, mul_right_comm, ih]
    linear_combination qPochhammer (α * x) q N * hf

/-- The `q`-binomial theorem: `∑ₙ (α; q)ₙ/(q; q)ₙ xⁿ = (αx; q)_∞/(x; q)_∞` for `|x| < 1`. -/
theorem hasSum_qBinomial (α : ℂ) {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun n => qBinomCoeff α q n * x ^ n)
      (qPochhammerInf (α * x) q / qPochhammerInf x q) := by
  have hqn := norm_ofReal_lt_one_of_pos hq0 hq1
  have hne : qPochhammerInf x q ≠ 0 := by
    refine qPochhammerInf_ne_zero hqn fun k h => ?_
    have : ‖x * (q : ℂ) ^ k‖ < 1 := by
      rw [norm_mul, norm_pow]
      exact (mul_le_of_le_one_right (norm_nonneg _)
        (pow_le_one₀ (norm_nonneg _) hqn.le)).trans_lt hx
    rw [← sub_eq_zero.1 h, norm_one] at this
    exact lt_irrefl _ this
  have hl := ((dlmf_5_18_3 (a := x) hqn).2.mul_const (∑' n, qBinomCoeff α q n * x ^ n))
  have hr := (dlmf_5_18_3 (a := α * x) hqn).2.mul (tendsto_qBinom_zero hq0 hq1 α hx)
  rw [mul_one] at hr
  have heq := tendsto_nhds_unique hl (hr.congr fun N => (qBinom_iterate hq0 hq1 α hx N).symm)
  rw [← heq, mul_div_cancel_left₀ _ hne]
  exact (summable_qBinom hq0 hq1 α hx).hasSum

end QBinomial

/-! ### 5.18.12 -/

section Integral

variable {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
include hq0 hq1

omit hq1 in
theorem ofReal_pow_nat_cpow (n : ℕ) (s : ℂ) : ((q ^ n : ℝ) : ℂ) ^ s = ((q : ℂ) ^ s) ^ n := by
  have hq : (q : ℂ) ≠ 0 := ofReal_ne_zero.2 hq0.ne'
  have hqn : ((q ^ n : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 (pow_pos hq0 n).ne'
  rw [cpow_def_of_ne_zero hqn, cpow_def_of_ne_zero hq, ← Complex.exp_nat_mul,
    ← ofReal_log (pow_pos hq0 n).le, Real.log_pow, ← ofReal_log hq0.le]
  push_cast; ring_nf

theorem norm_cpow_lt_one {s : ℂ} (hs : 0 < s.re) : ‖(q : ℂ) ^ s‖ < 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hq0]
  exact Real.rpow_lt_one hq0.le hq1 hs

theorem qPochhammerInf_cpow_ne_zero {s : ℂ} (hs : 0 < s.re) :
    qPochhammerInf ((q : ℂ) ^ s) q ≠ 0 := by
  have hqn := norm_ofReal_lt_one_of_pos hq0 hq1
  refine qPochhammerInf_ne_zero hqn fun k h => ?_
  have : ‖(q : ℂ) ^ s * (q : ℂ) ^ k‖ < 1 := by
    rw [norm_mul, norm_pow]
    exact (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hqn.le)).trans_lt
      (norm_cpow_lt_one hq0 hq1 hs)
  rw [← sub_eq_zero.1 h, norm_one] at this
  exact lt_irrefl _ this

/-- The `n`-th term of the Jackson sum of 5.18.12. -/
theorem qBetaIntegrand_term {a b : ℂ} (hb : 0 < b.re) (n : ℕ) :
    qBetaIntegrand q a b (1 * q ^ n) * (q : ℂ) ^ n =
      qPochhammerInf q q / qPochhammerInf ((q : ℂ) ^ b) q *
        (qBinomCoeff ((q : ℂ) ^ b) q n * ((q : ℂ) ^ a) ^ n) := by
  have hqn := norm_ofReal_lt_one_of_pos hq0 hq1
  have hq : (q : ℂ) ≠ 0 := ofReal_ne_zero.2 hq0.ne'
  have hA := qPochhammerInf_eq_mul (a := (q : ℂ)) hqn n
  have hB := qPochhammerInf_eq_mul (a := (q : ℂ) ^ b) hqn n
  have hBne := qPochhammerInf_cpow_ne_zero hq0 hq1 hb
  rw [hB] at hBne
  have hPb : qPochhammer ((q : ℂ) ^ b) q n ≠ 0 := left_ne_zero_of_mul hBne
  have hTb : qPochhammerInf ((q : ℂ) ^ b * (q : ℂ) ^ n) q ≠ 0 := right_ne_zero_of_mul hBne
  have hPq := qPochhammer_self_ne_zero hq0 hq1 n
  have hpow : ((q ^ n : ℝ) : ℂ) ^ (a - 1) * (q : ℂ) ^ n = ((q : ℂ) ^ a) ^ n := by
    rw [ofReal_pow_nat_cpow hq0, ← mul_pow, cpow_sub _ _ hq, cpow_one, div_mul_cancel₀ _ hq]
  have e1 : qPochhammerInf (((q ^ n : ℝ) : ℂ) * q) q =
      qPochhammerInf ((q : ℂ) * (q : ℂ) ^ n) q := by
    congr 1; push_cast; ring
  have e2 : qPochhammerInf (((q ^ n : ℝ) : ℂ) * (q : ℂ) ^ b) q =
      qPochhammerInf ((q : ℂ) ^ b * (q : ℂ) ^ n) q := by
    congr 1; push_cast; ring
  rw [qBetaIntegrand, one_mul, e1, e2, hA, hB, qBinomCoeff]
  rw [show ((q ^ n : ℝ) : ℂ) ^ (a - 1) * qPochhammerInf ((q : ℂ) * (q : ℂ) ^ n) q /
      qPochhammerInf ((q : ℂ) ^ b * (q : ℂ) ^ n) q * (q : ℂ) ^ n =
      (((q ^ n : ℝ) : ℂ) ^ (a - 1) * (q : ℂ) ^ n) * qPochhammerInf ((q : ℂ) * (q : ℂ) ^ n) q /
      qPochhammerInf ((q : ℂ) ^ b * (q : ℂ) ^ n) q by ring, hpow]
  field_simp

/-- The Jackson sum of 5.18.12 converges to `B_q(a, b) / (1 − q)`. -/
theorem hasSum_dlmf_5_18_12 {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    HasSum (fun n : ℕ => qBetaIntegrand q a b (1 * q ^ n) * (q : ℂ) ^ n)
      (qBeta q a b / (1 - q)) := by
  have hq : (q : ℂ) ≠ 0 := ofReal_ne_zero.2 hq0.ne'
  have h1 := one_sub_ofReal_ne_zero hq1
  have hs := (hasSum_qBinomial hq0 hq1 ((q : ℂ) ^ b) (norm_cpow_lt_one hq0 hq1 ha)).mul_left
    (qPochhammerInf q q / qPochhammerInf ((q : ℂ) ^ b) q)
  convert hs using 1
  · funext n; exact qBetaIntegrand_term hq0 hq1 hb n
  · have hA := qPochhammerInf_self_ne_zero hq0 hq1
    have hBa := qPochhammerInf_cpow_ne_zero hq0 hq1 ha
    have hBb := qPochhammerInf_cpow_ne_zero hq0 hq1 hb
    have hab : 0 < (a + b).re := by simp; linarith
    have hBab := qPochhammerInf_cpow_ne_zero hq0 hq1 hab
    have hpab : (q : ℂ) ^ (a + b) = (q : ℂ) ^ b * (q : ℂ) ^ a := by
      rw [cpow_add _ _ hq, mul_comm]
    have h1' : ((1 - q : ℝ) : ℂ) ≠ 0 := by push_cast; exact h1
    have hc : ((1 - q : ℝ) : ℂ) ^ (1 - a) * ((1 - q : ℝ) : ℂ) ^ (1 - b) =
        ((1 - q : ℝ) : ℂ) ^ (1 - (a + b)) * (1 - q) := by
      rw [← cpow_add _ _ h1', show 1 - a + (1 - b) = 1 - (a + b) + 1 by ring,
        cpow_add _ _ h1', cpow_one]
      push_cast; ring
    have hcne : ((1 - q : ℝ) : ℂ) ^ (1 - (a + b)) ≠ 0 := by
      rw [cpow_def_of_ne_zero h1']; exact Complex.exp_ne_zero _
    rw [qBeta, qGamma, qGamma, qGamma, ← hpab]
    rw [show qPochhammerInf q q * ((1 - q : ℝ) : ℂ) ^ (1 - a) / qPochhammerInf ((q : ℂ) ^ a) q *
        (qPochhammerInf q q * ((1 - q : ℝ) : ℂ) ^ (1 - b) / qPochhammerInf ((q : ℂ) ^ b) q) =
        qPochhammerInf q q * qPochhammerInf q q *
          (((1 - q : ℝ) : ℂ) ^ (1 - a) * ((1 - q : ℝ) : ℂ) ^ (1 - b)) /
          (qPochhammerInf ((q : ℂ) ^ a) q * qPochhammerInf ((q : ℂ) ^ b) q) by ring, hc]
    field_simp

/-- DLMF 5.18.12: `B_q(a, b) = ∫₀¹ t^{a−1} (tq; q)_∞ / (tq^b; q)_∞ d_q t` for `0 < q < 1`,
`ℜa > 0`, `ℜb > 0`. -/
theorem dlmf_5_18_12 {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    qBeta q a b = jacksonIntegral q 1 (qBetaIntegrand q a b) := by
  rw [jacksonIntegral, (hasSum_dlmf_5_18_12 hq0 hq1 ha hb).tsum_eq, ofReal_one, one_mul,
    mul_div_cancel₀ _ (one_sub_ofReal_ne_zero hq1)]

end Integral

end Azurite.DLMF
