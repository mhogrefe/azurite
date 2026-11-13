/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section18Gamma
import Azurite.DLMF.Chapter5.Section16
import Azurite.DLMF.Chapter2.Section5Laplace
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# DLMF 5.18.10: `lim_{q→1⁻} Γ_q(z) = Γ(z)`

Formalization of <https://dlmf.nist.gov/5.18.E10> (`dlmf_5_18_10`, for every `z ∈ ℂ`; at the
poles `z = −n` both sides are `0` in Lean).

Write `q = e^{−h}` and `F_h(t) = Ln(1 − e^{−ht})` (`qLogF`). For `ℜz ≥ 1`,
`Γ_q(z) = exp ∑_k L_k(h)` with
`L_k(h) = F_h(k + 1) − F_h(k + z) + (1 − z)(F_h(k + 1) − F_h(k + 2))` (`qLogTerm`): the partial
sums exponentiate to `(q; q)ₙ / (q^z; q)ₙ · ((1 − q)/(1 − q^{n+1}))^{1−z}`. Expanding
`F_h(t) = −∑_m e^{−hmt}/m` gives `L_k(h) = −∑_m e^{−hm(k+1)}/m · β(hm)` with
`β(u) = −(e^{−uw} − 1 + uw) − (1 − z)(e^{−u} − 1 + u)`, `w = z − 1`, so
`|L_k(h)| ≤ K h² ρ/(1 − ρ)² ≤ K/(k + 1)²` (`ρ = e^{−h(k+1)}`, using `y² e^{−y} ≤ (1 − e^{−y})²`),
uniformly in `h > 0`. As `h → 0⁺`, `L_k(h) → ln(k + 1) − ln(k + z) + (1 − z)(ln(k + 1) −
ln(k + 2))` (`gammaLogTerm`), whose sum exponentiates to `Γ(z)` by Euler's limit. Tannery's theorem
finishes `ℜz ≥ 1`; the recurrence 5.18.7 and `(1 − q^{z+k})/(1 − q) → z + k` give all `z`.
-/

open Complex Filter Topology Finset

namespace Azurite.DLMF

/-- `F_h(t) = Ln(1 − e^{−ht})`. -/
noncomputable def qLogF (h : ℝ) (t : ℂ) : ℂ := Complex.log (1 - cexp (-(h * t)))

/-- `L_k(h) = F_h(k + 1) − F_h(k + z) + (1 − z)(F_h(k + 1) − F_h(k + 2))`. -/
noncomputable def qLogTerm (h : ℝ) (z : ℂ) (k : ℕ) : ℂ :=
  qLogF h (k + 1) - qLogF h (k + z) + (1 - z) * (qLogF h (k + 1) - qLogF h (k + 2))

/-- `ℓ_k = ln(k + 1) − ln(k + z) + (1 − z)(ln(k + 1) − ln(k + 2))`. -/
noncomputable def gammaLogTerm (z : ℂ) (k : ℕ) : ℂ :=
  Complex.log (k + 1) - Complex.log (k + z) +
    (1 - z) * (Complex.log (k + 1) - Complex.log (k + 2))

theorem norm_cexp_neg_ofReal_mul_cplx (h : ℝ) (t : ℂ) :
    ‖cexp (-(h * t))‖ = Real.exp (-(h * t.re)) := by
  rw [Complex.norm_exp]; simp

theorem norm_cexp_neg_ofReal_mul_lt_one {h : ℝ} (hh : 0 < h) {t : ℂ} (ht : 0 < t.re) :
    ‖cexp (-(h * t))‖ < 1 := by
  rw [norm_cexp_neg_ofReal_mul_cplx]; exact Real.exp_lt_one_iff.2 (by nlinarith)

theorem one_sub_cexp_ne_zero {h : ℝ} (hh : 0 < h) {t : ℂ} (ht : 0 < t.re) :
    1 - cexp (-(h * t)) ≠ 0 := by
  intro h0
  have := norm_cexp_neg_ofReal_mul_lt_one hh ht
  rw [← sub_eq_zero.1 h0, norm_one] at this
  exact lt_irrefl _ this

theorem hasSum_qLogF {h : ℝ} (hh : 0 < h) {t : ℂ} (ht : 0 < t.re) :
    HasSum (fun m : ℕ => -(cexp (-(h * t)) ^ m / m)) (qLogF h t) := by
  simpa [qLogF] using (Complex.hasSum_taylorSeries_neg_log
    (norm_cexp_neg_ofReal_mul_lt_one hh ht)).neg

/-- `|e^x − 1 − x| ≤ 3|x|²` for `ℜx ≤ 0`. -/
theorem norm_exp_sub_one_sub_le_of_re_nonpos {x : ℂ} (hx : x.re ≤ 0) :
    ‖cexp x - 1 - x‖ ≤ 3 * ‖x‖ ^ 2 := by
  by_cases h1 : ‖x‖ ≤ 1
  · have := Complex.norm_exp_sub_one_sub_id_le h1
    nlinarith [sq_nonneg ‖x‖]
  · push Not at h1
    have he : ‖cexp x‖ ≤ 1 := by rw [Complex.norm_exp]; exact Real.exp_le_one_iff.2 hx
    calc ‖cexp x - 1 - x‖ ≤ ‖cexp x‖ + ‖(1 : ℂ)‖ + ‖x‖ := by
          refine (norm_sub_le _ _).trans ?_
          gcongr
          exact norm_sub_le _ _
      _ ≤ 3 * ‖x‖ ^ 2 := by rw [norm_one]; nlinarith

/-- `y² e^{−y} ≤ (1 − e^{−y})²` for `y ≥ 0`. -/
theorem sq_mul_exp_neg_le {y : ℝ} (hy : 0 ≤ y) :
    y ^ 2 * Real.exp (-y) ≤ (1 - Real.exp (-y)) ^ 2 := by
  set e := Real.exp (-(y / 2)) with he
  have he0 : 0 < e := Real.exp_pos _
  have hs : y ≤ 2 * Real.sinh (y / 2) := by
    have := Real.self_le_sinh_iff.2 (by linarith : 0 ≤ y / 2); linarith
  have hsinh : Real.sinh (y / 2) = (e⁻¹ - e) / 2 := by
    rw [Real.sinh_eq, he, Real.exp_neg, inv_inv]
  have hey : Real.exp (-y) = e ^ 2 := by
    rw [he, ← Real.exp_nat_mul]; ring_nf
  have hid : 1 - Real.exp (-y) = e * (2 * Real.sinh (y / 2)) := by
    rw [hey, hsinh]; field_simp
  rw [hid, hey, mul_pow, mul_comm]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy hs 2) (by positivity)

section Bound

variable {h : ℝ} (hh : 0 < h) {z : ℂ} (hz : 1 ≤ z.re)
include hh hz

/-- The series of `L_k(h)`. -/
theorem hasSum_qLogTerm (k : ℕ) :
    HasSum (fun m : ℕ => -(cexp (-(h * (k + 1))) ^ m / m) *
      ((1 - cexp (-(h * (z - 1))) ^ m) + (1 - z) * (1 - cexp (-(h : ℂ)) ^ m)))
      (qLogTerm h z k) := by
  have r1 : 0 < ((k : ℂ) + 1).re := by simp; positivity
  have r2 : 0 < ((k : ℂ) + z).re := by simp; linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
  have r3 : 0 < ((k : ℂ) + 2).re := by simp; positivity
  have H := ((hasSum_qLogF hh r1).sub (hasSum_qLogF hh r2)).add
    (((hasSum_qLogF hh r1).sub (hasSum_qLogF hh r3)).mul_left (1 - z))
  have hb : cexp (-(h * ((k : ℂ) + z))) = cexp (-(h * (k + 1))) * cexp (-(h * (z - 1))) := by
    rw [← Complex.exp_add]; ring_nf
  have hc : cexp (-(h * ((k : ℂ) + 2))) = cexp (-(h * (k + 1))) * cexp (-(h : ℂ)) := by
    rw [← Complex.exp_add]; ring_nf
  convert H using 1
  funext m
  rw [hb, hc, mul_pow, mul_pow]
  ring
  rfl

/-- `‖L_k(h)‖ ≤ K h² ρ/(1 − ρ)²` with `ρ = e^{−h(k+1)}`, `K = 3(‖1 − z‖² + ‖1 − z‖)`. -/
theorem norm_qLogTerm_le_geom (k : ℕ) :
    ‖qLogTerm h z k‖ ≤ 3 * (‖1 - z‖ ^ 2 + ‖1 - z‖) * h ^ 2 *
      (Real.exp (-(h * (k + 1))) / (1 - Real.exp (-(h * (k + 1)))) ^ 2) := by
  set ρ := Real.exp (-(h * (k + 1))) with hρ
  set K := 3 * (‖1 - z‖ ^ 2 + ‖1 - z‖) with hK
  have hρ0 : 0 ≤ ρ := (Real.exp_pos _).le
  have hρ1 : ‖ρ‖ < 1 := by
    rw [Real.norm_of_nonneg hρ0]
    exact Real.exp_lt_one_iff.2 (by nlinarith [k.cast_nonneg (α := ℝ)])
  have hg := (hasSum_coe_mul_geometric_of_norm_lt_one hρ1).mul_left (K * h ^ 2)
  refine (hasSum_qLogTerm hh hz k).norm_le_of_bounded hg fun m => ?_
  have hna : ‖cexp (-(h * ((k : ℂ) + 1)))‖ = ρ := by
    rw [norm_cexp_neg_ofReal_mul_cplx]; simp [hρ]
  -- the bracket
  set x1 : ℂ := (m : ℂ) * (-(h * (z - 1))) with hx1
  set x2 : ℂ := (m : ℂ) * (-(h : ℂ)) with hx2
  have hd : cexp (-(h * (z - 1))) ^ m = cexp x1 := by rw [hx1, Complex.exp_nat_mul]
  have he : cexp (-(h : ℂ)) ^ m = cexp x2 := by rw [hx2, Complex.exp_nat_mul]
  have hx1re : x1.re ≤ 0 := by
    have e : x1.re = -((m : ℝ) * h * (z.re - 1)) := by simp [hx1]; ring
    have : 0 ≤ z.re - 1 := by linarith
    have := mul_nonneg (mul_nonneg m.cast_nonneg hh.le) this
    linarith
  have hx2re : x2.re ≤ 0 := by
    have e : x2.re = -((m : ℝ) * h) := by simp [hx2]
    have := mul_nonneg m.cast_nonneg hh.le
    linarith
  have hnx1 : ‖x1‖ = m * h * ‖1 - z‖ := by
    rw [hx1, norm_mul, norm_neg, norm_mul, Complex.norm_natCast, Complex.norm_real,
      Real.norm_of_nonneg hh.le, ← norm_neg (z - 1), neg_sub]; ring
  have hnx2 : ‖x2‖ = m * h := by
    rw [hx2, norm_mul, norm_neg, Complex.norm_natCast, Complex.norm_real,
      Real.norm_of_nonneg hh.le]
  have hβ : (1 - cexp x1) + (1 - z) * (1 - cexp x2) =
      -(cexp x1 - 1 - x1) - (1 - z) * (cexp x2 - 1 - x2) := by
    rw [hx1, hx2]; ring
  have hβn : ‖(1 - cexp x1) + (1 - z) * (1 - cexp x2)‖ ≤ K * (m * h) ^ 2 := by
    rw [hβ]
    have b1 := norm_exp_sub_one_sub_le_of_re_nonpos hx1re
    have b2 := norm_exp_sub_one_sub_le_of_re_nonpos hx2re
    calc ‖-(cexp x1 - 1 - x1) - (1 - z) * (cexp x2 - 1 - x2)‖
        ≤ ‖cexp x1 - 1 - x1‖ + ‖1 - z‖ * ‖cexp x2 - 1 - x2‖ := by
          refine (norm_sub_le _ _).trans ?_; rw [norm_neg, norm_mul]
      _ ≤ 3 * ‖x1‖ ^ 2 + ‖1 - z‖ * (3 * ‖x2‖ ^ 2) := by
          gcongr
      _ = K * (m * h) ^ 2 := by rw [hnx1, hnx2, hK]; ring
  rw [hd, he]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    rw [norm_mul, norm_neg, norm_div, norm_pow, hna, Complex.norm_natCast]
    calc ρ ^ m / m * ‖(1 - cexp x1) + (1 - z) * (1 - cexp x2)‖
        ≤ ρ ^ m / m * (K * (m * h) ^ 2) := by gcongr
      _ = K * h ^ 2 * (m * ρ ^ m) := by field_simp

/-- `‖L_k(h)‖ ≤ K/(k + 1)²`, uniformly in `h > 0`. -/
theorem norm_qLogTerm_le (k : ℕ) :
    ‖qLogTerm h z k‖ ≤ 3 * (‖1 - z‖ ^ 2 + ‖1 - z‖) / ((k : ℝ) + 1) ^ 2 := by
  refine (norm_qLogTerm_le_geom hh hz k).trans ?_
  set y := h * ((k : ℝ) + 1) with hy
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hy0 : 0 < y := by positivity
  have hρ1 : Real.exp (-y) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hd : 0 < (1 - Real.exp (-y)) ^ 2 := by
    have : 0 < 1 - Real.exp (-y) := by linarith
    positivity
  have key := sq_mul_exp_neg_le hy0.le
  have hK : 0 ≤ 3 * (‖1 - z‖ ^ 2 + ‖1 - z‖) := by positivity
  have hh2 : h ^ 2 = y ^ 2 / ((k : ℝ) + 1) ^ 2 := by rw [hy]; field_simp
  rw [hh2, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
  have : y ^ 2 / ((k : ℝ) + 1) ^ 2 * Real.exp (-y) * ((k : ℝ) + 1) ^ 2 ≤
      (1 - Real.exp (-y)) ^ 2 := by
    rw [div_mul_eq_mul_div, div_mul_cancel₀ _ (by positivity)]; exact key
  calc 3 * (‖1 - z‖ ^ 2 + ‖1 - z‖) * (y ^ 2 / ((k : ℝ) + 1) ^ 2) * Real.exp (-y) *
        ((k : ℝ) + 1) ^ 2
      = 3 * (‖1 - z‖ ^ 2 + ‖1 - z‖) *
        (y ^ 2 / ((k : ℝ) + 1) ^ 2 * Real.exp (-y) * ((k : ℝ) + 1) ^ 2) := by ring
    _ ≤ 3 * (‖1 - z‖ ^ 2 + ‖1 - z‖) * (1 - Real.exp (-y)) ^ 2 := by gcongr

end Bound

/-! ### Pointwise limits as `h → 0⁺` -/

theorem tendsto_div_one_sub_cexp (t : ℂ) :
    Tendsto (fun h : ℝ => (1 - cexp (-(h * t))) / h) (𝓝[>] 0) (𝓝 t) := by
  have hd : HasDerivAt (fun s : ℝ => 1 - cexp (-((s : ℂ) * t))) t 0 := by
    have h1 : HasDerivAt (fun s : ℂ => 1 - cexp (-(s * t))) (-(cexp (-((0 : ℂ) * t)) *
        -(1 * t))) ((0 : ℝ) : ℂ) := by
      have := ((hasDerivAt_id ((0 : ℝ) : ℂ)).mul_const t).neg.cexp.const_sub 1
      simpa using this
    have h2 := h1.comp_ofReal
    simpa using h2
  have := hd.tendsto_slope_zero_right
  refine this.congr fun s => ?_
  simp only [zero_add, ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, sub_self, sub_zero,
    Complex.real_smul, ofReal_inv]
  ring

theorem qLogF_sub_eq {h : ℝ} (hh : 0 < h) {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    qLogF h a - qLogF h b = Complex.log ((1 - cexp (-(h * a))) / h) -
      Complex.log ((1 - cexp (-(h * b))) / h) := by
  have hh' : (h : ℂ) ≠ 0 := ofReal_ne_zero.2 hh.ne'
  have e : ∀ t : ℂ, 0 < t.re → qLogF h t =
      Real.log h + Complex.log ((1 - cexp (-(h * t))) / h) := by
    intro t ht
    rw [qLogF, ← Complex.log_ofReal_mul hh (div_ne_zero (one_sub_cexp_ne_zero hh ht) hh'),
      mul_div_cancel₀ _ hh']
  rw [e a ha, e b hb]; ring

theorem tendsto_qLogF_sub {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    Tendsto (fun h : ℝ => qLogF h a - qLogF h b) (𝓝[>] 0)
      (𝓝 (Complex.log a - Complex.log b)) := by
  have hla := ((continuousAt_clog (Or.inl ha)).tendsto).comp (tendsto_div_one_sub_cexp a)
  have hlb := ((continuousAt_clog (Or.inl hb)).tendsto).comp (tendsto_div_one_sub_cexp b)
  refine (hla.sub hlb).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact (qLogF_sub_eq hh ha hb).symm

theorem tendsto_qLogTerm {z : ℂ} (hz : 0 < z.re) (k : ℕ) :
    Tendsto (fun h : ℝ => qLogTerm h z k) (𝓝[>] 0) (𝓝 (gammaLogTerm z k)) := by
  have r1 : 0 < ((k : ℂ) + 1).re := by simp; positivity
  have r2 : 0 < ((k : ℂ) + z).re := by simp; linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
  have r3 : 0 < ((k : ℂ) + 2).re := by simp; positivity
  exact (tendsto_qLogF_sub r1 r2).add ((tendsto_qLogF_sub r1 r3).const_mul (1 - z))

/-! ### Exponentiated partial sums -/

theorem cexp_tsum_eq_of_tendsto {L : ℕ → ℂ} (hL : Summable L) {X : ℂ}
    (h : Tendsto (fun n => cexp (∑ k ∈ range n, L k)) atTop (𝓝 X)) : cexp (∑' k, L k) = X :=
  tendsto_nhds_unique ((Complex.continuous_exp.tendsto _).comp hL.hasSum.tendsto_sum_nat) h

/-- Telescoping exponential factor. -/
theorem cexp_sum_mul_sub {f : ℕ → ℂ} (c : ℂ) (n : ℕ) :
    cexp (∑ k ∈ range n, c * (f k - f (k + 1))) = cexp (c * (f 0 - f n)) := by
  rw [← Finset.mul_sum, Finset.sum_range_sub']

theorem exp_sum_qLogTerm {h : ℝ} (hh : 0 < h) {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    cexp (∑ k ∈ range n, qLogTerm h z k) =
      (∏ k ∈ range n, (1 - cexp (-(h * ((k : ℂ) + 1))))) /
        (∏ k ∈ range n, (1 - cexp (-(h * ((k : ℂ) + z))))) *
        cexp ((1 - z) * (qLogF h 1 - qLogF h ((n : ℂ) + 1))) := by
  have hsplit : ∑ k ∈ range n, qLogTerm h z k =
      ∑ k ∈ range n, (qLogF h ((k : ℂ) + 1) - qLogF h ((k : ℂ) + z)) +
        ∑ k ∈ range n, (1 - z) * (qLogF h (((k : ℕ) : ℂ) + 1) -
          qLogF h ((((k + 1 : ℕ)) : ℂ) + 1)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [qLogTerm]; push_cast; ring_nf
  rw [hsplit, Complex.exp_add, cexp_sum_mul_sub (f := fun k : ℕ => qLogF h ((k : ℂ) + 1)),
    Complex.exp_sum, ← Finset.prod_div_distrib]
  simp only [Nat.cast_zero, zero_add]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  have r1 : 0 < ((k : ℂ) + 1).re := by simp; positivity
  have r2 : 0 < ((k : ℂ) + z).re := by simp; linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
  rw [Complex.exp_sub, qLogF, qLogF, Complex.exp_log (one_sub_cexp_ne_zero hh r1),
    Complex.exp_log (one_sub_cexp_ne_zero hh r2)]

section QSide

variable {h : ℝ} (hh : 0 < h) {z : ℂ} (hz : 0 < z.re)
include hh hz

omit hh hz in
theorem cpow_ofReal_exp_neg :
    ((Real.exp (-h) : ℝ) : ℂ) ^ z = cexp (-(h * z)) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.2 (Real.exp_pos _).ne'), ← ofReal_log
    (Real.exp_pos _).le, Real.log_exp]
  push_cast; ring_nf

/-- For `ℜz > 0`, `Γ_{e^{−h}}(z) = exp ∑_k L_k(h)`. -/
theorem qGamma_exp_neg_eq (hsum : Summable (qLogTerm h z)) :
    qGamma (Real.exp (-h)) z = cexp (∑' k, qLogTerm h z k) := by
  set q := Real.exp (-h) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hqn := norm_ofReal_lt_one_of_pos hq0 hq1
  have hqc : (q : ℂ) = cexp (-(h : ℂ)) := by rw [hq, ofReal_exp]; push_cast; ring_nf
  have hqk : ∀ k : ℕ, (q : ℂ) ^ k = cexp (-(h * (k : ℂ))) := by
    intro k; rw [hqc, ← Complex.exp_nat_mul]; ring_nf
  have hqz : (q : ℂ) ^ z = cexp (-(h * z)) := cpow_ofReal_exp_neg
  -- numerator and denominator
  have hA := (dlmf_5_18_3 (a := (q : ℂ)) hqn).2
  have hB := (dlmf_5_18_3 (a := (q : ℂ) ^ z) hqn).2
  have hA' : ∀ n, qPochhammer q q n = ∏ k ∈ range n, (1 - cexp (-(h * ((k : ℂ) + 1)))) := by
    intro n; refine Finset.prod_congr rfl fun k _ => ?_
    rw [hqk, hqc, ← Complex.exp_add]; ring_nf
  have hB' : ∀ n, qPochhammer ((q : ℂ) ^ z) q n =
      ∏ k ∈ range n, (1 - cexp (-(h * ((k : ℂ) + z)))) := by
    intro n; refine Finset.prod_congr rfl fun k _ => ?_
    rw [hqk, hqz, ← Complex.exp_add]; ring_nf
  have hBne : qPochhammerInf ((q : ℂ) ^ z) q ≠ 0 := by
    refine qPochhammerInf_ne_zero hqn fun k => ?_
    rw [hqk, hqz, ← Complex.exp_add]
    have hr : 0 < ((k : ℂ) + z).re := by simp; linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
    convert one_sub_cexp_ne_zero hh hr using 2; ring_nf
  -- the exponential factor
  have hF : Tendsto (fun n : ℕ => qLogF h ((n : ℂ) + 1)) atTop (𝓝 0) := by
    have hp : Tendsto (fun n : ℕ => cexp (-(h : ℂ)) ^ (n + 1)) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by rw [← hqc]; exact hqn)).comp
        (tendsto_add_atTop_nat 1)
    have h1 : Tendsto (fun n : ℕ => 1 - cexp (-(h : ℂ)) ^ (n + 1)) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.sub hp
    have := ((continuousAt_clog (by simp : (1 : ℂ) ∈ slitPlane)).tendsto).comp h1
    rw [Complex.log_one] at this
    refine this.congr fun n => ?_
    simp only [Function.comp_apply, qLogF]
    rw [← Complex.exp_nat_mul]; congr 3; push_cast; ring
  have hE : Tendsto (fun n : ℕ => cexp ((1 - z) * (qLogF h 1 - qLogF h ((n : ℂ) + 1)))) atTop
      (𝓝 (((1 - q : ℝ) : ℂ) ^ (1 - z))) := by
    have := (Complex.continuous_exp.tendsto _).comp
      ((tendsto_const_nhds (x := qLogF h 1)).sub hF |>.const_mul (1 - z))
    rw [sub_zero] at this
    have hne : ((1 - q : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 (by linarith)
    have hval : ((1 - q : ℝ) : ℂ) ^ (1 - z) = cexp ((1 - z) * qLogF h 1) := by
      rw [cpow_def_of_ne_zero hne, qLogF, mul_comm (1 - z)]
      congr 3
      push_cast; rw [hqc]; ring_nf
    rw [hval]; exact this
  have hlim := ((hA.div hB hBne).mul hE)
  have hval : qGamma q z = qPochhammerInf q q / qPochhammerInf ((q : ℂ) ^ z) q *
      ((1 - q : ℝ) : ℂ) ^ (1 - z) := by rw [qGamma]; ring
  rw [hval]
  refine (cexp_tsum_eq_of_tendsto hsum ?_).symm
  convert hlim using 1
  funext n
  simp only [Pi.div_apply]
  rw [exp_sum_qLogTerm hh hz n, hA', hB']

end QSide

/-! ### The `Γ` side -/

theorem tendsto_sq_ratio (z : ℂ) :
    Tendsto (fun n : ℕ => (z + n) * (z + n + 1) / ((n : ℂ) + 1) ^ 2) atTop (𝓝 1) := by
  have hinv : Tendsto (fun n : ℕ => ((n : ℂ) + 1)⁻¹) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝 ((0 : ℝ) : ℂ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.ofReal
    simpa [one_div] using this
  have h := ((tendsto_const_nhds (x := (1 : ℂ))).add (hinv.const_mul (z - 1))).mul
    ((tendsto_const_nhds (x := (1 : ℂ))).add (hinv.const_mul z))
  simp only [mul_zero, add_zero, mul_one] at h
  refine h.congr fun n => ?_
  have : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast n.succ_ne_zero
  field_simp
  ring

/-- For `ℜz > 0`, `exp ∑_{k<n} ℓ_k = GammaSeq z (n + 1) · (z + n)(z + n + 1)/(n + 1)²`. -/
theorem exp_sum_gammaLogTerm {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    cexp (∑ k ∈ range n, gammaLogTerm z k) =
      GammaSeq z (n + 1) * ((z + n) * (z + n + 1) / ((n : ℂ) + 1) ^ 2) := by
  have hzk : ∀ k : ℕ, (k : ℂ) + z ≠ 0 := fun k h0 => by
    have := congrArg Complex.re h0; simp at this; linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
  have hk1 : ∀ k : ℕ, (k : ℂ) + 1 ≠ 0 := fun k => by exact_mod_cast k.succ_ne_zero
  have hsplit : ∑ k ∈ range n, gammaLogTerm z k =
      ∑ k ∈ range n, (Complex.log ((k : ℂ) + 1) - Complex.log ((k : ℂ) + z)) +
        ∑ k ∈ range n, (1 - z) * (Complex.log (((k : ℕ) : ℂ) + 1) -
          Complex.log ((((k + 1 : ℕ)) : ℂ) + 1)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [gammaLogTerm]; push_cast; ring_nf
  rw [hsplit, Complex.exp_add, cexp_sum_mul_sub (f := fun k : ℕ => Complex.log ((k : ℂ) + 1)),
    Complex.exp_sum]
  simp only [Nat.cast_zero, zero_add, Complex.log_one, zero_sub]
  have hprod : ∏ k ∈ range n, cexp (Complex.log ((k : ℂ) + 1) - Complex.log ((k : ℂ) + z)) =
      (n.factorial : ℂ) / ∏ k ∈ range n, (z + k) := by
    rw [← Finset.prod_range_add_one_eq_factorial, Nat.cast_prod, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Complex.exp_sub, Complex.exp_log (hk1 k), Complex.exp_log (hzk k), add_comm z]
    push_cast; ring
  have hn1 : ((n : ℂ) + 1) ≠ 0 := hk1 n
  have hcp : cexp ((1 - z) * -Complex.log ((n : ℂ) + 1)) = ((n : ℂ) + 1) ^ z / ((n : ℂ) + 1) := by
    rw [show (1 - z) * -Complex.log ((n : ℂ) + 1) = Complex.log ((n : ℂ) + 1) * (z - 1) by ring,
      ← cpow_def_of_ne_zero hn1, cpow_sub _ _ hn1, cpow_one]
  rw [hprod, hcp, GammaSeq]
  rw [Finset.prod_range_succ, Finset.prod_range_succ, Nat.factorial_succ]
  have hP : ∏ k ∈ range n, (z + k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => by rw [add_comm]; exact hzk k
  have hzn : z + n ≠ 0 := by rw [add_comm]; exact hzk n
  have hzn1 : z + ((n + 1 : ℕ) : ℂ) ≠ 0 := by rw [add_comm]; exact hzk (n + 1)
  push_cast at hzn1 ⊢
  field_simp
  ring

theorem cexp_tsum_gammaLogTerm {z : ℂ} (hz : 0 < z.re) (hsum : Summable (gammaLogTerm z)) :
    cexp (∑' k, gammaLogTerm z k) = Complex.Gamma z := by
  refine cexp_tsum_eq_of_tendsto hsum ?_
  have := ((GammaSeq_tendsto_Gamma z).comp (tendsto_add_atTop_nat 1)).mul (tendsto_sq_ratio z)
  rw [mul_one] at this
  refine this.congr fun n => ?_
  rw [exp_sum_gammaLogTerm hz n]; rfl

/-! ### Assembly -/

/-- `Γ_{e^{−h}}(z) → Γ(z)` as `h → 0⁺`, for `ℜz ≥ 1`. -/
theorem tendsto_qGamma_exp_neg {z : ℂ} (hz : 1 ≤ z.re) :
    Tendsto (fun h : ℝ => qGamma (Real.exp (-h)) z) (𝓝[>] 0) (𝓝 (Complex.Gamma z)) := by
  have hz0 : 0 < z.re := by linarith
  set K := 3 * (‖1 - z‖ ^ 2 + ‖1 - z‖)
  have hbs : Summable fun k : ℕ => K / ((k : ℝ) + 1) ^ 2 := by
    exact (summable_one_div_nat_add_one_sq.mul_left K).congr fun k => by ring
  have hT := tendsto_tsum_of_dominated_convergence hbs (tendsto_qLogTerm hz0)
    (by filter_upwards [self_mem_nhdsWithin] with h hh using norm_qLogTerm_le hh hz)
  have hsumℓ : Summable (gammaLogTerm z) := by
    refine Summable.of_norm_bounded hbs fun k => ?_
    refine le_of_tendsto ((tendsto_qLogTerm hz0 k).norm) ?_
    filter_upwards [self_mem_nhdsWithin] with h hh using norm_qLogTerm_le hh hz k
  rw [← cexp_tsum_gammaLogTerm hz0 hsumℓ]
  refine ((Complex.continuous_exp.tendsto _).comp hT).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hs : Summable (qLogTerm h z) :=
    Summable.of_norm_bounded hbs fun k => norm_qLogTerm_le hh hz k
  exact (qGamma_exp_neg_eq hh hz0 hs).symm

theorem tendsto_neg_log_nhdsLT_one :
    Tendsto (fun q : ℝ => -Real.log q) (𝓝[<] 1) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have := ((Real.continuousAt_log one_ne_zero).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Set.Iio 1))).neg
    simpa using this
  · filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with q hq
    exact neg_pos.2 (Real.log_neg hq.1 hq.2)

theorem tendsto_qGamma_of_one_le_re {z : ℂ} (hz : 1 ≤ z.re) :
    Tendsto (fun q : ℝ => qGamma q z) (𝓝[<] 1) (𝓝 (Complex.Gamma z)) := by
  refine ((tendsto_qGamma_exp_neg hz).comp tendsto_neg_log_nhdsLT_one).congr' ?_
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with q hq
  simp [Real.exp_log hq.1]

/-- `(1 − q^w)/(1 − q) → w` as `q → 1⁻`. -/
theorem tendsto_one_sub_cpow_div (w : ℂ) :
    Tendsto (fun q : ℝ => (1 - (q : ℂ) ^ w) / (1 - q)) (𝓝[<] 1) (𝓝 w) := by
  have hd : HasDerivAt (fun q : ℝ => (q : ℂ) ^ w) w 1 := by
    have := (Complex.hasStrictDerivAt_cpow_const (c := w) (x := ((1 : ℝ) : ℂ))
      (by simp)).hasDerivAt.comp_ofReal
    simpa using this
  have := hd.tendsto_slope.mono_left (nhdsWithin_mono _ fun q (hq : q < 1) => hq.ne)
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with q hq
  have hq1 : (1 : ℂ) - q ≠ 0 := by
    rw [sub_ne_zero]; intro h; have : (1 : ℝ) = q := by exact_mod_cast h
    exact (ne_of_lt (Set.mem_Iio.1 hq)) this.symm
  have hq1' : (q : ℂ) - 1 ≠ 0 := by
    intro h0; apply hq1; rw [← neg_sub, h0, neg_zero]
  rw [slope_def_module, Complex.real_smul, ofReal_one, one_cpow]
  push_cast
  field_simp
  ring

section Iterate

variable {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
include hq0 hq1

/-- Iterated 5.18.7. -/
theorem qGamma_add_nat (z : ℂ) (N : ℕ) (hN : ∀ k < N, (q : ℂ) ^ (z + k) ≠ 1) :
    qGamma q (z + N) = (∏ k ∈ range N, (1 - (q : ℂ) ^ (z + k)) / (1 - q)) * qGamma q z := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.prod_range_succ, Nat.cast_succ, ← add_assoc,
      dlmf_5_18_7 hq0 hq1 (hN N (by omega)), ih fun k hk => hN k (by omega)]
    ring

theorem qGamma_neg_nat (n : ℕ) : qGamma q (-n) = 0 := by
  have hqn := norm_ofReal_lt_one_of_pos hq0 hq1
  have hq : (q : ℂ) ≠ 0 := ofReal_ne_zero.2 hq0.ne'
  have h0 : qPochhammerInf ((q : ℂ) ^ (-(n : ℂ))) q = 0 := by
    refine qPochhammerInf_eq_zero hqn (k := n) ?_
    rw [cpow_neg, cpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ hq), sub_self]
  rw [qGamma, h0, div_zero]

end Iterate

/-- DLMF 5.18.10: `lim_{q→1⁻} Γ_q(z) = Γ(z)` (for every `z`; at `z = −n` both sides are `0`). -/
theorem dlmf_5_18_10 (z : ℂ) :
    Tendsto (fun q : ℝ => qGamma q z) (𝓝[<] 1) (𝓝 (Complex.Gamma z)) := by
  by_cases hp : ∃ n : ℕ, z = -n
  · obtain ⟨n, rfl⟩ := hp
    rw [Complex.Gamma_neg_nat_eq_zero]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with q hq
    exact (qGamma_neg_nat hq.1 hq.2 n).symm
  push Not at hp
  have hz : ∀ k : ℕ, z + k ≠ 0 := fun k h0 => hp k (eq_neg_of_add_eq_zero_left h0)
  set N := ⌈1 - z.re⌉₊
  have hN : 1 ≤ (z + N).re := by
    simp only [add_re, natCast_re]
    linarith [Nat.le_ceil (1 - z.re)]
  have hlimN := tendsto_qGamma_of_one_le_re hN
  have hr : ∀ k ∈ range N, Tendsto (fun q : ℝ => (1 - (q : ℂ) ^ (z + k)) / (1 - q)) (𝓝[<] 1)
      (𝓝 (z + k)) := fun k _ => tendsto_one_sub_cpow_div (z + k)
  have hP := tendsto_finsetProd (range N) hr
  have hPne : ∏ k ∈ range N, (z + k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hz k
  have hev : ∀ᶠ q : ℝ in 𝓝[<] 1, ∀ k ∈ range N, (1 - (q : ℂ) ^ (z + k)) / (1 - q) ≠ 0 :=
    (Filter.eventually_all_finset _).2 fun k hk =>
      (hr k hk).eventually (eventually_ne_nhds (hz k))
  rw [show Complex.Gamma z = Complex.Gamma (z + N) / ∏ k ∈ range N, (z + k) by
    rw [Gamma_add_nat_eq_prod_mul z N fun j _ => hz j, mul_div_cancel_left₀ _ hPne]]
  refine (hlimN.div hP hPne).congr' ?_
  filter_upwards [hev, Ioo_mem_nhdsLT zero_lt_one] with q hq hq01
  have hk : ∀ k < N, (q : ℂ) ^ (z + k) ≠ 1 := by
    intro k hk h1
    have := hq k (Finset.mem_range.2 hk)
    rw [h1, sub_self, zero_div] at this
    exact this rfl
  simp only [Pi.div_apply]
  rw [qGamma_add_nat hq01.1 hq01.2 z N hk, mul_div_cancel_left₀ _
    (Finset.prod_ne_zero_iff.2 hq)]

end Azurite.DLMF
