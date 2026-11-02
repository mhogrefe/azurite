/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section10
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# DLMF §2.10(i): Euler–Maclaurin with an infinite tail, and the remainder bound

Tools for the examples of §2.10(i) (2.10.4–2.10.5, 2.10.8):

* `periodicBernoulli_sub_sign`: `B̃_{2m}(x) − B_{2m}` has the constant sign `(−1)^m` (DLMF: "from
  §24.12(i), (24.2.2), and (24.4.27)"); proved from the Fourier series of `B_{2m}`
  (`hasSum_one_div_nat_pow_mul_cos`).
* `em_tail`: if `f^{(2m)}` is integrable on `(a, ∞)`, then for `n ≥ a`,
  `∑_{j=a}^{n} f(j) = ∫_a^n f + ½f(n) + K + ∑_{s=1}^{m−1} B_{2s}/(2s)! f^{(2s−1)}(n) + R(n)` with
  the constant `K = emConst` and `R(n) = ∫_n^∞ (B̃_{2m} − B_{2m})/(2m)! f^{(2m)}` (`emRem`).
* `tendsto_emRem`: `R(n) → 0`; `emRem_sign`: `(−1)^m R(n) ≥ 0` when `f^{(2m)} ≥ 0`.
* `const_eq_of_tendsto`, `remainder_bound`: the argument of DLMF after 2.10.5 — two consecutive
  remainders of opposite signs differing by the next term `t`, so that `0 ≤ (−1)^m R_m ≤ (−1)^m t`
  ("bounded in absolute value by this term and has the same sign").
-/

open Filter Topology Set MeasureTheory intervalIntegral Finset
open scoped Nat Real

namespace Azurite.DLMF

/-- `(−1)^m (B̃_{2m}(x) − B_{2m}) ≥ 0`. -/
theorem periodicBernoulli_sub_sign {m : ℕ} (hm : m ≠ 0) (x : ℝ) :
    0 ≤ (-1) ^ m * (periodicBernoulli (2 * m) x - bernoulli (2 * m)) := by
  set y := Int.fract x
  have hy : y ∈ Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hd := (hasSum_one_div_nat_pow_mul_cos hm hy).sub (hasSum_one_div_nat_pow_mul_cos hm h0)
  have hle := hasSum_le (fun n => ?_) hd hasSum_zero
  · set P : ℝ := (2 * π) ^ (2 * m) / 2 / ((2 * m)! : ℝ) with hP
    have hP0 : 0 < P := by positivity
    have hB : (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * m))).eval 0 =
        bernoulli (2 * m) := bernoulliFun_eval_zero (2 * m)
    have hBy : (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * m))).eval y =
        periodicBernoulli (2 * m) x := rfl
    rw [hB, hBy] at hle
    have key : (-1 : ℝ) ^ (m + 1) * P * (periodicBernoulli (2 * m) x - bernoulli (2 * m)) ≤ 0 := by
      have e : (-1 : ℝ) ^ (m + 1) * P * (periodicBernoulli (2 * m) x - bernoulli (2 * m)) =
          (-1) ^ (m + 1) * (2 * π) ^ (2 * m) / 2 / ((2 * m)! : ℝ) * periodicBernoulli (2 * m) x -
          (-1) ^ (m + 1) * (2 * π) ^ (2 * m) / 2 / ((2 * m)! : ℝ) * bernoulli (2 * m) := by
        rw [hP]
        ring
      rw [e]
      exact hle
    have e : (-1 : ℝ) ^ m * (periodicBernoulli (2 * m) x - bernoulli (2 * m)) =
        -((-1 : ℝ) ^ (m + 1) * P * (periodicBernoulli (2 * m) x - bernoulli (2 * m))) / P := by
      field_simp
      ring
    rw [e]
    exact div_nonneg (neg_nonneg.mpr key) hP0.le
  · have hc := Real.cos_le_one (2 * π * n * y)
    have hn : 0 ≤ 1 / (n : ℝ) ^ (2 * m) := by positivity
    simp only [mul_zero, Real.cos_zero, mul_one]
    nlinarith

section Tail

variable {D : ℕ → ℝ → ℝ}

/-- The constant of `em_tail`: `½f(a) − ∑_{s=1}^{m−1} B_{2s}/(2s)! f^{(2s−1)}(a)
+ ∫_a^∞ (B_{2m} − B̃_{2m})/(2m)! f^{(2m)}`. -/
noncomputable def emConst (a : ℝ) (m : ℕ) (D : ℕ → ℝ → ℝ) : ℝ :=
  D 0 a / 2 - ∑ s ∈ Finset.Icc 1 (m - 1), (bernoulli (2 * s) : ℝ) / ((2 * s)! : ℝ) *
    D (2 * s - 1) a +
  ∫ x in Ioi a, ((bernoulli (2 * m) : ℝ) - periodicBernoulli (2 * m) x) / ((2 * m)! : ℝ) *
    D (2 * m) x

/-- The remainder `∫_n^∞ (B̃_{2m} − B_{2m})/(2m)! f^{(2m)}`. -/
noncomputable def emRem (m : ℕ) (D : ℕ → ℝ → ℝ) (n : ℝ) : ℝ :=
  ∫ x in Ioi n, (periodicBernoulli (2 * m) x - bernoulli (2 * m)) / ((2 * m)! : ℝ) * D (2 * m) x

theorem integrableOn_periodicBernoulli_mul {h : ℝ → ℝ} {s : Set ℝ} (hh : IntegrableOn h s)
    (k : ℕ) (b c : ℝ) :
    IntegrableOn (fun x => (b - periodicBernoulli k x) / c * h x) s := by
  obtain ⟨C, hC⟩ := periodicBernoulli_bound k
  have hm : AEStronglyMeasurable (fun x : ℝ => (b - periodicBernoulli k x) / c) volume :=
    ((measurable_const.sub ((continuous_bernoulliFun k).measurable.comp measurable_fract)).div_const
      c).aestronglyMeasurable
  refine hh.bdd_mul hm.restrict (c := (|b| + C) / |c|) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_div]
  refine div_le_div_of_nonneg_right ?_ (abs_nonneg c)
  calc |b - periodicBernoulli k x| ≤ |b| + |periodicBernoulli k x| := abs_sub _ _
    _ ≤ |b| + C := by have := hC x; rw [periodicBernoulli]; linarith

theorem integral_Ioi_split {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hg : IntegrableOn g (Ioi a)) :
    ∫ x in Ioi a, g x = (∫ x in a..b, g x) + ∫ x in Ioi b, g x := by
  rw [← Ioc_union_Ioi_eq_Ioi hab, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hg.mono_set Ioc_subset_Ioi_self) (hg.mono_set (Ioi_subset_Ioi hab)), integral_of_le hab]

/-- Euler–Maclaurin with an infinite tail. -/
theorem em_tail {a : ℤ} {m : ℕ} (hm : 0 < m)
    (hd : ∀ k < 2 * m, ∀ x : ℝ, (a : ℝ) ≤ x → HasDerivAt (D k) (D (k + 1) x) x)
    (hint : IntegrableOn (D (2 * m)) (Ioi (a : ℝ))) {n : ℤ} (han : a ≤ n) :
    ∑ j ∈ Finset.Icc a n, D 0 j = (∫ x in (a : ℝ)..n, D 0 x) + D 0 n / 2 + emConst a m D +
      ∑ s ∈ Finset.Icc 1 (m - 1), (bernoulli (2 * s) : ℝ) / ((2 * s)! : ℝ) * D (2 * s - 1) n +
      emRem m D n := by
  have hg := integrableOn_periodicBernoulli_mul hint (2 * m) (bernoulli (2 * m)) ((2 * m)! : ℝ)
  have hsplit := integral_Ioi_split (show (a : ℝ) ≤ n by exact_mod_cast han) hg
  have hrem : emRem m D n = -∫ x in Ioi (n : ℝ), ((bernoulli (2 * m) : ℝ) -
      periodicBernoulli (2 * m) x) / ((2 * m)! : ℝ) * D (2 * m) x := by
    rw [emRem, ← MeasureTheory.integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    ring
  rcases han.lt_or_eq with h | h
  · have hd' : ∀ k < 2 * m, ∀ x ∈ Icc (a : ℝ) n, HasDerivAt (D k) (D (k + 1) x) x :=
      fun k hk x hx => hd k hk x hx.1
    have hi : IntervalIntegrable (D (2 * m)) volume a n :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by exact_mod_cast han)).mpr
        (hint.mono_set Ioc_subset_Ioi_self)
    rw [dlmf_2_10_1 h hm hd' hi, emConst, hrem]
    simp only [mul_sub, sum_sub_distrib]
    linarith
  · subst h
    simp only [Finset.Icc_self, sum_singleton, integral_same, emConst, hrem]
    rw [hsplit, integral_same, zero_add]
    ring

/-- `R(n) → 0`. -/
theorem tendsto_emRem {a : ℝ} {m : ℕ} (hint : IntegrableOn (D (2 * m)) (Ioi a)) :
    Tendsto (fun n : ℕ => emRem m D n) atTop (𝓝 0) := by
  have hg := integrableOn_periodicBernoulli_mul hint (2 * m) (bernoulli (2 * m)) ((2 * m)! : ℝ)
  have hlim := intervalIntegral_tendsto_integral_Ioi a hg tendsto_natCast_atTop_atTop
  have hconst := (tendsto_const_nhds (x := ∫ x in Ioi a, ((bernoulli (2 * m) : ℝ) -
    periodicBernoulli (2 * m) x) / ((2 * m)! : ℝ) * D (2 * m) x)).sub hlim
  rw [sub_self] at hconst
  have hneg := hconst.neg
  rw [neg_zero] at hneg
  refine hneg.congr' ?_
  filter_upwards [eventually_ge_atTop ⌈a⌉₊] with n hn
  have han : a ≤ n := (Nat.le_ceil a).trans (by exact_mod_cast hn)
  rw [integral_Ioi_split han hg, emRem, add_sub_cancel_left, ← MeasureTheory.integral_neg]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  ring

/-- `(−1)^m R(n) ≥ 0` when `f^{(2m)} ≥ 0` on `(n, ∞)`. -/
theorem emRem_sign {m : ℕ} (hm : m ≠ 0) {n : ℝ} (hpos : ∀ x, n < x → 0 ≤ D (2 * m) x) :
    0 ≤ (-1) ^ m * emRem m D n := by
  rw [emRem, ← MeasureTheory.integral_const_mul]
  refine setIntegral_nonneg measurableSet_Ioi fun x hx => ?_
  have h := periodicBernoulli_sub_sign hm x
  have hf : (0 : ℝ) ≤ ((2 * m)! : ℝ) := by positivity
  have := mul_nonneg (div_nonneg h hf) (hpos x hx)
  calc (0 : ℝ) ≤ _ := this
    _ = _ := by ring

end Tail

/-- Two representations differing only in their constants and terms tending to `0` have equal
constants. -/
theorem const_eq_of_tendsto {K₁ K₂ : ℝ} {u v : ℕ → ℝ} (h : ∀ᶠ n in atTop, K₁ + u n = K₂ + v n)
    (hu : Tendsto u atTop (𝓝 0)) (hv : Tendsto v atTop (𝓝 0)) : K₁ = K₂ := by
  have h1 : Tendsto (fun n => K₁ + u n) atTop (𝓝 (K₁ + 0)) := tendsto_const_nhds.add hu
  have h2 : Tendsto (fun n => K₂ + v n) atTop (𝓝 (K₂ + 0)) := tendsto_const_nhds.add hv
  have := tendsto_nhds_unique (h1.congr' h) h2
  simpa using this

/-- If `R = t + R'` with `(−1)^m R ≥ 0` and `(−1)^{m+1} R' ≥ 0`, then `0 ≤ (−1)^m R ≤ (−1)^m t`:
`R` is bounded in absolute value by `t` and has the same sign. -/
theorem remainder_bound {m : ℕ} {R R' t : ℝ} (h : R = t + R') (hR : 0 ≤ (-1) ^ m * R)
    (hR' : 0 ≤ (-1) ^ (m + 1) * R') : 0 ≤ (-1) ^ m * R ∧ (-1) ^ m * R ≤ (-1) ^ m * t := by
  refine ⟨hR, ?_⟩
  rw [pow_succ] at hR'
  rw [h]
  nlinarith

theorem remainder_bound_abs {m : ℕ} {R t : ℝ} (h : 0 ≤ (-1) ^ m * R ∧ (-1) ^ m * R ≤ (-1) ^ m * t) :
    |R| ≤ |t| ∧ (R ≠ 0 → SignType.sign R = SignType.sign t) := by
  rcases neg_one_pow_eq_or ℝ m with hs | hs <;> rw [hs] at h
  · refine ⟨by rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith,
      fun hR => ?_⟩
    rw [sign_pos (lt_of_le_of_ne (by linarith) (Ne.symm hR)), sign_pos (by
      have := lt_of_le_of_ne (by linarith : 0 ≤ R) (Ne.symm hR); linarith)]
  · refine ⟨by rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith,
      fun hR => ?_⟩
    rw [sign_neg (lt_of_le_of_ne (by linarith) hR), sign_neg (by
      have := lt_of_le_of_ne (by linarith : R ≤ 0) hR; linarith)]

end Azurite.DLMF
