/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section15
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# DLMF §1.15(viii): Tauberian theorems

https://dlmf.nist.gov/1.15.viii

Both theorems are proved by Karamata's method. For a polynomial `P`,
`(1 − x) ∑ bₙ xⁿ P(xⁿ) → s ∫_0^1 P` (`karamata_poly`), and in the Abel form
`∑ aₙ xⁿ Q(xⁿ) → s Q(1)` (`abel_poly`). A step function is squeezed between polynomials whose
integrals differ by less than `ε` (`exists_poly_sandwich`, via Weierstrass), and the series is
sampled at `x_N = e^{−1/(N+1/2)}` (`tauberPoint`), where `x_Nⁿ ≥ e^{−1}` exactly for `n ≤ N`.

* 1.15.54–1.15.55, Littlewood's theorem (`littlewood`, `dlmf_1_15_55`): if a real series is
  Abel summable to `s` and `aₙ > −K/n`, then it converges to `s`. The proof is Wielandt's
  version of Karamata's argument, with the step `1_{[e^{−1}, 1]}` written as
  `t + t(1 − t) h(t)`.
* 1.15.56–1.15.57, the Hardy–Littlewood theorem: if `(1 − x) ∑ aₙ xⁿ → s` and `aₙ ≥ 0`, then
  `(a₀ + ⋯ + aₙ)/(n + 1) → s` (`hardy_littlewood_nonneg`, `dlmf_1_15_57_nonneg`). The case
  `|aₙ| ≤ K` (`dlmf_1_15_57_bounded`) allows complex `aₙ`. It reduces to the nonnegative case
  through `aₙ + K`, applied to the real and imaginary parts.

In the case `aₙ ≥ 0`, convergence of `∑ aₙ xⁿ` on `(0, 1)` is assumed; DLMF leaves it implicit
in 1.15.56. In the bounded case it is automatic.
-/

open Set Filter Topology Finset Polynomial MeasureTheory
open scoped Nat

namespace Azurite.DLMF

/-! ### Karamata's method: polynomial test functions -/

theorem pow_mul_pow_pow (x : ℝ) (n k : ℕ) : x ^ n * (x ^ n) ^ k = (x ^ (k + 1)) ^ n := by
  rw [← pow_succ', ← pow_mul, ← pow_mul, mul_comm]

theorem tendsto_pow_nhdsLT_one (k : ℕ) :
    Tendsto (fun x : ℝ => x ^ (k + 1)) (𝓝[<] 1) (𝓝[<] 1) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have h := ((continuous_pow (k + 1)).tendsto (1 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Iio 1))
    rwa [one_pow] at h
  · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with x hx
    exact pow_lt_one₀ hx.1.le hx.2 (Nat.succ_ne_zero k)

/-- `(1 − x)/(1 − x^{k+1}) → 1/(k + 1)` as `x → 1−`, written with the geometric sum. -/
theorem tendsto_inv_geom_sum (k : ℕ) :
    Tendsto (fun x : ℝ => (∑ i ∈ range (k + 1), x ^ i)⁻¹) (𝓝[<] 1) (𝓝 ((k : ℝ) + 1)⁻¹) := by
  have h : Tendsto (fun x : ℝ => ∑ i ∈ range (k + 1), x ^ i) (𝓝[<] 1)
      (𝓝 (∑ i ∈ range (k + 1), (1 : ℝ) ^ i)) :=
    ((continuous_finsetSum _ fun i _ => continuous_pow i).tendsto 1).mono_left
      nhdsWithin_le_nhds
  simp only [one_pow, sum_const, card_range, nsmul_eq_mul, mul_one] at h
  push_cast at h
  exact h.inv₀ (by positivity)

theorem one_sub_pow_eq (x : ℝ) (k : ℕ) :
    1 - x ^ (k + 1) = (∑ i ∈ range (k + 1), x ^ i) * (1 - x) := by
  have := geom_sum_mul x (k + 1)
  linarith

/-- **Karamata's lemma** for polynomials: if `(1 − y) ∑ bₙ yⁿ → s` as `y → 1−`, then
`(1 − x) ∑ bₙ xⁿ P(xⁿ) → s ∫_0^1 P` for every polynomial `P`. -/
theorem karamata_poly {b : ℕ → ℝ} {s : ℝ}
    (hs : ∀ y ∈ Ioo (0 : ℝ) 1, Summable fun n => b n * y ^ n)
    (hl : Tendsto (fun y => (1 - y) * ∑' n, b n * y ^ n) (𝓝[<] 1) (𝓝 s)) (P : ℝ[X]) :
    (∀ x ∈ Ioo (0 : ℝ) 1, Summable fun n => b n * x ^ n * P.eval (x ^ n)) ∧
    Tendsto (fun x => (1 - x) * ∑' n, b n * x ^ n * P.eval (x ^ n)) (𝓝[<] 1)
      (𝓝 (s * ∫ t in (0 : ℝ)..1, P.eval t)) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    refine ⟨fun x hx => ?_, ?_⟩
    · simpa [eval_add, mul_add] using (hP.1 x hx).add (hQ.1 x hx)
    · have hi : ∫ t in (0 : ℝ)..1, (P + Q).eval t =
          (∫ t in (0 : ℝ)..1, P.eval t) + ∫ t in (0 : ℝ)..1, Q.eval t := by
        simp only [eval_add]
        exact intervalIntegral.integral_add (P.continuous.intervalIntegrable _ _)
          (Q.continuous.intervalIntegrable _ _)
      rw [hi, mul_add]
      refine (hP.2.add hQ.2).congr' ?_
      filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with x hx
      simp only [eval_add, mul_add]
      rw [(hP.1 x hx).tsum_add (hQ.1 x hx), mul_add]
  | monomial k c =>
    have hy : ∀ x ∈ Ioo (0 : ℝ) 1, x ^ (k + 1) ∈ Ioo (0 : ℝ) 1 := fun x hx =>
      ⟨pow_pos hx.1 _, pow_lt_one₀ hx.1.le hx.2 (Nat.succ_ne_zero k)⟩
    have he : ∀ x : ℝ, (fun n => b n * x ^ n * (monomial k c).eval (x ^ n)) =
        fun n => c * (b n * (x ^ (k + 1)) ^ n) := fun x => funext fun n => by
      rw [eval_monomial, ← pow_mul_pow_pow]; ring
    refine ⟨fun x hx => ?_, ?_⟩
    · rw [he]; exact (hs _ (hy x hx)).mul_left c
    · have hint : ∫ t in (0 : ℝ)..1, (monomial k c).eval t = c * ((k : ℝ) + 1)⁻¹ := by
        simp only [eval_monomial]
        rw [intervalIntegral.integral_const_mul, integral_pow]
        simp
      rw [hint]
      have h := ((tendsto_inv_geom_sum k).mul (hl.comp (tendsto_pow_nhdsLT_one k))).const_mul c
      refine (h.congr' ?_).trans (by rw [show c * (((k : ℝ) + 1)⁻¹ * s) =
        s * (c * ((k : ℝ) + 1)⁻¹) by ring])
      filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with x hx
      simp only [Function.comp, he]
      rw [tsum_mul_left, one_sub_pow_eq]
      have hg : 0 < ∑ i ∈ range (k + 1), x ^ i :=
        sum_pos (fun i _ => pow_pos hx.1 i) (by simp)
      field_simp

/-- The Abel analogue: if `∑ aₙ yⁿ → s` as `y → 1−`, then `∑ aₙ xⁿ Q(xⁿ) → s Q(1)`. -/
theorem abel_poly {a : ℕ → ℝ} {s : ℝ}
    (hs : ∀ y ∈ Ioo (0 : ℝ) 1, Summable fun n => a n * y ^ n)
    (hl : Tendsto (fun y => ∑' n, a n * y ^ n) (𝓝[<] 1) (𝓝 s)) (Q : ℝ[X]) :
    (∀ x ∈ Ioo (0 : ℝ) 1, Summable fun n => a n * x ^ n * Q.eval (x ^ n)) ∧
    Tendsto (fun x => ∑' n, a n * x ^ n * Q.eval (x ^ n)) (𝓝[<] 1) (𝓝 (s * Q.eval 1)) := by
  induction Q using Polynomial.induction_on' with
  | add P Q hP hQ =>
    refine ⟨fun x hx => ?_, ?_⟩
    · simpa [eval_add, mul_add] using (hP.1 x hx).add (hQ.1 x hx)
    · rw [eval_add, mul_add]
      refine (hP.2.add hQ.2).congr' ?_
      filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with x hx
      simp only [eval_add, mul_add]
      rw [(hP.1 x hx).tsum_add (hQ.1 x hx)]
  | monomial k c =>
    have hy : ∀ x ∈ Ioo (0 : ℝ) 1, x ^ (k + 1) ∈ Ioo (0 : ℝ) 1 := fun x hx =>
      ⟨pow_pos hx.1 _, pow_lt_one₀ hx.1.le hx.2 (Nat.succ_ne_zero k)⟩
    have he : ∀ x : ℝ, (fun n => a n * x ^ n * (monomial k c).eval (x ^ n)) =
        fun n => c * (a n * (x ^ (k + 1)) ^ n) := fun x => funext fun n => by
      rw [eval_monomial, ← pow_mul_pow_pow]; ring
    refine ⟨fun x hx => ?_, ?_⟩
    · rw [he]; exact (hs _ (hy x hx)).mul_left c
    · rw [eval_monomial, one_pow, mul_one, mul_comm s]
      refine ((hl.comp (tendsto_pow_nhdsLT_one k)).const_mul c).congr' ?_
      filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with x hx
      simp only [Function.comp, he]
      rw [tsum_mul_left]

/-! ### One-sided polynomial approximation of a step -/

/-- A function equal to a continuous `u` left of `c` and a continuous `v ≥ u` from `c` on, with
values in `[L, U]`, is squeezed on `[0, 1]` between polynomials `P₁ ≤ h ≤ P₂` with
`∫_0^1 (P₂ − P₁) < ε`. -/
theorem exists_poly_sandwich {u v : ℝ → ℝ} (hu : Continuous u) (hv : Continuous v) {L U c : ℝ}
    (hLu : ∀ t, L ≤ u t) (hvU : ∀ t, v t ≤ U) (huv : ∀ t, u t ≤ v t) {ε : ℝ} (hε : 0 < ε) :
    ∃ P₁ P₂ : ℝ[X], (∀ t ∈ Icc (0 : ℝ) 1,
      P₁.eval t ≤ (if t < c then u t else v t) ∧ (if t < c then u t else v t) ≤ P₂.eval t) ∧
      ∫ t in (0 : ℝ)..1, (P₂.eval t - P₁.eval t) < ε := by
  have hLU : L ≤ U := (hLu 0).trans ((huv 0).trans (hvU 0))
  set D := U - L with hD
  have hD0 : 0 ≤ D := by linarith
  set η := ε / (8 * (D + 1)) with hη
  have hη0 : 0 < η := by positivity
  set ℓ₂ : ℝ → ℝ := fun t => L + D * ((t - (c - η)) / η)
  set ℓ₁ : ℝ → ℝ := fun t => L + D * ((t - c) / η)
  set φ₂ : ℝ → ℝ := fun t => max (u t) (min (v t) (ℓ₂ t))
  set φ₁ : ℝ → ℝ := fun t => min (v t) (max (u t) (ℓ₁ t))
  set h : ℝ → ℝ := fun t => if t < c then u t else v t
  have hφ₂c : Continuous φ₂ := hu.max (hv.min (by fun_prop))
  have hφ₁c : Continuous φ₁ := hv.min (hu.max (by fun_prop))
  have hℓ₂U : ∀ t, c ≤ t → U ≤ ℓ₂ t := fun t ht => by
    have h1 : 1 ≤ (t - (c - η)) / η := by rw [le_div_iff₀ hη0]; linarith
    have := mul_le_mul_of_nonneg_left h1 hD0
    simp only [ℓ₂]; linarith
  have hℓ₂L : ∀ t, t ≤ c - η → ℓ₂ t ≤ L := fun t ht => by
    have h1 : (t - (c - η)) / η ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hη0.le
    have := mul_le_mul_of_nonneg_left h1 hD0
    simp only [ℓ₂]; linarith
  have hℓ₁U : ∀ t, c + η ≤ t → U ≤ ℓ₁ t := fun t ht => by
    have h1 : 1 ≤ (t - c) / η := by rw [le_div_iff₀ hη0]; linarith
    have := mul_le_mul_of_nonneg_left h1 hD0
    simp only [ℓ₁]; linarith
  have hℓ₁L : ∀ t, t < c → ℓ₁ t ≤ L := fun t ht => by
    have h1 : (t - c) / η ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hη0.le
    have := mul_le_mul_of_nonneg_left h1 hD0
    simp only [ℓ₁]; linarith
  have h2ge : ∀ t, h t ≤ φ₂ t := fun t => by
    by_cases ht : t < c
    · simp only [h, ht, ite_true]; exact le_max_left _ _
    · simp only [h, ht, ite_false, φ₂]
      rw [min_eq_left ((hvU t).trans (hℓ₂U t (not_lt.mp ht)))]
      exact le_max_right _ _
  have h1le : ∀ t, φ₁ t ≤ h t := fun t => by
    by_cases ht : t < c
    · simp only [h, ht, ite_true, φ₁]
      rw [max_eq_left ((hℓ₁L t ht).trans (hLu t))]
      exact min_le_right _ _
    · simp only [h, ht, ite_false]; exact min_le_left _ _
  have hdiff : ∀ t, φ₂ t - φ₁ t ≤ (Ioo (c - η) (c + η)).indicator (fun _ => D) t := fun t => by
    have hφ₂U : φ₂ t ≤ U := max_le ((huv t).trans (hvU t)) ((min_le_left _ _).trans (hvU t))
    have hφ₁L : L ≤ φ₁ t := le_min ((hLu t).trans (huv t)) ((hLu t).trans (le_max_left _ _))
    by_cases hm : t ∈ Ioo (c - η) (c + η)
    · rw [indicator_of_mem hm]; linarith
    · rw [indicator_of_notMem hm]
      rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hm
      rcases hm with hm | hm
      · have e2 : φ₂ t = u t := by
          simp only [φ₂]
          exact max_eq_left ((min_le_right _ _).trans ((hℓ₂L t hm).trans (hLu t)))
        have e1 : φ₁ t = u t := by
          simp only [φ₁]
          rw [max_eq_left ((hℓ₁L t (by linarith)).trans (hLu t))]
          exact min_eq_right (huv t)
        rw [e1, e2, sub_self]
      · have e2 : φ₂ t = v t := by
          simp only [φ₂]
          rw [min_eq_left ((hvU t).trans (hℓ₂U t (by linarith)))]
          exact max_eq_right (huv t)
        have e1 : φ₁ t = v t := by
          simp only [φ₁]
          rw [max_eq_right ((huv t).trans ((hvU t).trans (hℓ₁U t hm)))]
          exact min_eq_left ((hvU t).trans (hℓ₁U t hm))
        rw [e1, e2, sub_self]
  set δ := ε / 8 with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨p₂, hp₂⟩ := exists_polynomial_near_of_continuousOn 0 1 φ₂ hφ₂c.continuousOn δ hδ0
  obtain ⟨p₁, hp₁⟩ := exists_polynomial_near_of_continuousOn 0 1 φ₁ hφ₁c.continuousOn δ hδ0
  refine ⟨p₁ - Polynomial.C δ, p₂ + Polynomial.C δ, fun t ht => ?_, ?_⟩
  · have h1 := abs_lt.mp (hp₁ t ht)
    have h2 := abs_lt.mp (hp₂ t ht)
    simp only [eval_sub, eval_add, eval_C]
    exact ⟨by linarith [h1le t], by linarith [h2ge t]⟩
  · set ind : ℝ → ℝ := (Ioo (c - η) (c + η)).indicator fun _ => D
    have hind : IntervalIntegrable ind volume 0 1 :=
      ((integrable_indicator_iff measurableSet_Ioo).mpr
        (integrableOn_const (by simp) (by simp))).intervalIntegrable
    have hle : ∫ t in (0 : ℝ)..1, ((p₂ + Polynomial.C δ).eval t - (p₁ - Polynomial.C δ).eval t) ≤
        ∫ t in (0 : ℝ)..1, (ind t + 4 * δ) := by
      refine intervalIntegral.integral_mono_on zero_le_one
        (((p₂ + Polynomial.C δ).continuous.sub (p₁ - Polynomial.C δ).continuous).intervalIntegrable
          _ _) (hind.add intervalIntegrable_const) fun t ht => ?_
      have h1 := abs_lt.mp (hp₁ t ht)
      have h2 := abs_lt.mp (hp₂ t ht)
      simp only [eval_sub, eval_add, eval_C]
      linarith [hdiff t]
    have hI : ∫ t in (0 : ℝ)..1, ind t ≤ D * (2 * η) := by
      rw [intervalIntegral.integral_of_le zero_le_one, setIntegral_indicator measurableSet_Ioo,
        setIntegral_const, smul_eq_mul, mul_comm]
      refine mul_le_mul_of_nonneg_left ?_ hD0
      calc volume.real (Ioc (0 : ℝ) 1 ∩ Ioo (c - η) (c + η))
          ≤ volume.real (Ioo (c - η) (c + η)) :=
            measureReal_mono inter_subset_right measure_Ioo_lt_top.ne
        _ = 2 * η := by rw [Real.volume_real_Ioo_of_le (by linarith)]; ring
    rw [intervalIntegral.integral_add hind intervalIntegrable_const,
      intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul] at hle
    have hDη : D * (2 * η) < ε / 4 := by
      rw [hη, show D * (2 * (ε / (8 * (D + 1)))) = ε / 4 * (D / (D + 1)) by field_simp; ring]
      have : D / (D + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
      nlinarith
    linarith

/-! ### The sample points `x_N = e^{−1/(N+1/2)}` -/

/-- `x_N = e^{−1/(N + 1/2)}`, chosen so that `x_Nⁿ ≥ e^{−1}` exactly when `n ≤ N`. -/
noncomputable def tauberPoint (N : ℕ) : ℝ := Real.exp (-1 / ((N : ℝ) + 1 / 2))

theorem tauberPoint_mem (N : ℕ) : tauberPoint N ∈ Ioo (0 : ℝ) 1 :=
  ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by norm_num) (by positivity))⟩

theorem exp_neg_one_le_tauberPoint_pow_iff (N n : ℕ) :
    Real.exp (-1) ≤ tauberPoint N ^ n ↔ n ≤ N := by
  have hN : (0 : ℝ) < N + 1 / 2 := by positivity
  rw [tauberPoint, ← Real.exp_nat_mul, Real.exp_le_exp, mul_div_assoc', mul_neg_one,
    le_div_iff₀ hN]
  constructor
  · intro h
    by_contra hc
    have : (N : ℝ) + 1 ≤ n := by exact_mod_cast (not_le.mp hc)
    linarith
  · intro h
    have : (n : ℝ) ≤ N := by exact_mod_cast h
    linarith

theorem tendsto_tauberPoint : Tendsto tauberPoint atTop (𝓝[<] 1) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun N => (tauberPoint_mem N).2⟩
  have h : Tendsto (fun N : ℕ => -1 / ((N : ℝ) + 1 / 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have := (Real.continuous_exp.tendsto 0).comp h
  rwa [Real.exp_zero] at this

theorem tendsto_add_div_add (a b : ℝ) (hb : 0 < b) :
    Tendsto (fun N : ℕ => ((N : ℝ) + a) / ((N : ℝ) + b)) atTop (𝓝 1) := by
  have h : Tendsto (fun N : ℕ => (a - b) / ((N : ℝ) + b)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have h2 := h.const_add 1
  rw [add_zero] at h2
  refine h2.congr fun N => ?_
  have : (0 : ℝ) < N + b := by positivity
  field_simp
  ring

/-- `(1 − x_N)(N + 1) → 1`. -/
theorem tendsto_one_sub_tauberPoint_mul :
    Tendsto (fun N : ℕ => (1 - tauberPoint N) * ((N : ℝ) + 1)) atTop (𝓝 1) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_add_div_add 1 (3 / 2) (by norm_num))
    (tendsto_add_div_add 1 (1 / 2) (by norm_num)) (fun N => ?_) (fun N => ?_)
  · have hN : (0 : ℝ) < N + 1 / 2 := by positivity
    set h := 1 / ((N : ℝ) + 1 / 2)
    have hh : 0 < h := by positivity
    have h1 : Real.exp (-h) ≤ 1 / (1 + h) := by
      rw [Real.exp_neg, ← one_div]
      exact one_div_le_one_div_of_le (by positivity) (by linarith [Real.add_one_le_exp h])
    have h2 : h / (1 + h) ≤ 1 - tauberPoint N := by
      rw [tauberPoint, show -1 / ((N : ℝ) + 1 / 2) = -h by simp [h, neg_div]]
      have : h / (1 + h) = 1 - 1 / (1 + h) := by field_simp; ring
      linarith
    have e : h / (1 + h) = 1 / ((N : ℝ) + 3 / 2) := by
      simp only [h]; field_simp; ring
    rw [e] at h2
    calc ((N : ℝ) + 1) / ((N : ℝ) + 3 / 2) = 1 / ((N : ℝ) + 3 / 2) * ((N : ℝ) + 1) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h2 (by positivity)
  · have hN : (0 : ℝ) < N + 1 / 2 := by positivity
    have h1 : 1 - tauberPoint N ≤ 1 / ((N : ℝ) + 1 / 2) := by
      have := Real.add_one_le_exp (-1 / ((N : ℝ) + 1 / 2))
      rw [tauberPoint]
      rw [neg_div] at this ⊢
      linarith
    calc (1 - tauberPoint N) * ((N : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1 / 2) * ((N : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = ((N : ℝ) + 1) / ((N : ℝ) + 1 / 2) := by ring

/-! ### Littlewood's theorem (1.15.54–1.15.55) -/

theorem one_sub_pow_le (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) (n : ℕ) : 1 - x ^ n ≤ n * (1 - x) := by
  have h := geom_sum_mul x n
  have hs : ∑ i ∈ range n, x ^ i ≤ n := by
    calc ∑ i ∈ range n, x ^ i ≤ ∑ _i ∈ range n, (1 : ℝ) :=
          sum_le_sum fun i _ => pow_le_one₀ hx.1 hx.2
      _ = n := by simp
  nlinarith [hx.2]

theorem summable_one_mul_geometric : ∀ y ∈ Ioo (0 : ℝ) 1, Summable fun n => (1 : ℝ) * y ^ n :=
  fun _ hy => (summable_geometric_of_lt_one hy.1.le hy.2).mul_left 1

theorem tendsto_one_sub_mul_geometric :
    Tendsto (fun y : ℝ => (1 - y) * ∑' n, (1 : ℝ) * y ^ n) (𝓝[<] 1) (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with y hy
  simp only [one_mul]
  rw [tsum_geometric_of_lt_one hy.1.le hy.2, mul_inv_cancel₀ (by linarith [hy.2])]

/-- Elementary bounds for one term of Littlewood's sandwich. -/
theorem tauber_term {t H G p₁ p₂ : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hG : G = t + t * (1 - t) * H)
    (h1 : p₁ ≤ H) (h2 : H ≤ p₂) :
    0 ≤ t * (1 + (1 - t) * p₂) - G ∧ t * (1 + (1 - t) * p₂) - G ≤ t * (1 - t) * (p₂ - p₁) ∧
      0 ≤ G - t * (1 + (1 - t) * p₁) ∧ G - t * (1 + (1 - t) * p₁) ≤ t * (1 - t) * (p₂ - p₁) := by
  have hw : 0 ≤ t * (1 - t) := mul_nonneg ht.1 (by linarith [ht.2])
  subst hG
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [mul_le_mul_of_nonneg_left h1 hw,
    mul_le_mul_of_nonneg_left h2 hw]

/-- The step `1_{[e^{−1}, 1]}` written as `t + t(1 − t) h(t)` on `[0, 1]`. -/
theorem littlewood_step (t : ℝ) :
    (if Real.exp (-1) ≤ t then (1 : ℝ) else 0) = t + t * (1 - t) *
      (if t < Real.exp (-1) then -1 / (1 - min t (Real.exp (-1)))
        else 1 / max t (Real.exp (-1))) := by
  have hc0 : 0 < Real.exp (-1) := Real.exp_pos _
  have hc1 : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  by_cases h : t < Real.exp (-1)
  · have h' : ¬ Real.exp (-1) ≤ t := not_le.mpr h
    simp only [h, h', ↓reduceIte, min_eq_left h.le]
    have : 1 - t ≠ 0 := by linarith
    field_simp
    ring
  · simp only [h, not_lt.mp h, ↓reduceIte, max_eq_left (not_lt.mp h)]
    have : t ≠ 0 := by linarith [not_lt.mp h]
    field_simp
    ring

/-- **Littlewood's Tauberian theorem** (real form): if `∑ aₙ yⁿ → s` as `y → 1−` and
`aₙ > −K/n`, then `∑ aₙ` converges to `s`. -/
theorem littlewood {a : ℕ → ℝ} {s K : ℝ} (hK : 0 < K) (ha : ∀ n, 0 < n → -K / n < a n)
    (hs : ∀ y ∈ Ioo (0 : ℝ) 1, Summable fun n => a n * y ^ n)
    (hl : Tendsto (fun y => ∑' n, a n * y ^ n) (𝓝[<] 1) (𝓝 s)) :
    Tendsto (fun N => ∑ n ∈ range (N + 1), a n) atTop (𝓝 s) := by
  have hc0 : 0 < Real.exp (-1) := Real.exp_pos _
  have hc1 : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hden : ∀ t, 0 < 1 - min t (Real.exp (-1)) := fun t => by
    linarith [min_le_right t (Real.exp (-1))]
  have hmax : ∀ t, 0 < max t (Real.exp (-1)) := fun t =>
    lt_of_lt_of_le hc0 (le_max_right _ _)
  have hu : Continuous fun t => -1 / (1 - min t (Real.exp (-1))) :=
    continuous_const.div (continuous_const.sub (continuous_id.min continuous_const))
      fun t => (hden t).ne'
  have hv : Continuous fun t => 1 / max t (Real.exp (-1)) :=
    continuous_const.div (continuous_id.max continuous_const) fun t => (hmax t).ne'
  have hLu : ∀ t, -1 / (1 - Real.exp (-1)) ≤ -1 / (1 - min t (Real.exp (-1))) := fun t => by
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact one_div_le_one_div_of_le (by linarith) (by linarith [min_le_right t (Real.exp (-1))])
  have hvU : ∀ t, 1 / max t (Real.exp (-1)) ≤ 1 / Real.exp (-1) := fun t =>
    one_div_le_one_div_of_le hc0 (le_max_right _ _)
  have huv : ∀ t, -1 / (1 - min t (Real.exp (-1))) ≤ 1 / max t (Real.exp (-1)) := fun t => by
    have h1 : -1 / (1 - min t (Real.exp (-1))) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by norm_num) (hden t).le
    have h2 : 0 ≤ 1 / max t (Real.exp (-1)) := (one_div_pos.mpr (hmax t)).le
    linarith
  set Q : ℝ[X] → ℝ[X] := fun P => 1 + (1 - X) * P
  have hQ : ∀ P t, (Q P).eval t = 1 + (1 - t) * P.eval t := fun P t => by simp [Q]
  have hQ1 : ∀ P, (Q P).eval 1 = 1 := fun P => by rw [hQ]; ring
  have hgN : ∀ N n, (if Real.exp (-1) ≤ tauberPoint N ^ n then (1 : ℝ) else 0) =
      if n ≤ N then 1 else 0 := fun N n => by
    rw [if_congr (exp_neg_one_le_tauberPoint_pow_iff N n) rfl rfl]
  have hout : ∀ N n, n ∉ range (N + 1) →
      a n * (if Real.exp (-1) ≤ tauberPoint N ^ n then (1 : ℝ) else 0) = 0 := fun N n hn => by
    rw [hgN, ite_eq_right (fun h => hn (mem_range.mpr (Nat.lt_succ_of_le h))), mul_zero]
  have hSN : ∀ N, ∑ n ∈ range (N + 1), a n =
      ∑' n, a n * (if Real.exp (-1) ≤ tauberPoint N ^ n then (1 : ℝ) else 0) := fun N => by
    rw [tsum_eq_sum (hout N)]
    refine sum_congr rfl fun n hn => ?_
    rw [hgN, ite_eq_left (Nat.lt_succ_iff.mp (mem_range.mp hn)), mul_one]
  have hsumN : ∀ N, Summable fun n =>
      a n * (if Real.exp (-1) ≤ tauberPoint N ^ n then (1 : ℝ) else 0) := fun N =>
    summable_of_ne_finset_zero (hout N)
  -- the two-sided bound for a given polynomial sandwich
  have key : ∀ P₁ P₂ : ℝ[X], (∀ t ∈ Icc (0 : ℝ) 1,
      P₁.eval t ≤ (if t < Real.exp (-1) then -1 / (1 - min t (Real.exp (-1)))
        else 1 / max t (Real.exp (-1))) ∧
      (if t < Real.exp (-1) then -1 / (1 - min t (Real.exp (-1)))
        else 1 / max t (Real.exp (-1))) ≤ P₂.eval t) → ∀ N,
      (∑' n, a n * tauberPoint N ^ n * (Q P₁).eval (tauberPoint N ^ n)) -
          K * ((1 - tauberPoint N) *
            ∑' n, 1 * tauberPoint N ^ n * (P₂ - P₁).eval (tauberPoint N ^ n)) ≤
        ∑ n ∈ range (N + 1), a n ∧
      ∑ n ∈ range (N + 1), a n ≤
        (∑' n, a n * tauberPoint N ^ n * (Q P₂).eval (tauberPoint N ^ n)) +
          K * ((1 - tauberPoint N) *
            ∑' n, 1 * tauberPoint N ^ n * (P₂ - P₁).eval (tauberPoint N ^ n)) := by
    intro P₁ P₂ hP N
    set x := tauberPoint N with hxdef
    have hx := tauberPoint_mem N
    have hA1 := (abel_poly hs hl (Q P₁)).1 x hx
    have hA2 := (abel_poly hs hl (Q P₂)).1 x hx
    have hR := (karamata_poly summable_one_mul_geometric tendsto_one_sub_mul_geometric
      (P₂ - P₁)).1 x hx
    have hterm : ∀ n : ℕ, x ^ n ∈ Icc (0 : ℝ) 1 ∧ (1 - x ^ n ≤ n * (1 - x)) := fun n =>
      ⟨⟨pow_nonneg hx.1.le n, pow_le_one₀ hx.1.le hx.2.le⟩,
        one_sub_pow_le x ⟨hx.1.le, hx.2.le⟩ n⟩
    have hb : ∀ n, a n * x ^ n * (Q P₁).eval (x ^ n) -
          K * ((1 - x) * (1 * x ^ n * (P₂ - P₁).eval (x ^ n))) ≤
          a n * (if Real.exp (-1) ≤ x ^ n then (1 : ℝ) else 0) ∧
        a n * (if Real.exp (-1) ≤ x ^ n then (1 : ℝ) else 0) ≤
          a n * x ^ n * (Q P₂).eval (x ^ n) +
            K * ((1 - x) * (1 * x ^ n * (P₂ - P₁).eval (x ^ n))) := fun n => by
      obtain ⟨ht, hbern⟩ := hterm n
      obtain ⟨h1, h2⟩ := hP _ ht
      obtain ⟨d0, d1, e0, e1⟩ := tauber_term ht (littlewood_step _) h1 h2
      set t := x ^ n
      set G := if Real.exp (-1) ≤ t then (1 : ℝ) else 0
      rw [hQ, hQ, eval_sub]
      set p₁ := P₁.eval t
      set p₂ := P₂.eval t
      have hw : 0 ≤ p₂ - p₁ := by linarith
      have hx1 : 0 ≤ 1 - x := by linarith [hx.2]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · have ht1 : t = 1 := pow_zero x
        have hG1 : G = 1 := by simp only [G, ht1, ite_eq_left hc1.le]
        rw [ht1] at *
        rw [hG1]
        have : 0 ≤ K * ((1 - x) * (1 * 1 * (p₂ - p₁))) := by positivity
        constructor <;> nlinarith
      · have hKn := ha n hn
        have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
        have hKn' : -a n * n < K := by
          have := (div_lt_iff₀ hnpos).mp hKn
          linarith
        have hbt : t * (1 - t) * (p₂ - p₁) ≤ n * ((1 - x) * (t * (p₂ - p₁))) := by
          have := mul_le_mul_of_nonneg_right hbern (mul_nonneg ht.1 hw)
          nlinarith
        constructor
        · -- a G = a·lower + a d', with d' ≥ 0
          have hd : -a n * (G - t * (1 + (1 - t) * p₁)) * n ≤
              K * (t * (1 - t) * (p₂ - p₁)) := by
            have := mul_le_mul_of_nonneg_right hKn'.le e0
            nlinarith [mul_le_mul_of_nonneg_left e1 hK.le]
          have : -a n * (G - t * (1 + (1 - t) * p₁)) ≤ K * ((1 - x) * (t * (p₂ - p₁))) := by
            have h3 : -a n * (G - t * (1 + (1 - t) * p₁)) * n ≤
                K * (n * ((1 - x) * (t * (p₂ - p₁)))) :=
              hd.trans (mul_le_mul_of_nonneg_left hbt hK.le)
            have h4 : K * (n * ((1 - x) * (t * (p₂ - p₁)))) =
                (K * ((1 - x) * (t * (p₂ - p₁)))) * n := by ring
            rw [h4] at h3
            exact le_of_mul_le_mul_right h3 hnpos
          nlinarith
        · have hd : -a n * (t * (1 + (1 - t) * p₂) - G) * n ≤
              K * (t * (1 - t) * (p₂ - p₁)) := by
            have := mul_le_mul_of_nonneg_right hKn'.le d0
            nlinarith [mul_le_mul_of_nonneg_left d1 hK.le]
          have : -a n * (t * (1 + (1 - t) * p₂) - G) ≤ K * ((1 - x) * (t * (p₂ - p₁))) := by
            have h3 : -a n * (t * (1 + (1 - t) * p₂) - G) * n ≤
                K * (n * ((1 - x) * (t * (p₂ - p₁)))) :=
              hd.trans (mul_le_mul_of_nonneg_left hbt hK.le)
            have h4 : K * (n * ((1 - x) * (t * (p₂ - p₁)))) =
                (K * ((1 - x) * (t * (p₂ - p₁)))) * n := by ring
            rw [h4] at h3
            exact le_of_mul_le_mul_right h3 hnpos
          nlinarith
    have hRs : Summable fun n => K * ((1 - x) * (1 * x ^ n * (P₂ - P₁).eval (x ^ n))) :=
      (hR.mul_left (1 - x)).mul_left K
    rw [hSN N]
    constructor
    · have := (hA1.sub hRs).tsum_le_tsum (fun n => (hb n).1) (hsumN N)
      rwa [hA1.tsum_sub hRs, tsum_mul_left, tsum_mul_left] at this
    · have := (hsumN N).tsum_le_tsum (fun n => (hb n).2) (hA2.add hRs)
      rwa [hA2.tsum_add hRs, tsum_mul_left, tsum_mul_left] at this
  -- limits of the bounds
  have hlim : ∀ P₁ P₂ : ℝ[X],
      Tendsto (fun N => (∑' n, a n * tauberPoint N ^ n * (Q P₁).eval (tauberPoint N ^ n)) -
          K * ((1 - tauberPoint N) *
            ∑' n, 1 * tauberPoint N ^ n * (P₂ - P₁).eval (tauberPoint N ^ n))) atTop
        (𝓝 (s - K * ∫ t in (0 : ℝ)..1, (P₂.eval t - P₁.eval t))) ∧
      Tendsto (fun N => (∑' n, a n * tauberPoint N ^ n * (Q P₂).eval (tauberPoint N ^ n)) +
          K * ((1 - tauberPoint N) *
            ∑' n, 1 * tauberPoint N ^ n * (P₂ - P₁).eval (tauberPoint N ^ n))) atTop
        (𝓝 (s + K * ∫ t in (0 : ℝ)..1, (P₂.eval t - P₁.eval t))) := by
    intro P₁ P₂
    have hR := (karamata_poly summable_one_mul_geometric tendsto_one_sub_mul_geometric
      (P₂ - P₁)).2
    simp only [eval_sub, one_mul] at hR
    have h1 := (abel_poly hs hl (Q P₁)).2
    have h2 := (abel_poly hs hl (Q P₂)).2
    rw [hQ1, mul_one] at h1 h2
    simp only [eval_sub, one_mul]
    exact ⟨((h1.sub (hR.const_mul K)).comp tendsto_tauberPoint),
      ((h2.add (hR.const_mul K)).comp tendsto_tauberPoint)⟩
  rw [tendsto_order]
  constructor
  · intro s' hs'
    obtain ⟨P₁, P₂, hP, hI⟩ := exists_poly_sandwich hu hv hLu hvU huv (c := Real.exp (-1))
      (show 0 < (s - s') / (2 * K) by have := sub_pos.mpr hs'; positivity)
    have hgt : s' < s - K * ∫ t in (0 : ℝ)..1, (P₂.eval t - P₁.eval t) := by
      have := mul_lt_mul_of_pos_left hI hK
      rw [show K * ((s - s') / (2 * K)) = (s - s') / 2 by field_simp] at this
      linarith
    filter_upwards [(hlim P₁ P₂).1.eventually (lt_mem_nhds hgt)] with N hN
    exact hN.trans_le (key P₁ P₂ hP N).1
  · intro s' hs'
    obtain ⟨P₁, P₂, hP, hI⟩ := exists_poly_sandwich hu hv hLu hvU huv (c := Real.exp (-1))
      (show 0 < (s' - s) / (2 * K) by have := sub_pos.mpr hs'; positivity)
    have hlt : s + K * ∫ t in (0 : ℝ)..1, (P₂.eval t - P₁.eval t) < s' := by
      have := mul_lt_mul_of_pos_left hI hK
      rw [show K * ((s' - s) / (2 * K)) = (s' - s) / 2 by field_simp] at this
      linarith
    filter_upwards [(hlim P₁ P₂).2.eventually (gt_mem_nhds hlt)] with N hN
    exact (key P₁ P₂ hP N).2.trans_lt hN

/-! ### The Hardy–Littlewood theorem (1.15.56–1.15.57) -/

theorem karamata_step (t : ℝ) :
    t * (if t < Real.exp (-1) then 0 else 1 / max t (Real.exp (-1))) =
      if Real.exp (-1) ≤ t then 1 else 0 := by
  by_cases h : t < Real.exp (-1)
  · rw [ite_eq_left h, ite_eq_right (not_le.mpr h), mul_zero]
  · have h' := not_lt.mp h
    have : t ≠ 0 := by linarith [Real.exp_pos (-1)]
    rw [ite_eq_right h, ite_eq_left h', max_eq_left h']
    field_simp

/-- **Hardy–Littlewood (Karamata)**: if `bₙ ≥ 0` and `(1 − x) ∑ bₙ xⁿ → s` as `x → 1−`, then
`(b₀ + ⋯ + b_N)/(N + 1) → s`. -/
theorem hardy_littlewood_nonneg {b : ℕ → ℝ} {s : ℝ} (hb : ∀ n, 0 ≤ b n)
    (hs : ∀ y ∈ Ioo (0 : ℝ) 1, Summable fun n => b n * y ^ n)
    (hl : Tendsto (fun y => (1 - y) * ∑' n, b n * y ^ n) (𝓝[<] 1) (𝓝 s)) :
    Tendsto (fun N : ℕ => (∑ n ∈ range (N + 1), b n) / ((N : ℝ) + 1)) atTop (𝓝 s) := by
  have hc0 : 0 < Real.exp (-1) := Real.exp_pos _
  have hmax : ∀ t, 0 < max t (Real.exp (-1)) := fun t =>
    lt_of_lt_of_le hc0 (le_max_right _ _)
  have hv : Continuous fun t => 1 / max t (Real.exp (-1)) :=
    continuous_const.div (continuous_id.max continuous_const) fun t => (hmax t).ne'
  have hvU : ∀ t, 1 / max t (Real.exp (-1)) ≤ 1 / Real.exp (-1) := fun t =>
    one_div_le_one_div_of_le hc0 (le_max_right _ _)
  have huv : ∀ t, (0 : ℝ) ≤ 1 / max t (Real.exp (-1)) := fun t => (one_div_pos.mpr (hmax t)).le
  have hs0 : 0 ≤ s := by
    refine ge_of_tendsto hl ?_
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with y hy
    exact mul_nonneg (by linarith [hy.2]) (tsum_nonneg fun n => mul_nonneg (hb n)
      (pow_nonneg hy.1.le n))
  -- the sandwich for an arbitrary nonnegative weight sequence
  have bound : ∀ w : ℕ → ℝ, (∀ n, 0 ≤ w n) → ∀ {r : ℝ},
      (∀ y ∈ Ioo (0 : ℝ) 1, Summable fun n => w n * y ^ n) →
      Tendsto (fun y => (1 - y) * ∑' n, w n * y ^ n) (𝓝[<] 1) (𝓝 r) →
      ∀ P₁ P₂ : ℝ[X], (∀ t ∈ Icc (0 : ℝ) 1,
        P₁.eval t ≤ (if t < Real.exp (-1) then 0 else 1 / max t (Real.exp (-1))) ∧
        (if t < Real.exp (-1) then 0 else 1 / max t (Real.exp (-1))) ≤ P₂.eval t) → ∀ N,
      (1 - tauberPoint N) * ∑' n, w n * tauberPoint N ^ n * P₁.eval (tauberPoint N ^ n) ≤
          (1 - tauberPoint N) * ∑ n ∈ range (N + 1), w n ∧
        (1 - tauberPoint N) * ∑ n ∈ range (N + 1), w n ≤
          (1 - tauberPoint N) * ∑' n, w n * tauberPoint N ^ n * P₂.eval (tauberPoint N ^ n) := by
    intro w hw r hws hwl P₁ P₂ hP N
    set x := tauberPoint N
    have hx := tauberPoint_mem N
    have hx1 : 0 ≤ 1 - x := by linarith [hx.2]
    have h1 := (karamata_poly hws hwl P₁).1 x hx
    have h2 := (karamata_poly hws hwl P₂).1 x hx
    have hout : ∀ n ∉ range (N + 1),
        w n * (if Real.exp (-1) ≤ x ^ n then (1 : ℝ) else 0) = 0 := fun n hn => by
      rw [if_congr (exp_neg_one_le_tauberPoint_pow_iff N n) rfl rfl,
        ite_eq_right (fun h => hn (mem_range.mpr (Nat.lt_succ_of_le h))), mul_zero]
    have hS : ∑ n ∈ range (N + 1), w n =
        ∑' n, w n * (if Real.exp (-1) ≤ x ^ n then (1 : ℝ) else 0) := by
      rw [tsum_eq_sum hout]
      refine sum_congr rfl fun n hn => ?_
      rw [if_congr (exp_neg_one_le_tauberPoint_pow_iff N n) rfl rfl,
        ite_eq_left (Nat.lt_succ_iff.mp (mem_range.mp hn)), mul_one]
    have hsum : Summable fun n => w n * (if Real.exp (-1) ≤ x ^ n then (1 : ℝ) else 0) :=
      summable_of_ne_finset_zero hout
    have hterm : ∀ n, w n * x ^ n * P₁.eval (x ^ n) ≤
          w n * (if Real.exp (-1) ≤ x ^ n then (1 : ℝ) else 0) ∧
        w n * (if Real.exp (-1) ≤ x ^ n then (1 : ℝ) else 0) ≤
          w n * x ^ n * P₂.eval (x ^ n) := fun n => by
      have ht : x ^ n ∈ Icc (0 : ℝ) 1 := ⟨pow_nonneg hx.1.le n, pow_le_one₀ hx.1.le hx.2.le⟩
      obtain ⟨hp1, hp2⟩ := hP _ ht
      rw [← karamata_step (x ^ n), mul_assoc, mul_assoc]
      exact ⟨mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp1 ht.1) (hw n),
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp2 ht.1) (hw n)⟩
    rw [hS]
    exact ⟨mul_le_mul_of_nonneg_left (h1.tsum_le_tsum (fun n => (hterm n).1) hsum) hx1,
      mul_le_mul_of_nonneg_left (hsum.tsum_le_tsum (fun n => (hterm n).2) h2) hx1⟩
  -- the integrals of the sandwiching polynomials straddle 1
  have hone : ∀ P₁ P₂ : ℝ[X], (∀ t ∈ Icc (0 : ℝ) 1,
      P₁.eval t ≤ (if t < Real.exp (-1) then 0 else 1 / max t (Real.exp (-1))) ∧
      (if t < Real.exp (-1) then 0 else 1 / max t (Real.exp (-1))) ≤ P₂.eval t) →
      (∫ t in (0 : ℝ)..1, P₁.eval t) ≤ 1 ∧ 1 ≤ ∫ t in (0 : ℝ)..1, P₂.eval t := by
    intro P₁ P₂ hP
    have hb1 := bound (fun _ => 1) (fun _ => zero_le_one) summable_one_mul_geometric
      tendsto_one_sub_mul_geometric P₁ P₂ hP
    have hc : ∀ N : ℕ, (1 - tauberPoint N) * ∑ n ∈ range (N + 1), (fun _ => (1 : ℝ)) n =
        (1 - tauberPoint N) * ((N : ℝ) + 1) := fun N => by simp
    have l1 := ((karamata_poly summable_one_mul_geometric tendsto_one_sub_mul_geometric
      P₁).2.comp tendsto_tauberPoint)
    have l2 := ((karamata_poly summable_one_mul_geometric tendsto_one_sub_mul_geometric
      P₂).2.comp tendsto_tauberPoint)
    rw [one_mul] at l1 l2
    constructor
    · exact le_of_tendsto_of_tendsto' l1 tendsto_one_sub_tauberPoint_mul fun N => by
        have := (hb1 N).1; rw [hc] at this; exact this
    · exact le_of_tendsto_of_tendsto' tendsto_one_sub_tauberPoint_mul l2 fun N => by
        have := (hb1 N).2; rw [hc] at this; exact this
  -- `(1 − x_N) S_N → s`
  have hT : Tendsto (fun N => (1 - tauberPoint N) * ∑ n ∈ range (N + 1), b n) atTop (𝓝 s) := by
    rw [tendsto_order]
    constructor
    · intro s' hs'
      obtain ⟨P₁, P₂, hP, hI⟩ := exists_poly_sandwich continuous_const hv (fun _ => le_rfl)
        hvU huv (c := Real.exp (-1))
        (show 0 < (s - s') / (2 * (s + 1)) by have := sub_pos.mpr hs'; positivity)
      obtain ⟨h1, h2⟩ := hone P₁ P₂ hP
      rw [intervalIntegral.integral_sub (P₂.continuous.intervalIntegrable _ _)
        (P₁.continuous.intervalIntegrable _ _)] at hI
      have hgt : s' < s * ∫ t in (0 : ℝ)..1, P₁.eval t := by
        have hε : s * ((s - s') / (2 * (s + 1))) < s - s' := by
          rw [show s * ((s - s') / (2 * (s + 1))) = (s - s') / 2 * (s / (s + 1)) by
            field_simp]
          have : s / (s + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
          nlinarith [sub_pos.mpr hs']
        nlinarith [mul_le_mul_of_nonneg_left hI.le hs0]
      filter_upwards [((karamata_poly hs hl P₁).2.comp tendsto_tauberPoint).eventually
        (lt_mem_nhds hgt)] with N hN
      exact hN.trans_le (bound b hb hs hl P₁ P₂ hP N).1
    · intro s' hs'
      obtain ⟨P₁, P₂, hP, hI⟩ := exists_poly_sandwich continuous_const hv (fun _ => le_rfl)
        hvU huv (c := Real.exp (-1))
        (show 0 < (s' - s) / (2 * (s + 1)) by have := sub_pos.mpr hs'; positivity)
      obtain ⟨h1, h2⟩ := hone P₁ P₂ hP
      rw [intervalIntegral.integral_sub (P₂.continuous.intervalIntegrable _ _)
        (P₁.continuous.intervalIntegrable _ _)] at hI
      have hlt : s * ∫ t in (0 : ℝ)..1, P₂.eval t < s' := by
        have hε : s * ((s' - s) / (2 * (s + 1))) < s' - s := by
          rw [show s * ((s' - s) / (2 * (s + 1))) = (s' - s) / 2 * (s / (s + 1)) by
            field_simp]
          have : s / (s + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
          nlinarith [sub_pos.mpr hs']
        nlinarith [mul_le_mul_of_nonneg_left hI.le hs0]
      filter_upwards [((karamata_poly hs hl P₂).2.comp tendsto_tauberPoint).eventually
        (gt_mem_nhds hlt)] with N hN
      exact (bound b hb hs hl P₁ P₂ hP N).2.trans_lt hN
  have h := hT.div tendsto_one_sub_tauberPoint_mul one_ne_zero
  rw [div_one] at h
  refine h.congr fun N => ?_
  have hx := tauberPoint_mem N
  have : 1 - tauberPoint N ≠ 0 := by linarith [hx.2]
  simp only [Pi.div_apply]
  field_simp

/-- The bounded case of the Hardy–Littlewood theorem, for real coefficients. -/
theorem hardy_littlewood_bounded_real {a : ℕ → ℝ} {s K : ℝ} (ha : ∀ n, |a n| ≤ K)
    (hl : Tendsto (fun y => (1 - y) * ∑' n, a n * y ^ n) (𝓝[<] 1) (𝓝 s)) :
    Tendsto (fun N : ℕ => (∑ n ∈ range (N + 1), a n) / ((N : ℝ) + 1)) atTop (𝓝 s) := by
  have hsa : ∀ y ∈ Ioo (0 : ℝ) 1, Summable fun n => a n * y ^ n := fun y hy =>
    Summable.of_norm_bounded ((summable_geometric_of_lt_one hy.1.le hy.2).mul_left K) fun n => by
      rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_of_nonneg hy.1.le]
      exact mul_le_mul_of_nonneg_right (ha n) (pow_nonneg hy.1.le n)
  have hg : ∀ y ∈ Ioo (0 : ℝ) 1, Summable fun n => K * y ^ n := fun y hy =>
    (summable_geometric_of_lt_one hy.1.le hy.2).mul_left K
  have hb : ∀ n, 0 ≤ a n + K := fun n => by linarith [neg_abs_le (a n), ha n]
  have hsb : ∀ y ∈ Ioo (0 : ℝ) 1, Summable fun n => (a n + K) * y ^ n := fun y hy => by
    simpa [add_mul] using (hsa y hy).add (hg y hy)
  have hlb : Tendsto (fun y => (1 - y) * ∑' n, (a n + K) * y ^ n) (𝓝[<] 1) (𝓝 (s + K)) := by
    refine (hl.add_const K).congr' ?_
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with y hy
    simp only [add_mul]
    rw [(hsa y hy).tsum_add (hg y hy), tsum_mul_left, tsum_geometric_of_lt_one hy.1.le hy.2]
    have : (1 : ℝ) - y ≠ 0 := by linarith [hy.2]
    field_simp
  have h := (hardy_littlewood_nonneg hb hsb hlb).sub_const K
  rw [add_sub_cancel_right] at h
  refine h.congr fun N => ?_
  rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul]
  have : (0 : ℝ) < N + 1 := by positivity
  field_simp
  push_cast
  ring

/-! ### The DLMF statements -/

/-- Abel summability of a real series: the power series converges absolutely on `(0, 1)`, the
Abel sum is real, and the real sums tend to it. -/
theorem abelSum_real {a : ℕ → ℝ} {s : ℂ} (h : AbelSum (fun n => (a n : ℂ)) s) :
    (∀ y ∈ Ioo (0 : ℝ) 1, Summable fun n => a n * y ^ n) ∧ s = (s.re : ℂ) ∧
      Tendsto (fun y => ∑' n, a n * y ^ n) (𝓝[<] 1) (𝓝 s.re) := by
  obtain ⟨f, hconv, hlim⟩ := h
  have hsum : ∀ y ∈ Ioo (0 : ℝ) 1, Summable fun n => a n * y ^ n := by
    intro y hy
    obtain ⟨x, hyx, hx1⟩ : ∃ x : ℝ, y < x ∧ x < 1 :=
      ⟨(y + 1) / 2, by linarith [hy.2], by linarith [hy.2]⟩
    have hx : x ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hy.1], hx1⟩
    obtain ⟨M, -, hM⟩ := bounded_of_tendsto (hconv x hx).tendsto_zero
    have hq0 : 0 ≤ y / x := div_nonneg hy.1.le hx.1.le
    have hq1 : y / x < 1 := (div_lt_one hx.1).mpr hyx
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hq0 hq1).mul_left M)
      fun n => ?_
    have h1 := hM n
    rw [norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hx.1.le] at h1
    rw [norm_mul, norm_pow, Real.norm_of_nonneg hy.1.le, div_pow]
    have hxn : 0 < x ^ n := pow_pos hx.1 n
    calc ‖a n‖ * y ^ n = (‖a n‖ * x ^ n) * (y ^ n / x ^ n) := by field_simp
      _ ≤ M * (y ^ n / x ^ n) :=
          mul_le_mul_of_nonneg_right h1 (div_nonneg (pow_nonneg hy.1.le n) hxn.le)
  have hf : ∀ y ∈ Ioo (0 : ℝ) 1, f y = ((∑' n, a n * y ^ n : ℝ) : ℂ) := fun y hy => by
    have hT := ((Complex.continuous_ofReal.tendsto _).comp
      (hsum y hy).hasSum.tendsto_sum_nat)
    have hC := seriesConverges_iff.mp (hconv y hy)
    refine tendsto_nhds_unique hC (hT.congr fun N => ?_)
    simp [Function.comp]
  have hre := (Complex.continuous_re.tendsto s).comp hlim
  have him := (Complex.continuous_im.tendsto s).comp hlim
  have hev : ∀ᶠ y in 𝓝[<] (1 : ℝ), y ∈ Ioo (0 : ℝ) 1 :=
    Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)
  have him0 : s.im = 0 := by
    refine tendsto_nhds_unique him (tendsto_const_nhds.congr' ?_)
    filter_upwards [hev] with y hy
    simp [Function.comp, hf y hy]
  refine ⟨hsum, Complex.ext (by simp) (by simp [him0]), hre.congr' ?_⟩
  filter_upwards [hev] with y hy
  simp [Function.comp, hf y hy]

/-- **DLMF 1.15.54–1.15.55** (Littlewood's Tauberian theorem): if `∑ aₙ = s (A)` and
`aₙ > −K/n` for `n > 0`, `K > 0`, then `∑ aₙ = s`. -/
theorem dlmf_1_15_55 {a : ℕ → ℝ} {s : ℂ} {K : ℝ} (h : AbelSum (fun n => (a n : ℂ)) s)
    (hK : 0 < K) (ha : ∀ n, 0 < n → -K / n < a n) : SeriesConverges (fun n => (a n : ℂ)) s := by
  obtain ⟨hs, hsre, hl⟩ := abelSum_real h
  rw [hsre]
  refine ((Complex.continuous_ofReal.tendsto _).comp (littlewood hK ha hs hl)).congr fun N => ?_
  simp [partialSum, Function.comp]

/-- **DLMF 1.15.56–1.15.57**, case `aₙ ≥ 0`: if `(1 − x) ∑ aₙ xⁿ → s` as `x → 1−`, then
`(a₀ + ⋯ + aₙ)/(n + 1) → s`. -/
theorem dlmf_1_15_57_nonneg {a : ℕ → ℝ} {s : ℝ} (ha : ∀ n, 0 ≤ a n)
    (hs : ∀ x ∈ Ioo (0 : ℝ) 1, Summable fun n => a n * x ^ n)
    (hl : Tendsto (fun x => (1 - x) * ∑' n, a n * x ^ n) (𝓝[<] 1) (𝓝 s)) :
    Tendsto (fun n : ℕ => (∑ k ∈ range (n + 1), a k) / ((n : ℝ) + 1)) atTop (𝓝 s) :=
  hardy_littlewood_nonneg ha hs hl

/-- **DLMF 1.15.56–1.15.57**, case `|aₙ| ≤ K` (complex coefficients): if
`(1 − x) ∑ aₙ xⁿ → s` as `x → 1−`, then `(a₀ + ⋯ + aₙ)/(n + 1) → s`. -/
theorem dlmf_1_15_57_bounded {a : ℕ → ℂ} {s : ℂ} {K : ℝ} (ha : ∀ n, ‖a n‖ ≤ K)
    (hl : Tendsto (fun x : ℝ => ((1 - x : ℝ) : ℂ) * ∑' n, a n * (x : ℂ) ^ n) (𝓝[<] 1)
      (𝓝 s)) :
    Tendsto (fun n : ℕ => (∑ k ∈ range (n + 1), a k) / ((n : ℂ) + 1)) atTop (𝓝 s) := by
  have hsum : ∀ x ∈ Ioo (0 : ℝ) 1,
      HasSum (fun n => a n * ((x ^ n : ℝ) : ℂ)) (∑' n, a n * (x : ℂ) ^ n) := fun x hx => by
    have hs : Summable fun n => a n * ((x ^ n : ℝ) : ℂ) :=
      Summable.of_norm_bounded ((summable_geometric_of_lt_one hx.1.le hx.2).mul_left K)
        fun n => by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg hx.1.le n)]
          exact mul_le_mul_of_nonneg_right (ha n) (pow_nonneg hx.1.le n)
    have h := hs.hasSum
    rwa [show (∑' n, a n * ((x ^ n : ℝ) : ℂ)) = ∑' n, a n * (x : ℂ) ^ n by
      simp [Complex.ofReal_pow]] at h
  have hev : ∀ᶠ x in 𝓝[<] (1 : ℝ), x ∈ Ioo (0 : ℝ) 1 :=
    Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)
  have hre : Tendsto (fun x => (1 - x) * ∑' n, (a n).re * x ^ n) (𝓝[<] 1) (𝓝 s.re) := by
    refine ((Complex.continuous_re.tendsto s).comp hl).congr' ?_
    filter_upwards [hev] with x hx
    have h1 := ((Complex.hasSum_iff _ _).mp (hsum x hx)).1
    simp only [Complex.re_mul_ofReal] at h1
    simp only [Function.comp, Complex.re_ofReal_mul, h1.tsum_eq]
  have him : Tendsto (fun x => (1 - x) * ∑' n, (a n).im * x ^ n) (𝓝[<] 1) (𝓝 s.im) := by
    refine ((Complex.continuous_im.tendsto s).comp hl).congr' ?_
    filter_upwards [hev] with x hx
    have h1 := ((Complex.hasSum_iff _ _).mp (hsum x hx)).2
    simp only [Complex.im_mul_ofReal] at h1
    simp only [Function.comp, Complex.im_ofReal_mul, h1.tsum_eq]
  have hR := hardy_littlewood_bounded_real (a := fun n => (a n).re)
    (fun n => (Complex.abs_re_le_norm _).trans (ha n)) hre
  have hI := hardy_littlewood_bounded_real (a := fun n => (a n).im)
    (fun n => (Complex.abs_im_le_norm _).trans (ha n)) him
  have h := ((Complex.continuous_ofReal.tendsto _).comp hR).add
    (((Complex.continuous_ofReal.tendsto _).comp hI).mul_const Complex.I)
  rw [Complex.re_add_im] at h
  refine h.congr fun N => ?_
  have e : ((N : ℂ) + 1) = (((N : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
  rw [e]
  apply Complex.ext <;>
    simp only [Function.comp_apply, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.div_ofReal_re, Complex.div_ofReal_im, Complex.re_sum, Complex.im_sum] <;> ring

end Azurite.DLMF
