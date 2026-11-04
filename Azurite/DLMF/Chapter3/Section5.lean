/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter2.Section10
import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue

/-!
# DLMF §3.5(i): trapezoidal rules

* `exists_mem_Ioo_integral_mul_eq`: the weighted mean value theorem with an interior point
  (Mathlib's gives `ξ ∈ [a, b]`; DLMF's `ξ` satisfy `a < ξ < b`).
* 3.5.1: `dlmf_3_5_1`, for `f ∈ C²` on an open set containing `[a, b]`, via
  `∫ f − ½h(f(a) + f(b)) = ∫ ½(x − a)(x − b) f″(x) dx` (an antiderivative identity) and the
  weighted mean value theorem with the one-signed kernel.
* 3.5.2–3.5.3: `trapezoidSum`, `trapError` (`E_n(f)`), `dlmf_3_5_2` (the displayed weights),
  `dlmf_3_5_3` (3.5.1 on each subinterval, the average of the `f″(ξ_k)` by the intermediate value
  theorem, `exists_sum_eq_card_mul`).
* 3.5.4: `dlmf_3_5_4` (explicit: `|E_n(f)| ≤ (b − a) max|f⁽ᵏ⁾| max_{[0,1]}|B_k|/k! · hᵏ` for every
  `k ≥ 1`, odd or even), `dlmf_3_5_4_isBigO`. Proof: the Euler–Maclaurin expansion of order `k` on
  each unit subinterval (`em_iter` of §2.10(i)); the boundary terms telescope to zero because the
  derivatives of `f` are periodic (`periodic_iteratedDeriv`).
* The remark that for `k = ∞` the error is exponentially small in `1/h` is false for general
  `C^∞` functions: see `Section5Smooth` and `docs/dlmf_errata.md`.
-/

open Finset Filter Topology Set MeasureTheory intervalIntegral Asymptotics

namespace Azurite.DLMF

/-! ### A strict weighted mean value theorem -/

/-- **Mean value theorem for integrals with an interior point**: for `f` continuous and a weight
`g ≥ 0` continuous on `[a, b]` and positive on `(a, b)`, `∫ f g = f(ξ) ∫ g` for some
`ξ ∈ (a, b)`. -/
theorem exists_mem_Ioo_integral_mul_eq {f g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hg0 : ∀ x ∈ Icc a b, 0 ≤ g x) (hgpos : ∀ x ∈ Ioo a b, 0 < g x) :
    ∃ ξ ∈ Ioo a b, ∫ x in a..b, f x * g x = f ξ * ∫ x in a..b, g x := by
  have hu : uIcc a b = Icc a b := uIcc_of_le hab.le
  obtain ⟨c, -, hc⟩ := exists_eq_const_mul_intervalIntegral_of_nonneg (μ := volume)
    (hu ▸ hf) ((hu ▸ hg).intervalIntegrable) fun x hx => hg0 x (by
      rw [uIoc_of_le hab.le] at hx; exact ⟨hx.1.le, hx.2⟩)
  set v := f c
  have hgi : 0 < ∫ x in a..b, g x :=
    intervalIntegral_pos_of_pos_on ((hu ▸ hg).intervalIntegrable) hgpos hab
  by_contra hne
  push Not at hne
  have hfv : ∀ x ∈ Ioo a b, f x ≠ v := fun x hx h =>
    hne x hx (by rw [hc, h])
  -- `f − v` has a constant sign on `(a, b)`
  set m := (a + b) / 2
  have hm : m ∈ Ioo a b := ⟨by simp only [m]; linarith, by simp only [m]; linarith⟩
  have hsign : (∀ x ∈ Ioo a b, v < f x) ∨ ∀ x ∈ Ioo a b, f x < v := by
    have hcont : ∀ x ∈ Ioo a b, ContinuousOn f (uIcc m x) := fun x hx =>
      hf.mono (uIcc_subset_Icc (Ioo_subset_Icc_self hm) (Ioo_subset_Icc_self hx))
    have hsub : ∀ x ∈ Ioo a b, uIcc m x ⊆ Ioo a b := fun x hx y hy => by
      rw [Set.mem_uIcc] at hy
      constructor <;> rcases hy with h | h <;> linarith [hm.1, hm.2, hx.1, hx.2, h.1, h.2]
    rcases lt_or_gt_of_ne (hfv m hm) with h | h
    · right
      intro x hx
      by_contra hx'
      push Not at hx'
      obtain ⟨y, hy, hy'⟩ := intermediate_value_uIcc (hcont x hx)
        (show v ∈ uIcc (f m) (f x) from mem_uIcc.mpr (Or.inl ⟨h.le, hx'⟩))
      exact hfv y (hsub x hx hy) hy'
    · left
      intro x hx
      by_contra hx'
      push Not at hx'
      obtain ⟨y, hy, hy'⟩ := intermediate_value_uIcc (hcont x hx)
        (show v ∈ uIcc (f m) (f x) from mem_uIcc.mpr (Or.inr ⟨hx', h.le⟩))
      exact hfv y (hsub x hx hy) hy'
  have hfg : IntervalIntegrable (fun x => f x * g x) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab.le (hf.mul hg)
  have hvg : IntervalIntegrable (fun x => v * g x) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab.le (continuousOn_const.mul hg)
  have hzero : ∫ x in a..b, (f x - v) * g x = 0 := by
    simp only [sub_mul]
    rw [intervalIntegral.integral_sub hfg hvg, intervalIntegral.integral_const_mul, hc, sub_self]
  rcases hsign with h | h
  · have := intervalIntegral_pos_of_pos_on
      (ContinuousOn.intervalIntegrable_of_Icc hab.le (u := fun x => (f x - v) * g x)
        ((hf.sub continuousOn_const).mul hg))
      (fun x hx => mul_pos (sub_pos.mpr (h x hx)) (hgpos x hx)) hab
    linarith
  · have hzero' : ∫ x in a..b, (v - f x) * g x = 0 := by
      rw [show (fun x => (v - f x) * g x) = fun x => -((f x - v) * g x) by ext x; ring,
        intervalIntegral.integral_neg, hzero, neg_zero]
    have := intervalIntegral_pos_of_pos_on
      (ContinuousOn.intervalIntegrable_of_Icc hab.le (u := fun x => (v - f x) * g x)
        ((continuousOn_const.sub hf).mul hg))
      (fun x hx => mul_pos (sub_pos.mpr (h x hx)) (hgpos x hx)) hab
    linarith

/-! ### The elementary trapezoidal rule 3.5.1 -/

/-- **DLMF 3.5.1**: for `f ∈ C²` on an open set containing `[a, b]`, `h = b − a`,
`∫ₐᵇ f = ½h(f(a) + f(b)) − (1/12) h³ f″(ξ)` with `a < ξ < b`. -/
theorem dlmf_3_5_1 {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) {U : Set ℝ} (hU : IsOpen U)
    (hIU : Icc a b ⊆ U) (hf : ContDiffOn ℝ 2 f U) :
    ∃ ξ ∈ Ioo a b, ∫ x in a..b, f x =
      1 / 2 * (b - a) * (f a + f b) - 1 / 12 * (b - a) ^ 3 * deriv (deriv f) ξ := by
  have hd1 : ContDiffOn ℝ 1 (deriv f) U := hf.deriv_of_isOpen hU (by norm_num)
  have hd2 : ContDiffOn ℝ 0 (deriv (deriv f)) U := hd1.deriv_of_isOpen hU (by norm_num)
  have hfd : ∀ x ∈ U, HasDerivAt f (deriv f x) x := fun x hx =>
    ((hf.differentiableOn (by norm_num)) x hx).differentiableAt (hU.mem_nhds hx) |>.hasDerivAt
  have hf'd : ∀ x ∈ U, HasDerivAt (deriv f) (deriv (deriv f) x) x := fun x hx =>
    ((hd1.differentiableOn (by norm_num)) x hx).differentiableAt (hU.mem_nhds hx) |>.hasDerivAt
  have hf2c : ContinuousOn (deriv (deriv f)) (Icc a b) := hd2.continuousOn.mono hIU
  have hfc : ContinuousOn f (Icc a b) := (hf.continuousOn).mono hIU
  -- `φ′ = K f″ − f` with `K(x) = (x − a)(x − b)/2`
  set φ : ℝ → ℝ := fun x => (x - a) * (x - b) / 2 * deriv f x - (x - (a + b) / 2) * f x
  have hφ : ∀ x ∈ uIcc a b, HasDerivAt φ ((x - a) * (x - b) / 2 * deriv (deriv f) x - f x) x := by
    intro x hx
    rw [uIcc_of_le hab.le] at hx
    have h1 : HasDerivAt (fun x => (x - a) * (x - b) / 2) ((2 * x - a - b) / 2) x := by
      have := (((hasDerivAt_id' x).sub_const a).fun_mul
        ((hasDerivAt_id' x).sub_const b)).div_const 2
      convert this using 1; ring
    have h2 : HasDerivAt (fun x => x - (a + b) / 2) 1 x := (hasDerivAt_id x).sub_const _
    have := (h1.mul (hf'd x (hIU hx))).sub (h2.mul (hfd x (hIU hx)))
    convert this using 1
    ring
  have hφi : IntervalIntegrable (fun x => (x - a) * (x - b) / 2 * deriv (deriv f) x - f x)
      volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab.le]
    exact ((ContinuousOn.mul (by fun_prop) hf2c).sub hfc).integrableOn_Icc
  have hFTC := integral_eq_sub_of_hasDerivAt hφ hφi
  have hK : ContinuousOn (fun x => (x - a) * (x - b) / 2) (Icc a b) := by fun_prop
  rw [intervalIntegral.integral_sub (f := fun x => (x - a) * (x - b) / 2 * deriv (deriv f) x)
    (g := f) ((hK.mul hf2c).intervalIntegrable_of_Icc hab.le)
    (hfc.intervalIntegrable_of_Icc hab.le)] at hFTC
  -- the weighted mean value theorem with `g(x) = (x − a)(b − x)/2`
  obtain ⟨ξ, hξ, hmv⟩ := exists_mem_Ioo_integral_mul_eq (f := deriv (deriv f))
    (g := fun x => (x - a) * (b - x) / 2) hab hf2c (by fun_prop)
    (fun x hx => by have := hx.1; have := hx.2; positivity)
    (fun x hx => by have := hx.1; have := hx.2; apply div_pos (mul_pos _ _) two_pos <;> linarith)
  have hKint : ∫ x in a..b, (x - a) * (b - x) / 2 = (b - a) ^ 3 / 12 := by
    have hd : ∀ x ∈ uIcc a b, HasDerivAt (fun x => (b - a) * (x - a) ^ 2 / 4 - (x - a) ^ 3 / 6)
        ((x - a) * (b - x) / 2) x := fun x _ => by
      have := ((((hasDerivAt_id' x).sub_const a).pow 2).const_mul (b - a)).div_const 4 |>.sub
        ((((hasDerivAt_id' x).sub_const a).pow 3).div_const 6)
      convert this using 1; push_cast; ring
    rw [integral_eq_sub_of_hasDerivAt hd
      ((show Continuous fun x : ℝ => (x - a) * (b - x) / 2 by fun_prop).intervalIntegrable _ _)]
    ring
  have hneg : ∫ x in a..b, (x - a) * (x - b) / 2 * deriv (deriv f) x =
      -∫ x in a..b, deriv (deriv f) x * ((x - a) * (b - x) / 2) := by
    rw [← intervalIntegral.integral_neg]; congr 1; ext x; ring
  refine ⟨ξ, hξ, ?_⟩
  rw [hneg, hmv, hKint] at hFTC
  simp only [φ] at hFTC
  linarith

/-! ### The composite trapezoidal rule 3.5.2–3.5.3 -/

/-- The composite trapezoidal sum `h(½f₀ + f₁ + ⋯ + f_{n−1} + ½fₙ)`, `h = (b − a)/n`,
`f_k = f(a + kh)`. -/
noncomputable def trapezoidSum (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) : ℝ :=
  (b - a) / n * (∑ k ∈ range (n + 1), f (a + k * ((b - a) / n)) - f a / 2 -
    f (a + n * ((b - a) / n)) / 2)

/-- The error `E_n(f)` of the composite trapezoidal rule. -/
noncomputable def trapError (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) : ℝ :=
  (∫ x in a..b, f x) - trapezoidSum f a b n

theorem sum_range_avg (g : ℕ → ℝ) (N : ℕ) :
    ∑ i ∈ range N, (g i + g (i + 1)) / 2 = ∑ i ∈ range (N + 1), g i - g 0 / 2 - g N / 2 := by
  induction N with
  | zero => simp; ring
  | succ N ih => rw [sum_range_succ, ih, sum_range_succ (n := N + 1)]; ring

/-- **DLMF 3.5.2**: for `n ≥ 1`, `∫ₐᵇ f = h(½f₀ + f₁ + ⋯ + f_{n−1} + ½fₙ) + E_n(f)`. -/
theorem dlmf_3_5_2 (f : ℝ → ℝ) (a b : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    ∫ x in a..b, f x = (b - a) / n * (1 / 2 * f a + ∑ k ∈ Ico 1 n, f (a + k * ((b - a) / n)) +
      1 / 2 * f b) + trapError f a b n := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hb : a + n * ((b - a) / n) = b := by field_simp; ring
  rw [trapError, trapezoidSum, hb]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [sum_range_succ, sum_range_succ', Finset.sum_Ico_eq_sum_range]
  simp only [Nat.cast_zero, zero_mul, add_zero, add_tsub_cancel_right]
  rw [hb]
  have : ∀ k ∈ range m, f (a + ((k + 1 : ℕ) : ℝ) * ((b - a) / (m + 1 : ℕ))) =
      f (a + ((1 + k : ℕ) : ℝ) * ((b - a) / (m + 1 : ℕ))) := fun k _ => by
    congr 3; push_cast; ring
  rw [sum_congr rfl this]
  ring

/-- `Σ_{k<n} F(ξ_k) = n F(ξ)` for some `ξ ∈ (a, b)` when all `ξ_k ∈ (a, b)` and `F` is continuous
on `[a, b]`. -/
theorem exists_sum_eq_card_mul {F : ℝ → ℝ} {a b : ℝ} (hF : ContinuousOn F (Icc a b)) {n : ℕ}
    (hn : 1 ≤ n) {ξ : ℕ → ℝ} (hξ : ∀ k ∈ range n, ξ k ∈ Ioo a b) :
    ∃ η ∈ Ioo a b, ∑ k ∈ range n, F (ξ k) = n * F η := by
  have hne : (range n).Nonempty := nonempty_range_iff.mpr (by omega)
  obtain ⟨kmin, hkmin, hmin⟩ := (range n).exists_min_image (fun k => F (ξ k)) hne
  obtain ⟨kmax, hkmax, hmax⟩ := (range n).exists_max_image (fun k => F (ξ k)) hne
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set avg := (∑ k ∈ range n, F (ξ k)) / n
  have hlo : F (ξ kmin) ≤ avg := by
    rw [le_div_iff₀ hn0]
    calc F (ξ kmin) * n = ∑ k ∈ range n, F (ξ kmin) := by simp [mul_comm]
      _ ≤ _ := sum_le_sum hmin
  have hhi : avg ≤ F (ξ kmax) := by
    rw [div_le_iff₀ hn0]
    calc ∑ k ∈ range n, F (ξ k) ≤ ∑ k ∈ range n, F (ξ kmax) := sum_le_sum hmax
      _ = F (ξ kmax) * n := by simp [mul_comm]
  have hsub : uIcc (ξ kmin) (ξ kmax) ⊆ Ioo a b := fun y hy => by
    rw [Set.mem_uIcc] at hy
    have h1 := hξ kmin hkmin; have h2 := hξ kmax hkmax
    constructor <;> rcases hy with h | h <;> linarith [h1.1, h1.2, h2.1, h2.2, h.1, h.2]
  obtain ⟨η, hη, hη'⟩ := intermediate_value_uIcc (hF.mono (hsub.trans Ioo_subset_Icc_self))
    (show avg ∈ uIcc (F (ξ kmin)) (F (ξ kmax)) from Set.mem_uIcc.mpr (Or.inl ⟨hlo, hhi⟩))
  refine ⟨η, hsub hη, ?_⟩
  rw [hη']; simp only [avg]; field_simp

/-- **DLMF 3.5.3**: for `f ∈ C²` on an open set containing `[a, b]` and `n ≥ 1`,
`E_n(f) = −((b − a)/12) h² f″(ξ)` with `a < ξ < b`, `h = (b − a)/n`. -/
theorem dlmf_3_5_3 {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) {n : ℕ} (hn : 1 ≤ n) {U : Set ℝ}
    (hU : IsOpen U) (hIU : Icc a b ⊆ U) (hf : ContDiffOn ℝ 2 f U) :
    ∃ ξ ∈ Ioo a b, trapError f a b n = -((b - a) / 12) * ((b - a) / n) ^ 2 * deriv (deriv f) ξ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set h := (b - a) / n with hh
  have hpos : 0 < h := div_pos (by linarith) hn0
  set x : ℕ → ℝ := fun k => a + k * h
  have hxn : x n = b := by simp only [x, h]; field_simp; ring
  have hxs : ∀ k : ℕ, x (k + 1) = x k + h := fun k => by simp only [x]; push_cast; ring
  have hxI : ∀ k ≤ n, x k ∈ Icc a b := fun k hk => by
    have hk' : (k : ℝ) ≤ n := by exact_mod_cast hk
    refine ⟨by simp only [x]; nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)], ?_⟩
    rw [← hxn]; simp only [x]; nlinarith
  have hsubI : ∀ k ∈ range n, Icc (x k) (x (k + 1)) ⊆ Icc a b := fun k hk =>
    Icc_subset_Icc (hxI k (by have := mem_range.mp hk; omega)).1
      (hxI (k + 1) (by have := mem_range.mp hk; omega)).2
  have hloc : ∀ k ∈ range n, ∃ ξ ∈ Ioo (x k) (x (k + 1)), ∫ t in x k..x (k + 1), f t =
      1 / 2 * h * (f (x k) + f (x (k + 1))) - 1 / 12 * h ^ 3 * deriv (deriv f) ξ := fun k hk => by
    obtain ⟨ξ, hξ, he⟩ := dlmf_3_5_1 (by rw [hxs]; linarith) hU ((hsubI k hk).trans hIU) hf
    refine ⟨ξ, hξ, ?_⟩
    rw [he, hxs, add_sub_cancel_left]
  choose! ξ hξ hloc using hloc
  have hfc : ContinuousOn f (Icc a b) := hf.continuousOn.mono hIU
  have hint : ∫ t in a..b, f t = ∑ k ∈ range n, ∫ t in x k..x (k + 1), f t := by
    rw [sum_integral_adjacent_intervals fun k hk => (hfc.mono (hsubI k (mem_range.mpr hk))
      |>.intervalIntegrable_of_Icc (by rw [hxs]; linarith))]
    simp only [x, Nat.cast_zero, zero_mul, add_zero]
    rw [← hxn]
  have hξI : ∀ k ∈ range n, ξ k ∈ Ioo a b := fun k hk =>
    ⟨lt_of_le_of_lt (hxI k (by have := mem_range.mp hk; omega)).1 (hξ k hk).1,
      lt_of_lt_of_le (hξ k hk).2 (hxI (k + 1) (by have := mem_range.mp hk; omega)).2⟩
  have hd2 : ContinuousOn (deriv (deriv f)) (Icc a b) :=
    ((hf.deriv_of_isOpen hU (by norm_num : ((1 : ℕ) : WithTop ℕ∞) + 1 ≤ 2)).deriv_of_isOpen hU
      (by norm_num : ((0 : ℕ) : WithTop ℕ∞) + 1 ≤ 1)).continuousOn.mono hIU
  obtain ⟨η, hη, hsum⟩ := exists_sum_eq_card_mul hd2 hn hξI
  refine ⟨η, hη, ?_⟩
  have hT : trapezoidSum f a b n = ∑ k ∈ range n, 1 / 2 * h * (f (x k) + f (x (k + 1))) := by
    rw [trapezoidSum, ← mul_sum, show ∑ k ∈ range n, (f (x k) + f (x (k + 1))) =
      2 * ∑ k ∈ range n, (f (x k) + f (x (k + 1))) / 2 by rw [mul_sum]; congr 1; ext k; ring,
      sum_range_avg (fun k => f (x k)) n]
    simp only [x, Nat.cast_zero, zero_mul, add_zero]
    ring
  rw [trapError, hint, hT, sum_congr rfl hloc, sum_sub_distrib,
    ← Finset.mul_sum (range n) (fun k => deriv (deriv f) (ξ k)) (1 / 12 * h ^ 3), hsum]
  have : (n : ℝ) * h = b - a := by simp only [h]; field_simp
  rw [show 1 / 12 * h ^ 3 * (n * deriv (deriv f) η) = (n * h) / 12 * h ^ 2 * deriv (deriv f) η by
    ring, this]
  ring

/-! ### Periodic functions 3.5.4 -/

/-- The derivatives of a periodic function are periodic. -/
theorem periodic_iteratedDeriv {f : ℝ → ℝ} {P : ℝ} (hp : Function.Periodic f P) :
    ∀ l, Function.Periodic (iteratedDeriv l f) P
  | 0 => by simpa using hp
  | l + 1 => fun x => by
    rw [iteratedDeriv_succ, ← deriv_comp_add_const]
    congr 1
    exact funext (periodic_iteratedDeriv hp l)

/-- **DLMF 3.5.4**: if `f ∈ Cᵏ(ℝ)`, `k ≥ 1`, is periodic with period `b − a`, then
`|E_n(f)| ≤ C hᵏ` for all `n ≥ 1`, `h = (b − a)/n`, with
`C = (b − a) max_{[a,b]} |f⁽ᵏ⁾| max_{[0,1]} |B_k| / k!`. Proof: the Euler–Maclaurin expansion of
order `k` on each `[a + ih, a + (i+1)h]` (`em_iter`); by periodicity the boundary terms telescope
to zero. -/
theorem dlmf_3_5_4 {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) {k : ℕ} (hk : 1 ≤ k)
    (hf : ContDiff ℝ k f) (hp : Function.Periodic f (b - a)) :
    ∃ C, ∀ n : ℕ, 1 ≤ n → |trapError f a b n| ≤ C * ((b - a) / n) ^ k := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc a b)
    (hf.continuous_iteratedDeriv k le_rfl).continuousOn
  obtain ⟨β, hβ⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0 : ℝ) 1)
    (continuous_bernoulliFun (k := k)).continuousOn
  refine ⟨(b - a) * (M * β / k.factorial), fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set h := (b - a) / n with hh
  have hpos : 0 < h := div_pos (by linarith) hn0
  have hnh : (n : ℝ) * h = b - a := by simp only [h]; field_simp
  set D : ℕ → ℝ → ℝ := fun l s => h ^ l * iteratedDeriv l f (a + s * h)
  have hd : ∀ l < k, ∀ s, HasDerivAt (D l) (D (l + 1) s) s := fun l hl s => by
    have hdiff := hf.differentiable_iteratedDeriv l (by exact_mod_cast hl)
    have := ((hdiff (a + s * h)).hasDerivAt.comp s
      (((hasDerivAt_id' s).mul_const h).const_add a)).const_mul (h ^ l)
    convert this using 1
    · simp only [D]; rfl
    · simp only [D, iteratedDeriv_succ]; ring
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM a ⟨le_rfl, hab.le⟩)
  have hβ0 : 0 ≤ β := (norm_nonneg _).trans (hβ 0 ⟨le_rfl, zero_le_one⟩)
  have hDc : Continuous (D k) := by
    simp only [D]
    exact continuous_const.mul ((hf.continuous_iteratedDeriv k le_rfl).comp (by fun_prop))
  -- Euler–Maclaurin on each unit interval
  have hunit : ∀ i ∈ range n, ∫ s in (i : ℝ)..(i : ℝ) + 1, D 0 s =
      (D 0 i + D 0 ((i : ℝ) + 1)) / 2 +
        ∑ j ∈ range (k - 1), (-1) ^ (j + 1) * ((bernoulli (j + 2) : ℝ) / ((j + 2).factorial : ℝ)) *
          (D (j + 1) ((i : ℝ) + 1) - D (j + 1) i) +
        (-1) ^ k * ∫ s in (i : ℝ)..(i : ℝ) + 1,
          D k s * (bernoulliFun k (s - i) / (k.factorial : ℝ)) :=
    fun i _ => em_iter hk (fun l hl s _ => hd l hl s) (hDc.intervalIntegrable _ _)
  have hcast : ∀ i : ℕ, ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := fun i => by push_cast; ring
  -- the pieces
  have hint : ∑ i ∈ range n, ∫ s in (i : ℝ)..(i : ℝ) + 1, D 0 s = ∫ s in (0 : ℝ)..n, D 0 s := by
    have := sum_integral_adjacent_intervals (a := fun i : ℕ => (i : ℝ)) (n := n) (f := D 0)
      (μ := volume) fun i _ => ((hd 0 (by omega) |> fun h0 =>
        continuous_iff_continuousAt.mpr fun s => (h0 s).continuousAt)).intervalIntegrable _ _
    simpa [hcast] using this
  have htel : ∀ j ∈ range (k - 1), ∑ i ∈ range n, (D (j + 1) ((i : ℝ) + 1) - D (j + 1) i) = 0 :=
    fun j _ => by
      have := sum_range_sub (fun i : ℕ => D (j + 1) i) n
      simp only [hcast] at this
      rw [this]
      simp only [D, Nat.cast_zero, zero_mul, add_zero, hnh]
      rw [show a + (b - a) = a + (b - a) from rfl, periodic_iteratedDeriv hp (j + 1) a, sub_self]
  have hbound : ∀ i ∈ range n, |∫ s in (i : ℝ)..(i : ℝ) + 1, D k s *
      (bernoulliFun k (s - i) / (k.factorial : ℝ))| ≤ h ^ k * (M * β / k.factorial) :=
    fun i hi => by
      have hi' : (i : ℝ) + 1 ≤ n := by exact_mod_cast mem_range.mp hi
      have := norm_integral_le_of_norm_le_const (a := (i : ℝ)) (b := (i : ℝ) + 1)
        (C := h ^ k * (M * β / k.factorial))
        (f := fun s => D k s * (bernoulliFun k (s - i) / (k.factorial : ℝ))) fun s hs => by
          rw [uIoc_of_le (by linarith)] at hs
          have h0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
          have hx : a + s * h ∈ Icc a b := by
            constructor
            · nlinarith [mul_nonneg (h0.trans hs.1.le) hpos.le]
            · nlinarith [mul_le_mul_of_nonneg_right (hs.2.trans hi') hpos.le]
          have hb := hβ (s - i) ⟨by linarith [hs.1], by linarith [hs.2]⟩
          have hm := hM (a + s * h) hx
          rw [Real.norm_eq_abs] at hb hm ⊢
          simp only [D]
          rw [abs_mul, abs_mul, abs_div, abs_of_pos (pow_pos hpos k), Nat.abs_cast]
          have hkf : (0 : ℝ) < k.factorial := by positivity
          calc h ^ k * |iteratedDeriv k f (a + s * h)| * (|bernoulliFun k (s - i)| / k.factorial)
              ≤ h ^ k * M * (β / k.factorial) :=
                mul_le_mul (mul_le_mul_of_nonneg_left hm (pow_pos hpos k).le)
                  (div_le_div_of_nonneg_right hb hkf.le) (by positivity)
                  (mul_nonneg (pow_pos hpos k).le hM0)
            _ = h ^ k * (M * β / k.factorial) := by ring
      simpa using this
  -- assemble
  have hE : trapError f a b n = h * (-1) ^ k * ∑ i ∈ range n,
      ∫ s in (i : ℝ)..(i : ℝ) + 1, D k s * (bernoulliFun k (s - i) / (k.factorial : ℝ)) := by
    have hsum := sum_congr rfl hunit
    have hB : ∑ i ∈ range n, ∑ j ∈ range (k - 1), (-1) ^ (j + 1) *
        ((bernoulli (j + 2) : ℝ) / ((j + 2).factorial : ℝ)) *
        (D (j + 1) ((i : ℝ) + 1) - D (j + 1) i) = 0 := by
      rw [sum_comm]
      exact sum_eq_zero fun j hj => by rw [← mul_sum, htel j hj, mul_zero]
    rw [hint, sum_add_distrib, sum_add_distrib, hB, add_zero, ← mul_sum] at hsum
    have havg := sum_range_avg (fun i => D 0 i) n
    simp only [hcast] at havg
    rw [havg] at hsum
    have hI : ∫ x in a..b, f x = h * ∫ s in (0 : ℝ)..n, D 0 s := by
      have := intervalIntegral.integral_comp_mul_add (a := (0 : ℝ)) (b := n) (f := f) hpos.ne' a
      simp only [mul_zero, zero_add] at this
      rw [show h * n + a = b by rw [mul_comm, hnh]; ring] at this
      simp only [D, pow_zero, one_mul, iteratedDeriv_zero]
      rw [show (fun s : ℝ => f (a + s * h)) = fun s => f (h * s + a) by ext s; ring_nf, this,
        smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
    rw [trapError, hI, hsum, trapezoidSum]
    simp only [D, pow_zero, one_mul, iteratedDeriv_zero, Nat.cast_zero, zero_mul, add_zero]
    ring
  rw [hE, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one, abs_of_pos hpos]
  calc h * |∑ i ∈ range n, ∫ s in (i : ℝ)..(i : ℝ) + 1, D k s *
        (bernoulliFun k (s - i) / (k.factorial : ℝ))|
      ≤ h * ∑ i ∈ range n, h ^ k * (M * β / k.factorial) :=
        mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs _ _).trans (sum_le_sum hbound)) hpos.le
    _ = (n * h) * (M * β / k.factorial) * h ^ k := by rw [sum_const, card_range, nsmul_eq_mul]; ring
    _ = _ := by rw [hnh]

/-- **DLMF 3.5.4** in `O`-form: `E_n(f) = O(hᵏ)` as `n → ∞`, `h = (b − a)/n`. -/
theorem dlmf_3_5_4_isBigO {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) {k : ℕ} (hk : 1 ≤ k)
    (hf : ContDiff ℝ k f) (hp : Function.Periodic f (b - a)) :
    (fun n : ℕ => trapError f a b n) =O[atTop] fun n : ℕ => ((b - a) / n) ^ k := by
  obtain ⟨C, hC⟩ := dlmf_3_5_4 hab hk hf hp
  refine IsBigO.of_bound C (eventually_atTop.mpr ⟨1, fun n hn => ?_⟩)
  have hnn : 0 ≤ ((b - a) / (n : ℝ)) ^ k :=
    pow_nonneg (div_nonneg (sub_nonneg.mpr hab.le) (Nat.cast_nonneg n)) k
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn]
  exact hC n hn

end Azurite.DLMF
