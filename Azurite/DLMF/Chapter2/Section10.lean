/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section1
import Mathlib.NumberTheory.ZetaValues
import Mathlib.MeasureTheory.Function.Floor

/-!
# DLMF §2.10(i): the Euler–Maclaurin formula 2.10.1

* `periodicBernoulli k x = B̃ₖ(x) = Bₖ(x − ⌊x⌋)` (Mathlib's `bernoulliFun` and `bernoulli`, with
  `B₁ = −1/2`, as in §24.2).
* 2.10.1 (`dlmf_2_10_1`): for integers `a < n`, `m > 0`, and `f` with derivatives
  `f′, …, f^{(2m)}` on `[a, n]` (`D k = f^{(k)}`), `f^{(2m)}` absolutely integrable over `[a, n]`,
  `∑_{j=a}^{n} f(j) = ∫_a^n f + ½f(a) + ½f(n) + ∑_{s=1}^{m−1} B_{2s}/(2s)! (f^{(2s−1)}(n) −
  f^{(2s−1)}(a)) + ∫_a^n (B_{2m} − B̃_{2m}(x))/(2m)! f^{(2m)}(x) dx`.

The proof integrates by parts on each unit interval (`em_base`, `em_step`, iterated in `em_iter`),
drops the odd Bernoulli numbers (`em_alt_sum`), and sums over the intervals (`em_sum`), for any
real starting point `t` with the periodic function `B̃(x − t)`.
-/

open Filter Topology Set MeasureTheory intervalIntegral Finset
open scoped Nat

namespace Azurite.DLMF

/-- **DLMF §2.10(i)**: the Bernoulli periodic function `B̃ₖ(x) = Bₖ(x − ⌊x⌋)`. -/
noncomputable def periodicBernoulli (k : ℕ) (x : ℝ) : ℝ := bernoulliFun k (Int.fract x)

theorem periodicBernoulli_bound (k : ℕ) : ∃ C, ∀ x, |bernoulliFun k (Int.fract x)| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuous_bernoulliFun k).continuousOn (s := Icc (0 : ℝ) 1)
  exact ⟨C, fun x => hC _ ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩⟩

/-- `x ↦ h(x) B̃ₖ(x − t)` is integrable where `h` is. -/
theorem IntervalIntegrable.mul_periodicBernoulli {h : ℝ → ℝ} {a b : ℝ}
    (hh : IntervalIntegrable h volume a b) (k : ℕ) (t c : ℝ) :
    IntervalIntegrable (fun x => h x * (bernoulliFun k (Int.fract (x - t)) / c)) volume a b := by
  obtain ⟨C, hC⟩ := periodicBernoulli_bound k
  have hm : AEStronglyMeasurable (fun x : ℝ => bernoulliFun k (Int.fract (x - t)) / c) volume :=
    (((continuous_bernoulliFun k).measurable.comp
      (measurable_fract.comp (measurable_id.sub_const t))).div_const c).aestronglyMeasurable
  refine ⟨hh.1.mul_bdd hm.restrict (c := C / |c|) (Eventually.of_forall fun x => ?_),
    hh.2.mul_bdd hm.restrict (c := C / |c|) (Eventually.of_forall fun x => ?_)⟩ <;>
  · rw [Real.norm_eq_abs, abs_div]
    exact div_le_div_of_nonneg_right (hC _) (abs_nonneg c)

section EulerMaclaurin

variable {D : ℕ → ℝ → ℝ} {t : ℝ}

theorem hasDerivAt_bernoulliFun_sub (k : ℕ) (t x : ℝ) :
    HasDerivAt (fun y => bernoulliFun (k + 1) (y - t) / ((k + 1)! : ℝ))
      (bernoulliFun k (x - t) / (k ! : ℝ)) x := by
  have h := ((hasDerivAt_bernoulliFun (k + 1) (x - t)).comp x
    ((hasDerivAt_id x).sub_const t)).div_const ((k + 1)! : ℝ)
  convert h using 1
  · rfl
  · rw [Nat.add_sub_cancel, Nat.factorial_succ]
    push_cast
    have : ((k ! : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    field_simp

theorem continuous_bernoulliFun_sub_div (k : ℕ) (t c : ℝ) :
    Continuous (fun x => bernoulliFun k (x - t) / c) :=
  ((continuous_bernoulliFun k).comp (continuous_id.sub continuous_const)).div_const c

/-- One integration by parts: `∫ f^{(k)} Bₖ(x−t)/k! = B_{k+1}/(k+1)! Δf^{(k)} −
∫ f^{(k+1)} B_{k+1}(x−t)/(k+1)!` over `[t, t+1]`, `k ≥ 1`. -/
theorem em_step {k : ℕ} (hk : 1 ≤ k) (hd : ∀ x ∈ uIcc t (t + 1), HasDerivAt (D k) (D (k + 1) x) x)
    (hi : IntervalIntegrable (D (k + 1)) volume t (t + 1)) :
    ∫ x in t..t + 1, D k x * (bernoulliFun k (x - t) / (k ! : ℝ)) =
      (bernoulli (k + 1) : ℝ) / ((k + 1)! : ℝ) * (D k (t + 1) - D k t) -
        ∫ x in t..t + 1, D (k + 1) x * (bernoulliFun (k + 1) (x - t) / ((k + 1)! : ℝ)) := by
  rw [integral_mul_deriv_eq_deriv_mul hd (fun x _ => hasDerivAt_bernoulliFun_sub k t x) hi
    ((continuous_bernoulliFun_sub_div k t _).intervalIntegrable _ _)]
  have h1 : bernoulliFun (k + 1) (t + 1 - t) = bernoulli (k + 1) := by
    rw [add_sub_cancel_left, bernoulliFun_endpoints_eq_of_ne_one (by omega),
      bernoulliFun_eval_zero]
  have h0 : bernoulliFun (k + 1) (t - t) = bernoulli (k + 1) := by
    rw [sub_self, bernoulliFun_eval_zero]
  rw [h1, h0]
  ring

/-- The first integration by parts: `∫ f = ½(f(t) + f(t+1)) − ∫ f′ B₁(x−t)`. -/
theorem em_base (hd : ∀ x ∈ uIcc t (t + 1), HasDerivAt (D 0) (D 1 x) x)
    (hi : IntervalIntegrable (D 1) volume t (t + 1)) :
    ∫ x in t..t + 1, D 0 x = (D 0 t + D 0 (t + 1)) / 2 -
      ∫ x in t..t + 1, D 1 x * (bernoulliFun 1 (x - t) / ((1 : ℕ)! : ℝ)) := by
  have h := integral_mul_deriv_eq_deriv_mul hd (fun x _ => hasDerivAt_bernoulliFun_sub 0 t x) hi
    ((continuous_bernoulliFun_sub_div 0 t _).intervalIntegrable _ _)
  simp only [bernoulliFun_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one,
    zero_add] at h
  rw [h]
  simp only [bernoulliFun_one, Nat.factorial_one, Nat.cast_one, div_one]
  ring

theorem continuousOn_of_hasDerivAt {f f' : ℝ → ℝ} {s : Set ℝ}
    (h : ∀ x ∈ s, HasDerivAt f (f' x) x) : ContinuousOn f s :=
  fun x hx => (h x hx).continuousAt.continuousWithinAt

/-- The iterated integrations by parts on `[t, t+1]`, up to order `K`. -/
theorem em_iter {K : ℕ} (hK : 1 ≤ K)
    (hd : ∀ k < K, ∀ x ∈ uIcc t (t + 1), HasDerivAt (D k) (D (k + 1) x) x)
    (hi : IntervalIntegrable (D K) volume t (t + 1)) :
    ∫ x in t..t + 1, D 0 x = (D 0 t + D 0 (t + 1)) / 2 +
      ∑ i ∈ range (K - 1), (-1) ^ (i + 1) * ((bernoulli (i + 2) : ℝ) / ((i + 2)! : ℝ)) *
        (D (i + 1) (t + 1) - D (i + 1) t) +
      (-1) ^ K * ∫ x in t..t + 1, D K x * (bernoulliFun K (x - t) / (K ! : ℝ)) := by
  induction K, hK using Nat.le_induction with
  | base =>
    rw [em_base (hd 0 one_pos) hi]
    simp
    ring
  | succ K hK ih =>
    have hiK : IntervalIntegrable (D K) volume t (t + 1) :=
      (continuousOn_of_hasDerivAt (hd K (by omega))).intervalIntegrable
    rw [ih (fun k hk => hd k (by omega)) hiK, em_step hK (hd K (by omega)) hi,
      show K + 1 - 1 = K - 1 + 1 by omega, sum_range_succ, show K - 1 + 2 = K + 1 by omega,
      show K - 1 + 1 = K by omega]
    ring

/-- The odd Bernoulli numbers drop out. -/
theorem em_alt_sum (Δ : ℕ → ℝ) (M : ℕ) :
    ∑ i ∈ range (2 * M + 1), (-1) ^ (i + 1) * ((bernoulli (i + 2) : ℝ) / ((i + 2)! : ℝ)) *
        Δ (i + 1) =
      -∑ s ∈ range (M + 1), (bernoulli (2 * s + 2) : ℝ) / ((2 * s + 2)! : ℝ) * Δ (2 * s + 1) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show 2 * (M + 1) + 1 = 2 * M + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ (n := M + 1)]
    have hodd : (bernoulli (2 * M + 1 + 2) : ℝ) = 0 := by
      rw [bernoulli_eq_zero_of_odd ⟨M + 1, by ring⟩ (by omega), Rat.cast_zero]
    rw [hodd, show 2 * M + 1 + 1 + 2 = 2 * (M + 1) + 2 by ring,
      show 2 * M + 1 + 1 + 1 = 2 * (M + 1) + 1 by ring,
      show ((-1 : ℝ)) ^ (2 * (M + 1) + 1) = -1 by rw [pow_succ, pow_mul]; norm_num]
    ring

/-- The Euler–Maclaurin formula on one unit interval, with `2M + 2` derivatives. -/
theorem em_unit (M : ℕ)
    (hd : ∀ k < 2 * M + 2, ∀ x ∈ uIcc t (t + 1), HasDerivAt (D k) (D (k + 1) x) x)
    (hi : IntervalIntegrable (D (2 * M + 2)) volume t (t + 1)) :
    ∫ x in t..t + 1, D 0 x = (D 0 t + D 0 (t + 1)) / 2 -
      ∑ s ∈ range (M + 1), (bernoulli (2 * s + 2) : ℝ) / ((2 * s + 2)! : ℝ) *
        (D (2 * s + 1) (t + 1) - D (2 * s + 1) t) +
      ∫ x in t..t + 1, D (2 * M + 2) x *
        (bernoulliFun (2 * M + 2) (x - t) / ((2 * M + 2)! : ℝ)) := by
  rw [em_iter (by omega) hd hi, show 2 * M + 2 - 1 = 2 * M + 1 by omega,
    em_alt_sum (fun k => D k (t + 1) - D k t) M,
    show ((-1 : ℝ)) ^ (2 * M + 2) = 1 by
      rw [show 2 * M + 2 = 2 * (M + 1) by ring, pow_mul]; norm_num]
  ring

/-- On `(t + i, t + i + 1)`, `B̃(x − t) = B(x − t − i)`. -/
theorem integral_fract_unit (h : ℝ → ℝ) (k : ℕ) (c : ℝ) (i : ℕ) :
    ∫ x in t + i..t + i + 1, h x * (bernoulliFun k (Int.fract (x - t)) / c) =
      ∫ x in t + i..t + i + 1, h x * (bernoulliFun k (x - (t + i)) / c) := by
  rw [integral_of_le (by linarith), integral_of_le (by linarith),
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  have hf : Int.fract (x - t) = x - (t + i) := by
    rw [Int.fract_eq_iff]
    refine ⟨by linarith [hx.1], by linarith [hx.2], i, ?_⟩
    push_cast
    ring
  rw [hf]

theorem sum_avg (f : ℝ → ℝ) (t : ℝ) (N : ℕ) :
    ∑ i ∈ range N, (f (t + i) + f (t + i + 1)) / 2 =
      ∑ i ∈ range (N + 1), f (t + i) - f t / 2 - f (t + N) / 2 := by
  induction N with
  | zero =>
    simp
    ring
  | succ N ih =>
    rw [sum_range_succ, ih, sum_range_succ (n := N + 1)]
    push_cast
    ring_nf

/-- The Euler–Maclaurin formula on `[t, t + N]`, `2M + 2` derivatives, `B̃(x − t)`. -/
theorem em_sum (M N : ℕ)
    (hd : ∀ k < 2 * M + 2, ∀ x ∈ Icc t (t + N), HasDerivAt (D k) (D (k + 1) x) x)
    (hi : IntervalIntegrable (D (2 * M + 2)) volume t (t + N)) :
    ∑ i ∈ range (N + 1), D 0 (t + i) = (∫ x in t..t + N, D 0 x) + D 0 t / 2 + D 0 (t + N) / 2 +
      ∑ s ∈ range (M + 1), (bernoulli (2 * s + 2) : ℝ) / ((2 * s + 2)! : ℝ) *
        (D (2 * s + 1) (t + N) - D (2 * s + 1) t) -
      ∫ x in t..t + N, D (2 * M + 2) x *
        (bernoulliFun (2 * M + 2) (Int.fract (x - t)) / ((2 * M + 2)! : ℝ)) := by
  have hsub : ∀ i < N, uIcc (t + i) (t + i + 1) ⊆ Icc t (t + N) := by
    intro i hi x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    have : (i : ℝ) + 1 ≤ N := by exact_mod_cast hi
    exact ⟨by linarith [hx.1, (Nat.cast_nonneg i : (0 : ℝ) ≤ i)], by linarith [hx.2]⟩
  have hN : t ≤ t + N := by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hiu : ∀ i < N, IntervalIntegrable (D (2 * M + 2)) volume (t + i) (t + i + 1) := fun i h =>
    hi.mono_set (by rw [Set.uIcc_of_le hN]; exact hsub i h)
  have hunit : ∀ i < N, ∫ x in t + i..t + i + 1, D 0 x =
      (D 0 (t + i) + D 0 (t + i + 1)) / 2 -
        ∑ s ∈ range (M + 1), (bernoulli (2 * s + 2) : ℝ) / ((2 * s + 2)! : ℝ) *
          (D (2 * s + 1) (t + i + 1) - D (2 * s + 1) (t + i)) +
        ∫ x in t + i..t + i + 1, D (2 * M + 2) x *
          (bernoulliFun (2 * M + 2) (Int.fract (x - t)) / ((2 * M + 2)! : ℝ)) := by
    intro i h
    rw [integral_fract_unit]
    exact em_unit M (fun k hk x hx => hd k hk x (hsub i h hx)) (hiu i h)
  have hpts : ∀ k : ℕ, t + ((k + 1 : ℕ) : ℝ) = t + k + 1 := fun k => by push_cast; ring
  have hint0 : ∑ i ∈ range N, ∫ x in t + i..t + i + 1, D 0 x = ∫ x in t..t + N, D 0 x := by
    have := sum_integral_adjacent_intervals (a := fun k : ℕ => t + k) (n := N) (f := D 0)
      (μ := volume) fun k hk => (continuousOn_of_hasDerivAt (fun x hx => hd 0 (by omega) x
        (hsub k hk (by rw [hpts k] at hx; exact hx)))).intervalIntegrable
    simp only [Nat.cast_zero, add_zero, hpts] at this
    exact this
  have hint1 : ∑ i ∈ range N, ∫ x in t + i..t + i + 1, D (2 * M + 2) x *
      (bernoulliFun (2 * M + 2) (Int.fract (x - t)) / ((2 * M + 2)! : ℝ)) =
      ∫ x in t..t + N, D (2 * M + 2) x *
        (bernoulliFun (2 * M + 2) (Int.fract (x - t)) / ((2 * M + 2)! : ℝ)) := by
    have := sum_integral_adjacent_intervals (a := fun k : ℕ => t + k) (n := N)
      (f := fun x => D (2 * M + 2) x *
        (bernoulliFun (2 * M + 2) (Int.fract (x - t)) / ((2 * M + 2)! : ℝ)))
      (μ := volume) fun k hk => by
        rw [hpts k]
        exact IntervalIntegrable.mul_periodicBernoulli (hiu k hk) _ t _
    simp only [Nat.cast_zero, add_zero, hpts] at this
    exact this
  have htel : ∀ s, ∑ i ∈ range N, (D (2 * s + 1) (t + i + 1) - D (2 * s + 1) (t + i)) =
      D (2 * s + 1) (t + N) - D (2 * s + 1) t := by
    intro s
    have := sum_range_sub (fun i : ℕ => D (2 * s + 1) (t + i)) N
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero, ← add_assoc] at this
    exact this
  have hsum := sum_congr rfl fun i hi => hunit i (mem_range.mp hi)
  rw [hint0, sum_add_distrib, sum_sub_distrib, hint1, sum_avg (D 0) t N, sum_comm] at hsum
  simp only [← mul_sum, htel] at hsum
  linarith

end EulerMaclaurin

theorem sum_Icc_int_eq (f : ℤ → ℝ) (a : ℤ) (N : ℕ) :
    ∑ j ∈ Finset.Icc a (a + N), f j = ∑ i ∈ range (N + 1), f (a + i) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ← ih, show a + ((N + 1 : ℕ) : ℤ) = a + N + 1 by push_cast; ring,
      ← Finset.insert_Icc_right_eq_Icc_add_one (by omega), sum_insert (by simp)]
    ring

theorem sum_Icc_one_eq_sum_range_real (F : ℕ → ℝ) (n : ℕ) :
    ∑ r ∈ Finset.Icc 1 n, F r = ∑ i ∈ range n, F (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, sum_range_succ]

/-- **DLMF 2.10.1** (Euler–Maclaurin): for integers `a < n`, `m > 0`, and `f = D 0` with
derivatives `f^{(k)} = D k` on `[a, n]` up to order `2m`, `f^{(2m)}` absolutely integrable over
`[a, n]`, `∑_{j=a}^{n} f(j) = ∫_a^n f + ½f(a) + ½f(n) + ∑_{s=1}^{m−1} B_{2s}/(2s)! (f^{(2s−1)}(n) −
f^{(2s−1)}(a)) + ∫_a^n (B_{2m} − B̃_{2m}(x))/(2m)! f^{(2m)}(x) dx`. -/
theorem dlmf_2_10_1 {a n : ℤ} (han : a < n) {m : ℕ} (hm : 0 < m) {D : ℕ → ℝ → ℝ}
    (hd : ∀ k < 2 * m, ∀ x ∈ Icc (a : ℝ) n, HasDerivAt (D k) (D (k + 1) x) x)
    (hi : IntervalIntegrable (D (2 * m)) volume a n) :
    ∑ j ∈ Finset.Icc a n, D 0 j = (∫ x in (a : ℝ)..n, D 0 x) + D 0 a / 2 + D 0 n / 2 +
      ∑ s ∈ Finset.Icc 1 (m - 1), (bernoulli (2 * s) : ℝ) / ((2 * s)! : ℝ) *
        (D (2 * s - 1) n - D (2 * s - 1) a) +
      ∫ x in (a : ℝ)..n, ((bernoulli (2 * m) : ℝ) - periodicBernoulli (2 * m) x) /
        ((2 * m)! : ℝ) * D (2 * m) x := by
  obtain ⟨M, rfl⟩ : ∃ M, m = M + 1 := ⟨m - 1, by omega⟩
  obtain ⟨N, hN⟩ : ∃ N : ℕ, n = a + N := ⟨(n - a).toNat, by omega⟩
  subst hN
  have hcast : ((a + N : ℤ) : ℝ) = (a : ℝ) + N := by push_cast; ring
  rw [show 2 * (M + 1) = 2 * M + 2 by ring] at hd hi ⊢
  rw [hcast] at hd hi ⊢
  have hem := em_sum (t := (a : ℝ)) (D := D) M N hd hi
  have hper : ∀ x : ℝ, periodicBernoulli (2 * M + 2) x =
      bernoulliFun (2 * M + 2) (Int.fract (x - a)) := fun x => by
    rw [periodicBernoulli, Int.fract_sub_intCast]
  have hN0 : (a : ℝ) ≤ a + N := by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hftc : ∫ x in (a : ℝ)..a + N, D (2 * M + 2) x =
      D (2 * M + 1) (a + N) - D (2 * M + 1) a :=
    integral_eq_sub_of_hasDerivAt (fun x hx => hd (2 * M + 1) (by omega) x
      (by rw [Set.uIcc_of_le hN0] at hx; exact hx)) hi
  have hrem : ∫ x in (a : ℝ)..a + N, ((bernoulli (2 * M + 2) : ℝ) -
      periodicBernoulli (2 * M + 2) x) / ((2 * M + 2)! : ℝ) * D (2 * M + 2) x =
      (bernoulli (2 * M + 2) : ℝ) / ((2 * M + 2)! : ℝ) *
        (D (2 * M + 1) (a + N) - D (2 * M + 1) a) -
      ∫ x in (a : ℝ)..a + N, D (2 * M + 2) x *
        (bernoulliFun (2 * M + 2) (Int.fract (x - a)) / ((2 * M + 2)! : ℝ)) := by
    rw [← hftc, ← intervalIntegral.integral_const_mul, ← integral_sub (hi.const_mul _)
      (IntervalIntegrable.mul_periodicBernoulli hi _ _ _)]
    refine integral_congr fun x _ => ?_
    rw [hper]
    ring
  have hsumI : ∑ j ∈ Finset.Icc a (a + N), D 0 j = ∑ i ∈ range (N + 1), D 0 (a + i) := by
    rw [sum_Icc_int_eq (fun j : ℤ => D 0 j) a N]
    push_cast
    rfl
  rw [hsumI, hem, hrem, show M + 1 - 1 = M by omega, sum_Icc_one_eq_sum_range_real,
    sum_range_succ]
  have e : ∀ i : ℕ, (bernoulli (2 * (i + 1)) : ℝ) / ((2 * (i + 1))! : ℝ) *
      (D (2 * (i + 1) - 1) (a + N) - D (2 * (i + 1) - 1) a) =
      (bernoulli (2 * i + 2) : ℝ) / ((2 * i + 2)! : ℝ) *
        (D (2 * i + 1) (a + N) - D (2 * i + 1) a) := fun i => by
    rw [show 2 * (i + 1) = 2 * i + 2 by ring, show 2 * i + 2 - 1 = 2 * i + 1 by omega]
  simp only [e]
  ring

end Azurite.DLMF
