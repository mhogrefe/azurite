/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section5Cubature
import Azurite.DLMF.Chapter1.Section18ODE
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# DLMF §3.7(v): the Runge–Kutta method

The order estimates are proved by a calculus of **jets** (`IsJet n g c`:
`g(h) = ∑_{i<n} cᵢ hⁱ + O(hⁿ)` as `h → 0`). Jets are closed under sums, products, powers,
`h ↦ h g(h)` and `∫₀ʰ` (`IsJet.add`, `IsJet.mul`, `IsJet.pow`, `IsJet.mul_id`,
`IsJet.integral`). They are closed under composition with `f ∈ C⁴` through Taylor's formula of
order 3 in coordinates (`taylor3_isBigO`, `taylor3_coord`, `IsJet.comp_taylor`; in three variables
`taylor3_coord3`, `IsJet.comp_taylor3`), with closed-form coefficients (`compC`, `compC3`). The
exact solution is expanded by bootstrapping `w(z + h) − w(z) = ∫₀ʰ f(z + s, w(z + s)) ds`, and
the order conditions are polynomial identities checked by `ring`.

* 3.7.18–3.7.19 (`rkK1`–`rkK4`, `rk4Step`): local error `O(h⁵)` for `f ∈ C⁴` (`dlmf_3_7_18`).
  **Erratum**: "holds if the solution `w(z)` has five continuous derivatives" is not sufficient,
  since `k₂, k₃, k₄` evaluate `f` off the solution. For `f = 2z + √|w − z²|` and `w = z²` the
  error is `≥ h²/6` (`dlmf_3_7_v_erratum`).
* 3.7.20–3.7.21 (`nysK1`–`nysK4`, `nysW`, `nysWD`): with `k₃` as printed, the `w`-update is
  `O(h⁵)` (`dlmf_3_7_20_w`) but the `w′`-update is not. **Erratum**: `k₃` must contain `h k₁/8`
  instead of `h k₂/8`, as in the Runge–Kutta–Nyström rule (Abramowitz and Stegun 25.5.20). For
  `w″ = w`, `w = sinh` the printed rule is off by `h⁴/48 + h⁶/192` (`dlmf_3_7_21_erratum`). With
  the correction (`nysK3'`) both updates are `O(h⁵)` (`dlmf_3_7_20`).

Not formalized: the remarks on the method (equivalence to truncated Taylor series, no analytic
differentiation) and the references.
-/

open Filter Topology Asymptotics Polynomial Finset

namespace Azurite.DLMF

/-! ### Jets: `g(h) = ∑_{i<n} cᵢ hⁱ + O(hⁿ)` as `h → 0` -/

/-- `g(h) = ∑_{i<n} cᵢ hⁱ + O(hⁿ)` as `h → 0`. -/
def IsJet (n : ℕ) (g : ℝ → ℝ) (c : ℕ → ℝ) : Prop :=
  (fun h => g h - ∑ i ∈ range n, c i * h ^ i) =O[𝓝 0] fun h => h ^ n

/-- The polynomial `∑_{i<n} cᵢ Xⁱ`. -/
noncomputable def jpoly (n : ℕ) (c : ℕ → ℝ) : ℝ[X] := ∑ i ∈ range n, C (c i) * X ^ i

theorem jpoly_eval (n : ℕ) (c : ℕ → ℝ) (h : ℝ) :
    (jpoly n c).eval h = ∑ i ∈ range n, c i * h ^ i := by
  simp [jpoly, eval_finsetSum]

theorem jpoly_coeff (n : ℕ) (c : ℕ → ℝ) (j : ℕ) :
    (jpoly n c).coeff j = if j < n then c j else 0 := by
  simp [jpoly, coeff_C_mul, coeff_X_pow, mul_ite]

/-- A polynomial with vanishing coefficients below `n` is `O(hⁿ)` at `0`. -/
theorem eval_isBigO_of_coeff {P : ℝ[X]} {n : ℕ} (hP : ∀ i < n, P.coeff i = 0) :
    (fun h => P.eval h) =O[𝓝 0] fun h => h ^ n := by
  obtain ⟨Q, hQ⟩ := X_pow_dvd_iff.mpr hP
  have e : (fun h => P.eval h) = fun h => h ^ n * Q.eval h := by
    funext h; rw [hQ]; simp
  rw [e]
  have hQb : (fun h => Q.eval h) =O[𝓝 (0 : ℝ)] (fun _ => (1 : ℝ)) :=
    (Q.continuous.tendsto 0).isBigO_one ℝ
  simpa using (isBigO_refl (fun h : ℝ => h ^ n) (𝓝 0)).mul hQb

theorem pow_isBigO_pow {m n : ℕ} (hmn : n ≤ m) :
    (fun h : ℝ => h ^ m) =O[𝓝 0] fun h => h ^ n := by
  have := eval_isBigO_of_coeff (P := (X ^ m : ℝ[X])) (n := n) fun i hi => by
    rw [coeff_X_pow]; simp only [ite_eq_right_iff, one_ne_zero, imp_false]; omega
  simpa using this

theorem isBigO_one_of_poly (n : ℕ) (c : ℕ → ℝ) :
    (fun h => ∑ i ∈ range n, c i * h ^ i) =O[𝓝 (0 : ℝ)] (fun _ => (1 : ℝ)) := by
  have := ((jpoly n c).continuous.tendsto 0).isBigO_one ℝ
  simpa [jpoly_eval] using this

namespace IsJet

variable {n m : ℕ} {g g' : ℝ → ℝ} {c d : ℕ → ℝ}

theorem congr (hg : IsJet n g c) (hc : ∀ i < n, c i = d i) : IsJet n g d := by
  unfold IsJet at *
  refine hg.congr_left fun h => ?_
  congr 1
  exact sum_congr rfl fun i hi => by rw [hc i (mem_range.mp hi)]

theorem congr_fun (hg : IsJet n g c) (he : ∀ h, g h = g' h) : IsJet n g' c := by
  have : g = g' := funext he
  rwa [← this]

theorem isBigO_one (hg : IsJet n g c) : g =O[𝓝 0] fun _ => (1 : ℝ) := by
  have h1 : (fun h : ℝ => h ^ n) =O[𝓝 (0 : ℝ)] (fun _ => (1 : ℝ)) :=
    ((continuous_pow n).tendsto 0).isBigO_one ℝ
  have := (hg.trans h1).add (isBigO_one_of_poly n c)
  simpa using this

theorem zero : IsJet n (fun _ => 0) 0 := by
  simpa [IsJet] using isBigO_zero (fun h : ℝ => h ^ n) (𝓝 0)

theorem add (hg : IsJet n g c) (hg' : IsJet n g' d) : IsJet n (fun h => g h + g' h) (c + d) := by
  unfold IsJet at *
  refine (hg.add hg').congr_left fun h => ?_
  simp only [Pi.add_apply, add_mul, sum_add_distrib]
  ring

theorem sub (hg : IsJet n g c) (hg' : IsJet n g' d) : IsJet n (fun h => g h - g' h) (c - d) := by
  unfold IsJet at *
  refine (hg.sub hg').congr_left fun h => ?_
  simp only [Pi.sub_apply, sub_mul, sum_sub_distrib]
  ring

theorem const_mul (a : ℝ) (hg : IsJet n g c) : IsJet n (fun h => a * g h) (a • c) := by
  unfold IsJet at *
  refine (hg.const_mul_left a).congr_left fun h => ?_
  simp only [Pi.smul_apply, smul_eq_mul, mul_sub, mul_sum]
  congr 1
  exact sum_congr rfl fun i _ => by ring

theorem sum {ι : Type*} (s : Finset ι) {G : ι → ℝ → ℝ} {Cs : ι → ℕ → ℝ}
    (hG : ∀ k ∈ s, IsJet n (G k) (Cs k)) :
    IsJet n (fun h => ∑ k ∈ s, G k h) (∑ k ∈ s, Cs k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero (n := n))
  | insert a s ha ih =>
    have := (hG a (mem_insert_self a s)).add (ih fun k hk => hG k (mem_insert_of_mem hk))
    refine (this.congr fun i _ => ?_).congr_fun fun h => ?_
    · simp [sum_insert ha]
    · simp [sum_insert ha]

/-- `jconst a = (a, 0, 0, …)`. -/
def jconst (a : ℝ) : ℕ → ℝ := fun k => if k = 0 then a else 0

/-- `jX = (0, 1, 0, …)`, the jet of `h`. -/
def jX : ℕ → ℝ := fun k => if k = 1 then 1 else 0

theorem const (a : ℝ) : IsJet n (fun _ => a) (jconst a) := by
  unfold IsJet
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using (isBigO_const_const a (one_ne_zero (α := ℝ)) (𝓝 0))
  · have : ∀ h : ℝ, ∑ i ∈ range n, jconst a i * h ^ i = a := fun h => by
      rw [sum_eq_single 0 (fun i _ hi => by simp [jconst, hi]) (by simp [hn])]
      simp [jconst]
    simpa [this] using isBigO_zero (fun h : ℝ => h ^ n) (𝓝 0)

theorem id : IsJet n (fun h => h) jX := by
  unfold IsJet
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · simpa using ((continuous_id.tendsto (0 : ℝ)).isBigO_one ℝ)
    · simpa [jX] using isBigO_refl (fun h : ℝ => h) (𝓝 0)
  · have : ∀ h : ℝ, ∑ i ∈ range n, jX i * h ^ i = h := fun h => by
      rw [sum_eq_single 1 (fun i _ hi => by simp [jX, hi]) (by simp; omega)]
      simp [jX]
    simpa [this] using isBigO_zero (fun h : ℝ => h ^ n) (𝓝 0)

theorem mono (hmn : n ≤ m) (hg : IsJet m g c) : IsJet n g c := by
  unfold IsJet at *
  have hP := eval_isBigO_of_coeff (P := jpoly m c - jpoly n c) (n := n) fun i hi => by
    simp only [coeff_sub, jpoly_coeff, hi, show i < m by omega, ↓reduceIte, sub_self]
  refine ((hg.trans (pow_isBigO_pow hmn)).add hP).congr_left fun h => ?_
  simp only [eval_sub, jpoly_eval]
  ring

/-- `jmul c d k = ∑_{i+j=k} cᵢ dⱼ`. -/
def jmul (c d : ℕ → ℝ) : ℕ → ℝ := fun k => ∑ x ∈ antidiagonal k, c x.1 * d x.2

theorem mul (hg : IsJet n g c) (hg' : IsJet n g' d) :
    IsJet n (fun h => g h * g' h) (jmul c d) := by
  unfold IsJet at *
  have hP := eval_isBigO_of_coeff (P := jpoly n c * jpoly n d - jpoly n (jmul c d)) (n := n)
    fun i hi => by
      rw [coeff_sub, coeff_mul, jpoly_coeff]
      simp only [hi, ↓reduceIte, jmul]
      rw [sub_eq_zero]
      refine sum_congr rfl fun x hx => ?_
      rw [mem_antidiagonal] at hx
      rw [jpoly_coeff, jpoly_coeff]
      simp only [show x.1 < n by omega, show x.2 < n by omega, ↓reduceIte]
  have h1 : (fun h => (g h - ∑ i ∈ range n, c i * h ^ i) * g' h) =O[𝓝 0] fun h => h ^ n := by
    simpa using hg.mul (isBigO_one (n := n) (c := d) hg')
  have h2 : (fun h => (∑ i ∈ range n, c i * h ^ i) * (g' h - ∑ i ∈ range n, d i * h ^ i))
      =O[𝓝 0] fun h => h ^ n := by
    simpa using (isBigO_one_of_poly n c).mul hg'
  refine ((h1.add h2).add hP).congr_left fun h => ?_
  simp only [eval_sub, eval_mul, jpoly_eval]
  ring

/-- Powers of jets. -/
def jpow (c : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => jconst 1
  | k + 1 => jmul (jpow c k) c

theorem pow (hg : IsJet n g c) (k : ℕ) : IsJet n (fun h => g h ^ k) (jpow c k) := by
  induction k with
  | zero => exact (const (n := n) (1 : ℝ)).congr_fun fun h => by simp
  | succ k ih => exact (ih.mul hg).congr_fun fun h => by ring

/-- `jshift c = (0, c₀, c₁, …)`, the jet of `h g(h)`. -/
def jshift (c : ℕ → ℝ) : ℕ → ℝ := fun k => if k = 0 then 0 else c (k - 1)

theorem mul_id (hg : IsJet n g c) : IsJet (n + 1) (fun h => h * g h) (jshift c) := by
  unfold IsJet at *
  refine ((isBigO_refl (fun h : ℝ => h) (𝓝 0)).mul hg).congr' (Eventually.of_forall fun h => ?_)
    (Eventually.of_forall fun h => by ring)
  dsimp only
  rw [sum_range_succ']
  simp only [jshift, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, zero_mul, add_zero,
    mul_sub, mul_sum]
  congr 1
  exact sum_congr rfl fun i _ => by ring

/-- `jinteg c = (0, c₀, c₁/2, c₂/3, …)`, the jet of `∫₀ʰ g`. -/
noncomputable def jinteg (c : ℕ → ℝ) : ℕ → ℝ := fun k => if k = 0 then 0 else c (k - 1) / k

theorem integral (hgc : Continuous g) (hg : IsJet n g c) :
    IsJet (n + 1) (fun h => ∫ s in (0 : ℝ)..h, g s) (jinteg c) := by
  unfold IsJet at *
  obtain ⟨K, hK⟩ := hg.bound
  obtain ⟨δ, hδ, hδK⟩ := Metric.eventually_nhds_iff.mp hK
  set G : ℝ → ℝ := fun s => g s - ∑ i ∈ range n, c i * s ^ i
  have hGc : Continuous G := hgc.sub (continuous_finsetSum _ fun i _ => by fun_prop)
  have hint : ∀ h, ∫ s in (0 : ℝ)..h, g s =
      (∫ s in (0 : ℝ)..h, G s) + ∑ k ∈ range (n + 1), jinteg c k * h ^ k := fun h => by
    have hP : ∫ s in (0 : ℝ)..h, ∑ i ∈ range n, c i * s ^ i =
        ∑ k ∈ range (n + 1), jinteg c k * h ^ k := by
      rw [intervalIntegral.integral_finsetSum fun i _ => by
        exact (by fun_prop : Continuous fun s : ℝ => c i * s ^ i).intervalIntegrable _ _]
      rw [sum_range_succ']
      simp only [jinteg, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, zero_mul, add_zero]
      refine sum_congr rfl fun i _ => ?_
      rw [intervalIntegral.integral_const_mul, integral_pow]
      push_cast
      field_simp
      ring
    rw [← hP, ← intervalIntegral.integral_add (hGc.intervalIntegrable _ _)
      ((continuous_finsetSum _ fun i _ => by fun_prop).intervalIntegrable _ _)]
    exact intervalIntegral.integral_congr fun s _ => by simp [G]
  refine IsBigO.of_bound (|K| / (n + 1)) ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with h hh
  rw [hint, add_sub_cancel_right, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
  have hb := abs_integral_le_pow hGc (x0 := 0) (x := h) (C := |K|) n fun t ht => by
    have htδ : dist t 0 < δ := by
      rw [Real.dist_eq, sub_zero]
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hh
      have := Set.abs_sub_left_of_mem_uIcc ht
      simp only [sub_zero] at this
      exact lt_of_le_of_lt this hh
    have := hδK htδ
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow] at this
    rw [sub_zero]
    exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity))
  rw [sub_zero] at hb
  calc |∫ s in (0 : ℝ)..h, G s| ≤ |K| * |h| ^ (n + 1) / (n + 1) := hb
    _ = |K| / (n + 1) * |h| ^ (n + 1) := by ring

end IsJet

/-! ### Taylor's formula in two variables -/

section Taylor

open scoped Nat

variable {f : ℝ × ℝ → ℝ}

/-- Taylor's formula of order 3 with remainder `O(‖v‖⁴)`, for `f ∈ C⁴`. -/
theorem taylor3_isBigO {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {f : E → ℝ} (hf : ContDiff ℝ 4 f) (p : E) :
    (fun v : E => f (p + v) -
      ∑ k ∈ range 4, (k ! : ℝ)⁻¹ * iteratedFDeriv ℝ k f p (fun _ => v)) =O[𝓝 0]
      fun v => ‖v‖ ^ 4 := by
  obtain ⟨K, hK⟩ := (isCompact_closedBall p 1).exists_bound_of_continuousOn
    (hf.continuous_iteratedFDeriv (m := 4) le_rfl).continuousOn
  refine IsBigO.of_bound |K| ?_
  filter_upwards [Metric.closedBall_mem_nhds (0 : E) one_pos] with v hv
  rw [Metric.mem_closedBall, dist_zero_right] at hv
  have ht := map_add_eq_sum_add_integral_iteratedFDeriv (n := 3) (x := p) (y := v) (f := f)
    fun t _ => hf.contDiffAt.of_le (by norm_num)
  have e : f (p + v) - ∑ k ∈ range 4, (k ! : ℝ)⁻¹ * iteratedFDeriv ℝ k f p (fun _ => v) =
      (3 ! : ℝ)⁻¹ * ∫ t in (0 : ℝ)..1, (1 - t) ^ 3 *
        iteratedFDeriv ℝ (3 + 1) f (p + t • v) (fun _ => v) := by
    rw [ht]; simp [smul_eq_mul]
  rw [e, norm_mul, norm_pow, norm_norm, Real.norm_eq_abs, Real.norm_eq_abs]
  have hb : ‖∫ t in (0 : ℝ)..1, (1 - t) ^ 3 * iteratedFDeriv ℝ (3 + 1) f (p + t • v) (fun _ => v)‖
      ≤ |K| * ‖v‖ ^ 4 * |1 - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
    rw [Set.uIoc_of_le zero_le_one] at ht
    have hq : p + t • v ∈ Metric.closedBall p 1 := by
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos ht.1]
      nlinarith [norm_nonneg v, ht.2]
    have h1 := (iteratedFDeriv ℝ 4 f (p + t • v)).le_opNorm (fun _ => v)
    rw [prod_const, card_univ, Fintype.card_fin] at h1
    rw [norm_mul, Real.norm_eq_abs, abs_pow, abs_of_nonneg (by linarith [ht.2])]
    have h2 : (1 - t) ^ 3 ≤ 1 := pow_le_one₀ (by linarith [ht.2]) (by linarith [ht.1])
    have h3 := hK _ hq
    calc (1 - t) ^ 3 * ‖iteratedFDeriv ℝ (3 + 1) f (p + t • v) (fun _ => v)‖
        ≤ 1 * (|K| * ‖v‖ ^ 4) := by
          exact mul_le_mul h2 (h1.trans (mul_le_mul_of_nonneg_right (h3.trans (le_abs_self K))
            (by positivity))) (norm_nonneg _) zero_le_one
      _ = |K| * ‖v‖ ^ 4 := one_mul _
  rw [sub_zero, abs_one, mul_one, Real.norm_eq_abs] at hb
  calc |(3 ! : ℝ)⁻¹| * |∫ t in (0 : ℝ)..1, (1 - t) ^ 3 *
        iteratedFDeriv ℝ (3 + 1) f (p + t • v) (fun _ => v)|
      ≤ 1 * (|K| * ‖v‖ ^ 4) := by
        gcongr
        rw [abs_inv]
        exact inv_le_one_of_one_le₀ (by norm_cast)
    _ = |K| * ‖v‖ ^ 4 := one_mul _

/-- The coefficients of `D^k f(p)(v, …, v)` in `v = (x, y)`: `x^i y^{k−i}`, with `1/k!`. -/
noncomputable def taylorCoeff2 (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) (k i : ℕ) : ℝ :=
  (k ! : ℝ)⁻¹ * ∑ r ∈ univ.filter (fun r : Fin k → Fin 2 =>
    (univ.filter fun m => r m = 0).card = i), iteratedFDeriv ℝ k f p (fun m => coordVec (r m))

theorem diag_eq_sum {k : ℕ} (L : ContinuousMultilinearMap ℝ (fun _ : Fin k => ℝ × ℝ) ℝ)
    (x y : ℝ) : L (fun _ => (x, y)) = ∑ i ∈ range (k + 1),
      (∑ r ∈ univ.filter (fun r : Fin k → Fin 2 => (univ.filter fun m => r m = 0).card = i),
        L (fun m => coordVec (r m))) * x ^ i * y ^ (k - i) := by
  rw [multilinear_diag_eq]
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (t := range (k + 1))
    (g := fun r : Fin k → Fin 2 => (univ.filter fun m => r m = 0).card) fun r _ => by
      rw [mem_range, Nat.lt_succ_iff]
      exact (card_filter_le _ _).trans (by simp)]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_mul, sum_mul]
  refine sum_congr rfl fun r hr => ?_
  rw [mem_filter] at hr
  have h1 := card_filter_zero_add_one r
  simp only at h1 ⊢
  rw [hr.2] at h1 ⊢
  rw [show (univ.filter fun m => r m = 1).card = k - i by omega]
  ring

theorem taylorCoeff2_zero (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : taylorCoeff2 f p 0 0 = f p := by
  simp [taylorCoeff2]

/-- Taylor's formula of order 3 in coordinates. -/
theorem taylor3_coord (hf : ContDiff ℝ 4 f) (p : ℝ × ℝ) :
    (fun v : ℝ × ℝ => f (p + v) - ∑ k ∈ range 4, ∑ i ∈ range (k + 1),
      taylorCoeff2 f p k i * v.1 ^ i * v.2 ^ (k - i)) =O[𝓝 0] fun v => ‖v‖ ^ 4 := by
  refine (taylor3_isBigO hf p).congr_left fun v => ?_
  congr 1
  refine sum_congr rfl fun k _ => ?_
  rw [show v = (v.1, v.2) from rfl, diag_eq_sum, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  simp only [taylorCoeff2]
  ring

end Taylor

/-! ### Composition of a jet with `f` -/

section Comp

open IsJet

/-- The jet of `T(a h, Y(h))`, `T(x, y) = ∑_{k<4} ∑_{i≤k} κ_{k,i} xⁱ y^{k−i}`. -/
noncomputable def compJet (κ : ℕ → ℕ → ℝ) (a : ℝ) (c : ℕ → ℝ) : ℕ → ℝ :=
  ∑ k ∈ range 4, ∑ i ∈ range (k + 1), κ k i • jmul (jpow (a • jX) i) (jpow c (k - i))

/-- The same jet in closed form (for `c₀ = 0`, indices `< 4`). -/
def compC (κ : ℕ → ℕ → ℝ) (a : ℝ) (c : ℕ → ℝ) : ℕ → ℝ := fun k =>
  if k = 0 then κ 0 0
  else if k = 1 then κ 1 0 * c 1 + κ 1 1 * a
  else if k = 2 then κ 1 0 * c 2 + κ 2 0 * c 1 ^ 2 + κ 2 1 * a * c 1 + κ 2 2 * a ^ 2
  else if k = 3 then κ 1 0 * c 3 + 2 * κ 2 0 * c 1 * c 2 + κ 2 1 * a * c 2 + κ 3 0 * c 1 ^ 3 +
    κ 3 1 * a * c 1 ^ 2 + κ 3 2 * a ^ 2 * c 1 + κ 3 3 * a ^ 3
  else 0

theorem compJet_eq (κ : ℕ → ℕ → ℝ) (a : ℝ) {c : ℕ → ℝ} (hc0 : c 0 = 0) :
    ∀ k < 4, compJet κ a c k = compC κ a c k := by
  intro k hk
  interval_cases k <;>
    simp [compJet, compC, jmul, jpow, jconst, jX, sum_range_succ, Finset.sum_apply, hc0,
      Finset.Nat.antidiagonal_succ] <;> ring

theorem IsJet.isBigO_id {m : ℕ} {Y : ℝ → ℝ} {c : ℕ → ℝ} (hm : 1 ≤ m) (hY : IsJet m Y c)
    (hc0 : c 0 = 0) : Y =O[𝓝 0] fun h => h := by
  have hP := eval_isBigO_of_coeff (P := jpoly m c) (n := 1) fun i hi => by
    rw [jpoly_coeff]; simp [show i = 0 by omega, hc0]
  have e1 : (fun h : ℝ => h ^ m) =O[𝓝 0] fun h => h := by simpa using pow_isBigO_pow (n := 1) hm
  have e2 : (fun h => (jpoly m c).eval h) =O[𝓝 0] fun h => h := by simpa using hP
  have hY' : (fun h => Y h - ∑ i ∈ range m, c i * h ^ i) =O[𝓝 0] fun h => h ^ m := hY
  have := (hY'.trans e1).add e2
  simpa [jpoly_eval] using this

/-- **Composition**: if `Y(h) = ∑_{i<m} cᵢ hⁱ + O(hᵐ)` with `c₀ = 0` and `1 ≤ m ≤ 4`, then
`f(p + (a h, Y(h)))` has the jet `compJet` (`f ∈ C⁴`). -/
theorem IsJet.comp_taylor {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 4 f) (p : ℝ × ℝ) (a : ℝ)
    {m : ℕ} {Y : ℝ → ℝ} {c : ℕ → ℝ} (hm1 : 1 ≤ m) (hm4 : m ≤ 4) (hY : IsJet m Y c)
    (hc0 : c 0 = 0) :
    IsJet m (fun h => f (p + (a * h, Y h))) (compC (taylorCoeff2 f p) a c) := by
  set κ := taylorCoeff2 f p
  have hT : IsJet m (fun h => ∑ k ∈ range 4, ∑ i ∈ range (k + 1),
      κ k i * (a * h) ^ i * Y h ^ (k - i)) (compJet κ a c) := by
    refine (IsJet.sum _ fun k _ => IsJet.sum _ fun i _ =>
      IsJet.const_mul (κ k i) (((IsJet.const_mul a IsJet.id).pow i).mul (hY.pow (k - i)))).congr_fun
      fun h => ?_
    exact sum_congr rfl fun k _ => sum_congr rfl fun i _ => by ring
  have hYO := hY.isBigO_id hm1 hc0
  have hv : Tendsto (fun h => ((a * h, Y h) : ℝ × ℝ)) (𝓝 0) (𝓝 0) := by
    have h1 : Tendsto (fun h : ℝ => a * h) (𝓝 0) (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := a)).mul (tendsto_id (x := 𝓝 (0 : ℝ)))
    have h2 : Tendsto Y (𝓝 0) (𝓝 0) := hYO.trans_tendsto tendsto_id
    rw [show (0 : ℝ × ℝ) = (0, 0) from rfl]
    exact h1.prodMk_nhds h2
  have hR := (taylor3_coord hf p).comp_tendsto hv
  have hvO : (fun h => ‖((a * h, Y h) : ℝ × ℝ)‖ ^ 4) =O[𝓝 0] fun h => h ^ m := by
    have h1 : (fun h : ℝ => a * h) =O[𝓝 0] fun h => h := isBigO_const_mul_self a _ _
    have := ((h1.prod_left hYO).norm_left.pow 4).trans (pow_isBigO_pow hm4)
    simpa using this
  have hcomb := (hR.trans hvO).add (show _ =O[𝓝 0] _ from hT)
  have hJ : IsJet m (fun h => f (p + (a * h, Y h))) (compJet κ a c) := by
    unfold IsJet
    refine hcomb.congr_left fun h => ?_
    simp only [Function.comp_apply]
    ring
  exact hJ.congr fun i hi => compJet_eq κ a hc0 i (by omega)

end Comp

/-! ### The fourth-order rule for `w′ = f(z, w)` (3.7.18–3.7.19) -/

section FirstOrder

open IsJet

/-- **DLMF 3.7.19**, `k₁ = h f(zₙ, wₙ)`. -/
noncomputable def rkK1 (f : ℝ × ℝ → ℝ) (z w h : ℝ) : ℝ := h * f (z, w)

/-- **DLMF 3.7.19**, `k₂ = h f(zₙ + h/2, wₙ + k₁/2)`. -/
noncomputable def rkK2 (f : ℝ × ℝ → ℝ) (z w h : ℝ) : ℝ := h * f (z + h / 2, w + rkK1 f z w h / 2)

/-- **DLMF 3.7.19**, `k₃ = h f(zₙ + h/2, wₙ + k₂/2)`. -/
noncomputable def rkK3 (f : ℝ × ℝ → ℝ) (z w h : ℝ) : ℝ := h * f (z + h / 2, w + rkK2 f z w h / 2)

/-- **DLMF 3.7.19**, `k₄ = h f(zₙ + h, wₙ + k₃)`. -/
noncomputable def rkK4 (f : ℝ × ℝ → ℝ) (z w h : ℝ) : ℝ := h * f (z + h, w + rkK3 f z w h)

/-- **DLMF 3.7.18**: `w_{n+1} = wₙ + (k₁ + 2k₂ + 2k₃ + k₄)/6`. -/
noncomputable def rk4Step (f : ℝ × ℝ → ℝ) (z w h : ℝ) : ℝ :=
  w + (rkK1 f z w h + 2 * rkK2 f z w h + 2 * rkK3 f z w h + rkK4 f z w h) / 6

theorem isJet_zero_of_continuous {F : ℝ → ℝ} (hF : Continuous F) : IsJet 0 F 0 := by
  unfold IsJet
  simpa using (hF.tendsto 0).isBigO_one ℝ

theorem isBigO_of_isJet_zero {n : ℕ} {g : ℝ → ℝ} {c : ℕ → ℝ} (hg : IsJet n g c)
    (hc : ∀ i < n, c i = 0) : g =O[𝓝 0] fun h => h ^ n := by
  have := hg.congr (d := 0) hc
  unfold IsJet at this
  simpa using this

/-- **DLMF 3.7.18**: for `f ∈ C⁴` and a solution of `w′ = f(z, w)`, the local error of the
fourth-order rule is `O(h⁵)`. -/
theorem dlmf_3_7_18 {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 4 f) {w : ℝ → ℝ}
    (hw : ∀ x, HasDerivAt w (f (x, w x)) x) (z : ℝ) :
    (fun h => w (z + h) - rk4Step f z (w z) h) =O[𝓝 0] fun h => h ^ 5 := by
  set p : ℝ × ℝ := (z, w z)
  set κ := taylorCoeff2 f p
  have hκ : κ 0 0 = f p := taylorCoeff2_zero f p
  have hwc : Continuous w := continuous_iff_continuousAt.mpr fun x => (hw x).continuousAt
  -- the stages
  have J1 : IsJet 5 (rkK1 f z (w z)) (jshift (jconst (f p))) :=
    ((IsJet.const (n := 4) (f p)).mul_id).congr_fun fun h => rfl
  have c0 : ∀ c : ℕ → ℝ, ∀ a : ℝ, (a • jshift c) 0 = 0 := fun c a => by simp [jshift]
  have J2 : IsJet 5 (rkK2 f z (w z))
      (jshift (compC κ (1 / 2) ((1 / 2 : ℝ) • jshift (jconst (f p))))) := by
    have hY := (J1.mono (by norm_num : 4 ≤ 5)).const_mul (1 / 2)
    refine (IsJet.comp_taylor hf p (1 / 2) (by norm_num) le_rfl hY (c0 _ _)).mul_id.congr_fun
      fun h => ?_
    simp only [rkK2, p, Prod.mk_add_mk]
    congr 2; ring_nf
  have J3 : IsJet 5 (rkK3 f z (w z)) (jshift (compC κ (1 / 2) ((1 / 2 : ℝ) •
      jshift (compC κ (1 / 2) ((1 / 2 : ℝ) • jshift (jconst (f p))))))) := by
    have hY := (J2.mono (by norm_num : 4 ≤ 5)).const_mul (1 / 2)
    refine (IsJet.comp_taylor hf p (1 / 2) (by norm_num) le_rfl hY (c0 _ _)).mul_id.congr_fun
      fun h => ?_
    simp only [rkK3, p, Prod.mk_add_mk]
    congr 2; ring_nf
  have J4 : IsJet 5 (rkK4 f z (w z)) (jshift (compC κ 1 ((1 : ℝ) • jshift (compC κ (1 / 2)
      ((1 / 2 : ℝ) • jshift (compC κ (1 / 2) ((1 / 2 : ℝ) • jshift (jconst (f p))))))))) := by
    have hY := (J3.mono (by norm_num : 4 ≤ 5)).const_mul 1
    refine (IsJet.comp_taylor hf p 1 (by norm_num) le_rfl hY (c0 _ _)).mul_id.congr_fun
      fun h => ?_
    simp only [rkK4, p, Prod.mk_add_mk]
    congr 2; ring_nf
  have Jrk := (((J1.add (J2.const_mul 2)).add (J3.const_mul 2)).add J4).const_mul (1 / 6)
  -- the exact solution
  set F : ℝ → ℝ := fun s => f (z + s, w (z + s))
  have hFc : Continuous F :=
    hf.continuous.comp ((continuous_const.add continuous_id).prodMk
      (hwc.comp (continuous_const.add continuous_id)))
  have hWF : ∀ h, w (z + h) - w z = ∫ s in (0 : ℝ)..h, F s := fun h => by
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => w (z + s)) (a := 0)
      (b := h) (f' := F) (fun s _ =>
        ((hw (z + s)).comp s ((hasDerivAt_id s).const_add z)).congr_deriv (by simp [F]))
      (hFc.intervalIntegrable _ _)
    simp only [add_zero] at this
    exact this.symm
  have hFe : ∀ h, f (p + (1 * h, w (z + h) - w z)) = F h := fun h => by
    simp only [p, F, Prod.mk_add_mk, one_mul]
    congr 2; ring
  have step : ∀ {m : ℕ} {c : ℕ → ℝ}, 1 ≤ m → m ≤ 4 → c 0 = 0 →
      IsJet m (fun h => w (z + h) - w z) c → IsJet (m + 1) (fun h => w (z + h) - w z)
        (jinteg (compC κ 1 c)) := fun hm1 hm4 hc0 hW =>
    ((IsJet.integral hFc ((IsJet.comp_taylor hf p 1 hm1 hm4 hW hc0).congr_fun hFe)).congr_fun
      fun h => (hWF h).symm)
  have W1 : IsJet 1 (fun h => w (z + h) - w z) (jinteg 0) :=
    (IsJet.integral hFc (isJet_zero_of_continuous hFc)).congr_fun fun h => (hWF h).symm
  have ji0 : ∀ c, jinteg c 0 = 0 := fun c => by simp [jinteg]
  have W5 := step (by norm_num) le_rfl (ji0 _) <| step (by norm_num) (by norm_num) (ji0 _) <|
    step (by norm_num) (by norm_num) (ji0 _) <| step le_rfl (by norm_num) (ji0 _) W1
  have hΦ := W5.sub Jrk
  refine isBigO_of_isJet_zero (hΦ.congr_fun fun h => ?_) fun i hi => ?_
  · simp only [rk4Step]; ring
  · interval_cases i <;>
      simp [jinteg, compC, jshift, jconst, hκ, Pi.smul_apply, Pi.add_apply, Pi.sub_apply] <;>
      ring

/-- **DLMF §3.7(v)**: "The order estimate `O(h⁵)` holds if the solution `w(z)` has five
continuous derivatives" is not enough, since `k₂, k₃, k₄` evaluate `f` off the solution. For
`f(z, w) = 2z + √|w − z²|` the solution `w = z²` is a polynomial, yet the local error of
3.7.18 at `z = 0` is at least `h²/6` for `h > 0`. -/
theorem dlmf_3_7_v_erratum :
    let f : ℝ × ℝ → ℝ := fun q => 2 * q.1 + √|q.2 - q.1 ^ 2|
    let w : ℝ → ℝ := fun z => z ^ 2
    (∀ x, HasDerivAt w (f (x, w x)) x) ∧ ContDiff ℝ 5 w ∧
      (∀ h, 0 < h → h ^ 2 / 6 ≤ |w (0 + h) - rk4Step f 0 (w 0) h|) ∧
      ¬ (fun h => w (0 + h) - rk4Step f 0 (w 0) h) =O[𝓝 0] fun h => h ^ 5 := by
  intro f w
  have hlow : ∀ h, 0 < h → h ^ 2 / 6 ≤ |w (0 + h) - rk4Step f 0 (w 0) h| := by
    intro h hh
    rw [show w 0 = 0 by simp [w], show w (0 + h) = h ^ 2 by simp [w]]
    have k1 : rkK1 f 0 0 h = 0 := by simp [rkK1, f]
    have k2 : rkK2 f 0 0 h = 3 * h ^ 2 / 2 := by
      simp only [rkK2, k1, f]
      have : √|0 + 0 / 2 - (0 + h / 2) ^ 2| = h / 2 := by
        rw [show |0 + 0 / 2 - (0 + h / 2) ^ 2| = (h / 2) ^ 2 by
          rw [abs_of_nonpos (by nlinarith)]; ring]
        exact Real.sqrt_sq (by linarith)
      rw [this]; ring
    have k3 : h ^ 2 ≤ rkK3 f 0 0 h := by
      simp only [rkK3, f]
      nlinarith [Real.sqrt_nonneg |0 + rkK2 f 0 0 h / 2 - (0 + h / 2) ^ 2|]
    have k4 : 2 * h ^ 2 ≤ rkK4 f 0 0 h := by
      simp only [rkK4, f]
      nlinarith [Real.sqrt_nonneg |0 + rkK3 f 0 0 h - (0 + h) ^ 2|]
    simp only [rk4Step, k1, k2]
    have hsq := sq_nonneg h
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  refine ⟨fun x => ?_, by simp only [w]; fun_prop, hlow, fun hO => ?_⟩
  · have : f (x, w x) = 2 * x := by simp [f, w]
    rw [this]
    simpa [w] using hasDerivAt_pow 2 x
  · obtain ⟨C, hC⟩ := hO.bound
    obtain ⟨δ, hδ, hδC⟩ := Metric.eventually_nhds_iff.mp hC
    set h := min (δ / 2) (1 / (6 * (|C| + 1)))
    have hpos : 0 < h := lt_min (by linarith) (by positivity)
    have hδh : dist h 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hpos]
      linarith [min_le_left (δ / 2) (1 / (6 * (|C| + 1)))]
    have h1 := hδC hδh
    have h2 := hlow h hpos
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, abs_of_pos hpos] at h1
    have hh1 : h ≤ 1 / (6 * (|C| + 1)) := min_le_right _ _
    have hh1' : h ≤ 1 := hh1.trans (by
      rw [div_le_one (by positivity)]; nlinarith [abs_nonneg C])
    have : h ^ 2 / 6 ≤ |C| * h ^ 5 := h2.trans (h1.trans (by
      gcongr; exact le_abs_self C))
    have h3 : h ^ 3 ≤ h := by nlinarith [pow_le_one₀ hpos.le hh1' (n := 2)]
    have h4 : |C| * h ≤ |C| / (6 * (|C| + 1)) :=
      calc |C| * h ≤ |C| * (1 / (6 * (|C| + 1))) := mul_le_mul_of_nonneg_left hh1 (abs_nonneg C)
        _ = |C| / (6 * (|C| + 1)) := by ring
    have h5 : |C| / (6 * (|C| + 1)) < 1 / 6 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith [abs_nonneg C]
    have h6 : 1 / 6 ≤ |C| * h ^ 3 := by
      have hp2 : 0 < h ^ 2 := by positivity
      have : h ^ 2 / 6 ≤ (|C| * h ^ 3) * h ^ 2 := by nlinarith
      nlinarith
    nlinarith [abs_nonneg C, mul_le_mul_of_nonneg_left h3 (abs_nonneg C)]

end FirstOrder

/-! ### Taylor's formula in three variables -/

section Taylor3

open scoped Nat
open IsJet

/-- The coordinates of `ℝ × ℝ × ℝ`. -/
def coord3 (i : Fin 3) (y : ℝ × ℝ × ℝ) : ℝ :=
  if i = 0 then y.1 else if i = 1 then y.2.1 else y.2.2

/-- The unit vectors of `ℝ × ℝ × ℝ`. -/
def coordVec3 (i : Fin 3) : ℝ × ℝ × ℝ :=
  if i = 0 then (1, 0, 0) else if i = 1 then (0, 1, 0) else (0, 0, 1)

theorem sum_coord3_smul (y : ℝ × ℝ × ℝ) : ∑ i : Fin 3, coord3 i y • coordVec3 i = y := by
  simp [Fin.sum_univ_three, coord3, coordVec3]

theorem prod_coord3 {j : ℕ} (r : Fin j → Fin 3) (y : ℝ × ℝ × ℝ) :
    ∏ m, coord3 (r m) y = y.1 ^ (univ.filter fun m => r m = 0).card *
      y.2.1 ^ (univ.filter fun m => r m = 1).card *
        y.2.2 ^ (univ.filter fun m => r m = 2).card := by
  rw [← Finset.prod_fiberwise univ r (fun m => coord3 (r m) y), Fin.prod_univ_three]
  congr 1
  · congr 1
    · rw [Finset.prod_congr rfl (g := fun _ => y.1) fun m hm => by
        simp only [Finset.mem_filter] at hm; simp [coord3, hm.2], Finset.prod_const]
    · rw [Finset.prod_congr rfl (g := fun _ => y.2.1) fun m hm => by
        simp only [Finset.mem_filter] at hm; simp [coord3, hm.2], Finset.prod_const]
  · rw [Finset.prod_congr rfl (g := fun _ => y.2.2) fun m hm => by
      simp only [Finset.mem_filter] at hm; simp [coord3, hm.2], Finset.prod_const]

theorem card_filter3 {j : ℕ} (r : Fin j → Fin 3) :
    (univ.filter fun m => r m = 0).card + (univ.filter fun m => r m = 1).card +
      (univ.filter fun m => r m = 2).card = j := by
  have := Finset.card_eq_sum_card_fiberwise (s := (univ : Finset (Fin j))) (t := univ)
    (f := r) fun m _ => mem_univ _
  rw [Fin.sum_univ_three, Finset.card_univ, Fintype.card_fin] at this
  exact this.symm

theorem multilinear_diag_eq3 {j : ℕ}
    (L : ContinuousMultilinearMap ℝ (fun _ : Fin j => ℝ × ℝ × ℝ) ℝ) (y : ℝ × ℝ × ℝ) :
    L (fun _ => y) = ∑ r : Fin j → Fin 3,
      (y.1 ^ (univ.filter fun m => r m = 0).card * y.2.1 ^ (univ.filter fun m => r m = 1).card *
        y.2.2 ^ (univ.filter fun m => r m = 2).card) * L (fun m => coordVec3 (r m)) := by
  conv_lhs => rw [show (fun _ : Fin j => y) = fun _ => ∑ i : Fin 3, coord3 i y • coordVec3 i
    from funext fun _ => (sum_coord3_smul y).symm]
  rw [L.map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [L.map_smul_univ (fun m => coord3 (r m) y) (fun m => coordVec3 (r m)), prod_coord3,
    smul_eq_mul]

/-- The fibre of the words `r` with `i` zeros and `j` ones. -/
def wordFiber (k i j : ℕ) : Finset (Fin k → Fin 3) :=
  univ.filter fun r => (univ.filter fun m => r m = 0).card = i ∧
    (univ.filter fun m => r m = 1).card = j

/-- The coefficients of `D^k f(p)(v, …, v)` in `v = (x, y, u)`: `xⁱ yʲ u^{k−i−j}`, with `1/k!`. -/
noncomputable def taylorCoeff3 (f : ℝ × ℝ × ℝ → ℝ) (p : ℝ × ℝ × ℝ) (k i j : ℕ) : ℝ :=
  (k ! : ℝ)⁻¹ * ∑ r ∈ wordFiber k i j, iteratedFDeriv ℝ k f p (fun m => coordVec3 (r m))

theorem diag_eq_sum3 {k : ℕ} (L : ContinuousMultilinearMap ℝ (fun _ : Fin k => ℝ × ℝ × ℝ) ℝ)
    (x y u : ℝ) : L (fun _ => (x, y, u)) = ∑ i ∈ range (k + 1), ∑ j ∈ range (k + 1 - i),
      (∑ r ∈ wordFiber k i j, L (fun m => coordVec3 (r m))) * x ^ i * y ^ j * u ^ (k - i - j) := by
  rw [multilinear_diag_eq3, Finset.sum_sigma']
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ)
    (t := (range (k + 1)).sigma fun i => range (k + 1 - i))
    (g := fun r : Fin k → Fin 3 => (⟨(univ.filter fun m => r m = 0).card,
      (univ.filter fun m => r m = 1).card⟩ : Σ _ : ℕ, ℕ)) fun r _ => by
      have := card_filter3 r
      simp only [mem_sigma, mem_range]
      omega]
  refine sum_congr rfl fun ⟨i, j⟩ _ => ?_
  simp only
  rw [sum_mul, sum_mul, sum_mul]
  refine sum_congr ?_ fun r hr => ?_
  · ext r; simp [wordFiber, Sigma.mk.injEq]
  · simp only [wordFiber, mem_filter, mem_univ, true_and] at hr
    have h3 := card_filter3 r
    rw [hr.1, hr.2] at h3 ⊢
    rw [show (univ.filter fun m => r m = 2).card = k - i - j by omega]
    ring

theorem taylorCoeff3_zero (f : ℝ × ℝ × ℝ → ℝ) (p : ℝ × ℝ × ℝ) : taylorCoeff3 f p 0 0 0 = f p := by
  simp [taylorCoeff3, wordFiber]

theorem taylor3_coord3 {f : ℝ × ℝ × ℝ → ℝ} (hf : ContDiff ℝ 4 f) (p : ℝ × ℝ × ℝ) :
    (fun v : ℝ × ℝ × ℝ => f (p + v) - ∑ k ∈ range 4, ∑ i ∈ range (k + 1),
      ∑ j ∈ range (k + 1 - i), taylorCoeff3 f p k i j * v.1 ^ i * v.2.1 ^ j *
        v.2.2 ^ (k - i - j)) =O[𝓝 0] fun v => ‖v‖ ^ 4 := by
  refine (taylor3_isBigO hf p).congr_left fun v => ?_
  congr 1
  refine sum_congr rfl fun k _ => ?_
  rw [show v = (v.1, v.2.1, v.2.2) from rfl, diag_eq_sum3, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun j _ => ?_
  simp only [taylorCoeff3]
  ring

/-- The jet of `T(a h, Y(h), U(h))`. -/
noncomputable def compJet3 (κ : ℕ → ℕ → ℕ → ℝ) (a : ℝ) (cy cu : ℕ → ℝ) : ℕ → ℝ :=
  ∑ k ∈ range 4, ∑ i ∈ range (k + 1), ∑ j ∈ range (k + 1 - i),
    κ k i j • jmul (jmul (jpow (a • jX) i) (jpow cy j)) (jpow cu (k - i - j))

/-- The same jet in closed form (for `cy₀ = cu₀ = 0`, indices `< 4`). -/
def compC3 (κ : ℕ → ℕ → ℕ → ℝ) (a : ℝ) (cy cu : ℕ → ℝ) : ℕ → ℝ := fun k =>
  if k = 0 then κ 0 0 0
  else if k = 1 then κ 1 1 0 * a + κ 1 0 1 * cy 1 + κ 1 0 0 * cu 1
  else if k = 2 then κ 1 0 1 * cy 2 + κ 1 0 0 * cu 2 + κ 2 2 0 * a ^ 2 + κ 2 1 1 * a * cy 1 +
    κ 2 1 0 * a * cu 1 + κ 2 0 2 * cy 1 ^ 2 + κ 2 0 1 * cy 1 * cu 1 + κ 2 0 0 * cu 1 ^ 2
  else if k = 3 then κ 1 0 1 * cy 3 + κ 1 0 0 * cu 3 + κ 2 1 1 * a * cy 2 + κ 2 1 0 * a * cu 2 +
    2 * κ 2 0 2 * cy 1 * cy 2 + κ 2 0 1 * (cy 1 * cu 2 + cy 2 * cu 1) + 2 * κ 2 0 0 * cu 1 * cu 2 +
    κ 3 3 0 * a ^ 3 + κ 3 2 1 * a ^ 2 * cy 1 + κ 3 2 0 * a ^ 2 * cu 1 + κ 3 1 2 * a * cy 1 ^ 2 +
    κ 3 1 1 * a * cy 1 * cu 1 + κ 3 1 0 * a * cu 1 ^ 2 + κ 3 0 3 * cy 1 ^ 3 +
    κ 3 0 2 * cy 1 ^ 2 * cu 1 + κ 3 0 1 * cy 1 * cu 1 ^ 2 + κ 3 0 0 * cu 1 ^ 3
  else 0

theorem compJet3_eq (κ : ℕ → ℕ → ℕ → ℝ) (a : ℝ) {cy cu : ℕ → ℝ} (hy0 : cy 0 = 0)
    (hu0 : cu 0 = 0) : ∀ k < 4, compJet3 κ a cy cu k = compC3 κ a cy cu k := by
  intro k hk
  interval_cases k <;>
    simp [compJet3, compC3, jmul, jpow, jconst, jX, sum_range_succ, Finset.sum_apply, hy0, hu0,
      Finset.Nat.antidiagonal_succ] <;> ring

/-- **Composition in three variables**. -/
theorem IsJet.comp_taylor3 {f : ℝ × ℝ × ℝ → ℝ} (hf : ContDiff ℝ 4 f) (p : ℝ × ℝ × ℝ) (a : ℝ)
    {m : ℕ} {Y U : ℝ → ℝ} {cy cu : ℕ → ℝ} (hm1 : 1 ≤ m) (hm4 : m ≤ 4) (hY : IsJet m Y cy)
    (hU : IsJet m U cu) (hy0 : cy 0 = 0) (hu0 : cu 0 = 0) :
    IsJet m (fun h => f (p + (a * h, Y h, U h))) (compC3 (taylorCoeff3 f p) a cy cu) := by
  set κ := taylorCoeff3 f p
  have hT : IsJet m (fun h => ∑ k ∈ range 4, ∑ i ∈ range (k + 1), ∑ j ∈ range (k + 1 - i),
      κ k i j * (a * h) ^ i * Y h ^ j * U h ^ (k - i - j)) (compJet3 κ a cy cu) := by
    refine (IsJet.sum _ fun k _ => IsJet.sum _ fun i _ => IsJet.sum _ fun j _ =>
      IsJet.const_mul (κ k i j) ((((IsJet.const_mul a IsJet.id).pow i).mul (hY.pow j)).mul
        (hU.pow (k - i - j)))).congr_fun fun h => ?_
    exact sum_congr rfl fun k _ => sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  have hYO := hY.isBigO_id hm1 hy0
  have hUO := hU.isBigO_id hm1 hu0
  have hv : Tendsto (fun h => ((a * h, Y h, U h) : ℝ × ℝ × ℝ)) (𝓝 0) (𝓝 0) := by
    have h1 : Tendsto (fun h : ℝ => a * h) (𝓝 0) (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := a)).mul (tendsto_id (x := 𝓝 (0 : ℝ)))
    rw [show (0 : ℝ × ℝ × ℝ) = (0, 0, 0) from rfl]
    exact h1.prodMk_nhds ((hYO.trans_tendsto tendsto_id).prodMk_nhds
      (hUO.trans_tendsto tendsto_id))
  have hR := (taylor3_coord3 hf p).comp_tendsto hv
  have hvO : (fun h => ‖((a * h, Y h, U h) : ℝ × ℝ × ℝ)‖ ^ 4) =O[𝓝 0] fun h => h ^ m := by
    have h1 : (fun h : ℝ => a * h) =O[𝓝 0] fun h => h := isBigO_const_mul_self a _ _
    have := ((h1.prod_left (hYO.prod_left hUO)).norm_left.pow 4).trans (pow_isBigO_pow hm4)
    simpa using this
  have hcomb := (hR.trans hvO).add (show _ =O[𝓝 0] _ from hT)
  have hJ : IsJet m (fun h => f (p + (a * h, Y h, U h))) (compJet3 κ a cy cu) := by
    unfold IsJet
    refine hcomb.congr_left fun h => ?_
    simp only [Function.comp_apply]
    ring
  exact hJ.congr fun i hi => compJet3_eq κ a hy0 hu0 i (by omega)

end Taylor3

/-- A function bounded below by `c hᵐ` on `(0, 1]` is not `O(hⁿ)` for `n > m`. -/
theorem not_isBigO_pow_of_le {g : ℝ → ℝ} {c : ℝ} {m n : ℕ} (hc : 0 < c) (hmn : m < n)
    (hg : ∀ h, 0 < h → h ≤ 1 → c * h ^ m ≤ |g h|) : ¬ g =O[𝓝 0] fun h => h ^ n := by
  intro hO
  obtain ⟨C, hC⟩ := hO.bound
  obtain ⟨δ, hδ, hδC⟩ := Metric.eventually_nhds_iff.mp hC
  set h := min (δ / 2) (min 1 (c / (2 * (|C| + 1))))
  have hC1 : 0 < |C| + 1 := by positivity
  have hpos : 0 < h := lt_min (by linarith) (lt_min one_pos (by positivity))
  have hh1 : h ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hh2 : h ≤ c / (2 * (|C| + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hδh : dist h 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hpos]
    linarith [min_le_left (δ / 2) (min 1 (c / (2 * (|C| + 1))))]
  have h1 := hδC hδh
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, abs_of_pos hpos] at h1
  have h2 := hg h hpos hh1
  have hpm : 0 < h ^ m := pow_pos hpos m
  have h3 : h ^ n ≤ h ^ m * h := by
    rw [← pow_succ]; exact pow_le_pow_of_le_one hpos.le hh1 (by omega)
  have h4 : c * h ^ m ≤ |C| * (h ^ m * h) :=
    h2.trans (h1.trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)).trans
      (mul_le_mul_of_nonneg_left h3 (abs_nonneg C))))
  have h5 : c ≤ |C| * h := by
    have : c * h ^ m ≤ (|C| * h) * h ^ m := by linarith
    exact le_of_mul_le_mul_right this hpm
  have h6 : |C| * h ≤ c / 2 := by
    calc |C| * h ≤ |C| * (c / (2 * (|C| + 1))) := mul_le_mul_of_nonneg_left hh2 (abs_nonneg C)
      _ ≤ (|C| + 1) * (c / (2 * (|C| + 1))) := by gcongr; linarith
      _ = c / 2 := by field_simp
  linarith

/-! ### The fourth-order rule for `w″ = f(z, w, w′)` (3.7.20–3.7.21) -/

section SecondOrder

open IsJet

/-- **DLMF 3.7.21**, `k₁ = h f(zₙ, wₙ, wₙ′)`. -/
noncomputable def nysK1 (f : ℝ × ℝ × ℝ → ℝ) (z w w' h : ℝ) : ℝ := h * f (z, w, w')

/-- **DLMF 3.7.21**, `k₂ = h f(zₙ + h/2, wₙ + h wₙ′/2 + h k₁/8, wₙ′ + k₁/2)`. -/
noncomputable def nysK2 (f : ℝ × ℝ × ℝ → ℝ) (z w w' h : ℝ) : ℝ :=
  h * f (z + h / 2, w + h * w' / 2 + h * nysK1 f z w w' h / 8, w' + nysK1 f z w w' h / 2)

/-- **DLMF 3.7.21** as printed: `k₃ = h f(zₙ + h/2, wₙ + h wₙ′/2 + h k₂/8, wₙ′ + k₂/2)`. -/
noncomputable def nysK3 (f : ℝ × ℝ × ℝ → ℝ) (z w w' h : ℝ) : ℝ :=
  h * f (z + h / 2, w + h * w' / 2 + h * nysK2 f z w w' h / 8, w' + nysK2 f z w w' h / 2)

/-- The corrected `k₃ = h f(zₙ + h/2, wₙ + h wₙ′/2 + h k₁/8, wₙ′ + k₂/2)` (the Runge–Kutta–Nyström
rule; Abramowitz and Stegun 25.5.20). -/
noncomputable def nysK3' (f : ℝ × ℝ × ℝ → ℝ) (z w w' h : ℝ) : ℝ :=
  h * f (z + h / 2, w + h * w' / 2 + h * nysK1 f z w w' h / 8, w' + nysK2 f z w w' h / 2)

/-- **DLMF 3.7.21**, `k₄ = h f(zₙ + h, wₙ + h wₙ′ + h k₃/2, wₙ′ + k₃)`, for a given `k₃`. -/
noncomputable def nysK4 (f : ℝ × ℝ × ℝ → ℝ) (z w w' h k3 : ℝ) : ℝ :=
  h * f (z + h, w + h * w' + h * k3 / 2, w' + k3)

/-- **DLMF 3.7.20**, `w_{n+1} = wₙ + h(6wₙ′ + k₁ + k₂ + k₃)/6`. -/
noncomputable def nysW (f : ℝ × ℝ × ℝ → ℝ) (z w w' h k3 : ℝ) : ℝ :=
  w + h * (6 * w' + nysK1 f z w w' h + nysK2 f z w w' h + k3) / 6

/-- **DLMF 3.7.20**, `w′_{n+1} = wₙ′ + (k₁ + 2k₂ + 2k₃ + k₄)/6`. -/
noncomputable def nysWD (f : ℝ × ℝ × ℝ → ℝ) (z w w' h k3 : ℝ) : ℝ :=
  w' + (nysK1 f z w w' h + 2 * nysK2 f z w w' h + 2 * k3 + nysK4 f z w w' h k3) / 6

/-- The jets behind 3.7.20: the `w`-update with `k₃` as printed, and both updates with the
corrected `k₃`, are `O(h⁵)`. -/
theorem nystrom_isBigO {f : ℝ × ℝ × ℝ → ℝ} (hf : ContDiff ℝ 4 f) {w w1 : ℝ → ℝ}
    (hw : ∀ x, HasDerivAt w (w1 x) x) (hw1 : ∀ x, HasDerivAt w1 (f (x, w x, w1 x)) x) (z : ℝ) :
    ((fun h => w (z + h) - nysW f z (w z) (w1 z) h (nysK3 f z (w z) (w1 z) h)) =O[𝓝 0]
      fun h => h ^ 5) ∧
    ((fun h => w (z + h) - nysW f z (w z) (w1 z) h (nysK3' f z (w z) (w1 z) h)) =O[𝓝 0]
      fun h => h ^ 5) ∧
    ((fun h => w1 (z + h) - nysWD f z (w z) (w1 z) h (nysK3' f z (w z) (w1 z) h)) =O[𝓝 0]
      fun h => h ^ 5) := by
  set w0 := w z
  set d0 := w1 z
  set p : ℝ × ℝ × ℝ := (z, w0, d0)
  set κ := taylorCoeff3 f p
  have hκ : κ 0 0 0 = f p := taylorCoeff3_zero f p
  have hwc : Continuous w := continuous_iff_continuousAt.mpr fun x => (hw x).continuousAt
  have hw1c : Continuous w1 := continuous_iff_continuousAt.mpr fun x => (hw1 x).continuousAt
  -- the exact solution
  set F : ℝ → ℝ := fun s => f (z + s, w (z + s), w1 (z + s))
  have hzc : Continuous fun s : ℝ => z + s := continuous_const.add continuous_id
  have hFc : Continuous F :=
    hf.continuous.comp (hzc.prodMk ((hwc.comp hzc).prodMk (hw1c.comp hzc)))
  have hVF : ∀ h, w1 (z + h) - d0 = ∫ s in (0 : ℝ)..h, F s := fun h => by
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => w1 (z + s)) (a := 0)
      (b := h) (f' := F) (fun s _ =>
        ((hw1 (z + s)).comp s ((hasDerivAt_id s).const_add z)).congr_deriv (by simp [F]))
      (hFc.intervalIntegrable _ _)
    simp only [add_zero] at this
    exact this.symm
  set G : ℝ → ℝ := fun s => d0 + (w1 (z + s) - d0)
  have hGc : Continuous G := continuous_const.add ((hw1c.comp hzc).sub continuous_const)
  have hWG : ∀ h, w (z + h) - w0 = ∫ s in (0 : ℝ)..h, G s := fun h => by
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => w (z + s)) (a := 0)
      (b := h) (f' := G) (fun s _ =>
        ((hw (z + s)).comp s ((hasDerivAt_id s).const_add z)).congr_deriv (by simp [G]))
      (hGc.intervalIntegrable _ _)
    simp only [add_zero] at this
    exact this.symm
  have hFe : ∀ h, f (p + (1 * h, w (z + h) - w0, w1 (z + h) - d0)) = F h := fun h => by
    simp only [p, F, Prod.mk_add_mk, one_mul]
    congr 2
    (try congr 1) <;> ring
  have hG : ∀ {m : ℕ} {cv : ℕ → ℝ}, IsJet m (fun h => w1 (z + h) - d0) cv →
      IsJet (m + 1) (fun h => w (z + h) - w0) (jinteg (jconst d0 + cv)) := fun hV =>
    (IsJet.integral hGc ((IsJet.const d0).add hV)).congr_fun fun h => (hWG h).symm
  have step : ∀ {m : ℕ} {cv cw : ℕ → ℝ}, 1 ≤ m → m ≤ 4 → cv 0 = 0 → cw 0 = 0 →
      IsJet m (fun h => w1 (z + h) - d0) cv → IsJet (m + 1) (fun h => w (z + h) - w0) cw →
      IsJet (m + 1) (fun h => w1 (z + h) - d0) (jinteg (compC3 κ 1 cw cv)) :=
    fun hm1 hm4 hcv hcw hV hW =>
      (IsJet.integral hFc ((IsJet.comp_taylor3 hf p 1 hm1 hm4 (hW.mono (Nat.le_succ _)) hV hcw
        hcv).congr_fun hFe)).congr_fun fun h => (hVF h).symm
  have ji0 : ∀ c, jinteg c 0 = 0 := fun c => by simp [jinteg]
  have V1 : IsJet 1 (fun h => w1 (z + h) - d0) (jinteg 0) :=
    (IsJet.integral hFc (isJet_zero_of_continuous hFc)).congr_fun fun h => (hVF h).symm
  have V2 := step le_rfl (by norm_num) (ji0 _) (ji0 _) V1 (hG V1)
  have V3 := step (by norm_num) (by norm_num) (ji0 _) (ji0 _) V2 (hG V2)
  have V4 := step (by norm_num) (by norm_num) (ji0 _) (ji0 _) V3 (hG V3)
  have V5 := step (by norm_num) le_rfl (ji0 _) (ji0 _) V4 (hG V4)
  have W5 := hG V4
  -- the stages
  have hYjet : ∀ {K : ℝ → ℝ} {c : ℕ → ℝ} (b e : ℝ), IsJet 5 K c →
      IsJet 4 (fun h => h * (b + e * K h)) (jshift (jconst b + e • c)) := fun b e hK =>
    ((IsJet.const b).add ((hK.mono (by norm_num : 3 ≤ 5)).const_mul e)).mul_id
  have c0 : ∀ (c : ℕ → ℝ) (b e : ℝ), jshift (jconst b + e • c) 0 = 0 := fun c b e => by
    simp [jshift]
  have c0' : ∀ (c : ℕ → ℝ) (e : ℝ), (e • jshift c) 0 = 0 := fun c e => by simp [jshift]
  have J1 : IsJet 5 (nysK1 f z w0 d0) (jshift (jconst (f p))) :=
    ((IsJet.const (n := 4) (f p)).mul_id).congr_fun fun h => rfl
  have J2 := ((IsJet.comp_taylor3 hf p (1 / 2) (by norm_num) le_rfl (hYjet (d0 / 2) (1 / 8) J1)
    ((J1.mono (by norm_num : 4 ≤ 5)).const_mul (1 / 2)) (c0 _ _ _) (c0' _ _)).mul_id).congr_fun
    (g' := nysK2 f z w0 d0) fun h => by
      simp only [nysK2, p, Prod.mk_add_mk]
      congr 2
      (try congr 1) <;> ring_nf
  have J3 := ((IsJet.comp_taylor3 hf p (1 / 2) (by norm_num) le_rfl (hYjet (d0 / 2) (1 / 8) J2)
    ((J2.mono (by norm_num : 4 ≤ 5)).const_mul (1 / 2)) (c0 _ _ _) (c0' _ _)).mul_id).congr_fun
    (g' := nysK3 f z w0 d0) fun h => by
      simp only [nysK3, p, Prod.mk_add_mk]
      congr 2
      (try congr 1) <;> ring_nf
  have J3' := ((IsJet.comp_taylor3 hf p (1 / 2) (by norm_num) le_rfl (hYjet (d0 / 2) (1 / 8) J1)
    ((J2.mono (by norm_num : 4 ≤ 5)).const_mul (1 / 2)) (c0 _ _ _) (c0' _ _)).mul_id).congr_fun
    (g' := nysK3' f z w0 d0) fun h => by
      simp only [nysK3', p, Prod.mk_add_mk]
      congr 2
      (try congr 1) <;> ring_nf
  have J4' := ((IsJet.comp_taylor3 hf p 1 (by norm_num) le_rfl (hYjet d0 (1 / 2) J3')
    ((J3'.mono (by norm_num : 4 ≤ 5)).const_mul 1) (c0 _ _ _) (c0' _ _)).mul_id).congr_fun
    (g' := fun h => nysK4 f z w0 d0 h (nysK3' f z w0 d0 h)) fun h => by
      simp only [nysK4, p, Prod.mk_add_mk]
      congr 2
      (try congr 1) <;> ring_nf
  have upd : ∀ {K : ℝ → ℝ} {c : ℕ → ℝ}, IsJet 5 K c →
      IsJet 5 (fun h => h * (d0 + (1 / 6) * (nysK1 f z w0 d0 h + nysK2 f z w0 d0 h + K h)))
        (jshift (jconst d0 + (1 / 6 : ℝ) • (jshift (jconst (f p)) + jshift (compC3 κ (1 / 2)
          (jshift (jconst (d0 / 2) + (1 / 8 : ℝ) • jshift (jconst (f p))))
          ((1 / 2 : ℝ) • jshift (jconst (f p)))) + c))) := fun hK =>
    ((IsJet.const d0).add ((((J1.mono (by norm_num : 4 ≤ 5)).add
      (J2.mono (by norm_num : 4 ≤ 5))).add (hK.mono (by norm_num : 4 ≤ 5))).const_mul
      (1 / 6))).mul_id
  refine ⟨?_, ?_, ?_⟩
  · refine isBigO_of_isJet_zero (((W5.mono (by norm_num)).sub (upd J3)).congr_fun
      fun h => ?_) fun i hi => ?_
    · simp only [nysW, w0, d0]; ring
    · interval_cases i <;>
        simp [jinteg, compC3, jshift, jconst, hκ, taylorCoeff3_zero, Pi.smul_apply, Pi.add_apply,
          Pi.sub_apply] <;>
        ring
  · refine isBigO_of_isJet_zero (((W5.mono (by norm_num)).sub (upd J3')).congr_fun
      fun h => ?_) fun i hi => ?_
    · simp only [nysW, w0, d0]; ring
    · interval_cases i <;>
        simp [jinteg, compC3, jshift, jconst, hκ, taylorCoeff3_zero, Pi.smul_apply, Pi.add_apply,
          Pi.sub_apply] <;>
        ring
  · have Jrk := ((((J1.add (J2.const_mul 2)).add (J3'.const_mul 2)).add J4').const_mul (1 / 6))
    refine isBigO_of_isJet_zero ((V5.sub Jrk).congr_fun fun h => ?_) fun i hi => ?_
    · simp only [nysWD, w0, d0]; ring
    · interval_cases i <;>
        simp [jinteg, compC3, jshift, jconst, hκ, taylorCoeff3_zero, Pi.smul_apply, Pi.add_apply,
          Pi.sub_apply] <;>
        ring

/-- **DLMF 3.7.20–3.7.21**, with `k₃` corrected to use `k₁` in its second argument
(`nysK3'`): for `f ∈ C⁴` and a solution of `w″ = f(z, w, w′)`, both updates have local error
`O(h⁵)`. -/
theorem dlmf_3_7_20 {f : ℝ × ℝ × ℝ → ℝ} (hf : ContDiff ℝ 4 f) {w w1 : ℝ → ℝ}
    (hw : ∀ x, HasDerivAt w (w1 x) x) (hw1 : ∀ x, HasDerivAt w1 (f (x, w x, w1 x)) x) (z : ℝ) :
    ((fun h => w (z + h) - nysW f z (w z) (w1 z) h (nysK3' f z (w z) (w1 z) h)) =O[𝓝 0]
      fun h => h ^ 5) ∧
    ((fun h => w1 (z + h) - nysWD f z (w z) (w1 z) h (nysK3' f z (w z) (w1 z) h)) =O[𝓝 0]
      fun h => h ^ 5) :=
  (nystrom_isBigO hf hw hw1 z).2

/-- **DLMF 3.7.20** (first line) with `k₃` as printed: the `w`-update is `O(h⁵)`. -/
theorem dlmf_3_7_20_w {f : ℝ × ℝ × ℝ → ℝ} (hf : ContDiff ℝ 4 f) {w w1 : ℝ → ℝ}
    (hw : ∀ x, HasDerivAt w (w1 x) x) (hw1 : ∀ x, HasDerivAt w1 (f (x, w x, w1 x)) x) (z : ℝ) :
    (fun h => w (z + h) - nysW f z (w z) (w1 z) h (nysK3 f z (w z) (w1 z) h)) =O[𝓝 0]
      fun h => h ^ 5 :=
  (nystrom_isBigO hf hw hw1 z).1

/-- **Erratum in DLMF 3.7.21**: with `k₃` as printed (`h k₂/8` in its second argument), the
`w′`-update of 3.7.20 is not `O(h⁵)`. For `w″ = w`, `w = sinh`, `w′ = cosh`, at `z = 0`, it
differs from the corrected rule by `h⁴/48 + h⁶/192`. -/
theorem dlmf_3_7_21_erratum :
    let f : ℝ × ℝ × ℝ → ℝ := fun q => q.2.1
    ¬ (fun h => Real.cosh (0 + h) - nysWD f 0 (Real.sinh 0) (Real.cosh 0) h
      (nysK3 f 0 (Real.sinh 0) (Real.cosh 0) h)) =O[𝓝 0] fun h => h ^ 5 := by
  intro f hO
  have hf : ContDiff ℝ 4 f := contDiff_fst.comp contDiff_snd
  have hc := (dlmf_3_7_20 hf (w := Real.sinh) (w1 := Real.cosh) (fun x => Real.hasDerivAt_sinh x)
    (fun x => Real.hasDerivAt_cosh x) 0).2
  have hD : ∀ h, nysWD f 0 (Real.sinh 0) (Real.cosh 0) h (nysK3 f 0 (Real.sinh 0) (Real.cosh 0) h) -
      nysWD f 0 (Real.sinh 0) (Real.cosh 0) h (nysK3' f 0 (Real.sinh 0) (Real.cosh 0) h) =
      h ^ 4 / 48 + h ^ 6 / 192 := fun h => by
    simp [nysWD, nysK4, nysK3, nysK3', nysK2, nysK1, f]
    ring
  refine not_isBigO_pow_of_le (c := 1 / 48) (m := 4) (by norm_num) (by norm_num)
    (g := fun h => h ^ 4 / 48 + h ^ 6 / 192) (fun h hh _ => ?_) ((hc.sub hO).congr_left fun h => ?_)
  · rw [abs_of_pos (by positivity)]
    nlinarith [pow_pos hh 6]
  · rw [← hD h]; ring

end SecondOrder

end Azurite.DLMF
