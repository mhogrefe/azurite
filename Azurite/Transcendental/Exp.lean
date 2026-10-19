/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.NumberTheory.Transcendental.Lindemann.AnalyticalPart
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Localization.Integral
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Hermite's theorem: `e` is transcendental

`e = exp 1` is transcendental over `ℚ` (`transcendental_exp_one`), hence so is `e^q` for every
nonzero rational `q` (`transcendental_exp_rat`), and `e`, `e^q` and `ln r` (`r ∈ ℚ_{>0}`, `r ≠ 1`)
are irrational (`irrational_exp_one`, `irrational_exp_rat`, `irrational_log_rat`,
`irrational_log_two`).  The last is what makes the rounding loop of the `AzFloat` constant `ln 2`
provably terminating.

The analytic heart is Mathlib's `LindemannWeierstrass.exp_polynomial_approx` (Hermite's
approximation lemma, after Jacobson, *Basic Algebra I*, §4.12): for `f ∈ ℤ[X]` with `f(0) ≠ 0`
there is `c` such that every prime `p > |f(0)|` admits `nₚ ∈ ℤ` with `p ∤ nₚ` and `gₚ ∈ ℤ[X]`
with `|nₚ e^r − p gₚ(r)| ≤ c^p/(p−1)!` at every complex root `r` of `f`.

From it, Hermite's theorem is short.  Suppose `Q ∈ ℤ[X]` has `Q(0) ≠ 0` and `Q(e) = 0`, say
`∑_{k≤n} a_k e^k = 0`.  Take `f = ∏_{k=1}^{n} (X − k)` (`rootsPoly`), whose roots are `1, …, n`.
Multiplying the relation by `nₚ` and replacing each `nₚ e^k` by `p gₚ(k)` plus an error gives the
integer `E = a₀ nₚ + p ∑_{k≥1} a_k gₚ(k)` with `|E| ≤ (∑ |a_k|) c^p/(p−1)!`, which is `< 1` for
large `p`, so `E = 0` and `p ∣ a₀ nₚ`; as `p ∤ nₚ` and `p > |a₀|`, this is impossible.  A general
nonzero `P` with `P(e) = 0` is reduced to this case by dividing out the power of `X`
(`exists_eq_pow_rootMultiplicity_mul_and_not_dvd`), since `e ≠ 0`.
-/

namespace Azurite

open Polynomial Finset Filter Topology
open scoped Nat

/-! ### The polynomial with roots `1, …, n` -/

/-- `∏_{k<n} (X − (k+1)) ∈ ℤ[X]`, with roots `1, …, n`. -/
noncomputable def rootsPoly (n : ℕ) : ℤ[X] := ∏ k ∈ range n, (X - C ((k : ℤ) + 1))

theorem rootsPoly_ne_zero (n : ℕ) : rootsPoly n ≠ 0 :=
  prod_ne_zero_iff.mpr fun _ _ => X_sub_C_ne_zero _

theorem rootsPoly_eval_zero_ne (n : ℕ) : (rootsPoly n).eval 0 ≠ 0 := by
  rw [rootsPoly, eval_prod]
  exact prod_ne_zero_iff.mpr fun _k _ => by simp; omega

theorem mem_aroots_rootsPoly {n k : ℕ} (hk : k < n) :
    ((k : ℂ) + 1) ∈ (rootsPoly n).aroots ℂ := by
  rw [mem_aroots]
  refine ⟨rootsPoly_ne_zero n, ?_⟩
  rw [rootsPoly, map_prod]
  exact prod_eq_zero (mem_range.mpr hk) (by simp)

/-! ### Hermite's theorem -/

/-- No integer polynomial with nonzero constant term vanishes at `e`. -/
theorem aeval_exp_one_ne_zero {Q : ℤ[X]} (hQ0 : Q.eval 0 ≠ 0) : aeval (Real.exp 1) Q ≠ 0 := by
  intro hQe
  set n := Q.natDegree with hn
  have ha0 : Q.coeff 0 ≠ 0 := by rwa [coeff_zero_eq_eval_zero]
  -- the relation `∑_{k≤n} a_k e^k = 0` over `ℂ`
  have hsum : ∑ k ∈ range (n + 1), (Q.coeff k : ℂ) * Complex.exp k = 0 := by
    have h := congrArg (fun x : ℝ => (x : ℂ)) hQe
    rw [aeval_eq_sum_range] at h
    simp only [Complex.ofReal_sum, Complex.ofReal_zero] at h
    rw [← h]
    refine sum_congr rfl fun k _ => ?_
    simp only [zsmul_eq_mul, Complex.ofReal_mul, Complex.ofReal_intCast, Complex.ofReal_pow,
      Complex.ofReal_exp, Complex.ofReal_one, ← Complex.exp_nat_mul, mul_one]
  have hsum' : (Q.coeff 0 : ℂ)
      + ∑ k ∈ range n, (Q.coeff (k + 1) : ℂ) * Complex.exp ((k : ℂ) + 1) = 0 := by
    rw [sum_range_succ', Nat.cast_zero, Complex.exp_zero, mul_one, add_comm] at hsum
    rw [← hsum]
    congr 1
    exact sum_congr rfl fun k _ => by push_cast; ring_nf
  -- Hermite's approximation lemma for `f = ∏ (X − k)`
  obtain ⟨c, hc⟩ := LindemannWeierstrass.exp_polynomial_approx (rootsPoly n)
    (rootsPoly_eval_zero_ne n)
  set A : ℝ := ∑ k ∈ range n, ‖((Q.coeff (k + 1) : ℤ) : ℂ)‖ with hA
  -- `A c^p/(p−1)! → 0`
  have hlim : Tendsto (fun p : ℕ => A * (c ^ p / ((p - 1)! : ℝ))) atTop (𝓝 0) := by
    have h2 : Tendsto (fun p : ℕ => c ^ (p - 1) / ((p - 1)! : ℝ)) atTop (𝓝 0) :=
      (FloorSemiring.tendsto_pow_div_factorial_atTop c).comp (tendsto_sub_atTop_nat 1)
    have h3 : Tendsto (fun p : ℕ => A * c * (c ^ (p - 1) / ((p - 1)! : ℝ))) atTop (𝓝 0) := by
      simpa using h2.const_mul (A * c)
    refine h3.congr' (eventually_atTop.mpr ⟨1, fun p hp => ?_⟩)
    obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
    simp only [Nat.add_sub_cancel, pow_succ]
    ring
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds one_pos))
  -- a large prime
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes
    (max N (max ((rootsPoly n).eval 0).natAbs (Q.eval 0).natAbs) + 1)
  obtain ⟨nₚ, hnp, gₚ, -, hbound⟩ := hc p (by omega) hp
  -- the values `gₚ(k+1)` are integers
  have hg : ∀ k : ℕ, aeval ((k : ℂ) + 1) gₚ = ((gₚ.eval ((k : ℤ) + 1) : ℤ) : ℂ) := fun k => by
    have e : ((k : ℂ) + 1) = algebraMap ℤ ℂ ((k : ℤ) + 1) := by simp
    rw [e, aeval_algebraMap_apply_eq_algebraMap_eval]
    simp
  -- the integer `E`
  set E : ℤ := Q.coeff 0 * nₚ + p * ∑ k ∈ range n, Q.coeff (k + 1) * gₚ.eval ((k : ℤ) + 1)
    with hEdef
  have hE : (E : ℂ) = ∑ k ∈ range n, (Q.coeff (k + 1) : ℂ)
      * ((p : ℂ) * aeval ((k : ℂ) + 1) gₚ - (nₚ : ℂ) * Complex.exp ((k : ℂ) + 1)) := by
    have e1 : ∑ k ∈ range n, (Q.coeff (k + 1) : ℂ)
        * ((p : ℂ) * aeval ((k : ℂ) + 1) gₚ - (nₚ : ℂ) * Complex.exp ((k : ℂ) + 1))
        = (p : ℂ) * ∑ k ∈ range n, (Q.coeff (k + 1) : ℂ) * aeval ((k : ℂ) + 1) gₚ
          - (nₚ : ℂ) * ∑ k ∈ range n, (Q.coeff (k + 1) : ℂ) * Complex.exp ((k : ℂ) + 1) := by
      rw [mul_sum, mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun k _ => by ring
    rw [e1]
    simp only [hEdef, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_sum, hg]
    linear_combination (nₚ : ℂ) * hsum'
  -- `|E| < 1`, so `E = 0`
  have hEle : ‖(E : ℂ)‖ ≤ A * (c ^ p / ((p - 1)! : ℝ)) := by
    rw [hE, hA, sum_mul]
    refine (norm_sum_le _ _).trans (sum_le_sum fun k hk => ?_)
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hb := hbound (mem_aroots_rootsPoly (mem_range.mp hk))
    rwa [zsmul_eq_mul, nsmul_eq_mul, ← norm_neg, neg_sub] at hb
  have hlt : ‖(E : ℂ)‖ < 1 := hEle.trans_lt (hN p (by omega))
  have hE0 : E = 0 := by
    rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs, ← Int.cast_abs] at hlt
    exact Int.abs_lt_one_iff.mp (by exact_mod_cast hlt)
  -- hence `p ∣ a₀ nₚ`, impossible
  have hdvd : (p : ℤ) ∣ Q.coeff 0 * nₚ := by
    rw [hEdef] at hE0
    exact ⟨-(∑ k ∈ range n, Q.coeff (k + 1) * gₚ.eval ((k : ℤ) + 1)), by linear_combination hE0⟩
  rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd hdvd with h | h
  · have h1 : p ∣ (Q.coeff 0).natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr h
      simpa using this
    have h2 := Nat.le_of_dvd (Int.natAbs_pos.mpr ha0) h1
    rw [coeff_zero_eq_eval_zero] at h2
    omega
  · exact hnp h

/-- **Hermite's theorem**: `e` is transcendental over `ℤ`. -/
theorem transcendental_exp_one_int : Transcendental ℤ (Real.exp 1) := by
  rintro ⟨P, hP0, hPe⟩
  obtain ⟨Q, hPQ, hQ⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd P hP0 0
  rw [map_zero, sub_zero] at hPQ hQ
  have hQ0 : Q.eval 0 ≠ 0 := by rwa [← coeff_zero_eq_eval_zero, Ne, ← X_dvd_iff]
  have hQe : aeval (Real.exp 1) Q = 0 := by
    rw [hPQ, map_mul, map_pow, aeval_X] at hPe
    exact (mul_eq_zero.mp hPe).resolve_left (pow_ne_zero _ (Real.exp_pos 1).ne')
  exact aeval_exp_one_ne_zero hQ0 hQe

/-- **Hermite's theorem**: `e` is transcendental over `ℚ`. -/
theorem transcendental_exp_one : Transcendental ℚ (Real.exp 1) := fun h =>
  transcendental_exp_one_int ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr h)

/-- `e^m` is transcendental for every positive natural `m`. -/
theorem transcendental_exp_nat {m : ℕ} (hm : 0 < m) : Transcendental ℚ (Real.exp m) := by
  intro h
  apply transcendental_exp_one
  refine IsAlgebraic.of_pow hm ?_
  rwa [← Real.exp_nat_mul, mul_one]

/-- `e^q` is transcendental for every nonzero rational `q`. -/
theorem transcendental_exp_rat {q : ℚ} (hq : q ≠ 0) : Transcendental ℚ (Real.exp q) := by
  intro h
  have hnum : q.num ≠ 0 := Rat.num_ne_zero.mpr hq
  have h1 : IsAlgebraic ℚ (Real.exp q.num) := by
    have := h.pow q.den
    rwa [← Real.exp_nat_mul, show (q.den : ℝ) * q = (q.num : ℝ) by
      rw [mul_comm]; exact_mod_cast Rat.mul_den_eq_num q] at this
  have hm : 0 < q.num.natAbs := Int.natAbs_pos.mpr hnum
  apply transcendental_exp_nat hm
  rcases lt_or_gt_of_ne hnum with hneg | hpos
  · have e : (q.num : ℝ) = -(q.num.natAbs : ℝ) := by
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast hneg)]
      ring
    rw [e, Real.exp_neg] at h1
    exact IsAlgebraic.inv_iff.mp h1
  · have e : (q.num : ℝ) = (q.num.natAbs : ℝ) := by
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast hpos)]
    rwa [e] at h1

/-! ### Irrationality -/

theorem irrational_exp_one : Irrational (Real.exp 1) := transcendental_exp_one.irrational

theorem irrational_exp_rat {q : ℚ} (hq : q ≠ 0) : Irrational (Real.exp q) :=
  (transcendental_exp_rat hq).irrational

/-- `ln r` is irrational for every positive rational `r ≠ 1`. -/
theorem irrational_log_rat {r : ℚ} (hr : 0 < r) (hr1 : r ≠ 1) : Irrational (Real.log r) := by
  rintro ⟨q, hq⟩
  have hq0 : q ≠ 0 := by
    rintro rfl
    have : Real.log (r : ℝ) = 0 := by rw [← hq]; simp
    rw [Real.log_eq_zero] at this
    rcases this with h | h | h
    · exact absurd h (by exact_mod_cast hr.ne')
    · exact hr1 (by exact_mod_cast h)
    · have : (0 : ℝ) < r := by exact_mod_cast hr
      linarith
  apply transcendental_exp_rat hq0
  rw [hq, Real.exp_log (by exact_mod_cast hr)]
  exact isAlgebraic_algebraMap r

/-- **`ln 2` is irrational.** -/
theorem irrational_log_two : Irrational (Real.log 2) := by
  simpa using irrational_log_rat (r := 2) (by norm_num) (by norm_num)

end Azurite
