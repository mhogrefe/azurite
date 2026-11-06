/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Algebra.Order.Floor

/-!
# Padé approximants of the exponential function (for DLMF §4.9)

The tools behind the continued fractions 4.9.3 and 4.9.4 for `e^z`.

* `expInt u z = ∫₀¹ u(t) e^{tz} dt` for a polynomial `u`, and
  `expPhi α β z = ∫₀¹ t^α (1 − t)^β e^{tz} dt`, with the contiguous relations `expPhi_add`
  (`φ(α,β) = φ(α+1,β) + φ(α,β+1)`) and `z_mul_expPhi` (integration by parts).
* `z_pow_mul_expInt`: repeated integration by parts,
  `z^{N+1} ∫₀¹ u(t)e^{tz} dt = e^z ∑ (−1)ⁱ z^{N−i} u⁽ⁱ⁾(1) − ∑ (−1)ⁱ z^{N−i} u⁽ⁱ⁾(0)` (`deg u ≤ N`).
* The Padé approximants `padeP m k / padeQ m k` of type `[m/k]` and their error
  `e^z Q − P = z^{m+k+1} φ(k, m)` (`padeExp_err`).
* `padeQ_eq`: `Q_{m,k}(z) = (−1)^k (m+k)! S_{m,k}(z)` with
  `S_{m,k}(z) = ∑_{l ≤ k} k^{\underline l}/(m+k)^{\underline l} (−z)^l/l!` (`padeS`).
* `exp_mul_poly_eq_zero`, `IsPolyFun.eq_zero_of_exp_mul`: if `e^z X(z) = Y(z)` for polynomial
  functions `X`, `Y`, then `X = 0`.
* `padeExp_tendsto`: along any sequence of types with `k → ∞` and `k/(m + k) → θ`, the
  normalized denominators tend to `e^{−θz} ≠ 0` and `P/Q → e^z`, for every complex `z`.
-/

open Complex Set Filter Topology Finset Polynomial intervalIntegral
open scoped Real Nat

namespace Azurite.DLMF

/-! ### The integrals `∫₀¹ u(t) e^{tz} dt` -/

/-- `∫₀¹ u(t) e^{tz} dt`. -/
noncomputable def expInt (u : ℂ[X]) (z : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, u.eval (t : ℂ) * exp (t * z)

theorem expInt_integrand_continuous (u : ℂ[X]) (z : ℂ) :
    Continuous fun t : ℝ => u.eval (t : ℂ) * exp (t * z) := by
  have : Continuous fun t : ℝ => u.eval (t : ℂ) :=
    u.differentiable.continuous.comp continuous_ofReal
  fun_prop

theorem expInt_add (u v : ℂ[X]) (z : ℂ) : expInt (u + v) z = expInt u z + expInt v z := by
  simp only [expInt, eval_add, add_mul]
  exact integral_add ((expInt_integrand_continuous u z).intervalIntegrable _ _)
    ((expInt_integrand_continuous v z).intervalIntegrable _ _)

theorem expInt_sub (u v : ℂ[X]) (z : ℂ) : expInt (u - v) z = expInt u z - expInt v z := by
  simp only [expInt, eval_sub, sub_mul]
  exact integral_sub ((expInt_integrand_continuous u z).intervalIntegrable _ _)
    ((expInt_integrand_continuous v z).intervalIntegrable _ _)

theorem expInt_C_mul (c : ℂ) (u : ℂ[X]) (z : ℂ) : expInt (C c * u) z = c * expInt u z := by
  simp only [expInt, eval_mul, eval_C, mul_assoc]
  exact integral_const_mul c _

/-- One integration by parts: `z ∫₀¹ u e^{tz} = u(1)e^z − u(0) − ∫₀¹ u′ e^{tz}`. -/
theorem z_mul_expInt (u : ℂ[X]) (z : ℂ) :
    z * expInt u z = u.eval 1 * exp z - u.eval 0 - expInt (derivative u) z := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => u.eval (t : ℂ) * exp (t * z))
      ((derivative u).eval (t : ℂ) * exp (t * z) + u.eval (t : ℂ) * (z * exp (t * z))) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => u.eval (t : ℂ)) ((derivative u).eval (t : ℂ)) t :=
      (u.hasDerivAt (t : ℂ)).comp_ofReal
    have h2 : HasDerivAt (fun t : ℝ => exp (t * z)) (exp (t * z) * z) t := by
      have := ((hasDerivAt_id t).ofReal_comp.mul_const z).cexp
      simpa using this
    convert h1.mul h2 using 1; ring
  have hint := integral_eq_sub_of_hasDerivAt (a := 0) (b := 1) (fun t _ => hd t)
    (by
      have : Continuous fun t : ℝ =>
          (derivative u).eval (t : ℂ) * exp (t * z) + u.eval (t : ℂ) * (z * exp (t * z)) := by
        have h1 : Continuous fun t : ℝ => (derivative u).eval (t : ℂ) :=
          (derivative u).differentiable.continuous.comp continuous_ofReal
        have h2 : Continuous fun t : ℝ => u.eval (t : ℂ) :=
          u.differentiable.continuous.comp continuous_ofReal
        fun_prop
      exact this.intervalIntegrable _ _)
  rw [integral_add ((expInt_integrand_continuous _ z).intervalIntegrable _ _)
    (by
      have : Continuous fun t : ℝ => u.eval (t : ℂ) * (z * exp (t * z)) := by
        have h2 : Continuous fun t : ℝ => u.eval (t : ℂ) :=
          u.differentiable.continuous.comp continuous_ofReal
        fun_prop
      exact this.intervalIntegrable _ _)] at hint
  have e : ∫ t in (0 : ℝ)..1, u.eval (t : ℂ) * (z * exp (t * z)) = z * expInt u z := by
    rw [expInt, ← integral_const_mul]
    exact integral_congr fun t _ => by ring
  rw [e] at hint
  simp only [ofReal_one, one_mul, ofReal_zero, zero_mul, exp_zero, mul_one] at hint
  rw [show expInt (derivative u) z =
    ∫ t in (0 : ℝ)..1, (derivative u).eval (t : ℂ) * exp (t * z) from rfl]
  linear_combination hint

/-- Repeated integration by parts: for `deg u ≤ N`,
`z^{N+1} ∫₀¹ u e^{tz} = e^z ∑_{i≤N} (−1)ⁱ z^{N−i} u⁽ⁱ⁾(1) − ∑_{i≤N} (−1)ⁱ z^{N−i} u⁽ⁱ⁾(0)`. -/
theorem z_pow_mul_expInt (N : ℕ) : ∀ (u : ℂ[X]), u.natDegree ≤ N → ∀ z : ℂ,
    z ^ (N + 1) * expInt u z =
      exp z * ∑ i ∈ range (N + 1), (-1) ^ i * z ^ (N - i) * (derivative^[i] u).eval 1 -
        ∑ i ∈ range (N + 1), (-1) ^ i * z ^ (N - i) * (derivative^[i] u).eval 0 := by
  induction N with
  | zero =>
    intro u hu z
    have hd : derivative u = 0 := by
      obtain ⟨c, rfl⟩ := natDegree_eq_zero.mp (Nat.le_zero.mp hu)
      simp
    have := z_mul_expInt u z
    rw [hd] at this
    simp only [expInt, eval_zero, zero_mul, integral_zero, sub_zero] at this
    simp only [zero_add, pow_one, Finset.sum_range_one, pow_zero, tsub_zero,
      Function.iterate_zero, id, one_mul, mul_one]
    rw [expInt, this]; ring
  | succ N ih =>
    intro u hu z
    have hd : (derivative u).natDegree ≤ N := by
      have := natDegree_derivative_le u; omega
    have h1 := z_mul_expInt u z
    have h2 := ih (derivative u) hd z
    rw [sum_range_succ' (fun i => (-1) ^ i * z ^ (N + 1 - i) * (derivative^[i] u).eval 1),
      sum_range_succ' (fun i => (-1) ^ i * z ^ (N + 1 - i) * (derivative^[i] u).eval 0)]
    simp only [Function.iterate_succ_apply, pow_succ (-1 : ℂ), Nat.add_sub_add_right,
      tsub_zero, pow_zero, one_mul, Function.iterate_zero, id] at h2 ⊢
    have e1 : z ^ (N + 1 + 1) * expInt u z = z ^ (N + 1) * (z * expInt u z) := by ring
    rw [e1, h1]
    have e2 : ∀ (r : ℂ), ∑ i ∈ range (N + 1), (-1) ^ i * (-1) * z ^ (N - i) *
        (derivative^[i] (derivative u)).eval r =
        -∑ i ∈ range (N + 1), (-1) ^ i * z ^ (N - i) * (derivative^[i] (derivative u)).eval r :=
      fun r => by rw [← sum_neg_distrib]; exact sum_congr rfl fun i _ => by ring
    rw [e2, e2]
    linear_combination (-1 : ℂ) * h2

/-! ### The functions `φ(α, β)` -/

/-- `X^α (1 − X)^β`. -/
noncomputable def phiPoly (α β : ℕ) : ℂ[X] := X ^ α * (1 - X) ^ β

/-- `φ(α, β; z) = ∫₀¹ t^α (1 − t)^β e^{tz} dt`. -/
noncomputable def expPhi (α β : ℕ) (z : ℂ) : ℂ := expInt (phiPoly α β) z

theorem expPhi_add (α β : ℕ) (z : ℂ) :
    expPhi α β z = expPhi (α + 1) β z + expPhi α (β + 1) z := by
  rw [expPhi, expPhi, expPhi, ← expInt_add]
  congr 1
  simp only [phiPoly]; ring

theorem derivative_phiPoly (α β : ℕ) :
    derivative (phiPoly α β) = C (α : ℂ) * phiPoly (α - 1) β - C (β : ℂ) * phiPoly α (β - 1) := by
  simp only [phiPoly, derivative_mul, derivative_pow, derivative_sub,
    derivative_one, derivative_X]
  ring

/-- Integration by parts for `φ`: `zφ(α,β) = [β = 0]e^z − [α = 0] − αφ(α−1,β) + βφ(α,β−1)`. -/
theorem z_mul_expPhi (α β : ℕ) (z : ℂ) :
    z * expPhi α β z = (if β = 0 then exp z else 0) - (if α = 0 then 1 else 0) -
      α * expPhi (α - 1) β z + β * expPhi α (β - 1) z := by
  rw [expPhi, z_mul_expInt, derivative_phiPoly, expInt_sub, expInt_C_mul, expInt_C_mul]
  simp only [expPhi, phiPoly, eval_mul, eval_pow, eval_X, eval_sub, eval_one, one_pow, sub_self,
    zero_pow_eq, sub_zero, one_mul]
  split_ifs <;> simp_all
  ring

/-! ### Padé approximants and their error -/

/-- The Padé denominator `Q_{m,k}(z) = ∑_{i ≤ m+k} (−1)ⁱ z^{m+k−i} u⁽ⁱ⁾(1)`, `u = t^k(1 − t)^m`. -/
noncomputable def padeQ (m k : ℕ) (z : ℂ) : ℂ :=
  ∑ i ∈ range (m + k + 1), (-1) ^ i * z ^ (m + k - i) * (derivative^[i] (phiPoly k m)).eval 1

/-- The Padé numerator `P_{m,k}(z) = ∑_{i ≤ m+k} (−1)ⁱ z^{m+k−i} u⁽ⁱ⁾(0)`. -/
noncomputable def padeP (m k : ℕ) (z : ℂ) : ℂ :=
  ∑ i ∈ range (m + k + 1), (-1) ^ i * z ^ (m + k - i) * (derivative^[i] (phiPoly k m)).eval 0

theorem natDegree_phiPoly (α β : ℕ) : (phiPoly α β).natDegree ≤ α + β := by
  unfold phiPoly
  refine (natDegree_mul_le).trans (add_le_add ((natDegree_pow_le).trans ?_)
    ((natDegree_pow_le).trans ?_))
  · simp
  · have : (1 - X : ℂ[X]).natDegree ≤ 1 := by
      rw [show (1 - X : ℂ[X]) = C 1 - X by simp]
      exact (natDegree_sub_le _ _).trans (by simp)
    nlinarith

/-- **The Padé error**: `e^z Q_{m,k}(z) − P_{m,k}(z) = z^{m+k+1} φ(k, m; z)`. -/
theorem padeExp_err (m k : ℕ) (z : ℂ) :
    exp z * padeQ m k z - padeP m k z = z ^ (m + k + 1) * expPhi k m z := by
  rw [expPhi, z_pow_mul_expInt (m + k) (phiPoly k m) (by
    have := natDegree_phiPoly k m; omega) z]
  rfl

/-! ### `e^z X = Y` forces `X = 0` -/

theorem eq_zero_of_add_derivative_eq_zero {p : ℂ[X]} (h : p + derivative p = 0) : p = 0 := by
  by_contra hp
  have hc := congrArg (fun q => q.coeff p.natDegree) h
  simp only [coeff_add, coeff_derivative, coeff_zero] at hc
  rw [coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < p.natDegree + 1), zero_mul,
    add_zero] at hc
  exact hp (leadingCoeff_eq_zero.mp hc)

/-- If `e^z p(z) = q(z)` for all `z` (polynomials `p`, `q`), then `p = 0`. -/
theorem exp_mul_poly_eq_zero (n : ℕ) : ∀ p q : ℂ[X], q.natDegree ≤ n →
    (∀ z, exp z * p.eval z = q.eval z) → p = 0 := by
  induction n with
  | zero =>
    intro p q hq h
    obtain ⟨c, rfl⟩ := natDegree_eq_zero.mp (Nat.le_zero.mp hq)
    have hd : ∀ z, exp z * (p + derivative p).eval z = 0 := fun z => by
      have h1 : HasDerivAt (fun z => exp z * p.eval z)
          (exp z * p.eval z + exp z * (derivative p).eval z) z :=
        (hasDerivAt_exp z).mul (p.hasDerivAt z)
      have h2 : HasDerivAt (fun z => exp z * p.eval z) 0 z := by
        rw [show (fun z => exp z * p.eval z) = fun _ => c by funext z; rw [h z, eval_C]]
        exact hasDerivAt_const z c
      rw [eval_add, mul_add]; exact h1.unique h2
    apply eq_zero_of_add_derivative_eq_zero
    exact Polynomial.funext fun z => by
      have := hd z; rw [eval_zero]
      exact (mul_eq_zero.mp this).resolve_left (exp_ne_zero z)
  | succ n ih =>
    intro p q hq h
    have hd : ∀ z, exp z * (p + derivative p).eval z = (derivative q).eval z := fun z => by
      have h1 : HasDerivAt (fun z => exp z * p.eval z)
          (exp z * p.eval z + exp z * (derivative p).eval z) z :=
        (hasDerivAt_exp z).mul (p.hasDerivAt z)
      have h2 : HasDerivAt (fun z => exp z * p.eval z) ((derivative q).eval z) z := by
        rw [show (fun z => exp z * p.eval z) = fun z => q.eval z from funext h]
        exact q.hasDerivAt z
      rw [eval_add, mul_add]; exact h1.unique h2
    apply eq_zero_of_add_derivative_eq_zero
    exact ih _ _ ((natDegree_derivative_le q).trans (by omega)) hd

/-- Functions of `z` given by a polynomial. -/
def IsPolyFun (f : ℂ → ℂ) : Prop := ∃ p : ℂ[X], ∀ z, f z = p.eval z

theorem IsPolyFun.add {f g : ℂ → ℂ} (hf : IsPolyFun f) (hg : IsPolyFun g) :
    IsPolyFun fun z => f z + g z := by
  obtain ⟨p, hp⟩ := hf; obtain ⟨q, hq⟩ := hg
  exact ⟨p + q, fun z => by simp only [hp, hq, eval_add]⟩

theorem IsPolyFun.sub {f g : ℂ → ℂ} (hf : IsPolyFun f) (hg : IsPolyFun g) :
    IsPolyFun fun z => f z - g z := by
  obtain ⟨p, hp⟩ := hf; obtain ⟨q, hq⟩ := hg
  exact ⟨p - q, fun z => by simp only [hp, hq, eval_sub]⟩

theorem IsPolyFun.mul {f g : ℂ → ℂ} (hf : IsPolyFun f) (hg : IsPolyFun g) :
    IsPolyFun fun z => f z * g z := by
  obtain ⟨p, hp⟩ := hf; obtain ⟨q, hq⟩ := hg
  exact ⟨p * q, fun z => by simp only [hp, hq, eval_mul]⟩

theorem isPolyFun_const (c : ℂ) : IsPolyFun fun _ => c := ⟨C c, fun z => by simp⟩

theorem isPolyFun_id : IsPolyFun fun z => z := ⟨X, fun z => by simp⟩

theorem isPolyFun_sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℂ} (hf : ∀ i ∈ s, IsPolyFun (f i)) :
    IsPolyFun fun z => ∑ i ∈ s, f i z := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun z => by simp⟩
  | insert a s ha ih =>
    simp only [sum_insert ha]
    exact (hf a (mem_insert_self a s)).add (ih fun i hi => hf i (mem_insert_of_mem hi))

theorem isPolyFun_pow (n : ℕ) : IsPolyFun fun z : ℂ => z ^ n := ⟨X ^ n, fun z => by simp⟩

theorem isPolyFun_padeQ (m k : ℕ) : IsPolyFun (padeQ m k) := by
  unfold padeQ
  exact isPolyFun_sum _ fun i _ => ((isPolyFun_const _).mul (isPolyFun_pow _)).mul
    (isPolyFun_const _)

theorem isPolyFun_padeP (m k : ℕ) : IsPolyFun (padeP m k) := by
  unfold padeP
  exact isPolyFun_sum _ fun i _ => ((isPolyFun_const _).mul (isPolyFun_pow _)).mul
    (isPolyFun_const _)

/-- If `e^z f(z) = g(z)` for polynomial functions `f`, `g`, then `f = 0`. -/
theorem IsPolyFun.eq_zero_of_exp_mul {f g : ℂ → ℂ} (hf : IsPolyFun f) (hg : IsPolyFun g)
    (h : ∀ z, exp z * f z = g z) : ∀ z, f z = 0 := by
  obtain ⟨p, hp⟩ := hf; obtain ⟨q, hq⟩ := hg
  have := exp_mul_poly_eq_zero q.natDegree p q le_rfl fun z => by rw [← hp, ← hq, h]
  intro z; rw [hp, this, eval_zero]

/-! ### The explicit denominator -/

theorem iterate_derivative_eval_eq (u : ℂ[X]) (i : ℕ) (r : ℂ) :
    (derivative^[i] u).eval r = i ! * (taylor r u).coeff i := by
  have h := congrFun (factorial_smul_hasseDeriv (R := ℂ) (k := i)) u
  rw [← h, LinearMap.smul_apply, eval_smul, nsmul_eq_mul, taylor_coeff]

theorem taylor_one_phiPoly (k m : ℕ) :
    taylor 1 (phiPoly k m) = (-1 : ℂ[X]) ^ m * (X ^ m * (X + 1) ^ k) := by
  simp only [phiPoly, taylor_mul, taylor_pow, taylor_X, map_sub, taylor_one, map_one]
  ring

theorem phiPoly_derivative_one (m k i : ℕ) :
    (derivative^[i] (phiPoly k m)).eval 1 =
      i ! * ((-1) ^ m * if m ≤ i then (k.choose (i - m) : ℂ) else 0) := by
  rw [iterate_derivative_eval_eq, taylor_one_phiPoly, ← C_1, ← C_neg, ← C_pow, coeff_C_mul,
    mul_comm (X ^ m), coeff_mul_X_pow', C_1, coeff_X_add_one_pow]

/-- The normalized denominator `S_{m,k}(z) = ∑_{l ≤ k} k^{\underline l}/(m+k)^{\underline l}
(−z)^l/l!`. -/
noncomputable def padeS (m k : ℕ) (z : ℂ) : ℂ :=
  ∑ l ∈ range (k + 1), (k.descFactorial l : ℂ) / ((m + k).descFactorial l : ℂ) * (-z) ^ l / l !

/-- `Q_{m,k}(z) = (−1)^k (m+k)! S_{m,k}(z)`. -/
theorem padeQ_eq (m k : ℕ) (z : ℂ) : padeQ m k z = (-1) ^ k * (m + k)! * padeS m k z := by
  unfold padeQ padeS
  simp only [phiPoly_derivative_one]
  rw [← sum_range_reflect, Finset.mul_sum]
  -- split off the vanishing terms `l > k`
  have hsplit : range (m + k + 1) = range (k + 1) ∪ Ico (k + 1) (m + k + 1) := by
    rw [range_eq_Ico, range_eq_Ico, Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)]
  rw [hsplit, sum_union (by
    rw [range_eq_Ico]; exact Ico_disjoint_Ico_consecutive _ _ _)]
  rw [sum_eq_zero (s := Ico (k + 1) (m + k + 1)) fun l hl => by
    rw [Finset.mem_Ico] at hl
    rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega))]; simp, add_zero]
  refine sum_congr rfl fun l hl => ?_
  rw [Finset.mem_range] at hl
  have hl' : l ≤ k := by omega
  have hm : m ≤ m + k + 1 - 1 - l := by omega
  simp only [hm, ↓reduceIte]
  have h1 : m + k + 1 - 1 - l = m + k - l := by omega
  have h2 : m + k - (m + k - l) = l := by omega
  have h3 : m + k - l - m = k - l := by omega
  rw [h1, h2, h3, Nat.choose_symm hl']
  have hd : ((m + k).descFactorial l : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr (by omega) |>.ne')
  have hf := Nat.factorial_mul_descFactorial (n := m + k) (k := l) (by omega)
  have hc := Nat.descFactorial_eq_factorial_mul_choose k l
  have hf' : ((m + k - l)! : ℂ) * ((m + k).descFactorial l : ℂ) = ((m + k)! : ℂ) := by
    exact_mod_cast hf
  rw [hc, ← hf']
  push_cast
  have hl0 : (l ! : ℂ) ≠ 0 := by exact_mod_cast l.factorial_ne_zero
  rw [neg_pow, show ((-1 : ℂ) ^ (m + k - l)) = (-1) ^ k * (-1) ^ m * (-1) ^ l by
    rw [← pow_add, ← pow_add, show m + k - l = (k + m + l) - 2 * l by omega]
    rw [pow_sub₀ _ (by norm_num) (by omega), pow_mul]; norm_num]
  field_simp
  ring_nf
  rw [mul_comm m 2, pow_mul]
  norm_num

/-! ### Convergence -/

theorem norm_expPhi_le (α β : ℕ) (z : ℂ) : ‖expPhi α β z‖ ≤ Real.exp ‖z‖ := by
  have h := norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := Real.exp ‖z‖)
    (f := fun t : ℝ => (phiPoly α β).eval (t : ℂ) * exp (t * z)) (fun t ht => by
      rw [uIoc_of_le zero_le_one] at ht
      simp only [phiPoly, eval_mul, eval_pow, eval_X, eval_sub, eval_one, norm_mul, norm_pow,
        norm_exp]
      have h1 : ‖(t : ℂ)‖ ≤ 1 := by
        rw [norm_real, Real.norm_eq_abs, abs_of_pos ht.1]; exact ht.2
      have h2 : ‖1 - (t : ℂ)‖ ≤ 1 := by
        rw [← ofReal_one, ← ofReal_sub, norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by linarith [ht.2])]
        linarith [ht.1]
      have h3 : Real.exp ((t : ℂ) * z).re ≤ Real.exp ‖z‖ := by
        apply Real.exp_le_exp.mpr
        rw [re_ofReal_mul]
        have := abs_le.mp (abs_re_le_norm z)
        nlinarith [ht.1, ht.2, norm_nonneg z]
      have ha : ‖(t : ℂ)‖ ^ α ≤ 1 := pow_le_one₀ (norm_nonneg _) h1
      have hb : ‖1 - (t : ℂ)‖ ^ β ≤ 1 := pow_le_one₀ (norm_nonneg _) h2
      calc ‖(t : ℂ)‖ ^ α * ‖1 - (t : ℂ)‖ ^ β * Real.exp ((t : ℂ) * z).re
          ≤ 1 * 1 * Real.exp ‖z‖ := by
            apply mul_le_mul (mul_le_mul ha hb (by positivity) zero_le_one) h3 (by positivity)
              (by norm_num)
        _ = Real.exp ‖z‖ := by ring)
  rw [expPhi, expInt]
  simpa using h

/-- The terms `k^{\underline l}/(m+k)^{\underline l} (−z)^l/l!` of `S_{m,k}`. -/
noncomputable def padeSTerm (m k : ℕ) (z : ℂ) (l : ℕ) : ℂ :=
  (k.descFactorial l : ℂ) / ((m + k).descFactorial l : ℂ) * (-z) ^ l / l !

theorem padeS_eq_tsum (m k : ℕ) (z : ℂ) : padeS m k z = ∑' l, padeSTerm m k z l := by
  rw [tsum_eq_sum (s := range (k + 1)) fun l hl => by
    rw [Finset.mem_range, not_lt] at hl
    simp [padeSTerm, Nat.descFactorial_eq_zero_iff_lt.mpr (by omega : k < l)]]
  rfl

theorem norm_padeSTerm_le (m k : ℕ) (z : ℂ) (l : ℕ) :
    ‖padeSTerm m k z l‖ ≤ ‖z‖ ^ l / l ! := by
  unfold padeSTerm
  rw [norm_div, norm_mul, norm_div, norm_pow, norm_neg]
  simp only [norm_natCast]
  have hle : (k.descFactorial l : ℝ) ≤ ((m + k).descFactorial l : ℝ) := by
    exact_mod_cast Nat.descFactorial_le l (by omega)
  have hr : (k.descFactorial l : ℝ) / ((m + k).descFactorial l : ℝ) ≤ 1 := by
    rcases Nat.eq_zero_or_pos ((m + k).descFactorial l) with h | h
    · rw [h]; simp
    · exact (div_le_one (by exact_mod_cast h)).mpr hle
  have hf : (0 : ℝ) < l ! := by exact_mod_cast l.factorial_pos
  rw [div_le_div_iff_of_pos_right hf]
  calc (k.descFactorial l : ℝ) / ((m + k).descFactorial l : ℝ) * ‖z‖ ^ l ≤ 1 * ‖z‖ ^ l :=
        mul_le_mul_of_nonneg_right hr (by positivity)
    _ = ‖z‖ ^ l := one_mul _

/-- Along types with `k → ∞` and `k/(m + k) → θ`, `k^{\underline l}/(m+k)^{\underline l} → θ^l`. -/
theorem descFactorial_ratio_tendsto {m k : ℕ → ℕ} {θ : ℝ} (hk : Tendsto k atTop atTop)
    (hθ : Tendsto (fun n => (k n : ℝ) / (m n + k n)) atTop (𝓝 θ)) (l : ℕ) :
    Tendsto (fun n => ((k n).descFactorial l : ℝ) / ((m n + k n).descFactorial l : ℝ)) atTop
      (𝓝 (θ ^ l)) := by
  have hN : Tendsto (fun n => ((m n + k n : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_atTop_mono (fun n => by omega) hk)
  have hfac : ∀ i : ℕ, Tendsto (fun n => (((k n - i : ℕ) : ℝ)) / ((m n + k n - i : ℕ) : ℝ))
      atTop (𝓝 θ) := by
    intro i
    have hinv : Tendsto (fun n => (i : ℝ) / ((m n + k n : ℕ) : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hN
    have h := (hθ.sub hinv).div (tendsto_const_nhds.sub hinv) (by norm_num : (1 : ℝ) - 0 ≠ 0)
    rw [sub_zero, sub_zero, div_one] at h
    refine h.congr' ?_
    filter_upwards [hk.eventually_ge_atTop (i + 1)] with n hn
    simp only [Pi.div_apply]
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    have hpos : (0 : ℝ) < (m n : ℝ) + k n := by
      have : (i : ℝ) + 1 ≤ k n := by exact_mod_cast hn
      have : (0 : ℝ) ≤ m n := by positivity
      have : (0 : ℝ) ≤ i := by positivity
      linarith
    have hne : (m n : ℝ) + k n - i ≠ 0 := by
      have : (i : ℝ) + 1 ≤ k n := by exact_mod_cast hn
      have : (0 : ℝ) ≤ m n := by positivity
      linarith
    push_cast
    field_simp
  have hprod := tendsto_finsetProd (range l) fun i _ => hfac i
  simp only [prod_const, card_range] at hprod
  refine hprod.congr' ?_
  filter_upwards [hk.eventually_ge_atTop l] with n hn
  rw [Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_prod_range]
  push_cast
  rw [← prod_div_distrib]

/-- **Normalized denominators**: `S_{m,k}(z) → e^{−θz}`. -/
theorem padeS_tendsto {m k : ℕ → ℕ} {θ : ℝ} (hk : Tendsto k atTop atTop)
    (hθ : Tendsto (fun n => (k n : ℝ) / (m n + k n)) atTop (𝓝 θ)) (z : ℂ) :
    Tendsto (fun n => padeS (m n) (k n) z) atTop (𝓝 (exp (-(θ * z)))) := by
  have hser : HasSum (fun l : ℕ => (θ : ℂ) ^ l * (-z) ^ l / l !) (exp (-(θ * z))) := by
    have := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℂ) (-(θ * z))
    rw [← exp_eq_exp_ℂ] at this
    convert this using 2 with l
    rw [neg_mul_eq_mul_neg, mul_pow]
  rw [← hser.tsum_eq]
  simp only [padeS_eq_tsum]
  refine tendsto_tsum_of_dominated_convergence (bound := fun l => ‖z‖ ^ l / l !)
    (Real.summable_pow_div_factorial ‖z‖) (fun l => ?_)
    (Eventually.of_forall fun n l => norm_padeSTerm_le _ _ z l)
  have h := ((continuous_ofReal.tendsto _).comp (descFactorial_ratio_tendsto hk hθ l))
  have := (h.mul_const ((-z) ^ l)).div_const (l ! : ℂ)
  simp only [Function.comp_def, ofReal_pow] at this
  refine this.congr fun n => ?_
  simp only [padeSTerm]
  push_cast
  ring_nf

/-- **Convergence of the Padé approximants of `e^z`**: along types `[mₙ/kₙ]` with `kₙ → ∞` and
`kₙ/(mₙ + kₙ) → θ`, the denominators are eventually nonzero and `P/Q → e^z`, for every `z ∈ ℂ`. -/
theorem padeExp_tendsto {m k : ℕ → ℕ} {θ : ℝ} (hk : Tendsto k atTop atTop)
    (hθ : Tendsto (fun n => (k n : ℝ) / (m n + k n)) atTop (𝓝 θ)) (z : ℂ) :
    (∀ᶠ n in atTop, padeQ (m n) (k n) z ≠ 0) ∧
      Tendsto (fun n => padeP (m n) (k n) z / padeQ (m n) (k n) z) atTop (𝓝 (exp z)) := by
  have hS := padeS_tendsto hk hθ z
  have hS0 : ∀ᶠ n in atTop, padeS (m n) (k n) z ≠ 0 := hS.eventually_ne (exp_ne_zero _)
  have hQ0 : ∀ᶠ n in atTop, padeQ (m n) (k n) z ≠ 0 := hS0.mono fun n h => by
    rw [padeQ_eq]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast
      (Nat.factorial_ne_zero _))) h
  refine ⟨hQ0, ?_⟩
  -- `e^z − P/Q = z^{N+1} φ/Q`, bounded by `|z|^{N+1} e^{|z|}/(N! |S|)`
  have hN : Tendsto (fun n => m n + k n) atTop atTop := tendsto_atTop_mono (fun n => by omega) hk
  have hpow : Tendsto (fun n => ‖z‖ ^ (m n + k n) / ((m n + k n)! : ℝ)) atTop (𝓝 0) :=
    (FloorSemiring.tendsto_pow_div_factorial_atTop ‖z‖).comp hN
  have hSn : Tendsto (fun n => ‖padeS (m n) (k n) z‖) atTop (𝓝 ‖exp (-(θ * z))‖) := hS.norm
  have hbound := ((hpow.mul_const (‖z‖ * Real.exp ‖z‖)).div hSn
    (norm_ne_zero_iff.mpr (exp_ne_zero _)))
  rw [zero_mul, zero_div] at hbound
  rw [← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_norm_tendsto_zero]
  have hneg : Tendsto (fun n => ‖exp z - padeP (m n) (k n) z / padeQ (m n) (k n) z‖) atTop
      (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hbound
    filter_upwards [hQ0, hS0] with n hQ hS'
    have herr := padeExp_err (m n) (k n) z
    have e : exp z - padeP (m n) (k n) z / padeQ (m n) (k n) z =
        z ^ (m n + k n + 1) * expPhi (k n) (m n) z / padeQ (m n) (k n) z := by
      rw [← herr]; field_simp
    show _ ≤ ‖z‖ ^ (m n + k n) / ((m n + k n)! : ℝ) * (‖z‖ * Real.exp ‖z‖) /
      ‖padeS (m n) (k n) z‖
    rw [e, padeQ_eq, norm_div, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, norm_neg,
      norm_one, one_pow, one_mul, norm_natCast, pow_succ]
    have hφ := norm_expPhi_le (k n) (m n) z
    have hSpos : 0 < ‖padeS (m n) (k n) z‖ := norm_pos_iff.mpr hS'
    have hfpos : (0 : ℝ) < ((m n + k n)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
    calc ‖z‖ ^ (m n + k n) * ‖z‖ * ‖expPhi (k n) (m n) z‖ /
          (((m n + k n)! : ℝ) * ‖padeS (m n) (k n) z‖)
        = ‖z‖ ^ (m n + k n) / ((m n + k n)! : ℝ) * (‖z‖ * ‖expPhi (k n) (m n) z‖) /
          ‖padeS (m n) (k n) z‖ := by field_simp
      _ ≤ ‖z‖ ^ (m n + k n) / ((m n + k n)! : ℝ) * (‖z‖ * Real.exp ‖z‖) /
          ‖padeS (m n) (k n) z‖ := by gcongr
  refine hneg.congr fun n => ?_
  rw [← norm_neg, neg_sub]

end Azurite.DLMF
