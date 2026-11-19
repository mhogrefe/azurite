/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Feldman.Theorem3
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Data.Nat.Size

/-!
# Fel'dman's Theorem 4: a transcendence measure of `π`

N. I. Fel'dman, *Approximation of certain transcendental numbers. I*, Izv. Akad. Nauk SSSR
Ser. Mat. 15 (1951), 53–74, §2, Theorem 4 (deduced from Theorem 3 as Theorem 2 from
Theorem 1).

* `one_le_norm_aeval_pi_irreducible`: for an irreducible `p ∈ ℤ[X]` of degree `n ≥ 1`, the root
  `ξ` of `p` nearest to `π` has `|π − ξ| ≤ |p(π)| · 2^(n(1 + b + 2Nb))` (Lemma 5), and Theorem 3
  bounds `|π − ξ|` below: `1 ≤ |p(π)| 2^(κ n)`, `κ = 1 + b + 2Nb + 9934848000 N b³`.  The size
  of `p` enters through its Mahler measure `μ`: its height is at most `2ⁿ μ`.
* `feldman_theorem4_mahler`: the exponent `κ n` is additive in the degree and the Mahler measure
  is multiplicative and `≥ 1` on nonzero integer polynomials, so the bound passes to products:
  `1 ≤ |P(π)| 2^(κ deg P)` for every nonzero `P ∈ ℤ[X]` of degree `≤ N` and Mahler measure `≤ μ`
  (induction on the factorization into irreducibles).
* **`pi_measure`**: for `P ≠ 0` of degree `≤ t` and height `≤ 2^t` (`t ≥ 1`), with
  `b = 2 size t + 30`: `1 ≤ |P(π)| · 2^((1 + b + 2tb + 9934848000 t b³) t)`, i.e.
  `|P(π)| ≥ exp(−O(t² log³ t))`: the field `ℚ(π)` has transcendence type `≤ 2 + ε`
  (Lemme 1.3 of Waldschmidt's exposé of Chudnovsky's theorem).
* `transcendental_pi`, `transcendental_pi_real`: `π` is transcendental.
-/

namespace Azurite.Feldman

open Polynomial Finset

/-- The Mahler measure of a nonzero integer polynomial is at least `1`. -/
theorem one_le_mahlerMeasure_toC {P : ℤ[X]} (hP : P ≠ 0) : 1 ≤ (toC P).mahlerMeasure := by
  refine one_le_mahlerMeasure_of_one_le_norm_leadingCoeff ?_
  rw [toC, leadingCoeff_map_of_injective Int.cast_injective, eq_intCast, Complex.norm_intCast]
  exact_mod_cast Int.one_le_abs (leadingCoeff_ne_zero.mpr hP)

/-- The constant `κ` of the measure. -/
def kappa (N b : ℕ) : ℕ := 1 + b + 2 * N * b + 9934848000 * N * b ^ 3

/-- **The measure for an irreducible polynomial.** -/
theorem one_le_norm_aeval_pi_irreducible {p : ℤ[X]} (hp : Irreducible p)
    (hn : p.natDegree ≠ 0) {N b : ℕ} (hnN : p.natDegree ≤ N) (hb1 : 1 ≤ b) {μ : ℝ}
    (hμ : (toC p).mahlerMeasure ≤ μ) (hsz : ((N : ℝ) + 1) * ((2 : ℝ) ^ N * μ) ≤ (2 : ℝ) ^ (N * b))
    (hb : 2 ^ 23 * (N * b) ≤ 2 ^ b) :
    1 ≤ ‖aeval (Real.pi : ℂ) p‖ * (2 : ℝ) ^ (kappa N b * p.natDegree) := by
  set n := p.natDegree with hn_def
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  have hp0' : p ≠ 0 := fun h => hn (by rw [hn_def, h, natDegree_zero])
  have hμ1 : 1 ≤ μ := (one_le_mahlerMeasure_toC hp0').trans hμ
  set H : ℝ := (2 : ℝ) ^ N * μ with hH_def
  have hH0 : 0 ≤ H := by positivity
  -- the height of `p`
  have hH : ∀ i, |(p.coeff i : ℝ)| ≤ H := by
    intro i
    rw [← norm_coeff_toC]
    refine (norm_coeff_le_choose_mul_mahlerMeasure i (toC p)).trans ?_
    rw [natDegree_toC]
    have h1 : ((p.natDegree.choose i : ℕ) : ℝ) ≤ (2 : ℝ) ^ N := by
      have h2 : p.natDegree.choose i ≤ 2 ^ N :=
        (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by norm_num) hnN)
      exact_mod_cast h2
    exact mul_le_mul h1 hμ (mahlerMeasure_nonneg _) (by positivity)
  have hnNr : (n : ℝ) ≤ N := by exact_mod_cast hnN
  have hHN : ((n : ℝ) + 1) * H ≤ (2 : ℝ) ^ (N * b) :=
    (mul_le_mul_of_nonneg_right (by linarith) hH0).trans hsz
  -- the root nearest to `π`
  have hsplit : (toC p).Splits := IsAlgClosed.splits _
  have hp0 : toC p ≠ 0 := fun h => hn (by rw [hn_def, ← natDegree_toC, h, natDegree_zero])
  have hne : (toC p).roots.toFinset.Nonempty := by
    rw [Multiset.toFinset_nonempty]
    intro h0
    have := hsplit.natDegree_eq_card_roots
    rw [h0, natDegree_toC, Multiset.card_zero] at this
    exact hn this
  obtain ⟨ξ, hξmem, hmin⟩ := Finset.exists_min_image (toC p).roots.toFinset
    (fun η => ‖(Real.pi : ℂ) - η‖) hne
  have hroot : ∀ η : ℂ, aeval η p = 0 ↔ η ∈ (toC p).roots.toFinset := fun η => by
    rw [Multiset.mem_toFinset, mem_roots hp0, IsRoot, aeval_eq_eval_toC]
  have hξ : aeval ξ p = 0 := (hroot ξ).mpr hξmem
  have hL5 := norm_aeval_ge_dist_root hp hn hξ (ζ := (Real.pi : ℂ))
    (fun η hη => hmin η ((hroot η).mp hη)) hH
  have hT3 := feldman_theorem3 hp hn hξ hH hnN hb1 hHN hb
  rw [norm_sub_rev] at hT3
  -- the constant of Lemma 5
  have hnb : (n : ℝ) ≤ (2 : ℝ) ^ b := by
    have h1 : n ≤ 2 ^ b := by
      have : N ≤ 2 ^ 23 * (N * b) := by nlinarith [Nat.mul_le_mul_left N hb1]
      omega
    exact_mod_cast h1
  have hnH : (n : ℝ) * H ≤ (2 : ℝ) ^ (N * b) := by nlinarith
  have hb2 : (1 : ℝ) ≤ (2 : ℝ) ^ b * (2 : ℝ) ^ (N * b) := by
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ b := one_le_pow₀ (by norm_num)
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (N * b) := one_le_pow₀ (by norm_num)
    nlinarith
  have hNb1 : (1 : ℝ) ≤ (2 : ℝ) ^ (N * b) := one_le_pow₀ (by norm_num)
  have t1 : (2 : ℝ) ^ (n - 1) ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
  have t2 : ((n : ℝ) * (n * H)) ^ (n - 1) ≤ ((2 : ℝ) ^ b * (2 : ℝ) ^ (N * b)) ^ n :=
    (pow_le_pow_left₀ (by positivity) (mul_le_mul hnb hnH (by positivity) (by positivity)) _).trans
      (pow_le_pow_right₀ hb2 (Nat.sub_le _ _))
  have t3 : (((n : ℝ) + 1) * H) ^ (n - 1) ≤ ((2 : ℝ) ^ (N * b)) ^ n :=
    (pow_le_pow_left₀ (by positivity) hHN _).trans (pow_le_pow_right₀ hNb1 (Nat.sub_le _ _))
  have hconst : (2 : ℝ) ^ (n - 1) * ((n : ℝ) * (n * H)) ^ (n - 1) * (((n : ℝ) + 1) * H) ^ (n - 1)
      ≤ (2 : ℝ) ^ (n + (b + N * b) * n + N * b * n) := by
    calc (2 : ℝ) ^ (n - 1) * ((n : ℝ) * (n * H)) ^ (n - 1) * (((n : ℝ) + 1) * H) ^ (n - 1)
        ≤ (2 : ℝ) ^ n * ((2 : ℝ) ^ b * (2 : ℝ) ^ (N * b)) ^ n * ((2 : ℝ) ^ (N * b)) ^ n := by
          gcongr
      _ = (2 : ℝ) ^ (n + (b + N * b) * n + N * b * n) := by
          simp only [← pow_mul, ← pow_add]
  have hpn := norm_nonneg (aeval (Real.pi : ℂ) p)
  have hΦ0 : (0 : ℝ) < (2 : ℝ) ^ (4 * b * (84000 * N * b) * (29568 * n * b)) := by positivity
  calc (1 : ℝ) ≤ ‖(Real.pi : ℂ) - ξ‖ * (2 : ℝ) ^ (4 * b * (84000 * N * b) * (29568 * n * b)) :=
        hT3
    _ ≤ ‖aeval (Real.pi : ℂ) p‖ * (2 : ℝ) ^ (n + (b + N * b) * n + N * b * n)
          * (2 : ℝ) ^ (4 * b * (84000 * N * b) * (29568 * n * b)) :=
        mul_le_mul_of_nonneg_right (hL5.trans (mul_le_mul_of_nonneg_left hconst hpn)) hΦ0.le
    _ = ‖aeval (Real.pi : ℂ) p‖ * (2 : ℝ) ^ (kappa N b * n) := by
        rw [mul_assoc, ← pow_add]
        congr 2
        unfold kappa
        ring

/-- **Fel'dman's Theorem 4**, with the size measured by the Mahler measure. -/
theorem feldman_theorem4_mahler {N b : ℕ} (hb1 : 1 ≤ b) {μ : ℝ}
    (hsz : ((N : ℝ) + 1) * ((2 : ℝ) ^ N * μ) ≤ (2 : ℝ) ^ (N * b))
    (hb : 2 ^ 23 * (N * b) ≤ 2 ^ b) (P : ℤ[X]) :
    P ≠ 0 → P.natDegree ≤ N → (toC P).mahlerMeasure ≤ μ →
      1 ≤ ‖aeval (Real.pi : ℂ) P‖ * (2 : ℝ) ^ (kappa N b * P.natDegree) := by
  induction P using WfDvdMonoid.induction_on_irreducible with
  | zero => exact fun h => absurd rfl h
  | unit u hu =>
    intro _ _ _
    obtain ⟨r, hr, rfl⟩ := Polynomial.isUnit_iff.mp hu
    rw [natDegree_C, mul_zero, pow_zero, mul_one, aeval_C, eq_intCast, Complex.norm_intCast]
    have : |r| = 1 := Int.isUnit_iff_abs_eq.mp hr
    have h1 : |(r : ℝ)| = 1 := by exact_mod_cast this
    rw [h1]
  | mul a i ha hi ih =>
    intro _ hdeg hM
    have hi0 := hi.ne_zero
    have hdeg' : (i * a).natDegree = i.natDegree + a.natDegree := natDegree_mul hi0 ha
    have hMmul : (toC (i * a)).mahlerMeasure = (toC i).mahlerMeasure * (toC a).mahlerMeasure := by
      rw [toC, Polynomial.map_mul, mahlerMeasure_mul]
    have hMi1 := one_le_mahlerMeasure_toC hi0
    have hMa1 := one_le_mahlerMeasure_toC ha
    rw [hMmul] at hM
    have hMa : (toC a).mahlerMeasure ≤ μ := by nlinarith
    have hMi : (toC i).mahlerMeasure ≤ μ := by nlinarith
    have ha' := ih ha (by omega) hMa
    have hi' : 1 ≤ ‖aeval (Real.pi : ℂ) i‖ * (2 : ℝ) ^ (kappa N b * i.natDegree) := by
      by_cases hid : i.natDegree = 0
      · obtain ⟨c, hc⟩ : ∃ c : ℤ, i = C c := ⟨i.coeff 0, eq_C_of_natDegree_eq_zero hid⟩
        have hc0 : c ≠ 0 := fun h => hi0 (by rw [hc, h, C_0])
        rw [hid, mul_zero, pow_zero, mul_one, hc, aeval_C, eq_intCast, Complex.norm_intCast]
        exact_mod_cast Int.one_le_abs hc0
      · exact one_le_norm_aeval_pi_irreducible hi hid (by omega) hb1 hMi hsz hb
    rw [map_mul, norm_mul, hdeg', mul_add, pow_add]
    have h0 : 0 ≤ ‖aeval (Real.pi : ℂ) i‖ * (2 : ℝ) ^ (kappa N b * i.natDegree) := by positivity
    calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
      _ ≤ (‖aeval (Real.pi : ℂ) i‖ * (2 : ℝ) ^ (kappa N b * i.natDegree))
          * (‖aeval (Real.pi : ℂ) a‖ * (2 : ℝ) ^ (kappa N b * a.natDegree)) :=
          mul_le_mul hi' ha' zero_le_one h0
      _ = ‖aeval (Real.pi : ℂ) i‖ * ‖aeval (Real.pi : ℂ) a‖
          * ((2 : ℝ) ^ (kappa N b * i.natDegree) * (2 : ℝ) ^ (kappa N b * a.natDegree)) := by ring

/-- **A transcendence measure of `π`** (Fel'dman's Theorem 4): for a nonzero `P ∈ ℤ[X]` of
degree `≤ t` and height `≤ 2^t`, `t ≥ 1`, and `b = 2 size t + 30`,
`1 ≤ |P(π)| · 2^(κ(t, b) t)`, `κ(t, b) = 1 + b + 2tb + 9934848000 t b³`. -/
theorem pi_measure {P : ℤ[X]} (hP : P ≠ 0) {t : ℕ} (ht : 1 ≤ t) (hdeg : P.natDegree ≤ t)
    (hH : ∀ i, |(P.coeff i : ℝ)| ≤ (2 : ℝ) ^ t) :
    1 ≤ ‖aeval (Real.pi : ℂ) P‖ * (2 : ℝ) ^ (kappa t (2 * Nat.size t + 30) * t) := by
  set b := 2 * Nat.size t + 30 with hb_def
  have hb1 : 1 ≤ b := by omega
  -- `2^23 t b ≤ 2^b`
  have hsize : t < 2 ^ Nat.size t := Nat.lt_size_self t
  have hb : 2 ^ 23 * (t * b) ≤ 2 ^ b := by
    have h1 : b ≤ 2 ^ (Nat.size t + 5) := by
      have : Nat.size t < 2 ^ Nat.size t := Nat.lt_two_pow_self
      have h2 : 2 ^ (Nat.size t + 5) = 32 * 2 ^ Nat.size t := by ring
      omega
    calc 2 ^ 23 * (t * b) ≤ 2 ^ 23 * (2 ^ Nat.size t * 2 ^ (Nat.size t + 5)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul hsize.le h1)
      _ = 2 ^ (2 * Nat.size t + 28) := by ring
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
  -- the Mahler measure
  set μ : ℝ := ((t : ℝ) + 1) * (2 : ℝ) ^ t with hμ_def
  have hμ : (toC P).mahlerMeasure ≤ μ := by
    refine (mahlerMeasure_le_of_coeff_le (toC P) (H := (2 : ℝ) ^ t)
      (fun i => by rw [norm_coeff_toC]; exact hH i)).trans ?_
    rw [natDegree_toC]
    have : (P.natDegree : ℝ) ≤ t := by exact_mod_cast hdeg
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have ht1 : (t : ℝ) + 1 ≤ (2 : ℝ) ^ t := by
    have : t + 1 ≤ 2 ^ t := Nat.lt_two_pow_self
    exact_mod_cast this
  have hsz : ((t : ℝ) + 1) * ((2 : ℝ) ^ t * μ) ≤ (2 : ℝ) ^ (t * b) := by
    have h4 : (2 : ℝ) ^ (t * 4) ≤ (2 : ℝ) ^ (t * b) :=
      pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left _ (by omega))
    have h0 : (0 : ℝ) < (2 : ℝ) ^ t := by positivity
    calc ((t : ℝ) + 1) * ((2 : ℝ) ^ t * μ)
        ≤ (2 : ℝ) ^ t * ((2 : ℝ) ^ t * ((2 : ℝ) ^ t * (2 : ℝ) ^ t)) := by
          rw [hμ_def]
          gcongr
      _ = (2 : ℝ) ^ (t * 4) := by
          rw [pow_mul]
          ring
      _ ≤ (2 : ℝ) ^ (t * b) := h4
  have h := feldman_theorem4_mahler hb1 hsz hb P hP hdeg hμ
  have hmono : (2 : ℝ) ^ (kappa t b * P.natDegree) ≤ (2 : ℝ) ^ (kappa t b * t) :=
    pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left _ hdeg)
  exact h.trans (mul_le_mul_of_nonneg_left hmono (norm_nonneg _))

/-- **`π` is transcendental.** -/
theorem transcendental_pi : Transcendental ℤ (Real.pi : ℂ) := by
  intro halg
  obtain ⟨P, hP, hroot⟩ := halg
  -- a size `t` for `P`
  obtain ⟨h, hh⟩ : ∃ h : ℕ, ∀ i, |(P.coeff i : ℝ)| ≤ (2 : ℝ) ^ h := by
    obtain ⟨B, hB⟩ : ∃ B : ℕ, ∀ i, (P.coeff i).natAbs ≤ B :=
      ⟨(range (P.natDegree + 1)).sup fun i => (P.coeff i).natAbs, fun i => by
        by_cases hi : i ≤ P.natDegree
        · exact Finset.le_sup (f := fun i => (P.coeff i).natAbs)
            (mem_range.mpr (Nat.lt_succ_of_le hi))
        · rw [coeff_eq_zero_of_natDegree_lt (not_le.mp hi)]
          simp⟩
    refine ⟨B, fun i => ?_⟩
    have h1 : (B : ℝ) ≤ (2 : ℝ) ^ B := by
      have : B ≤ 2 ^ B := Nat.lt_two_pow_self.le
      exact_mod_cast this
    have h2 : |(P.coeff i : ℝ)| = ((P.coeff i).natAbs : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [h2]
    exact (by exact_mod_cast hB i : ((P.coeff i).natAbs : ℝ) ≤ B).trans h1
  set t := max 1 (max P.natDegree h) with ht
  have hm := pi_measure hP (t := t) (le_max_left _ _)
    ((le_max_left _ _).trans (le_max_right _ _))
    (fun i => (hh i).trans (pow_le_pow_right₀ (by norm_num)
      ((le_max_right _ _).trans (le_max_right _ _))))
  rw [hroot, norm_zero, zero_mul] at hm
  exact absurd hm (by norm_num)

/-- `π` is transcendental as a real number. -/
theorem transcendental_pi_real : Transcendental ℤ Real.pi := fun h =>
  transcendental_pi (h.algebraMap (A := ℂ))

end Azurite.Feldman
