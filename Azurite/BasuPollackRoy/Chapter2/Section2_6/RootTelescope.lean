/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_6.LimitSeries
import Azurite.BasuPollackRoy.Chapter2.Section2_6.RecursionInvariants

/-! # BPR §2.6 — telescoping the root through the recursion

With the limit `x̄` in hand, the root of `P₀` is reached by peeling off one substitution at a time.
Write `ηₙ = Σ_{k≤n} ξₖ` and the partial sum `Sⱼ = Σ_{n<j} xₙ ε^{ηₙ}`. The *tail root* at level `j`
is `ρⱼ = ε^{−η_{j-1}}·(x̄ − Sⱼ)` (with `η_{-1} = 0`), which satisfies the recursion

> `ρⱼ = ε^{ξⱼ}(xⱼ + ρ_{j+1})`  (pure field algebra),

with `ρ₀ = x̄`. Combined with `substPoly_eval` this telescopes `P₀.eval x̄` into
`ε^{Σ_{k<j}βₖ}·Pⱼ.eval ρⱼ`, whose order exceeds `Σ_{k<j}βₖ → ∞`, forcing `P₀.eval x̄ = 0`. -/

namespace Azurite.BPR

open Polynomial HahnSeries

variable {R : Type*} [Field R] [IsRealClosed R]

/-- `η_{j-1} = ξ₀ + ⋯ + ξ_{j-1}` (the exponent shift at level `j`; `prevEta 0 = 0`). -/
noncomputable def prevEta (s0 : RecState R) (j : ℕ) : ℚ := ∑ k ∈ Finset.range j, xiSeq s0 k

theorem prevEta_succ (s0 : RecState R) (j : ℕ) :
    prevEta s0 (j + 1) = prevEta s0 j + xiSeq s0 j := Finset.sum_range_succ _ _

/-- `ηₙ = η_{(n+1)-1}`: the cumulative exponent is the next shift. -/
theorem etaSeq_eq_prevEta_succ (s0 : RecState R) (n : ℕ) : etaSeq s0 n = prevEta s0 (n + 1) := rfl

/-- The partial sum `Sⱼ = Σ_{n<j} xₙ ε^{ηₙ}`. -/
noncomputable def partialSumP (s0 : RecState R) (j : ℕ) : PuiseuxSeries R :=
  ∑ n ∈ Finset.range j, constPuiseux (xSeq s0 n) * puiseuxMonomial (etaSeq s0 n)

theorem partialSumP_succ (s0 : RecState R) (j : ℕ) :
    partialSumP s0 (j + 1)
      = partialSumP s0 j + constPuiseux (xSeq s0 j) * puiseuxMonomial (etaSeq s0 j) :=
  Finset.sum_range_succ _ _

/-- The tail root `ρⱼ = ε^{−η_{j-1}}·(x̄ − Sⱼ)`. -/
noncomputable def rho (s0 : RecState R) (hnb : ∀ n, (stateSeq s0 n).poly.coeff 0 ≠ 0) (j : ℕ) :
    PuiseuxSeries R :=
  puiseuxMonomial (-(prevEta s0 j)) * (xbarP s0 hnb - partialSumP s0 j)

theorem rho_zero (s0 : RecState R) (hnb : ∀ n, (stateSeq s0 n).poly.coeff 0 ≠ 0) :
    rho s0 hnb 0 = xbarP s0 hnb := by
  rw [rho, prevEta, Finset.sum_range_zero, neg_zero, puiseuxMonomial_zero, partialSumP,
    Finset.sum_range_zero, sub_zero, one_mul]

/-- **The tail recursion** `ρⱼ = ε^{ξⱼ}(xⱼ + ρ_{j+1})` — pure field algebra. -/
theorem rho_succ_eq (s0 : RecState R) (hnb : ∀ n, (stateSeq s0 n).poly.coeff 0 ≠ 0) (j : ℕ) :
    rho s0 hnb j
      = puiseuxMonomial (xiSeq s0 j) * (constPuiseux (xSeq s0 j) + rho s0 hnb (j + 1)) := by
  -- `ε^{−η_{j-1}}·ε^{ηⱼ} = ε^{ξⱼ}`, since `ηⱼ = η_{j-1} + ξⱼ`
  have hkey : puiseuxMonomial (-(prevEta s0 j)) * puiseuxMonomial (etaSeq s0 j)
      = (puiseuxMonomial (xiSeq s0 j) : PuiseuxSeries R) := by
    rw [puiseuxMonomial_mul, etaSeq_eq_prevEta_succ, prevEta_succ]; congr 1; ring
  -- `ε^{ξⱼ}·ε^{−η_j} = ε^{−η_{j-1}}`
  have hsplit : puiseuxMonomial (xiSeq s0 j) * puiseuxMonomial (-(prevEta s0 (j + 1)))
      = (puiseuxMonomial (-(prevEta s0 j)) : PuiseuxSeries R) := by
    rw [puiseuxMonomial_mul, prevEta_succ]; congr 1; ring
  simp only [rho]
  rw [partialSumP_succ, mul_add,
    ← mul_assoc (puiseuxMonomial (xiSeq s0 j)) (puiseuxMonomial (-(prevEta s0 (j + 1)))), hsplit]
  linear_combination (constPuiseux (xSeq s0 j)) * hkey

/-- The single monomial `xₙ ε^{ηₙ}` as a Hahn series. -/
theorem partialSumP_term_coe (s0 : RecState R) (n : ℕ) :
    ((constPuiseux (xSeq s0 n) * puiseuxMonomial (etaSeq s0 n) : PuiseuxSeries R)
        : HahnSeries ℚ R) = HahnSeries.single (etaSeq s0 n) (xSeq s0 n) := by
  rw [Subfield.coe_mul, coe_constPuiseux, coe_puiseuxMonomial, HahnSeries.single_mul_single,
    mul_one, zero_add]

theorem partialSumP_coeff_eta (s0 : RecState R) (hnb : ∀ n, (stateSeq s0 n).poly.coeff 0 ≠ 0)
    (n m : ℕ) (h : n < m) :
    ((partialSumP s0 m : PuiseuxSeries R) : HahnSeries ℚ R).coeff (etaSeq s0 n) = xSeq s0 n := by
  rw [partialSumP, AddSubmonoidClass.coe_finsetSum, HahnSeries.coeff_sum, Finset.sum_eq_single n]
  · rw [partialSumP_term_coe, HahnSeries.coeff_single_same]
  · intro b _ hbn
    rw [partialSumP_term_coe,
      HahnSeries.coeff_single_of_ne (fun heq => hbn ((strictMono_etaSeq s0 hnb).injective heq).symm)]
  · intro hn; exact absurd (Finset.mem_range.mpr h) hn

theorem partialSumP_coeff_notMem (s0 : RecState R) (m : ℕ) {d : ℚ} (h : ∀ n, d ≠ etaSeq s0 n) :
    ((partialSumP s0 m : PuiseuxSeries R) : HahnSeries ℚ R).coeff d = 0 := by
  rw [partialSumP, AddSubmonoidClass.coe_finsetSum, HahnSeries.coeff_sum]
  refine Finset.sum_eq_zero (fun n _ => ?_)
  rw [partialSumP_term_coe, HahnSeries.coeff_single_of_ne (h n)]

/-- The tail `x̄ − Sₘ` has no coefficient below `ηₘ`. -/
theorem tail_coeff_lt (s0 : RecState R) (hnb : ∀ n, (stateSeq s0 n).poly.coeff 0 ≠ 0) (m : ℕ)
    {d : ℚ} (hd : d < etaSeq s0 m) :
    ((xbarP s0 hnb - partialSumP s0 m : PuiseuxSeries R) : HahnSeries ℚ R).coeff d = 0 := by
  rw [Subfield.coe_sub, HahnSeries.coeff_sub, xbarP_coe]
  by_cases h : ∃ n, d = etaSeq s0 n
  · obtain ⟨n, rfl⟩ := h
    have hnm : n < m := (strictMono_etaSeq s0 hnb).lt_iff_lt.mp hd
    rw [xbar_coeff_eta, partialSumP_coeff_eta s0 hnb n m hnm, sub_self]
  · push Not at h
    rw [xbar_coeff_notMem s0 hnb h, partialSumP_coeff_notMem s0 m h, sub_zero]

/-- **The tail root has strictly positive order**, so it can feed the order jump (Lemma 2.95b). -/
theorem rho_order_pos (s0 : RecState R) (hnb : ∀ n, (stateSeq s0 n).poly.coeff 0 ≠ 0) (j : ℕ) :
    (0 : WithTop ℚ) < puiseuxOrder R (rho s0 hnb (j + 1)) := by
  -- order of the tail is at least `η_{j+1}`
  have hge : (etaSeq s0 (j + 1) : WithTop ℚ)
      ≤ puiseuxOrder R (xbarP s0 hnb - partialSumP s0 (j + 1)) := by
    rw [puiseuxOrder, HahnSeries.le_orderTop_iff_forall]
    intro d hdlt
    exact tail_coeff_lt s0 hnb (j + 1) (by exact_mod_cast hdlt)
  rw [rho, puiseuxOrder_mul, puiseuxOrder_puiseuxMonomial]
  -- `−η_{j-1} + η_{j+1} = ξ_{j+1}` (a `ℚ` identity)
  have hηsucc : -(prevEta s0 (j + 1)) + etaSeq s0 (j + 1) = xiSeq s0 (j + 1) := by
    simp only [etaSeq, prevEta, Finset.sum_range_succ]; ring
  have key : (↑(-(prevEta s0 (j + 1))) : WithTop ℚ) + ↑(etaSeq s0 (j + 1))
      = ↑(xiSeq s0 (j + 1)) := by rw [← WithTop.coe_add, hηsucc]
  calc (0 : WithTop ℚ) < ↑(xiSeq s0 (j + 1)) := by exact_mod_cast xiSeq_pos s0 hnb (j + 1)
    _ = ↑(-(prevEta s0 (j + 1))) + ↑(etaSeq s0 (j + 1)) := key.symm
    _ ≤ ↑(-(prevEta s0 (j + 1))) + puiseuxOrder R (xbarP s0 hnb - partialSumP s0 (j + 1)) := by
        gcongr

/-- The recentered next polynomial is `substPoly` of the current one. -/
theorem stateSeq_succ_poly (s0 : RecState R) (hnb : ∀ n, (stateSeq s0 n).poly.coeff 0 ≠ 0) (j : ℕ) :
    (stateSeq s0 (j + 1)).poly
      = substPoly (stateSeq s0 j).poly (xSeq s0 j) (xiSeq s0 j) (betaSeq s0 j) :=
  ((stateSeq s0 j).step_props (hnb j)).2.2

/-- The evaluation `Pⱼ(ρⱼ)` has positive order (it exceeds `βⱼ > 0`, by Lemma 2.95b). -/
theorem eval_rho_order_pos (s0 : RecState R) (hnb : ∀ n, (stateSeq s0 n).poly.coeff 0 ≠ 0) (j : ℕ) :
    (0 : WithTop ℚ) < puiseuxOrder R ((stateSeq s0 j).poly.eval (rho s0 hnb j)) := by
  rw [rho_succ_eq s0 hnb j]
  exact lt_trans (by exact_mod_cast betaSeq_pos s0 hnb j)
    ((stateSeq s0 j).step_order_jump (hnb j) (rho s0 hnb (j + 1)) (rho_order_pos s0 hnb j))

/-- The accumulated order increment `Σ_{k<j} βₖ`. -/
noncomputable def sumBeta (s0 : RecState R) (j : ℕ) : ℚ := ∑ k ∈ Finset.range j, betaSeq s0 k

theorem sumBeta_succ (s0 : RecState R) (j : ℕ) :
    sumBeta s0 (j + 1) = sumBeta s0 j + betaSeq s0 j := Finset.sum_range_succ _ _

/-- **The order increments accumulate without bound** (`βₖ ≥ 1/M` for `k ≥ N`). -/
theorem sumBeta_unbounded (s0 : RecState R) (hnb : ∀ n, (stateSeq s0 n).poly.coeff 0 ≠ 0)
    (q : ℚ) : ∃ j, q < sumBeta s0 j := by
  obtain ⟨N, M, hmem⟩ := stateSeq_xibeta_mem s0
  have hM : (0 : ℚ) < (M : ℚ) := by exact_mod_cast M.pos
  -- `βₖ ≥ 1/M` for `k ≥ N`
  have hbeta : ∀ k, N ≤ k → (1 : ℚ) / (M : ℚ) ≤ betaSeq s0 k := by
    intro k hk
    obtain ⟨b, hb⟩ := (hmem k hk).2
    have hpos : 0 < betaSeq s0 k := betaSeq_pos s0 hnb k
    have hb1 : (1 : ℤ) ≤ b := by
      rw [hb] at hpos
      rcases div_pos_iff.mp hpos with ⟨hbp, _⟩ | ⟨_, hMn⟩
      · have : (0 : ℤ) < b := by exact_mod_cast hbp
        omega
      · exact absurd hMn (not_lt.mpr hM.le)
    rw [hb, div_le_div_iff_of_pos_right hM]
    exact_mod_cast hb1
  -- `(t:ℚ)/M ≤ sumBeta (N + t)`
  have hgrow : ∀ t : ℕ, (t : ℚ) / (M : ℚ) ≤ sumBeta s0 (N + t) := by
    intro t
    induction t with
    | zero =>
      simp only [Nat.add_zero, Nat.cast_zero, zero_div, sumBeta]
      exact Finset.sum_nonneg (fun k _ => (betaSeq_pos s0 hnb k).le)
    | succ t ih =>
      have hstep : sumBeta s0 (N + (t + 1)) = sumBeta s0 (N + t) + betaSeq s0 (N + t) := by
        rw [show N + (t + 1) = (N + t) + 1 from by omega, sumBeta_succ]
      have h1 := hbeta (N + t) (Nat.le_add_right N t)
      have hcast : ((t + 1 : ℕ) : ℚ) / (M : ℚ) = (t : ℚ) / (M : ℚ) + 1 / (M : ℚ) := by
        push_cast; ring
      rw [hstep, hcast]
      linarith
  obtain ⟨t, ht⟩ := exists_nat_gt (q * (M : ℚ))
  refine ⟨N + t, lt_of_lt_of_le ?_ (hgrow t)⟩
  rw [lt_div_iff₀ hM]; linarith

/-- **Telescoping.** `P₀.eval x̄ = ε^{Σ_{k<j}βₖ}·Pⱼ.eval ρⱼ`. -/
theorem telescope (s0 : RecState R) (hnb : ∀ n, (stateSeq s0 n).poly.coeff 0 ≠ 0) (j : ℕ) :
    (stateSeq s0 0).poly.eval (rho s0 hnb 0)
      = puiseuxMonomial (sumBeta s0 j) * (stateSeq s0 j).poly.eval (rho s0 hnb j) := by
  induction j with
  | zero => rw [sumBeta, Finset.sum_range_zero, puiseuxMonomial_zero, one_mul]
  | succ j ih =>
    rw [ih, sumBeta_succ, rho_succ_eq s0 hnb j,
      substPoly_eval (stateSeq s0 j).poly (xSeq s0 j) (xiSeq s0 j) (betaSeq s0 j)
        (rho s0 hnb (j + 1)),
      ← stateSeq_succ_poly s0 hnb j, ← mul_assoc, puiseuxMonomial_mul]

/-- **The limit is a root of `P₀`** (the never-barrier case). -/
theorem eval_xbar_eq_zero (s0 : RecState R) (hnb : ∀ n, (stateSeq s0 n).poly.coeff 0 ≠ 0) :
    (stateSeq s0 0).poly.eval (xbarP s0 hnb) = 0 := by
  have hgt : ∀ j, (↑(sumBeta s0 j) : WithTop ℚ)
      < puiseuxOrder R ((stateSeq s0 0).poly.eval (xbarP s0 hnb)) := by
    intro j
    have ht := telescope s0 hnb j
    rw [rho_zero] at ht
    rw [ht, puiseuxOrder_mul, puiseuxOrder_puiseuxMonomial]
    rcases eq_or_ne (puiseuxOrder R ((stateSeq s0 j).poly.eval (rho s0 hnb j))) ⊤ with ho | ho
    · rw [ho, WithTop.add_top]; exact WithTop.coe_lt_top _
    · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp ho
      rw [← hr, ← WithTop.coe_add, WithTop.coe_lt_coe]
      have hrpos : 0 < r := by
        have h := eval_rho_order_pos s0 hnb j; rw [← hr] at h; exact_mod_cast h
      linarith
  have hval : puiseuxOrder R ((stateSeq s0 0).poly.eval (xbarP s0 hnb)) = ⊤ := by
    by_contra htop
    obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp htop
    obtain ⟨j, hj⟩ := sumBeta_unbounded s0 hnb q
    have hlt := hgt j
    rw [← hq] at hlt
    exact absurd hj (not_lt.mpr (by exact_mod_cast hlt.le))
  rw [← ZeroMemClass.coe_eq_zero]
  exact HahnSeries.orderTop_eq_top.mp hval

/-! ### The barrier (finite) case and the final assembly -/

/-- The recentered next polynomial, from a single non-barrier step. -/
theorem stateSeq_succ_poly' (s0 : RecState R) (j : ℕ) (h : (stateSeq s0 j).poly.coeff 0 ≠ 0) :
    (stateSeq s0 (j + 1)).poly
      = substPoly (stateSeq s0 j).poly (xSeq s0 j) (xiSeq s0 j) (betaSeq s0 j) :=
  ((stateSeq s0 j).step_props h).2.2

/-- The tail root relative to an arbitrary target `T` (the algebra needs no property of `T`). -/
noncomputable def rhoG (s0 : RecState R) (T : PuiseuxSeries R) (j : ℕ) : PuiseuxSeries R :=
  puiseuxMonomial (-(prevEta s0 j)) * (T - partialSumP s0 j)

theorem rhoG_zero (s0 : RecState R) (T : PuiseuxSeries R) : rhoG s0 T 0 = T := by
  rw [rhoG, prevEta, Finset.sum_range_zero, neg_zero, puiseuxMonomial_zero, partialSumP,
    Finset.sum_range_zero, sub_zero, one_mul]

theorem rhoG_succ_eq (s0 : RecState R) (T : PuiseuxSeries R) (j : ℕ) :
    rhoG s0 T j = puiseuxMonomial (xiSeq s0 j) * (constPuiseux (xSeq s0 j) + rhoG s0 T (j + 1)) := by
  have hkey : puiseuxMonomial (-(prevEta s0 j)) * puiseuxMonomial (etaSeq s0 j)
      = (puiseuxMonomial (xiSeq s0 j) : PuiseuxSeries R) := by
    rw [puiseuxMonomial_mul, etaSeq_eq_prevEta_succ, prevEta_succ]; congr 1; ring
  have hsplit : puiseuxMonomial (xiSeq s0 j) * puiseuxMonomial (-(prevEta s0 (j + 1)))
      = (puiseuxMonomial (-(prevEta s0 j)) : PuiseuxSeries R) := by
    rw [puiseuxMonomial_mul, prevEta_succ]; congr 1; ring
  simp only [rhoG]
  rw [partialSumP_succ, mul_add,
    ← mul_assoc (puiseuxMonomial (xiSeq s0 j)) (puiseuxMonomial (-(prevEta s0 (j + 1)))), hsplit]
  linear_combination (constPuiseux (xSeq s0 j)) * hkey

/-- **Generic telescoping** through any non-barrier prefix, for any target `T`. -/
theorem telescopeG (s0 : RecState R) (T : PuiseuxSeries R) (j : ℕ)
    (hb : ∀ k, k < j → (stateSeq s0 k).poly.coeff 0 ≠ 0) :
    (stateSeq s0 0).poly.eval (rhoG s0 T 0)
      = puiseuxMonomial (sumBeta s0 j) * (stateSeq s0 j).poly.eval (rhoG s0 T j) := by
  induction j with
  | zero => rw [sumBeta, Finset.sum_range_zero, puiseuxMonomial_zero, one_mul]
  | succ j ih =>
    rw [ih (fun k hk => hb k (Nat.lt_succ_of_lt hk)), sumBeta_succ, rhoG_succ_eq s0 T j,
      substPoly_eval (stateSeq s0 j).poly (xSeq s0 j) (xiSeq s0 j) (betaSeq s0 j)
        (rhoG s0 T (j + 1)),
      ← stateSeq_succ_poly' s0 j (hb j (Nat.lt_succ_self j)), ← mul_assoc, puiseuxMonomial_mul]

/-- **The barrier case.** If step `n` hits the barrier (`coeff 0 = 0`) after a non-barrier prefix,
the finite partial sum `Sₙ` is an exact root of `P₀`. -/
theorem eval_partialSum_eq_zero (s0 : RecState R) (n : ℕ)
    (hb : ∀ k, k < n → (stateSeq s0 k).poly.coeff 0 ≠ 0)
    (hbar : (stateSeq s0 n).poly.coeff 0 = 0) :
    (stateSeq s0 0).poly.eval (partialSumP s0 n) = 0 := by
  have h := telescopeG s0 (partialSumP s0 n) n hb
  rw [rhoG_zero] at h
  have hz : rhoG s0 (partialSumP s0 n) n = 0 := by rw [rhoG, sub_self, mul_zero]
  rw [h, hz, ← Polynomial.coeff_zero_eq_eval_zero, hbar, mul_zero]

/-- **Every recursion state's polynomial has a Puiseux-series root** (barrier or limit). -/
theorem exists_root_recState (s0 : RecState R) : ∃ y : PuiseuxSeries R, s0.poly.eval y = 0 := by
  classical
  by_cases h : ∃ n, (stateSeq s0 n).poly.coeff 0 = 0
  · exact ⟨partialSumP s0 (Nat.find h),
      eval_partialSum_eq_zero s0 (Nat.find h) (fun k hk => Nat.find_min h hk) (Nat.find_spec h)⟩
  · push Not at h
    exact ⟨xbarP s0 h, eval_xbar_eq_zero s0 h⟩

/-- **Odd-degree polynomials over `R⟨⟨ε⟩⟩` have roots** — the Newton–Puiseux construction. -/
theorem exists_root_of_odd {P : Polynomial (PuiseuxSeries R)} (hodd : Odd P.natDegree) :
    ∃ x, P.IsRoot x := by
  by_cases h0 : P.coeff 0 = 0
  · exact ⟨0, by rw [Polynomial.IsRoot.def, ← Polynomial.coeff_zero_eq_eval_zero]; exact h0⟩
  · obtain ⟨x, ξ, β, s, _, hpoly, _⟩ := exists_initial_RecState hodd h0
    obtain ⟨y, hy⟩ := exists_root_recState s
    refine ⟨puiseuxMonomial ξ * (constPuiseux x + y), ?_⟩
    rw [Polynomial.IsRoot.def, substPoly_eval P x ξ β y, ← hpoly, hy, mul_zero]

end Azurite.BPR
