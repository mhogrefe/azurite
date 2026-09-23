/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter1.Section1_2.Definition1_10
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Proposition1_8
import Mathlib.Tactic.LinearCombination

/-!
# Lemma 1.11

Three identities for the extended signed remainder sequence:

(i) Bezout: $\lcode{SRemS}_n = \lcode{SRemU}_n \cdot P + \lcode{SRemV}_n \cdot Q$.
(ii) Degree of $\lcode{SRemU}_{i+1}$ equals $\deg Q - \deg \lcode{SRemS}_i$.
(iii) Degree of $\lcode{SRemV}_{i+1}$ equals $\deg P - \deg \lcode{SRemS}_i$.

Plus the supporting degree machinery on the SRemS sequence.
-/

namespace Azurite.BPR

open Polynomial

variable {K : Type*} [Field K]

open Classical in
/-- BPR Lemma 1.11 (i): For all i, SRemS_i(P,Q) = SRemU_i(P,Q) · P + SRemV_i(P,Q) · Q. -/
theorem lemma_1_11_bezout (P Q : K[X]) (n : ℕ) :
    SRemS P Q n = SRemU P Q n * P + SRemV P Q n * Q := by
  match n with
  | 0 => simp [SRemS, SRemU, SRemV]
  | 1 => simp [SRemS, SRemU, SRemV]
  | n + 2 =>
    by_cases hne : SRemS P Q (n + 1) = 0
    · simp [SRemS, SRemU, SRemV, hne]
    · rw [SRemS_ss P Q n hne, SRemU_ss P Q n hne, SRemV_ss P Q n hne]
      set a := SRemS P Q n / SRemS P Q (n + 1)
      have ih0 := lemma_1_11_bezout P Q n
      have ih1 := lemma_1_11_bezout P Q (n + 1)
      have hdiv : SRemS P Q n % SRemS P Q (n + 1) =
          SRemS P Q n - SRemS P Q (n + 1) * a := by
        have h := EuclideanDomain.div_add_mod (SRemS P Q n) (SRemS P Q (n + 1))
        linear_combination h
      rw [hdiv, ih0, ih1]; ring

open Classical in
/-- The degree of SRemS strictly decreases at each step: when SRemS(n+1) ≠ 0,
    deg(SRemS(n+2)) < deg(SRemS(n+1)). -/
theorem degree_SRemS_lt (P Q : K[X]) (n : ℕ) (hne : SRemS P Q (n + 1) ≠ 0) :
    (SRemS P Q (n + 2)).degree < (SRemS P Q (n + 1)).degree := by
  rw [SRemS_ss P Q n hne]
  rw [Polynomial.degree_neg]
  exact Polynomial.degree_mod_lt _ hne

open Classical in
/-- For consecutive nonzero entries in SRemS with n ≥ 1, the degrees
    strictly decrease: deg(SRemS(n+1)) < deg(SRemS(n)). -/
theorem degree_SRemS_chain_lt (P Q : K[X]) (n : ℕ)
    (hn : n ≥ 1)
    (hne : SRemS P Q n ≠ 0) :
    (SRemS P Q (n + 1)).degree < (SRemS P Q n).degree := by
  cases n with
  | zero => omega
  | succ m => exact degree_SRemS_lt P Q m hne

open Classical in
/-- Entries of SRemS between 0 and k are nonzero when the sequence terminates at k+1. -/
theorem SRemS_ne_zero_of_le (P Q : K[X]) (k : ℕ) (j : ℕ)
    (_ : SRemS P Q (k + 1) = 0) (hk_ne : SRemS P Q k ≠ 0)
    (hj1 : 1 ≤ j) (hj2 : j ≤ k) : SRemS P Q j ≠ 0 := by
  intro heq
  cases j with
  | zero => omega
  | succ p =>
    exact hk_ne (SRemS_zero_ge P Q p heq k (by omega))

open Classical in
/-- The quotient SRemS(n) / SRemS(n+1) is nonzero when both entries are nonzero
    and the degree decreases. -/
theorem SRemS_div_ne_zero (P Q : K[X]) (n : ℕ)
    (hne0 : SRemS P Q n ≠ 0) (hne : SRemS P Q (n + 1) ≠ 0)
    (hle : (SRemS P Q (n + 1)).degree ≤ (SRemS P Q n).degree) :
    SRemS P Q n / SRemS P Q (n + 1) ≠ 0 := by
  intro heq
  have h := Polynomial.degree_add_div hne hle
  simp [heq] at h
  exact hne0 (Polynomial.degree_eq_bot.mp h.symm)

open Classical in
/-- natDegree of the quotient SRemS(n) / SRemS(n+1) when both are nonzero
    and deg(SRemS(n+1)) ≤ deg(SRemS(n)). -/
theorem natDegree_SRemS_div (P Q : K[X]) (n : ℕ)
    (hne0 : SRemS P Q n ≠ 0)
    (hne : SRemS P Q (n + 1) ≠ 0)
    (hle : (SRemS P Q (n + 1)).degree ≤ (SRemS P Q n).degree) :
    (SRemS P Q n / SRemS P Q (n + 1)).natDegree =
      (SRemS P Q n).natDegree - (SRemS P Q (n + 1)).natDegree := by
  have h := Polynomial.degree_add_div hne hle
  have hne_div := SRemS_div_ne_zero P Q n hne0 hne hle
  rw [Polynomial.degree_eq_natDegree hne, Polynomial.degree_eq_natDegree hne_div,
      Polynomial.degree_eq_natDegree hne0] at h
  exact_mod_cast Nat.eq_sub_of_add_eq (by rw [add_comm]; exact_mod_cast h)

open Classical in
/-- natDegree of SRemS is strictly decreasing: for m < n with all entries nonzero,
    natDegree(SRemS(n+1)) < natDegree(SRemS(m+1)). -/
theorem natDegree_SRemS_lt_of_lt (P Q : K[X]) (m n : ℕ)
    (hmn : m < n)
    (hne : ∀ j, m + 1 ≤ j → j ≤ n + 1 → SRemS P Q j ≠ 0) :
    (SRemS P Q (n + 1)).natDegree < (SRemS P Q (m + 1)).natDegree := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hmn' : m < n
    · have h1 : (SRemS P Q (n + 1 + 1)).natDegree < (SRemS P Q (n + 1)).natDegree :=
        Polynomial.natDegree_lt_natDegree (hne (n + 1 + 1) (by omega) (by omega))
          (degree_SRemS_lt P Q n (hne (n + 1) (by omega) (by omega)))
      exact lt_trans h1 (ih hmn' (fun j hj1 hj2 => hne j hj1 (by omega)))
    · have hm : m = n := by omega
      subst hm
      exact Polynomial.natDegree_lt_natDegree (hne (m + 1 + 1) (by omega) (by omega))
        (degree_SRemS_lt P Q m (hne (m + 1) (by omega) (by omega)))

open Classical in
/-- BPR Lemma 1.11 (ii): For 1 ≤ i ≤ k, natDeg(SRemU_{i+1}(P,Q)) = natDeg(Q) − natDeg(SRemS_i),
    where the SRemS sequence terminates at index k+1. -/
theorem lemma_1_11_degU (P Q : K[X]) (k : ℕ) (i : ℕ)
    (hk : SRemS P Q (k + 1) = 0) (hk_ne : SRemS P Q k ≠ 0)
    (hi : 1 ≤ i) (hik : i ≤ k)
    (_hP : P ≠ 0) (hQ : Q ≠ 0)
    (_hle : Q.degree ≤ P.degree) :
    (SRemU P Q (i + 1)).natDegree = Q.natDegree - (SRemS P Q i).natDegree := by
  induction i using Nat.strongRecOn with
  | _ i ih =>
    match i, hi, hik with
    | 1, _, _ =>
      have h1 : SRemS P Q 1 ≠ 0 := by simp [SRemS]; exact hQ
      rw [SRemU_ss P Q 0 h1]
      simp [SRemU, SRemS]
    | i + 2, _, _ =>
      have hsi : SRemS P Q (i + 2) ≠ 0 :=
        SRemS_ne_zero_of_le P Q k (i + 2) hk hk_ne (by omega) (by omega)
      have hsi1 : SRemS P Q (i + 1) ≠ 0 :=
        SRemS_ne_zero_of_le P Q k (i + 1) hk hk_ne (by omega) (by omega)
      rw [SRemU_ss P Q (i + 1) hsi]
      have hle_deg : (SRemS P Q (i + 2)).degree ≤ (SRemS P Q (i + 1)).degree :=
        le_of_lt (degree_SRemS_lt P Q i hsi1)
      have hdq := natDegree_SRemS_div P Q (i + 1) hsi1 hsi hle_deg
      have hne_div := SRemS_div_ne_zero P Q (i + 1) hsi1 hsi hle_deg
      have ih_cur := ih (i + 1) (by omega) (by omega) (by omega)
      have hnd_dec : (SRemS P Q (i + 2)).natDegree < (SRemS P Q (i + 1)).natDegree :=
        Polynomial.natDegree_lt_natDegree hsi (degree_SRemS_lt P Q i hsi1)
      cases i with
      | zero =>
        have hne_u : SRemU P Q 2 ≠ 0 := by
          intro heq; simp [SRemU, SRemS] at heq; exact hQ heq
        show (-SRemU P Q 1 + _ * SRemU P Q 2).natDegree = _
        simp only [show SRemU P Q 1 = 0 from rfl, neg_zero, zero_add]
        rw [Polynomial.natDegree_mul hne_div hne_u, hdq, ih_cur]
        simp [SRemS]
      | succ j =>
        have hnd_le_q : (SRemS P Q (j + 1 + 1)).natDegree < Q.natDegree := by
          have := natDegree_SRemS_lt_of_lt P Q 0 (j + 1) (by omega) (fun l hl1 hl2 =>
            SRemS_ne_zero_of_le P Q k l hk hk_ne (by omega) (by omega))
          simp [SRemS_snd] at this; exact this
        have hnd_le_q2 : (SRemS P Q (j + 1 + 2)).natDegree < Q.natDegree :=
          lt_trans hnd_dec hnd_le_q
        have hne_u : SRemU P Q (j + 1 + 1 + 1) ≠ 0 := by
          intro heq; rw [heq, Polynomial.natDegree_zero] at ih_cur; omega
        have ih_prev := ih (j + 1) (by omega) (by omega) (by omega)
        have hnd_le_q_j : (SRemS P Q (j + 1)).natDegree ≤ Q.natDegree := by
          cases j with
          | zero => simp [SRemS_snd]
          | succ j' =>
            have := natDegree_SRemS_lt_of_lt P Q 0 (j' + 1) (by omega) (fun l hl1 hl2 =>
              SRemS_ne_zero_of_le P Q k l hk hk_ne (by omega) (by omega))
            simp [SRemS_snd] at this; exact le_of_lt this
        have hne_u_prev : SRemU P Q (j + 1 + 1) ≠ 0 := by
          cases j with
          | zero => simp [SRemU, SRemS]; exact hQ
          | succ j' =>
            have hlt_j' : (SRemS P Q (j' + 2)).natDegree < Q.natDegree := by
              have := natDegree_SRemS_lt_of_lt P Q 0 (j' + 1) (by omega) (fun l hl1 hl2 =>
                SRemS_ne_zero_of_le P Q k l hk hk_ne (by omega) (by omega))
              simp [SRemS_snd] at this; exact this
            intro heq; rw [heq, Polynomial.natDegree_zero] at ih_prev
            exact absurd ih_prev (ne_of_gt (Nat.sub_pos_of_lt hlt_j')).symm
        have hsi_j : SRemS P Q (j + 1) ≠ 0 :=
          SRemS_ne_zero_of_le P Q k (j + 1) hk hk_ne (by omega) (by omega)
        have hd_step : (SRemS P Q (j + 1 + 1)).natDegree < (SRemS P Q (j + 1)).natDegree :=
          Polynomial.natDegree_lt_natDegree hsi1 (degree_SRemS_lt P Q j hsi_j)
        have hd_skip : (SRemS P Q (j + 1 + 2)).natDegree < (SRemS P Q (j + 1)).natDegree :=
          lt_trans hnd_dec hd_step
        rw [Polynomial.natDegree_add_eq_right_of_degree_lt]
        · -- natDeg(quot * SRemU(j+3)) = Q - SRemS(j+3)
          rw [Polynomial.natDegree_mul hne_div hne_u, hdq, ih_cur]
          -- (d₂ - d₃) + (Q - d₂) = Q - d₃
          rw [Nat.add_comm]
          exact Nat.sub_add_sub_cancel (le_of_lt hnd_le_q) (le_of_lt hnd_dec)
        · -- deg(-SRemU(j+2)) < deg(quot * SRemU(j+3))
          apply Polynomial.degree_lt_degree
          calc Polynomial.natDegree (-SRemU P Q (j + 1 + 1))
              = (SRemU P Q (j + 1 + 1)).natDegree := Polynomial.natDegree_neg _
            _ = Q.natDegree - (SRemS P Q (j + 1)).natDegree := ih_prev
            _ < Q.natDegree - (SRemS P Q (j + 1 + 2)).natDegree :=
                Nat.sub_lt_sub_left (lt_of_lt_of_le hd_skip hnd_le_q_j) hd_skip
            _ = Polynomial.natDegree (SRemS P Q (j + 1 + 1) / SRemS P Q (j + 1 + 1 + 1) *
                SRemU P Q (j + 1 + 1 + 1)) := by
                rw [Polynomial.natDegree_mul hne_div hne_u, hdq, ih_cur,
                    show j + 1 + 1 + 1 = j + 1 + 2 from rfl]
                omega

open Classical in
/-- BPR Lemma 1.11 (iii): For 1 ≤ i ≤ k, natDeg(SRemV_{i+1}(P,Q)) = natDeg(P) − natDeg(SRemS_i),
    where the SRemS sequence terminates at index k+1. -/
theorem lemma_1_11_degV (P Q : K[X]) (k : ℕ) (i : ℕ)
    (hk : SRemS P Q (k + 1) = 0) (hk_ne : SRemS P Q k ≠ 0)
    (hi : 1 ≤ i) (hik : i ≤ k)
    (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hle : Q.degree ≤ P.degree) :
    (SRemV P Q (i + 1)).natDegree = P.natDegree - (SRemS P Q i).natDegree := by
  induction i using Nat.strongRecOn with
  | _ i ih =>
    match i, hi, hik with
    | 1, _, _ =>
      have h1 : SRemS P Q 1 ≠ 0 := by simp [SRemS]; exact hQ
      rw [SRemV_ss P Q 0 h1]
      simp [SRemV, SRemS]
      -- natDeg(P / Q) = P.natDeg - Q.natDeg = P.natDeg - SRemS(1).natDeg
      exact natDegree_SRemS_div P Q 0 hP hQ (by simp [SRemS]; exact hle)
    | i + 2, _, _ =>
      have hsi : SRemS P Q (i + 2) ≠ 0 :=
        SRemS_ne_zero_of_le P Q k (i + 2) hk hk_ne (by omega) (by omega)
      have hsi1 : SRemS P Q (i + 1) ≠ 0 :=
        SRemS_ne_zero_of_le P Q k (i + 1) hk hk_ne (by omega) (by omega)
      rw [SRemV_ss P Q (i + 1) hsi]
      have hle_deg : (SRemS P Q (i + 2)).degree ≤ (SRemS P Q (i + 1)).degree :=
        le_of_lt (degree_SRemS_lt P Q i hsi1)
      have hdq := natDegree_SRemS_div P Q (i + 1) hsi1 hsi hle_deg
      have hne_div := SRemS_div_ne_zero P Q (i + 1) hsi1 hsi hle_deg
      have ih_cur := ih (i + 1) (by omega) (by omega) (by omega)
      have hnd_dec : (SRemS P Q (i + 2)).natDegree < (SRemS P Q (i + 1)).natDegree :=
        Polynomial.natDegree_lt_natDegree hsi (degree_SRemS_lt P Q i hsi1)
      -- Need SRemS(l).natDeg ≤ P.natDeg for various l
      have hp_ge_q : Q.natDegree ≤ P.natDegree :=
        Polynomial.natDegree_le_natDegree hle
      cases i with
      | zero =>
        -- SRemV 2 = -SRemV 0 + (SRemS 0 / SRemS 1) * SRemV 1 = 0 + (P/Q) * 1 = P/Q
        -- which is hne_div (SRemS 0 / SRemS 1 ≠ 0)
        have hne_v : SRemV P Q 2 ≠ 0 := by
          simp only [SRemV, show SRemS P Q 1 = Q from rfl, hQ, ↓reduceIte,
                     show SRemS P Q 0 = P from rfl, neg_zero, zero_add, mul_one]
          exact SRemS_div_ne_zero P Q 0 hP hQ (by simp [SRemS]; exact hle)
        rw [Polynomial.natDegree_add_eq_right_of_degree_lt]
        · rw [Polynomial.natDegree_mul hne_div hne_v, hdq, ih_cur]
          rw [Nat.add_comm]
          exact Nat.sub_add_sub_cancel hp_ge_q
            (le_of_lt (Polynomial.natDegree_lt_natDegree hsi
              (degree_SRemS_lt P Q 0 hsi1)))
        · rw [Polynomial.degree_neg]
          calc (1 : K[X]).degree = (0 : ℕ) := Polynomial.degree_one
            _ < ↑((SRemS P Q (0 + 1) / SRemS P Q (0 + 1 + 1) * SRemV P Q (0 + 1 + 1)).natDegree) := by
                rw [Nat.cast_lt, Polynomial.natDegree_mul hne_div hne_v, hdq, ih_cur]
                -- 0 < (P.natDeg - SRemS(1).natDeg) + (SRemS(1).natDeg - SRemS(2).natDeg)
                have hsrem1_le : (SRemS P Q (0 + 1)).natDegree ≤ P.natDegree := by
                  simp [SRemS_snd]; exact hp_ge_q
                rw [Nat.add_comm, Nat.sub_add_sub_cancel hsrem1_le (le_of_lt hnd_dec)]
                -- 0 < P.natDeg - SRemS(2).natDeg
                omega
            _ = (SRemS P Q (0 + 1) / SRemS P Q (0 + 1 + 1) * SRemV P Q (0 + 1 + 1)).degree :=
                (Polynomial.degree_eq_natDegree (mul_ne_zero hne_div hne_v)).symm
      | succ j =>
        have hnd_le_p : (SRemS P Q (j + 1 + 1)).natDegree < P.natDegree := by
          have : (SRemS P Q (j + 1 + 1)).natDegree < Q.natDegree := by
            have := natDegree_SRemS_lt_of_lt P Q 0 (j + 1) (by omega) (fun l hl1 hl2 =>
              SRemS_ne_zero_of_le P Q k l hk hk_ne (by omega) (by omega))
            simp [SRemS_snd] at this; exact this
          exact lt_of_lt_of_le this hp_ge_q
        have hnd_le_p2 : (SRemS P Q (j + 1 + 2)).natDegree < P.natDegree :=
          lt_trans hnd_dec hnd_le_p
        have hne_v : SRemV P Q (j + 1 + 1 + 1) ≠ 0 := by
          intro heq; rw [heq, Polynomial.natDegree_zero] at ih_cur; omega
        have ih_prev := ih (j + 1) (by omega) (by omega) (by omega)
        have hnd_le_p_j : (SRemS P Q (j + 1)).natDegree ≤ P.natDegree := by
          cases j with
          | zero => simp [SRemS_snd]; exact hp_ge_q
          | succ j' =>
            have : (SRemS P Q (j' + 2)).natDegree < Q.natDegree := by
              have := natDegree_SRemS_lt_of_lt P Q 0 (j' + 1) (by omega) (fun l hl1 hl2 =>
                SRemS_ne_zero_of_le P Q k l hk hk_ne (by omega) (by omega))
              simp [SRemS_snd] at this; exact this
            exact le_of_lt (lt_of_lt_of_le this hp_ge_q)
        have hne_v_prev : SRemV P Q (j + 1 + 1) ≠ 0 := by
          cases j with
          | zero => simp [SRemV, SRemS]; exact ⟨hQ, SRemS_div_ne_zero P Q 0 hP hQ (by simp [SRemS]; exact hle)⟩
          | succ j' =>
            have hlt_j' : (SRemS P Q (j' + 2)).natDegree < P.natDegree := by
              have : (SRemS P Q (j' + 2)).natDegree < Q.natDegree := by
                have := natDegree_SRemS_lt_of_lt P Q 0 (j' + 1) (by omega) (fun l hl1 hl2 =>
                  SRemS_ne_zero_of_le P Q k l hk hk_ne (by omega) (by omega))
                simp [SRemS_snd] at this; exact this
              exact lt_of_lt_of_le this hp_ge_q
            intro heq; rw [heq, Polynomial.natDegree_zero] at ih_prev
            exact absurd ih_prev (ne_of_gt (Nat.sub_pos_of_lt hlt_j')).symm
        have hsi_j : SRemS P Q (j + 1) ≠ 0 :=
          SRemS_ne_zero_of_le P Q k (j + 1) hk hk_ne (by omega) (by omega)
        have hd_step : (SRemS P Q (j + 1 + 1)).natDegree < (SRemS P Q (j + 1)).natDegree :=
          Polynomial.natDegree_lt_natDegree hsi1 (degree_SRemS_lt P Q j hsi_j)
        have hd_skip : (SRemS P Q (j + 1 + 2)).natDegree < (SRemS P Q (j + 1)).natDegree :=
          lt_trans hnd_dec hd_step
        rw [Polynomial.natDegree_add_eq_right_of_degree_lt]
        · -- natDeg(quot * SRemV(j+3)) = P - SRemS(j+3)
          rw [Polynomial.natDegree_mul hne_div hne_v, hdq, ih_cur]
          rw [Nat.add_comm]
          exact Nat.sub_add_sub_cancel (le_of_lt hnd_le_p) (le_of_lt hnd_dec)
        · -- deg(-SRemV(j+2)) < deg(quot * SRemV(j+3))
          apply Polynomial.degree_lt_degree
          calc Polynomial.natDegree (-SRemV P Q (j + 1 + 1))
              = (SRemV P Q (j + 1 + 1)).natDegree := Polynomial.natDegree_neg _
            _ = P.natDegree - (SRemS P Q (j + 1)).natDegree := ih_prev
            _ < P.natDegree - (SRemS P Q (j + 1 + 2)).natDegree :=
                Nat.sub_lt_sub_left (lt_of_lt_of_le hd_skip hnd_le_p_j) hd_skip
            _ = Polynomial.natDegree (SRemS P Q (j + 1 + 1) / SRemS P Q (j + 1 + 1 + 1) *
                SRemV P Q (j + 1 + 1 + 1)) := by
                rw [Polynomial.natDegree_mul hne_div hne_v, hdq, ih_cur,
                    show j + 1 + 1 + 1 = j + 1 + 2 from rfl]
                omega

end Azurite.BPR
