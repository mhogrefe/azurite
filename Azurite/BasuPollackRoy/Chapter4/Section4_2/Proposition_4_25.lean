/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter4.Section4_2.Lemma_4_24
import Azurite.BasuPollackRoy.Chapter4.Section4_2.Proposition_4_16

/-!
# BPR Proposition 4.25: deg(gcd) ≥ j iff sRes_0 = ⋯ = sRes_{j-1} = 0

Over a field `K`, for `0 ≤ j ≤ q` (if `p > q`) or `0 ≤ j ≤ p - 1` (if
`p = q`), the degree of `gcd(P, Q)` is at least `j` if and only if the
first `j` signed subresultant coefficients vanish.

## Proof strategy

The proof routes through the auxiliary bridge

  `(∃ U V ≠ 0 : K[X], deg U ≤ q - j, deg V ≤ p - j, U·P + V·Q = 0)
   ↔ (gcd P Q).natDegree ≥ j`,

which follows by combining the standard polynomial argument
(`U·P = -V·Q = lcm(P, Q)` up to associates) with the BPR Proposition 1.5
degree identity `deg(lcm) + deg(gcd) = deg(P) + deg(Q)`.

* **Forward** (`deg gcd ≥ j → ∀ i < j, sRes_i = 0`): use the bridge to
  get a single `(U, V)` with `U·P + V·Q = 0`; apply Lemma 4.24 at each
  `i < j` using this same `(U, V)`.
* **Reverse** (`∀ i < j, sRes_i = 0 → deg gcd ≥ j`): induct on `j`.
  The step uses Lemma 4.24 at `j - 1` to obtain `(U, V)` with
  `deg(U·P + V·Q) < j - 1`; the induction hypothesis gives
  `deg gcd ≥ j - 1`, which (combined with `gcd | U·P + V·Q`) forces
  `U·P + V·Q = 0`; then the bridge upgrades to `deg gcd ≥ j`.
-/

namespace Azurite.BPR.Chapter4

open Polynomial

variable {K : Type*} [Field K] [DecidableEq K]

/-! ### Bridge: existence of a single `(U, V)` ↔ degree bound -/

omit [DecidableEq K] in
/-- Bridge lemma: existence of non-zero `(U, V)` with the bounded
    degrees and `U·P + V·Q = 0` is equivalent to a bound on the
    `lcm`'s degree. -/
private theorem exists_UV_zero_iff_lcm_natDegree_le
    (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (j : ℕ) (hj_q : j ≤ Q.natDegree) (hj_p : j ≤ P.natDegree) :
    (∃ U V : K[X], U ≠ 0 ∧ V ≠ 0 ∧
      U.natDegree ≤ Q.natDegree - j ∧
      V.natDegree ≤ P.natDegree - j ∧
      U * P + V * Q = 0) ↔
        (lcm P Q).natDegree ≤ P.natDegree + Q.natDegree - j := by
  constructor
  · rintro ⟨U, V, hU, hV, hUq, hVp, h_rel⟩
    have h_UP_ne : U * P ≠ 0 := mul_ne_zero hU hP
    have h_UP_dvd_P : P ∣ U * P := ⟨U, by ring⟩
    have h_UP_dvd_Q : Q ∣ U * P := by
      rw [show U * P = -(V * Q) from by linear_combination h_rel]
      exact ⟨-V, by ring⟩
    have h_lcm_dvd : lcm P Q ∣ U * P := lcm_dvd h_UP_dvd_P h_UP_dvd_Q
    have h_deg_le : (lcm P Q).natDegree ≤ (U * P).natDegree :=
      Polynomial.natDegree_le_of_dvd h_lcm_dvd h_UP_ne
    have h_UP_deg : (U * P).natDegree = U.natDegree + P.natDegree :=
      Polynomial.natDegree_mul hU hP
    omega
  · intro h_lcm_le
    have h_lcm_ne : lcm P Q ≠ 0 :=
      fun h => ((lcm_eq_zero_iff P Q).mp h).elim hP hQ
    obtain ⟨U, hU_eq⟩ := dvd_lcm_left P Q
    obtain ⟨V, hV_eq⟩ := dvd_lcm_right P Q
    have hU_ne : U ≠ 0 := by
      intro h; rw [h, mul_zero] at hU_eq; exact h_lcm_ne hU_eq
    have hV_ne : V ≠ 0 := by
      intro h; rw [h, mul_zero] at hV_eq; exact h_lcm_ne hV_eq
    refine ⟨U, -V, hU_ne, neg_ne_zero.mpr hV_ne, ?_, ?_, ?_⟩
    · have : (P * U).natDegree = (lcm P Q).natDegree := by rw [← hU_eq]
      rw [Polynomial.natDegree_mul hP hU_ne] at this
      omega
    · rw [Polynomial.natDegree_neg]
      have : (Q * V).natDegree = (lcm P Q).natDegree := by rw [← hV_eq]
      rw [Polynomial.natDegree_mul hQ hV_ne] at this
      omega
    · have h1 : U * P = lcm P Q := by rw [mul_comm]; exact hU_eq.symm
      have h2 : V * Q = lcm P Q := by rw [mul_comm]; exact hV_eq.symm
      linear_combination h1 - h2

omit [DecidableEq K] in
/-- Bridge in gcd form: existence of non-zero `(U, V)` with bounded
    degrees and `U·P + V·Q = 0` is equivalent to `deg(gcd) ≥ j`. -/
theorem exists_UV_zero_iff_gcd_natDegree_ge
    (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (j : ℕ) (hj_q : j ≤ Q.natDegree) (hj_p : j ≤ P.natDegree) :
    (∃ U V : K[X], U ≠ 0 ∧ V ≠ 0 ∧
      U.natDegree ≤ Q.natDegree - j ∧
      V.natDegree ≤ P.natDegree - j ∧
      U * P + V * Q = 0) ↔
        (gcd P Q).natDegree ≥ j := by
  rw [exists_UV_zero_iff_lcm_natDegree_le P Q hP hQ j hj_q hj_p]
  have h_eq := lcm_natDegree_eq P Q hP hQ
  omega

/-! ### Proposition 4.25 -/

/-- **BPR Proposition 4.25.** Over a field `K`, for `j` in the BPR
    range, `deg(gcd(P, Q)) ≥ j` is equivalent to the vanishing of the
    first `j` signed subresultant coefficients. -/
theorem Proposition_4_25 (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (j : ℕ) (hj_q : j ≤ Q.natDegree) (hj_p : j < P.natDegree) :
    (∀ i, i < j → sRes P Q i = 0) ↔ (gcd P Q).natDegree ≥ j := by
  revert hj_q hj_p
  induction j with
  | zero =>
    intros _ _
    refine ⟨fun _ => Nat.zero_le _, fun _ i hi => ?_⟩
    exact absurd hi (Nat.not_lt_zero _)
  | succ n ih =>
    intros hj_q hj_p
    have hj_q' : n ≤ Q.natDegree := by omega
    have hj_p' : n < P.natDegree := by omega
    constructor
    · -- Reverse direction (induction step): `∀ i < n+1, sRes_i = 0` → `deg gcd ≥ n+1`.
      intro h_all_zero
      have h_gcd_n : (gcd P Q).natDegree ≥ n := by
        apply (ih hj_q' hj_p').mp
        intro i hi
        exact h_all_zero i (by omega)
      have h_sres_n : sRes P Q n = 0 := h_all_zero n (Nat.lt_succ_self n)
      obtain ⟨U, V, hU, hV, hUq, hVp, h_lt⟩ :=
        (Lemma_4_24 P Q n hj_q' hj_p' hP hQ).mp h_sres_n
      have h_U_natDeg : U.natDegree < Q.natDegree - n := by
        rw [Polynomial.degree_eq_natDegree hU] at hUq
        exact_mod_cast hUq
      have h_V_natDeg : V.natDegree < P.natDegree - n := by
        rw [Polynomial.degree_eq_natDegree hV] at hVp
        exact_mod_cast hVp
      have h_UV_zero : U * P + V * Q = 0 := by
        by_contra h_ne_zero
        have h_div : (gcd P Q) ∣ U * P + V * Q := by
          apply dvd_add
          · exact (gcd_dvd_left P Q).mul_left U
          · exact (gcd_dvd_right P Q).mul_left V
        have h_deg_le : (gcd P Q).natDegree ≤ (U * P + V * Q).natDegree :=
          Polynomial.natDegree_le_of_dvd h_div h_ne_zero
        have h_UV_natDeg : (U * P + V * Q).natDegree < n := by
          rw [Polynomial.degree_eq_natDegree h_ne_zero] at h_lt
          exact_mod_cast h_lt
        omega
      apply (exists_UV_zero_iff_gcd_natDegree_ge P Q hP hQ (n+1)
              hj_q (Nat.le_of_lt hj_p)).mp
      refine ⟨U, V, hU, hV, ?_, ?_, h_UV_zero⟩
      · omega
      · omega
    · -- Forward direction: `deg gcd ≥ n+1` → `∀ i < n+1, sRes_i = 0`.
      intro h_gcd i hi
      obtain ⟨U, V, hU, hV, hUq, hVp, h_UV_zero⟩ :=
        (exists_UV_zero_iff_gcd_natDegree_ge P Q hP hQ (n+1) hj_q
            (Nat.le_of_lt hj_p)).mpr h_gcd
      refine (Lemma_4_24 P Q i (by omega : i ≤ Q.natDegree)
          (by omega : i < P.natDegree) hP hQ).mpr
        ⟨U, V, hU, hV, ?_, ?_, ?_⟩
      · rw [Polynomial.degree_eq_natDegree hU]
        have : U.natDegree < Q.natDegree - i := by omega
        exact_mod_cast this
      · rw [Polynomial.degree_eq_natDegree hV]
        have : V.natDegree < P.natDegree - i := by omega
        exact_mod_cast this
      · rw [h_UV_zero, Polynomial.degree_zero]
        exact WithBot.bot_lt_coe i

end Azurite.BPR.Chapter4
