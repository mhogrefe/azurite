/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_2.Notation_2_56

/-!
# BPR Proposition 2.65

Let `P, Q ∈ R[X]` over a real closed field `R` (a linearly ordered field
suffices), with `Z = Zer(P, R)` and the counts `c(Q ⋈ 0, Z)` of
`P`-roots `x` with `Q(x) ⋈ 0` as in Proposition 2.64. Unlike
Proposition 2.64, here `P` and `Q` may share roots: the third
Tarski-query `TaQ(Q², P)` supplies the missing information.

**Proposition 2.65.**

* `c(Q = 0, Z) = TaQ(1, P) − TaQ(Q², P)`,
* `c(Q > 0, Z) = (TaQ(Q², P) + TaQ(Q, P)) / 2`,
* `c(Q < 0, Z) = (TaQ(Q², P) − TaQ(Q, P)) / 2`.

The proof rests on three identities:

* `TaQ(1, P)  = c(Q = 0, Z) + c(Q > 0, Z) + c(Q < 0, Z)` (every root,
  each contributing `sign(1) = 1`; the roots partition by the sign of
  `Q`);
* `TaQ(Q, P)  = c(Q > 0, Z) − c(Q < 0, Z)`
  (`tarskiQueryOn_eq_card_pos_sub_card_neg`);
* `TaQ(Q², P) = c(Q > 0, Z) + c(Q < 0, Z)` (`sign(Q(x)²) = 1` exactly
  when `Q(x) ≠ 0`, counting the roots off `Z(Q)`).

Then solve the linear system.
-/

open scoped Polynomial

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- **BPR Proposition 2.65.** The three counts of `P`-roots by the sign
of `Q` are recovered from the Tarski-queries `TaQ(1, P)`, `TaQ(Q, P)`,
and `TaQ(Q², P)` — no coprimality assumption is needed. -/
theorem proposition_2_65 (P Q : R[X]) :
    ((P.roots.toFinset.filter (fun x => Q.eval x = 0)).card : ℤ)
        = tarskiQuery 1 P - tarskiQuery (Q ^ 2) P ∧
    ((P.roots.toFinset.filter (fun x => 0 < Q.eval x)).card : ℤ)
        = (tarskiQuery (Q ^ 2) P + tarskiQuery Q P) / 2 ∧
    ((P.roots.toFinset.filter (fun x => Q.eval x < 0)).card : ℤ)
        = (tarskiQuery (Q ^ 2) P - tarskiQuery Q P) / 2 := by
  classical
  -- (i) `TaQ(Q, P) = c(Q > 0) − c(Q < 0)`.
  have hfp : P.roots.toFinset.filter
        (fun x => x ∈ ExtendedPoint.openInterval (R := R) .negInf .posInf ∧
                  0 < Q.eval x)
      = P.roots.toFinset.filter (fun x => 0 < Q.eval x) := by
    apply Finset.filter_congr; intro x _; simp [ExtendedPoint.openInterval]
  have hfn : P.roots.toFinset.filter
        (fun x => x ∈ ExtendedPoint.openInterval (R := R) .negInf .posInf ∧
                  Q.eval x < 0)
      = P.roots.toFinset.filter (fun x => Q.eval x < 0) := by
    apply Finset.filter_congr; intro x _; simp [ExtendedPoint.openInterval]
  have htaQ : tarskiQuery Q P =
      ((P.roots.toFinset.filter (fun x => 0 < Q.eval x)).card : ℤ) -
      ((P.roots.toFinset.filter (fun x => Q.eval x < 0)).card : ℤ) := by
    rw [tarskiQuery, tarskiQueryOn_eq_card_pos_sub_card_neg, hfp, hfn]
  -- (ii) `TaQ(1, P) = #Z` (every root of `P`).
  have hta1 : tarskiQuery (1 : R[X]) P = (P.roots.toFinset.card : ℤ) := by
    rw [tarskiQuery, tarskiQueryOn_eq_card_pos_sub_card_neg]
    rw [show P.roots.toFinset.filter
            (fun x => x ∈ ExtendedPoint.openInterval (R := R) .negInf .posInf ∧
                      0 < (1 : R[X]).eval x)
          = P.roots.toFinset from by
          apply Finset.filter_eq_self.mpr
          intro x _; exact ⟨Set.mem_univ x, by simp⟩,
      show P.roots.toFinset.filter
            (fun x => x ∈ ExtendedPoint.openInterval (R := R) .negInf .posInf ∧
                      (1 : R[X]).eval x < 0)
          = ∅ from by
          rw [Finset.filter_eq_empty_iff]; intro x _; simp,
      Finset.card_empty]
    simp
  -- (iii) `TaQ(Q², P) = #{root | Q ≠ 0}` (`sign(Q²) = 1` iff `Q ≠ 0`).
  have htaQ2 : tarskiQuery (Q ^ 2) P =
      ((P.roots.toFinset.filter (fun x => ¬ Q.eval x = 0)).card : ℤ) := by
    rw [tarskiQuery, tarskiQueryOn_eq_card_pos_sub_card_neg]
    rw [show P.roots.toFinset.filter
            (fun x => x ∈ ExtendedPoint.openInterval (R := R) .negInf .posInf ∧
                      0 < (Q ^ 2).eval x)
          = P.roots.toFinset.filter (fun x => ¬ Q.eval x = 0) from by
          apply Finset.filter_congr
          intro x _
          rw [Polynomial.eval_pow]
          constructor
          · rintro ⟨_, h⟩ hq0; rw [hq0] at h; simp at h
          · intro hq; exact ⟨Set.mem_univ x, by rw [pow_two]; exact mul_self_pos.mpr hq⟩,
      show P.roots.toFinset.filter
            (fun x => x ∈ ExtendedPoint.openInterval (R := R) .negInf .posInf ∧
                      (Q ^ 2).eval x < 0)
          = ∅ from by
          rw [Finset.filter_eq_empty_iff]
          intro x _
          rw [Polynomial.eval_pow]
          rintro ⟨_, h⟩
          exact absurd h (not_lt.mpr (sq_nonneg _)),
      Finset.card_empty]
    simp
  -- The roots with `Q ≠ 0` split into the `Q > 0` and `Q < 0` parts.
  have hFp : (P.roots.toFinset.filter (fun x => ¬ Q.eval x = 0)).filter
        (fun x => 0 < Q.eval x)
      = P.roots.toFinset.filter (fun x => 0 < Q.eval x) := by
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro x _
    exact ⟨fun h => h.2, fun h => ⟨ne_of_gt h, h⟩⟩
  have hFn : (P.roots.toFinset.filter (fun x => ¬ Q.eval x = 0)).filter
        (fun x => ¬ 0 < Q.eval x)
      = P.roots.toFinset.filter (fun x => Q.eval x < 0) := by
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro x _
    constructor
    · rintro ⟨hne, hnpos⟩; exact lt_of_le_of_ne (not_lt.mp hnpos) hne
    · intro h; exact ⟨ne_of_lt h, not_lt.mpr h.le⟩
  have hB : ((P.roots.toFinset.filter (fun x => ¬ Q.eval x = 0)).card : ℤ) =
      ((P.roots.toFinset.filter (fun x => 0 < Q.eval x)).card : ℤ) +
      ((P.roots.toFinset.filter (fun x => Q.eval x < 0)).card : ℤ) := by
    rw [← hFp, ← hFn]
    exact_mod_cast (Finset.card_filter_add_card_filter_not
      (s := P.roots.toFinset.filter (fun x => ¬ Q.eval x = 0))
      (fun x => 0 < Q.eval x)).symm
  -- `#Z = c(Q = 0) + #{Q ≠ 0}`.
  have hcompl : (P.roots.toFinset.card : ℤ) =
      ((P.roots.toFinset.filter (fun x => Q.eval x = 0)).card : ℤ) +
      ((P.roots.toFinset.filter (fun x => ¬ Q.eval x = 0)).card : ℤ) := by
    exact_mod_cast (Finset.card_filter_add_card_filter_not
      (s := P.roots.toFinset) (fun x => Q.eval x = 0)).symm
  refine ⟨?_, ?_, ?_⟩ <;> omega

end Azurite.BPR
