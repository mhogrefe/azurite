/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_2.Notation_2_56

/-!
# BPR Proposition 2.64

Let `P, Q ∈ R[X]` over a real closed field `R` (a linearly ordered field
suffices here). Write `Z = Zer(P, R) = {x | P(x) = 0}` and, for a sign
`⋈ ∈ {>, <}`, let `c(Q ⋈ 0, Z)` be the number of roots `x` of `P` with
`Q(x) ⋈ 0` (the cardinality of `Reali(Q ⋈ 0, Z)`).

**Proposition 2.64.** If `P` and `Q` have no common root in `R`, then

* `c(Q > 0, Z) = (TaQ(1, P) + TaQ(Q, P)) / 2`,
* `c(Q < 0, Z) = (TaQ(1, P) − TaQ(Q, P)) / 2`,

where `TaQ` is the Tarski-query (`tarskiQuery`).

The proof rests on two identities:

* `TaQ(1, P) = c(Q > 0, Z) + c(Q < 0, Z)` — `TaQ(1, P)` counts all roots
  of `P` (each contributing `sign(1) = 1`), and since `P, Q` have no
  common root every root has `Q ≠ 0`, so the roots split into the
  `Q > 0` and `Q < 0` parts (the `Q = 0` part `c(Q = 0, Z)` is empty);
* `TaQ(Q, P) = c(Q > 0, Z) − c(Q < 0, Z)` —
  `tarskiQueryOn_eq_card_pos_sub_card_neg` on the whole line.

Adding and subtracting then solves for the two cardinalities.
-/

open scoped Polynomial

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- **BPR Proposition 2.64.** When `P` and `Q` have no common root, the
counts of `P`-roots with `Q > 0` (resp. `Q < 0`) are recovered from the
Tarski-queries `TaQ(1, P)` and `TaQ(Q, P)`. -/
theorem proposition_2_64 (P Q : R[X]) (hP : P ≠ 0)
    (hndisjoint : ∀ x : R, P.IsRoot x → Q.eval x ≠ 0) :
    ((P.roots.toFinset.filter (fun x => 0 < Q.eval x)).card : ℤ)
        = (tarskiQuery 1 P + tarskiQuery Q P) / 2 ∧
    ((P.roots.toFinset.filter (fun x => Q.eval x < 0)).card : ℤ)
        = (tarskiQuery 1 P - tarskiQuery Q P) / 2 := by
  classical
  -- On the whole line the interval condition `x ∈ (−∞, +∞)` is vacuous.
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
  -- (i) `TaQ(Q, P) = c(Q > 0) − c(Q < 0)`.
  have htaQ : tarskiQuery Q P =
      ((P.roots.toFinset.filter (fun x => 0 < Q.eval x)).card : ℤ) -
      ((P.roots.toFinset.filter (fun x => Q.eval x < 0)).card : ℤ) := by
    rw [tarskiQuery, tarskiQueryOn_eq_card_pos_sub_card_neg, hfp, hfn]
  -- On the roots of `P`, `¬ (0 < Q)` is the same as `Q < 0` (since `Q ≠ 0`).
  have hfilter_neg : P.roots.toFinset.filter (fun x => ¬ 0 < Q.eval x)
      = P.roots.toFinset.filter (fun x => Q.eval x < 0) := by
    apply Finset.filter_congr
    intro x hx
    have hx' : P.IsRoot x := by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hP] at hx; exact hx
    have hQne : Q.eval x ≠ 0 := hndisjoint x hx'
    constructor
    · intro h; exact lt_of_le_of_ne (not_lt.mp h) hQne
    · intro h; exact not_lt.mpr h.le
  -- (ii) `TaQ(1, P) = c(Q > 0) + c(Q < 0)`.
  have hta1 : tarskiQuery (1 : R[X]) P =
      ((P.roots.toFinset.filter (fun x => 0 < Q.eval x)).card : ℤ) +
      ((P.roots.toFinset.filter (fun x => Q.eval x < 0)).card : ℤ) := by
    -- `TaQ(1, P)` counts every root of `P` (`sign(1) = 1`).
    have hroots : tarskiQuery (1 : R[X]) P = (P.roots.toFinset.card : ℤ) := by
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
    rw [hroots, ← hfilter_neg]
    exact_mod_cast (Finset.card_filter_add_card_filter_not
      (s := P.roots.toFinset) (fun x => 0 < Q.eval x)).symm
  refine ⟨?_, ?_⟩ <;> omega

end Azurite.BPR
