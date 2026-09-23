/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzPolynomial.ExtendedSRemS
import Azurite.AzPolynomial.Equiv.Mul
import Azurite.AzPolynomial.Equiv.Neg
import Azurite.AzPolynomial.Equiv.QuoRem
import Azurite.AzPolynomial.Equiv.SturmSequence
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Definition1_10
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Lemma1_11

/-!
# Equivalence: AzPolynomial extended signed remainder sequence ↔ `Polynomial`

`toPoly (sRemU P Q n) = Azurite.BPR.SRemU (toPoly P) (toPoly Q) n` and likewise
for `sRemV`, mirroring `toPoly_sRemS`. Together with the abstract Bézout identity
(BPR Lemma 1.11) this gives the correctness of Algorithm 8.20: the computable
cofactors satisfy `sRemUₙ · P + sRemVₙ · Q = sRemSₙ`.
-/

open Polynomial

namespace Azurite.AzPolynomial

variable {K : Type _} [Field K] [DecidableEq K]

/-- `toPoly (sRemU P Q n) = BPR.SRemU (toPoly P) (toPoly Q) n`. -/
theorem toPoly_sRemU (P Q : AzPolynomial K) (n : ℕ) :
    AzPolynomial.toPoly (sRemU P Q n) =
      Azurite.BPR.SRemU (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [sRemU, Azurite.BPR.SRemU]
    | 1 => simp [sRemU, Azurite.BPR.SRemU]
    | n + 2 =>
      have hu_n := ih n (by omega)
      have hu_succ := ih (n + 1) (by omega)
      rw [sRemU_succ_succ]
      by_cases hprev : sRemS P Q (n + 1) = 0
      · have hs0 : Azurite.BPR.SRemS (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) (n + 1) = 0 := by
          rw [← toPoly_sRemS, hprev, toPoly_zero]
        rw [ite_eq_left hprev, toPoly_zero, Azurite.BPR.SRemU, ite_eq_left hs0]
      · have hsne : AzPolynomial.toPoly (sRemS P Q (n + 1)) ≠ 0 := by
          rw [Ne, ← toPoly_zero (R := K), toPoly_inj]; exact hprev
        have hs0' : Azurite.BPR.SRemS (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) (n + 1) ≠ 0 := by
          rw [← toPoly_sRemS]; exact hsne
        rw [ite_eq_right hprev, Azurite.BPR.SRemU_ss _ _ _ hs0', toPoly_add, toPoly_neg,
          toPoly_mul, toPoly_quo _ _ hsne, hu_n, hu_succ, toPoly_sRemS, toPoly_sRemS]

/-- `toPoly (sRemV P Q n) = BPR.SRemV (toPoly P) (toPoly Q) n`. -/
theorem toPoly_sRemV (P Q : AzPolynomial K) (n : ℕ) :
    AzPolynomial.toPoly (sRemV P Q n) =
      Azurite.BPR.SRemV (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [sRemV, Azurite.BPR.SRemV]
    | 1 => simp [sRemV, Azurite.BPR.SRemV]
    | n + 2 =>
      have hv_n := ih n (by omega)
      have hv_succ := ih (n + 1) (by omega)
      rw [sRemV_succ_succ]
      by_cases hprev : sRemS P Q (n + 1) = 0
      · have hs0 : Azurite.BPR.SRemS (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) (n + 1) = 0 := by
          rw [← toPoly_sRemS, hprev, toPoly_zero]
        rw [ite_eq_left hprev, toPoly_zero, Azurite.BPR.SRemV, ite_eq_left hs0]
      · have hsne : AzPolynomial.toPoly (sRemS P Q (n + 1)) ≠ 0 := by
          rw [Ne, ← toPoly_zero (R := K), toPoly_inj]; exact hprev
        have hs0' : Azurite.BPR.SRemS (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) (n + 1) ≠ 0 := by
          rw [← toPoly_sRemS]; exact hsne
        rw [ite_eq_right hprev, Azurite.BPR.SRemV_ss _ _ _ hs0', toPoly_add, toPoly_neg,
          toPoly_mul, toPoly_quo _ _ hsne, hv_n, hv_succ, toPoly_sRemS, toPoly_sRemS]

/-- `sRemUList`/`sRemVList` mapped through `toPoly` match the abstract sequences. -/
theorem map_sRemUList_toPoly (P Q : AzPolynomial K) (n : ℕ) :
    (sRemUList P Q n).map AzPolynomial.toPoly =
      (List.range n).map (Azurite.BPR.SRemU (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q)) := by
  simp only [sRemUList, List.map_map]
  exact List.map_congr_left fun i _ => toPoly_sRemU P Q i

theorem map_sRemVList_toPoly (P Q : AzPolynomial K) (n : ℕ) :
    (sRemVList P Q n).map AzPolynomial.toPoly =
      (List.range n).map (Azurite.BPR.SRemV (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q)) := by
  simp only [sRemVList, List.map_map]
  exact List.map_congr_left fun i _ => toPoly_sRemV P Q i

/-- **Correctness of Algorithm 8.20 (Bézout identity).** The computable cofactors
    satisfy `sRemUₙ · P + sRemVₙ · Q = sRemSₙ` (BPR Lemma 1.11). -/
theorem sRemS_eq_bezout (P Q : AzPolynomial K) (n : ℕ) :
    sRemS P Q n = sRemU P Q n * P + sRemV P Q n * Q := by
  apply toPoly_inj.mp
  rw [toPoly_add, toPoly_mul, toPoly_mul, toPoly_sRemU, toPoly_sRemV, toPoly_sRemS]
  exact Azurite.BPR.lemma_1_11_bezout (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) n

end Azurite.AzPolynomial
