/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_5.Proposition_2_87
import Azurite.BasuPollackRoy.Chapter2.Section2_1.Exercise_2_11
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Algebra.AlgebraicCard

/-! # BPR remark following Proposition 2.87 — non-uniqueness of the extension, concretely

BPR illustrate that `Ext(S, R')` is not the *only* semialgebraic subset of `R'ᵏ` whose
intersection with `Rᵏ` is `S`. Their example takes `R = R_alg` (the real algebraic numbers),
`R' = ℝ`, and `S = [0,4]`: then `Ext(S, ℝ) = [0,4]`, but the punctured interval
`[0, π) ∪ (π, 4] = [0,4] ∖ {π}` also meets `R_alg` in `S`, since `π ∉ R_alg`.

We formalize this. `π`'s transcendence is not available in Mathlib, but it is not needed:
*any* transcendental real in `(0, 4)` plays the role of `π`, and one exists because the
real algebraic numbers are countable while `(0, 4)` is uncountable. The general
non-uniqueness statement is `ext_not_unique`; here we instantiate it at `R_alg ⊆ ℝ`.
-/

namespace Azurite.BPR

open Azurite.BPR.Exercise2_11

/-- There is a transcendental real number in the open interval `(0, 4)`: the real algebraic
numbers are countable (`Algebraic.countable`), but `(0, 4)` is uncountable
(`Real.Ioo_countable_iff`). This element plays the role of `π` in BPR's example. -/
theorem exists_transcendental_mem_Ioo :
    ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 4 ∧ t ∉ realAlgebraicNumbers := by
  have hcount : (realAlgebraicNumbers).Countable := Algebraic.countable ℤ ℝ
  have hunc : ¬ (Set.Ioo (0 : ℝ) 4).Countable := by
    rw [Cardinal.Real.Ioo_countable_iff]; norm_num
  obtain ⟨t, htin, htnotin⟩ := Set.not_subset.mp (fun hsub => hunc (hcount.mono hsub))
  exact ⟨t, htin, htnotin⟩

/-- **BPR's example following Proposition 2.87.** Over the real algebraic numbers `R_alg`,
take `S = [0,4]`. Its extension to `ℝ` is `Ext(S, ℝ) = [0,4]`, yet the punctured interval
`[0,4] ∖ {t}` (for a transcendental `t ∈ (0,4)`, in BPR's example `t = π`) is a *different*
semialgebraic subset of `ℝ` whose intersection with `R_alg` is again `S`. Hence `Ext` is not
characterized by `Ext(S, ℝ) ∩ R_alg = S`. -/
theorem ext_not_unique_R_alg :
    ∃ (S : Set (Fin 1 → R_alg)) (hS : IsSemialgebraicSet S) (T' : Set (Fin 1 → ℝ)),
      IsSemialgebraicSet T' ∧
      (fun y : Fin 1 → R_alg => algebraMap R_alg ℝ ∘ y) ⁻¹' T' = S ∧
      T' ≠ extension (R' := ℝ) S hS := by
  obtain ⟨t, htin, htnotin⟩ := exists_transcendental_mem_Ioo
  refine ext_not_unique (R := R_alg) (R' := ℝ) t ?_ htin.1 htin.2
  intro y heq
  apply htnotin
  have hy : (y : ℝ) ∈ realAlgebraicNumbers := mem_R_alg_iff_isAlgebraic_int.mp y.2
  have hcoe : algebraMap (R_alg) ℝ y = (y : ℝ) := rfl
  rw [hcoe] at heq
  rwa [heq] at hy

end Azurite.BPR
