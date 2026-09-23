/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_4.Lemma_2_74
import Azurite.BasuPollackRoy.Chapter1.Section1_3.SplitLast
import Azurite.BasuPollackRoy.Chapter2.Section2_4.Theorem_2_76

/-! # The basic-cell projection kernel of Theorem 2.76 (in progress)

The remaining content of BPR Theorem 2.76 is the **basic-cell projection**:
`{y | ∃ x, P(y,x) = 0 ∧ ⋀ q ∈ 𝒬, q(y,x) > 0}` is semialgebraic over `D`. Following
BPR, this is the parametrized sign determination — the family analogue of
`fiberFormula_high` (Theorem 2.62).

## Plan

1. **Fixed-field bridge** (`basicCell_nonempty_iff`, this file) — over a fixed real
   closed field, `P ≠ 0` has a root at which every `q ∈ 𝒬` is positive iff the
   all-positive component of `Mₛ⁻¹ · TaQ(𝒬^A, P)` is positive (Lemma 2.74 with the
   all-`+` sign condition).
2. **Parametrized Tarski queries** — express each `TaQ(𝒬_y^α, P_y)` as a function of
   `y` via the leaf machinery of `goodRootLeafPatterns` applied to `P_y' · 𝒬_y^α`
   (reusing `sturmCount_eq_actual_varAt_diff`, the `splitLast` bridge
   `aeval_snoc_eq_eval_splitLast`, and the degree locus `degFormula`).
3. **Assemble** the `basicCellFormula` (a quantifier-free formula over `D` whose
   realization is the `P_y ≢ 0` stratum of the cell projection) and the `P_y ≡ 0`
   stratum via Lemma 2.75.
-/

open _root_.Polynomial
open scoped Matrix

namespace Azurite.BPR

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- **Basic cell emptiness via Lemma 2.74 (fixed field).** A polynomial `P ≠ 0`
has a root at which every member of the family `Q` is strictly positive iff the
all-positive component of `Mₛ⁻¹ · TaQ(𝒬^A, P)` is positive. This is Lemma 2.74
instantiated at the all-`+` sign condition. -/
theorem basicCell_nonempty_iff (s : ℕ) (P : R[X]) (Q : Fin s → R[X]) (hP : P ≠ 0) :
    (∃ x, P.IsRoot x ∧ ∀ i, 0 < (Q i).eval x) ↔
    0 < ((signMatrixQ s)⁻¹ *ᵥ (fun i => (tarskiQuery (familyPow Q (expFn s i)) P : ℚ)))
      ((signEquiv s).symm (fun _ => SignType.pos)) := by
  have hsf : signFn s ((signEquiv s).symm (fun _ => SignType.pos)) = (fun _ => SignType.pos) :=
    (signEquiv s).apply_symm_apply (fun _ => SignType.pos)
  rw [← lemma_2_74 s P Q hP ((signEquiv s).symm (fun _ => SignType.pos)), hsf]
  constructor
  · rintro ⟨x, hr, hpos⟩
    exact ⟨x, hr, fun i => sign_eq_one_iff.mpr (hpos i)⟩
  · rintro ⟨x, hx⟩
    rw [SignCondition.realizationOver, Set.mem_ofPred_eq] at hx
    exact ⟨x, hx.1, fun i => sign_eq_one_iff.mp (hx.2 i)⟩

variable {k : ℕ} {D : Type*} [CommRing D] [Algebra D R]

omit [IsStrictOrderedRing R] in
/-- **`splitLast` bridge.** The projection of the multivariate basic cell equals the
set of `y` for which the *specialized univariate* polynomial `P_y = (splitLast P)`
evaluated at `y` has a root at which every `q_y` is positive — the univariate form
where `basicCell_nonempty_iff` applies. -/
theorem cellProjection_eq_split (P : MvPolynomial (Fin (k+1)) D)
    (Q : Finset (MvPolynomial (Fin (k+1)) D)) :
    Fin.init '' {x : Fin (k+1) → R |
        MvPolynomial.aeval x P = 0 ∧ ∀ q ∈ Q, MvPolynomial.aeval x q > 0} =
    {y : Fin k → R | ∃ x : R, ((splitLast P).map (MvPolynomial.aeval y).toRingHom).IsRoot x ∧
      ∀ q ∈ Q, 0 < ((splitLast q).map (MvPolynomial.aeval y).toRingHom).eval x} := by
  rw [Fin.init_image_eq_setOf_exists_snoc]
  ext y
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, hP, hQ⟩
    refine ⟨x, ?_, fun q hq => ?_⟩
    · rw [Polynomial.IsRoot, ← aeval_snoc_eq_eval_splitLast]; exact hP
    · rw [← aeval_snoc_eq_eval_splitLast]; exact hQ q hq
  · rintro ⟨x, hP, hQ⟩
    refine ⟨x, ?_, fun q hq => ?_⟩
    · rw [aeval_snoc_eq_eval_splitLast]; exact hP
    · rw [aeval_snoc_eq_eval_splitLast]; exact hQ q hq

omit [IsStrictOrderedRing R] in
/-- Splitting the existence of a root carrying a side condition by whether the
polynomial vanishes identically: if it does, the root condition is vacuous (every
`x` is a root), so only the side condition survives. -/
theorem exists_root_and_split (p : R[X]) (Φ : R → Prop) :
    (∃ x, p.IsRoot x ∧ Φ x) ↔
      (p ≠ 0 ∧ ∃ x, p.IsRoot x ∧ Φ x) ∨ (p = 0 ∧ ∃ x, Φ x) := by
  by_cases hp : p = 0
  · subst hp; simp [Polynomial.IsRoot]
  · simp [hp]

omit [IsStrictOrderedRing R] in
/-- **Two-strata split of the basic-cell projection (univariate form).** Splitting on
whether the specialized polynomial `P_y` vanishes identically: the `P_y ≢ 0` stratum
(finitely many roots — Lemma 2.74) and the `P_y ≡ 0` stratum (every `x` a root, so the
root condition drops — Lemma 2.75). -/
theorem cellProjSplit_strata (P : MvPolynomial (Fin (k+1)) D)
    (Q : Finset (MvPolynomial (Fin (k+1)) D)) :
    {y : Fin k → R | ∃ x : R, ((splitLast P).map (MvPolynomial.aeval y).toRingHom).IsRoot x ∧
        ∀ q ∈ Q, 0 < ((splitLast q).map (MvPolynomial.aeval y).toRingHom).eval x} =
    {y | (splitLast P).map (MvPolynomial.aeval y).toRingHom ≠ 0 ∧
        ∃ x, ((splitLast P).map (MvPolynomial.aeval y).toRingHom).IsRoot x ∧
          ∀ q ∈ Q, 0 < ((splitLast q).map (MvPolynomial.aeval y).toRingHom).eval x} ∪
    {y | (splitLast P).map (MvPolynomial.aeval y).toRingHom = 0 ∧
        ∃ x, ∀ q ∈ Q, 0 < ((splitLast q).map (MvPolynomial.aeval y).toRingHom).eval x} := by
  ext y
  exact exists_root_and_split _ _

omit [IsStrictOrderedRing R] in
/-- Rewrite a `Finset`-membership universal as a `Fin`-indexed one over the
`toList` enumeration — the bridge from the `Finset` family `Q` to the `Fin s`
family demanded by `basicCell_nonempty_iff` / Lemma 2.74. -/
private theorem forall_mem_iff_forall_get {α : Type*} (Q : Finset α) (Φ : α → Prop) :
    (∀ q ∈ Q, Φ q) ↔ ∀ i : Fin Q.toList.length, Φ (Q.toList.get i) := by
  constructor
  · intro h i; exact h _ (Finset.mem_toList.mp (Q.toList.get_mem i))
  · intro h q hq
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp (Finset.mem_toList.mpr hq)
    exact h i

/-- **Stratum A as a parametrized matrix condition.** On `{y | P_y ≠ 0}`, the basic
cell is nonempty iff the all-positive component of `Mₛ⁻¹ · TaQ(𝒬_y^A, P_y)` is positive
(Lemma 2.74, with the family `𝒬_y` reindexed from the `Finset` `Q` via its `toList`).
This reduces Stratum A's semialgebraicity over `D` to (i) `{y | P_y ≠ 0}` semialgebraic
(degree locus) and (ii) the **parametrized Tarski-query** matrix locus being
semialgebraic over `D` — the remaining deep content. -/
theorem stratumA_eq_matrix (P : MvPolynomial (Fin (k+1)) D)
    (Q : Finset (MvPolynomial (Fin (k+1)) D)) :
    {y : Fin k → R | (splitLast P).map (MvPolynomial.aeval y).toRingHom ≠ 0 ∧
        ∃ x, ((splitLast P).map (MvPolynomial.aeval y).toRingHom).IsRoot x ∧
          ∀ q ∈ Q, 0 < ((splitLast q).map (MvPolynomial.aeval y).toRingHom).eval x} =
    {y : Fin k → R | (splitLast P).map (MvPolynomial.aeval y).toRingHom ≠ 0 ∧
        0 < ((signMatrixQ Q.toList.length)⁻¹ *ᵥ
            (fun i => (tarskiQuery
              (familyPow (fun j : Fin Q.toList.length =>
                (splitLast (Q.toList.get j)).map (MvPolynomial.aeval y).toRingHom)
                (expFn Q.toList.length i))
              ((splitLast P).map (MvPolynomial.aeval y).toRingHom) : ℚ)))
          ((signEquiv Q.toList.length).symm (fun _ => SignType.pos))} := by
  ext y
  simp only [Set.mem_ofPred_eq]
  refine and_congr_right (fun hPy => ?_)
  rw [← basicCell_nonempty_iff Q.toList.length
    ((splitLast P).map (MvPolynomial.aeval y).toRingHom)
    (fun j : Fin Q.toList.length =>
      (splitLast (Q.toList.get j)).map (MvPolynomial.aeval y).toRingHom) hPy]
  refine exists_congr (fun x => and_congr_right (fun _ => ?_))
  exact forall_mem_iff_forall_get Q
    (fun q => 0 < ((splitLast q).map (MvPolynomial.aeval y).toRingHom).eval x)

omit [IsStrictOrderedRing R] in
/-- **Kernel reduced to two deep strata.** The basic-cell projection is semialgebraic
over `D` once each of its two strata is: the `P_y ≢ 0` stratum (Lemma 2.74, parametrized
Tarski queries) and the `P_y ≡ 0` stratum (Lemma 2.75). Combining
`cellProjection_eq_split` with `cellProjSplit_strata`, the projection is their union, so
`IsSemialgebraicSetOver.union` reassembles. -/
theorem basicCellProjection_of_strata (P : MvPolynomial (Fin (k+1)) D)
    (Q : Finset (MvPolynomial (Fin (k+1)) D))
    (hA : IsSemialgebraicSetOver D
      {y : Fin k → R | (splitLast P).map (MvPolynomial.aeval y).toRingHom ≠ 0 ∧
        ∃ x, ((splitLast P).map (MvPolynomial.aeval y).toRingHom).IsRoot x ∧
          ∀ q ∈ Q, 0 < ((splitLast q).map (MvPolynomial.aeval y).toRingHom).eval x})
    (hB : IsSemialgebraicSetOver D
      {y : Fin k → R | (splitLast P).map (MvPolynomial.aeval y).toRingHom = 0 ∧
        ∃ x, ∀ q ∈ Q, 0 < ((splitLast q).map (MvPolynomial.aeval y).toRingHom).eval x}) :
    IsSemialgebraicSetOver D
      (Fin.init '' {x : Fin (k+1) → R |
        MvPolynomial.aeval x P = 0 ∧ ∀ q ∈ Q, MvPolynomial.aeval x q > 0}) := by
  rw [cellProjection_eq_split, cellProjSplit_strata]
  exact hA.union hB

end Azurite.BPR
