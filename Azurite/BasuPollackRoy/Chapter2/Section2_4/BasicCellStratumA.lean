/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_4.ParametrizedTarskiQuery
import Azurite.BasuPollackRoy.Chapter2.Section2_4.BasicCellProjection
import Azurite.BasuPollackRoy.Chapter2.Section2_4.Proposition_2_68

/-! # Stratum A of the Theorem 2.76 kernel: the matrix locus

`stratumA_eq_matrix` reduces Stratum A (the `P_y ≢ 0` part of the basic-cell
projection) to the locus
`{y | P_y ≠ 0 ∧ 0 < (Mₛ⁻¹ ·ᵥ TaQvec(y))_{j₀}}`,
where `TaQvec(y)_i = TaQ(𝒬_y^{expFn i}, P_y)` and `Mₛ⁻¹` is a **constant** rational
matrix. This file proves that locus semialgebraic over `D`.

The Tarski-query vector `TaQvec(y)` takes integer values bounded by `deg P_y ≤ N`
(`abs_tarskiQuery_le_natDegree`), so there are only finitely many possible value
vectors `c`. On each fibre `{y | TaQvec(y) = c}` the matrix condition
`0 < (Mₛ⁻¹ ·ᵥ c)_{j₀}` is constant, so the locus is the **finite union**, over the
value vectors `c` (in a bounded box) satisfying the positivity, of the **finite
intersection** over the components `i` of the parametrized Tarski loci
`{y | P_y ≠ 0 ∧ TaQ(𝒬_y^{expFn i}, P_y) = c i}` — each semialgebraic over `D` by
`tarskiLocus_isSemialgebraicSetOver`. Finite unions/intersections preserve
semialgebraicity.
-/

open _root_.Polynomial
open scoped Matrix

namespace Azurite.BPR

/-! ### Finite-set closure helpers -/

variable {k : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable {D : Type*} [CommRing D] [Algebra D R]

omit [IsStrictOrderedRing R] in
theorem IsSemialgebraicSetOver.univ' :
    IsSemialgebraicSetOver D (Set.univ : Set (Fin k → R)) :=
  .algebraic ⟨∅, by ext x; simp⟩

omit [IsStrictOrderedRing R] in
/-- A finite intersection of sets semialgebraic over `D` is semialgebraic over `D`. -/
theorem IsSemialgebraicSetOver.finsetBiInter {ι : Type*} (t : Finset ι)
    (A : ι → Set (Fin k → R)) (h : ∀ i ∈ t, IsSemialgebraicSetOver D (A i)) :
    IsSemialgebraicSetOver D (⋂ i ∈ t, A i) := by
  classical
  induction t using Finset.induction with
  | empty => simpa using IsSemialgebraicSetOver.univ'
  | insert a t ha ih =>
    rw [Finset.set_biInter_insert]
    exact (h a (Finset.mem_insert_self _ _)).inter
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

omit [IsStrictOrderedRing R] in
/-- A finite union of sets semialgebraic over `D` is semialgebraic over `D`. -/
theorem IsSemialgebraicSetOver.finsetBiUnion {ι : Type*} (t : Finset ι)
    (A : ι → Set (Fin k → R)) (h : ∀ i ∈ t, IsSemialgebraicSetOver D (A i)) :
    IsSemialgebraicSetOver D (⋃ i ∈ t, A i) := by
  classical
  induction t using Finset.induction with
  | empty =>
    simpa using (IsSemialgebraicSetOver.empty : IsSemialgebraicSetOver D (∅ : Set (Fin k → R)))
  | insert a t ha ih =>
    rw [Finset.set_biUnion_insert]
    exact (h a (Finset.mem_insert_self _ _)).union
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-! ### The Tarski-query bound -/

omit [IsStrictOrderedRing R] [Algebra D R] in
/-- `|TaQ(Q, P)| ≤ deg P`: the Tarski query is a sum of root signs, so its
absolute value is at most the number of distinct roots, itself at most `deg P`. -/
theorem abs_tarskiQuery_le_natDegree (Q' P : R[X]) :
    |tarskiQuery Q' P| ≤ (P.natDegree : ℤ) := by
  rw [tarskiQuery_eq_sum_roots]
  have hsign : ∀ x, |(SignType.sign (Q'.eval x) : ℤ)| ≤ 1 := by
    intro x; rcases SignType.sign (Q'.eval x) with _ | _ | _ <;> decide
  calc |∑ x ∈ P.roots.toFinset, (SignType.sign (Q'.eval x) : ℤ)|
      ≤ ∑ x ∈ P.roots.toFinset, |(SignType.sign (Q'.eval x) : ℤ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x ∈ P.roots.toFinset, (1 : ℤ) := Finset.sum_le_sum (fun x _ => hsign x)
    _ = (P.roots.toFinset.card : ℤ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ (P.natDegree : ℤ) := by
        exact_mod_cast le_trans (Multiset.toFinset_card_le _) (Polynomial.card_roots' P)

/-! ### The matrix locus is semialgebraic; Stratum A is closed -/

section MatrixLocus

variable {s : ℕ} [IsDomain D] [IsRealClosed R]

/-- **The matrix locus is semialgebraic over `D`.** For a constant rational matrix
`M`, the locus `{y | P_y ≠ 0 ∧ 0 < (M ·ᵥ TaQvec(y))_{j₀}}` (where
`TaQvec(y)_i = TaQ(𝒬_y^{expFn i}, P_y)`) is semialgebraic over `D`.

The integer vector `TaQvec(y)` is bounded by `deg P_y ≤ N := deg P_split`
(`abs_tarskiQuery_le_natDegree`), so only finitely many value vectors `c` occur. On
each fibre `{y | TaQvec(y) = c}` the matrix condition is constant, so the locus is the
finite union, over value vectors `c` (in the box `[-N,N]^{3^s}`) with
`0 < (M ·ᵥ c)_{j₀}`, of the finite intersection over `i` of the parametrized Tarski
loci `tarskiLocus_isSemialgebraicSetOver`. -/
theorem matrixLocus_isSemialgebraicSetOver
    (P_split : Polynomial (MvPolynomial (Fin k) D))
    (𝒬 : Fin s → Polynomial (MvPolynomial (Fin k) D))
    (M : Matrix (Fin (3 ^ s)) (Fin (3 ^ s)) ℚ) (j₀ : Fin (3 ^ s))
    (hinj : Function.Injective (algebraMap D R)) :
    IsSemialgebraicSetOver D
      {y : Fin k → R | P_split.map (MvPolynomial.aeval y).toRingHom ≠ 0 ∧
        0 < (M *ᵥ (fun i => (tarskiQuery
              (familyPow (fun j => (𝒬 j).map (MvPolynomial.aeval y).toRingHom) (expFn s i))
              (P_split.map (MvPolynomial.aeval y).toRingHom) : ℚ))) j₀} := by
  classical
  set N := P_split.natDegree with hN
  set taq : (Fin k → R) → Fin (3 ^ s) → ℤ := fun y i =>
    tarskiQuery (familyPow (fun j => (𝒬 j).map (MvPolynomial.aeval y).toRingHom) (expFn s i))
      (P_split.map (MvPolynomial.aeval y).toRingHom) with htaq
  set Box : Finset (Fin (3 ^ s) → ℤ) :=
    Fintype.piFinset (fun _ => Finset.Icc (-(N : ℤ)) N) with hBox
  set S : Finset (Fin (3 ^ s) → ℤ) :=
    Box.filter (fun c => 0 < (M *ᵥ (fun i => (c i : ℚ))) j₀) with hS
  have hset : {y : Fin k → R | P_split.map (MvPolynomial.aeval y).toRingHom ≠ 0 ∧
        0 < (M *ᵥ (fun i => (taq y i : ℚ))) j₀} =
      ⋃ c ∈ S, ⋂ i ∈ (Finset.univ : Finset (Fin (3 ^ s))),
        {y : Fin k → R | P_split.map (MvPolynomial.aeval y).toRingHom ≠ 0 ∧ taq y i = c i} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter,
      exists_prop, Finset.mem_univ, forall_true_left]
    constructor
    · rintro ⟨hPy, hpos⟩
      refine ⟨taq y, ?_, fun i => ⟨hPy, rfl⟩⟩
      rw [hS, Finset.mem_filter]
      refine ⟨?_, hpos⟩
      rw [hBox, Fintype.mem_piFinset]
      intro i
      rw [Finset.mem_Icc]
      have hb : |taq y i| ≤ (N : ℤ) := by
        rw [htaq]
        exact le_trans (abs_tarskiQuery_le_natDegree _ _)
          (by exact_mod_cast Polynomial.natDegree_map_le)
      constructor <;> [exact (abs_le.mp hb).1; exact (abs_le.mp hb).2]
    · rintro ⟨c, hcS, hAi⟩
      have hPy : P_split.map (MvPolynomial.aeval y).toRingHom ≠ 0 := (hAi j₀).1
      have htc : ∀ i, taq y i = c i := fun i => (hAi i).2
      rw [hS, Finset.mem_filter] at hcS
      refine ⟨hPy, ?_⟩
      have hvc : (fun i => (taq y i : ℚ)) = (fun i => (c i : ℚ)) :=
        funext (fun i => by rw [htc i])
      rw [hvc]; exact hcS.2
  rw [hset]
  apply IsSemialgebraicSetOver.finsetBiUnion
  intro c _
  apply IsSemialgebraicSetOver.finsetBiInter
  intro i _
  exact tarskiLocus_isSemialgebraicSetOver P_split 𝒬 (expFn s i) (c i) hinj

/-- **Stratum A is semialgebraic over `D`.** Combining `stratumA_eq_matrix` (Lemma 2.74)
with `matrixLocus_isSemialgebraicSetOver`: the `P_y ≢ 0` stratum of the basic-cell
projection — `{y | P_y ≠ 0 ∧ ∃ x, P_y(x) = 0 ∧ ⋀_{q ∈ 𝒬} q_y(x) > 0}` — is
semialgebraic over `D`. -/
theorem stratumA_isSemialgebraicSetOver
    (hinj : Function.Injective (algebraMap D R))
    (P : MvPolynomial (Fin (k + 1)) D) (Q : Finset (MvPolynomial (Fin (k + 1)) D)) :
    IsSemialgebraicSetOver D
      {y : Fin k → R | (splitLast P).map (MvPolynomial.aeval y).toRingHom ≠ 0 ∧
        ∃ x, ((splitLast P).map (MvPolynomial.aeval y).toRingHom).IsRoot x ∧
          ∀ q ∈ Q, 0 < ((splitLast q).map (MvPolynomial.aeval y).toRingHom).eval x} := by
  rw [stratumA_eq_matrix]
  exact matrixLocus_isSemialgebraicSetOver (splitLast P)
    (fun j => splitLast (Q.toList.get j)) ((signMatrixQ Q.toList.length)⁻¹)
    ((signEquiv Q.toList.length).symm (fun _ => SignType.pos)) hinj

end MatrixLocus

end Azurite.BPR
