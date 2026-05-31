import Azurite.BasuPollackRoy.Chapter2.Section2_4.BasicCellStratumA
import Azurite.BasuPollackRoy.Chapter2.Section2_4.BasicCellStratumB
import Azurite.BasuPollackRoy.Chapter2.Section2_4.Lemma_2_75

/-! # Stratum B of the Theorem 2.76 kernel, and the proof of Theorem 2.76

Stratum B is the `P_y ≡ 0` part of the basic-cell projection:
`{y | P_y ≡ 0 ∧ ∃ x, ⋀_{q ∈ 𝒬} q_y(x) > 0}`. With `P_y ≡ 0` the cell at `y` is
`{x | ⋀ q_y(x) > 0}`, whose nonemptiness is the **realizability over `R`** of the
all-positive sign condition for the family `𝒬_y`.

By BPR Lemma 2.75 this realizability is decided by the signs of the `q_y` at `±∞`
together with a `matrixLocus`-style Tarski-query condition for `C' = (∏ 𝒬_y)'`. Each
ingredient is a semialgebraic locus (`BasicCellStratumB`/`BasicCellStratumA`), so the
realizability locus — and hence Stratum B — is semialgebraic over `D`.

Combined with `stratumA_isSemialgebraicSetOver`, the basic-cell projection is
semialgebraic over `D` (`basicCellProjection_of_strata`), which by
`theorem_2_76_of_basicCellProjection` gives **BPR Theorem 2.76**: the projection of a
semialgebraic set defined over `D` is semialgebraic over `D`.
-/

open _root_.Polynomial
open scoped Matrix

namespace Azurite.BPR

/-! ### The per-`y` realizability dichotomy (Lemma 2.75) -/

section Realizable

variable {s : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- If `C' = (∏ q)' ≡ 0` (so, in characteristic zero, each `q i` is a nonzero
constant) and the all-positive sign condition is realized, then each `q i` is
positive at `+∞`. The constant case of `realizable_iff_disjuncts`. -/
private theorem realizable_const_signPos (q : Fin s → R[X]) (hq : ∀ i, q i ≠ 0)
    (hC' : (∏ i, q i).derivative = 0) (hreal : ∃ x, ∀ i, 0 < (q i).eval x) (i : Fin s) :
    signAtPosInfty (q i) = SignType.pos := by
  have hprodne : (∏ i, q i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hq i)
  have hdeg0 : (∏ i, q i).natDegree = 0 := Polynomial.natDegree_eq_zero_of_derivative_eq_zero hC'
  have hqi0 : (q i).natDegree = 0 := by
    have := Polynomial.natDegree_le_of_dvd (Finset.dvd_prod_of_mem q (Finset.mem_univ i)) hprodne
    omega
  obtain ⟨x, hx⟩ := hreal
  have hev : (q i).eval x = (q i).leadingCoeff := by
    rw [Polynomial.eq_C_of_natDegree_eq_zero hqi0]; simp [Polynomial.leadingCoeff]
  rw [signAtPosInfty_eq_sign_leadingCoeff]; exact sign_eq_one_iff.mpr (hev ▸ hx i)

/-- **BPR Lemma 2.75 as a realizability dichotomy.** The all-positive sign condition
for a univariate family `q` is realized over `R` iff every `q i` is nonzero and one
of: all signs agree at `−∞`, all agree at `+∞`, or `(∏ q)' ≠ 0` with the all-positive
component of `Mₛ⁻¹ · TaQ(q^A, (∏ q)')` positive (Lemma 2.74). -/
theorem realizable_iff_disjuncts (hIVP : HasIntermediateValueProperty R) (q : Fin s → R[X]) :
    (∃ x, ∀ i, 0 < (q i).eval x) ↔
    (∀ i, q i ≠ 0) ∧
      ((∀ i, signAtNegInfty (q i) = SignType.pos) ∨
       (∀ i, signAtPosInfty (q i) = SignType.pos) ∨
       ((∏ i, q i).derivative ≠ 0 ∧
        0 < ((signMatrixQ s)⁻¹ *ᵥ
            (fun α => (tarskiQuery (familyPow q (expFn s α)) (∏ i, q i).derivative : ℚ)))
          ((signEquiv s).symm (fun _ => SignType.pos)))) := by
  set jp := (signEquiv s).symm (fun _ => SignType.pos) with hj
  have hsf : signFn s jp = (fun _ => SignType.pos) := (signEquiv s).apply_symm_apply _
  have hσ : SignCondition.IsStrict (signFn s jp) := by
    rw [hsf]; intro i; exact (by decide : (SignType.pos : SignType) ≠ 0)
  have hReeq : (∃ x, ∀ i, 0 < (q i).eval x) ↔
      (SignCondition.realization (signFn s jp) (fun i x => (q i).eval x)).Nonempty := by
    simp only [Set.Nonempty, SignCondition.realization, SignCondition.IsRealizedBy,
      Set.mem_setOf_eq, hsf]
    exact exists_congr (fun x => forall_congr' (fun i => sign_eq_one_iff.symm))
  constructor
  · intro hreal
    have hall : ∀ i, q i ≠ 0 := fun i hi => by
      obtain ⟨x, hx⟩ := hreal; have := hx i; rw [hi] at this; simp at this
    refine ⟨hall, ?_⟩
    by_cases hC' : (∏ i, q i).derivative = 0
    · exact Or.inr (Or.inl (fun i => realizable_const_signPos q hall hC' hreal i))
    · have hr2 := (lemma_2_75 hIVP s q hall hC' jp hσ).mp (hReeq.mp hreal)
      rw [hsf] at hr2
      rcases hr2 with h | h | h
      · exact Or.inl (fun i => (h i).symm)
      · exact Or.inr (Or.inl (fun i => (h i).symm))
      · exact Or.inr (Or.inr ⟨hC', h⟩)
  · rintro ⟨hall, h⟩
    rw [hReeq]
    rcases h with h | h | h
    · refine (lemma_2_75_reduction hIVP (signFn s jp) hσ q hall).mpr (Or.inl ?_)
      intro i; rw [hsf]; exact (h i).symm
    · refine (lemma_2_75_reduction hIVP (signFn s jp) hσ q hall).mpr (Or.inr (Or.inl ?_))
      intro i; rw [hsf]; exact (h i).symm
    · exact (lemma_2_75 hIVP s q hall h.1 jp hσ).mpr (Or.inr (Or.inr h.2))

end Realizable

/-! ### The realizability locus is semialgebraic over `D` -/

variable {k s : ℕ} {D : Type*} [CommRing D] [IsDomain D]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [Algebra D R] [IsRealClosed R]

/-- **The realizability locus is semialgebraic over `D`.** The set of `y` for which the
all-positive sign condition of the specialised family `𝒬_y` is realized over `R` is
semialgebraic over `D`. By `realizable_iff_disjuncts` it is the intersection of
`{∀ i, 𝒬_y i ≠ 0}` with the union of the two sign-at-`±∞` loci and the `matrixLocus`
for `C' = (∏ 𝒬)'` — each semialgebraic over `D`. -/
theorem realizabilityLocus_isSemialgebraicSetOver
    (𝒬 : Fin s → Polynomial (MvPolynomial (Fin k) D))
    (hinj : Function.Injective (algebraMap D R)) :
    IsSemialgebraicSetOver D
      {y : Fin k → R | ∃ x : R, ∀ i, 0 < ((𝒬 i).map (MvPolynomial.aeval y).toRingHom).eval x} := by
  have hCeq : ∀ (y : Fin k → R),
      (∏ i, (𝒬 i).map (MvPolynomial.aeval y).toRingHom).derivative
        = ((∏ i, 𝒬 i).derivative).map (MvPolynomial.aeval y).toRingHom := by
    intro y; rw [← Polynomial.map_prod, Polynomial.derivative_map]
  have hNeZero : IsSemialgebraicSetOver D
      (⋂ i ∈ (Finset.univ : Finset (Fin s)),
        {y : Fin k → R | (𝒬 i).map (MvPolynomial.aeval y).toRingHom ≠ 0}) :=
    IsSemialgebraicSetOver.finsetBiInter (Finset.univ : Finset (Fin s))
      (fun i => {y : Fin k → R | (𝒬 i).map (MvPolynomial.aeval y).toRingHom ≠ 0})
      (fun i _ => by
        have h := (degLocus_isSemialgebraicSetOver (R := R) (𝒬 i) (⊥ : WithBot ℕ)).compl
        convert h using 1; ext y; simp [Polynomial.degree_eq_bot])
  have hNeg := IsSemialgebraicSetOver.finsetBiInter (Finset.univ : Finset (Fin s))
    (fun i => {y : Fin k → R | signAtNegInfty ((𝒬 i).map (MvPolynomial.aeval y).toRingHom)
      = SignType.pos}) (fun i _ => signAtNegInfty_pos_locus (R := R) (𝒬 i))
  have hPos := IsSemialgebraicSetOver.finsetBiInter (Finset.univ : Finset (Fin s))
    (fun i => {y : Fin k → R | signAtPosInfty ((𝒬 i).map (MvPolynomial.aeval y).toRingHom)
      = SignType.pos}) (fun i _ => signAtPosInfty_pos_locus (R := R) (𝒬 i))
  have hMat := matrixLocus_isSemialgebraicSetOver (R := R) (∏ i, 𝒬 i).derivative 𝒬
    ((signMatrixQ s)⁻¹) ((signEquiv s).symm (fun _ => SignType.pos)) hinj
  have hset : {y : Fin k → R | ∃ x : R, ∀ i,
        0 < ((𝒬 i).map (MvPolynomial.aeval y).toRingHom).eval x} =
      (⋂ i ∈ (Finset.univ : Finset (Fin s)),
          {y : Fin k → R | (𝒬 i).map (MvPolynomial.aeval y).toRingHom ≠ 0}) ∩
        ((⋂ i ∈ (Finset.univ : Finset (Fin s)),
            {y : Fin k → R | signAtNegInfty ((𝒬 i).map (MvPolynomial.aeval y).toRingHom)
              = SignType.pos}) ∪
         (⋂ i ∈ (Finset.univ : Finset (Fin s)),
            {y : Fin k → R | signAtPosInfty ((𝒬 i).map (MvPolynomial.aeval y).toRingHom)
              = SignType.pos}) ∪
         {y : Fin k → R | ((∏ i, 𝒬 i).derivative).map (MvPolynomial.aeval y).toRingHom ≠ 0 ∧
            0 < ((signMatrixQ s)⁻¹ *ᵥ
                (fun i => (tarskiQuery
                  (familyPow (fun j => (𝒬 j).map (MvPolynomial.aeval y).toRingHom) (expFn s i))
                  (((∏ i, 𝒬 i).derivative).map (MvPolynomial.aeval y).toRingHom) : ℚ)))
              ((signEquiv s).symm (fun _ => SignType.pos))}) := by
    ext y
    rw [Set.mem_setOf_eq, realizable_iff_disjuncts hasIVP_of_isRealClosed
      (fun i => (𝒬 i).map (MvPolynomial.aeval y).toRingHom), hCeq y]
    simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_iInter, Set.mem_setOf_eq,
      Finset.mem_univ, forall_true_left]
    tauto
  rw [hset]
  exact hNeZero.inter ((hNeg.union hPos).union hMat)

/-! ### Stratum B and the proof of Theorem 2.76 -/

/-- Rewrite a `Finset`-membership universal as a `Fin`-indexed one over the `toList`
enumeration (a local copy of `BasicCellProjection`'s private helper). -/
private theorem forall_mem_iff_forall_get {α : Type*} (Q : Finset α) (Φ : α → Prop) :
    (∀ q ∈ Q, Φ q) ↔ ∀ i : Fin Q.toList.length, Φ (Q.toList.get i) := by
  constructor
  · intro h i; exact h _ (Finset.mem_toList.mp (Q.toList.get_mem i))
  · intro h q hq
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp (Finset.mem_toList.mpr hq)
    exact h i

/-- **Stratum B is semialgebraic over `D`.** The `P_y ≡ 0` stratum of the basic-cell
projection — `{y | P_y ≡ 0 ∧ ∃ x, ⋀_{q ∈ 𝒬} q_y(x) > 0}` — is semialgebraic over `D`:
it is the intersection of the degree locus `{P_y ≡ 0}` with the realizability locus of
the family `(splitLast q)_{q ∈ 𝒬}`. -/
theorem stratumB_isSemialgebraicSetOver
    (hinj : Function.Injective (algebraMap D R))
    (P : MvPolynomial (Fin (k + 1)) D) (Q : Finset (MvPolynomial (Fin (k + 1)) D)) :
    IsSemialgebraicSetOver D
      {y : Fin k → R | (splitLast P).map (MvPolynomial.aeval y).toRingHom = 0 ∧
        ∃ x, ∀ q ∈ Q, 0 < ((splitLast q).map (MvPolynomial.aeval y).toRingHom).eval x} := by
  classical
  have hset : {y : Fin k → R | (splitLast P).map (MvPolynomial.aeval y).toRingHom = 0 ∧
        ∃ x, ∀ q ∈ Q, 0 < ((splitLast q).map (MvPolynomial.aeval y).toRingHom).eval x} =
      {y : Fin k → R | (splitLast P).map (MvPolynomial.aeval y).toRingHom = 0} ∩
      {y : Fin k → R | ∃ x : R, ∀ i : Fin Q.toList.length,
        0 < ((splitLast (Q.toList.get i)).map (MvPolynomial.aeval y).toRingHom).eval x} := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    refine and_congr_right (fun _ => exists_congr (fun x => ?_))
    exact forall_mem_iff_forall_get Q
      (fun q => 0 < ((splitLast q).map (MvPolynomial.aeval y).toRingHom).eval x)
  rw [hset]
  refine IsSemialgebraicSetOver.inter ?_
    (realizabilityLocus_isSemialgebraicSetOver (fun i => splitLast (Q.toList.get i)) hinj)
  have h := degLocus_isSemialgebraicSetOver (R := R) (splitLast P) (⊥ : WithBot ℕ)
  convert h using 1; ext y; simp [Polynomial.degree_eq_bot]

/-- **BPR Theorem 2.76.** The projection (drop the last coordinate, `Fin.init`) of a
semialgebraic subset of `Rᵏ⁺¹` defined over `D` is a semialgebraic subset of `Rᵏ`
defined over `D`.

The disjunctive normal form reduces this to the projection of a single basic cell
(`theorem_2_76_of_basicCellProjection`); the basic-cell projection is the union of
Stratum A (`P_y ≢ 0`, Lemma 2.74) and Stratum B (`P_y ≡ 0`, Lemma 2.75), both
semialgebraic over `D` (`basicCellProjection_of_strata`). -/
theorem theorem_2_76 (hinj : Function.Injective (algebraMap D R))
    {S : Set (Fin (k + 1) → R)} (hS : IsSemialgebraicSetOver D S) :
    IsSemialgebraicSetOver D (Fin.init '' S) :=
  theorem_2_76_of_basicCellProjection
    (fun P Q => basicCellProjection_of_strata P Q
      (stratumA_isSemialgebraicSetOver hinj P Q) (stratumB_isSemialgebraicSetOver hinj P Q)) hS

end Azurite.BPR
