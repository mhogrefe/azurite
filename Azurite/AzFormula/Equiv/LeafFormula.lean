/-
  Equivalence between the computable `azLeafFormula` / `azLeafFormulaAux`
  and BPR's noncomputable `leafFormula` / `leafFormulaAux`.

  The main theorem shows that `azRealization` of the computable formula
  equals `realization` of the BPR formula under the `liftPoly` bridge.
-/
import Azurite.AzFormula.LeafFormula
import Azurite.AzFormula.Equiv.DegFormula
import Azurite.AzPolynomial.Equiv.TRems

namespace Azurite

open AzMvPolynomial BPR Polynomial

variable {k : ℕ} {D : Type*} [CommRing D] [IsDomain D] [DecidableEq D]
         {ord : MonomialOrder}
         {C : Type*} [Field C] [Algebra D C]

/-- The computable `azLeafFormulaAux` has the same realization as BPR's
noncomputable `leafFormulaAux` under the `liftPoly` bridge. -/
theorem azRealization_azLeafFormulaAux
    (parent cur : AzPolynomial (AzMvPolynomial k D ord))
    (rest : List (AzPolynomial (AzMvPolynomial k D ord)))
    (hcur : cur ≠ 0) :
    azRealization (azLeafFormulaAux parent cur rest) (C := C) =
      (BPR.leafFormulaAux (liftPoly parent) (liftPoly cur)
        (rest.map liftPoly)).realization := by
  induction rest generalizing parent cur with
  | nil =>
    simp only [azLeafFormulaAux, BPR.leafFormulaAux, List.map]
    rw [azRealization_azDegFormula, liftPoly_neg, liftPoly_pRem_eq_pRemMv _ _ hcur]
  | cons next rest' ih =>
    simp only [azLeafFormulaAux, List.map]
    by_cases h0 : next = 0
    · -- next = 0: both sides reduce to degFormula(-(pRem parent cur), ⊥)
      subst h0
      simp only [beq_self_eq_true, ↓reduceIte, BPR.leafFormulaAux, liftPoly_zero]
      rw [azRealization_azDegFormula, liftPoly_neg, liftPoly_pRem_eq_pRemMv _ _ hcur]
    · -- next ≠ 0: conjoin degree formula with recursive call
      have hbeq : ¬(next == 0) = true := by rwa [beq_iff_eq]
      rw [if_neg hbeq]
      have hlift_ne : liftPoly next ≠ 0 := (liftPoly_eq_zero_iff _).not.mpr h0
      simp only [BPR.leafFormulaAux, hlift_ne, ↓reduceIte]
      rw [azRealization_azSmartAnd, azRealization_azDegFormula,
          ih cur next h0, liftPoly_natDegree, Formula.realization_and,
          liftPoly_neg, liftPoly_pRem_eq_pRemMv _ _ hcur]

/-- The computable `azLeafFormula` has the same realization as BPR's
noncomputable `leafFormula` under the `liftPoly` bridge. -/
theorem azRealization_azLeafFormula
    (P Q : AzPolynomial (AzMvPolynomial k D ord))
    (path : List (AzPolynomial (AzMvPolynomial k D ord))) :
    azRealization (azLeafFormula P Q path) (C := C) =
      (BPR.leafFormula (liftPoly P) (liftPoly Q)
        (path.map liftPoly)).realization := by
  match path with
  | [] =>
    simp only [azLeafFormula, BPR.leafFormula, List.map]
    exact azRealization_azDegFormula Q ⊥
  | q :: rest =>
    simp only [azLeafFormula, List.map]
    by_cases h0 : q = 0
    · subst h0
      simp only [beq_self_eq_true, ↓reduceIte, BPR.leafFormula, liftPoly_zero]
      exact azRealization_azDegFormula Q ⊥
    · have hbeq : ¬(q == 0) = true := by rwa [beq_iff_eq]
      rw [if_neg hbeq]
      have hlift_ne : liftPoly q ≠ 0 := (liftPoly_eq_zero_iff _).not.mpr h0
      simp only [BPR.leafFormula, hlift_ne, ↓reduceIte]
      rw [azRealization_azSmartAnd, azRealization_azDegFormula,
          azRealization_azLeafFormulaAux P q rest h0, liftPoly_natDegree,
          Formula.realization_and]

end Azurite
