/-
  Equivalence between the computable `azDegFormula` / `azDegEqFormula`
  and BPR's noncomputable `degFormula` / `degEqFormula`.

  The main theorems show that the `azRealization` of the computable
  formula equals the `realization` of the corresponding BPR formula
  under the `liftPoly` bridge.
-/
import Azurite.AzFormula.DegFormula
import Azurite.AzFormula.Equiv.Basic
import Azurite.AzPolynomial.Equiv.Tru
import Azurite.BasuPollackRoy.Chapter1.Section1_3.DegFormula

namespace Azurite

open AzMvPolynomial BPR Polynomial

variable {k : ℕ} {D : Type*} [CommRing D] [IsDomain D] [DecidableEq D]
         {ord : MonomialOrder}

/-! ### Bridge lemma: liftPoly coefficient -/

@[simp] theorem liftPoly_coeff
    (Q : AzPolynomial (AzMvPolynomial k D ord)) (i : ℕ) :
    (liftPoly Q).coeff i = (Q.coeff i).toMvPoly := by
  unfold liftPoly
  simp [Polynomial.coeff_map, coeff_toPoly_eq, AzMvPolynomial.toMvPolyHom]

/-! ### Atom conversion lemmas -/

omit [IsDomain D] [DecidableEq D] in
@[simp] theorem azFormulaToFieldFormula_azEqZero
    (p : AzMvPolynomial k D ord) :
    azFormulaToFieldFormula (azEqZero p) =
      Formula.eq_zero (p.toMvPoly) := by
  simp [azFormulaToFieldFormula, azEqZero, AzFieldAtom.eqZero,
    Formula.mapAtom, AzFieldAtom.toFieldAtom, Formula.eq_zero,
    FieldAtom.eqZero]

omit [IsDomain D] [DecidableEq D] in
@[simp] theorem azFormulaToFieldFormula_azNeZero
    (p : AzMvPolynomial k D ord) :
    azFormulaToFieldFormula (azNeZero p) =
      Formula.ne_zero (p.toMvPoly) := by
  simp [azFormulaToFieldFormula, azNeZero, AzFieldAtom.neZero,
    Formula.mapAtom, AzFieldAtom.toFieldAtom, Formula.ne_zero,
    FieldAtom.neZero]

/-! ### Realization of list combinators -/

variable {C : Type*} [Field C] [Algebra D C]

omit [IsDomain D] [DecidableEq D] in
@[simp] theorem azRealization_azTrueFormula :
    azRealization (azTrueFormula (n := k) (R := D) (ord := ord)) (C := C) =
      Set.univ := by
  show (azFormulaToFieldFormula (azEqZero (0 : AzMvPolynomial k D ord))).realization = _
  rw [azFormulaToFieldFormula_azEqZero, toMvPoly_zero]
  simp [Formula.realization_eq_zero]

omit [IsDomain D] [DecidableEq D] in
@[simp] theorem azRealization_azFalseFormula :
    azRealization (azFalseFormula (n := k) (R := D) (ord := ord)) (C := C) =
      ∅ := by
  show (azFormulaToFieldFormula (azNeZero (0 : AzMvPolynomial k D ord))).realization = _
  rw [azFormulaToFieldFormula_azNeZero, toMvPoly_zero]
  simp [Formula.realization_ne_zero]

omit [IsDomain D] [DecidableEq D] in
@[simp] theorem azRealization_and
    (Φ₁ Φ₂ : Formula (Fin k) (AzFieldAtom k D ord)) :
    azRealization (Φ₁.and Φ₂) (C := C) =
      azRealization Φ₁ ∩ azRealization Φ₂ := by
  simp [azRealization, azFormulaToFieldFormula, Formula.mapAtom]

omit [IsDomain D] [DecidableEq D] in
@[simp] theorem azRealization_or
    (Φ₁ Φ₂ : Formula (Fin k) (AzFieldAtom k D ord)) :
    azRealization (Φ₁.or Φ₂) (C := C) =
      azRealization Φ₁ ∪ azRealization Φ₂ := by
  simp [azRealization, azFormulaToFieldFormula, Formula.mapAtom]

omit [IsDomain D] [DecidableEq D] in
@[simp] theorem azRealization_azEqZero
    (p : AzMvPolynomial k D ord) :
    azRealization (azEqZero p) (C := C) =
      { y | MvPolynomial.aeval y p.toMvPoly = 0 } := by
  simp [azRealization, Formula.realization_eq_zero]

omit [IsDomain D] [DecidableEq D] in
@[simp] theorem azRealization_azNeZero
    (p : AzMvPolynomial k D ord) :
    azRealization (azNeZero p) (C := C) =
      { y | MvPolynomial.aeval y p.toMvPoly ≠ 0 } := by
  simp [azRealization, Formula.realization_ne_zero]

/-! ### Trivial atom realization -/

omit [IsDomain D] in
theorem isAzTrue_azRealization [FaithfulSMul D C]
    (Φ : Formula (Fin k) (AzFieldAtom k D ord))
    (h : isAzTrue Φ = true) : azRealization Φ (C := C) = Set.univ := by
  match Φ with
  | .atom ⟨P, true⟩ =>
    have h' : P == 0 := by simpa [isAzTrue] using h
    have : P = 0 := by simpa using h'
    subst this
    exact azRealization_azTrueFormula
  | .atom ⟨P, false⟩ =>
    have h' : P.isConstant && !(P == 0) := by simpa [isAzTrue] using h
    rw [Bool.and_eq_true] at h'
    obtain ⟨hconst, hne⟩ := h'
    rw [Bool.not_eq_true', beq_eq_false_iff_ne] at hne
    obtain ⟨c, hc⟩ := (AzMvPolynomial.isConstant_iff P).mp hconst
    have hc_ne : c ≠ 0 := fun hc0 => hne (toMvPoly_injective
      (by rw [hc, hc0, toMvPoly_zero, MvPolynomial.C_0]))
    have hmap : algebraMap D C c ≠ 0 := fun habs =>
      hc_ne (FaithfulSMul.algebraMap_injective D C (by rw [habs, map_zero]))
    show azRealization (azNeZero P) (C := C) = Set.univ
    rw [azRealization_azNeZero]
    ext y; simp [hc, hmap]
  | .not _ | .and _ _ | .or _ _ | .implies _ _
  | .exists_ _ _ | .forall_ _ _ => simp [isAzTrue] at h

omit [IsDomain D] in
theorem isAzFalse_azRealization [FaithfulSMul D C]
    (Φ : Formula (Fin k) (AzFieldAtom k D ord))
    (h : isAzFalse Φ = true) : azRealization Φ (C := C) = ∅ := by
  match Φ with
  | .atom ⟨P, false⟩ =>
    have h' : P == 0 := by simpa [isAzFalse] using h
    have : P = 0 := by simpa using h'
    subst this
    exact azRealization_azFalseFormula
  | .atom ⟨P, true⟩ =>
    have h' : P.isConstant && !(P == 0) := by simpa [isAzFalse] using h
    rw [Bool.and_eq_true] at h'
    obtain ⟨hconst, hne⟩ := h'
    rw [Bool.not_eq_true', beq_eq_false_iff_ne] at hne
    obtain ⟨c, hc⟩ := (AzMvPolynomial.isConstant_iff P).mp hconst
    have hc_ne : c ≠ 0 := fun hc0 => hne (toMvPoly_injective
      (by rw [hc, hc0, toMvPoly_zero, MvPolynomial.C_0]))
    have hmap : algebraMap D C c ≠ 0 := fun habs =>
      hc_ne (FaithfulSMul.algebraMap_injective D C (by rw [habs, map_zero]))
    show azRealization (azEqZero P) (C := C) = ∅
    rw [azRealization_azEqZero]
    ext y; simp [hc, hmap]
  | .not _ | .and _ _ | .or _ _ | .implies _ _
  | .exists_ _ _ | .forall_ _ _ => simp [isAzFalse] at h

/-! ### Smart constructor realization -/

omit [IsDomain D] in
@[simp] theorem azRealization_azSmartAnd [FaithfulSMul D C]
    (Φ₁ Φ₂ : Formula (Fin k) (AzFieldAtom k D ord)) :
    azRealization (azSmartAnd Φ₁ Φ₂) (C := C) =
      azRealization Φ₁ ∩ azRealization Φ₂ := by
  simp only [azSmartAnd]
  split
  next h =>
    rw [isAzTrue_azRealization (C := C) _ h, Set.univ_inter]
  next _ =>
    split
    next h =>
      rw [isAzTrue_azRealization (C := C) _ h, Set.inter_univ]
    next _ =>
      split
      next h =>
        simp only [Bool.or_eq_true] at h
        rw [azRealization_azFalseFormula]
        rcases h with h | h
        · rw [isAzFalse_azRealization _ h, Set.empty_inter]
        · rw [isAzFalse_azRealization _ h, Set.inter_empty]
      next _ =>
        exact azRealization_and _ _

omit [IsDomain D] in
@[simp] theorem azRealization_azSmartOr [FaithfulSMul D C]
    (Φ₁ Φ₂ : Formula (Fin k) (AzFieldAtom k D ord)) :
    azRealization (azSmartOr Φ₁ Φ₂) (C := C) =
      azRealization Φ₁ ∪ azRealization Φ₂ := by
  simp only [azSmartOr]
  split
  next h =>
    rw [isAzFalse_azRealization (C := C) _ h, Set.empty_union]
  next _ =>
    split
    next h =>
      rw [isAzFalse_azRealization (C := C) _ h, Set.union_empty]
    next _ =>
      split
      next h =>
        simp only [Bool.or_eq_true] at h
        rw [azRealization_azTrueFormula]
        rcases h with h | h
        · rw [isAzTrue_azRealization _ h, Set.univ_union]
        · rw [isAzTrue_azRealization _ h, Set.union_univ]
      next _ =>
        exact azRealization_or _ _

omit [IsDomain D] in
@[simp] theorem azRealization_azConjList [FaithfulSMul D C]
    (Φs : List (Formula (Fin k) (AzFieldAtom k D ord))) :
    azRealization (azConjList Φs) (C := C) =
      { y | ∀ Φ ∈ Φs, y ∈ azRealization Φ } := by
  induction Φs with
  | nil => simp [azConjList]
  | cons Φ Φs ih =>
    cases Φs with
    | nil => simp [azConjList]
    | cons Φ' Φs' =>
      simp only [azConjList, azRealization_azSmartAnd, ih]
      ext y; simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, List.forall_mem_cons]

omit [IsDomain D] in
@[simp] theorem azRealization_azDisjList [FaithfulSMul D C]
    (Φs : List (Formula (Fin k) (AzFieldAtom k D ord))) :
    azRealization (azDisjList Φs) (C := C) =
      { y | ∃ Φ ∈ Φs, y ∈ azRealization Φ } := by
  induction Φs with
  | nil => simp [azDisjList]
  | cons Φ Φs ih =>
    cases Φs with
    | nil => simp [azDisjList]
    | cons Φ' Φs' =>
      simp only [azDisjList, azRealization_azSmartOr, ih]
      ext y; simp [Set.mem_union, List.mem_cons, exists_eq_or_imp]

/-! ### Main equivalence theorems -/

/-- The computable `azDegFormula` has the same realization as BPR's
noncomputable `degFormula` under the `liftPoly` bridge. -/
theorem azRealization_azDegFormula [FaithfulSMul D C]
    (Q : AzPolynomial (AzMvPolynomial k D ord)) (i : WithBot ℕ) :
    azRealization (azDegFormula Q i) (C := C) =
      (BPR.degFormula (liftPoly Q) i).realization := by
  -- Unfold both definitions and show both sides reduce to the same set
  simp only [azDegFormula, BPR.degFormula]
  match i with
  | ⊥ =>
    ext y
    simp only [azRealization_azConjList, azRealization_azEqZero,
      Formula.realization_conjList, Formula.realization_eq_zero,
      Set.mem_ofPred_eq, List.mem_map, List.mem_range,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      liftPoly_coeff, liftPoly_natDegree]
  | some n =>
    ext y
    simp only [azRealization_azSmartAnd, azRealization_azNeZero,
      azRealization_azConjList, azRealization_azEqZero,
      Formula.realization_and, Formula.realization_ne_zero,
      Formula.realization_conjList, Formula.realization_eq_zero,
      Set.mem_inter_iff, Set.mem_ofPred_eq,
      List.mem_map, List.mem_range,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      liftPoly_coeff, liftPoly_natDegree]

/-- The computable `azDegEqFormula` has the same realization as BPR's
noncomputable `degEqFormula` under the `liftPoly` bridge. -/
theorem azRealization_azDegEqFormula [FaithfulSMul D C]
    (Q₁ Q₂ : AzPolynomial (AzMvPolynomial k D ord)) :
    azRealization (azDegEqFormula Q₁ Q₂) (C := C) =
      (BPR.degEqFormula (liftPoly Q₁) (liftPoly Q₂)).realization := by
  -- Key: each disjunct's realization matches across the two sides
  have key : ∀ (i : WithBot ℕ) (y : Fin k → C),
      y ∈ azRealization (C := C) (azSmartAnd (azDegFormula Q₁ i) (azDegFormula Q₂ i)) ↔
      y ∈ ((BPR.degFormula (liftPoly Q₁) i).and
           (BPR.degFormula (liftPoly Q₂) i)).realization (C := C) := by
    intro i y
    simp only [azRealization_azSmartAnd, Set.mem_inter_iff,
      azRealization_azDegFormula, Formula.realization_and]
  simp only [azDegEqFormula, BPR.degEqFormula, liftPoly_natDegree]
  ext y
  simp only [azRealization_azDisjList, Formula.realization_disjList,
    Set.mem_ofPred_eq, List.mem_cons, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨_, rfl | ⟨i, hi, rfl⟩, hmem⟩
    · exact ⟨_, Or.inl rfl, (key _ y).mp hmem⟩
    · exact ⟨_, Or.inr ⟨i, hi, rfl⟩, (key _ y).mp hmem⟩
  · rintro ⟨_, rfl | ⟨i, hi, rfl⟩, hmem⟩
    · exact ⟨_, Or.inl rfl, (key _ y).mpr hmem⟩
    · exact ⟨_, Or.inr ⟨i, hi, rfl⟩, (key _ y).mpr hmem⟩

end Azurite
