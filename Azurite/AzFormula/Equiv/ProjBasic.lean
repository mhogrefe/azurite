/-
  Correctness proofs for `azProjBasic`, `azProjectQF`, `azProjectQFAt`.

  This file establishes two structural properties of the computable
  projection:

  * **Quantifier-free preservation** — the output of `azProjectQF` and
    `azProjectQFAt` is itself quantifier-free.
  * **Variable absence** — the projected variable does not appear (via
    its natural embedding into the input variable space) in the output's
    free variables. This is ultimately a type-level guarantee because
    the output has type `Formula (Fin k)` while the input has type
    `Formula (Fin (k+1))`, and the embedding skips the projected position.
-/
import Azurite.AzFormula.ProjBasic
import Azurite.AzFormula.Equiv.Posgcd
import Azurite.AzFormula.Equiv.ElimTrivialAtoms
import Azurite.AzFormula.Equiv.Prenex
import Azurite.AzMvPolynomial.Equiv.FinSuccEquiv
import Azurite.BasuPollackRoy.Chapter1.Section1_3.Theorem1_22

namespace Azurite

open AzMvPolynomial BPR

variable {k : ℕ} {D : Type*} [CommRing D] [IsDomain D] [DecidableEq D]
         {ord : MonomialOrder}

/-! ### QF preservation for smart constructors and list combinators -/

omit [IsDomain D] in
theorem azSmartAnd_isQF {n : ℕ}
    (Φ₁ Φ₂ : Formula (Fin n) (AzFieldAtom n D ord))
    (h₁ : Φ₁.IsQuantifierFree) (h₂ : Φ₂.IsQuantifierFree) :
    (azSmartAnd Φ₁ Φ₂).IsQuantifierFree := by
  unfold azSmartAnd
  split_ifs
  · exact h₂
  · exact h₁
  · trivial
  · exact ⟨h₁, h₂⟩

omit [IsDomain D] in
theorem azSmartOr_isQF {n : ℕ}
    (Φ₁ Φ₂ : Formula (Fin n) (AzFieldAtom n D ord))
    (h₁ : Φ₁.IsQuantifierFree) (h₂ : Φ₂.IsQuantifierFree) :
    (azSmartOr Φ₁ Φ₂).IsQuantifierFree := by
  unfold azSmartOr
  split_ifs
  · exact h₂
  · exact h₁
  · trivial
  · exact ⟨h₁, h₂⟩

omit [IsDomain D] in
theorem azConjList_isQF
    (Φs : List (Formula (Fin k) (AzFieldAtom k D ord)))
    (h : ∀ Φ ∈ Φs, Φ.IsQuantifierFree) :
    (azConjList Φs).IsQuantifierFree := by
  induction Φs with
  | nil => trivial
  | cons Φ rest ih =>
    cases rest with
    | nil => exact h Φ List.mem_cons_self
    | cons Φ' rest' =>
      refine azSmartAnd_isQF _ _ (h Φ List.mem_cons_self) ?_
      exact ih (fun φ hφ => h φ (List.mem_cons_of_mem _ hφ))

omit [IsDomain D] in
theorem azDisjList_isQF
    (Φs : List (Formula (Fin k) (AzFieldAtom k D ord)))
    (h : ∀ Φ ∈ Φs, Φ.IsQuantifierFree) :
    (azDisjList Φs).IsQuantifierFree := by
  induction Φs with
  | nil => trivial
  | cons Φ rest ih =>
    cases rest with
    | nil => exact h Φ List.mem_cons_self
    | cons Φ' rest' =>
      refine azSmartOr_isQF _ _ (h Φ List.mem_cons_self) ?_
      exact ih (fun φ hφ => h φ (List.mem_cons_of_mem _ hφ))

/-! ### QF preservation for degree / leaf / posgcd / projection formulas -/

theorem azDegFormula_isQF
    (Q : AzPolynomial (AzMvPolynomial k D ord)) (i : WithBot ℕ) :
    (azDegFormula Q i).IsQuantifierFree := by
  cases i with
  | bot =>
    apply azConjList_isQF
    intro Φ hΦ
    simp only [List.mem_map] at hΦ
    obtain ⟨j, _, rfl⟩ := hΦ
    trivial
  | coe n =>
    refine azSmartAnd_isQF _ _ trivial ?_
    apply azConjList_isQF
    intro Φ hΦ
    simp only [List.mem_map] at hΦ
    obtain ⟨j, _, rfl⟩ := hΦ
    trivial

theorem azDegEqFormula_isQF
    (Q₁ Q₂ : AzPolynomial (AzMvPolynomial k D ord)) :
    (azDegEqFormula Q₁ Q₂).IsQuantifierFree := by
  apply azDisjList_isQF
  intro Φ hΦ
  simp only [List.mem_cons, List.mem_map] at hΦ
  rcases hΦ with rfl | ⟨i, _, rfl⟩
  · exact azSmartAnd_isQF _ _ (azDegFormula_isQF _ _) (azDegFormula_isQF _ _)
  · exact azSmartAnd_isQF _ _ (azDegFormula_isQF _ _) (azDegFormula_isQF _ _)

theorem azDegNeqFormula_isQF
    (Q₁ Q₂ : AzPolynomial (AzMvPolynomial k D ord)) :
    (azDegNeqFormula Q₁ Q₂).IsQuantifierFree :=
  azDegEqFormula_isQF Q₁ Q₂

theorem azLeafFormulaAux_isQF
    (parent cur : AzPolynomial (AzMvPolynomial k D ord))
    (rest : List (AzPolynomial (AzMvPolynomial k D ord))) :
    (azLeafFormulaAux parent cur rest).IsQuantifierFree := by
  induction rest generalizing parent cur with
  | nil => exact azDegFormula_isQF _ _
  | cons q rest ih =>
    simp only [azLeafFormulaAux]
    split_ifs
    · exact azDegFormula_isQF _ _
    · exact azSmartAnd_isQF _ _ (azDegFormula_isQF _ _) (ih _ _)

theorem azLeafFormula_isQF
    (P Q : AzPolynomial (AzMvPolynomial k D ord))
    (path : List (AzPolynomial (AzMvPolynomial k D ord))) :
    (azLeafFormula P Q path).IsQuantifierFree := by
  cases path with
  | nil =>
    simp only [azLeafFormula]
    exact azDegFormula_isQF _ _
  | cons q rest =>
    simp only [azLeafFormula]
    split_ifs
    · exact azDegFormula_isQF _ _
    · exact azSmartAnd_isQF _ _ (azDegFormula_isQF _ _) (azLeafFormulaAux_isQF _ _ _)

/-- Every formula appearing as the second component of an element of
`azPosgcd Ps` is quantifier-free. -/
theorem azPosgcd_snd_isQF
    (Ps : List (AzPolynomial (AzMvPolynomial k D ord)))
    {G : AzPolynomial (AzMvPolynomial k D ord)}
    {𝒞 : Formula (Fin k) (AzFieldAtom k D ord)}
    (hmem : (G, 𝒞) ∈ azPosgcd Ps) : 𝒞.IsQuantifierFree := by
  induction Ps generalizing G 𝒞 with
  | nil =>
    simp only [azPosgcd, List.mem_singleton, Prod.mk.injEq] at hmem
    obtain ⟨_, rfl⟩ := hmem
    trivial
  | cons P rest ih =>
    simp only [azPosgcd, List.mem_flatMap, List.mem_map, Prod.mk.injEq] at hmem
    obtain ⟨⟨Q, C_q⟩, hQC_mem, path, _, _, hC_eq⟩ := hmem
    subst hC_eq
    exact azSmartAnd_isQF _ _ (ih hQC_mem) (azLeafFormula_isQF _ _ _)

/-- `azProjBasic Ps Qs` is quantifier-free. -/
theorem azProjBasic_isQF
    (Ps Qs : List (AzMvPolynomial (k+1) D ord)) :
    (azProjBasic Ps Qs).IsQuantifierFree := by
  apply azDisjList_isQF
  intro Φ hΦ
  simp only [List.mem_flatMap, List.mem_map, Prod.exists] at hΦ
  obtain ⟨G, 𝒞, hmem, path, _, rfl⟩ := hΦ
  refine azSmartAnd_isQF _ _ (azPosgcd_snd_isQF _ hmem) ?_
  exact azSmartAnd_isQF _ _ (azLeafFormula_isQF _ _ _) (azDegNeqFormula_isQF _ _)

/-! ### QF preservation for simplification -/

omit [IsDomain D] in
private theorem azSimplifyNot_isQF {n : ℕ}
    (Φ' : Formula (Fin n) (AzFieldAtom n D ord))
    (h : Φ'.IsQuantifierFree) :
    (azSimplifyNot Φ').IsQuantifierFree := by
  unfold azSimplifyNot
  match Φ' with
  | .not Ψ => exact h
  | .atom _ =>
    split_ifs <;> trivial
  | .and _ _ | .or _ _ | .implies _ _ =>
    split_ifs
    · trivial
    · trivial
    · exact h
  | .exists_ _ _ | .forall_ _ _ => exact h.elim

omit [IsDomain D] in
/-- `azSimplify` preserves quantifier-freeness. -/
theorem azSimplify_isQF {n : ℕ}
    (Φ : Formula (Fin n) (AzFieldAtom n D ord))
    (h : Φ.IsQuantifierFree) :
    (azSimplify Φ).IsQuantifierFree := by
  induction Φ with
  | atom _ => trivial
  | not Ψ ih =>
    simp only [azSimplify]
    exact azSimplifyNot_isQF _ (ih h)
  | and Φ₁ Φ₂ ih₁ ih₂ =>
    simp only [azSimplify]
    split_ifs
    · exact ih₂ h.2
    · exact ih₁ h.1
    · trivial
    · exact ⟨ih₁ h.1, ih₂ h.2⟩
  | or Φ₁ Φ₂ ih₁ ih₂ =>
    simp only [azSimplify]
    split_ifs
    · exact ih₂ h.2
    · exact ih₁ h.1
    · trivial
    · exact ⟨ih₁ h.1, ih₂ h.2⟩
  | implies Φ₁ Φ₂ ih₁ ih₂ =>
    simp only [azSimplify]
    split_ifs
    · exact ih₂ h.2
    · trivial
    · exact ⟨ih₁ h.1, ih₂ h.2⟩
  | exists_ _ _ _ => exact h.elim
  | forall_ _ _ _ => exact h.elim

/-! ### Main QF theorems -/

/-- `azProjectQF` produces a quantifier-free formula. -/
theorem azProjectQF_isQF
    (Φ : Formula (Fin (k+1)) (AzFieldAtom (k+1) D ord))
    (hqf : Φ.IsQuantifierFree) :
    (azProjectQF Φ hqf).IsQuantifierFree := by
  unfold azProjectQF
  apply azSimplify_isQF
  apply toNNF_isQF
  apply azDisjList_isQF
  intro Ψ hΨ
  simp only [List.mem_map, Prod.exists] at hΨ
  obtain ⟨Ps, Qs, _, rfl⟩ := hΨ
  exact azProjBasic_isQF _ _

/-- `azProjectQFAt` produces a quantifier-free formula. -/
theorem azProjectQFAt_isQF
    (i : Fin (k+1))
    (Φ : Formula (Fin (k+1)) (AzFieldAtom (k+1) D ord))
    (hqf : Φ.IsQuantifierFree) :
    (azProjectQFAt i Φ hqf).IsQuantifierFree := by
  unfold azProjectQFAt
  exact azProjectQF_isQF _ _

/-! ### Variable absence

Because `azProjectQF` has output type `Formula (Fin k)`, the projected
variable (position `0` of the input `Fin (k+1)` space) cannot appear
among the output's free variables: embedding `Finset (Fin k)` into
`Finset (Fin (k+1))` via `Fin.succ` never produces `0`.

`azProjectQFAt i` generalizes this: embedding via `Fin.succAbove i`
never produces `i`. -/

/-- The projected variable `0 : Fin (k+1)` does not appear in the free
variables of `azProjectQF Φ hqf` when embedded back into the input
variable space via `Fin.succ`. -/
theorem azProjectQF_zero_not_mem_freeVars_image
    (Φ : Formula (Fin (k+1)) (AzFieldAtom (k+1) D ord))
    (hqf : Φ.IsQuantifierFree) :
    (0 : Fin (k+1)) ∉ (freeVarsOf (azProjectQF Φ hqf)).image Fin.succ := by
  intro hmem
  simp only [Finset.mem_image] at hmem
  obtain ⟨j, _, hj⟩ := hmem
  exact Fin.succ_ne_zero j hj

/-- The projected variable `i : Fin (k+1)` does not appear in the free
variables of `azProjectQFAt i Φ hqf` when embedded back into the input
variable space via `Fin.succAbove i` (which skips `i`). -/
theorem azProjectQFAt_projected_not_mem_freeVars_image
    (i : Fin (k+1))
    (Φ : Formula (Fin (k+1)) (AzFieldAtom (k+1) D ord))
    (hqf : Φ.IsQuantifierFree) :
    i ∉ (freeVarsOf (azProjectQFAt i Φ hqf)).image (Fin.succAbove i) := by
  intro hmem
  simp only [Finset.mem_image] at hmem
  obtain ⟨j, _, hj⟩ := hmem
  exact Fin.succAbove_ne i j hj

/-! ### Bridge lemmas for `liftPoly` and `finSuccEquiv` -/

variable {C : Type*} [Field C] [Algebra D C]

/-- `liftPoly` is multiplicative. -/
theorem liftPoly_mul (p q : AzPolynomial (AzMvPolynomial k D ord)) :
    liftPoly (p * q) = liftPoly p * liftPoly q := by
  unfold liftPoly
  rw [AzPolynomial.toPoly_mul, Polynomial.map_mul]

/-- `liftPoly 1 = 1`. -/
theorem liftPoly_one : liftPoly (1 : AzPolynomial (AzMvPolynomial k D ord)) = 1 := by
  unfold liftPoly
  rw [toPoly_one, Polynomial.map_one]

/-- `liftPoly` of a list-prod is the prod of `liftPoly` images. -/
theorem liftPoly_list_prod
    (l : List (AzPolynomial (AzMvPolynomial k D ord))) :
    liftPoly l.prod = (l.map liftPoly).prod := by
  induction l with
  | nil => simp [liftPoly_one]
  | cons p rest ih =>
    simp only [List.prod_cons, List.map_cons, liftPoly_mul, ih]

/-- `liftPoly` of a power is the power of the `liftPoly` image. -/
theorem liftPoly_pow
    (p : AzPolynomial (AzMvPolynomial k D ord)) (n : ℕ) :
    liftPoly (p ^ n) = liftPoly p ^ n := by
  induction n with
  | zero => simp [liftPoly_one]
  | succ n ih =>
    rw [pow_succ, pow_succ, liftPoly_mul, ih]

/-- Evaluating a multivariate polynomial at `Fin.cons x y` agrees with
evaluating the split polynomial (via `AzMvPolynomial.finSuccEquiv` and
`liftPoly`) at `x` after mapping its coefficients through `aeval y`.

This is the Azurite analogue of BPR's `aeval_snoc_eq_eval_splitLast`,
but using `Fin.cons` (prepend) and `AzMvPolynomial.finSuccEquiv`
(first-variable split) instead of `Fin.snoc` and `splitLast`. -/
theorem aeval_cons_eq_eval_finSuccEquiv
    (y : Fin k → C) (x : C) (P : AzMvPolynomial (k+1) D ord) :
    MvPolynomial.aeval (Fin.cons x y) P.toMvPoly =
      Polynomial.eval x
        ((liftPoly (AzMvPolynomial.finSuccEquiv P)).map
          (MvPolynomial.aeval y).toRingHom) := by
  show _ = Polynomial.eval x
    ((Polynomial.map toMvPolyHom (AzPolynomial.toPoly
      (AzMvPolynomial.finSuccEquiv P))).map
        (MvPolynomial.aeval y).toRingHom)
  rw [toPoly_map_finSuccEquiv]
  induction P.toMvPoly using MvPolynomial.induction_on with
  | C d =>
    simp [MvPolynomial.finSuccEquiv_apply]
  | add p q hp hq =>
    simp only [map_add, Polynomial.map_add, Polynomial.eval_add]
    rw [hp, hq]
  | mul_X p i ih =>
    simp only [map_mul, MvPolynomial.aeval_X, Polynomial.map_mul,
      Polynomial.eval_mul]
    rw [ih]
    refine Fin.cases ?_ ?_ i
    · simp [Fin.cons_zero, MvPolynomial.finSuccEquiv_apply]
    · intro j; simp [Fin.cons_succ, MvPolynomial.finSuccEquiv_apply]

/-- Fiber-level version of the projection predicate: rewritten via
`AzMvPolynomial.finSuccEquiv` so that the variable `X` is explicit
and then mapped through `aeval y` to land in `C[X]`. Azurite analogue
of BPR's `exists_snoc_iff_exists_eval_splitLast`. -/
theorem exists_cons_iff_exists_eval_finSuccEquiv
    (y : Fin k → C)
    (Ps Qs : List (AzMvPolynomial (k+1) D ord)) :
    (∃ x : C, (∀ P ∈ Ps, MvPolynomial.aeval (Fin.cons x y) P.toMvPoly = 0) ∧
              (∀ Q ∈ Qs, MvPolynomial.aeval (Fin.cons x y) Q.toMvPoly ≠ 0)) ↔
    (∃ x : C,
      (∀ P' ∈ ((Ps.map AzMvPolynomial.finSuccEquiv).map liftPoly).map
          (Polynomial.map (MvPolynomial.aeval y).toRingHom),
        Polynomial.eval x P' = 0) ∧
      (∀ Q' ∈ ((Qs.map AzMvPolynomial.finSuccEquiv).map liftPoly).map
          (Polynomial.map (MvPolynomial.aeval y).toRingHom),
        Polynomial.eval x Q' ≠ 0)) := by
  simp only [List.map_map, List.forall_mem_map, Function.comp_apply]
  constructor
  · rintro ⟨x, hP, hQ⟩
    refine ⟨x, ?_, ?_⟩
    · intro P hP_mem
      rw [← aeval_cons_eq_eval_finSuccEquiv]; exact hP P hP_mem
    · intro Q hQ_mem
      rw [← aeval_cons_eq_eval_finSuccEquiv]; exact hQ Q hQ_mem
  · rintro ⟨x, hP, hQ⟩
    refine ⟨x, ?_, ?_⟩
    · intro P hP_mem
      rw [aeval_cons_eq_eval_finSuccEquiv]; exact hP P hP_mem
    · intro Q hQ_mem
      rw [aeval_cons_eq_eval_finSuccEquiv]; exact hQ Q hQ_mem

/-- The realization of `azDegNeqFormula Q₁ Q₂` matches BPR's
`degNeqFormula (liftPoly Q₁) (liftPoly Q₂)`. -/
theorem azRealization_azDegNeqFormula [FaithfulSMul D C]
    (Q₁ Q₂ : AzPolynomial (AzMvPolynomial k D ord)) :
    azRealization (azDegNeqFormula Q₁ Q₂) (C := C) =
      (BPR.degNeqFormula (liftPoly Q₁) (liftPoly Q₂)).realization := by
  simp only [azDegNeqFormula, BPR.degNeqFormula]
  show (azFormulaToFieldFormula ((azDegEqFormula Q₁ Q₂).not)).realization = _
  simp only [azFormulaToFieldFormula, Formula.mapAtom, Formula.realization]
  show (azRealization (azDegEqFormula Q₁ Q₂))ᶜ = _
  rw [azRealization_azDegEqFormula]

/-! ### DNF-to-ConjDisjForms bridge

`azToConjDisjForms` splits each DNF clause's atoms into (eqs, neqs)
based on the `isEq` flag. The realization of the original formula is
the union of clauses, each of which evaluates to a conjunction of
equalities and disequalities. -/

variable {n : ℕ}

omit [IsDomain D] [DecidableEq D] in
/-- For a clause (list of atoms) processed by the foldr, the resulting
(eqs, neqs) pair captures: `eqs` = polynomials of atoms with `isEq = true`,
`neqs` = polynomials of atoms with `isEq = false`. Membership iff the
corresponding atom was in the original clause. -/
private theorem mem_foldr_azToConjDisjForms
    (cl : List (AzFieldAtom n D ord)) (y : Fin n → C) :
    let r := cl.foldr (init := (([] : List (AzMvPolynomial n D ord)),
                                 ([] : List (AzMvPolynomial n D ord))))
      (fun a (eqs, neqs) =>
        if a.isEq then (a.poly :: eqs, neqs) else (eqs, a.poly :: neqs))
    ((∀ P ∈ r.1, MvPolynomial.aeval y P.toMvPoly = 0) ∧
     (∀ Q ∈ r.2, MvPolynomial.aeval y Q.toMvPoly ≠ 0)) ↔
    (∀ a ∈ cl, y ∈ azFieldAtomInterpret (K := C) a) := by
  induction cl with
  | nil => simp
  | cons a rest ih =>
    simp only [List.foldr_cons]
    rcases ha : a.isEq with _ | _
    · -- a.isEq = false: neqs gets a.poly prepended
      simp only [Bool.false_eq_true, ↓reduceIte, List.mem_cons]
      constructor
      · rintro ⟨heq, hne⟩ b hb
        rcases hb with rfl | hb
        · simp only [azFieldAtomInterpret, ha, Bool.false_eq_true, ↓reduceIte,
            Set.mem_ofPred_eq]
          exact hne _ (Or.inl rfl)
        · exact (ih.mp ⟨heq, fun Q hQ => hne Q (Or.inr hQ)⟩) b hb
      · intro h
        refine ⟨?_, ?_⟩
        · intro P hP
          exact (ih.mpr (fun b hb => h b (Or.inr hb))).1 P hP
        · intro Q hQ
          rcases hQ with rfl | hQ
          · have := h a (Or.inl rfl)
            simp only [azFieldAtomInterpret, ha, Bool.false_eq_true, ↓reduceIte,
              Set.mem_ofPred_eq] at this
            exact this
          · exact (ih.mpr (fun b hb => h b (Or.inr hb))).2 Q hQ
    · -- a.isEq = true: eqs gets a.poly prepended
      simp only [↓reduceIte, List.mem_cons]
      constructor
      · rintro ⟨heq, hne⟩ b hb
        rcases hb with rfl | hb
        · simp only [azFieldAtomInterpret, ha, ↓reduceIte, Set.mem_ofPred_eq]
          exact heq _ (Or.inl rfl)
        · exact (ih.mp ⟨fun P hP => heq P (Or.inr hP), hne⟩) b hb
      · intro h
        refine ⟨?_, ?_⟩
        · intro P hP
          rcases hP with rfl | hP
          · have := h a (Or.inl rfl)
            simp only [azFieldAtomInterpret, ha, ↓reduceIte, Set.mem_ofPred_eq] at this
            exact this
          · exact (ih.mpr (fun b hb => h b (Or.inr hb))).1 P hP
        · intro Q hQ
          exact (ih.mpr (fun b hb => h b (Or.inr hb))).2 Q hQ

/-- The realization of a quantifier-free formula equals the union of its
clauses in `azToConjDisjForms`, where each clause `(eqs, neqs)` evaluates
to `(∀ P ∈ eqs, P = 0) ∧ (∀ Q ∈ neqs, Q ≠ 0)`. -/
theorem azRealization_azToConjDisjForms
    (Φ : Formula (Fin n) (AzFieldAtom n D ord)) (hqf : Φ.IsQuantifierFree) :
    azRealization Φ (C := C) =
      { y | ∃ cl ∈ azToConjDisjForms Φ,
              (∀ P ∈ cl.1, MvPolynomial.aeval y P.toMvPoly = 0) ∧
              (∀ Q ∈ cl.2, MvPolynomial.aeval y Q.toMvPoly ≠ 0) } := by
  rw [← gRealization_eq_azRealization, toDNF_gRealization (K := C) Φ hqf]
  ext y
  simp only [azToConjDisjForms, Set.mem_ofPred_eq, List.mem_map]
  constructor
  · rintro ⟨cl, hcl, hatom⟩
    refine ⟨_, ⟨cl, hcl, rfl⟩, ?_⟩
    exact (mem_foldr_azToConjDisjForms cl y).mpr
      (fun a ha => show y ∈ AtomRealization.interpret a from hatom a ha)
  · rintro ⟨_, ⟨cl, hcl, rfl⟩, hsplit⟩
    refine ⟨cl, hcl, ?_⟩
    intro a ha
    exact (show y ∈ azFieldAtomInterpret (K := C) a from
      (mem_foldr_azToConjDisjForms cl y).mp hsplit a ha)

/-! ### Main correctness theorem: `azRealization_azProjBasic` -/

/-- **Correctness of `azProjBasic`.** Its realization (as an Azurite
quantifier-free formula) is precisely the projection over the first
variable (`Fin 0`) of the basic constructible set defined by `Ps`
(equalities) and `Qs` (disequalities). -/
theorem azRealization_azProjBasic
    [IsAlgClosed C]
    (hinj : Function.Injective (algebraMap D C))
    (Ps Qs : List (AzMvPolynomial (k+1) D ord)) :
    azRealization (azProjBasic Ps Qs) (C := C) =
      { y : Fin k → C | ∃ x : C,
          (∀ P ∈ Ps, MvPolynomial.aeval (Fin.cons x y) P.toMvPoly = 0) ∧
          (∀ Q ∈ Qs, MvPolynomial.aeval (Fin.cons x y) Q.toMvPoly ≠ 0) } := by
  have : FaithfulSMul D C := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  set Ps'_az : List (AzPolynomial (AzMvPolynomial k D ord)) :=
    Ps.map AzMvPolynomial.finSuccEquiv with Ps'_az_def
  set Qs'_az : List (AzPolynomial (AzMvPolynomial k D ord)) :=
    Qs.map AzMvPolynomial.finSuccEquiv with Qs'_az_def
  set d : ℕ := 1 + (Ps'_az.map AzPolynomial.natDegree).foldr max 0 with d_def
  have hd_pos : 0 < d := by rw [d_def]; omega
  set extra_az : AzPolynomial (AzMvPolynomial k D ord) := Qs'_az.prod ^ d with extra_az_def
  -- BPR-side aliases via liftPoly
  set Ps' : List (Polynomial (MvPolynomial (Fin k) D)) := Ps'_az.map liftPoly with Ps'_def
  set Qs' : List (Polynomial (MvPolynomial (Fin k) D)) := Qs'_az.map liftPoly with Qs'_def
  -- liftPoly extra_az = Qs'.prod ^ d
  have hextra_lift : liftPoly extra_az = Qs'.prod ^ d := by
    rw [extra_az_def, liftPoly_pow, liftPoly_list_prod]
  -- d bound: Ps'.map natDegree = Ps'_az.map natDegree
  have hd_bound : ∀ P' ∈ Ps', P'.natDegree < d := by
    intro P' hP'
    rw [Ps'_def, List.mem_map] at hP'
    obtain ⟨P, hP_mem, rfl⟩ := hP'
    rw [liftPoly_natDegree, d_def]
    have h_le : P.natDegree ≤ (Ps'_az.map AzPolynomial.natDegree).foldr max 0 :=
      List.le_max_of_le' (b := 0) (List.mem_map.mpr ⟨P, hP_mem, rfl⟩) le_rfl
    omega
  -- Unfold the LHS
  show azRealization (azDisjList ((azPosgcd Ps'_az).flatMap fun QC₁ =>
    (AzPolynomial.tremsTree extra_az QC₁.1).leafPaths.map fun path =>
      azSmartAnd QC₁.2 (azSmartAnd
        (azLeafFormula extra_az QC₁.1 path)
        (azDegNeqFormula (azPathLeafParent extra_az path) QC₁.1)))) = _
  rw [azRealization_azDisjList]
  ext y
  simp only [Set.mem_ofPred_eq]
  rw [exists_cons_iff_exists_eval_finSuccEquiv y Ps Qs]
  -- Unfold the mapped list structure in the RHS
  show (∃ Φ ∈ _, y ∈ azRealization Φ (C := C)) ↔ _
  constructor
  · -- LHS → RHS: we have a witness clause in azPosgcd × leafPaths
    rintro ⟨Φ, hΦ_mem, hy_Φ⟩
    simp only [List.mem_flatMap, List.mem_map, Prod.exists] at hΦ_mem
    obtain ⟨G, 𝒞, h_mem_posgcd, path, hpath_mem, hΦ_eq⟩ := hΦ_mem
    subst hΦ_eq
    simp only [azRealization_azSmartAnd, Set.mem_inter_iff,
      azRealization_azLeafFormula, azRealization_azDegNeqFormula,
      BPR.realization_degNeqFormula, Set.mem_ofPred_eq] at hy_Φ
    obtain ⟨hy_C, hy_leaf, hy_deg⟩ := hy_Φ
    -- Transfer to BPR via azPosgcd_forward
    obtain ⟨G', C', hmem', hG_eq, hR⟩ :=
      azPosgcd_forward (C := C) Ps'_az G 𝒞 h_mem_posgcd
    -- posgcd_gcd on Ps' gives IsListGCD
    have h_G_1_isListGCD :
        IsListGCD (G'.map (MvPolynomial.aeval y).toRingHom)
          (Ps'.map (Polynomial.map (MvPolynomial.aeval y).toRingHom)) := by
      have := BPR.posgcd_gcd Ps' hmem' y (hR ▸ hy_C)
      exact this
    -- Bridge leaf path into BPR.TRems
    have hpath'_mem : path.map liftPoly ∈
        (BPR.TRems (liftPoly extra_az) G').leafPaths := by
      rw [← hG_eq]
      exact leafPaths_tremsTree_bridge extra_az G path hpath_mem
    -- Construct h_G_isGCD in the BPR form with extra = Qs'.prod^d and G_BPR = G'
    have hy_leaf' : y ∈ (BPR.leafFormula (liftPoly extra_az) G'
        (path.map liftPoly)).realization := by
      rw [← hG_eq]; exact hy_leaf
    have h_G_isGCD_raw :=
      BPR.leafFormula_gcd (liftPoly extra_az) G' hpath'_mem y hy_leaf'
    -- Reshape to match fiber_iff_degree_ne: need extra as `Qs'.prod^d` and
    -- the first arg as `pathLeafParent (Qs'.prod^d) (path.map liftPoly)`.
    rw [hextra_lift] at h_G_isGCD_raw
    -- Build h_deg_ne in the same BPR form
    have h_deg_ne :
        Polynomial.degree
          ((BPR.pathLeafParent (Qs'.prod ^ d) (path.map liftPoly)).map
            (MvPolynomial.aeval y).toRingHom) ≠
        Polynomial.degree
          (G'.map (MvPolynomial.aeval y).toRingHom) := by
      rw [← hextra_lift, ← liftPoly_azPathLeafParent, ← hG_eq]
      exact hy_deg
    exact (BPR.fiber_iff_degree_ne Ps' Qs' d hd_bound hd_pos y
      h_G_1_isListGCD h_G_isGCD_raw).mpr h_deg_ne
  · -- RHS → LHS: use posgcd_covering + leafFormula_covering to find clause
    rintro ⟨x, hP, hQ⟩
    -- Apply posgcd_covering on BPR side
    obtain ⟨G', C', h_mem_posgcd', hy_C'⟩ :=
      BPR.posgcd_covering hinj Ps' y
    -- Transfer back to azPosgcd
    obtain ⟨G, 𝒞, h_mem_posgcd, hG_eq, hR⟩ :=
      azPosgcd_backward (C := C) Ps'_az G' C' h_mem_posgcd'
    have hy_C : y ∈ azRealization 𝒞 (C := C) := hR ▸ hy_C'
    -- Apply leafFormula_covering on BPR side
    obtain ⟨path', hpath'_mem, hy_leaf'⟩ :=
      BPR.leafFormula_covering hinj (liftPoly extra_az) G' y
    -- Transfer back to tremsTree via bridge_rev
    have hpath'_mem_G : path' ∈
        (BPR.TRems (liftPoly extra_az) (liftPoly G)).leafPaths := by
      rw [hG_eq]; exact hpath'_mem
    obtain ⟨path, hpath_mem, hpath_eq⟩ :=
      leafPaths_tremsTree_bridge_rev extra_az G path' hpath'_mem_G
    -- Transfer leaf formula realization back (we need G', not liftPoly G)
    have hy_leaf : y ∈ azRealization (azLeafFormula extra_az G path) (C := C) := by
      rw [azRealization_azLeafFormula, hpath_eq, hG_eq]
      exact hy_leaf'
    -- posgcd_gcd + leafFormula_gcd
    have h_G_1_isListGCD :
        IsListGCD (G'.map (MvPolynomial.aeval y).toRingHom)
          (Ps'.map (Polynomial.map (MvPolynomial.aeval y).toRingHom)) :=
      BPR.posgcd_gcd Ps' h_mem_posgcd' y hy_C'
    have h_G_isGCD :=
      BPR.leafFormula_gcd (liftPoly extra_az) G' hpath'_mem y hy_leaf'
    rw [hextra_lift] at h_G_isGCD
    -- Use fiber_iff_degree_ne in forward direction
    have h_deg :=
      (BPR.fiber_iff_degree_ne Ps' Qs' d hd_bound hd_pos y
        h_G_1_isListGCD h_G_isGCD).mp ⟨x, hP, hQ⟩
    -- Build the witness clause
    refine ⟨azSmartAnd 𝒞 (azSmartAnd
        (azLeafFormula extra_az G path)
        (azDegNeqFormula (azPathLeafParent extra_az path) G)), ?_, ?_⟩
    · simp only [List.mem_flatMap, List.mem_map, Prod.exists]
      exact ⟨G, 𝒞, h_mem_posgcd, path, hpath_mem, rfl⟩
    · simp only [azRealization_azSmartAnd, Set.mem_inter_iff,
        azRealization_azLeafFormula, azRealization_azDegNeqFormula,
        BPR.realization_degNeqFormula, Set.mem_ofPred_eq]
      rw [azRealization_azLeafFormula] at hy_leaf
      refine ⟨hy_C, hy_leaf, ?_⟩
      rw [liftPoly_azPathLeafParent, hpath_eq, hG_eq]
      rw [hextra_lift]
      exact h_deg

/-! ### Correctness of `azProjectQF` -/

/-- **Correctness of `azProjectQF`.** The realization of `azProjectQF Φ`
is precisely the projection over the first variable (`Fin 0`) of the
realization of `Φ`, i.e. the set of `y ∈ C^k` such that some extension
`Fin.cons x y : Fin (k+1) → C` lies in `Φ`'s realization. -/
theorem azRealization_azProjectQF
    [IsAlgClosed C]
    (hinj : Function.Injective (algebraMap D C))
    (Φ : Formula (Fin (k+1)) (AzFieldAtom (k+1) D ord))
    (hqf : Φ.IsQuantifierFree) :
    azRealization (azProjectQF Φ hqf) (C := C) =
      { y : Fin k → C | ∃ x : C,
          Fin.cons x y ∈ azRealization Φ (C := C) } := by
  have : FaithfulSMul D C := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  unfold azProjectQF
  rw [azRealization_azSimplify,
      ← gRealization_eq_azRealization (K := C), toNNF_gRealization,
      gRealization_eq_azRealization, azRealization_azDisjList,
      azRealization_azToConjDisjForms (C := C) Φ hqf]
  ext y
  simp only [List.mem_map, Prod.exists, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨Ψ, ⟨Ps', Qs', h_cl, rfl⟩, hy⟩
    rw [azRealization_azProjBasic hinj Ps' Qs'] at hy
    obtain ⟨x, hP, hQ⟩ := hy
    exact ⟨x, Ps', Qs', h_cl, hP, hQ⟩
  · rintro ⟨x, Ps', Qs', h_cl, hP, hQ⟩
    refine ⟨azProjBasic Ps' Qs', ⟨Ps', Qs', h_cl, rfl⟩, ?_⟩
    rw [azRealization_azProjBasic hinj Ps' Qs']
    exact ⟨x, hP, hQ⟩

/-- **Correctness of `azProjectQFAt`.** Projection over an arbitrary
variable `i : Fin (k+1)`. The realization is precisely the set of
`y : Fin k → C` such that some extension `(Fin.cons x y) ∘ swap 0 i`
lies in `Φ`'s realization, i.e. placing `x` at position `i` in the
ambient `Fin (k+1)`-vector. -/
theorem azRealization_azProjectQFAt
    [IsAlgClosed C]
    (hinj : Function.Injective (algebraMap D C))
    (i : Fin (k+1))
    (Φ : Formula (Fin (k+1)) (AzFieldAtom (k+1) D ord))
    (hqf : Φ.IsQuantifierFree) :
    azRealization (azProjectQFAt i Φ hqf) (C := C) =
      { y : Fin k → C | ∃ x : C,
          (Fin.cons x y) ∘ (Equiv.swap (0 : Fin (k+1)) i) ∈
            azRealization Φ (C := C) } := by
  have : FaithfulSMul D C := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  unfold azProjectQFAt
  dsimp only
  rw [azRealization_azProjectQF hinj (renameFormulaEquiv (Equiv.swap 0 i) Φ)
    (Formula.rename_isQF _ _ Φ hqf)]
  ext y
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [← gRealization_eq_azRealization (K := C)] at hx
    rw [rename_gRealization_equiv] at hx
    simp only [Set.mem_preimage] at hx
    rw [← gRealization_eq_azRealization (K := C)]
    exact hx
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [← gRealization_eq_azRealization (K := C)] at hx
    rw [← gRealization_eq_azRealization (K := C),
        rename_gRealization_equiv]
    exact hx

end Azurite
