import Azurite.BasuPollackRoy.Chapter1.Section1_1.ConstructibleSets
import Azurite.BasuPollackRoy.Chapter1.Section1_1.Definitions
import Azurite.BasuPollackRoy.Chapter1.Section1_1.Exercise1_1
import Azurite.BasuPollackRoy.Chapter1.Section1_1.Exercise1_2
import Azurite.BasuPollackRoy.Chapter1.Section1_1.Exercise1_3
import Azurite.BasuPollackRoy.Chapter1.Section1_1.FieldFormula
import Azurite.BasuPollackRoy.Chapter1.Section1_1.Formula
import Azurite.BasuPollackRoy.Chapter1.Section1_1.Notation1_1
import Azurite.BasuPollackRoy.Chapter1.Section1_1.PrenexNormalForm
import Azurite.BasuPollackRoy.Chapter1.Section1_1.Realization
import Azurite.BasuPollackRoy.Chapter1.Section1_1.RealizationInvariance
import Azurite.BasuPollackRoy.Chapter1.Section1_1.Sentences

namespace Azurite.BPR

open MvPolynomial Polynomial

variable {k : ℕ} {C : Type*} [Field C] [IsAlgClosed C]

namespace Formula

variable {σ : Type*} {D : Type*} [CommRing D]
variable [Algebra D C]

/-!
### Exercise 1.4: Field Axioms

The field axioms as formulas. The ring axioms
(commutativity, associativity, distributivity, identities)
are tautological polynomial identities. The remaining
non-trivial axioms are:
-/

/-- ∀X₀ ∃X₁, X₀ + X₁ = 0 (additive inverse). -/
noncomputable def additiveInverse : Formula (Fin 2) (FieldAtom (Fin 2) ℤ) :=
  forall_ 0 (.exists_ 1 (eq_zero (X 0 + X 1)))

/-- ∀X₀, X₀ = 0 ∨ ∃X₁, X₀X₁ − 1 = 0
    (multiplicative inverse for nonzero elements). -/
noncomputable def multiplicativeInverse : Formula (Fin 2) (FieldAtom (Fin 2) ℤ) :=
  forall_ 0 (.or (eq_zero (X 0))
    (.exists_ 1 (eq_zero (X 0 * X 1 - 1))))

/-- 1 ≠ 0 (nontriviality). -/
noncomputable def fieldNontriviality : Formula (Fin 2) (FieldAtom (Fin 2) ℤ) :=
  ne_zero 1

omit [IsAlgClosed C] in
theorem additiveInverse_holds :
    additiveInverse.realization (C := C) =
      Set.univ := by
  ext y; simp [additiveInverse, realization]
  intro c
  exact ⟨-c, by simp⟩

omit [IsAlgClosed C] in
theorem multiplicativeInverse_holds :
    multiplicativeInverse.realization (C := C) =
      Set.univ := by
  ext y; simp [multiplicativeInverse, realization]
  intro c; by_cases hc : c = 0
  · subst hc; simp
  · right; exact ⟨c⁻¹, by field_simp [hc]; ring⟩

omit [IsAlgClosed C] in
theorem fieldNontriviality_holds :
    fieldNontriviality.realization (C := C) =
      Set.univ := by
  ext y; simp [fieldNontriviality, ne_zero, realization, FieldAtom.neZero]

/-!
### Algebraic Closure Axiom Φ_d

Φ_d asserts that every monic polynomial of degree d has a
root: ∀Y₁...∀Y_d ∃X, X^d + Y₁X^(d-1) + ... + Y_d = 0.
-/

/-- The generic monic polynomial of degree d:
    X₀^d + X₁ · X₀^(d-1) + X₂ · X₀^(d-2) + ... + X_d.
    Variable 0 is the root variable, variables 1..d are
    coefficients. -/
noncomputable def monicPoly (d : ℕ) :
    MvPolynomial (Fin (d + 1)) ℤ :=
  X 0 ^ d + ∑ i : Fin d,
    X ⟨i + 1, by omega⟩ * X 0 ^ (d - 1 - i)

/-- Φ_d: ∀Y₁ ∀Y₂ ... ∀Y_d ∃X, monicPoly d = 0.
    Example: Φ₂ = ∀Y₁ ∀Y₂ ∃X, X² + Y₁X + Y₂ = 0. -/
noncomputable def phiD (d : ℕ) : Formula (Fin (d + 1)) (FieldAtom (Fin (d + 1)) ℤ) :=
  (List.finRange d).foldr
    (fun i acc => forall_ ⟨i.val + 1, by omega⟩ acc)
    (.exists_ 0 (eq_zero (monicPoly d)))

omit [IsAlgClosed C] in
private theorem realization_forall_of_univ [DecidableEq σ]
    (x : σ) (Φ : Formula σ (FieldAtom σ D))
    (h : Φ.realization (C := C) = Set.univ) :
    (forall_ x Φ).realization (C := C) = Set.univ := by
  ext y; simp [realization, h]

omit [IsAlgClosed C] in
private theorem realization_foldr_forall_of_univ
    [DecidableEq σ] (xs : List σ) (body : Formula σ (FieldAtom σ D))
    (h : body.realization (C := C) = Set.univ) :
    (xs.foldr (fun x acc => forall_ x acc)
      body).realization (C := C) = Set.univ := by
  induction xs with
  | nil => exact h
  | cons x xs ih =>
    simp [List.foldr]
    exact realization_forall_of_univ x _ ih

omit [IsAlgClosed C] in
private theorem realization_finRange_forall_of_univ {n : ℕ}
    (d : ℕ) (g : Fin d → Fin (n + 1)) (body : Formula (Fin (n + 1)) (FieldAtom (Fin (n + 1)) ℤ))
    (h : body.realization (C := C) = Set.univ) :
    ((List.finRange d).foldr (fun i acc => forall_ (g i) acc)
      body).realization (C := C) = Set.univ := by
  induction (List.finRange d) with
  | nil => exact h
  | cons x xs ih =>
    simp only [List.foldr]
    exact realization_forall_of_univ (g x) _ ih

/-- Φ_d holds in any algebraically closed field. -/
theorem phiD_holds (d : ℕ) (hd : 0 < d) :
    (phiD d).realization (C := C) = Set.univ := by
  unfold phiD
  apply realization_finRange_forall_of_univ
  ext y
  simp only [realization, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  let q := ∑ i : Fin d,
    Polynomial.C (y ⟨↑i + 1, by omega⟩) * Polynomial.X ^ (d - 1 - (i : ℕ))
  let p : C[X] := Polynomial.X ^ d + q
  -- natDegree q ≤ d - 1
  have hnd : q.natDegree ≤ d - 1 := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i _
    exact le_trans (Polynomial.natDegree_C_mul_X_pow_le _ _) (by omega)
  -- degree q < d
  have hq : q.degree < (d : WithBot ℕ) := by
    by_cases hq0 : q = 0
    · simp [hq0]
    · rw [← Polynomial.natDegree_lt_iff_degree_lt hq0]; omega
  -- p is monic
  have hp : p.Monic := Polynomial.monic_X_pow_add hq
  -- p.natDegree = d
  have hpnd : p.natDegree = d := by
    show (Polynomial.X ^ d + q).natDegree = d
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
    · simp
    · by_cases hq0 : q = 0
      · simp [hq0, hd]
      · simp; exact lt_of_le_of_lt hnd (by omega)
  -- degree p ≠ 0
  have hdeg : p.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hp.ne_zero, hpnd]
    exact_mod_cast hd.ne'
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_root p hdeg
  rw [Polynomial.IsRoot] at hc
  refine ⟨c, ?_⟩
  simp only [monicPoly]
  convert hc using 1
  simp [p, q, Polynomial.eval_add, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C]

omit [IsAlgClosed C] in
private lemma forall_realization_univ_iff
    {D : Type*} [CommRing D] [Algebra D C]
    {σ : Type*} [DecidableEq σ]
    (x : σ) (Φ : Formula σ (FieldAtom σ D)) :
    (forall_ x Φ).realization (C := C) = Set.univ ↔
    Φ.realization (C := C) = Set.univ := by
  constructor
  · intro h; ext z; simp only [Set.mem_univ, iff_true]
    have hz := (Set.eq_univ_iff_forall.mp h) z
    simp only [realization, Set.mem_setOf_eq] at hz
    convert hz (z x); exact (Function.update_eq_self x z).symm
  · intro h; ext y; simp only [Set.mem_univ, iff_true]
    simp only [realization, Set.mem_setOf_eq]
    intro c; exact Set.eq_univ_iff_forall.mp h _

omit [IsAlgClosed C] in
private lemma phiD_univ_iff (d : ℕ) :
    (phiD d).realization (C := C) = Set.univ ↔
    (Formula.exists_ (0 : Fin (d + 1))
      (Formula.eq_zero (monicPoly d))).realization (C := C) = Set.univ := by
  unfold phiD
  suffices h : ∀ (xs : List (Fin d)) (body : Formula (Fin (d + 1)) (FieldAtom (Fin (d + 1)) ℤ)),
    (xs.foldr (fun i acc => forall_ ⟨i.val + 1, by omega⟩ acc)
      body).realization (C := C) = Set.univ ↔
    body.realization (C := C) = Set.univ from h _ _
  intro xs body; induction xs with
  | nil => exact Iff.rfl
  | cons x xs ih =>
    simp only [List.foldr_cons]
    exact (forall_realization_univ_iff _ _).trans ih

omit [IsAlgClosed C] in
/-- Converse of `phiD_holds`: if Φ_d holds for all d ≥ 1,
    then C is algebraically closed. -/
theorem isAlgClosed_of_phiD_holds
    (h : ∀ d, 0 < d → (phiD d).realization (C := C) = Set.univ) :
    IsAlgClosed C := by
  apply IsAlgClosed.of_exists_root
  intro p hp hirr
  have hd : 0 < p.natDegree := by
    by_contra hle; push Not at hle
    exact not_irreducible_one
      ((Polynomial.eq_one_of_monic_natDegree_zero hp (by omega)) ▸ hirr)
  set d := p.natDegree with d_def
  have hphi := (phiD_univ_iff d).mp (h d hd)
  have hR := Set.eq_univ_iff_forall.mp hphi
  set y : Fin (d + 1) → C := fun j => p.coeff (d - j.val)
  have hy := hR y
  simp only [realization, Set.mem_setOf_eq] at hy
  obtain ⟨c, hc⟩ := hy
  refine ⟨c, ?_⟩
  simp only [monicPoly] at hc
  have h_upd : ∀ i : Fin d,
    Function.update y (0 : Fin (d + 1)) c ⟨↑i + 1, by omega⟩ =
    p.coeff (d - 1 - (i : ℕ)) := by
    intro i
    rw [Function.update_of_ne (show (⟨↑i + 1, by omega⟩ : Fin (d + 1)) ≠ 0
      from by simp [Fin.ext_iff])]
    simp only [y]; congr 1; omega
  simp only [realization_eq_zero, Set.mem_setOf_eq] at hc
  simp only [map_add, map_pow, MvPolynomial.aeval_X,
    map_sum, map_mul, Function.update_self] at hc
  simp_rw [h_upd] at hc
  rw [← hc]
  conv_lhs => rw [Polynomial.as_sum_range_C_mul_X_pow p]
  simp only [d_def, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  rw [Finset.sum_range_succ,
    show p.coeff p.natDegree = 1 from hp.coeff_natDegree,
    one_mul, add_comm]
  congr 1
  rw [← Finset.sum_range_reflect (fun j => p.coeff j * c ^ j) d]
  symm
  apply Finset.sum_nbij (fun (i : Fin d) => (i : ℕ))
  · intro i _; exact Finset.mem_range.mpr i.isLt
  · intro i₁ i₂ _ _ h; exact Fin.val_injective h
  · intro j hj
    exact ⟨⟨j, Finset.mem_range.mp hj⟩, Finset.mem_univ _, rfl⟩
  · intro _ _; rfl

end Formula

/-!
### Example 1.2

Φ = (∃Y)(XY − 1 = 0) and Ψ = (X ≠ 0) are formulas over ℤ
with Free(Φ) = Free(Ψ) = {X}. Ψ is quantifier-free, and
Φ and Ψ are C-equivalent for any algebraically closed field C.
-/

section Example_1_2

open Formula

/-- Φ = ∃Y, XY - 1 = 0 (0 = X, 1 = Y). -/
noncomputable def Φ_ex : Formula (Fin 2) (FieldAtom (Fin 2) ℤ) :=
  .exists_ 1 (eq_zero (X 0 * X 1 - 1))

/-- Ψ = X ≠ 0. -/
noncomputable def Ψ_ex : Formula (Fin 2) (FieldAtom (Fin 2) ℤ) :=
  Formula.ne_zero (X 0)

theorem freeVars_Φ : Φ_ex.freeVars = {0} := by
  simp only [Φ_ex, freeVars, eq_zero, FieldAtom.eqZero, FieldAtom.vars]
  ext x; fin_cases x
  · -- x = 0
    simp only [Finset.mem_sdiff, Finset.mem_singleton]
    exact ⟨fun _ => rfl, fun _ =>
      ⟨(MvPolynomial.mem_vars _).mpr
        ⟨Finsupp.single 0 1 + Finsupp.single 1 1,
          MvPolynomial.mem_support_iff.mpr (by
            simp only [MvPolynomial.coeff_sub, MvPolynomial.coeff_one]
            rw [show MvPolynomial.X (0 : Fin 2) * MvPolynomial.X 1 =
              MvPolynomial.monomial (Finsupp.single 0 1 + Finsupp.single 1 1) (1 : ℤ)
              from by simp [MvPolynomial.X, MvPolynomial.monomial_mul]]
            simp only [MvPolynomial.coeff_monomial,
              if_neg (show (0 : (Fin 2) →₀ ℕ) ≠ Finsupp.single 0 1 + Finsupp.single 1 1
                from by intro h; have := DFunLike.congr_fun h 0; simp at this)]
            norm_num),
          by simp [Finsupp.mem_support_iff]⟩, by decide⟩⟩
  · -- x = 1
    simp [Finset.mem_sdiff, Finset.mem_singleton]

theorem freeVars_Ψ : Ψ_ex.freeVars = {0} := by
  simp only [Ψ_ex, ne_zero, freeVars, FieldAtom.neZero, FieldAtom.vars,
    MvPolynomial.vars_X]

theorem freeVars_eq : Φ_ex.freeVars = Ψ_ex.freeVars := by
  rw [freeVars_Φ, freeVars_Ψ]

theorem Ψ_qf : Ψ_ex.IsQuantifierFree := trivial

variable {C : Type*} [Field C] [IsAlgClosed C]

omit [IsAlgClosed C] in
/-- Example 1.2: Φ and Ψ are C-equivalent. -/
theorem example_1_2 :
    Formula.CEquiv (C := C) Φ_ex Ψ_ex := by
  unfold CEquiv Φ_ex Ψ_ex ne_zero realization
  ext y
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨c, hc⟩
    simp only [realization_eq_zero, Set.mem_setOf_eq] at *
    simp only [map_sub, map_mul, map_one, MvPolynomial.aeval_X] at *
    simp only [Function.update_self,
      Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)] at hc
    intro h0
    simp only [FieldAtom.neZero, MvPolynomial.aeval_X] at h0
    rw [h0, zero_mul, zero_sub] at hc
    exact one_ne_zero (neg_eq_zero.mp hc)
  · intro h
    simp only [realization_eq_zero, Set.mem_setOf_eq] at *
    simp only [map_sub, map_mul, map_one, MvPolynomial.aeval_X] at *
    refine ⟨(y 0)⁻¹, ?_⟩
    simp only [Function.update_self,
      Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)]
    simp only [FieldAtom.neZero, MvPolynomial.aeval_X] at h
    rw [mul_inv_cancel₀ h, sub_self]

end Example_1_2

/-!
### Constructible ↔ QF-Realizable

A set is constructible if and only if it is the realization of
a quantifier-free formula.
-/

namespace Formula

variable {D : Type*} [CommRing D] {σ : Type*}
variable {C : Type*} [Field C] [Algebra D C]

/-- Conjunction of `eq_zero` atoms from a list. -/
noncomputable def conjEqZero : List (MvPolynomial σ D) → Formula σ (FieldAtom σ D)
  | [] => eq_zero 0
  | [P] => eq_zero P
  | P :: Ps => .and (eq_zero P) (conjEqZero Ps)

theorem conjEqZero_isQF :
    ∀ (L : List (MvPolynomial σ D)),
    (conjEqZero L).IsQuantifierFree
  | [] => trivial
  | [_] => trivial
  | _ :: _ :: Ps =>
    ⟨trivial, conjEqZero_isQF (_ :: Ps)⟩

theorem conjEqZero_realization [DecidableEq σ]
    {C : Type*} [Field C] [Algebra D C] :
    ∀ (L : List (MvPolynomial σ D)),
    (conjEqZero L).realization (C := C) =
      { y | ∀ P ∈ L, MvPolynomial.aeval y P = 0}
  | [] => by
    ext y; simp [conjEqZero, map_zero]
  | [P] => by
    ext y; simp [conjEqZero]
  | P :: Q :: Ps => by
    ext y
    simp only [conjEqZero, realization, Set.mem_inter_iff,
      Set.mem_setOf_eq, List.mem_cons]
    rw [show (conjEqZero (Q :: Ps)).realization (C := C) =
      { y | ∀ P ∈ (Q :: Ps), MvPolynomial.aeval y P = 0}
      from conjEqZero_realization (Q :: Ps)]
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨hP, hrest⟩ R hR
      rcases hR with rfl | hR
      · exact hP
      · exact hrest R (List.mem_cons.mpr hR)
    · intro h
      exact ⟨h P (Or.inl rfl),
        fun R hR => h R (Or.inr (List.mem_cons.mp hR))⟩

end Formula

open Formula in
omit [IsAlgClosed C] in
/-- Backward: QF-realizable → constructible. -/
theorem qf_realizable_isConstructible
    {Φ : Formula (Fin k) (FieldAtom (Fin k) C)} (hqf : Φ.IsQuantifierFree) :
    IsConstructibleSet (Φ.realization (C := C)) := by
  induction Φ with
  | atom a =>
    by_cases h : a.isEq = true
    · -- P = 0 case: algebraic set
      exact .algebraic ⟨{a.poly}, by
        ext y; simp [Zer, realization, h, MvPolynomial.aeval_def]⟩
    · -- P ≠ 0 case: complement of algebraic set
      have : (atom a).realization (C := C) =
          ({y | MvPolynomial.eval y a.poly = 0} : Set (Fin k → C))ᶜ := by
        ext y; simp [realization, h, Set.mem_compl_iff, Set.mem_setOf_eq]
      rw [this]
      exact .compl (.algebraic ⟨{a.poly}, by
        ext y; simp [Zer]⟩)
  | not Φ ih => exact .compl (ih hqf)
  | and Φ₁ Φ₂ ih₁ ih₂ =>
    exact .inter (ih₁ hqf.1) (ih₂ hqf.2)
  | or Φ₁ Φ₂ ih₁ ih₂ =>
    exact (ih₁ hqf.1).union (ih₂ hqf.2)
  | implies Φ₁ Φ₂ ih₁ ih₂ =>
    exact (IsConstructibleSet.compl (ih₁ hqf.1)).union (ih₂ hqf.2)
  | exists_ x Φ _ => exact absurd hqf id
  | forall_ x Φ _ => exact absurd hqf id

open Formula in
omit [IsAlgClosed C] in
/-- Forward: constructible → QF-realizable. -/
theorem constructible_isQFRealizable
    (V : Set (Fin k → C)) (hV : IsConstructibleSet V) :
    ∃ Φ : Formula (Fin k) (FieldAtom (Fin k) C), Φ.IsQuantifierFree ∧
      V = Φ.realization (C := C) := by
  induction hV with
  | algebraic hA =>
    obtain ⟨poly_set, rfl⟩ := hA
    exact ⟨conjEqZero poly_set.toList, conjEqZero_isQF _,
      by rw [conjEqZero_realization]
         ext y; simp [Zer, MvPolynomial.aeval_def]⟩
  | compl _ ih =>
    obtain ⟨Φ, hqf, rfl⟩ := ih
    exact ⟨.not Φ, hqf, by simp [realization]⟩
  | inter _ _ ih₁ ih₂ =>
    obtain ⟨Φ₁, hqf₁, rfl⟩ := ih₁
    obtain ⟨Φ₂, hqf₂, rfl⟩ := ih₂
    exact ⟨.and Φ₁ Φ₂, ⟨hqf₁, hqf₂⟩,
      by simp [realization]⟩

omit [IsAlgClosed C] in
/-- A set is constructible iff it is the realization of a
    quantifier-free formula. -/
theorem constructible_iff_qfRealizable
    (V : Set (Fin k → C)) :
    IsConstructibleSet V ↔
    ∃ Φ : Formula (Fin k) (FieldAtom (Fin k) C), Φ.IsQuantifierFree ∧
      V = Φ.realization (C := C) :=
  ⟨constructible_isQFRealizable V,
   fun ⟨_, hqf, hV⟩ => hV ▸ qf_realizable_isConstructible hqf⟩

end Azurite.BPR
