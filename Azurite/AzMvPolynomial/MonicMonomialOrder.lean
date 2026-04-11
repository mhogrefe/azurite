/-
  LinearOrder instance for `MonicMonomial σ` (legacy `Var`-polymorphic wrapper).

  The vector-level `compareExponents_*` lemmas now live in
  `Azurite.AzMvPolynomial.New.MonicMonomialOrder`; this file only defines
  the `MonicMonomial σ` wrapper.
-/
import Azurite.AzMvPolynomial.MonicMonomial
import Azurite.AzMvPolynomial.New.MonicMonomialOrder

namespace Azurite
open MonomialOrder MonicMonomial

variable {n : ℕ}

/-! ### LinearOrder instance -/

variable {σ : Type _} [LinearOrder σ] [Var σ n] {ord : MonomialOrder}

/-- Compare two monic monomials using the specified monomial ordering.
    We use `def` (not `abbrev`) so that rewrite tactics work predictably. -/
private def cmpM (a b : MonicMonomial σ ord) : Ordering :=
  compareExponents ord a.exponents b.exponents

private theorem cmpM_refl (a : MonicMonomial σ ord) : cmpM a a = .eq :=
  compareExponents_refl ord _

private theorem cmpM_swap (a b : MonicMonomial σ ord) :
    (cmpM a b).swap = cmpM b a :=
  compareExponents_swap ord _ _

private theorem cmpM_eq (a b : MonicMonomial σ ord) (h : cmpM a b = .eq) : a = b :=
  MonicMonomial.ext (compareExponents_eq ord _ _ h)

private theorem cmpM_trans_lt (a b c : MonicMonomial σ ord)
    (h1 : cmpM a b = .lt) (h2 : cmpM b c = .lt) : cmpM a c = .lt :=
  compareExponents_trans_lt ord _ _ _ h1 h2

private theorem cmpM_lt_of_gt {a b : MonicMonomial σ ord} (h : cmpM a b = .gt) :
    cmpM b a = .lt := by
  have := cmpM_swap a b; rw [h] at this; exact this.symm

private theorem cmpM_gt_of_lt {a b : MonicMonomial σ ord} (h : cmpM a b = .lt) :
    cmpM b a = .gt := by
  have := cmpM_swap a b; rw [h] at this; exact this.symm

instance : LE (MonicMonomial σ ord) := ⟨fun a b => cmpM a b ≠ .gt⟩
instance : LT (MonicMonomial σ ord) := ⟨fun a b => cmpM a b = .lt⟩

instance : DecidableRel (LE.le (α := MonicMonomial σ ord)) := fun a b =>
  inferInstanceAs (Decidable (cmpM a b ≠ .gt))

instance : DecidableRel (LT.lt (α := MonicMonomial σ ord)) := fun a b =>
  inferInstanceAs (Decidable (cmpM a b = .lt))

instance : PartialOrder (MonicMonomial σ ord) where
  le_refl a := by
    show cmpM a a ≠ .gt; rw [cmpM_refl]; decide
  le_trans a b c hab hbc := by
    show cmpM a c ≠ .gt
    change cmpM a b ≠ .gt at hab; change cmpM b c ≠ .gt at hbc
    intro hac
    match hab' : cmpM a b, hbc' : cmpM b c with
    | .lt, .lt =>
      have := cmpM_trans_lt a b c hab' hbc'; rw [this] at hac; exact Ordering.noConfusion hac
    | .lt, .eq =>
      have heq := cmpM_eq b c hbc'; subst heq; rw [hab'] at hac; exact Ordering.noConfusion hac
    | .eq, _ =>
      have heq := cmpM_eq a b hab'; subst heq; exact hbc hac
    | .gt, _ => exact hab hab'
    | _, .gt => exact hbc hbc'
  le_antisymm a b hab hba := by
    change cmpM a b ≠ .gt at hab; change cmpM b a ≠ .gt at hba
    match h : cmpM a b with
    | .lt => exact absurd (cmpM_gt_of_lt h) hba
    | .eq => exact cmpM_eq a b h
    | .gt => exact absurd h hab
  lt_iff_le_not_ge a b := by
    change cmpM a b = .lt ↔ cmpM a b ≠ .gt ∧ ¬(cmpM b a ≠ .gt)
    constructor
    · intro h
      exact ⟨by rw [h]; decide, by push Not; exact cmpM_gt_of_lt h⟩
    · intro ⟨hab, hba⟩
      push Not at hba
      match h : cmpM a b with
      | .lt => rfl
      | .eq =>
        have hsw := cmpM_swap a b; rw [h] at hsw; simp [Ordering.swap] at hsw
        rw [hsw.symm] at hba; exact Ordering.noConfusion hba
      | .gt => exact absurd h hab

instance MonicMonomial.instLinearOrder : LinearOrder (MonicMonomial σ ord) where
  le_total a b := by
    show cmpM a b ≠ .gt ∨ cmpM b a ≠ .gt
    match h : cmpM a b with
    | .lt => left; decide
    | .eq => left; decide
    | .gt => right; rw [cmpM_lt_of_gt h]; decide
  toDecidableLE := inferInstance
  toDecidableEq := inferInstance
  toDecidableLT := inferInstance
  compare_eq_compareOfLessAndEq a b := by
    -- Ord.compare a b = compareExponents ... = cmpM a b (by definition)
    show cmpM a b = compareOfLessAndEq a b
    unfold compareOfLessAndEq
    match h : cmpM a b with
    | .lt =>
      have : a < b := h
      simp [this]
    | .eq =>
      have : ¬(a < b) := by show ¬(cmpM a b = .lt); rw [h]; decide
      have : a = b := cmpM_eq a b h
      simp [*]
    | .gt =>
      have : ¬(a < b) := by show ¬(cmpM a b = .lt); rw [h]; decide
      have : ¬(a = b) := by
        intro heq; subst heq; rw [cmpM_refl] at h; exact Ordering.noConfusion h
      simp [*]

end Azurite
