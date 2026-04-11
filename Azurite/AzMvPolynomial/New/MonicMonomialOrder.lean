/-
  LinearOrder instance for `MonicMonomialNew` (Fin-only).

  This file also contains the vector-level `compareExponents_*` lemmas
  (`refl`, `swap`, `eq`, `trans_lt`) which are variable-type independent
  and are shared with the legacy `MonicMonomial σ` wrapper.
-/
import Azurite.AzMvPolynomial.New.MonicMonomial

namespace Azurite
open MonomialOrder

theorem compare_swap_eq {α : Type _} [LinearOrder α] (a b : α) :
    (compare a b).swap = compare b a := by
  cases h : compare a b <;> simp only [Ordering.swap]
  · exact (compare_gt_iff_gt.mpr (compare_lt_iff_lt.mp h)).symm
  · have := compare_eq_iff_eq.mp h; subst this; simp
  · exact (compare_lt_iff_lt.mpr (compare_gt_iff_gt.mp h)).symm

variable {n : ℕ}

/-! ### lexCompareAux properties -/

private theorem lexCompareAux_refl (a : Vector ℕ n) (i : ℕ) :
    lexCompareAux a a i = .eq := by
  unfold lexCompareAux; split
  · simp [lexCompareAux_refl a (i + 1)]
  · rfl
termination_by n - i

private theorem lexCompareAux_swap (a b : Vector ℕ n) (i : ℕ) :
    (lexCompareAux a b i).swap = lexCompareAux b a i := by
  unfold lexCompareAux
  split
  · next h =>
    have csw := compare_swap_eq (a[i]'h : ℕ) (b[i]'h : ℕ)
    cases hc : compare (a[i]'h : ℕ) (b[i]'h : ℕ) <;>
      simp only [Ordering.swap, hc] at csw ⊢ <;>
      simp only [← csw]
    exact lexCompareAux_swap a b (i + 1)
  · rfl
termination_by n - i

private theorem lexCompareAux_eq (a b : Vector ℕ n) (i : ℕ)
    (h : lexCompareAux a b i = .eq) (j : Fin n) (hj : i ≤ j.val) :
    a[j] = b[j] := by
  unfold lexCompareAux at h
  split at h
  · next hi =>
    rcases hc : compare (a[i]'hi : ℕ) (b[i]'hi : ℕ) with _ | _ | _
    · simp only [hc] at h; cases h
    · simp only [hc] at h
      by_cases hij : i = j.val
      · have hj_eq : (⟨i, hi⟩ : Fin n) = j := Fin.ext hij
        exact hj_eq ▸ compare_eq_iff_eq.mp hc
      · exact lexCompareAux_eq a b (i + 1) h j (by omega)
    · simp only [hc] at h; cases h
  · omega
termination_by n - i

private theorem lexCompareAux_trans_lt (a b c : Vector ℕ n) (i : ℕ)
    (hab : lexCompareAux a b i = .lt) (hbc : lexCompareAux b c i = .lt) :
    lexCompareAux a c i = .lt := by
  unfold lexCompareAux at hab hbc ⊢
  split
  · next h =>
    simp only [show i < n from h, ↓reduceDIte] at hab hbc
    rcases hab_c : compare (a[i]'h : ℕ) (b[i]'h : ℕ) with _ | _ | _
    · -- a[i] < b[i]
      simp only [hab_c] at hab
      rcases hbc_c : compare (b[i]'h : ℕ) (c[i]'h : ℕ) with _ | _ | _
      · simp [compare_lt_iff_lt.mpr (lt_trans (compare_lt_iff_lt.mp hab_c) (compare_lt_iff_lt.mp hbc_c))]
      · simp [(compare_eq_iff_eq.mp hbc_c) ▸ hab_c]
      · simp only [hbc_c] at hbc; cases hbc
    · -- a[i] = b[i]
      simp only [hab_c] at hab
      rcases hbc_c : compare (b[i]'h : ℕ) (c[i]'h : ℕ) with _ | _ | _
      · simp [(compare_eq_iff_eq.mp hab_c) ▸ hbc_c]
      · simp only [hbc_c] at hbc
        simp [compare_eq_iff_eq.mpr ((compare_eq_iff_eq.mp hab_c).trans (compare_eq_iff_eq.mp hbc_c))]
        exact lexCompareAux_trans_lt a b c (i + 1) hab hbc
      · simp only [hbc_c] at hbc; cases hbc
    · simp only [hab_c] at hab; cases hab
  · next h => simp [h] at hab
termination_by n - i

private theorem lexCompare_refl (a : Vector ℕ n) : lexCompare a a = .eq :=
  lexCompareAux_refl a 0

private theorem lexCompare_swap (a b : Vector ℕ n) : (lexCompare a b).swap = lexCompare b a :=
  lexCompareAux_swap a b 0

private theorem lexCompare_eq (a b : Vector ℕ n) (h : lexCompare a b = .eq) :
    a = b := by
  ext j : 1; exact lexCompareAux_eq a b 0 h ⟨j, by omega⟩ (Nat.zero_le _)

private theorem lexCompare_trans_lt (a b c : Vector ℕ n)
    (hab : lexCompare a b = .lt) (hbc : lexCompare b c = .lt) :
    lexCompare a c = .lt :=
  lexCompareAux_trans_lt a b c 0 hab hbc


/-! ### revlexCompareAux properties -/

private theorem revlexCompareAux_refl (a : Vector ℕ n) (i : ℕ) :
    revlexCompareAux a a i = .eq := by
  unfold revlexCompareAux; split
  · simp [revlexCompareAux_refl a (i + 1)]
  · rfl
termination_by n - i

private theorem revlexCompareAux_swap (a b : Vector ℕ n) (i : ℕ) :
    (revlexCompareAux a b i).swap = revlexCompareAux b a i := by
  unfold revlexCompareAux
  split
  · next h =>
    have csw := compare_swap_eq (a[n - 1 - i]'(by omega) : ℕ) (b[n - 1 - i]'(by omega) : ℕ)
    cases hc : compare (a[n - 1 - i]'(by omega) : ℕ) (b[n - 1 - i]'(by omega) : ℕ) <;>
      simp only [Ordering.swap, hc] at csw ⊢ <;>
      simp only [← csw]
    exact revlexCompareAux_swap a b (i + 1)
  · rfl
termination_by n - i

private theorem revlexCompareAux_eq_at (a b : Vector ℕ n) (i : ℕ)
    (h : revlexCompareAux a b i = .eq) (hi : i < n) :
    a[n-1-i]'(by omega) = b[n-1-i]'(by omega) := by
  unfold revlexCompareAux at h
  simp only [show i < n from hi, ↓reduceDIte] at h
  rcases hc : compare (a[n-1-i]'(by omega) : ℕ) (b[n-1-i]'(by omega) : ℕ) with _ | _ | _
  · simp only [hc] at h; cases h
  · exact compare_eq_iff_eq.mp hc
  · simp only [hc] at h; cases h

private theorem revlexCompareAux_sub (a b : Vector ℕ n) (i : ℕ)
    (h : revlexCompareAux a b i = .eq) (hi : i < n) :
    revlexCompareAux a b (i + 1) = .eq := by
  unfold revlexCompareAux at h
  simp only [show i < n from hi, ↓reduceDIte] at h
  rcases hc : compare (a[n-1-i]'(by omega) : ℕ) (b[n-1-i]'(by omega) : ℕ) with _ | _ | _
  · simp only [hc] at h; cases h
  · simp only [hc] at h; exact h
  · simp only [hc] at h; cases h

private theorem revlexCompareAux_trans_lt (a b c : Vector ℕ n) (i : ℕ)
    (hab : revlexCompareAux a b i = .lt) (hbc : revlexCompareAux b c i = .lt) :
    revlexCompareAux a c i = .lt := by
  unfold revlexCompareAux at hab hbc ⊢
  split
  · next h =>
    simp only [show i < n from h, ↓reduceDIte] at hab hbc
    rcases hab_c : compare (a[n-1-i]'(by omega) : ℕ) (b[n-1-i]'(by omega) : ℕ) with _ | _ | _
    · simp only [hab_c] at hab; cases hab
    · simp only [hab_c] at hab
      rcases hbc_c : compare (b[n-1-i]'(by omega) : ℕ) (c[n-1-i]'(by omega) : ℕ) with _ | _ | _
      · simp only [hbc_c] at hbc; cases hbc
      · simp only [hbc_c] at hbc
        simp [compare_eq_iff_eq.mpr ((compare_eq_iff_eq.mp hab_c).trans (compare_eq_iff_eq.mp hbc_c))]
        exact revlexCompareAux_trans_lt a b c (i + 1) hab hbc
      · have := (compare_eq_iff_eq.mp hab_c) ▸ hbc_c; simp [this]
    · simp only [hab_c] at hab
      rcases hbc_c : compare (b[n-1-i]'(by omega) : ℕ) (c[n-1-i]'(by omega) : ℕ) with _ | _ | _
      · simp only [hbc_c] at hbc; cases hbc
      · have := (compare_eq_iff_eq.mp hbc_c).symm ▸ hab_c; simp [this]
      · have := compare_gt_iff_gt.mpr (lt_trans (compare_gt_iff_gt.mp hbc_c) (compare_gt_iff_gt.mp hab_c))
        simp [this]
  · next h => simp [h] at hab
termination_by n - i

private theorem revlexCompare_refl (a : Vector ℕ n) : revlexCompare a a = .eq :=
  revlexCompareAux_refl a 0

private theorem revlexCompare_swap (a b : Vector ℕ n) :
    (revlexCompare a b).swap = revlexCompare b a :=
  revlexCompareAux_swap a b 0

private theorem revlexCompare_eq (a b : Vector ℕ n) (h : revlexCompare a b = .eq) :
    a = b := by
  ext j : 1
  suffices ∀ i, i ≤ n → revlexCompareAux a b i = .eq from by
    have heq := revlexCompareAux_eq_at a b (n - 1 - j) (this (n - 1 - j) (by omega)) (by omega)
    convert heq using 2 <;> omega
  intro i hi
  induction i with
  | zero => exact h
  | succ k ih => exact revlexCompareAux_sub a b k (ih (by omega)) (by omega)

private theorem revlexCompare_trans_lt (a b c : Vector ℕ n)
    (hab : revlexCompare a b = .lt) (hbc : revlexCompare b c = .lt) :
    revlexCompare a c = .lt :=
  revlexCompareAux_trans_lt a b c 0 hab hbc

/-! ### compareExponents properties -/

theorem compareExponents_refl (ord : MonomialOrder) (a : Vector ℕ n) :
    compareExponents ord a a = .eq := by
  unfold compareExponents
  cases ord <;> simp [lexCompare_refl, revlexCompare_refl]

theorem compareExponents_swap (ord : MonomialOrder) (a b : Vector ℕ n) :
    (compareExponents ord a b).swap = compareExponents ord b a := by
  unfold compareExponents
  cases ord
  · exact lexCompare_swap a b
  · simp only
    have csw := compare_swap_eq (totalDeg a) (totalDeg b)
    cases hd : compare (totalDeg a) (totalDeg b) <;>
      simp only [Ordering.swap, hd] at csw ⊢ <;>
      simp only [← csw]
    exact lexCompare_swap a b
  · simp only
    have csw := compare_swap_eq (totalDeg a) (totalDeg b)
    cases hd : compare (totalDeg a) (totalDeg b) <;>
      simp only [Ordering.swap, hd] at csw ⊢ <;>
      simp only [← csw]
    exact revlexCompare_swap a b

theorem compareExponents_eq (ord : MonomialOrder) (a b : Vector ℕ n)
    (h : compareExponents ord a b = .eq) : a = b := by
  unfold compareExponents at h
  cases ord
  · exact lexCompare_eq a b h
  · rcases hd : compare (totalDeg a) (totalDeg b) with _ | _ | _
    · simp only [hd] at h; cases h
    · simp only [hd] at h; exact lexCompare_eq a b h
    · simp only [hd] at h; cases h
  · rcases hd : compare (totalDeg a) (totalDeg b) with _ | _ | _
    · simp only [hd] at h; cases h
    · simp only [hd] at h; exact revlexCompare_eq a b h
    · simp only [hd] at h; cases h

theorem compareExponents_trans_lt (ord : MonomialOrder) (a b c : Vector ℕ n)
    (hab : compareExponents ord a b = .lt) (hbc : compareExponents ord b c = .lt) :
    compareExponents ord a c = .lt := by
  unfold compareExponents at hab hbc ⊢
  cases ord
  · exact lexCompare_trans_lt a b c hab hbc
  · rcases hab_d : compare (totalDeg a) (totalDeg b) with _ | _ | _
    · simp only [hab_d] at hab
      rcases hbc_d : compare (totalDeg b) (totalDeg c) with _ | _ | _
      · simp [compare_lt_iff_lt.mpr (lt_trans (compare_lt_iff_lt.mp hab_d) (compare_lt_iff_lt.mp hbc_d))]
      · simp [(compare_eq_iff_eq.mp hbc_d) ▸ hab_d]
      · simp only [hbc_d] at hbc; cases hbc
    · simp only [hab_d] at hab
      rcases hbc_d : compare (totalDeg b) (totalDeg c) with _ | _ | _
      · simp [(compare_eq_iff_eq.mp hab_d) ▸ hbc_d]
      · simp only [hbc_d] at hbc
        simp [compare_eq_iff_eq.mpr ((compare_eq_iff_eq.mp hab_d).trans (compare_eq_iff_eq.mp hbc_d))]
        exact lexCompare_trans_lt a b c hab hbc
      · simp only [hbc_d] at hbc; cases hbc
    · simp only [hab_d] at hab; cases hab
  · rcases hab_d : compare (totalDeg a) (totalDeg b) with _ | _ | _
    · simp only [hab_d] at hab
      rcases hbc_d : compare (totalDeg b) (totalDeg c) with _ | _ | _
      · simp [compare_lt_iff_lt.mpr (lt_trans (compare_lt_iff_lt.mp hab_d) (compare_lt_iff_lt.mp hbc_d))]
      · simp [(compare_eq_iff_eq.mp hbc_d) ▸ hab_d]
      · simp only [hbc_d] at hbc; cases hbc
    · simp only [hab_d] at hab
      rcases hbc_d : compare (totalDeg b) (totalDeg c) with _ | _ | _
      · simp [(compare_eq_iff_eq.mp hab_d) ▸ hbc_d]
      · simp only [hbc_d] at hbc
        simp [compare_eq_iff_eq.mpr ((compare_eq_iff_eq.mp hab_d).trans (compare_eq_iff_eq.mp hbc_d))]
        exact revlexCompare_trans_lt a b c hab hbc
      · simp only [hbc_d] at hbc; cases hbc
    · simp only [hab_d] at hab; cases hab

/-! ### LinearOrder instance for `MonicMonomialNew` -/

variable {ord : MonomialOrder}

namespace MonicMonomialNew

/-- Compare two monic monomials using the specified monomial ordering. -/
private def cmpM (a b : MonicMonomialNew n ord) : Ordering :=
  compareExponents ord a.exponents b.exponents

private theorem cmpM_refl (a : MonicMonomialNew n ord) : cmpM a a = .eq :=
  compareExponents_refl ord _

private theorem cmpM_swap (a b : MonicMonomialNew n ord) :
    (cmpM a b).swap = cmpM b a :=
  compareExponents_swap ord _ _

private theorem cmpM_eq (a b : MonicMonomialNew n ord) (h : cmpM a b = .eq) : a = b :=
  MonicMonomialNew.ext (compareExponents_eq ord _ _ h)

private theorem cmpM_trans_lt (a b c : MonicMonomialNew n ord)
    (h1 : cmpM a b = .lt) (h2 : cmpM b c = .lt) : cmpM a c = .lt :=
  compareExponents_trans_lt ord _ _ _ h1 h2

private theorem cmpM_lt_of_gt {a b : MonicMonomialNew n ord} (h : cmpM a b = .gt) :
    cmpM b a = .lt := by
  have := cmpM_swap a b; rw [h] at this; exact this.symm

private theorem cmpM_gt_of_lt {a b : MonicMonomialNew n ord} (h : cmpM a b = .lt) :
    cmpM b a = .gt := by
  have := cmpM_swap a b; rw [h] at this; exact this.symm

instance : LE (MonicMonomialNew n ord) := ⟨fun a b => cmpM a b ≠ .gt⟩
instance : LT (MonicMonomialNew n ord) := ⟨fun a b => cmpM a b = .lt⟩

instance : DecidableRel (LE.le (α := MonicMonomialNew n ord)) := fun a b =>
  inferInstanceAs (Decidable (cmpM a b ≠ .gt))

instance : DecidableRel (LT.lt (α := MonicMonomialNew n ord)) := fun a b =>
  inferInstanceAs (Decidable (cmpM a b = .lt))

instance : PartialOrder (MonicMonomialNew n ord) where
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

instance instLinearOrder : LinearOrder (MonicMonomialNew n ord) where
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

end MonicMonomialNew

end Azurite
