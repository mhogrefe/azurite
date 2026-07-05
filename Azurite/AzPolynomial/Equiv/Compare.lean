import Azurite.AzPolynomial.Compare
import Azurite.AzPolynomial.Equiv.Basic
import Mathlib.Order.Compare

/-!
# The `LinearOrder` on `AzPolynomial`

Lawfulness of the degree-then-top-down-lexicographic comparison of
`Azurite.AzPolynomial.Compare`: the `LinearOrder (AzPolynomial R)` instance
(for linearly ordered coefficient semirings), in the house `AzInt` style
(`compare := compare` with `compare_eq_compareOfLessAndEq`), plus the
degree-domination corollaries `zero_le'` and `lt_of_natDegree_lt`.

(Inside this namespace `compare` on coefficients must be written
`Ord.compare` — `AzPolynomial.compare` shadows the export.)
-/

namespace Azurite.AzPolynomial

variable {R : Type _} [Semiring R] [LinearOrder R]

/-! ### Laws of the top-down scan -/

private theorem compareTopDown_self (a : Array R) (k : ℕ) :
    compareTopDown a a k = .eq := by
  induction k with
  | zero => rfl
  | succ m ih =>
    rw [compareTopDown, compare_eq_iff_eq.mpr rfl]
    exact ih

private theorem compareTopDown_swap (a b : Array R) (k : ℕ) :
    compareTopDown b a k = (compareTopDown a b k).swap := by
  induction k with
  | zero => rfl
  | succ m ih =>
    rw [compareTopDown, compareTopDown]
    rcases lt_trichotomy (a.getD m 0) (b.getD m 0) with h | h | h
    · rw [compare_lt_iff_lt.mpr h, compare_gt_iff_gt.mpr h]
      rfl
    · rw [compare_eq_iff_eq.mpr h, compare_eq_iff_eq.mpr h.symm]
      exact ih
    · rw [compare_gt_iff_gt.mpr h, compare_lt_iff_lt.mpr h]
      rfl

private theorem getD_eq_of_compareTopDown_eq {a b : Array R} {k : ℕ}
    (h : compareTopDown a b k = .eq) :
    ∀ i, i < k → a.getD i 0 = b.getD i 0 := by
  induction k with
  | zero => omega
  | succ m ih =>
    rw [compareTopDown] at h
    rcases hm : Ord.compare (a.getD m 0) (b.getD m 0) with _ | _ | _ <;> rw [hm] at h
    · exact absurd h (by simp)
    · intro i hi
      rcases Nat.lt_or_ge i m with him | him
      · exact ih h i him
      · have hieq : i = m := by omega
        subst hieq
        exact compare_eq_iff_eq.mp hm
    · exact absurd h (by simp)

private theorem compareTopDown_trans {a b c : Array R} {k : ℕ}
    (h1 : compareTopDown a b k ≠ .gt) (h2 : compareTopDown b c k ≠ .gt) :
    compareTopDown a c k ≠ .gt := by
  induction k with
  | zero => simp [compareTopDown]
  | succ m ih =>
    rw [compareTopDown] at h1 h2 ⊢
    rcases lt_trichotomy (a.getD m 0) (b.getD m 0) with hab | hab | hab <;>
      rcases lt_trichotomy (b.getD m 0) (c.getD m 0) with hbc | hbc | hbc
    · rw [compare_lt_iff_lt.mpr (hab.trans hbc)]
      simp
    · rw [compare_lt_iff_lt.mpr (hbc ▸ hab)]
      simp
    · rw [compare_gt_iff_gt.mpr hbc] at h2
      exact absurd rfl h2
    · rw [hab, compare_lt_iff_lt.mpr hbc]
      simp
    · rw [compare_eq_iff_eq.mpr (hab.trans hbc)]
      rw [compare_eq_iff_eq.mpr hab] at h1
      rw [compare_eq_iff_eq.mpr hbc] at h2
      exact ih h1 h2
    · rw [compare_gt_iff_gt.mpr hbc] at h2
      exact absurd rfl h2
    · rw [compare_gt_iff_gt.mpr hab] at h1
      exact absurd rfl h1
    · rw [compare_gt_iff_gt.mpr hab] at h1
      exact absurd rfl h1
    · rw [compare_gt_iff_gt.mpr hab] at h1
      exact absurd rfl h1

/-! ### Laws of the full comparison -/

private theorem compare_self' (p : AzPolynomial R) : compare p p = .eq := by
  rw [compare, if_neg (by omega), if_neg (by omega)]
  exact compareTopDown_self _ _

private theorem compare_swap' (p q : AzPolynomial R) :
    compare q p = (compare p q).swap := by
  rcases lt_trichotomy p.coeffs.size q.coeffs.size with h | h | h
  · rw [show compare p q = .lt from by rw [compare, if_pos h],
      show compare q p = .gt from by rw [compare, if_neg (by omega), if_pos h]]
    rfl
  · rw [show compare p q = compareTopDown p.coeffs q.coeffs p.coeffs.size from by
        rw [compare, if_neg (by omega), if_neg (by omega)],
      show compare q p = compareTopDown q.coeffs p.coeffs q.coeffs.size from by
        rw [compare, if_neg (by omega), if_neg (by omega)],
      h, compareTopDown_swap]
  · rw [show compare p q = .gt from by rw [compare, if_neg (by omega), if_pos h],
      show compare q p = .lt from by rw [compare, if_pos h]]
    rfl

private theorem eq_of_compare_eq {p q : AzPolynomial R} (h : compare p q = .eq) :
    p = q := by
  rw [compare] at h
  rcases lt_trichotomy p.coeffs.size q.coeffs.size with hs | hs | hs
  · rw [if_pos hs] at h
    exact absurd h (by simp)
  · rw [if_neg (by omega), if_neg (by omega)] at h
    apply AzPolynomial.ext
    apply Array.ext hs
    intro i hi _
    have h2 := getD_eq_of_compareTopDown_eq h i hi
    rwa [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem (by omega)] at h2
  · rw [if_neg (by omega), if_pos hs] at h
    exact absurd h (by simp)

private theorem compare_trans' {p q r : AzPolynomial R}
    (h1 : compare p q ≠ .gt) (h2 : compare q r ≠ .gt) : compare p r ≠ .gt := by
  rcases lt_trichotomy p.coeffs.size q.coeffs.size with hpq | hpq | hpq <;>
    rcases lt_trichotomy q.coeffs.size r.coeffs.size with hqr | hqr | hqr
  · rw [compare, if_pos (by omega)]; simp
  · rw [compare, if_pos (by omega)]; simp
  · exfalso; exact h2 (by rw [compare, if_neg (by omega), if_pos (by omega)])
  · rw [compare, if_pos (by omega)]; simp
  · -- equal sizes throughout: the top-down scans compose
    rw [compare, if_neg (by omega), if_neg (by omega)]
    have h1' : compareTopDown p.coeffs q.coeffs p.coeffs.size ≠ .gt := fun hx =>
      h1 (by rw [compare, if_neg (by omega), if_neg (by omega)]; exact hx)
    have h2' : compareTopDown q.coeffs r.coeffs p.coeffs.size ≠ .gt := fun hx =>
      h2 (by rw [compare, if_neg (by omega), if_neg (by omega), ← hpq]; exact hx)
    exact compareTopDown_trans h1' h2'
  · exfalso; exact h2 (by rw [compare, if_neg (by omega), if_pos (by omega)])
  · exfalso; exact h1 (by rw [compare, if_neg (by omega), if_pos (by omega)])
  · exfalso; exact h1 (by rw [compare, if_neg (by omega), if_pos (by omega)])
  · exfalso; exact h1 (by rw [compare, if_neg (by omega), if_pos (by omega)])

/-! ### The `LinearOrder` instance -/

instance : LinearOrder (AzPolynomial R) where
  le_refl p := by
    show compare p p ≠ .gt
    rw [compare_self']
    simp
  le_trans _ _ _ := compare_trans'
  le_antisymm p q h1 h2 := by
    have h2' : (compare p q).swap ≠ .gt := by
      rw [← compare_swap']
      exact h2
    apply eq_of_compare_eq
    rcases h : compare p q with _ | _ | _
    · rw [h] at h2'
      exact absurd rfl h2'
    · rfl
    · exact absurd h h1
  le_total p q := by
    show compare p q ≠ .gt ∨ compare q p ≠ .gt
    rw [compare_swap' p q]
    rcases compare p q with _ | _ | _ <;> simp
  lt_iff_le_not_ge p q := by
    show compare p q = .lt ↔ compare p q ≠ .gt ∧ ¬ compare q p ≠ .gt
    rw [compare_swap' p q]
    rcases compare p q with _ | _ | _ <;> simp
  toDecidableLE := inferInstance
  toDecidableEq := inferInstance
  toDecidableLT := inferInstance
  min_def := fun _ _ => rfl
  max_def := fun _ _ => rfl
  compare := compare
  compare_eq_compareOfLessAndEq p q := by
    rw [compareOfLessAndEq]
    rcases h : compare p q with _ | _ | _
    · rw [if_pos (show p < q from h)]
    · rw [if_neg (show ¬ p < q from fun h2 => by
          rw [show compare p q = .lt from h2] at h
          exact absurd h (by simp)),
        if_pos (eq_of_compare_eq h)]
    · rw [if_neg (show ¬ p < q from fun h2 => by
          rw [show compare p q = .lt from h2] at h
          exact absurd h (by simp)),
        if_neg (fun h2 => by
          subst h2
          rw [compare_self'] at h
          exact absurd h (by simp))]

/-! ### Degree domination -/

/-- The zero polynomial is the least element. -/
theorem zero_le' (p : AzPolynomial R) : (0 : AzPolynomial R) ≤ p := by
  show compare 0 p ≠ .gt
  have hz : (0 : AzPolynomial R).coeffs.size = 0 := rfl
  rcases Nat.eq_zero_or_pos p.coeffs.size with h | h
  · rw [compare, if_neg (by omega), if_neg (by omega), hz]
    simp [compareTopDown]
  · rw [compare, if_pos (by omega)]
    simp

/-- Strictly smaller degree means strictly smaller polynomial (for a nonzero
right-hand side): the degree dominates the coefficients entirely. -/
theorem lt_of_natDegree_lt {p q : AzPolynomial R} (hq : q ≠ 0)
    (h : p.natDegree < q.natDegree) : p < q := by
  show compare p q = .lt
  have hqs : q.coeffs.size ≠ 0 := by
    intro h0
    apply hq
    apply AzPolynomial.ext
    rw [Array.eq_empty_of_size_eq_zero h0]
    rfl
  have hd : p.natDegree = p.coeffs.size - 1 := rfl
  have hd2 : q.natDegree = q.coeffs.size - 1 := rfl
  rw [compare, if_pos (by omega)]

end Azurite.AzPolynomial
