import Azurite.AzMvPolynomial.Compare
import Mathlib.Order.Compare

/-!
# The `LinearOrder` on `AzMvPolynomial`

Lawfulness of the total-degree-then-lexicographic comparison of
`Azurite.AzMvPolynomial.Compare`: the `LinearOrder (AzMvPolynomial n R ord)`
instance (for linearly ordered coefficient semirings), in the house `AzInt`
style (`compare := compare` with `compare_eq_compareOfLessAndEq`), plus the
degree-domination corollaries `zero_le'` and `lt_of_totalDegree_lt`.

The comparison first compares *degree keys* (`0` for the zero polynomial,
`totalDegree + 1` otherwise), and on a tie scans the two descending,
normalized term lists together via `compareTerms` ("lex with implicit zeros").
Transitivity of `compareTerms` is threaded through the descending-sorted
invariant carried by every `AzMvPolynomial`.

(Inside this namespace `compare` on coefficients / monics / naturals must be
written `Ord.compare` — `AzMvPolynomial.compare` shadows the export.)
-/

namespace Azurite.AzMvPolynomial

variable {R : Type _} [Semiring R] [LinearOrder R] {n : ℕ} {ord : MonomialOrder}

/-! ### Definitional reductions of `compareTerms` -/

private theorem compareTerms_nil_nil :
    compareTerms ([] : List (Monomial n R ord)) [] = .eq := rfl

private theorem compareTerms_nil_cons (y : Monomial n R ord) (ys : List (Monomial n R ord)) :
    compareTerms [] (y :: ys) = Ord.compare (0 : R) y.coeff.val := rfl

private theorem compareTerms_cons_nil (x : Monomial n R ord) (xs : List (Monomial n R ord)) :
    compareTerms (x :: xs) [] = Ord.compare x.coeff.val (0 : R) := rfl

private theorem compareTerms_cons_cons (x : Monomial n R ord) (xs : List (Monomial n R ord))
    (y : Monomial n R ord) (ys : List (Monomial n R ord)) :
    compareTerms (x :: xs) (y :: ys) =
      match Ord.compare x.monic y.monic with
      | .gt => Ord.compare x.coeff.val (0 : R)
      | .lt => Ord.compare (0 : R) y.coeff.val
      | .eq =>
        match Ord.compare x.coeff.val y.coeff.val with
        | .eq => compareTerms xs ys
        | o => o := rfl

/-! ### Coefficient-sign helpers -/

private theorem coeff_neg_of_le {x : Monomial n R ord}
    (h : Ord.compare x.coeff.val (0 : R) ≠ .gt) : x.coeff.val < 0 := by
  rcases lt_trichotomy x.coeff.val (0 : R) with hlt | heq | hgt
  · exact hlt
  · exact absurd heq x.coeff.property
  · exact absurd (compare_gt_iff_gt.mpr hgt) h

private theorem coeff_pos_of_le {y : Monomial n R ord}
    (h : Ord.compare (0 : R) y.coeff.val ≠ .gt) : (0 : R) < y.coeff.val := by
  rcases lt_trichotomy (0 : R) y.coeff.val with hlt | heq | hgt
  · exact hlt
  · exact absurd heq.symm y.coeff.property
  · exact absurd (compare_gt_iff_gt.mpr hgt) h

private theorem compare_zero_ne_gt {c : R} (h : (0 : R) < c) :
    Ord.compare (0 : R) c ≠ .gt := by
  rw [compare_lt_iff_lt.mpr h]; decide

private theorem compare_ne_gt_of_neg {c : R} (h : c < 0) :
    Ord.compare c (0 : R) ≠ .gt := by
  rw [compare_lt_iff_lt.mpr h]; decide

/-! ### Laws of the term-list scan -/

private theorem compareTerms_self (a : List (Monomial n R ord)) :
    compareTerms a a = .eq := by
  induction a with
  | nil => rfl
  | cons x xs ih =>
    rw [compareTerms_cons_cons]
    simp only [compare_eq_iff_eq.mpr (rfl : x.monic = x.monic),
      compare_eq_iff_eq.mpr (rfl : x.coeff.val = x.coeff.val)]
    exact ih

private theorem compareTerms_swap (a b : List (Monomial n R ord)) :
    compareTerms b a = (compareTerms a b).swap := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons y ys =>
      rw [compareTerms_cons_nil, compareTerms_nil_cons]
      exact (compare_swap_eq _ _).symm
  | cons x xs ih =>
    cases b with
    | nil =>
      rw [compareTerms_nil_cons, compareTerms_cons_nil]
      exact (compare_swap_eq _ _).symm
    | cons y ys =>
      rw [compareTerms_cons_cons, compareTerms_cons_cons]
      rcases hxy : Ord.compare x.monic y.monic with _ | _ | _
      · have hyx : Ord.compare y.monic x.monic = .gt := by rw [← compare_swap_eq, hxy]; rfl
        simp only [hyx]
        exact (compare_swap_eq _ _).symm
      · have hyx : Ord.compare y.monic x.monic = .eq := by rw [← compare_swap_eq, hxy]; rfl
        simp only [hyx]
        rcases hc : Ord.compare x.coeff.val y.coeff.val with _ | _ | _
        · have hcs : Ord.compare y.coeff.val x.coeff.val = .gt := by
            rw [← compare_swap_eq, hc]; rfl
          simp only [hcs]; rfl
        · have hcs : Ord.compare y.coeff.val x.coeff.val = .eq := by
            rw [← compare_swap_eq, hc]; rfl
          simp only [hcs]; exact ih ys
        · have hcs : Ord.compare y.coeff.val x.coeff.val = .lt := by
            rw [← compare_swap_eq, hc]; rfl
          simp only [hcs]; rfl
      · have hyx : Ord.compare y.monic x.monic = .lt := by rw [← compare_swap_eq, hxy]; rfl
        simp only [hyx]
        exact (compare_swap_eq _ _).symm

private theorem compareTerms_eq_imp (a b : List (Monomial n R ord))
    (h : compareTerms a b = .eq) : a = b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons y ys =>
      rw [compareTerms_nil_cons] at h
      exact absurd (compare_eq_iff_eq.mp h).symm y.coeff.property
  | cons x xs ih =>
    cases b with
    | nil =>
      rw [compareTerms_cons_nil] at h
      exact absurd (compare_eq_iff_eq.mp h) x.coeff.property
    | cons y ys =>
      rw [compareTerms_cons_cons] at h
      rcases hxy : Ord.compare x.monic y.monic with _ | _ | _ <;> simp only [hxy] at h
      · exact absurd (compare_eq_iff_eq.mp h).symm y.coeff.property
      · rcases hc : Ord.compare x.coeff.val y.coeff.val with _ | _ | _ <;> simp only [hc] at h
        · exact absurd h (by decide)
        · have hcoeff : x.coeff.val = y.coeff.val := compare_eq_iff_eq.mp hc
          have hmonic : x.monic = y.monic := compare_eq_iff_eq.mp hxy
          rw [ih ys h]
          exact congrArg (· :: ys) (Monomial.ext' x y hcoeff hmonic)
        · exact absurd h (by decide)
      · exact absurd (compare_eq_iff_eq.mp h) x.coeff.property

private theorem compareTerms_trans :
    ∀ (a b c : List (Monomial n R ord)),
      a.Pairwise (fun p q => p.monic > q.monic) →
      b.Pairwise (fun p q => p.monic > q.monic) →
      c.Pairwise (fun p q => p.monic > q.monic) →
      compareTerms a b ≠ .gt → compareTerms b c ≠ .gt → compareTerms a c ≠ .gt
  | [], [], [], _, _, _, _, _ => by rw [compareTerms_nil_nil]; decide
  | [], [], _ :: _, _, _, _, _, h2 => h2
  | [], _ :: _, [], _, _, _, _, _ => by rw [compareTerms_nil_nil]; decide
  | [], y :: ys, z :: zs, _, _, _, h1, h2 => by
    rw [compareTerms_nil_cons] at h1
    rw [compareTerms_cons_cons] at h2
    rw [compareTerms_nil_cons]
    have hcy_pos := coeff_pos_of_le h1
    rcases hyz : Ord.compare y.monic z.monic with _ | _ | _
    · simp only [hyz] at h2; exact h2
    · rcases hcyz : Ord.compare y.coeff.val z.coeff.val with _ | _ | _ <;>
        simp only [hyz, hcyz] at h2
      · exact compare_zero_ne_gt (lt_trans hcy_pos (compare_lt_iff_lt.mp hcyz))
      · exact compare_zero_ne_gt (by rw [← compare_eq_iff_eq.mp hcyz]; exact hcy_pos)
      · exact absurd rfl h2
    · simp only [hyz] at h2
      exact absurd hcy_pos (not_lt.mpr (le_of_lt (coeff_neg_of_le h2)))
  | x :: xs, [], [], _, _, _, h1, _ => h1
  | x :: xs, [], z :: zs, _, _, _, h1, h2 => by
    rw [compareTerms_cons_nil] at h1
    rw [compareTerms_nil_cons] at h2
    rw [compareTerms_cons_cons]
    have hcx_neg := coeff_neg_of_le h1
    have hcz_pos := coeff_pos_of_le h2
    rcases hmxz : Ord.compare x.monic z.monic with _ | _ | _
    · exact compare_zero_ne_gt hcz_pos
    · simp only [compare_lt_iff_lt.mpr (hcx_neg.trans hcz_pos)]; decide
    · exact compare_ne_gt_of_neg hcx_neg
  | x :: xs, y :: ys, [], _, _, _, h1, h2 => by
    rw [compareTerms_cons_nil] at h2
    rw [compareTerms_cons_cons] at h1
    rw [compareTerms_cons_nil]
    have hcy_neg := coeff_neg_of_le h2
    rcases hxy : Ord.compare x.monic y.monic with _ | _ | _
    · simp only [hxy] at h1
      exact absurd (coeff_pos_of_le h1) (not_lt.mpr (le_of_lt hcy_neg))
    · rcases hcxy : Ord.compare x.coeff.val y.coeff.val with _ | _ | _ <;>
        simp only [hxy, hcxy] at h1
      · exact compare_ne_gt_of_neg (lt_trans (compare_lt_iff_lt.mp hcxy) hcy_neg)
      · exact compare_ne_gt_of_neg (by rw [compare_eq_iff_eq.mp hcxy]; exact hcy_neg)
      · exact absurd rfl h1
    · simp only [hxy] at h1
      exact compare_ne_gt_of_neg (coeff_neg_of_le h1)
  | x :: xs, y :: ys, z :: zs, ha, hb, hc, h1, h2 => by
    rw [compareTerms_cons_cons] at h1 h2
    rw [compareTerms_cons_cons]
    rcases hxy : Ord.compare x.monic y.monic with _ | _ | _
    · -- x.monic < y.monic
      simp only [hxy] at h1
      have hcy_pos := coeff_pos_of_le h1
      rcases hyz : Ord.compare y.monic z.monic with _ | _ | _
      · simp only [hyz] at h2
        have hmxz : Ord.compare x.monic z.monic = .lt :=
          compare_lt_iff_lt.mpr (lt_trans (compare_lt_iff_lt.mp hxy) (compare_lt_iff_lt.mp hyz))
        simp only [hmxz]; exact h2
      · have hmxz : Ord.compare x.monic z.monic = .lt :=
          compare_lt_iff_lt.mpr
            (lt_of_lt_of_eq (compare_lt_iff_lt.mp hxy) (compare_eq_iff_eq.mp hyz))
        simp only [hmxz]
        rcases hcyz : Ord.compare y.coeff.val z.coeff.val with _ | _ | _ <;>
          simp only [hyz, hcyz] at h2
        · exact compare_zero_ne_gt (lt_trans hcy_pos (compare_lt_iff_lt.mp hcyz))
        · exact compare_zero_ne_gt (by rw [← compare_eq_iff_eq.mp hcyz]; exact hcy_pos)
        · exact absurd rfl h2
      · simp only [hyz] at h2
        exact absurd hcy_pos (not_lt.mpr (le_of_lt (coeff_neg_of_le h2)))
    · -- x.monic = y.monic
      simp only [hxy] at h1
      rcases hyz : Ord.compare y.monic z.monic with _ | _ | _
      · -- y.monic < z.monic
        simp only [hyz] at h2
        have hmxz : Ord.compare x.monic z.monic = .lt :=
          compare_lt_iff_lt.mpr
            (lt_of_eq_of_lt (compare_eq_iff_eq.mp hxy) (compare_lt_iff_lt.mp hyz))
        simp only [hmxz]; exact h2
      · -- y.monic = z.monic
        have hmxz : Ord.compare x.monic z.monic = .eq :=
          compare_eq_iff_eq.mpr ((compare_eq_iff_eq.mp hxy).trans (compare_eq_iff_eq.mp hyz))
        simp only [hmxz]
        rcases hcxy : Ord.compare x.coeff.val y.coeff.val with _ | _ | _ <;>
          simp only [hcxy] at h1
        · rcases hcyz : Ord.compare y.coeff.val z.coeff.val with _ | _ | _ <;>
            simp only [hyz, hcyz] at h2
          · simp only [compare_lt_iff_lt.mpr
              (lt_trans (compare_lt_iff_lt.mp hcxy) (compare_lt_iff_lt.mp hcyz))]; decide
          · simp only [compare_lt_iff_lt.mpr
              (lt_of_lt_of_eq (compare_lt_iff_lt.mp hcxy) (compare_eq_iff_eq.mp hcyz))]; decide
          · exact absurd rfl h2
        · rcases hcyz : Ord.compare y.coeff.val z.coeff.val with _ | _ | _ <;>
            simp only [hyz, hcyz] at h2
          · simp only [compare_lt_iff_lt.mpr
              (lt_of_eq_of_lt (compare_eq_iff_eq.mp hcxy) (compare_lt_iff_lt.mp hcyz))]; decide
          · have hcxz : Ord.compare x.coeff.val z.coeff.val = .eq :=
              compare_eq_iff_eq.mpr
                ((compare_eq_iff_eq.mp hcxy).trans (compare_eq_iff_eq.mp hcyz))
            simp only [hcxz]
            exact compareTerms_trans xs ys zs (List.pairwise_cons.mp ha).2
              (List.pairwise_cons.mp hb).2 (List.pairwise_cons.mp hc).2 h1 h2
          · exact absurd rfl h2
        · exact absurd rfl h1
      · -- y.monic > z.monic
        simp only [hyz] at h2
        have hcy_neg := coeff_neg_of_le h2
        have hmxz : Ord.compare x.monic z.monic = .gt :=
          compare_gt_iff_gt.mpr
            (lt_of_lt_of_eq (compare_gt_iff_gt.mp hyz) (compare_eq_iff_eq.mp hxy).symm)
        simp only [hmxz]
        rcases hcxy : Ord.compare x.coeff.val y.coeff.val with _ | _ | _ <;>
          simp only [hcxy] at h1
        · exact compare_ne_gt_of_neg (lt_trans (compare_lt_iff_lt.mp hcxy) hcy_neg)
        · exact compare_ne_gt_of_neg (by rw [compare_eq_iff_eq.mp hcxy]; exact hcy_neg)
        · exact absurd rfl h1
    · -- x.monic > y.monic
      simp only [hxy] at h1
      have hcx_neg := coeff_neg_of_le h1
      rcases hyz : Ord.compare y.monic z.monic with _ | _ | _
      · -- y.monic < z.monic
        simp only [hyz] at h2
        have hcz_pos := coeff_pos_of_le h2
        rcases hmxz : Ord.compare x.monic z.monic with _ | _ | _
        · exact compare_zero_ne_gt hcz_pos
        · simp only [compare_lt_iff_lt.mpr (hcx_neg.trans hcz_pos)]; decide
        · exact compare_ne_gt_of_neg hcx_neg
      · -- y.monic = z.monic
        have hmxz : Ord.compare x.monic z.monic = .gt :=
          compare_gt_iff_gt.mpr
            (lt_of_eq_of_lt (compare_eq_iff_eq.mp hyz).symm (compare_gt_iff_gt.mp hxy))
        simp only [hmxz]; exact compare_ne_gt_of_neg hcx_neg
      · -- y.monic > z.monic
        have hmxz : Ord.compare x.monic z.monic = .gt :=
          compare_gt_iff_gt.mpr
            (lt_trans (compare_gt_iff_gt.mp hyz) (compare_gt_iff_gt.mp hxy))
        simp only [hmxz]; exact compare_ne_gt_of_neg hcx_neg
  termination_by a b c _ _ _ _ _ => a.length + b.length + c.length
  decreasing_by simp_wf; omega

/-! ### Reductions of the full comparison -/

private theorem compare_of_degreeKey_lt {p q : AzMvPolynomial n R ord}
    (h : degreeKey p < degreeKey q) : compare p q = .lt := by
  unfold compare; rw [compare_lt_iff_lt.mpr h]

private theorem compare_of_degreeKey_gt {p q : AzMvPolynomial n R ord}
    (h : degreeKey q < degreeKey p) : compare p q = .gt := by
  unfold compare; rw [compare_gt_iff_gt.mpr h]

private theorem compare_of_degreeKey_eq {p q : AzMvPolynomial n R ord}
    (h : degreeKey p = degreeKey q) :
    compare p q = compareTerms p.terms.toList q.terms.toList := by
  unfold compare; rw [compare_eq_iff_eq.mpr h]

/-! ### Laws of the full comparison -/

private theorem compare_self' (p : AzMvPolynomial n R ord) : compare p p = .eq := by
  rw [compare_of_degreeKey_eq rfl]; exact compareTerms_self _

private theorem compare_swap' (p q : AzMvPolynomial n R ord) :
    compare q p = (compare p q).swap := by
  rcases lt_trichotomy (degreeKey p) (degreeKey q) with h | h | h
  · rw [compare_of_degreeKey_lt h, compare_of_degreeKey_gt h]; rfl
  · rw [compare_of_degreeKey_eq h, compare_of_degreeKey_eq h.symm]
    exact compareTerms_swap _ _
  · rw [compare_of_degreeKey_gt h, compare_of_degreeKey_lt h]; rfl

private theorem eq_of_compare_eq {p q : AzMvPolynomial n R ord}
    (h : compare p q = .eq) : p = q := by
  rcases lt_trichotomy (degreeKey p) (degreeKey q) with hd | hd | hd
  · rw [compare_of_degreeKey_lt hd] at h; exact absurd h (by decide)
  · rw [compare_of_degreeKey_eq hd] at h
    have hlist := compareTerms_eq_imp _ _ h
    obtain ⟨pt, ph⟩ := p
    obtain ⟨qt, qh⟩ := q
    have hpt : pt = qt := Array.ext' hlist
    subst hpt; rfl
  · rw [compare_of_degreeKey_gt hd] at h; exact absurd h (by decide)

private theorem compare_trans' {p q r : AzMvPolynomial n R ord}
    (h1 : compare p q ≠ .gt) (h2 : compare q r ≠ .gt) : compare p r ≠ .gt := by
  rcases lt_trichotomy (degreeKey p) (degreeKey q) with hpq | hpq | hpq <;>
    rcases lt_trichotomy (degreeKey q) (degreeKey r) with hqr | hqr | hqr
  · rw [compare_of_degreeKey_lt (hpq.trans hqr)]; decide
  · rw [compare_of_degreeKey_lt (lt_of_lt_of_eq hpq hqr)]; decide
  · exact absurd (compare_of_degreeKey_gt hqr) h2
  · rw [compare_of_degreeKey_lt (lt_of_eq_of_lt hpq hqr)]; decide
  · rw [compare_of_degreeKey_eq (hpq.trans hqr)]
    exact compareTerms_trans _ _ _ p.sorted q.sorted r.sorted
      (fun hx => h1 (by rw [compare_of_degreeKey_eq hpq]; exact hx))
      (fun hx => h2 (by rw [compare_of_degreeKey_eq hqr]; exact hx))
  · exact absurd (compare_of_degreeKey_gt hqr) h2
  · exact absurd (compare_of_degreeKey_gt hpq) h1
  · exact absurd (compare_of_degreeKey_gt hpq) h1
  · exact absurd (compare_of_degreeKey_gt hpq) h1

/-! ### The `LinearOrder` instance -/

instance : LinearOrder (AzMvPolynomial n R ord) where
  le_refl p := by
    show compare p p ≠ .gt
    rw [compare_self']; simp
  le_trans _ _ _ := compare_trans'
  le_antisymm p q h1 h2 := by
    have h2' : (compare p q).swap ≠ .gt := by rw [← compare_swap']; exact h2
    apply eq_of_compare_eq
    rcases h : compare p q with _ | _ | _
    · rw [h] at h2'; exact absurd rfl h2'
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
            rw [show compare p q = .lt from h2] at h; exact absurd h (by simp)),
        if_pos (eq_of_compare_eq h)]
    · rw [if_neg (show ¬ p < q from fun h2 => by
            rw [show compare p q = .lt from h2] at h; exact absurd h (by simp)),
        if_neg (fun h2 => by
          subst h2; rw [compare_self'] at h; exact absurd h (by simp))]

/-! ### Degree domination -/

omit [LinearOrder R] in
private theorem toList_nil_of_degreeKey_zero {p : AzMvPolynomial n R ord}
    (h : degreeKey p = 0) : p.terms.toList = [] := by
  rw [degreeKey] at h
  by_cases he : p.terms.isEmpty = true
  · exact Array.toList_eq_nil_iff.mpr (Array.isEmpty_iff.mp he)
  · rw [if_neg he] at h; omega

omit [LinearOrder R] in
private theorem degreeKey_of_ne {p : AzMvPolynomial n R ord}
    (hp : p.terms.isEmpty = false) : degreeKey p = p.totalDegree + 1 := by
  rw [degreeKey, if_neg (by rw [hp]; decide)]

/-- The zero polynomial is the least element. -/
theorem zero_le' (p : AzMvPolynomial n R ord) : (0 : AzMvPolynomial n R ord) ≤ p := by
  show compare 0 p ≠ .gt
  have hz : degreeKey (0 : AzMvPolynomial n R ord) = 0 := rfl
  rcases Nat.eq_zero_or_pos (degreeKey p) with h | h
  · have hkey : degreeKey (0 : AzMvPolynomial n R ord) = degreeKey p := by rw [hz, h]
    rw [compare_of_degreeKey_eq hkey]
    have h0 : (0 : AzMvPolynomial n R ord).terms.toList = [] := rfl
    rw [h0, toList_nil_of_degreeKey_zero h, compareTerms_nil_nil]
    decide
  · have hlt : degreeKey (0 : AzMvPolynomial n R ord) < degreeKey p := by rw [hz]; exact h
    rw [compare_of_degreeKey_lt hlt]; decide

/-- Strictly smaller total degree means strictly smaller polynomial (for a
nonzero left-hand side): total degree dominates the term scan entirely. -/
theorem lt_of_totalDegree_lt {p q : AzMvPolynomial n R ord} (hp : p ≠ 0)
    (h : p.totalDegree < q.totalDegree) : p < q := by
  show compare p q = .lt
  have hpne : p.terms.isEmpty = false := by
    cases hb : p.terms.isEmpty
    · rfl
    · exfalso; apply hp
      have hpe : p.terms = #[] := Array.isEmpty_iff.mp hb
      obtain ⟨pt, ph⟩ := p
      simp only at hpe
      subst hpe; rfl
  have hqne : q.terms.isEmpty = false := by
    cases hb : q.terms.isEmpty
    · rfl
    · exfalso
      have hq0 : q.totalDegree = 0 := by
        rw [totalDegree, Array.isEmpty_iff.mp hb]; rfl
      omega
  exact compare_of_degreeKey_lt (by rw [degreeKey_of_ne hpne, degreeKey_of_ne hqne]; omega)

end Azurite.AzMvPolynomial
