/-
  Partial derivative for `AzMvPolynomialNew` with respect to a variable
  index `j : Fin n`.

  Three implementation tiers (dispatched via typeclass):
  1. `pderivGeneral`       — always safe; filters zeroes, re-sorts
  2. `pderivNoCancel`      — CharZero + NoZeroDivisors; no filtering needed
  3. `pderivLexVar0`       — CharZero + NoZeroDivisors + lex + var 0; no resort
-/
import Azurite.AzMvPolynomial.New.Basic
import Azurite.AzMvPolynomial.New.MonicMonomialOrder

namespace Azurite

open MonicMonomialNew MonomialNew AzMvPolynomialNew

variable {R : Type _} [Semiring R] [DecidableEq R]
         {n : ℕ} {ord : MonomialOrder}

/-! ### Monomial-level derivative -/

/-- Decrement the exponent of variable `j` in a monic monomial. -/
def MonicMonomialNew.decrExp (m : MonicMonomialNew n ord) (j : Fin n) :
    MonicMonomialNew n ord :=
  ⟨Vector.ofFn (fun i => if i = j then m.exponents[i] - 1 else m.exponents[i])⟩

/-- Differentiate a monomial with respect to variable index `j`. -/
def MonomialNew.pderivAt (m : MonomialNew n R ord) (j : Fin n) :
    Option (MonomialNew n R ord) :=
  let e := m.monic.exponents[j]
  if he : e = 0 then none
  else
    let newCoeff := m.coeff.val * (↑e : R)
    if hc : newCoeff = 0 then none
    else some ⟨⟨newCoeff, hc⟩, m.monic.decrExp j⟩

omit [DecidableEq R] in
/-- Non-filtering variant for CharZero + NoZeroDivisors. -/
def MonomialNew.pderivAtNoCancel [CharZero R] [NoZeroDivisors R]
    (m : MonomialNew n R ord) (j : Fin n) :
    Option (MonomialNew n R ord) :=
  let e := m.monic.exponents[j]
  if he : e = 0 then none
  else
    have hc : m.coeff.val * (↑e : R) ≠ 0 :=
      mul_ne_zero m.coeff.property (Nat.cast_ne_zero.mpr he)
    some ⟨⟨m.coeff.val * (↑e : R), hc⟩, m.monic.decrExp j⟩

/-! ### Sorting preservation -/

theorem MonomialNew.pderivAt_monic {m : MonomialNew n R ord} {j : Fin n}
    {m' : MonomialNew n R ord} (h : m.pderivAt j = some m') :
    m'.monic = m.monic.decrExp j := by
  simp only [pderivAt] at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · injection h with h'; subst h'; rfl

omit [DecidableEq R] in
theorem MonomialNew.pderivAtNoCancel_monic [CharZero R] [NoZeroDivisors R]
    {m : MonomialNew n R ord} {j : Fin n}
    {m' : MonomialNew n R ord} (h : m.pderivAtNoCancel j = some m') :
    m'.monic = m.monic.decrExp j := by
  simp only [pderivAtNoCancel] at h
  split at h
  · contradiction
  · injection h with h'; subst h'; rfl

theorem MonicMonomialNew.decrExp_ne (j : Fin n)
    {a b : MonicMonomialNew n ord}
    (hab : a ≠ b) (ha : a.exponents[j] > 0) (hb : b.exponents[j] > 0) :
    a.decrExp j ≠ b.decrExp j := by
  intro h
  apply hab; ext1; ext i hi
  simp only [decrExp, MonicMonomialNew.mk.injEq] at h
  have heq := congr_arg (fun v => v[i]) h
  simp only [Vector.getElem_ofFn] at heq
  by_cases hij : (⟨i, hi⟩ : Fin n) = j
  · have : i = j.val := Fin.val_eq_of_eq hij
    simp [this] at heq ha hb ⊢; omega
  · simp [hij] at heq; exact heq

theorem MonomialNew.pderivAt_exp_pos {m : MonomialNew n R ord} {j : Fin n}
    {m' : MonomialNew n R ord} (h : m.pderivAt j = some m') :
    m.monic.exponents[j] > 0 := by
  simp only [pderivAt] at h
  split at h
  · contradiction
  · rename_i hne; exact Nat.pos_of_ne_zero hne

theorem pderivAt_monic_ne_of_sorted_new {j : Fin n}
    {l : List (MonomialNew n R ord)}
    (hp : l.Pairwise (fun a b => a.monic > b.monic)) :
    (l.filterMap (MonomialNew.pderivAt · j)).Pairwise
      (fun a b => a.monic ≠ b.monic) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a t ih =>
    rw [List.pairwise_cons] at hp; rw [List.filterMap_cons]
    rcases ha : MonomialNew.pderivAt a j with _ | a'
    · exact ih hp.2
    · rw [List.pairwise_cons]; refine ⟨fun b hb => ?_, ih hp.2⟩
      obtain ⟨m', hm', hmap⟩ := List.mem_filterMap.mp hb
      rw [MonomialNew.pderivAt_monic ha, MonomialNew.pderivAt_monic hmap]
      exact MonicMonomialNew.decrExp_ne j (ne_of_gt (hp.1 m' hm'))
        (MonomialNew.pderivAt_exp_pos ha) (MonomialNew.pderivAt_exp_pos hmap)

/-! ### Polynomial-level derivative implementations -/

/-- General partial derivative: filters zero terms, re-sorts the result. -/
def AzMvPolynomialNew.pderivGeneral (j : Fin n) (p : AzMvPolynomialNew n R ord) :
    AzMvPolynomialNew n R ord :=
  let terms := p.terms.toList.filterMap (MonomialNew.pderivAt · j)
  AzMvPolynomialNew.ofMonomials terms.toArray
    (by rw [List.toList_toArray]; exact pderivAt_monic_ne_of_sorted_new p.sorted)

omit [DecidableEq R] in
theorem MonomialNew.pderivAtNoCancel_exp_pos [CharZero R] [NoZeroDivisors R]
    {m : MonomialNew n R ord} {j : Fin n}
    {m' : MonomialNew n R ord} (h : m.pderivAtNoCancel j = some m') :
    m.monic.exponents[j] > 0 := by
  simp only [pderivAtNoCancel] at h
  split at h
  · contradiction
  · rename_i hne; exact Nat.pos_of_ne_zero hne

omit [DecidableEq R] in
theorem pderivAtNoCancel_monic_ne_of_sorted_new [CharZero R] [NoZeroDivisors R]
    {j : Fin n}
    {l : List (MonomialNew n R ord)}
    (hp : l.Pairwise (fun a b => a.monic > b.monic)) :
    (l.filterMap (MonomialNew.pderivAtNoCancel · j)).Pairwise
      (fun a b => a.monic ≠ b.monic) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a t ih =>
    rw [List.pairwise_cons] at hp; rw [List.filterMap_cons]
    rcases ha : MonomialNew.pderivAtNoCancel a j with _ | a'
    · exact ih hp.2
    · rw [List.pairwise_cons]; refine ⟨fun b hb => ?_, ih hp.2⟩
      obtain ⟨m', hm', hmap⟩ := List.mem_filterMap.mp hb
      rw [MonomialNew.pderivAtNoCancel_monic ha, MonomialNew.pderivAtNoCancel_monic hmap]
      exact MonicMonomialNew.decrExp_ne j (ne_of_gt (hp.1 m' hm'))
        (MonomialNew.pderivAtNoCancel_exp_pos ha) (MonomialNew.pderivAtNoCancel_exp_pos hmap)

omit [DecidableEq R] in
/-- No-cancellation variant: for CharZero + NoZeroDivisors. -/
def AzMvPolynomialNew.pderivNoCancel [CharZero R] [NoZeroDivisors R]
    (j : Fin n) (p : AzMvPolynomialNew n R ord) : AzMvPolynomialNew n R ord :=
  let terms := p.terms.toList.filterMap (MonomialNew.pderivAtNoCancel · j)
  AzMvPolynomialNew.ofMonomials terms.toArray
    (by rw [List.toList_toArray]; exact pderivAtNoCancel_monic_ne_of_sorted_new p.sorted)

/-- `lexCompareAux` depends only on elements at indices ≥ k. -/
private theorem lexCompareAux_ext_new {v1 v2 w1 w2 : Vector ℕ n} (k : ℕ)
    (h1 : ∀ j, k ≤ j → (hj : j < n) → v1[j]'hj = w1[j]'hj)
    (h2 : ∀ j, k ≤ j → (hj : j < n) → v2[j]'hj = w2[j]'hj) :
    MonomialOrder.lexCompareAux v1 v2 k = MonomialOrder.lexCompareAux w1 w2 k := by
  unfold MonomialOrder.lexCompareAux
  split
  · next hk =>
    rw [h1 k le_rfl hk, h2 k le_rfl hk]
    rcases compare (w1[k]'hk) (w2[k]'hk) with _ | _ | _
    · rfl
    · exact lexCompareAux_ext_new (k + 1)
        (fun j hj hj' => h1 j (by omega) hj')
        (fun j hj hj' => h2 j (by omega) hj')
    · rfl
  · rfl
termination_by n - k

/-- `decrExp 0` preserves strict lex ordering when both monomials have positive
    exponent at position 0. -/
private theorem MonicMonomialNew.decrExp_zero_preserves_lex_gt (hn : 0 < n)
    {a b : MonicMonomialNew n (MonomialOrder.Lex)}
    (hab : a > b) (ha : a.exponents[0]'hn > 0)
    (hb : b.exponents[0]'hn > 0) :
    a.decrExp ⟨0, hn⟩ > b.decrExp ⟨0, hn⟩ := by
  show b.decrExp ⟨0, hn⟩ < a.decrExp ⟨0, hn⟩
  rw [← compare_lt_iff_lt]
  have hab' : compare b a = .lt := compare_lt_iff_lt.mpr hab
  simp only [compare] at hab' ⊢
  simp only [MonomialOrder.compareExponents, MonomialOrder.lexCompare] at hab' ⊢
  simp only [MonicMonomialNew.decrExp]
  unfold MonomialOrder.lexCompareAux
  simp only [hn, ↓reduceDIte, Vector.getElem_ofFn]
  simp only [show (⟨0, hn⟩ : Fin n) = ⟨0, hn⟩ from rfl, ite_true]
  unfold MonomialOrder.lexCompareAux at hab'
  simp only [hn, ↓reduceDIte] at hab'
  rcases hc : compare (b.exponents[0]'hn) (a.exponents[0]'hn) with _ | _ | _
  · have : compare (b.exponents[0]'hn - 1) (a.exponents[0]'hn - 1) = .lt := by
      have := compare_lt_iff_lt.mp hc
      exact compare_lt_iff_lt.mpr (by omega)
    simp [this]
  · have : compare (b.exponents[0]'hn - 1) (a.exponents[0]'hn - 1) = .eq := by
      have := compare_eq_iff_eq.mp hc
      exact compare_eq_iff_eq.mpr (by omega)
    simp [this, hc] at hab' ⊢
    exact lexCompareAux_ext_new 1
      (fun j hj hj' => by
        simp only [Vector.getElem_ofFn]
        have : ¬(⟨j, hj'⟩ : Fin n) = ⟨0, hn⟩ := by
          simp only [Fin.mk.injEq]; omega
        simp [this])
      (fun j hj hj' => by
        simp only [Vector.getElem_ofFn]
        have : ¬(⟨j, hj'⟩ : Fin n) = ⟨0, hn⟩ := by
          simp only [Fin.mk.injEq]; omega
        simp [this])
      |>.symm.trans hab'
  · simp [hc] at hab'

omit [DecidableEq R] in
private theorem pderivAtNoCancel_sorted_lex_new [CharZero R] [NoZeroDivisors R]
    (hn : 0 < n)
    {l : List (MonomialNew n R (.Lex))}
    (hp : l.Pairwise (fun a b => a.monic > b.monic)) :
    (l.filterMap (MonomialNew.pderivAtNoCancel · ⟨0, hn⟩)).Pairwise
      (fun a b => a.monic > b.monic) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a t ih =>
    rw [List.pairwise_cons] at hp; rw [List.filterMap_cons]
    rcases ha : MonomialNew.pderivAtNoCancel a ⟨0, hn⟩ with _ | a'
    · exact ih hp.2
    · rw [List.pairwise_cons]; refine ⟨fun b hb => ?_, ih hp.2⟩
      obtain ⟨m', hm', hmap⟩ := List.mem_filterMap.mp hb
      rw [MonomialNew.pderivAtNoCancel_monic ha, MonomialNew.pderivAtNoCancel_monic hmap]
      exact MonicMonomialNew.decrExp_zero_preserves_lex_gt hn
        (hp.1 m' hm')
        (MonomialNew.pderivAtNoCancel_exp_pos ha)
        (MonomialNew.pderivAtNoCancel_exp_pos hmap)

omit [DecidableEq R] in
/-- Optimized partial derivative w.r.t. variable 0 in lex order. -/
def AzMvPolynomialNew.pderivLexVar0 [CharZero R] [NoZeroDivisors R]
    (hn : 0 < n) (p : AzMvPolynomialNew n R (.Lex)) : AzMvPolynomialNew n R (.Lex) :=
  let j : Fin n := ⟨0, hn⟩
  let terms := p.terms.toList.filterMap (MonomialNew.pderivAtNoCancel · j)
  ⟨terms.toArray, by
    rw [List.toList_toArray]
    exact pderivAtNoCancel_sorted_lex_new hn p.sorted⟩

/-! ### Typeclass for auto-dispatch -/

/-- Typeclass providing the partial derivative implementation. -/
class MvPolynomialDerivativeNew (n : ℕ) (R : Type _) [Semiring R] [DecidableEq R]
    (ord : MonomialOrder) where
  pderiv : Fin n → AzMvPolynomialNew n R ord → AzMvPolynomialNew n R ord

instance (priority := default) : MvPolynomialDerivativeNew n R ord where
  pderiv := AzMvPolynomialNew.pderivGeneral

instance (priority := high) [CharZero R] [NoZeroDivisors R] :
    MvPolynomialDerivativeNew n R ord where
  pderiv := AzMvPolynomialNew.pderivNoCancel

/-- Partial derivative w.r.t. a variable index. -/
def AzMvPolynomialNew.pderiv [MvPolynomialDerivativeNew n R ord]
    (j : Fin n) (p : AzMvPolynomialNew n R ord) : AzMvPolynomialNew n R ord :=
  MvPolynomialDerivativeNew.pderiv j p

end Azurite
