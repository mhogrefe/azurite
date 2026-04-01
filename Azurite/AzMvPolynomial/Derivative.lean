/-
  Partial derivative for AzMvPolynomial with respect to a variable.

  Given a polynomial P and a variable v, ∂P/∂v differentiates each monomial:
  - If the exponent of v is 0, the term vanishes.
  - Otherwise, coefficient c becomes c * eᵥ, and eᵥ decrements by 1.

  Three implementation tiers (dispatched via typeclass):
  1. `pderivGeneral` — always safe; filters zeroes, re-sorts for non-lex orderings
  2. `pderivNoCancel` — for CharZero + NoZeroDivisors; no filtering needed
  3. `pderivLexVar0` — for CharZero + NoZeroDivisors + lex + var 0; no resort needed
-/
import Azurite.AzMvPolynomial.Basic
import Azurite.AzMvPolynomial.MonicMonomialOrder
import Azurite.AzMvPolynomial.ToString

namespace Azurite

open MonicMonomial Monomial AzMvPolynomial

variable {R : Type _} [Semiring R] [DecidableEq R]
         {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n]
         {ord : MonomialOrder}

/-! ### Monomial-level derivative -/

/-- Decrement the exponent of variable `v` in a monic monomial.
    Returns the new monic monomial (with `eᵥ - 1` at position `v`). -/
def MonicMonomial.decrExp (m : MonicMonomial σ ord) (j : Fin n) : MonicMonomial σ ord :=
  ⟨Vector.ofFn (fun i => if i = j then m.exponents[i] - 1 else m.exponents[i])⟩

/-- Differentiate a monomial with respect to variable index `j`.
    Returns `none` if the exponent is 0 (term vanishes),
    or `some (c * eⱼ, decremented monic)` otherwise.
    Returns `none` also if the new coefficient is zero (char p cancellation). -/
def Monomial.pderivAt (m : Monomial σ R ord) (j : Fin n) :
    Option (Monomial σ R ord) :=
  let e := m.monic.exponents[j]
  if he : e = 0 then none
  else
    let newCoeff := m.coeff.val * (↑e : R)
    if hc : newCoeff = 0 then none
    else some ⟨⟨newCoeff, hc⟩, m.monic.decrExp j⟩

omit [DecidableEq R] in
/-- Non-filtering variant: assumes `c * e ≠ 0` whenever `c ≠ 0` and `e > 0`.
    Suitable for CharZero + NoZeroDivisors. -/
def Monomial.pderivAtNoCancel [CharZero R] [NoZeroDivisors R]
    (m : Monomial σ R ord) (j : Fin n) :
    Option (Monomial σ R ord) :=
  let e := m.monic.exponents[j]
  if he : e = 0 then none
  else
    have hc : m.coeff.val * (↑e : R) ≠ 0 :=
      mul_ne_zero m.coeff.property (Nat.cast_ne_zero.mpr he)
    some ⟨⟨m.coeff.val * (↑e : R), hc⟩, m.monic.decrExp j⟩

/-! ### Sorting preservation -/

/-- `pderivAt` preserves the monic part ordering:
    if the result is `some`, its monic is `m.monic.decrExp j`. -/
theorem Monomial.pderivAt_monic {m : Monomial σ R ord} {j : Fin n}
    {m' : Monomial σ R ord} (h : m.pderivAt j = some m') :
    m'.monic = m.monic.decrExp j := by
  simp only [pderivAt] at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · injection h with h'; subst h'; rfl

omit [DecidableEq R] in
theorem Monomial.pderivAtNoCancel_monic [CharZero R] [NoZeroDivisors R]
    {m : Monomial σ R ord} {j : Fin n}
    {m' : Monomial σ R ord} (h : m.pderivAtNoCancel j = some m') :
    m'.monic = m.monic.decrExp j := by
  simp only [pderivAtNoCancel] at h
  split at h
  · contradiction
  · injection h with h'; subst h'; rfl

/-- Decrementing the same exponent position in monic monomials that both
    have a positive exponent at `j` preserves distinctness. -/
theorem MonicMonomial.decrExp_ne (j : Fin n)
    {a b : MonicMonomial σ ord}
    (hab : a ≠ b) (ha : a.exponents[j] > 0) (hb : b.exponents[j] > 0) :
    a.decrExp j ≠ b.decrExp j := by
  intro h
  apply hab; ext1; ext i hi
  simp only [decrExp, MonicMonomial.mk.injEq] at h
  have heq := congr_arg (fun v => v[i]) h
  simp only [Vector.getElem_ofFn] at heq
  by_cases hij : (⟨i, hi⟩ : Fin n) = j
  · have : i = j.val := Fin.val_eq_of_eq hij
    simp [this] at heq ha hb ⊢; omega
  · simp [hij] at heq; exact heq

/-- If `pderivAt` returns `some`, the original exponent was positive. -/
theorem Monomial.pderivAt_exp_pos {m : Monomial σ R ord} {j : Fin n}
    {m' : Monomial σ R ord} (h : m.pderivAt j = some m') :
    m.monic.exponents[j] > 0 := by
  simp only [pderivAt] at h
  split at h
  · contradiction
  · rename_i hne; exact Nat.pos_of_ne_zero hne

/-- Monic parts from `filterMap pderivAt` are pairwise distinct. -/
theorem pderivAt_monic_ne_of_sorted {j : Fin n}
    {l : List (Monomial σ R ord)}
    (hp : l.Pairwise (fun a b => a.monic > b.monic)) :
    (l.filterMap (Monomial.pderivAt · j)).Pairwise
      (fun a b => a.monic ≠ b.monic) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a t ih =>
    rw [List.pairwise_cons] at hp; rw [List.filterMap_cons]
    rcases ha : Monomial.pderivAt a j with _ | a'
    · exact ih hp.2
    · rw [List.pairwise_cons]; refine ⟨fun b hb => ?_, ih hp.2⟩
      obtain ⟨m', hm', hmap⟩ := List.mem_filterMap.mp hb
      rw [Monomial.pderivAt_monic ha, Monomial.pderivAt_monic hmap]
      exact MonicMonomial.decrExp_ne j (ne_of_gt (hp.1 m' hm'))
        (Monomial.pderivAt_exp_pos ha) (Monomial.pderivAt_exp_pos hmap)

/-! ### Polynomial-level derivative implementations -/

/-- General partial derivative: filters zero terms, re-sorts the result.
    Safe for any semiring and any monomial ordering. -/
def AzMvPolynomial.pderivGeneral (v : σ) (p : AzMvPolynomial σ R ord) :
    AzMvPolynomial σ R ord :=
  let j := Var.toFin v
  let terms := p.terms.toList.filterMap (Monomial.pderivAt · j)
  AzMvPolynomial.ofMonomials terms.toArray
    (by rw [List.toList_toArray]; exact pderivAt_monic_ne_of_sorted p.sorted)

omit [DecidableEq R] in
/-- If `pderivAtNoCancel` returns `some`, the original exponent was positive. -/
theorem Monomial.pderivAtNoCancel_exp_pos [CharZero R] [NoZeroDivisors R]
    {m : Monomial σ R ord} {j : Fin n}
    {m' : Monomial σ R ord} (h : m.pderivAtNoCancel j = some m') :
    m.monic.exponents[j] > 0 := by
  simp only [pderivAtNoCancel] at h
  split at h
  · contradiction
  · rename_i hne; exact Nat.pos_of_ne_zero hne

omit [DecidableEq R] in
/-- Monic parts from `filterMap pderivAtNoCancel` are pairwise distinct. -/
theorem pderivAtNoCancel_monic_ne_of_sorted [CharZero R] [NoZeroDivisors R]
    {j : Fin n}
    {l : List (Monomial σ R ord)}
    (hp : l.Pairwise (fun a b => a.monic > b.monic)) :
    (l.filterMap (Monomial.pderivAtNoCancel · j)).Pairwise
      (fun a b => a.monic ≠ b.monic) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a t ih =>
    rw [List.pairwise_cons] at hp; rw [List.filterMap_cons]
    rcases ha : Monomial.pderivAtNoCancel a j with _ | a'
    · exact ih hp.2
    · rw [List.pairwise_cons]; refine ⟨fun b hb => ?_, ih hp.2⟩
      obtain ⟨m', hm', hmap⟩ := List.mem_filterMap.mp hb
      rw [Monomial.pderivAtNoCancel_monic ha, Monomial.pderivAtNoCancel_monic hmap]
      exact MonicMonomial.decrExp_ne j (ne_of_gt (hp.1 m' hm'))
        (Monomial.pderivAtNoCancel_exp_pos ha) (Monomial.pderivAtNoCancel_exp_pos hmap)

omit [DecidableEq R] in
/-- No-cancellation variant: for CharZero + NoZeroDivisors.
    Still re-sorts for non-lex orderings. -/
def AzMvPolynomial.pderivNoCancel [CharZero R] [NoZeroDivisors R]
    (v : σ) (p : AzMvPolynomial σ R ord) : AzMvPolynomial σ R ord :=
  let j := Var.toFin v
  let terms := p.terms.toList.filterMap (Monomial.pderivAtNoCancel · j)
  AzMvPolynomial.ofMonomials terms.toArray
    (by rw [List.toList_toArray]; exact pderivAtNoCancel_monic_ne_of_sorted p.sorted)

/-- `lexCompareAux` depends only on elements at indices ≥ k. -/
private theorem lexCompareAux_ext {v1 v2 w1 w2 : Vector ℕ n} (k : ℕ)
    (h1 : ∀ j, k ≤ j → (hj : j < n) → v1[j]'hj = w1[j]'hj)
    (h2 : ∀ j, k ≤ j → (hj : j < n) → v2[j]'hj = w2[j]'hj) :
    MonomialOrder.lexCompareAux v1 v2 k = MonomialOrder.lexCompareAux w1 w2 k := by
  unfold MonomialOrder.lexCompareAux
  split
  · next hk =>
    rw [h1 k le_rfl hk, h2 k le_rfl hk]
    rcases compare (w1[k]'hk) (w2[k]'hk) with _ | _ | _
    · rfl
    · exact lexCompareAux_ext (k + 1)
        (fun j hj hj' => h1 j (by omega) hj')
        (fun j hj hj' => h2 j (by omega) hj')
    · rfl
  · rfl
termination_by n - k

/-- `decrExp 0` preserves strict lex ordering when both monomials have positive
    exponent at position 0. -/
private theorem MonicMonomial.decrExp_zero_preserves_lex_gt (hn : 0 < n)
    {a b : MonicMonomial σ (MonomialOrder.Lex)}
    (hab : a > b) (ha : a.exponents[0]'hn > 0)
    (hb : b.exponents[0]'hn > 0) :
    a.decrExp ⟨0, hn⟩ > b.decrExp ⟨0, hn⟩ := by
  show b.decrExp ⟨0, hn⟩ < a.decrExp ⟨0, hn⟩
  rw [← compare_lt_iff_lt]
  have hab' : compare b a = .lt := compare_lt_iff_lt.mpr hab
  simp only [compare] at hab' ⊢
  simp only [MonomialOrder.compareExponents, MonomialOrder.lexCompare] at hab' ⊢
  simp only [MonicMonomial.decrExp]
  unfold MonomialOrder.lexCompareAux
  simp only [hn, ↓reduceDIte, Vector.getElem_ofFn]
  simp only [show (⟨0, hn⟩ : Fin n) = ⟨0, hn⟩ from rfl, ite_true]
  unfold MonomialOrder.lexCompareAux at hab'
  simp only [hn, ↓reduceDIte] at hab'
  -- Now case-split on how b[0] compares to a[0]
  rcases hc : compare (b.exponents[0]'hn) (a.exponents[0]'hn) with _ | _ | _
  · -- b[0] < a[0] → (b[0]-1) < (a[0]-1)
    have : compare (b.exponents[0]'hn - 1) (a.exponents[0]'hn - 1) = .lt := by
      have := compare_lt_iff_lt.mp hc
      exact compare_lt_iff_lt.mpr (by omega)
    simp [this]
  · -- b[0] = a[0] → (b[0]-1) = (a[0]-1), rest continues
    have : compare (b.exponents[0]'hn - 1) (a.exponents[0]'hn - 1) = .eq := by
      have := compare_eq_iff_eq.mp hc
      exact compare_eq_iff_eq.mpr (by omega)
    simp [this, hc] at hab' ⊢
    exact lexCompareAux_ext 1
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
  · -- b[0] > a[0] → contradicts b < a
    simp [hc] at hab'

omit [DecidableEq R] in
/-- Lex-order preservation for filterMap of pderivAtNoCancel at position 0. -/
private theorem pderivAtNoCancel_sorted_lex [CharZero R] [NoZeroDivisors R]
    (hn : 0 < n)
    {l : List (Monomial σ R (.Lex))}
    (hp : l.Pairwise (fun a b => a.monic > b.monic)) :
    (l.filterMap (Monomial.pderivAtNoCancel · ⟨0, hn⟩)).Pairwise
      (fun a b => a.monic > b.monic) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a t ih =>
    rw [List.pairwise_cons] at hp; rw [List.filterMap_cons]
    rcases ha : Monomial.pderivAtNoCancel a ⟨0, hn⟩ with _ | a'
    · exact ih hp.2
    · rw [List.pairwise_cons]; refine ⟨fun b hb => ?_, ih hp.2⟩
      obtain ⟨m', hm', hmap⟩ := List.mem_filterMap.mp hb
      rw [Monomial.pderivAtNoCancel_monic ha, Monomial.pderivAtNoCancel_monic hmap]
      exact MonicMonomial.decrExp_zero_preserves_lex_gt hn
        (hp.1 m' hm')
        (Monomial.pderivAtNoCancel_exp_pos ha)
        (Monomial.pderivAtNoCancel_exp_pos hmap)

omit [DecidableEq R] in
/-- Optimized partial derivative w.r.t. variable 0 in lex order:
    for CharZero + NoZeroDivisors. No re-sorting needed because
    `decrExp 0` preserves lex ordering. -/
def AzMvPolynomial.pderivLexVar0 [CharZero R] [NoZeroDivisors R]
    (hn : 0 < n) (p : AzMvPolynomial σ R (.Lex)) : AzMvPolynomial σ R (.Lex) :=
  let j : Fin n := ⟨0, hn⟩
  let terms := p.terms.toList.filterMap (Monomial.pderivAtNoCancel · j)
  ⟨terms.toArray, by
    rw [List.toList_toArray]
    exact pderivAtNoCancel_sorted_lex hn p.sorted⟩

/-! ### Typeclass for auto-dispatch -/

/-- Typeclass providing the partial derivative implementation for `AzMvPolynomial`.
    Implementations must agree with `pderivGeneral` on coefficients. -/
class MvPolynomialDerivative (σ : Type _) {n : ℕ} [LinearOrder σ] [Var σ n]
    (R : Type _) [Semiring R] [DecidableEq R] (ord : MonomialOrder) where
  pderiv : σ → AzMvPolynomial σ R ord → AzMvPolynomial σ R ord

instance (priority := default) : MvPolynomialDerivative σ R ord where
  pderiv := AzMvPolynomial.pderivGeneral

instance (priority := high) [CharZero R] [NoZeroDivisors R] :
    MvPolynomialDerivative σ R ord where
  pderiv := AzMvPolynomial.pderivNoCancel

/-- Partial derivative of a multivariate polynomial with respect to a variable.
    Dispatches to `pderivNoCancel` for `CharZero + NoZeroDivisors` rings,
    and `pderivGeneral` otherwise. -/
def AzMvPolynomial.pderiv [MvPolynomialDerivative σ R ord]
    (v : σ) (p : AzMvPolynomial σ R ord) : AzMvPolynomial σ R ord :=
  MvPolynomialDerivative.pderiv v p

/-! ### Tests -/

section Tests
open AzMvPolynomial in

instance : Fact (3 ≤ 26) := ⟨by omega⟩

private def testPoly : AzMvPolynomial (AbcVar 3) ℤ .Lex :=
  AzMvPolynomial.ofMonomials #[
    ⟨⟨3, by decide⟩, ⟨Vector.mk #[2, 1, 0] rfl⟩⟩,
    ⟨⟨-2, by decide⟩, ⟨Vector.mk #[1, 0, 1] rfl⟩⟩,
    ⟨⟨5, by decide⟩, ⟨Vector.mk #[0, 0, 0] rfl⟩⟩
  ] (by native_decide)

private def a_var : AbcVar 3 := ⟨'a', by decide⟩
private def b_var : AbcVar 3 := ⟨'b', by decide⟩
private def c_var : AbcVar 3 := ⟨'c', by decide⟩

#guard toString testPoly == "3*a^2*b-2*a*c+5"
#guard toString (pderiv a_var testPoly) == "6*a*b-2*c"
#guard toString (pderiv b_var testPoly) == "3*a^2"
#guard toString (pderiv c_var testPoly) == "-2*a"
#guard toString (pderiv c_var (0 : AzMvPolynomial (AbcVar 3) ℤ .Lex)) == "0"
#guard toString (AzMvPolynomial.pderivLexVar0 (by omega : 0 < 3) testPoly) == "6*a*b-2*c"

end Tests

end Azurite
