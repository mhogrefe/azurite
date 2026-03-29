import Azurite.AzMvPolynomial.MonicMonomialOrder
import Azurite.AzMvPolynomial.Basic
import Azurite.AzPolynomial.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Conversion from AzPolynomial to AzMvPolynomial

Given a univariate polynomial `p : AzPolynomial R`, a variable type `σ` with `n` variables,
a specific variable `v : σ`, and a monomial ordering `ord`, we construct
`p.toAzMvPolynomial v : AzMvPolynomial σ R ord`.

Each nonzero coefficient `aᵢ` at position `i` becomes a monomial with
coefficient `aᵢ` and monic part `v^i`.

This corresponds to one direction of Mathlib's `MvPolynomial.pUnitAlgEquiv.symm`
(when `σ` has a single element).
-/

namespace Azurite
open AzMvPolynomial MonomialOrder

variable {R : Type _} [Semiring R] [DecidableEq R]
  {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n] {ord : MonomialOrder}

/-! ### MonicMonomial.ofVarPow -/

/-- The monic monomial `v^k`: exponent `k` at position `v`, all others zero. -/
def MonicMonomial.ofVarPow (v : σ) (k : ℕ) : MonicMonomial σ ord :=
  ⟨Vector.ofFn (fun i => if Var.toFin v = i then k else 0)⟩

@[simp] theorem MonicMonomial.ofVarPow_exponent (v : σ) (k : ℕ) (i : Fin n) :
    (MonicMonomial.ofVarPow v k : MonicMonomial σ ord).exponents[i] =
      if Var.toFin v = i then k else 0 := by
  simp [MonicMonomial.ofVarPow]

@[simp] theorem MonicMonomial.ofVarPow_zero (v : σ) :
    (MonicMonomial.ofVarPow v 0 : MonicMonomial σ ord) = 1 := by
  ext1; ext i hi; simp [MonicMonomial.ofVarPow]

@[simp] theorem MonicMonomial.ofVarPow_one (v : σ) :
    (MonicMonomial.ofVarPow v 1 : MonicMonomial σ ord) = MonicMonomial.ofVar v := by
  ext1; simp [ofVarPow, MonicMonomial.ofVar]

/-! ### totalDeg of ofVarPow -/

omit [Semiring R] [DecidableEq R] in
private theorem nat_foldl_add_eq_sum (l : List ℕ) :
    l.foldl (· + ·) 0 = l.sum := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.foldl_cons, List.sum_cons, Nat.zero_add]
    rw [← ih]; clear ih
    induction as generalizing a with
    | nil => simp
    | cons b bs ih =>
      simp only [List.foldl_cons, Nat.zero_add]
      rw [ih (a + b), ih b]; omega

omit [Semiring R] [DecidableEq R] in
theorem totalDeg_ofVarPow (v : σ) (k : ℕ) :
    totalDeg (MonicMonomial.ofVarPow v k : MonicMonomial σ ord).exponents = k := by
  unfold totalDeg MonicMonomial.ofVarPow
  simp only [Vector.toArray_ofFn]
  rw [← Array.foldl_toList, Array.toList_ofFn, nat_foldl_add_eq_sum,
      List.sum_ofFn, Finset.sum_ite_eq]
  simp

/-! ### Strict monotonicity of ofVarPow -/

omit [Semiring R] [DecidableEq R] in
private theorem lexCompareAux_ofVarPow (v : σ) (j k : ℕ) (hjk : j < k)
    (pos : ℕ) (hpos : pos ≤ (Var.toFin v).val) :
    lexCompareAux
      (MonicMonomial.ofVarPow v j : MonicMonomial σ ord).exponents
      (MonicMonomial.ofVarPow v k : MonicMonomial σ ord).exponents
      pos = .lt := by
  unfold lexCompareAux
  have hlt : pos < n := by omega
  simp only [hlt, ↓reduceDIte, MonicMonomial.ofVarPow, Vector.getElem_ofFn]
  by_cases hv : (Var.toFin v).val = pos
  · have : Var.toFin v = ⟨pos, hlt⟩ := Fin.ext hv
    simp [this, compare_lt_iff_lt.mpr hjk]
  · have hne : Var.toFin v ≠ ⟨pos, hlt⟩ := fun h => hv (Fin.val_eq_of_eq h)
    simp [hne]
    exact lexCompareAux_ofVarPow v j k hjk (pos + 1) (by omega)
termination_by n - pos

omit [Semiring R] [DecidableEq R] in
/-- `ofVarPow v k > ofVarPow v j` when `k > j` in any standard monomial ordering. -/
theorem MonicMonomial.ofVarPow_strictMono (v : σ) :
    StrictMono (fun k => (MonicMonomial.ofVarPow v k : MonicMonomial σ ord)) := by
  intro j k hjk
  show MonicMonomial.ofVarPow v j < MonicMonomial.ofVarPow v k
  change compareExponents ord
    (MonicMonomial.ofVarPow v j).exponents
    (MonicMonomial.ofVarPow v k).exponents = .lt
  unfold compareExponents
  cases ord
  · exact lexCompareAux_ofVarPow v j k hjk 0 (Nat.zero_le _)
  · simp only [totalDeg_ofVarPow, compare_lt_iff_lt.mpr hjk]
  · simp only [totalDeg_ofVarPow, compare_lt_iff_lt.mpr hjk]

/-! ### Efficient direct construction -/

/-- Build the terms array by iterating from the end of the coefficient array
    toward the beginning. Each nonzero coefficient `coeffs[idx]` produces a
    monomial term `coeffs[idx] * v^idx`. The resulting array is in descending
    order because we process from high degree to low. -/
def buildTermsDesc (v : σ) (coeffs : Array R)
    (fuel : ℕ) (idx : ℕ) (acc : Array (Monomial σ R ord)) :
    Array (Monomial σ R ord) :=
  match fuel with
  | 0 => acc
  | fuel + 1 =>
    let c := (coeffs[idx]?).getD 0
    let acc' := if hc : c = 0 then acc
                else acc.push ⟨⟨c, hc⟩, MonicMonomial.ofVarPow v idx⟩
    if idx = 0 then acc'
    else buildTermsDesc v coeffs fuel (idx - 1) acc'

omit [DecidableEq R] in
/-- Pushing a term to the end preserves the pairwise sorted property
    when the new term is smaller than all existing terms. -/
private theorem pairwise_push {l : List (Monomial σ R ord)} {m : Monomial σ R ord}
    (hsorted : l.Pairwise (fun a b => a.monic > b.monic))
    (hbound : ∀ x ∈ l, x.monic > m.monic) :
    (l ++ [m]).Pairwise (fun a b => a.monic > b.monic) := by
  rw [List.pairwise_append]
  exact ⟨hsorted, List.pairwise_singleton _ _, fun x hx y hy => by
    simp at hy; exact hy ▸ hbound x hx⟩

/-- The sorted invariant: `buildTermsDesc` produces terms in strictly descending
    monomial order. -/
private theorem buildTermsDesc_sorted (v : σ) (coeffs : Array R)
    (fuel idx : ℕ) (acc : Array (Monomial σ R ord))
    (hacc_sorted : acc.toList.Pairwise (fun a b => a.monic > b.monic))
    (hacc_bound : ∀ m ∈ acc.toList, m.monic > MonicMonomial.ofVarPow v idx) :
    (buildTermsDesc v coeffs fuel idx acc).toList.Pairwise
      (fun a b => a.monic > b.monic) := by
  match fuel with
  | 0 => exact hacc_sorted
  | fuel + 1 =>
    unfold buildTermsDesc
    simp only
    split -- on idx = 0
    · -- idx = 0, this is the last step
      split -- on c = 0
      · exact hacc_sorted
      · next hc =>
        rw [Array.toList_push]
        exact pairwise_push hacc_sorted (fun x hx => hacc_bound x hx)
    · -- idx > 0, recurse
      next hidx =>
      have hidx' : idx - 1 < idx := by omega
      split -- on c = 0
      · -- zero coefficient: acc unchanged
        exact buildTermsDesc_sorted v coeffs fuel (idx - 1) acc
          hacc_sorted (fun m hm => lt_trans
            (MonicMonomial.ofVarPow_strictMono v hidx') (hacc_bound m hm))
      · -- nonzero coefficient: acc gets a new term
        next hc =>
        have hpush_sorted : (acc.push ⟨⟨_, hc⟩, MonicMonomial.ofVarPow v idx⟩).toList.Pairwise
            (fun a b => a.monic > b.monic) := by
          rw [Array.toList_push]
          exact pairwise_push hacc_sorted (fun x hx => hacc_bound x hx)
        have hpush_bound : ∀ m ∈ (acc.push ⟨⟨_, hc⟩, MonicMonomial.ofVarPow v idx⟩).toList,
            m.monic > MonicMonomial.ofVarPow v (idx - 1) := by
          intro m hm
          rw [Array.toList_push, List.mem_append, List.mem_singleton] at hm
          rcases hm with hm | hm
          · exact lt_trans (MonicMonomial.ofVarPow_strictMono v hidx') (hacc_bound m hm)
          · simp at hm; exact hm ▸ MonicMonomial.ofVarPow_strictMono v hidx'
        exact buildTermsDesc_sorted v coeffs fuel (idx - 1) _ hpush_sorted hpush_bound

/-- Convert an `AzPolynomial R` to an `AzMvPolynomial σ R ord` using variable `v`.

Each nonzero coefficient `p.coeffs[i]` becomes a term `p.coeffs[i] * v^i`.
The terms are constructed in O(n) time by iterating through the coefficients
once from highest degree to lowest. -/
def AzPolynomial.toAzMvPolynomial {R : Type _} [Semiring R] [DecidableEq R]
    {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n]
    (v : σ) (ord : MonomialOrder := .Degrevlex)
    (p : AzPolynomial R) : AzMvPolynomial σ R ord :=
  if h : p.coeffs.size = 0 then ⟨#[], List.Pairwise.nil⟩
  else
    let idx := p.coeffs.size - 1
    let terms := buildTermsDesc v p.coeffs p.coeffs.size idx #[]
    ⟨terms, buildTermsDesc_sorted v p.coeffs p.coeffs.size idx #[]
      List.Pairwise.nil (by simp)⟩

/-! ### Guards -/

section Guards

private def mkPoly (cs : Array ℤ) (h : cs.back? ≠ some 0) : AzPolynomial ℤ := ⟨cs, h⟩

-- Use AbcVar 3 with variable 'a'
private instance : Fact ((3 : ℕ) ≤ 26) := ⟨by decide⟩
private abbrev testVar : AbcVar 3 := AbcVar.ofIndex (by decide) 0

-- Zero polynomial → zero multivariate polynomial
#guard (AzPolynomial.zero.toAzMvPolynomial testVar :
  AzMvPolynomial (AbcVar 3) ℤ).numTerms = 0

-- Constant 5 → one term
#guard ((mkPoly #[5] (by decide)).toAzMvPolynomial testVar).numTerms = 1

-- 2 + 3x → two terms
#guard ((mkPoly #[2, 3] (by decide)).toAzMvPolynomial testVar).numTerms = 2

-- 1 + 0x + 4x^2 → two terms (zero coefficient skipped)
#guard ((mkPoly #[1, 0, 4] (by decide)).toAzMvPolynomial testVar).numTerms = 2

end Guards

end Azurite
