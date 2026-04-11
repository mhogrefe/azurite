/-
  Conversion from `AzPolynomial` to `AzMvPolynomial`.

  Given a univariate polynomial `p : AzPolynomial R`, a number of variables
  `n`, an index `i : Fin n`, and a monomial ordering `ord`, we construct
  `p.toAzMvPolynomial i ord : AzMvPolynomial n R ord`.

  Each nonzero coefficient `aₖ` at position `k` becomes a monomial with
  coefficient `aₖ` and monic part `xᵢ^k`.
-/
import Azurite.AzMvPolynomial.Basic
import Azurite.AzPolynomial.Basic
import Mathlib.Algebra.BigOperators.Fin

namespace Azurite
open AzMvPolynomial MonomialOrder

variable {R : Type _} [Semiring R] [DecidableEq R]
  {n : ℕ} {ord : MonomialOrder}

/-! ### MonicMonomial.ofVarPow -/

/-- The monic monomial `xᵢ^k`: exponent `k` at position `i`, all others zero. -/
def MonicMonomial.ofVarPow (i : Fin n) (k : ℕ) : MonicMonomial n ord :=
  ⟨Vector.ofFn (fun j => if i = j then k else 0)⟩

@[simp] theorem MonicMonomial.ofVarPow_exponent (i : Fin n) (k : ℕ) (j : Fin n) :
    (MonicMonomial.ofVarPow i k : MonicMonomial n ord).exponents[j] =
      if i = j then k else 0 := by
  simp [MonicMonomial.ofVarPow]

@[simp] theorem MonicMonomial.ofVarPow_zero (i : Fin n) :
    (MonicMonomial.ofVarPow i 0 : MonicMonomial n ord) = 1 := by
  ext1; ext j hj; simp [MonicMonomial.ofVarPow]

@[simp] theorem MonicMonomial.ofVarPow_one (i : Fin n) :
    (MonicMonomial.ofVarPow i 1 : MonicMonomial n ord) = MonicMonomial.ofVar i := by
  ext1; simp [MonicMonomial.ofVarPow, MonicMonomial.ofVar]

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
theorem totalDeg_ofVarPow (i : Fin n) (k : ℕ) :
    totalDeg (MonicMonomial.ofVarPow i k : MonicMonomial n ord).exponents = k := by
  unfold totalDeg MonicMonomial.ofVarPow
  simp only [Vector.toArray_ofFn]
  rw [← Array.foldl_toList, Array.toList_ofFn, nat_foldl_add_eq_sum,
      List.sum_ofFn, Finset.sum_ite_eq]
  simp

/-! ### Strict monotonicity of ofVarPow -/

omit [Semiring R] [DecidableEq R] in
private theorem lexCompareAux_ofVarPow (i : Fin n) (j k : ℕ) (hjk : j < k)
    (pos : ℕ) (hpos : pos ≤ i.val) :
    lexCompareAux
      (MonicMonomial.ofVarPow i j : MonicMonomial n ord).exponents
      (MonicMonomial.ofVarPow i k : MonicMonomial n ord).exponents
      pos = .lt := by
  unfold lexCompareAux
  have hlt : pos < n := by omega
  simp only [hlt, ↓reduceDIte, MonicMonomial.ofVarPow, Vector.getElem_ofFn]
  by_cases hv : i.val = pos
  · have : i = ⟨pos, hlt⟩ := Fin.ext hv
    simp [this, compare_lt_iff_lt.mpr hjk]
  · have hne : i ≠ ⟨pos, hlt⟩ := fun h => hv (Fin.val_eq_of_eq h)
    simp [hne]
    exact lexCompareAux_ofVarPow i j k hjk (pos + 1) (by omega)
termination_by n - pos

omit [Semiring R] [DecidableEq R] in
/-- `ofVarPow i k > ofVarPow i j` when `k > j` in any standard monomial ordering. -/
theorem MonicMonomial.ofVarPow_strictMono (i : Fin n) :
    StrictMono (fun k => (MonicMonomial.ofVarPow i k : MonicMonomial n ord)) := by
  intro j k hjk
  show MonicMonomial.ofVarPow i j < MonicMonomial.ofVarPow i k
  change compareExponents ord
    (MonicMonomial.ofVarPow i j).exponents
    (MonicMonomial.ofVarPow i k).exponents = .lt
  unfold compareExponents
  cases ord
  · exact lexCompareAux_ofVarPow i j k hjk 0 (Nat.zero_le _)
  · simp only [totalDeg_ofVarPow, compare_lt_iff_lt.mpr hjk]
  · simp only [totalDeg_ofVarPow, compare_lt_iff_lt.mpr hjk]

/-! ### Efficient direct construction -/

/-- Build the terms array by iterating from the end of the coefficient array
    toward the beginning. Each nonzero coefficient `coeffs[idx]` produces a
    monomial term `coeffs[idx] * xᵢ^idx`. The resulting array is in
    descending order because we process from high degree to low. -/
def buildTermsDesc (i : Fin n) (coeffs : Array R)
    (fuel : ℕ) (idx : ℕ) (acc : Array (Monomial n R ord)) :
    Array (Monomial n R ord) :=
  match fuel with
  | 0 => acc
  | fuel + 1 =>
    let c := (coeffs[idx]?).getD 0
    let acc' := if hc : c = 0 then acc
                else acc.push ⟨⟨c, hc⟩, MonicMonomial.ofVarPow i idx⟩
    if idx = 0 then acc'
    else buildTermsDesc i coeffs fuel (idx - 1) acc'

omit [DecidableEq R] in
/-- Pushing a term to the end preserves the pairwise sorted property
    when the new term is smaller than all existing terms. -/
private theorem pairwise_push {l : List (Monomial n R ord)} {m : Monomial n R ord}
    (hsorted : l.Pairwise (fun a b => a.monic > b.monic))
    (hbound : ∀ x ∈ l, x.monic > m.monic) :
    (l ++ [m]).Pairwise (fun a b => a.monic > b.monic) := by
  rw [List.pairwise_append]
  exact ⟨hsorted, List.pairwise_singleton _ _, fun x hx y hy => by
    simp at hy; exact hy ▸ hbound x hx⟩

/-- The sorted invariant: `buildTermsDesc` produces terms in strictly
    descending monomial order. -/
private theorem buildTermsDesc_sorted (i : Fin n) (coeffs : Array R)
    (fuel idx : ℕ) (acc : Array (Monomial n R ord))
    (hacc_sorted : acc.toList.Pairwise (fun a b => a.monic > b.monic))
    (hacc_bound : ∀ m ∈ acc.toList, m.monic > MonicMonomial.ofVarPow i idx) :
    (buildTermsDesc i coeffs fuel idx acc).toList.Pairwise
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
        exact buildTermsDesc_sorted i coeffs fuel (idx - 1) acc
          hacc_sorted (fun m hm => lt_trans
            (MonicMonomial.ofVarPow_strictMono i hidx') (hacc_bound m hm))
      · -- nonzero coefficient: acc gets a new term
        next hc =>
        have hpush_sorted :
            (acc.push ⟨⟨_, hc⟩, MonicMonomial.ofVarPow i idx⟩).toList.Pairwise
              (fun a b => a.monic > b.monic) := by
          rw [Array.toList_push]
          exact pairwise_push hacc_sorted (fun x hx => hacc_bound x hx)
        have hpush_bound : ∀ m ∈ (acc.push
            ⟨⟨_, hc⟩, MonicMonomial.ofVarPow i idx⟩).toList,
            m.monic > MonicMonomial.ofVarPow i (idx - 1) := by
          intro m hm
          rw [Array.toList_push, List.mem_append, List.mem_singleton] at hm
          rcases hm with hm | hm
          · exact lt_trans (MonicMonomial.ofVarPow_strictMono i hidx') (hacc_bound m hm)
          · simp at hm; exact hm ▸ MonicMonomial.ofVarPow_strictMono i hidx'
        exact buildTermsDesc_sorted i coeffs fuel (idx - 1) _ hpush_sorted hpush_bound

/-- Convert an `AzPolynomial R` to an `AzMvPolynomial n R ord` using
    variable index `i : Fin n`.

Each nonzero coefficient `p.coeffs[k]` becomes a term `p.coeffs[k] * xᵢ^k`.
The terms are constructed in O(n) time by iterating through the coefficients
once from highest degree to lowest. -/
def AzPolynomial.toAzMvPolynomial {R : Type _} [Semiring R] [DecidableEq R]
    {n : ℕ} (i : Fin n) (ord : MonomialOrder := .Degrevlex)
    (p : AzPolynomial R) : AzMvPolynomial n R ord :=
  if h : p.coeffs.size = 0 then ⟨#[], List.Pairwise.nil⟩
  else
    let idx := p.coeffs.size - 1
    let terms := buildTermsDesc i p.coeffs p.coeffs.size idx #[]
    ⟨terms, buildTermsDesc_sorted i p.coeffs p.coeffs.size idx #[]
      List.Pairwise.nil (by simp)⟩

end Azurite
