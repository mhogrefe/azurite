import Azurite.AzMvPolynomial.Vars
import Azurite.AzMvPolynomial.Equiv.Basic
import Mathlib.Algebra.MvPolynomial.Variables

/-!
# Equivalence: `AzMvPolynomial.vars` ↔ `MvPolynomial.vars`

We prove `(toMvPoly p).vars = p.vars`.
-/

namespace Azurite
open AzMvPolynomial

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]
  {n : ℕ} {ord : MonomialOrder}

/-! ### MonicMonomial.vars ↔ Finsupp.support -/

omit [NoZeroDivisors R] [DecidableEq R] in
/-- The `vars` of a monic monomial equals the support of its `toFinsupp`. -/
theorem MonicMonomial.vars_eq_toFinsupp_support (m : MonicMonomial n ord) :
    m.vars = m.toFinsupp.support := by
  ext v
  simp only [MonicMonomial.vars, Finset.mem_filter, Finset.mem_univ, true_and,
    Finsupp.mem_support_iff, MonicMonomial.toFinsupp, Finsupp.onFinset_apply]

/-! ### Membership in foldl union -/

omit [NoZeroDivisors R] [DecidableEq R] in
/-- `v ∈ foldl (∪) init l ↔ v ∈ init ∨ ∃ m ∈ l, v ∈ m.vars` -/
private theorem mem_foldl_union_vars
    (l : List (Monomial n R ord)) (init : Finset (Fin n)) (v : Fin n) :
    v ∈ l.foldl (fun acc m => acc ∪ m.vars) init ↔
    v ∈ init ∨ ∃ m ∈ l, v ∈ m.vars := by
  induction l generalizing init with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rw [ih]
    constructor
    · rintro (hv | ⟨m, hm, hv⟩)
      · simp only [Finset.mem_union] at hv
        rcases hv with h | h
        · exact Or.inl h
        · exact Or.inr ⟨hd, .head _, h⟩
      · exact Or.inr ⟨m, .tail _ hm, hv⟩
    · rintro (h | ⟨m, hm, hv⟩)
      · exact Or.inl (Finset.mem_union_left _ h)
      · cases hm with
        | head => exact Or.inl (Finset.mem_union_right _ hv)
        | tail _ hm' => exact Or.inr ⟨m, hm', hv⟩

/-! ### Main equivalence -/

omit [NoZeroDivisors R] [DecidableEq R] in
@[simp] theorem toMvPoly_vars (p : AzMvPolynomial n R ord) :
    (toMvPoly p).vars = p.vars := by
  classical
  rw [MvPolynomial.vars_eq_support_biUnion_support, support_toMvPoly]
  unfold AzMvPolynomial.vars
  rw [← Array.foldl_toList]
  ext v
  rw [mem_foldl_union_vars]
  constructor
  · intro hv
    rw [Finset.mem_biUnion] at hv
    obtain ⟨fs, hfs, hv⟩ := hv
    rw [List.mem_toFinset, List.mem_map] at hfs
    obtain ⟨m, hm, rfl⟩ := hfs
    rw [← MonicMonomial.vars_eq_toFinsupp_support] at hv
    exact Or.inr ⟨m, hm, hv⟩
  · rintro (h | ⟨m, hm, hv⟩)
    · exact absurd h (Finset.notMem_empty v)
    · rw [Finset.mem_biUnion]
      rw [show m.vars = m.monic.vars from rfl,
          MonicMonomial.vars_eq_toFinsupp_support] at hv
      exact ⟨m.monic.toFinsupp,
        List.mem_toFinset.mpr (List.mem_map.mpr ⟨m, hm, rfl⟩), hv⟩

end Azurite
