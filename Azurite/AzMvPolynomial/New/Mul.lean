/-
  Multiplication for `AzMvPolynomialNew`.
-/
import Azurite.AzMvPolynomial.New.Basic

namespace Azurite
open AzMvPolynomialNew

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]
         {n : ℕ} {ord : MonomialOrder}

/-! ### Combine adjacent like terms -/

/-- Combine adjacent monomials with equal monic parts in a sorted list,
    dropping zero-coefficient results. -/
def combineSortedNew : List (MonomialNew n R ord) → List (MonomialNew n R ord)
  | [] => []
  | [m] => [m]
  | m₁ :: m₂ :: rest =>
    if m₁.monic = m₂.monic then
      if hc : m₁.coeff.val + m₂.coeff.val = 0 then combineSortedNew rest
      else combineSortedNew (⟨⟨m₁.coeff.val + m₂.coeff.val, hc⟩, m₁.monic⟩ :: rest)
    else m₁ :: combineSortedNew (m₂ :: rest)
termination_by l => l.length

omit [NoZeroDivisors R] in
theorem combineSortedNew_forall_le (m : MonicMonomialNew n ord)
    (l : List (MonomialNew n R ord)) (hl : ∀ x ∈ l, x.monic ≤ m) :
    ∀ x ∈ combineSortedNew l, x.monic ≤ m := by
  induction l using combineSortedNew.induct with
  | case1 => simp [combineSortedNew]
  | case2 m' => simp [combineSortedNew]; exact hl m' (List.mem_cons_self ..)
  | case3 m₁ m₂ rest heq hcz ih =>
    simp only [combineSortedNew, if_pos heq, dif_pos hcz]
    exact ih (fun x hx => hl x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)))
  | case4 m₁ m₂ rest heq hcnz ih =>
    simp only [combineSortedNew, if_pos heq, dif_neg hcnz]
    have hm₁ : m₁.monic ≤ m := hl m₁ (List.mem_cons_self ..)
    exact ih (fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hm₁
      · exact hl x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)))
  | case5 m₁ m₂ rest hneq ih =>
    simp only [combineSortedNew, if_neg hneq]
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hl _ (List.mem_cons_self ..)
    · exact ih (fun y hy => hl y (List.mem_cons_of_mem _ hy)) x hx

omit [NoZeroDivisors R] in
theorem combineSortedNew_sorted_of_ge (l : List (MonomialNew n R ord))
    (hl : l.Pairwise (fun a b => a.monic ≥ b.monic)) :
    (combineSortedNew l).Pairwise (fun a b => a.monic > b.monic) := by
  induction l using combineSortedNew.induct with
  | case1 => simp [combineSortedNew]
  | case2 _ => simp [combineSortedNew]
  | case3 m₁ m₂ rest heq hcz ih =>
    simp only [combineSortedNew, if_pos heq, dif_pos hcz]
    rw [List.pairwise_cons] at hl
    exact ih (List.pairwise_cons.mp hl.2).2
  | case4 m₁ m₂ rest heq hcnz ih =>
    simp only [combineSortedNew, if_pos heq, dif_neg hcnz]
    rw [List.pairwise_cons] at hl
    rw [List.pairwise_cons] at hl
    exact ih (List.pairwise_cons.mpr ⟨fun x hx =>
      le_trans (hl.2.1 x hx) (heq ▸ le_refl _), hl.2.2⟩)
  | case5 m₁ m₂ rest hneq ih =>
    simp only [combineSortedNew, if_neg hneq]
    rw [List.pairwise_cons] at hl
    have hgt : m₁.monic > m₂.monic :=
      lt_of_le_of_ne (hl.1 m₂ (List.mem_cons_self ..)) (Ne.symm hneq)
    rw [List.pairwise_cons]
    refine ⟨fun x hx => lt_of_le_of_lt ?_ hgt, ih hl.2⟩
    exact combineSortedNew_forall_le m₂.monic (m₂ :: rest) (by
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact le_refl _
      · rw [List.pairwise_cons] at hl; exact hl.2.1 y hy) x hx

/-! ### Sort descending -/

def sortDescendingNew (l : List (MonomialNew n R ord)) : List (MonomialNew n R ord) :=
  l.mergeSort (fun a b => decide (a.monic ≥ b.monic))

omit [NoZeroDivisors R] [DecidableEq R] in
theorem sortDescendingNew_pairwise (l : List (MonomialNew n R ord)) :
    (sortDescendingNew l).Pairwise (fun a b => a.monic ≥ b.monic) := by
  have := List.pairwise_mergeSort
    (le := fun a b => decide (a.monic ≥ b.monic))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; exact le_trans hbc hab)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; exact le_total b.monic a.monic)
    l
  simp only [decide_eq_true_eq] at this
  exact this

/-! ### Normalization -/

def normalizeMonomialsNew (l : List (MonomialNew n R ord)) : List (MonomialNew n R ord) :=
  combineSortedNew (sortDescendingNew l)

omit [NoZeroDivisors R] in
theorem normalizeMonomialsNew_sorted (l : List (MonomialNew n R ord)) :
    (normalizeMonomialsNew l).Pairwise (fun a b => a.monic > b.monic) :=
  combineSortedNew_sorted_of_ge _ (sortDescendingNew_pairwise l)

/-! ### Naive multiplication -/

def mulPairsNew (ps qs : List (MonomialNew n R ord)) : List (MonomialNew n R ord) :=
  ps.flatMap (fun p => qs.map (fun q => p * q))

/-- Naive polynomial multiplication. -/
def AzMvPolynomialNew.mulNaive (p q : AzMvPolynomialNew n R ord) : AzMvPolynomialNew n R ord :=
  let products := mulPairsNew p.terms.toList q.terms.toList
  ⟨(normalizeMonomialsNew products).toArray,
   by rw [List.toList_toArray]; exact normalizeMonomialsNew_sorted _⟩

/-- Polynomial multiplication, currently delegating to `mulNaive`. -/
def AzMvPolynomialNew.mul (p q : AzMvPolynomialNew n R ord) : AzMvPolynomialNew n R ord :=
  p.mulNaive q

instance : Mul (AzMvPolynomialNew n R ord) := ⟨AzMvPolynomialNew.mul⟩

end Azurite
