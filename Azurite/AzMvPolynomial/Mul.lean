/-
  Multiplication for `AzMvPolynomial`.
-/
import Azurite.AzMvPolynomial.Basic

namespace Azurite
open AzMvPolynomial

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]
         {n : ℕ} {ord : MonomialOrder}

/-! ### Combine adjacent like terms -/

/-- Combine adjacent monomials with equal monic parts in a sorted list,
    dropping zero-coefficient results. -/
def combineSorted : List (Monomial n R ord) → List (Monomial n R ord)
  | [] => []
  | [m] => [m]
  | m₁ :: m₂ :: rest =>
    if m₁.monic = m₂.monic then
      if hc : m₁.coeff.val + m₂.coeff.val = 0 then combineSorted rest
      else combineSorted (⟨⟨m₁.coeff.val + m₂.coeff.val, hc⟩, m₁.monic⟩ :: rest)
    else m₁ :: combineSorted (m₂ :: rest)
termination_by l => l.length

omit [NoZeroDivisors R] in
theorem combineSorted_forall_le (m : MonicMonomial n ord)
    (l : List (Monomial n R ord)) (hl : ∀ x ∈ l, x.monic ≤ m) :
    ∀ x ∈ combineSorted l, x.monic ≤ m := by
  induction l using combineSorted.induct with
  | case1 => simp [combineSorted]
  | case2 m' => simp [combineSorted]; exact hl m' (List.mem_cons_self ..)
  | case3 m₁ m₂ rest heq hcz ih =>
    simp only [combineSorted, ite_eq_left heq, dite_eq_left hcz]
    exact ih (fun x hx => hl x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)))
  | case4 m₁ m₂ rest heq hcnz ih =>
    simp only [combineSorted, ite_eq_left heq, dite_eq_right hcnz]
    have hm₁ : m₁.monic ≤ m := hl m₁ (List.mem_cons_self ..)
    exact ih (fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hm₁
      · exact hl x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)))
  | case5 m₁ m₂ rest hneq ih =>
    simp only [combineSorted, ite_eq_right hneq]
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hl _ (List.mem_cons_self ..)
    · exact ih (fun y hy => hl y (List.mem_cons_of_mem _ hy)) x hx

omit [NoZeroDivisors R] in
theorem combineSorted_sorted_of_ge (l : List (Monomial n R ord))
    (hl : l.Pairwise (fun a b => a.monic ≥ b.monic)) :
    (combineSorted l).Pairwise (fun a b => a.monic > b.monic) := by
  induction l using combineSorted.induct with
  | case1 => simp [combineSorted]
  | case2 _ => simp [combineSorted]
  | case3 m₁ m₂ rest heq hcz ih =>
    simp only [combineSorted, ite_eq_left heq, dite_eq_left hcz]
    rw [List.pairwise_cons] at hl
    exact ih (List.pairwise_cons.mp hl.2).2
  | case4 m₁ m₂ rest heq hcnz ih =>
    simp only [combineSorted, ite_eq_left heq, dite_eq_right hcnz]
    rw [List.pairwise_cons] at hl
    rw [List.pairwise_cons] at hl
    exact ih (List.pairwise_cons.mpr ⟨fun x hx =>
      le_trans (hl.2.1 x hx) (heq ▸ le_refl _), hl.2.2⟩)
  | case5 m₁ m₂ rest hneq ih =>
    simp only [combineSorted, ite_eq_right hneq]
    rw [List.pairwise_cons] at hl
    have hgt : m₁.monic > m₂.monic :=
      lt_of_le_of_ne (hl.1 m₂ (List.mem_cons_self ..)) (Ne.symm hneq)
    rw [List.pairwise_cons]
    refine ⟨fun x hx => lt_of_le_of_lt ?_ hgt, ih hl.2⟩
    exact combineSorted_forall_le m₂.monic (m₂ :: rest) (by
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact le_refl _
      · rw [List.pairwise_cons] at hl; exact hl.2.1 y hy) x hx

/-! ### Sort descending -/

def sortDescending (l : List (Monomial n R ord)) : List (Monomial n R ord) :=
  l.mergeSort (fun a b => decide (a.monic ≥ b.monic))

omit [NoZeroDivisors R] [DecidableEq R] in
theorem sortDescending_pairwise (l : List (Monomial n R ord)) :
    (sortDescending l).Pairwise (fun a b => a.monic ≥ b.monic) := by
  have := List.pairwise_mergeSort
    (le := fun a b => decide (a.monic ≥ b.monic))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; exact le_trans hbc hab)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; exact le_total b.monic a.monic)
    l
  simp only [decide_eq_true_eq] at this
  exact this

/-! ### Normalization -/

def normalizeMonomials (l : List (Monomial n R ord)) : List (Monomial n R ord) :=
  combineSorted (sortDescending l)

omit [NoZeroDivisors R] in
theorem normalizeMonomials_sorted (l : List (Monomial n R ord)) :
    (normalizeMonomials l).Pairwise (fun a b => a.monic > b.monic) :=
  combineSorted_sorted_of_ge _ (sortDescending_pairwise l)

/-! ### Naive multiplication -/

def mulPairs (ps qs : List (Monomial n R ord)) : List (Monomial n R ord) :=
  ps.flatMap (fun p => qs.map (fun q => p * q))

/-- Naive polynomial multiplication. -/
def AzMvPolynomial.mulNaive (p q : AzMvPolynomial n R ord) : AzMvPolynomial n R ord :=
  let products := mulPairs p.terms.toList q.terms.toList
  ⟨(normalizeMonomials products).toArray,
   by rw [List.toList_toArray]; exact normalizeMonomials_sorted _⟩

/-- Polynomial multiplication, currently delegating to `mulNaive`. -/
def AzMvPolynomial.mul (p q : AzMvPolynomial n R ord) : AzMvPolynomial n R ord :=
  p.mulNaive q

instance instAzMvPolynomialMul : Mul (AzMvPolynomial n R ord) := ⟨AzMvPolynomial.mul⟩

end Azurite
