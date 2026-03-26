/-
  Addition for AzMvPolynomial via sorted merge.

  Since both polynomials share the same monomial order, their term lists
  are sorted in strictly descending order by monic part.  We merge them
  in a single linear sweep (O(n + m)), combining coefficients when the
  monic parts match and dropping terms whose sum is zero.
-/
import Azurite.AzMvPolynomial.Basic

namespace Azurite
open AzMvPolynomial

variable {R : Type _} [Semiring R] [DecidableEq R]
         {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n]
         {ord : MonomialOrder}

/-- Merge two sorted monomial lists into a single sorted list,
    combining coefficients when monic parts match and dropping
    terms whose coefficients sum to zero.

    Both input lists must be sorted in strictly descending order
    by monic part. The output maintains the same invariant. -/
def addSorted : List (Monomial σ R ord) → List (Monomial σ R ord) →
    List (Monomial σ R ord)
  | [], qs => qs
  | ps, [] => ps
  | p :: ps, q :: qs =>
    if p.monic > q.monic then p :: addSorted ps (q :: qs)
    else if q.monic > p.monic then q :: addSorted (p :: ps) qs
    else
      if h : p.coeff.val + q.coeff.val = 0 then addSorted ps qs
      else ⟨⟨p.coeff.val + q.coeff.val, h⟩, p.monic⟩ :: addSorted ps qs
termination_by a b => a.length + b.length

/-! ### Sorted-invariant proof -/

/-- Every monic in the result of `addSorted` is `< m`, provided
    every monic in both inputs is `< m`. -/
theorem addSorted_forall_lt (m : MonicMonomial σ ord)
    (ps qs : List (Monomial σ R ord))
    (hp : ∀ x ∈ ps, x.monic < m) (hq : ∀ x ∈ qs, x.monic < m) :
    ∀ x ∈ addSorted ps qs, x.monic < m := by
  match ps, qs with
  | [], qs =>
    simp only [addSorted]; exact hq
  | p :: ps', [] =>
    simp only [addSorted]; exact hp
  | p :: ps', q :: qs' =>
    unfold addSorted; split_ifs with hpq hqp hc
    · -- p > q: emit p
      intro x hx; rcases List.mem_cons.mp hx with rfl | hx
      · exact hp x (List.mem_cons_self ..)
      · exact addSorted_forall_lt m ps' (q :: qs')
          (fun y hy => hp y (List.mem_cons_of_mem _ hy)) hq x hx
    · -- q > p: emit q
      intro x hx; rcases List.mem_cons.mp hx with rfl | hx
      · exact hq x (List.mem_cons_self ..)
      · exact addSorted_forall_lt m (p :: ps') qs'
          hp (fun y hy => hq y (List.mem_cons_of_mem _ hy)) x hx
    · -- equal, zero sum
      exact addSorted_forall_lt m ps' qs'
        (fun y hy => hp y (List.mem_cons_of_mem _ hy))
        (fun y hy => hq y (List.mem_cons_of_mem _ hy))
    · -- equal, nonzero sum
      intro x hx; rcases List.mem_cons.mp hx with rfl | hx
      · exact hp p (List.mem_cons_self ..)
      · exact addSorted_forall_lt m ps' qs'
          (fun y hy => hp y (List.mem_cons_of_mem _ hy))
          (fun y hy => hq y (List.mem_cons_of_mem _ hy)) x hx
termination_by ps.length + qs.length

/-- `addSorted` preserves the strictly-descending pairwise invariant. -/
theorem addSorted_sorted
    (ps qs : List (Monomial σ R ord))
    (hp : ps.Pairwise (fun a b => a.monic > b.monic))
    (hq : qs.Pairwise (fun a b => a.monic > b.monic)) :
    (addSorted ps qs).Pairwise (fun a b => a.monic > b.monic) := by
  match ps, qs with
  | [], qs => simp only [addSorted]; exact hq
  | p :: ps', [] => simp only [addSorted]; exact hp
  | p :: ps', q :: qs' =>
    rw [List.pairwise_cons] at hp hq
    unfold addSorted; split_ifs with hpq hqp hc
    · -- p > q: emit p
      rw [List.pairwise_cons]
      refine ⟨?_, addSorted_sorted ps' (q :: qs') hp.2 (List.pairwise_cons.mpr hq)⟩
      exact addSorted_forall_lt p.monic ps' (q :: qs')
        hp.1
        (fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hpq
          · exact lt_trans (hq.1 x hx) hpq)
    · -- q > p: emit q
      rw [List.pairwise_cons]
      refine ⟨?_, addSorted_sorted (p :: ps') qs' (List.pairwise_cons.mpr hp) hq.2⟩
      exact addSorted_forall_lt q.monic (p :: ps') qs'
        (fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hqp
          · exact lt_trans (hp.1 x hx) hqp)
        hq.1
    · -- equal, zero sum
      exact addSorted_sorted ps' qs' hp.2 hq.2
    · -- equal, nonzero sum
      rw [List.pairwise_cons]
      have heq : p.monic = q.monic := by
        have h1 : ¬ p.monic < q.monic := hqp
        have h2 : ¬ q.monic < p.monic := hpq
        exact le_antisymm (not_lt.mp h2) (not_lt.mp h1)
      refine ⟨?_, addSorted_sorted ps' qs' hp.2 hq.2⟩
      exact addSorted_forall_lt p.monic ps' qs'
        hp.1 (fun x hx => heq ▸ hq.1 x hx)
termination_by ps.length + qs.length

/-! ### Add instance -/

/-- Add two `AzMvPolynomial`s by merging their sorted term lists. -/
def AzMvPolynomial.add (p q : AzMvPolynomial σ R ord) : AzMvPolynomial σ R ord :=
  ⟨(addSorted p.terms.toList q.terms.toList).toArray,
   by rw [List.toList_toArray]; exact addSorted_sorted _ _ p.sorted q.sorted⟩

instance : Add (AzMvPolynomial σ R ord) := ⟨AzMvPolynomial.add⟩

end Azurite
