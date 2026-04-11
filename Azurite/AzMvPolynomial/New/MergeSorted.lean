/-
  Generic sorted merge for `AzMvPolynomialNew` (Fin-indexed).

  `mergeSorted f hf` merges two sorted monomial lists, applying `f` to each
  coefficient from the second list before combining.  This is the common
  engine behind both addition (`f = id`) and subtraction (`f = Neg.neg`).
-/
import Azurite.AzMvPolynomial.New.Basic

namespace Azurite
open AzMvPolynomialNew

variable {R : Type _} [Semiring R] [DecidableEq R]
         {n : ℕ} {ord : MonomialOrder}

/-- Generic merge of two sorted monomial lists. The function `f` is applied
    to each coefficient from the second list before combining.
    Requires `hf : ∀ x, x ≠ 0 → f x ≠ 0`.

    - `mergeSorted id …`      = addition
    - `mergeSorted Neg.neg …` = subtraction -/
@[specialize]
def mergeSortedNew (f : R → R) (hf : ∀ x, x ≠ 0 → f x ≠ 0) :
    List (MonomialNew n R ord) → List (MonomialNew n R ord) → List (MonomialNew n R ord)
  | [], [] => []
  | [], q :: qs =>
    ⟨⟨f q.coeff.val, hf q.coeff.val q.coeff.property⟩, q.monic⟩ :: mergeSortedNew f hf [] qs
  | ps, [] => ps
  | p :: ps, q :: qs =>
    if p.monic > q.monic then p :: mergeSortedNew f hf ps (q :: qs)
    else if q.monic > p.monic then
      ⟨⟨f q.coeff.val, hf q.coeff.val q.coeff.property⟩, q.monic⟩ ::
        mergeSortedNew f hf (p :: ps) qs
    else
      if h : p.coeff.val + f q.coeff.val = 0 then mergeSortedNew f hf ps qs
      else ⟨⟨p.coeff.val + f q.coeff.val, h⟩, p.monic⟩ :: mergeSortedNew f hf ps qs
termination_by a b => a.length + b.length

/-! ### Sorted-invariant proofs -/

/-- Every monic in the result of `mergeSortedNew` is `< m`, provided
    every monic in both inputs is `< m`. -/
theorem mergeSortedNew_forall_lt (f : R → R) (hf : ∀ x, x ≠ 0 → f x ≠ 0)
    (m : MonicMonomialNew n ord)
    (ps qs : List (MonomialNew n R ord))
    (hp : ∀ x ∈ ps, x.monic < m) (hq : ∀ x ∈ qs, x.monic < m) :
    ∀ x ∈ mergeSortedNew f hf ps qs, x.monic < m := by
  match ps, qs with
  | [], [] => simp [mergeSortedNew]
  | [], q :: qs' =>
    unfold mergeSortedNew
    intro x hx; rcases List.mem_cons.mp hx with rfl | hx
    · exact hq q (List.mem_cons_self ..)
    · exact mergeSortedNew_forall_lt f hf m [] qs'
        (fun _ h => nomatch h)
        (fun y hy => hq y (List.mem_cons_of_mem _ hy)) x hx
  | p :: ps', [] =>
    simp only [mergeSortedNew]; exact hp
  | p :: ps', q :: qs' =>
    unfold mergeSortedNew; split_ifs with hpq hqp hc
    · intro x hx; rcases List.mem_cons.mp hx with rfl | hx
      · exact hp x (List.mem_cons_self ..)
      · exact mergeSortedNew_forall_lt f hf m ps' (q :: qs')
          (fun y hy => hp y (List.mem_cons_of_mem _ hy)) hq x hx
    · intro x hx; rcases List.mem_cons.mp hx with rfl | hx
      · exact hq q (List.mem_cons_self ..)
      · exact mergeSortedNew_forall_lt f hf m (p :: ps') qs'
          hp (fun y hy => hq y (List.mem_cons_of_mem _ hy)) x hx
    · exact mergeSortedNew_forall_lt f hf m ps' qs'
        (fun y hy => hp y (List.mem_cons_of_mem _ hy))
        (fun y hy => hq y (List.mem_cons_of_mem _ hy))
    · intro x hx; rcases List.mem_cons.mp hx with rfl | hx
      · exact hp p (List.mem_cons_self ..)
      · exact mergeSortedNew_forall_lt f hf m ps' qs'
          (fun y hy => hp y (List.mem_cons_of_mem _ hy))
          (fun y hy => hq y (List.mem_cons_of_mem _ hy)) x hx
termination_by ps.length + qs.length

/-- `mergeSortedNew` preserves the strictly-descending pairwise invariant. -/
theorem mergeSortedNew_sorted (f : R → R) (hf : ∀ x, x ≠ 0 → f x ≠ 0)
    (ps qs : List (MonomialNew n R ord))
    (hp : ps.Pairwise (fun a b => a.monic > b.monic))
    (hq : qs.Pairwise (fun a b => a.monic > b.monic)) :
    (mergeSortedNew f hf ps qs).Pairwise (fun a b => a.monic > b.monic) := by
  match ps, qs with
  | [], [] => simp [mergeSortedNew]
  | [], q :: qs' =>
    unfold mergeSortedNew; rw [List.pairwise_cons] at hq ⊢
    refine ⟨?_, mergeSortedNew_sorted f hf [] qs' List.Pairwise.nil hq.2⟩
    exact mergeSortedNew_forall_lt f hf q.monic [] qs'
      (fun _ h => nomatch h) hq.1
  | p :: ps', [] =>
    simp only [mergeSortedNew]; exact hp
  | p :: ps', q :: qs' =>
    rw [List.pairwise_cons] at hp hq
    unfold mergeSortedNew; split_ifs with hpq hqp hc
    · rw [List.pairwise_cons]
      refine ⟨?_, mergeSortedNew_sorted f hf ps' (q :: qs') hp.2 (List.pairwise_cons.mpr hq)⟩
      exact mergeSortedNew_forall_lt f hf p.monic ps' (q :: qs')
        hp.1
        (fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hpq
          · exact lt_trans (hq.1 x hx) hpq)
    · rw [List.pairwise_cons]
      refine ⟨?_, mergeSortedNew_sorted f hf (p :: ps') qs' (List.pairwise_cons.mpr hp) hq.2⟩
      exact mergeSortedNew_forall_lt f hf q.monic (p :: ps') qs'
        (fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hqp
          · exact lt_trans (hp.1 x hx) hqp)
        hq.1
    · exact mergeSortedNew_sorted f hf ps' qs' hp.2 hq.2
    · rw [List.pairwise_cons]
      have heq : p.monic = q.monic :=
        le_antisymm (not_lt.mp hpq) (not_lt.mp hqp)
      refine ⟨?_, mergeSortedNew_sorted f hf ps' qs' hp.2 hq.2⟩
      exact mergeSortedNew_forall_lt f hf p.monic ps' qs'
        hp.1 (fun x hx => heq ▸ hq.1 x hx)
termination_by ps.length + qs.length

end Azurite
