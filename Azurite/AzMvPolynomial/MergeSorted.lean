/-
  Generic sorted merge for AzMvPolynomial.

  `mergeSorted f hf` merges two sorted monomial lists, applying `f` to each
  coefficient from the second list before combining.  This is the common
  engine behind both addition (`f = id`) and subtraction (`f = Neg.neg`).
-/
import Azurite.AzMvPolynomial.Basic

namespace Azurite
open AzMvPolynomial

variable {R : Type _} [Ring R] [DecidableEq R]
         {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n]
         {ord : MonomialOrder}

/-- Generic merge of two sorted monomial lists. The function `f` is applied
    to each coefficient from the second list before combining.
    Requires `hf : ∀ x, x ≠ 0 → f x ≠ 0`.

    - `mergeSorted id …`      = addition
    - `mergeSorted Neg.neg …` = subtraction -/
@[specialize]
def mergeSorted (f : R → R) (hf : ∀ x, x ≠ 0 → f x ≠ 0) :
    List (Monomial σ R ord) → List (Monomial σ R ord) → List (Monomial σ R ord)
  | [], [] => []
  | [], q :: qs =>
    ⟨⟨f q.coeff.val, hf q.coeff.val q.coeff.property⟩, q.monic⟩ :: mergeSorted f hf [] qs
  | ps, [] => ps
  | p :: ps, q :: qs =>
    if p.monic > q.monic then p :: mergeSorted f hf ps (q :: qs)
    else if q.monic > p.monic then
      ⟨⟨f q.coeff.val, hf q.coeff.val q.coeff.property⟩, q.monic⟩ ::
        mergeSorted f hf (p :: ps) qs
    else
      if h : p.coeff.val + f q.coeff.val = 0 then mergeSorted f hf ps qs
      else ⟨⟨p.coeff.val + f q.coeff.val, h⟩, p.monic⟩ :: mergeSorted f hf ps qs
termination_by a b => a.length + b.length

/-! ### Sorted-invariant proofs -/

/-- Every monic in the result of `mergeSorted` is `< m`, provided
    every monic in both inputs is `< m`. -/
theorem mergeSorted_forall_lt (f : R → R) (hf : ∀ x, x ≠ 0 → f x ≠ 0)
    (m : MonicMonomial σ ord)
    (ps qs : List (Monomial σ R ord))
    (hp : ∀ x ∈ ps, x.monic < m) (hq : ∀ x ∈ qs, x.monic < m) :
    ∀ x ∈ mergeSorted f hf ps qs, x.monic < m := by
  match ps, qs with
  | [], [] => simp [mergeSorted]
  | [], q :: qs' =>
    unfold mergeSorted
    intro x hx; rcases List.mem_cons.mp hx with rfl | hx
    · exact hq q (List.mem_cons_self ..)
    · exact mergeSorted_forall_lt f hf m [] qs'
        (fun _ h => nomatch h)
        (fun y hy => hq y (List.mem_cons_of_mem _ hy)) x hx
  | p :: ps', [] =>
    simp only [mergeSorted]; exact hp
  | p :: ps', q :: qs' =>
    unfold mergeSorted; split_ifs with hpq hqp hc
    · intro x hx; rcases List.mem_cons.mp hx with rfl | hx
      · exact hp x (List.mem_cons_self ..)
      · exact mergeSorted_forall_lt f hf m ps' (q :: qs')
          (fun y hy => hp y (List.mem_cons_of_mem _ hy)) hq x hx
    · intro x hx; rcases List.mem_cons.mp hx with rfl | hx
      · exact hq q (List.mem_cons_self ..)
      · exact mergeSorted_forall_lt f hf m (p :: ps') qs'
          hp (fun y hy => hq y (List.mem_cons_of_mem _ hy)) x hx
    · exact mergeSorted_forall_lt f hf m ps' qs'
        (fun y hy => hp y (List.mem_cons_of_mem _ hy))
        (fun y hy => hq y (List.mem_cons_of_mem _ hy))
    · intro x hx; rcases List.mem_cons.mp hx with rfl | hx
      · exact hp p (List.mem_cons_self ..)
      · exact mergeSorted_forall_lt f hf m ps' qs'
          (fun y hy => hp y (List.mem_cons_of_mem _ hy))
          (fun y hy => hq y (List.mem_cons_of_mem _ hy)) x hx
termination_by ps.length + qs.length

/-- `mergeSorted` preserves the strictly-descending pairwise invariant. -/
theorem mergeSorted_sorted (f : R → R) (hf : ∀ x, x ≠ 0 → f x ≠ 0)
    (ps qs : List (Monomial σ R ord))
    (hp : ps.Pairwise (fun a b => a.monic > b.monic))
    (hq : qs.Pairwise (fun a b => a.monic > b.monic)) :
    (mergeSorted f hf ps qs).Pairwise (fun a b => a.monic > b.monic) := by
  match ps, qs with
  | [], [] => simp [mergeSorted]
  | [], q :: qs' =>
    unfold mergeSorted; rw [List.pairwise_cons] at hq ⊢
    refine ⟨?_, mergeSorted_sorted f hf [] qs' List.Pairwise.nil hq.2⟩
    exact mergeSorted_forall_lt f hf q.monic [] qs'
      (fun _ h => nomatch h) hq.1
  | p :: ps', [] =>
    simp only [mergeSorted]; exact hp
  | p :: ps', q :: qs' =>
    rw [List.pairwise_cons] at hp hq
    unfold mergeSorted; split_ifs with hpq hqp hc
    · -- p > q: emit p
      rw [List.pairwise_cons]
      refine ⟨?_, mergeSorted_sorted f hf ps' (q :: qs') hp.2 (List.pairwise_cons.mpr hq)⟩
      exact mergeSorted_forall_lt f hf p.monic ps' (q :: qs')
        hp.1
        (fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hpq
          · exact lt_trans (hq.1 x hx) hpq)
    · -- q > p: emit f(q)
      rw [List.pairwise_cons]
      refine ⟨?_, mergeSorted_sorted f hf (p :: ps') qs' (List.pairwise_cons.mpr hp) hq.2⟩
      exact mergeSorted_forall_lt f hf q.monic (p :: ps') qs'
        (fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hqp
          · exact lt_trans (hp.1 x hx) hqp)
        hq.1
    · -- equal, zero: drop
      exact mergeSorted_sorted f hf ps' qs' hp.2 hq.2
    · -- equal, nonzero: emit combined
      rw [List.pairwise_cons]
      have heq : p.monic = q.monic :=
        le_antisymm (not_lt.mp hpq) (not_lt.mp hqp)
      refine ⟨?_, mergeSorted_sorted f hf ps' qs' hp.2 hq.2⟩
      exact mergeSorted_forall_lt f hf p.monic ps' qs'
        hp.1 (fun x hx => heq ▸ hq.1 x hx)
termination_by ps.length + qs.length

end Azurite
