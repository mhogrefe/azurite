import Azurite.BasuPollackRoy.Chapter2.Section2_6.NewtonPolygon

/-! # BPR §2.6 — an odd-degree polynomial has an edge of odd horizontal length

For the Puiseux root construction one chooses, at each step, a Newton-polygon edge whose
horizontal projection has odd length (so its characteristic polynomial has odd degree and hence a
root over the real closed coefficient field). This file provides the combinatorial input: if
`deg P` is odd, some edge `[A, B]` of the Newton polygon has `B.1 − A.1` odd
(`exists_odd_length_edge`).

The horizontal projections of the edges partition `[0, deg P]`, so their lengths sum to `deg P`;
an odd total forces an odd summand. We prove it as a parity telescoping along the vertex chain.
-/

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R]

/-- In a chain with strictly increasing first coordinates, the first column does not exceed the
last. -/
theorem chain_head_fst_le_getLast_fst : ∀ M : List (ℕ × ℚ),
    M.IsChain (fun A B => A.1 < B.1) → ∀ A B : ℕ × ℚ,
    M.head? = some A → M.getLast? = some B → A.1 ≤ B.1 := by
  intro M
  induction M with
  | nil => intro _ A B hA _; simp at hA
  | cons a t ih =>
    intro hch A B hA hB
    rw [List.head?_cons, Option.some_inj] at hA; subst hA
    cases t with
    | nil =>
        rw [List.getLast?_singleton, Option.some_inj] at hB
        exact le_of_eq (congrArg Prod.fst hB)
    | cons b l =>
        rw [List.isChain_cons] at hch
        obtain ⟨hab_head, hchbl⟩ := hch
        have hab : a.1 < b.1 := hab_head b rfl
        rw [List.getLast?_cons_cons] at hB
        have := ih hchbl b B (by rw [List.head?_cons]) hB
        omega

/-- **An odd horizontal span forces an odd edge.** If the columns of a strictly increasing vertex
chain run from `A` to `B` with `B.1 − A.1` odd, then some edge `[U, V]` has `V.1 − U.1` odd. -/
theorem exists_odd_length_edge_aux : ∀ M : List (ℕ × ℚ),
    M.IsChain (fun A B => A.1 < B.1) → ∀ A B : ℕ × ℚ,
    M.head? = some A → M.getLast? = some B → Odd (B.1 - A.1) →
    ∃ U V : ℕ × ℚ, (U, V) ∈ M.zip M.tail ∧ Odd (V.1 - U.1) := by
  intro M
  induction M with
  | nil => intro _ A B hA _ _; simp at hA
  | cons a t ih =>
    intro hch A B hA hB hodd
    rw [List.head?_cons, Option.some_inj] at hA; subst hA
    cases t with
    | nil =>
        rw [List.getLast?_singleton, Option.some_inj] at hB
        rw [← hB, Nat.sub_self] at hodd
        exact absurd hodd (by simp)
    | cons b l =>
        rw [List.isChain_cons] at hch
        obtain ⟨hab_head, hchbl⟩ := hch
        have hab : a.1 < b.1 := hab_head b rfl
        rw [List.getLast?_cons_cons] at hB
        by_cases hbo : Odd (b.1 - a.1)
        · exact ⟨a, b, by rw [List.tail_cons, List.zip_cons_cons]; exact List.mem_cons_self, hbo⟩
        · rw [Nat.not_odd_iff_even] at hbo
          have hbB : b.1 ≤ B.1 :=
            chain_head_fst_le_getLast_fst (b :: l) hchbl b B (by rw [List.head?_cons]) hB
          have hodd' : Odd (B.1 - b.1) := by
            rw [Nat.odd_iff] at hodd ⊢; rw [Nat.even_iff] at hbo; omega
          obtain ⟨U, V, hUV, hUVodd⟩ := ih hchbl b B (by rw [List.head?_cons]) hB hodd'
          exact ⟨U, V, by rw [List.tail_cons, List.zip_cons_cons]; exact List.mem_cons_of_mem _ hUV, hUVodd⟩

/-- **An odd-degree polynomial has a Newton-polygon edge of odd horizontal length.** -/
theorem exists_odd_length_edge {P : Polynomial (PuiseuxSeries R)} {M : List (ℕ × ℚ)}
    (hM : IsNewtonPolygon P M) (hodd : Odd P.natDegree) :
    ∃ U V : ℕ × ℚ, (U, V) ∈ M.zip M.tail ∧ Odd (V.1 - U.1) := by
  obtain ⟨y0, hhead⟩ := hM.head_eq
  obtain ⟨yN, hlast⟩ := hM.getLast_eq
  refine exists_odd_length_edge_aux M hM.strictMono_fst (0, y0) (P.natDegree, yN) hhead hlast ?_
  simpa using hodd

end Azurite.BPR
