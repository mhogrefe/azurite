/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_6.NewtonPolygonExists
import Azurite.BasuPollackRoy.Chapter2.Section2_6.CharacteristicPolynomial

/-! # BPR §2.6 — edge data of a Newton polygon

For the Puiseux root construction one selects an edge `[A, B]` of the Newton polygon (a consecutive
pair `(A, B) ∈ M.zip M.tail`) and feeds it to Lemma 2.95. This file extracts the data Lemma 2.95
needs from an edge: the endpoints are distinct columns (`newtonEdge_fst_lt`), they are column
points (`newtonEdge_colPoint_left/right`), the edge supports the whole diagram
(`newtonEdge_onOrAbove`), and — packaged for Lemma 2.95 — every column lies on or above the edge
line (`newtonEdge_hsupport`).

The remaining Lemma-2.95 hypothesis `honseg` (on-line columns lie within `[A.1, B.1]`) is a
strict-convexity property and is handled separately. -/

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R]

/-- **A consecutive pair of a chain satisfies the chain relation.** -/
theorem isChain_rel_of_mem_zip {α : Type*} {Rel : α → α → Prop} : ∀ (M : List α),
    M.IsChain Rel → ∀ e : α × α, e ∈ M.zip M.tail → Rel e.1 e.2 := by
  intro M
  induction M with
  | nil => intro _ e he; simp at he
  | cons a t ih =>
    intro hch e he
    cases t with
    | nil => simp at he
    | cons b l =>
        rw [List.tail_cons, List.zip_cons_cons] at he
        rw [List.isChain_cons] at hch
        obtain ⟨hhead, hchbl⟩ := hch
        rcases List.mem_cons.mp he with rfl | he
        · exact hhead b rfl
        · exact ih hchbl e he

/-- The columns of an edge are distinct (in fact increasing). -/
theorem newtonEdge_fst_lt {P : Polynomial (PuiseuxSeries R)} {M : List (ℕ × ℚ)}
    (hM : IsNewtonPolygon P M) {A B : ℕ × ℚ} (hAB : (A, B) ∈ M.zip M.tail) : A.1 < B.1 :=
  isChain_rel_of_mem_zip M hM.strictMono_fst (A, B) hAB

/-- **The edge lies on or above every Newton-diagram point.** -/
theorem newtonEdge_onOrAbove {P : Polynomial (PuiseuxSeries R)} {M : List (ℕ × ℚ)}
    (hM : IsNewtonPolygon P M) {A B : ℕ × ℚ} (hAB : (A, B) ∈ M.zip M.tail) :
    ∀ Q ∈ newtonDiagram P, OnOrAbove A B Q :=
  isChain_rel_of_mem_zip M hM.diagram_onOrAbove (A, B) hAB

/-- The left endpoint of an edge is a column point. -/
theorem newtonEdge_colPoint_left {P : Polynomial (PuiseuxSeries R)} {M : List (ℕ × ℚ)}
    (hM : IsNewtonPolygon P M) {A B : ℕ × ℚ} (hAB : (A, B) ∈ M.zip M.tail) :
    puiseuxOrder R (P.coeff A.1) = (A.2 : WithTop ℚ) :=
  hM.isColumnPoint A (List.of_mem_zip hAB).1

/-- The right endpoint of an edge is a column point. -/
theorem newtonEdge_colPoint_right {P : Polynomial (PuiseuxSeries R)} {M : List (ℕ × ℚ)}
    (hM : IsNewtonPolygon P M) {A B : ℕ × ℚ} (hAB : (A, B) ∈ M.zip M.tail) :
    puiseuxOrder R (P.coeff B.1) = (B.2 : WithTop ℚ) :=
  hM.isColumnPoint B (List.mem_of_mem_tail (List.of_mem_zip hAB).2)

/-- **The supporting-line hypothesis for Lemma 2.95.** Every column lies on or above the edge line:
`lineValue A B h ≤ o(ā_h)` for all `h`. -/
theorem newtonEdge_hsupport {P : Polynomial (PuiseuxSeries R)} {M : List (ℕ × ℚ)}
    (hM : IsNewtonPolygon P M) {A B : ℕ × ℚ} (hAB : (A, B) ∈ M.zip M.tail) :
    ∀ h, (lineValue A B h : WithTop ℚ) ≤ puiseuxOrder R (P.coeff h) := by
  intro h
  have hoa := newtonEdge_onOrAbove hM hAB
  by_cases hc : P.coeff h = 0
  · rw [hc, puiseuxOrder_zero]; exact le_top
  · have hmem : (h, colOrd P h) ∈ newtonDiagram P :=
      mem_newtonDiagram_of_puiseuxOrder_eq (puiseuxOrder_eq_colOrd hc)
    have hQ := hoa (h, colOrd P h) hmem
    rw [onOrAbove_iff] at hQ
    rw [puiseuxOrder_eq_colOrd hc, WithTop.coe_le_coe, lineValue]
    dsimp only at hQ
    linarith [hQ]

end Azurite.BPR
