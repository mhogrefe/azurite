import Azurite.BasuPollackRoy.Chapter2.Section2_6.NewtonDiagram

/-! # BPR §2.6 — the Newton polygon of a polynomial over `R⟨⟨ε⟩⟩`

For `P(X) = ā₀ + ā₁ X + ⋯ + ā_p X^p ∈ R⟨⟨ε⟩⟩[X]`, let `M_i = (i, o(ā_i))` (`i = 0, …, p`) be
the bottom point of column `i` of the Newton diagram, where `o = puiseuxOrder` is the order of
the Puiseux coefficient `ā_i = P.coeff i` (a rational number when `ā_i ≠ 0`, and `∞` when
`ā_i = 0`).

The **Newton polygon** of `P` is a sequence of points `M_0 = M_{i_0}, …, M_{i_ℓ} = M_p` such
that the `x`-coordinates are strictly increasing, every point of the Newton diagram lies on or
above each edge `M_{i_{j-1}} M_{i_j}`, and the vertex chain is convex (turns counterclockwise):
each vertex lies on or above the edge through the two preceding vertices. We encode this as the
predicate `IsNewtonPolygon P M` on the list `M` of (finite) vertices.
-/

namespace Azurite.BPR

open HahnSeries Polynomial

variable {R : Type*} [Field R]

/-- **The column point `M_i = (i, o(a_i))` is a genuine Newton-diagram point.** When the order
of `a_i = P.coeff i` is the finite value `y`, the point `(i, y)` lies in the diagram: the
coefficient of `ε^y` in `a_i` is its (nonzero) leading coefficient. -/
theorem mem_newtonDiagram_of_puiseuxOrder_eq {P : Polynomial (PuiseuxSeries R)} {i : ℕ} {y : ℚ}
    (h : puiseuxOrder R (P.coeff i) = (y : WithTop ℚ)) : (i, y) ∈ newtonDiagram P := by
  rw [mem_newtonDiagram, newtonCoeff]
  set x : HahnSeries ℚ R := ((P.coeff i : PuiseuxSeries R) : HahnSeries ℚ R) with hxdef
  have hox : x.orderTop = (y : WithTop ℚ) := h
  have hx_ne : x ≠ 0 := by intro h0; rw [h0] at hox; simp at hox
  have hord : x.order = y := by
    have h1 := HahnSeries.order_eq_orderTop_of_ne_zero hx_ne
    rw [hox] at h1; exact_mod_cast h1
  rw [← hord, ← HahnSeries.leadingCoeff_eq]
  exact HahnSeries.leadingCoeff_ne_zero.mpr hx_ne

/-- **The Newton polygon of `P`** (BPR §2.6). A list `M` of points of `ℕ × ℚ` is a Newton
polygon of `P` when it is the vertex sequence `M_0 = M_{i_0}, …, M_{i_ℓ} = M_p` of the lower
convex hull of the Newton diagram. -/
structure IsNewtonPolygon (P : Polynomial (PuiseuxSeries R)) (M : List (ℕ × ℚ)) : Prop where
  /-- Every vertex `(i, y)` is the bottom point `M_i = (i, o(a_i))` of its column: `y` is the
  order of `a_i = P.coeff i` (so in particular `a_i ≠ 0`). -/
  isColumnPoint : ∀ V ∈ M, puiseuxOrder R (P.coeff V.1) = (V.2 : WithTop ℚ)
  /-- The first vertex is `M_0` (column `0`). -/
  head_eq : ∃ y, M.head? = some (0, y)
  /-- The last vertex is `M_p` (column `p = deg P`). -/
  getLast_eq : ∃ y, M.getLast? = some (P.natDegree, y)
  /-- The `x`-coordinates (columns) are strictly increasing along the polygon. -/
  strictMono_fst : M.IsChain fun A B => A.1 < B.1
  /-- Every point of the Newton diagram lies on or above each edge `M_{i_{j-1}} M_{i_j}`. -/
  diagram_onOrAbove : M.IsChain fun A B => ∀ Q ∈ newtonDiagram P, OnOrAbove A B Q
  /-- The vertex chain turns counterclockwise: each vertex `M_{i_{j+1}}` lies on or above the
  edge `M_{i_{j-1}} M_{i_j}` through the two preceding vertices. -/
  convex : (M.zip M.tail).IsChain fun e₁ e₂ => OnOrAbove e₁.1 e₁.2 e₂.2

/-- **Every vertex of a Newton polygon is a point of the Newton diagram.** -/
theorem IsNewtonPolygon.vertex_mem_newtonDiagram {P : Polynomial (PuiseuxSeries R)}
    {M : List (ℕ × ℚ)} (hM : IsNewtonPolygon P M) {V : ℕ × ℚ} (hV : V ∈ M) :
    V ∈ newtonDiagram P := by
  simpa using mem_newtonDiagram_of_puiseuxOrder_eq (hM.isColumnPoint V hV)

end Azurite.BPR
