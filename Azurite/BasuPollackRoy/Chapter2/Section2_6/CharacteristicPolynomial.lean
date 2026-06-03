import Azurite.BasuPollackRoy.Chapter2.Section2_6.NewtonPolygon

/-! # BPR §2.6 — the characteristic polynomial of a Newton-polygon edge

To an edge `E = [M_{i_{j-1}}, M_{i_j}]` of the Newton polygon of `P ∈ R⟨⟨ε⟩⟩[X]`, with
horizontal projection `[i_{j-1}, i_j]`, we associate its **characteristic polynomial**
`Q(P, E, X) = ∑ a_h X^h ∈ R[X]`, where the sum is over all columns `h` for which the column
point `M_h = (h, o(ā_h))` lies on `E`, and the coefficient is `a_h = In(ā_h)`, the initial
(leading) coefficient of the Puiseux series `ā_h = P.coeff h`.

We represent the edge by its two endpoints `A = M_{i_{j-1}}` and `B = M_{i_j}` (points of
`ℕ × ℚ`), so the horizontal projection is `[A.1, B.1]`.
-/

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R]

/-- The `y`-value at `x = h` of the line through `A` and `B`. -/
def lineValue (A B : ℕ × ℚ) (h : ℕ) : ℚ := A.2 + newtonSlope A B * ((h : ℚ) - A.1)

theorem lineValue_left (A B : ℕ × ℚ) : lineValue A B A.1 = A.2 := by
  rw [lineValue, sub_self, mul_zero, add_zero]

theorem lineValue_right {A B : ℕ × ℚ} (hAB : A.1 ≠ B.1) : lineValue A B B.1 = B.2 := by
  rw [lineValue, newtonSlope_mul_sub hAB]; ring

/-- The column point `M_h = (h, o(a_h))` lies on the line through `A` and `B`: the order of
`a_h = P.coeff h` equals the line's value `A.2 + slope(A,B)·(h − A.1)` at `x = h`. (Combined
with `A.1 ≤ h ≤ B.1`, this says `M_h` lies on the segment `[A, B]`.) -/
def colOnLine (P : Polynomial (PuiseuxSeries R)) (A B : ℕ × ℚ) (h : ℕ) : Prop :=
  puiseuxOrder R (P.coeff h) = (lineValue A B h : WithTop ℚ)

open Classical in
/-- **The characteristic polynomial `Q(P, E, X)` of the edge `E = [A, B]`**: the sum
`∑ In(a_h) X^h` over the columns `h ∈ [A.1, B.1]` whose column point `M_h = (h, o(a_h))` lies on
the edge. -/
noncomputable def charPoly (P : Polynomial (PuiseuxSeries R)) (A B : ℕ × ℚ) : Polynomial R :=
  ∑ h ∈ (Finset.Icc A.1 B.1).filter (colOnLine P A B),
    Polynomial.monomial h (puiseuxInitCoeff R (P.coeff h))

open Classical in
/-- **The coefficients of the characteristic polynomial.** The coefficient of `X^k` is the
initial coefficient `In(a_k)` when the column point `M_k` lies on the edge `[A, B]`, and `0`
otherwise. -/
theorem charPoly_coeff (P : Polynomial (PuiseuxSeries R)) (A B : ℕ × ℚ) (k : ℕ) :
    (charPoly P A B).coeff k =
      if k ∈ (Finset.Icc A.1 B.1).filter (colOnLine P A B) then puiseuxInitCoeff R (P.coeff k)
      else 0 := by
  rw [charPoly, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']

/-- The characteristic polynomial has degree at most `i_j = B.1`. -/
theorem charPoly_natDegree_le (P : Polynomial (PuiseuxSeries R)) (A B : ℕ × ℚ) :
    (charPoly P A B).natDegree ≤ B.1 := by
  classical
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [charPoly_coeff, if_neg]
  rintro hmem
  exact absurd (Finset.mem_Icc.mp (Finset.mem_filter.mp hmem).1).2 (by omega)

/-- The **left endpoint** `M_{i_{j-1}} = A` lies on its own edge: if `A` is the column point of
column `A.1`, then `colOnLine P A B A.1` holds. -/
theorem colOnLine_left {P : Polynomial (PuiseuxSeries R)} {A B : ℕ × ℚ}
    (hA : puiseuxOrder R (P.coeff A.1) = (A.2 : WithTop ℚ)) : colOnLine P A B A.1 := by
  rw [colOnLine, lineValue_left, hA]

/-- The **right endpoint** `M_{i_j} = B` lies on its own edge: if `B` is the column point of
column `B.1` and `A.1 ≠ B.1`, then `colOnLine P A B B.1` holds. -/
theorem colOnLine_right {P : Polynomial (PuiseuxSeries R)} {A B : ℕ × ℚ} (hAB : A.1 ≠ B.1)
    (hB : puiseuxOrder R (P.coeff B.1) = (B.2 : WithTop ℚ)) : colOnLine P A B B.1 := by
  rw [colOnLine, lineValue_right hAB, hB]

/-- **The defining property of the edge slope.** If `−ξ` is the slope of `E = [A, B]` (i.e.
`slope(A, B) = −ξ`), then the line height `lineValue A B h` plus `h ξ` is the constant
`β = A.2 + A.1 ξ`, independent of `h`. -/
theorem lineValue_add_mul (A B : ℕ × ℚ) (h : ℕ) {ξ : ℚ} (hξ : newtonSlope A B = -ξ) :
    lineValue A B h + (h : ℚ) * ξ = A.2 + (A.1 : ℚ) * ξ := by
  rw [lineValue, hξ]; ring

/-- **`o(a_h) + h ξ` is constant along the edge.** If `−ξ` is the slope of `E = [A, B]`, then for
every column `h` whose point `M_h = (h, o(a_h))` lies on `E`, the value `o(a_h) + h ξ` equals the
constant `β = A.2 + A.1 ξ` (independent of `h`). -/
theorem colOnLine_order_add {P : Polynomial (PuiseuxSeries R)} {A B : ℕ × ℚ} {ξ : ℚ}
    (hξ : newtonSlope A B = -ξ) {h : ℕ} (hh : colOnLine P A B h) :
    puiseuxOrder R (P.coeff h) + (((h : ℚ) * ξ : ℚ) : WithTop ℚ)
      = ((A.2 + (A.1 : ℚ) * ξ : ℚ) : WithTop ℚ) := by
  rw [hh, ← WithTop.coe_add]
  exact_mod_cast lineValue_add_mul A B h hξ

end Azurite.BPR
