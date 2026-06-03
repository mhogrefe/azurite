import Azurite.BasuPollackRoy.Chapter2.Section2_6.NewtonPolygonStrict
import Azurite.BasuPollackRoy.Chapter2.Section2_6.NewtonPolygonOddEdge
import Azurite.BasuPollackRoy.Chapter2.Section2_6.NewtonPolygonEdge

/-! # BPR §2.6 — a negative-slope odd edge over `[0, r]`

Given the order structure of a recentered polynomial `P₁` produced by `recursion_step`
(`o(b_i) ≥ 0` for all `i`, `o(b_i) > 0` for `i < r`, `o(b_r) = 0`, `r` odd, and `b₀ ≠ 0` in the
continue case), the next step needs an edge of *odd* length, with right endpoint `B.1 ≤ r` and
*negative* slope (so the slope `−ξ` has `ξ > 0`, hence `β > 0`).

We obtain it from the truncation `g := P₁ mod X^{r+1}`: `g` has degree `r` (since `b_r ≠ 0`) and
nonzero constant term, so its Newton polygon has an odd-length edge with `B.1 ≤ r`. The slope is
negative because the supporting line lies on or below the column point `(r, o(b_r)) = (r, 0)`
while `A.2 = o(b_{A.1}) > 0` (`A.1 < r`). The Lemma-2.95 data transfers from `g` to `P₁`: for
columns `≤ r` they agree, and for columns `> r` the negative-slope line is `< 0 ≤ o(b_h)`. -/

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R]

/-- **A negative-slope odd edge over `[0, r]`** for a recentered polynomial. -/
theorem exists_neg_slope_odd_edge {P₁ : Polynomial (PuiseuxSeries R)} {r : ℕ}
    (hr_odd : Odd r) (h0 : P₁.coeff 0 ≠ 0)
    (hbr : puiseuxOrder R (P₁.coeff r) = (0 : WithTop ℚ))
    (hbi : ∀ i, i < r → 0 < puiseuxOrder R (P₁.coeff i))
    (hge : ∀ i, (0 : WithTop ℚ) ≤ puiseuxOrder R (P₁.coeff i)) :
    ∃ A B : ℕ × ℚ, A.1 < B.1 ∧ B.1 ≤ r ∧ Odd (B.1 - A.1) ∧ newtonSlope A B < 0 ∧
      puiseuxOrder R (P₁.coeff A.1) = (A.2 : WithTop ℚ) ∧
      puiseuxOrder R (P₁.coeff B.1) = (B.2 : WithTop ℚ) ∧
      (∀ h, (lineValue A B h : WithTop ℚ) ≤ puiseuxOrder R (P₁.coeff h)) ∧
      (∀ h, colOnLine P₁ A B h → A.1 ≤ h ∧ h ≤ B.1) := by
  classical
  set g : Polynomial (PuiseuxSeries R) :=
    ∑ k ∈ Finset.range (r + 1), monomial k (P₁.coeff k) with hgdef
  have hgcoeff : ∀ j, g.coeff j = if j < r + 1 then P₁.coeff j else 0 := by
    intro j
    rw [hgdef, finsetSum_coeff]
    simp only [coeff_monomial, Finset.sum_ite_eq', Finset.mem_range]
  have hgcoeff_le : ∀ j, j ≤ r → g.coeff j = P₁.coeff j :=
    fun j hj => by rw [hgcoeff, if_pos (by omega)]
  have hbr_ne : P₁.coeff r ≠ 0 := by
    intro h; rw [h, puiseuxOrder_zero] at hbr; simp at hbr
  have hgr : g.coeff r ≠ 0 := by rw [hgcoeff_le r (le_refl r)]; exact hbr_ne
  have hg0 : g.coeff 0 ≠ 0 := by rw [hgcoeff_le 0 (Nat.zero_le r)]; exact h0
  have hgdeg : g.natDegree = r := by
    apply le_antisymm
    · apply natDegree_le_iff_coeff_eq_zero.mpr
      intro k hk; rw [hgcoeff, if_neg (by omega)]
    · exact le_natDegree_of_ne_zero hgr
  obtain ⟨Mg, hMg, hhonMg⟩ := exists_isNewtonPolygon_honseg g hg0
  obtain ⟨A, B, hAB_zip, hABodd⟩ := exists_odd_length_edge hMg (by rw [hgdeg]; exact hr_odd)
  have hABlt : A.1 < B.1 := newtonEdge_fst_lt hMg hAB_zip
  have hBmem : B ∈ Mg := List.mem_of_mem_tail (List.of_mem_zip hAB_zip).2
  have hBr : B.1 ≤ r := by
    have := fst_le_natDegree (hMg.vertex_mem_newtonDiagram hBmem)
    rwa [hgdeg] at this
  have hABr : A.1 < r := lt_of_lt_of_le hABlt hBr
  have hcolA : puiseuxOrder R (P₁.coeff A.1) = (A.2 : WithTop ℚ) := by
    rw [← hgcoeff_le A.1 (le_of_lt hABr)]; exact newtonEdge_colPoint_left hMg hAB_zip
  have hcolB : puiseuxOrder R (P₁.coeff B.1) = (B.2 : WithTop ℚ) := by
    rw [← hgcoeff_le B.1 hBr]; exact newtonEdge_colPoint_right hMg hAB_zip
  have hsup_g := newtonEdge_hsupport hMg hAB_zip
  have hA2pos : (0 : ℚ) < A.2 := by
    have := hbi A.1 hABr; rw [hcolA] at this; exact_mod_cast this
  have hlvr : lineValue A B r ≤ 0 := by
    have := hsup_g r; rw [hgcoeff_le r (le_refl r), hbr] at this; exact_mod_cast this
  have hslope : newtonSlope A B < 0 := by
    have hrA : (0 : ℚ) < (r : ℚ) - A.1 := by
      have : (A.1 : ℚ) < r := by exact_mod_cast hABr
      linarith
    have hexp : lineValue A B r = A.2 + newtonSlope A B * ((r : ℚ) - A.1) := by rw [lineValue]
    nlinarith [hlvr, hA2pos, hrA, hexp]
  have hlvh : ∀ h, r < h → lineValue A B h < 0 := by
    intro h hh
    have hexp : lineValue A B h = lineValue A B r + newtonSlope A B * ((h : ℚ) - r) := by
      rw [lineValue, lineValue]; ring
    have hpos : (0 : ℚ) < (h : ℚ) - r := by
      have : (r : ℚ) < h := by exact_mod_cast hh
      linarith
    rw [hexp]; nlinarith [hlvr, mul_neg_of_neg_of_pos hslope hpos]
  refine ⟨A, B, hABlt, hBr, hABodd, hslope, hcolA, hcolB, ?_, ?_⟩
  · intro h
    by_cases hhr : h ≤ r
    · rw [← hgcoeff_le h hhr]; exact hsup_g h
    · rw [not_le] at hhr
      refine le_trans (le_of_lt ?_) (hge h)
      rw [show (0 : WithTop ℚ) = ((0 : ℚ) : WithTop ℚ) from WithTop.coe_zero.symm, WithTop.coe_lt_coe]
      exact hlvh h hhr
  · intro h hcol
    by_cases hhr : h ≤ r
    · exact hhonMg A B hAB_zip h (by
        show puiseuxOrder R (g.coeff h) = (lineValue A B h : WithTop ℚ)
        rw [hgcoeff_le h hhr]; exact hcol)
    · exfalso
      rw [not_le] at hhr
      have hc : puiseuxOrder R (P₁.coeff h) = (lineValue A B h : WithTop ℚ) := hcol
      have := hge h
      rw [hc] at this
      rw [show (0 : WithTop ℚ) = ((0 : ℚ) : WithTop ℚ) from WithTop.coe_zero.symm,
        WithTop.coe_le_coe] at this
      exact absurd this (not_le.mpr (hlvh h hhr))

end Azurite.BPR
