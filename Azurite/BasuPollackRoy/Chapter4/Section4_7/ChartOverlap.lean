import Azurite.BasuPollackRoy.Chapter4.Section4_7.AffineCharts
import Azurite.BasuPollackRoy.Chapter4.Section4_7.SemialgebraicC

/-!
# BPR §4.7: the chart overlaps are semialgebraic

The pulled-back overlap `φᵢ⁻¹(𝒰ᵢ ∩ 𝒰ⱼ) ⊆ Cᵏ` is the locus where the `j`-th homogeneous coordinate of
`φᵢ(x)` is nonzero. After inserting a `1` in coordinate `i`, that coordinate is either the constant
`1` (when `j = i`, so the overlap is all of `Cᵏ`) or one of the affine coordinates `x_b` (when
`j = i.succAbove b`, so the overlap is `{x | x_b ≠ 0}`). Either way it is semialgebraic over `C`.
-/

namespace Azurite.BPR.Chapter4

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] {k : ℕ}

/-- The pulled-back chart overlap `φᵢ⁻¹(𝒰ᵢ ∩ 𝒰ⱼ) ⊆ Cᵏ`. -/
def chartOverlap (i j : Fin (k + 1)) : Set (Fin k → Ri R) :=
  chartMap i ⁻¹' (chartSet i ∩ chartSet j)

set_option linter.unusedSectionVars false in
/-- The overlap is the locus where the `j`-th coordinate of the vector `insertNth i 1 x` is nonzero
(the `i`-th coordinate is the constant `1`, so the `𝒰ᵢ` condition is automatic). -/
theorem chartOverlap_eq (i j : Fin (k + 1)) :
    chartOverlap i j
      = {x : Fin k → Ri R | (Fin.insertNth i (1 : Ri R) x : Fin (k + 1) → Ri R) j ≠ 0} := by
  ext x
  obtain ⟨c, hc, hrep⟩ := exists_rep_smul (Fin.insertNth i 1 x) (insertNth_one_ne_zero i x)
  constructor
  · intro hx
    simp only [chartOverlap, Set.mem_preimage, Set.mem_inter_iff, chartSet_eq,
      Set.mem_ofPred_eq] at hx
    have h2 := hx.2
    rw [chartMap, hrep, Pi.smul_apply, smul_eq_mul, ne_eq, mul_eq_zero, not_or] at h2
    exact h2.2
  · intro hx
    simp only [Set.mem_ofPred_eq] at hx
    simp only [chartOverlap, Set.mem_preimage, Set.mem_inter_iff, chartSet_eq, Set.mem_ofPred_eq]
    rw [chartMap, hrep]
    refine ⟨?_, ?_⟩
    · rw [Pi.smul_apply, smul_eq_mul, Fin.insertNth_apply_same, mul_one]; exact hc
    · rw [Pi.smul_apply, smul_eq_mul, ne_eq, mul_eq_zero, not_or]; exact ⟨hc, hx⟩

/-- **BPR §4.7 (Note, part 4 — semialgebraic).** The pulled-back chart overlap
`φᵢ⁻¹(𝒰ᵢ ∩ 𝒰ⱼ)` is a semialgebraic subset of `Cᵏ`. -/
theorem isSemialgebraicSetC_chartOverlap (i j : Fin (k + 1)) :
    IsSemialgebraicSetC (chartOverlap i j : Set (Fin k → Ri R)) := by
  rw [chartOverlap_eq]
  by_cases hji : j = i
  · subst hji
    have huniv : {x : Fin k → Ri R | (Fin.insertNth j (1 : Ri R) x : Fin (k + 1) → Ri R) j ≠ 0}
        = (Set.univ : Set (Fin k → Ri R)) := by
      ext x; simp [Fin.insertNth_apply_same]
    rw [huniv]; exact IsSemialgebraicSetC.univ
  · obtain ⟨b, hb⟩ := Fin.exists_succAbove_eq hji
    have hcoord : {x : Fin k → Ri R | (Fin.insertNth i (1 : Ri R) x : Fin (k + 1) → Ri R) j ≠ 0}
        = {x : Fin k → Ri R | x b ≠ 0} := by
      ext x; simp only [Set.mem_ofPred_eq, ← hb, Fin.insertNth_apply_succAbove]
    rw [hcoord]; exact isSemialgebraicSetC_coord_ne_zero b

end Azurite.BPR.Chapter4
