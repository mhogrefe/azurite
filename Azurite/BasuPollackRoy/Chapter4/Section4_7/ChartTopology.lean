import Azurite.BasuPollackRoy.Chapter4.Section4_7.ChartOverlap
import Azurite.BasuPollackRoy.Chapter4.Section4_7.ComplexPolySemialgebraic
import Azurite.BasuPollackRoy.Chapter3.Section3_1.Topology
import Mathlib.Topology.Order

/-!
# BPR §4.7: the chart overlaps are open

We equip `Cᵏ = R^{2k}` with the euclidean (ball) topology of §3.1, transported along the realification
`realEquiv : Cᵏ ≅ R^{2k}` (the induced topology, making `realEquiv` an open embedding). The locus
`{x | x_a ≠ 0}` is open — around a point with `x_a ≠ 0` a small ball keeps the `a`-th real or
imaginary part bounded away from `0` — and hence so is every chart overlap
`φᵢ⁻¹(𝒰ᵢ ∩ 𝒰ⱼ)`. Together with the semialgebraic structure (`ChartOverlap`, `ChartTransition`), this
completes BPR's "semialgebraic open" claim.
-/

namespace Azurite.BPR.Chapter4

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] {k : ℕ}

omit [IsRealClosed R] in
/-- A single squared coordinate is at most the squared euclidean norm. -/
theorem coord_sq_le_euclideanNormSq {n : ℕ} (v : Fin n → R) (i : Fin n) :
    v i ^ 2 ≤ euclideanNormSq v :=
  Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)

/-- The locus where a real coordinate is nonzero is open in the euclidean topology on `Rⁿ`. -/
theorem isOpen_coord_ne_zero {n : ℕ} (i : Fin n) :
    IsOpen {w : Fin n → R | w i ≠ 0} := by
  rw [isOpen_iff]
  intro x hx
  refine ⟨x, |x i|, abs_pos.mpr hx, mem_openBall_self x (abs_pos.mpr hx), ?_⟩
  intro y hy
  rw [mem_openBall] at hy
  rw [Set.mem_setOf_eq]
  intro hy0
  have h1 : (y - x) i ^ 2 ≤ euclideanNormSq (y - x) := coord_sq_le_euclideanNormSq _ i
  rw [Pi.sub_apply, hy0, zero_sub, neg_sq] at h1
  rw [sq_abs] at hy
  linarith

/-- **The euclidean topology on `Cᵏ`**, transported from `R^{2k}` along the realification. -/
noncomputable instance : TopologicalSpace (Fin k → Ri R) :=
  TopologicalSpace.induced realEquiv inferInstance

/-- The locus where a complex coordinate is nonzero is open in `Cᵏ`: it is the preimage under
`realEquiv` of the open set where the corresponding real or imaginary part is nonzero. -/
theorem isOpen_coordC_ne_zero (a : Fin k) :
    IsOpen {x : Fin k → Ri R | x a ≠ 0} := by
  rw [isOpen_induced_iff]
  refine ⟨{w : Fin (k + k) → R | w (Fin.castAdd k a) ≠ 0 ∨ w (Fin.natAdd k a) ≠ 0}, ?_, ?_⟩
  · have hunion : {w : Fin (k + k) → R | w (Fin.castAdd k a) ≠ 0 ∨ w (Fin.natAdd k a) ≠ 0}
        = {w | w (Fin.castAdd k a) ≠ 0} ∪ {w | w (Fin.natAdd k a) ≠ 0} := by
      ext w; simp only [Set.mem_setOf_eq, Set.mem_union]
    rw [hunion]
    exact (isOpen_coord_ne_zero _).union (isOpen_coord_ne_zero _)
  · ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq, realEquiv_apply_castAdd, realEquiv_apply_natAdd,
      reL_eq_zero_and_imL_eq_zero_iff, not_and_or, ne_eq]

/-- **BPR §4.7 (Note, part 4 — open).** The chart overlap `φᵢ⁻¹(𝒰ᵢ ∩ 𝒰ⱼ)` is open in `Cᵏ = R^{2k}`. -/
theorem isOpen_chartOverlap (i j : Fin (k + 1)) :
    IsOpen (chartOverlap i j : Set (Fin k → Ri R)) := by
  rw [chartOverlap_eq]
  by_cases hji : j = i
  · subst hji
    have huniv : {x : Fin k → Ri R | (Fin.insertNth j (1 : Ri R) x : Fin (k + 1) → Ri R) j ≠ 0}
        = (Set.univ : Set (Fin k → Ri R)) := by
      ext x; simp [Fin.insertNth_apply_same]
    rw [huniv]; exact isOpen_univ
  · obtain ⟨b, hb⟩ := Fin.exists_succAbove_eq hji
    have hcoord : {x : Fin k → Ri R | (Fin.insertNth i (1 : Ri R) x : Fin (k + 1) → Ri R) j ≠ 0}
        = {x : Fin k → Ri R | x b ≠ 0} := by
      ext x; simp only [Set.mem_setOf_eq, ← hb, Fin.insertNth_apply_succAbove]
    rw [hcoord]; exact isOpen_coordC_ne_zero b

end Azurite.BPR.Chapter4
