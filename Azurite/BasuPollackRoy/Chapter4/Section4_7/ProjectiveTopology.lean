import Azurite.BasuPollackRoy.Chapter4.Section4_7.ChartTopology

/-!
# BPR §4.7: the euclidean topology and semialgebraic sets of `ℙ_k(C)`

Following BPR, the euclidean topology and the semialgebraic subsets of projective space are defined
*chart by chart*: a subset `U ⊆ ℙ_k(C)` is **open** when, for every `i = 0, …, k`, its pullback
`φᵢ⁻¹(U ∩ 𝒰ᵢ)` is open in `Cᵏ = R^{2k}`; it is **semialgebraic** when each such pullback is
semialgebraic in `Cᵏ`. Since `φᵢ(x) ∈ 𝒰ᵢ` always, `φᵢ⁻¹(U ∩ 𝒰ᵢ) = φᵢ⁻¹(U) ∩ 𝒰ᵢ`-pullback is just
`chartMap i ⁻¹' (U ∩ chartSet i)`.

The open-set axioms hold because the pullback commutes with intersections and unions (and the chart
covers `𝒰ᵢ`), reducing them to the corresponding facts in `Cᵏ`.
-/

namespace Azurite.BPR.Chapter4

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] {k : ℕ}

/-- **The euclidean topology on `ℙ_k(C)`.** `U` is open iff every chart pullback
`φᵢ⁻¹(U ∩ 𝒰ᵢ)` is open in `Cᵏ`. -/
noncomputable instance : TopologicalSpace (complexProjectiveSpace R k) where
  IsOpen U := ∀ i : Fin (k + 1), IsOpen (chartMap i ⁻¹' (U ∩ chartSet i))
  isOpen_univ := by
    intro i
    have h : chartMap i ⁻¹' (Set.univ ∩ chartSet i) = (Set.univ : Set (Fin k → Ri R)) := by
      ext x
      simp only [Set.univ_inter, Set.mem_preimage, Set.mem_univ, iff_true, chartSet]
      exact Set.mem_range_self x
    rw [h]; exact isOpen_univ
  isOpen_inter := by
    intro U V hU hV i
    have h : chartMap i ⁻¹' ((U ∩ V) ∩ chartSet i)
        = (chartMap i ⁻¹' (U ∩ chartSet i)) ∩ (chartMap i ⁻¹' (V ∩ chartSet i)) := by
      rw [← Set.preimage_inter]; congr 1; ext p; simp only [Set.mem_inter_iff]; tauto
    rw [h]; exact (hU i).inter (hV i)
  isOpen_sUnion := by
    intro S hS i
    have h : chartMap i ⁻¹' (⋃₀ S ∩ chartSet i)
        = ⋃ U ∈ S, chartMap i ⁻¹' (U ∩ chartSet i) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_sUnion, Set.mem_iUnion]
      tauto
    rw [h]; exact isOpen_biUnion (fun U hU => hS U hU i)

/-- **Fidelity to BPR.** A subset of `ℙ_k(C)` is open exactly when each chart pullback is open. -/
theorem isOpenP_iff {U : Set (complexProjectiveSpace R k)} :
    IsOpen U ↔ ∀ i : Fin (k + 1), IsOpen (chartMap i ⁻¹' (U ∩ chartSet i)) :=
  Iff.rfl

/-- **BPR §4.7 (semialgebraic subset of `ℙ_k(C)`).** `S` is semialgebraic iff every chart pullback
`φᵢ⁻¹(S ∩ 𝒰ᵢ)` is semialgebraic in `Cᵏ = R^{2k}`. -/
def IsSemialgebraicSetP (S : Set (complexProjectiveSpace R k)) : Prop :=
  ∀ i : Fin (k + 1), IsSemialgebraicSetC (chartMap i ⁻¹' (S ∩ chartSet i) : Set (Fin k → Ri R))

/-- For any charts `m, i`, the pullback of `𝒰ᵢ` into the `m`-th chart is the overlap. -/
theorem chartMap_preimage_chartSet_inter (m i : Fin (k + 1)) :
    chartMap m ⁻¹' (chartSet i ∩ chartSet m) = (chartOverlap m i : Set (Fin k → Ri R)) := by
  rw [chartOverlap, Set.inter_comm]

/-- **BPR §4.7 (Note).** Each chart domain `𝒰ᵢ` is open in `ℙ_k(C)`. -/
theorem isOpen_chartSet (i : Fin (k + 1)) :
    IsOpen (chartSet i : Set (complexProjectiveSpace R k)) := by
  rw [isOpenP_iff]
  intro m
  rw [chartMap_preimage_chartSet_inter]
  exact isOpen_chartOverlap m i

/-- **BPR §4.7 (Note).** Each chart domain `𝒰ᵢ` is a semialgebraic subset of `ℙ_k(C)`. -/
theorem isSemialgebraicSetP_chartSet (i : Fin (k + 1)) :
    IsSemialgebraicSetP (chartSet i : Set (complexProjectiveSpace R k)) := by
  intro m
  rw [chartMap_preimage_chartSet_inter]
  exact isSemialgebraicSetC_chartOverlap m i

end Azurite.BPR.Chapter4
