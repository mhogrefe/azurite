import Azurite.BasuPollackRoy.Chapter3.Section3_1.Proposition_3_3
import Mathlib.Topology.Compactness.Compact

/-! # BPR §3.4 — closed bounded ≠ compact: the abstract obstruction

Over a general real closed field `R`, the closed bounded interval `[0, 1] ⊆ R¹` (`unitIcc`) need not
be **compact** (Mathlib's topological `IsCompact`, for the euclidean ball topology of §3.1). The
obstruction is always a *gap* in the order of `R` inside `[0, 1]`: a family of "two-sided tails"
`{u | u₀ < r ∨ s < u₀}` indexed by pairs `(r, s)` with `r` below the gap and `s` above it. Such a
family covers `[0, 1]` (every point lies on one side of the gap) but no finite subfamily does (between
the finitely many left endpoints and right endpoints there is always a point of `R`, by density).

This file proves that abstract obstruction (`not_isCompact_unitIcc_of_cover`); the two concrete
examples (`R = ℝ_alg` with a transcendental gap, and `R = R⟨ε⟩` with the infinitesimal gap) are in
the sibling files. -/

namespace Azurite.BPR

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- The closed unit interval `[0, 1]` as a subset of `R¹ = Fin 1 → R`. -/
def unitIcc : Set (Fin 1 → R) := {u | 0 ≤ u 0 ∧ u 0 ≤ 1}

/-- The half-space `{u | u₀ < r}` is open. -/
theorem isOpen_setOf_coord_lt (r : R) : IsOpen {u : Fin 1 → R | u 0 < r} := by
  rw [isOpen_iff]
  intro x hx
  refine ⟨x, r - x 0, by simp only [Set.mem_ofPred_eq] at hx; linarith,
    mem_openBall_self x (by simp only [Set.mem_ofPred_eq] at hx; linarith), ?_⟩
  intro u hu
  rw [mem_openBall_iff_norm (by simp only [Set.mem_ofPred_eq] at hx; linarith),
    euclideanNorm_fin_one, Pi.sub_apply] at hu
  simp only [Set.mem_ofPred_eq] at hx ⊢
  have := (abs_lt.mp hu).2
  linarith

/-- The half-space `{u | s < u₀}` is open. -/
theorem isOpen_setOf_coord_gt (s : R) : IsOpen {u : Fin 1 → R | s < u 0} := by
  rw [isOpen_iff]
  intro x hx
  refine ⟨x, x 0 - s, by simp only [Set.mem_ofPred_eq] at hx; linarith,
    mem_openBall_self x (by simp only [Set.mem_ofPred_eq] at hx; linarith), ?_⟩
  intro u hu
  rw [mem_openBall_iff_norm (by simp only [Set.mem_ofPred_eq] at hx; linarith),
    euclideanNorm_fin_one, Pi.sub_apply] at hu
  simp only [Set.mem_ofPred_eq] at hx ⊢
  have := (abs_lt.mp hu).1
  linarith

/-- **The abstract non-compactness obstruction.** Let `C ⊆ R × R` be a set of pairs `(r, s)` with:
`hcover` — every point of `[0, 1]` lies below some left endpoint or above some right endpoint;
`hsep` — every left endpoint is `<` every right endpoint (the pairs straddle a common gap);
`hlo`/`hhi` — the endpoints lie in `(0, 1)`. Then `[0, 1] ⊆ R¹` is not compact: the open cover
`{u | u₀ < r ∨ s < u₀}` has no finite subcover. -/
theorem not_isCompact_unitIcc_of_cover (C : Set (R × R))
    (hcover : ∀ u : Fin 1 → R, 0 ≤ u 0 → u 0 ≤ 1 → ∃ p ∈ C, u 0 < p.1 ∨ p.2 < u 0)
    (hsep : ∀ p ∈ C, ∀ q ∈ C, p.1 < q.2)
    (hlo : ∀ p ∈ C, 0 < p.1) (hhi : ∀ p ∈ C, p.2 < 1) :
    ¬ IsCompact (unitIcc : Set (Fin 1 → R)) := by
  intro hcompact
  rw [isCompact_iff_finite_subcover] at hcompact
  set U : {p : R × R // p ∈ C} → Set (Fin 1 → R) :=
    fun p => {u | u 0 < p.val.1 ∨ p.val.2 < u 0} with hU
  have hUopen : ∀ p, IsOpen (U p) := by
    intro p
    rw [hU]
    show IsOpen {u : Fin 1 → R | u 0 < p.val.1 ∨ p.val.2 < u 0}
    rw [Set.ofPred_or]
    exact (isOpen_setOf_coord_lt _).union (isOpen_setOf_coord_gt _)
  have hUcover : (unitIcc : Set (Fin 1 → R)) ⊆ ⋃ p, U p := by
    intro u hu
    obtain ⟨p, hpC, hpu⟩ := hcover u hu.1 hu.2
    exact Set.mem_iUnion.mpr ⟨⟨p, hpC⟩, hpu⟩
  obtain ⟨T, hT⟩ := hcompact U hUopen hUcover
  rcases T.eq_empty_or_nonempty with hTe | hTne
  · have hmem : (fun _ : Fin 1 => (1 / 2 : R)) ∈ (unitIcc : Set (Fin 1 → R)) := by
      refine ⟨by norm_num, by norm_num⟩
    have hcontra := hT hmem
    rw [hTe] at hcontra
    simp at hcontra
  · set maxR := T.sup' hTne (fun p => p.val.1) with hmaxR
    set minS := T.inf' hTne (fun p => p.val.2) with hminS
    have hmaxpos : 0 < maxR := by
      rw [hmaxR, Finset.lt_sup'_iff]
      obtain ⟨p, hp⟩ := hTne
      exact ⟨p, hp, hlo p.val p.property⟩
    have hminlt1 : minS < 1 := by
      rw [hminS, Finset.inf'_lt_iff]
      obtain ⟨p, hp⟩ := hTne
      exact ⟨p, hp, hhi p.val p.property⟩
    have hml : maxR < minS := by
      rw [hmaxR, Finset.sup'_lt_iff]
      intro p hpT
      rw [hminS, Finset.lt_inf'_iff]
      intro q hqT
      exact hsep p.val p.property q.val q.property
    set z : R := (maxR + minS) / 2 with hz
    have hz1 : maxR < z := by rw [hz]; linarith
    have hz2 : z < minS := by rw [hz]; linarith
    have hzunit : (fun _ : Fin 1 => z) ∈ (unitIcc : Set (Fin 1 → R)) :=
      ⟨by simp only; linarith, by simp only; linarith⟩
    obtain ⟨p, hpT, hpz⟩ := Set.mem_iUnion₂.mp (hT hzunit)
    have hpz' : z < p.val.1 ∨ p.val.2 < z := hpz
    have hle_max : p.val.1 ≤ maxR := by rw [hmaxR]; exact Finset.le_sup' (fun p => p.val.1) hpT
    have hge_min : minS ≤ p.val.2 := by rw [hminS]; exact Finset.inf'_le (fun p => p.val.2) hpT
    rcases hpz' with h | h <;> linarith

end Azurite.BPR
