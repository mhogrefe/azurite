import Azurite.BasuPollackRoy.Chapter4.Section4_7.ProjectiveTopology

/-!
# BPR §4.7: semialgebraic path connectedness in `ℙ_k(C)`

A semialgebraic subset `S ⊆ ℙ_k(C)` is **semialgebraically path connected** if any two of its points
can be joined by a continuous path `γ : [0,1] → S` whose graph is semialgebraic. The path parameter is
modeled, as elsewhere in the project, by `R¹ = Fin 1 → R` (so `[0,1]` is `Set.Icc 0 1` and the
endpoints are `0, 1 : Fin 1 → R`), with `R¹` carrying the §3.1 euclidean topology and `ℙ_k(C)` the
chart topology of `ProjectiveTopology`.

The graph of `γ` lives in `R¹ × ℙ_k(C)`; its semialgebraicity is the mixed real–projective notion
`IsSemialgebraicSetRP`, defined chart by chart on the `ℙ_k(C)` factor (realifying `Cᵏ = R^{2k}`).
-/

namespace Azurite.BPR.Chapter4

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] {p k : ℕ}

/-- **Semialgebraic subset of `Rᵖ × ℙ_k(C)`.** A subset `T` is semialgebraic when, for every chart
`i`, its pullback along `id × φᵢ` — the set of `(t, x) ∈ Rᵖ × Cᵏ` with `(t, φᵢ(x)) ∈ T` — is a
semialgebraic subset of `Rᵖ × Cᵏ = R^{p + 2k}` (recording `t` in the first `p` coordinates and the
realification of `x` in the last `2k`). -/
def IsSemialgebraicSetRP (T : Set ((Fin p → R) × complexProjectiveSpace R k)) : Prop :=
  ∀ i : Fin (k + 1),
    IsSemialgebraicSet
      {w : Fin (p + (k + k)) → R |
        (w ∘ Fin.castAdd (k + k), chartMap i (realEquiv.symm (w ∘ Fin.natAdd p))) ∈ T}

/-- **BPR §4.7 (semialgebraic path connectedness).** `S ⊆ ℙ_k(C)` is *semialgebraically path
connected* if for every `x, y ∈ S` there is a continuous map `γ : [0,1] → ℙ_k(C)` taking values in
`S`, with `γ(0) = x`, `γ(1) = y`, and semialgebraic graph. -/
def IsSemialgebraicallyPathConnected (S : Set (complexProjectiveSpace R k)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S,
    ∃ γ : (Fin 1 → R) → complexProjectiveSpace R k,
      ContinuousOn γ (Set.Icc 0 1) ∧
      Set.MapsTo γ (Set.Icc 0 1) S ∧
      γ 0 = x ∧ γ 1 = y ∧
      IsSemialgebraicSetRP
        {tp : (Fin 1 → R) × complexProjectiveSpace R k | tp.1 ∈ Set.Icc 0 1 ∧ tp.2 = γ tp.1}

end Azurite.BPR.Chapter4
