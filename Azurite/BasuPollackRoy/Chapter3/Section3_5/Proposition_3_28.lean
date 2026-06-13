import Azurite.BasuPollackRoy.Chapter3.Section3_5.SDiffeomorphism
import Azurite.BasuPollackRoy.Chapter3.Section3_5.InverseSmoothness

/-! # BPR §3.5, Proposition 3.28(a) — open subsets of submanifolds

**A semialgebraic open subset of an `𝒮^∞` submanifold `V` of dimension `i` is an `𝒮^∞`
submanifold of dimension `i`.**

"Clear": near a point `x` of the open subset `W`, take `V`'s chart `ϕ : U → Ω` and shrink
the target to `Ω' = Ω ∩ B(x, r)` for a ball with `V ∩ B(x, r) ⊆ W`; the restricted
`ϕ : U ∩ ϕ⁻¹(Ω') → Ω'` (`IsSInftyDiffeomorphism.restrict`) is a chart realizing `W` as a
submanifold, since `ϕ(U' ∩ (R^i × {0})) = V ∩ Ω' = W ∩ Ω'`.

(Part (b) — that a `j`-dimensional submanifold inside an `i`-dimensional one forces
`j ≤ i` — needs the tangent-space *dimension* theory (`finrank` of the tangent space equals
the submanifold dimension, via invertibility of `dϕ(0)`) and tangent-space monotonicity; it
is left for a separate development.) -/

namespace Azurite.BPR

open MvPolynomial

variable {k : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [IsRealClosed R]

/-- `𝒮^∞` membership restricts to a semialgebraic subdomain (with retargeting). -/
theorem SClassInfty.mono {p : ℕ} {f : (Fin k → R) → (Fin p → R)}
    {U U' : Set (Fin k → R)} {B B' : Set (Fin p → R)}
    (h : f ∈ SClassInfty U B) (hU' : IsSemialgebraicSet U') (hsub : U' ⊆ U)
    (hmaps : Set.MapsTo f U' B') : f ∈ SClassInfty U' B' := by
  rw [mem_sClassInfty_iff]
  intro ℓ
  exact ⟨hmaps, fun l => ((mem_sClassInfty_iff.mp h ℓ).2 l).mono_set hU' hsub⟩

/-- The source map of an `𝒮^∞`-diffeomorphism is continuous. -/
theorem IsSInftyDiffeomorphism.continuousOn_source [Nonempty (Fin k)]
    {U Ω : Set (Fin k → R)} {ϕ ϕinv : (Fin k → R) → (Fin k → R)}
    (h : IsSInftyDiffeomorphism U Ω ϕ ϕinv) : ContinuousOn ϕ U := by
  refine continuousOn_of_components fun l => ?_
  exact (((mem_sClassInfty_iff.mp h.mem_sClassInfty 1).2 l).isSemialgContinuousOn).2

/-- **Restriction of an `𝒮^∞`-diffeomorphism** to a semialgebraic open subset `Ω' ⊆ Ω` of
the target (and the corresponding source `U ∩ ϕ⁻¹(Ω')`). -/
theorem IsSInftyDiffeomorphism.restrict [Nonempty (Fin k)]
    {U Ω : Set (Fin k → R)} {ϕ ϕinv : (Fin k → R) → (Fin k → R)}
    (h : IsSInftyDiffeomorphism U Ω ϕ ϕinv)
    {Ω' : Set (Fin k → R)} (hΩ'open : IsOpen Ω') (hΩ'sa : IsSemialgebraicSet Ω')
    (hΩ'sub : Ω' ⊆ Ω) :
    IsSInftyDiffeomorphism (U ∩ ϕ ⁻¹' Ω') Ω' ϕ ϕinv := by
  have hϕsa : IsSemialgebraicFunction U ϕ :=
    isSemialgebraicFunction_of_coords fun l =>
      (((mem_sClassInfty_iff.mp h.mem_sClassInfty 1).2 l).isSemialgContinuousOn).1
  have hU'sub : U ∩ ϕ ⁻¹' Ω' ⊆ U := fun _ hz => hz.1
  have hU'sa : IsSemialgebraicSet (U ∩ ϕ ⁻¹' Ω') := (proposition_2_83 hϕsa).2 hΩ'sa
  have hϕinvMaps : Set.MapsTo ϕinv Ω U := by
    intro y hy
    obtain ⟨z, hzU, hϕz⟩ := h.bijOn.surjOn hy
    rw [← hϕz, h.invOn.1 hzU]
    exact hzU
  -- `ϕinv` maps `Ω'` into the restricted source
  have hϕinvMaps' : Set.MapsTo ϕinv Ω' (U ∩ ϕ ⁻¹' Ω') := by
    intro y hy
    exact ⟨hϕinvMaps (hΩ'sub hy),
      by rw [Set.mem_preimage, h.invOn.2 (hΩ'sub hy)]; exact hy⟩
  exact
  { isOpen_source :=
      ContinuousOn.isOpen_inter_preimage h.continuousOn_source h.isOpen_source hΩ'open
    isSemialgebraic_source := hU'sa
    isOpen_target := hΩ'open
    isSemialgebraic_target := hΩ'sa
    bijOn := ⟨fun _ hz => hz.2, h.bijOn.injOn.mono hU'sub, fun y hy =>
      ⟨ϕinv y, hϕinvMaps' hy, h.invOn.2 (hΩ'sub hy)⟩⟩
    mem_sClassInfty := SClassInfty.mono h.mem_sClassInfty hU'sa hU'sub fun _ hz => hz.2
    invOn := ⟨fun _ hz => h.invOn.1 hz.1, fun _ hy => h.invOn.2 (hΩ'sub hy)⟩
    inv_mem_sClassInfty := SClassInfty.mono h.inv_mem_sClassInfty hΩ'sa hΩ'sub hϕinvMaps' }

/-- **BPR Proposition 3.28(a).** A semialgebraic, relatively open subset `W` of an `𝒮^∞`
submanifold `V` of dimension `i` is itself an `𝒮^∞` submanifold of dimension `i`. -/
theorem proposition_3_28a {i : ℕ} {V W : Set (Fin k → R)}
    (hV : IsSInftySubmanifold i V) (hWsa : IsSemialgebraicSet W) (hWV : W ⊆ V)
    (hWopen : ∀ x ∈ W, ∃ r : R, 0 < r ∧ V ∩ openBall x r ⊆ W) :
    IsSInftySubmanifold i W := by
  refine ⟨hWsa, fun x hx => ?_⟩
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · -- `k = 0`: everything is a subsingleton, so `W = V` and `V`'s chart works
    subst hk0
    obtain ⟨U, Ω, ϕ, ϕinv, hchart, h0U, hxΩ, hϕ0, hslice⟩ := hV.2 x (hWV hx)
    have hWeqV : W = V := le_antisymm hWV fun z _ => (Subsingleton.elim x z) ▸ hx
    exact ⟨U, Ω, ϕ, ϕinv, hchart, h0U, hxΩ, hϕ0, by rw [hWeqV]; exact hslice⟩
  haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  obtain ⟨U, Ω, ϕ, ϕinv, hchart, h0U, hxΩ, hϕ0, hslice⟩ := hV.2 x (hWV hx)
  obtain ⟨r, hr, hball⟩ := hWopen x hx
  set Ω' : Set (Fin k → R) := Ω ∩ openBall x r with hΩ'def
  have hΩ'open : IsOpen Ω' := hchart.isOpen_target.inter (isOpen_openBall x hr)
  have hΩ'sa : IsSemialgebraicSet Ω' :=
    hchart.isSemialgebraic_target.inter (isSemialgebraicSet_openBall x r)
  have hΩ'sub : Ω' ⊆ Ω := fun _ hz => hz.1
  have hxΩ' : x ∈ Ω' := ⟨hxΩ, mem_openBall_self x hr⟩
  refine ⟨U ∩ ϕ ⁻¹' Ω', Ω', ϕ, ϕinv, hchart.restrict hΩ'open hΩ'sa hΩ'sub,
    ⟨h0U, by rw [Set.mem_preimage, hϕ0]; exact hxΩ'⟩, hxΩ', hϕ0, ?_⟩
  -- the slice condition
  have hreorder : (U ∩ ϕ ⁻¹' Ω') ∩ coordSubspace k i
      = (U ∩ coordSubspace k i) ∩ ϕ ⁻¹' Ω' := by
    ext z; simp only [Set.mem_inter_iff, Set.mem_preimage]; tauto
  rw [hreorder, Set.image_inter_preimage, hslice]
  -- `(V ∩ Ω) ∩ Ω' = W ∩ Ω'`
  ext z
  constructor
  · rintro ⟨⟨hzV, _⟩, hzΩ'⟩
    exact ⟨hball ⟨hzV, hzΩ'.2⟩, hzΩ'⟩
  · rintro ⟨hzW, hzΩ'⟩
    exact ⟨⟨hWV hzW, hzΩ'.1⟩, hzΩ'⟩

end Azurite.BPR
