import Azurite.BasuPollackRoy.Chapter3.Section3_1.Topology
import Mathlib.Topology.Closure
import Mathlib.Topology.Order
import Mathlib.Topology.Constructions

/-! # BPR §3.1 — closure, interior, and the relative topology on `R^k`

The **closure** `S̄` of `S` is the intersection of all closed sets containing `S`; the **interior**
`S°` is the union of all open subsets of `S` (equivalently, of all open balls in `S`). Since the
euclidean topology on `R^k` is inherited from Mathlib (`Topology.lean`), these are exactly Mathlib's
`closure` and `interior` — *definitionally* the BPR notions (`closure_eq_sInter`,
`interior_eq_sUnion`).

A subset `T` is **open in `S`** (`IsOpenIn`) if it is the intersection of an open set with `S`, and
**closed in `S`** (`IsClosedIn`) if it is the intersection of a closed set with `S` — the subspace
topology, here phrased on subsets of `R^k` as BPR does. The lemmas
`isOpenIn_iff_isOpen_subtype`/`isClosedIn_iff_isClosed_subtype` identify these with Mathlib's
subspace topology on the subtype `↥S`. -/

namespace Azurite.BPR

variable {k : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-! ### Closure and interior -/

/-- **Closure** = intersection of all closed sets containing `S` (BPR's definition; this is Mathlib's
`closure`, by definition). -/
theorem closure_eq_sInter (S : Set (Fin k → R)) :
    closure S = ⋂₀ {F : Set (Fin k → R) | IsClosed F ∧ S ⊆ F} := rfl

/-- **Interior** = union of all open subsets of `S` (BPR's definition; Mathlib's `interior`). -/
theorem interior_eq_sUnion (S : Set (Fin k → R)) :
    interior S = ⋃₀ {U : Set (Fin k → R) | IsOpen U ∧ U ⊆ S} := rfl

/-- The interior of `S` is also the union of all open balls contained in `S`. -/
theorem mem_interior_iff_ball {S : Set (Fin k → R)} {x : Fin k → R} :
    x ∈ interior S ↔ ∃ (c : Fin k → R) (r : R), 0 < r ∧ x ∈ openBall c r ∧ openBall c r ⊆ S := by
  rw [mem_interior]
  constructor
  · rintro ⟨t, htS, htopen, hxt⟩
    obtain ⟨c, r, hr, hxc, hsub⟩ := (isOpen_iff.mp htopen) x hxt
    exact ⟨c, r, hr, hxc, hsub.trans htS⟩
  · rintro ⟨c, r, hr, hxc, hsub⟩
    exact ⟨openBall c r, hsub, isOpen_openBall c hr, hxc⟩

/-! ### The relative (subspace) topology -/

/-- A subset `T` is **open in `S`** if it is the intersection of an open set with `S`. -/
def IsOpenIn (S T : Set (Fin k → R)) : Prop := ∃ U, IsOpen U ∧ T = U ∩ S

/-- A subset `T` is **closed in `S`** if it is the intersection of a closed set with `S`. -/
def IsClosedIn (S T : Set (Fin k → R)) : Prop := ∃ F, IsClosed F ∧ T = F ∩ S

theorem isOpenIn_self (S : Set (Fin k → R)) : IsOpenIn S S :=
  ⟨Set.univ, isOpen_univ, (Set.univ_inter S).symm⟩

theorem isOpenIn_empty (S : Set (Fin k → R)) : IsOpenIn S ∅ :=
  ⟨∅, isOpen_empty, (Set.empty_inter S).symm⟩

theorem isClosedIn_self (S : Set (Fin k → R)) : IsClosedIn S S :=
  ⟨Set.univ, isClosed_univ, (Set.univ_inter S).symm⟩

theorem isClosedIn_empty (S : Set (Fin k → R)) : IsClosedIn S ∅ :=
  ⟨∅, isClosed_empty, (Set.empty_inter S).symm⟩

/-- For `T ⊆ S`, `T` is open in `S` iff it is open in the subspace topology on `S` — connecting
BPR's relative notion to Mathlib's subspace topology. -/
theorem isOpenIn_iff_isOpen_subtype {S T : Set (Fin k → R)} (hTS : T ⊆ S) :
    IsOpenIn S T ↔ IsOpen (Subtype.val ⁻¹' T : Set S) := by
  rw [isOpen_induced_iff]
  constructor
  · rintro ⟨U, hU, rfl⟩
    exact ⟨U, hU, by ext x; simp [Set.mem_preimage]⟩
  · rintro ⟨U, hU, hUT⟩
    refine ⟨U, hU, ?_⟩
    ext x
    refine ⟨fun hx => ⟨(hUT ▸ hx : (⟨x, hTS hx⟩ : S) ∈ Subtype.val ⁻¹' U), hTS hx⟩, ?_⟩
    rintro ⟨hxU, hxS⟩
    have h : (⟨x, hxS⟩ : S) ∈ Subtype.val ⁻¹' U := hxU
    rw [hUT] at h; exact h

/-- For `T ⊆ S`, `T` is closed in `S` iff it is closed in the subspace topology on `S`. -/
theorem isClosedIn_iff_isClosed_subtype {S T : Set (Fin k → R)} (hTS : T ⊆ S) :
    IsClosedIn S T ↔ IsClosed (Subtype.val ⁻¹' T : Set S) := by
  rw [isClosed_induced_iff]
  constructor
  · rintro ⟨F, hF, rfl⟩
    exact ⟨F, hF, by ext x; simp [Set.mem_preimage]⟩
  · rintro ⟨F, hF, hFT⟩
    refine ⟨F, hF, ?_⟩
    ext x
    refine ⟨fun hx => ⟨(hFT ▸ hx : (⟨x, hTS hx⟩ : S) ∈ Subtype.val ⁻¹' F), hTS hx⟩, ?_⟩
    rintro ⟨hxF, hxS⟩
    have h : (⟨x, hxS⟩ : S) ∈ Subtype.val ⁻¹' F := hxF
    rw [hFT] at h; exact h

end Azurite.BPR
