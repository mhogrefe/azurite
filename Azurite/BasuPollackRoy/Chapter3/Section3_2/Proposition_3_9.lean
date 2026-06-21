import Azurite.BasuPollackRoy.Chapter3.Section3_2.SemialgebraicallyConnected
import Azurite.BasuPollackRoy.Chapter2.Section2_5.Proposition_2_83
import Azurite.BasuPollackRoy.Chapter2.Section2_5.PNormIsSemialgebraic

/-! # BPR §3.2, Proposition 3.9 — locally constant semialgebraic functions on connected sets

If `S` is a semialgebraically connected semialgebraic set and `f : S → R^ℓ` is a locally constant
semialgebraic function, then `f` is constant. For `d ∈ f(S)`, the fibre `f⁻¹(d)` is open in `S` (local
constancy), and so is its complement `f⁻¹(f(S) ∖ {d})`; if `f` were non-constant these would split
`S` into two non-empty open (hence clopen) semialgebraic pieces, contradicting connectedness. -/

namespace Azurite.BPR

open MvPolynomial

variable {k ℓ : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- **`f` is locally constant on `S`**: every point of `S` has a relative-open neighbourhood on
which `f` agrees with its value at the point. -/
def IsLocallyConstantOn (S : Set (Fin k → R)) (f : (Fin k → R) → (Fin ℓ → R)) : Prop :=
  ∀ x ∈ S, ∃ U, IsOpenIn S U ∧ x ∈ U ∧ ∀ y ∈ U, f y = f x

/-- A subset all of whose points have a relative-open neighbourhood inside it is relatively open. -/
theorem isOpenIn_of_forall_mem {S A : Set (Fin k → R)} (hAS : A ⊆ S)
    (h : ∀ x ∈ A, ∃ V, IsOpen V ∧ x ∈ V ∧ V ∩ S ⊆ A) : IsOpenIn S A := by
  choose! V hVo hxV hVA using h
  refine ⟨⋃ x ∈ A, V x, isOpen_biUnion hVo, Set.Subset.antisymm ?_ ?_⟩
  · intro y hyA
    exact ⟨Set.mem_biUnion hyA (hxV y hyA), hAS hyA⟩
  · rintro y ⟨hyU, hyS⟩
    obtain ⟨x, hxA, hyVx⟩ := Set.mem_iUnion₂.mp hyU
    exact hVA x hxA ⟨hyVx, hyS⟩

omit [IsStrictOrderedRing R] [IsRealClosed R] in
/-- A singleton in `R^ℓ` is semialgebraic. -/
theorem isSemialgebraicSet_singleton (d : Fin ℓ → R) :
    IsSemialgebraicSet ({d} : Set (Fin ℓ → R)) := by
  have he : ({d} : Set (Fin ℓ → R))
      = ⋂ i ∈ (Finset.univ : Finset (Fin ℓ)), {w : Fin ℓ → R | eval w (X i - C (d i)) = 0} := by
    ext w
    simp only [Set.mem_singleton_iff, Set.mem_iInter, Finset.mem_univ, forall_true_left,
      Set.mem_setOf_eq, map_sub, eval_X, eval_C, sub_eq_zero, funext_iff]
  rw [he]; exact IsSemialgebraicSet.iInter_finset _ fun i _ => IsSemialgebraicSet.eqZero _

/-- **BPR Proposition 3.9.** A locally constant semialgebraic function on a semialgebraically
connected semialgebraic set is constant. -/
theorem proposition_3_9 {S : Set (Fin k → R)} {f : (Fin k → R) → (Fin ℓ → R)}
    (hSconn : IsSemialgebraicallyConnected S) (hfsa : IsSemialgebraicFunction S f)
    (hlc : IsLocallyConstantOn S f) : ∀ x ∈ S, ∀ y ∈ S, f x = f y := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x₀, hx₀, x₁, hx₁, hne⟩ := hcon
  set d := f x₀ with hd
  set A : Set (Fin k → R) := S ∩ f ⁻¹' {d} with hA
  set B : Set (Fin k → R) := S ∩ f ⁻¹' {d}ᶜ with hB
  have hmemA : ∀ x, x ∈ A ↔ x ∈ S ∧ f x = d := fun x => by
    simp only [hA, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
  have hmemB : ∀ x, x ∈ B ↔ x ∈ S ∧ f x ≠ d := fun x => by
    simp only [hB, Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
  -- both fibres are open in `S`
  have hAopen : IsOpenIn S A := by
    refine isOpenIn_of_forall_mem Set.inter_subset_left fun x hxA => ?_
    obtain ⟨hxS, hfx⟩ := (hmemA x).mp hxA
    obtain ⟨U, ⟨V, hVo, hUV⟩, hxU, hUc⟩ := hlc x hxS
    refine ⟨V, hVo, (hUV ▸ hxU).1, fun y hy => ?_⟩
    have hyU : y ∈ U := hUV ▸ hy
    exact (hmemA y).mpr ⟨hy.2, by rw [hUc y hyU, hfx]⟩
  have hBopen : IsOpenIn S B := by
    refine isOpenIn_of_forall_mem Set.inter_subset_left fun x hxB => ?_
    obtain ⟨hxS, hfx⟩ := (hmemB x).mp hxB
    obtain ⟨U, ⟨V, hVo, hUV⟩, hxU, hUc⟩ := hlc x hxS
    refine ⟨V, hVo, (hUV ▸ hxU).1, fun y hy => ?_⟩
    have hyU : y ∈ U := hUV ▸ hy
    exact (hmemB y).mpr ⟨hy.2, by rw [hUc y hyU]; exact hfx⟩
  -- complementation: each is the relative complement of the other
  have hABc : A = S \ B := by
    rw [hA, hB]; ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_sdiff,
      Set.mem_compl_iff, not_and]
    tauto
  have hBAc : B = S \ A := by
    rw [hA, hB]; ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_sdiff,
      Set.mem_compl_iff, not_and]
    tauto
  -- the splitting contradicts connectedness
  refine hSconn ⟨A, B, ⟨x₀, (hmemA x₀).mpr ⟨hx₀, rfl⟩⟩, ⟨x₁, (hmemB x₁).mpr ⟨hx₁, hne.symm⟩⟩,
    (proposition_2_83 hfsa).2 (isSemialgebraicSet_singleton d),
    (proposition_2_83 hfsa).2 (isSemialgebraicSet_singleton d).compl,
    hABc ▸ isClosedIn_sdiff_of_isOpenIn hBopen, hBAc ▸ isClosedIn_sdiff_of_isOpenIn hAopen, ?_, ?_⟩
  · rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hxA, hxB⟩
    exact ((hmemB x).mp hxB).2 ((hmemA x).mp hxA).2
  · ext x
    simp only [Set.mem_union]
    constructor
    · rintro (hxA | hxB)
      · exact ((hmemA x).mp hxA).1
      · exact ((hmemB x).mp hxB).1
    · intro hxS
      by_cases hfx : f x = d
      · exact Or.inl ((hmemA x).mpr ⟨hxS, hfx⟩)
      · exact Or.inr ((hmemB x).mpr ⟨hxS, hfx⟩)

end Azurite.BPR
