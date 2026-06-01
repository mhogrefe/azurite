import Azurite.BasuPollackRoy.Chapter2.Section2_5.Theorem_2_77
import Azurite.BasuPollackRoy.Chapter2.Section2_5.SemialgebraicFunction

/-! # BPR Proposition 2.83: image and inverse image under a semialgebraic function

If `f : S → T` is semialgebraic, `S' ⊆ S` semialgebraic, then `f(S')` is semialgebraic; if
`T' ⊆ T` semialgebraic, then `f⁻¹(T')` is semialgebraic. Both are projections of an
intersection with the graph, hence semialgebraic by the projection theorem (BPR Theorem
2.76, here packaged as the cylindrical projections `exists_update`).

The two projections `{y | ∃ x, (x, y) ∈ W}` and `{x | ∃ y, (x, y) ∈ W}` of a semialgebraic
`W ⊆ R^{k+ℓ}` are the reusable core (`IsSemialgebraicSet.exists_append_left` / `_right`).
-/

namespace Azurite.BPR

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

omit [IsRealClosed R] in
/-- Absolute semialgebraic sets are semialgebraic over the whole field `R` (every
`R`-coefficient atom is, trivially, an `R`-coefficient atom). -/
theorem isSemialgebraicSetOver_self {k : ℕ} {V : Set (Fin k → R)}
    (hV : IsSemialgebraicSet V) : IsSemialgebraicSetOver R V := by
  obtain ⟨Φ, hqf, rfl⟩ := semialgebraic_isQFRealizable V hV
  exact qfRealizable_isSemialgebraicSetOver hqf

omit [IsStrictOrderedRing R] [IsRealClosed R] in
/-- Any subset of `R⁰` (a one-point space) is semialgebraic. -/
theorem isSemialgebraicSet_fin_zero (V : Set (Fin 0 → R)) : IsSemialgebraicSet V := by
  by_cases h : V.Nonempty
  · have hu : V = Set.univ := by
      ext z; simp only [Set.mem_univ, iff_true]
      obtain ⟨w, hw⟩ := h; rwa [Subsingleton.elim z w]
    rw [hu]; exact .algebraic ⟨∅, by ext z; simp [Zer]⟩
  · rw [Set.not_nonempty_iff_eq_empty.mp h, ← Set.compl_univ]
    exact IsSemialgebraicSet.compl (.algebraic ⟨∅, by ext z; simp [Zer]⟩)

variable {D : Type*} [CommRing D] [IsDomain D] [Algebra D R]

/-- **Iterated cylindrical projection.** Existentially freeing every coordinate in a list
`L` keeps the set semialgebraic over `D`. The set is the points `w` admitting some `g ∈ V`
agreeing with `w` outside `L`. -/
theorem IsSemialgebraicSetOver.exists_update_list (hinj : Function.Injective (algebraMap D R))
    {n : ℕ} :
    ∀ (L : List (Fin n)) {V : Set (Fin n → R)}, IsSemialgebraicSetOver D V →
      IsSemialgebraicSetOver D
        {w : Fin n → R | ∃ g : Fin n → R, (∀ i ∉ L, g i = w i) ∧ g ∈ V}
  | [], V, hV => by
    convert hV using 1
    ext w
    simp only [Set.mem_setOf_eq, List.not_mem_nil, not_false_eq_true, forall_const]
    constructor
    · rintro ⟨g, hg, hgV⟩; rwa [show g = w from funext hg] at hgV
    · intro hw; exact ⟨w, fun _ => rfl, hw⟩
  | (x :: L'), V, hV => by
    have ih := IsSemialgebraicSetOver.exists_update_list hinj L' hV
    have hu := IsSemialgebraicSetOver.exists_update hinj x ih
    convert hu using 1
    ext w
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨g, hg, hgV⟩
      refine ⟨g x, g, fun i hi => ?_, hgV⟩
      by_cases hix : i = x
      · subst hix; rw [Function.update_self]
      · rw [Function.update_of_ne hix]
        exact hg i (by rw [List.mem_cons, not_or]; exact ⟨hix, hi⟩)
    · rintro ⟨c, g, hg, hgV⟩
      refine ⟨g, fun i hi => ?_, hgV⟩
      rw [List.mem_cons, not_or] at hi
      rw [hg i hi.2, Function.update_of_ne hi.1]

/-- **Projection onto the last `ℓ` coordinates.** If `W ⊆ R^{k+ℓ}` is semialgebraic, so is
its projection `{y | ∃ x, (x, y) ∈ W}` (the image under dropping the first `k`
coordinates). -/
theorem IsSemialgebraicSet.exists_append_left {k ℓ : ℕ} {W : Set (Fin (k + ℓ) → R)}
    (hW : IsSemialgebraicSet W) :
    IsSemialgebraicSet {y : Fin ℓ → R | ∃ x : Fin k → R, Fin.append x y ∈ W} := by
  rcases Nat.eq_zero_or_pos ℓ with hℓ0 | hℓpos
  · subst hℓ0; exact isSemialgebraicSet_fin_zero _
  · have hinj : Function.Injective (algebraMap R R) := FaithfulSMul.algebraMap_injective R R
    have hWover := isSemialgebraicSetOver_self hW
    set firstK : List (Fin (k + ℓ)) := List.ofFn (Fin.castAdd ℓ) with hfk
    have hnat_notin : ∀ j : Fin ℓ, (Fin.natAdd k j) ∉ firstK := by
      intro j hmem
      rw [hfk, List.mem_ofFn] at hmem
      obtain ⟨a, ha⟩ := hmem
      have hv := congrArg Fin.val ha
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
      omega
    set g_map : Fin (k + ℓ) → Fin ℓ :=
      Fin.addCases (fun _ : Fin k => (⟨0, hℓpos⟩ : Fin ℓ)) (fun j : Fin ℓ => j) with hgm
    have hgm_nat : ∀ j : Fin ℓ, g_map (Fin.natAdd k j) = j := fun j => by
      simp only [hgm, Fin.addCases_right]
    have hcomap := IsSemialgebraicSetOver.comap g_map
      (IsSemialgebraicSetOver.exists_update_list (D := R) hinj firstK hWover)
    apply IsSemialgebraicSet.of_definedOver (D := R)
    convert hcomap using 1
    ext y
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, hxW⟩
      refine ⟨Fin.append x y, fun i hi => ?_, hxW⟩
      induction i using Fin.addCases with
      | left a =>
        exact absurd (by rw [hfk, List.mem_ofFn]; exact ⟨a, rfl⟩) hi
      | right j =>
        rw [Fin.append_right, Function.comp_apply, hgm_nat]
    · rintro ⟨g, hg, hgW⟩
      refine ⟨g ∘ Fin.castAdd ℓ, ?_⟩
      have hgeq : Fin.append (g ∘ Fin.castAdd ℓ) y = g := by
        funext p
        induction p using Fin.addCases with
        | left a => rw [Fin.append_left, Function.comp_apply]
        | right j =>
          rw [Fin.append_right]
          have hgi := hg (Fin.natAdd k j) (hnat_notin j)
          rw [Function.comp_apply, hgm_nat] at hgi
          exact hgi.symm
      rw [hgeq]; exact hgW

/-- **Projection onto the first `k` coordinates.** If `W ⊆ R^{k+ℓ}` is semialgebraic, so is
its projection `{x | ∃ y, (x, y) ∈ W}`. -/
theorem IsSemialgebraicSet.exists_append_right {k ℓ : ℕ} {W : Set (Fin (k + ℓ) → R)}
    (hW : IsSemialgebraicSet W) :
    IsSemialgebraicSet {x : Fin k → R | ∃ y : Fin ℓ → R, Fin.append x y ∈ W} := by
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0; exact isSemialgebraicSet_fin_zero _
  · have hinj : Function.Injective (algebraMap R R) := FaithfulSMul.algebraMap_injective R R
    have hWover := isSemialgebraicSetOver_self hW
    set lastL : List (Fin (k + ℓ)) := List.ofFn (Fin.natAdd k) with hll
    have hcast_notin : ∀ i : Fin k, (Fin.castAdd ℓ i) ∉ lastL := by
      intro i hmem
      rw [hll, List.mem_ofFn] at hmem
      obtain ⟨a, ha⟩ := hmem
      have hv := congrArg Fin.val ha
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
      omega
    set g_map : Fin (k + ℓ) → Fin k :=
      Fin.addCases (fun i : Fin k => i) (fun _ : Fin ℓ => (⟨0, hkpos⟩ : Fin k)) with hgm
    have hgm_cast : ∀ i : Fin k, g_map (Fin.castAdd ℓ i) = i := fun i => by
      simp only [hgm, Fin.addCases_left]
    have hcomap := IsSemialgebraicSetOver.comap g_map
      (IsSemialgebraicSetOver.exists_update_list (D := R) hinj lastL hWover)
    apply IsSemialgebraicSet.of_definedOver (D := R)
    convert hcomap using 1
    ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨y, hyW⟩
      refine ⟨Fin.append x y, fun i hi => ?_, hyW⟩
      induction i using Fin.addCases with
      | left a =>
        rw [Fin.append_left, Function.comp_apply, hgm_cast]
      | right j =>
        exact absurd (by rw [hll, List.mem_ofFn]; exact ⟨j, rfl⟩) hi
    · rintro ⟨g, hg, hgW⟩
      refine ⟨g ∘ Fin.natAdd k, ?_⟩
      have hgeq : Fin.append x (g ∘ Fin.natAdd k) = g := by
        funext p
        induction p using Fin.addCases with
        | left a =>
          rw [Fin.append_left]
          have hgi := hg (Fin.castAdd ℓ a) (hcast_notin a)
          rw [Function.comp_apply, hgm_cast] at hgi
          exact hgi.symm
        | right j => rw [Fin.append_right, Function.comp_apply]
      rw [hgeq]; exact hgW

omit [IsRealClosed R] in
/-- Pullback of an absolute semialgebraic set along a coordinate reindexing. -/
theorem IsSemialgebraicSet.comap {a b : ℕ} (g : Fin a → Fin b) {W : Set (Fin a → R)}
    (hW : IsSemialgebraicSet W) : IsSemialgebraicSet {y : Fin b → R | y ∘ g ∈ W} :=
  IsSemialgebraicSet.of_definedOver
    (IsSemialgebraicSetOver.comap g (isSemialgebraicSetOver_self hW))

omit [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
@[simp] theorem append_comp_castAdd {k ℓ : ℕ} (x : Fin k → R) (y : Fin ℓ → R) :
    Fin.append x y ∘ Fin.castAdd ℓ = x := by funext i; simp [Fin.append_left]

omit [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
@[simp] theorem append_comp_natAdd {k ℓ : ℕ} (x : Fin k → R) (y : Fin ℓ → R) :
    Fin.append x y ∘ Fin.natAdd k = y := by funext j; simp [Fin.append_right]

omit [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- Membership of an explicit point `(x, y)` in the graph. -/
theorem append_mem_funGraph {k ℓ : ℕ} (S : Set (Fin k → R)) (f : (Fin k → R) → (Fin ℓ → R))
    (x : Fin k → R) (y : Fin ℓ → R) :
    Fin.append x y ∈ funGraph S f ↔ x ∈ S ∧ y = f x := by
  rw [mem_funGraph, append_comp_castAdd, append_comp_natAdd]

/-- **BPR Proposition 2.83.** Let `f : S → T` be a semialgebraic function. The image of a
semialgebraic `S' ⊆ S` is semialgebraic, and the inverse image of a semialgebraic
`T' ⊆ T` is semialgebraic. -/
theorem proposition_2_83 {k ℓ : ℕ} {S : Set (Fin k → R)} {f : (Fin k → R) → (Fin ℓ → R)}
    (hf : IsSemialgebraicFunction S f) :
    (∀ {S' : Set (Fin k → R)}, IsSemialgebraicSet S' → S' ⊆ S →
        IsSemialgebraicSet (f '' S')) ∧
    (∀ {T' : Set (Fin ℓ → R)}, IsSemialgebraicSet T' →
        IsSemialgebraicSet (S ∩ f ⁻¹' T')) := by
  constructor
  · intro S' hS' hsub
    have hW : IsSemialgebraicSet
        (funGraph S f ∩ {z : Fin (k + ℓ) → R | z ∘ Fin.castAdd ℓ ∈ S'}) :=
      hf.inter (IsSemialgebraicSet.comap (Fin.castAdd ℓ) hS')
    have heq : f '' S' = {y : Fin ℓ → R | ∃ x : Fin k → R,
        Fin.append x y ∈ funGraph S f ∩ {z | z ∘ Fin.castAdd ℓ ∈ S'}} := by
      ext y
      simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_inter_iff, append_mem_funGraph,
        append_comp_castAdd]
      constructor
      · rintro ⟨x, hxS', rfl⟩
        exact ⟨x, ⟨hsub hxS', rfl⟩, hxS'⟩
      · rintro ⟨x, ⟨_, hfx⟩, hxS'⟩
        exact ⟨x, hxS', hfx.symm⟩
    rw [heq]; exact hW.exists_append_left
  · intro T' hT'
    have hW : IsSemialgebraicSet
        (funGraph S f ∩ {z : Fin (k + ℓ) → R | z ∘ Fin.natAdd k ∈ T'}) :=
      hf.inter (IsSemialgebraicSet.comap (Fin.natAdd k) hT')
    have heq : S ∩ f ⁻¹' T' = {x : Fin k → R | ∃ y : Fin ℓ → R,
        Fin.append x y ∈ funGraph S f ∩ {z | z ∘ Fin.natAdd k ∈ T'}} := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, append_mem_funGraph,
        append_comp_natAdd]
      constructor
      · rintro ⟨hxS, hfx⟩
        exact ⟨f x, ⟨hxS, rfl⟩, hfx⟩
      · rintro ⟨y, ⟨hxS, hfx⟩, hyT'⟩
        exact ⟨hxS, hfx ▸ hyT'⟩
    rw [heq]; exact hW.exists_append_right

end Azurite.BPR
