import Azurite.BasuPollackRoy.Chapter1.Section1_1.RealizationInvariance

/-!
# Prenex Normal Form

Every formula over an infinite variable type is C-equivalent to a prenex
formula. The proof proceeds via a sequence of helper lemmas:

* `not_prenex` -- negation of a prenex formula is C-equivalent to a prenex
  formula (just push the negation inward, swapping `∃` and `∀`).
* `exists_swap_equiv` and `forall_swap_equiv` -- renaming the bound variable
  of a quantifier via a swap preserves realization, provided the new name is
  fresh in the body.
* `and_prenex` -- conjunction of two prenex formulas is C-equivalent to a
  prenex formula. Proved by induction on the total quantifier depth, pulling
  quantifiers from each side outward via swap-rename to dodge variable
  collisions.

The final theorem `prenex_normal_form` reduces an arbitrary formula to a
prenex equivalent by structural induction, dispatching the propositional
connectives via De Morgan plus the helpers above.
-/

namespace Azurite.BPR

open MvPolynomial Polynomial

namespace Formula

variable {σ : Type*} {D : Type*} [CommRing D]
variable {C : Type*} [Field C] [Algebra D C]

/-- Negation of a prenex formula is C-equivalent to a prenex formula. -/
private theorem not_prenex [DecidableEq σ]
    {Ψ : Formula σ (FieldAtom σ D)} (hΨ : IsPrenex Ψ) :
    ∃ Ψ' : Formula σ (FieldAtom σ D), IsPrenex Ψ' ∧
      CEquiv (C := C) (.not Ψ) Ψ' := by
  induction hΨ with
  | qf hqf => exact ⟨.not _, .qf hqf, rfl⟩
  | @exists_ x Φ _ ih =>
    obtain ⟨Φ', hP, hE⟩ := ih
    refine ⟨.forall_ x Φ', .forall_ hP, ?_⟩
    unfold CEquiv at hE ⊢
    have hΦ' : Φ'.realization (C := C) = (Φ.realization (C := C))ᶜ := by
      rw [show (Φ.realization (C := C))ᶜ = (Formula.not Φ).realization (C := C) from rfl]
      exact hE.symm
    simp only [realization]
    ext y; simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_exists]
    exact forall_congr' fun c => by rw [hΦ']; simp
  | @forall_ x Φ _ ih =>
    obtain ⟨Φ', hP, hE⟩ := ih
    refine ⟨.exists_ x Φ', .exists_ hP, ?_⟩
    unfold CEquiv at hE ⊢
    have hΦ' : Φ'.realization (C := C) = (Φ.realization (C := C))ᶜ := by
      rw [show (Φ.realization (C := C))ᶜ = (Formula.not Φ).realization (C := C) from rfl]
      exact hE.symm
    simp only [realization]
    ext y; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_forall]
    exact exists_congr fun c => by rw [hΦ']; simp

/-- Renaming the bound variable of ∃x, Φ via a swap preserves realization. -/
private theorem exists_swap_equiv [DecidableEq σ]
    (Φ : Formula σ (FieldAtom σ D)) (x z : σ) (hz : z ∉ Φ.freeVars) :
    CEquiv (C := C) (.exists_ x Φ) (.exists_ z (Φ.rename (Equiv.swap x z) (FieldAtom.renameVars (Equiv.swap x z)))) := by
  unfold CEquiv; simp only [realization]
  ext y; simp only [Set.mem_setOf_eq]
  by_cases hxz : x = z
  · subst hxz
    simp only [Equiv.swap_self]
    exact exists_congr fun c => by
      simp only [Equiv.coe_refl]
      rw [rename_realization id Function.injective_id]; simp
  · have hzx : z ≠ x := Ne.symm hxz
    have key : ∀ c, Function.update y z c ∘ ⇑(Equiv.swap x z) =
        Function.update (Function.update y z (y x)) x c := by
      intro c; ext i; simp only [Function.comp, Function.update_apply]
      split_ifs with h1 h2 h2 <;> simp_all [Equiv.swap_apply_left,
        Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      rw [rename_realization (Equiv.swap x z) (Equiv.injective _)]
      simp only [Set.mem_preimage]; rw [key]
      rw [Function.update_comm hzx]
      exact (realization_invariant_update Φ z hz (Function.update y x c) (y x)).mp hc
    · rintro ⟨c, hc⟩
      rw [rename_realization (Equiv.swap x z) (Equiv.injective _)] at hc
      simp only [Set.mem_preimage] at hc; rw [key] at hc
      refine ⟨c, ?_⟩
      rw [Function.update_comm hzx] at hc
      exact (realization_invariant_update Φ z hz (Function.update y x c) (y x)).mpr hc

/-- Renaming the bound variable of ∀x, Φ via a swap preserves realization. -/
private theorem forall_swap_equiv [DecidableEq σ]
    (Φ : Formula σ (FieldAtom σ D)) (x z : σ) (hz : z ∉ Φ.freeVars) :
    CEquiv (C := C) (.forall_ x Φ) (.forall_ z (Φ.rename (Equiv.swap x z) (FieldAtom.renameVars (Equiv.swap x z)))) := by
  unfold CEquiv; simp only [realization]
  ext y; simp only [Set.mem_setOf_eq]
  by_cases hxz : x = z
  · subst hxz
    simp only [Equiv.swap_self]
    exact forall_congr' fun c => by
      simp only [Equiv.coe_refl]
      rw [rename_realization id Function.injective_id]; simp
  · have hzx : z ≠ x := Ne.symm hxz
    have key : ∀ c, Function.update y z c ∘ ⇑(Equiv.swap x z) =
        Function.update (Function.update y z (y x)) x c := by
      intro c; ext i; simp only [Function.comp, Function.update_apply]
      split_ifs with h1 h2 h2 <;> simp_all [Equiv.swap_apply_left,
        Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne]
    constructor
    · intro hc c
      rw [rename_realization (Equiv.swap x z) (Equiv.injective _)]
      simp only [Set.mem_preimage]; rw [key]
      rw [Function.update_comm hzx]
      exact (realization_invariant_update Φ z hz (Function.update y x c) (y x)).mp (hc c)
    · intro hc c
      have hc' := hc c
      rw [rename_realization (Equiv.swap x z) (Equiv.injective _)] at hc'
      simp only [Set.mem_preimage] at hc'; rw [key] at hc'
      rw [Function.update_comm hzx] at hc'
      exact (realization_invariant_update Φ z hz (Function.update y x c) (y x)).mpr hc'

/-- Conjunction of two prenex formulas is C-equivalent to a prenex formula. -/
private theorem and_prenex [Infinite σ] [DecidableEq σ]
    {Ψ₁ Ψ₂ : Formula σ (FieldAtom σ D)} (h₁ : IsPrenex Ψ₁) (h₂ : IsPrenex Ψ₂) :
    ∃ Ψ : Formula σ (FieldAtom σ D), IsPrenex Ψ ∧
      CEquiv (C := C) (.and Ψ₁ Ψ₂) Ψ := by
  have key : ∀ n, (∀ m, m < n → ∀ {Ψ₁ Ψ₂ : Formula σ (FieldAtom σ D)},
      IsPrenex Ψ₁ → IsPrenex Ψ₂ →
      Ψ₁.quantifierDepth + Ψ₂.quantifierDepth = m →
      ∃ Ψ : Formula σ (FieldAtom σ D), IsPrenex Ψ ∧ CEquiv (C := C) (.and Ψ₁ Ψ₂) Ψ) →
    ∀ {Ψ₁ Ψ₂ : Formula σ (FieldAtom σ D)},
      IsPrenex Ψ₁ → IsPrenex Ψ₂ →
      Ψ₁.quantifierDepth + Ψ₂.quantifierDepth = n →
      ∃ Ψ : Formula σ (FieldAtom σ D), IsPrenex Ψ ∧ CEquiv (C := C) (.and Ψ₁ Ψ₂) Ψ := by
    intro n ih Ψ₁ Ψ₂ h₁ h₂ hn
    cases h₁ with
    | qf hqf₁ =>
      cases h₂ with
      | qf hqf₂ => exact ⟨.and _ _, .qf ⟨hqf₁, hqf₂⟩, rfl⟩
      | exists_ hPB =>
        rename_i z B
        obtain ⟨w, hw⟩ := Infinite.exists_notMem_finset (B.freeVars ∪ Ψ₁.freeVars)
        have hwB : w ∉ B.freeVars := fun h => hw (Finset.mem_union_left _ h)
        have hwΨ₁ : w ∉ Ψ₁.freeVars := fun h => hw (Finset.mem_union_right _ h)
        have hswap := exists_swap_equiv (C := C) B z w hwB
        let B' := B.rename (Equiv.swap z w) (FieldAtom.renameVars (Equiv.swap z w))
        have hB'_prenex : IsPrenex B' := rename_isPrenex _ _ hPB
        have hdepth : Ψ₁.quantifierDepth + B'.quantifierDepth < n := by
          show Ψ₁.quantifierDepth + (B.rename (Equiv.swap z w) (FieldAtom.renameVars (Equiv.swap z w))).quantifierDepth < n
          rw [rename_quantifierDepth _ (FieldAtom.renameVars _)]; simp [quantifierDepth] at hn; omega
        obtain ⟨Ψ_inner, hΨP, hΨE⟩ := ih _ hdepth (.qf hqf₁) hB'_prenex rfl
        refine ⟨.exists_ w Ψ_inner, .exists_ hΨP, ?_⟩
        unfold CEquiv at hswap hΨE ⊢
        simp only [realization] at hswap hΨE ⊢
        rw [hswap]
        ext y; simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
        constructor
        · rintro ⟨hΨ₁, ⟨c, hc⟩⟩
          exact ⟨c, hΨE ▸ ⟨(realization_invariant_update Ψ₁ w hwΨ₁ y c).mp hΨ₁, hc⟩⟩
        · rintro ⟨c, hc⟩
          rw [← hΨE] at hc; simp only [Set.mem_inter_iff] at hc
          exact ⟨(realization_invariant_update Ψ₁ w hwΨ₁ y c).mpr hc.1, c, hc.2⟩
      | forall_ hPB =>
        rename_i z B
        obtain ⟨w, hw⟩ := Infinite.exists_notMem_finset (B.freeVars ∪ Ψ₁.freeVars)
        have hwB : w ∉ B.freeVars := fun h => hw (Finset.mem_union_left _ h)
        have hwΨ₁ : w ∉ Ψ₁.freeVars := fun h => hw (Finset.mem_union_right _ h)
        let B' := B.rename (Equiv.swap z w) (FieldAtom.renameVars (Equiv.swap z w))
        have hB'_prenex : IsPrenex B' := rename_isPrenex _ _ hPB
        have hdepth : Ψ₁.quantifierDepth + B'.quantifierDepth < n := by
          show Ψ₁.quantifierDepth + (B.rename (Equiv.swap z w) (FieldAtom.renameVars (Equiv.swap z w))).quantifierDepth < n
          rw [rename_quantifierDepth _ (FieldAtom.renameVars _)]; simp [quantifierDepth] at hn; omega
        obtain ⟨Ψ_inner, hΨP, hΨE⟩ := ih _ hdepth (.qf hqf₁) hB'_prenex rfl
        refine ⟨.forall_ w Ψ_inner, .forall_ hΨP, ?_⟩
        have hswap := forall_swap_equiv (C := C) B z w hwB
        unfold CEquiv at hswap hΨE ⊢
        simp only [realization] at hswap hΨE ⊢
        rw [hswap]
        ext y; simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
        constructor
        · rintro ⟨hΨ₁, hB⟩ c
          rw [← hΨE]; simp only [Set.mem_inter_iff]
          exact ⟨(realization_invariant_update Ψ₁ w hwΨ₁ y c).mp hΨ₁, hB c⟩
        · intro h
          refine ⟨?_, fun c => ?_⟩
          · have := h (y w)
            rw [← hΨE] at this; simp only [Set.mem_inter_iff] at this
            exact (realization_invariant_update Ψ₁ w hwΨ₁ y (y w)).mpr this.1
          · have := h c
            rw [← hΨE] at this; simp only [Set.mem_inter_iff] at this
            exact this.2
    | exists_ hPA =>
      rename_i x A
      obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset (A.freeVars ∪ Ψ₂.freeVars)
      have hzA : z ∉ A.freeVars := fun h => hz (Finset.mem_union_left _ h)
      have hzΨ : z ∉ Ψ₂.freeVars := fun h => hz (Finset.mem_union_right _ h)
      have hswap := exists_swap_equiv (C := C) A x z hzA
      let A' := A.rename (Equiv.swap x z) (FieldAtom.renameVars (Equiv.swap x z))
      have hA'_prenex : IsPrenex A' := rename_isPrenex _ _ hPA
      have hdepth : A'.quantifierDepth + Ψ₂.quantifierDepth < n := by
        show (A.rename (Equiv.swap x z) (FieldAtom.renameVars (Equiv.swap x z))).quantifierDepth + Ψ₂.quantifierDepth < n
        rw [rename_quantifierDepth _ (FieldAtom.renameVars _)]; simp [quantifierDepth] at hn; omega
      obtain ⟨Ψ_inner, hΨP, hΨE⟩ := ih _ hdepth hA'_prenex h₂ rfl
      refine ⟨.exists_ z Ψ_inner, .exists_ hΨP, ?_⟩
      unfold CEquiv at hswap hΨE ⊢
      simp only [realization] at hswap hΨE ⊢
      rw [hswap]
      ext y; simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
      constructor
      · rintro ⟨⟨c, hc⟩, hΨ₂⟩
        exact ⟨c, hΨE ▸ ⟨hc, (realization_invariant_update Ψ₂ z hzΨ y c).mp hΨ₂⟩⟩
      · rintro ⟨c, hc⟩
        rw [← hΨE] at hc; simp only [Set.mem_inter_iff] at hc
        exact ⟨⟨c, hc.1⟩, (realization_invariant_update Ψ₂ z hzΨ y c).mpr hc.2⟩
    | forall_ hPA =>
      rename_i x A
      obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset (A.freeVars ∪ Ψ₂.freeVars)
      have hzA : z ∉ A.freeVars := fun h => hz (Finset.mem_union_left _ h)
      have hzΨ : z ∉ Ψ₂.freeVars := fun h => hz (Finset.mem_union_right _ h)
      have hswap := forall_swap_equiv (C := C) A x z hzA
      let A' := A.rename (Equiv.swap x z) (FieldAtom.renameVars (Equiv.swap x z))
      have hA'_prenex : IsPrenex A' := rename_isPrenex _ _ hPA
      have hdepth : A'.quantifierDepth + Ψ₂.quantifierDepth < n := by
        show (A.rename (Equiv.swap x z) (FieldAtom.renameVars (Equiv.swap x z))).quantifierDepth + Ψ₂.quantifierDepth < n
        rw [rename_quantifierDepth _ (FieldAtom.renameVars _)]; simp [quantifierDepth] at hn; omega
      obtain ⟨Ψ_inner, hΨP, hΨE⟩ := ih _ hdepth hA'_prenex h₂ rfl
      refine ⟨.forall_ z Ψ_inner, .forall_ hΨP, ?_⟩
      unfold CEquiv at hswap hΨE ⊢
      simp only [realization] at hswap hΨE ⊢
      rw [hswap]
      ext y; simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
      constructor
      · rintro ⟨hA, hΨ₂⟩ c
        rw [← hΨE]; simp only [Set.mem_inter_iff]
        exact ⟨hA c, (realization_invariant_update Ψ₂ z hzΨ y c).mp hΨ₂⟩
      · intro h
        refine ⟨fun c => ?_, ?_⟩
        · have := h c
          rw [← hΨE] at this; simp only [Set.mem_inter_iff] at this
          exact this.1
        · have := h (y z); rw [← hΨE] at this; simp only [Set.mem_inter_iff] at this
          exact (realization_invariant_update Ψ₂ z hzΨ y (y z)).mpr this.2
  exact (@Nat.strongRecOn (fun n => ∀ {Ψ₁ Ψ₂ : Formula σ (FieldAtom σ D)},
      IsPrenex Ψ₁ → IsPrenex Ψ₂ →
      Ψ₁.quantifierDepth + Ψ₂.quantifierDepth = n →
      ∃ Ψ : Formula σ (FieldAtom σ D), IsPrenex Ψ ∧ CEquiv (C := C) (.and Ψ₁ Ψ₂) Ψ)
    (Ψ₁.quantifierDepth + Ψ₂.quantifierDepth) key) h₁ h₂ rfl


/-- Every formula over an infinite variable type is
    C-equivalent to a prenex formula. -/
theorem prenex_normal_form [Infinite σ] [DecidableEq σ]
    (Φ : Formula σ (FieldAtom σ D)) :
    ∃ Ψ : Formula σ (FieldAtom σ D), IsPrenex Ψ ∧
      CEquiv (C := C) Φ Ψ := by
  induction Φ with
  | atom a => exact ⟨.atom a, .qf True.intro, rfl⟩
  | not Φ ih =>
    obtain ⟨Ψ, hP, hE⟩ := ih
    obtain ⟨Ψ', hP', hE'⟩ := not_prenex (C := C) hP
    exact ⟨Ψ', hP', by
      unfold CEquiv at hE hE' ⊢
      simp only [realization] at hE' ⊢; rw [hE]; exact hE'⟩
  | and Φ₁ Φ₂ ih₁ ih₂ =>
    obtain ⟨Ψ₁, hP₁, hE₁⟩ := ih₁
    obtain ⟨Ψ₂, hP₂, hE₂⟩ := ih₂
    obtain ⟨Ψ, hP, hE⟩ := and_prenex (C := C) hP₁ hP₂
    exact ⟨Ψ, hP, by
      unfold CEquiv at hE₁ hE₂ hE ⊢
      simp only [realization] at hE ⊢; rw [hE₁, hE₂]; exact hE⟩
  | or Φ₁ Φ₂ ih₁ ih₂ =>
    -- A ∨ B = ¬(¬A ∧ ¬B)
    obtain ⟨Ψ₁, hP₁, hE₁⟩ := ih₁
    obtain ⟨Ψ₂, hP₂, hE₂⟩ := ih₂
    obtain ⟨Ψ₁', hP₁', hE₁'⟩ := not_prenex (C := C) hP₁
    obtain ⟨Ψ₂', hP₂', hE₂'⟩ := not_prenex (C := C) hP₂
    obtain ⟨Ψ_and, hP_and, hE_and⟩ := and_prenex (C := C) hP₁' hP₂'
    obtain ⟨Ψ_final, hP_final, hE_final⟩ := not_prenex (C := C) hP_and
    refine ⟨Ψ_final, hP_final, ?_⟩
    unfold CEquiv at hE₁ hE₂ hE₁' hE₂' hE_and hE_final ⊢
    simp only [realization] at hE₁' hE₂' hE_and hE_final ⊢
    rw [hE₁, hE₂]
    -- Goal: Ψ₁.realization ∪ Ψ₂.realization = Ψ_final.realization
    -- Use De Morgan: A ∪ B = (Aᶜ ∩ Bᶜ)ᶜ
    rw [show Ψ₁.realization (C := C) ∪ Ψ₂.realization (C := C) =
        ((Ψ₁.realization (C := C))ᶜ ∩ (Ψ₂.realization (C := C))ᶜ)ᶜ from by
          simp [Set.compl_inter, compl_compl]]
    rw [hE₁', hE₂', hE_and, hE_final]
  | exists_ x Φ ih =>
    obtain ⟨Ψ, hP, hE⟩ := ih
    refine ⟨.exists_ x Ψ, .exists_ hP, ?_⟩
    unfold CEquiv at hE ⊢; simp only [realization]
    ext y; simp only [Set.mem_setOf_eq]
    exact exists_congr fun c => by rw [← hE]
  | forall_ x Φ ih =>
    obtain ⟨Ψ, hP, hE⟩ := ih
    refine ⟨.forall_ x Ψ, .forall_ hP, ?_⟩
    unfold CEquiv at hE ⊢; simp only [realization]
    ext y; simp only [Set.mem_setOf_eq]
    exact forall_congr' fun c => by rw [← hE]
  | implies Φ₁ Φ₂ ih₁ ih₂ =>
    -- Φ₁ → Φ₂ has realization Φ₁ᶜ ∪ Φ₂ = ¬(Φ₁ ∧ ¬Φ₂)
    obtain ⟨Ψ₁, hP₁, hE₁⟩ := ih₁
    obtain ⟨Ψ₂, hP₂, hE₂⟩ := ih₂
    obtain ⟨Ψ₂', hP₂', hE₂'⟩ := not_prenex (C := C) hP₂
    obtain ⟨Ψ_and, hP_and, hE_and⟩ := and_prenex (C := C) hP₁ hP₂'
    obtain ⟨Ψ_final, hP_final, hE_final⟩ := not_prenex (C := C) hP_and
    refine ⟨Ψ_final, hP_final, ?_⟩
    unfold CEquiv at hE₁ hE₂ hE₂' hE_and hE_final ⊢
    simp only [realization] at hE₂' hE_and hE_final ⊢
    rw [hE₁, hE₂]
    -- Goal: Ψ₁.realization ᶜ ∪ Ψ₂.realization = Ψ_final.realization
    -- ¬Ψ₂ ≡ Ψ₂' via hE₂', Ψ₁ ∧ Ψ₂' ≡ Ψ_and via hE_and, ¬Ψ_and ≡ Ψ_final via hE_final
    -- Aᶜ ∪ B = (A ∩ Bᶜ)ᶜ
    rw [show (Ψ₁.realization (C := C))ᶜ ∪ Ψ₂.realization (C := C) =
        (Ψ₁.realization (C := C) ∩ (Ψ₂.realization (C := C))ᶜ)ᶜ from by
      simp [Set.compl_inter, compl_compl]]
    rw [hE₂', hE_and, hE_final]

end Formula

end Azurite.BPR
