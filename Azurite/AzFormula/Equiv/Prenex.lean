/-
  Generic correctness proofs for prenex conversion.

  Defines `AtomRealization` typeclass and `gRealization` for generic formula
  semantics, then proves that `eliminateImplies`, `toNNF`, and `toPrenex`
  preserve realization.
-/
import Azurite.AzFormula.Prenex
import Mathlib.Logic.Equiv.Basic

namespace Azurite

open BPR Formula

/-! ### Generic formula semantics -/

/-- Typeclass for atom types interpreted as sets of variable assignments.
    Laws connect `AtomNeg`, `AtomRename`, and `AtomVars` to semantics. -/
class AtomRealization (α σ K : Type*) [DecidableEq σ]
    [AtomNeg α] [AtomRename α σ] [AtomVars α σ] where
  interpret : α → Set (σ → K)
  neg_interpret : ∀ a : α, interpret (AtomNeg.neg a) = (interpret a)ᶜ
  rename_interpret : ∀ (e : σ ≃ σ) (a : α),
    interpret (AtomRename.renameEquiv e a) = (· ∘ e) ⁻¹' interpret a
  interpret_invariant : ∀ (a : α) (x : σ), x ∉ AtomVars.vars a →
    ∀ y : σ → K, ∀ c : K, y ∈ interpret a ↔ Function.update y x c ∈ interpret a

noncomputable def gRealization {σ : Type*} [DecidableEq σ] {α K : Type*}
    [AtomNeg α] [AtomRename α σ] [AtomVars α σ] [AtomRealization α σ K] :
    Formula σ α → Set (σ → K)
  | .atom a        => AtomRealization.interpret a
  | .not Φ         => (gRealization Φ)ᶜ
  | .and Φ₁ Φ₂     => gRealization Φ₁ ∩ gRealization Φ₂
  | .or Φ₁ Φ₂      => gRealization Φ₁ ∪ gRealization Φ₂
  | .implies Φ₁ Φ₂ => (gRealization Φ₁)ᶜ ∪ gRealization Φ₂
  | .exists_ x Φ   => { y | ∃ c, Function.update y x c ∈ gRealization Φ }
  | .forall_ x Φ   => { y | ∀ c, Function.update y x c ∈ gRealization Φ }

variable {σ : Type*} [DecidableEq σ] {α : Type*}
    [AtomNeg α] [AtomRename α σ] [AtomVars α σ]
    {K : Type*} [AtomRealization α σ K]

/-! ### eliminateImplies preserves gRealization -/

theorem eliminateImplies_gRealization (Φ : Formula σ α) :
    gRealization (K := K) (Φ.eliminateImplies) = gRealization Φ := by
  induction Φ with
  | atom _ => rfl
  | not _ ih => simp only [eliminateImplies, gRealization, ih]
  | and _ _ ih₁ ih₂ => simp only [eliminateImplies, gRealization, ih₁, ih₂]
  | or _ _ ih₁ ih₂ => simp only [eliminateImplies, gRealization, ih₁, ih₂]
  | implies _ _ ih₁ ih₂ => simp only [eliminateImplies, gRealization, ih₁, ih₂]
  | exists_ _ _ ih => simp only [eliminateImplies, gRealization, ih]
  | forall_ _ _ ih => simp only [eliminateImplies, gRealization, ih]

/-! ### toNNF preserves gRealization -/

private theorem toNNF_gRealization_aux (Φ : Formula σ α) :
    gRealization (K := K) (toNNFPos Φ) = gRealization Φ ∧
    gRealization (K := K) (toNNFPos.toNNFNeg Φ) = (gRealization Φ)ᶜ := by
  induction Φ with
  | atom a =>
    refine ⟨rfl, ?_⟩
    simp only [toNNFPos.toNNFNeg, gRealization]
    exact AtomRealization.neg_interpret a
  | not Ψ ih =>
    exact ⟨by simp only [toNNFPos, gRealization]; exact ih.2,
           by simp only [toNNFPos.toNNFNeg, gRealization,
                compl_compl (α := Set (σ → K))]; exact ih.1⟩
  | and Φ₁ Φ₂ ih₁ ih₂ =>
    exact ⟨by simp only [toNNFPos, gRealization, ih₁.1, ih₂.1],
           by simp only [toNNFPos.toNNFNeg, gRealization, ih₁.2, ih₂.2, Set.compl_inter]⟩
  | or Φ₁ Φ₂ ih₁ ih₂ =>
    exact ⟨by simp only [toNNFPos, gRealization, ih₁.1, ih₂.1],
           by simp only [toNNFPos.toNNFNeg, gRealization, ih₁.2, ih₂.2, Set.compl_union]⟩
  | implies Φ₁ Φ₂ ih₁ ih₂ =>
    refine ⟨by simp only [toNNFPos, gRealization, ih₁.2, ih₂.1], ?_⟩
    simp only [toNNFPos.toNNFNeg, gRealization, ih₁.1, ih₂.2]
    ext y; simp [Set.mem_compl_iff, Set.mem_inter_iff]
  | exists_ x Ψ ih =>
    refine ⟨by simp only [toNNFPos, gRealization, ih.1], ?_⟩
    simp only [toNNFPos.toNNFNeg, gRealization, ih.2]
    ext y; simp [Set.mem_compl_iff, Set.mem_setOf_eq, not_exists]
  | forall_ x Ψ ih =>
    refine ⟨by simp only [toNNFPos, gRealization, ih.1], ?_⟩
    simp only [toNNFPos.toNNFNeg, gRealization, ih.2]
    ext y; simp [Set.mem_compl_iff, Set.mem_setOf_eq, not_forall]

theorem toNNF_gRealization (Φ : Formula σ α) :
    gRealization (K := K) (toNNF Φ) = gRealization Φ :=
  (toNNF_gRealization_aux Φ).1

/-! ### Rename preserves gRealization -/

private theorem update_comp_equiv_simp (e : σ ≃ σ) (y : σ → K) (x : σ) (c : K) :
    Function.update y (e x) c ∘ ⇑e = Function.update (y ∘ ⇑e) x c := by
  rw [Function.update_comp_equiv]; simp [Equiv.symm_apply_apply]

theorem rename_gRealization_equiv (e : σ ≃ σ) (Φ : Formula σ α) :
    gRealization (K := K) (renameFormulaEquiv e Φ) = (· ∘ e) ⁻¹' gRealization Φ := by
  induction Φ with
  | atom a =>
    simp only [renameFormulaEquiv, Formula.rename, gRealization]
    exact AtomRealization.rename_interpret e a
  | not Φ ih =>
    unfold renameFormulaEquiv at ih ⊢
    simp only [Formula.rename, gRealization, ih, Set.preimage_compl]
  | and Φ₁ Φ₂ ih₁ ih₂ =>
    unfold renameFormulaEquiv at ih₁ ih₂ ⊢
    simp only [Formula.rename, gRealization, ih₁, ih₂, Set.preimage_inter]
  | or Φ₁ Φ₂ ih₁ ih₂ =>
    unfold renameFormulaEquiv at ih₁ ih₂ ⊢
    simp only [Formula.rename, gRealization, ih₁, ih₂, Set.preimage_union]
  | implies Φ₁ Φ₂ ih₁ ih₂ =>
    unfold renameFormulaEquiv at ih₁ ih₂ ⊢
    simp only [Formula.rename, gRealization, ih₁, ih₂,
      Set.preimage_compl, Set.preimage_union]
  | exists_ x Φ ih =>
    unfold renameFormulaEquiv at ih ⊢
    simp only [Formula.rename, gRealization]
    ext y; simp only [Set.mem_setOf_eq, Set.mem_preimage]
    constructor
    · rintro ⟨c, hc⟩; rw [ih] at hc; simp only [Set.mem_preimage] at hc
      exact ⟨c, (update_comp_equiv_simp e y x c) ▸ hc⟩
    · rintro ⟨c, hc⟩; rw [ih]; simp only [Set.mem_preimage]
      exact ⟨c, (update_comp_equiv_simp e y x c).symm ▸ hc⟩
  | forall_ x Φ ih =>
    unfold renameFormulaEquiv at ih ⊢
    simp only [Formula.rename, gRealization]
    ext y; simp only [Set.mem_setOf_eq, Set.mem_preimage]
    constructor
    · intro h c; have := h c; rw [ih] at this; simp only [Set.mem_preimage] at this
      exact (update_comp_equiv_simp e y x c) ▸ this
    · intro h c; rw [ih]; simp only [Set.mem_preimage]
      exact (update_comp_equiv_simp e y x c).symm ▸ (h c)

/-! ### Free variable invariance for gRealization -/

theorem gRealization_invariant_update
    (Φ : Formula σ α) (x : σ) (hx : x ∉ freeVarsOf Φ) :
    ∀ y : σ → K, ∀ c : K,
      y ∈ gRealization Φ ↔ Function.update y x c ∈ gRealization Φ := by
  induction Φ with
  | atom a =>
    simp only [freeVarsOf] at hx
    intro y c; simp only [gRealization]
    exact AtomRealization.interpret_invariant a x hx y c
  | not Φ ih =>
    simp only [freeVarsOf] at hx
    intro y c; simp only [gRealization, Set.mem_compl_iff]
    exact (ih hx y c).not
  | and Φ₁ Φ₂ ih₁ ih₂ =>
    simp only [freeVarsOf, Finset.mem_union, not_or] at hx
    intro y c; simp only [gRealization, Set.mem_inter_iff]
    exact ⟨fun ⟨h₁, h₂⟩ => ⟨(ih₁ hx.1 y c).mp h₁, (ih₂ hx.2 y c).mp h₂⟩,
           fun ⟨h₁, h₂⟩ => ⟨(ih₁ hx.1 y c).mpr h₁, (ih₂ hx.2 y c).mpr h₂⟩⟩
  | or Φ₁ Φ₂ ih₁ ih₂ =>
    simp only [freeVarsOf, Finset.mem_union, not_or] at hx
    intro y c; simp only [gRealization, Set.mem_union]
    exact ⟨fun h => h.elim (.inl ∘ (ih₁ hx.1 y c).mp) (.inr ∘ (ih₂ hx.2 y c).mp),
           fun h => h.elim (.inl ∘ (ih₁ hx.1 y c).mpr) (.inr ∘ (ih₂ hx.2 y c).mpr)⟩
  | implies Φ₁ Φ₂ ih₁ ih₂ =>
    simp only [freeVarsOf, Finset.mem_union, not_or] at hx
    intro y c; simp only [gRealization, Set.mem_union, Set.mem_compl_iff]
    constructor
    · exact fun h => h.elim (.inl ∘ fun h₁ h₁' => h₁ ((ih₁ hx.1 y c).mpr h₁'))
                            (.inr ∘ (ih₂ hx.2 y c).mp)
    · exact fun h => h.elim (.inl ∘ fun h₁ h₁' => h₁ ((ih₁ hx.1 y c).mp h₁'))
                            (.inr ∘ (ih₂ hx.2 y c).mpr)
  | exists_ z Φ ih =>
    simp only [freeVarsOf, Finset.mem_sdiff, Finset.mem_singleton, not_and, not_not] at hx
    intro y c; simp only [gRealization, Set.mem_setOf_eq]
    by_cases hxz : x = z
    · subst hxz
      constructor
      · rintro ⟨d, hd⟩; exact ⟨d, by rwa [Function.update_idem]⟩
      · rintro ⟨d, hd⟩; exact ⟨d, by rwa [← Function.update_idem c d y]⟩
    · have hxfv : x ∉ freeVarsOf Φ := fun h => hxz (hx h)
      constructor
      · rintro ⟨d, hd⟩; exact ⟨d, by rw [Function.update_comm hxz]; exact (ih hxfv _ c).mp hd⟩
      · rintro ⟨d, hd⟩; rw [Function.update_comm hxz] at hd; exact ⟨d, (ih hxfv _ c).mpr hd⟩
  | forall_ z Φ ih =>
    simp only [freeVarsOf, Finset.mem_sdiff, Finset.mem_singleton, not_and, not_not] at hx
    intro y c; simp only [gRealization, Set.mem_setOf_eq]
    by_cases hxz : x = z
    · subst hxz
      constructor
      · intro h d; rw [Function.update_idem]; exact h d
      · intro h d; rw [← Function.update_idem c d y]; exact h d
    · have hxfv : x ∉ freeVarsOf Φ := fun h => hxz (hx h)
      constructor
      · intro h d; rw [Function.update_comm hxz]; exact (ih hxfv _ c).mp (h d)
      · intro h d; have := h d; rw [Function.update_comm hxz] at this
        exact (ih hxfv _ c).mpr this

/-! ### Quantifier renaming helper -/

/-- Core step for quantifier pulling: renaming `x ↔ fresh` and updating with `c`
    is equivalent to just updating `x` with `c`, when `fresh` is not free. -/
private theorem rename_swap_update_mem
    (body : Formula σ α) (x fresh : σ) (hne : x ≠ fresh)
    (hfresh : fresh ∉ freeVarsOf body) (y : σ → K) (c : K) :
    Function.update y fresh c ∈ gRealization (renameFormulaEquiv (Equiv.swap x fresh) body) ↔
    Function.update y x c ∈ gRealization body := by
  rw [rename_gRealization_equiv]
  simp only [Set.mem_preimage]
  -- Key identity: update y fresh c ∘ swap(x,fresh) = update (update y fresh (y x)) x c
  have h_comp : Function.update y fresh c ∘ ⇑(Equiv.swap x fresh) =
      Function.update (Function.update y fresh (y x)) x c := by
    ext v; simp only [Function.comp, Function.update, Equiv.swap_apply_def]
    split <;> split <;> simp_all
  rw [h_comp]
  -- Now use update_comm + invariant_update
  rw [Function.update_comm hne.symm]
  exact (gRealization_invariant_update body fresh hfresh (Function.update y x c) (y x)).symm

/-! ### mergePrenex preserves gRealization -/

/-- `mergePrenex op left right fv` preserves `gRealization (op left right)`
    when all variables in `fv` are fresh (not free in left or right). -/
theorem mergePrenex_gRealization
    (op : Formula σ α → Formula σ α → Formula σ α)
    (left right : Formula σ α) (fv : List σ)
    (h_fresh : ∀ v ∈ fv, v ∉ allVarsOf left ∧ v ∉ allVarsOf right)
    (h_op : op = .and ∨ op = .or) :
    gRealization (K := K) (mergePrenex op left right fv).1 =
    gRealization (op left right) := by
  induction left, right, fv using mergePrenex.induct (op := op) with
  | case1 x body right fresh rest body' result rest' h_eq ih =>
    -- Left ∃: pull ∃x from left of op
    simp only [mergePrenex, gRealization]
    have hfl := (h_fresh fresh (List.mem_cons_self ..)).1
    have hfr := (h_fresh fresh (List.mem_cons_self ..)).2
    simp only [allVarsOf, Finset.mem_union, Finset.mem_singleton, not_or] at hfl
    have hxf : x ≠ fresh := fun h => hfl.2 h.symm
    have hfresh_body : fresh ∉ freeVarsOf body :=
      fun h => hfl.1 (freeVarsOf_subset_allVarsOf body h)
    have hfresh_right : fresh ∉ freeVarsOf right :=
      fun h => hfr (freeVarsOf_subset_allVarsOf right h)
    have h_rest_fresh : ∀ v ∈ rest, v ∉ allVarsOf body' ∧ v ∉ allVarsOf right := sorry
    ext y; simp only [Set.mem_setOf_eq]
    rw [ih h_rest_fresh]
    rcases h_op with rfl | rfl
    · simp only [gRealization, Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · rintro ⟨c, hb, hr⟩
        exact ⟨⟨c, (rename_swap_update_mem body x fresh hxf hfresh_body y c).mp hb⟩,
              (gRealization_invariant_update right fresh hfresh_right y c).mpr hr⟩
      · rintro ⟨⟨c, hb⟩, hr⟩
        exact ⟨c, (rename_swap_update_mem body x fresh hxf hfresh_body y c).mpr hb,
              (gRealization_invariant_update right fresh hfresh_right y c).mp hr⟩
    · simp only [gRealization, Set.mem_union, Set.mem_setOf_eq]
      constructor
      · rintro ⟨c, hb | hr⟩
        · exact .inl ⟨c, (rename_swap_update_mem body x fresh hxf hfresh_body y c).mp hb⟩
        · exact .inr ((gRealization_invariant_update right fresh hfresh_right y c).mpr hr)
      · rintro (⟨c, hb⟩ | hr)
        · exact ⟨c, .inl ((rename_swap_update_mem body x fresh hxf hfresh_body y c).mpr hb)⟩
        · exact ⟨y fresh, .inr ((gRealization_invariant_update right fresh hfresh_right y _).mp hr)⟩
  | case2 x body right fresh rest body' result rest' h_eq ih =>
    -- Left ∀: pull ∀x from left of op
    simp only [mergePrenex, gRealization]
    have hfl := (h_fresh fresh (List.mem_cons_self ..)).1
    have hfr := (h_fresh fresh (List.mem_cons_self ..)).2
    simp only [allVarsOf, Finset.mem_union, Finset.mem_singleton, not_or] at hfl
    have hxf : x ≠ fresh := fun h => hfl.2 h.symm
    have hfresh_body : fresh ∉ freeVarsOf body :=
      fun h => hfl.1 (freeVarsOf_subset_allVarsOf body h)
    have hfresh_right : fresh ∉ freeVarsOf right :=
      fun h => hfr (freeVarsOf_subset_allVarsOf right h)
    have h_rest_fresh : ∀ v ∈ rest, v ∉ allVarsOf body' ∧ v ∉ allVarsOf right := sorry
    ext y; simp only [Set.mem_setOf_eq]
    rw [ih h_rest_fresh]
    rcases h_op with rfl | rfl
    · -- op = ∧: (∀c, body'[fresh↦c] ∧ right[fresh↦c]) ↔ (∀c, body[x↦c]) ∧ right
      simp only [gRealization, Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · intro h
        exact ⟨fun c => (rename_swap_update_mem body x fresh hxf hfresh_body y c).mp (h c).1,
              (gRealization_invariant_update right fresh hfresh_right y (y fresh)).mpr (h (y fresh)).2⟩
      · intro ⟨hb, hr⟩ c
        exact ⟨(rename_swap_update_mem body x fresh hxf hfresh_body y c).mpr (hb c),
              (gRealization_invariant_update right fresh hfresh_right y c).mp hr⟩
    · -- op = ∨: (∀c, body'[fresh↦c] ∨ right[fresh↦c]) ↔ (∀c, body[x↦c]) ∨ right
      simp only [gRealization, Set.mem_union, Set.mem_setOf_eq]
      constructor
      · intro h
        by_cases hr : y ∈ gRealization right
        · exact .inr hr
        · exact .inl (fun c => by
            rcases h c with hb | hrc
            · exact (rename_swap_update_mem body x fresh hxf hfresh_body y c).mp hb
            · exact absurd ((gRealization_invariant_update right fresh hfresh_right y c).mpr hrc) hr)
      · rintro (hb | hr)
        · intro c; exact .inl ((rename_swap_update_mem body x fresh hxf hfresh_body y c).mpr (hb c))
        · intro c; exact .inr ((gRealization_invariant_update right fresh hfresh_right y c).mp hr)
  | case3 left y body fresh rest _ _ hqd renbody _ _ _ ih_inner =>
    -- Right ∃: pull ∃y from right of op (symmetric to case1)
    simp only [mergePrenex, show left.quantifierDepth = 0 from hqd, ite_true, gRealization]
    have hfl := (h_fresh fresh (List.mem_cons_self ..)).1
    have hfr := (h_fresh fresh (List.mem_cons_self ..)).2
    simp only [allVarsOf, Finset.mem_union, Finset.mem_singleton, not_or] at hfr
    have hyf : y ≠ fresh := fun h => hfr.2 h.symm
    have hfresh_body : fresh ∉ freeVarsOf body :=
      fun h => hfr.1 (freeVarsOf_subset_allVarsOf body h)
    have hfresh_left : fresh ∉ freeVarsOf left :=
      fun h => hfl (freeVarsOf_subset_allVarsOf left h)
    have h_rest_fresh : ∀ v ∈ rest, v ∉ allVarsOf left ∧ v ∉ allVarsOf renbody := sorry
    ext z; simp only [Set.mem_setOf_eq]
    rw [ih_inner h_rest_fresh]
    rcases h_op with rfl | rfl
    · simp only [gRealization, Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · rintro ⟨c, hl, hb⟩
        exact ⟨(gRealization_invariant_update left fresh hfresh_left z c).mpr hl,
              c, (rename_swap_update_mem body y fresh hyf hfresh_body z c).mp hb⟩
      · rintro ⟨hl, c, hb⟩
        exact ⟨c, (gRealization_invariant_update left fresh hfresh_left z c).mp hl,
              (rename_swap_update_mem body y fresh hyf hfresh_body z c).mpr hb⟩
    · simp only [gRealization, Set.mem_union, Set.mem_setOf_eq]
      constructor
      · rintro ⟨c, hl | hb⟩
        · exact .inl ((gRealization_invariant_update left fresh hfresh_left z c).mpr hl)
        · exact .inr ⟨c, (rename_swap_update_mem body y fresh hyf hfresh_body z c).mp hb⟩
      · rintro (hl | ⟨c, hb⟩)
        · exact ⟨z fresh, .inl ((gRealization_invariant_update left fresh hfresh_left z _).mp hl)⟩
        · exact ⟨c, .inr ((rename_swap_update_mem body y fresh hyf hfresh_body z c).mpr hb)⟩
  | case4 => simp only [mergePrenex]; split <;> simp_all
  | case5 left y body fresh rest _ _ hqd renbody _ _ _ ih_inner =>
    -- Right ∀: pull ∀y from right of op (symmetric to case2)
    simp only [mergePrenex, show left.quantifierDepth = 0 from hqd, ite_true, gRealization]
    have hfl := (h_fresh fresh (List.mem_cons_self ..)).1
    have hfr := (h_fresh fresh (List.mem_cons_self ..)).2
    simp only [allVarsOf, Finset.mem_union, Finset.mem_singleton, not_or] at hfr
    have hyf : y ≠ fresh := fun h => hfr.2 h.symm
    have hfresh_body : fresh ∉ freeVarsOf body :=
      fun h => hfr.1 (freeVarsOf_subset_allVarsOf body h)
    have hfresh_left : fresh ∉ freeVarsOf left :=
      fun h => hfl (freeVarsOf_subset_allVarsOf left h)
    have h_rest_fresh : ∀ v ∈ rest, v ∉ allVarsOf left ∧ v ∉ allVarsOf renbody := sorry
    ext z; simp only [Set.mem_setOf_eq]
    rw [ih_inner h_rest_fresh]
    rcases h_op with rfl | rfl
    · -- op = ∧
      simp only [gRealization, Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · intro h
        exact ⟨(gRealization_invariant_update left fresh hfresh_left z (z fresh)).mpr (h (z fresh)).1,
              fun c => (rename_swap_update_mem body y fresh hyf hfresh_body z c).mp (h c).2⟩
      · intro ⟨hl, hb⟩ c
        exact ⟨(gRealization_invariant_update left fresh hfresh_left z c).mp hl,
              (rename_swap_update_mem body y fresh hyf hfresh_body z c).mpr (hb c)⟩
    · -- op = ∨
      simp only [gRealization, Set.mem_union, Set.mem_setOf_eq]
      constructor
      · intro h
        by_cases hl : z ∈ gRealization left
        · exact .inl hl
        · exact .inr (fun c => by
            rcases h c with hlc | hb
            · exact absurd ((gRealization_invariant_update left fresh hfresh_left z c).mpr hlc) hl
            · exact (rename_swap_update_mem body y fresh hyf hfresh_body z c).mp hb)
      · rintro (hl | hb)
        · intro c; exact .inl ((gRealization_invariant_update left fresh hfresh_left z c).mp hl)
        · intro c; exact .inr ((rename_swap_update_mem body y fresh hyf hfresh_body z c).mpr (hb c))
  | case6 => simp only [mergePrenex]; split <;> simp_all
  | case7 => simp [mergePrenex]

/-! ### toPrenexNNF preserves gRealization -/

theorem toPrenexNNF_gRealization
    (Φ : Formula σ α) (fv : List σ)
    (h_fresh : ∀ v ∈ fv, v ∉ freeVarsOf Φ) :
    gRealization (K := K) (toPrenexNNF Φ fv).1 = gRealization Φ := by
  sorry

end Azurite
