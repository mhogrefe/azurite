/-
  Generic correctness proofs for prenex conversion.

  Defines `AtomRealization` typeclass and `gRealization` for generic formula
  semantics, then proves that `eliminateImplies`, `toNNF`, and `toPrenex`
  preserve realization.
-/
import Azurite.AzFormula.Prenex
import Azurite.AzMvPolynomial.Equiv.Vars
import Azurite.AzMvPolynomial.Equiv.Rename
import Mathlib.Logic.Equiv.Basic
import Mathlib.Algebra.MvPolynomial.Variables
import Azurite.AzFormula.Realization

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

/-! ### allVarsOf under renaming -/

omit [AtomNeg α] in
/-- Renaming a formula via an equivalence maps `allVarsOf` via `Finset.image`. -/
theorem allVarsOf_renameFormulaEquiv (e : σ ≃ σ)
    (Φ : Formula σ α)
    (h_atom_vars : ∀ a : α,
      AtomVars.vars (AtomRename.renameEquiv e a) = (AtomVars.vars a).image e) :
    allVarsOf (renameFormulaEquiv e Φ) = (allVarsOf Φ).image e := by
  induction Φ with
  | atom a =>
    simp only [renameFormulaEquiv, Formula.rename, allVarsOf, h_atom_vars]
  | not Φ ih =>
    simp only [renameFormulaEquiv, Formula.rename, allVarsOf] at ih ⊢; exact ih
  | and Φ₁ Φ₂ ih₁ ih₂ =>
    simp only [renameFormulaEquiv, Formula.rename, allVarsOf, Finset.image_union] at ih₁ ih₂ ⊢
    rw [ih₁, ih₂]
  | or Φ₁ Φ₂ ih₁ ih₂ =>
    simp only [renameFormulaEquiv, Formula.rename, allVarsOf, Finset.image_union] at ih₁ ih₂ ⊢
    rw [ih₁, ih₂]
  | implies Φ₁ Φ₂ ih₁ ih₂ =>
    simp only [renameFormulaEquiv, Formula.rename, allVarsOf, Finset.image_union] at ih₁ ih₂ ⊢
    rw [ih₁, ih₂]
  | exists_ x Φ ih =>
    simp only [renameFormulaEquiv, Formula.rename, allVarsOf, Finset.image_union,
      Finset.image_singleton] at ih ⊢; rw [ih]
  | forall_ x Φ ih =>
    simp only [renameFormulaEquiv, Formula.rename, allVarsOf, Finset.image_union,
      Finset.image_singleton] at ih ⊢; rw [ih]

/-- `mergePrenex op left right fv` preserves `gRealization (op left right)`
    when all variables in `fv` are fresh (not free in left or right). -/
theorem mergePrenex_gRealization
    (op : Formula σ α → Formula σ α → Formula σ α)
    (left right : Formula σ α) (fv : List σ)
    (h_fresh : ∀ v ∈ fv, v ∉ allVarsOf left ∧ v ∉ allVarsOf right)
    (h_nodup : fv.Nodup)
    (h_op : op = .and ∨ op = .or)
    (h_rename_vars : ∀ (e : σ ≃ σ) (a : α),
      AtomVars.vars (AtomRename.renameEquiv e a) = (AtomVars.vars a).image e) :
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
    have h_nodup_rest := (List.nodup_cons.mp h_nodup).2
    have hfresh_not_rest := (List.nodup_cons.mp h_nodup).1
    have h_rest_fresh : ∀ v ∈ rest, v ∉ allVarsOf body' ∧ v ∉ allVarsOf right := by
      intro v hv
      have hv_fresh := h_fresh v (List.mem_cons_of_mem _ hv)
      have hv_left := hv_fresh.1
      simp only [allVarsOf, Finset.mem_union, Finset.mem_singleton, not_or] at hv_left
      constructor
      · rw [allVarsOf_renameFormulaEquiv (Equiv.swap x fresh) body (h_rename_vars _)]
        intro hm; rw [Finset.mem_image] at hm
        obtain ⟨w, hw_mem, hw_eq⟩ := hm
        simp only [Equiv.swap_apply_def] at hw_eq
        split_ifs at hw_eq with h1 h2
        · exact hfresh_not_rest (hw_eq ▸ hv)
        · exact hfl.1 (h2 ▸ hw_mem)
        · exact hv_left.1 (hw_eq ▸ hw_mem)
      · exact hv_fresh.2
    ext y; simp only [Set.mem_setOf_eq]
    rw [ih h_rest_fresh h_nodup_rest]
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
    have h_nodup_rest := (List.nodup_cons.mp h_nodup).2
    have hfresh_not_rest := (List.nodup_cons.mp h_nodup).1
    have h_rest_fresh : ∀ v ∈ rest, v ∉ allVarsOf body' ∧ v ∉ allVarsOf right := by
      intro v hv
      have hv_fresh := h_fresh v (List.mem_cons_of_mem _ hv)
      have hv_left := hv_fresh.1
      simp only [allVarsOf, Finset.mem_union, Finset.mem_singleton, not_or] at hv_left
      exact ⟨fun hm => by
        rw [allVarsOf_renameFormulaEquiv (Equiv.swap x fresh) body (h_rename_vars _)] at hm
        obtain ⟨w, hw_mem, hw_eq⟩ := Finset.mem_image.mp hm
        simp only [Equiv.swap_apply_def] at hw_eq
        split_ifs at hw_eq with h1 h2
        · exact hfresh_not_rest (hw_eq ▸ hv)
        · exact hfl.1 (h2 ▸ hw_mem)
        · exact hv_left.1 (hw_eq ▸ hw_mem), hv_fresh.2⟩
    ext y; simp only [Set.mem_setOf_eq]
    rw [ih h_rest_fresh h_nodup_rest]
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
    have h_nodup_rest := (List.nodup_cons.mp h_nodup).2
    have hfresh_not_rest := (List.nodup_cons.mp h_nodup).1
    have h_rest_fresh : ∀ v ∈ rest, v ∉ allVarsOf left ∧ v ∉ allVarsOf renbody := by
      intro v hv
      have hv_fresh := h_fresh v (List.mem_cons_of_mem _ hv)
      have hv_right := hv_fresh.2
      simp only [allVarsOf, Finset.mem_union, Finset.mem_singleton, not_or] at hv_right
      exact ⟨hv_fresh.1, fun hm => by
        rw [allVarsOf_renameFormulaEquiv (Equiv.swap y fresh) body (h_rename_vars _)] at hm
        obtain ⟨w, hw_mem, hw_eq⟩ := Finset.mem_image.mp hm
        simp only [Equiv.swap_apply_def] at hw_eq
        split_ifs at hw_eq with h1 h2
        · exact hfresh_not_rest (hw_eq ▸ hv)
        · exact hfr.1 (h2 ▸ hw_mem)
        · exact hv_right.1 (hw_eq ▸ hw_mem)⟩
    ext z; simp only [Set.mem_setOf_eq]
    rw [ih_inner h_rest_fresh h_nodup_rest]
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
    have h_nodup_rest := (List.nodup_cons.mp h_nodup).2
    have hfresh_not_rest := (List.nodup_cons.mp h_nodup).1
    have h_rest_fresh : ∀ v ∈ rest, v ∉ allVarsOf left ∧ v ∉ allVarsOf renbody := by
      intro v hv
      have hv_fresh := h_fresh v (List.mem_cons_of_mem _ hv)
      have hv_right := hv_fresh.2
      simp only [allVarsOf, Finset.mem_union, Finset.mem_singleton, not_or] at hv_right
      exact ⟨hv_fresh.1, fun hm => by
        rw [allVarsOf_renameFormulaEquiv (Equiv.swap y fresh) body (h_rename_vars _)] at hm
        obtain ⟨w, hw_mem, hw_eq⟩ := Finset.mem_image.mp hm
        simp only [Equiv.swap_apply_def] at hw_eq
        split_ifs at hw_eq with h1 h2
        · exact hfresh_not_rest (hw_eq ▸ hv)
        · exact hfr.1 (h2 ▸ hw_mem)
        · exact hv_right.1 (hw_eq ▸ hw_mem)⟩
    ext z; simp only [Set.mem_setOf_eq]
    rw [ih_inner h_rest_fresh h_nodup_rest]
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

/-! ### Structural properties of mergePrenex and toPrenexNNF -/

omit [AtomNeg α] [AtomVars α σ] in
/-- The remaining fresh variables after `mergePrenex` are a suffix of the input. -/
theorem mergePrenex_fv_suffix
    (op : Formula σ α → Formula σ α → Formula σ α)
    (left right : Formula σ α) (fv : List σ) :
    (mergePrenex op left right fv).2 <:+ fv := by
  induction left, right, fv using mergePrenex.induct (op := op) with
  | case1 x body right fresh rest body' result rest' h_eq ih =>
    simp only [mergePrenex]
    exact List.IsSuffix.trans ih (List.suffix_cons _ _)
  | case2 x body right fresh rest body' result rest' h_eq ih =>
    simp only [mergePrenex]
    exact List.IsSuffix.trans ih (List.suffix_cons _ _)
  | case3 left y body fresh rest _ _ hqd renbody result' rest' _ ih_inner =>
    simp only [mergePrenex, show left.quantifierDepth = 0 from hqd, ite_true]
    exact List.IsSuffix.trans ih_inner (List.suffix_cons _ _)
  | case4 => simp only [mergePrenex]; split; contradiction; exact List.suffix_refl _
  | case5 left y body fresh rest _ _ hqd renbody result' rest' _ ih_inner =>
    simp only [mergePrenex, show left.quantifierDepth = 0 from hqd, ite_true]
    exact List.IsSuffix.trans ih_inner (List.suffix_cons _ _)
  | case6 => simp only [mergePrenex]; split; contradiction; exact List.suffix_refl _
  | case7 => simp [mergePrenex]

omit [AtomNeg α] [AtomVars α σ] in
/-- The remaining fresh variables after `toPrenexNNF` are a suffix of the input. -/
theorem toPrenexNNF_fv_suffix (Φ : Formula σ α) (fv : List σ) :
    (toPrenexNNF Φ fv).2 <:+ fv := by
  induction Φ generalizing fv with
  | atom _ => exact List.suffix_refl _
  | not _ _ => exact List.suffix_refl _
  | exists_ _ _ ih => exact ih fv
  | forall_ _ _ ih => exact ih fv
  | and _ _ ih₁ ih₂ =>
    exact List.IsSuffix.trans (mergePrenex_fv_suffix _ _ _ _)
      (List.IsSuffix.trans (ih₂ _) (ih₁ _))
  | or _ _ ih₁ ih₂ =>
    exact List.IsSuffix.trans (mergePrenex_fv_suffix _ _ _ _)
      (List.IsSuffix.trans (ih₂ _) (ih₁ _))
  | implies _ _ _ _ => exact List.suffix_refl _

omit [AtomNeg α] in
/-- Unconsumed fresh variables after `mergePrenex` are fresh for the result. -/
theorem mergePrenex_fv_fresh_result
    (op : Formula σ α → Formula σ α → Formula σ α)
    (left right : Formula σ α) (fv : List σ)
    (h_fresh : ∀ v ∈ fv, v ∉ allVarsOf left ∧ v ∉ allVarsOf right)
    (h_nodup : fv.Nodup)
    (h_op : op = .and ∨ op = .or)
    (h_rename_vars : ∀ (e : σ ≃ σ) (a : α),
      AtomVars.vars (AtomRename.renameEquiv e a) = (AtomVars.vars a).image e) :
    ∀ v ∈ (mergePrenex op left right fv).2,
      v ∉ allVarsOf (mergePrenex op left right fv).1 := by
  induction left, right, fv using mergePrenex.induct (op := op) with
  | case1 x body right fresh rest body' result rest' h_eq ih =>
    simp only [mergePrenex, allVarsOf]
    intro v hv hm
    rw [Finset.mem_union, Finset.mem_singleton] at hm
    have h_nodup_rest := (List.nodup_cons.mp h_nodup).2
    have hfresh_not_rest := (List.nodup_cons.mp h_nodup).1
    rcases hm with hm | rfl
    · -- v ∈ allVarsOf result: use IH
      have h_rest_fresh : ∀ v ∈ rest, v ∉ allVarsOf body' ∧ v ∉ allVarsOf right := by
        intro v hv
        have hv_fresh := h_fresh v (List.mem_cons_of_mem _ hv)
        have hv_left := hv_fresh.1
        simp only [allVarsOf, Finset.mem_union, Finset.mem_singleton, not_or] at hv_left
        have hfl := (h_fresh fresh (List.mem_cons_self ..)).1
        simp only [allVarsOf, Finset.mem_union, Finset.mem_singleton, not_or] at hfl
        exact ⟨fun hm => by
          rw [allVarsOf_renameFormulaEquiv (Equiv.swap x fresh) body (h_rename_vars _)] at hm
          obtain ⟨w, hw_mem, hw_eq⟩ := Finset.mem_image.mp hm
          simp only [Equiv.swap_apply_def] at hw_eq
          split_ifs at hw_eq with h1 h2
          · exact hfresh_not_rest (hw_eq ▸ hv)
          · exact hfl.1 (h2 ▸ hw_mem)
          · exact hv_left.1 (hw_eq ▸ hw_mem), hv_fresh.2⟩
      have h_suf : (mergePrenex op body' right rest).2 <:+ rest :=
        mergePrenex_fv_suffix op body' right rest
      exact ih h_rest_fresh h_nodup_rest v hv hm
    · -- v = fresh: fresh ∉ rest' since rest' <:+ rest and fresh ∉ rest
      have h_suf : (mergePrenex op body' right rest).2 <:+ rest :=
        mergePrenex_fv_suffix op body' right rest
      exact hfresh_not_rest (h_suf.subset hv)
  | case2 x body right fresh rest body' result rest' h_eq ih =>
    simp only [mergePrenex, allVarsOf]
    intro v hv hm
    rw [Finset.mem_union, Finset.mem_singleton] at hm
    have h_nodup_rest := (List.nodup_cons.mp h_nodup).2
    have hfresh_not_rest := (List.nodup_cons.mp h_nodup).1
    rcases hm with hm | rfl
    · have h_rest_fresh : ∀ v ∈ rest, v ∉ allVarsOf body' ∧ v ∉ allVarsOf right := by
        intro v hv
        have hv_fresh := h_fresh v (List.mem_cons_of_mem _ hv)
        have hv_left := hv_fresh.1
        simp only [allVarsOf, Finset.mem_union, Finset.mem_singleton, not_or] at hv_left
        have hfl := (h_fresh fresh (List.mem_cons_self ..)).1
        simp only [allVarsOf, Finset.mem_union, Finset.mem_singleton, not_or] at hfl
        exact ⟨fun hm => by
          rw [allVarsOf_renameFormulaEquiv (Equiv.swap x fresh) body (h_rename_vars _)] at hm
          obtain ⟨w, hw_mem, hw_eq⟩ := Finset.mem_image.mp hm
          simp only [Equiv.swap_apply_def] at hw_eq
          split_ifs at hw_eq with h1 h2
          · exact hfresh_not_rest (hw_eq ▸ hv)
          · exact hfl.1 (h2 ▸ hw_mem)
          · exact hv_left.1 (hw_eq ▸ hw_mem), hv_fresh.2⟩
      exact ih h_rest_fresh h_nodup_rest v hv hm
    · exact hfresh_not_rest ((mergePrenex_fv_suffix op body' right rest).subset hv)
  | case3 left y body fresh rest _ _ hqd renbody result' rest' _ ih_inner =>
    simp only [mergePrenex, show left.quantifierDepth = 0 from hqd, ite_true, allVarsOf]
    intro v hv hm
    rw [Finset.mem_union, Finset.mem_singleton] at hm
    have h_nodup_rest := (List.nodup_cons.mp h_nodup).2
    have hfresh_not_rest := (List.nodup_cons.mp h_nodup).1
    rcases hm with hm | rfl
    · have h_rest_fresh : ∀ v ∈ rest, v ∉ allVarsOf left ∧ v ∉ allVarsOf renbody := by
        intro v hv
        have hv_fresh := h_fresh v (List.mem_cons_of_mem _ hv)
        have hv_right := hv_fresh.2
        simp only [allVarsOf, Finset.mem_union, Finset.mem_singleton, not_or] at hv_right
        have hfr := (h_fresh fresh (List.mem_cons_self ..)).2
        simp only [allVarsOf, Finset.mem_union, Finset.mem_singleton, not_or] at hfr
        exact ⟨hv_fresh.1, fun hm => by
          rw [allVarsOf_renameFormulaEquiv (Equiv.swap y fresh) body (h_rename_vars _)] at hm
          obtain ⟨w, hw_mem, hw_eq⟩ := Finset.mem_image.mp hm
          simp only [Equiv.swap_apply_def] at hw_eq
          split_ifs at hw_eq with h1 h2
          · exact hfresh_not_rest (hw_eq ▸ hv)
          · exact hfr.1 (h2 ▸ hw_mem)
          · exact hv_right.1 (hw_eq ▸ hw_mem)⟩
      exact ih_inner h_rest_fresh h_nodup_rest v hv hm
    · exact hfresh_not_rest ((mergePrenex_fv_suffix op left renbody rest).subset hv)
  | case4 =>
    simp only [mergePrenex]; split; contradiction
    intro v hv hm
    have ⟨hl, hr⟩ := h_fresh v hv
    rcases h_op with rfl | rfl <;>
      simp only [allVarsOf, Finset.mem_union] at hm <;>
      rcases hm with hm | hm
    · exact hl hm
    · exact hr (Finset.mem_union.mpr hm)
    · exact hl hm
    · exact hr (Finset.mem_union.mpr hm)
  | case5 left y body fresh rest _ _ hqd renbody result' rest' _ ih_inner =>
    simp only [mergePrenex, show left.quantifierDepth = 0 from hqd, ite_true, allVarsOf]
    intro v hv hm
    rw [Finset.mem_union, Finset.mem_singleton] at hm
    have h_nodup_rest := (List.nodup_cons.mp h_nodup).2
    have hfresh_not_rest := (List.nodup_cons.mp h_nodup).1
    rcases hm with hm | rfl
    · have h_rest_fresh : ∀ v ∈ rest, v ∉ allVarsOf left ∧ v ∉ allVarsOf renbody := by
        intro v hv
        have hv_fresh := h_fresh v (List.mem_cons_of_mem _ hv)
        have hv_right := hv_fresh.2
        simp only [allVarsOf, Finset.mem_union, Finset.mem_singleton, not_or] at hv_right
        have hfr := (h_fresh fresh (List.mem_cons_self ..)).2
        simp only [allVarsOf, Finset.mem_union, Finset.mem_singleton, not_or] at hfr
        exact ⟨hv_fresh.1, fun hm => by
          rw [allVarsOf_renameFormulaEquiv (Equiv.swap y fresh) body (h_rename_vars _)] at hm
          obtain ⟨w, hw_mem, hw_eq⟩ := Finset.mem_image.mp hm
          simp only [Equiv.swap_apply_def] at hw_eq
          split_ifs at hw_eq with h1 h2
          · exact hfresh_not_rest (hw_eq ▸ hv)
          · exact hfr.1 (h2 ▸ hw_mem)
          · exact hv_right.1 (hw_eq ▸ hw_mem)⟩
      exact ih_inner h_rest_fresh h_nodup_rest v hv hm
    · exact hfresh_not_rest ((mergePrenex_fv_suffix op left renbody rest).subset hv)
  | case6 =>
    simp only [mergePrenex]; split; contradiction
    intro v hv hm
    have ⟨hl, hr⟩ := h_fresh v hv
    rcases h_op with rfl | rfl <;>
      simp only [allVarsOf, Finset.mem_union] at hm <;>
      rcases hm with hm | hm
    · exact hl hm
    · exact hr (Finset.mem_union.mpr hm)
    · exact hl hm
    · exact hr (Finset.mem_union.mpr hm)
  | case7 =>
    simp only [mergePrenex]
    intro v hv hm
    have ⟨hl, hr⟩ := h_fresh v hv
    rcases h_op with rfl | rfl <;>
      simp only [allVarsOf, Finset.mem_union] at hm <;>
      rcases hm with hm | hm
    · exact hl hm
    · exact hr hm
    · exact hl hm
    · exact hr hm

omit [AtomNeg α] in
/-- Unconsumed fresh variables are still fresh for the result formula. -/
theorem toPrenexNNF_fv_fresh_result (Φ : Formula σ α) (fv : List σ)
    (h_fresh : ∀ v ∈ fv, v ∉ allVarsOf Φ) (h_nodup : fv.Nodup)
    (h_rename_vars : ∀ (e : σ ≃ σ) (a : α),
      AtomVars.vars (AtomRename.renameEquiv e a) = (AtomVars.vars a).image e) :
    ∀ v ∈ (toPrenexNNF Φ fv).2, v ∉ allVarsOf (toPrenexNNF Φ fv).1 := by
  induction Φ generalizing fv with
  | atom _ => intro v hv; exact h_fresh v hv
  | not _ _ => intro v hv; exact h_fresh v hv
  | exists_ x Φ ih =>
    simp only [toPrenexNNF, allVarsOf]
    intro v hv hm
    rw [Finset.mem_union, Finset.mem_singleton] at hm
    rcases hm with hm | rfl
    · exact ih fv (fun v hv h => h_fresh v hv (Finset.mem_union.mpr (.inl h)))
        h_nodup v hv hm
    · exact h_fresh v ((toPrenexNNF_fv_suffix Φ fv).subset hv)
        (Finset.mem_union.mpr (.inr (Finset.mem_singleton.mpr rfl)))
  | forall_ x Φ ih =>
    simp only [toPrenexNNF, allVarsOf]
    intro v hv hm
    rw [Finset.mem_union, Finset.mem_singleton] at hm
    rcases hm with hm | rfl
    · exact ih fv (fun v hv h => h_fresh v hv (Finset.mem_union.mpr (.inl h)))
        h_nodup v hv hm
    · exact h_fresh v ((toPrenexNNF_fv_suffix Φ fv).subset hv)
        (Finset.mem_union.mpr (.inr (Finset.mem_singleton.mpr rfl)))
  | and Φ₁ Φ₂ ih₁ ih₂ =>
    simp only [toPrenexNNF]
    set p₁ := toPrenexNNF Φ₁ fv
    set p₂ := toPrenexNNF Φ₂ p₁.2
    have h_fv₁_suffix := toPrenexNNF_fv_suffix Φ₁ fv
    have h_fv₁_nodup := h_nodup.sublist h_fv₁_suffix.sublist
    have h_fresh₂ : ∀ v ∈ p₁.2, v ∉ allVarsOf Φ₂ :=
      fun v hv h => h_fresh v (h_fv₁_suffix.subset hv)
        (Finset.mem_union.mpr (.inr h))
    have h_fv₂_nodup := h_fv₁_nodup.sublist (toPrenexNNF_fv_suffix Φ₂ p₁.2).sublist
    have h_fv₁_fresh₁ : ∀ v ∈ p₁.2, v ∉ allVarsOf p₁.1 := ih₁ fv
      (fun v hv h => h_fresh v hv (Finset.mem_union.mpr (.inl h))) h_nodup
    have h_fv₂_fresh₂ : ∀ v ∈ p₂.2, v ∉ allVarsOf p₂.1 := ih₂ p₁.2 h_fresh₂ h_fv₁_nodup
    have h_fv₂_fresh₁ : ∀ v ∈ p₂.2, v ∉ allVarsOf p₁.1 :=
      fun v hv => h_fv₁_fresh₁ v ((toPrenexNNF_fv_suffix Φ₂ p₁.2).subset hv)
    have h_merge_fresh : ∀ v ∈ p₂.2, v ∉ allVarsOf p₁.1 ∧ v ∉ allVarsOf p₂.1 :=
      fun v hv => ⟨h_fv₂_fresh₁ v hv, h_fv₂_fresh₂ v hv⟩
    exact mergePrenex_fv_fresh_result _ p₁.1 p₂.1 p₂.2 h_merge_fresh h_fv₂_nodup (.inl rfl) h_rename_vars
  | or Φ₁ Φ₂ ih₁ ih₂ =>
    simp only [toPrenexNNF]
    set p₁ := toPrenexNNF Φ₁ fv
    set p₂ := toPrenexNNF Φ₂ p₁.2
    have h_fv₁_suffix := toPrenexNNF_fv_suffix Φ₁ fv
    have h_fv₁_nodup := h_nodup.sublist h_fv₁_suffix.sublist
    have h_fresh₂ : ∀ v ∈ p₁.2, v ∉ allVarsOf Φ₂ :=
      fun v hv h => h_fresh v (h_fv₁_suffix.subset hv)
        (Finset.mem_union.mpr (.inr h))
    have h_fv₂_nodup := h_fv₁_nodup.sublist (toPrenexNNF_fv_suffix Φ₂ p₁.2).sublist
    have h_fv₁_fresh₁ : ∀ v ∈ p₁.2, v ∉ allVarsOf p₁.1 := ih₁ fv
      (fun v hv h => h_fresh v hv (Finset.mem_union.mpr (.inl h))) h_nodup
    have h_fv₂_fresh₂ : ∀ v ∈ p₂.2, v ∉ allVarsOf p₂.1 := ih₂ p₁.2 h_fresh₂ h_fv₁_nodup
    have h_fv₂_fresh₁ : ∀ v ∈ p₂.2, v ∉ allVarsOf p₁.1 :=
      fun v hv => h_fv₁_fresh₁ v ((toPrenexNNF_fv_suffix Φ₂ p₁.2).subset hv)
    have h_merge_fresh : ∀ v ∈ p₂.2, v ∉ allVarsOf p₁.1 ∧ v ∉ allVarsOf p₂.1 :=
      fun v hv => ⟨h_fv₂_fresh₁ v hv, h_fv₂_fresh₂ v hv⟩
    exact mergePrenex_fv_fresh_result _ p₁.1 p₂.1 p₂.2 h_merge_fresh h_fv₂_nodup (.inr rfl) h_rename_vars
  | implies _ _ _ _ => intro v hv; exact h_fresh v hv

/-! ### toPrenexNNF preserves gRealization -/

theorem toPrenexNNF_gRealization
    (Φ : Formula σ α) (fv : List σ)
    (h_fresh : ∀ v ∈ fv, v ∉ allVarsOf Φ)
    (h_nodup : fv.Nodup)
    (h_rename_vars : ∀ (e : σ ≃ σ) (a : α),
      AtomVars.vars (AtomRename.renameEquiv e a) = (AtomVars.vars a).image e) :
    gRealization (K := K) (toPrenexNNF Φ fv).1 = gRealization Φ := by
  induction Φ generalizing fv with
  | atom a => simp [toPrenexNNF]
  | not Φ _ => simp [toPrenexNNF]
  | exists_ x Φ ih =>
    simp only [toPrenexNNF, gRealization]
    ext y; simp only [Set.mem_setOf_eq]
    have h_sub : ∀ v ∈ fv, v ∉ allVarsOf Φ := by
      intro v hv h
      exact h_fresh v hv (Finset.mem_union.mpr (.inl h))
    rw [ih fv h_sub h_nodup]
  | forall_ x Φ ih =>
    simp only [toPrenexNNF, gRealization]
    ext y; simp only [Set.mem_setOf_eq]
    have h_sub : ∀ v ∈ fv, v ∉ allVarsOf Φ := by
      intro v hv h
      exact h_fresh v hv (Finset.mem_union.mpr (.inl h))
    rw [ih fv h_sub h_nodup]
  | and Φ₁ Φ₂ ih₁ ih₂ =>
    simp only [toPrenexNNF]
    set p₁ := toPrenexNNF Φ₁ fv with hp₁
    set p₂ := toPrenexNNF Φ₂ p₁.2 with hp₂
    have h_fresh₁ : ∀ v ∈ fv, v ∉ allVarsOf Φ₁ :=
      fun v hv h => h_fresh v hv (Finset.mem_union.mpr (.inl h))
    have h_fresh₂_fv : ∀ v ∈ fv, v ∉ allVarsOf Φ₂ :=
      fun v hv h => h_fresh v hv (Finset.mem_union.mpr (.inr h))
    have h_fv₁_suffix : p₁.2 <:+ fv := toPrenexNNF_fv_suffix Φ₁ fv
    have h_fv₁_nodup : p₁.2.Nodup := h_nodup.sublist h_fv₁_suffix.sublist
    have h_fresh₂ : ∀ v ∈ p₁.2, v ∉ allVarsOf Φ₂ :=
      fun v hv => h_fresh₂_fv v (h_fv₁_suffix.subset hv)
    have h_eq₁ : gRealization (K := K) p₁.1 = gRealization Φ₁ :=
      ih₁ fv h_fresh₁ h_nodup
    have h_eq₂ : gRealization (K := K) p₂.1 = gRealization Φ₂ :=
      ih₂ p₁.2 h_fresh₂ h_fv₁_nodup
    -- Need freshness of fv₂ for mergePrenex
    have h_fv₂_suffix : p₂.2 <:+ p₁.2 := toPrenexNNF_fv_suffix Φ₂ p₁.2
    have h_fv₂_nodup : p₂.2.Nodup := h_fv₁_nodup.sublist h_fv₂_suffix.sublist
    have h_fv₁_fresh₁ : ∀ v ∈ p₁.2, v ∉ allVarsOf p₁.1 :=
      toPrenexNNF_fv_fresh_result Φ₁ fv h_fresh₁ h_nodup h_rename_vars
    have h_fv₂_fresh₂ : ∀ v ∈ p₂.2, v ∉ allVarsOf p₂.1 :=
      toPrenexNNF_fv_fresh_result Φ₂ p₁.2 h_fresh₂ h_fv₁_nodup h_rename_vars
    have h_fv₂_fresh₁ : ∀ v ∈ p₂.2, v ∉ allVarsOf p₁.1 :=
      fun v hv => h_fv₁_fresh₁ v (h_fv₂_suffix.subset hv)
    have h_merge_fresh : ∀ v ∈ p₂.2, v ∉ allVarsOf p₁.1 ∧ v ∉ allVarsOf p₂.1 :=
      fun v hv => ⟨h_fv₂_fresh₁ v hv, h_fv₂_fresh₂ v hv⟩
    calc gRealization (K := K) (mergePrenex Formula.and p₁.1 p₂.1 p₂.2).1
        = gRealization (.and p₁.1 p₂.1) :=
          mergePrenex_gRealization _ p₁.1 p₂.1 p₂.2 h_merge_fresh h_fv₂_nodup
            (.inl rfl) h_rename_vars
      _ = gRealization (.and Φ₁ Φ₂) := by simp only [gRealization, h_eq₁, h_eq₂]
  | or Φ₁ Φ₂ ih₁ ih₂ =>
    simp only [toPrenexNNF]
    set p₁ := toPrenexNNF Φ₁ fv with hp₁
    set p₂ := toPrenexNNF Φ₂ p₁.2 with hp₂
    have h_fresh₁ : ∀ v ∈ fv, v ∉ allVarsOf Φ₁ :=
      fun v hv h => h_fresh v hv (Finset.mem_union.mpr (.inl h))
    have h_fresh₂_fv : ∀ v ∈ fv, v ∉ allVarsOf Φ₂ :=
      fun v hv h => h_fresh v hv (Finset.mem_union.mpr (.inr h))
    have h_fv₁_suffix : p₁.2 <:+ fv := toPrenexNNF_fv_suffix Φ₁ fv
    have h_fv₁_nodup : p₁.2.Nodup := h_nodup.sublist h_fv₁_suffix.sublist
    have h_fresh₂ : ∀ v ∈ p₁.2, v ∉ allVarsOf Φ₂ :=
      fun v hv => h_fresh₂_fv v (h_fv₁_suffix.subset hv)
    have h_eq₁ : gRealization (K := K) p₁.1 = gRealization Φ₁ :=
      ih₁ fv h_fresh₁ h_nodup
    have h_eq₂ : gRealization (K := K) p₂.1 = gRealization Φ₂ :=
      ih₂ p₁.2 h_fresh₂ h_fv₁_nodup
    have h_fv₂_suffix : p₂.2 <:+ p₁.2 := toPrenexNNF_fv_suffix Φ₂ p₁.2
    have h_fv₂_nodup : p₂.2.Nodup := h_fv₁_nodup.sublist h_fv₂_suffix.sublist
    have h_fv₁_fresh₁ : ∀ v ∈ p₁.2, v ∉ allVarsOf p₁.1 :=
      toPrenexNNF_fv_fresh_result Φ₁ fv h_fresh₁ h_nodup h_rename_vars
    have h_fv₂_fresh₂ : ∀ v ∈ p₂.2, v ∉ allVarsOf p₂.1 :=
      toPrenexNNF_fv_fresh_result Φ₂ p₁.2 h_fresh₂ h_fv₁_nodup h_rename_vars
    have h_fv₂_fresh₁ : ∀ v ∈ p₂.2, v ∉ allVarsOf p₁.1 :=
      fun v hv => h_fv₁_fresh₁ v (h_fv₂_suffix.subset hv)
    have h_merge_fresh : ∀ v ∈ p₂.2, v ∉ allVarsOf p₁.1 ∧ v ∉ allVarsOf p₂.1 :=
      fun v hv => ⟨h_fv₂_fresh₁ v hv, h_fv₂_fresh₂ v hv⟩
    calc gRealization (K := K) (mergePrenex Formula.or p₁.1 p₂.1 p₂.2).1
        = gRealization (.or p₁.1 p₂.1) :=
          mergePrenex_gRealization _ p₁.1 p₂.1 p₂.2 h_merge_fresh h_fv₂_nodup
            (.inr rfl) h_rename_vars
      _ = gRealization (.or Φ₁ Φ₂) := by simp only [gRealization, h_eq₁, h_eq₂]
  | implies Φ₁ Φ₂ _ _ => simp [toPrenexNNF]

/-! ### Concrete h_rename_vars for AzFieldAtom -/

/-- `MvPolynomial.rename` by an equivalence gives exact equality on `vars`. -/
private theorem MvPolynomial.vars_rename_equiv {σ' τ : Type*} [DecidableEq σ'] [DecidableEq τ]
    {R' : Type*} [CommSemiring R']
    (e : σ' ≃ τ) (φ : MvPolynomial σ' R') :
    (MvPolynomial.rename e φ).vars = φ.vars.image e := by
  apply Finset.Subset.antisymm
  · exact MvPolynomial.vars_rename e φ
  · intro v hv
    rw [Finset.mem_image] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    have h1 : (MvPolynomial.rename e.symm (MvPolynomial.rename e φ)).vars = φ.vars := by
      simp [MvPolynomial.rename_rename]
    have h2 := MvPolynomial.vars_rename e.symm (MvPolynomial.rename e φ)
    rw [h1] at h2
    obtain ⟨u, hu, hue⟩ := Finset.mem_image.mp (h2 hw)
    rw [← hue, Equiv.apply_symm_apply]; exact hu

/-- The `h_rename_vars` hypothesis holds for `AzFieldAtom`. -/
theorem azFieldAtom_rename_vars {n : ℕ} {σ' : Type*} [LinearOrder σ'] [Var σ' n]
    {R' : Type*} [CommSemiring R'] [NoZeroDivisors R'] [DecidableEq R']
    {ord' : MonomialOrder} (e : σ' ≃ σ') (a : AzFieldAtom σ' R' ord') :
    AtomVars.vars (AtomRename.renameEquiv e a) = (AtomVars.vars a).image e := by
  change (a.renameVarsInjective ⇑e e.injective).poly.vars = a.poly.vars.image ⇑e
  rw [show (a.renameVarsInjective ⇑e e.injective).poly = a.poly.renameInjective ⇑e e.injective
    from rfl]
  rw [← toMvPoly_vars, ← toMvPoly_vars, AzMvPolynomial.toMvPoly_renameInjective]
  exact MvPolynomial.vars_rename_equiv e (AzMvPolynomial.toMvPoly a.poly)

/-! ### AtomRealization instance for AzFieldAtom -/

/-- Noncomputable interpretation for `AzFieldAtom`: maps an atom to the set of
    variable assignments satisfying `P = 0` (if `isEq`) or `P ≠ 0`. -/
noncomputable def azFieldAtomInterpret {n : ℕ} {σ' : Type*} [LinearOrder σ'] [Var σ' n]
    {R' : Type*} [CommRing R'] {ord' : MonomialOrder}
    {K : Type*} [Field K] [Algebra R' K]
    (a : AzFieldAtom σ' R' ord') : Set (σ' → K) :=
  if a.isEq then { y | MvPolynomial.aeval y a.poly.toMvPoly = 0 }
  else { y | MvPolynomial.aeval y a.poly.toMvPoly ≠ 0 }

noncomputable instance azFieldAtomRealization
    {n : ℕ} {σ' : Type*} [LinearOrder σ'] [Var σ' n]
    {R' : Type*} [CommRing R'] [NoZeroDivisors R'] [DecidableEq R']
    {ord' : MonomialOrder}
    {K : Type*} [Field K] [Algebra R' K] :
    AtomRealization (AzFieldAtom σ' R' ord') σ' K where
  interpret := azFieldAtomInterpret
  neg_interpret := by
    intro a
    simp only [AtomNeg.neg, azFieldAtomInterpret]
    cases a.isEq <;> simp [Set.compl_setOf, ne_eq, not_not]
  rename_interpret := by
    intro e a
    simp only [AtomRename.renameEquiv, azFieldAtomInterpret, AzFieldAtom.renameVarsInjective]
    ext y
    simp_rw [AzMvPolynomial.toMvPoly_renameInjective, MvPolynomial.aeval_rename]
    cases a.isEq <;> simp [Set.mem_setOf_eq]
  interpret_invariant := by
    intro a x hx y c
    simp only [azFieldAtomInterpret]
    suffices h : MvPolynomial.aeval (Function.update y x c) a.poly.toMvPoly =
        MvPolynomial.aeval y a.poly.toMvPoly by
      cases a.isEq <;> simp [Set.mem_setOf_eq, h]
    simp only [MvPolynomial.aeval_def]
    apply MvPolynomial.eval₂_congr (algebraMap R' K)
    intro i ci hi hci
    have hix : i ≠ x := by
      intro heq; apply hx; subst heq
      change i ∈ a.poly.vars
      have h1 : ci ∈ a.poly.toMvPoly.support := MvPolynomial.mem_support_iff.mpr hci
      have h2 : i ∈ a.poly.toMvPoly.vars := (MvPolynomial.mem_vars i).mpr ⟨ci, h1, hi⟩
      convert h2 using 1
      exact (toMvPoly_vars a.poly).symm
    simp [hix]

/-! ### freshIndexedVars properties -/

/-- The list `freshIndexedVars m start count h` has no duplicates. -/
theorem freshIndexedVars_nodup (m start count : ℕ) (h : start + count ≤ m) :
    (freshIndexedVars m start count h).Nodup := by
  simp only [freshIndexedVars]
  apply List.Nodup.map
  · intro a b hab
    simp only [IndexedVar.mk.injEq, Fin.mk.injEq] at hab
    exact Fin.ext (by omega)
  · exact List.nodup_finRange count

/-- Every variable in the embedded formula has index `< n`, so it is disjoint from
    fresh variables with index `≥ n`. -/
theorem freshIndexedVars_fresh {R' : Type*} [Semiring R'] {ord' : MonomialOrder}
    (m n depth : ℕ) (h : n + depth ≤ m)
    (embedded : Formula (IndexedVar m) (AzFieldAtom (IndexedVar m) R' ord'))
    (h_bound : ∀ v ∈ allVarsOf embedded, (v : IndexedVar m).val.val < n) :
    ∀ v ∈ freshIndexedVars m n depth h, v ∉ allVarsOf embedded := by
  intro v hv hm
  simp only [freshIndexedVars, List.mem_map, List.mem_finRange] at hv
  obtain ⟨i, _, rfl⟩ := hv
  have := h_bound _ hm
  show False
  have : n + i.val < n := this
  omega

end Azurite
