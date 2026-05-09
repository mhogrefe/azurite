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

open AzMvPolynomial MonicMonomial Monomial BPR Formula

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
theorem azFieldAtom_rename_vars {n : ℕ}
    {R' : Type*} [CommSemiring R'] [NoZeroDivisors R'] [DecidableEq R']
    {ord' : MonomialOrder} (e : Fin n ≃ Fin n) (a : AzFieldAtom n R' ord') :
    AtomVars.vars (AtomRename.renameEquiv e a) = (AtomVars.vars a).image e := by
  change (a.renameVarsInjective ⇑e e.injective).poly.vars = a.poly.vars.image ⇑e
  rw [show (a.renameVarsInjective ⇑e e.injective).poly = a.poly.renameInjective ⇑e e.injective
    from rfl]
  rw [← toMvPoly_vars, ← toMvPoly_vars, AzMvPolynomial.toMvPoly_renameInjective]
  exact MvPolynomial.vars_rename_equiv e (AzMvPolynomial.toMvPoly a.poly)

/-! ### AtomRealization instance for AzFieldAtom -/

/-- Noncomputable interpretation for `AzFieldAtom`: maps an atom to the set of
    variable assignments satisfying `P = 0` (if `isEq`) or `P ≠ 0`. -/
noncomputable def azFieldAtomInterpret {n : ℕ}
    {R' : Type*} [CommRing R'] {ord' : MonomialOrder}
    {K : Type*} [Field K] [Algebra R' K]
    (a : AzFieldAtom n R' ord') : Set (Fin n → K) :=
  if a.isEq then { y | MvPolynomial.aeval y a.poly.toMvPoly = 0}
  else { y | MvPolynomial.aeval y a.poly.toMvPoly ≠ 0}

noncomputable instance azFieldAtomRealization
    {n : ℕ} {R' : Type*} [CommRing R'] [NoZeroDivisors R'] [DecidableEq R']
    {ord' : MonomialOrder}
    {K : Type*} [Field K] [Algebra R' K] :
    AtomRealization (AzFieldAtom n R' ord') (Fin n) K where
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
      have h2 : i ∈ a.poly.toMvPoly.vars := (MvPolynomial.mem_vars_iff_mem_support i).mpr ⟨ci, h1, hi⟩
      convert h2 using 1
      exact (toMvPoly_vars a.poly).symm
    simp [hix]

/-! ### freshVars properties -/

/-- The list `freshVars m start count h` has no duplicates. -/
theorem freshVars_nodup (m start count : ℕ)
    (h : start + count ≤ m) :
    (freshVars m start count h).Nodup := by
  simp only [freshVars]
  apply List.Nodup.map
  · intro a b hab
    simp only [Fin.mk.injEq] at hab
    exact Fin.ext (by omega)
  · exact List.nodup_finRange count

/-- Every variable in the embedded formula has index `< n`, so it is disjoint from
    fresh variables with index `≥ n`. -/
theorem freshVars_fresh
    {R' : Type*} [Semiring R'] {ord' : MonomialOrder}
    (m n depth : ℕ) (h : n + depth ≤ m)
    (embedded : Formula (Fin m) (AzFieldAtom m R' ord'))
    (h_bound : ∀ v ∈ allVarsOf embedded, v.val < n) :
    ∀ v ∈ freshVars m n depth h, v ∉ allVarsOf embedded := by
  intro v hv hm
  simp only [freshVars, List.mem_map, List.mem_finRange] at hv
  obtain ⟨i, _, rfl⟩ := hv
  have h1 := h_bound _ hm
  change n + i.val < n at h1
  omega

/-! ### gRealization ↔ azRealization bridge -/

/-- `gRealization` with the `azFieldAtomRealization` instance equals `azRealization`. -/
theorem gRealization_eq_azRealization {n : ℕ}
    {R' : Type*} [CommRing R'] [NoZeroDivisors R'] [DecidableEq R']
    {ord' : MonomialOrder}
    {K : Type*} [Field K] [Algebra R' K]
    (Φ : Formula (Fin n) (AzFieldAtom n R' ord')) :
    gRealization (K := K) Φ = azRealization (C := K) Φ := by
  induction Φ with
  | atom a =>
    show azFieldAtomInterpret a = (BPR.Formula.atom (AzFieldAtom.toFieldAtom a)).realization
    simp only [azFieldAtomInterpret, BPR.Formula.realization, AzFieldAtom.toFieldAtom]
  | not _ ih => simp only [gRealization, azRealization, azFormulaToFieldFormula, mapAtom,
      BPR.Formula.realization]; exact congrArg Set.compl ih
  | and _ _ ih₁ ih₂ => simp only [gRealization, azRealization, azFormulaToFieldFormula, mapAtom,
      BPR.Formula.realization]; exact congr (congrArg _ ih₁) ih₂
  | or _ _ ih₁ ih₂ => simp only [gRealization, azRealization, azFormulaToFieldFormula, mapAtom,
      BPR.Formula.realization]; exact congr (congrArg _ ih₁) ih₂
  | implies _ _ ih₁ ih₂ => simp only [gRealization, azRealization, azFormulaToFieldFormula,
      mapAtom, BPR.Formula.realization]; exact congr (congrArg _ (congrArg _ ih₁)) ih₂
  | exists_ x _ ih =>
    show { y | ∃ c, Function.update y x c ∈ gRealization _} =
         { y | ∃ c, Function.update y x c ∈ (mapAtom AzFieldAtom.toFieldAtom _).realization}
    simp_rw [ih]; rfl
  | forall_ x _ ih =>
    show { y | ∀ c, Function.update y x c ∈ gRealization _} =
         { y | ∀ c, Function.update y x c ∈ (mapAtom AzFieldAtom.toFieldAtom _).realization}
    simp_rw [ih]; rfl

/-! ### allVarsOf bound for embedded formulas -/

/-- All variables in a formula renamed via `Fin.castLE` have index `< n`. -/
theorem allVarsOf_rename_embed_bound
    {n m : ℕ} {R' : Type*} [CommRing R']
    [NoZeroDivisors R'] [DecidableEq R'] {ord' : MonomialOrder}
    (h_le : n ≤ m)
    (Φ : Formula (Fin n) (AzFieldAtom n R' ord'))
    (v : Fin m) :
    v ∈ allVarsOf (Φ.rename (Fin.castLE h_le)
      (AzFieldAtom.renameVarsMonotone (Fin.castLE h_le)
        (fun _ _ hab => hab))) →
    v.val < n := by
  induction Φ with
  | atom a =>
    intro hv
    -- Unfold to AzMvPolynomial.vars
    change v ∈ (a.poly.renameMonotone (Fin.castLE h_le)
      (fun _ _ hab => hab)).vars at hv
    -- Bridge to MvPolynomial.vars
    have key : v ∈ (MvPolynomial.rename
        (Fin.castLE h_le : Fin n → Fin m) a.poly.toMvPoly).vars := by
      rw [← @toMvPoly_vars R' _ m ord'] at hv
      rw [AzMvPolynomial.toMvPoly_renameMonotone
        a.poly (Fin.castLE h_le) (fun _ _ hab => hab)] at hv
      exact hv
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp
      (MvPolynomial.vars_rename (Fin.castLE h_le) a.poly.toMvPoly key)
    simp only [Fin.val_castLE]
    exact w.isLt
  | not _ ih => exact ih
  | and _ _ ih₁ ih₂ =>
    simp only [Formula.rename, allVarsOf, Finset.mem_union]
    rintro (h | h)
    · exact ih₁ h
    · exact ih₂ h
  | or _ _ ih₁ ih₂ =>
    simp only [Formula.rename, allVarsOf, Finset.mem_union]
    rintro (h | h)
    · exact ih₁ h
    · exact ih₂ h
  | implies _ _ ih₁ ih₂ =>
    simp only [Formula.rename, allVarsOf, Finset.mem_union]
    rintro (h | h)
    · exact ih₁ h
    · exact ih₂ h
  | exists_ x _ ih =>
    simp only [Formula.rename, allVarsOf, Finset.mem_union, Finset.mem_singleton]
    rintro (h | h)
    · exact ih h
    · subst h
      simp only [Fin.val_castLE]
      exact x.isLt
  | forall_ x _ ih =>
    simp only [Formula.rename, allVarsOf, Finset.mem_union, Finset.mem_singleton]
    rintro (h | h)
    · exact ih h
    · subst h
      simp only [Fin.val_castLE]
      exact x.isLt
/-! ### azRealization and rename -/

/-- Converting to FieldFormula commutes with rename: convert-then-rename = rename-then-convert. -/
theorem azFormulaToFieldFormula_rename {n m : ℕ}
    {R' : Type*} [CommRing R'] [NoZeroDivisors R'] [DecidableEq R']
    {ord' : MonomialOrder}
    (f : Fin n → Fin m) (hg : StrictMono f)
    (Φ : Formula (Fin n) (AzFieldAtom n R' ord')) :
    azFormulaToFieldFormula (Φ.rename f (AzFieldAtom.renameVarsMonotone f hg)) =
      (azFormulaToFieldFormula Φ).rename f (FieldAtom.renameVars f) := by
  induction Φ with
  | atom a =>
    simp only [Formula.rename, azFormulaToFieldFormula, mapAtom, AzFieldAtom.toFieldAtom,
      AzFieldAtom.renameVarsMonotone, FieldAtom.renameVars]
    simp only [Formula.atom.injEq, FieldAtom.mk.injEq]
    exact ⟨AzMvPolynomial.toMvPoly_renameMonotone a.poly f hg, trivial⟩
  | not _ ih =>
    simp only [Formula.rename, azFormulaToFieldFormula, mapAtom]
    exact congrArg Formula.not ih
  | and _ _ ih₁ ih₂ =>
    simp only [Formula.rename, azFormulaToFieldFormula, mapAtom]
    exact congrArg₂ Formula.and ih₁ ih₂
  | or _ _ ih₁ ih₂ =>
    simp only [Formula.rename, azFormulaToFieldFormula, mapAtom]
    exact congrArg₂ Formula.or ih₁ ih₂
  | implies _ _ ih₁ ih₂ =>
    simp only [Formula.rename, azFormulaToFieldFormula, mapAtom]
    exact congrArg₂ Formula.implies ih₁ ih₂
  | exists_ x _ ih =>
    simp only [Formula.rename, azFormulaToFieldFormula, mapAtom]
    exact congrArg (Formula.exists_ (f x)) ih
  | forall_ x _ ih =>
    simp only [Formula.rename, azFormulaToFieldFormula, mapAtom]
    exact congrArg (Formula.forall_ (f x)) ih

/-- `azRealization` is preserved under injective rename via preimage. -/
theorem azRealization_rename {n m : ℕ}
    {R' : Type*} [CommRing R'] [NoZeroDivisors R'] [DecidableEq R']
    {ord' : MonomialOrder}
    {K : Type*} [Field K] [Algebra R' K]
    (f : Fin n → Fin m) (hf : Function.Injective f) (hg : StrictMono f)
    (Φ : Formula (Fin n) (AzFieldAtom n R' ord')) :
    azRealization (C := K) (Φ.rename f (AzFieldAtom.renameVarsMonotone f hg)) =
      (· ∘ f) ⁻¹' azRealization (C := K) Φ := by
  simp only [azRealization, azFormulaToFieldFormula_rename f hg]
  exact rename_realization f hf (azFormulaToFieldFormula Φ)
/-! ### Syntactic prenex form -/

/-- A formula is in negation normal form: no `implies`, no `not`. -/
inductive IsNNF : Formula σ α → Prop where
  | atom (a : α) : IsNNF (.atom a)
  | and {Φ₁ Φ₂} : IsNNF Φ₁ → IsNNF Φ₂ → IsNNF (.and Φ₁ Φ₂)
  | or {Φ₁ Φ₂} : IsNNF Φ₁ → IsNNF Φ₂ → IsNNF (.or Φ₁ Φ₂)
  | exists_ (x : σ) {Φ} : IsNNF Φ → IsNNF (.exists_ x Φ)
  | forall_ (x : σ) {Φ} : IsNNF Φ → IsNNF (.forall_ x Φ)

omit [DecidableEq σ] [AtomNeg α] [AtomRename α σ] [AtomVars α σ] in
/-- `toNNFPos` and `toNNFNeg` both produce NNF formulas (no implies, no not). -/
private theorem toNNF_isNNF_aux [AtomNeg α] (Φ : Formula σ α) :
    IsNNF (toNNFPos Φ) ∧ IsNNF (toNNFPos.toNNFNeg Φ) := by
  induction Φ with
  | atom a => exact ⟨.atom a, .atom (AtomNeg.neg a)⟩
  | not _ ih => exact ⟨ih.2, ih.1⟩
  | and _ _ ih₁ ih₂ => exact ⟨.and ih₁.1 ih₂.1, .or ih₁.2 ih₂.2⟩
  | or _ _ ih₁ ih₂ => exact ⟨.or ih₁.1 ih₂.1, .and ih₁.2 ih₂.2⟩
  | implies _ _ ih₁ ih₂ => exact ⟨.or ih₁.2 ih₂.1, .and ih₁.1 ih₂.2⟩
  | exists_ x _ ih => exact ⟨.exists_ x ih.1, .forall_ x ih.2⟩
  | forall_ x _ ih => exact ⟨.forall_ x ih.1, .exists_ x ih.2⟩

omit [DecidableEq σ] [AtomNeg α] [AtomRename α σ] [AtomVars α σ] in
theorem toNNF_isNNF [AtomNeg α] (Φ : Formula σ α) : IsNNF (toNNF Φ) :=
  (toNNF_isNNF_aux Φ).1

omit [DecidableEq σ] [AtomNeg α] [AtomRename α σ] [AtomVars α σ] in
/-- `toNNFPos` and `toNNFPos.toNNFNeg` both preserve quantifier-freeness. -/
private theorem toNNFPos_and_Neg_isQF [AtomNeg α]
    (Ψ : Formula σ α) (h : Ψ.IsQuantifierFree) :
    (toNNFPos Ψ).IsQuantifierFree ∧ (toNNFPos.toNNFNeg Ψ).IsQuantifierFree := by
  induction Ψ with
  | atom _ => exact ⟨trivial, trivial⟩
  | not Ψ ih => exact ⟨(ih h).2, (ih h).1⟩
  | and Φ₁ Φ₂ ih₁ ih₂ =>
    obtain ⟨h₁, h₂⟩ := h
    exact ⟨⟨(ih₁ h₁).1, (ih₂ h₂).1⟩, ⟨(ih₁ h₁).2, (ih₂ h₂).2⟩⟩
  | or Φ₁ Φ₂ ih₁ ih₂ =>
    obtain ⟨h₁, h₂⟩ := h
    exact ⟨⟨(ih₁ h₁).1, (ih₂ h₂).1⟩, ⟨(ih₁ h₁).2, (ih₂ h₂).2⟩⟩
  | implies Φ₁ Φ₂ ih₁ ih₂ =>
    obtain ⟨h₁, h₂⟩ := h
    exact ⟨⟨(ih₁ h₁).2, (ih₂ h₂).1⟩, ⟨(ih₁ h₁).1, (ih₂ h₂).2⟩⟩
  | exists_ _ _ _ => exact h.elim
  | forall_ _ _ _ => exact h.elim

omit [DecidableEq σ] [AtomNeg α] [AtomRename α σ] [AtomVars α σ] in
/-- NNF conversion preserves quantifier-freeness. -/
theorem toNNF_isQF [AtomNeg α]
    (Φ : Formula σ α) (h : Φ.IsQuantifierFree) :
    (toNNF Φ).IsQuantifierFree :=
  (toNNFPos_and_Neg_isQF Φ h).1

/-! ### DNF realization

For a formula that is both in negation normal form and quantifier-free,
its realization equals the union (over DNF clauses) of the intersection
(over atoms in each clause) of atom realizations. -/

theorem nnfToDNF_gRealization (Φ : Formula σ α) (hnnf : IsNNF Φ)
    (hqf : Φ.IsQuantifierFree) :
    gRealization (K := K) Φ =
      { y | ∃ cl ∈ nnfToDNF Φ, ∀ a ∈ cl, y ∈ AtomRealization.interpret a } := by
  induction Φ with
  | atom a =>
    simp only [nnfToDNF, gRealization]
    ext y
    constructor
    · intro h
      refine ⟨[a], List.mem_singleton.mpr rfl, ?_⟩
      intro a' ha'
      simp only [List.mem_singleton] at ha'
      exact ha' ▸ h
    · rintro ⟨cl, hcl, h⟩
      simp only [List.mem_singleton] at hcl
      subst hcl
      exact h a (List.mem_singleton.mpr rfl)
  | not Φ' _ => cases hnnf
  | and Φ₁ Φ₂ ih₁ ih₂ =>
    cases hnnf with
    | and h₁ h₂ =>
      obtain ⟨hqf₁, hqf₂⟩ := hqf
      simp only [nnfToDNF, gRealization, ih₁ h₁ hqf₁, ih₂ h₂ hqf₂]
      ext y
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, List.mem_flatMap, List.mem_map]
      constructor
      · rintro ⟨⟨cl₁, hcl₁, h₁⟩, ⟨cl₂, hcl₂, h₂⟩⟩
        refine ⟨cl₁ ++ cl₂, ⟨cl₁, hcl₁, cl₂, hcl₂, rfl⟩, ?_⟩
        intro a ha
        rcases List.mem_append.mp ha with h | h
        · exact h₁ a h
        · exact h₂ a h
      · rintro ⟨cl, ⟨cl₁, hcl₁, cl₂, hcl₂, rfl⟩, h⟩
        refine ⟨⟨cl₁, hcl₁, fun a ha => h a (List.mem_append.mpr (.inl ha))⟩,
                ⟨cl₂, hcl₂, fun a ha => h a (List.mem_append.mpr (.inr ha))⟩⟩
  | or Φ₁ Φ₂ ih₁ ih₂ =>
    cases hnnf with
    | or h₁ h₂ =>
      obtain ⟨hqf₁, hqf₂⟩ := hqf
      simp only [nnfToDNF, gRealization, ih₁ h₁ hqf₁, ih₂ h₂ hqf₂]
      ext y
      simp only [Set.mem_union, Set.mem_setOf_eq, List.mem_append]
      constructor
      · rintro (⟨cl, hcl, h⟩ | ⟨cl, hcl, h⟩)
        · exact ⟨cl, .inl hcl, h⟩
        · exact ⟨cl, .inr hcl, h⟩
      · rintro ⟨cl, (hcl | hcl), h⟩
        · exact .inl ⟨cl, hcl, h⟩
        · exact .inr ⟨cl, hcl, h⟩
  | implies Φ₁ Φ₂ _ _ => cases hnnf
  | exists_ _ _ _ => exact hqf.elim
  | forall_ _ _ _ => exact hqf.elim

/-- DNF realization: for any quantifier-free formula `Φ`, `toDNF Φ`
represents the realization as a union (over clauses) of intersections
(over atoms). -/
theorem toDNF_gRealization (Φ : Formula σ α) (hqf : Φ.IsQuantifierFree) :
    gRealization (K := K) Φ =
      { y | ∃ cl ∈ toDNF Φ, ∀ a ∈ cl, y ∈ AtomRealization.interpret a } := by
  rw [← toNNF_gRealization (K := K) Φ]
  exact nnfToDNF_gRealization (toNNF Φ) (toNNF_isNNF Φ) (toNNF_isQF Φ hqf)

omit [DecidableEq σ] [AtomNeg α] [AtomRename α σ] [AtomVars α σ] in
/-- Renaming via an equiv preserves `IsPrenex`. -/
theorem renameFormulaEquiv_isPrenex [AtomRename α σ] (e : σ ≃ σ)
    {Φ : Formula σ α} (h : IsPrenex Φ) : IsPrenex (renameFormulaEquiv e Φ) := by
  exact rename_isPrenex e (AtomRename.renameEquiv e) h

omit [DecidableEq σ] [AtomNeg α] [AtomRename α σ] [AtomVars α σ] in
/-- Renaming via an equiv preserves `IsNNF`. -/
theorem renameFormulaEquiv_isNNF [AtomRename α σ] (e : σ ≃ σ)
    {Φ : Formula σ α} (h : IsNNF Φ) : IsNNF (renameFormulaEquiv e Φ) := by
  induction h with
  | atom a => exact .atom _
  | and _ _ ih₁ ih₂ => exact .and ih₁ ih₂
  | or _ _ ih₁ ih₂ => exact .or ih₁ ih₂
  | exists_ x _ ih => exact .exists_ (e x) ih
  | forall_ x _ ih => exact .forall_ (e x) ih

omit [DecidableEq σ] [AtomNeg α] [AtomRename α σ] [AtomVars α σ] in
/-- Quantifier-free formulas have quantifier depth 0. -/
theorem isQF_quantifierDepth_zero {Φ : Formula σ α} (h : Φ.IsQuantifierFree) :
    Φ.quantifierDepth = 0 := by
  induction Φ with
  | atom => rfl
  | not _ ih => exact ih h
  | and _ _ ih₁ ih₂ => simp [quantifierDepth, ih₁ h.1, ih₂ h.2]
  | or _ _ ih₁ ih₂ => simp [quantifierDepth, ih₁ h.1, ih₂ h.2]
  | implies _ _ ih₁ ih₂ => simp [quantifierDepth, ih₁ h.1, ih₂ h.2]
  | exists_ => exact absurd h (by simp [IsQuantifierFree])
  | forall_ => exact absurd h (by simp [IsQuantifierFree])

omit [DecidableEq σ] [AtomNeg α] [AtomRename α σ] [AtomVars α σ] in
/-- `mergePrenex` produces prenex formulas when given prenex inputs and a
    QF-preserving connective. -/
theorem mergePrenex_isPrenex [DecidableEq σ] [AtomRename α σ]
    (op : Formula σ α → Formula σ α → Formula σ α)
    (hop : ∀ Φ₁ Φ₂, Φ₁.IsQuantifierFree → Φ₂.IsQuantifierFree →
      (op Φ₁ Φ₂).IsQuantifierFree)
    (left right : Formula σ α) (fv : List σ)
    (hl : IsPrenex left) (hr : IsPrenex right)
    (hlen : left.quantifierDepth + right.quantifierDepth ≤ fv.length) :
    IsPrenex (mergePrenex op left right fv).1 := by
  induction left, right, fv using mergePrenex.induct op with
  | case1 x body right fresh rest =>
    simp only [mergePrenex]; apply IsPrenex.exists_
    rename_i body' _ _ _ ih
    have hbody := by cases hl with
      | exists_ h => exact h
      | qf h => exact absurd h (by simp [IsQuantifierFree])
    refine ih (renameFormulaEquiv_isPrenex _ hbody) hr ?_
    show (renameFormulaEquiv _ body).quantifierDepth + _ ≤ _
    rw [renameFormulaEquiv_quantifierDepth]
    simp [quantifierDepth, List.length_cons] at hlen; omega
  | case2 x body right fresh rest =>
    simp only [mergePrenex]; apply IsPrenex.forall_
    rename_i body' _ _ _ ih
    have hbody := by cases hl with
      | forall_ h => exact h
      | qf h => exact absurd h (by simp [IsQuantifierFree])
    refine ih (renameFormulaEquiv_isPrenex _ hbody) hr ?_
    show (renameFormulaEquiv _ body).quantifierDepth + _ ≤ _
    rw [renameFormulaEquiv_quantifierDepth]
    simp [quantifierDepth, List.length_cons] at hlen; omega
  | case3 left y body fresh rest h_not_ex h_not_all h_qd_eq =>
    simp only [mergePrenex, h_qd_eq, ↓reduceIte]; apply IsPrenex.exists_
    rename_i body' _ _ _ ih
    have hbody := by cases hr with
      | exists_ h => exact h
      | qf h => exact absurd h (by simp [IsQuantifierFree])
    refine ih hl (renameFormulaEquiv_isPrenex _ hbody) ?_
    show left.quantifierDepth + (renameFormulaEquiv _ body).quantifierDepth ≤ _
    rw [renameFormulaEquiv_quantifierDepth]
    simp [quantifierDepth, List.length_cons, h_qd_eq] at hlen; omega
  | case4 left y body fresh rest h_not_ex h_not_all h_qd =>
    exfalso; apply h_qd
    cases hl with
    | qf h => exact isQF_quantifierDepth_zero h
    | exists_ h => exact absurd rfl (h_not_ex _ _)
    | forall_ h => exact absurd rfl (h_not_all _ _)
  | case5 left y body fresh rest h_not_ex h_not_all h_qd_eq =>
    simp only [mergePrenex, h_qd_eq, ↓reduceIte]; apply IsPrenex.forall_
    rename_i body' _ _ _ ih
    have hbody := by cases hr with
      | forall_ h => exact h
      | qf h => exact absurd h (by simp [IsQuantifierFree])
    refine ih hl (renameFormulaEquiv_isPrenex _ hbody) ?_
    show left.quantifierDepth + (renameFormulaEquiv _ body).quantifierDepth ≤ _
    rw [renameFormulaEquiv_quantifierDepth]
    simp [quantifierDepth, List.length_cons, h_qd_eq] at hlen; omega
  | case6 left y body fresh rest h_not_ex h_not_all h_qd =>
    exfalso; apply h_qd
    cases hl with
    | qf h => exact isQF_quantifierDepth_zero h
    | exists_ h => exact absurd rfl (h_not_ex _ _)
    | forall_ h => exact absurd rfl (h_not_all _ _)
  | case7 =>
    simp only [mergePrenex]
    apply IsPrenex.qf; apply hop
    · rename_i fv h_nexl h_nall h_nexr h_nforr
      cases hl with
      | qf h => exact h
      | exists_ h =>
        exfalso
        cases fv with
        | nil => simp [quantifierDepth] at hlen
        | cons f r => exact h_nexl _ _ _ _ rfl rfl
      | forall_ h =>
        exfalso
        cases fv with
        | nil => simp [quantifierDepth] at hlen
        | cons f r => exact h_nall _ _ _ _ rfl rfl
    · rename_i fv h_nexl h_nall h_nexr h_nforr
      cases hr with
      | qf h => exact h
      | exists_ h =>
        exfalso
        cases fv with
        | nil => simp [quantifierDepth] at hlen
        | cons f r => exact h_nexr _ _ _ _ rfl rfl
      | forall_ h =>
        exfalso
        cases fv with
        | nil => simp [quantifierDepth] at hlen
        | cons f r => exact h_nforr _ _ _ _ rfl rfl

omit [DecidableEq σ] [AtomNeg α] [AtomRename α σ] [AtomVars α σ] in
/-- `mergePrenex` consumes exactly `left.quantifierDepth + right.quantifierDepth` fresh variables. -/
theorem mergePrenex_snd_length [DecidableEq σ] [AtomRename α σ]
    (op : Formula σ α → Formula σ α → Formula σ α)
    (left right : Formula σ α) (fv : List σ)
    (hlen : left.quantifierDepth + right.quantifierDepth ≤ fv.length)
    (hl : left.IsPrenex) (hr : right.IsPrenex) :
    (mergePrenex op left right fv).2.length +
      left.quantifierDepth + right.quantifierDepth = fv.length := by
  induction left, right, fv using mergePrenex.induct (op := op) with
  | case1 x body right fresh rest =>
    simp only [mergePrenex, quantifierDepth, List.length_cons] at hlen ⊢
    rename_i body' _ _ _ ih
    have hbody : body.IsPrenex := by cases hl with
      | exists_ h => exact h | qf h => exact absurd h (by simp [IsQuantifierFree])
    have h_ih := ih (by
      show (renameFormulaEquiv _ body).quantifierDepth + _ ≤ _
      rw [renameFormulaEquiv_quantifierDepth]; omega)
      (renameFormulaEquiv_isPrenex _ hbody) hr
    rw [show body' = renameFormulaEquiv _ body from rfl,
        renameFormulaEquiv_quantifierDepth] at h_ih
    omega
  | case2 x body right fresh rest =>
    simp only [mergePrenex, quantifierDepth, List.length_cons] at hlen ⊢
    rename_i body' _ _ _ ih
    have hbody : body.IsPrenex := by cases hl with
      | forall_ h => exact h | qf h => exact absurd h (by simp [IsQuantifierFree])
    have h_ih := ih (by
      show (renameFormulaEquiv _ body).quantifierDepth + _ ≤ _
      rw [renameFormulaEquiv_quantifierDepth]; omega)
      (renameFormulaEquiv_isPrenex _ hbody) hr
    rw [show body' = renameFormulaEquiv _ body from rfl,
        renameFormulaEquiv_quantifierDepth] at h_ih
    omega
  | case3 left y body fresh rest h_not_ex h_not_all h_qd_eq =>
    simp only [mergePrenex, h_qd_eq, ↓reduceIte, quantifierDepth, List.length_cons] at hlen ⊢
    rename_i body' _ _ _ ih
    have hbody : body.IsPrenex := by cases hr with
      | exists_ h => exact h | qf h => exact absurd h (by simp [IsQuantifierFree])
    have h_ih := ih (by
      show _ + (renameFormulaEquiv _ body).quantifierDepth ≤ _
      rw [renameFormulaEquiv_quantifierDepth]; omega)
      hl (renameFormulaEquiv_isPrenex _ hbody)
    rw [show body' = renameFormulaEquiv _ body from rfl,
        renameFormulaEquiv_quantifierDepth] at h_ih
    omega
  | case4 left y body fresh rest h_not_ex h_not_all h_qd =>
    -- Impossible: left is prenex, not exists/forall, but qd > 0
    exfalso; apply h_qd
    cases hl with
    | qf h => exact isQF_quantifierDepth_zero h
    | exists_ h => exact absurd rfl (h_not_ex _ _)
    | forall_ h => exact absurd rfl (h_not_all _ _)
  | case5 left y body fresh rest h_not_ex h_not_all h_qd_eq =>
    simp only [mergePrenex, h_qd_eq, ↓reduceIte, quantifierDepth, List.length_cons] at hlen ⊢
    rename_i body' _ _ _ ih
    have hbody : body.IsPrenex := by cases hr with
      | forall_ h => exact h | qf h => exact absurd h (by simp [IsQuantifierFree])
    have h_ih := ih (by
      show _ + (renameFormulaEquiv _ body).quantifierDepth ≤ _
      rw [renameFormulaEquiv_quantifierDepth]; omega)
      hl (renameFormulaEquiv_isPrenex _ hbody)
    rw [show body' = renameFormulaEquiv _ body from rfl,
        renameFormulaEquiv_quantifierDepth] at h_ih
    omega
  | case6 left y body fresh rest h_not_ex h_not_all h_qd =>
    exfalso; apply h_qd
    cases hl with
    | qf h => exact isQF_quantifierDepth_zero h
    | exists_ h => exact absurd rfl (h_not_ex _ _)
    | forall_ h => exact absurd rfl (h_not_all _ _)
  | case7 =>
    simp only [mergePrenex]
    -- Both QF (from IsPrenex + not matching quantifier patterns)
    rename_i left right fv h_nexl h_nall h_nexr h_nforr
    have hql : left.quantifierDepth = 0 := by
      cases hl with
      | qf h => exact isQF_quantifierDepth_zero h
      | exists_ h =>
        cases fv with
        | nil => simp [quantifierDepth] at hlen
        | cons f r => exact absurd rfl (h_nexl _ _ _ _ rfl)
      | forall_ h =>
        cases fv with
        | nil => simp [quantifierDepth] at hlen
        | cons f r => exact absurd rfl (h_nall _ _ _ _ rfl)
    have hqr : right.quantifierDepth = 0 := by
      cases hr with
      | qf h => exact isQF_quantifierDepth_zero h
      | exists_ h =>
        cases fv with
        | nil => simp [quantifierDepth] at hlen
        | cons f r => exact absurd rfl (h_nexr _ _ _ _ rfl)
      | forall_ h =>
        cases fv with
        | nil => simp [quantifierDepth] at hlen
        | cons f r => exact absurd rfl (h_nforr _ _ _ _ rfl)
    omega

omit [DecidableEq σ] [AtomNeg α] [AtomRename α σ] [AtomVars α σ] in
/-- `mergePrenex` preserves the total quantifier depth. -/
theorem mergePrenex_fst_quantifierDepth [DecidableEq σ] [AtomRename α σ]
    (op : Formula σ α → Formula σ α → Formula σ α)
    (hop : ∀ Φ₁ Φ₂ : Formula σ α, (op Φ₁ Φ₂).quantifierDepth =
      Φ₁.quantifierDepth + Φ₂.quantifierDepth)
    (left right : Formula σ α) (fv : List σ) :
    (mergePrenex op left right fv).1.quantifierDepth =
      left.quantifierDepth + right.quantifierDepth := by
  induction left, right, fv using mergePrenex.induct (op := op) with
  | case1 x body right fresh rest =>
    simp only [mergePrenex, quantifierDepth]
    rename_i body' _ _ _ ih
    rw [ih, show body' = renameFormulaEquiv _ body from rfl,
        renameFormulaEquiv_quantifierDepth]; omega
  | case2 x body right fresh rest =>
    simp only [mergePrenex, quantifierDepth]
    rename_i body' _ _ _ ih
    rw [ih, show body' = renameFormulaEquiv _ body from rfl,
        renameFormulaEquiv_quantifierDepth]; omega
  | case3 left y body fresh rest h_not_ex h_not_all h_qd_eq =>
    simp only [mergePrenex, h_qd_eq, ↓reduceIte, quantifierDepth]
    rename_i body' _ _ _ ih
    rw [ih, show body' = renameFormulaEquiv _ body from rfl,
        renameFormulaEquiv_quantifierDepth]; omega
  | case4 left y body fresh rest h_not_ex h_not_all h_qd =>
    simp only [mergePrenex, if_neg h_qd, hop, quantifierDepth]
  | case5 left y body fresh rest h_not_ex h_not_all h_qd_eq =>
    simp only [mergePrenex, h_qd_eq, ↓reduceIte, quantifierDepth]
    rename_i body' _ _ _ ih
    rw [ih, show body' = renameFormulaEquiv _ body from rfl,
        renameFormulaEquiv_quantifierDepth]; omega
  | case6 left y body fresh rest h_not_ex h_not_all h_qd =>
    simp only [mergePrenex, if_neg h_qd, hop, quantifierDepth]
  | case7 => simp only [mergePrenex, hop]

omit [DecidableEq σ] [AtomNeg α] [AtomRename α σ] [AtomVars α σ] in
/-- Combined properties of `toPrenexNNF`:
    1. Preserves quantifier depth
    2. Consumes exactly `freshVarsNeeded Φ` fresh variables
    3. Produces prenex output from NNF input -/
theorem toPrenexNNF_properties [DecidableEq σ] [AtomRename α σ]
    (Φ : Formula σ α) (fv : List σ) (hnnf : IsNNF Φ)
    (hlen : freshVarsNeeded Φ ≤ fv.length) :
    (toPrenexNNF Φ fv).1.quantifierDepth = Φ.quantifierDepth ∧
    (toPrenexNNF Φ fv).2.length + freshVarsNeeded Φ = fv.length ∧
    IsPrenex (toPrenexNNF Φ fv).1 := by
  induction Φ generalizing fv with
  | atom _ => exact ⟨rfl, by simp [toPrenexNNF, freshVarsNeeded], .qf trivial⟩
  | not _ _ => cases hnnf
  | exists_ x Φ ih =>
    have hnnf' : IsNNF Φ := by cases hnnf with | exists_ _ h => exact h
    simp only [toPrenexNNF, freshVarsNeeded] at hlen ⊢
    have ⟨hqd, hsnd, hpre⟩ := ih fv hnnf' hlen
    exact ⟨by simp [quantifierDepth, hqd], hsnd, .exists_ hpre⟩
  | forall_ x Φ ih =>
    have hnnf' : IsNNF Φ := by cases hnnf with | forall_ _ h => exact h
    simp only [toPrenexNNF, freshVarsNeeded] at hlen ⊢
    have ⟨hqd, hsnd, hpre⟩ := ih fv hnnf' hlen
    exact ⟨by simp [quantifierDepth, hqd], hsnd, .forall_ hpre⟩
  | and Φ₁ Φ₂ ih₁ ih₂ =>
    have ⟨hnnf1, hnnf2⟩ : IsNNF Φ₁ ∧ IsNNF Φ₂ := by cases hnnf with | and a b => exact ⟨a, b⟩
    simp only [toPrenexNNF, freshVarsNeeded] at hlen ⊢
    have ⟨hqd₁, hl₁, hp₁⟩ := ih₁ fv hnnf1 (by omega)
    have ⟨hqd₂, hl₂, hp₂⟩ := ih₂ (toPrenexNNF Φ₁ fv).2 hnnf2 (by omega)
    refine ⟨?_, ?_, ?_⟩
    · rw [mergePrenex_fst_quantifierDepth _ (by intros; simp [quantifierDepth]),
          hqd₁, hqd₂]; simp [quantifierDepth]
    · have h₃ := mergePrenex_snd_length .and (toPrenexNNF Φ₁ fv).1
        (toPrenexNNF Φ₂ (toPrenexNNF Φ₁ fv).2).1
        (toPrenexNNF Φ₂ (toPrenexNNF Φ₁ fv).2).2
        (by rw [hqd₁, hqd₂]; omega) hp₁ hp₂
      rw [hqd₁, hqd₂] at h₃; omega
    · exact mergePrenex_isPrenex .and (fun _ _ a b => ⟨a, b⟩) _ _ _
        hp₁ hp₂ (by rw [hqd₁, hqd₂]; omega)
  | or Φ₁ Φ₂ ih₁ ih₂ =>
    have ⟨hnnf1, hnnf2⟩ : IsNNF Φ₁ ∧ IsNNF Φ₂ := by cases hnnf with | or a b => exact ⟨a, b⟩
    simp only [toPrenexNNF, freshVarsNeeded] at hlen ⊢
    have ⟨hqd₁, hl₁, hp₁⟩ := ih₁ fv hnnf1 (by omega)
    have ⟨hqd₂, hl₂, hp₂⟩ := ih₂ (toPrenexNNF Φ₁ fv).2 hnnf2 (by omega)
    refine ⟨?_, ?_, ?_⟩
    · rw [mergePrenex_fst_quantifierDepth _ (by intros; simp [quantifierDepth]),
          hqd₁, hqd₂]; simp [quantifierDepth]
    · have h₃ := mergePrenex_snd_length .or (toPrenexNNF Φ₁ fv).1
        (toPrenexNNF Φ₂ (toPrenexNNF Φ₁ fv).2).1
        (toPrenexNNF Φ₂ (toPrenexNNF Φ₁ fv).2).2
        (by rw [hqd₁, hqd₂]; omega) hp₁ hp₂
      rw [hqd₁, hqd₂] at h₃; omega
    · exact mergePrenex_isPrenex .or (fun _ _ a b => ⟨a, b⟩) _ _ _
        hp₁ hp₂ (by rw [hqd₁, hqd₂]; omega)
  | implies _ _ _ _ => cases hnnf

omit [DecidableEq σ] [AtomNeg α] [AtomRename α σ] [AtomVars α σ] in
/-- `toPrenexNNF` produces prenex formulas from NNF inputs. -/
theorem toPrenexNNF_isPrenex [DecidableEq σ] [AtomRename α σ]
    (Φ : Formula σ α) (fv : List σ) (hnnf : IsNNF Φ)
    (hlen : freshVarsNeeded Φ ≤ fv.length) :
    IsPrenex (toPrenexNNF Φ fv).1 :=
  (toPrenexNNF_properties Φ fv hnnf hlen).2.2

omit [DecidableEq σ] [AtomNeg α] [AtomRename α σ] [AtomVars α σ] in
/-- `Formula.rename` preserves `IsNNF`. -/
theorem rename_isNNF {τ : Type*} {β : Type*} (f : σ → τ) (ra : α → β)
    {Φ : Formula σ α} (h : IsNNF Φ) : IsNNF (Φ.rename f ra) := by
  induction h with
  | atom a => exact .atom (ra a)
  | and _ _ ih₁ ih₂ => exact .and ih₁ ih₂
  | or _ _ ih₁ ih₂ => exact .or ih₁ ih₂
  | exists_ x _ ih => exact .exists_ (f x) ih
  | forall_ x _ ih => exact .forall_ (f x) ih

omit [DecidableEq σ] [AtomNeg α] [AtomRename α σ] [AtomVars α σ] in
/-- `Formula.rename` preserves `freshVarsNeeded`. -/
theorem rename_freshVarsNeeded {τ : Type*} {β : Type*} (f : σ → τ) (ra : α → β)
    (Φ : Formula σ α) :
    freshVarsNeeded (Φ.rename f ra) = freshVarsNeeded Φ := by
  induction Φ with
  | atom _ => simp [Formula.rename, freshVarsNeeded]
  | not _ ih => simp [Formula.rename, freshVarsNeeded, ih]
  | exists_ _ _ ih => simp [Formula.rename, freshVarsNeeded, ih]
  | forall_ _ _ ih => simp [Formula.rename, freshVarsNeeded, ih]
  | and _ _ ih₁ ih₂ => simp [Formula.rename, freshVarsNeeded, ih₁, ih₂,
    Formula.rename_quantifierDepth]
  | or _ _ ih₁ ih₂ => simp [Formula.rename, freshVarsNeeded, ih₁, ih₂,
    Formula.rename_quantifierDepth]
  | implies _ _ ih₁ ih₂ => simp [Formula.rename, freshVarsNeeded, ih₁, ih₂]

/-- The full `toPrenex` pipeline produces a prenex formula. -/
theorem toPrenex_isPrenex
    {n : ℕ} {R' : Type*} [Semiring R']
    {ord' : MonomialOrder}
    (Φ : Formula (Fin n) (AzFieldAtom n R' ord')) :
    IsPrenex (toPrenex Φ) := by
  unfold toPrenex
  apply (toPrenexNNF_properties _ _ _ _).2.2
  · exact rename_isNNF _ _ (toNNF_isNNF Φ)
  · rw [rename_freshVarsNeeded]
    simp [freshVars, List.length_map, List.length_finRange]

/-! ### Top-level toPrenex correctness -/

/-- The prenex conversion preserves `azRealization` up to embedding:
    `y ∈ azRealization(toPrenex Φ) ↔ (y ∘ castLE) ∈ azRealization(Φ)` -/
theorem toPrenex_azRealization
    {n : ℕ} {R' : Type*} [CommRing R']
    [NoZeroDivisors R'] [DecidableEq R'] {ord' : MonomialOrder}
    {K : Type*} [Field K] [Algebra R' K]
    (Φ : Formula (Fin n) (AzFieldAtom n R' ord')) :
    azRealization (C := K) (toPrenex Φ) =
      (· ∘ Fin.castLE (Nat.le_add_right n (freshVarsNeeded (toNNF Φ)))) ⁻¹'
        azRealization (C := K) Φ := by
  -- Abbreviations
  set fvn := freshVarsNeeded (toNNF Φ)
  set m := n + fvn
  set h_le : n ≤ m := Nat.le_add_right n fvn
  set nnf := toNNF Φ with hnnf
  set embedded : Formula (Fin m) (AzFieldAtom m R' ord') :=
    nnf.rename (Fin.castLE h_le)
    (AzFieldAtom.renameVarsMonotone (Fin.castLE h_le)
      (fun _ _ hab => hab)) with hemb
  set fv := freshVars m n fvn (le_refl m) with hfv

  -- Step 1: azRealization(toPrenex Φ) = gRealization(toPrenex Φ)
  rw [show toPrenex Φ = (toPrenexNNF embedded fv).1 from rfl]
  rw [← gRealization_eq_azRealization]

  -- Step 2: gRealization((toPrenexNNF embedded fv).1) = gRealization(embedded)
  rw [toPrenexNNF_gRealization embedded fv
    (freshVars_fresh m n fvn (le_refl m) embedded
      (allVarsOf_rename_embed_bound h_le nnf))
    (freshVars_nodup m n fvn (le_refl m))
    (fun e a => azFieldAtom_rename_vars e a)]

  -- Step 3: gRealization(embedded) = azRealization(embedded) = (· ∘ castLE) ⁻¹' azRealization(nnf)
  rw [gRealization_eq_azRealization]
  rw [azRealization_rename (Fin.castLE h_le)
    (Fin.castLE_injective h_le)
    (fun _ _ hab => hab) nnf]

  -- Step 4: azRealization(toNNF Φ) = azRealization(Φ)
  rw [hnnf]
  congr 1
  rw [← gRealization_eq_azRealization, ← gRealization_eq_azRealization,
    toNNF_gRealization]

end Azurite
