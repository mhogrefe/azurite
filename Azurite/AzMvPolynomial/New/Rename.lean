/-
  Renaming variables for `AzMvPolynomialNew` — Fin-indexed core.

  A non-injective `f : Fin n₁ → Fin n₂` may merge exponents, so the
  general pipeline sorts + collapses + filters zero-coefficient results.
  Specializations: `renameInjective` (injective f) and `renameMonotone`
  (strictly monotone f).  Mathlib correspondence lives in the Equiv layer.
-/
import Azurite.AzMvPolynomial.New.Basic
import Azurite.AzMvPolynomial.New.CompareEmbed

namespace Azurite

open MonicMonomialNew MonomialNew MonomialOrder AzMvPolynomialNew

/-! ### Collapsing adjacent duplicates -/

section Collapse

variable {R : Type _} [Semiring R] {n : ℕ} {ord : MonomialOrder}

/-- Process a sorted-descending list of monomials, collapsing adjacent
    monomials with equal monic parts by summing their coefficients. -/
def collapseAuxNew (cur : MonicMonomialNew n ord × R)
    (acc : List (MonicMonomialNew n ord × R))
    (rest : List (MonomialNew n R ord)) : List (MonicMonomialNew n ord × R) :=
  match rest with
  | [] => (cur :: acc).reverse
  | m :: rest' =>
    if m.monic = cur.1 then
      collapseAuxNew (cur.1, cur.2 + m.coeff.val) acc rest'
    else
      collapseAuxNew (m.monic, m.coeff.val) (cur :: acc) rest'
termination_by rest.length

/-- Collapse adjacent monomials with equal monic parts in a sorted list. -/
def collapseMonicsNew (l : List (MonomialNew n R ord)) :
    List (MonicMonomialNew n ord × R) :=
  match l with
  | [] => []
  | m :: rest => collapseAuxNew (m.monic, m.coeff.val) [] rest

theorem pairwise_fst_cons_update_snd_new
    {α β : Type _} {r : α → α → Prop}
    {a : α} {b₁ b₂ : β} {l : List (α × β)}
    (h : ((a, b₁) :: l).Pairwise (fun x y => r x.1 y.1)) :
    ((a, b₂) :: l).Pairwise (fun x y => r x.1 y.1) := by
  rw [List.pairwise_cons] at h ⊢; exact ⟨h.1, h.2⟩

theorem collapseAuxNew_pairwise
    (curM : MonicMonomialNew n ord) (curC : R)
    (acc : List (MonicMonomialNew n ord × R))
    (rest : List (MonomialNew n R ord))
    (hacc_lt : ((curM, curC) :: acc).Pairwise (fun a b => a.1 < b.1))
    (hrest_le : ∀ m ∈ rest, m.monic ≤ curM)
    (hrest_sorted : rest.Pairwise (fun a b => a.monic ≥ b.monic)) :
    (collapseAuxNew (curM, curC) acc rest).Pairwise (fun a b => a.1 > b.1) := by
  induction rest generalizing curM curC acc with
  | nil =>
    simp only [collapseAuxNew]; rwa [List.pairwise_reverse]
  | cons m rest' ih =>
    simp only [collapseAuxNew]
    rw [List.pairwise_cons] at hrest_sorted
    split
    · next heq =>
      exact ih curM (curC + m.coeff.val) acc
        (pairwise_fst_cons_update_snd_new hacc_lt)
        (fun m' hm' => le_trans (hrest_sorted.1 m' hm') (heq ▸ le_refl _))
        hrest_sorted.2
    · next hne =>
      have hlt : m.monic < curM :=
        lt_of_le_of_ne (hrest_le m (List.mem_cons_self ..)) hne
      exact ih m.monic m.coeff.val ((curM, curC) :: acc)
        (by rw [List.pairwise_cons]
            exact ⟨fun p hp => by
              rcases List.mem_cons.mp hp with rfl | hp
              · exact hlt
              · exact lt_trans hlt ((List.pairwise_cons.mp hacc_lt).1 p hp),
              hacc_lt⟩)
        (fun m' hm' => hrest_sorted.1 m' hm')
        hrest_sorted.2

theorem collapseMonicsNew_pairwise_gt
    {l : List (MonomialNew n R ord)}
    (hsorted : l.Pairwise (fun a b => a.monic ≥ b.monic)) :
    (collapseMonicsNew l).Pairwise (fun a b => a.1 > b.1) := by
  match l, hsorted with
  | [], _ => exact List.Pairwise.nil
  | m :: rest, hsorted =>
    rw [List.pairwise_cons] at hsorted
    exact collapseAuxNew_pairwise m.monic m.coeff.val [] rest
      (List.pairwise_singleton ..)
      hsorted.1
      hsorted.2

theorem pairwise_filterMap_gt_new [DecidableEq R]
    {l : List (MonicMonomialNew n ord × R)}
    (hp : l.Pairwise (fun a b => a.1 > b.1)) :
    (l.filterMap (fun p =>
      if h : p.2 = 0 then none else some ⟨⟨p.2, h⟩, p.1⟩)).Pairwise
      (fun (a : MonomialNew n R ord) (b : MonomialNew n R ord) => a.monic > b.monic) :=
  hp.filterMap _ (fun a a' (h : a.1 > a'.1) b hb b' hb' => by
    split at hb <;> split at hb' <;> try contradiction
    have := Option.some_injective _ hb
    have := Option.some_injective _ hb'
    subst_vars
    exact h)

end Collapse

/-! ### The rename function -/

section Rename

variable {R : Type _} [Semiring R]
    {n₁ n₂ : ℕ} {ord ord₂ : MonomialOrder}

/-- Rename the variables of a polynomial via a map `f : Fin n₁ → Fin n₂`.
    Non-injective maps may merge monomials and cancel terms.
    The result is re-sorted under `ord₂`. -/
def AzMvPolynomialNew.rename [DecidableEq R]
    (p : AzMvPolynomialNew n₁ R ord) (f : Fin n₁ → Fin n₂)
    (ord₂ : MonomialOrder := ord) : AzMvPolynomialNew n₂ R ord₂ :=
  let renamed := p.terms.toList.map (fun m => m.rename f ord₂)
  let sorted := renamed.mergeSort monicGeq
  let collapsed := collapseMonicsNew sorted
  let terms := collapsed.filterMap (fun p =>
    if h : p.2 = 0 then none else some ⟨⟨p.2, h⟩, p.1⟩)
  ⟨terms.toArray, by
    rw [List.toList_toArray]
    have hsorted : sorted.Pairwise (fun a b => a.monic ≥ b.monic) :=
      (List.pairwise_mergeSort monicGeq_trans monicGeq_total renamed).imp
        (fun h => (monicGeq_iff_ge _ _).mp h)
    exact pairwise_filterMap_gt_new (collapseMonicsNew_pairwise_gt hsorted)⟩

/-! ### Injective rename -/

/-- `MonicMonomialNew.rename` is injective when `f : Fin n₁ → Fin n₂` is
    injective: distinct source exponent vectors remain distinct after
    renaming because each `j = f i` picks out exactly one source index. -/
theorem MonicMonomialNew.rename_injective
    (f : Fin n₁ → Fin n₂) (hf : Function.Injective f) (ord₂ : MonomialOrder) :
    Function.Injective (fun m : MonicMonomialNew n₁ ord => m.rename f ord₂) := by
  intro a b hab
  apply MonicMonomialNew.ext
  apply Vector.ext
  intro idx hidx
  let i : Fin n₁ := ⟨idx, hidx⟩
  have h := congrArg (fun m : MonicMonomialNew n₂ ord₂ => m.exponents[(f i).val]'(f i).isLt) hab
  simp only [MonicMonomialNew.rename, Vector.getElem_ofFn] at h
  have hfilter : ∀ v : MonicMonomialNew n₁ ord,
      (Finset.univ.sum (fun i' : Fin n₁ =>
        if f i' = (⟨(f i).val, (f i).isLt⟩ : Fin n₂) then v.exponents[i'] else 0)) =
          v.exponents[i] := by
    intro v
    have hfeq : (⟨(f i).val, (f i).isLt⟩ : Fin n₂) = f i := Fin.ext rfl
    rw [hfeq, Finset.sum_eq_single i]
    · simp
    · intro b _ hbi
      have : f b ≠ f i := fun heq => hbi (hf heq)
      simp [this]
    · intro hnot; exact absurd (Finset.mem_univ i) hnot
  rw [hfilter a, hfilter b] at h
  exact h

private theorem pairwise_gt_of_ge_monic_nodup_new
    {l : List (MonomialNew n₂ R ord₂)}
    (hge : l.Pairwise (fun a b => a.monic ≥ b.monic))
    (hnd : (l.map MonomialNew.monic).Nodup) :
    l.Pairwise (fun a b => a.monic > b.monic) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a t ih =>
    rw [List.pairwise_cons] at hge ⊢
    rw [List.map_cons, List.nodup_cons] at hnd
    exact ⟨fun b hb => lt_of_le_of_ne (hge.1 b hb) (fun heq =>
      hnd.1 (List.mem_map.mpr ⟨b, hb, heq⟩)),
      ih hge.2 hnd.2⟩

/-- Rename variables using an injective map `f : Fin n₁ → Fin n₂`.
    Since `f` is injective, no two distinct monic monomials merge, so
    only sort-by-new-ordering is required (no collapse or filter). -/
def AzMvPolynomialNew.renameInjective
    (p : AzMvPolynomialNew n₁ R ord) (f : Fin n₁ → Fin n₂)
    (hf : Function.Injective f) (ord₂ : MonomialOrder := ord) :
    AzMvPolynomialNew n₂ R ord₂ :=
  let renamed := p.terms.toList.map (fun m => m.rename f ord₂)
  let sorted := renamed.mergeSort monicGeq
  ⟨sorted.toArray, by
    rw [List.toList_toArray]
    have hge : sorted.Pairwise (fun a b => a.monic ≥ b.monic) :=
      (List.pairwise_mergeSort monicGeq_trans monicGeq_total renamed).imp
        (fun h => (monicGeq_iff_ge _ _).mp h)
    have horig_monic_nodup : (p.terms.toList.map MonomialNew.monic).Nodup :=
      List.pairwise_map.mpr (p.sorted.imp (fun h => ne_of_gt h))
    have hrenamed_monic_nodup : (renamed.map MonomialNew.monic).Nodup := by
      simp only [renamed, List.map_map, Function.comp_def, MonomialNew.rename]
      rw [show (fun m : MonomialNew n₁ R ord => m.monic.rename f ord₂) =
            ((fun m => m.rename f ord₂) ∘ MonomialNew.monic) from rfl, ← List.map_map]
      exact horig_monic_nodup.map (MonicMonomialNew.rename_injective f hf ord₂)
    have hsorted_monic_nodup : (sorted.map MonomialNew.monic).Nodup :=
      ((List.mergeSort_perm _ monicGeq).map MonomialNew.monic).nodup_iff.mpr
        hrenamed_monic_nodup
    exact pairwise_gt_of_ge_monic_nodup_new hge hsorted_monic_nodup⟩

/-- Rename variables using a strictly-monotone map `f : Fin n₁ → Fin n₂`.
    Since `f` preserves order, the renamed monomials are already in the
    correct descending order — no sort, collapse or filter needed. -/
def AzMvPolynomialNew.renameMonotone
    (p : AzMvPolynomialNew n₁ R ord) (f : Fin n₁ → Fin n₂)
    (hg : StrictMono f) : AzMvPolynomialNew n₂ R ord :=
  let renamed := p.terms.toList.map (fun m => m.rename f ord)
  ⟨renamed.toArray, by
    rw [List.toList_toArray]
    exact List.pairwise_map.mpr (p.sorted.imp (fun h =>
      MonicMonomialNew.rename_strictMono (ord := ord) f hg h))⟩

/-- Embed a polynomial from `n₁` variables into `n₂` variables, where
    `n₁ ≤ n₂`, by padding with zero exponents.  Uses `Fin.castLE`, which is
    strictly monotone, so no sorting is required. -/
def AzMvPolynomialNew.embed
    (h : n₁ ≤ n₂) (p : AzMvPolynomialNew n₁ R ord) : AzMvPolynomialNew n₂ R ord :=
  p.renameMonotone (Fin.castLE h) (fun _ _ hab => hab)

end Rename

end Azurite
