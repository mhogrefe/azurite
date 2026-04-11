/-
  Round-trip proof: `parseWith F (toCharsWith F m) = some m`
  for `MonicMonomial n ord`, parameterized over a display type `F`
  with `[ParsableVar F n]`.
-/
import Azurite.AzMvPolynomial.MonicMonomial
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Azurite
open AzPolynomial
namespace MonicMonomial

variable {n : ℕ} {ord : MonomialOrder}
variable (F : Type _) [LinearOrder F] [pv : ParsableVar F n]

/-! ### Definitions -/

/-- Recursive factor-list builder for indices `k, k+1, ..., n-1`. -/
private def toCharsAuxWith (m : MonicMonomial n ord) (k : ℕ) : List (List Char) :=
  if h : k < n then
    if m.exponents[k]'h = 0 then toCharsAuxWith m (k + 1)
    else if m.exponents[k]'h = 1 then
      pv.toChars (pv.ofFin ⟨k, h⟩) :: toCharsAuxWith m (k + 1)
    else
      (pv.toChars (pv.ofFin ⟨k, h⟩) ++ '^' :: natToChars (m.exponents[k]'h)) ::
        toCharsAuxWith m (k + 1)
  else []
termination_by n - k

/-- The factor function used in `toCharsWith`, extracted for the
    `filterMap` connection. -/
private def mkFactorWith (m : MonicMonomial n ord) (i : Fin n) : Option (List Char) :=
  if m.exponents[i] = 0 then none
  else if m.exponents[i] = 1 then some (pv.toChars (pv.ofFin i))
  else some (pv.toChars (pv.ofFin i) ++ '^' :: natToChars m.exponents[i])

/-! ### Single-factor lemmas -/

private theorem parseFactorWith_exp1 (i : Fin n) (exps : Vector ℕ n) (h0 : exps.get i = 0) :
    parseFactorWith (n := n) F (pv.toChars (pv.ofFin i)) exps =
      some (exps.set i.val 1 i.isLt) := by
  unfold parseFactorWith
  have hne : (pv.toChars (pv.ofFin i)).isEmpty = false := by
    rcases hn : pv.toChars (pv.ofFin i) with _ | ⟨_, _⟩
    · exact absurd hn (pv.toChars_nonempty _)
    · rfl
  simp only [hne, Bool.false_eq_true, ↓reduceIte]
  have hnc : '^' ∉ pv.toChars (pv.ofFin i) :=
    fun h => pv.toChars_no_syntax _ '^' h (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  rw [show (pv.toChars (pv.ofFin i)).splitOn '^' = [pv.toChars (pv.ofFin i)] from by
    conv_lhs => rw [← show ['^'].intercalate [pv.toChars (pv.ofFin i)] =
        pv.toChars (pv.ofFin i) from by simp [List.intercalate]]
    exact List.splitOn_intercalate _ (by simp [hnc]) (by simp)]
  simp [pv.parse_toChars, pv.toFin_ofFin, h0]

private theorem parseFactorWith_expN (i : Fin n) (e : ℕ) (he : e ≥ 2)
    (exps : Vector ℕ n) (h0 : exps.get i = 0) :
    parseFactorWith (n := n) F (pv.toChars (pv.ofFin i) ++ '^' :: natToChars e) exps =
      some (exps.set i.val e i.isLt) := by
  unfold parseFactorWith
  have hne : (pv.toChars (pv.ofFin i) ++ '^' :: natToChars e).isEmpty = false := by
    cases pv.toChars (pv.ofFin i) <;> simp
  simp only [hne, Bool.false_eq_true, ↓reduceIte]
  rw [show (pv.toChars (pv.ofFin i) ++ '^' :: natToChars e).splitOn '^' =
      [pv.toChars (pv.ofFin i), natToChars e] from by
    conv_lhs => rw [← show ['^'].intercalate [pv.toChars (pv.ofFin i), natToChars e] =
        pv.toChars (pv.ofFin i) ++ '^' :: natToChars e from by
      simp [List.intercalate, List.intersperse]]
    exact List.splitOn_intercalate _
      (by intro l hl; simp at hl; rcases hl with rfl | rfl
          · exact fun h => pv.toChars_no_syntax _ '^' h (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
          · exact not_mem_natToChars_of_not_digit '^' (by decide) _) (by simp)]
  simp only [parseNatChars_natToChars, show ¬(e = 0) from by omega, ↓reduceIte,
    pv.parse_toChars, pv.toFin_ofFin, h0, ne_eq, not_true_eq_false]

/-! ### Main loop proof -/

/-- Processing `toCharsAuxWith F m k` through `parseFactorListWith F` reconstructs
    `m.exponents`, given that `exps` agrees with `m` below index `k` and is zero above. -/
private theorem parseFactorListWith_toCharsAuxWith
    (m : MonicMonomial n ord) (k : ℕ) (hk : k ≤ n) (exps : Vector ℕ n)
    (hlow : ∀ j, (hj : j < n) → j < k → exps[j]'hj = m.exponents[j]'hj)
    (hhigh : ∀ j, (hj : j < n) → j ≥ k → exps[j]'hj = 0) :
    parseFactorListWith (n := n) F (toCharsAuxWith F m k) exps = some m.exponents := by
  by_cases hkn : k < n
  · rw [toCharsAuxWith, dif_pos hkn]
    have h0 : exps.get ⟨k, hkn⟩ = 0 := hhigh k hkn (by omega)
    by_cases he : m.exponents[k]'hkn = 0
    · rw [if_pos he]
      exact parseFactorListWith_toCharsAuxWith m (k + 1) (by omega) exps
        (fun j hj hjk => by
          by_cases hjk' : j < k
          · exact hlow j hj hjk'
          · have hjk'' : j = k := by omega
            subst hjk''
            rw [hhigh j hj (by omega)]; exact he.symm)
        (fun j hj hjk => hhigh j hj (by omega))
    · rw [if_neg he]
      by_cases he1 : m.exponents[k]'hkn = 1
      · rw [if_pos he1, parseFactorListWith, parseFactorWith_exp1 F ⟨k, hkn⟩ exps h0]
        exact parseFactorListWith_toCharsAuxWith m (k + 1) (by omega) _
          (fun j hj hjk => by
            by_cases hjk' : j < k
            · rw [Vector.getElem_set_ne hkn hj (show k ≠ j by omega)]
              exact hlow j hj hjk'
            · have hjk'' : j = k := by omega
              subst hjk''
              simp only [Vector.getElem_set (hi := hkn) (hj := hj), ↓reduceIte, he1])
          (fun j hj hjk => by
            rw [Vector.getElem_set_ne hkn hj (show k ≠ j by omega)]
            exact hhigh j hj (by omega))
      · rw [if_neg he1, parseFactorListWith, parseFactorWith_expN F ⟨k, hkn⟩ _ (by omega) exps h0]
        exact parseFactorListWith_toCharsAuxWith m (k + 1) (by omega) _
          (fun j hj hjk => by
            by_cases hjk' : j < k
            · rw [Vector.getElem_set_ne hkn hj (show k ≠ j by omega)]
              exact hlow j hj hjk'
            · have hjk'' : j = k := by omega
              subst hjk''
              simp only [Vector.getElem_set (hi := hkn) (hj := hj), ↓reduceIte])
          (fun j hj hjk => by
            rw [Vector.getElem_set_ne hkn hj (show k ≠ j by omega)]
            exact hhigh j hj (by omega))
  · rw [toCharsAuxWith, dif_neg hkn]; simp only [parseFactorListWith]
    congr 1; exact Vector.ext (fun j hj => hlow j hj (by omega))
termination_by n - k

/-! ### Connection: toCharsAuxWith ↔ toCharsWith -/

private theorem toCharsAuxWith_eq (m : MonicMonomial n ord) (k : ℕ) (hk : k ≤ n) :
    toCharsAuxWith F m k = ((List.finRange n).drop k).filterMap (mkFactorWith F m) := by
  by_cases hkn : k < n
  · rw [toCharsAuxWith, dif_pos hkn,
      List.drop_eq_getElem_cons (show k < (List.finRange n).length by simp; exact hkn),
      List.filterMap_cons]
    simp only [List.getElem_finRange, Fin.cast_mk]
    by_cases he : m.exponents[k]'hkn = 0
    · have hmk : mkFactorWith F m ⟨k, hkn⟩ = none := by simp [mkFactorWith, he]
      rw [if_pos he, hmk]; dsimp; exact toCharsAuxWith_eq m (k + 1) (by omega)
    · rw [if_neg he]; by_cases he1 : m.exponents[k]'hkn = 1
      · have hmk : mkFactorWith F m ⟨k, hkn⟩ = some (pv.toChars (pv.ofFin ⟨k, hkn⟩)) := by
          simp [mkFactorWith, he1]
        rw [if_pos he1, hmk]; dsimp; congr 1; exact toCharsAuxWith_eq m (k + 1) (by omega)
      · have hmk : mkFactorWith F m ⟨k, hkn⟩ =
            some (pv.toChars (pv.ofFin ⟨k, hkn⟩) ++ '^' :: natToChars (m.exponents[k]'hkn)) := by
          simp [mkFactorWith, he, he1]
        rw [if_neg he1, hmk]; dsimp; congr 1; exact toCharsAuxWith_eq m (k + 1) (by omega)
  · rw [toCharsAuxWith, dif_neg hkn, List.drop_eq_nil_of_le (by simp; omega)]; simp
termination_by n - k

private theorem toCharsWith_eq_intercalate (m : MonicMonomial n ord) :
    m.toCharsWith F = List.intercalate ['*'] (toCharsAuxWith F m 0) := by
  rw [toCharsAuxWith_eq F m 0 (by omega), List.drop_zero]
  simp only [toCharsWith]; congr 1

/-- No factor in `toCharsAuxWith` contains `'*'`. -/
private theorem star_notin_toCharsAuxWith (m : MonicMonomial n ord) (k : ℕ) (_hk : k ≤ n) :
    ∀ factor ∈ toCharsAuxWith F m k, '*' ∉ factor := by
  by_cases hkn : k < n
  · rw [toCharsAuxWith, dif_pos hkn]
    by_cases he : m.exponents[k]'hkn = 0
    · rw [if_pos he]; exact star_notin_toCharsAuxWith m (k + 1) (by omega)
    · rw [if_neg he]; by_cases he1 : m.exponents[k]'hkn = 1
      · rw [if_pos he1]; intro f hf; simp at hf; rcases hf with rfl | hf
        · exact fun h => pv.toChars_no_syntax _ '*' h (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
        · exact star_notin_toCharsAuxWith m (k + 1) (by omega) f hf
      · rw [if_neg he1]; intro f hf; simp at hf; rcases hf with rfl | hf
        · intro h
          rcases List.mem_append.mp h with h | h
          · exact pv.toChars_no_syntax _ '*' h (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
          · cases List.mem_cons.mp h with
            | inl h => exact absurd h (by decide)
            | inr h => exact absurd h (not_mem_natToChars_of_not_digit '*' (by decide) _)
        · exact star_notin_toCharsAuxWith m (k + 1) (by omega) f hf
  · rw [toCharsAuxWith, dif_neg hkn]; intro _ h; simp at h
termination_by n - k

private theorem toCharsAuxWith_nil_of_zero (m : MonicMonomial n ord) (k : ℕ) (_hk : k ≤ n)
    (hall : ∀ j, (hj : j < n) → j ≥ k → m.exponents[j]'hj = 0) :
    toCharsAuxWith F m k = [] := by
  by_cases hkn : k < n
  · rw [toCharsAuxWith, dif_pos hkn, if_pos (hall k hkn (by omega))]
    exact toCharsAuxWith_nil_of_zero m (k + 1) (by omega) (fun j hj hjk => hall j hj (by omega))
  · rw [toCharsAuxWith, dif_neg hkn]
termination_by n - k

private theorem toCharsAuxWith_nil_imp (m : MonicMonomial n ord) (k : ℕ) (hk : k ≤ n) :
    toCharsAuxWith F m k = [] → ∀ j, (hj : j < n) → j ≥ k → m.exponents[j]'hj = 0 := by
  by_cases hkn : k < n
  · rw [toCharsAuxWith, dif_pos hkn]
    by_cases he : m.exponents[k]'hkn = 0
    · rw [if_pos he]; intro h j hj hjk
      by_cases hjk' : j = k
      · subst hjk'; exact he
      · exact toCharsAuxWith_nil_imp m (k + 1) (by omega) h j hj (by omega)
    · rw [if_neg he]; by_cases he1 : m.exponents[k]'hkn = 1
      · rw [if_pos he1]; intro h; simp at h
      · rw [if_neg he1]; intro h; simp at h
  · rw [toCharsAuxWith, dif_neg hkn]; intro _ j hj hjk; omega
termination_by n - k

private theorem toCharsAuxWith_factors_nonempty (m : MonicMonomial n ord) (k : ℕ) (_hk : k ≤ n) :
    ∀ f ∈ toCharsAuxWith F m k, f ≠ [] := by
  by_cases hkn : k < n
  · rw [toCharsAuxWith, dif_pos hkn]
    by_cases he : m.exponents[k]'hkn = 0
    · rw [if_pos he]; exact toCharsAuxWith_factors_nonempty m (k + 1) (by omega)
    · rw [if_neg he]; by_cases he1 : m.exponents[k]'hkn = 1
      · rw [if_pos he1]; intro f hf; simp at hf; rcases hf with rfl | hf
        · exact pv.toChars_nonempty _
        · exact toCharsAuxWith_factors_nonempty m (k + 1) (by omega) f hf
      · rw [if_neg he1]; intro f hf; simp at hf; rcases hf with rfl | hf
        · intro h; cases hl : pv.toChars (pv.ofFin ⟨k, hkn⟩) with
          | nil => exact absurd hl (pv.toChars_nonempty _)
          | cons => simp at h
        · exact toCharsAuxWith_factors_nonempty m (k + 1) (by omega) f hf
  · rw [toCharsAuxWith, dif_neg hkn]; intro _ h; simp at h
termination_by n - k

/-! ### Nonemptiness of `toCharsWith` -/

theorem toCharsWith_ne_nil (m : MonicMonomial n ord) (hm : m ≠ 1) :
    m.toCharsWith F ≠ [] := by
  have hem : m.exponents ≠ Vector.replicate n 0 := by
    intro he; exact hm (MonicMonomial.ext he)
  have haux_ne : toCharsAuxWith F m 0 ≠ [] := by
    intro h
    exact hem (Vector.ext (fun j hj => by
      rw [toCharsAuxWith_nil_imp F m 0 (by omega) h j hj (by omega)]
      simp [Vector.getElem_replicate]))
  rw [toCharsWith_eq_intercalate]; intro h
  cases hL : toCharsAuxWith F m 0 with
  | nil => exact haux_ne hL
  | cons hd tl =>
    have hhd : hd ≠ [] := toCharsAuxWith_factors_nonempty F m 0 (by omega) hd (by rw [hL]; simp)
    rw [hL] at h; simp [List.intercalate] at h
    have hmem : hd ∈ List.intersperse ['*'] (hd :: tl) := by
      cases tl with | nil => simp [List.intersperse] | cons => simp [List.intersperse]
    exact hhd (h _ hmem)

private theorem toCharsAuxWith_factors_head_not_syntax (m : MonicMonomial n ord) (k : ℕ) :
    ∀ f ∈ toCharsAuxWith F m k, ∀ hf : f ≠ [], ¬ Azurite.isPolySyntaxChar (f.head hf) := by
  by_cases hkn : k < n
  · rw [toCharsAuxWith, dif_pos hkn]
    by_cases he : m.exponents[k]'hkn = 0
    · rw [if_pos he]; exact toCharsAuxWith_factors_head_not_syntax m (k + 1)
    · rw [if_neg he]; by_cases he1 : m.exponents[k]'hkn = 1
      · rw [if_pos he1]; intro f hf hfne
        simp only [List.mem_cons] at hf
        rcases hf with rfl | hf
        · exact pv.toChars_no_syntax _ _ (List.head_mem hfne)
        · exact toCharsAuxWith_factors_head_not_syntax m (k + 1) f hf hfne
      · rw [if_neg he1]; intro f hf hfne
        simp only [List.mem_cons] at hf
        rcases hf with rfl | hf
        · have hne' := pv.toChars_nonempty (pv.ofFin ⟨k, hkn⟩)
          rw [List.head_append_of_ne_nil hne']
          exact pv.toChars_no_syntax _ _ (List.head_mem hne')
        · exact toCharsAuxWith_factors_head_not_syntax m (k + 1) f hf hfne
  · rw [toCharsAuxWith, dif_neg hkn]; intro _ h; simp at h
termination_by n - k

theorem toCharsWith_head_not_syntax (m : MonicMonomial n ord) (hm : m ≠ 1) :
    ¬ Azurite.isPolySyntaxChar ((m.toCharsWith F).head (toCharsWith_ne_nil F m hm)) := by
  have hem : m.exponents ≠ Vector.replicate n 0 :=
    fun he => hm (MonicMonomial.ext he)
  have haux_ne : toCharsAuxWith F m 0 ≠ [] := fun h =>
    hem (Vector.ext (fun j hj => by
      rw [toCharsAuxWith_nil_imp F m 0 (by omega) h j hj (by omega)]
      simp [Vector.getElem_replicate]))
  have heq : m.toCharsWith F = List.intercalate ['*'] (toCharsAuxWith F m 0) :=
    toCharsWith_eq_intercalate F m
  obtain ⟨first, rest, hfr⟩ := List.exists_cons_of_ne_nil haux_ne
  have hfne : first ≠ [] :=
    toCharsAuxWith_factors_nonempty F m 0 (by omega) first (by rw [hfr]; simp)
  have hhl := toCharsAuxWith_factors_head_not_syntax F m 0 first (by rw [hfr]; simp) hfne
  have h_prefix : ∃ suffix, m.toCharsWith F = first ++ suffix := by
    rw [heq, hfr, List.intercalate]
    cases rest with
    | nil => exact ⟨[], by simp [List.intersperse, List.flatten]⟩
    | cons r rs =>
      exact ⟨['*'] ++ (List.intersperse ['*'] (r :: rs)).flatten, by
        simp [List.intersperse, List.flatten]⟩
  obtain ⟨suffix, hsuf⟩ := h_prefix
  have hne' : first ++ suffix ≠ [] := by rw [← hsuf]; exact toCharsWith_ne_nil F m hm
  have : (m.toCharsWith F).head (toCharsWith_ne_nil F m hm) = (first ++ suffix).head hne' := by
    congr 1
  rw [this, List.head_append_of_ne_nil hfne]
  exact hhl

/-! ### Exclusion of `+` and `-` from `toCharsWith` -/

private lemma mem_intersperse_of_list {sep : List α} {L : List (List α)} {s : List α}
    (hs : s ∈ List.intersperse sep L) : s ∈ L ∨ s = sep := by
  induction L with
  | nil => simp [List.intersperse] at hs
  | cons hd tl ih =>
    match tl with
    | [] => simp [List.intersperse] at hs; left; simp [hs]
    | b :: bs =>
      unfold List.intersperse at hs
      simp only [List.mem_cons] at hs
      rcases hs with rfl | rfl | hs
      · left; simp
      · right; rfl
      · rcases ih hs with h | h
        · left; simp [h]
        · right; exact h

private lemma not_mem_intercalate {c : α} [BEq α] {sep : List α} {parts : List (List α)}
    (hc_sep : c ∉ sep) (hc_parts : ∀ p ∈ parts, c ∉ p) :
    c ∉ List.intercalate sep parts := by
  simp only [List.intercalate]
  intro hmem; rw [List.mem_flatten] at hmem
  obtain ⟨s, hs, hcs⟩ := hmem
  rcases mem_intersperse_of_list hs with h | h
  · exact hc_parts s h hcs
  · exact hc_sep (h ▸ hcs)

private theorem plus_minus_notin_toCharsAuxWith (m : MonicMonomial n ord) (k : ℕ) (_hk : k ≤ n) :
    ∀ factor ∈ toCharsAuxWith F m k, '+' ∉ factor ∧ '-' ∉ factor := by
  by_cases hkn : k < n
  · rw [toCharsAuxWith, dif_pos hkn]
    by_cases he : m.exponents[k]'hkn = 0
    · rw [if_pos he]; exact plus_minus_notin_toCharsAuxWith m (k + 1) (by omega)
    · rw [if_neg he]; by_cases he1 : m.exponents[k]'hkn = 1
      · rw [if_pos he1]; intro f hf; simp at hf; rcases hf with rfl | hf
        · exact ⟨fun h => pv.toChars_no_syntax _ '+' h (Or.inr (Or.inl rfl)),
                 fun h => pv.toChars_no_syntax _ '-' h (Or.inr (Or.inr (Or.inl rfl)))⟩
        · exact plus_minus_notin_toCharsAuxWith m (k + 1) (by omega) f hf
      · rw [if_neg he1]; intro f hf; simp at hf; rcases hf with rfl | hf
        · constructor
          · intro h; rcases List.mem_append.mp h with h | h
            · exact pv.toChars_no_syntax _ '+' h (Or.inr (Or.inl rfl))
            · cases List.mem_cons.mp h with
              | inl h => exact absurd h (by decide)
              | inr h => exact absurd h (not_mem_natToChars_of_not_digit '+' (by decide) _)
          · intro h; rcases List.mem_append.mp h with h | h
            · exact pv.toChars_no_syntax _ '-' h (Or.inr (Or.inr (Or.inl rfl)))
            · cases List.mem_cons.mp h with
              | inl h => exact absurd h (by decide)
              | inr h => exact absurd h (not_mem_natToChars_of_not_digit '-' (by decide) _)
        · exact plus_minus_notin_toCharsAuxWith m (k + 1) (by omega) f hf
  · rw [toCharsAuxWith, dif_neg hkn]; intro _ h; simp at h
termination_by n - k

theorem plus_notin_toCharsWith (m : MonicMonomial n ord) : '+' ∉ m.toCharsWith F := by
  rw [toCharsWith_eq_intercalate]
  exact not_mem_intercalate (by simp)
    (fun p hp => (plus_minus_notin_toCharsAuxWith F m 0 (by omega) p hp).1)

theorem minus_notin_toCharsWith (m : MonicMonomial n ord) : '-' ∉ m.toCharsWith F := by
  rw [toCharsWith_eq_intercalate]
  exact not_mem_intercalate (by simp)
    (fun p hp => (plus_minus_notin_toCharsAuxWith F m 0 (by omega) p hp).2)

/-! ### Final round-trip theorem -/

theorem parseWith_toCharsWith (m : MonicMonomial n ord) :
    parseWith (n := n) F (m.toCharsWith F) = some m := by
  unfold parseWith
  by_cases hem : m.exponents = Vector.replicate n 0
  · have hnil : m.toCharsWith F = [] := by
      show _ = List.intercalate ['*'] []
      rw [toCharsWith_eq_intercalate,
        toCharsAuxWith_nil_of_zero F m 0 (by omega)
          (fun j hj _ => by rw [hem]; simp [Vector.getElem_replicate])]
    simp [hnil]; ext i hi; simp; rw [hem]; simp [Vector.getElem_replicate]
  · have haux_ne : toCharsAuxWith F m 0 ≠ [] := by
      intro h
      have hall := toCharsAuxWith_nil_imp F m 0 (by omega) h
      exact hem (Vector.ext (fun j hj => by
        rw [hall j hj (by omega)]; simp [Vector.getElem_replicate]))
    have hemp : m.toCharsWith F ≠ [] := by
      rw [toCharsWith_eq_intercalate]; intro h
      cases hL : toCharsAuxWith F m 0 with
      | nil => exact haux_ne hL
      | cons hd tl =>
        have hhd : hd ≠ [] := toCharsAuxWith_factors_nonempty F m 0 (by omega) hd (by rw [hL]; simp)
        rw [hL] at h; simp [List.intercalate] at h
        have hmem : hd ∈ List.intersperse ['*'] (hd :: tl) := by
          cases tl with | nil => simp [List.intersperse] | cons => simp [List.intersperse]
        exact hhd (h _ hmem)
    have hne : ¬(m.toCharsWith F).isEmpty := by simp [List.isEmpty_iff]; exact hemp
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    rw [toCharsWith_eq_intercalate, List.splitOn_intercalate _
      (star_notin_toCharsAuxWith F m 0 (by omega)) haux_ne]
    rw [parseFactorListWith_toCharsAuxWith F m 0 (by omega) _
      (fun _ _ h => by omega) (fun j hj _ => by simp [Vector.getElem_replicate])]

/-! ### Default-display corollaries (`F := IndexedVar n`) -/

theorem toChars_ne_nil (m : MonicMonomial n ord) (hm : m ≠ 1) : m.toChars ≠ [] :=
  toCharsWith_ne_nil (IndexedVar n) m hm

theorem toChars_head_not_syntax (m : MonicMonomial n ord) (hm : m ≠ 1) :
    ¬ Azurite.isPolySyntaxChar (m.toChars.head (toChars_ne_nil m hm)) :=
  toCharsWith_head_not_syntax (IndexedVar n) m hm

theorem plus_notin_toChars (m : MonicMonomial n ord) : '+' ∉ m.toChars :=
  plus_notin_toCharsWith (IndexedVar n) m

theorem minus_notin_toChars (m : MonicMonomial n ord) : '-' ∉ m.toChars :=
  minus_notin_toCharsWith (IndexedVar n) m

theorem parse_toChars (m : MonicMonomial n ord) :
    parse (n := n) (m.toChars) = some m :=
  parseWith_toCharsWith (IndexedVar n) m

/-! ### eval / rename / mul lemmas -/

theorem eval_rename {n₂ : ℕ} {R : Type _} [CommMonoid R]
    (m : MonicMonomial n ord) (f : Fin n → Fin n₂) (g : Fin n₂ → R)
    (ord₂ : MonomialOrder) :
    (m.rename f ord₂).eval g = m.eval (g ∘ f) := by
  simp only [eval, rename, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, Function.comp]
  conv_lhs => arg 2; ext j; rw [← Finset.prod_pow_eq_pow_sum]
  simp_rw [pow_ite, pow_zero]
  rw [Finset.prod_comm]
  congr 1; ext i
  rw [Finset.prod_ite_eq Finset.univ (f i)]
  simp

theorem eval_mul {R : Type _} [CommMonoid R]
    (a b : MonicMonomial n ord) (f : Fin n → R) :
    (a * b).eval f = a.eval f * b.eval f := by
  simp only [eval, mul_exponents, Fin.getElem_fin, Vector.getElem_ofFn, pow_add]
  exact Finset.prod_mul_distrib

end MonicMonomial

end Azurite
