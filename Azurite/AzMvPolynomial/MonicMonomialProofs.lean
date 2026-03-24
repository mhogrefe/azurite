/-
  Round-trip proof: parse (toChars m) = some m for MonicMonomial.

  Strategy:
  1. `parseFactor` and `parseFactorList` are defined in MonicMonomial.lean.
  2. Define `toCharsAux` (recursive factor-list builder matching `toChars`).
  3. Prove single-factor correctness: `parseFactor_exp1`, `parseFactor_expN`.
  4. Prove main loop: `parseFactorList_toCharsAux m 0` recovers `m.exponents`.
  5. Connect `toCharsAux` to `toChars` via `filterMap`, then `splitOn_intercalate`.
  6. Assemble the round-trip theorem.
-/
import Azurite.AzMvPolynomial.MonicMonomial
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.SplitOn

namespace Azurite
open AzPolynomial
namespace MonicMonomial

variable {σ : Type _} {n : ℕ} [LinearOrder σ] [pv : ParsableVar σ n] {ord : MonomialOrder}

/-! ### Definitions -/

/-- Recursive factor-list builder for indices `k, k+1, ..., n-1`. -/
private def toCharsAux (m : MonicMonomial σ ord) (k : ℕ) : List (List Char) :=
  if h : k < n then
    if m.exponents[k]'h = 0 then toCharsAux m (k + 1)
    else if m.exponents[k]'h = 1 then
      pv.toChars (pv.ofFin ⟨k, h⟩) :: toCharsAux m (k + 1)
    else
      (pv.toChars (pv.ofFin ⟨k, h⟩) ++ '^' :: natToChars (m.exponents[k]'h)) :: toCharsAux m (k + 1)
  else []
termination_by n - k

/-- The factor function used in `toChars`, extracted for `filterMap` connection. -/
private def mkFactor (m : MonicMonomial σ ord) (i : Fin n) : Option (List Char) :=
  if m.exponents[i] = 0 then none
  else if m.exponents[i] = 1 then some (pv.toChars (pv.ofFin i))
  else some (pv.toChars (pv.ofFin i) ++ '^' :: natToChars m.exponents[i])

/-! ### Single-factor lemmas -/

/-- `parseFactor` correctly handles exp=1 factors. -/
private theorem parseFactor_exp1 (i : Fin n) (exps : Vector ℕ n) (h0 : exps.get i = 0) :
    parseFactor (σ := σ) (pv.toChars (pv.ofFin i)) exps = some (exps.set i.val 1 i.isLt) := by
  unfold parseFactor
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
    exact List.splitOn_intercalate _ _ (by simp [hnc]) (by simp)]
  simp [pv.parse_toChars, pv.toFin_ofFin, h0]

/-- `parseFactor` correctly handles exp≥2 factors. -/
private theorem parseFactor_expN (i : Fin n) (e : ℕ) (he : e ≥ 2)
    (exps : Vector ℕ n) (h0 : exps.get i = 0) :
    parseFactor (σ := σ) (pv.toChars (pv.ofFin i) ++ '^' :: natToChars e) exps =
    some (exps.set i.val e i.isLt) := by
  unfold parseFactor
  have hne : (pv.toChars (pv.ofFin i) ++ '^' :: natToChars e).isEmpty = false := by
    cases pv.toChars (pv.ofFin i) <;> simp
  simp only [hne, Bool.false_eq_true, ↓reduceIte]
  rw [show (pv.toChars (pv.ofFin i) ++ '^' :: natToChars e).splitOn '^' =
      [pv.toChars (pv.ofFin i), natToChars e] from by
    conv_lhs => rw [← show ['^'].intercalate [pv.toChars (pv.ofFin i), natToChars e] =
        pv.toChars (pv.ofFin i) ++ '^' :: natToChars e from by
      simp [List.intercalate, List.intersperse]]
    exact List.splitOn_intercalate _ _
      (by intro l hl; simp at hl; rcases hl with rfl | rfl
          · exact fun h => pv.toChars_no_syntax _ '^' h (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
          · exact not_mem_natToChars_of_not_digit '^' (by decide) _) (by simp)]
  simp only [parseNatChars_natToChars, show ¬(e = 0) from by omega, ↓reduceIte,
    pv.parse_toChars, pv.toFin_ofFin, h0, ne_eq, not_true_eq_false]

/-! ### Main loop proof -/

/-- Processing `toCharsAux m k` through `parseFactorList` reconstructs `m.exponents`,
    given that `exps` already agrees with `m` below index `k` and is zero above. -/
private theorem parseFactorList_toCharsAux
    (m : MonicMonomial σ ord) (k : ℕ) (hk : k ≤ n) (exps : Vector ℕ n)
    (hlow : ∀ j, (hj : j < n) → j < k → exps[j]'hj = m.exponents[j]'hj)
    (hhigh : ∀ j, (hj : j < n) → j ≥ k → exps[j]'hj = 0) :
    parseFactorList (σ := σ) (toCharsAux m k) exps = some m.exponents := by
  by_cases hkn : k < n
  · rw [toCharsAux, dif_pos hkn]
    have h0 : exps.get ⟨k, hkn⟩ = 0 := hhigh k hkn (by omega)
    by_cases he : m.exponents[k]'hkn = 0
    · rw [if_pos he]
      exact parseFactorList_toCharsAux m (k + 1) (by omega) exps
        (fun j hj hjk => by
          by_cases hjk' : j < k
          · exact hlow j hj hjk'
          · have hjk'' : j = k := by omega
            subst hjk''
            rw [hhigh j hj (by omega)]; exact he.symm)
        (fun j hj hjk => hhigh j hj (by omega))
    · rw [if_neg he]
      by_cases he1 : m.exponents[k]'hkn = 1
      · rw [if_pos he1, parseFactorList, parseFactor_exp1 ⟨k, hkn⟩ exps h0]
        exact parseFactorList_toCharsAux m (k + 1) (by omega) _
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
      · rw [if_neg he1, parseFactorList, parseFactor_expN ⟨k, hkn⟩ _ (by omega) exps h0]
        exact parseFactorList_toCharsAux m (k + 1) (by omega) _
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
  · rw [toCharsAux, dif_neg hkn]; simp only [parseFactorList]
    congr 1; exact Vector.ext (fun j hj => hlow j hj (by omega))
termination_by n - k

/-! ### Connection: toCharsAux ↔ toChars -/

/-- `toCharsAux` equals `filterMap mkFactor` on the tail of `finRange n`. -/
private theorem toCharsAux_eq (m : MonicMonomial σ ord) (k : ℕ) (hk : k ≤ n) :
    toCharsAux m k = ((List.finRange n).drop k).filterMap (mkFactor m) := by
  by_cases hkn : k < n
  · rw [toCharsAux, dif_pos hkn,
      List.drop_eq_getElem_cons (show k < (List.finRange n).length by simp; exact hkn),
      List.filterMap_cons]
    simp only [List.getElem_finRange, Fin.cast_mk]
    by_cases he : m.exponents[k]'hkn = 0
    · have hmk : mkFactor m ⟨k, hkn⟩ = none := by simp [mkFactor, he]
      rw [if_pos he, hmk]; dsimp; exact toCharsAux_eq m (k + 1) (by omega)
    · rw [if_neg he]; by_cases he1 : m.exponents[k]'hkn = 1
      · have hmk : mkFactor m ⟨k, hkn⟩ = some (pv.toChars (pv.ofFin ⟨k, hkn⟩)) := by
          simp [mkFactor, he1]
        rw [if_pos he1, hmk]; dsimp; congr 1; exact toCharsAux_eq m (k + 1) (by omega)
      · have hmk : mkFactor m ⟨k, hkn⟩ =
            some (pv.toChars (pv.ofFin ⟨k, hkn⟩) ++ '^' :: natToChars (m.exponents[k]'hkn)) := by
          simp [mkFactor, he, he1]
        rw [if_neg he1, hmk]; dsimp; congr 1; exact toCharsAux_eq m (k + 1) (by omega)
  · rw [toCharsAux, dif_neg hkn, List.drop_eq_nil_of_le (by simp; omega)]; simp
termination_by n - k

/-- `toChars` equals `intercalate` of `toCharsAux`. -/
private theorem toChars_eq_intercalate (m : MonicMonomial σ ord) :
    m.toChars = List.intercalate ['*'] (toCharsAux m 0) := by
  rw [toCharsAux_eq m 0 (by omega), List.drop_zero]
  simp only [toChars]; congr 1

/-- No factor in `toCharsAux` contains `'*'`. -/
private theorem star_notin_toCharsAux (m : MonicMonomial σ ord) (k : ℕ) (_hk : k ≤ n) :
    ∀ factor ∈ toCharsAux m k, '*' ∉ factor := by
  by_cases hkn : k < n
  · rw [toCharsAux, dif_pos hkn]
    by_cases he : m.exponents[k]'hkn = 0
    · rw [if_pos he]; exact star_notin_toCharsAux m (k + 1) (by omega)
    · rw [if_neg he]; by_cases he1 : m.exponents[k]'hkn = 1
      · rw [if_pos he1]; intro f hf; simp at hf; rcases hf with rfl | hf
        · exact fun h => pv.toChars_no_syntax _ '*' h (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
        · exact star_notin_toCharsAux m (k + 1) (by omega) f hf
      · rw [if_neg he1]; intro f hf; simp at hf; rcases hf with rfl | hf
        · intro h
          rcases List.mem_append.mp h with h | h
          · exact pv.toChars_no_syntax _ '*' h (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
          · cases List.mem_cons.mp h with
            | inl h => exact absurd h (by decide)
            | inr h => exact absurd h (not_mem_natToChars_of_not_digit '*' (by decide) _)
        · exact star_notin_toCharsAux m (k + 1) (by omega) f hf
  · rw [toCharsAux, dif_neg hkn]; intro _ h; simp at h
termination_by n - k

/-- If all exponents ≥ k are zero, `toCharsAux m k = []`. -/
private theorem toCharsAux_nil_of_zero (m : MonicMonomial σ ord) (k : ℕ) (_hk : k ≤ n)
    (hall : ∀ j, (hj : j < n) → j ≥ k → m.exponents[j]'hj = 0) :
    toCharsAux m k = [] := by
  by_cases hkn : k < n
  · rw [toCharsAux, dif_pos hkn, if_pos (hall k hkn (by omega))]
    exact toCharsAux_nil_of_zero m (k + 1) (by omega) (fun j hj hjk => hall j hj (by omega))
  · rw [toCharsAux, dif_neg hkn]
termination_by n - k

/-- If `toCharsAux m k = []`, all exponents at index ≥ k are zero. -/
private theorem toCharsAux_nil_imp (m : MonicMonomial σ ord) (k : ℕ) (hk : k ≤ n) :
    toCharsAux m k = [] → ∀ j, (hj : j < n) → j ≥ k → m.exponents[j]'hj = 0 := by
  by_cases hkn : k < n
  · rw [toCharsAux, dif_pos hkn]
    by_cases he : m.exponents[k]'hkn = 0
    · rw [if_pos he]; intro h j hj hjk
      by_cases hjk' : j = k
      · subst hjk'; exact he
      · exact toCharsAux_nil_imp m (k + 1) (by omega) h j hj (by omega)
    · rw [if_neg he]; by_cases he1 : m.exponents[k]'hkn = 1
      · rw [if_pos he1]; intro h; simp at h
      · rw [if_neg he1]; intro h; simp at h
  · rw [toCharsAux, dif_neg hkn]; intro _ j hj hjk; omega
termination_by n - k

/-- Every factor in `toCharsAux` is nonempty (starts with `pv.toChars`). -/
private theorem toCharsAux_factors_nonempty (m : MonicMonomial σ ord) (k : ℕ) (_hk : k ≤ n) :
    ∀ f ∈ toCharsAux m k, f ≠ [] := by
  by_cases hkn : k < n
  · rw [toCharsAux, dif_pos hkn]
    by_cases he : m.exponents[k]'hkn = 0
    · rw [if_pos he]; exact toCharsAux_factors_nonempty m (k + 1) (by omega)
    · rw [if_neg he]; by_cases he1 : m.exponents[k]'hkn = 1
      · rw [if_pos he1]; intro f hf; simp at hf; rcases hf with rfl | hf
        · exact pv.toChars_nonempty _
        · exact toCharsAux_factors_nonempty m (k + 1) (by omega) f hf
      · rw [if_neg he1]; intro f hf; simp at hf; rcases hf with rfl | hf
        · intro h; cases hl : pv.toChars (pv.ofFin ⟨k, hkn⟩) with
          | nil => exact absurd hl (pv.toChars_nonempty _)
          | cons => simp at h
        · exact toCharsAux_factors_nonempty m (k + 1) (by omega) f hf
  · rw [toCharsAux, dif_neg hkn]; intro _ h; simp at h
termination_by n - k

/-! ### Nonemptiness of toChars -/

/-- `toChars` is nonempty when the monomial is not the identity. -/
theorem toChars_ne_nil (m : MonicMonomial σ ord) (hm : m ≠ 1) : m.toChars ≠ [] := by
  have hem : m.exponents ≠ Vector.replicate n 0 := by
    intro he; exact hm (MonicMonomial.ext he)
  have haux_ne : toCharsAux m 0 ≠ [] := by
    intro h
    exact hem (Vector.ext (fun j hj => by
      rw [toCharsAux_nil_imp m 0 (by omega) h j hj (by omega)]
      simp [Vector.getElem_replicate]))
  rw [toChars_eq_intercalate]; intro h
  cases hL : toCharsAux m 0 with
  | nil => exact haux_ne hL
  | cons hd tl =>
    have hhd : hd ≠ [] := toCharsAux_factors_nonempty m 0 (by omega) hd (by rw [hL]; simp)
    rw [hL] at h; simp [List.intercalate] at h
    have hmem : hd ∈ List.intersperse ['*'] (hd :: tl) := by
      cases tl with | nil => simp [List.intersperse] | cons => simp [List.intersperse]
    exact hhd (h _ hmem)

/-- `toString` is nonempty when the monomial is not the identity. -/
theorem toString_ne_empty (m : MonicMonomial σ ord) (hm : m ≠ 1) : toString m ≠ "" := by
  show String.ofList m.toChars ≠ ""
  intro h; apply toChars_ne_nil m hm
  have := congr_arg String.toList h
  simp [String.toList_ofList] at this
  exact this

/-- Every factor in `toCharsAux` starts with a non-poly-syntax character. -/
private theorem toCharsAux_factors_head_not_syntax (m : MonicMonomial σ ord) (k : ℕ) :
    ∀ f ∈ toCharsAux m k, ∀ hf : f ≠ [], ¬ Azurite.isPolySyntaxChar (f.head hf) := by
  by_cases hkn : k < n
  · rw [toCharsAux, dif_pos hkn]
    by_cases he : m.exponents[k]'hkn = 0
    · rw [if_pos he]; exact toCharsAux_factors_head_not_syntax m (k + 1)
    · rw [if_neg he]; by_cases he1 : m.exponents[k]'hkn = 1
      · rw [if_pos he1]; intro f hf hfne
        simp only [List.mem_cons] at hf
        rcases hf with rfl | hf
        · exact pv.toChars_no_syntax _ _ (List.head_mem hfne)
        · exact toCharsAux_factors_head_not_syntax m (k + 1) f hf hfne
      · rw [if_neg he1]; intro f hf hfne
        simp only [List.mem_cons] at hf
        rcases hf with rfl | hf
        · have hne' := pv.toChars_nonempty (pv.ofFin ⟨k, hkn⟩)
          rw [List.head_append_of_ne_nil hne']
          exact pv.toChars_no_syntax _ _ (List.head_mem hne')
        · exact toCharsAux_factors_head_not_syntax m (k + 1) f hf hfne
  · rw [toCharsAux, dif_neg hkn]; intro _ h; simp at h
termination_by n - k

/-- The first character of `toChars` is not a poly-syntax character when `m ≠ 1`. -/
theorem toChars_head_not_syntax (m : MonicMonomial σ ord) (hm : m ≠ 1) :
    ¬ Azurite.isPolySyntaxChar (m.toChars.head (toChars_ne_nil m hm)) := by
  have hem : m.exponents ≠ Vector.replicate n 0 :=
    fun he => hm (MonicMonomial.ext he)
  have haux_ne : toCharsAux m 0 ≠ [] := fun h =>
    hem (Vector.ext (fun j hj => by
      rw [toCharsAux_nil_imp m 0 (by omega) h j hj (by omega)]
      simp [Vector.getElem_replicate]))
  have heq : m.toChars = List.intercalate ['*'] (toCharsAux m 0) := toChars_eq_intercalate m
  obtain ⟨first, rest, hfr⟩ := List.exists_cons_of_ne_nil haux_ne
  have hfne : first ≠ [] :=
    toCharsAux_factors_nonempty m 0 (by omega) first (by rw [hfr]; simp)
  have hhl := toCharsAux_factors_head_not_syntax m 0 first (by rw [hfr]; simp) hfne
  have h_prefix : ∃ suffix, m.toChars = first ++ suffix := by
    rw [heq, hfr, List.intercalate]
    cases rest with
    | nil => exact ⟨[], by simp [List.intersperse, List.flatten]⟩
    | cons r rs =>
      exact ⟨['*'] ++ (List.intersperse ['*'] (r :: rs)).flatten, by
        simp [List.intersperse, List.flatten]⟩
  obtain ⟨suffix, hsuf⟩ := h_prefix
  have hne' : first ++ suffix ≠ [] := by rw [← hsuf]; exact toChars_ne_nil m hm
  have : m.toChars.head (toChars_ne_nil m hm) = (first ++ suffix).head hne' := by
    congr 1
  rw [this, List.head_append_of_ne_nil hfne]
  exact hhl

/-! ### Exclusion of `+` and `-` from toChars -/

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

/-- Neither `+` nor `-` appears in any factor of `toCharsAux`. -/
private theorem plus_minus_notin_toCharsAux (m : MonicMonomial σ ord) (k : ℕ) (_hk : k ≤ n) :
    ∀ factor ∈ toCharsAux m k, '+' ∉ factor ∧ '-' ∉ factor := by
  by_cases hkn : k < n
  · rw [toCharsAux, dif_pos hkn]
    by_cases he : m.exponents[k]'hkn = 0
    · rw [if_pos he]; exact plus_minus_notin_toCharsAux m (k + 1) (by omega)
    · rw [if_neg he]; by_cases he1 : m.exponents[k]'hkn = 1
      · rw [if_pos he1]; intro f hf; simp at hf; rcases hf with rfl | hf
        · exact ⟨fun h => pv.toChars_no_syntax _ '+' h (Or.inr (Or.inl rfl)),
                 fun h => pv.toChars_no_syntax _ '-' h (Or.inr (Or.inr (Or.inl rfl)))⟩
        · exact plus_minus_notin_toCharsAux m (k + 1) (by omega) f hf
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
        · exact plus_minus_notin_toCharsAux m (k + 1) (by omega) f hf
  · rw [toCharsAux, dif_neg hkn]; intro _ h; simp at h
termination_by n - k

/-- `+` does not appear in any `toChars` output. -/
theorem plus_notin_toChars (m : MonicMonomial σ ord) : '+' ∉ m.toChars := by
  rw [toChars_eq_intercalate]
  exact not_mem_intercalate (by simp)
    (fun p hp => (plus_minus_notin_toCharsAux m 0 (by omega) p hp).1)

/-- `-` does not appear in any `toChars` output. -/
theorem minus_notin_toChars (m : MonicMonomial σ ord) : '-' ∉ m.toChars := by
  rw [toChars_eq_intercalate]
  exact not_mem_intercalate (by simp)
    (fun p hp => (plus_minus_notin_toCharsAux m 0 (by omega) p hp).2)

/-! ### Final round-trip theorem -/

/-- Parse-toChars round-trip: `parse` correctly inverts `toChars`. -/
theorem parse_toChars (m : MonicMonomial σ ord) :
    parse (σ := σ) (m.toChars) = some m := by
  unfold parse
  by_cases hem : m.exponents = Vector.replicate n 0
  · -- All exponents are zero: toChars m = []
    have hnil : m.toChars = [] := by
      show _ = List.intercalate ['*'] []
      rw [toChars_eq_intercalate,
        toCharsAux_nil_of_zero m 0 (by omega)
          (fun j hj _ => by rw [hem]; simp [Vector.getElem_replicate])]
    simp [hnil]; ext i hi; simp; rw [hem]; simp [Vector.getElem_replicate]
  · -- Some exponent is nonzero: toCharsAux m 0 ≠ []
    have haux_ne : toCharsAux m 0 ≠ [] := by
      intro h
      have hall := toCharsAux_nil_imp m 0 (by omega) h
      exact hem (Vector.ext (fun j hj => by
        rw [hall j hj (by omega)]; simp [Vector.getElem_replicate]))
    -- toChars m ≠ [] (intercalate of nonempty list with nonempty factors)
    have hemp : m.toChars ≠ [] := by
      rw [toChars_eq_intercalate]; intro h
      cases hL : toCharsAux m 0 with
      | nil => exact haux_ne hL
      | cons hd tl =>
        have hhd : hd ≠ [] := toCharsAux_factors_nonempty m 0 (by omega) hd (by rw [hL]; simp)
        rw [hL] at h; simp [List.intercalate] at h
        have hmem : hd ∈ List.intersperse ['*'] (hd :: tl) := by
          cases tl with | nil => simp [List.intersperse] | cons => simp [List.intersperse]
        exact hhd (h _ hmem)
    have hne : ¬(m.toChars).isEmpty := by simp [List.isEmpty_iff]; exact hemp
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    rw [toChars_eq_intercalate, List.splitOn_intercalate _ _
      (star_notin_toCharsAux m 0 (by omega)) haux_ne]
    rw [parseFactorList_toCharsAux m 0 (by omega) _
      (fun _ _ h => by omega) (fun j hj _ => by simp [Vector.getElem_replicate])]
end MonicMonomial

section EvalRename

variable {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n] {ord : MonomialOrder}

namespace MonicMonomial

/-- Evaluating a renamed monomial equals evaluating the original with a composed assignment. -/
theorem eval_rename {σ₂ : Type _} {n₂ : ℕ} [LinearOrder σ₂] [v₂ : Var σ₂ n₂]
    {R : Type _} [CommMonoid R]
    (m : MonicMonomial σ ord) (f : σ → σ₂) (g : σ₂ → R) (ord₂ : MonomialOrder) :
    (m.rename f ord₂).eval (n := n₂) g = m.eval (g ∘ f) := by
  simp only [eval, rename, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, Function.comp]
  conv_lhs => arg 2; ext j; rw [← Finset.prod_pow_eq_pow_sum]
  simp_rw [pow_ite, pow_zero]
  rw [Finset.prod_comm]
  congr 1; ext i
  rw [Finset.prod_ite_eq Finset.univ (v₂.toFin (f (Var.ofFin i)))]
  simp [Var.ofFin_toFin]

/-- Evaluating a product of monic monomials equals the product of their evaluations. -/
theorem eval_mul {R : Type _} [CommMonoid R]
    (a b : MonicMonomial σ ord) (f : σ → R) :
    (a * b).eval f = a.eval f * b.eval f := by
  simp only [eval, mul_exponents, Fin.getElem_fin, Vector.getElem_ofFn, pow_add]
  exact Finset.prod_mul_distrib

end MonicMonomial

end EvalRename

end Azurite
