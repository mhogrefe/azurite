/-
  Round-trip proof: `parseWith F (p.toCharsWith F) = some p`, and its
  default-display specialization `parse (toChars p) = some p`.
-/
import Azurite.AzMvPolynomial.Parse
import Azurite.AzMvPolynomial.ToString
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Nodup

namespace Azurite

open AzPolynomial Monomial MonicMonomial AzMvPolynomial

variable {R : Type _} [DecidableEq R] [Semiring R] [NeZero (1 : R)] [ParsableCoeff R]
         {n : ℕ} {ord : MonomialOrder}

/-! ### Helpers -/

theorem isNotSign_of_not_plus_not_minus {c : Char}
    (hp : c ≠ '+') (hm : c ≠ '-') : isNotSign c = true := by
  simp [isNotSign, bne_iff_ne, hp, hm]

theorem all_isNotSign_tail {m : List Char}
    (hno_plus : '+' ∉ m) (hno_minus_tail : '-' ∉ m.tail) :
    ∀ c ∈ m.tail, isNotSign c = true := by
  intro c hc
  exact isNotSign_of_not_plus_not_minus
    (fun h => hno_plus (h ▸ List.mem_of_mem_tail hc))
    (fun h => hno_minus_tail (h ▸ hc))

/-! ### Layer 1: splitting inverts joining -/

private theorem joinMonomialsAux_head_cond
    (ms : List (List Char)) (hne : ∀ m ∈ ms, m ≠ []) :
    joinMonomialsAux ms = [] ∨
    ∃ c cs, joinMonomialsAux ms = c :: cs ∧ isNotSign c = false := by
  match ms with
  | [] => left; rfl
  | m :: rest =>
    right
    obtain ⟨c, t, hm⟩ := List.exists_cons_of_ne_nil (hne m (List.mem_cons_self ..))
    subst hm; simp only [joinMonomialsAux]
    split
    · rename_i tail heq; obtain ⟨rfl, rfl⟩ := List.cons.inj heq
      exact ⟨'-', t ++ joinMonomialsAux rest, by simp, by decide⟩
    · exact ⟨'+', (c :: t) ++ joinMonomialsAux rest, by simp, by decide⟩

/-- Helper: takeWhile/dropWhile on monomial tail ++ joinMonomialsAux rest. -/
private theorem tw_dw_tail
    {c : Char} {t : List Char} {ms : List (List Char)}
    (hm_np : '+' ∉ (c :: t)) (hm_nmt : '-' ∉ (c :: t).tail)
    (hne' : ∀ m' ∈ ms, m' ≠ []) :
    (t ++ joinMonomialsAux ms).takeWhile isNotSign = t ∧
    (t ++ joinMonomialsAux ms).dropWhile isNotSign = joinMonomialsAux ms := by
  have ht : ∀ ch ∈ t, isNotSign ch = true := all_isNotSign_tail hm_np hm_nmt
  constructor
  · rw [List.takeWhile_append,
        show (t.takeWhile isNotSign).length = t.length from by
          rw [(List.takeWhile_eq_self_iff).mpr ht],
        if_pos rfl]
    rcases joinMonomialsAux_head_cond ms hne' with h | ⟨d, ds, h, hd⟩
    · rw [h]; simp
    · rw [h, List.takeWhile_cons_of_neg (Bool.eq_false_iff.mp hd)]; simp
  · rw [List.dropWhile_append,
        show (t.dropWhile isNotSign).isEmpty = true from by
          simp [(List.dropWhile_eq_nil_iff).mpr ht]]
    rcases joinMonomialsAux_head_cond ms hne' with h | ⟨d, ds, h, hd⟩
    · simp [h]
    · simp [h, List.dropWhile_cons_of_neg (Bool.eq_false_iff.mp hd)]

theorem splitMonomialsAux_joinMonomialsAux
    (ms : List (List Char))
    (hne : ∀ m ∈ ms, m ≠ [])
    (hno_plus : ∀ m ∈ ms, '+' ∉ m)
    (hno_minus_tail : ∀ m ∈ ms, '-' ∉ m.tail) :
    splitMonomialsAux (joinMonomialsAux ms) = ms := by
  induction ms with
  | nil => simp [splitMonomialsAux.eq_1, joinMonomialsAux.eq_1]
  | cons m ms ih =>
    have hm_ne := hne m (List.mem_cons_self ..)
    have hm_np := hno_plus m (List.mem_cons_self ..)
    have hm_nmt := hno_minus_tail m (List.mem_cons_self ..)
    have hne' := fun m' h => hne m' (List.mem_cons_of_mem _ h)
    have hnp' := fun m' h => hno_plus m' (List.mem_cons_of_mem _ h)
    have hnmt' := fun m' h => hno_minus_tail m' (List.mem_cons_of_mem _ h)
    have hih := ih hne' hnp' hnmt'
    obtain ⟨c, t, hm⟩ := List.exists_cons_of_ne_nil hm_ne
    subst hm
    have ⟨htw, hdw⟩ := tw_dw_tail hm_np hm_nmt hne'
    -- Case split: does m start with '-'?
    by_cases hc_minus : c = '-'
    · -- m starts with '-': sep = []
      subst hc_minus
      rw [joinMonomialsAux.eq_2]
      simp only [List.nil_append, List.cons_append]
      rw [splitMonomialsAux.eq_3 '-' (t ++ joinMonomialsAux ms) (by decide), htw, hdw, hih]
    · -- m doesn't start with '-': sep = ['+']
      have hc_np : c ≠ '+' := fun h => hm_np (h ▸ List.mem_cons_self ..)
      rw [joinMonomialsAux.eq_3 _ _ (fun _ heq => hc_minus (List.cons.inj heq).1)]
      simp only [List.nil_append, List.cons_append,
                 splitMonomialsAux.eq_2, takeMonomial.eq_2, htw, hdw, hih]

theorem splitMonomials_joinMonomials
    (ms : List (List Char))
    (hne : ∀ m ∈ ms, m ≠ [])
    (hno_plus : ∀ m ∈ ms, '+' ∉ m)
    (hno_minus_tail : ∀ m ∈ ms, '-' ∉ m.tail) :
    splitMonomials (joinMonomials ms) = ms := by
  match ms with
  | [] => simp [joinMonomials, splitMonomials]
  | m :: ms =>
    have hm_np := hno_plus m (List.mem_cons_self ..)
    have hm_nmt := hno_minus_tail m (List.mem_cons_self ..)
    have hne' := fun m' h => hne m' (List.mem_cons_of_mem _ h)
    have hnp' := fun m' h => hno_plus m' (List.mem_cons_of_mem _ h)
    have hnmt' := fun m' h => hno_minus_tail m' (List.mem_cons_of_mem _ h)
    obtain ⟨c, t, hm⟩ := List.exists_cons_of_ne_nil (hne m (List.mem_cons_self ..))
    subst hm
    have ⟨htw, hdw⟩ := tw_dw_tail hm_np hm_nmt hne'
    simp only [joinMonomials, List.cons_append,
               splitMonomials, takeMonomial, htw, hdw]
    exact congrArg ((c :: t) :: ·) (splitMonomialsAux_joinMonomialsAux ms hne' hnp' hnmt')

/-! ### Layer 3: ofMonomials? on already-sorted terms -/

omit [DecidableEq R] [NeZero (1 : R)] [ParsableCoeff R] in
private theorem mergeSort_sorted_eq
    {l : List (Monomial n R ord)}
    (hsorted : l.Pairwise (fun a b => a.monic > b.monic)) :
    l.mergeSort monicGeq = l := by
  have hperm := List.mergeSort_perm l monicGeq
  have hge_sorted : (l.mergeSort monicGeq).Pairwise (fun a b => a.monic ≥ b.monic) :=
    (List.pairwise_mergeSort monicGeq_trans monicGeq_total l).imp
      (fun h => (monicGeq_iff_ge _ _).mp h)
  have hge_orig : l.Pairwise (fun a b => a.monic ≥ b.monic) :=
    hsorted.imp (fun h => le_of_lt h)
  have hmap_nodup : (l.map Monomial.monic).Nodup :=
    (hsorted.map Monomial.monic (fun _ _ h => h)).imp (fun h => ne_of_gt h)
  exact hperm.eq_of_pairwise
    (fun a b ha hb hab hba =>
      List.inj_on_of_nodup_map hmap_nodup (hperm.mem_iff.mp ha) hb (le_antisymm hba hab))
    hge_sorted hge_orig

omit [DecidableEq R] [NeZero (1 : R)] [ParsableCoeff R] in
private theorem adjacentDistinct_of_pairwise_gt
    {l : List (Monomial n R ord)}
    (h : l.Pairwise (fun a b => a.monic > b.monic)) :
    adjacentDistinct l = true := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    match t, h with
    | [], _ => rfl
    | b :: _, h' =>
      simp only [adjacentDistinct, Bool.and_eq_true, bne_iff_ne, ne_eq]
      rw [List.pairwise_cons] at h'
      exact ⟨ne_of_gt (h'.1 b (List.mem_cons_self ..)), ih h'.2⟩

omit [DecidableEq R] [NeZero (1 : R)] [ParsableCoeff R] in
theorem ofMonomials?_terms (p : AzMvPolynomial n R ord) :
    ofMonomials? p.terms = some p := by
  unfold ofMonomials?
  have hs := mergeSort_sorted_eq p.sorted
  have hadj : adjacentDistinct p.terms.toList = true := adjacentDistinct_of_pairwise_gt p.sorted
  simp only [hs, hadj, dite_true]

/-! ### Layer 2 + 4: round-trip, parametrized over display `F` -/

section Display

variable (F : Type _) [LinearOrder F] [ParsableVar F n]

theorem mapM_parseWith_map_toCharsWith (ms : List (Monomial n R ord)) :
    (ms.map (fun m => m.toCharsWith F)).mapM
        (Monomial.parseWith (n := n) (ord := ord) (R := R) F) = some ms := by
  induction ms with
  | nil => simp
  | cons m ms ih =>
    simp only [List.map_cons, List.mapM_cons, Monomial.parseWith_toCharsWith]
    simp [ih]

/-- A monomial's char-list representation is never just `['0']`, because monomials
    always have nonzero coefficient. -/
private theorem Monomial.toCharsWith_ne_zeroChar (m : Monomial n R ord) :
    m.toCharsWith F ≠ ['0'] := by
  intro hmtc
  unfold Monomial.toCharsWith at hmtc
  split_ifs at hmtc with hmonic hcoeff
  · -- monic = 1: hmtc : ParsableCoeff.toChars m.coeff.val = ['0']
    have h1 := ParsableCoeff.parse_toChars (R := R) m.coeff.val
    have h2 := ParsableCoeff.parse_toChars (R := R) (0 : R)
    rw [hmtc] at h1
    rw [ParsableCoeff.toChars_zero] at h2
    exact m.coeff.property (Option.some.inj (h2.symm.trans h1)).symm
  · -- coeff = 1, monic ≠ 1: hmtc : m.monic.toCharsWith F = ['0']
    -- Extract '0' as head of m.monic.toCharsWith F and apply head_not_syntax.
    obtain ⟨c_m, t_m, hctm⟩ := List.exists_cons_of_ne_nil
      (MonicMonomial.toCharsWith_ne_nil F m.monic hmonic)
    have hc_zero : c_m = '0' := by rw [hctm] at hmtc; exact (List.cons.inj hmtc).1
    have hhead_not : ¬ isPolySyntaxChar c_m := by
      have h := MonicMonomial.toCharsWith_head_not_syntax F m.monic hmonic
      simp only [hctm, List.head_cons] at h
      exact h
    exact hhead_not (hc_zero ▸ Or.inl ⟨by decide, by decide⟩)
  · -- Case 3: negOne branch or coeff*monic. Both produce a list containing '*' or
    -- a leading '-', neither of which matches `['0']`.
    split at hmtc
    · split_ifs at hmtc with _
      · -- '-' :: m.monic.toCharsWith F = ['0']: first char '-' ≠ '0'
        exact absurd (List.cons.inj hmtc).1 (by decide)
      · -- coeffChars ++ ['*'] ++ monicChars = ['0']: contains '*', contradiction
        have : '*' ∈ (['0'] : List Char) := hmtc ▸
          List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_self ..))
        simp at this
    · -- coeffChars ++ ['*'] ++ monicChars = ['0']: contains '*', contradiction
      have : '*' ∈ (['0'] : List Char) := hmtc ▸
        List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_self ..))
      simp at this

/-- A nonempty polynomial's char-list representation is never just `['0']`. -/
private theorem toCharsWith_ne_zeroChar_of_nonempty (p : AzMvPolynomial n R ord)
    (hemp : p.terms.isEmpty = false) :
    joinMonomials (p.terms.toList.map (fun m => m.toCharsWith F)) ≠ ['0'] := by
  intro heq
  have hne : p.terms.toList ≠ [] := by simp at hemp; simp [hemp]
  obtain ⟨m, ms, hms⟩ := List.exists_cons_of_ne_nil hne
  rw [hms, List.map_cons, joinMonomials] at heq
  obtain ⟨c, t, hct⟩ := List.exists_cons_of_ne_nil (Monomial.toCharsWith_ne_nil F m)
  rw [hct, List.cons_append] at heq
  obtain ⟨rfl, htail⟩ := List.cons.inj heq
  have ⟨ht_nil, _⟩ := List.append_eq_nil_iff.mp htail
  exact Monomial.toCharsWith_ne_zeroChar F m (by rw [hct, ht_nil])

/-- Round-trip: parsing the string representation recovers the polynomial. -/
theorem AzMvPolynomial.parseWith_toCharsWith (p : AzMvPolynomial n R ord) :
    AzMvPolynomial.parseWith F (p.toCharsWith F) = some p := by
  by_cases hemp : p.terms.isEmpty
  · -- Zero case: `toCharsWith F p = ['0']` (via `toChars_zero`), so `parseWith` returns `some 0`.
    cases p with | mk terms sorted =>
    simp only [Array.isEmpty_iff] at hemp
    subst hemp
    unfold AzMvPolynomial.toCharsWith AzMvPolynomial.parseWith
    simp only [show (#[] : Array (Monomial n R ord)).isEmpty = true from rfl, ↓reduceIte,
      ParsableCoeff.toChars_zero]
    rfl
  · -- Nonempty case: `toCharsWith F p = joinMonomials (...)`, invert via
    -- `splitMonomials_joinMonomials` then `mapM_parseWith_map_toCharsWith`.
    unfold AzMvPolynomial.toCharsWith AzMvPolynomial.parseWith
    simp only [hemp, ↓reduceIte, Bool.false_eq_true]
    rw [if_neg (toCharsWith_ne_zeroChar_of_nonempty F p (by simp [hemp])),
      splitMonomials_joinMonomials _
        (by intro m hm; obtain ⟨mono, _, rfl⟩ := List.mem_map.mp hm
            exact Monomial.toCharsWith_ne_nil F _)
        (by intro m hm; obtain ⟨mono, _, rfl⟩ := List.mem_map.mp hm
            exact Monomial.plus_notin_toCharsWith F _)
        (by intro m hm; obtain ⟨mono, _, rfl⟩ := List.mem_map.mp hm
            exact Monomial.minus_notin_tail_toCharsWith F _),
      mapM_parseWith_map_toCharsWith]
    simpa using ofMonomials?_terms p

end Display

/-- Default-display round-trip: `parse (toChars p) = some p`. -/
theorem AzMvPolynomial.parse_toChars (p : AzMvPolynomial n R ord) :
    AzMvPolynomial.parse p.toChars = some p :=
  AzMvPolynomial.parseWith_toCharsWith (IndexedVar n) p

end Azurite
