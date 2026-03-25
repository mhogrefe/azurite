/-
  Round-trip proof: `parse (toChars p) = some p`.
-/
import Azurite.AzMvPolynomial.Parse
import Azurite.AzMvPolynomial.ToString
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Nodup

namespace Azurite

open AzPolynomial Monomial MonicMonomial AzMvPolynomial

variable {R : Type _} [DecidableEq R] [Semiring R] [ParsableCoeff R]
         {σ : Type _} {n : ℕ} [LinearOrder σ] [ParsableVar σ n]
         {ord : MonomialOrder}

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

private theorem takeWhile_eq_of_forall {l : List α} {p : α → Bool}
    (h : ∀ x ∈ l, p x = true) : l.takeWhile p = l := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.takeWhile_cons_of_pos (h a (List.mem_cons_self ..))]
    exact congrArg _ (ih (fun x hx => h x (List.mem_cons_of_mem _ hx)))

private theorem dropWhile_nil_of_forall {l : List α} {p : α → Bool}
    (h : ∀ x ∈ l, p x = true) : l.dropWhile p = [] := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.dropWhile_cons_of_pos (h a (List.mem_cons_self ..))]
    exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx))

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
        show (t.takeWhile isNotSign).length = t.length from by rw [takeWhile_eq_of_forall ht],
        if_pos rfl]
    rcases joinMonomialsAux_head_cond ms hne' with h | ⟨d, ds, h, hd⟩
    · rw [h]; simp
    · rw [h, List.takeWhile_cons_of_neg (Bool.eq_false_iff.mp hd)]; simp
  · rw [List.dropWhile_append,
        show (t.dropWhile isNotSign).isEmpty = true from by simp [dropWhile_nil_of_forall ht]]
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
               splitMonomials.eq_2, takeMonomial.eq_2, htw, hdw]
    exact congrArg ((c :: t) :: ·) (splitMonomialsAux_joinMonomialsAux ms hne' hnp' hnmt')

/-! ### Layer 2: monomial round-trip via mapM -/

theorem mapM_parse_map_toChars (ms : List (Monomial σ R ord)) :
    (ms.map Monomial.toChars).mapM (Monomial.parse (σ := σ) (R := R) (ord := ord))
      = some ms := by
  induction ms with
  | nil => simp
  | cons m ms ih =>
    simp only [List.map_cons, List.mapM_cons, Monomial.parse_toChars]
    simp [ih]

/-! ### Layer 3: ofMonomials? on already-sorted terms -/

omit [DecidableEq R] [ParsableCoeff R] in
private theorem mergeSort_sorted_eq
    {l : List (Monomial σ R ord)}
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

omit [DecidableEq R] [ParsableCoeff R] in
private theorem adjacentDistinct_of_pairwise_gt
    {l : List (Monomial σ R ord)}
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

omit [DecidableEq R] [ParsableCoeff R] in
theorem ofMonomials?_terms (p : AzMvPolynomial σ R ord) :
    ofMonomials? p.terms = some p := by
  unfold ofMonomials?
  have hs := mergeSort_sorted_eq p.sorted
  have hadj : adjacentDistinct p.terms.toList = true := adjacentDistinct_of_pairwise_gt p.sorted
  simp only [hs, hadj, dite_true]

/-! ### Layer 4: main theorem -/

private theorem toChars_ne_zero_of_nonempty (p : AzMvPolynomial σ R ord)
    (hemp : p.terms.isEmpty = false) :
    joinMonomials (p.terms.toList.map Monomial.toChars) ≠
        ParsableCoeff.toChars (0 : R) := by
  intro heq
  have hne : p.terms.toList ≠ [] := by simp at hemp; simp [hemp]
  obtain ⟨m, ms, hms⟩ := List.exists_cons_of_ne_nil hne
  rw [hms, List.map_cons] at heq
  match ms with
  | [] =>
    -- Single monomial: joinMonomials [Monomial.toChars m] = Monomial.toChars m
    simp only [List.map_nil, joinMonomials, joinMonomialsAux, List.append_nil] at heq
    -- Case split on monic and coeff
    by_cases hmonic : m.monic = 1
    · -- monic = 1: toChars m = ParsableCoeff.toChars coeff, injectivity gives coeff = 0
      simp only [Monomial.toChars, hmonic, ↓reduceIte] at heq
      have h1 := ParsableCoeff.parse_toChars (R := R) m.coeff.val
      rw [heq, ParsableCoeff.parse_toChars] at h1
      exact m.coeff.property (Option.some.inj h1.symm)
    · by_cases hcoeff : m.coeff.val = 1
      · -- coeff = 1, monic ≠ 1: first char is ¬isPolySyntaxChar vs isPolySyntaxChar
        simp only [Monomial.toChars, show (m.monic = 1) = False from propext ⟨hmonic, False.elim⟩,
                   ↓reduceIte, hcoeff, ↓reduceIte] at heq
        have hhead_not := MonicMonomial.toChars_head_not_syntax m.monic hmonic
        obtain ⟨hne0, hhead_is⟩ := ParsableCoeff.toChars_head_is_syntax (0 : R)
        have hne_monic := MonicMonomial.toChars_ne_nil m.monic hmonic
        have : (ParsableCoeff.toChars (0 : R)).head hne0 = m.monic.toChars.head hne_monic := by
          congr 1; exact heq.symm
        rw [this] at hhead_is
        exact hhead_not hhead_is
      · -- coeff ≠ 1, monic ≠ 1: contains '*', which toChars 0 can't have
        simp only [Monomial.toChars, show (m.monic = 1) = False from propext ⟨hmonic, False.elim⟩,
                   ↓reduceIte, show (m.coeff.val = 1) = False from propext ⟨hcoeff, False.elim⟩,
                   ↓reduceIte] at heq
        have : '*' ∈ ParsableCoeff.toChars (0 : R) := by
          rw [← heq]; exact List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_self ..))
        exact ParsableCoeff.toChars_no_syntax (0 : R) '*' this (Or.inr (Or.inl rfl))
  | m₂ :: rest =>
    -- ≥2 monomials: joinMonomialsAux starts with '+' or '-'
    -- Either way, this char appears in the tail of the full result, which is impossible.
    simp only [List.map_cons] at heq
    have hm₂ne := Monomial.toChars_ne_nil m₂
    have hne' : ∀ x ∈ (Monomial.toChars m₂ :: rest.map Monomial.toChars), x ≠ [] := by
      intro x hx; simp at hx
      rcases hx with rfl | ⟨a, _, rfl⟩
      · exact hm₂ne
      · exact Monomial.toChars_ne_nil a
    rcases joinMonomialsAux_head_cond _ hne' with h | ⟨c, cs, hjoin, hnsign⟩
    · -- joinMonomialsAux = []: impossible
      -- joinMonomialsAux of nonempty list with nonempty head is always nonempty
      obtain ⟨c₂, t₂, hm₂⟩ := List.exists_cons_of_ne_nil hm₂ne
      rw [show Monomial.toChars m₂ = c₂ :: t₂ from hm₂] at h
      simp only [joinMonomialsAux] at h; split at h
      · simp at h
      · exact List.cons_ne_nil _ _ h
    · -- joinMonomialsAux starts with c where isNotSign c = false, i.e. c = '+' or c = '-'
      simp only [isNotSign, bne_iff_ne, Bool.and_eq_true, ne_eq,
                 Bool.eq_false_iff, not_and, Decidable.not_not] at hnsign
      -- joinMonomials (m.toChars :: m₂.toChars :: ...) = m.toChars ++ joinMonomialsAux (...)
      rw [joinMonomials] at heq
      rw [hjoin] at heq
      -- heq : Monomial.toChars m ++ c :: cs = ParsableCoeff.toChars 0
      -- c appears at position |Monomial.toChars m| > 0
      have hm_ne := Monomial.toChars_ne_nil m
      by_cases hc_plus : c = '+'
      · -- c = '+', but '+' ∉ ParsableCoeff.toChars 0
        have : '+' ∈ ParsableCoeff.toChars (0 : R) := by
          rw [← heq, hc_plus]
          exact List.mem_append_right _ (List.mem_cons_self ..)
        exact ParsableCoeff.toChars_no_syntax (0 : R) '+' this (Or.inl rfl)
      · -- c = '-' (since isNotSign c = false and c ≠ '+')
        have hc_minus : c = '-' := hnsign hc_plus
        -- '-' appears in tail of result
        have : '-' ∈ (ParsableCoeff.toChars (0 : R)).tail := by
          rw [← heq, hc_minus]
          have ⟨a, t, hat⟩ := List.exists_cons_of_ne_nil hm_ne
          rw [hat, List.cons_append, List.tail_cons]
          exact List.mem_append_right _ (List.mem_cons_self ..)
        exact ParsableCoeff.toChars_no_minus_tail (0 : R) '-' this rfl

/-- Round-trip: parsing the string representation recovers the polynomial. -/
theorem AzMvPolynomial.parse_toChars (p : AzMvPolynomial σ R ord) :
    AzMvPolynomial.parse p.toChars = some p := by
  unfold AzMvPolynomial.toChars AzMvPolynomial.parse
  by_cases hemp : p.terms.isEmpty
  · -- Zero case: p is the zero polynomial
    cases p with | mk terms sorted =>
    simp only [Array.isEmpty_iff] at hemp
    subst hemp
    simp only [show (#[] : Array (Monomial σ R ord)).isEmpty = true from rfl, ↓reduceIte]
    cases sorted; rfl
  · simp only [hemp, ↓reduceIte, Bool.false_eq_true]
    split_ifs with hzero
    · exact absurd hzero (toChars_ne_zero_of_nonempty p (by simp [hemp]))
    · rw [splitMonomials_joinMonomials _
        (by intro m hm; obtain ⟨mono, _, rfl⟩ := List.mem_map.mp hm
            exact Monomial.toChars_ne_nil _)
        (by intro m hm; obtain ⟨mono, _, rfl⟩ := List.mem_map.mp hm
            exact Monomial.plus_notin_toChars _)
        (by intro m hm; obtain ⟨mono, _, rfl⟩ := List.mem_map.mp hm
            exact Monomial.minus_notin_tail_toChars _),
        mapM_parse_map_toChars]
      simpa using ofMonomials?_terms p

end Azurite
