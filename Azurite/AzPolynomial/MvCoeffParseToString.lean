/-
  Round-trip proof for the nested `AzPolynomial` serializer
  (`AzPolynomial.toCharsMvCoeffWith` / `parseMvCoeffWith`).

  The hypothesis is that both the coefficient ring `R` and the variable naming
  scheme `F` are paren-free (`ParenFreeCoeff` / `ParenFreeVar`).  This ensures
  that every character inside the `(...)`-wrapped coefficient block is neither
  a `(` nor a `)`, so the outer parser's `span (· != ')')` reliably locates the
  matching closing paren, and the top-level `+` splitter correctly distinguishes
  outer term-separating `+`s from inner coefficient `+`s.
-/
import Azurite.AzPolynomial.MvCoeffParse
import Azurite.AzMvPolynomial.ParenFree
import Azurite.AzMvPolynomial.ParsableElement
import Azurite.AzPolynomial.Equiv.Add
import Azurite.AzPolynomial.Equiv.Monomial

namespace Azurite

open _root_.Azurite.AzPolynomial AzMvPolynomial

variable {R : Type _} [DecidableEq R] [CommSemiring R] [NoZeroDivisors R]
         [NeZero (1 : R)] [ParsableCoeff R] [ParenFreeCoeff R]
         {n : ℕ} {ord : MonomialOrder}

/-! ### Paren-free lemmas lifted to `AzMvPolynomial.toCharsWith` -/

section ParenFree
variable (F : Type _) [LinearOrder F] [ParsableVar F n] [ParenFreeVar F n]

omit [NoZeroDivisors R] in
theorem AzMvPolynomial.toCharsWith_no_lparen (p : AzMvPolynomial n R ord) :
    '(' ∉ p.toCharsWith F :=
  AzMvPolynomial.char_notin_toCharsWith F '('
    ParenFreeCoeff.toChars_no_lparen
    ParenFreeVar.toChars_no_lparen
    (not_mem_natToChars_of_not_digit '(' (by decide))
    (by decide) (by decide) (by decide) (by decide) p

omit [NoZeroDivisors R] in
theorem AzMvPolynomial.toCharsWith_no_rparen (p : AzMvPolynomial n R ord) :
    ')' ∉ p.toCharsWith F :=
  AzMvPolynomial.char_notin_toCharsWith F ')'
    ParenFreeCoeff.toChars_no_rparen
    ParenFreeVar.toChars_no_rparen
    (not_mem_natToChars_of_not_digit ')' (by decide))
    (by decide) (by decide) (by decide) (by decide) p

end ParenFree

/-! ### `xPowerChars` contains no parens and no `+` -/

theorem AzPolynomial.xPowerChars_no_lparen (i : ℕ) :
    '(' ∉ AzPolynomial.xPowerChars i := by
  intro hc
  unfold AzPolynomial.xPowerChars at hc
  split_ifs at hc
  · simp at hc
  · simp at hc
  · simp only [List.mem_cons] at hc
    rcases hc with heq | heq | hc
    · exact absurd heq (by decide)
    · exact absurd heq (by decide)
    · exact not_mem_natToChars_of_not_digit '(' (by decide) i hc

theorem AzPolynomial.xPowerChars_no_rparen (i : ℕ) :
    ')' ∉ AzPolynomial.xPowerChars i := by
  intro hc
  unfold AzPolynomial.xPowerChars at hc
  split_ifs at hc
  · simp at hc
  · simp at hc
  · simp only [List.mem_cons] at hc
    rcases hc with heq | heq | hc
    · exact absurd heq (by decide)
    · exact absurd heq (by decide)
    · exact not_mem_natToChars_of_not_digit ')' (by decide) i hc

theorem AzPolynomial.xPowerChars_no_plus (i : ℕ) :
    '+' ∉ AzPolynomial.xPowerChars i := by
  intro hc
  unfold AzPolynomial.xPowerChars at hc
  split_ifs at hc
  · simp at hc
  · simp at hc
  · simp only [List.mem_cons] at hc
    rcases hc with heq | heq | hc
    · exact absurd heq (by decide)
    · exact absurd heq (by decide)
    · exact not_mem_natToChars_of_not_digit '+' (by decide) i hc

/-! ### `splitTermsAux` consumption lemmas -/

/-- Equation lemma for `splitTermsAux` on cons. -/
private theorem AzPolynomial.splitTermsAux_cons
    (c : Char) (cs : List Char) (d : ℕ) (curRev : List Char)
    (accRev : List (List Char)) :
    AzPolynomial.splitTermsAux (c :: cs) d curRev accRev =
      (if c = '+' ∧ d = 0 then
        AzPolynomial.splitTermsAux cs 0 [] (curRev.reverse :: accRev)
      else if c = '(' then
        AzPolynomial.splitTermsAux cs (d + 1) (c :: curRev) accRev
      else if c = ')' then
        AzPolynomial.splitTermsAux cs (d - 1) (c :: curRev) accRev
      else
        AzPolynomial.splitTermsAux cs d (c :: curRev) accRev) := rfl

/-- Consuming a single character that is not `+`, `(`, or `)` (or is `+` but at
    positive depth) simply prepends it to `curRev`. -/
private theorem AzPolynomial.splitTermsAux_cons_neutral
    (c : Char) (cs curRev : List Char) (accRev : List (List Char)) (d : ℕ)
    (hlp : c ≠ '(') (hrp : c ≠ ')') (htop : c = '+' → d ≠ 0) :
    AzPolynomial.splitTermsAux (c :: cs) d curRev accRev =
    AzPolynomial.splitTermsAux cs d (c :: curRev) accRev := by
  rw [splitTermsAux_cons]
  by_cases h_plus : c = '+'
  · have hd : d ≠ 0 := htop h_plus
    rw [if_neg (fun ⟨_, hd0⟩ => hd hd0), if_neg (h_plus ▸ hlp), if_neg (h_plus ▸ hrp)]
  · rw [if_neg (fun ⟨hp, _⟩ => h_plus hp), if_neg hlp, if_neg hrp]

/-- Consuming a paren-free, non-top-plus prefix just prepends (in reverse) to
    `curRev`.  The depth is preserved because there are no parens. -/
private theorem AzPolynomial.splitTermsAux_consume_neutral
    (t : List Char) (cs : List Char) (d : ℕ) (accRev : List (List Char))
    (h1 : '(' ∉ t) (h2 : ')' ∉ t) (htop : d = 0 → '+' ∉ t) :
    ∀ curRev : List Char,
    AzPolynomial.splitTermsAux (t ++ cs) d curRev accRev =
    AzPolynomial.splitTermsAux cs d (t.reverse ++ curRev) accRev := by
  induction t with
  | nil => intro curRev; simp
  | cons c t' ih =>
    intro curRev
    have hc1 : c ≠ '(' := fun h => h1 (h ▸ List.mem_cons_self ..)
    have hc2 : c ≠ ')' := fun h => h2 (h ▸ List.mem_cons_self ..)
    have hctop : c = '+' → d ≠ 0 := fun h hd =>
      htop hd (h ▸ List.mem_cons_self ..)
    have ht1 : '(' ∉ t' := fun hc => h1 (List.mem_cons_of_mem _ hc)
    have ht2 : ')' ∉ t' := fun hc => h2 (List.mem_cons_of_mem _ hc)
    have httop : d = 0 → '+' ∉ t' :=
      fun hd hc => htop hd (List.mem_cons_of_mem _ hc)
    rw [List.cons_append, splitTermsAux_cons_neutral c _ _ _ _ hc1 hc2 hctop,
        ih ht1 ht2 httop]
    simp

/-- Consuming a paren-wrapped, paren-free block `'(' :: inner ++ ')'` at any
    depth `d` returns to depth `d`. -/
private theorem AzPolynomial.splitTermsAux_consume_paren_wrapped
    (inner cs : List Char) (d : ℕ) (accRev : List (List Char))
    (h1 : '(' ∉ inner) (h2 : ')' ∉ inner) :
    ∀ curRev : List Char,
    AzPolynomial.splitTermsAux ('(' :: inner ++ ')' :: cs) d curRev accRev =
    AzPolynomial.splitTermsAux cs d (')' :: (inner.reverse ++ '(' :: curRev)) accRev := by
  intro curRev
  -- Rewrite to canonical form
  have hrewrite : ('(' :: inner ++ ')' :: cs) = '(' :: (inner ++ ')' :: cs) := by simp
  rw [hrewrite]
  -- Step 1: consume '('
  rw [splitTermsAux_cons]
  rw [if_neg (fun ⟨hp, _⟩ => absurd hp (by decide : ('(' : Char) ≠ '+'))]
  rw [if_pos rfl]
  -- Step 2: consume `inner` (paren-free, depth = d+1 > 0 so `+` is fine)
  rw [splitTermsAux_consume_neutral inner (')' :: cs) (d + 1) accRev h1 h2
      (fun hd => by omega) ('(' :: curRev)]
  -- Step 3: consume ')'
  rw [splitTermsAux_cons]
  rw [if_neg (fun ⟨hp, _⟩ => absurd hp (by decide : (')' : Char) ≠ '+'))]
  rw [if_neg (by decide : ¬(')' : Char) = '(')]
  rw [if_pos rfl]
  show AzPolynomial.splitTermsAux cs (d + 1 - 1) _ _ = _
  rw [show d + 1 - 1 = d from by omega]

/-! ### Term-consumable character lists -/

/-- A character list is "term-consumable": when appearing at depth 0 in
    `splitTermsAux`, consuming it simply prepends the reversed chars to
    `curRev`, without splitting.  This is the abstract property that makes a
    character list a valid top-level "term" for the splitter. -/
private def AzPolynomial.IsTerm (t : List Char) : Prop :=
  ∀ cs curRev accRev,
    AzPolynomial.splitTermsAux (t ++ cs) 0 curRev accRev =
    AzPolynomial.splitTermsAux cs 0 (t.reverse ++ curRev) accRev

/-- A paren-free, `+`-free list is term-consumable. -/
private theorem AzPolynomial.IsTerm.ofNoParensNoPlus
    {t : List Char} (h1 : '(' ∉ t) (h2 : ')' ∉ t) (h3 : '+' ∉ t) :
    AzPolynomial.IsTerm t := fun cs curRev accRev =>
  AzPolynomial.splitTermsAux_consume_neutral t cs 0 accRev h1 h2 (fun _ => h3) curRev

/-- A `'(' :: inner ++ ')' :: tail` list is term-consumable, provided `inner`
    contains no parens and `tail` is paren-free and `+`-free. -/
private theorem AzPolynomial.IsTerm.ofWrapped
    {inner tail : List Char}
    (h_in_lp : '(' ∉ inner) (h_in_rp : ')' ∉ inner)
    (h_tail_lp : '(' ∉ tail) (h_tail_rp : ')' ∉ tail) (h_tail_pl : '+' ∉ tail) :
    AzPolynomial.IsTerm ('(' :: inner ++ ')' :: tail) := by
  intro cs curRev accRev
  have hreassoc : ('(' :: inner ++ ')' :: tail) ++ cs = ('(' :: inner ++ ')' :: (tail ++ cs)) := by
    simp
  rw [hreassoc]
  rw [AzPolynomial.splitTermsAux_consume_paren_wrapped inner (tail ++ cs) 0 accRev h_in_lp h_in_rp curRev]
  rw [AzPolynomial.splitTermsAux_consume_neutral tail cs 0 accRev h_tail_lp h_tail_rp
        (fun _ => h_tail_pl) _]
  congr 1
  simp

/-! ### Each term shape is a term -/

section TermShapes
variable (F : Type _) [LinearOrder F] [ParsableVar F n] [ParenFreeVar F n]

omit [NoZeroDivisors R] in
private theorem AzPolynomial.xPowerChars_isTerm (i : ℕ) :
    AzPolynomial.IsTerm (AzPolynomial.xPowerChars i) :=
  AzPolynomial.IsTerm.ofNoParensNoPlus
    (AzPolynomial.xPowerChars_no_lparen i)
    (AzPolynomial.xPowerChars_no_rparen i)
    (AzPolynomial.xPowerChars_no_plus i)

omit [NoZeroDivisors R] in
private theorem AzPolynomial.termCharsMvCoeffWith_isTerm
    (c : AzMvPolynomial n R ord) (i : ℕ) :
    AzPolynomial.IsTerm (AzPolynomial.termCharsMvCoeffWith F c i) := by
  unfold AzPolynomial.termCharsMvCoeffWith
  by_cases h1 : c = 1 ∧ i ≠ 0
  · rw [if_pos h1]; exact AzPolynomial.xPowerChars_isTerm i
  · rw [if_neg h1]
    by_cases h2 : i = 0
    · -- wrapped, i = 0: '(' :: c.toCharsWith F ++ [')']
      rw [show (if i = 0 then ('(' :: c.toCharsWith F ++ [')'] : List Char)
            else '(' :: c.toCharsWith F ++ [')'] ++ '*' :: AzPolynomial.xPowerChars i)
          = '(' :: c.toCharsWith F ++ ')' :: [] from by simp [h2]]
      exact AzPolynomial.IsTerm.ofWrapped
        (AzMvPolynomial.toCharsWith_no_lparen F c)
        (AzMvPolynomial.toCharsWith_no_rparen F c)
        (by simp) (by simp) (by simp)
    · -- wrapped, i ≠ 0: '(' :: c.toCharsWith F ++ [')'] ++ '*' :: xPowerChars i
      rw [show (if i = 0 then ('(' :: c.toCharsWith F ++ [')'] : List Char)
            else '(' :: c.toCharsWith F ++ [')'] ++ '*' :: AzPolynomial.xPowerChars i)
          = '(' :: c.toCharsWith F ++ ')' :: ('*' :: AzPolynomial.xPowerChars i) from by
            rw [if_neg h2]; simp]
      refine AzPolynomial.IsTerm.ofWrapped
        (AzMvPolynomial.toCharsWith_no_lparen F c)
        (AzMvPolynomial.toCharsWith_no_rparen F c)
        ?_ ?_ ?_
      · intro hc
        simp only [List.mem_cons] at hc
        rcases hc with heq | hc
        · exact absurd heq (by decide)
        · exact AzPolynomial.xPowerChars_no_lparen i hc
      · intro hc
        simp only [List.mem_cons] at hc
        rcases hc with heq | hc
        · exact absurd heq (by decide)
        · exact AzPolynomial.xPowerChars_no_rparen i hc
      · intro hc
        simp only [List.mem_cons] at hc
        rcases hc with heq | hc
        · exact absurd heq (by decide)
        · exact AzPolynomial.xPowerChars_no_plus i hc

end TermShapes

/-! ### `parseBareX` / `parseCoeffSuffix` on `xPowerChars` -/

private theorem AzPolynomial.parseBareX_xPowerChars (i : ℕ) (hi : i ≠ 0) :
    AzPolynomial.parseBareX (AzPolynomial.xPowerChars i) = some i := by
  unfold AzPolynomial.xPowerChars
  rw [if_neg hi]
  by_cases h1 : i = 1
  · rw [if_pos h1, h1]; rfl
  · rw [if_neg h1]
    show AzPolynomial.parseBareX ('x' :: '^' :: natToChars i) = some i
    simp [AzPolynomial.parseBareX, parseNatChars_natToChars]

private theorem AzPolynomial.parseCoeffSuffix_mul_xPowerChars (i : ℕ) (hi : i ≠ 0) :
    AzPolynomial.parseCoeffSuffix ('*' :: AzPolynomial.xPowerChars i) = some i := by
  unfold AzPolynomial.xPowerChars
  rw [if_neg hi]
  by_cases h1 : i = 1
  · rw [if_pos h1, h1]; rfl
  · rw [if_neg h1]
    show AzPolynomial.parseCoeffSuffix ('*' :: 'x' :: '^' :: natToChars i) = some i
    simp [AzPolynomial.parseCoeffSuffix, parseNatChars_natToChars]

/-! ### `parseOneTermMvCoeff` inverts `termCharsMvCoeffWith` -/

section ParseTerm
variable (F : Type _) [LinearOrder F] [ParsableVar F n] [ParenFreeVar F n]

omit [NoZeroDivisors R] in
/-- Wrapped case: parsing `'(' :: c.toCharsWith F ++ ')' :: suffix` returns
    `(c, i)` whenever `parseCoeffSuffix suffix = some i`. -/
private theorem AzPolynomial.parseOneTermMvCoeff_wrapped
    (c : AzMvPolynomial n R ord) (suffix : List Char) (i : ℕ)
    (hsuf : AzPolynomial.parseCoeffSuffix suffix = some i) :
    AzPolynomial.parseOneTermMvCoeff F ('(' :: (c.toCharsWith F ++ ')' :: suffix)) =
      some (c, i) := by
  unfold AzPolynomial.parseOneTermMvCoeff
  have h_norp : ')' ∉ c.toCharsWith F := AzMvPolynomial.toCharsWith_no_rparen F c
  have h_all : ∀ x ∈ c.toCharsWith F, (x != ')') = true :=
    fun x hx => by simp; intro h; exact h_norp (h ▸ hx)
  have htw : List.takeWhile (· != ')') (c.toCharsWith F ++ ')' :: suffix) = c.toCharsWith F := by
    rw [List.takeWhile_append, (List.takeWhile_eq_self_iff).mpr h_all]
    simp
  have hdw : List.dropWhile (· != ')') (c.toCharsWith F ++ ')' :: suffix) = ')' :: suffix := by
    rw [List.dropWhile_append, (List.dropWhile_eq_nil_iff).mpr h_all]
    simp
  simp only [List.span_eq_takeWhile_dropWhile, htw, hdw]
  simp only [hsuf, Option.bind_some, AzMvPolynomial.parseWith_toCharsWith, Option.map_some]

omit [NoZeroDivisors R] in
private theorem AzPolynomial.parseOneTermMvCoeff_termCharsMvCoeffWith
    (c : AzMvPolynomial n R ord) (i : ℕ) :
    AzPolynomial.parseOneTermMvCoeff F (AzPolynomial.termCharsMvCoeffWith F c i) =
      some (c, i) := by
  unfold AzPolynomial.termCharsMvCoeffWith
  by_cases h1 : c = 1 ∧ i ≠ 0
  · rw [if_pos h1]
    obtain ⟨hc, hi⟩ := h1
    subst hc
    -- xPowerChars i; parseOneTerm goes through the bare-x branch.
    have hx : ∃ rest, AzPolynomial.xPowerChars i = 'x' :: rest := by
      unfold AzPolynomial.xPowerChars
      rw [if_neg hi]
      by_cases h1' : i = 1
      · rw [if_pos h1']; exact ⟨[], rfl⟩
      · rw [if_neg h1']; exact ⟨_, rfl⟩
    obtain ⟨rest, hrest⟩ := hx
    rw [hrest]
    show ((AzPolynomial.parseBareX ('x' :: rest)).map (fun i => (1, i))) = some (1, i)
    rw [← hrest, parseBareX_xPowerChars i hi]
    rfl
  · rw [if_neg h1]
    by_cases h2 : i = 0
    · subst h2
      simp only
      -- Goal: parseOneTerm ('(' :: c.toCharsWith F ++ [')']) = some (c, 0)
      have : ('(' :: c.toCharsWith F ++ [')'] : List Char) =
          '(' :: (c.toCharsWith F ++ ')' :: []) := by simp
      rw [this]
      exact parseOneTermMvCoeff_wrapped F c [] 0 rfl
    · rw [if_neg h2]
      -- Goal: parseOneTerm ('(' :: c.toCharsWith F ++ [')'] ++ '*' :: xPowerChars i) = some (c, i)
      have : ('(' :: c.toCharsWith F ++ [')'] ++ '*' :: AzPolynomial.xPowerChars i) =
          '(' :: (c.toCharsWith F ++ ')' :: ('*' :: AzPolynomial.xPowerChars i)) := by simp
      rw [this]
      exact parseOneTermMvCoeff_wrapped F c _ i
        (parseCoeffSuffix_mul_xPowerChars i h2)

end ParseTerm

/-! ### `splitTerms` inverts `joinWithPlus` on lists of `IsTerm`s -/

/-- Generalized invariant: consuming `joinWithPlus ts` at depth 0 with empty
    `curRev` yields `accRev.reverse ++ ts` (when `ts` is nonempty and each term
    is `IsTerm`). -/
private theorem AzPolynomial.splitTermsAux_joinWithPlus
    {ts : List (List Char)} (hts : ∀ t ∈ ts, AzPolynomial.IsTerm t) (hne : ts ≠ []) :
    ∀ accRev : List (List Char),
    AzPolynomial.splitTermsAux (AzPolynomial.joinWithPlus ts) 0 [] accRev =
    accRev.reverse ++ ts := by
  induction ts with
  | nil => exact absurd rfl hne
  | cons t rest ih =>
    intro accRev
    match hrest : rest with
    | [] =>
      -- `joinWithPlus [t] = t`
      simp only [AzPolynomial.joinWithPlus]
      have ht : AzPolynomial.IsTerm t := hts t (List.mem_cons_self ..)
      -- Convert `splitTermsAux t 0 [] accRev` via `IsTerm`: append `[]` to `t`.
      have : AzPolynomial.splitTermsAux t 0 [] accRev =
          AzPolynomial.splitTermsAux [] 0 (t.reverse ++ []) accRev := by
        have := ht [] [] accRev
        simpa using this
      rw [this]
      simp [AzPolynomial.splitTermsAux]
    | t' :: rest' =>
      -- `joinWithPlus (t :: t' :: rest') = t ++ '+' :: joinWithPlus (t' :: rest')`
      have hjoin : AzPolynomial.joinWithPlus (t :: t' :: rest') =
          t ++ '+' :: AzPolynomial.joinWithPlus (t' :: rest') := rfl
      rw [hjoin]
      have ht : AzPolynomial.IsTerm t := hts t (List.mem_cons_self ..)
      -- Consume `t` using `IsTerm`.
      have h1 : AzPolynomial.splitTermsAux (t ++ '+' :: AzPolynomial.joinWithPlus (t' :: rest'))
                  0 [] accRev =
          AzPolynomial.splitTermsAux ('+' :: AzPolynomial.joinWithPlus (t' :: rest')) 0
              (t.reverse ++ []) accRev := ht _ _ _
      rw [h1]
      -- Consume the top-level `+`.
      rw [splitTermsAux_cons]
      rw [if_pos ⟨rfl, rfl⟩]
      simp only [List.append_nil, List.reverse_reverse]
      -- Apply induction hypothesis.
      have hts' : ∀ s ∈ (t' :: rest'), AzPolynomial.IsTerm s :=
        fun s hs => hts s (List.mem_cons_of_mem _ hs)
      have hne' : (t' :: rest') ≠ [] := by simp
      rw [ih hts' hne' (t :: accRev)]
      simp

/-- If every term in a nonempty list is `IsTerm`, `splitTerms` inverts
    `joinWithPlus`. -/
private theorem AzPolynomial.splitTerms_joinWithPlus
    {ts : List (List Char)} (hts : ∀ t ∈ ts, AzPolynomial.IsTerm t) (hne : ts ≠ []) :
    AzPolynomial.splitTerms (AzPolynomial.joinWithPlus ts) = ts := by
  unfold AzPolynomial.splitTerms
  have := AzPolynomial.splitTermsAux_joinWithPlus hts hne []
  simpa using this

/-! ### Reconstructing a polynomial via `foldl` over `(coeff, index)` pairs -/

/-- `foldl (+ monomial)` toPoly's to an accumulator plus a sum-of-monomials. -/
private theorem AzPolynomial.foldl_add_monomial_toPoly
    {S : Type _} [DecidableEq S] [CommSemiring S]
    (L : List (S × ℕ)) (init : AzPolynomial S) :
    AzPolynomial.toPoly
      (L.foldl (fun acc x => acc + AzPolynomial.monomial x.2 x.1) init) =
    AzPolynomial.toPoly init +
      (L.map (fun x => (Polynomial.monomial x.2) x.1)).sum := by
  induction L generalizing init with
  | nil => simp
  | cons x L' ih =>
    show AzPolynomial.toPoly
      (L'.foldl _ (init + AzPolynomial.monomial x.2 x.1)) = _
    rw [ih (init + AzPolynomial.monomial x.2 x.1)]
    rw [toPoly_add, toPoly_monomial]
    simp only [List.map_cons, List.sum_cons]
    rw [add_assoc]

/-- `List.range.map.sum` equals `Finset.range.sum`. -/
private theorem AzPolynomial.listRange_map_sum
    {M : Type _} [AddCommMonoid M] (N : ℕ) (f : ℕ → M) :
    ((List.range N).map f).sum = ∑ i ∈ Finset.range N, f i := by
  induction N with
  | zero => simp
  | succ N ih => simp [List.range_succ, ih, Finset.sum_range_succ]

/-- The `(reverse . filterMap)` mapped list's sum equals a Finset-range sum
    (zero entries vanish since `Polynomial.monomial _ 0 = 0`). -/
private theorem AzPolynomial.sum_filterMap_eq_sum_range
    {S : Type _} [CommSemiring S] [DecidableEq S] (p : AzPolynomial S) (N : ℕ) :
    (((List.range N).reverse.filterMap
        (fun i => if p.coeff i = 0 then none else some (p.coeff i, i))).map
          (fun x => (Polynomial.monomial x.2) x.1)).sum =
      ∑ i ∈ Finset.range N, (Polynomial.monomial i) (p.coeff i) := by
  -- Step 1: push the outer `map` through the `filterMap`.
  have step1 :
      (((List.range N).reverse.filterMap
          (fun i => if p.coeff i = 0 then none else some (p.coeff i, i))).map
            (fun x => (Polynomial.monomial x.2) x.1)) =
      ((List.range N).reverse.filterMap
        (fun i => if p.coeff i = 0 then none
                  else some ((Polynomial.monomial i) (p.coeff i)))) := by
    rw [List.map_filterMap]
    congr 1
    funext i
    by_cases h : p.coeff i = 0 <;> simp [h]
  rw [step1]
  -- Step 2: drop the filter since missing entries map to 0.
  have step2 :
      (((List.range N).reverse.filterMap
          (fun i => if p.coeff i = 0 then none
                    else some ((Polynomial.monomial i) (p.coeff i)))).sum) =
      (((List.range N).reverse.map
          (fun i => (Polynomial.monomial i) (p.coeff i))).sum) := by
    induction (List.range N).reverse with
    | nil => rfl
    | cons i L' ih =>
      by_cases h : p.coeff i = 0
      · rw [List.filterMap_cons]
        simp only [h, if_true]
        rw [ih]
        simp only [List.map_cons, List.sum_cons]
        rw [h, Polynomial.monomial_zero_right, zero_add]
      · rw [List.filterMap_cons]
        simp only [h, if_false]
        rw [List.map_cons, List.sum_cons, List.sum_cons, ih]
  rw [step2]
  -- Step 3: reverse preserves sum in a comm monoid.
  rw [show ((List.range N).reverse.map (fun i => (Polynomial.monomial i) (p.coeff i)))
        = ((List.range N).map (fun i => (Polynomial.monomial i) (p.coeff i))).reverse from by
      rw [List.map_reverse]]
  rw [List.sum_reverse]
  rw [listRange_map_sum]

/-- Main reconstruction: the parse-time foldl over the char-split of `p`
    recovers `p`, when `N ≥ p.coeffs.size`. -/
private theorem AzPolynomial.foldl_monomial_recovers_poly
    {S : Type _} [CommSemiring S] [DecidableEq S]
    (p : AzPolynomial S) (N : ℕ) (hN : p.coeffs.size ≤ N) :
    (((List.range N).reverse.filterMap
        (fun i => if p.coeff i = 0 then none else some (p.coeff i, i))).foldl
      (fun acc x => acc + AzPolynomial.monomial x.2 x.1) 0) = p := by
  -- Handle `p = 0` separately (N could be 0, which breaks `as_sum_range'`).
  by_cases hp0 : p = 0
  · subst hp0
    -- All coefficients are 0, so the filterMap list is empty.
    have hempty : (List.range N).reverse.filterMap
        (fun i => if (0 : AzPolynomial S).coeff i = 0 then none else some ((0 : AzPolynomial S).coeff i, i))
        = [] := by
      apply List.filterMap_eq_nil_iff.mpr
      intro i _
      simp [AzPolynomial.coeff]
    rw [hempty, List.foldl_nil]
  apply toPoly_inj.mp
  rw [foldl_add_monomial_toPoly, sum_filterMap_eq_sum_range]
  rw [toPoly_zero, zero_add]
  -- Bound: natDegree (toPoly p) < N.
  have hbound : (AzPolynomial.toPoly p).natDegree < N := by
    have hs : p.coeffs.size ≠ 0 := fun h => hp0 (AzPolynomial.ext (Array.eq_empty_of_size_eq_zero h))
    have hpos : 0 < p.coeffs.size := Nat.pos_of_ne_zero hs
    apply Nat.lt_of_le_of_lt _ (Nat.lt_of_lt_of_le (Nat.sub_lt hpos Nat.one_pos) hN)
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro m hm
    rw [coeff_toPoly_eq]
    have hm' : p.coeffs.size ≤ m := by omega
    simp [AzPolynomial.coeff, Array.getElem?_eq_none hm']
  rw [Polynomial.as_sum_range' (AzPolynomial.toPoly p) N hbound]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [coeff_toPoly_eq]

/-! ### Round-trip theorem -/

section RoundTrip
variable (F : Type _) [LinearOrder F] [ParsableVar F n] [ParenFreeVar F n]

omit [NoZeroDivisors R] [ParenFreeCoeff R] [ParenFreeVar F n] in
/-- Each rendered term has first character `'('` or `'x'`, never `'0'`. -/
private theorem AzPolynomial.termCharsMvCoeffWith_head_ne_zero
    (c : AzMvPolynomial n R ord) (i : ℕ) :
    ∃ ch t, AzPolynomial.termCharsMvCoeffWith F c i = ch :: t ∧ ch ≠ '0' := by
  unfold AzPolynomial.termCharsMvCoeffWith
  by_cases h1 : c = 1 ∧ i ≠ 0
  · rw [if_pos h1]
    unfold AzPolynomial.xPowerChars
    rw [if_neg h1.2]
    by_cases h2 : i = 1
    · rw [if_pos h2]; exact ⟨'x', [], rfl, by decide⟩
    · rw [if_neg h2]; exact ⟨'x', _, rfl, by decide⟩
  · rw [if_neg h1]
    by_cases h2 : i = 0
    · rw [if_pos h2]
      exact ⟨'(', c.toCharsWith F ++ [')'], by simp, by decide⟩
    · rw [if_neg h2]
      refine ⟨'(', c.toCharsWith F ++ [')'] ++ '*' :: AzPolynomial.xPowerChars i, ?_, by decide⟩
      simp

/-- Generic helper: the coefficient at index `size - 1` of a nonempty polynomial
    is nonzero (consequence of `last_ne_zero`). -/
private theorem AzPolynomial.coeff_size_sub_one_ne_zero
    {S : Type _} [Semiring S] [DecidableEq S]
    (p : AzPolynomial S) (hp : p.coeffs.size ≠ 0) :
    p.coeff (p.coeffs.size - 1) ≠ 0 := by
  intro h
  apply p.last_ne_zero
  have hpos : 0 < p.coeffs.size := Nat.pos_of_ne_zero hp
  have hlt : p.coeffs.size - 1 < p.coeffs.size := Nat.sub_lt hpos Nat.one_pos
  have hback : p.coeffs.back? = some (p.coeffs[p.coeffs.size - 1]'hlt) := by
    simp [Array.back?, Array.getElem?_eq_getElem hlt]
  rw [hback]
  congr 1
  have : p.coeffs[p.coeffs.size - 1]'hlt = p.coeff (p.coeffs.size - 1) := by
    simp [AzPolynomial.coeff, Array.getElem?_eq_getElem hlt]
  rw [this, h]

/-- The reversed range of a positive size starts with `size - 1`. -/
private theorem AzPolynomial.reverse_range_cons
    {sz : ℕ} (hsz : 0 < sz) :
    (List.range sz).reverse =
      (sz - 1) :: (List.range (sz - 1)).reverse := by
  conv_lhs => rw [show sz = (sz - 1) + 1 from (Nat.sub_add_cancel hsz).symm]
  rw [List.range_succ, List.reverse_append]
  simp

omit [ParenFreeCoeff R] [ParenFreeVar F n] in
/-- The terms list used in `toCharsMvCoeffWith` is nonempty when `p` is nonzero. -/
private theorem AzPolynomial.terms_ne_nil
    (p : AzPolynomial (AzMvPolynomial n R ord)) (hp : p.coeffs.size ≠ 0) :
    ((List.range p.coeffs.size).reverse.filterMap (fun i =>
        let c := p.coeff i
        if c = 0 then none else
          some (AzPolynomial.termCharsMvCoeffWith F c i))) ≠ [] := by
  have hpos : 0 < p.coeffs.size := Nat.pos_of_ne_zero hp
  have hlast := AzPolynomial.coeff_size_sub_one_ne_zero p hp
  rw [AzPolynomial.reverse_range_cons hpos]
  simp only [List.filterMap_cons]
  rw [if_neg hlast]
  simp

omit [ParenFreeCoeff R] [ParenFreeVar F n] in
/-- The char list of a nonempty polynomial is not `['0']`. -/
private theorem AzPolynomial.toCharsMvCoeffWith_ne_zeroChar
    (p : AzPolynomial (AzMvPolynomial n R ord)) (hp : p.coeffs.size ≠ 0) :
    AzPolynomial.toCharsMvCoeffWith F p ≠ ['0'] := by
  unfold AzPolynomial.toCharsMvCoeffWith
  rw [if_neg hp]
  have hpos : 0 < p.coeffs.size := Nat.pos_of_ne_zero hp
  have hlast := AzPolynomial.coeff_size_sub_one_ne_zero p hp
  rw [AzPolynomial.reverse_range_cons hpos]
  simp only [List.filterMap_cons]
  rw [if_neg hlast]
  -- Get the head character of the first term.
  obtain ⟨ch, tl, heq, hch⟩ :=
    AzPolynomial.termCharsMvCoeffWith_head_ne_zero F
      (p.coeff (p.coeffs.size - 1)) (p.coeffs.size - 1)
  rw [heq]
  -- Now abstract over the tail list and split.
  generalize ((List.range (p.coeffs.size - 1)).reverse.filterMap (fun i =>
      let c := p.coeff i
      if c = 0 then none else
        some (AzPolynomial.termCharsMvCoeffWith F c i))) = L
  intro hc
  match L with
  | [] =>
    -- joinWithPlus [ch :: tl] = ch :: tl
    have : AzPolynomial.joinWithPlus ([ch :: tl]) = ch :: tl := rfl
    rw [this] at hc
    rw [List.cons.injEq] at hc
    exact hch hc.1
  | t :: rest =>
    -- joinWithPlus ((ch :: tl) :: t :: rest) = ch :: (tl ++ '+' :: joinWithPlus (t :: rest))
    have : AzPolynomial.joinWithPlus ((ch :: tl) :: t :: rest) =
        ch :: (tl ++ '+' :: AzPolynomial.joinWithPlus (t :: rest)) := by
      show (ch :: tl) ++ '+' :: AzPolynomial.joinWithPlus (t :: rest) = _
      simp
    rw [this] at hc
    rw [List.cons.injEq] at hc
    exact hch hc.1

/-- Round-trip: parsing the nested-polynomial serialization recovers the
    original polynomial. -/
theorem AzPolynomial.parseMvCoeffWith_toCharsMvCoeffWith
    (p : AzPolynomial (AzMvPolynomial n R ord)) :
    AzPolynomial.parseMvCoeffWith F (AzPolynomial.toCharsMvCoeffWith F p) = some p := by
  by_cases hp0 : p.coeffs.size = 0
  · -- p = 0 case
    have hp : p = 0 := AzPolynomial.ext (Array.eq_empty_of_size_eq_zero hp0)
    subst hp
    unfold AzPolynomial.parseMvCoeffWith AzPolynomial.toCharsMvCoeffWith
    simp
  · -- Nonempty case
    have hne : AzPolynomial.toCharsMvCoeffWith F p ≠ ['0'] :=
      AzPolynomial.toCharsMvCoeffWith_ne_zeroChar F p hp0
    unfold AzPolynomial.parseMvCoeffWith
    rw [if_neg hne]
    -- The terms list and pairs list (both filterMap'd over the reversed range).
    let indices := (List.range p.coeffs.size).reverse
    let terms : List (List Char) := indices.filterMap (fun i =>
      let c := p.coeff i
      if c = 0 then none else some (AzPolynomial.termCharsMvCoeffWith F c i))
    let pairs : List (AzMvPolynomial n R ord × ℕ) := indices.filterMap (fun i =>
      if p.coeff i = 0 then none else some (p.coeff i, i))
    -- Step 1: toCharsMvCoeffWith F p = joinWithPlus terms (using `hp0`).
    have htoCs : AzPolynomial.toCharsMvCoeffWith F p = AzPolynomial.joinWithPlus terms := by
      unfold AzPolynomial.toCharsMvCoeffWith
      rw [if_neg hp0]
    rw [htoCs]
    -- Step 2: splitTerms inverts joinWithPlus because each term is `IsTerm`.
    have hterms_isTerm : ∀ t ∈ terms, AzPolynomial.IsTerm t := by
      intro t ht
      simp only [terms, List.mem_filterMap] at ht
      obtain ⟨i, _, hi⟩ := ht
      by_cases hc : p.coeff i = 0
      · rw [if_pos hc] at hi; exact absurd hi (by simp)
      · rw [if_neg hc] at hi
        rw [Option.some.injEq] at hi
        rw [← hi]
        exact AzPolynomial.termCharsMvCoeffWith_isTerm F (p.coeff i) i
    have hterms_ne : terms ≠ [] := AzPolynomial.terms_ne_nil F p hp0
    rw [AzPolynomial.splitTerms_joinWithPlus hterms_isTerm hterms_ne]
    -- Step 3: terms.mapM parseOneTerm = some pairs.
    have hmapM : terms.mapM (AzPolynomial.parseOneTermMvCoeff F) = some pairs := by
      show (indices.filterMap
            (fun i =>
              let c := p.coeff i
              if c = 0 then none else
                some (AzPolynomial.termCharsMvCoeffWith F c i))).mapM
            (AzPolynomial.parseOneTermMvCoeff F) =
          some (indices.filterMap
            (fun i => if p.coeff i = 0 then none else some (p.coeff i, i)))
      induction indices with
      | nil => rfl
      | cons i rest ih =>
        simp only [List.filterMap_cons]
        by_cases hc : p.coeff i = 0
        · simp only [hc, ↓reduceIte]
          exact ih
        · simp only [hc, ↓reduceIte]
          rw [List.mapM_cons,
              AzPolynomial.parseOneTermMvCoeff_termCharsMvCoeffWith F]
          simp [ih]
    rw [hmapM]
    -- Step 4: Foldl over pairs reconstructs p.
    show some (pairs.foldl (fun acc x => acc + AzPolynomial.monomial x.2 x.1) 0) = some p
    rw [AzPolynomial.foldl_monomial_recovers_poly p p.coeffs.size (le_refl _)]

end RoundTrip

end Azurite

