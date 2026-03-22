/-
  Monomials (coefficient × monic monomial) for multivariate polynomials.
-/
import Azurite.AzMvPolynomial.MonicMonomial
import Azurite.AzMvPolynomial.MonicMonomialProofs
import Azurite.AzPolynomial.StringLemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.List.TakeDrop

namespace Azurite
open AzPolynomial

instance : DecidablePred isLowerAscii := fun c =>
  if h : c.toNat ≥ 'a'.toNat ∧ c.toNat ≤ 'z'.toNat then isTrue h else isFalse h

/-- A character used in polynomial syntax that must not appear in coefficient
    representations: `+`, `*`, `^`. (Digits and `-` are allowed.) -/
def isCoeffSyntaxChar (c : Char) : Prop :=
  c = '+' ∨ c = '*' ∨ c = '^'

/-- Typeclass for coefficient types that can be serialized/deserialized as character
    sequences. Unlike `ParsableVar`, this does not extend `Var`, and `-` is permitted
    as the first character of the representation (to support negative coefficients). -/
class ParsableCoeff (R : Type _) where
  toChars : R → List Char
  parseChars : List Char → Option R
  parse_toChars : ∀ r : R, parseChars (toChars r) = some r
  toChars_nonempty : ∀ r : R, toChars r ≠ []
  /-- No coefficient-syntax character (`+`, `*`, `^`) occurs anywhere. -/
  toChars_no_syntax : ∀ r : R, ∀ c ∈ toChars r, ¬ isCoeffSyntaxChar c
  /-- `-` may only occur as the very first character. -/
  toChars_no_minus_tail : ∀ r : R, ∀ c ∈ (toChars r).tail, c ≠ '-'
  /-- No lowercase ASCII letter appears anywhere. -/
  toChars_no_lower : ∀ r : R, ∀ c ∈ toChars r, ¬ isLowerAscii c

/-- A monomial: a nonzero coefficient of type `R` paired with a monic monomial.
    The coefficient is stored as a subtype `{c : R // c ≠ 0}` to ensure
    that zero monomials are unrepresentable. -/
structure Monomial (R : Type _) [Zero R] (σ : Type _) {n : ℕ} [LinearOrder σ] [Var σ n]
    (ord : MonomialOrder := .Degrevlex) where
  coeff : {c : R // c ≠ 0}
  monic : MonicMonomial σ ord

namespace Monomial

variable {R : Type _} [Zero R] {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n]
    {ord : MonomialOrder}

/-- The identity monomial with coefficient `1` and all exponents zero. -/
def one [One R] (h : (1 : R) ≠ 0) : Monomial R σ ord :=
  ⟨⟨1, h⟩, MonicMonomial.one⟩

/-- Convert a monomial to a list of characters.
    - If the monic part is `1`, return the coefficient representation.
    - If the coefficient is `1`, return the monic monomial representation.
    - Otherwise, join the two with `*`. -/
def toChars [DecidableEq R] [One R] [ParsableCoeff R] [pv : ParsableVar σ n]
    (m : Monomial R σ ord) : List Char :=
  if m.monic = 1 then
    ParsableCoeff.toChars m.coeff.val
  else if m.coeff.val = 1 then
    m.monic.toChars
  else
    ParsableCoeff.toChars m.coeff.val ++ ['*'] ++ m.monic.toChars

/-- Parse a character list into a `Monomial`.
    Uses the first character to distinguish:
    - Lowercase letter → starts a monic monomial (coefficient is implicitly `1`).
    - Otherwise → starts a coefficient. A `*` separator, if present, separates
      the coefficient from the monic monomial part. -/
def parse [DecidableEq R] [One R] [ParsableCoeff R] [pv : ParsableVar σ n]
    (cs : List Char) (h1 : (1 : R) ≠ 0) : Option (Monomial R σ ord) :=
  match cs with
  | [] => none
  | c :: _ =>
    if decide (isLowerAscii c) then
      -- Starts with lowercase: parse as monic monomial, coeff = 1
      (MonicMonomial.parse (ord := ord) cs).map (fun m => ⟨⟨1, h1⟩, m⟩)
    else
      -- Starts with non-lowercase: find first '*' to split coeff from monic
      let (coeffPart, rest) := cs.span (· != '*')
      match rest with
      | [] =>
        -- No '*': entire input is a coefficient, monic = 1
        (ParsableCoeff.parseChars coeffPart).bind (fun c =>
          if hc : c = 0 then none else some ⟨⟨c, hc⟩, 1⟩)
      | '*' :: monicPart =>
        -- Has '*': left is coefficient, right is monic monomial
        (ParsableCoeff.parseChars coeffPart).bind (fun c =>
          if hc : c = 0 then none
          else (MonicMonomial.parse (ord := ord) monicPart).map
            (fun m => ⟨⟨c, hc⟩, m⟩))
      | _ => none  -- unreachable: span stops at '*'

theorem toChars_ne_nil {R : Type _} [Zero R] {σ : Type _} {n : ℕ} [LinearOrder σ]
    [pv : ParsableVar σ n] {ord : MonomialOrder}
    [DecidableEq R] [One R] [ParsableCoeff R]
    (m : Monomial R σ ord) : m.toChars ≠ [] := by
  unfold toChars
  split_ifs with h1 h2
  · exact ParsableCoeff.toChars_nonempty _
  · exact MonicMonomial.toChars_ne_nil m.monic h1
  · intro h; simp at h

theorem plus_notin_toChars {R : Type _} [Zero R] {σ : Type _} {n : ℕ} [LinearOrder σ]
    [pv : ParsableVar σ n] {ord : MonomialOrder}
    [DecidableEq R] [One R] [ParsableCoeff R]
    (m : Monomial R σ ord) : '+' ∉ m.toChars := by
  unfold toChars
  split_ifs with h1 h2
  · intro h; exact ParsableCoeff.toChars_no_syntax _ _ h (Or.inl rfl)
  · exact MonicMonomial.plus_notin_toChars m.monic
  · intro h
    rw [List.mem_append, List.mem_append] at h
    rcases h with (h | h) | h
    · exact ParsableCoeff.toChars_no_syntax _ _ h (Or.inl rfl)
    · simp at h
    · exact MonicMonomial.plus_notin_toChars m.monic h

theorem minus_notin_tail_toChars {R : Type _} [Zero R] {σ : Type _} {n : ℕ} [LinearOrder σ]
    [pv : ParsableVar σ n] {ord : MonomialOrder}
    [DecidableEq R] [One R] [ParsableCoeff R]
    (m : Monomial R σ ord) : '-' ∉ m.toChars.tail := by
  unfold toChars
  split_ifs with h1 h2
  · exact fun h => ParsableCoeff.toChars_no_minus_tail _ _ h rfl
  · exact fun h => MonicMonomial.minus_notin_toChars m.monic (List.mem_of_mem_tail h)
  · have hne := ParsableCoeff.toChars_nonempty m.coeff.val
    rw [List.append_assoc, List.tail_append_of_ne_nil hne]
    intro h
    rw [List.mem_append] at h
    rcases h with h | h
    · exact ParsableCoeff.toChars_no_minus_tail _ _ h rfl
    · simp only [List.singleton_append, List.mem_cons] at h
      rcases h with h | h
      · exact absurd h (by decide)
      · exact MonicMonomial.minus_notin_toChars m.monic h

private lemma takeWhile_all (l : List Char) (h : ∀ x ∈ l, (x != '*') = true) :
    List.takeWhile (· != '*') l = l := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp [h a (List.mem_cons_self ..)]
    exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx))

private lemma dropWhile_all (l : List Char) (h : ∀ x ∈ l, (x != '*') = true) :
    List.dropWhile (· != '*') l = [] := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp [h a (List.mem_cons_self ..)]
    exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx))

private lemma coeffChars_bne_star {R : Type _} [ParsableCoeff R] (r : R) :
    ∀ x ∈ ParsableCoeff.toChars r, (x != '*') = true := by
  intro x hx; simp [bne_iff_ne]
  intro heq; exact ParsableCoeff.toChars_no_syntax _ _ (heq ▸ hx) (Or.inr (Or.inl rfl))

/-- Parse-toChars round-trip: `parse` correctly inverts `toChars`. -/
theorem parse_toChars {R : Type _} [Zero R] {σ : Type _} {n : ℕ} [LinearOrder σ]
    [pv : ParsableVar σ n] {ord : MonomialOrder}
    [DecidableEq R] [One R] [ParsableCoeff R]
    (m : Monomial R σ ord) (h1 : (1 : R) ≠ 0) :
    parse m.toChars h1 = some m := by
  unfold toChars parse
  simp only [List.span_eq_takeWhile_dropWhile]
  split_ifs with hmonic hcoeff
  · -- Case 1: monic = 1
    have hne := ParsableCoeff.toChars_nonempty m.coeff.val
    obtain ⟨c, t, hct⟩ := List.exists_cons_of_ne_nil hne
    rw [hct]
    have hnotlower : ¬ isLowerAscii c :=
      ParsableCoeff.toChars_no_lower _ _ (by rw [hct]; exact List.mem_cons_self ..)
    simp only [decide_eq_false hnotlower, Bool.false_eq_true, ↓reduceIte]
    have hall : ∀ x ∈ (c :: t), (x != '*') = true :=
      fun x hx => coeffChars_bne_star m.coeff.val x (by rw [hct]; exact hx)
    rw [takeWhile_all (c :: t) hall, dropWhile_all (c :: t) hall]
    simp [← hct, ParsableCoeff.parse_toChars, dif_neg m.coeff.property]
    show { coeff := m.coeff, monic := 1 } = m
    cases m; simp_all
  · -- Case 2: coeff = 1, monic ≠ 1
    have hne := MonicMonomial.toChars_ne_nil m.monic hmonic
    obtain ⟨c, t, hct⟩ := List.exists_cons_of_ne_nil hne
    rw [hct]
    have hlower : isLowerAscii c := by
      have h := MonicMonomial.toChars_head_isLowerAscii m.monic hmonic
      simp only [hct, List.head_cons] at h; exact h
    simp only [decide_eq_true hlower, ↓reduceIte]
    rw [← hct, MonicMonomial.parse_toChars]
    show Option.some { coeff := ⟨1, h1⟩, monic := m.monic } = some m
    congr 1; cases m; simp only [Monomial.mk.injEq]; exact ⟨Subtype.ext hcoeff.symm, trivial⟩
  · -- Case 3: coeff ≠ 1, monic ≠ 1
    have hne := ParsableCoeff.toChars_nonempty m.coeff.val
    obtain ⟨c, t, hct⟩ := List.exists_cons_of_ne_nil hne
    have hnotlower : ¬ isLowerAscii c :=
      ParsableCoeff.toChars_no_lower _ _ (by rw [hct]; exact List.mem_cons_self ..)
    rw [hct]
    have hc_bne : (c != '*') = true :=
      coeffChars_bne_star m.coeff.val c (by rw [hct]; exact List.mem_cons_self ..)
    have hall : ∀ x ∈ t, (x != '*') = true :=
      fun x hx => coeffChars_bne_star m.coeff.val x
        (by rw [hct]; exact List.mem_cons_of_mem _ hx)
    -- Pre-compute takeWhile/dropWhile on c :: t ++ ['*'] ++ monic.toChars
    have htw : List.takeWhile (· != '*') (c :: (t ++ ['*'] ++ m.monic.toChars)) = c :: t := by
      simp [hc_bne, List.takeWhile_append,
            takeWhile_all t hall]
    have hdw : List.dropWhile (· != '*') (c :: (t ++ ['*'] ++ m.monic.toChars)) =
        '*' :: m.monic.toChars := by
      simp [hc_bne, List.dropWhile_append,
            dropWhile_all t hall]
    simp only [List.cons_append, decide_eq_false hnotlower, Bool.false_eq_true, ↓reduceIte,
               htw, hdw]
    simp [← hct, ParsableCoeff.parse_toChars, dif_neg m.coeff.property,
          MonicMonomial.parse_toChars]

end Monomial

/-! ### ParsableCoeff instances -/

section ParsableCoeffInstances

private lemma tail_mem_of_drop {c : α} {l : List α} (h : c ∈ l.tail) : c ∈ l.drop 1 := by
  cases l <;> simp_all

private lemma natToChars_no_coeff_syntax (n : ℕ) (c : Char) (hc : c ∈ natToChars n) :
    ¬ isCoeffSyntaxChar c := by
  intro h; rcases h with rfl | rfl | rfl
  · exact not_mem_natToChars_of_not_digit '+' (by decide) n hc
  · exact not_mem_natToChars_of_not_digit '*' (by decide) n hc
  · exact not_mem_natToChars_of_not_digit '^' (by decide) n hc

private lemma intToChars_no_coeff_syntax (z : ℤ) (c : Char) (hc : c ∈ intToChars z) :
    ¬ isCoeffSyntaxChar c := by
  rw [intToChars_natAbs] at hc
  split at hc
  · simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · intro h
      rcases h with h | h | h <;> exact absurd h (by decide)
    · exact natToChars_no_coeff_syntax _ c hc
  · exact natToChars_no_coeff_syntax _ c hc

private lemma ratToChars_no_coeff_syntax (q : ℚ) (c : Char) (hc : c ∈ ratToChars q) :
    ¬ isCoeffSyntaxChar c := by
  simp only [ratToChars] at hc
  split at hc
  · exact intToChars_no_coeff_syntax _ c hc
  · simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with (hc | rfl) | hc
    · exact intToChars_no_coeff_syntax _ c hc
    · intro h
      rcases h with h | h | h <;> exact absurd h (by decide)
    · exact natToChars_no_coeff_syntax _ c hc

private lemma natToChars_no_lower (n : ℕ) (c : Char) (hc : c ∈ natToChars n) :
    ¬ isLowerAscii c := by
  have ⟨hge, hle⟩ := mem_natToChars_only_digits n c hc
  intro ⟨hlo, _⟩
  simp only [show ('0' : Char).toNat = 48 from by decide,
             show ('9' : Char).toNat = 57 from by decide,
             show ('a' : Char).toNat = 97 from by decide] at *
  omega

private lemma intToChars_no_lower (z : ℤ) (c : Char) (hc : c ∈ intToChars z) :
    ¬ isLowerAscii c := by
  rw [intToChars_natAbs] at hc
  split at hc
  · simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · intro ⟨h, _⟩; simp only [show ('-' : Char).toNat = 45 from by decide,
                              show ('a' : Char).toNat = 97 from by decide] at h; omega
    · exact natToChars_no_lower _ c hc
  · exact natToChars_no_lower _ c hc

private lemma ratToChars_no_lower (q : ℚ) (c : Char) (hc : c ∈ ratToChars q) :
    ¬ isLowerAscii c := by
  simp only [ratToChars] at hc
  split at hc
  · exact intToChars_no_lower _ c hc
  · simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with (hc | rfl) | hc
    · exact intToChars_no_lower _ c hc
    · intro ⟨h, _⟩; simp only [show ('/' : Char).toNat = 47 from by decide,
                              show ('a' : Char).toNat = 97 from by decide] at h; omega
    · exact natToChars_no_lower _ c hc

instance : ParsableCoeff ℕ where
  toChars := natToChars
  parseChars := parseNatChars
  parse_toChars := parseNatChars_natToChars
  toChars_nonempty := natToChars_ne_nil
  toChars_no_syntax := natToChars_no_coeff_syntax
  toChars_no_minus_tail := fun n _ hc heq =>
    not_mem_natToChars n (heq ▸ List.mem_of_mem_tail hc)
  toChars_no_lower := natToChars_no_lower

instance : ParsableCoeff ℤ where
  toChars := intToChars
  parseChars := parseIntChars
  parse_toChars := parseIntChars_intToChars
  toChars_nonempty := intToChars_ne_nil
  toChars_no_syntax := intToChars_no_coeff_syntax
  toChars_no_minus_tail := fun z _ hc heq =>
    not_mem_tail_intToChars z (heq ▸ tail_mem_of_drop hc)
  toChars_no_lower := intToChars_no_lower

instance : ParsableCoeff ℚ where
  toChars := ratToChars
  parseChars := parseRatChars
  parse_toChars := parseRatChars_ratToChars
  toChars_nonempty := ratToChars_ne_nil
  toChars_no_syntax := ratToChars_no_coeff_syntax
  toChars_no_minus_tail := fun q _ hc heq =>
    not_mem_tail_ratToChars q (heq ▸ tail_mem_of_drop hc)
  toChars_no_lower := ratToChars_no_lower

/-- Parse a character list as a `ZMod n` value: parse as ℕ, check `< n`, cast. -/
def parseZmodChars (m : ℕ) [NeZero m] (cs : List Char) : Option (ZMod m) :=
  (parseNatChars cs).bind (fun k => if k < m then some (k : ZMod m) else none)

private lemma parseZmodChars_zmodToChars {m : ℕ} [NeZero m] (c : ZMod m) :
    parseZmodChars m (zmodToChars c) = some c := by
  simp only [parseZmodChars, zmodToChars, parseNatChars_natToChars]
  simp only [Option.bind, if_pos (ZMod.val_lt c)]
  congr 1
  exact ZMod.natCast_zmod_val c

instance {m : ℕ} [NeZero m] : ParsableCoeff (ZMod m) where
  toChars := zmodToChars
  parseChars := parseZmodChars m
  parse_toChars := parseZmodChars_zmodToChars
  toChars_nonempty := zmodToChars_ne_nil
  toChars_no_syntax := fun c _ch hch => natToChars_no_coeff_syntax c.val _ch hch
  toChars_no_minus_tail := fun c _ch hch heq =>
    not_mem_natToChars c.val (heq ▸ List.mem_of_mem_tail hch)
  toChars_no_lower := fun c _ch hch => natToChars_no_lower c.val _ch hch

end ParsableCoeffInstances

section MonomialGuards

-- Use ℤ coefficients with AbcVar 3 variables: a, b, c
private def mkMon (c : ℤ) (hc : c ≠ 0) (v : Vector ℕ 3) : Monomial ℤ (AbcVar 3) :=
  ⟨⟨c, hc⟩, ⟨v⟩⟩

-- toChars: coefficient only (monic = 1)
#guard (mkMon 5 (by omega) (Vector.mk #[0, 0, 0] rfl)).toChars == "5".toList
#guard (mkMon (-3) (by omega) (Vector.mk #[0, 0, 0] rfl)).toChars == "-3".toList

-- toChars: monic only (coeff = 1)
#guard (mkMon 1 (by omega) (Vector.mk #[1, 0, 0] rfl)).toChars == "a".toList
#guard (mkMon 1 (by omega) (Vector.mk #[2, 1, 0] rfl)).toChars == "a^2*b".toList

-- toChars: coefficient * monic
#guard (mkMon 3 (by omega) (Vector.mk #[1, 0, 0] rfl)).toChars == "3*a".toList
#guard (mkMon (-2) (by omega) (Vector.mk #[1, 1, 0] rfl)).toChars == "-2*a*b".toList
#guard (mkMon 7 (by omega) (Vector.mk #[0, 0, 3] rfl)).toChars == "7*c^3".toList

-- parse round-trip: parse then toChars should give back the original string
#guard (Monomial.parse (R := ℤ) (σ := AbcVar 3) (ord := .Degrevlex) "5".toList (by omega)).map
  Monomial.toChars == some "5".toList
#guard (Monomial.parse (R := ℤ) (σ := AbcVar 3) (ord := .Degrevlex) "a".toList (by omega)).map
  Monomial.toChars == some "a".toList
#guard (Monomial.parse (R := ℤ) (σ := AbcVar 3) (ord := .Degrevlex) "3*a".toList (by omega)).map
  Monomial.toChars == some "3*a".toList
#guard (Monomial.parse (R := ℤ) (σ := AbcVar 3) (ord := .Degrevlex) "-2*a*b".toList (by omega)).map
  Monomial.toChars == some "-2*a*b".toList
#guard (Monomial.parse (R := ℤ) (σ := AbcVar 3) (ord := .Degrevlex) "a^2*b".toList (by omega)).map
  Monomial.toChars == some "a^2*b".toList

-- parse rejects invalid input
#guard (Monomial.parse (R := ℤ) (σ := AbcVar 3) (ord := .Degrevlex) "".toList (by omega)).map
  Monomial.toChars == (none : Option (List Char))
#guard (Monomial.parse (R := ℤ) (σ := AbcVar 3) (ord := .Degrevlex) "0".toList (by omega)).map
  Monomial.toChars == (none : Option (List Char))

end MonomialGuards

end Azurite
