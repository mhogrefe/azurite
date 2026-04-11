/-
  `ParsableCoeff` class + canonical instances (`ℕ`/`ℤ`/`ℚ`/`ZMod`).
-/
import Azurite.AzMvPolynomial.Var
import Azurite.AzPolynomial.StringLemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.List.TakeWhile

namespace Azurite
open AzPolynomial

/-- A character used in polynomial syntax that must not appear in coefficient
    representations: `+`, `*`, `^`. (Digits and `-` are allowed.) -/
def isCoeffSyntaxChar (c : Char) : Prop :=
  c = '+' ∨ c = '*' ∨ c = '^'

/-- Typeclass for coefficient types that can be serialized/deserialized as character
    sequences. Unlike `ParsableVar`, this does not extend `Var`, and `-` is permitted
    as the first character of the representation (to support negative coefficients). -/
class ParsableCoeff (R : Type _) [Semiring R] [NeZero (1 : R)] where
  toChars : R → List Char
  parseChars : List Char → Option R
  parse_toChars : ∀ r : R, parseChars (toChars r) = some r
  toChars_nonempty : ∀ r : R, toChars r ≠ []
  /-- No coefficient-syntax character (`+`, `*`, `^`) occurs anywhere. -/
  toChars_no_syntax : ∀ r : R, ∀ c ∈ toChars r, ¬ isCoeffSyntaxChar c
  /-- `-` may only occur as the very first character. -/
  toChars_no_minus_tail : ∀ r : R, ∀ c ∈ (toChars r).tail, c ≠ '-'
  /-- The first character is a poly-syntax character (digit or `-`). -/
  toChars_head_is_syntax : ∀ r : R, ∀ c t, toChars r = c :: t → isPolySyntaxChar c
  /-- An optional representation of `-1`, used for displaying `-x` instead of `-1*x`. -/
  negOne : Option {c : R // c ≠ 0 ∧ c ≠ 1} := none
  /-- If `toChars r` starts with `-`, then the tail is nonempty and its head is
      a poly-syntax character (a digit). This ensures the parser can distinguish
      `-3*x` (coefficient) from `-x` (negOne). -/
  toChars_minus_next_syntax : ∀ r : R, ∀ t, toChars r = '-' :: t →
    ∃ c t', t = c :: t' ∧ isPolySyntaxChar c

namespace Monomial

lemma coeffChars_bne_star {R : Type _} [Semiring R] [NeZero (1 : R)] [ParsableCoeff R] (r : R) :
    ∀ x ∈ ParsableCoeff.toChars r, (x != '*') = true := by
  intro x hx; simp [bne_iff_ne]
  intro heq; exact ParsableCoeff.toChars_no_syntax _ _ (heq ▸ hx) (Or.inr (Or.inl rfl))

end Monomial

/-! ### ParsableCoeff instances -/

section ParsableCoeffInstances

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

private lemma natToChars_head_is_syntax (n : ℕ) :
    ∀ c t, natToChars n = c :: t → isPolySyntaxChar c := by
  intro c t hct
  have hc_mem : c ∈ natToChars n := hct ▸ List.mem_cons_self ..
  have ⟨hge, hle⟩ := mem_natToChars_only_digits n c hc_mem
  left; exact ⟨hge, hle⟩

private lemma intToChars_head_is_syntax (z : ℤ) :
    ∀ c t, intToChars z = c :: t → isPolySyntaxChar c := by
  intro c t hct
  have hc_mem : c ∈ intToChars z := hct ▸ List.mem_cons_self ..
  rcases mem_intToChars_only_digits_or_dash z c hc_mem with hdash | hdig
  · rw [hdash]; exact Or.inr (Or.inr (Or.inl rfl))
  · left; exact hdig

private lemma ratToChars_head_is_syntax (q : ℚ) :
    ∀ c t, ratToChars q = c :: t → isPolySyntaxChar c := by
  intro c t hct
  simp only [ratToChars] at hct
  split at hct
  · exact intToChars_head_is_syntax q.num c t hct
  · obtain ⟨c', rest', hcr'⟩ := List.exists_cons_of_ne_nil (intToChars_ne_nil q.num)
    rw [hcr', List.cons_append, List.cons_append] at hct
    obtain ⟨rfl, _⟩ := List.cons.inj hct
    exact intToChars_head_is_syntax q.num c' rest' hcr'

private lemma intToChars_minus_next_syntax (z : ℤ) :
    ∀ t, intToChars z = '-' :: t →
    ∃ c t', t = c :: t' ∧ isPolySyntaxChar c := by
  intro t hct
  have heq := intToChars_natAbs z
  rw [hct] at heq
  split_ifs at heq with hz
  · have ht : t = natToChars z.natAbs := (List.cons.inj heq).2
    obtain ⟨c, t', hct'⟩ := List.exists_cons_of_ne_nil (natToChars_ne_nil z.natAbs)
    refine ⟨c, t', ht.trans hct', ?_⟩
    have hc_mem : c ∈ natToChars z.natAbs := hct' ▸ List.mem_cons_self ..
    have ⟨hge, hle⟩ := mem_natToChars_only_digits z.natAbs c hc_mem
    left; exact ⟨hge, hle⟩
  · exact absurd ((heq ▸ List.mem_cons_self ..) : '-' ∈ natToChars z.natAbs)
      (not_mem_natToChars _)

private lemma ratToChars_minus_next_syntax (q : ℚ) :
    ∀ t, ratToChars q = '-' :: t →
    ∃ c t', t = c :: t' ∧ isPolySyntaxChar c := by
  intro t hct
  simp only [ratToChars] at hct
  split at hct
  · exact intToChars_minus_next_syntax q.num t hct
  · -- ratToChars q = intToChars q.num ++ ['/'] ++ natToChars q.den
    -- and the whole thing equals '-' :: t
    obtain ⟨cn, tn, hctn⟩ := List.exists_cons_of_ne_nil (intToChars_ne_nil q.num)
    rw [hctn, List.cons_append, List.cons_append] at hct
    obtain ⟨rfl, htail⟩ := List.cons.inj hct
    -- Now cn = '-', so intToChars q.num = '-' :: tn
    -- Apply intToChars_minus_next_syntax to q.num
    obtain ⟨c', tn', hteq, hs⟩ := intToChars_minus_next_syntax q.num tn hctn
    -- tn = c' :: tn', so t = c' :: tn' ++ ['/'] ++ natToChars q.den
    refine ⟨c', tn' ++ ['/'] ++ natToChars q.den, ?_, hs⟩
    rw [← htail, hteq, List.cons_append, List.cons_append]

instance : ParsableCoeff ℕ where
  toChars := natToChars
  parseChars := parseNatChars
  parse_toChars := parseNatChars_natToChars
  toChars_nonempty := natToChars_ne_nil
  toChars_no_syntax := natToChars_no_coeff_syntax
  toChars_no_minus_tail := fun n _ hc heq =>
    not_mem_natToChars n (heq ▸ List.mem_of_mem_tail hc)
  toChars_head_is_syntax := natToChars_head_is_syntax
  toChars_minus_next_syntax := fun n t hct => by
    exact absurd ((hct ▸ List.mem_cons_self ..) : '-' ∈ natToChars n)
      (not_mem_natToChars n)

instance : ParsableCoeff ℤ where
  toChars := intToChars
  parseChars := parseIntChars
  parse_toChars := parseIntChars_intToChars
  toChars_nonempty := intToChars_ne_nil
  toChars_no_syntax := intToChars_no_coeff_syntax
  toChars_no_minus_tail := fun z _ hc heq => by
    apply not_mem_tail_intToChars z
    rw [List.drop_one]
    exact heq ▸ hc
  toChars_head_is_syntax := intToChars_head_is_syntax
  negOne := some ⟨-1, by omega, by omega⟩
  toChars_minus_next_syntax := intToChars_minus_next_syntax

instance : ParsableCoeff ℚ where
  toChars := ratToChars
  parseChars := parseRatChars
  parse_toChars := parseRatChars_ratToChars
  toChars_nonempty := ratToChars_ne_nil
  toChars_no_syntax := ratToChars_no_coeff_syntax
  toChars_no_minus_tail := fun q _ hc heq => by
    apply not_mem_tail_ratToChars q
    rw [List.drop_one]
    exact heq ▸ hc
  toChars_head_is_syntax := ratToChars_head_is_syntax
  negOne := some ⟨-1, by decide, by decide⟩
  toChars_minus_next_syntax := ratToChars_minus_next_syntax

/-- Parse a character list as a `ZMod n` value: parse as ℕ (possibly with a
    leading `-`), check `< n`, cast (and negate if there was a leading `-`). -/
def parseZmodChars (m : ℕ) [NeZero m] (cs : List Char) : Option (ZMod m) :=
  match cs with
  | '-' :: rest =>
    (parseNatChars rest).bind
      (fun k => if k < m then some (-(k : ZMod m)) else none)
  | _ =>
    (parseNatChars cs).bind
      (fun k => if k < m then some (k : ZMod m) else none)

private lemma parseZmodChars_zmodToChars {m : ℕ} [NeZero m] (c : ZMod m) :
    parseZmodChars m (zmodToChars c) = some c := by
  have hne : ∀ rest, zmodToChars c ≠ '-' :: rest := by
    intro rest hr
    exact not_mem_natToChars c.val
      ((show zmodToChars c = natToChars c.val from rfl) ▸ hr ▸ List.mem_cons_self ..)
  unfold parseZmodChars
  split
  · rename_i rest heq
    exact absurd heq (hne rest)
  · show ((parseNatChars (natToChars c.val)).bind _) = _
    rw [parseNatChars_natToChars]
    simp only [Option.bind, if_pos (ZMod.val_lt c)]
    congr 1
    exact ZMod.natCast_zmod_val c

instance {m : ℕ} [NeZero m] [Fact (1 < m)] : ParsableCoeff (ZMod m) where
  toChars := zmodToChars
  parseChars := parseZmodChars m
  parse_toChars := parseZmodChars_zmodToChars
  toChars_nonempty := zmodToChars_ne_nil
  toChars_no_syntax := fun c _ch hch => natToChars_no_coeff_syntax c.val _ch hch
  toChars_no_minus_tail := fun c _ch hch heq =>
    not_mem_natToChars c.val (heq ▸ List.mem_of_mem_tail hch)
  toChars_head_is_syntax := fun c => natToChars_head_is_syntax c.val
  negOne :=
    if h0 : ((-1 : ZMod m) = 0) then none
    else if h1 : ((-1 : ZMod m) = 1) then none
    else some ⟨-1, h0, h1⟩
  toChars_minus_next_syntax := fun c t hct => by
    simp only [zmodToChars] at hct
    exact absurd ((hct ▸ List.mem_cons_self ..) : '-' ∈ natToChars c.val)
      (not_mem_natToChars _)

end ParsableCoeffInstances

end Azurite
