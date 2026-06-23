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
  /-- An optional representation of `-1` in `R`, used to pretty-print monomials
      with coefficient `-1` as `-x` instead of `-1*x`. Set to `some ⟨-1, _, _⟩`
      for rings like `ℤ` or `ℚ` where `-1 ≠ 0` and `-1 ≠ 1`; leave as `none`
      for `ℕ` (where no such element exists) or for rings of characteristic 2
      where `-1 = 1` (rendered directly as `x`). The `c ≠ 0 ∧ c ≠ 1` constraint
      ensures the parser/printer can unambiguously recognize this special case:
      if `c = 0`, negation would produce the zero polynomial; if `c = 1`, it
      would clash with the positive-coefficient path. -/
  negOne : Option {c : R // c ≠ 0 ∧ c ≠ 1} := none
  /-- If `toChars r` starts with `-`, then the tail is nonempty and its head is
      a poly-syntax character (a digit). This ensures the parser can distinguish
      `-3*x` (coefficient) from `-x` (negOne). -/
  toChars_minus_next_syntax : ∀ r : R, ∀ t, toChars r = '-' :: t →
    ∃ c t', t = c :: t' ∧ isPolySyntaxChar c
  /-- The zero element is represented as the single character `'0'`. -/
  toChars_zero : toChars (0 : R) = ['0']
  /-- No `,` occurs in the representation (so coefficients can be used as
      `AzVector`/`AzMatrix` entries). -/
  toChars_no_comma : ∀ r : R, ',' ∉ toChars r
  /-- No `;` occurs in the representation (so coefficients can be used as
      `AzVector`/`AzMatrix` entries). -/
  toChars_no_semicolon : ∀ r : R, ';' ∉ toChars r

/-- Smart constructor for coefficient types whose representation consists
    entirely of ASCII digits (e.g. `ℕ`, `ZMod`). Automatically discharges all
    the "no special char" conditions that are vacuous for digit strings. -/
@[reducible] def ParsableCoeff.mkDigitOnly {R : Type _} [Semiring R] [NeZero (1 : R)]
    (toChars : R → List Char)
    (parseChars : List Char → Option R)
    (parse_toChars : ∀ r : R, parseChars (toChars r) = some r)
    (toChars_nonempty : ∀ r : R, toChars r ≠ [])
    (all_digits : ∀ r : R, ∀ c ∈ toChars r,
      c.toNat ≥ '0'.toNat ∧ c.toNat ≤ '9'.toNat)
    (toChars_zero : toChars (0 : R) = ['0']) : ParsableCoeff R where
  toChars := toChars
  parseChars := parseChars
  parse_toChars := parse_toChars
  toChars_nonempty := toChars_nonempty
  toChars_no_syntax := fun r c hc hsyn => by
    have ⟨h1, h2⟩ := all_digits r c hc
    rcases hsyn with rfl | rfl | rfl
    · exact absurd h1 (by decide)
    · exact absurd h1 (by decide)
    · exact absurd h2 (by decide)
  toChars_no_minus_tail := fun r c hc heq => by
    have : c.toNat ≥ '0'.toNat := (all_digits r c (List.mem_of_mem_tail hc)).1
    rw [heq] at this; exact absurd this (by decide)
  toChars_head_is_syntax := fun r c t hct =>
    Or.inl (all_digits r c (hct ▸ List.mem_cons_self ..))
  toChars_minus_next_syntax := fun r t hct => by
    have : ('-').toNat ≥ '0'.toNat :=
      (all_digits r '-' ((hct ▸ List.mem_cons_self ..) : '-' ∈ toChars r)).1
    exact absurd this (by decide)
  toChars_zero := toChars_zero
  toChars_no_comma := fun r hc => by
    have : (',').toNat ≥ '0'.toNat := (all_digits r ',' hc).1
    exact absurd this (by decide)
  toChars_no_semicolon := fun r hc => by
    have : (';').toNat ≤ '9'.toNat := (all_digits r ';' hc).2
    exact absurd this (by decide)

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

/- `ParsableCoeff` instances for the non-Az types `ℕ`, `ℤ`, `ℚ`, and `ZMod` have
   been removed: `AzPolynomial`/`AzMvPolynomial` should use the Az coefficient
   types (`AzNat`, `AzInt`, `AzRat`, `AzZMod`, `AzZModPow2`) instead of the
   GMP-backed `ℕ`/`ℤ`/`ℚ`/`ZMod`.  (`AzPolynomialQ` now serializes through
   `AzPolynomial AzRat` rather than `AzPolynomial ℚ`.)  The supporting
   digit/dash lemmas above are kept as shared scaffolding. -/

end ParsableCoeffInstances

end Azurite
