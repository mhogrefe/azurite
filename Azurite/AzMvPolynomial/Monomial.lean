/-
  Monomials (coefficient × monic monomial) for multivariate polynomials.
-/
import Azurite.AzMvPolynomial.MonicMonomial
import Azurite.AzPolynomial.StringLemmas
import Mathlib.Data.ZMod.Basic

namespace Azurite
open AzPolynomial

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
structure Monomial (R : Type _) [Zero R] (σ : Type _) (n : ℕ) [LinearOrder σ] [Var σ n]
    (ord : MonomialOrder) where
  coeff : {c : R // c ≠ 0}
  monic : MonicMonomial σ n ord

namespace Monomial

variable {R : Type _} [Zero R] {σ : Type _} {n : ℕ} [LinearOrder σ] [Var σ n]
    {ord : MonomialOrder}

/-- The identity monomial with coefficient `1` and all exponents zero. -/
def one [One R] (h : (1 : R) ≠ 0) : Monomial R σ n ord :=
  ⟨⟨1, h⟩, MonicMonomial.one⟩

/-- Convert a monomial to a list of characters.
    - If the monic part is `1`, return the coefficient representation.
    - If the coefficient is `1`, return the monic monomial representation.
    - Otherwise, join the two with `*`. -/
def toChars [DecidableEq R] [One R] [ParsableCoeff R] [pv : ParsableVar σ n]
    (m : Monomial R σ n ord) : List Char :=
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
    (cs : List Char) (h1 : (1 : R) ≠ 0) : Option (Monomial R σ n ord) :=
  match cs with
  | [] => none
  | c :: _ =>
    if c.isAlpha && c.isLower then
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

end Azurite
