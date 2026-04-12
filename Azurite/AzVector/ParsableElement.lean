/-
  `ParsableElement` class + canonical instances (`ℕ`/`ℤ`/`ℚ`/`ZMod`).

  Used to serialize/deserialize entries of `AzVector` and `AzMatrix`.
  The serialization format for containers uses `,` and `;` as delimiters,
  so element representations must not contain either character, and must
  be nonempty (so the parser can reliably detect element boundaries).
-/
import Azurite.AzPolynomial.StringLemmas

namespace Azurite

open AzPolynomial

/-- Typeclass for element types that can be serialized/deserialized as character
    sequences, suitable for use as entries in `AzVector` / `AzMatrix` string
    representations. The representation must be nonempty, and must not contain
    `,` or `;`, which are reserved as container delimiters. -/
class ParsableElement (R : Type _) where
  toChars : R → List Char
  parseChars : List Char → Option R
  parse_toChars : ∀ r : R, parseChars (toChars r) = some r
  /-- No `,` occurs in the representation. -/
  toChars_no_comma : ∀ r : R, ',' ∉ toChars r
  /-- No `;` occurs in the representation. -/
  toChars_no_semicolon : ∀ r : R, ';' ∉ toChars r

namespace ParsableElement

variable {R : Type _} [ParsableElement R]

lemma not_mem_toChars_comma (r : R) : ',' ∉ toChars r := toChars_no_comma r
lemma not_mem_toChars_semicolon (r : R) : ';' ∉ toChars r := toChars_no_semicolon r

end ParsableElement

/-! ### ParsableElement instances -/

section ParsableElementInstances

instance : ParsableElement ℕ where
  toChars := natToChars
  parseChars := parseNatChars
  parse_toChars := parseNatChars_natToChars
  toChars_no_comma n := not_mem_natToChars_of_not_digit ',' (by decide) n
  toChars_no_semicolon n := not_mem_natToChars_of_not_digit ';' (by decide) n

instance : ParsableElement ℤ where
  toChars := intToChars
  parseChars := parseIntChars
  parse_toChars := parseIntChars_intToChars
  toChars_no_comma z hc := by
    rcases mem_intToChars_only_digits_or_dash z ',' hc with h | ⟨h1, _⟩
    · exact absurd h (by decide)
    · exact absurd h1 (by decide)
  toChars_no_semicolon z hc := by
    rcases mem_intToChars_only_digits_or_dash z ';' hc with h | ⟨_, h2⟩
    · exact absurd h (by decide)
    · exact absurd h2 (by decide)

instance : ParsableElement ℚ where
  toChars := ratToChars
  parseChars := parseRatChars
  parse_toChars := parseRatChars_ratToChars
  toChars_no_comma q hc := by
    rcases mem_ratToChars_only_digits_or_dash_or_slash q ',' hc with h | h | ⟨h1, _⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h1 (by decide)
  toChars_no_semicolon q hc := by
    rcases mem_ratToChars_only_digits_or_dash_or_slash q ';' hc with h | h | ⟨_, h2⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h2 (by decide)

instance {m : ℕ} [NeZero m] : ParsableElement (ZMod m) where
  toChars := zmodToChars
  parseChars := fun cs => (parseNatChars cs).bind
    (fun k => if k < m then some (k : ZMod m) else none)
  parse_toChars c := by
    show ((parseNatChars (natToChars c.val)).bind _) = _
    rw [parseNatChars_natToChars]
    simp only [Option.bind, if_pos (ZMod.val_lt c)]
    congr 1
    exact ZMod.natCast_zmod_val c
  toChars_no_comma c := not_mem_natToChars_of_not_digit ',' (by decide) c.val
  toChars_no_semicolon c := not_mem_natToChars_of_not_digit ';' (by decide) c.val

end ParsableElementInstances

end Azurite
