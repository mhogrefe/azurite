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

/- `ParsableElement` instances for the non-Az types `ℕ`, `ℤ`, `ℚ`, and `ZMod`
   have been removed: `AzVector`/`AzMatrix` should use the Az element types
   (`AzNat`, `AzInt`, `AzRat`, `AzZMod`, `AzZModPow2`) instead of the GMP-backed
   `ℕ`/`ℤ`/`ℚ`/`ZMod`. -/

end ParsableElementInstances

end Azurite
