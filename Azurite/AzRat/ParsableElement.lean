/-
  `ParsableElement AzRat` instance, so `AzRat` works as an entry type for
  `AzVector` / `AzMatrix` string conversion. Routes through the limb-level
  `AzRat.toChars` / `AzRat.parse` pipeline; the char-set facts are shared
  with the `ParsableCoeff AzRat` instance.
-/
import Azurite.AzMatrix.Mul
import Azurite.AzMatrix.Parse
import Azurite.AzMvPolynomial.ParsableCoeff.AzRat
import Azurite.AzVector.ParsableElement

namespace Azurite

instance : ParsableElement AzRat where
  toChars := AzRat.toChars
  parseChars := AzRat.parseChars
  parse_toChars := AzRat.parseChars_toChars
  toChars_no_comma := AzRat.toChars_no_comma
  toChars_no_semicolon := AzRat.toChars_no_semicolon

/-! ### Demonstration: `AzMatrix` over `AzRat`

    Two `2 × 2` matrices with `AzRat` entries are parsed from strings,
    multiplied, and the product is serialized back to a string. Both
    `parseStr` and `toString` on `AzMatrix` delegate to the `AzRat`
    instance for individual entries. -/
section MatrixDemo

private def demoA : AzMatrix AzRat 2 2 :=
  (AzMatrix.parseStr "[1/2, -1/3; 0, 2]").getD (AzMatrix.ofFn (fun _ _ => 0))

private def demoB : AzMatrix AzRat 2 2 :=
  (AzMatrix.parseStr "[6, 0; 3/2, 1]").getD (AzMatrix.ofFn (fun _ _ => 0))

#guard toString (demoA * demoB) = "[5/2, -1/3; 3, 2]"

end MatrixDemo

end Azurite
