/-
  `ParsableElement AzRat` instance, so `AzRat` works as an entry type for
  `AzVector` / `AzMatrix` string conversion. Routes through the limb-level
  `AzRat.toChars` / `AzRat.parse` pipeline; the char-set facts are shared
  with the `ParsableCoeff AzRat` instance.
-/
import Azurite.AzMvPolynomial.ParsableCoeff.AzRat
import Azurite.AzVector.ParsableElement

namespace Azurite

instance : ParsableElement AzRat where
  toChars := AzRat.toChars
  parseChars := AzRat.parseChars
  parse_toChars := AzRat.parseChars_toChars
  toChars_no_comma := AzRat.toChars_no_comma
  toChars_no_semicolon := AzRat.toChars_no_semicolon

end Azurite
