import Azurite.AzRat.Basic
import Azurite.AzInt.ToString

/-!
# Rendering `AzRat`s as strings

`AzRat.toChars`/`AzRat.toString` produce `"0"`, `"4"`, `"1/3"`, `"-1/3"`: the sign rides
on the numerator, and integers (`den = 1`) print without the `"/den"` suffix. Since an
`AzRat` is always reduced, the output is canonical — `parse` (in `Azurite/AzRat/Parse.lean`)
round-trips it exactly (`parse_toString` in `Azurite/AzRat/Equiv/Parse.lean`).
-/

namespace Azurite.AzRat

/-- The signed numerator of an `AzRat`, as an `AzInt` (the denominator forgotten). -/
def numInt (q : AzRat) : AzInt :=
  { sign := q.sign, abs := q.num, zero_sign := q.zero_sign }

/-- The decimal characters of an `AzRat`: signed numerator, then `'/'` and the
denominator unless the denominator is `1`. -/
def toChars (q : AzRat) : List Char :=
  if q.den = 1 then (AzInt.toString q.numInt).toList
  else (AzInt.toString q.numInt).toList ++ '/' :: (AzNat.toString q.den).toList

/-- Convert an `AzRat` to its decimal `String` representation: `"0"`, `"4"`, `"1/3"`,
`"-1/3"`. -/
def toString (q : AzRat) : String :=
  String.ofList q.toChars

instance : ToString AzRat where
  toString := AzRat.toString

end Azurite.AzRat
