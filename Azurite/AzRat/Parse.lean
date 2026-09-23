/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzRat.Construct
import Azurite.AzRat.Conversion
import Azurite.AzRat.ToString
import Azurite.AzInt.Parse

/-!
# Parsing `AzRat`s from strings

`AzRat.parse` accepts `"num"`, `"-num"`, `"num/den"`, and `"-num/den"`. It is
permissive where harmless:

* the fraction need not be reduced — `"2/4"` parses to `1/2`;
* a zero numerator with any denominator parses to `0` — `"0/7"`;
* a zero denominator follows the `mkRat` convention — `"5/0"` parses to `0`.

It rejects what would be ambiguous or non-canonical at the structural level: the
denominator must be a bare natural (a `'-'` after the slash is `none`; note that a
literal `'/'` followed by `'-'` cannot even be written in this comment, since that
two-character sequence opens a nested block comment), there is no negative zero
(`"-0"` is `none`, matching `AzInt.parse`), and a second slash fails the denominator
parse (`"1/2"` followed by `"/3"` is `none`).
-/

namespace Azurite.AzRat

/-- Split a character list at the first `'/'`: everything before it, and (if a `'/'`
was found) everything after it. -/
def splitAtSlash : List Char → List Char × Option (List Char)
  | [] => ([], none)
  | c :: cs =>
    if c = '/' then ([], some cs)
    else
      let (pre, post) := splitAtSlash cs
      (c :: pre, post)

/-- Parse a `String` to `Option AzRat`. See the module docstring for the accepted
grammar; the numerator is parsed via `AzInt.parse` and the denominator via
`AzNat.parse`, and the result is reduced by `ofSignAzNats`. -/
def parse (s : String) : Option AzRat :=
  match splitAtSlash s.toList with
  | (numChars, none) =>
    (AzInt.parse (String.ofList numChars)).map AzInt.toAzRat
  | (numChars, some denChars) =>
    match AzInt.parse (String.ofList numChars), AzNat.parse (String.ofList denChars) with
    | some z, some d => some (ofSignAzNats z.sign z.abs d)
    | _, _ => none

end Azurite.AzRat

namespace Azurite

-- Sanity checks.

#guard AzRat.parse "0" = some 0
#guard (AzRat.parse "4").isSome
#guard (AzRat.toString <$> AzRat.parse "4") = some "4"
#guard (AzRat.toString <$> AzRat.parse "1/3") = some "1/3"
#guard (AzRat.toString <$> AzRat.parse "-1/3") = some "-1/3"
#guard (AzRat.toString <$> AzRat.parse "2/4") = some "1/2"   -- permissive: reduces
#guard (AzRat.toString <$> AzRat.parse "0/7") = some "0"     -- permissive: canonicalizes zero
#guard AzRat.parse "5/0" = some 0                            -- mkRat convention
#guard AzRat.parse "1/-2" = none
#guard AzRat.parse "-0" = none
#guard AzRat.parse "-0/3" = none
#guard AzRat.parse "" = none
#guard AzRat.parse "1/" = none
#guard AzRat.parse "/3" = none
#guard AzRat.parse "1/2/3" = none

end Azurite
