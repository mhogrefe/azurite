/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  `ParsableElement AzInt` instance. Reuses the underlying signed decimal
  `intToChars` / `parseIntChars` from `Azurite.AzPolynomial.CoeffChars` and
  routes through the `Int ↔ AzInt` round-trip.
-/
import Azurite.AzInt.Basic
import Azurite.AzInt.Conversion
import Azurite.AzInt.Equiv.Basic
import Azurite.AzVector.ParsableElement
import Azurite.AzPolynomial.StringLemmas

namespace Azurite

open AzPolynomial

instance : ParsableElement AzInt where
  toChars z := intToChars z.toInt
  parseChars cs := (parseIntChars cs).map AzInt.ofInt
  parse_toChars z := by
    show (parseIntChars (intToChars z.toInt)).map AzInt.ofInt = some z
    rw [parseIntChars_intToChars]
    show some (AzInt.ofInt z.toInt) = some z
    rw [AzInt.ofInt_toInt]
  toChars_no_comma z hc := by
    rcases mem_intToChars_only_digits_or_dash z.toInt ',' hc with h | ⟨h1, _⟩
    · exact absurd h (by decide)
    · exact absurd h1 (by decide)
  toChars_no_semicolon z hc := by
    rcases mem_intToChars_only_digits_or_dash z.toInt ';' hc with h | ⟨_, h2⟩
    · exact absurd h (by decide)
    · exact absurd h2 (by decide)

end Azurite
