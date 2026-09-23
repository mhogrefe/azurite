/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  `ParsableElement AzNat` instance. Reuses the underlying decimal
  `natToChars` / `parseNatChars` from `Azurite.AzPolynomial.CoeffChars`
  and routes through the `Nat ↔ AzNat` round-trip.
-/
import Azurite.AzNat.Basic
import Azurite.AzNat.Conversion
import Azurite.AzNat.Equiv.Basic
import Azurite.AzVector.ParsableElement
import Azurite.AzPolynomial.StringLemmas

namespace Azurite

open AzPolynomial

instance : ParsableElement AzNat where
  toChars n := natToChars n.toNat
  parseChars cs := (parseNatChars cs).map AzNat.ofNat
  parse_toChars n := by
    show (parseNatChars (natToChars n.toNat)).map AzNat.ofNat = some n
    rw [parseNatChars_natToChars]
    show some (AzNat.ofNat n.toNat) = some n
    rw [AzNat.ofNat_toNat]
  toChars_no_comma n :=
    not_mem_natToChars_of_not_digit ',' (by decide) n.toNat
  toChars_no_semicolon n :=
    not_mem_natToChars_of_not_digit ';' (by decide) n.toNat

end Azurite
