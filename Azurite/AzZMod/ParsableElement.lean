/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  `ParsableElement (AzZMod m)` instance, plus the shared char-list facade
  (`AzZMod.toChars` / `AzZMod.parseChars`) over the limb-level decimal
  `AzZMod.toString` / `AzZMod.parse` pipeline.  The representation is the decimal
  of the canonical residue `val`, so it is all digits — the same facade feeds the
  `ParsableCoeff` instance.  Mirrors `AzZModPow2/ParsableElement.lean`, with the
  `parse` round-trip reused from `Equiv/Parse.lean` and `NeZero m.toNat` carried
  wherever `parse` is involved.
-/
import Azurite.AzZMod.Equiv.Parse
import Azurite.AzVector.ParsableElement
import Azurite.AzNat.Equiv.ToStringBase

namespace Azurite

open AzPolynomial

namespace AzZMod

variable {m : AzNat}

/-! ### Char-list facade over `AzZMod.toString` / `AzZMod.parse` -/

/-- `AzZMod.toChars a := (AzZMod.toString a).toList`. -/
def toChars (a : AzZMod m) : List Char := (AzZMod.toString a).toList

/-- `AzZMod.parseChars cs := AzZMod.parse (String.ofList cs)`. -/
def parseChars [NeZero m.toNat] (cs : List Char) : Option (AzZMod m) :=
  AzZMod.parse (String.ofList cs)

theorem parseChars_toChars [NeZero m.toNat] (a : AzZMod m) :
    AzZMod.parseChars (AzZMod.toChars a) = some a := by
  unfold parseChars toChars
  rw [show String.ofList (AzZMod.toString a).toList = AzZMod.toString a from by
    apply String.toList_inj.mp; rw [String.toList_ofList]]
  exact parse_toString a

/-- `AzZMod.toChars a` is the decimal of `val`, hence `AzNat.toString val`'s chars. -/
theorem toChars_eq (a : AzZMod m) : AzZMod.toChars a = (AzNat.toString a.val).toList := rfl

/-- Every character of `AzZMod.toChars a` is a decimal digit `'0'`–`'9'`. -/
theorem mem_toChars_digit (a : AzZMod m) (c : Char) (hc : c ∈ AzZMod.toChars a) :
    '0'.toNat ≤ c.toNat ∧ c.toNat ≤ '9'.toNat :=
  AzNat.toString_char_digit a.val c hc

theorem toChars_ne_nil (a : AzZMod m) : AzZMod.toChars a ≠ [] :=
  AzNat.toString_ne_empty a.val

/-- The zero residue renders as the single character `'0'`. -/
theorem toChars_zero [NeZero m.toNat] : AzZMod.toChars (0 : AzZMod m) = ['0'] := by
  rw [toChars_eq, val_zero]; exact AzNat.toString_zero

end AzZMod

/-! ### `ParsableElement` instance -/

instance {m : AzNat} [NeZero m.toNat] : ParsableElement (AzZMod m) where
  toChars := AzZMod.toChars
  parseChars := AzZMod.parseChars
  parse_toChars := AzZMod.parseChars_toChars
  toChars_no_comma a hc := absurd (AzZMod.mem_toChars_digit a ',' hc).1 (by decide)
  toChars_no_semicolon a hc := absurd (AzZMod.mem_toChars_digit a ';' hc).2 (by decide)

end Azurite

section Tests
open Azurite Azurite.AzZMod

-- The facade renders the canonical residue as decimal and round-trips.
-- `19 mod 7 = 5`; `456 < 1000`.
#guard (String.ofList (ParsableElement.toChars (AzZMod.ofNat (AzNat.ofNat 7) 19))) == "5"
#guard (String.ofList (ParsableElement.toChars (AzZMod.ofNat (AzNat.ofNat 1000) 456))) == "456"
#guard ((ParsableElement.parseChars (ParsableElement.toChars (AzZMod.ofNat (AzNat.ofNat 1000) 456))
  : Option (AzZMod (AzNat.ofNat 1000))).map AzZMod.val) == some (AzZMod.ofNat (AzNat.ofNat 1000) 456).val
end Tests
