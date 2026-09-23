/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  `ParsableElement (AzZModPow2 k)` instance, plus the shared char-list facade
  (`AzZModPow2.toChars` / `AzZModPow2.parseChars`) over the limb-level decimal
  `AzZModPow2.toString` / `AzZModPow2.parse` pipeline.  The representation is the
  decimal of the canonical residue `val`, so it is all digits — the same facade
  feeds the `ParsableCoeff` instance.
-/
import Azurite.AzZModPow2.ToString
import Azurite.AzZModPow2.Parse
import Azurite.AzVector.ParsableElement
import Azurite.AzNat.Equiv.ToStringBase
import Azurite.AzNat.Equiv.ParseBase

namespace Azurite

open AzPolynomial

namespace AzZModPow2

variable {k : Nat}

/-! ### Char-list facade over `AzZModPow2.toString` / `AzZModPow2.parse` -/

/-- `AzZModPow2.toChars a := (AzZModPow2.toString a).toList`. -/
def toChars (a : AzZModPow2 k) : List Char := (AzZModPow2.toString a).toList

/-- `AzZModPow2.parseChars cs := AzZModPow2.parse (String.ofList cs)`. -/
def parseChars (cs : List Char) : Option (AzZModPow2 k) := AzZModPow2.parse (String.ofList cs)

/-- The decimal round-trip: parsing the rendered residue recovers it. The masking
in `parse`/`ofAzNat` is the identity because `val` is already canonical. -/
theorem parse_toString (a : AzZModPow2 k) :
    AzZModPow2.parse (AzZModPow2.toString a) = some a := by
  unfold AzZModPow2.parse AzZModPow2.toString
  rw [AzNat.parse_toString]
  show some (ofAzNat k a.val) = some a
  rw [ofAzNat_val]

theorem parseChars_toChars (a : AzZModPow2 k) :
    AzZModPow2.parseChars (AzZModPow2.toChars a) = some a := by
  unfold parseChars toChars
  rw [show String.ofList (AzZModPow2.toString a).toList = AzZModPow2.toString a from by
    apply String.toList_inj.mp; rw [String.toList_ofList]]
  exact parse_toString a

/-- `AzZModPow2.toChars a` is the decimal of `val`, hence `AzNat.toString val`'s chars. -/
theorem toChars_eq (a : AzZModPow2 k) : AzZModPow2.toChars a = (AzNat.toString a.val).toList := rfl

/-- Every character of `AzZModPow2.toChars a` is a decimal digit `'0'`–`'9'`. -/
theorem mem_toChars_digit (a : AzZModPow2 k) (c : Char) (hc : c ∈ AzZModPow2.toChars a) :
    '0'.toNat ≤ c.toNat ∧ c.toNat ≤ '9'.toNat :=
  AzNat.toString_char_digit a.val c hc

theorem toChars_ne_nil (a : AzZModPow2 k) : AzZModPow2.toChars a ≠ [] :=
  AzNat.toString_ne_empty a.val

/-- The zero residue renders as the single character `'0'`. -/
theorem toChars_zero : AzZModPow2.toChars (0 : AzZModPow2 k) = ['0'] := by
  rw [toChars_eq, val_zero]; exact AzNat.toString_zero

end AzZModPow2

/-! ### `ParsableElement` instance -/

instance {k : Nat} : ParsableElement (AzZModPow2 k) where
  toChars := AzZModPow2.toChars
  parseChars := AzZModPow2.parseChars
  parse_toChars := AzZModPow2.parseChars_toChars
  toChars_no_comma a hc := absurd (AzZModPow2.mem_toChars_digit a ',' hc).1 (by decide)
  toChars_no_semicolon a hc := absurd (AzZModPow2.mem_toChars_digit a ';' hc).2 (by decide)

end Azurite

section Tests
open Azurite Azurite.AzZModPow2

-- The facade renders the canonical residue as decimal and round-trips.
-- `19 mod 16 = 3` in `ℤ/16`; `200 < 256` in `ℤ/256`.
#guard (String.ofList (ParsableElement.toChars (AzZModPow2.ofNat 4 19))) == "3"
#guard (String.ofList (ParsableElement.toChars (AzZModPow2.ofNat 8 200))) == "200"
#guard ((ParsableElement.parseChars (ParsableElement.toChars (AzZModPow2.ofNat 8 200))
  : Option (AzZModPow2 8)).map AzZModPow2.val) == some (AzZModPow2.ofNat 8 200).val
end Tests
