/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  `ParsableCoeff AzNat` instance: routes through the limb-level
  `AzNat.toString` / `AzNat.parse` pipeline.
-/
import Azurite.AzMvPolynomial.ParsableCoeff
import Azurite.AzNat.Equiv.ParseBase
import Azurite.AzNat.Instances

namespace Azurite

open AzPolynomial

/-! ### Char-list facade over `AzNat.toString` / `AzNat.parse` -/

/-- `AzNat.toChars n := (AzNat.toString n).toList`. -/
def AzNat.toChars (n : AzNat) : List Char := (AzNat.toString n).toList

/-- `AzNat.parseChars cs := AzNat.parse (String.ofList cs)`. -/
def AzNat.parseChars (cs : List Char) : Option AzNat := AzNat.parse (String.ofList cs)

private theorem AzNat.parseChars_toChars (n : AzNat) :
    AzNat.parseChars (AzNat.toChars n) = some n := by
  unfold AzNat.parseChars AzNat.toChars
  rw [show String.ofList (AzNat.toString n).toList = AzNat.toString n from by
    apply String.toList_inj.mp; rw [String.toList_ofList]]
  exact AzNat.parse_toString n

instance : ParsableCoeff AzNat :=
  ParsableCoeff.mkDigitOnly
    AzNat.toChars
    AzNat.parseChars
    AzNat.parseChars_toChars
    (fun n => AzNat.toString_ne_empty n)
    (fun n c hc => AzNat.toString_char_digit n c hc)
    AzNat.toString_zero

end Azurite
