/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Round-trip: `parseAzPolynomial (toChars p) = some p`.

  This sits above `FinOneAlgEquiv` in the import chain because its proof
  uses the `AzMvPolynomial 1 ↔ AzPolynomial` round-trip lemma from that
  module. Kept separate from `AzPolynomial.Parse` so the latter can be
  imported by `AzPolynomial.Mul` / `AzPolynomial.Add` etc. (which are
  themselves imported transitively by `FinOneAlgEquiv`).
-/
import Azurite.AzPolynomial.Parse
import Azurite.AzMvPolynomial.ParseToString
import Azurite.AzMvPolynomial.Equiv.FinOneAlgEquiv

namespace Azurite.AzPolynomial

variable {R : Type _} [CommSemiring R] [DecidableEq R] [NeZero (1 : R)] [ParsableCoeff R]

/-- Round-trip: parsing the string representation of a polynomial recovers it. -/
theorem parseAzPolynomial_toChars (p : AzPolynomial R) :
    parseAzPolynomial (toChars p) = some p := by
  unfold parseAzPolynomial toChars
  unfold AzMvPolynomial.parseStrWith AzMvPolynomial.toStrWith
  rw [String.toList_ofList, AzMvPolynomial.parseWith_toCharsWith]
  rw [Option.map_some]
  exact congrArg some (Azurite.toAzMvPolynomial_toAzPolynomial_roundtrip p)

end Azurite.AzPolynomial
