/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  A `LinearOrder` on `AzZMod m`, by canonical residue value.

  This is NOT an order compatible with the ring structure (none exists on
  ℤ/m) — it is the canonical-representative order `a ≤ b ↔ a.val ≤ b.val`,
  lifted from the `AzNat` order along the injective `val`.  Its purpose is
  canonical SORTING: polynomial coefficient orders (`AzPolynomial`'s
  degree-then-top-down-lex `LinearOrder` requires `LinearOrder` on the
  coefficients), and through them canonical factor lists in
  `AzPolynomial.factorization`.
-/
import Azurite.AzZMod.Basic
import Azurite.AzNat.Equiv.Compare

namespace Azurite

namespace AzZMod

variable {m : AzNat}

instance instLinearOrder : LinearOrder (AzZMod m) :=
  LinearOrder.lift' (fun a => a.val) (fun _ _ h => ext h)

theorem le_def (a b : AzZMod m) : a ≤ b ↔ a.val ≤ b.val := Iff.rfl

end AzZMod

end Azurite
