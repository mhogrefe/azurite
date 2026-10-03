/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Sci
import Azurite.AzFloat.Equiv.Conversion
import Azurite.AzFloat.Equiv.Rounding
import Azurite.AzRat.Equiv.ToSci

/-!
# Correctness of `toSci` for floats

The rendering is `AzRat.toSci` of the exact value, so its specification is `AzRat`'s: at `p`
significant digits in base `b` the printed number is the rounding of the value to `p` base-`b`
digits (`toSciNumber_value_precision`).
-/

namespace Azurite.AzFloat

open RoundingTarget

theorem toSciNumber_eq (x : AzFloat) (q : AzRat) (hq : x.toAzRat? = some q) (o : SciOptions) :
    x.toSciNumber o = q.toSciNumber o := by
  unfold toSciNumber
  rw [hq, Option.bind_some]

theorem toSci_eq (x : AzFloat) (q : AzRat) (hq : x.toAzRat? = some q) (o : SciOptions) :
    x.toSci o = q.toSci o := by
  cases x with
  | nan => simp [toAzRat?] at hq
  | infinity _ => simp [toAzRat?] at hq
  | zero => simp only [toSci, hq, Option.bind_some]
  | finite s e p m hv => simp only [toSci, hq, Option.bind_some]

/-- At `p` significant digits the rendered number is the rounding of the float's value to `p`
digits in the chosen base, in the chosen mode. -/
theorem toSciNumber_value_precision (x : AzFloat) (q : AzRat) (hq : x.toAzRat? = some q)
    (o : SciOptions) (hv : o.valid = true) (p : ℕ) (hp : o.size = .precision p)
    [Fact (1 < o.base.toNat)] [NeZero p] :
    ∃ sn, x.toSciNumber o = some sn ∧ x.toVal = some ((AzRat.toRat q : ℝ) : EReal) ∧
      ((sn.value : ℝ) : EReal)
        = (RoundingTarget.round (precisionSet o.base.toNat p) o.mode (AzRat.toRat q : ℝ)).val := by
  obtain ⟨sn, hsn, hval⟩ := AzRat.toSciNumber_value_precision q o hv p hp
  exact ⟨sn, by rw [toSciNumber_eq x q hq, hsn], toVal_of_toAzRat? x q hq, hval⟩

end Azurite.AzFloat
