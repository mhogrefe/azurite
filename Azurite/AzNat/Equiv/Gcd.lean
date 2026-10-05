/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Equiv.Gcd.Binary
import Azurite.AzNat.Equiv.Gcd.HalfBinary
import Azurite.AzNat.Gcd

/-!
## Correctness of `AzNat.gcd` and `AzNat.coprime`

Both dispatch targets compute `Nat.gcd` (`toNat_gcdBinary`, `toNat_gcdHalfBinary`), hence so does
`gcd`; `coprime` agrees with `Nat.Coprime`.
-/

namespace Azurite.AzNat

/-- Correctness of `gcd`: it computes `Nat.gcd`. -/
theorem toNat_gcd (a b : AzNat) : (gcd a b).toNat = Nat.gcd a.toNat b.toNat := by
  unfold gcd
  split_ifs
  · exact toNat_gcdBinary a b
  · exact toNat_gcdHalfBinary a b

/-- Correctness of `coprime`: agrees with `Nat.Coprime`. -/
theorem coprime_iff (a b : AzNat) :
    AzNat.coprime a b = true ↔ Nat.Coprime a.toNat b.toNat := by
  show (if a.isEven && b.isEven then false else AzNat.gcd a b == 1) = true
    ↔ Nat.gcd a.toNat b.toNat = 1
  by_cases h_both_even : (a.isEven && b.isEven) = true
  · rw [ite_eq_left h_both_even]
    simp only [Bool.false_eq_true, false_iff]
    have ha_even : a.isEven = true := by
      have := h_both_even; simp [Bool.and_eq_true] at this; exact this.1
    have hb_even : b.isEven = true := by
      have := h_both_even; simp [Bool.and_eq_true] at this; exact this.2
    rw [isEven_iff] at ha_even hb_even
    obtain ⟨ka, hka⟩ := ha_even
    obtain ⟨kb, hkb⟩ := hb_even
    intro h_gcd
    have h2g : 2 ∣ Nat.gcd a.toNat b.toNat :=
      Nat.dvd_gcd ⟨ka, by omega⟩ ⟨kb, by omega⟩
    omega
  · rw [ite_eq_right (Bool.not_eq_true _ ▸ h_both_even)]
    rw [beq_iff_eq]
    constructor
    · intro h
      rw [← toNat_gcd a b, h]; rfl
    · intro h
      apply toNat_injective
      rw [toNat_gcd, h]; rfl

end Azurite.AzNat
