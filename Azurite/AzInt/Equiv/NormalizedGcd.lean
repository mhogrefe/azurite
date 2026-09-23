/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  The base bridge of the nested-gcd correctness tower:
  `NormalizedGcdBridge AzInt ℤ`.

  `Azurite.NormalizedGcd.ngcd` on `AzInt` (the nonnegative gcd, computed
  magnitude-wise by `AzNat.gcd`) represents Mathlib's normalized `ℤ` gcd
  (`toInt_ngcd`); the bridge homomorphism is `AzInt.toIntRingHom` (a ring
  isomorphism, so injectivity, divisibility reflection, and surjectivity —
  needed by `NormalizedGcdBridge.step` — are all immediate).
-/
import Azurite.AzInt.NormalizedGcd
import Azurite.AzInt.Equiv.RingEquiv
import Azurite.AzNat.Equiv.Gcd
import Azurite.AzPolynomial.Equiv.Content
import Azurite.AzPolynomial.Equiv.GcdTower
import Mathlib.Algebra.GCDMonoid.Nat

namespace Azurite.AzInt

/-- The `AzInt` normalized gcd represents Mathlib's normalized `ℤ` gcd
(both are the nonnegative representative). -/
theorem toInt_ngcd (a b : AzInt) :
    (NormalizedGcd.ngcd a b).toInt = GCDMonoid.gcd a.toInt b.toInt := by
  show ((AzNat.gcd a.abs b.abs).toNat : ℤ) = GCDMonoid.gcd a.toInt b.toInt
  rw [Azurite.AzNat.toNat_gcd, ← Azurite.AzInt.toNat_abs,
    ← Azurite.AzInt.toNat_abs,
    show Nat.gcd a.toInt.natAbs b.toInt.natAbs = Int.gcd a.toInt b.toInt
      from rfl,
    Int.coe_gcd]

/-- **The base bridge `AzInt → ℤ`** of the nested-gcd correctness tower. -/
noncomputable def intNormalizedGcdBridge :
    Azurite.AzPolynomial.NormalizedGcdBridge AzInt ℤ where
  hom := AzInt.toIntRingHom
  injective := fun a b h =>
    Azurite.AzInt.ringEquivInt.injective (by simpa using h)
  dvd_reflect := by
    intro a b h
    obtain ⟨c, hc⟩ := h
    refine ⟨Azurite.AzInt.ringEquivInt.symm c,
      Azurite.AzInt.ringEquivInt.injective ?_⟩
    rw [map_mul]
    simpa using hc
  map_ngcd := toInt_ngcd

/-- The base bridge homomorphism is surjective (it is `toInt`, a ring
isomorphism) — the hypothesis `NormalizedGcdBridge.step` iterates on. -/
theorem intNormalizedGcdBridge_hom_surjective :
    Function.Surjective intNormalizedGcdBridge.hom := fun z =>
  ⟨Azurite.AzInt.ringEquivInt.symm z,
    Azurite.AzInt.ringEquivInt.apply_symm_apply z⟩

end Azurite.AzInt
