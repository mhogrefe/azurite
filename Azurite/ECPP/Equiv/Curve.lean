/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.ECPP.Curve
import Azurite.ECPP.Theory.Ladder
import Azurite.AzZMod.Equiv.RingEquiv
import Azurite.AzNat.Equiv.TestBit
import Azurite.AzNat.Equiv.ShiftRight

/-!
# Equivalence: curve arithmetic over `AzZMod n`

Through `AzZMod.toZMod : AzZMod n → ZMod n.toNat` the functions of `ECPP/Curve.lean` are the
specification functions of `Theory/Ladder.lean`: `mapPt_jacDbl`, `mapPt_jacAddMixed`,
`jacMul_map`.
-/

namespace Azurite.ECPP

open AzZMod

variable {n : AzNat} [NeZero n.toNat]

/-- The image of a point in `ZMod n.toNat`. -/
def mapPt (P : JacPoint n) : ZMod n.toNat × ZMod n.toNat × ZMod n.toNat :=
  (toZMod P.1, toZMod P.2.1, toZMod P.2.2)

/-- **`jacDbl` is the doubling of the specification.** -/
theorem mapPt_jacDbl (a : AzZMod n) (P : JacPoint n) :
    mapPt (jacDbl a P) = dblShort (toZMod a) (mapPt P) := by
  simp only [jacDbl, mapPt, dblShort, toZMod_add, toZMod_sub, toZMod_mul, toZMod_square]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> ring

/-- **`jacAddMixed` is the mixed addition of the specification.** -/
theorem mapPt_jacAddMixed (u v : AzZMod n) (P : JacPoint n) :
    mapPt (jacAddMixed u v P) = addMixed (toZMod u) (toZMod v) (mapPt P) := by
  simp only [jacAddMixed, mapPt, addMixed, toZMod_add, toZMod_sub, toZMod_mul, toZMod_square]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> ring

/-- **`jacMul` is the ladder of the specification.** -/
theorem jacMul_map (a u v : AzZMod n) : ∀ (fuel : ℕ) (k : AzNat),
    (jacMul a u v fuel k).map mapPt = ladder (toZMod a) (toZMod u) (toZMod v) fuel k.toNat
  | 0, _ => rfl
  | fuel + 1, k => by
    rw [jacMul, ladder]
    have h1 : k = AzNat.ofNat 1 ↔ k.toNat = 1 := by
      constructor
      · rintro rfl
        exact AzNat.toNat_ofNat 1
      · intro h
        exact AzNat.toNat_injective (by rw [h, AzNat.toNat_ofNat])
    by_cases hk : k = AzNat.ofNat 1
    · rw [ite_eq_left hk, ite_eq_left (h1.mp hk)]
      simp [mapPt]
    · rw [ite_eq_right hk, ite_eq_right (mt h1.mpr hk)]
      have hshift : (k.shiftRight 1).toNat = k.toNat / 2 := by
        rw [AzNat.toNat_shiftRight, pow_one]
      have ih := jacMul_map a u v fuel (k.shiftRight 1)
      rw [hshift] at ih
      rw [← ih]
      have hbit : k.testBit 0 = decide (k.toNat % 2 = 1) := by
        rw [AzNat.testBit_eq_toNat_testBit, Nat.testBit_zero]
      cases jacMul a u v fuel (k.shiftRight 1) with
      | none => rfl
      | some T =>
        simp only [Option.map_some]
        congr 1
        by_cases hodd : k.toNat % 2 = 1
        · have ht : k.testBit 0 = true := by rw [hbit]; exact decide_eq_true hodd
          rw [ite_eq_left ht, ite_eq_left hodd, mapPt_jacAddMixed, mapPt_jacDbl]
        · have ht : ¬ k.testBit 0 = true := by rw [hbit]; simpa using hodd
          rw [ite_eq_right ht, ite_eq_right hodd, mapPt_jacDbl]

end Azurite.ECPP
