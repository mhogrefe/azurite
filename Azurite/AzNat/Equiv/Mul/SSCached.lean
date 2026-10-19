/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Mul.SSCached
import Azurite.AzNat.Equiv.Mul.SchonhageStrassen

/-!
# Correctness of the cached Schönhage–Strassen products

`SSPlan.mulModF_transform_toNat`: with the transform of `A`, `mulModF` is `A · B mod (2^bits + 1)`
for `A, B < 2^bits` — a restatement of `fftMulModWith_toNat`.  `SSPlan.ofLimbs_bits`:
`64 L ≤ (ofLimbs L).bits`.  `toZMod_eq_natCast`: a residue is the cast of its value.
-/

namespace Azurite.AzNat

open AzFermat

namespace SSPlan

theorem ofLimbs_bits (L : Nat) : 64 * L ≤ (ofLimbs L).bits := by
  unfold ofLimbs bits
  have := ssParams_le L
  dsimp only
  calc 64 * L ≤ 64 * ((ssParams L).2 * 2 ^ ((ssParams L).1 + 1)) := Nat.mul_le_mul_left _ this
    _ = 64 * (ssParams L).2 * 2 ^ ((ssParams L).1 + 1) := by ring

theorem mulModF_transform_toNat (p : SSPlan) (mulFn : AzNat → AzNat → AzNat)
    (hmul : ∀ x y : AzNat, (mulFn x y).toNat = x.toNat * y.toNat) (A B : AzNat)
    (hA : A.toNat < 2 ^ p.bits) (hB : B.toNat < 2 ^ p.bits) :
    (p.mulModF mulFn (p.transform A) (p.transform_size A) B).val.toNat
      = (A.toNat * B.toNat) % (2 ^ p.bits + 1) :=
  fftMulModWith_toNat p.k p.w p.N p.hw0 (ssFermatExponent_ge p.k p.w)
    (two_pow_dvd_ssFermatExponent p.k p.w) mulFn hmul A B hA hB

theorem mulModF'_toNat (p : SSPlan) (mulFn : AzNat → AzNat → AzNat)
    (hmul : ∀ x y : AzNat, (mulFn x y).toNat = x.toNat * y.toNat) (A B : AzNat)
    (hA : A.toNat < 2 ^ p.bits) (hB : B.toNat < 2 ^ p.bits) :
    (p.mulModF' mulFn A B).val.toNat = (A.toNat * B.toNat) % (2 ^ p.bits + 1) :=
  p.mulModF_transform_toNat mulFn hmul A B hA hB

end SSPlan

/-- A residue is the cast of its canonical value. -/
theorem toZMod_eq_natCast {N : Nat} (x : AzFermat N) :
    toZMod x = (x.val.toNat : ZMod (2 ^ N + 1)) := by
  rw [← toZMod_val, ZMod.natCast_zmod_val]

end Azurite.AzNat
