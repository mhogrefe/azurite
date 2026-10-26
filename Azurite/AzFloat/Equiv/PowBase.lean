/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.PowBase
import Azurite.AzFloat.Equiv.Div

/-!
# Equivalence: `u^x` for a natural base

* `Spec.powBase u`: the extended-real `u^a` with `0^a = +∞` for `a < 0`, `0^(±∞)` and `u^(±∞)`
  by continuity, `1^(±∞)` undefined.
* `powBasePrecRound_eq_liftVal : powBasePrecRound u x p mode = liftVal (Spec.powBase u) x p mode`:
  `u^x` is correctly rounded in every mode, with the exact comparison, and without fuel.
-/

namespace Azurite.AzFloat

namespace Spec

open Classical in
/-- Extended-real `u^a` for a natural `u`: `0^a = +∞` for `a < 0`; `0^(+∞) = 0`, `0^(−∞) = +∞`;
`1^(±∞)` undefined; `u^(+∞) = +∞`, `u^(−∞) = 0` for `u ≥ 2`; otherwise the real power
(`0^0 = 1`, `1^a = 1`). -/
noncomputable def powBase (u : ℕ) (a : EReal) : Option EReal :=
  if a = ⊤ then (if u = 0 then some 0 else if u = 1 then none else some ⊤)
  else if a = ⊥ then (if u = 0 then some ⊤ else if u = 1 then none else some 0)
  else if u = 0 ∧ a.toReal < 0 then some ⊤
  else some (((u : ℝ) ^ a.toReal : ℝ) : EReal)

theorem powBase_coe (u : ℕ) (r : ℝ) :
    powBase u (r : EReal)
      = if u = 0 ∧ r < 0 then some ⊤ else some (((u : ℝ) ^ r : ℝ) : EReal) := by
  unfold powBase
  rw [ite_eq_right (EReal.coe_ne_top r), ite_eq_right (EReal.coe_ne_bot r), EReal.toReal_coe]

@[simp] theorem powBase_top (u : ℕ) :
    powBase u ⊤ = if u = 0 then some 0 else if u = 1 then none else some ⊤ := by
  unfold powBase
  rw [ite_eq_left rfl]

@[simp] theorem powBase_bot (u : ℕ) :
    powBase u ⊥ = if u = 0 then some ⊤ else if u = 1 then none else some 0 := by
  unfold powBase
  rw [ite_eq_right bot_ne_top, ite_eq_left rfl]

end Spec

/-- The value of `AzInt.toInt` by the sign. -/
theorem toInt_eq_of_sign (n : AzInt) :
    n.toInt = if n.sign then (n.abs.toNat : ℤ) else -(n.abs.toNat : ℤ) := rfl

/-- **`u^x` is correctly rounded.** -/
theorem powBasePrecRound_eq_liftVal (u : UInt64) (x : AzFloat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    powBasePrecRound u x p mode = liftVal (Spec.powBase u.toNat) x p mode := by
  unfold liftVal
  cases x with
  | nan => rfl
  | infinity s =>
    cases s <;> by_cases h0 : u.toNat = 0 <;> by_cases h1 : u.toNat = 1 <;>
      simp [powBasePrecRound, h0, h1]
  | zero =>
    simp only [powBasePrecRound, toVal_zero, Option.bind_some]
    rw [ite_eq_right (NeZero.ne p), ← EReal.coe_zero, Spec.powBase_coe,
      ite_eq_right (fun h => lt_irrefl _ h.2), Real.rpow_zero,
      setPrecRound_eq_roundVal toVal_one']
  | finite s e q m hv =>
    simp only [powBasePrecRound, toVal_finite, Option.bind_some, Spec.powBase_coe]
    by_cases h0 : u.toNat = 0
    · rw [dite_eq_left h0]
      cases s
      · have hneg : finiteVal false e m < 0 := by
          rw [finiteVal_false]; linarith [finiteVal_true_pos e hv]
        simp [h0, hneg]
      · have hpos := finiteVal_true_pos e hv
        simp [h0, not_lt.mpr hpos.le, Real.zero_rpow hpos.ne']
    rw [dite_eq_right h0, dite_eq_right (NeZero.ne p), ite_eq_right (fun h => h0 h.1)]
    by_cases h1 : u.toNat = 1
    · rw [dite_eq_left h1, h1, Nat.cast_one, Real.one_rpow, setPrecRound_eq_roundVal toVal_one']
    · rw [dite_eq_right h1]
      have hu2 : 2 ≤ (AzNat.ofNat u.toNat).toNat := by rw [AzNat.toNat_ofNat]; omega
      split
      · rename_i r n hx
        obtain ⟨hr, hval⟩ := powBaseExact?_some _ _ hu2 (toVal_finite s e q m hv) hx
        rw [AzNat.toNat_ofNat] at hval
        obtain ⟨hcs, -, hc2, -⟩ := maxRootBase_spec (AzNat.ofNat u.toNat) hu2
        rw [← hr] at hc2
        have hrR : (0 : ℝ) < (r.toNat : ℝ) ^ n.abs.toNat := by positivity
        rw [hval, toInt_eq_of_sign]
        split_ifs with hs
        · rw [zpow_natCast, setPrecRound_eq_roundVal (toVal_ofAzNat _), AzNat.toNat_pow,
            Nat.cast_pow]
        · rw [zpow_neg, zpow_natCast, divPrecRound_eq_liftVal₂, liftVal₂, toVal_one',
            toVal_ofAzNat, Option.bind_some, Option.bind_some, AzNat.toNat_pow, Nat.cast_pow,
            Spec.div_coe_coe _ _ hrR.ne', one_div]
      · rename_i hx
        exact zivLoopCertified_eq_threshold p mode _ ((u.toNat : ℝ) ^ finiteVal s e m) _
          (by unfold powBaseStart zivGuardBits; omega)
          (fun w hw => by
            obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ := powBaseApprox_spec (w := w) s e hv u
              (by omega)
              (AzNat.toNat_ofNat u.toNat ▸
                irrational_of_powBaseExact?_none s e hv (AzNat.ofNat u.toNat) hu2
                  (by rw [AzNat.toNat_ofNat]; exact u.toBitVec.isLt) hx)
              (by unfold powBaseStart at hw; omega)
            exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, fun h => absurd h hlo.ne⟩) _

end Azurite.AzFloat
