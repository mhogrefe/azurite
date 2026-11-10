/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.PowBase
import Azurite.AzFloat.Equiv.Pow
import Azurite.AzFloat.Equiv.Div

/-!
# Equivalence: `u^x` for a natural base

* `Spec.powBase u`: the extended-real `u^a` with `0^a = +∞` for `a < 0`, `0^(±∞)` and `u^(±∞)`
  by continuity, `1^(±∞) = 1` (MPFR); `Spec.powBaseOpt u` extends it to `NaN` (`none`):
  `1^NaN = 1`, otherwise `NaN`.
* `powBasePrecRound_eq : powBasePrecRound u x p mode = roundVal p mode (Spec.powBaseOpt u x)`:
  `u^x` is correctly rounded in every mode, with the exact comparison, and without fuel;
  `powBasePrecRound_eq_liftVal` (`= liftVal (Spec.powBase u) x p mode`) for `u ≠ 1`.
-/

namespace Azurite.AzFloat

namespace Spec

open Classical in
/-- Extended-real `u^a` for a natural `u`: `0^a = +∞` for `a < 0`; `0^(+∞) = 0`, `0^(−∞) = +∞`;
`1^(±∞) = 1` (MPFR); `u^(+∞) = +∞`, `u^(−∞) = 0` for `u ≥ 2`; otherwise the real power
(`0^0 = 1`, `1^a = 1`). -/
noncomputable def powBase (u : ℕ) (a : EReal) : Option EReal :=
  if a = ⊤ then (if u = 0 then some 0 else if u = 1 then some 1 else some ⊤)
  else if a = ⊥ then (if u = 0 then some ⊤ else if u = 1 then some 1 else some 0)
  else if u = 0 ∧ a.toReal < 0 then some ⊤
  else some (((u : ℝ) ^ a.toReal : ℝ) : EReal)

theorem powBase_coe (u : ℕ) (r : ℝ) :
    powBase u (r : EReal)
      = if u = 0 ∧ r < 0 then some ⊤ else some (((u : ℝ) ^ r : ℝ) : EReal) := by
  unfold powBase
  rw [ite_eq_right (EReal.coe_ne_top r), ite_eq_right (EReal.coe_ne_bot r), EReal.toReal_coe]

@[simp] theorem powBase_top (u : ℕ) :
    powBase u ⊤ = if u = 0 then some 0 else if u = 1 then some 1 else some ⊤ := by
  unfold powBase
  rw [ite_eq_left rfl]

@[simp] theorem powBase_bot (u : ℕ) :
    powBase u ⊥ = if u = 0 then some ⊤ else if u = 1 then some 1 else some 0 := by
  unfold powBase
  rw [ite_eq_right bot_ne_top, ite_eq_left rfl]

/-- `u^a` on `Option EReal` (`none` = `NaN`): `1^NaN = 1` (MPFR), otherwise `NaN` propagates. -/
noncomputable def powBaseOpt (u : ℕ) : Option EReal → Option EReal
  | none => if u = 1 then some 1 else none
  | some a => powBase u a

@[simp] theorem powBaseOpt_none (u : ℕ) : powBaseOpt u none = if u = 1 then some 1 else none :=
  rfl

@[simp] theorem powBaseOpt_some (u : ℕ) (a : EReal) : powBaseOpt u (some a) = powBase u a := rfl

/-- Away from `u = 1`, `powBaseOpt` is `powBase` with `NaN` propagated. -/
theorem powBaseOpt_eq_bind {u : ℕ} (hu : u ≠ 1) (a : Option EReal) :
    powBaseOpt u a = a.bind (powBase u) := by
  cases a with
  | none => simp [hu]
  | some a => rfl

end Spec

/-- The value of `AzInt.toInt` by the sign. -/
theorem toInt_eq_of_sign (n : AzInt) :
    n.toInt = if n.sign then (n.abs.toNat : ℤ) else -(n.abs.toNat : ℤ) := rfl

/-- **`u^x` is correctly rounded** (with `1^x = 1` for every `x`, even `NaN`). -/
theorem powBasePrecRound_eq (u : UInt64) (x : AzFloat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    powBasePrecRound u x p mode = roundVal p mode (Spec.powBaseOpt u.toNat x.toVal) := by
  cases x with
  | nan =>
    by_cases h1 : u.toNat = 1 <;>
      simp [powBasePrecRound, h1, NeZero.ne p, setPrecRound_one_eq]
  | infinity s =>
    cases s <;> by_cases h0 : u.toNat = 0 <;> by_cases h1 : u.toNat = 1 <;>
      simp [powBasePrecRound, h0, h1, NeZero.ne p, setPrecRound_one_eq]
  | zero =>
    simp only [powBasePrecRound, toVal_zero, Spec.powBaseOpt_some]
    rw [ite_eq_right (NeZero.ne p), ← EReal.coe_zero, Spec.powBase_coe,
      ite_eq_right (fun h => lt_irrefl _ h.2), Real.rpow_zero,
      setPrecRound_eq_roundVal toVal_one']
  | finite s e q m hv =>
    simp only [powBasePrecRound, toVal_finite, Spec.powBaseOpt_some, Spec.powBase_coe]
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
      · next r' hT =>
        exact expNearOne?_natBase_eq (by omega) u.toBitVec.isLt (abs_finiteVal_bounds s e hv).2
          (finiteVal_ne_zero s e hv) (finiteVal_sign_iff s e hv) hT
      split
      · rename_i r n hx
        obtain ⟨hr, hval⟩ := powBaseExact?_some _ _ hu2 (toVal_finite s e q m hv) hx
        rw [AzNat.toNat_ofNat] at hval
        obtain ⟨hcs, -, hc2, -⟩ := maxRootBase_spec (AzNat.ofNat u.toNat) hu2
        rw [← hr] at hc2
        have hr0 : r ≠ 0 := fun h => by rw [h, AzNat.toNat_zero] at hc2; omega
        rw [hval, natPowOrZiv_eq hr0]
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

/-- **`u^x` is correctly rounded**, as a lift of `Spec.powBase u` (`NaN` propagated), for
`u ≠ 1`. -/
theorem powBasePrecRound_eq_liftVal (u : UInt64) (hu : u.toNat ≠ 1) (x : AzFloat) (p : ℕ)
    [NeZero p] (mode : RoundingMode) :
    powBasePrecRound u x p mode = liftVal (Spec.powBase u.toNat) x p mode := by
  rw [powBasePrecRound_eq, Spec.powBaseOpt_eq_bind hu]
  rfl

end Azurite.AzFloat
