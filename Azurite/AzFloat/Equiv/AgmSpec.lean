/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.AgmWidth

/-!
# The specifications of the AGM functions as fuel-bound functions

`agmPrecRoundFuel_zivSpec`, `agmRatPrecRoundFuel_zivSpec`, `agmFloatRatPrecRoundFuel_zivSpec`
(`ZivSpec`, `Equiv/ZivSpec.lean`): the three functions are sound at every fuel, complete in the
limit of the fuel wherever the value is no rounding boundary (the interval AGM converges,
`Equiv/AgmWidth.lean`), and correct at every fuel wherever the value is known exactly — an
argument that is not positive, or two equal arguments.

`AGM(a, b)` is transcendental for distinct positive algebraic `a`, `b` (Chudnovsky for the
curves with complex multiplication, Wüstholz for the others), so no pair of distinct positive
arguments has a dyadic value; that is not formalized, and the sets of known non-dyadic values
are empty here, apart from `AGM(q, q) = q` for a rational `q` that is not dyadic.
-/

namespace Azurite.AzFloat

open Azurite.BZ

/-- A real value of the extended AGM is dyadic when equal positive arguments are. -/
theorem isDyadic_of_agm {a' b' : EReal} {v : ℝ} (h : Spec.agm a' b' = some (v : EReal))
    (hD : ∀ a b : ℝ, a' = (a : EReal) → b' = (b : EReal) → 0 < a → 0 < b →
      a = b ∧ IsDyadic a) : IsDyadic v := by
  unfold Spec.agm at h
  by_cases h1 : a' < 0 ∨ b' < 0
  · rw [ite_eq_left h1] at h
    exact absurd h (by simp)
  rw [ite_eq_right h1] at h
  by_cases h2 : a' = 0 ∨ b' = 0
  · rw [ite_eq_left h2] at h
    by_cases h3 : a' = ⊤ ∨ b' = ⊤
    · rw [ite_eq_left h3] at h
      exact absurd h (by simp)
    · rw [ite_eq_right h3, Option.some.injEq] at h
      have : v = 0 := by exact_mod_cast h.symm
      rw [this]
      exact isDyadic_zero
  rw [ite_eq_right h2] at h
  by_cases h3 : a' = ⊤ ∨ b' = ⊤
  · rw [ite_eq_left h3, Option.some.injEq] at h
    exact absurd h (by simp)
  · rw [ite_eq_right h3] at h
    rw [not_or] at h1 h2 h3
    induction a' using EReal.rec with
    | bot => exact absurd EReal.bot_lt_zero h1.1
    | top => exact absurd rfl h3.1
    | coe a =>
      induction b' using EReal.rec with
      | bot => exact absurd EReal.bot_lt_zero h1.2
      | top => exact absurd rfl h3.2
      | coe b =>
        have ha : 0 < a := lt_of_le_of_ne (by exact_mod_cast not_lt.mp h1.1)
          (fun h0 => h2.1 (by exact_mod_cast h0.symm))
        have hb : 0 < b := lt_of_le_of_ne (by exact_mod_cast not_lt.mp h1.2)
          (fun h0 => h2.2 (by exact_mod_cast h0.symm))
        obtain ⟨hab, hdy⟩ := hD a b rfl rfl ha hb
        rw [EReal.toReal_coe, EReal.toReal_coe, Option.some.injEq, EReal.coe_eq_coe_iff, ← hab,
          AGM_self ha.le] at h
        rw [← h]
        exact hdy

/-- **The specification of `AGM(x, y)`** for floats. -/
theorem agmPrecRoundFuel_zivSpec :
    ZivSpec
      (fun xy : AzFloat × AzFloat => xy.1.toVal.bind fun a => xy.2.toVal.bind fun b =>
        Spec.agm a b)
      (fun fuel xy p mode => agmPrecRoundFuel fuel xy.1 xy.2 p mode)
      {xy | ∀ a b : ℝ, xy.1.toVal = some (a : EReal) → xy.2.toVal = some (b : EReal) →
        a ≤ 0 ∨ b ≤ 0 ∨ a = b} ∅ where
  sound := fun fuel xy p _ mode => agmPrecRoundFuel_eq_or fuel xy.1 xy.2 p mode
  complete := fun xy p _ mode hB => by
    by_cases hgen : ∃ a b : ℝ, xy.1.toVal = some (a : EReal) ∧ xy.2.toVal = some (b : EReal) ∧
        0 < a ∧ 0 < b ∧ a ≠ b
    · obtain ⟨a, b, hx, hy, ha, hb, hab⟩ := hgen
      have hval : (xy.1.toVal.bind fun a => xy.2.toVal.bind fun b => Spec.agm a b)
          = some ((AGM a b : ℝ) : EReal) := by
        rw [hx, hy, Option.bind_some, Option.bind_some, Spec.agm_coe_coe ha hb]
      have hB' := hB _ hval
      obtain ⟨F, hF⟩ := zivLoop_eventually_eq p mode _ (agmApprox_bracketConv hx hy ha hb)
        (ne_zero_of_not_mem_floatSet hB') hB' (p + zivGuardBits)
        (by unfold zivGuardBits; omega) (fun w hw => Or.inl (by
          have : NeZero w := ⟨by unfold zivGuardBits at hw; omega⟩
          obtain ⟨lv, hv, h1, h2, h3, h4, -⟩ := agmApprox_spec hx hy ha hb hab w
          exact ⟨lv, hv, h1, h2, h3, h4⟩))
      refine ⟨F, fun fuel hfuel => ?_⟩
      rcases agmPrecRoundFuel_eq_or_loop fuel xy.1 xy.2 p mode with h | ⟨-, -, -, -, -, -, -, h⟩
      · exact h
      · show agmPrecRoundFuel fuel xy.1 xy.2 p mode = _
        rw [h, hval]
        exact hF fuel hfuel
    · refine ⟨0, fun fuel _ => ?_⟩
      rcases agmPrecRoundFuel_eq_or_loop fuel xy.1 xy.2 p mode with
        h | ⟨a, b, hx, hy, ha, hb, hab, -⟩
      · exact h
      · exact absurd ⟨a, b, hx, hy, ha, hb, hab⟩ hgen
  dyadic := fun xy hxy v hv => by
    cases hx : xy.1.toVal with
    | none => rw [hx] at hv; exact absurd hv (by simp)
    | some a' =>
      cases hy : xy.2.toVal with
      | none => rw [hx, hy] at hv; exact absurd hv (by simp)
      | some b' =>
        rw [hx, hy, Option.bind_some, Option.bind_some] at hv
        refine isDyadic_of_agm hv fun a b ha' hb' ha hb => ?_
        subst ha' hb'
        rcases hxy a b hx hy with h | h | h
        · exact absurd ha (not_lt.mpr h)
        · exact absurd hb (not_lt.mpr h)
        · exact ⟨h, isDyadic_of_toVal hx⟩
  nondyadic := fun xy h => absurd h (Set.notMem_empty _)
  correct := fun xy hxy fuel p _ mode => by
    rcases hxy with hD | hN
    · rcases agmPrecRoundFuel_eq_or_loop fuel xy.1 xy.2 p mode with
        h | ⟨a, b, hx, hy, ha, hb, hab, -⟩
      · exact h
      · exfalso
        rcases hD a b hx hy with h | h | h
        · exact absurd ha (not_lt.mpr h)
        · exact absurd hb (not_lt.mpr h)
        · exact hab h
    · exact absurd hN (Set.notMem_empty _)

/-- **The specification of `AGM(q₁, q₂)`** for rationals: `AGM(q, q) = q` is produced exactly,
dyadic or not. -/
theorem agmRatPrecRoundFuel_zivSpec :
    ZivSpec
      (fun qq : AzRat × AzRat => Spec.agm (AzRat.toRat qq.1 : ℝ) (AzRat.toRat qq.2 : ℝ))
      (fun fuel qq p mode => agmRatPrecRoundFuel fuel qq.1 qq.2 p mode)
      {qq | (AzRat.toRat qq.1 : ℝ) ≤ 0 ∨ (AzRat.toRat qq.2 : ℝ) ≤ 0 ∨
        ((AzRat.toRat qq.1 : ℝ) = AzRat.toRat qq.2 ∧ IsDyadic (AzRat.toRat qq.1 : ℝ))}
      {qq | 0 < (AzRat.toRat qq.1 : ℝ) ∧ (AzRat.toRat qq.1 : ℝ) = AzRat.toRat qq.2 ∧
        ¬ IsDyadic (AzRat.toRat qq.1 : ℝ)} where
  sound := fun fuel qq p _ mode => agmRatPrecRoundFuel_eq_or fuel qq.1 qq.2 p mode
  complete := fun qq p _ mode hB => by
    by_cases hgen : 0 < (AzRat.toRat qq.1 : ℝ) ∧ 0 < (AzRat.toRat qq.2 : ℝ) ∧
        (AzRat.toRat qq.1 : ℝ) ≠ AzRat.toRat qq.2
    · obtain ⟨ha, hb, hab⟩ := hgen
      have hval := Spec.agm_coe_coe ha hb
      have hB' := hB _ hval
      obtain ⟨F, hF⟩ := zivLoop_eventually_eq p mode _ (agmRatApprox_bracketConv ha hb)
        (ne_zero_of_not_mem_floatSet hB') hB' (p + zivGuardBits)
        (by unfold zivGuardBits; omega) (fun w hw => Or.inl (by
          have : NeZero w := ⟨by unfold zivGuardBits at hw; omega⟩
          obtain ⟨lv, hv, h1, h2, h3, h4, -⟩ := agmRatApprox_spec ha hb hab w
          exact ⟨lv, hv, h1, h2, h3, h4⟩))
      refine ⟨F, fun fuel hfuel => ?_⟩
      rcases agmRatPrecRoundFuel_eq_or_loop fuel qq.1 qq.2 p mode with h | ⟨-, -, -, h⟩
      · exact h
      · show agmRatPrecRoundFuel fuel qq.1 qq.2 p mode = _
        rw [h, hval]
        exact hF fuel hfuel
    · refine ⟨0, fun fuel _ => ?_⟩
      rcases agmRatPrecRoundFuel_eq_or_loop fuel qq.1 qq.2 p mode with h | ⟨ha, hb, hab, -⟩
      · exact h
      · exact absurd ⟨ha, hb, hab⟩ hgen
  dyadic := fun qq hqq v hv => by
    refine isDyadic_of_agm hv fun a b ha' hb' ha hb => ?_
    have ea : (AzRat.toRat qq.1 : ℝ) = a := by exact_mod_cast ha'
    have eb : (AzRat.toRat qq.2 : ℝ) = b := by exact_mod_cast hb'
    subst ea eb
    rcases hqq with h | h | h
    · exact absurd ha (not_lt.mpr h)
    · exact absurd hb (not_lt.mpr h)
    · exact h
  nondyadic := fun qq h => by
    obtain ⟨ha, hab, hnd⟩ := h
    refine ⟨_, ?_, hnd⟩
    rw [← hab, Spec.agm_coe_coe ha ha, AGM_self ha.le]
  correct := fun qq hqq fuel p _ mode => by
    rcases agmRatPrecRoundFuel_eq_or_loop fuel qq.1 qq.2 p mode with h | ⟨ha, hb, hab, -⟩
    · exact h
    · exfalso
      rcases hqq with (h | h | h) | h
      · exact absurd ha (not_lt.mpr h)
      · exact absurd hb (not_lt.mpr h)
      · exact hab h.1
      · exact hab h.2.1

/-- **The specification of `AGM(x, q)`** for a float and a rational. -/
theorem agmFloatRatPrecRoundFuel_zivSpec :
    ZivSpec
      (fun xq : AzFloat × AzRat => xq.1.toVal.bind fun a => Spec.agm a (AzRat.toRat xq.2 : ℝ))
      (fun fuel xq p mode => agmFloatRatPrecRoundFuel fuel xq.1 xq.2 p mode)
      {xq | ∀ a : ℝ, xq.1.toVal = some (a : EReal) →
        a ≤ 0 ∨ (AzRat.toRat xq.2 : ℝ) ≤ 0 ∨ a = AzRat.toRat xq.2} ∅ where
  sound := fun fuel xq p _ mode => agmFloatRatPrecRoundFuel_eq_or fuel xq.1 xq.2 p mode
  complete := fun xq p _ mode hB => by
    by_cases hgen : ∃ a : ℝ, xq.1.toVal = some (a : EReal) ∧ 0 < a ∧
        0 < (AzRat.toRat xq.2 : ℝ) ∧ a ≠ AzRat.toRat xq.2
    · obtain ⟨a, hx, ha, hb, hab⟩ := hgen
      have hval : (xq.1.toVal.bind fun a => Spec.agm a (AzRat.toRat xq.2 : ℝ))
          = some ((AGM a (AzRat.toRat xq.2) : ℝ) : EReal) := by
        rw [hx, Option.bind_some, Spec.agm_coe_coe ha hb]
      have hB' := hB _ hval
      obtain ⟨F, hF⟩ := zivLoop_eventually_eq p mode _
        (agmFloatRatApprox_bracketConv hx ha hb) (ne_zero_of_not_mem_floatSet hB') hB'
        (p + zivGuardBits) (by unfold zivGuardBits; omega) (fun w hw => Or.inl (by
          have : NeZero w := ⟨by unfold zivGuardBits at hw; omega⟩
          obtain ⟨lv, hv, h1, h2, h3, h4, -⟩ := agmFloatRatApprox_spec hx ha hb hab w
          exact ⟨lv, hv, h1, h2, h3, h4⟩))
      refine ⟨F, fun fuel hfuel => ?_⟩
      rcases agmFloatRatPrecRoundFuel_eq_or_loop fuel xq.1 xq.2 p mode with
        h | ⟨-, -, -, -, -, h⟩
      · exact h
      · show agmFloatRatPrecRoundFuel fuel xq.1 xq.2 p mode = _
        rw [h, hval]
        exact hF fuel hfuel
    · refine ⟨0, fun fuel _ => ?_⟩
      rcases agmFloatRatPrecRoundFuel_eq_or_loop fuel xq.1 xq.2 p mode with
        h | ⟨a, hx, ha, hb, hab, -⟩
      · exact h
      · exact absurd ⟨a, hx, ha, hb, hab⟩ hgen
  dyadic := fun xq hxq v hv => by
    cases hx : xq.1.toVal with
    | none => rw [hx] at hv; exact absurd hv (by simp)
    | some a' =>
      rw [hx, Option.bind_some] at hv
      refine isDyadic_of_agm hv fun a b ha' hb' ha hb => ?_
      subst ha'
      have eb : (AzRat.toRat xq.2 : ℝ) = b := by exact_mod_cast hb'
      subst eb
      rcases hxq a hx with h | h | h
      · exact absurd ha (not_lt.mpr h)
      · exact absurd hb (not_lt.mpr h)
      · exact ⟨h, isDyadic_of_toVal hx⟩
  nondyadic := fun xq h => absurd h (Set.notMem_empty _)
  correct := fun xq hxq fuel p _ mode => by
    rcases hxq with hD | hN
    · rcases agmFloatRatPrecRoundFuel_eq_or_loop fuel xq.1 xq.2 p mode with
        h | ⟨a, hx, ha, hb, hab, -⟩
      · exact h
      · exfalso
        rcases hD a hx with h | h | h
        · exact absurd ha (not_lt.mpr h)
        · exact absurd hb (not_lt.mpr h)
        · exact hab h
    · exact absurd hN (Set.notMem_empty _)

end Azurite.AzFloat
