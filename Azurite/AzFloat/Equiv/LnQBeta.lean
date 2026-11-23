/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LnQBeta
import Azurite.AzFloat.Equiv.QBeta
import Azurite.AzFloat.Equiv.LnBeta
import Azurite.AzFloat.Equiv.LnBetaRat
import Azurite.AzFloat.Equiv.BetaFloatRat

/-!
# Equivalence: `ln |B_q|` and `ln B_q`

`Spec.lnAbsQBeta` (`ln |·|` of `Spec.qBeta`), `Spec.lnQBeta` (`ln` of it) and the
specifications of the twelve functions of `AzFloat/LnQBeta.lean`: for each of the six kinds
of `(q; a, b)` a **`lnAbsQBeta…PrecRoundFuel_zivSpec`** (the value component), the sign
theorem `…_sign`, and a **`lnQBeta…PrecRoundFuel_zivSpec`**.

Each is sound at every fuel and complete in the limit of the fuel wherever the value is no
rounding boundary.  Correct at every fuel: on the dyadic set `QBase2D … QLnBetaPD` — a base
that is no positive real, arguments that are not both real, the poles and zeros of `B_q`
(values `NaN`, `+∞`, `−∞`), and `B_q(1, 1) = 1` (value `0`) —, and on the non-dyadic set
`QBase2N … QLnBetaPN`: **positive integers whose value is formed and is not `1`** (`ln` of a
positive rational `≠ 1` is irrational), in every base.

All twelve are instances of `qBase2_zivSpec` (a function of a base and two arguments: `NaN`
on a bad base, a given function at the base `1`, a given function on the real class), through
`lnAbsQBeta_zivSpec_sides` and `lnQBeta_zivSpec_sides`; the function on the real class is
`lnAbsQBetaOf` (`lnAbsQBetaOf_eq_or_loop`, `_main`, `_complete`) and `lnOfSigned` of it.
-/

namespace Azurite.AzFloat

open Filter Topology Finset DLMF

namespace Spec

/-- `ln |B_q|` for a real base `q > 0`, `q ≠ 1`, on the extended reals. -/
noncomputable def lnAbsQBetaAt (qv : ℝ) (a b : EReal) : Option EReal :=
  (qBetaAt qv a b).map lnAbsE

/-- **`ln |B_q(a, b)|` on the extended reals**: the logarithm of the absolute value of
`Spec.qBeta` (`lnAbsQBeta_eq`). -/
noncomputable def lnAbsQBeta (q a b : EReal) : Option EReal :=
  qBaseLift (fun x : EReal × EReal => lnAbsBeta x.1 x.2)
    (fun qv x => lnAbsQBetaAt qv x.1 x.2) q (a, b)

/-- `ln B_q` for a real base `q > 0`, `q ≠ 1`, on the extended reals. -/
noncomputable def lnQBetaAt (qv : ℝ) (a b : EReal) : Option EReal :=
  (qBetaAt qv a b).bind log

/-- **`ln B_q(a, b)` on the extended reals**: the logarithm of `Spec.qBeta`, undefined where
`B_q(a, b) < 0` (`lnQBeta_eq`). -/
noncomputable def lnQBeta (q a b : EReal) : Option EReal :=
  qBaseLift (fun x : EReal × EReal => lnBeta x.1 x.2) (fun qv x => lnQBetaAt qv x.1 x.2) q
    (a, b)

theorem lnAbsQBeta_eq (q a b : EReal) : lnAbsQBeta q a b = (qBeta q a b).map lnAbsE := by
  unfold lnAbsQBeta qBeta qBaseLift lnAbsQBetaAt lnAbsBeta
  split_ifs <;> rfl

theorem lnQBeta_eq (q a b : EReal) : lnQBeta q a b = (qBeta q a b).bind log := by
  unfold lnQBeta qBeta qBaseLift lnQBetaAt lnBeta
  split_ifs <;> rfl

theorem lnAbsE_zero' : lnAbsE (0 : EReal) = ⊥ := by
  rw [← EReal.coe_zero]
  exact lnAbsE_zero

/-- Where the value is not negative, `ln` is `ln |·|`. -/
theorem bind_log_eq_map_lnAbsE {o : Option EReal}
    (hnn : ∀ v : ℝ, o = some (v : EReal) → 0 ≤ v) (hb : o ≠ some ⊥) :
    o.bind log = o.map lnAbsE := by
  cases o with
  | none => rfl
  | some e =>
    induction e using EReal.rec with
    | bot => exact absurd rfl hb
    | top => rw [Option.bind_some, Option.map_some, log_top, lnAbsE_top]
    | coe r => rw [Option.bind_some, Option.map_some, log_coe_of_nonneg (hnn r rfl)]

theorem bind_log_eq_none {o : Option EReal} {v : ℝ} (h : o = some (v : EReal)) (hv : v < 0) :
    o.bind log = none := by
  rw [h, Option.bind_some, log_coe_neg v hv]

/-- At arguments that are not both real, `B_q` is undefined or `0`. -/
theorem qBetaAt_nonreal_cases (qv : ℝ) {x y : EReal}
    (h : ¬ ∃ av bv : ℝ, x = (av : EReal) ∧ y = (bv : EReal)) :
    qBetaAt qv x y = none ∨ qBetaAt qv x y = some 0 := by
  have hz : ∀ {c : Prop} [Decidable c], (if c then some (0 : EReal) else none) = none ∨
      (if c then some (0 : EReal) else none) = some 0 := by
    intro c _
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  induction x using EReal.rec with
  | bot => exact Or.inl (qBetaAt_bot_left qv y)
  | top =>
    induction y using EReal.rec with
    | bot => exact Or.inl (qBetaAt_bot_right qv _)
    | top =>
      rw [qBetaAt_top_top]
      exact hz
    | coe bv =>
      rw [qBetaAt_top_coe]
      exact hz
  | coe av =>
    induction y using EReal.rec with
    | bot => exact Or.inl (qBetaAt_bot_right qv _)
    | top =>
      rw [qBetaAt_coe_top]
      exact hz
    | coe bv => exact absurd ⟨av, bv, rfl, rfl⟩ h

/-- `B_q` is never `−∞` at real arguments. -/
theorem qBetaAt_coe_ne_bot (qv av bv : ℝ) : qBetaAt qv (av : EReal) (bv : EReal) ≠ some ⊥ := by
  by_cases hnp : (av < 0 ∧ ∃ k : ℤ, av = k) ∨ (bv < 0 ∧ ∃ k : ℤ, bv = k)
  · rw [qBetaAt_coe_of_pole qv hnp]
    simp
  · by_cases hz : av = 0 ∨ bv = 0
    · rw [qBetaAt_coe_of_zero qv hnp hz]
      simp
    · by_cases hs : av + bv ≤ 0 ∧ ∃ k : ℤ, av + bv = k
      · rw [qBetaAt_coe_of_sum qv hnp hz hs]
        simp
      · rw [qBetaAt_coe qv hnp hz hs]
        simp

end Spec

/-! ### A function of a base and two arguments -/

/-- The dyadic set of a function of a base and two arguments: a base that is no positive
real; or a base `q > 0`, `q ≠ 1`, with arguments that are not both real or with `PD`. -/
def QBase2D {α : Type*} (qe xe ye : α → Option EReal) (PD : α → ℝ → ℝ → ℝ → Prop) (a : α) :
    Prop :=
  (∀ qv : ℝ, qe a = some (qv : EReal) → qv ≤ 0) ∨
    ((∃ qv : ℝ, qe a = some (qv : EReal) ∧ 0 < qv ∧ qv ≠ 1) ∧
      ∀ qv av bv : ℝ, qe a = some (qv : EReal) → xe a = some (av : EReal) →
        ye a = some (bv : EReal) → PD a qv av bv)

/-- The non-dyadic set of a function of a base and two arguments: the real class with
`PN`. -/
def QBase2N {α : Type*} (qe xe ye : α → Option EReal) (PN : α → ℝ → ℝ → ℝ → Prop) (a : α) :
    Prop :=
  ∃ qv av bv : ℝ, qe a = some (qv : EReal) ∧ 0 < qv ∧ qv ≠ 1 ∧ xe a = some (av : EReal) ∧
    ye a = some (bv : EReal) ∧ PN a qv av bv

open Classical in
/-- **The specification of a function `f` of a base and two arguments** with values `qe`,
`xe`, `ye` in the extended reals: `NaN` on a base that is no positive real, the function `fΓ`
at the base `1`, the function `g` on the real class (a base `q > 0`, `q ≠ 1`, and real
arguments), and the rounding of the value at arguments that are not both real.  `PD` and `PN`
are properties on the real class where `g` is known to be exact with dyadic and non-dyadic
values. -/
theorem qBase2_zivSpec {α : Type*} {qe xe ye : α → Option EReal}
    {f fΓ g : ℕ → α → ℕ → RoundingMode → AzFloat × Ordering}
    {VΓ : EReal → EReal → Option EReal} {VAt : ℝ → EReal → EReal → Option EReal}
    (PD PN : α → ℝ → ℝ → ℝ → Prop)
    (hΓs : ∀ fuel a (p : ℕ) [NeZero p] mode,
      fΓ fuel a p mode = roundVal p mode ((xe a).bind fun x => (ye a).bind fun y => VΓ x y) ∨
        fΓ fuel a p mode = (nan, .eq))
    (hΓc : ∀ a (p : ℕ) [NeZero p] mode,
      (∀ v : ℝ, ((xe a).bind fun x => (ye a).bind fun y => VΓ x y) = some (v : EReal) →
        ((v : ℝ) : EReal) ∉ floatSet (p + 1)) →
      ∃ F : ℕ, ∀ fuel, F ≤ fuel → fΓ fuel a p mode
        = roundVal p mode ((xe a).bind fun x => (ye a).bind fun y => VΓ x y))
    (hgs : ∀ a (qv av bv : ℝ), qe a = some (qv : EReal) → 0 < qv → qv ≠ 1 →
      xe a = some (av : EReal) → ye a = some (bv : EReal) → ∀ fuel (p : ℕ) [NeZero p] mode,
      g fuel a p mode = roundVal p mode (VAt qv (av : EReal) (bv : EReal)) ∨
        g fuel a p mode = (nan, .eq))
    (hgc : ∀ a (qv av bv : ℝ), qe a = some (qv : EReal) → 0 < qv → qv ≠ 1 →
      xe a = some (av : EReal) → ye a = some (bv : EReal) → ∀ (p : ℕ) [NeZero p] mode,
      (∀ v : ℝ, VAt qv (av : EReal) (bv : EReal) = some (v : EReal) →
        ((v : ℝ) : EReal) ∉ floatSet (p + 1)) →
      ∃ F : ℕ, ∀ fuel, F ≤ fuel →
        g fuel a p mode = roundVal p mode (VAt qv (av : EReal) (bv : EReal)))
    (hD : ∀ a (qv av bv : ℝ), qe a = some (qv : EReal) → 0 < qv → qv ≠ 1 →
      xe a = some (av : EReal) → ye a = some (bv : EReal) → PD a qv av bv →
      (∀ v : ℝ, VAt qv (av : EReal) (bv : EReal) = some (v : EReal) → IsDyadic v) ∧
        ∀ fuel (p : ℕ) [NeZero p] mode,
          g fuel a p mode = roundVal p mode (VAt qv (av : EReal) (bv : EReal)))
    (hN : ∀ a (qv av bv : ℝ), qe a = some (qv : EReal) → 0 < qv → qv ≠ 1 →
      xe a = some (av : EReal) → ye a = some (bv : EReal) → PN a qv av bv →
      (∃ v : ℝ, VAt qv (av : EReal) (bv : EReal) = some (v : EReal) ∧ ¬ IsDyadic v) ∧
        ∀ fuel (p : ℕ) [NeZero p] mode,
          g fuel a p mode = roundVal p mode (VAt qv (av : EReal) (bv : EReal)))
    (hnr : ∀ (qv : ℝ) (x y : EReal), (¬ ∃ av bv : ℝ, x = (av : EReal) ∧ y = (bv : EReal)) →
      ∀ v : ℝ, VAt qv x y = some (v : EReal) → IsDyadic v)
    (hf_bad : ∀ fuel a p mode, (∀ qv : ℝ, qe a = some (qv : EReal) → qv ≤ 0) →
      f fuel a p mode = (nan, .eq))
    (hf_one : ∀ fuel a p mode, qe a = some ((1 : ℝ) : EReal) →
      f fuel a p mode = fΓ fuel a p mode)
    (hf_real : ∀ fuel a p mode (qv av bv : ℝ), qe a = some (qv : EReal) → 0 < qv → qv ≠ 1 →
      xe a = some (av : EReal) → ye a = some (bv : EReal) →
      f fuel a p mode = g fuel a p mode)
    (hf_nonreal : ∀ fuel a (p : ℕ) [NeZero p] mode (qv : ℝ), qe a = some (qv : EReal) →
      0 < qv → qv ≠ 1 →
      (¬ ∃ av bv : ℝ, xe a = some (av : EReal) ∧ ye a = some (bv : EReal)) →
      f fuel a p mode
        = roundVal p mode ((xe a).bind fun x => (ye a).bind fun y => VAt qv x y)) :
    ZivSpec
      (fun a => (qe a).bind fun q => (xe a).bind fun x => (ye a).bind fun y =>
        Spec.qBaseLift (fun z : EReal × EReal => VΓ z.1 z.2) (fun qv z => VAt qv z.1 z.2) q
          (x, y))
      f {a | QBase2D qe xe ye PD a} {a | QBase2N qe xe ye PN a} := by
  have hval_bad : ∀ a, (∀ qv : ℝ, qe a = some (qv : EReal) → qv ≤ 0) →
      ((qe a).bind fun q => (xe a).bind fun x => (ye a).bind fun y =>
        Spec.qBaseLift (fun z : EReal × EReal => VΓ z.1 z.2) (fun qv z => VAt qv z.1 z.2) q
          (x, y)) = none := by
    intro a hb
    cases hq : qe a with
    | none => rfl
    | some e =>
      rw [Option.bind_some]
      have hn : e ≤ 0 ∨ e = ⊤ := by
        induction e using EReal.rec with
        | bot => exact Or.inl bot_le
        | top => exact Or.inr rfl
        | coe r => exact Or.inl (by exact_mod_cast hb r hq)
      simp only [Spec.qBaseLift_none hn]
      exact bind_bind_const_none _ _
  have hval_one : ∀ a, qe a = some ((1 : ℝ) : EReal) →
      ((qe a).bind fun q => (xe a).bind fun x => (ye a).bind fun y =>
        Spec.qBaseLift (fun z : EReal × EReal => VΓ z.1 z.2) (fun qv z => VAt qv z.1 z.2) q
          (x, y)) = (xe a).bind fun x => (ye a).bind fun y => VΓ x y := by
    intro a hq
    rw [hq, Option.bind_some]
    simp only [EReal.coe_one, Spec.qBaseLift_one]
  have hval_pos : ∀ a (qv : ℝ), qe a = some (qv : EReal) → 0 < qv → qv ≠ 1 →
      ((qe a).bind fun q => (xe a).bind fun x => (ye a).bind fun y =>
        Spec.qBaseLift (fun z : EReal × EReal => VΓ z.1 z.2) (fun qv z => VAt qv z.1 z.2) q
          (x, y)) = (xe a).bind fun x => (ye a).bind fun y => VAt qv x y := by
    intro a qv hq h0 h1
    rw [hq, Option.bind_some]
    simp only [Spec.qBaseLift_coe h0 h1]
  have hval_real : ∀ a (qv av bv : ℝ), qe a = some (qv : EReal) → 0 < qv → qv ≠ 1 →
      xe a = some (av : EReal) → ye a = some (bv : EReal) →
      ((qe a).bind fun q => (xe a).bind fun x => (ye a).bind fun y =>
        Spec.qBaseLift (fun z : EReal × EReal => VΓ z.1 z.2) (fun qv z => VAt qv z.1 z.2) q
          (x, y)) = VAt qv (av : EReal) (bv : EReal) := by
    intro a qv av bv hq h0 h1 hx hy
    rw [hval_pos a qv hq h0 h1, hx, hy, Option.bind_some, Option.bind_some]
  have hnrd : ∀ a (qv : ℝ),
      (¬ ∃ av bv : ℝ, xe a = some (av : EReal) ∧ ye a = some (bv : EReal)) → ∀ v : ℝ,
      ((xe a).bind fun x => (ye a).bind fun y => VAt qv x y) = some (v : EReal) →
      IsDyadic v := by
    intro a qv hR v hv
    cases hxe : xe a with
    | none =>
      rw [hxe] at hv
      exact absurd hv (by simp)
    | some x =>
      cases hye : ye a with
      | none =>
        rw [hxe, hye] at hv
        exact absurd hv (by simp)
      | some y =>
        rw [hxe, hye, Option.bind_some, Option.bind_some] at hv
        exact hnr qv x y
          (fun ⟨av, bv, h1, h2⟩ => hR ⟨av, bv, by rw [hxe, h1], by rw [hye, h2]⟩) v hv
  have hcases : ∀ a, (∀ qv : ℝ, qe a = some (qv : EReal) → qv ≤ 0) ∨
      qe a = some ((1 : ℝ) : EReal) ∨
      ∃ qv : ℝ, qe a = some (qv : EReal) ∧ 0 < qv ∧ qv ≠ 1 ∧
        ((∃ av bv : ℝ, xe a = some (av : EReal) ∧ ye a = some (bv : EReal)) ∨
          ¬ ∃ av bv : ℝ, xe a = some (av : EReal) ∧ ye a = some (bv : EReal)) := by
    intro a
    by_cases hb : ∀ qv : ℝ, qe a = some (qv : EReal) → qv ≤ 0
    · exact Or.inl hb
    · push Not at hb
      obtain ⟨qv, hq, h0⟩ := hb
      by_cases h1 : qv = 1
      · exact Or.inr (Or.inl (h1 ▸ hq))
      · exact Or.inr (Or.inr ⟨qv, hq, h0, h1, Classical.em _⟩)
  refine ⟨fun fuel a p _ mode => ?_, fun a p _ mode hB => ?_, fun a ha v hv => ?_,
    fun a ha => ?_, fun a ha fuel p _ mode => ?_⟩
  · rcases hcases a with hb | h1 | ⟨qv, hq, h0, h1, ⟨av, bv, hx, hy⟩ | hx⟩
    · left
      rw [hf_bad fuel a p mode hb, hval_bad a hb, roundVal_none]
    · rw [hf_one fuel a p mode h1, hval_one a h1]
      exact hΓs fuel a p mode
    · rw [hf_real fuel a p mode qv av bv hq h0 h1 hx hy, hval_real a qv av bv hq h0 h1 hx hy]
      exact hgs a qv av bv hq h0 h1 hx hy fuel p mode
    · left
      rw [hf_nonreal fuel a p mode qv hq h0 h1 hx, hval_pos a qv hq h0 h1]
  · rcases hcases a with hb | h1 | ⟨qv, hq, h0, h1, ⟨av, bv, hx, hy⟩ | hx⟩
    · exact ⟨0, fun fuel _ => by rw [hf_bad fuel a p mode hb, hval_bad a hb, roundVal_none]⟩
    · rw [hval_one a h1] at hB ⊢
      obtain ⟨F, hF⟩ := hΓc a p mode hB
      exact ⟨F, fun fuel hfuel => by rw [hf_one fuel a p mode h1]; exact hF fuel hfuel⟩
    · rw [hval_real a qv av bv hq h0 h1 hx hy] at hB ⊢
      obtain ⟨F, hF⟩ := hgc a qv av bv hq h0 h1 hx hy p mode hB
      exact ⟨F, fun fuel hfuel => by
        rw [hf_real fuel a p mode qv av bv hq h0 h1 hx hy]; exact hF fuel hfuel⟩
    · exact ⟨0, fun fuel _ => by
        rw [hf_nonreal fuel a p mode qv hq h0 h1 hx, hval_pos a qv hq h0 h1]⟩
  · rcases ha with hb | ⟨⟨qv, hq, h0, h1⟩, hsp⟩
    · rw [hval_bad a hb] at hv
      exact absurd hv (by simp)
    · by_cases hR : ∃ av bv : ℝ, xe a = some (av : EReal) ∧ ye a = some (bv : EReal)
      · obtain ⟨av, bv, hx, hy⟩ := hR
        rw [hval_real a qv av bv hq h0 h1 hx hy] at hv
        exact (hD a qv av bv hq h0 h1 hx hy (hsp qv av bv hq hx hy)).1 v hv
      · rw [hval_pos a qv hq h0 h1] at hv
        exact hnrd a qv hR v hv
  · obtain ⟨qv, av, bv, hq, h0, h1, hx, hy, hPN⟩ := ha
    rw [hval_real a qv av bv hq h0 h1 hx hy]
    exact (hN a qv av bv hq h0 h1 hx hy hPN).1
  · rcases ha with (hb | ⟨⟨qv, hq, h0, h1⟩, hsp⟩) | ⟨qv, av, bv, hq, h0, h1, hx, hy, hPN⟩
    · rw [hf_bad fuel a p mode hb, hval_bad a hb, roundVal_none]
    · by_cases hR : ∃ av bv : ℝ, xe a = some (av : EReal) ∧ ye a = some (bv : EReal)
      · obtain ⟨av, bv, hx, hy⟩ := hR
        rw [hf_real fuel a p mode qv av bv hq h0 h1 hx hy,
          hval_real a qv av bv hq h0 h1 hx hy]
        exact (hD a qv av bv hq h0 h1 hx hy (hsp qv av bv hq hx hy)).2 fuel p mode
      · rw [hf_nonreal fuel a p mode qv hq h0 h1 hR, hval_pos a qv hq h0 h1]
    · rw [hf_real fuel a p mode qv av bv hq h0 h1 hx hy,
        hval_real a qv av bv hq h0 h1 hx hy]
      exact (hN a qv av bv hq h0 h1 hx hy hPN).2 fuel p mode

/-! ### `ln |B_q|` on a base and arguments -/

variable {Q : QBase} {Sa Sb Ss : QArg} {qv av bv : ℝ}

/-- The enclosure of `ln |B_q|` in terms of `B_q(a, b)`. -/
theorem qBetaLnEnclOf_real_spec (hQ : QBaseSpec Q qv) (hSa : QArgSpec Sa av)
    (hSb : QArgSpec Sb bv) (hSs : QSumSpec Ss (av + bv)) {w : ℕ} {neg : Bool} {L : Encl}
    (hc : qBetaLnEnclOf (qGammaInOf Q Sa) (qGammaInOf Q Sb) (qGammaInOf Q Ss) w
      = some (neg, L)) :
    0 < (if neg then (-1 : ℝ) else 1) * qBetaReal qv av bv ∧
      IsEncl L (Real.log ((if neg then (-1 : ℝ) else 1) * qBetaReal qv av bv)) :=
  qBetaLnEnclOf_spec
    (fun _ _ h => qGammaLnEnclOf_real_spec' hQ (qGammaArg_of hQ hSa) h)
    (fun _ _ h => qGammaLnEnclOf_real_spec' hQ (qGammaArg_of hQ hSb) h)
    (fun _ _ h => qGammaLnEnclOf_real_spec' hQ (qGammaArg_of_sum hQ hSa hSs) h) hc

/-- `B_q(a, b) ≠ 0` off the poles and the zeros. -/
theorem qBetaReal_ne_zero_of (hQ : QBaseSpec Q qv) (hSa : QArgSpec Sa av)
    (hSb : QArgSpec Sb bv) (hSs : QSumSpec Ss (av + bv)) (hnza : ∀ m : ℕ, av ≠ -m)
    (hnzb : ∀ m : ℕ, bv ≠ -m) (hnzs : ∀ m : ℕ, av + bv ≠ -m) : qBetaReal qv av bv ≠ 0 :=
  div_ne_zero
    (mul_ne_zero (qGammaReal_ne_zero_of hQ (qGammaArg_of hQ hSa) hnza)
      (qGammaReal_ne_zero_of hQ (qGammaArg_of hQ hSb) hnzb))
    (qGammaReal_ne_zero_of hQ (qGammaArg_of_sum hQ hSa hSs) hnzs)

/-- The enclosure of `ln |B_q|` converges off the poles and the zeros. -/
theorem qBetaLnEnclOf_real_conv (hQ : QBaseSpec Q qv) (hSa : QArgSpec Sa av)
    (hSb : QArgSpec Sb bv) (hSs : QSumSpec Ss (av + bv)) (hnza : ∀ m : ℕ, av ≠ -m)
    (hnzb : ∀ m : ℕ, bv ≠ -m) (hnzs : ∀ m : ℕ, av + bv ≠ -m) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ w in atTop, ∃ (neg : Bool) (L : Encl),
      qBetaLnEnclOf (qGammaInOf Q Sa) (qGammaInOf Q Sb) (qGammaInOf Q Ss) w = some (neg, L) ∧
        AEncl L (Real.log |qBetaReal qv av bv|) (ε w) := by
  have hAa := qGammaArg_of hQ hSa
  have hAb := qGammaArg_of hQ hSb
  have hAs := qGammaArg_of_sum hQ hSa hSs
  have ga0 := abs_ne_zero.mpr (qGammaReal_ne_zero_of hQ hAa hnza)
  have gb0 := abs_ne_zero.mpr (qGammaReal_ne_zero_of hQ hAb hnzb)
  have gs0 := abs_ne_zero.mpr (qGammaReal_ne_zero_of hQ hAs hnzs)
  have hlog : Real.log |qGammaReal qv av| + Real.log |qGammaReal qv bv|
      - Real.log |qGammaReal qv (av + bv)| = Real.log |qBetaReal qv av bv| := by
    unfold qBetaReal
    rw [abs_div, abs_mul, Real.log_div (mul_ne_zero ga0 gb0) gs0, Real.log_mul ga0 gb0]
  have hc := qBetaLnEnclOf_conv (qGammaLnEnclOf_real_conv hQ hAa hnza)
    (qGammaLnEnclOf_real_conv hQ hAb hnzb) (qGammaLnEnclOf_real_conv hQ hAs hnzs)
  rwa [hlog] at hc

/-- `B_q(m, n) > 0` at positive integers. -/
theorem qBetaReal_pos_of_exact (hQ : QBaseSpec Q qv) (hSa : QArgSpec Sa av)
    (hSb : QArgSpec Sb bv) {p : ℕ} {r : AzRat}
    (hex : qBetaExact? Q Sa.kind Sb.kind p = some r) :
    0 < qBetaReal qv av bv ∧ (∀ m : ℕ, av ≠ -m) ∧ (∀ m : ℕ, bv ≠ -m) ∧
      ∀ m : ℕ, av + bv ≠ -m := by
  obtain ⟨m, n, ra, rb, rc, hka, hkb, -, -, -, -⟩ := qBetaExact?_eq_some hex
  have hA := hSa.kind
  rw [hka] at hA
  obtain ⟨hm1, ham⟩ := hA
  have hB := hSb.kind
  rw [hkb] at hB
  obtain ⟨hn1, hbn⟩ := hB
  have h1 : (0 : ℝ) < av := by rw [ham]; exact_mod_cast hm1
  have h2 : (0 : ℝ) < bv := by rw [hbn]; exact_mod_cast hn1
  refine ⟨?_, posInt_ne_neg_nat hm1 ham, posInt_ne_neg_nat hn1 hbn,
    posInt_ne_neg_nat (n := m + n) (by omega) (by rw [ham, hbn]; push_cast; ring)⟩
  unfold qBetaReal
  exact div_pos (mul_pos (qGammaReal_pos hQ.pos h1) (qGammaReal_pos hQ.pos h2))
    (qGammaReal_pos hQ.pos (by linarith))

/-- **`ln |B_q|` on a base and arguments is correctly rounded with the sign `true` (and
`B_q ≥ 0`), or it is the loop** off the poles and the zeros. -/
theorem lnAbsQBetaOf_eq_or_loop (hQ : QBaseSpec Q qv) (hSa : QArgSpec Sa av)
    (hSb : QArgSpec Sb bv) (hSs : QSumSpec Ss (av + bv)) (fuel p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    (lnAbsQBetaOf Q Sa Sb Ss fuel p mode
        = (roundVal p mode (Spec.lnAbsQBetaAt qv (av : EReal) (bv : EReal)), true) ∧
        ∀ v : ℝ, Spec.qBetaAt qv (av : EReal) (bv : EReal) = some (v : EReal) → 0 ≤ v) ∨
      ((∀ m : ℕ, av ≠ -m) ∧ (∀ m : ℕ, bv ≠ -m) ∧ (∀ m : ℕ, av + bv ≠ -m) ∧
        qBetaExact? Q Sa.kind Sb.kind p = none ∧
        lnAbsQBetaOf Q Sa Sb Ss fuel p mode
          = lnAbsLoop (qBetaLnEnclOf (qGammaInOf Q Sa) (qGammaInOf Q Sb) (qGammaInOf Q Ss))
            p mode fuel (max 64 (p + 32))) := by
  have hp := NeZero.ne p
  unfold lnAbsQBetaOf
  by_cases hpole : (Sa.kind.isPole || Sb.kind.isPole) = true
  · rw [ite_eq_left hpole]
    rw [Bool.or_eq_true, hSa.isPole_iff, hSb.isPole_iff] at hpole
    have hval := Spec.qBetaAt_coe_of_pole qv hpole
    refine Or.inl ⟨?_, fun v h => ?_⟩
    · rw [Spec.lnAbsQBetaAt, hval, Option.map_none, roundVal_none]
    · rw [hval] at h
      exact absurd h (by simp)
  · rw [ite_eq_right hpole]
    have hnp : ¬ ((av < 0 ∧ ∃ k : ℤ, av = k) ∨ (bv < 0 ∧ ∃ k : ℤ, bv = k)) := by
      rw [Bool.or_eq_true, hSa.isPole_iff, hSb.isPole_iff] at hpole
      exact hpole
    by_cases hzero : (Sa.kind.isZero || Sb.kind.isZero) = true
    · rw [ite_eq_left hzero]
      rw [Bool.or_eq_true, hSa.isZero_iff, hSb.isZero_iff] at hzero
      have hval := Spec.qBetaAt_coe_of_zero qv hnp hzero
      refine Or.inl ⟨?_, fun v h => ?_⟩
      · rw [Spec.lnAbsQBetaAt, hval, Option.map_some, Spec.lnAbsE_top, roundVal_top]
      · rw [hval] at h
        exact absurd h (by simp)
    · rw [ite_eq_right hzero, ite_eq_right hp]
      have hz : ¬ (av = 0 ∨ bv = 0) := by
        rw [Bool.or_eq_true, hSa.isZero_iff, hSb.isZero_iff] at hzero
        exact hzero
      by_cases hsum : (Ss.kind.isZero || Ss.kind.isPole) = true
      · rw [ite_eq_left hsum]
        have hval := Spec.qBetaAt_coe_of_sum qv hnp hz
          (nonpos_int_iff_neg_nat.mpr (hSs.kind.mp hsum))
        refine Or.inl ⟨?_, fun v h => ?_⟩
        · rw [Spec.lnAbsQBetaAt, hval, Option.map_some, Spec.lnAbsE_zero', roundVal_bot]
        · rw [hval, Option.some.injEq] at h
          exact le_of_eq (by exact_mod_cast h)
      · rw [ite_eq_right hsum]
        have hnza : ∀ m : ℕ, av ≠ -m :=
          ne_neg_nat_of_not_pole (fun h => hz (Or.inl h)) (fun h => hnp (Or.inl h))
        have hnzb : ∀ m : ℕ, bv ≠ -m :=
          ne_neg_nat_of_not_pole (fun h => hz (Or.inr h)) (fun h => hnp (Or.inr h))
        have hnzs : ∀ m : ℕ, av + bv ≠ -m := fun m h => hsum (hSs.kind.mpr ⟨m, h⟩)
        cases hex : qBetaExact? Q Sa.kind Sb.kind p with
        | none => exact Or.inr ⟨hnza, hnzb, hnzs, rfl, rfl⟩
        | some r =>
          have hpos := (qBetaReal_pos_of_exact hQ hSa hSb hex).1
          have hval := qBetaAt_general qv hnza hnzb hnzs
          refine Or.inl ⟨?_, fun v h => ?_⟩
          · dsimp only
            rw [lnRatPrecRound_eq, qBetaExact?_spec hQ hSa hSb hex, Spec.log_coe _ hpos,
              Spec.lnAbsQBetaAt, hval, Option.map_some, Spec.lnAbsE_coe hpos.ne',
              abs_of_pos hpos]
          · rw [hval, Option.some.injEq, EReal.coe_eq_coe_iff] at h
            rw [← h]
            exact hpos.le

/-- **`ln |B_q|` with the sign**: `NaN`, or the rounding of `ln |B_q(a, b)|` with
`B_q(a, b) ≥ 0` as the sign. -/
theorem lnAbsQBetaOf_main (hQ : QBaseSpec Q qv) (hSa : QArgSpec Sa av) (hSb : QArgSpec Sb bv)
    (hSs : QSumSpec Ss (av + bv)) (fuel p : ℕ) [NeZero p] (mode : RoundingMode) :
    (lnAbsQBetaOf Q Sa Sb Ss fuel p mode).1 = (nan, .eq) ∨
      ((lnAbsQBetaOf Q Sa Sb Ss fuel p mode).1
          = roundVal p mode (Spec.lnAbsQBetaAt qv (av : EReal) (bv : EReal)) ∧
        ((lnAbsQBetaOf Q Sa Sb Ss fuel p mode).2 = true ↔
          ∀ v : ℝ, Spec.qBetaAt qv (av : EReal) (bv : EReal) = some (v : EReal) → 0 ≤ v)) := by
  rcases lnAbsQBetaOf_eq_or_loop hQ hSa hSb hSs fuel p mode with
    ⟨h, hnn⟩ | ⟨hnza, hnzb, hnzs, -, h⟩
  · right
    rw [h]
    exact ⟨rfl, fun _ => hnn, fun _ => rfl⟩
  · rw [h]
    have hB0 := qBetaReal_ne_zero_of hQ hSa hSb hSs hnza hnzb hnzs
    have hval := qBetaAt_general qv hnza hnzb hnzs
    rcases lnAbsLoop_spec (v := qBetaReal qv av bv) (w₀ := 64)
      (fun w _ neg L hc => qBetaLnEnclOf_real_spec hQ hSa hSb hSs hc) p mode fuel _
      (le_max_left _ _) with h1 | ⟨h1, h2⟩
    · exact Or.inl h1
    · right
      refine ⟨by rw [h1, Spec.lnAbsQBetaAt, hval, Option.map_some, Spec.lnAbsE_coe hB0],
        h2.trans ⟨fun hpos v hv => ?_, fun hnn => ?_⟩⟩
      · rw [hval, Option.some.injEq, EReal.coe_eq_coe_iff] at hv
        rw [← hv]
        exact hpos.le
      · exact lt_of_le_of_ne (hnn _ hval) (Ne.symm hB0)

/-- **`ln |B_q|` is correctly rounded for every large enough fuel** where the value is no
rounding boundary. -/
theorem lnAbsQBetaOf_complete (hQ : QBaseSpec Q qv) (hSa : QArgSpec Sa av)
    (hSb : QArgSpec Sb bv) (hSs : QSumSpec Ss (av + bv)) (p : ℕ) [NeZero p]
    (mode : RoundingMode)
    (hB : ∀ v : ℝ, Spec.lnAbsQBetaAt qv (av : EReal) (bv : EReal) = some (v : EReal) →
      ((v : ℝ) : EReal) ∉ floatSet (p + 1)) :
    ∃ F : ℕ, ∀ fuel, F ≤ fuel → (lnAbsQBetaOf Q Sa Sb Ss fuel p mode).1
      = roundVal p mode (Spec.lnAbsQBetaAt qv (av : EReal) (bv : EReal)) := by
  by_cases hg : (∀ m : ℕ, av ≠ -m) ∧ (∀ m : ℕ, bv ≠ -m) ∧ ∀ m : ℕ, av + bv ≠ -m
  · obtain ⟨hnza, hnzb, hnzs⟩ := hg
    have hB0 := qBetaReal_ne_zero_of hQ hSa hSb hSs hnza hnzb hnzs
    have hlat : Spec.lnAbsQBetaAt qv (av : EReal) (bv : EReal)
        = some ((Real.log |qBetaReal qv av bv| : ℝ) : EReal) := by
      rw [Spec.lnAbsQBetaAt, qBetaAt_general qv hnza hnzb hnzs, Option.map_some,
        Spec.lnAbsE_coe hB0]
    have hB' := hB _ hlat
    obtain ⟨F, hF⟩ := lnAbsLoop_eventually (v := Real.log |qBetaReal qv av bv|) p mode
      (core := qBetaLnEnclOf (qGammaInOf Q Sa) (qGammaInOf Q Sb) (qGammaInOf Q Ss))
      (w₀ := max 64 (p + 32)) (by omega)
      (fun w hw neg L hc => by
        obtain ⟨hpos, hL⟩ := qBetaLnEnclOf_real_spec hQ hSa hSb hSs hc
        rwa [sign_mul_eq_abs hpos] at hL)
      (qBetaLnEnclOf_real_conv hQ hSa hSb hSs hnza hnzb hnzs) hB'
    refine ⟨F, fun fuel hfuel => ?_⟩
    rcases lnAbsQBetaOf_eq_or_loop hQ hSa hSb hSs fuel p mode with
      ⟨h, -⟩ | ⟨-, -, -, -, h⟩
    · rw [h]
    · rw [h, hlat]
      exact hF fuel hfuel
  · refine ⟨0, fun fuel _ => ?_⟩
    rcases lnAbsQBetaOf_eq_or_loop hQ hSa hSb hSs fuel p mode with
      ⟨h, -⟩ | ⟨h1, h2, h3, -, -⟩
    · rw [h]
    · exact absurd ⟨h1, h2, h3⟩ hg

/-! ### The classes of exact values -/

/-- The property with the values `NaN`, `±∞` and `0`: `a`, `b` or `a + b` a non-positive
integer, or positive integers whose value is formed and is `1`. -/
def QLnBetaPD {α : Type*} (Q : α → QBase) (Sa Sb : α → QArg) (a : α) (qv av bv : ℝ) : Prop :=
  (∃ m : ℕ, av = -m) ∨ (∃ m : ℕ, bv = -m) ∨ (∃ m : ℕ, av + bv = -m) ∨
    ((qBetaExact? (Q a) (Sa a).kind (Sb a).kind 0).isSome = true ∧ qBetaReal qv av bv = 1)

/-- The property with irrational values: positive integers whose value is formed and is not
`1`. -/
def QLnBetaPN {α : Type*} (Q : α → QBase) (Sa Sb : α → QArg) (a : α) (qv av bv : ℝ) : Prop :=
  (qBetaExact? (Q a) (Sa a).kind (Sb a).kind 0).isSome = true ∧ qBetaReal qv av bv ≠ 1

/-- On the exact classes the result is correctly rounded at every fuel, with the sign `true`,
and `B_q ≥ 0`. -/
theorem lnAbsQBetaOf_exact (hQ : QBaseSpec Q qv) (hSa : QArgSpec Sa av) (hSb : QArgSpec Sb bv)
    (hSs : QSumSpec Ss (av + bv))
    (hE : (∃ m : ℕ, av = -m) ∨ (∃ m : ℕ, bv = -m) ∨ (∃ m : ℕ, av + bv = -m) ∨
      (qBetaExact? Q Sa.kind Sb.kind 0).isSome = true) (fuel p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    lnAbsQBetaOf Q Sa Sb Ss fuel p mode
        = (roundVal p mode (Spec.lnAbsQBetaAt qv (av : EReal) (bv : EReal)), true) ∧
      ∀ v : ℝ, Spec.qBetaAt qv (av : EReal) (bv : EReal) = some (v : EReal) → 0 ≤ v := by
  rcases lnAbsQBetaOf_eq_or_loop hQ hSa hSb hSs fuel p mode with h | ⟨ha, hb, hs, hn, -⟩
  · exact h
  · rcases hE with ⟨m, h⟩ | ⟨m, h⟩ | ⟨m, h⟩ | h
    · exact absurd h (ha m)
    · exact absurd h (hb m)
    · exact absurd h (hs m)
    · have := qBetaExact?_isSome_mono h p
      rw [hn] at this
      exact absurd this (by simp)

/-- At the poles and the zeros `ln |B_q|` has no real value. -/
theorem lnAbsQBetaAt_special_nonreal (qv : ℝ) {av bv : ℝ}
    (hsp : (∃ m : ℕ, av = -m) ∨ (∃ m : ℕ, bv = -m) ∨ ∃ m : ℕ, av + bv = -m) (v : ℝ) :
    Spec.lnAbsQBetaAt qv (av : EReal) (bv : EReal) ≠ some (v : EReal) := by
  unfold Spec.lnAbsQBetaAt
  by_cases hnp : (av < 0 ∧ ∃ k : ℤ, av = k) ∨ (bv < 0 ∧ ∃ k : ℤ, bv = k)
  · rw [Spec.qBetaAt_coe_of_pole qv hnp]
    simp
  · by_cases hz : av = 0 ∨ bv = 0
    · rw [Spec.qBetaAt_coe_of_zero qv hnp hz, Option.map_some, Spec.lnAbsE_top]
      simp
    · by_cases hs : av + bv ≤ 0 ∧ ∃ k : ℤ, av + bv = k
      · rw [Spec.qBetaAt_coe_of_sum qv hnp hz hs, Option.map_some, Spec.lnAbsE_zero']
        simp
      · exfalso
        rcases hsp with ⟨m, h⟩ | ⟨m, h⟩ | ⟨m, h⟩
        · exact ne_neg_nat_of_not_pole (fun h0 => hz (Or.inl h0))
            (fun hc => hnp (Or.inl hc)) m h
        · exact ne_neg_nat_of_not_pole (fun h0 => hz (Or.inr h0))
            (fun hc => hnp (Or.inr hc)) m h
        · exact hs (nonpos_int_iff_neg_nat.mpr ⟨m, h⟩)

/-- At positive integers whose value is formed, `ln |B_q|` is the logarithm of a positive
rational. -/
theorem lnAbsQBetaAt_of_exact (hQ : QBaseSpec Q qv) (hSa : QArgSpec Sa av)
    (hSb : QArgSpec Sb bv) (hE : (qBetaExact? Q Sa.kind Sb.kind 0).isSome = true) :
    Spec.lnAbsQBetaAt qv (av : EReal) (bv : EReal)
        = some ((Real.log (qBetaReal qv av bv) : ℝ) : EReal) ∧
      ∃ r : ℚ, 0 < r ∧ ((r : ℚ) : ℝ) = qBetaReal qv av bv := by
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hE
  obtain ⟨hpos, hnza, hnzb, hnzs⟩ := qBetaReal_pos_of_exact hQ hSa hSb hr
  have hspec := qBetaExact?_spec hQ hSa hSb hr
  refine ⟨?_, AzRat.toRat r, ?_, hspec⟩
  · rw [Spec.lnAbsQBetaAt, qBetaAt_general qv hnza hnzb hnzs, Option.map_some,
      Spec.lnAbsE_coe hpos.ne', abs_of_pos hpos]
  · have : (0 : ℝ) < ((AzRat.toRat r : ℚ) : ℝ) := by rw [hspec]; exact hpos
    exact_mod_cast this

/-- On `QLnBetaPD` the real values are `0`. -/
theorem lnAbsQBetaAt_dyadic (hQ : QBaseSpec Q qv) (hSa : QArgSpec Sa av) (hSb : QArgSpec Sb bv)
    (hD : (∃ m : ℕ, av = -m) ∨ (∃ m : ℕ, bv = -m) ∨ (∃ m : ℕ, av + bv = -m) ∨
      ((qBetaExact? Q Sa.kind Sb.kind 0).isSome = true ∧ qBetaReal qv av bv = 1)) {v : ℝ}
    (hv : Spec.lnAbsQBetaAt qv (av : EReal) (bv : EReal) = some (v : EReal)) : IsDyadic v := by
  rcases hD with h | h | h | ⟨hE, h1⟩
  · exact absurd hv (lnAbsQBetaAt_special_nonreal qv (Or.inl h) v)
  · exact absurd hv (lnAbsQBetaAt_special_nonreal qv (Or.inr (Or.inl h)) v)
  · exact absurd hv (lnAbsQBetaAt_special_nonreal qv (Or.inr (Or.inr h)) v)
  · rw [(lnAbsQBetaAt_of_exact hQ hSa hSb hE).1, h1, Real.log_one, Option.some.injEq,
      EReal.coe_eq_coe_iff] at hv
    rw [← hv]
    exact isDyadic_zero

/-- On `QLnBetaPN` the value is irrational. -/
theorem lnAbsQBetaAt_not_dyadic (hQ : QBaseSpec Q qv) (hSa : QArgSpec Sa av)
    (hSb : QArgSpec Sb bv)
    (hN : (qBetaExact? Q Sa.kind Sb.kind 0).isSome = true ∧ qBetaReal qv av bv ≠ 1) :
    ∃ v : ℝ, Spec.lnAbsQBetaAt qv (av : EReal) (bv : EReal) = some (v : EReal) ∧
      ¬ IsDyadic v := by
  obtain ⟨hval, r, hr0, hr⟩ := lnAbsQBetaAt_of_exact hQ hSa hSb hN.1
  refine ⟨_, hval, not_isDyadic_of_irrational ?_⟩
  rw [← hr]
  exact irrational_log_rat hr0 (fun h1 => hN.2 (by rw [← hr, h1]; simp))

/-! ### `ln B_q` on a base and arguments -/

theorem lnQBetaAt_eq_of_nonneg {qv av bv : ℝ}
    (hnn : ∀ v : ℝ, Spec.qBetaAt qv (av : EReal) (bv : EReal) = some (v : EReal) → 0 ≤ v) :
    Spec.lnQBetaAt qv (av : EReal) (bv : EReal)
      = Spec.lnAbsQBetaAt qv (av : EReal) (bv : EReal) :=
  Spec.bind_log_eq_map_lnAbsE hnn (Spec.qBetaAt_coe_ne_bot qv av bv)

theorem lnQBetaAt_eq_none_of_neg {qv av bv : ℝ}
    (hnn : ¬ ∀ v : ℝ, Spec.qBetaAt qv (av : EReal) (bv : EReal) = some (v : EReal) → 0 ≤ v) :
    Spec.lnQBetaAt qv (av : EReal) (bv : EReal) = none := by
  push Not at hnn
  obtain ⟨v, hv, hneg⟩ := hnn
  exact Spec.bind_log_eq_none hv hneg

/-- **`ln B_q`**: the rounding of `ln B_q(a, b)` (`NaN` where `B_q(a, b) < 0`), or `NaN`. -/
theorem lnQBetaOf_main (hQ : QBaseSpec Q qv) (hSa : QArgSpec Sa av) (hSb : QArgSpec Sb bv)
    (hSs : QSumSpec Ss (av + bv)) (fuel p : ℕ) [NeZero p] (mode : RoundingMode) :
    lnOfSigned (lnAbsQBetaOf Q Sa Sb Ss fuel p mode)
        = roundVal p mode (Spec.lnQBetaAt qv (av : EReal) (bv : EReal)) ∨
      lnOfSigned (lnAbsQBetaOf Q Sa Sb Ss fuel p mode) = (nan, .eq) := by
  unfold lnOfSigned
  rcases lnAbsQBetaOf_main hQ hSa hSb hSs fuel p mode with h | ⟨h1, h2⟩
  · right
    split_ifs
    · exact h
    · rfl
  · by_cases hnn : ∀ v : ℝ, Spec.qBetaAt qv (av : EReal) (bv : EReal) = some (v : EReal) →
        0 ≤ v
    · left
      rw [ite_eq_left (h2.mpr hnn), h1, lnQBetaAt_eq_of_nonneg hnn]
    · right
      rw [ite_eq_right fun h => hnn (h2.mp h)]

/-- **`ln B_q` is correctly rounded for every large enough fuel** where the value is no
rounding boundary. -/
theorem lnQBetaOf_complete (hQ : QBaseSpec Q qv) (hSa : QArgSpec Sa av) (hSb : QArgSpec Sb bv)
    (hSs : QSumSpec Ss (av + bv)) (p : ℕ) [NeZero p] (mode : RoundingMode)
    (hB : ∀ v : ℝ, Spec.lnQBetaAt qv (av : EReal) (bv : EReal) = some (v : EReal) →
      ((v : ℝ) : EReal) ∉ floatSet (p + 1)) :
    ∃ F : ℕ, ∀ fuel, F ≤ fuel → lnOfSigned (lnAbsQBetaOf Q Sa Sb Ss fuel p mode)
      = roundVal p mode (Spec.lnQBetaAt qv (av : EReal) (bv : EReal)) := by
  by_cases hnn : ∀ v : ℝ, Spec.qBetaAt qv (av : EReal) (bv : EReal) = some (v : EReal) → 0 ≤ v
  · rw [lnQBetaAt_eq_of_nonneg hnn] at hB ⊢
    obtain ⟨F, hF⟩ := lnAbsQBetaOf_complete hQ hSa hSb hSs p mode hB
    refine ⟨F, fun fuel hfuel => ?_⟩
    have h1 := hF fuel hfuel
    unfold lnOfSigned
    rcases lnAbsQBetaOf_main hQ hSa hSb hSs fuel p mode with h | ⟨-, h2⟩
    · split_ifs
      · exact h1
      · rw [← h1, h]
    · rw [ite_eq_left (h2.mpr hnn)]
      exact h1
  · refine ⟨0, fun fuel _ => ?_⟩
    rw [lnQBetaAt_eq_none_of_neg hnn, roundVal_none]
    unfold lnOfSigned
    rcases lnAbsQBetaOf_main hQ hSa hSb hSs fuel p mode with h | ⟨-, h2⟩
    · split_ifs
      · exact h
      · rfl
    · rw [ite_eq_right fun h => hnn (h2.mp h)]

/-- On the exact classes `ln B_q` is correctly rounded at every fuel. -/
theorem lnQBetaOf_exact (hQ : QBaseSpec Q qv) (hSa : QArgSpec Sa av) (hSb : QArgSpec Sb bv)
    (hSs : QSumSpec Ss (av + bv))
    (hE : (∃ m : ℕ, av = -m) ∨ (∃ m : ℕ, bv = -m) ∨ (∃ m : ℕ, av + bv = -m) ∨
      (qBetaExact? Q Sa.kind Sb.kind 0).isSome = true) (fuel p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    lnOfSigned (lnAbsQBetaOf Q Sa Sb Ss fuel p mode)
      = roundVal p mode (Spec.lnQBetaAt qv (av : EReal) (bv : EReal)) ∧
    Spec.lnQBetaAt qv (av : EReal) (bv : EReal)
      = Spec.lnAbsQBetaAt qv (av : EReal) (bv : EReal) := by
  obtain ⟨h, hnn⟩ := lnAbsQBetaOf_exact hQ hSa hSb hSs hE fuel p mode
  refine ⟨?_, lnQBetaAt_eq_of_nonneg hnn⟩
  rw [h, lnQBetaAt_eq_of_nonneg hnn]
  rfl

/-! ### The specifications, generically -/

/-- **The specification of a function that is `ln |B_q|`** on a base and two arguments with
values `qe`, `xe`, `ye` in the extended reals. -/
theorem lnAbsQBeta_zivSpec_sides {α : Type*} {qe xe ye : α → Option EReal}
    {f fΓ : ℕ → α → ℕ → RoundingMode → AzFloat × Ordering} (Q : α → QBase)
    (Sa Sb Ss : α → QArg)
    (hbase : ∀ a (qv : ℝ), qe a = some (qv : EReal) → 0 < qv → qv ≠ 1 → QBaseSpec (Q a) qv)
    (harg : ∀ a (av bv : ℝ), xe a = some (av : EReal) → ye a = some (bv : EReal) →
      QArgSpec (Sa a) av ∧ QArgSpec (Sb a) bv ∧ QSumSpec (Ss a) (av + bv))
    (hΓs : ∀ fuel a (p : ℕ) [NeZero p] mode,
      fΓ fuel a p mode
          = roundVal p mode ((xe a).bind fun x => (ye a).bind fun y => Spec.lnAbsBeta x y) ∨
        fΓ fuel a p mode = (nan, .eq))
    (hΓc : ∀ a (p : ℕ) [NeZero p] mode,
      (∀ v : ℝ, ((xe a).bind fun x => (ye a).bind fun y => Spec.lnAbsBeta x y)
        = some (v : EReal) → ((v : ℝ) : EReal) ∉ floatSet (p + 1)) →
      ∃ F : ℕ, ∀ fuel, F ≤ fuel → fΓ fuel a p mode
        = roundVal p mode ((xe a).bind fun x => (ye a).bind fun y => Spec.lnAbsBeta x y))
    (hf_bad : ∀ fuel a p mode, (∀ qv : ℝ, qe a = some (qv : EReal) → qv ≤ 0) →
      f fuel a p mode = (nan, .eq))
    (hf_one : ∀ fuel a p mode, qe a = some ((1 : ℝ) : EReal) →
      f fuel a p mode = fΓ fuel a p mode)
    (hf_real : ∀ fuel a p mode (qv av bv : ℝ), qe a = some (qv : EReal) → 0 < qv → qv ≠ 1 →
      xe a = some (av : EReal) → ye a = some (bv : EReal) →
      f fuel a p mode = (lnAbsQBetaOf (Q a) (Sa a) (Sb a) (Ss a) fuel p mode).1)
    (hf_nonreal : ∀ fuel a (p : ℕ) [NeZero p] mode (qv : ℝ), qe a = some (qv : EReal) →
      0 < qv → qv ≠ 1 →
      (¬ ∃ av bv : ℝ, xe a = some (av : EReal) ∧ ye a = some (bv : EReal)) →
      f fuel a p mode = roundVal p mode
        ((xe a).bind fun x => (ye a).bind fun y => Spec.lnAbsQBetaAt qv x y)) :
    ZivSpec
      (fun a => (qe a).bind fun q => (xe a).bind fun x => (ye a).bind fun y =>
        Spec.lnAbsQBeta q x y)
      f {a | QBase2D qe xe ye (QLnBetaPD Q Sa Sb) a}
      {a | QBase2N qe xe ye (QLnBetaPN Q Sa Sb) a} :=
  qBase2_zivSpec (g := fun fuel a p mode =>
      (lnAbsQBetaOf (Q a) (Sa a) (Sb a) (Ss a) fuel p mode).1)
    (QLnBetaPD Q Sa Sb) (QLnBetaPN Q Sa Sb) hΓs hΓc
    (hgs := fun a qv av bv hq h0 h1 hx hy fuel p _ mode => by
      obtain ⟨hSa, hSb, hSs⟩ := harg a av bv hx hy
      rcases lnAbsQBetaOf_main (hbase a qv hq h0 h1) hSa hSb hSs fuel p mode with h | h
      · exact Or.inr h
      · exact Or.inl h.1)
    (hgc := fun a qv av bv hq h0 h1 hx hy p _ mode hB => by
      obtain ⟨hSa, hSb, hSs⟩ := harg a av bv hx hy
      exact lnAbsQBetaOf_complete (hbase a qv hq h0 h1) hSa hSb hSs p mode hB)
    (hD := fun a qv av bv hq h0 h1 hx hy hPD => by
      obtain ⟨hSa, hSb, hSs⟩ := harg a av bv hx hy
      have hPD' : (∃ m : ℕ, av = -m) ∨ (∃ m : ℕ, bv = -m) ∨ (∃ m : ℕ, av + bv = -m) ∨
          ((qBetaExact? (Q a) (Sa a).kind (Sb a).kind 0).isSome = true ∧
            qBetaReal qv av bv = 1) := hPD
      exact ⟨fun v hv => lnAbsQBetaAt_dyadic (hbase a qv hq h0 h1) hSa hSb hPD' hv,
        fun fuel p _ mode => by
          rw [(lnAbsQBetaOf_exact (hbase a qv hq h0 h1) hSa hSb hSs
            (hPD'.imp_right (Or.imp_right (Or.imp_right And.left))) fuel p mode).1]⟩)
    (hN := fun a qv av bv hq h0 h1 hx hy hPN => by
      obtain ⟨hSa, hSb, hSs⟩ := harg a av bv hx hy
      have hPN' : (qBetaExact? (Q a) (Sa a).kind (Sb a).kind 0).isSome = true ∧
          qBetaReal qv av bv ≠ 1 := hPN
      exact ⟨lnAbsQBetaAt_not_dyadic (hbase a qv hq h0 h1) hSa hSb hPN',
        fun fuel p _ mode => by
          rw [(lnAbsQBetaOf_exact (hbase a qv hq h0 h1) hSa hSb hSs
            (Or.inr (Or.inr (Or.inr hPN'.1))) fuel p mode).1]⟩)
    (hnr := fun qv x y h v hv => by
      rcases Spec.qBetaAt_nonreal_cases qv h with h0 | h0
      · rw [Spec.lnAbsQBetaAt, h0] at hv
        exact absurd hv (by simp)
      · rw [Spec.lnAbsQBetaAt, h0, Option.map_some, Spec.lnAbsE_zero'] at hv
        exact absurd hv (by simp))
    hf_bad hf_one hf_real hf_nonreal

/-- **The specification of a function that is `ln B_q`** on a base and two arguments with
values `qe`, `xe`, `ye` in the extended reals. -/
theorem lnQBeta_zivSpec_sides {α : Type*} {qe xe ye : α → Option EReal}
    {f fΓ : ℕ → α → ℕ → RoundingMode → AzFloat × Ordering} (Q : α → QBase)
    (Sa Sb Ss : α → QArg)
    (hbase : ∀ a (qv : ℝ), qe a = some (qv : EReal) → 0 < qv → qv ≠ 1 → QBaseSpec (Q a) qv)
    (harg : ∀ a (av bv : ℝ), xe a = some (av : EReal) → ye a = some (bv : EReal) →
      QArgSpec (Sa a) av ∧ QArgSpec (Sb a) bv ∧ QSumSpec (Ss a) (av + bv))
    (hΓs : ∀ fuel a (p : ℕ) [NeZero p] mode,
      fΓ fuel a p mode
          = roundVal p mode ((xe a).bind fun x => (ye a).bind fun y => Spec.lnBeta x y) ∨
        fΓ fuel a p mode = (nan, .eq))
    (hΓc : ∀ a (p : ℕ) [NeZero p] mode,
      (∀ v : ℝ, ((xe a).bind fun x => (ye a).bind fun y => Spec.lnBeta x y)
        = some (v : EReal) → ((v : ℝ) : EReal) ∉ floatSet (p + 1)) →
      ∃ F : ℕ, ∀ fuel, F ≤ fuel → fΓ fuel a p mode
        = roundVal p mode ((xe a).bind fun x => (ye a).bind fun y => Spec.lnBeta x y))
    (hf_bad : ∀ fuel a p mode, (∀ qv : ℝ, qe a = some (qv : EReal) → qv ≤ 0) →
      f fuel a p mode = (nan, .eq))
    (hf_one : ∀ fuel a p mode, qe a = some ((1 : ℝ) : EReal) →
      f fuel a p mode = fΓ fuel a p mode)
    (hf_real : ∀ fuel a p mode (qv av bv : ℝ), qe a = some (qv : EReal) → 0 < qv → qv ≠ 1 →
      xe a = some (av : EReal) → ye a = some (bv : EReal) →
      f fuel a p mode = lnOfSigned (lnAbsQBetaOf (Q a) (Sa a) (Sb a) (Ss a) fuel p mode))
    (hf_nonreal : ∀ fuel a (p : ℕ) [NeZero p] mode (qv : ℝ), qe a = some (qv : EReal) →
      0 < qv → qv ≠ 1 →
      (¬ ∃ av bv : ℝ, xe a = some (av : EReal) ∧ ye a = some (bv : EReal)) →
      f fuel a p mode = roundVal p mode
        ((xe a).bind fun x => (ye a).bind fun y => Spec.lnQBetaAt qv x y)) :
    ZivSpec
      (fun a => (qe a).bind fun q => (xe a).bind fun x => (ye a).bind fun y =>
        Spec.lnQBeta q x y)
      f {a | QBase2D qe xe ye (QLnBetaPD Q Sa Sb) a}
      {a | QBase2N qe xe ye (QLnBetaPN Q Sa Sb) a} :=
  qBase2_zivSpec (g := fun fuel a p mode =>
      lnOfSigned (lnAbsQBetaOf (Q a) (Sa a) (Sb a) (Ss a) fuel p mode))
    (QLnBetaPD Q Sa Sb) (QLnBetaPN Q Sa Sb) hΓs hΓc
    (hgs := fun a qv av bv hq h0 h1 hx hy fuel p _ mode => by
      obtain ⟨hSa, hSb, hSs⟩ := harg a av bv hx hy
      exact lnQBetaOf_main (hbase a qv hq h0 h1) hSa hSb hSs fuel p mode)
    (hgc := fun a qv av bv hq h0 h1 hx hy p _ mode hB => by
      obtain ⟨hSa, hSb, hSs⟩ := harg a av bv hx hy
      exact lnQBetaOf_complete (hbase a qv hq h0 h1) hSa hSb hSs p mode hB)
    (hD := fun a qv av bv hq h0 h1 hx hy hPD => by
      obtain ⟨hSa, hSb, hSs⟩ := harg a av bv hx hy
      have hPD' : (∃ m : ℕ, av = -m) ∨ (∃ m : ℕ, bv = -m) ∨ (∃ m : ℕ, av + bv = -m) ∨
          ((qBetaExact? (Q a) (Sa a).kind (Sb a).kind 0).isSome = true ∧
            qBetaReal qv av bv = 1) := hPD
      have hE := hPD'.imp_right (Or.imp_right (Or.imp_right And.left))
      have he := (lnQBetaOf_exact (hbase a qv hq h0 h1) hSa hSb hSs hE 0 1 .Nearest).2
      exact ⟨fun v hv => lnAbsQBetaAt_dyadic (hbase a qv hq h0 h1) hSa hSb hPD'
          (by rw [← he]; exact hv),
        fun fuel p _ mode =>
          (lnQBetaOf_exact (hbase a qv hq h0 h1) hSa hSb hSs hE fuel p mode).1⟩)
    (hN := fun a qv av bv hq h0 h1 hx hy hPN => by
      obtain ⟨hSa, hSb, hSs⟩ := harg a av bv hx hy
      have hPN' : (qBetaExact? (Q a) (Sa a).kind (Sb a).kind 0).isSome = true ∧
          qBetaReal qv av bv ≠ 1 := hPN
      have hE : (∃ m : ℕ, av = -m) ∨ (∃ m : ℕ, bv = -m) ∨ (∃ m : ℕ, av + bv = -m) ∨
          (qBetaExact? (Q a) (Sa a).kind (Sb a).kind 0).isSome = true :=
        Or.inr (Or.inr (Or.inr hPN'.1))
      have he := (lnQBetaOf_exact (hbase a qv hq h0 h1) hSa hSb hSs hE 0 1 .Nearest).2
      refine ⟨?_, fun fuel p _ mode =>
        (lnQBetaOf_exact (hbase a qv hq h0 h1) hSa hSb hSs hE fuel p mode).1⟩
      rw [he]
      exact lnAbsQBetaAt_not_dyadic (hbase a qv hq h0 h1) hSa hSb hPN')
    (hnr := fun qv x y h v hv => by
      rcases Spec.qBetaAt_nonreal_cases qv h with h0 | h0
      · rw [Spec.lnQBetaAt, h0] at hv
        exact absurd hv (by simp)
      · rw [Spec.lnQBetaAt, h0, Option.bind_some, Spec.log_zero] at hv
        exact absurd hv (by simp))
    hf_bad hf_one hf_real hf_nonreal

/-! ### Arguments that are not real -/

theorem lnOfZeroOrNan_nan : lnOfZeroOrNan (nan, .eq) = (nan, .eq) := by
  show (if isZeroVal nan = true then _ else _) = _
  rw [show isZeroVal nan = false from by decide]
  rfl

theorem lnOfZeroOrNan_zero : lnOfZeroOrNan (zero, .eq) = (infinity false, .eq) := by
  show (if isZeroVal zero = true then _ else _) = _
  rw [show isZeroVal zero = true from by decide]
  rfl

/-- The logarithm of a value of `B_q` at arguments that are not both real. -/
theorem lnOfZeroOrNan_nonreal (qv : ℝ) {xo yo : Option EReal}
    (h : ¬ ∃ av bv : ℝ, xo = some (av : EReal) ∧ yo = some (bv : EReal)) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    lnOfZeroOrNan (roundVal 1 .Nearest (xo.bind fun x => yo.bind fun y => Spec.qBetaAt qv x y))
      = roundVal p mode (xo.bind fun x => yo.bind fun y => Spec.lnAbsQBetaAt qv x y) := by
  cases xo with
  | none => exact lnOfZeroOrNan_nan
  | some x =>
    cases yo with
    | none => exact lnOfZeroOrNan_nan
    | some y =>
      rw [Option.bind_some, Option.bind_some, Option.bind_some, Option.bind_some,
        Spec.lnAbsQBetaAt]
      rcases Spec.qBetaAt_nonreal_cases qv (x := x) (y := y)
        (fun ⟨av, bv, h1, h2⟩ => h ⟨av, bv, by rw [h1], by rw [h2]⟩) with h0 | h0
      · rw [h0, roundVal_none, Option.map_none, roundVal_none]
        exact lnOfZeroOrNan_nan
      · rw [h0, roundVal_zero, Option.map_some, Spec.lnAbsE_zero', roundVal_bot]
        exact lnOfZeroOrNan_zero

/-- `ln B_q` is `ln |B_q|` at arguments that are not both real. -/
theorem lnQBetaAt_nonreal (qv : ℝ) {xo yo : Option EReal}
    (h : ¬ ∃ av bv : ℝ, xo = some (av : EReal) ∧ yo = some (bv : EReal)) :
    (xo.bind fun x => yo.bind fun y => Spec.lnQBetaAt qv x y)
      = xo.bind fun x => yo.bind fun y => Spec.lnAbsQBetaAt qv x y := by
  cases xo with
  | none => rfl
  | some x =>
    cases yo with
    | none => rfl
    | some y =>
      rw [Option.bind_some, Option.bind_some, Option.bind_some, Option.bind_some,
        Spec.lnQBetaAt, Spec.lnAbsQBetaAt]
      rcases Spec.qBetaAt_nonreal_cases qv (x := x) (y := y)
        (fun ⟨av, bv, h1, h2⟩ => h ⟨av, bv, by rw [h1], by rw [h2]⟩) with h0 | h0
      · rw [h0]
        rfl
      · rw [h0, Option.bind_some, Option.map_some, Spec.log_zero, Spec.lnAbsE_zero']

theorem lnAbsQBetaFloatArgs_eq_of (Q : QBase) (fuel : ℕ) {a b : AzFloat} {av bv : ℝ}
    (ha : a.toVal = some (av : EReal)) (hb : b.toVal = some (bv : EReal)) (p : ℕ)
    (mode : RoundingMode) :
    lnAbsQBetaFloatArgs Q fuel a b p mode
      = lnAbsQBetaOf Q (qArgFloat a) (qArgFloat b) (qArgSumFloat a b) fuel p mode := by
  unfold lnAbsQBetaFloatArgs
  rw [isFinite_of_toVal_coe ha, isFinite_of_toVal_coe hb]
  rfl

theorem lnAbsQBetaFloatArgs_nonreal (hQ : QBaseSpec Q qv) (fuel : ℕ) (a b : AzFloat)
    (h : ¬ ∃ av bv : ℝ, a.toVal = some (av : EReal) ∧ b.toVal = some (bv : EReal)) (p : ℕ)
    [NeZero p] (mode : RoundingMode) :
    lnAbsQBetaFloatArgs Q fuel a b p mode = (roundVal p mode
      (a.toVal.bind fun x => b.toVal.bind fun y => Spec.lnAbsQBetaAt qv x y), true) := by
  have hfin : (a.isFinite && b.isFinite) = false := by
    rw [← Bool.not_eq_true, Bool.and_eq_true]
    rintro ⟨ha, hb⟩
    exact h ⟨_, _, toVal_of_isFinite ha, toVal_of_isFinite hb⟩
  unfold lnAbsQBetaFloatArgs
  rw [hfin]
  show (lnOfZeroOrNan (qBetaFloatArgs Q 0 a b 1 .Nearest), true) = _
  rw [qBetaFloatArgs_nonreal hQ 0 a b h 1 .Nearest, lnOfZeroOrNan_nonreal qv h p mode]

theorem lnQBetaFloatArgs_nonreal (hQ : QBaseSpec Q qv) (fuel : ℕ) (a b : AzFloat)
    (h : ¬ ∃ av bv : ℝ, a.toVal = some (av : EReal) ∧ b.toVal = some (bv : EReal)) (p : ℕ)
    [NeZero p] (mode : RoundingMode) :
    lnOfSigned (lnAbsQBetaFloatArgs Q fuel a b p mode) = roundVal p mode
      (a.toVal.bind fun x => b.toVal.bind fun y => Spec.lnQBetaAt qv x y) := by
  rw [lnAbsQBetaFloatArgs_nonreal hQ fuel a b h p mode, lnQBetaAt_nonreal qv h]
  rfl

theorem lnAbsQBetaMixedArgs_eq_of (Q : QBase) (fuel : ℕ) {a : AzFloat} {r : AzRat}
    (hr : a.toAzRat? = some r) (b : AzRat) (p : ℕ) (mode : RoundingMode) :
    lnAbsQBetaMixedArgs Q fuel a b p mode
      = lnAbsQBetaOf Q (qArgRat r) (qArgRat b) (qArgRat (r + b)) fuel p mode := by
  unfold lnAbsQBetaMixedArgs
  rw [hr]
  rfl

theorem lnAbsQBetaMixedArgs_nonreal (hQ : QBaseSpec Q qv) (fuel : ℕ) (a : AzFloat) (b : AzRat)
    (h : ∀ av : ℝ, a.toVal ≠ some (av : EReal)) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    lnAbsQBetaMixedArgs Q fuel a b p mode = (roundVal p mode (a.toVal.bind fun x =>
      Spec.lnAbsQBetaAt qv x (((AzRat.toRat b : ℚ) : ℝ) : EReal)), true) := by
  have hnone : a.toAzRat? = none := by
    rcases exists_real_or_not a with ⟨av, ha⟩ | rfl | rfl | rfl
    · exact absurd ha (h av)
    · rfl
    · rfl
    · rfl
  have hnr : ¬ ∃ av bv : ℝ, a.toVal = some (av : EReal) ∧
      some ((((AzRat.toRat b : ℚ) : ℝ) : ℝ) : EReal) = some (bv : EReal) :=
    fun ⟨av, _, ha, _⟩ => h av ha
  unfold lnAbsQBetaMixedArgs
  rw [hnone]
  show (lnOfZeroOrNan (qBetaMixedArgs Q 0 a b 1 .Nearest), true) = _
  rw [qBetaMixedArgs_nonreal hQ 0 a b h 1 .Nearest]
  exact congrArg (fun r => (r, true)) (lnOfZeroOrNan_nonreal qv hnr p mode)

theorem lnQBetaMixedArgs_nonreal (hQ : QBaseSpec Q qv) (fuel : ℕ) (a : AzFloat) (b : AzRat)
    (h : ∀ av : ℝ, a.toVal ≠ some (av : EReal)) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    lnOfSigned (lnAbsQBetaMixedArgs Q fuel a b p mode) = roundVal p mode (a.toVal.bind fun x =>
      Spec.lnQBetaAt qv x (((AzRat.toRat b : ℚ) : ℝ) : EReal)) := by
  have hnr : ¬ ∃ av bv : ℝ, a.toVal = some (av : EReal) ∧
      some ((((AzRat.toRat b : ℚ) : ℝ) : ℝ) : EReal) = some (bv : EReal) :=
    fun ⟨av, _, ha, _⟩ => h av ha
  rw [lnAbsQBetaMixedArgs_nonreal hQ fuel a b h p mode]
  exact congrArg (roundVal p mode) (lnQBetaAt_nonreal qv hnr).symm

/-! ### The functions on the real class, and the sign -/

theorem lnAbsQBetaPrecRoundFuel_eq_of (fuel : ℕ) {q : AzFloat} {qv : ℝ}
    (hq : q.toVal = some (qv : EReal)) (h0 : 0 < qv) (h1 : qv ≠ 1)
    {a b : AzFloat} {av bv : ℝ} (ha : a.toVal = some (av : EReal))
    (hb : b.toVal = some (bv : EReal)) (p : ℕ) (mode : RoundingMode) :
    lnAbsQBetaPrecRoundFuel fuel q a b p mode
      = lnAbsQBetaOf (qBaseFloat q) (qArgFloat a) (qArgFloat b)
        (qArgSumFloat a b) fuel p mode := by
  rw [show lnAbsQBetaPrecRoundFuel fuel q a b p mode
      = lnAbsQBetaFloatArgs (qBaseFloat q) fuel a b p mode
    from floatBaseSel_real hq h0 h1 _ _ _]
  exact lnAbsQBetaFloatArgs_eq_of _ fuel ha hb p mode

/-- **The sign component is the sign of `B_q(a, b)`** (`true`: not negative) whenever the
value is not `NaN`, for floats. -/
theorem lnAbsQBetaPrecRoundFuel_sign (fuel : ℕ) {q : AzFloat} {qv : ℝ}
    (hq : q.toVal = some (qv : EReal)) (h0 : 0 < qv) (h1 : qv ≠ 1)
    {a b : AzFloat} {av bv : ℝ} (ha : a.toVal = some (av : EReal))
    (hb : b.toVal = some (bv : EReal)) (p : ℕ) [NeZero p] (mode : RoundingMode)
    (hne : (lnAbsQBetaPrecRoundFuel fuel q a b p mode).1 ≠ (nan, .eq)) :
    (lnAbsQBetaPrecRoundFuel fuel q a b p mode).2 = true ↔
      ∀ v : ℝ, Spec.qBetaAt qv (av : EReal) (bv : EReal) = some (v : EReal) →
        0 ≤ v := by
  have hQ := qBaseFloat_spec hq h0 h1
  have hSa := qArgFloat_spec ha
  have hSb := qArgFloat_spec hb
  have hSs := qArgSumFloat_spec ha hb
  rw [lnAbsQBetaPrecRoundFuel_eq_of fuel hq h0 h1 ha hb] at hne ⊢
  rcases lnAbsQBetaOf_main hQ hSa hSb hSs fuel p mode with h | h
  · exact absurd h hne
  · exact h.2

theorem lnAbsQBetaFloatFloatRatPrecRoundFuel_eq_of (fuel : ℕ) {q : AzFloat} {qv : ℝ}
    (hq : q.toVal = some (qv : EReal)) (h0 : 0 < qv) (h1 : qv ≠ 1)
    {a : AzFloat} {av : ℝ} (ha : a.toVal = some (av : EReal))
    (b : AzRat) (p : ℕ) (mode : RoundingMode) :
    lnAbsQBetaFloatFloatRatPrecRoundFuel fuel q a b p mode
      = lnAbsQBetaOf (qBaseFloat q) (qArgRat (a.toAzRat?.getD 0)) (qArgRat b)
        (qArgRat (a.toAzRat?.getD 0 + b)) fuel p mode := by
  rw [show lnAbsQBetaFloatFloatRatPrecRoundFuel fuel q a b p mode
      = lnAbsQBetaMixedArgs (qBaseFloat q) fuel a b p mode
    from floatBaseSel_real hq h0 h1 _ _ _]
  obtain ⟨r, hr, -⟩ := exists_toAzRat? ha
  rw [lnAbsQBetaMixedArgs_eq_of _ fuel hr, hr]
  rfl

/-- **The sign component is the sign of `B_q(a, b)`** (`true`: not negative) whenever the
value is not `NaN`, for a float `q`, a float `a` and a rational `b`. -/
theorem lnAbsQBetaFloatFloatRatPrecRoundFuel_sign (fuel : ℕ) {q : AzFloat} {qv : ℝ}
    (hq : q.toVal = some (qv : EReal)) (h0 : 0 < qv) (h1 : qv ≠ 1)
    {a : AzFloat} {av : ℝ} (ha : a.toVal = some (av : EReal))
    (b : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode)
    (hne : (lnAbsQBetaFloatFloatRatPrecRoundFuel fuel q a b p mode).1 ≠ (nan, .eq)) :
    (lnAbsQBetaFloatFloatRatPrecRoundFuel fuel q a b p mode).2 = true ↔
      ∀ v : ℝ, Spec.qBetaAt qv (av : EReal) (((AzRat.toRat b : ℚ) : ℝ) : EReal) = some (v : EReal) →
        0 ≤ v := by
  have hQ := qBaseFloat_spec hq h0 h1
  obtain ⟨hSa, hSb, hSs⟩ := qBetaMixed_arg ha b
  rw [lnAbsQBetaFloatFloatRatPrecRoundFuel_eq_of fuel hq h0 h1 ha] at hne ⊢
  rcases lnAbsQBetaOf_main hQ hSa hSb hSs fuel p mode with h | h
  · exact absurd h hne
  · exact h.2

theorem lnAbsQBetaFloatRatRatPrecRoundFuel_eq_of (fuel : ℕ) {q : AzFloat} {qv : ℝ}
    (hq : q.toVal = some (qv : EReal)) (h0 : 0 < qv) (h1 : qv ≠ 1)
    (a b : AzRat) (p : ℕ) (mode : RoundingMode) :
    lnAbsQBetaFloatRatRatPrecRoundFuel fuel q a b p mode
      = lnAbsQBetaOf (qBaseFloat q) (qArgRat a) (qArgRat b)
        (qArgRat (a + b)) fuel p mode := by
  rw [show lnAbsQBetaFloatRatRatPrecRoundFuel fuel q a b p mode
      = lnAbsQBetaRatArgs (qBaseFloat q) fuel a b p mode
    from floatBaseSel_real hq h0 h1 _ _ _]
  rfl

/-- **The sign component is the sign of `B_q(a, b)`** (`true`: not negative) whenever the
value is not `NaN`, for a float `q` and rationals `a`, `b`. -/
theorem lnAbsQBetaFloatRatRatPrecRoundFuel_sign (fuel : ℕ) {q : AzFloat} {qv : ℝ}
    (hq : q.toVal = some (qv : EReal)) (h0 : 0 < qv) (h1 : qv ≠ 1)
    (a b : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode)
    (hne : (lnAbsQBetaFloatRatRatPrecRoundFuel fuel q a b p mode).1 ≠ (nan, .eq)) :
    (lnAbsQBetaFloatRatRatPrecRoundFuel fuel q a b p mode).2 = true ↔
      ∀ v : ℝ, Spec.qBetaAt qv (((AzRat.toRat a : ℚ) : ℝ) : EReal)
          (((AzRat.toRat b : ℚ) : ℝ) : EReal) = some (v : EReal) →
        0 ≤ v := by
  have hQ := qBaseFloat_spec hq h0 h1
  obtain ⟨hSa, hSb, hSs⟩ := qBetaRat_arg a b
  rw [lnAbsQBetaFloatRatRatPrecRoundFuel_eq_of fuel hq h0 h1 ] at hne ⊢
  rcases lnAbsQBetaOf_main hQ hSa hSb hSs fuel p mode with h | h
  · exact absurd h hne
  · exact h.2

theorem lnAbsQBetaRatFloatFloatPrecRoundFuel_eq_of (fuel : ℕ) {q : AzRat}
    (h0 : 0 < ((AzRat.toRat q : ℚ) : ℝ))
    (h1 : ((AzRat.toRat q : ℚ) : ℝ) ≠ 1)
    {a b : AzFloat} {av bv : ℝ} (ha : a.toVal = some (av : EReal))
    (hb : b.toVal = some (bv : EReal)) (p : ℕ) (mode : RoundingMode) :
    lnAbsQBetaRatFloatFloatPrecRoundFuel fuel q a b p mode
      = lnAbsQBetaOf (qBaseRat q) (qArgFloat a) (qArgFloat b)
        (qArgSumFloat a b) fuel p mode := by
  rw [show lnAbsQBetaRatFloatFloatPrecRoundFuel fuel q a b p mode
      = lnAbsQBetaFloatArgs (qBaseRat q) fuel a b p mode
    from ratBaseSel_real h0 h1 _ _ _]
  exact lnAbsQBetaFloatArgs_eq_of _ fuel ha hb p mode

/-- **The sign component is the sign of `B_q(a, b)`** (`true`: not negative) whenever the
value is not `NaN`, for a rational `q` and floats `a`, `b`. -/
theorem lnAbsQBetaRatFloatFloatPrecRoundFuel_sign (fuel : ℕ) {q : AzRat}
    (h0 : 0 < ((AzRat.toRat q : ℚ) : ℝ))
    (h1 : ((AzRat.toRat q : ℚ) : ℝ) ≠ 1)
    {a b : AzFloat} {av bv : ℝ} (ha : a.toVal = some (av : EReal))
    (hb : b.toVal = some (bv : EReal)) (p : ℕ) [NeZero p] (mode : RoundingMode)
    (hne : (lnAbsQBetaRatFloatFloatPrecRoundFuel fuel q a b p mode).1 ≠ (nan, .eq)) :
    (lnAbsQBetaRatFloatFloatPrecRoundFuel fuel q a b p mode).2 = true ↔
      ∀ v : ℝ, Spec.qBetaAt ((AzRat.toRat q : ℚ) : ℝ) (av : EReal) (bv : EReal) = some (v : EReal) →
        0 ≤ v := by
  have hQ := qBaseRat_spec q h0 h1
  have hSa := qArgFloat_spec ha
  have hSb := qArgFloat_spec hb
  have hSs := qArgSumFloat_spec ha hb
  rw [lnAbsQBetaRatFloatFloatPrecRoundFuel_eq_of fuel h0 h1 ha hb] at hne ⊢
  rcases lnAbsQBetaOf_main hQ hSa hSb hSs fuel p mode with h | h
  · exact absurd h hne
  · exact h.2

theorem lnAbsQBetaRatFloatRatPrecRoundFuel_eq_of (fuel : ℕ) {q : AzRat}
    (h0 : 0 < ((AzRat.toRat q : ℚ) : ℝ))
    (h1 : ((AzRat.toRat q : ℚ) : ℝ) ≠ 1)
    {a : AzFloat} {av : ℝ} (ha : a.toVal = some (av : EReal))
    (b : AzRat) (p : ℕ) (mode : RoundingMode) :
    lnAbsQBetaRatFloatRatPrecRoundFuel fuel q a b p mode
      = lnAbsQBetaOf (qBaseRat q) (qArgRat (a.toAzRat?.getD 0)) (qArgRat b)
        (qArgRat (a.toAzRat?.getD 0 + b)) fuel p mode := by
  rw [show lnAbsQBetaRatFloatRatPrecRoundFuel fuel q a b p mode
      = lnAbsQBetaMixedArgs (qBaseRat q) fuel a b p mode
    from ratBaseSel_real h0 h1 _ _ _]
  obtain ⟨r, hr, -⟩ := exists_toAzRat? ha
  rw [lnAbsQBetaMixedArgs_eq_of _ fuel hr, hr]
  rfl

/-- **The sign component is the sign of `B_q(a, b)`** (`true`: not negative) whenever the
value is not `NaN`, for a rational `q`, a float `a` and a rational `b`. -/
theorem lnAbsQBetaRatFloatRatPrecRoundFuel_sign (fuel : ℕ) {q : AzRat}
    (h0 : 0 < ((AzRat.toRat q : ℚ) : ℝ))
    (h1 : ((AzRat.toRat q : ℚ) : ℝ) ≠ 1)
    {a : AzFloat} {av : ℝ} (ha : a.toVal = some (av : EReal))
    (b : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode)
    (hne : (lnAbsQBetaRatFloatRatPrecRoundFuel fuel q a b p mode).1 ≠ (nan, .eq)) :
    (lnAbsQBetaRatFloatRatPrecRoundFuel fuel q a b p mode).2 = true ↔
      ∀ v : ℝ, Spec.qBetaAt ((AzRat.toRat q : ℚ) : ℝ) (av : EReal)
          (((AzRat.toRat b : ℚ) : ℝ) : EReal) = some (v : EReal) →
        0 ≤ v := by
  have hQ := qBaseRat_spec q h0 h1
  obtain ⟨hSa, hSb, hSs⟩ := qBetaMixed_arg ha b
  rw [lnAbsQBetaRatFloatRatPrecRoundFuel_eq_of fuel h0 h1 ha] at hne ⊢
  rcases lnAbsQBetaOf_main hQ hSa hSb hSs fuel p mode with h | h
  · exact absurd h hne
  · exact h.2

theorem lnAbsQBetaRatPrecRoundFuel_eq_of (fuel : ℕ) {q : AzRat} (h0 : 0 < ((AzRat.toRat q : ℚ) : ℝ))
    (h1 : ((AzRat.toRat q : ℚ) : ℝ) ≠ 1)
    (a b : AzRat) (p : ℕ) (mode : RoundingMode) :
    lnAbsQBetaRatPrecRoundFuel fuel q a b p mode
      = lnAbsQBetaOf (qBaseRat q) (qArgRat a) (qArgRat b)
        (qArgRat (a + b)) fuel p mode := by
  rw [show lnAbsQBetaRatPrecRoundFuel fuel q a b p mode
      = lnAbsQBetaRatArgs (qBaseRat q) fuel a b p mode
    from ratBaseSel_real h0 h1 _ _ _]
  rfl

/-- **The sign component is the sign of `B_q(a, b)`** (`true`: not negative) whenever the
value is not `NaN`, for rationals `q`, `a`, `b`. -/
theorem lnAbsQBetaRatPrecRoundFuel_sign (fuel : ℕ) {q : AzRat} (h0 : 0 < ((AzRat.toRat q : ℚ) : ℝ))
    (h1 : ((AzRat.toRat q : ℚ) : ℝ) ≠ 1)
    (a b : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode)
    (hne : (lnAbsQBetaRatPrecRoundFuel fuel q a b p mode).1 ≠ (nan, .eq)) :
    (lnAbsQBetaRatPrecRoundFuel fuel q a b p mode).2 = true ↔
      ∀ v : ℝ, Spec.qBetaAt ((AzRat.toRat q : ℚ) : ℝ) (((AzRat.toRat a : ℚ) : ℝ) : EReal)
          (((AzRat.toRat b : ℚ) : ℝ) : EReal) = some (v : EReal) →
        0 ≤ v := by
  have hQ := qBaseRat_spec q h0 h1
  obtain ⟨hSa, hSb, hSs⟩ := qBetaRat_arg a b
  rw [lnAbsQBetaRatPrecRoundFuel_eq_of fuel h0 h1 ] at hne ⊢
  rcases lnAbsQBetaOf_main hQ hSa hSb hSs fuel p mode with h | h
  · exact absurd h hne
  · exact h.2

/-! ### The twelve specifications -/

/-- **The specification of `ln |B_q(a, b)|` for floats** (the value component; `ZivSpec`). -/
theorem lnAbsQBetaPrecRoundFuel_zivSpec :
    ZivSpec
      (fun a : AzFloat × AzFloat × AzFloat =>
        a.1.toVal.bind fun q => a.2.1.toVal.bind fun x => a.2.2.toVal.bind fun y => Spec.lnAbsQBeta
            q x y)
      (fun fuel a p mode => (lnAbsQBetaPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode).1)
      {a | QBase2D (fun a : AzFloat × AzFloat × AzFloat => a.1.toVal)
          (fun a => a.2.1.toVal)
          (fun a => a.2.2.toVal)
          (QLnBetaPD (fun a => qBaseFloat a.1) (fun a => qArgFloat a.2.1)
            (fun a => qArgFloat a.2.2)) a}
      {a | QBase2N (fun a : AzFloat × AzFloat × AzFloat => a.1.toVal)
          (fun a => a.2.1.toVal)
          (fun a => a.2.2.toVal)
          (QLnBetaPN (fun a => qBaseFloat a.1) (fun a => qArgFloat a.2.1)
            (fun a => qArgFloat a.2.2)) a} :=
  lnAbsQBeta_zivSpec_sides (α := AzFloat × AzFloat × AzFloat)
    (qe := fun a => a.1.toVal)
    (xe := fun a => a.2.1.toVal)
    (ye := fun a => a.2.2.toVal)
    (f := fun fuel a p mode => (lnAbsQBetaPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode).1)
    (fΓ := fun fuel a p mode => (lnAbsBetaPrecRoundFuel fuel a.2.1 a.2.2 p mode).1)
    (fun a => qBaseFloat a.1) (fun a => qArgFloat a.2.1) (fun a => qArgFloat a.2.2)
    (fun a => qArgSumFloat a.2.1 a.2.2)
    (fun a qv hq h0 h1 => qBaseFloat_spec hq h0 h1)
    (fun a av bv hx hy => ⟨qArgFloat_spec hx, qArgFloat_spec hy, qArgSumFloat_spec hx hy⟩)
    (fun fuel a p _ mode => lnAbsBetaPrecRoundFuel_zivSpec.sound fuel a.2 p mode)
    (fun a p _ mode hB => lnAbsBetaPrecRoundFuel_zivSpec.complete a.2 p mode hB)
    (fun fuel a p mode hb => congrArg Prod.fst (floatBaseSel_bad hb _ _ _))
    (fun fuel a p mode hq => congrArg Prod.fst (floatBaseSel_one hq _ _ _))
    (fun fuel a p mode qv av bv hq h0 h1 hx hy => by
      show (lnAbsQBetaPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode).1 = _
      rw [lnAbsQBetaPrecRoundFuel_eq_of fuel hq h0 h1 hx hy])
    (fun fuel a p _ mode qv hq h0 h1 hx => by
      have hQ := qBaseFloat_spec hq h0 h1
      show (lnAbsQBetaPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode).1 = _
      rw [show lnAbsQBetaPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode
          = lnAbsQBetaFloatArgs (qBaseFloat a.1) fuel a.2.1 a.2.2 p mode
        from floatBaseSel_real hq h0 h1 _ _ _]
      exact congrArg Prod.fst (lnAbsQBetaFloatArgs_nonreal hQ fuel a.2.1 a.2.2 hx p mode))

/-- **The specification of `ln B_q(a, b)` for floats** (`ZivSpec`). -/
theorem lnQBetaPrecRoundFuel_zivSpec :
    ZivSpec
      (fun a : AzFloat × AzFloat × AzFloat =>
        a.1.toVal.bind fun q => a.2.1.toVal.bind fun x => a.2.2.toVal.bind fun y => Spec.lnQBeta q
            x y)
      (fun fuel a p mode => lnQBetaPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode)
      {a | QBase2D (fun a : AzFloat × AzFloat × AzFloat => a.1.toVal)
          (fun a => a.2.1.toVal)
          (fun a => a.2.2.toVal)
          (QLnBetaPD (fun a => qBaseFloat a.1) (fun a => qArgFloat a.2.1)
            (fun a => qArgFloat a.2.2)) a}
      {a | QBase2N (fun a : AzFloat × AzFloat × AzFloat => a.1.toVal)
          (fun a => a.2.1.toVal)
          (fun a => a.2.2.toVal)
          (QLnBetaPN (fun a => qBaseFloat a.1) (fun a => qArgFloat a.2.1)
            (fun a => qArgFloat a.2.2)) a} :=
  lnQBeta_zivSpec_sides (α := AzFloat × AzFloat × AzFloat)
    (qe := fun a => a.1.toVal)
    (xe := fun a => a.2.1.toVal)
    (ye := fun a => a.2.2.toVal)
    (f := fun fuel a p mode => lnQBetaPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode)
    (fΓ := fun fuel a p mode => lnBetaPrecRoundFuel fuel a.2.1 a.2.2 p mode)
    (fun a => qBaseFloat a.1) (fun a => qArgFloat a.2.1) (fun a => qArgFloat a.2.2)
    (fun a => qArgSumFloat a.2.1 a.2.2)
    (fun a qv hq h0 h1 => qBaseFloat_spec hq h0 h1)
    (fun a av bv hx hy => ⟨qArgFloat_spec hx, qArgFloat_spec hy, qArgSumFloat_spec hx hy⟩)
    (fun fuel a p _ mode => lnBetaPrecRoundFuel_zivSpec.sound fuel a.2 p mode)
    (fun a p _ mode hB => lnBetaPrecRoundFuel_zivSpec.complete a.2 p mode hB)
    (fun fuel a p mode hb => floatBaseSel_bad hb _ _ _)
    (fun fuel a p mode hq => floatBaseSel_one hq _ _ _)
    (fun fuel a p mode qv av bv hq h0 h1 hx hy => by
      show lnQBetaPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode = _
      rw [show lnQBetaPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode
          = lnOfSigned (lnAbsQBetaPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode)
        from (floatBaseSel_real hq h0 h1 _ _ _).trans
            (congrArg lnOfSigned (floatBaseSel_real hq h0 h1 _ _ _).symm),
        lnAbsQBetaPrecRoundFuel_eq_of fuel hq h0 h1 hx hy])
    (fun fuel a p _ mode qv hq h0 h1 hx => by
      have hQ := qBaseFloat_spec hq h0 h1
      show lnQBetaPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode = _
      rw [show lnQBetaPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode
          = lnOfSigned (lnAbsQBetaFloatArgs (qBaseFloat a.1) fuel a.2.1 a.2.2 p mode)
        from floatBaseSel_real hq h0 h1 _ _ _]
      exact lnQBetaFloatArgs_nonreal hQ fuel a.2.1 a.2.2 hx p mode)

/-- **The specification of `ln |B_q(a, b)|` for a float `q`, a float `a` and a rational `b`** (the
value component; `ZivSpec`). -/
theorem lnAbsQBetaFloatFloatRatPrecRoundFuel_zivSpec :
    ZivSpec
      (fun a : AzFloat × AzFloat × AzRat =>
        a.1.toVal.bind fun q => a.2.1.toVal.bind fun x => Spec.lnAbsQBeta q x
            (((AzRat.toRat a.2.2 : ℚ) : ℝ) : EReal))
      (fun fuel a p mode => (lnAbsQBetaFloatFloatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode).1)
      {a | QBase2D (fun a : AzFloat × AzFloat × AzRat => a.1.toVal)
          (fun a => a.2.1.toVal)
          (fun a => some (((AzRat.toRat a.2.2 : ℚ) : ℝ) : EReal))
          (QLnBetaPD (fun a => qBaseFloat a.1) (fun a => qArgRat (a.2.1.toAzRat?.getD 0))
            (fun a => qArgRat a.2.2)) a}
      {a | QBase2N (fun a : AzFloat × AzFloat × AzRat => a.1.toVal)
          (fun a => a.2.1.toVal)
          (fun a => some (((AzRat.toRat a.2.2 : ℚ) : ℝ) : EReal))
          (QLnBetaPN (fun a => qBaseFloat a.1) (fun a => qArgRat (a.2.1.toAzRat?.getD 0))
            (fun a => qArgRat a.2.2)) a} :=
  lnAbsQBeta_zivSpec_sides (α := AzFloat × AzFloat × AzRat)
    (qe := fun a => a.1.toVal)
    (xe := fun a => a.2.1.toVal)
    (ye := fun a => some (((AzRat.toRat a.2.2 : ℚ) : ℝ) : EReal))
    (f := fun fuel a p mode => (lnAbsQBetaFloatFloatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode).1)
    (fΓ := fun fuel a p mode => (lnAbsBetaFloatRatPrecRoundFuel fuel a.2.1 a.2.2 p mode).1)
    (fun a => qBaseFloat a.1) (fun a => qArgRat (a.2.1.toAzRat?.getD 0)) (fun a => qArgRat a.2.2)
    (fun a => qArgRat (a.2.1.toAzRat?.getD 0 + a.2.2))
    (fun a qv hq h0 h1 => qBaseFloat_spec hq h0 h1)
    (fun a av bv hx hy => by
      have e := coe_eq_of_some_eq hy
      rw [← e]
      exact qBetaMixed_arg hx a.2.2)
    (fun fuel a p _ mode => lnAbsBetaFloatRatPrecRoundFuel_zivSpec.sound fuel a.2 p mode)
    (fun a p _ mode hB => lnAbsBetaFloatRatPrecRoundFuel_zivSpec.complete a.2 p mode hB)
    (fun fuel a p mode hb => congrArg Prod.fst (floatBaseSel_bad hb _ _ _))
    (fun fuel a p mode hq => congrArg Prod.fst (floatBaseSel_one hq _ _ _))
    (fun fuel a p mode qv av bv hq h0 h1 hx hy => by
      show (lnAbsQBetaFloatFloatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode).1 = _
      rw [lnAbsQBetaFloatFloatRatPrecRoundFuel_eq_of fuel hq h0 h1 hx])
    (fun fuel a p _ mode qv hq h0 h1 hx => by
      have hQ := qBaseFloat_spec hq h0 h1
      show (lnAbsQBetaFloatFloatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode).1 = _
      rw [show lnAbsQBetaFloatFloatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode
          = lnAbsQBetaMixedArgs (qBaseFloat a.1) fuel a.2.1 a.2.2 p mode
        from floatBaseSel_real hq h0 h1 _ _ _]
      exact congrArg Prod.fst (lnAbsQBetaMixedArgs_nonreal hQ fuel a.2.1 a.2.2
        (fun av h => hx ⟨av, _, h, rfl⟩) p mode))

/-- **The specification of `ln B_q(a, b)` for a float `q`, a float `a` and a rational `b`**
(`ZivSpec`). -/
theorem lnQBetaFloatFloatRatPrecRoundFuel_zivSpec :
    ZivSpec
      (fun a : AzFloat × AzFloat × AzRat =>
        a.1.toVal.bind fun q => a.2.1.toVal.bind fun x => Spec.lnQBeta q x
            (((AzRat.toRat a.2.2 : ℚ) : ℝ) : EReal))
      (fun fuel a p mode => lnQBetaFloatFloatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode)
      {a | QBase2D (fun a : AzFloat × AzFloat × AzRat => a.1.toVal)
          (fun a => a.2.1.toVal)
          (fun a => some (((AzRat.toRat a.2.2 : ℚ) : ℝ) : EReal))
          (QLnBetaPD (fun a => qBaseFloat a.1) (fun a => qArgRat (a.2.1.toAzRat?.getD 0))
            (fun a => qArgRat a.2.2)) a}
      {a | QBase2N (fun a : AzFloat × AzFloat × AzRat => a.1.toVal)
          (fun a => a.2.1.toVal)
          (fun a => some (((AzRat.toRat a.2.2 : ℚ) : ℝ) : EReal))
          (QLnBetaPN (fun a => qBaseFloat a.1) (fun a => qArgRat (a.2.1.toAzRat?.getD 0))
            (fun a => qArgRat a.2.2)) a} :=
  lnQBeta_zivSpec_sides (α := AzFloat × AzFloat × AzRat)
    (qe := fun a => a.1.toVal)
    (xe := fun a => a.2.1.toVal)
    (ye := fun a => some (((AzRat.toRat a.2.2 : ℚ) : ℝ) : EReal))
    (f := fun fuel a p mode => lnQBetaFloatFloatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode)
    (fΓ := fun fuel a p mode => lnBetaFloatRatPrecRoundFuel fuel a.2.1 a.2.2 p mode)
    (fun a => qBaseFloat a.1) (fun a => qArgRat (a.2.1.toAzRat?.getD 0)) (fun a => qArgRat a.2.2)
    (fun a => qArgRat (a.2.1.toAzRat?.getD 0 + a.2.2))
    (fun a qv hq h0 h1 => qBaseFloat_spec hq h0 h1)
    (fun a av bv hx hy => by
      have e := coe_eq_of_some_eq hy
      rw [← e]
      exact qBetaMixed_arg hx a.2.2)
    (fun fuel a p _ mode => lnBetaFloatRatPrecRoundFuel_zivSpec.sound fuel a.2 p mode)
    (fun a p _ mode hB => lnBetaFloatRatPrecRoundFuel_zivSpec.complete a.2 p mode hB)
    (fun fuel a p mode hb => floatBaseSel_bad hb _ _ _)
    (fun fuel a p mode hq => floatBaseSel_one hq _ _ _)
    (fun fuel a p mode qv av bv hq h0 h1 hx hy => by
      show lnQBetaFloatFloatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode = _
      rw [show lnQBetaFloatFloatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode
          = lnOfSigned (lnAbsQBetaFloatFloatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode)
        from (floatBaseSel_real hq h0 h1 _ _ _).trans
            (congrArg lnOfSigned (floatBaseSel_real hq h0 h1 _ _ _).symm),
        lnAbsQBetaFloatFloatRatPrecRoundFuel_eq_of fuel hq h0 h1 hx])
    (fun fuel a p _ mode qv hq h0 h1 hx => by
      have hQ := qBaseFloat_spec hq h0 h1
      show lnQBetaFloatFloatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode = _
      rw [show lnQBetaFloatFloatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode
          = lnOfSigned (lnAbsQBetaMixedArgs (qBaseFloat a.1) fuel a.2.1 a.2.2 p mode)
        from floatBaseSel_real hq h0 h1 _ _ _]
      exact lnQBetaMixedArgs_nonreal hQ fuel a.2.1 a.2.2
        (fun av h => hx ⟨av, _, h, rfl⟩) p mode)

/-- **The specification of `ln |B_q(a, b)|` for a float `q` and rationals `a`, `b`** (the value
component; `ZivSpec`). -/
theorem lnAbsQBetaFloatRatRatPrecRoundFuel_zivSpec :
    ZivSpec
      (fun a : AzFloat × AzRat × AzRat =>
        a.1.toVal.bind fun q => Spec.lnAbsQBeta q (((AzRat.toRat a.2.1 : ℚ) : ℝ) : EReal)
            (((AzRat.toRat a.2.2 : ℚ) : ℝ) : EReal))
      (fun fuel a p mode => (lnAbsQBetaFloatRatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode).1)
      {a | QBase2D (fun a : AzFloat × AzRat × AzRat => a.1.toVal)
          (fun a => some (((AzRat.toRat a.2.1 : ℚ) : ℝ) : EReal))
          (fun a => some (((AzRat.toRat a.2.2 : ℚ) : ℝ) : EReal))
          (QLnBetaPD (fun a => qBaseFloat a.1) (fun a => qArgRat a.2.1)
            (fun a => qArgRat a.2.2)) a}
      {a | QBase2N (fun a : AzFloat × AzRat × AzRat => a.1.toVal)
          (fun a => some (((AzRat.toRat a.2.1 : ℚ) : ℝ) : EReal))
          (fun a => some (((AzRat.toRat a.2.2 : ℚ) : ℝ) : EReal))
          (QLnBetaPN (fun a => qBaseFloat a.1) (fun a => qArgRat a.2.1)
            (fun a => qArgRat a.2.2)) a} :=
  lnAbsQBeta_zivSpec_sides (α := AzFloat × AzRat × AzRat)
    (qe := fun a => a.1.toVal)
    (xe := fun a => some (((AzRat.toRat a.2.1 : ℚ) : ℝ) : EReal))
    (ye := fun a => some (((AzRat.toRat a.2.2 : ℚ) : ℝ) : EReal))
    (f := fun fuel a p mode => (lnAbsQBetaFloatRatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode).1)
    (fΓ := fun fuel a p mode => (lnAbsBetaRatPrecRoundFuel fuel a.2.1 a.2.2 p mode).1)
    (fun a => qBaseFloat a.1) (fun a => qArgRat a.2.1) (fun a => qArgRat a.2.2)
    (fun a => qArgRat (a.2.1 + a.2.2))
    (fun a qv hq h0 h1 => qBaseFloat_spec hq h0 h1)
    (fun a av bv hx hy => by
      have e1 := coe_eq_of_some_eq hx
      have e2 := coe_eq_of_some_eq hy
      rw [← e1, ← e2]
      exact qBetaRat_arg a.2.1 a.2.2)
    (fun fuel a p _ mode => lnAbsBetaRatPrecRoundFuel_zivSpec.sound fuel a.2 p mode)
    (fun a p _ mode hB => lnAbsBetaRatPrecRoundFuel_zivSpec.complete a.2 p mode hB)
    (fun fuel a p mode hb => congrArg Prod.fst (floatBaseSel_bad hb _ _ _))
    (fun fuel a p mode hq => congrArg Prod.fst (floatBaseSel_one hq _ _ _))
    (fun fuel a p mode qv av bv hq h0 h1 hx hy => by
      show (lnAbsQBetaFloatRatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode).1 = _
      rw [lnAbsQBetaFloatRatRatPrecRoundFuel_eq_of fuel hq h0 h1 ])
    (fun fuel a p _ mode qv hq h0 h1 hx => by
      have hQ := qBaseFloat_spec hq h0 h1
      show (lnAbsQBetaFloatRatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode).1 = _
      rw [show lnAbsQBetaFloatRatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode
          = lnAbsQBetaRatArgs (qBaseFloat a.1) fuel a.2.1 a.2.2 p mode
        from floatBaseSel_real hq h0 h1 _ _ _]
      exact absurd ⟨_, _, rfl, rfl⟩ hx)

/-- **The specification of `ln B_q(a, b)` for a float `q` and rationals `a`, `b`** (`ZivSpec`). -/
theorem lnQBetaFloatRatRatPrecRoundFuel_zivSpec :
    ZivSpec
      (fun a : AzFloat × AzRat × AzRat =>
        a.1.toVal.bind fun q => Spec.lnQBeta q (((AzRat.toRat a.2.1 : ℚ) : ℝ) : EReal)
            (((AzRat.toRat a.2.2 : ℚ) : ℝ) : EReal))
      (fun fuel a p mode => lnQBetaFloatRatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode)
      {a | QBase2D (fun a : AzFloat × AzRat × AzRat => a.1.toVal)
          (fun a => some (((AzRat.toRat a.2.1 : ℚ) : ℝ) : EReal))
          (fun a => some (((AzRat.toRat a.2.2 : ℚ) : ℝ) : EReal))
          (QLnBetaPD (fun a => qBaseFloat a.1) (fun a => qArgRat a.2.1)
            (fun a => qArgRat a.2.2)) a}
      {a | QBase2N (fun a : AzFloat × AzRat × AzRat => a.1.toVal)
          (fun a => some (((AzRat.toRat a.2.1 : ℚ) : ℝ) : EReal))
          (fun a => some (((AzRat.toRat a.2.2 : ℚ) : ℝ) : EReal))
          (QLnBetaPN (fun a => qBaseFloat a.1) (fun a => qArgRat a.2.1)
            (fun a => qArgRat a.2.2)) a} :=
  lnQBeta_zivSpec_sides (α := AzFloat × AzRat × AzRat)
    (qe := fun a => a.1.toVal)
    (xe := fun a => some (((AzRat.toRat a.2.1 : ℚ) : ℝ) : EReal))
    (ye := fun a => some (((AzRat.toRat a.2.2 : ℚ) : ℝ) : EReal))
    (f := fun fuel a p mode => lnQBetaFloatRatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode)
    (fΓ := fun fuel a p mode => lnBetaRatPrecRoundFuel fuel a.2.1 a.2.2 p mode)
    (fun a => qBaseFloat a.1) (fun a => qArgRat a.2.1) (fun a => qArgRat a.2.2)
    (fun a => qArgRat (a.2.1 + a.2.2))
    (fun a qv hq h0 h1 => qBaseFloat_spec hq h0 h1)
    (fun a av bv hx hy => by
      have e1 := coe_eq_of_some_eq hx
      have e2 := coe_eq_of_some_eq hy
      rw [← e1, ← e2]
      exact qBetaRat_arg a.2.1 a.2.2)
    (fun fuel a p _ mode => lnBetaRatPrecRoundFuel_zivSpec.sound fuel a.2 p mode)
    (fun a p _ mode hB => lnBetaRatPrecRoundFuel_zivSpec.complete a.2 p mode hB)
    (fun fuel a p mode hb => floatBaseSel_bad hb _ _ _)
    (fun fuel a p mode hq => floatBaseSel_one hq _ _ _)
    (fun fuel a p mode qv av bv hq h0 h1 hx hy => by
      show lnQBetaFloatRatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode = _
      rw [show lnQBetaFloatRatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode
          = lnOfSigned (lnAbsQBetaFloatRatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode)
        from (floatBaseSel_real hq h0 h1 _ _ _).trans
            (congrArg lnOfSigned (floatBaseSel_real hq h0 h1 _ _ _).symm),
        lnAbsQBetaFloatRatRatPrecRoundFuel_eq_of fuel hq h0 h1 ])
    (fun fuel a p _ mode qv hq h0 h1 hx => by
      have hQ := qBaseFloat_spec hq h0 h1
      show lnQBetaFloatRatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode = _
      rw [show lnQBetaFloatRatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode
          = lnOfSigned (lnAbsQBetaRatArgs (qBaseFloat a.1) fuel a.2.1 a.2.2 p mode)
        from floatBaseSel_real hq h0 h1 _ _ _]
      exact absurd ⟨_, _, rfl, rfl⟩ hx)

/-- **The specification of `ln |B_q(a, b)|` for a rational `q` and floats `a`, `b`** (the value
component; `ZivSpec`). -/
theorem lnAbsQBetaRatFloatFloatPrecRoundFuel_zivSpec :
    ZivSpec
      (fun a : AzRat × AzFloat × AzFloat =>
        a.2.1.toVal.bind fun x => a.2.2.toVal.bind fun y => Spec.lnAbsQBeta
            (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal) x y)
      (fun fuel a p mode => (lnAbsQBetaRatFloatFloatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode).1)
      {a | QBase2D (fun a : AzRat × AzFloat × AzFloat => some (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal))
          (fun a => a.2.1.toVal)
          (fun a => a.2.2.toVal)
          (QLnBetaPD (fun a => qBaseRat a.1) (fun a => qArgFloat a.2.1)
            (fun a => qArgFloat a.2.2)) a}
      {a | QBase2N (fun a : AzRat × AzFloat × AzFloat => some (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal))
          (fun a => a.2.1.toVal)
          (fun a => a.2.2.toVal)
          (QLnBetaPN (fun a => qBaseRat a.1) (fun a => qArgFloat a.2.1)
            (fun a => qArgFloat a.2.2)) a} :=
  lnAbsQBeta_zivSpec_sides (α := AzRat × AzFloat × AzFloat)
    (qe := fun a => some (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal))
    (xe := fun a => a.2.1.toVal)
    (ye := fun a => a.2.2.toVal)
    (f := fun fuel a p mode => (lnAbsQBetaRatFloatFloatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode).1)
    (fΓ := fun fuel a p mode => (lnAbsBetaPrecRoundFuel fuel a.2.1 a.2.2 p mode).1)
    (fun a => qBaseRat a.1) (fun a => qArgFloat a.2.1) (fun a => qArgFloat a.2.2)
    (fun a => qArgSumFloat a.2.1 a.2.2)
    (fun a qv hq h0 h1 => by
      have e := coe_eq_of_some_eq hq
      rw [← e] at h0 h1 ⊢
      exact qBaseRat_spec a.1 h0 h1)
    (fun a av bv hx hy => ⟨qArgFloat_spec hx, qArgFloat_spec hy, qArgSumFloat_spec hx hy⟩)
    (fun fuel a p _ mode => lnAbsBetaPrecRoundFuel_zivSpec.sound fuel a.2 p mode)
    (fun a p _ mode hB => lnAbsBetaPrecRoundFuel_zivSpec.complete a.2 p mode hB)
    (fun fuel a p mode hb => congrArg Prod.fst (ratBaseSel_bad (hb _ rfl) _ _ _))
    (fun fuel a p mode hq => congrArg Prod.fst (ratBaseSel_one (coe_eq_of_some_eq hq) _ _ _))
    (fun fuel a p mode qv av bv hq h0 h1 hx hy => by
      have e := coe_eq_of_some_eq hq
      rw [← e] at h0 h1
      show (lnAbsQBetaRatFloatFloatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode).1 = _
      rw [lnAbsQBetaRatFloatFloatPrecRoundFuel_eq_of fuel h0 h1 hx hy])
    (fun fuel a p _ mode qv hq h0 h1 hx => by
      have hQ : QBaseSpec (qBaseRat a.1) qv := by
        have e' := coe_eq_of_some_eq hq
        rw [← e'] at h0 h1 ⊢
        exact qBaseRat_spec a.1 h0 h1
      have e := coe_eq_of_some_eq hq
      rw [← e] at h0 h1
      show (lnAbsQBetaRatFloatFloatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode).1 = _
      rw [show lnAbsQBetaRatFloatFloatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode
          = lnAbsQBetaFloatArgs (qBaseRat a.1) fuel a.2.1 a.2.2 p mode
        from ratBaseSel_real h0 h1 _ _ _]
      exact congrArg Prod.fst (lnAbsQBetaFloatArgs_nonreal hQ fuel a.2.1 a.2.2 hx p mode))

/-- **The specification of `ln B_q(a, b)` for a rational `q` and floats `a`, `b`** (`ZivSpec`). -/
theorem lnQBetaRatFloatFloatPrecRoundFuel_zivSpec :
    ZivSpec
      (fun a : AzRat × AzFloat × AzFloat =>
        a.2.1.toVal.bind fun x => a.2.2.toVal.bind fun y => Spec.lnQBeta
            (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal) x y)
      (fun fuel a p mode => lnQBetaRatFloatFloatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode)
      {a | QBase2D (fun a : AzRat × AzFloat × AzFloat => some (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal))
          (fun a => a.2.1.toVal)
          (fun a => a.2.2.toVal)
          (QLnBetaPD (fun a => qBaseRat a.1) (fun a => qArgFloat a.2.1)
            (fun a => qArgFloat a.2.2)) a}
      {a | QBase2N (fun a : AzRat × AzFloat × AzFloat => some (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal))
          (fun a => a.2.1.toVal)
          (fun a => a.2.2.toVal)
          (QLnBetaPN (fun a => qBaseRat a.1) (fun a => qArgFloat a.2.1)
            (fun a => qArgFloat a.2.2)) a} :=
  lnQBeta_zivSpec_sides (α := AzRat × AzFloat × AzFloat)
    (qe := fun a => some (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal))
    (xe := fun a => a.2.1.toVal)
    (ye := fun a => a.2.2.toVal)
    (f := fun fuel a p mode => lnQBetaRatFloatFloatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode)
    (fΓ := fun fuel a p mode => lnBetaPrecRoundFuel fuel a.2.1 a.2.2 p mode)
    (fun a => qBaseRat a.1) (fun a => qArgFloat a.2.1) (fun a => qArgFloat a.2.2)
    (fun a => qArgSumFloat a.2.1 a.2.2)
    (fun a qv hq h0 h1 => by
      have e := coe_eq_of_some_eq hq
      rw [← e] at h0 h1 ⊢
      exact qBaseRat_spec a.1 h0 h1)
    (fun a av bv hx hy => ⟨qArgFloat_spec hx, qArgFloat_spec hy, qArgSumFloat_spec hx hy⟩)
    (fun fuel a p _ mode => lnBetaPrecRoundFuel_zivSpec.sound fuel a.2 p mode)
    (fun a p _ mode hB => lnBetaPrecRoundFuel_zivSpec.complete a.2 p mode hB)
    (fun fuel a p mode hb => ratBaseSel_bad (hb _ rfl) _ _ _)
    (fun fuel a p mode hq => ratBaseSel_one (coe_eq_of_some_eq hq) _ _ _)
    (fun fuel a p mode qv av bv hq h0 h1 hx hy => by
      have e := coe_eq_of_some_eq hq
      rw [← e] at h0 h1
      show lnQBetaRatFloatFloatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode = _
      rw [show lnQBetaRatFloatFloatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode
          = lnOfSigned (lnAbsQBetaRatFloatFloatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode)
        from (ratBaseSel_real h0 h1 _ _ _).trans
            (congrArg lnOfSigned (ratBaseSel_real h0 h1 _ _ _).symm),
        lnAbsQBetaRatFloatFloatPrecRoundFuel_eq_of fuel h0 h1 hx hy])
    (fun fuel a p _ mode qv hq h0 h1 hx => by
      have hQ : QBaseSpec (qBaseRat a.1) qv := by
        have e' := coe_eq_of_some_eq hq
        rw [← e'] at h0 h1 ⊢
        exact qBaseRat_spec a.1 h0 h1
      have e := coe_eq_of_some_eq hq
      rw [← e] at h0 h1
      show lnQBetaRatFloatFloatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode = _
      rw [show lnQBetaRatFloatFloatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode
          = lnOfSigned (lnAbsQBetaFloatArgs (qBaseRat a.1) fuel a.2.1 a.2.2 p mode)
        from ratBaseSel_real h0 h1 _ _ _]
      exact lnQBetaFloatArgs_nonreal hQ fuel a.2.1 a.2.2 hx p mode)

/-- **The specification of `ln |B_q(a, b)|` for a rational `q`, a float `a` and a rational `b`**
(the value component; `ZivSpec`). -/
theorem lnAbsQBetaRatFloatRatPrecRoundFuel_zivSpec :
    ZivSpec
      (fun a : AzRat × AzFloat × AzRat =>
        a.2.1.toVal.bind fun x => Spec.lnAbsQBeta (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal) x
            (((AzRat.toRat a.2.2 : ℚ) : ℝ) : EReal))
      (fun fuel a p mode => (lnAbsQBetaRatFloatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode).1)
      {a | QBase2D (fun a : AzRat × AzFloat × AzRat => some (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal))
          (fun a => a.2.1.toVal)
          (fun a => some (((AzRat.toRat a.2.2 : ℚ) : ℝ) : EReal))
          (QLnBetaPD (fun a => qBaseRat a.1) (fun a => qArgRat (a.2.1.toAzRat?.getD 0))
            (fun a => qArgRat a.2.2)) a}
      {a | QBase2N (fun a : AzRat × AzFloat × AzRat => some (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal))
          (fun a => a.2.1.toVal)
          (fun a => some (((AzRat.toRat a.2.2 : ℚ) : ℝ) : EReal))
          (QLnBetaPN (fun a => qBaseRat a.1) (fun a => qArgRat (a.2.1.toAzRat?.getD 0))
            (fun a => qArgRat a.2.2)) a} :=
  lnAbsQBeta_zivSpec_sides (α := AzRat × AzFloat × AzRat)
    (qe := fun a => some (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal))
    (xe := fun a => a.2.1.toVal)
    (ye := fun a => some (((AzRat.toRat a.2.2 : ℚ) : ℝ) : EReal))
    (f := fun fuel a p mode => (lnAbsQBetaRatFloatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode).1)
    (fΓ := fun fuel a p mode => (lnAbsBetaFloatRatPrecRoundFuel fuel a.2.1 a.2.2 p mode).1)
    (fun a => qBaseRat a.1) (fun a => qArgRat (a.2.1.toAzRat?.getD 0)) (fun a => qArgRat a.2.2)
    (fun a => qArgRat (a.2.1.toAzRat?.getD 0 + a.2.2))
    (fun a qv hq h0 h1 => by
      have e := coe_eq_of_some_eq hq
      rw [← e] at h0 h1 ⊢
      exact qBaseRat_spec a.1 h0 h1)
    (fun a av bv hx hy => by
      have e := coe_eq_of_some_eq hy
      rw [← e]
      exact qBetaMixed_arg hx a.2.2)
    (fun fuel a p _ mode => lnAbsBetaFloatRatPrecRoundFuel_zivSpec.sound fuel a.2 p mode)
    (fun a p _ mode hB => lnAbsBetaFloatRatPrecRoundFuel_zivSpec.complete a.2 p mode hB)
    (fun fuel a p mode hb => congrArg Prod.fst (ratBaseSel_bad (hb _ rfl) _ _ _))
    (fun fuel a p mode hq => congrArg Prod.fst (ratBaseSel_one (coe_eq_of_some_eq hq) _ _ _))
    (fun fuel a p mode qv av bv hq h0 h1 hx hy => by
      have e := coe_eq_of_some_eq hq
      rw [← e] at h0 h1
      show (lnAbsQBetaRatFloatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode).1 = _
      rw [lnAbsQBetaRatFloatRatPrecRoundFuel_eq_of fuel h0 h1 hx])
    (fun fuel a p _ mode qv hq h0 h1 hx => by
      have hQ : QBaseSpec (qBaseRat a.1) qv := by
        have e' := coe_eq_of_some_eq hq
        rw [← e'] at h0 h1 ⊢
        exact qBaseRat_spec a.1 h0 h1
      have e := coe_eq_of_some_eq hq
      rw [← e] at h0 h1
      show (lnAbsQBetaRatFloatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode).1 = _
      rw [show lnAbsQBetaRatFloatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode
          = lnAbsQBetaMixedArgs (qBaseRat a.1) fuel a.2.1 a.2.2 p mode
        from ratBaseSel_real h0 h1 _ _ _]
      exact congrArg Prod.fst (lnAbsQBetaMixedArgs_nonreal hQ fuel a.2.1 a.2.2
        (fun av h => hx ⟨av, _, h, rfl⟩) p mode))

/-- **The specification of `ln B_q(a, b)` for a rational `q`, a float `a` and a rational `b`**
(`ZivSpec`). -/
theorem lnQBetaRatFloatRatPrecRoundFuel_zivSpec :
    ZivSpec
      (fun a : AzRat × AzFloat × AzRat =>
        a.2.1.toVal.bind fun x => Spec.lnQBeta (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal) x
            (((AzRat.toRat a.2.2 : ℚ) : ℝ) : EReal))
      (fun fuel a p mode => lnQBetaRatFloatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode)
      {a | QBase2D (fun a : AzRat × AzFloat × AzRat => some (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal))
          (fun a => a.2.1.toVal)
          (fun a => some (((AzRat.toRat a.2.2 : ℚ) : ℝ) : EReal))
          (QLnBetaPD (fun a => qBaseRat a.1) (fun a => qArgRat (a.2.1.toAzRat?.getD 0))
            (fun a => qArgRat a.2.2)) a}
      {a | QBase2N (fun a : AzRat × AzFloat × AzRat => some (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal))
          (fun a => a.2.1.toVal)
          (fun a => some (((AzRat.toRat a.2.2 : ℚ) : ℝ) : EReal))
          (QLnBetaPN (fun a => qBaseRat a.1) (fun a => qArgRat (a.2.1.toAzRat?.getD 0))
            (fun a => qArgRat a.2.2)) a} :=
  lnQBeta_zivSpec_sides (α := AzRat × AzFloat × AzRat)
    (qe := fun a => some (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal))
    (xe := fun a => a.2.1.toVal)
    (ye := fun a => some (((AzRat.toRat a.2.2 : ℚ) : ℝ) : EReal))
    (f := fun fuel a p mode => lnQBetaRatFloatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode)
    (fΓ := fun fuel a p mode => lnBetaFloatRatPrecRoundFuel fuel a.2.1 a.2.2 p mode)
    (fun a => qBaseRat a.1) (fun a => qArgRat (a.2.1.toAzRat?.getD 0)) (fun a => qArgRat a.2.2)
    (fun a => qArgRat (a.2.1.toAzRat?.getD 0 + a.2.2))
    (fun a qv hq h0 h1 => by
      have e := coe_eq_of_some_eq hq
      rw [← e] at h0 h1 ⊢
      exact qBaseRat_spec a.1 h0 h1)
    (fun a av bv hx hy => by
      have e := coe_eq_of_some_eq hy
      rw [← e]
      exact qBetaMixed_arg hx a.2.2)
    (fun fuel a p _ mode => lnBetaFloatRatPrecRoundFuel_zivSpec.sound fuel a.2 p mode)
    (fun a p _ mode hB => lnBetaFloatRatPrecRoundFuel_zivSpec.complete a.2 p mode hB)
    (fun fuel a p mode hb => ratBaseSel_bad (hb _ rfl) _ _ _)
    (fun fuel a p mode hq => ratBaseSel_one (coe_eq_of_some_eq hq) _ _ _)
    (fun fuel a p mode qv av bv hq h0 h1 hx hy => by
      have e := coe_eq_of_some_eq hq
      rw [← e] at h0 h1
      show lnQBetaRatFloatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode = _
      rw [show lnQBetaRatFloatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode
          = lnOfSigned (lnAbsQBetaRatFloatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode)
        from (ratBaseSel_real h0 h1 _ _ _).trans
            (congrArg lnOfSigned (ratBaseSel_real h0 h1 _ _ _).symm),
        lnAbsQBetaRatFloatRatPrecRoundFuel_eq_of fuel h0 h1 hx])
    (fun fuel a p _ mode qv hq h0 h1 hx => by
      have hQ : QBaseSpec (qBaseRat a.1) qv := by
        have e' := coe_eq_of_some_eq hq
        rw [← e'] at h0 h1 ⊢
        exact qBaseRat_spec a.1 h0 h1
      have e := coe_eq_of_some_eq hq
      rw [← e] at h0 h1
      show lnQBetaRatFloatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode = _
      rw [show lnQBetaRatFloatRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode
          = lnOfSigned (lnAbsQBetaMixedArgs (qBaseRat a.1) fuel a.2.1 a.2.2 p mode)
        from ratBaseSel_real h0 h1 _ _ _]
      exact lnQBetaMixedArgs_nonreal hQ fuel a.2.1 a.2.2
        (fun av h => hx ⟨av, _, h, rfl⟩) p mode)

/-- **The specification of `ln |B_q(a, b)|` for rationals `q`, `a`, `b`** (the value component;
`ZivSpec`). -/
theorem lnAbsQBetaRatPrecRoundFuel_zivSpec :
    ZivSpec
      (fun a : AzRat × AzRat × AzRat =>
        Spec.lnAbsQBeta (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal)
            (((AzRat.toRat a.2.1 : ℚ) : ℝ) : EReal) (((AzRat.toRat a.2.2 : ℚ) : ℝ) : EReal))
      (fun fuel a p mode => (lnAbsQBetaRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode).1)
      {a | QBase2D (fun a : AzRat × AzRat × AzRat => some (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal))
          (fun a => some (((AzRat.toRat a.2.1 : ℚ) : ℝ) : EReal))
          (fun a => some (((AzRat.toRat a.2.2 : ℚ) : ℝ) : EReal))
          (QLnBetaPD (fun a => qBaseRat a.1) (fun a => qArgRat a.2.1)
            (fun a => qArgRat a.2.2)) a}
      {a | QBase2N (fun a : AzRat × AzRat × AzRat => some (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal))
          (fun a => some (((AzRat.toRat a.2.1 : ℚ) : ℝ) : EReal))
          (fun a => some (((AzRat.toRat a.2.2 : ℚ) : ℝ) : EReal))
          (QLnBetaPN (fun a => qBaseRat a.1) (fun a => qArgRat a.2.1)
            (fun a => qArgRat a.2.2)) a} :=
  lnAbsQBeta_zivSpec_sides (α := AzRat × AzRat × AzRat)
    (qe := fun a => some (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal))
    (xe := fun a => some (((AzRat.toRat a.2.1 : ℚ) : ℝ) : EReal))
    (ye := fun a => some (((AzRat.toRat a.2.2 : ℚ) : ℝ) : EReal))
    (f := fun fuel a p mode => (lnAbsQBetaRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode).1)
    (fΓ := fun fuel a p mode => (lnAbsBetaRatPrecRoundFuel fuel a.2.1 a.2.2 p mode).1)
    (fun a => qBaseRat a.1) (fun a => qArgRat a.2.1) (fun a => qArgRat a.2.2)
    (fun a => qArgRat (a.2.1 + a.2.2))
    (fun a qv hq h0 h1 => by
      have e := coe_eq_of_some_eq hq
      rw [← e] at h0 h1 ⊢
      exact qBaseRat_spec a.1 h0 h1)
    (fun a av bv hx hy => by
      have e1 := coe_eq_of_some_eq hx
      have e2 := coe_eq_of_some_eq hy
      rw [← e1, ← e2]
      exact qBetaRat_arg a.2.1 a.2.2)
    (fun fuel a p _ mode => lnAbsBetaRatPrecRoundFuel_zivSpec.sound fuel a.2 p mode)
    (fun a p _ mode hB => lnAbsBetaRatPrecRoundFuel_zivSpec.complete a.2 p mode hB)
    (fun fuel a p mode hb => congrArg Prod.fst (ratBaseSel_bad (hb _ rfl) _ _ _))
    (fun fuel a p mode hq => congrArg Prod.fst (ratBaseSel_one (coe_eq_of_some_eq hq) _ _ _))
    (fun fuel a p mode qv av bv hq h0 h1 hx hy => by
      have e := coe_eq_of_some_eq hq
      rw [← e] at h0 h1
      show (lnAbsQBetaRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode).1 = _
      rw [lnAbsQBetaRatPrecRoundFuel_eq_of fuel h0 h1 ])
    (fun fuel a p _ mode qv hq h0 h1 hx => by
      have hQ : QBaseSpec (qBaseRat a.1) qv := by
        have e' := coe_eq_of_some_eq hq
        rw [← e'] at h0 h1 ⊢
        exact qBaseRat_spec a.1 h0 h1
      have e := coe_eq_of_some_eq hq
      rw [← e] at h0 h1
      show (lnAbsQBetaRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode).1 = _
      rw [show lnAbsQBetaRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode
          = lnAbsQBetaRatArgs (qBaseRat a.1) fuel a.2.1 a.2.2 p mode
        from ratBaseSel_real h0 h1 _ _ _]
      exact absurd ⟨_, _, rfl, rfl⟩ hx)

/-- **The specification of `ln B_q(a, b)` for rationals `q`, `a`, `b`** (`ZivSpec`). -/
theorem lnQBetaRatPrecRoundFuel_zivSpec :
    ZivSpec
      (fun a : AzRat × AzRat × AzRat =>
        Spec.lnQBeta (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal) (((AzRat.toRat a.2.1 : ℚ) : ℝ) : EReal)
            (((AzRat.toRat a.2.2 : ℚ) : ℝ) : EReal))
      (fun fuel a p mode => lnQBetaRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode)
      {a | QBase2D (fun a : AzRat × AzRat × AzRat => some (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal))
          (fun a => some (((AzRat.toRat a.2.1 : ℚ) : ℝ) : EReal))
          (fun a => some (((AzRat.toRat a.2.2 : ℚ) : ℝ) : EReal))
          (QLnBetaPD (fun a => qBaseRat a.1) (fun a => qArgRat a.2.1)
            (fun a => qArgRat a.2.2)) a}
      {a | QBase2N (fun a : AzRat × AzRat × AzRat => some (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal))
          (fun a => some (((AzRat.toRat a.2.1 : ℚ) : ℝ) : EReal))
          (fun a => some (((AzRat.toRat a.2.2 : ℚ) : ℝ) : EReal))
          (QLnBetaPN (fun a => qBaseRat a.1) (fun a => qArgRat a.2.1)
            (fun a => qArgRat a.2.2)) a} :=
  lnQBeta_zivSpec_sides (α := AzRat × AzRat × AzRat)
    (qe := fun a => some (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal))
    (xe := fun a => some (((AzRat.toRat a.2.1 : ℚ) : ℝ) : EReal))
    (ye := fun a => some (((AzRat.toRat a.2.2 : ℚ) : ℝ) : EReal))
    (f := fun fuel a p mode => lnQBetaRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode)
    (fΓ := fun fuel a p mode => lnBetaRatPrecRoundFuel fuel a.2.1 a.2.2 p mode)
    (fun a => qBaseRat a.1) (fun a => qArgRat a.2.1) (fun a => qArgRat a.2.2)
    (fun a => qArgRat (a.2.1 + a.2.2))
    (fun a qv hq h0 h1 => by
      have e := coe_eq_of_some_eq hq
      rw [← e] at h0 h1 ⊢
      exact qBaseRat_spec a.1 h0 h1)
    (fun a av bv hx hy => by
      have e1 := coe_eq_of_some_eq hx
      have e2 := coe_eq_of_some_eq hy
      rw [← e1, ← e2]
      exact qBetaRat_arg a.2.1 a.2.2)
    (fun fuel a p _ mode => lnBetaRatPrecRoundFuel_zivSpec.sound fuel a.2 p mode)
    (fun a p _ mode hB => lnBetaRatPrecRoundFuel_zivSpec.complete a.2 p mode hB)
    (fun fuel a p mode hb => ratBaseSel_bad (hb _ rfl) _ _ _)
    (fun fuel a p mode hq => ratBaseSel_one (coe_eq_of_some_eq hq) _ _ _)
    (fun fuel a p mode qv av bv hq h0 h1 hx hy => by
      have e := coe_eq_of_some_eq hq
      rw [← e] at h0 h1
      show lnQBetaRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode = _
      rw [show lnQBetaRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode
          = lnOfSigned (lnAbsQBetaRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode)
        from (ratBaseSel_real h0 h1 _ _ _).trans
            (congrArg lnOfSigned (ratBaseSel_real h0 h1 _ _ _).symm),
        lnAbsQBetaRatPrecRoundFuel_eq_of fuel h0 h1 ])
    (fun fuel a p _ mode qv hq h0 h1 hx => by
      have hQ : QBaseSpec (qBaseRat a.1) qv := by
        have e' := coe_eq_of_some_eq hq
        rw [← e'] at h0 h1 ⊢
        exact qBaseRat_spec a.1 h0 h1
      have e := coe_eq_of_some_eq hq
      rw [← e] at h0 h1
      show lnQBetaRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode = _
      rw [show lnQBetaRatPrecRoundFuel fuel a.1 a.2.1 a.2.2 p mode
          = lnOfSigned (lnAbsQBetaRatArgs (qBaseRat a.1) fuel a.2.1 a.2.2 p mode)
        from ratBaseSel_real h0 h1 _ _ _]
      exact absurd ⟨_, _, rfl, rfl⟩ hx)

/-! ### At the default fuel -/

theorem lnAbsQBetaPrecRound_eq_or (q a b : AzFloat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    (lnAbsQBetaPrecRound q a b p mode).1 = roundVal p mode
        (q.toVal.bind fun qe => a.toVal.bind fun x => b.toVal.bind fun y =>
          Spec.lnAbsQBeta qe x
            y) ∨
      (lnAbsQBetaPrecRound q a b p mode).1 = (nan, .eq) :=
  lnAbsQBetaPrecRoundFuel_zivSpec.sound _ (q, a, b) p mode

theorem lnQBetaPrecRound_eq_or (q a b : AzFloat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    lnQBetaPrecRound q a b p mode = roundVal p mode
        (q.toVal.bind fun qe => a.toVal.bind fun x => b.toVal.bind fun y =>
          Spec.lnQBeta qe x
            y) ∨
      lnQBetaPrecRound q a b p mode = (nan, .eq) :=
  lnQBetaPrecRoundFuel_zivSpec.sound _ (q, a, b) p mode

theorem lnAbsQBetaFloatFloatRatPrecRound_eq_or (q a : AzFloat) (b : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    (lnAbsQBetaFloatFloatRatPrecRound q a b p mode).1 = roundVal p mode
        (q.toVal.bind fun qe => a.toVal.bind fun x =>
          Spec.lnAbsQBeta qe x
            (((AzRat.toRat b : ℚ) : ℝ) : EReal)) ∨
      (lnAbsQBetaFloatFloatRatPrecRound q a b p mode).1 = (nan, .eq) :=
  lnAbsQBetaFloatFloatRatPrecRoundFuel_zivSpec.sound _ (q, a, b) p mode

theorem lnQBetaFloatFloatRatPrecRound_eq_or (q a : AzFloat) (b : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    lnQBetaFloatFloatRatPrecRound q a b p mode = roundVal p mode
        (q.toVal.bind fun qe => a.toVal.bind fun x =>
          Spec.lnQBeta qe x
            (((AzRat.toRat b : ℚ) : ℝ) : EReal)) ∨
      lnQBetaFloatFloatRatPrecRound q a b p mode = (nan, .eq) :=
  lnQBetaFloatFloatRatPrecRoundFuel_zivSpec.sound _ (q, a, b) p mode

theorem lnAbsQBetaFloatRatRatPrecRound_eq_or (q : AzFloat) (a b : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    (lnAbsQBetaFloatRatRatPrecRound q a b p mode).1 = roundVal p mode
        (q.toVal.bind fun qe =>
          Spec.lnAbsQBeta qe (((AzRat.toRat a : ℚ) : ℝ) : EReal)
            (((AzRat.toRat b : ℚ) : ℝ) : EReal)) ∨
      (lnAbsQBetaFloatRatRatPrecRound q a b p mode).1 = (nan, .eq) :=
  lnAbsQBetaFloatRatRatPrecRoundFuel_zivSpec.sound _ (q, a, b) p mode

theorem lnQBetaFloatRatRatPrecRound_eq_or (q : AzFloat) (a b : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    lnQBetaFloatRatRatPrecRound q a b p mode = roundVal p mode
        (q.toVal.bind fun qe =>
          Spec.lnQBeta qe (((AzRat.toRat a : ℚ) : ℝ) : EReal)
            (((AzRat.toRat b : ℚ) : ℝ) : EReal)) ∨
      lnQBetaFloatRatRatPrecRound q a b p mode = (nan, .eq) :=
  lnQBetaFloatRatRatPrecRoundFuel_zivSpec.sound _ (q, a, b) p mode

theorem lnAbsQBetaRatFloatFloatPrecRound_eq_or (q : AzRat) (a b : AzFloat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    (lnAbsQBetaRatFloatFloatPrecRound q a b p mode).1 = roundVal p mode
        (a.toVal.bind fun x => b.toVal.bind fun y =>
          Spec.lnAbsQBeta (((AzRat.toRat q : ℚ) : ℝ) : EReal) x
            y) ∨
      (lnAbsQBetaRatFloatFloatPrecRound q a b p mode).1 = (nan, .eq) :=
  lnAbsQBetaRatFloatFloatPrecRoundFuel_zivSpec.sound _ (q, a, b) p mode

theorem lnQBetaRatFloatFloatPrecRound_eq_or (q : AzRat) (a b : AzFloat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    lnQBetaRatFloatFloatPrecRound q a b p mode = roundVal p mode
        (a.toVal.bind fun x => b.toVal.bind fun y =>
          Spec.lnQBeta (((AzRat.toRat q : ℚ) : ℝ) : EReal) x
            y) ∨
      lnQBetaRatFloatFloatPrecRound q a b p mode = (nan, .eq) :=
  lnQBetaRatFloatFloatPrecRoundFuel_zivSpec.sound _ (q, a, b) p mode

theorem lnAbsQBetaRatFloatRatPrecRound_eq_or (q : AzRat) (a : AzFloat) (b : AzRat) (p : ℕ)
    [NeZero p] (mode : RoundingMode) :
    (lnAbsQBetaRatFloatRatPrecRound q a b p mode).1 = roundVal p mode
        (a.toVal.bind fun x =>
          Spec.lnAbsQBeta (((AzRat.toRat q : ℚ) : ℝ) : EReal) x
            (((AzRat.toRat b : ℚ) : ℝ) : EReal)) ∨
      (lnAbsQBetaRatFloatRatPrecRound q a b p mode).1 = (nan, .eq) :=
  lnAbsQBetaRatFloatRatPrecRoundFuel_zivSpec.sound _ (q, a, b) p mode

theorem lnQBetaRatFloatRatPrecRound_eq_or (q : AzRat) (a : AzFloat) (b : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    lnQBetaRatFloatRatPrecRound q a b p mode = roundVal p mode
        (a.toVal.bind fun x =>
          Spec.lnQBeta (((AzRat.toRat q : ℚ) : ℝ) : EReal) x
            (((AzRat.toRat b : ℚ) : ℝ) : EReal)) ∨
      lnQBetaRatFloatRatPrecRound q a b p mode = (nan, .eq) :=
  lnQBetaRatFloatRatPrecRoundFuel_zivSpec.sound _ (q, a, b) p mode

theorem lnAbsQBetaRatPrecRound_eq_or (q a b : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    (lnAbsQBetaRatPrecRound q a b p mode).1 = roundVal p mode
        (Spec.lnAbsQBeta (((AzRat.toRat q : ℚ) : ℝ) : EReal) (((AzRat.toRat a : ℚ) : ℝ) : EReal)
            (((AzRat.toRat b : ℚ) : ℝ) : EReal)) ∨
      (lnAbsQBetaRatPrecRound q a b p mode).1 = (nan, .eq) :=
  lnAbsQBetaRatPrecRoundFuel_zivSpec.sound _ (q, a, b) p mode

theorem lnQBetaRatPrecRound_eq_or (q a b : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    lnQBetaRatPrecRound q a b p mode = roundVal p mode
        (Spec.lnQBeta (((AzRat.toRat q : ℚ) : ℝ) : EReal) (((AzRat.toRat a : ℚ) : ℝ) : EReal)
            (((AzRat.toRat b : ℚ) : ℝ) : EReal)) ∨
      lnQBetaRatPrecRound q a b p mode = (nan, .eq) :=
  lnQBetaRatPrecRoundFuel_zivSpec.sound _ (q, a, b) p mode

end Azurite.AzFloat
