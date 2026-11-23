/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.QGamma
import Azurite.AzFloat.Equiv.QGammaWidth
import Azurite.AzFloat.Equiv.Gamma
import Azurite.AzFloat.Equiv.GammaRat
import Azurite.AzFloat.Equiv.LnBarnesG
import Azurite.AzFloat.Equiv.PochhammerRatCertificate

/-!
# Equivalence: the `q`-gamma function

`Spec.qGamma` and the specifications of the four functions of `AzFloat/QGamma.lean`:
**`qGammaPrecRoundFuel_zivSpec`**, **`qGammaFloatRatPrecRoundFuel_zivSpec`**,
**`qGammaRatFloatPrecRoundFuel_zivSpec`**, **`qGammaRatPrecRoundFuel_zivSpec`** — sound at
every fuel, complete in the limit of the fuel wherever the value is no rounding boundary, and
correct at every fuel on the special values (a base that is not positive and finite, an
argument that is not finite, `0`, the poles) and on the exact values at a dyadic base.  At the
base `1` the function is `Γ` with its own specification.

The four are instances of `qGamma_zivSpec_of`, from the function on a base and an argument
given by their data: `qGammaOf_eq_or_loop` (exact, or the loop off the poles),
`qGammaOf_main`, `qGammaOf_complete` (the bracket converges: `Equiv/QGammaWidth.lean`),
`qGammaOf_exact` (**correct at every fuel on the exact class `QExact`**, whether the value is
dyadic or not: this is the statement for a rational base).
-/

namespace Azurite.AzFloat

open Finset DLMF

namespace Spec

open Classical in
/-- `Γ_q` for a real base `q > 0`, `q ≠ 1`, on the extended reals: `+∞` at `0` (from the
right) and at `+∞`; undefined at the poles `−1, −2, …` and at `−∞`. -/
noncomputable def qGammaAt (qv : ℝ) (x : EReal) : Option EReal :=
  if x = ⊤ then some ⊤ else if x = ⊥ then none else if x = 0 then some ⊤
  else if x < 0 ∧ ∃ k : ℤ, x.toReal = k then none
  else some ((qGammaReal qv x.toReal : ℝ) : EReal)

open Classical in
/-- **`Γ_q(x)` on the extended reals**: undefined for a base `q ≤ 0` or `q = +∞`, `Γ(x)` at
`q = 1`. -/
noncomputable def qGamma (q x : EReal) : Option EReal :=
  if q ≤ 0 ∨ q = ⊤ then none else if q = 1 then gamma x else qGammaAt q.toReal x

theorem qGammaAt_top (qv : ℝ) : qGammaAt qv ⊤ = some ⊤ := by simp [qGammaAt]

theorem qGammaAt_bot (qv : ℝ) : qGammaAt qv ⊥ = none := by
  unfold qGammaAt
  rw [ite_eq_right bot_ne_top, ite_eq_left rfl]

theorem qGammaAt_zero (qv : ℝ) : qGammaAt qv ((0 : ℝ) : EReal) = some ⊤ := by
  unfold qGammaAt
  rw [ite_eq_right (EReal.coe_ne_top _), ite_eq_right (EReal.coe_ne_bot _),
    ite_eq_left (by simp)]

theorem qGammaAt_pole (qv : ℝ) (m : ℕ) :
    qGammaAt qv ((-((m : ℝ) + 1) : ℝ) : EReal) = none := by
  have hneg : -((m : ℝ) + 1) < 0 := by
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  unfold qGammaAt
  rw [ite_eq_right (EReal.coe_ne_top _), ite_eq_right (EReal.coe_ne_bot _),
    ite_eq_right (by exact_mod_cast hneg.ne),
    ite_eq_left ⟨by exact_mod_cast hneg, ⟨-((m : ℤ) + 1), by
      rw [EReal.toReal_coe]
      push_cast
      ring⟩⟩]

theorem qGammaAt_coe (qv : ℝ) {xv : ℝ} (hnz : ∀ m : ℕ, xv ≠ -m) :
    qGammaAt qv (xv : EReal) = some ((qGammaReal qv xv : ℝ) : EReal) := by
  have h0 : xv ≠ 0 := by simpa using hnz 0
  have hp : ¬ (xv < 0 ∧ ∃ k : ℤ, xv = k) := by
    rintro ⟨hneg, k, hk⟩
    have hk0 : k < 0 := by exact_mod_cast (hk ▸ hneg : (k : ℝ) < 0)
    refine hnz (-k).toNat ?_
    have : ((-k).toNat : ℤ) = -k := Int.toNat_of_nonneg (by omega)
    have h2 : (((-k).toNat : ℤ) : ℝ) = ((-k : ℤ) : ℝ) := by rw [this]
    push_cast at h2
    rw [hk]
    linarith
  unfold qGammaAt
  rw [ite_eq_right (EReal.coe_ne_top _), ite_eq_right (EReal.coe_ne_bot _),
    ite_eq_right (by exact_mod_cast h0),
    ite_eq_right (fun hc => hp ⟨by exact_mod_cast hc.1, by simpa using hc.2⟩), EReal.toReal_coe]

theorem qGamma_none {q : EReal} (hq : q ≤ 0 ∨ q = ⊤) (x : EReal) : qGamma q x = none := by
  unfold qGamma
  rw [ite_eq_left hq]

theorem qGamma_one (x : EReal) : qGamma 1 x = gamma x := by
  unfold qGamma
  rw [ite_eq_right (by
      rintro (h | h)
      · have : (1 : ℝ) ≤ 0 := by exact_mod_cast h
        linarith
      · exact EReal.coe_ne_top 1 (by exact_mod_cast h)), ite_eq_left rfl]

theorem qGamma_coe {qv : ℝ} (hq0 : 0 < qv) (hq1 : qv ≠ 1) (x : EReal) :
    qGamma (qv : EReal) x = qGammaAt qv x := by
  unfold qGamma
  rw [ite_eq_right (by
      rintro (h | h)
      · have : qv ≤ 0 := by exact_mod_cast h
        linarith
      · exact EReal.coe_ne_top _ h),
    ite_eq_right (by
      intro h
      exact hq1 (by exact_mod_cast h)), EReal.toReal_coe]

theorem qGamma_coe_nonpos {qv : ℝ} (hq : qv ≤ 0) (x : EReal) : qGamma (qv : EReal) x = none :=
  qGamma_none (Or.inl (by exact_mod_cast hq)) x

end Spec

/-! ### Dyadic numbers -/

theorem IsDyadic.mul {a b : ℝ} (ha : IsDyadic a) (hb : IsDyadic b) : IsDyadic (a * b) := by
  obtain ⟨m, k, rfl⟩ := ha
  obtain ⟨n, l, rfl⟩ := hb
  refine ⟨m * n, k + l, ?_⟩
  rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  push_cast
  ring

theorem two_zpow_eq_natCast {k : ℤ} (hk : 0 ≤ k) :
    (2 : ℝ) ^ k = (((2 : ℤ) ^ k.toNat : ℤ) : ℝ) := by
  conv_lhs => rw [← Int.toNat_of_nonneg hk]
  rw [zpow_natCast]
  push_cast
  rfl

theorem IsDyadic.add {a b : ℝ} (ha : IsDyadic a) (hb : IsDyadic b) : IsDyadic (a + b) := by
  obtain ⟨m, k, rfl⟩ := ha
  obtain ⟨n, l, rfl⟩ := hb
  refine ⟨m * 2 ^ (k - min k l).toNat + n * 2 ^ (l - min k l).toNat, min k l, ?_⟩
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have e1 : (2 : ℝ) ^ k = (2 : ℝ) ^ (k - min k l) * (2 : ℝ) ^ min k l := by
    rw [← zpow_add₀ h2, sub_add_cancel]
  have e2 : (2 : ℝ) ^ l = (2 : ℝ) ^ (l - min k l) * (2 : ℝ) ^ min k l := by
    rw [← zpow_add₀ h2, sub_add_cancel]
  rw [e1, e2, two_zpow_eq_natCast (sub_nonneg.mpr (min_le_left k l)),
    two_zpow_eq_natCast (sub_nonneg.mpr (min_le_right k l))]
  push_cast
  ring

theorem IsDyadic.pow {a : ℝ} (ha : IsDyadic a) : ∀ n : ℕ, IsDyadic (a ^ n)
  | 0 => by simpa using isDyadic_one
  | n + 1 => by
    rw [pow_succ]
    exact (IsDyadic.pow ha n).mul ha

theorem isDyadic_sum_range {f : ℕ → ℝ} (hf : ∀ i, IsDyadic (f i)) :
    ∀ n : ℕ, IsDyadic (∑ i ∈ range n, f i)
  | 0 => by simpa using isDyadic_zero
  | n + 1 => by
    rw [sum_range_succ]
    exact (isDyadic_sum_range hf n).add (hf n)

theorem isDyadic_prod_range {f : ℕ → ℝ} (hf : ∀ i, IsDyadic (f i)) :
    ∀ n : ℕ, IsDyadic (∏ i ∈ range n, f i)
  | 0 => by simpa using isDyadic_one
  | n + 1 => by
    rw [prod_range_succ]
    exact (isDyadic_prod_range hf n).mul (hf n)

/-- The `q`-factorial of a dyadic `q` is dyadic. -/
theorem isDyadic_qFactorial {qv : ℝ} (hq : IsDyadic qv) (n : ℕ) :
    IsDyadic (∏ k ∈ range n, ∑ j ∈ range (k + 1), qv ^ j) :=
  isDyadic_prod_range (fun k => isDyadic_sum_range (fun j => hq.pow j) (k + 1)) n

/-! ### The exact values -/

theorem toRat_qFactorialRatAux (q : AzRat) : ∀ (k m : ℕ) (s g : AzRat),
    AzRat.toRat s = ∑ j ∈ range (m + 1), AzRat.toRat q ^ j →
    AzRat.toRat g = ∏ i ∈ range m, ∑ j ∈ range (i + 1), AzRat.toRat q ^ j →
    AzRat.toRat (qFactorialRatAux q k s g)
      = ∏ i ∈ range (m + k), ∑ j ∈ range (i + 1), AzRat.toRat q ^ j
  | 0, m, s, g, _, hg => by rw [qFactorialRatAux, hg, Nat.add_zero]
  | k + 1, m, s, g, hs, hg => by
    rw [qFactorialRatAux, toRat_qFactorialRatAux q k (m + 1) _ _ (by
      rw [AzRat.toRat_add, AzRat.toRat_mul, AzRat.toRat_one, hs, geom_sum_succ (n := m + 1)]
      ring) (by
      rw [AzRat.toRat_mul, hg, hs, prod_range_succ]),
      show m + 1 + k = m + (k + 1) by ring]

/-- **`qFactorialRat q n` is `∏_{k<n} (1 + q + ⋯ + q^k)`.** -/
theorem toRat_qFactorialRat (q : AzRat) (n : ℕ) :
    AzRat.toRat (qFactorialRat q n) = ∏ i ∈ range n, ∑ j ∈ range (i + 1), AzRat.toRat q ^ j := by
  unfold qFactorialRat
  rw [toRat_qFactorialRatAux q n 0 1 1 (by simp) (by simp), Nat.zero_add]

/-! ### The base and the argument -/

/-- **What a base says of `q`**: `q > 0`, `q ≠ 1`, `inv` iff `q > 1`, the enclosures of `q` or
`1/q`, and the rational is `q`. -/
structure QBaseSpec (Q : QBase) (qv : ℝ) : Prop where
  pos : 0 < qv
  ne_one : qv ≠ 1
  inv : Q.inv = true ↔ 1 < qv
  P : ∀ V, 64 ≤ V → LEncl (Q.P V) (if Q.inv then qv⁻¹ else qv) (6 * (1 / 2 : ℝ) ^ V)
  rat : ∀ r, Q.rat = some r → ((AzRat.toRat r : ℚ) : ℝ) = qv

/-- What a class says of the argument. -/
def QArgKind.Spec (k : QArgKind) (xv : ℝ) : Prop :=
  match k with
  | .zero => xv = 0
  | .pole => ∃ m : ℕ, xv = -((m : ℝ) + 1)
  | .posInt n => 1 ≤ n ∧ xv = n
  | .general => ∀ m : ℕ, xv ≠ -m

/-- **What an argument says of `x`.** -/
structure QArgSpec (S : QArg) (xv : ℝ) : Prop where
  X : ∃ C : ℝ, ∀ V, 64 ≤ V → AEncl (S.X V) xv (C * (1 / 2 : ℝ) ^ V)
  absX : ∃ C : ℝ, ∀ V, 64 ≤ V → AEncl0 (S.absX V) |xv| (C * (1 / 2 : ℝ) ^ V)
  kind : S.kind.Spec xv

/-- **The exact class**: `0`, a pole, or a positive integer whose value is formed at every
precision. -/
def QExact (Q : QBase) (S : QArg) : Prop :=
  match S.kind with
  | .zero => True
  | .pole => True
  | .posInt n => (qGammaExact? Q n 0).isSome = true
  | .general => False

variable {Q : QBase} {S : QArg} {qv xv : ℝ}

theorem qGammaArg_of (hQ : QBaseSpec Q qv) (hS : QArgSpec S xv) :
    QGammaArg (qGammaInOf Q S) (if Q.inv then qv⁻¹ else qv) xv where
  p_pos := by
    have := hQ.pos
    split_ifs
    · positivity
    · exact this
  p_lt := by
    by_cases h : Q.inv = true
    · rw [ite_eq_left h]
      exact inv_lt_one_of_one_lt₀ (hQ.inv.mp h)
    · rw [ite_eq_right h]
      have := mt hQ.inv.mpr h
      exact lt_of_le_of_ne (not_lt.mp this) hQ.ne_one
  P := hQ.P
  X := hS.X
  absX := hS.absX

/-- The value of the bracket is `Γ_q(x)`. -/
theorem qGammaVal_of (hQ : QBaseSpec Q qv) (xv : ℝ) :
    qGammaVal (qGammaInOf Q S).inv (if Q.inv then qv⁻¹ else qv) xv = qGammaReal qv xv := by
  have hq0 := hQ.pos
  show qGammaVal Q.inv _ xv = _
  unfold qGammaVal
  by_cases h : Q.inv = true
  · have h1 := hQ.inv.mp h
    rw [ite_eq_left h, ite_eq_left h, qGammaReal_of_one_lt h1, Real.log_inv, neg_neg,
      Real.rpow_def_of_pos hq0, mul_comm (Real.log qv)]
  · have h1 : qv < 1 := lt_of_le_of_ne (not_lt.mp (mt hQ.inv.mpr h)) hQ.ne_one
    rw [ite_eq_right h, ite_eq_right h, mul_one, qGammaReal_of_lt_one h1]

/-- The exact value is `Γ_q(n)`. -/
theorem qGammaExact?_spec (hQ : QBaseSpec Q qv) {n p : ℕ} {r : AzRat} (hn : 1 ≤ n)
    (h : qGammaExact? Q n p = some r) : ((AzRat.toRat r : ℚ) : ℝ) = qGammaReal qv n := by
  have hG := qGammaReal_nat hQ.pos hQ.ne_one (n - 1)
  have hcast : (((n - 1 : ℕ) : ℝ) + 1) = (n : ℝ) := by
    rw [Nat.cast_sub hn]
    push_cast
    ring
  rw [hcast] at hG
  rw [hG]
  unfold qGammaExact? at h
  by_cases h2 : n ≤ 2
  · rw [ite_eq_left h2, Option.some.injEq] at h
    subst h
    interval_cases n <;> simp
  · rw [ite_eq_right h2] at h
    split at h
    · next r0 hr0 =>
      split_ifs at h
      rw [Option.some.injEq] at h
      subst h
      rw [toRat_qFactorialRat, ← hQ.rat r0 hr0]
      push_cast
      rfl
    · exact absurd h (by simp)

/-- An exact value formed at precision `0` is formed at every precision. -/
theorem qGammaExact?_isSome_mono {n : ℕ} (h : (qGammaExact? Q n 0).isSome = true) (p : ℕ) :
    (qGammaExact? Q n p).isSome = true := by
  unfold qGammaExact? at h ⊢
  by_cases h2 : n ≤ 2
  · rw [ite_eq_left h2]
    rfl
  · rw [ite_eq_right h2] at h ⊢
    split
    · next r0 hr0 =>
      rw [hr0] at h
      dsimp only at h
      split_ifs at h with hc
      · rw [ite_eq_left (by omega)]
        rfl
      · exact absurd h (by simp)
    · next hnone =>
      rw [hnone] at h
      exact absurd h (by simp)

/-- **`Γ_q` on a base and an argument is correctly rounded, or it is the loop** off the
poles. -/
theorem qGammaOf_eq_or_loop (hQ : QBaseSpec Q qv) (hS : QArgSpec S xv) (fuel p : ℕ)
    [NeZero p] (mode : RoundingMode) :
    qGammaOf Q S fuel p mode = roundVal p mode (Spec.qGammaAt qv (xv : EReal)) ∨
      ((∀ m : ℕ, xv ≠ -m) ∧ qGammaOf Q S fuel p mode
        = zivLoop (qGammaApproxOf (qGammaInOf Q S)) p mode fuel (max 64 (p + 32))) := by
  have hp := NeZero.ne p
  have hk := hS.kind
  unfold qGammaOf
  cases hkind : S.kind with
  | zero =>
    rw [hkind] at hk
    left
    have : xv = 0 := hk
    dsimp only
    rw [this, Spec.qGammaAt_zero, roundVal_top]
  | pole =>
    rw [hkind] at hk
    left
    obtain ⟨m, hm⟩ := hk
    dsimp only
    rw [hm, Spec.qGammaAt_pole, roundVal_none]
  | posInt n =>
    rw [hkind] at hk
    obtain ⟨hn1, hxn⟩ := hk
    have hnz : ∀ m : ℕ, xv ≠ -m := fun m h => by
      have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      have h2 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      rw [hxn] at h
      linarith
    dsimp only
    rw [ite_eq_right hp]
    cases hex : qGammaExact? Q n p with
    | none => exact Or.inr ⟨hnz, rfl⟩
    | some r =>
      left
      dsimp only
      rw [ofAzRatRound_eq_roundVal, Spec.qGammaAt_coe qv hnz, qGammaExact?_spec hQ hn1 hex, hxn]
  | general =>
    rw [hkind] at hk
    dsimp only
    rw [ite_eq_right hp]
    exact Or.inr ⟨hk, rfl⟩

/-- The bracket of `Γ_q(x)` is valid, or rejected. -/
theorem qGammaApprox_valid_or_none (hQ : QBaseSpec Q qv) (hS : QArgSpec S xv) {w : ℕ}
    (hw : 64 ≤ w) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    (∃ lv hv : ℝ, Rounds (qGammaApproxOf (qGammaInOf Q S) w).1 lv ∧
        Rounds (qGammaApproxOf (qGammaInOf Q S) w).2 hv ∧
        lv ≤ qGammaReal qv xv ∧ qGammaReal qv xv ≤ hv ∧
        (lv = qGammaReal qv xv → hv = qGammaReal qv xv)) ∨
      roundingPossible (qGammaApproxOf (qGammaInOf Q S) w).1
        (qGammaApproxOf (qGammaInOf Q S) w).2 p mode = none :=
  gammaApproxOf_valid_or_none (fun _ _ hc => by
    have := qGammaCoreOf_spec (qGammaArg_of hQ hS) hw hc
    rwa [qGammaVal_of hQ] at this) w p mode

/-- **Correctly rounded or `NaN`, at every fuel.** -/
theorem qGammaOf_main (hQ : QBaseSpec Q qv) (hS : QArgSpec S xv) (fuel p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    qGammaOf Q S fuel p mode = roundVal p mode (Spec.qGammaAt qv (xv : EReal)) ∨
      qGammaOf Q S fuel p mode = (nan, .eq) := by
  rcases qGammaOf_eq_or_loop hQ hS fuel p mode with h | ⟨hnz, h⟩
  · exact Or.inl h
  · rcases eq_or_ne (qGammaOf Q S fuel p mode) (nan, .eq) with hz | hz
    · exact Or.inr hz
    · left
      rw [h] at hz ⊢
      rw [Spec.qGammaAt_coe qv hnz]
      exact zivLoop_eq_of_ne_nan_or_none p mode _ _ 64
        (fun w hw => qGammaApprox_valid_or_none hQ hS hw p mode) _ _ (le_max_left _ _) hz

/-- **Correctly rounded for every large enough fuel**, wherever the value is no rounding
boundary. -/
theorem qGammaOf_complete (hQ : QBaseSpec Q qv) (hS : QArgSpec S xv) (p : ℕ) [NeZero p]
    (mode : RoundingMode)
    (hB : ∀ v : ℝ, Spec.qGammaAt qv (xv : EReal) = some (v : EReal) →
      ((v : ℝ) : EReal) ∉ floatSet (p + 1)) :
    ∃ F : ℕ, ∀ fuel, F ≤ fuel →
      qGammaOf Q S fuel p mode = roundVal p mode (Spec.qGammaAt qv (xv : EReal)) := by
  by_cases hnz : ∀ m : ℕ, xv ≠ -m
  · have hB' := hB _ (Spec.qGammaAt_coe qv hnz)
    have hconv : CoreConv (qGammaCoreOf (qGammaInOf Q S)) (qGammaReal qv xv) := by
      have := qGammaCoreOf_coreConv (qGammaArg_of hQ hS) hnz
      rwa [qGammaVal_of hQ] at this
    obtain ⟨F, hF⟩ := zivLoop_eventually_eq p mode (qGammaApproxOf (qGammaInOf Q S))
      (gammaApproxOf_bracketConv hconv) (ne_zero_of_not_mem_floatSet hB') hB'
      (max 64 (p + 32)) (by omega)
      (fun w hw =>
        (qGammaApprox_valid_or_none hQ hS (le_trans (le_max_left _ _) hw) p mode).imp_left
          fun ⟨lv, hv, h1, h2, h3, h4, _⟩ => ⟨lv, hv, h1, h2, h3, h4⟩)
    refine ⟨F, fun fuel hfuel => ?_⟩
    rcases qGammaOf_eq_or_loop hQ hS fuel p mode with h | ⟨-, h⟩
    · exact h
    · rw [h, Spec.qGammaAt_coe qv hnz]
      exact hF fuel hfuel
  · refine ⟨0, fun fuel _ => ?_⟩
    rcases qGammaOf_eq_or_loop hQ hS fuel p mode with h | ⟨h, -⟩
    · exact h
    · exact absurd h hnz

/-- **On the exact class the result is correctly rounded at every fuel.** -/
theorem qGammaOf_exact (hQ : QBaseSpec Q qv) (hS : QArgSpec S xv) (hE : QExact Q S)
    (fuel p : ℕ) [NeZero p] (mode : RoundingMode) :
    qGammaOf Q S fuel p mode = roundVal p mode (Spec.qGammaAt qv (xv : EReal)) := by
  have hp := NeZero.ne p
  have hk := hS.kind
  unfold QExact at hE
  unfold qGammaOf
  cases hkind : S.kind with
  | zero =>
    rw [hkind] at hk
    have : xv = 0 := hk
    dsimp only
    rw [this, Spec.qGammaAt_zero, roundVal_top]
  | pole =>
    rw [hkind] at hk
    obtain ⟨m, hm⟩ := hk
    dsimp only
    rw [hm, Spec.qGammaAt_pole, roundVal_none]
  | posInt n =>
    rw [hkind] at hk hE
    obtain ⟨hn1, hxn⟩ := hk
    have hnz : ∀ m : ℕ, xv ≠ -m := fun m h => by
      have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      have h2 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      rw [hxn] at h
      linarith
    dsimp only
    rw [ite_eq_right hp]
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (qGammaExact?_isSome_mono hE p)
    rw [hr]
    dsimp only
    rw [ofAzRatRound_eq_roundVal, Spec.qGammaAt_coe qv hnz, qGammaExact?_spec hQ hn1 hr, hxn]
  | general =>
    rw [hkind] at hE
    exact hE.elim

/-- On the exact class at a dyadic base the real values are dyadic. -/
theorem isDyadic_of_qExact (hQ : QBaseSpec Q qv) (hS : QArgSpec S xv) (hE : QExact Q S)
    (hd : IsDyadic qv) {v : ℝ} (hv : Spec.qGammaAt qv (xv : EReal) = some (v : EReal)) :
    IsDyadic v := by
  have hk := hS.kind
  unfold QExact at hE
  cases hkind : S.kind with
  | zero =>
    rw [hkind] at hk
    have : xv = 0 := hk
    rw [this, Spec.qGammaAt_zero] at hv
    exact absurd hv (by simp)
  | pole =>
    rw [hkind] at hk
    obtain ⟨m, hm⟩ := hk
    rw [hm, Spec.qGammaAt_pole] at hv
    exact absurd hv (by simp)
  | posInt n =>
    rw [hkind] at hk
    obtain ⟨hn1, hxn⟩ := hk
    have hnz : ∀ m : ℕ, xv ≠ -m := fun m h => by
      have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      have h2 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      rw [hxn] at h
      linarith
    rw [Spec.qGammaAt_coe qv hnz, Option.some.injEq, EReal.coe_eq_coe_iff] at hv
    have hG := qGammaReal_nat hQ.pos hQ.ne_one (n - 1)
    have hcast : (((n - 1 : ℕ) : ℝ) + 1) = (n : ℝ) := by
      rw [Nat.cast_sub hn1]
      push_cast
      ring
    rw [hcast, ← hxn, hv] at hG
    rw [hG]
    exact isDyadic_qFactorial hd _
  | general =>
    rw [hkind] at hE
    exact hE.elim

/-- **The specification of a function that is `Γ_q` on its real class `R`**, exact on the
trivial class `T`, and sound and complete elsewhere (the base `1`). -/
theorem qGamma_zivSpec_of {α : Type*} {val : α → Option EReal}
    {f : ℕ → α → ℕ → RoundingMode → AzFloat × Ordering} (R T : α → Prop) (Q : α → QBase)
    (S : α → QArg) (qr xr : α → ℝ) (hQ : ∀ a, R a → QBaseSpec (Q a) (qr a))
    (hS : ∀ a, R a → QArgSpec (S a) (xr a))
    (hval : ∀ a, R a → val a = Spec.qGammaAt (qr a) ((xr a : ℝ) : EReal))
    (hf : ∀ fuel a p mode, R a → f fuel a p mode = qGammaOf (Q a) (S a) fuel p mode)
    (hsound : ∀ fuel a (p : ℕ) [NeZero p] mode, ¬ R a →
      f fuel a p mode = roundVal p mode (val a) ∨ f fuel a p mode = (nan, .eq))
    (hcomp : ∀ a (p : ℕ) [NeZero p] mode, ¬ R a →
      (∀ v : ℝ, val a = some (v : EReal) → ((v : ℝ) : EReal) ∉ floatSet (p + 1)) →
      ∃ F : ℕ, ∀ fuel, F ≤ fuel → f fuel a p mode = roundVal p mode (val a))
    (hT : ∀ a, T a → (∀ v : ℝ, val a ≠ some (v : EReal)) ∧
      ∀ fuel (p : ℕ) [NeZero p] mode, f fuel a p mode = roundVal p mode (val a)) :
    ZivSpec val f {a | T a ∨ (R a ∧ QExact (Q a) (S a) ∧ IsDyadic (qr a))} ∅ := by
  refine ⟨fun fuel a p _ mode => ?_, fun a p _ mode hB => ?_, fun a ha v hv => ?_,
    fun a ha => absurd ha (Set.notMem_empty _), fun a ha fuel p _ mode => ?_⟩
  · by_cases hR : R a
    · rw [hf fuel a p mode hR, hval a hR]
      exact qGammaOf_main (hQ a hR) (hS a hR) fuel p mode
    · exact hsound fuel a p mode hR
  · by_cases hR : R a
    · rw [hval a hR] at hB ⊢
      obtain ⟨F, hF⟩ := qGammaOf_complete (hQ a hR) (hS a hR) p mode hB
      exact ⟨F, fun fuel hfuel => by rw [hf fuel a p mode hR]; exact hF fuel hfuel⟩
    · exact hcomp a p mode hR hB
  · rcases ha with hTa | ⟨hR, hE, hd⟩
    · exact absurd hv ((hT a hTa).1 v)
    · rw [hval a hR] at hv
      exact isDyadic_of_qExact (hQ a hR) (hS a hR) hE hd hv
  · rcases ha with (hTa | ⟨hR, hE, -⟩) | hN
    · exact (hT a hTa).2 fuel p mode
    · rw [hf fuel a p mode hR, hval a hR]
      exact qGammaOf_exact (hQ a hR) (hS a hR) hE fuel p mode
    · exact absurd hN (Set.notMem_empty _)

/-! ### Bases and arguments with values in the extended reals -/

/-- The real class: a base `q > 0`, `q ≠ 1`, and a real argument. -/
def QReal {α : Type*} (qe xe : α → Option EReal) (a : α) : Prop :=
  ∃ qv xv : ℝ, qe a = some (qv : EReal) ∧ 0 < qv ∧ qv ≠ 1 ∧ xe a = some (xv : EReal)

/-- The trivial class: a base that is no positive real, or a base `q > 0`, `q ≠ 1`, with an
argument that is no real. -/
def QTrivial {α : Type*} (qe xe : α → Option EReal) (a : α) : Prop :=
  (∀ qv : ℝ, qe a = some (qv : EReal) → qv ≤ 0) ∨
    ((∃ qv : ℝ, qe a = some (qv : EReal) ∧ 0 < qv ∧ qv ≠ 1) ∧
      ∀ xv : ℝ, xe a ≠ some (xv : EReal))

theorem bind_const_none {β γ : Type*} (o : Option β) :
    (o.bind fun _ => (none : Option γ)) = none := by
  cases o <;> rfl

open Classical in
/-- **The specification of a function that is `Γ_q`** on a base and an argument with values
`qe`, `xe` in the extended reals: `NaN` on a base that is no positive real, the function `fΓ`
(a function that is `Γ`) at the base `1`, the special values at an argument that is no real,
and `qGammaOf` elsewhere. -/
theorem qGamma_zivSpec_sides {α : Type*} {qe xe : α → Option EReal}
    {f fΓ : ℕ → α → ℕ → RoundingMode → AzFloat × Ordering} (Q : α → QBase) (S : α → QArg)
    (hbase : ∀ a (qv : ℝ), qe a = some (qv : EReal) → 0 < qv → qv ≠ 1 → QBaseSpec (Q a) qv)
    (harg : ∀ a (xv : ℝ), xe a = some (xv : EReal) → QArgSpec (S a) xv)
    (hΓs : ∀ fuel a (p : ℕ) [NeZero p] mode,
      fΓ fuel a p mode = roundVal p mode ((xe a).bind Spec.gamma) ∨
        fΓ fuel a p mode = (nan, .eq))
    (hΓc : ∀ a (p : ℕ) [NeZero p] mode,
      (∀ v : ℝ, (xe a).bind Spec.gamma = some (v : EReal) →
        ((v : ℝ) : EReal) ∉ floatSet (p + 1)) →
      ∃ F : ℕ, ∀ fuel, F ≤ fuel →
        fΓ fuel a p mode = roundVal p mode ((xe a).bind Spec.gamma))
    (hf_bad : ∀ fuel a p mode, (∀ qv : ℝ, qe a = some (qv : EReal) → qv ≤ 0) →
      f fuel a p mode = (nan, .eq))
    (hf_one : ∀ fuel a p mode, qe a = some ((1 : ℝ) : EReal) →
      f fuel a p mode = fΓ fuel a p mode)
    (hf_real : ∀ fuel a p mode (qv xv : ℝ), qe a = some (qv : EReal) → 0 < qv → qv ≠ 1 →
      xe a = some (xv : EReal) → f fuel a p mode = qGammaOf (Q a) (S a) fuel p mode)
    (hf_nonreal : ∀ fuel a p mode (qv : ℝ), qe a = some (qv : EReal) → 0 < qv → qv ≠ 1 →
      (∀ xv : ℝ, xe a ≠ some (xv : EReal)) →
      f fuel a p mode = if xe a = some ⊤ then (infinity true, .eq) else (nan, .eq)) :
    ZivSpec (fun a => (qe a).bind fun q => (xe a).bind fun x => Spec.qGamma q x) f
      {a | QTrivial qe xe a ∨ (QReal qe xe a ∧ QExact (Q a) (S a) ∧
        IsDyadic ((qe a).getD 0).toReal)} ∅ := by
  -- the value on a bad base
  have hval_bad : ∀ a, (∀ qv : ℝ, qe a = some (qv : EReal) → qv ≤ 0) →
      ((qe a).bind fun q => (xe a).bind fun x => Spec.qGamma q x) = none := by
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
      simp only [Spec.qGamma_none hn]
      exact bind_const_none _
  -- the value at the base `1`
  have hval_one : ∀ a, qe a = some ((1 : ℝ) : EReal) →
      ((qe a).bind fun q => (xe a).bind fun x => Spec.qGamma q x)
        = (xe a).bind Spec.gamma := by
    intro a hq
    rw [hq, Option.bind_some]
    congr 1
    funext x
    rw [EReal.coe_one, Spec.qGamma_one]
  -- the trivial class
  have htriv : ∀ a, QTrivial qe xe a →
      (∀ v : ℝ, ((qe a).bind fun q => (xe a).bind fun x => Spec.qGamma q x)
        ≠ some (v : EReal)) ∧
      ∀ fuel (p : ℕ) [NeZero p] mode, f fuel a p mode
        = roundVal p mode ((qe a).bind fun q => (xe a).bind fun x => Spec.qGamma q x) := by
    intro a hT
    rcases hT with hb | ⟨⟨qv, hq, h0, h1⟩, hx⟩
    · rw [hval_bad a hb]
      exact ⟨fun v h => by simp at h, fun fuel p _ mode => by
        rw [hf_bad fuel a p mode hb, roundVal_none]⟩
    · have hv : ((qe a).bind fun q => (xe a).bind fun x => Spec.qGamma q x)
          = if xe a = some ⊤ then some ⊤ else none := by
        rw [hq, Option.bind_some]
        cases hxe : xe a with
        | none => simp
        | some e =>
          rw [Option.bind_some, Spec.qGamma_coe h0 h1]
          induction e using EReal.rec with
          | bot => rw [Spec.qGammaAt_bot]; simp
          | top => rw [Spec.qGammaAt_top]; simp
          | coe r => exact absurd hxe (hx r)
      rw [hv]
      refine ⟨fun v h => ?_, fun fuel p _ mode => ?_⟩
      · split_ifs at h
        simp at h
      · rw [hf_nonreal fuel a p mode qv hq h0 h1 hx]
        split_ifs
        · rw [roundVal_top]
        · rw [roundVal_none]
  -- the classes of a base
  have hcases : ∀ a, (∃ qv : ℝ, qe a = some (qv : EReal) ∧ 0 < qv ∧ qv ≠ 1) ∨
      qe a = some ((1 : ℝ) : EReal) ∨ ∀ qv : ℝ, qe a = some (qv : EReal) → qv ≤ 0 := by
    intro a
    by_cases hb : ∀ qv : ℝ, qe a = some (qv : EReal) → qv ≤ 0
    · exact Or.inr (Or.inr hb)
    · push Not at hb
      obtain ⟨qv, hq, h0⟩ := hb
      by_cases h1 : qv = 1
      · exact Or.inr (Or.inl (h1 ▸ hq))
      · exact Or.inl ⟨qv, hq, h0, h1⟩
  have hnotR : ∀ a, ¬ QReal qe xe a → qe a = some ((1 : ℝ) : EReal) ∨ QTrivial qe xe a := by
    intro a hR
    rcases hcases a with ⟨qv, hq, h0, h1⟩ | h | h
    · refine Or.inr (Or.inr ⟨⟨qv, hq, h0, h1⟩, fun xv hx => hR ⟨qv, xv, hq, h0, h1, hx⟩⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have hqr : ∀ a (qv : ℝ), qe a = some (qv : EReal) → ((qe a).getD 0).toReal = qv :=
    fun a qv hq => by rw [hq, Option.getD_some, EReal.toReal_coe]
  have hxr : ∀ a (xv : ℝ), xe a = some (xv : EReal) → ((xe a).getD 0).toReal = xv :=
    fun a xv hx => by rw [hx, Option.getD_some, EReal.toReal_coe]
  refine qGamma_zivSpec_of (QReal qe xe) (QTrivial qe xe) Q S
    (fun a => ((qe a).getD 0).toReal) (fun a => ((xe a).getD 0).toReal) ?_ ?_ ?_ ?_ ?_ ?_ htriv
  · rintro a ⟨qv, xv, hq, h0, h1, hx⟩
    rw [hqr a qv hq]
    exact hbase a qv hq h0 h1
  · rintro a ⟨qv, xv, hq, h0, h1, hx⟩
    rw [hxr a xv hx]
    exact harg a xv hx
  · rintro a ⟨qv, xv, hq, h0, h1, hx⟩
    rw [hqr a qv hq, hxr a xv hx, hq, hx, Option.bind_some, Option.bind_some,
      Spec.qGamma_coe h0 h1]
  · rintro fuel a p mode ⟨qv, xv, hq, h0, h1, hx⟩
    exact hf_real fuel a p mode qv xv hq h0 h1 hx
  · intro fuel a p _ mode hR
    rcases hnotR a hR with h1 | hT
    · rw [hf_one fuel a p mode h1, hval_one a h1]
      exact hΓs fuel a p mode
    · exact Or.inl ((htriv a hT).2 fuel p mode)
  · intro a p _ mode hR hB
    rcases hnotR a hR with h1 | hT
    · rw [hval_one a h1] at hB ⊢
      obtain ⟨F, hF⟩ := hΓc a p mode hB
      exact ⟨F, fun fuel hfuel => by rw [hf_one fuel a p mode h1]; exact hF fuel hfuel⟩
    · exact ⟨0, fun fuel _ => (htriv a hT).2 fuel p mode⟩

/-! ### Floats and rationals as bases and arguments -/

theorem qBaseFloat_spec {q : AzFloat} {qv : ℝ} (hq : q.toVal = some (qv : EReal))
    (h0 : 0 < qv) (h1 : qv ≠ 1) : QBaseSpec (qBaseFloat q) qv where
  pos := h0
  ne_one := h1
  inv := lt_eq_true_iff toVal_one' hq
  P := fun V hV => by
    have hP : (qBaseFloat q).P = if lt one q = true then
        (fun V => Encl.div V (Encl.exact one) (Encl.exact q)) else fun _ => Encl.exact q := rfl
    have hI : (qBaseFloat q).inv = lt one q := rfl
    rw [hP, hI]
    by_cases hlt : lt one q = true
    · rw [ite_eq_left hlt, ite_eq_left hlt]
      have : NeZero V := ⟨by omega⟩
      have h := LEncl.div (w := V) (half_pow_le_eighth (by omega))
        (LEncl.exact toVal_one' one_pos) (LEncl.exact hq h0)
      simpa [one_div] using h
    · rw [ite_eq_right hlt, ite_eq_right hlt]
      exact (LEncl.exact hq h0).mono (by positivity)
  rat := fun r hr => by
    have hR : (qBaseFloat q).rat = if azIntPos (expOf q) ≤ 131072 ∧
        azIntPos (-(expOf q)) ≤ 131072 then q.toAzRat? else none := rfl
    rw [hR] at hr
    split_ifs at hr
    exact toRat_of_toAzRat? hr hq

theorem qBaseRat_spec (q : AzRat) (h0 : 0 < ((AzRat.toRat q : ℚ) : ℝ))
    (h1 : ((AzRat.toRat q : ℚ) : ℝ) ≠ 1) :
    QBaseSpec (qBaseRat q) ((AzRat.toRat q : ℚ) : ℝ) := by
  have hden := den_pos_real q
  have hs : q.sign = true := by
    by_contra hs
    have hs' : q.sign = false := by simpa using hs
    have h := coe_toRat_eq_sign_mul q
    rw [hs'] at h
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    have hnn : (0 : ℝ) ≤ (q.num.toNat : ℝ) / q.den.toNat := by positivity
    linarith
  have hval : ((AzRat.toRat q : ℚ) : ℝ) = (q.num.toNat : ℝ) / q.den.toNat := by
    rw [coe_toRat_eq_sign_mul, hs]
    simp
  have hinv : lt (ofAzNat q.den) (ofAzNat q.num) = true ↔ 1 < ((AzRat.toRat q : ℚ) : ℝ) := by
    rw [lt_eq_true_iff (toVal_ofAzNat _) (toVal_ofAzNat _), hval, one_lt_div hden]
  have hpow : ∀ V : ℕ, 6 * (1 / 2 : ℝ) ^ (V + 32) ≤ 6 * (1 / 2 : ℝ) ^ V := fun V => by
    have : (1 / 2 : ℝ) ^ (V + 32) ≤ (1 / 2 : ℝ) ^ V :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    linarith
  refine ⟨h0, h1, hinv, fun V _ => ?_, fun r hr => ?_⟩
  · show LEncl (lnGammaRatEncl (if lt (ofAzNat q.den) (ofAzNat q.num) = true then q⁻¹ else q) V)
      (if lt (ofAzNat q.den) (ofAzNat q.num) = true then _ else _) _
    by_cases hlt : lt (ofAzNat q.den) (ofAzNat q.num) = true
    · rw [ite_eq_left hlt, ite_eq_left hlt]
      have hpos : 0 < ((AzRat.toRat q⁻¹ : ℚ) : ℝ) := by
        rw [AzRat.toRat_inv]
        push_cast
        positivity
      have h := lnGammaRatEncl_L q⁻¹ hpos V
      rw [AzRat.toRat_inv] at h
      push_cast at h
      exact h.mono (hpow V)
    · rw [ite_eq_right hlt, ite_eq_right hlt]
      exact (lnGammaRatEncl_L q h0 V).mono (hpow V)
  · have hR : (qBaseRat q).rat = some q := rfl
    rw [hR, Option.some.injEq] at hr
    rw [hr]

theorem qArgKindFloat_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) :
    (qArgKindFloat x).Spec xv := by
  unfold qArgKindFloat
  by_cases hint : isInteger x = true
  · rw [ite_eq_left hint]
    obtain ⟨k, hk⟩ := (isInteger_iff_of_toVal hx).mp hint
    by_cases hpos : lt zero x = true
    · rw [ite_eq_left hpos]
      have hpos' : 0 < xv := (lt_eq_true_iff toVal_zero' hx).mp hpos
      have hk1 : 1 ≤ k := by
        have : (0 : ℝ) < (k : ℝ) := hk ▸ hpos'
        have : 0 < k := by exact_mod_cast this
        omega
      by_cases hb : le x (ofAzNat (AzNat.ofNat 1048576)) = true
      · rw [ite_eq_left hb]
        obtain ⟨ht, -⟩ := truncToAzInt_spec hx
        have hkt : (truncToAzInt x).toInt = k := by
          rw [hk, ← Int.cast_sub, ← Int.cast_abs] at ht
          have : |(truncToAzInt x).toInt - k| < 1 := by exact_mod_cast ht
          have := abs_lt.mp this
          omega
        obtain ⟨n, hn⟩ : ∃ n : ℕ, n = (truncToAzInt x).abs.toNat := ⟨_, rfl⟩
        have hnk : (n : ℤ) = k := by rw [hn, AzInt.abs_toNat_eq, hkt, abs_of_pos (by omega)]
        have hxn : xv = (n : ℕ) := by rw [hk]; exact_mod_cast hnk.symm
        rw [← hn]
        exact ⟨by omega, hxn⟩
      · rw [ite_eq_right hb]
        intro m h
        have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        linarith
    · rw [ite_eq_right hpos]
      have hle : xv ≤ 0 := not_lt.mp (mt (lt_eq_true_iff toVal_zero' hx).mpr hpos)
      by_cases hneg : lt x zero = true
      · rw [ite_eq_left hneg]
        have hneg' : xv < 0 := (lt_eq_true_iff hx toVal_zero').mp hneg
        have hk0 : k ≤ -1 := by
          have : (k : ℝ) < 0 := hk ▸ hneg'
          have : k < 0 := by exact_mod_cast this
          omega
        refine ⟨(-k - 1).toNat, ?_⟩
        have : ((-k - 1).toNat : ℤ) = -k - 1 := Int.toNat_of_nonneg (by omega)
        have h2 : (((-k - 1).toNat : ℤ) : ℝ) = ((-k - 1 : ℤ) : ℝ) := by rw [this]
        push_cast at h2
        rw [hk]
        linarith
      · rw [ite_eq_right hneg]
        have hge : 0 ≤ xv := not_lt.mp (mt (lt_eq_true_iff hx toVal_zero').mpr hneg)
        exact le_antisymm hle hge
  · rw [ite_eq_right hint]
    have hni : ¬ ∃ k : ℤ, xv = k := fun h => hint ((isInteger_iff_of_toVal hx).mpr h)
    exact fun m h => hni ⟨-(m : ℤ), by push_cast; exact h⟩

theorem qArgFloat_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) :
    QArgSpec (qArgFloat x) xv where
  X := ⟨0, fun V _ => AEncl.exact_level hx V⟩
  absX := ⟨0, fun V _ => by
    have hfin := isFinite_of_toVal_coe hx
    have habs := toVal_abs_of_isFinite hfin
    have hfv : fval x = xv := by
      have h := toVal_of_isFinite hfin
      rw [hx, Option.some.injEq, EReal.coe_eq_coe_iff] at h
      exact h.symm
    rw [hfv] at habs
    exact ⟨|xv|, |xv|, habs, habs, abs_nonneg _, le_rfl, le_rfl, by simp⟩⟩
  kind := qArgKindFloat_spec hx

theorem qArgKindRat_spec (x : AzRat) : (qArgKindRat x).Spec ((AzRat.toRat x : ℚ) : ℝ) := by
  unfold qArgKindRat
  by_cases hd : x.den = 1
  · rw [ite_eq_left hd]
    have hv := coe_toRat_eq_mkNorm_of_den_one x hd
    rw [AzNat.toInt_mkNorm] at hv
    by_cases hz : x.num = 0
    · rw [ite_eq_left hz]
      show _ = (0 : ℝ)
      rw [hv, hz, AzNat.toNat_zero]
      simp
    · rw [ite_eq_right hz]
      have hn0 : x.num.toNat ≠ 0 := fun h =>
        hz (AzNat.toNat_injective (by rw [h, AzNat.toNat_zero]))
      by_cases hs : x.sign = false
      · rw [ite_eq_left hs]
        refine ⟨x.num.toNat - 1, ?_⟩
        have h1 : 1 ≤ x.num.toNat := by omega
        rw [hv, hs, Nat.cast_sub h1]
        simp
      · rw [ite_eq_right hs]
        have hs' : x.sign = true := by simpa using hs
        have e : ((AzRat.toRat x : ℚ) : ℝ) = ((x.num.toNat : ℕ) : ℝ) := by
          rw [hv, hs']
          simp
        by_cases hb : le (ofAzNat x.num) (ofAzNat (AzNat.ofNat 1048576)) = true
        · rw [ite_eq_left hb]
          exact ⟨by omega, e⟩
        · rw [ite_eq_right hb]
          intro m h
          rw [e] at h
          have h1 : (0 : ℝ) < ((x.num.toNat : ℕ) : ℝ) := by
            exact_mod_cast Nat.pos_of_ne_zero hn0
          have h2 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
          linarith
  · rw [ite_eq_right hd]
    have hni := not_exists_int_of_den_ne_one x hd
    exact fun m h => hni ⟨-(m : ℤ), by push_cast; exact h⟩

theorem qArgRat_spec (x : AzRat) : QArgSpec (qArgRat x) ((AzRat.toRat x : ℚ) : ℝ) where
  X := ⟨4 * |((AzRat.toRat x : ℚ) : ℝ)|, fun V _ => lnGammaRatEncl_level x V⟩
  absX := ⟨4 * |((AzRat.toRat x : ℚ) : ℝ)|, fun V hV => by
    have h := lnGammaRatEncl_level x.abs V
    rw [AzRat.toRat_abs] at h
    push_cast at h
    rw [abs_abs] at h
    obtain ⟨l, u, hl, hu, h1, h2, h3⟩ := h
    have hu8 : (1 / 2 : ℝ) ^ V ≤ 1 / 8 := half_pow_le_eighth (by omega)
    refine ⟨l, u, hl, hu, ?_, h1, h2, h3⟩
    nlinarith [abs_nonneg ((AzRat.toRat x : ℚ) : ℝ)]⟩
  kind := qArgKindRat_spec x

/-! ### The bases -/

theorem qFloatBase_bad {q : AzFloat} (hb : ∀ qv : ℝ, q.toVal = some (qv : EReal) → qv ≤ 0) :
    (q.isFinite && lt zero q) = false := by
  by_contra h
  rw [Bool.not_eq_false, Bool.and_eq_true] at h
  obtain ⟨hf, hl⟩ := h
  have hv := toVal_of_isFinite hf
  have := (lt_eq_true_iff toVal_zero' hv).mp hl
  linarith [hb _ hv]

theorem qFloatBase_pos {q : AzFloat} {qv : ℝ} (hq : q.toVal = some (qv : EReal))
    (h0 : 0 < qv) : (q.isFinite && lt zero q) = true := by
  rw [Bool.and_eq_true]
  exact ⟨isFinite_of_toVal_coe hq, (lt_eq_true_iff toVal_zero' hq).mpr h0⟩

theorem qFloatBase_one_iff {q : AzFloat} {qv : ℝ} (hq : q.toVal = some (qv : EReal)) :
    (le q one && le one q) = true ↔ qv = 1 := by
  rw [Bool.and_eq_true, le_eq_true_iff hq toVal_one', le_eq_true_iff toVal_one' hq]
  constructor
  · rintro ⟨a, b⟩
    exact le_antisymm a b
  · rintro rfl
    exact ⟨le_rfl, le_rfl⟩

theorem qRatBase_pos_iff (q : AzRat) :
    (q.sign = true ∧ q.num ≠ 0) ↔ 0 < ((AzRat.toRat q : ℚ) : ℝ) := by
  constructor
  · rintro ⟨hs, h0⟩
    exact_mod_cast toRat_pos_of_sign q hs h0
  · intro hpos
    have hden := den_pos_real q
    have h := coe_toRat_eq_sign_mul q
    refine ⟨?_, fun h0 => ?_⟩
    · by_contra hs
      have hs' : q.sign = false := by simpa using hs
      rw [hs'] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      have hnn : (0 : ℝ) ≤ (q.num.toNat : ℝ) / q.den.toNat := by positivity
      linarith
    · rw [h0, AzNat.toNat_zero] at h
      simp only [Nat.cast_zero, zero_div, mul_zero] at h
      linarith

theorem qRatBase_one_iff (q : AzRat) (hs : q.sign = true) :
    q.num = q.den ↔ ((AzRat.toRat q : ℚ) : ℝ) = 1 := by
  have h := coe_toRat_eq_one_iff q
  rw [← EReal.coe_one, EReal.coe_eq_coe_iff] at h
  rw [h]
  exact ⟨fun h' => ⟨hs, h'⟩, fun h' => h'.2⟩

/-! ### The four specifications -/

/-- **The specification of `Γ_q(x)` for floats** (`ZivSpec`): sound at every fuel; complete in
the limit of the fuel wherever the value is no rounding boundary; and correct at every fuel on
the trivial class (a base that is no positive real, or an argument that is no real) and on
the exact class (`0`, the poles, the positive integers whose value is formed). -/
theorem qGammaPrecRoundFuel_zivSpec :
    ZivSpec
      (fun a : AzFloat × AzFloat =>
        a.1.toVal.bind fun q => a.2.toVal.bind fun x => Spec.qGamma q x)
      (fun fuel a p mode => qGammaPrecRoundFuel fuel a.1 a.2 p mode)
      {a | QTrivial (fun a : AzFloat × AzFloat => a.1.toVal) (fun a => a.2.toVal) a ∨
        (QReal (fun a : AzFloat × AzFloat => a.1.toVal) (fun a => a.2.toVal) a ∧
          QExact (qBaseFloat a.1) (qArgFloat a.2))} ∅ := by
  have h := qGamma_zivSpec_sides (α := AzFloat × AzFloat) (qe := fun a => a.1.toVal)
    (xe := fun a => a.2.toVal)
    (f := fun fuel a p mode => qGammaPrecRoundFuel fuel a.1 a.2 p mode)
    (fΓ := fun fuel a p mode => gammaPrecRoundFuel fuel a.2 p mode)
    (fun a => qBaseFloat a.1) (fun a => qArgFloat a.2)
    (fun a qv hq h0 h1 => qBaseFloat_spec hq h0 h1) (fun a xv hx => qArgFloat_spec hx)
    (fun fuel a p _ mode => gammaPrecRoundFuel_zivSpec.sound fuel a.2 p mode)
    (fun a p _ mode hB => gammaPrecRoundFuel_zivSpec.complete a.2 p mode hB)
    (fun fuel a p mode hb => by
      show qGammaPrecRoundFuel fuel a.1 a.2 p mode = _
      unfold qGammaPrecRoundFuel
      rw [qFloatBase_bad hb]
      rfl)
    (fun fuel a p mode hq => by
      show qGammaPrecRoundFuel fuel a.1 a.2 p mode = _
      unfold qGammaPrecRoundFuel
      rw [qFloatBase_pos hq one_pos, (qFloatBase_one_iff hq).mpr rfl]
      rfl)
    (fun fuel a p mode qv xv hq h0 h1 hx => by
      obtain ⟨q, x⟩ := a
      have hne : (le q one && le one q) = false := by
        rw [← Bool.not_eq_true]
        exact mt (qFloatBase_one_iff hq).mp h1
      show qGammaPrecRoundFuel fuel q x p mode = _
      unfold qGammaPrecRoundFuel
      rw [qFloatBase_pos hq h0, hne]
      cases x with
      | nan => simp at hx
      | infinity s => cases s <;> simp at hx
      | zero => rfl
      | finite s e pr m hv => rfl)
    (fun fuel a p mode qv hq h0 h1 hx => by
      obtain ⟨q, x⟩ := a
      have hne : (le q one && le one q) = false := by
        rw [← Bool.not_eq_true]
        exact mt (qFloatBase_one_iff hq).mp h1
      show qGammaPrecRoundFuel fuel q x p mode = _
      unfold qGammaPrecRoundFuel
      rw [qFloatBase_pos hq h0, hne]
      cases x with
      | nan => simp
      | infinity s => cases s <;> simp
      | zero => exact absurd toVal_zero' (hx 0)
      | finite s e pr m hv => exact absurd (toVal_finite s e pr m hv) (hx _))
  refine h.mono ?_ (Set.Subset.refl _)
  rintro a (hT | ⟨hR, hE⟩)
  · exact Or.inl hT
  · refine Or.inr ⟨hR, hE, ?_⟩
    obtain ⟨qv, xv, hq, -⟩ := hR
    have hq' : a.1.toVal = some (qv : EReal) := hq
    show IsDyadic ((a.1.toVal.getD 0).toReal)
    rw [hq', Option.getD_some, EReal.toReal_coe]
    exact isDyadic_of_toVal hq'

/-- **The specification of `Γ_q(x)` for a float `q` and a rational `x`.** -/
theorem qGammaFloatRatPrecRoundFuel_zivSpec :
    ZivSpec
      (fun a : AzFloat × AzRat =>
        a.1.toVal.bind fun q => Spec.qGamma q (((AzRat.toRat a.2 : ℚ) : ℝ) : EReal))
      (fun fuel a p mode => qGammaFloatRatPrecRoundFuel fuel a.1 a.2 p mode)
      {a | QTrivial (fun a : AzFloat × AzRat => a.1.toVal)
          (fun a => some (((AzRat.toRat a.2 : ℚ) : ℝ) : EReal)) a ∨
        (QReal (fun a : AzFloat × AzRat => a.1.toVal)
          (fun a => some (((AzRat.toRat a.2 : ℚ) : ℝ) : EReal)) a ∧
          QExact (qBaseFloat a.1) (qArgRat a.2))} ∅ := by
  have h := qGamma_zivSpec_sides (α := AzFloat × AzRat) (qe := fun a => a.1.toVal)
    (xe := fun a => some (((AzRat.toRat a.2 : ℚ) : ℝ) : EReal))
    (f := fun fuel a p mode => qGammaFloatRatPrecRoundFuel fuel a.1 a.2 p mode)
    (fΓ := fun fuel a p mode => gammaRatPrecRoundFuel fuel a.2 p mode)
    (fun a => qBaseFloat a.1) (fun a => qArgRat a.2)
    (fun a qv hq h0 h1 => qBaseFloat_spec hq h0 h1)
    (fun a xv hx => by
      rw [Option.some.injEq, EReal.coe_eq_coe_iff] at hx
      rw [← hx]
      exact qArgRat_spec a.2)
    (fun fuel a p _ mode => gammaRatPrecRoundFuel_zivSpec.sound fuel a.2 p mode)
    (fun a p _ mode hB => gammaRatPrecRoundFuel_zivSpec.complete a.2 p mode hB)
    (fun fuel a p mode hb => by
      show qGammaFloatRatPrecRoundFuel fuel a.1 a.2 p mode = _
      unfold qGammaFloatRatPrecRoundFuel
      rw [qFloatBase_bad hb]
      rfl)
    (fun fuel a p mode hq => by
      show qGammaFloatRatPrecRoundFuel fuel a.1 a.2 p mode = _
      unfold qGammaFloatRatPrecRoundFuel
      rw [qFloatBase_pos hq one_pos, (qFloatBase_one_iff hq).mpr rfl]
      rfl)
    (fun fuel a p mode qv xv hq h0 h1 hx => by
      have hne : (le a.1 one && le one a.1) = false := by
        rw [← Bool.not_eq_true]
        exact mt (qFloatBase_one_iff hq).mp h1
      show qGammaFloatRatPrecRoundFuel fuel a.1 a.2 p mode = _
      unfold qGammaFloatRatPrecRoundFuel
      rw [qFloatBase_pos hq h0, hne]
      rfl)
    (fun fuel a p mode qv hq h0 h1 hx => absurd rfl (hx _))
  refine h.mono ?_ (Set.Subset.refl _)
  rintro a (hT | ⟨hR, hE⟩)
  · exact Or.inl hT
  · refine Or.inr ⟨hR, hE, ?_⟩
    obtain ⟨qv, xv, hq, -⟩ := hR
    have hq' : a.1.toVal = some (qv : EReal) := hq
    show IsDyadic ((a.1.toVal.getD 0).toReal)
    rw [hq', Option.getD_some, EReal.toReal_coe]
    exact isDyadic_of_toVal hq'

/-- **The specification of `Γ_q(x)` for a rational `q` and a float `x`.**  The exact class
enters with a dyadic base; at every rational base it is correct at every fuel by
`qGammaOf_exact`. -/
theorem qGammaRatFloatPrecRoundFuel_zivSpec :
    ZivSpec
      (fun a : AzRat × AzFloat =>
        a.2.toVal.bind fun x => Spec.qGamma (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal) x)
      (fun fuel a p mode => qGammaRatFloatPrecRoundFuel fuel a.1 a.2 p mode)
      {a | QTrivial (fun a : AzRat × AzFloat => some (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal))
          (fun a => a.2.toVal) a ∨
        (QReal (fun a : AzRat × AzFloat => some (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal))
          (fun a => a.2.toVal) a ∧ QExact (qBaseRat a.1) (qArgFloat a.2) ∧
          IsDyadic ((AzRat.toRat a.1 : ℚ) : ℝ))} ∅ := by
  have hposof : ∀ (q : AzRat) (qv : ℝ),
      some (((AzRat.toRat q : ℚ) : ℝ) : EReal) = some (qv : EReal) →
      ((AzRat.toRat q : ℚ) : ℝ) = qv := fun q qv h => by
    rwa [Option.some.injEq, EReal.coe_eq_coe_iff] at h
  have h := qGamma_zivSpec_sides (α := AzRat × AzFloat)
    (qe := fun a => some (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal)) (xe := fun a => a.2.toVal)
    (f := fun fuel a p mode => qGammaRatFloatPrecRoundFuel fuel a.1 a.2 p mode)
    (fΓ := fun fuel a p mode => gammaPrecRoundFuel fuel a.2 p mode)
    (fun a => qBaseRat a.1) (fun a => qArgFloat a.2)
    (fun a qv hq h0 h1 => by
      have e := hposof a.1 qv hq
      rw [← e] at h0 h1 ⊢
      exact qBaseRat_spec a.1 h0 h1)
    (fun a xv hx => qArgFloat_spec hx)
    (fun fuel a p _ mode => gammaPrecRoundFuel_zivSpec.sound fuel a.2 p mode)
    (fun a p _ mode hB => gammaPrecRoundFuel_zivSpec.complete a.2 p mode hB)
    (fun fuel a p mode hb => by
      have hle := hb _ rfl
      show qGammaRatFloatPrecRoundFuel fuel a.1 a.2 p mode = _
      unfold qGammaRatFloatPrecRoundFuel
      rw [ite_eq_right (fun hc => by linarith [(qRatBase_pos_iff a.1).mp hc])])
    (fun fuel a p mode hq => by
      have e := hposof a.1 1 hq
      have hpos := (qRatBase_pos_iff a.1).mpr (by rw [e]; exact one_pos)
      show qGammaRatFloatPrecRoundFuel fuel a.1 a.2 p mode = _
      unfold qGammaRatFloatPrecRoundFuel
      rw [ite_eq_left hpos, ite_eq_left ((qRatBase_one_iff a.1 hpos.1).mpr e)])
    (fun fuel a p mode qv xv hq h0 h1 hx => by
      obtain ⟨q, x⟩ := a
      have e := hposof q qv hq
      have hpos := (qRatBase_pos_iff q).mpr (by rw [e]; exact h0)
      have hne : ¬ q.num = q.den := fun hc => h1 (e ▸ (qRatBase_one_iff q hpos.1).mp hc)
      show qGammaRatFloatPrecRoundFuel fuel q x p mode = _
      unfold qGammaRatFloatPrecRoundFuel
      rw [ite_eq_left hpos, ite_eq_right hne]
      cases x with
      | nan => simp at hx
      | infinity s => cases s <;> simp at hx
      | zero => rfl
      | finite s e pr m hv => rfl)
    (fun fuel a p mode qv hq h0 h1 hx => by
      obtain ⟨q, x⟩ := a
      have e := hposof q qv hq
      have hpos := (qRatBase_pos_iff q).mpr (by rw [e]; exact h0)
      have hne : ¬ q.num = q.den := fun hc => h1 (e ▸ (qRatBase_one_iff q hpos.1).mp hc)
      show qGammaRatFloatPrecRoundFuel fuel q x p mode = _
      unfold qGammaRatFloatPrecRoundFuel
      rw [ite_eq_left hpos, ite_eq_right hne]
      cases x with
      | nan => simp
      | infinity s => cases s <;> simp
      | zero => exact absurd toVal_zero' (hx 0)
      | finite s e pr m hv => exact absurd (toVal_finite s e pr m hv) (hx _))
  exact h

/-- **The specification of `Γ_q(x)` for rationals `q` and `x`.**  The exact class enters with
a dyadic base; at every rational base it is correct at every fuel by `qGammaOf_exact`. -/
theorem qGammaRatPrecRoundFuel_zivSpec :
    ZivSpec
      (fun a : AzRat × AzRat => Spec.qGamma (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal)
        (((AzRat.toRat a.2 : ℚ) : ℝ) : EReal))
      (fun fuel a p mode => qGammaRatPrecRoundFuel fuel a.1 a.2 p mode)
      {a | QTrivial (fun a : AzRat × AzRat => some (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal))
          (fun a => some (((AzRat.toRat a.2 : ℚ) : ℝ) : EReal)) a ∨
        (QReal (fun a : AzRat × AzRat => some (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal))
          (fun a => some (((AzRat.toRat a.2 : ℚ) : ℝ) : EReal)) a ∧
          QExact (qBaseRat a.1) (qArgRat a.2) ∧ IsDyadic ((AzRat.toRat a.1 : ℚ) : ℝ))} ∅ := by
  have hposof : ∀ (q : AzRat) (qv : ℝ),
      some (((AzRat.toRat q : ℚ) : ℝ) : EReal) = some (qv : EReal) →
      ((AzRat.toRat q : ℚ) : ℝ) = qv := fun q qv h => by
    rwa [Option.some.injEq, EReal.coe_eq_coe_iff] at h
  have h := qGamma_zivSpec_sides (α := AzRat × AzRat)
    (qe := fun a => some (((AzRat.toRat a.1 : ℚ) : ℝ) : EReal))
    (xe := fun a => some (((AzRat.toRat a.2 : ℚ) : ℝ) : EReal))
    (f := fun fuel a p mode => qGammaRatPrecRoundFuel fuel a.1 a.2 p mode)
    (fΓ := fun fuel a p mode => gammaRatPrecRoundFuel fuel a.2 p mode)
    (fun a => qBaseRat a.1) (fun a => qArgRat a.2)
    (fun a qv hq h0 h1 => by
      have e := hposof a.1 qv hq
      rw [← e] at h0 h1 ⊢
      exact qBaseRat_spec a.1 h0 h1)
    (fun a xv hx => by
      rw [Option.some.injEq, EReal.coe_eq_coe_iff] at hx
      rw [← hx]
      exact qArgRat_spec a.2)
    (fun fuel a p _ mode => gammaRatPrecRoundFuel_zivSpec.sound fuel a.2 p mode)
    (fun a p _ mode hB => gammaRatPrecRoundFuel_zivSpec.complete a.2 p mode hB)
    (fun fuel a p mode hb => by
      have hle := hb _ rfl
      show qGammaRatPrecRoundFuel fuel a.1 a.2 p mode = _
      unfold qGammaRatPrecRoundFuel
      rw [ite_eq_right (fun hc => by linarith [(qRatBase_pos_iff a.1).mp hc])])
    (fun fuel a p mode hq => by
      have e := hposof a.1 1 hq
      have hpos := (qRatBase_pos_iff a.1).mpr (by rw [e]; exact one_pos)
      show qGammaRatPrecRoundFuel fuel a.1 a.2 p mode = _
      unfold qGammaRatPrecRoundFuel
      rw [ite_eq_left hpos, ite_eq_left ((qRatBase_one_iff a.1 hpos.1).mpr e)])
    (fun fuel a p mode qv xv hq h0 h1 hx => by
      have e := hposof a.1 qv hq
      have hpos := (qRatBase_pos_iff a.1).mpr (by rw [e]; exact h0)
      have hne : ¬ a.1.num = a.1.den := fun hc => h1 (e ▸ (qRatBase_one_iff a.1 hpos.1).mp hc)
      show qGammaRatPrecRoundFuel fuel a.1 a.2 p mode = _
      unfold qGammaRatPrecRoundFuel
      rw [ite_eq_left hpos, ite_eq_right hne])
    (fun fuel a p mode qv hq h0 h1 hx => absurd rfl (hx _))
  exact h

/-! ### At the default fuel -/

/-- **`Γ_q(x)` for floats is correctly rounded, or the fuel ran out.** -/
theorem qGammaPrecRound_eq_or (q x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    qGammaPrecRound q x p mode
        = roundVal p mode (q.toVal.bind fun qe => x.toVal.bind fun xe => Spec.qGamma qe xe) ∨
      qGammaPrecRound q x p mode = (nan, .eq) :=
  qGammaPrecRoundFuel_zivSpec.sound (qGammaFuel (lt x zero) p) (q, x) p mode

theorem qGammaFloatRatPrecRound_eq_or (q : AzFloat) (x : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    qGammaFloatRatPrecRound q x p mode = roundVal p mode
        (q.toVal.bind fun qe => Spec.qGamma qe (((AzRat.toRat x : ℚ) : ℝ) : EReal)) ∨
      qGammaFloatRatPrecRound q x p mode = (nan, .eq) :=
  qGammaFloatRatPrecRoundFuel_zivSpec.sound (qGammaFuel (!x.sign) p) (q, x) p mode

theorem qGammaRatFloatPrecRound_eq_or (q : AzRat) (x : AzFloat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    qGammaRatFloatPrecRound q x p mode = roundVal p mode
        (x.toVal.bind fun xe => Spec.qGamma (((AzRat.toRat q : ℚ) : ℝ) : EReal) xe) ∨
      qGammaRatFloatPrecRound q x p mode = (nan, .eq) :=
  qGammaRatFloatPrecRoundFuel_zivSpec.sound (qGammaFuel (lt x zero) p) (q, x) p mode

theorem qGammaRatPrecRound_eq_or (q x : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    qGammaRatPrecRound q x p mode = roundVal p mode
        (Spec.qGamma (((AzRat.toRat q : ℚ) : ℝ) : EReal) (((AzRat.toRat x : ℚ) : ℝ) : EReal)) ∨
      qGammaRatPrecRound q x p mode = (nan, .eq) :=
  qGammaRatPrecRoundFuel_zivSpec.sound (qGammaFuel (!x.sign) p) (q, x) p mode

end Azurite.AzFloat
