/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Div.Newton
import Azurite.AzNat.Equiv.Div.Classic
import Azurite.AzNat.Equiv.Mul.Dispatch
import Azurite.AzNat.Equiv.Add
import Azurite.AzNat.Equiv.Sub
import Azurite.AzNat.Equiv.ShiftLeft
import Azurite.AzNat.Equiv.ShiftRight
import Azurite.AzNat.Equiv.ModPow2
import Azurite.AzNat.Equiv.Pow2
import Azurite.AzNat.Equiv.Compare
import Azurite.AzNat.Equiv.Size
import Azurite.AzNat.Equiv.Mul.SSCached
import Azurite.AzNat.Equiv.Mul.ShortProduct

/-!
# Correctness of Newton–Barrett division

* `newton_step_bounds`: the integer form of MCA Lemma 3.8 — one Newton step on an
  approximate reciprocal of the top `h` limbs gives `A X < β^(2n) < A (X + 2)`, for any base
  `β ≥ 10` (so β = 2^64).  The proof is the integer error analysis directly: with
  `A x + D = β^(n+h)`, the computed `X = x β^ℓ + ⌊x ⌊D/β^ℓ⌋ / β^(2h−ℓ)⌋` satisfies
  `β^(2h) A X ≤ β^(2n+2h) − D²` (upper) and loses less than `A β^(2h) ≥ 5β^(2n) > D² + A x β^ℓ`
  by the two truncations (lower).
* `approxReciprocal_spec`: `A X < β^(2n) < A (X + 2)` for `β^n/2 ≤ A < β^n` (by induction on
  the fuel).
* `barrett_bounds`, `barrettStep_toNat`: MCA Theorem 2.4 with the approximate reciprocal:
  `Q V ≤ A < V (Q + 5)`, so at most four corrections.
* `divModNewton_toNat`: `Q V + R = U` and `R < V`.
-/

namespace Azurite.AzNat

open AzFermat

/-! ### The Newton step (MCA Lemma 3.8, integer form) -/

theorem newton_step_bounds {b n h l A x D Tm Xl : ℕ} (hb : 10 ≤ b) (hn : n = h + l)
    (hlh : l < h) (hA1 : b ^ n ≤ 2 * A) (hA2 : A < b ^ n) (hT : A * x + D = b ^ (n + h))
    (hD0 : 0 < D) (hD : D < 2 * A) (hTm : Tm = D / b ^ l) (hXl : Xl = x * Tm / b ^ (2 * h - l)) :
    A * (x * b ^ l + Xl) < b ^ (2 * n) ∧ b ^ (2 * n) < A * (x * b ^ l + Xl + 2) := by
  have hb0 : 0 < b := by omega
  have hbl : 0 < b ^ l := pow_pos hb0 l
  have hbh : 0 < b ^ (2 * h) := pow_pos hb0 _
  have hP0 : 0 < b ^ (2 * h - l) := pow_pos hb0 _
  have hA0 : 0 < A := by omega
  have hP : b ^ (2 * h - l) * b ^ l = b ^ (2 * h) := by
    rw [← pow_add]; congr 1; omega
  have hNH : b ^ (2 * h) * b ^ l = b ^ (n + h) := by
    rw [← pow_add]; congr 1; omega
  have h2n : b ^ (2 * n) * b ^ (2 * h) = b ^ (n + h) * b ^ (n + h) := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have hnl : b ^ (n + h) * b ^ l = b ^ (2 * n) := by
    rw [← pow_add]; congr 1; omega
  have hn2h : b ^ n * b ^ (2 * h) = b ^ (2 * n) * b ^ (h - l) := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  -- floor facts
  have hXl1 : Xl * b ^ (2 * h - l) ≤ x * Tm := by rw [hXl]; exact Nat.div_mul_le_self _ _
  have hXl2 : x * Tm < b ^ (2 * h - l) * (Xl + 1) := by rw [hXl]; exact Nat.lt_mul_div_succ _ hP0
  have hTm1 : Tm * b ^ l ≤ D := by rw [hTm]; exact Nat.div_mul_le_self _ _
  have hTm2 : D < b ^ l * (Tm + 1) := by rw [hTm]; exact Nat.lt_mul_div_succ _ hbl
  -- `x ≥ 1`: otherwise `D = β^(n+h) ≥ β^(n+1) > 2A > D`
  have hx : 0 < x := by
    rcases Nat.eq_zero_or_pos x with hx0 | hx0
    · exfalso
      rw [hx0, mul_zero, zero_add] at hT
      have h1 : b ^ n * b ≤ b ^ (n + h) := by
        rw [pow_add]; exact Nat.mul_le_mul_left _ (Nat.le_self_pow (by omega) b)
      have h2 : 2 * A < b ^ n * b := by
        calc 2 * A < 2 * b ^ n := by omega
          _ ≤ b ^ n * b := by rw [mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
      omega
    · exact hx0
  -- the key identity `A x (β^(n+h) + D) + D² = β^(2(n+h))`
  have hkey : A * x * (b ^ (n + h) + D) + D * D = b ^ (n + h) * b ^ (n + h) := by
    calc A * x * (b ^ (n + h) + D) + D * D = A * x * b ^ (n + h) + D * (A * x + D) := by ring
      _ = A * x * b ^ (n + h) + D * b ^ (n + h) := by rw [hT]
      _ = (A * x + D) * b ^ (n + h) := by ring
      _ = b ^ (n + h) * b ^ (n + h) := by rw [hT]
  constructor
  · -- upper bound
    have h1 : Xl * b ^ (2 * h) ≤ x * D := by
      calc Xl * b ^ (2 * h) = Xl * b ^ (2 * h - l) * b ^ l := by rw [mul_assoc, hP]
        _ ≤ x * Tm * b ^ l := Nat.mul_le_mul_right _ hXl1
        _ = x * (Tm * b ^ l) := by ring
        _ ≤ x * D := Nat.mul_le_mul_left _ hTm1
    have h2 : A * (x * b ^ l + Xl) * b ^ (2 * h) ≤ A * x * (b ^ (n + h) + D) := by
      calc A * (x * b ^ l + Xl) * b ^ (2 * h)
          = A * x * (b ^ (2 * h) * b ^ l) + A * (Xl * b ^ (2 * h)) := by ring
        _ = A * x * b ^ (n + h) + A * (Xl * b ^ (2 * h)) := by rw [hNH]
        _ ≤ A * x * b ^ (n + h) + A * (x * D) := Nat.add_le_add_left (Nat.mul_le_mul_left _ h1) _
        _ = A * x * (b ^ (n + h) + D) := by ring
    have h3 : A * (x * b ^ l + Xl) * b ^ (2 * h) < b ^ (2 * n) * b ^ (2 * h) := by
      rw [h2n]
      have : 0 < D * D := Nat.mul_pos hD0 hD0
      omega
    exact Nat.lt_of_mul_lt_mul_right h3
  · -- lower bound
    have h4 : x * D < Xl * b ^ (2 * h) + b ^ (2 * h) + x * b ^ l := by
      calc x * D < x * (b ^ l * (Tm + 1)) := Nat.mul_lt_mul_of_pos_left hTm2 hx
        _ = x * Tm * b ^ l + x * b ^ l := by ring
        _ < b ^ (2 * h - l) * (Xl + 1) * b ^ l + x * b ^ l :=
            Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_right hXl2 hbl) _
        _ = Xl * b ^ (2 * h) + b ^ (2 * h) + x * b ^ l := by
            rw [mul_comm (b ^ (2 * h - l)) (Xl + 1), mul_assoc, hP]; ring
    have h5 : A * x * D < A * Xl * b ^ (2 * h) + A * b ^ (2 * h) + A * x * b ^ l := by
      calc A * x * D = A * (x * D) := by ring
        _ < A * (Xl * b ^ (2 * h) + b ^ (2 * h) + x * b ^ l) := Nat.mul_lt_mul_of_pos_left h4 hA0
        _ = A * Xl * b ^ (2 * h) + A * b ^ (2 * h) + A * x * b ^ l := by ring
    have h6 : D * D + A * x * b ^ l < 5 * b ^ (2 * n) := by
      have hD' : D < 2 * b ^ n := by omega
      have hDD : D * D < (2 * b ^ n) * (2 * b ^ n) := Nat.mul_lt_mul'' hD' hD'
      have hAx : A * x * b ^ l ≤ b ^ (2 * n) := by
        calc A * x * b ^ l ≤ (A * x + D) * b ^ l := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
          _ = b ^ (n + h) * b ^ l := by rw [hT]
          _ = b ^ (2 * n) := hnl
      have : (2 * b ^ n) * (2 * b ^ n) = 4 * b ^ (2 * n) := by
        rw [two_mul n, pow_add]; ring
      omega
    have h7 : 5 * b ^ (2 * n) ≤ A * b ^ (2 * h) := by
      have h71 : b ^ n * b ^ (2 * h) ≤ 2 * A * b ^ (2 * h) := Nat.mul_le_mul_right _ hA1
      have h72 : b ≤ b ^ (h - l) := by
        calc b = b ^ 1 := (pow_one b).symm
          _ ≤ b ^ (h - l) := Nat.pow_le_pow_right hb0 (by omega)
      have h73 : 10 * b ^ (2 * n) ≤ b ^ (2 * n) * b ^ (h - l) := by
        calc 10 * b ^ (2 * n) ≤ b * b ^ (2 * n) := Nat.mul_le_mul_right _ hb
          _ ≤ b ^ (h - l) * b ^ (2 * n) := Nat.mul_le_mul_right _ h72
          _ = b ^ (2 * n) * b ^ (h - l) := by ring
      rw [← hn2h] at h73
      have : 10 * b ^ (2 * n) ≤ 2 * (A * b ^ (2 * h)) := by
        calc 10 * b ^ (2 * n) ≤ b ^ n * b ^ (2 * h) := h73
          _ ≤ 2 * A * b ^ (2 * h) := h71
          _ = 2 * (A * b ^ (2 * h)) := by ring
      omega
    have hR : A * (x * b ^ l + Xl + 2) * b ^ (2 * h)
        = A * x * b ^ (n + h) + A * Xl * b ^ (2 * h) + 2 * (A * b ^ (2 * h)) := by
      calc A * (x * b ^ l + Xl + 2) * b ^ (2 * h)
          = A * x * (b ^ (2 * h) * b ^ l) + A * Xl * b ^ (2 * h) + 2 * (A * b ^ (2 * h)) := by
            ring
        _ = _ := by rw [hNH]
    have h8 : b ^ (2 * n) * b ^ (2 * h) < A * (x * b ^ l + Xl + 2) * b ^ (2 * h) := by
      rw [hR, h2n]
      have e1 : A * x * (b ^ (n + h) + D) = A * x * b ^ (n + h) + A * x * D := by ring
      omega
    exact Nat.lt_of_mul_lt_mul_right h8

/-! ### The base case and the correction loop -/

theorem reciprocalBase_toNat (A : AzNat) (n : Nat) :
    (reciprocalBase A n).toNat = (2 ^ (128 * n) - 1) / A.toNat := by
  unfold reciprocalBase
  have hN : (pow2 (128 * n) - 1).toNat = 2 ^ (128 * n) - 1 := by
    rw [toNat_sub, toNat_pow2, toNat_one]
  obtain ⟨h1, h2⟩ := divModClassic_toNat divDispatchThreshold (pow2 (128 * n) - 1) A
  rw [hN] at h1
  by_cases hA : A.toNat = 0
  · -- the quotient of a division by zero is zero by the dispatcher's convention
    have hsize := (toNat_eq_zero_iff A).mp hA
    rw [hA, Nat.div_zero]
    unfold divModClassic
    simp only [hsize, ↓reduceDIte, toNat_zero]
  · have hlt := h2 hA
    have hpos : 0 < A.toNat := Nat.pos_of_ne_zero hA
    have h_eq : 2 ^ (128 * n) - 1
        = (divModClassic divDispatchThreshold (pow2 (128 * n) - 1) A).2.toNat
          + (divModClassic divDispatchThreshold (pow2 (128 * n) - 1) A).1.toNat * A.toNat := by
      omega
    rw [h_eq, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hlt, Nat.zero_add]

/-- The exact reciprocal `⌊(β^(2n) − 1)/A⌋` satisfies the two-sided bound. -/
theorem reciprocalBase_spec (A : AzNat) (n : Nat) (hA1 : 2 ^ (64 * n) ≤ 2 * A.toNat)
    (hA2 : A.toNat < 2 ^ (64 * n)) :
    A.toNat * (reciprocalBase A n).toNat < 2 ^ (128 * n) ∧
      2 ^ (128 * n) < A.toNat * ((reciprocalBase A n).toNat + 2) := by
  rw [reciprocalBase_toNat]
  have hA0 : 0 < A.toNat := by
    have : 0 < 2 ^ (64 * n) := Nat.two_pow_pos _
    omega
  have hN0 : 0 < 2 ^ (128 * n) := Nat.two_pow_pos _
  set N := 2 ^ (128 * n) with hN
  have h1 : (N - 1) / A.toNat * A.toNat ≤ N - 1 := Nat.div_mul_le_self _ _
  have h2 : N - 1 < A.toNat * ((N - 1) / A.toNat + 1) := Nat.lt_mul_div_succ _ hA0
  constructor
  · rw [mul_comm]; omega
  · have : A.toNat * ((N - 1) / A.toNat + 2) = A.toNat * ((N - 1) / A.toNat + 1) + A.toNat := by
      ring
    omega

theorem reciprocalCorrect_spec (A B : AzNat) (hA : 0 < A.toNat) (hB : 0 < B.toNat) :
    ∀ (fuel : Nat) (x T : AzNat), T.toNat = A.toNat * x.toNat →
      T.toNat < B.toNat + fuel * A.toNat →
      (reciprocalCorrect A B fuel x T).2.toNat = A.toNat * (reciprocalCorrect A B fuel x T).1.toNat
      ∧ (reciprocalCorrect A B fuel x T).2.toNat < B.toNat
      ∧ (B.toNat ≤ T.toNat → B.toNat ≤ (reciprocalCorrect A B fuel x T).2.toNat + A.toNat)
      ∧ (T.toNat < B.toNat → reciprocalCorrect A B fuel x T = (x, T))
  | 0, x, T, hT, hbound => by
    simp only [zero_mul, add_zero] at hbound
    exact ⟨hT, hbound, fun h => by omega, fun _ => rfl⟩
  | fuel + 1, x, T, hT, hbound => by
    simp only [reciprocalCorrect]
    split_ifs with hle
    · rw [le_iff_toNat_le] at hle
      have hx : 0 < x.toNat := by
        rcases Nat.eq_zero_or_pos x.toNat with h0 | h0
        · rw [h0, mul_zero] at hT; omega
        · exact h0
      have hx' : (x - 1).toNat = x.toNat - 1 := by rw [toNat_sub, toNat_one]
      have hTA : T.toNat - A.toNat = A.toNat * (x.toNat - 1) := by
        rw [hT, Nat.mul_sub_one]
      have hT' : (T - A).toNat = A.toNat * (x - 1).toNat := by
        rw [toNat_sub, hx', hTA]
      have hbound' : (T - A).toNat < B.toNat + fuel * A.toNat := by
        rw [toNat_sub]
        have : T.toNat < B.toNat + fuel * A.toNat + A.toNat := by
          rw [Nat.succ_mul] at hbound; omega
        omega
      obtain ⟨h1, h2, h3, h4⟩ := reciprocalCorrect_spec A B hA hB fuel (x - 1) (T - A) hT' hbound'
      refine ⟨h1, h2, fun _ => ?_, fun hlt => absurd hle (not_le.mpr hlt)⟩
      rcases le_or_gt B.toNat (T - A).toNat with hle' | hlt'
      · exact h3 hle'
      · rw [h4 hlt']
        have hTge : A.toNat ≤ T.toNat := by
          rw [hT]; exact Nat.le_mul_of_pos_right _ hx
        rw [toNat_sub]
        omega
    · rw [le_iff_toNat_le] at hle
      exact ⟨hT, not_le.mp hle, fun h => absurd h hle, fun _ => rfl⟩

/-! ### The approximate reciprocal -/

/-- **The wrap-around trick** (MCA §3.4.1): the residue of `A X_h` modulo `2^m + 1` determines
it, given `β^(n+h) − 2β^n < A X_h < β^(n+h) + 2β^n` and `2^m ≥ 4β^n`. -/
theorem wrapProduct_toNat (n h : Nat) (hh : 1 ≤ h) (A Xh : AzNat)
    (hA : A.toNat < 2 ^ (64 * n)) (hXh : Xh.toNat < 2 ^ (64 * n))
    (hlo : 2 ^ (64 * (n + h)) < A.toNat * Xh.toNat + 2 * 2 ^ (64 * n))
    (hhi : A.toNat * Xh.toNat < 2 ^ (64 * (n + h)) + 2 * 2 ^ (64 * n)) :
    (wrapProduct n h A Xh).toNat = A.toNat * Xh.toNat := by
  simp only [wrapProduct]
  set p := SSPlan.ofLimbs (n + 1) with hp
  have hbits : 64 * (n + 1) ≤ p.bits := SSPlan.ofLimbs_bits (n + 1)
  have hpow : 4 * 2 ^ (64 * n) ≤ 2 ^ p.bits := by
    calc 4 * 2 ^ (64 * n) ≤ 2 ^ 64 * 2 ^ (64 * n) := Nat.mul_le_mul_right _ (by norm_num)
      _ = 2 ^ (64 * (n + 1)) := by rw [← pow_add]; congr 1; ring
      _ ≤ 2 ^ p.bits := Nat.pow_le_pow_right (by norm_num) hbits
  have hA' : A.toNat < 2 ^ p.bits := by omega
  have hXh' : Xh.toNat < 2 ^ p.bits := by omega
  have hT : (p.mulModF' (· * ·) A Xh).val.toNat = (A.toNat * Xh.toNat) % (2 ^ p.bits + 1) :=
    p.mulModF'_toNat (· * ·) (fun x y => toNat_mul x y) A Xh hA' hXh'
  have hpow_nh : 2 * 2 ^ (64 * n) ≤ 2 ^ (64 * (n + h)) := by
    calc 2 * 2 ^ (64 * n) ≤ 2 ^ 64 * 2 ^ (64 * n) := Nat.mul_le_mul_right _ (by norm_num)
      _ = 2 ^ (64 * (n + 1)) := by rw [← pow_add]; congr 1; ring
      _ ≤ 2 ^ (64 * (n + h)) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hlo_val : (pow2 (64 * (n + h)) - (pow2 (64 * n) <<< (1 : Nat)) + 1).toNat
      = 2 ^ (64 * (n + h)) - 2 * 2 ^ (64 * n) + 1 := by
    rw [toNat_add, toNat_sub, toNat_shl_pow, toNat_pow2, toNat_pow2, toNat_one, pow_one,
      mul_comm (2 ^ (64 * n)) 2]
  set lo := pow2 (64 * (n + h)) - (pow2 (64 * n) <<< (1 : Nat)) + 1 with hlo_def
  set r := (AzFermat.sub (p.mulModF' (· * ·) A Xh) (AzFermat.ofAzNat p.bits lo)).val with hr
  have hr_le : r.toNat ≤ 2 ^ p.bits := (AzFermat.sub _ _).isLe
  have hz : ((lo.toNat + r.toNat : ℕ) : ZMod (2 ^ p.bits + 1))
      = ((A.toNat * Xh.toNat : ℕ) : ZMod (2 ^ p.bits + 1)) := by
    have h1 : (r.toNat : ZMod (2 ^ p.bits + 1))
        = toZMod (AzFermat.sub (p.mulModF' (· * ·) A Xh) (AzFermat.ofAzNat p.bits lo)) :=
      (toZMod_eq_natCast _).symm
    rw [toZMod_sub', toZMod_ofAzNat, toZMod_eq_natCast (p.mulModF' (· * ·) A Xh), hT,
      ZMod.natCast_mod] at h1
    push_cast
    rw [h1]
    push_cast
    ring
  rw [toNat_add, hlo_val]
  rw [hlo_val] at hz
  have hcong := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hz
  set L := 2 ^ (64 * (n + h)) - 2 * 2 ^ (64 * n) + 1 with hL
  have hLle : L ≤ A.toNat * Xh.toNat := by omega
  have hPlt : A.toNat * Xh.toNat - L < 2 ^ p.bits + 1 := by omega
  have hrlt : r.toNat < 2 ^ p.bits + 1 := by omega
  have hsplit : A.toNat * Xh.toNat = L + (A.toNat * Xh.toNat - L) := (Nat.add_sub_cancel' hLle).symm
  rw [hsplit] at hcong
  have hmod : r.toNat % (2 ^ p.bits + 1) = (A.toNat * Xh.toNat - L) % (2 ^ p.bits + 1) :=
    Nat.ModEq.add_left_cancel' L hcong
  rw [Nat.mod_eq_of_lt hrlt, Nat.mod_eq_of_lt hPlt] at hmod
  omega

/-- Steps 6–11 from `X_h` and an exact `T₀ = A X_h` (however it was computed): the correction
loop, the scaled square, and the abstract Newton step. -/
theorem newtonStepAssemble_spec (n l h : Nat) (hn : n = h + l) (hlh : l < h) (A Xh T0 : AzNat)
    (hA1 : 2 ^ (64 * n) ≤ 2 * A.toNat) (hA2 : A.toNat < 2 ^ (64 * n))
    (hT0 : T0.toNat = A.toNat * Xh.toNat)
    (hT0_lt : T0.toNat < 2 ^ (64 * (n + h)) + 4 * A.toNat)
    (hB_lt : 2 ^ (64 * (n + h)) < T0.toNat + 2 * A.toNat) :
    A.toNat * (newtonStepAssemble n l h A Xh T0).toNat < 2 ^ (128 * n) ∧
      2 ^ (128 * n) < A.toNat * ((newtonStepAssemble n l h A Xh T0).toNat + 2) := by
  have hA0 : 0 < A.toNat := by
    have : 0 < 2 ^ (64 * n) := Nat.two_pow_pos _
    omega
  simp only [newtonStepAssemble]
  set B := pow2 (64 * (n + h)) with hB
  have hB_val : B.toNat = 2 ^ (64 * (n + h)) := toNat_pow2 _
  have hB0 : 0 < B.toNat := by rw [hB_val]; exact Nat.two_pow_pos _
  rw [← hB_val] at hT0_lt hB_lt
  -- the correction loop
  obtain ⟨hc1, hc2, hc3, hc4⟩ := reciprocalCorrect_spec A B hA0 hB0 4 Xh T0 hT0 hT0_lt
  set xt := reciprocalCorrect A B 4 Xh T0 with hxt
  have hD_lt : B.toNat < xt.2.toNat + 2 * A.toNat := by
    rcases le_or_gt B.toNat T0.toNat with hle | hlt
    · have := hc3 hle; omega
    · rw [hc4 hlt]; exact hB_lt
  set D := B - xt.2 with hD
  have hD_val : D.toNat = B.toNat - xt.2.toNat := toNat_sub _ _
  have hD0 : 0 < D.toNat := by rw [hD_val]; omega
  have hD2 : D.toNat < 2 * A.toNat := by rw [hD_val]; omega
  have hTeq : A.toNat * xt.1.toNat + D.toNat = 2 ^ (64 * (n + h)) := by
    rw [hD_val, ← hc1, ← hB_val]; omega
  -- the final assembly
  set Tm := D >>> (64 * l) with hTmd
  have hTm_val : Tm.toNat = D.toNat / 2 ^ (64 * l) := toNat_shr_pow D _
  have hU_val : (Tm * xt.1).toNat = xt.1.toNat * Tm.toNat := by
    rw [toNat_mul, mul_comm]
  have hres : ((xt.1 <<< (64 * l)) + ((Tm * xt.1) >>> (64 * (2 * h - l)))).toNat
      = xt.1.toNat * 2 ^ (64 * l) + xt.1.toNat * Tm.toNat / 2 ^ (64 * (2 * h - l)) := by
    rw [toNat_add, toNat_shl_pow, toNat_shr_pow, hU_val]
  rw [hres]
  -- pass to the abstract lemma with `b = 2^64`
  have key := newton_step_bounds (b := 2 ^ 64) (n := n) (h := h) (l := l) (A := A.toNat)
    (x := xt.1.toNat) (D := D.toNat) (Tm := Tm.toNat)
    (Xl := xt.1.toNat * Tm.toNat / 2 ^ (64 * (2 * h - l)))
    (by norm_num) hn hlh (by rw [← two_pow_64_mul]; exact hA1) (by rw [← two_pow_64_mul]; exact hA2)
    (by rw [← two_pow_64_mul]; exact hTeq) hD0 hD2 (by rw [← two_pow_64_mul]; exact hTm_val)
    (by rw [← two_pow_64_mul])
  rw [← two_pow_64_mul, ← two_pow_64_mul] at key
  have h2n : 128 * n = 64 * (2 * n) := by ring
  rw [h2n]
  exact key

theorem approxReciprocalFuel_spec (base fftFrom : Nat) (hbase : 2 ≤ base) :
    ∀ (fuel : Nat) (A : AzNat) (n : Nat), n ≤ fuel + base →
      2 ^ (64 * n) ≤ 2 * A.toNat → A.toNat < 2 ^ (64 * n) →
      A.toNat * (approxReciprocalFuel base fftFrom fuel A n).toNat < 2 ^ (128 * n) ∧
        2 ^ (128 * n) < A.toNat * ((approxReciprocalFuel base fftFrom fuel A n).toNat + 2)
  | 0, A, n, _, hA1, hA2 => by
    simp only [approxReciprocalFuel]
    exact reciprocalBase_spec A n hA1 hA2
  | fuel + 1, A, n, hnf, hA1, hA2 => by
    by_cases hnb : n ≤ base
    · simp only [approxReciprocalFuel, hnb, ↓reduceIte]
      exact reciprocalBase_spec A n hA1 hA2
    · simp only [approxReciprocalFuel, hnb, ↓reduceIte]
      push Not at hnb
      -- the split
      set l := (n - 1) / 2 with hl
      set h := n - l with hh
      have hn3 : 3 ≤ n := by omega
      have hl1 : 1 ≤ l := by omega
      have hlh : l < h := by omega
      have hn : n = h + l := by omega
      have hA0 : 0 < A.toNat := by
        have : 0 < 2 ^ (64 * n) := Nat.two_pow_pos _
        omega
      -- the top `h` limbs
      set Ah := A >>> (64 * l) with hAh
      have hAh_val : Ah.toNat = A.toNat / 2 ^ (64 * l) := toNat_shr_pow A (64 * l)
      have hpow_nl : (2 : ℕ) ^ (64 * n) = 2 ^ (64 * h) * 2 ^ (64 * l) := by
        rw [← pow_add]; congr 1; omega
      have hpow_l : 0 < (2 : ℕ) ^ (64 * l) := Nat.two_pow_pos _
      have hAh1 : 2 ^ (64 * h) ≤ 2 * Ah.toNat := by
        rw [hAh_val]
        have h1 : 2 ^ (64 * h - 1) * 2 ^ (64 * l) ≤ A.toNat := by
          have : 2 ^ (64 * h - 1) * 2 ^ (64 * l) * 2 = 2 ^ (64 * n) := by
            rw [mul_assoc, mul_comm (2 ^ (64 * l)) 2, ← mul_assoc, ← pow_succ, ← pow_add]
            congr 1; omega
          omega
        have h2 : 2 ^ (64 * h - 1) ≤ A.toNat / 2 ^ (64 * l) :=
          (Nat.le_div_iff_mul_le hpow_l).mpr h1
        have h3 : 2 ^ (64 * h) = 2 * 2 ^ (64 * h - 1) := by
          rw [← pow_succ']; congr 1; omega
        omega
      have hAh2 : Ah.toNat < 2 ^ (64 * h) := by
        rw [hAh_val, Nat.div_lt_iff_lt_mul hpow_l, ← hpow_nl]; exact hA2
      obtain ⟨hXh1, hXh2⟩ := approxReciprocalFuel_spec base fftFrom hbase fuel Ah h (by omega) hAh1 hAh2
      set Xh := approxReciprocalFuel base fftFrom fuel Ah h with hXh
      have hpow_B : (2 : ℕ) ^ (64 * (n + h)) = 2 ^ (128 * h) * 2 ^ (64 * l) := by
        rw [← pow_add]; congr 1; omega
      have hAhl : Ah.toNat * 2 ^ (64 * l) ≤ A.toNat := by
        rw [hAh_val]; exact Nat.div_mul_le_self _ _
      have hAlt : A.toNat < 2 ^ (64 * l) * (Ah.toNat + 1) := by
        rw [hAh_val]; exact Nat.lt_mul_div_succ _ hpow_l
      have hXh_lt : Xh.toNat < 2 * 2 ^ (64 * h) := by
        have h1 : Xh.toNat * 2 ^ (64 * h) ≤ Xh.toNat * (2 * Ah.toNat) :=
          Nat.mul_le_mul_left _ hAh1
        have h2 : Xh.toNat * (2 * Ah.toNat) = 2 * (Ah.toNat * Xh.toNat) := by ring
        have h3 : (2 : ℕ) ^ (128 * h) = 2 ^ (64 * h) * 2 ^ (64 * h) := by
          rw [← pow_add]; congr 1; omega
        have h4 : 0 < (2 : ℕ) ^ (64 * h) := Nat.two_pow_pos _
        have : Xh.toNat * 2 ^ (64 * h) < 2 * 2 ^ (64 * h) * 2 ^ (64 * h) := by
          calc Xh.toNat * 2 ^ (64 * h) ≤ 2 * (Ah.toNat * Xh.toNat) := h1.trans_eq h2
            _ < 2 * 2 ^ (128 * h) := by omega
            _ = 2 * 2 ^ (64 * h) * 2 ^ (64 * h) := by rw [h3]; ring
        exact Nat.lt_of_mul_lt_mul_right this
      -- `A X_h < β^(n+h) + 2β^n`
      have hT0_lt' : A.toNat * Xh.toNat < 2 ^ (64 * (n + h)) + 2 * 2 ^ (64 * n) := by
        rw [hpow_B]
        have h1 : A.toNat * Xh.toNat < 2 ^ (64 * l) * (Ah.toNat + 1) * Xh.toNat := by
          rcases Nat.eq_zero_or_pos Xh.toNat with h0 | h0
          · -- impossible: `β^(2h) < A_h (X_h + 2)` with `X_h = 0` gives `β^(2h) < 2 A_h`
            exfalso
            rw [h0, zero_add, mul_two] at hXh2
            have : 2 ^ (64 * h) * 2 ^ (64 * h) = 2 ^ (128 * h) := by
              rw [← pow_add]; congr 1; omega
            have h4 : 0 < (2 : ℕ) ^ (64 * h) := Nat.two_pow_pos _
            have h5 : Ah.toNat * 2 ^ (64 * h) < 2 ^ (64 * h) * 2 ^ (64 * h) :=
              Nat.mul_lt_mul_of_pos_right hAh2 h4
            have h6 : 2 ^ (64 * h) ≤ 2 ^ (64 * h) * 2 ^ (64 * h) := Nat.le_mul_of_pos_right _ h4
            have h7 : 2 ^ (64 * h) * 2 ^ (64 * h) ≤ 2 ^ (64 * h) * 2 ^ (64 * h) := le_rfl
            -- `A_h + A_h > β^(2h) ≥ β^h · β^h` while `A_h < β^h`: need `h ≥ 1`
            have h8 : 2 * Ah.toNat < 2 * 2 ^ (64 * h) := by omega
            have h9 : (2 : ℕ) ≤ 2 ^ (64 * h) := by
              calc (2 : ℕ) = 2 ^ 1 := rfl
                _ ≤ 2 ^ (64 * h) := Nat.pow_le_pow_right (by norm_num) (by omega)
            have h10 : 2 * 2 ^ (64 * h) ≤ 2 ^ (64 * h) * 2 ^ (64 * h) :=
              Nat.mul_le_mul_right _ h9
            omega
          · exact Nat.mul_lt_mul_of_pos_right hAlt h0
        have h2 : 2 ^ (64 * l) * (Ah.toNat + 1) * Xh.toNat
            = Ah.toNat * Xh.toNat * 2 ^ (64 * l) + 2 ^ (64 * l) * Xh.toNat := by ring
        have h3 : Ah.toNat * Xh.toNat * 2 ^ (64 * l) ≤ 2 ^ (128 * h) * 2 ^ (64 * l) :=
          Nat.mul_le_mul_right _ hXh1.le
        have h4 : 2 ^ (64 * l) * Xh.toNat < 2 ^ (64 * l) * (2 * 2 ^ (64 * h)) :=
          Nat.mul_lt_mul_of_pos_left hXh_lt hpow_l
        have h5 : 2 ^ (64 * l) * (2 * 2 ^ (64 * h)) = 2 * 2 ^ (64 * n) := by
          rw [hpow_nl]; ring
        omega
      -- `β^(n+h) < A X_h + 2A`
      have hB_lt' : 2 ^ (64 * (n + h)) < A.toNat * Xh.toNat + 2 * A.toNat := by
        rw [hpow_B]
        have h1 : 2 ^ (128 * h) * 2 ^ (64 * l) < Ah.toNat * (Xh.toNat + 2) * 2 ^ (64 * l) :=
          Nat.mul_lt_mul_of_pos_right hXh2 hpow_l
        have h2 : Ah.toNat * (Xh.toNat + 2) * 2 ^ (64 * l)
            = Ah.toNat * 2 ^ (64 * l) * (Xh.toNat + 2) := by ring
        have h3 : Ah.toNat * 2 ^ (64 * l) * (Xh.toNat + 2) ≤ A.toNat * (Xh.toNat + 2) :=
          Nat.mul_le_mul_right _ hAhl
        have h4 : A.toNat * (Xh.toNat + 2) = A.toNat * Xh.toNat + 2 * A.toNat := by ring
        omega
      -- the product `A X_h`, exactly, by the full product or the wrap-around trick
      have hXh_n : Xh.toNat < 2 ^ (64 * n) := by
        have : 2 * 2 ^ (64 * h) ≤ 2 ^ (64 * n) := by
          calc 2 * 2 ^ (64 * h) = 2 ^ (64 * h + 1) := by rw [pow_succ]; ring
            _ ≤ 2 ^ (64 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have hT0 : (if fftFrom ≤ n then wrapProduct n h A Xh else A * Xh).toNat
          = A.toNat * Xh.toNat := by
        split_ifs with hf
        · exact wrapProduct_toNat n h (by omega) A Xh hA2 hXh_n (by omega) hT0_lt'
        · exact toNat_mul A Xh
      exact newtonStepAssemble_spec n l h hn hlh A Xh _ hA1 hA2 hT0 (by omega) (by omega)

/-- **MCA Lemma 3.8**: `A X < β^(2n) < A (X + 2)` for `β^n/2 ≤ A < β^n`. -/
theorem approxReciprocal_spec (base fftFrom : Nat) (hbase : 2 ≤ base) (A : AzNat) (n : Nat)
    (hA1 : 2 ^ (64 * n) ≤ 2 * A.toNat) (hA2 : A.toNat < 2 ^ (64 * n)) :
    A.toNat * (approxReciprocal base fftFrom A n).toNat < 2 ^ (128 * n) ∧
      2 ^ (128 * n) < A.toNat * ((approxReciprocal base fftFrom A n).toNat + 2) :=
  approxReciprocalFuel_spec base fftFrom hbase n A n (by omega) hA1 hA2

/-! ### Barrett's step (MCA Theorem 2.4 with the approximate reciprocal) -/

theorem barrett_bounds {b A A1 A0 V X Q : ℕ} (hA : A = A1 * b + A0) (hA0 : A0 < b)
    (hA1 : A1 < b) (hV1 : b ≤ 2 * V) (hV2 : V < b) (hX1 : V * X < b * b)
    (hX2 : b * b < V * (X + 2)) (hQ : Q = A1 * X / b) : Q * V ≤ A ∧ A < V * (Q + 5) := by
  have hb0 : 0 < b := by omega
  have hV0 : 0 < V := by omega
  have hQ1 : Q * b ≤ A1 * X := by rw [hQ]; exact Nat.div_mul_le_self _ _
  have hQ2 : A1 * X < b * (Q + 1) := by rw [hQ]; exact Nat.lt_mul_div_succ _ hb0
  constructor
  · have h1 : Q * V * b ≤ A1 * b * b := by
      calc Q * V * b = Q * b * V := by ring
        _ ≤ A1 * X * V := Nat.mul_le_mul_right _ hQ1
        _ = A1 * (V * X) := by ring
        _ ≤ A1 * (b * b) := Nat.mul_le_mul_left _ hX1.le
        _ = A1 * b * b := by ring
    have h2 : Q * V ≤ A1 * b := Nat.le_of_mul_le_mul_right h1 hb0
    omega
  · have h1 : A1 * (b * b) ≤ A1 * (V * X) + 2 * A1 * V := by
      calc A1 * (b * b) ≤ A1 * (V * (X + 2)) := Nat.mul_le_mul_left _ hX2.le
        _ = A1 * (V * X) + 2 * A1 * V := by ring
    have h2 : A1 * (V * X) < b * (Q + 1) * V := by
      calc A1 * (V * X) = A1 * X * V := by ring
        _ < b * (Q + 1) * V := Nat.mul_lt_mul_of_pos_right hQ2 hV0
    have h3 : 2 * A1 * V ≤ 2 * b * V := by
      have := Nat.mul_le_mul_right V (Nat.mul_le_mul_left 2 hA1.le)
      exact this
    have h4 : A0 * b < 2 * V * b := by
      calc A0 * b < b * b := Nat.mul_lt_mul_of_pos_right hA0 hb0
        _ ≤ 2 * V * b := Nat.mul_le_mul_right _ hV1
    have h5 : A * b = A1 * (b * b) + A0 * b := by rw [hA]; ring
    have h6 : A * b < V * (Q + 5) * b := by
      have e1 : b * (Q + 1) * V = V * Q * b + V * b := by ring
      have e2 : V * (Q + 5) * b = V * Q * b + 5 * (V * b) := by ring
      have e3 : 2 * b * V = 2 * (V * b) := by ring
      have e4 : 2 * V * b = 2 * (V * b) := by ring
      omega
    exact Nat.lt_of_mul_lt_mul_right h6

theorem barrettCorrect_spec (V : AzNat) (hV : 0 < V.toNat) (A : Nat) :
    ∀ (fuel : Nat) (Q R : AzNat), Q.toNat * V.toNat + R.toNat = A → R.toNat < fuel * V.toNat →
      (barrettCorrect V fuel Q R).1.toNat * V.toNat + (barrettCorrect V fuel Q R).2.toNat = A ∧
        (barrettCorrect V fuel Q R).2.toNat < V.toNat
  | 0, Q, R, _, hbound => by simp at hbound
  | fuel + 1, Q, R, hQR, hbound => by
    simp only [barrettCorrect]
    split_ifs with hle
    · rw [le_iff_toNat_le] at hle
      apply barrettCorrect_spec V hV A fuel (Q + 1) (R - V)
      · rw [toNat_add, toNat_one, toNat_sub]
        have : (Q.toNat + 1) * V.toNat = Q.toNat * V.toNat + V.toNat := by ring
        omega
      · rw [toNat_sub]
        rw [Nat.succ_mul] at hbound
        omega
    · rw [le_iff_toNat_le] at hle
      exact ⟨hQR, not_le.mp hle⟩

theorem barrettStep_toNat (sp : Nat) (hsp : 3 ≤ sp) (V X : AzNat) (n : Nat)
    (hV1 : 2 ^ (64 * n) ≤ 2 * V.toNat) (hV2 : V.toNat < 2 ^ (64 * n))
    (hX1 : V.toNat * X.toNat < 2 ^ (128 * n)) (hX2 : 2 ^ (128 * n) < V.toNat * (X.toNat + 2))
    (A : AzNat) (hA : A.toNat < V.toNat * 2 ^ (64 * n)) :
    (barrettStep sp V X n A).1.toNat * V.toNat + (barrettStep sp V X n A).2.toNat = A.toNat ∧
      (barrettStep sp V X n A).2.toNat < V.toNat := by
  have hb0 : 0 < (2 : ℕ) ^ (64 * n) := Nat.two_pow_pos _
  have hV0 : 0 < V.toNat := by omega
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp only [mul_zero, pow_zero] at hV1 hV2; omega
    · exact h0
  have hbb : (2 : ℕ) ^ (128 * n) = 2 ^ (64 * n) * 2 ^ (64 * n) := by
    rw [← pow_add]; congr 1; omega
  have hpow2 : (2 : ℕ) ^ (64 * (n + 2)) = 2 ^ (64 * n) * 2 ^ 128 := by
    rw [show 64 * (n + 2) = 64 * n + 128 by ring, pow_add]
  have hpowm : (2 : ℕ) ^ (64 * (n + 2)) = 2 ^ (64 * (n - 1)) * 2 ^ 192 := by
    rw [show 64 * (n + 2) = 64 * (n - 1) + 192 by omega, pow_add]
  have h64n : (2 : ℕ) ^ (64 * (n - 1)) * 2 ^ 64 = 2 ^ (64 * n) := by
    rw [show 64 * n = 64 * (n - 1) + 64 by omega, pow_add]
  set w := n + 2 + Nat.size (3 * n + 9) / 64 with hw
  have h4 : (2 : ℕ) ^ (64 * w) = 2 ^ (64 * (Nat.size (3 * n + 9) / 64 + 1)) * 2 ^ (64 * n) * 2 ^ 64 := by
    rw [show 64 * w = 64 * (Nat.size (3 * n + 9) / 64 + 1) + 64 * n + 64 by rw [hw]; ring,
      pow_add, pow_add]
  set b := (2 : ℕ) ^ (64 * n) with hb
  have hA1lt : A.toNat / b < b := by
    rw [Nat.div_lt_iff_lt_mul hb0]
    calc A.toNat < V.toNat * b := hA
      _ ≤ b * b := Nat.mul_le_mul_right _ hV2.le
  have hX_lt : X.toNat < 2 * b := by
    have h1 : X.toNat * b ≤ X.toNat * (2 * V.toNat) := Nat.mul_le_mul_left _ hV1
    have h2 : X.toNat * (2 * V.toNat) = 2 * (V.toNat * X.toNat) := by ring
    have : X.toNat * b < 2 * b * b := by
      calc X.toNat * b ≤ 2 * (V.toNat * X.toNat) := h1.trans_eq h2
        _ < 2 * 2 ^ (128 * n) := by omega
        _ = 2 * b * b := by rw [hbb]; ring
    exact Nat.lt_of_mul_lt_mul_right this
  obtain ⟨hQV, hAQ⟩ := barrett_bounds (b := b) (A := A.toNat) (A1 := A.toNat / b)
    (A0 := A.toNat % b) (V := V.toNat) (X := X.toNat) (Q := A.toNat / b * X.toNat / b)
    (by rw [mul_comm, Nat.div_add_mod]) (Nat.mod_lt _ hb0) hA1lt hV1 hV2
    (by rw [← hbb]; exact hX1) (by rw [← hbb]; exact hX2) rfl
  unfold barrettStep
  simp only
  set A1 := A >>> (64 * n) with hA1def
  have hA1v : A1.toNat = A.toNat / b := toNat_shr_pow A _
  -- the high short product with one guard limb
  have hin1 : (A1 <<< 128).toNat < 2 ^ (64 * (n + 2)) := by
    rw [toNat_shl_pow, hA1v, hpow2]; exact Nat.mul_lt_mul_of_pos_right hA1lt (by norm_num)
  have hin2 : (X <<< 64).toNat < 2 ^ (64 * (n + 2)) := by
    rw [toNat_shl_pow, hpow2]
    calc X.toNat * 2 ^ 64 < 2 * b * 2 ^ 64 := Nat.mul_lt_mul_of_pos_right hX_lt (by norm_num)
      _ = b * (2 * 2 ^ 64) := by ring
      _ ≤ b * 2 ^ 128 := Nat.mul_le_mul_left _ (by norm_num)
  obtain ⟨hS1, hS2⟩ := mulHigh_spec sp hsp (A1 <<< 128) (X <<< 64) (n + 2) hin1 hin2
  rw [toNat_shl_pow, toNat_shl_pow, hA1v] at hS1 hS2
  set S := (mulHigh sp (A1 <<< 128) (X <<< 64) (n + 2)).toNat with hS
  have hT1 : S * 2 ^ (64 * (n - 1)) ≤ A.toNat / b * X.toNat := by
    have : S * 2 ^ (64 * (n - 1)) * 2 ^ 192 ≤ A.toNat / b * X.toNat * 2 ^ 192 := by
      calc S * 2 ^ (64 * (n - 1)) * 2 ^ 192 = S * 2 ^ (64 * (n + 2)) := by rw [hpowm]; ring
        _ ≤ A.toNat / b * 2 ^ 128 * (X.toNat * 2 ^ 64) := hS1
        _ = A.toNat / b * X.toNat * 2 ^ 192 := by ring
    exact Nat.le_of_mul_le_mul_right this (by norm_num)
  have hT2 : A.toNat / b * X.toNat < (S + 3 * (n + 2 - 1) + 1) * 2 ^ (64 * (n - 1)) := by
    have : A.toNat / b * X.toNat * 2 ^ 192
        < (S + 3 * (n + 2 - 1) + 1) * 2 ^ (64 * (n - 1)) * 2 ^ 192 := by
      calc A.toNat / b * X.toNat * 2 ^ 192 = A.toNat / b * 2 ^ 128 * (X.toNat * 2 ^ 64) := by ring
        _ < (S + 3 * (n + 2 - 1) + 1) * 2 ^ (64 * (n + 2)) := hS2
        _ = _ := by rw [hpowm]; ring
    exact Nat.lt_of_mul_lt_mul_right this
  set T := A.toNat / b * X.toNat / 2 ^ (64 * (n - 1)) with hT
  have hm0 : 0 < (2 : ℕ) ^ (64 * (n - 1)) := Nat.two_pow_pos _
  have hST : S ≤ T := (Nat.le_div_iff_mul_le hm0).mpr hT1
  have hTS : T ≤ S + 3 * (n + 1) := by
    have : T < S + 3 * (n + 2 - 1) + 1 := (Nat.div_lt_iff_lt_mul hm0).mpr hT2
    omega
  have hQdef : (mulHigh sp (A1 <<< 128) (X <<< 64) (n + 2) >>> 64).toNat = S / 2 ^ 64 :=
    toNat_shr_pow _ _
  have hTQ : T / 2 ^ 64 = A.toNat / b * X.toNat / b := by
    rw [hT, Nat.div_div_eq_div_mul, h64n]
  set Qh := S / 2 ^ 64 with hQh
  have h64 : (0 : ℕ) < 2 ^ 64 := by norm_num
  have hQhle : Qh ≤ A.toNat / b * X.toNat / b := by
    rw [← hTQ]; exact Nat.div_le_div_right hST
  have hQge : A.toNat / b * X.toNat / b ≤ Qh + 3 * (n + 1) := by
    rw [← hTQ]
    have h1 : S < 2 ^ 64 * (S / 2 ^ 64 + 1) := Nat.lt_mul_div_succ S h64
    have h2 : 3 * (n + 1) ≤ 3 * (n + 1) * 2 ^ 64 := Nat.le_mul_of_pos_right _ h64
    have h3 : T < (Qh + 3 * (n + 1) + 1) * 2 ^ 64 := by
      calc T ≤ S + 3 * (n + 1) := hTS
        _ < 2 ^ 64 * (Qh + 1) + 3 * (n + 1) * 2 ^ 64 := by rw [hQh]; omega
        _ = (Qh + 3 * (n + 1) + 1) * 2 ^ 64 := by ring
    exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul h64).mpr h3)
  -- the remainder from the exact low product
  have hW0 : 0 < (2 : ℕ) ^ (64 * w) := Nat.two_pow_pos _
  have hQhV : Qh * V.toNat ≤ A.toNat := (Nat.mul_le_mul_right _ hQhle).trans hQV
  have hAlt : A.toNat - Qh * V.toNat < (3 * n + 9) * V.toNat := by
    have h1 : V.toNat * (A.toNat / b * X.toNat / b + 5) ≤ V.toNat * (Qh + 3 * (n + 1) + 5) :=
      Nat.mul_le_mul_left _ (by omega)
    have e : V.toNat * (Qh + 3 * (n + 1) + 5) = Qh * V.toNat + (3 * n + 8) * V.toNat := by ring
    have e2 : (3 * n + 9) * V.toNat = (3 * n + 8) * V.toNat + V.toNat := by ring
    omega
  have hbound : (3 * n + 9) * V.toNat < 2 ^ (64 * w) := by
    have h1 : 3 * n + 9 < 2 ^ (Nat.size (3 * n + 9)) := Nat.lt_size_self _
    have h2 : Nat.size (3 * n + 9) ≤ 64 * (Nat.size (3 * n + 9) / 64 + 1) := by
      have := Nat.lt_div_mul_add (a := Nat.size (3 * n + 9)) (b := 64) (by norm_num); omega
    have h3 : (2 : ℕ) ^ (Nat.size (3 * n + 9)) ≤ 2 ^ (64 * (Nat.size (3 * n + 9) / 64 + 1)) :=
      Nat.pow_le_pow_right (by norm_num) h2
    calc (3 * n + 9) * V.toNat < (3 * n + 9) * b := Nat.mul_lt_mul_of_pos_left hV2 (by omega)
      _ ≤ 2 ^ (64 * (Nat.size (3 * n + 9) / 64 + 1)) * b :=
          Nat.mul_le_mul_right _ (h1.le.trans h3)
      _ ≤ 2 ^ (64 * (Nat.size (3 * n + 9) / 64 + 1)) * b * 2 ^ 64 :=
          Nat.le_mul_of_pos_right _ (by norm_num)
      _ = 2 ^ (64 * w) := h4.symm
  have hRdiff : A.toNat - Qh * V.toNat < 2 ^ (64 * w) := lt_trans hAlt hbound
  set Qf := mulHigh sp (A1 <<< 128) (X <<< 64) (n + 2) >>> 64 with hQf
  set R := ((A.modPow2 (64 * w) + pow2 (64 * w)) - mulLow sp Qf V w).modPow2 (64 * w) with hRdef
  have hR : R.toNat = A.toNat - Qh * V.toNat := by
    rw [hRdef, toNat_modPow2, toNat_sub, toNat_add, toNat_modPow2, toNat_pow2, mulLow_toNat,
      hQdef]
    set W := (2 : ℕ) ^ (64 * w) with hWdef
    have hP : Qh * V.toNat % W ≤ A.toNat % W + W :=
      (Nat.mod_lt _ hW0).le.trans (Nat.le_add_left _ _)
    have hz : ((A.toNat % W + W - Qh * V.toNat % W : ℕ) : ZMod W)
        = ((A.toNat - Qh * V.toNat : ℕ) : ZMod W) := by
      rw [Nat.cast_sub hP, Nat.cast_sub hQhV, Nat.cast_add, ZMod.natCast_mod, ZMod.natCast_mod,
        ZMod.natCast_self]
      ring
    have := congrArg ZMod.val hz
    rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hRdiff] at this
    exact this
  apply barrettCorrect_spec V hV0 A.toNat (3 * n + 9) Qf R
  · rw [hQdef, hR]; exact Nat.add_sub_cancel' hQhV
  · rw [hR]; exact hAlt

/-! ### The block loop -/

theorem newtonDivBlocks_spec (sp : Nat) (hsp : 3 ≤ sp) (V X : AzNat) (n : Nat) (hV1 : 2 ^ (64 * n) ≤ 2 * V.toNat)
    (hV2 : V.toNat < 2 ^ (64 * n)) (hX1 : V.toNat * X.toNat < 2 ^ (128 * n))
    (hX2 : 2 ^ (128 * n) < V.toNat * (X.toNat + 2)) (U : AzNat) :
    ∀ (j : Nat) (Q R : AzNat), Q.toNat * V.toNat + R.toNat = U.toNat / 2 ^ (64 * (n * j)) →
      R.toNat < V.toNat →
      (newtonDivBlocks sp V X n U j Q R).1.toNat * V.toNat
          + (newtonDivBlocks sp V X n U j Q R).2.toNat = U.toNat ∧
        (newtonDivBlocks sp V X n U j Q R).2.toNat < V.toNat
  | 0, Q, R, hQR, hR => by
    simp only [newtonDivBlocks, mul_zero, pow_zero, Nat.div_one] at hQR ⊢
    exact ⟨hQR, hR⟩
  | j + 1, Q, R, hQR, hR => by
    simp only [newtonDivBlocks]
    have hb0 : 0 < (2 : ℕ) ^ (64 * n) := Nat.two_pow_pos _
    set blk := (U >>> (64 * (n * j))).modPow2 (64 * n) with hblk
    have hblk_val : blk.toNat = U.toNat / 2 ^ (64 * (n * j)) % 2 ^ (64 * n) := by
      rw [toNat_modPow2, toNat_shr_pow]
    have hblk_lt : blk.toNat < 2 ^ (64 * n) := by rw [hblk_val]; exact Nat.mod_lt _ hb0
    set A := (R <<< (64 * n)) + blk with hAdef
    have hA_val : A.toNat = R.toNat * 2 ^ (64 * n) + blk.toNat := by
      rw [toNat_add, toNat_shl_pow]
    have hA_lt : A.toNat < V.toNat * 2 ^ (64 * n) := by
      rw [hA_val]
      have : (R.toNat + 1) * 2 ^ (64 * n) ≤ V.toNat * 2 ^ (64 * n) :=
        Nat.mul_le_mul_right _ hR
      have e : (R.toNat + 1) * 2 ^ (64 * n) = R.toNat * 2 ^ (64 * n) + 2 ^ (64 * n) := by ring
      omega
    obtain ⟨hq1, hq2⟩ := barrettStep_toNat sp hsp V X n hV1 hV2 hX1 hX2 A hA_lt
    apply newtonDivBlocks_spec sp hsp V X n hV1 hV2 hX1 hX2 U j _ _ _ hq2
    rw [toNat_add, toNat_shl_pow]
    have hdiv : U.toNat / 2 ^ (64 * (n * (j + 1)))
        = U.toNat / 2 ^ (64 * (n * j)) / 2 ^ (64 * n) := by
      rw [show 64 * (n * (j + 1)) = 64 * (n * j) + 64 * n by ring, pow_add,
        Nat.div_div_eq_div_mul]
    have hsplit := Nat.div_add_mod (U.toNat / 2 ^ (64 * (n * j))) (2 ^ (64 * n))
    rw [hdiv] at hQR
    calc (Q.toNat * 2 ^ (64 * n) + (barrettStep sp V X n A).1.toNat) * V.toNat
          + (barrettStep sp V X n A).2.toNat
        = (Q.toNat * V.toNat) * 2 ^ (64 * n)
          + ((barrettStep sp V X n A).1.toNat * V.toNat + (barrettStep sp V X n A).2.toNat) := by
          ring
      _ = (Q.toNat * V.toNat) * 2 ^ (64 * n) + A.toNat := by rw [hq1]
      _ = (Q.toNat * V.toNat + R.toNat) * 2 ^ (64 * n) + blk.toNat := by rw [hA_val]; ring
      _ = 2 ^ (64 * n) * (U.toNat / 2 ^ (64 * (n * j)) / 2 ^ (64 * n))
          + U.toNat / 2 ^ (64 * (n * j)) % 2 ^ (64 * n) := by rw [hQR, hblk_val]; ring
      _ = U.toNat / 2 ^ (64 * (n * j)) := hsplit

/-! ### Barrett's step with cached transforms -/

theorem barrettStepFFT_toNat (V X : AzNat) (n : Nat) (hV1 : 2 ^ (64 * n) ≤ 2 * V.toNat)
    (hV2 : V.toNat < 2 ^ (64 * n)) (hX1 : V.toNat * X.toNat < 2 ^ (128 * n))
    (hX2 : 2 ^ (128 * n) < V.toNat * (X.toNat + 2)) (A : AzNat)
    (hA : A.toNat < V.toNat * 2 ^ (64 * n)) :
    (barrettStepFFT (mkBarrettCache n V X) V n A).1.toNat * V.toNat
        + (barrettStepFFT (mkBarrettCache n V X) V n A).2.toNat = A.toNat ∧
      (barrettStepFFT (mkBarrettCache n V X) V n A).2.toNat < V.toNat := by
  have hb0 : 0 < (2 : ℕ) ^ (64 * n) := Nat.two_pow_pos _
  have hV0 : 0 < V.toNat := by omega
  have hbb : (2 : ℕ) ^ (128 * n) = 2 ^ (64 * n) * 2 ^ (64 * n) := by
    rw [← pow_add]; congr 1; omega
  set b := (2 : ℕ) ^ (64 * n) with hb
  have hA1lt : A.toNat / b < b := by
    rw [Nat.div_lt_iff_lt_mul hb0]
    calc A.toNat < V.toNat * b := hA
      _ ≤ b * b := Nat.mul_le_mul_right _ hV2.le
  have hX_lt : X.toNat < 2 * b := by
    have h1 : X.toNat * b ≤ X.toNat * (2 * V.toNat) := Nat.mul_le_mul_left _ hV1
    have h2 : X.toNat * (2 * V.toNat) = 2 * (V.toNat * X.toNat) := by ring
    have : X.toNat * b < 2 * b * b := by
      calc X.toNat * b ≤ 2 * (V.toNat * X.toNat) := h1.trans_eq h2
        _ < 2 * 2 ^ (128 * n) := by omega
        _ = 2 * b * b := by rw [hbb]; ring
    exact Nat.lt_of_mul_lt_mul_right this
  have hbounds := barrett_bounds (b := b) (A := A.toNat) (A1 := A.toNat / b) (A0 := A.toNat % b)
    (V := V.toNat) (X := X.toNat) (Q := A.toNat / b * X.toNat / b)
    (by rw [mul_comm, Nat.div_add_mod]) (Nat.mod_lt _ hb0) hA1lt hV1 hV2
    (by rw [← hbb]; exact hX1) (by rw [← hbb]; exact hX2) rfl
  obtain ⟨hQV, hAQ⟩ := hbounds
  -- the plans
  have hfull : 64 * (2 * n + 1) ≤ (SSPlan.ofLimbs (2 * n + 1)).bits := SSPlan.ofLimbs_bits _
  have hmodp : 64 * (n + 1) ≤ (SSPlan.ofLimbs (n + 1)).bits := SSPlan.ofLimbs_bits _
  have hpow_full : 2 * b * b ≤ 2 ^ (SSPlan.ofLimbs (2 * n + 1)).bits := by
    calc 2 * b * b ≤ 2 ^ 64 * (b * b) := by
          have : (2 : ℕ) ≤ 2 ^ 64 := by norm_num
          calc 2 * b * b = 2 * (b * b) := by ring
            _ ≤ 2 ^ 64 * (b * b) := Nat.mul_le_mul_right _ this
      _ = 2 ^ (64 * (2 * n + 1)) := by rw [hb, ← pow_add, ← pow_add]; congr 1; ring
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hfull
  have hpow_modp : 8 * b ≤ 2 ^ (SSPlan.ofLimbs (n + 1)).bits := by
    calc 8 * b ≤ 2 ^ 64 * b := Nat.mul_le_mul_right _ (by norm_num)
      _ = 2 ^ (64 * (n + 1)) := by rw [hb, ← pow_add]; congr 1; ring
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hmodp
  set c := mkBarrettCache n V X with hc
  have hpf : 2 * b * b ≤ 2 ^ c.full.bits := hpow_full
  have hpm : 8 * b ≤ 2 ^ c.modp.bits := hpow_modp
  have hb3 : b ≤ 2 * b * b := by nlinarith [hb0]
  have hb4 : 2 * b ≤ 2 * b * b := by nlinarith [hb0]
  -- the quotient
  have hQ : (barrettQuotientFFT c n A).toNat = A.toNat / b * X.toNat / b := by
    unfold barrettQuotientFFT
    have hP : (c.full.mulModF (· * ·) c.fX c.hfX (A >>> (64 * n))).val.toNat
        = (X.toNat * (A >>> (64 * n)).toNat) % (2 ^ c.full.bits + 1) :=
      SSPlan.mulModF_transform_toNat c.full (· * ·) (fun x y => toNat_mul x y) X (A >>> (64 * n))
        (lt_of_lt_of_le hX_lt (hb4.trans hpf))
        (by rw [toNat_shr_pow]; exact lt_of_lt_of_le hA1lt (hb3.trans hpf))
    rw [toNat_shr_pow, hP, toNat_shr_pow, mul_comm X.toNat]
    congr 1
    apply Nat.mod_eq_of_lt
    have : A.toNat / b * X.toNat < b * (2 * b) := Nat.mul_lt_mul'' hA1lt hX_lt
    calc A.toNat / b * X.toNat < b * (2 * b) := this
      _ = 2 * b * b := by ring
      _ ≤ 2 ^ c.full.bits := hpf
      _ ≤ 2 ^ c.full.bits + 1 := Nat.le_succ _
  -- the remainder
  have hR : (barrettRemainderFFT c A (barrettQuotientFFT c n A)).toNat
      = A.toNat - A.toNat / b * X.toNat / b * V.toNat := by
    unfold barrettRemainderFFT
    set Q := barrettQuotientFFT c n A with hQdef
    have hQlt : Q.toNat < 2 * b := by
      rw [hQ]
      have : A.toNat / b * X.toNat < b * (2 * b) := Nat.mul_lt_mul'' hA1lt hX_lt
      have e : b * (2 * b) = 2 * b * b := by ring
      rw [Nat.div_lt_iff_lt_mul hb0]; omega
    have hT : (c.modp.mulModF (· * ·) c.fV c.hfV Q).val.toNat
        = (V.toNat * Q.toNat) % (2 ^ c.modp.bits + 1) :=
      SSPlan.mulModF_transform_toNat c.modp (· * ·) (fun x y => toNat_mul x y) V Q
        (lt_of_lt_of_le hV2 ((Nat.le_mul_of_pos_left b (by norm_num : 0 < 8)).trans hpm))
        (lt_of_lt_of_le hQlt ((Nat.mul_le_mul_right b (by norm_num : 2 ≤ 8)).trans hpm))
    have hQV' : Q.toNat * V.toNat ≤ A.toNat := by rw [hQ]; exact hQV
    have hz : toZMod (AzFermat.sub (AzFermat.ofAzNat c.modp.bits A)
        (c.modp.mulModF (· * ·) c.fV c.hfV Q))
        = ((A.toNat - Q.toNat * V.toNat : ℕ) : ZMod (2 ^ c.modp.bits + 1)) := by
      rw [toZMod_sub', toZMod_ofAzNat, toZMod_eq_natCast, hT, ZMod.natCast_mod, Nat.cast_sub hQV',
        Nat.cast_mul, Nat.cast_mul, mul_comm (V.toNat : ZMod _)]
    have hlt : A.toNat - Q.toNat * V.toNat < 2 ^ c.modp.bits + 1 := by
      have : A.toNat - Q.toNat * V.toNat < 5 * V.toNat := by
        rw [hQ]
        have e : V.toNat * (A.toNat / b * X.toNat / b + 5)
            = A.toNat / b * X.toNat / b * V.toNat + 5 * V.toNat := by ring
        omega
      calc A.toNat - Q.toNat * V.toNat < 5 * V.toNat := this
        _ ≤ 5 * b := Nat.mul_le_mul_left 5 hV2.le
        _ ≤ 8 * b := Nat.mul_le_mul_right b (by norm_num)
        _ ≤ 2 ^ c.modp.bits := hpm
        _ ≤ 2 ^ c.modp.bits + 1 := Nat.le_succ _
    rw [← toZMod_val, hz, ZMod.val_natCast, Nat.mod_eq_of_lt hlt, hQ]
  unfold barrettStepFFT
  simp only
  apply barrettCorrect_spec V hV0 A.toNat 5 _ _
  · rw [hQ, hR]; omega
  · rw [hR]
    have : V.toNat * (A.toNat / b * X.toNat / b + 5) = A.toNat / b * X.toNat / b * V.toNat
        + 5 * V.toNat := by ring
    omega

theorem newtonDivBlocksFFT_spec (V X : AzNat) (n : Nat) (hV1 : 2 ^ (64 * n) ≤ 2 * V.toNat)
    (hV2 : V.toNat < 2 ^ (64 * n)) (hX1 : V.toNat * X.toNat < 2 ^ (128 * n))
    (hX2 : 2 ^ (128 * n) < V.toNat * (X.toNat + 2)) (U : AzNat) :
    ∀ (j : Nat) (Q R : AzNat), Q.toNat * V.toNat + R.toNat = U.toNat / 2 ^ (64 * (n * j)) →
      R.toNat < V.toNat →
      (newtonDivBlocksFFT (mkBarrettCache n V X) V n U j Q R).1.toNat * V.toNat
          + (newtonDivBlocksFFT (mkBarrettCache n V X) V n U j Q R).2.toNat = U.toNat ∧
        (newtonDivBlocksFFT (mkBarrettCache n V X) V n U j Q R).2.toNat < V.toNat
  | 0, Q, R, hQR, hR => by
    simp only [newtonDivBlocksFFT, mul_zero, pow_zero, Nat.div_one] at hQR ⊢
    exact ⟨hQR, hR⟩
  | j + 1, Q, R, hQR, hR => by
    simp only [newtonDivBlocksFFT]
    have hb0 : 0 < (2 : ℕ) ^ (64 * n) := Nat.two_pow_pos _
    set blk := (U >>> (64 * (n * j))).modPow2 (64 * n) with hblk
    have hblk_val : blk.toNat = U.toNat / 2 ^ (64 * (n * j)) % 2 ^ (64 * n) := by
      rw [toNat_modPow2, toNat_shr_pow]
    have hblk_lt : blk.toNat < 2 ^ (64 * n) := by rw [hblk_val]; exact Nat.mod_lt _ hb0
    set A := (R <<< (64 * n)) + blk with hAdef
    have hA_val : A.toNat = R.toNat * 2 ^ (64 * n) + blk.toNat := by
      rw [toNat_add, toNat_shl_pow]
    have hA_lt : A.toNat < V.toNat * 2 ^ (64 * n) := by
      rw [hA_val]
      have : (R.toNat + 1) * 2 ^ (64 * n) ≤ V.toNat * 2 ^ (64 * n) :=
        Nat.mul_le_mul_right _ hR
      have e : (R.toNat + 1) * 2 ^ (64 * n) = R.toNat * 2 ^ (64 * n) + 2 ^ (64 * n) := by ring
      omega
    obtain ⟨hq1, hq2⟩ := barrettStepFFT_toNat V X n hV1 hV2 hX1 hX2 A hA_lt
    set qr := barrettStepFFT (mkBarrettCache n V X) V n A with hqr
    apply newtonDivBlocksFFT_spec V X n hV1 hV2 hX1 hX2 U j _ _ _ hq2
    rw [toNat_add, toNat_shl_pow]
    have hdiv : U.toNat / 2 ^ (64 * (n * (j + 1)))
        = U.toNat / 2 ^ (64 * (n * j)) / 2 ^ (64 * n) := by
      rw [Nat.div_div_eq_div_mul, ← pow_add]; congr 2; ring
    have hsplit := Nat.div_add_mod (U.toNat / 2 ^ (64 * (n * j))) (2 ^ (64 * n))
    rw [hdiv] at hQR
    calc (Q.toNat * 2 ^ (64 * n) + qr.1.toNat) * V.toNat + qr.2.toNat
        = (Q.toNat * V.toNat) * 2 ^ (64 * n) + (qr.1.toNat * V.toNat + qr.2.toNat) := by ring
      _ = (Q.toNat * V.toNat) * 2 ^ (64 * n) + A.toNat := by rw [hq1]
      _ = (Q.toNat * V.toNat + R.toNat) * 2 ^ (64 * n) + blk.toNat := by rw [hA_val]; ring
      _ = 2 ^ (64 * n) * (U.toNat / 2 ^ (64 * (n * j)) / 2 ^ (64 * n))
          + U.toNat / 2 ^ (64 * (n * j)) % 2 ^ (64 * n) := by rw [hQR, hblk_val]; ring
      _ = U.toNat / 2 ^ (64 * (n * j)) := hsplit

theorem newtonDivBlocksDispatch_spec (sp fftFrom : Nat) (hsp : 3 ≤ sp) (V X : AzNat) (n : Nat)
    (hV1 : 2 ^ (64 * n) ≤ 2 * V.toNat) (hV2 : V.toNat < 2 ^ (64 * n))
    (hX1 : V.toNat * X.toNat < 2 ^ (128 * n)) (hX2 : 2 ^ (128 * n) < V.toNat * (X.toNat + 2))
    (U : AzNat) (j : Nat) (hU : U.toNat / 2 ^ (64 * (n * j)) = 0) :
    (newtonDivBlocksDispatch sp fftFrom V X n U j).1.toNat * V.toNat
        + (newtonDivBlocksDispatch sp fftFrom V X n U j).2.toNat = U.toNat ∧
      (newtonDivBlocksDispatch sp fftFrom V X n U j).2.toNat < V.toNat := by
  have hV0 : 0 < V.toNat := by have := Nat.two_pow_pos (64 * n); omega
  unfold newtonDivBlocksDispatch
  split_ifs
  · exact newtonDivBlocksFFT_spec V X n hV1 hV2 hX1 hX2 U j 0 0 (by simp [hU]) (by simp; omega)
  · exact newtonDivBlocks_spec sp hsp V X n hV1 hV2 hX1 hX2 U j 0 0 (by simp [hU]) (by simp; omega)

/-- **Newton–Barrett division is correct**: `Q V + R = U` and `R < V` (for `V ≠ 0`). -/
theorem divModNewton_toNat (base fftFrom sp : Nat) (hbase : 2 ≤ base) (hsp : 3 ≤ sp)
    (U V : AzNat) :
    (divModNewton base fftFrom sp U V).1.toNat * V.toNat
        + (divModNewton base fftFrom sp U V).2.toNat = U.toNat ∧
      (V.toNat ≠ 0 → (divModNewton base fftFrom sp U V).2.toNat < V.toNat) := by
  unfold divModNewton
  split_ifs with h0
  · have hV : V.toNat = 0 := (toNat_eq_zero_iff V).mpr h0
    simp only [toNat_zero, zero_mul, zero_add, true_and]
    intro h; exact absurd hV h
  · have hVpos : 0 < V.limbs.size := Nat.pos_of_ne_zero h0
    have hV0 : 0 < V.toNat := by
      have := toNat_pos_of_size_pos V hVpos
      have : 0 < 2 ^ (64 * (V.limbs.size - 1)) := Nat.two_pow_pos _
      omega
    have hs_nat : V.size = V.toNat.size := (size_toNat V).symm
    have hs_pos : 0 < V.toNat.size := Nat.size_pos.mpr hV0
    have hs_le : V.size ≤ 64 * V.limbs.size := by
      rw [hs_nat]; exact Nat.size_le.mpr (toNat_lt_pow V)
    have hlow : 2 ^ (V.size - 1) ≤ V.toNat := by
      rw [hs_nat]; exact Nat.lt_size.mp (by omega)
    have hhigh : V.toNat < 2 ^ V.size := by rw [hs_nat]; exact Nat.lt_size_self _
    set n := V.limbs.size with hn
    set s := V.size with hs
    set k := 64 * n - s with hk
    have hV'_val : (V <<< k).toNat = V.toNat * 2 ^ k := toNat_shl_pow V k
    have hV'1 : 2 ^ (64 * n) ≤ 2 * (V <<< k).toNat := by
      rw [hV'_val]
      have : 2 ^ (64 * n) = 2 * 2 ^ (s - 1) * 2 ^ k := by
        rw [mul_assoc, ← pow_add, ← pow_succ']; congr 1; omega
      rw [this]
      have h1 : 2 ^ (s - 1) * 2 ^ k ≤ V.toNat * 2 ^ k := Nat.mul_le_mul_right _ hlow
      linarith
    have hV'2 : (V <<< k).toNat < 2 ^ (64 * n) := by
      rw [hV'_val]
      have : 2 ^ (64 * n) = 2 ^ s * 2 ^ k := by rw [← pow_add]; congr 1; omega
      rw [this]
      exact Nat.mul_lt_mul_of_pos_right hhigh (Nat.two_pow_pos _)
    obtain ⟨hX1, hX2⟩ := approxReciprocal_spec base fftFrom hbase (V <<< k) n hV'1 hV'2
    set X := approxReciprocal base fftFrom (V <<< k) n with hX
    set U' := U <<< k with hU'
    have hU'_val : U'.toNat = U.toNat * 2 ^ k := toNat_shl_pow U k
    set j := (U'.limbs.size + n - 1) / n with hj
    have hj_ge : U'.limbs.size ≤ n * j := by
      rw [hj]
      have := Nat.div_add_mod (U'.limbs.size + n - 1) n
      have hm := Nat.mod_lt (U'.limbs.size + n - 1) hVpos
      omega
    have hU'_top : U'.toNat / 2 ^ (64 * (n * j)) = 0 := by
      apply Nat.div_eq_of_lt
      calc U'.toNat < 2 ^ (64 * U'.limbs.size) := toNat_lt_pow U'
        _ ≤ 2 ^ (64 * (n * j)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    obtain ⟨hq1, hq2⟩ := newtonDivBlocksDispatch_spec sp fftFrom hsp (V <<< k) X n hV'1 hV'2 hX1
      hX2 U' j hU'_top
    set qr := newtonDivBlocksDispatch sp fftFrom (V <<< k) X n U' j with hqr
    rw [hV'_val, hU'_val] at hq1
    rw [hV'_val] at hq2
    have hk0 : 0 < (2 : ℕ) ^ k := Nat.two_pow_pos _
    -- `R' = (U − Q V) 2^k`
    have hQV : qr.1.toNat * V.toNat ≤ U.toNat := by
      have : qr.1.toNat * V.toNat * 2 ^ k ≤ U.toNat * 2 ^ k := by
        have e : qr.1.toNat * (V.toNat * 2 ^ k) = qr.1.toNat * V.toNat * 2 ^ k := by ring
        omega
      exact Nat.le_of_mul_le_mul_right this hk0
    have hR' : qr.2.toNat = (U.toNat - qr.1.toNat * V.toNat) * 2 ^ k := by
      rw [Nat.sub_mul, mul_assoc]
      exact Nat.eq_sub_of_add_eq' hq1
    have hR_val : (qr.2 >>> k).toNat = U.toNat - qr.1.toNat * V.toNat := by
      rw [toNat_shr_pow, hR', Nat.mul_div_cancel _ hk0]
    refine ⟨?_, fun _ => ?_⟩
    · rw [hR_val]; exact Nat.add_sub_cancel' hQV
    · rw [hR_val]
      rw [hR'] at hq2
      exact Nat.lt_of_mul_lt_mul_right hq2

end Azurite.AzNat
