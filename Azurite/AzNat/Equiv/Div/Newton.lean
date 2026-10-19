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

/-! ### `toNat` of the notations -/

theorem toNat_shl_pow (a : AzNat) (sh : Nat) : (a <<< sh).toNat = a.toNat * 2 ^ sh := by
  rw [toNat_hShiftLeft, Nat.shiftLeft_eq]

theorem toNat_shr_pow (a : AzNat) (sh : Nat) : (a >>> sh).toNat = a.toNat / 2 ^ sh := by
  rw [toNat_hShiftRight, Nat.shiftRight_eq_div_pow]

theorem two_pow_64_mul (k : Nat) : (2 : Nat) ^ (64 * k) = (2 ^ 64) ^ k := pow_mul 2 64 k

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

theorem approxReciprocalFuel_spec (base : Nat) (hbase : 2 ≤ base) :
    ∀ (fuel : Nat) (A : AzNat) (n : Nat), n ≤ fuel + base →
      2 ^ (64 * n) ≤ 2 * A.toNat → A.toNat < 2 ^ (64 * n) →
      A.toNat * (approxReciprocalFuel base fuel A n).toNat < 2 ^ (128 * n) ∧
        2 ^ (128 * n) < A.toNat * ((approxReciprocalFuel base fuel A n).toNat + 2)
  | 0, A, n, _, hA1, hA2 => by
    simp only [approxReciprocalFuel]
    exact reciprocalBase_spec A n hA1 hA2
  | fuel + 1, A, n, hnf, hA1, hA2 => by
    simp only [approxReciprocalFuel]
    split_ifs with hnb
    · exact reciprocalBase_spec A n hA1 hA2
    · push Not at hnb
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
      obtain ⟨hXh1, hXh2⟩ := approxReciprocalFuel_spec base hbase fuel Ah h (by omega) hAh1 hAh2
      set Xh := approxReciprocalFuel base fuel Ah h with hXh
      -- `B = β^(n+h)`, `T₀ = A X_h`
      set B := pow2 (64 * (n + h)) with hB
      have hB_val : B.toNat = 2 ^ (64 * (n + h)) := toNat_pow2 _
      have hB0 : 0 < B.toNat := by rw [hB_val]; exact Nat.two_pow_pos _
      have hT0 : (A * Xh).toNat = A.toNat * Xh.toNat := toNat_mul A Xh
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
      -- `T₀ < B + 4A`
      have hT0_lt : (A * Xh).toNat < B.toNat + 4 * A.toNat := by
        rw [hT0, hB_val, hpow_B]
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
      -- `B < T₀ + 2A`
      have hB_lt : B.toNat < (A * Xh).toNat + 2 * A.toNat := by
        rw [hT0, hB_val, hpow_B]
        have h1 : 2 ^ (128 * h) * 2 ^ (64 * l) < Ah.toNat * (Xh.toNat + 2) * 2 ^ (64 * l) :=
          Nat.mul_lt_mul_of_pos_right hXh2 hpow_l
        have h2 : Ah.toNat * (Xh.toNat + 2) * 2 ^ (64 * l)
            = Ah.toNat * 2 ^ (64 * l) * (Xh.toNat + 2) := by ring
        have h3 : Ah.toNat * 2 ^ (64 * l) * (Xh.toNat + 2) ≤ A.toNat * (Xh.toNat + 2) :=
          Nat.mul_le_mul_right _ hAhl
        have h4 : A.toNat * (Xh.toNat + 2) = A.toNat * Xh.toNat + 2 * A.toNat := by ring
        omega
      -- the correction loop
      obtain ⟨hc1, hc2, hc3, hc4⟩ := reciprocalCorrect_spec A B hA0 hB0 4 Xh (A * Xh) hT0 hT0_lt
      set xt := reciprocalCorrect A B 4 Xh (A * Xh) with hxt
      have hD_lt : B.toNat < xt.2.toNat + 2 * A.toNat := by
        rcases le_or_gt B.toNat (A * Xh).toNat with hle | hlt
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

/-- **MCA Lemma 3.8**: `A X < β^(2n) < A (X + 2)` for `β^n/2 ≤ A < β^n`. -/
theorem approxReciprocal_spec (base : Nat) (hbase : 2 ≤ base) (A : AzNat) (n : Nat)
    (hA1 : 2 ^ (64 * n) ≤ 2 * A.toNat) (hA2 : A.toNat < 2 ^ (64 * n)) :
    A.toNat * (approxReciprocal base A n).toNat < 2 ^ (128 * n) ∧
      2 ^ (128 * n) < A.toNat * ((approxReciprocal base A n).toNat + 2) :=
  approxReciprocalFuel_spec base hbase n A n (by omega) hA1 hA2

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

theorem barrettStep_toNat (V X : AzNat) (n : Nat) (hV1 : 2 ^ (64 * n) ≤ 2 * V.toNat)
    (hV2 : V.toNat < 2 ^ (64 * n)) (hX1 : V.toNat * X.toNat < 2 ^ (128 * n))
    (hX2 : 2 ^ (128 * n) < V.toNat * (X.toNat + 2)) (A : AzNat)
    (hA : A.toNat < V.toNat * 2 ^ (64 * n)) :
    (barrettStep V X n A).1.toNat * V.toNat + (barrettStep V X n A).2.toNat = A.toNat ∧
      (barrettStep V X n A).2.toNat < V.toNat := by
  have hb0 : 0 < (2 : ℕ) ^ (64 * n) := Nat.two_pow_pos _
  have hV0 : 0 < V.toNat := by omega
  have hbb : (2 : ℕ) ^ (128 * n) = 2 ^ (64 * n) * 2 ^ (64 * n) := by
    rw [← pow_add]; congr 1; omega
  set b := (2 : ℕ) ^ (64 * n) with hb
  have hA1lt : A.toNat / b < b := by
    rw [Nat.div_lt_iff_lt_mul hb0]
    calc A.toNat < V.toNat * b := hA
      _ ≤ b * b := Nat.mul_le_mul_right _ hV2.le
  have hbounds := barrett_bounds (b := b) (A := A.toNat) (A1 := A.toNat / b) (A0 := A.toNat % b)
    (V := V.toNat) (X := X.toNat) (Q := A.toNat / b * X.toNat / b)
    (by rw [mul_comm, Nat.div_add_mod]) (Nat.mod_lt _ hb0) hA1lt hV1 hV2
    (by rw [← hbb]; exact hX1) (by rw [← hbb]; exact hX2) rfl
  obtain ⟨hQV, hAQ⟩ := hbounds
  unfold barrettStep
  have hQ_val : (((A >>> (64 * n)) * X) >>> (64 * n)).toNat = A.toNat / b * X.toNat / b := by
    rw [toNat_shr_pow, toNat_mul, toNat_shr_pow]
  have hR_val : (A - (((A >>> (64 * n)) * X) >>> (64 * n)) * V).toNat
      = A.toNat - A.toNat / b * X.toNat / b * V.toNat := by
    rw [toNat_sub, toNat_mul, hQ_val]
  apply barrettCorrect_spec V hV0 A.toNat 5 _ _
  · rw [hQ_val, hR_val]; omega
  · rw [hR_val]
    have : V.toNat * (A.toNat / b * X.toNat / b + 5) = A.toNat / b * X.toNat / b * V.toNat
        + 5 * V.toNat := by ring
    omega

/-! ### The block loop and the normalization -/

theorem newtonDivBlocks_spec (V X : AzNat) (n : Nat) (hV1 : 2 ^ (64 * n) ≤ 2 * V.toNat)
    (hV2 : V.toNat < 2 ^ (64 * n)) (hX1 : V.toNat * X.toNat < 2 ^ (128 * n))
    (hX2 : 2 ^ (128 * n) < V.toNat * (X.toNat + 2)) (U : AzNat) :
    ∀ (j : Nat) (Q R : AzNat), Q.toNat * V.toNat + R.toNat = U.toNat / 2 ^ (64 * (n * j)) →
      R.toNat < V.toNat →
      (newtonDivBlocks V X n U j Q R).1.toNat * V.toNat + (newtonDivBlocks V X n U j Q R).2.toNat
          = U.toNat ∧
        (newtonDivBlocks V X n U j Q R).2.toNat < V.toNat
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
    obtain ⟨hq1, hq2⟩ := barrettStep_toNat V X n hV1 hV2 hX1 hX2 A hA_lt
    set qr := barrettStep V X n A with hqr
    apply newtonDivBlocks_spec V X n hV1 hV2 hX1 hX2 U j _ _ _ hq2
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

/-- **Newton–Barrett division is correct**: `Q V + R = U` and `R < V` (for `V ≠ 0`). -/
theorem divModNewton_toNat (base : Nat) (hbase : 2 ≤ base) (U V : AzNat) :
    (divModNewton base U V).1.toNat * V.toNat + (divModNewton base U V).2.toNat = U.toNat ∧
      (V.toNat ≠ 0 → (divModNewton base U V).2.toNat < V.toNat) := by
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
    obtain ⟨hX1, hX2⟩ := approxReciprocal_spec base hbase (V <<< k) n hV'1 hV'2
    set X := approxReciprocal base (V <<< k) n with hX
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
    obtain ⟨hq1, hq2⟩ := newtonDivBlocks_spec (V <<< k) X n hV'1 hV'2 hX1 hX2 U' j 0 0
      (by simp [hU'_top]) (by rw [toNat_zero]; omega)
    set qr := newtonDivBlocks (V <<< k) X n U' j 0 0 with hqr
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
