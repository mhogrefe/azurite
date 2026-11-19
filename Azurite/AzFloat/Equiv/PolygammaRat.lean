/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.PolygammaRat
import Azurite.AzFloat.Equiv.Polygamma
import Azurite.AzFloat.Equiv.DigammaRat

/-!
# Equivalence: the polygamma functions of a rational

`polygammaRatPrecRound_eq_or`: `polygammaRatPrecRound n q p mode` is the correct rounding of
`Spec.polygamma n q` (`Equiv/Polygamma.lean`), or `(nan, .eq)` when the fuel of the Ziv loop
runs out.  The steps: `polygammaRatNegEncl_spec`, `polygammaRatEncl_spec`,
`polygammaRatTiny?_eq`.
-/

namespace Azurite.AzFloat

open Real Finset Nat

/-- **`polygammaRatNegEncl n q w` encloses `(−1)ⁿ⁺¹ ψ⁽ⁿ⁾(q)`** for a rational `q < 0` that is
not an integer. -/
theorem polygammaRatNegEncl_spec {n : ℕ} (hn : 1 ≤ n) (q : AzRat)
    (hlt : ((AzRat.toRat q : ℚ) : ℝ) < 0) (hni : ∀ k : ℤ, ((AzRat.toRat q : ℚ) : ℝ) ≠ k)
    {w : ℕ} (hw : 64 ≤ w) {H : Encl} (h : polygammaRatNegEncl n q w = some H) :
    IsEncl H ((-1) ^ (n + 1) * polygammaR n ((AzRat.toRat q : ℚ) : ℝ)) := by
  unfold polygammaRatNegEncl at h
  dsimp only at h
  generalize (q.round .Floor).1 = k at h
  set xv := ((AzRat.toRat q : ℚ) : ℝ) with hxv
  set m := k.abs.toNat with hm
  by_cases hc : k.sign = false ∧ (q - k.toAzRat).num ≠ 0 ∧ (q - k.toAzRat).sign = true
      ∧ (1 - (q - k.toAzRat)).num ≠ 0 ∧ (1 - (q - k.toAzRat)).sign = true
  swap
  · rw [ite_eq_right hc] at h
    exact absurd h (by simp)
  rw [ite_eq_left hc] at h
  obtain ⟨hks, hu0, hus, ha0, has⟩ := hc
  have hk : (k.toInt : ℝ) = -(m : ℝ) := by
    have htoInt : k.toInt = if k.sign then (k.abs.toNat : ℤ) else -(k.abs.toNat : ℤ) := rfl
    rw [htoInt, hks]
    simp [hm]
  have hu : ((AzRat.toRat (q - k.toAzRat) : ℚ) : ℝ) = xv + (m : ℕ) := by
    rw [AzRat.toRat_sub, AzRat.toRat_toAzRat_int]
    push_cast
    rw [hk]
    ring
  have ha₂ : ((AzRat.toRat (1 - (q - k.toAzRat)) : ℚ) : ℝ) = 1 - xv - (m : ℕ) := by
    rw [AzRat.toRat_sub, AzRat.toRat_one]
    push_cast
    rw [hu]
    ring
  have ha₁ : ((AzRat.toRat (1 - q) : ℚ) : ℝ) = 1 - xv := by
    rw [AzRat.toRat_sub, AzRat.toRat_one]
    push_cast
    rfl
  obtain ⟨hV, h32⟩ := polyWork_bounds hn hw
  have : NeZero (polyWork n w) := ⟨by omega⟩
  have : NeZero (w + 32) := ⟨by omega⟩
  have hU := lnGammaRatEncl_spec _ ((toRat_sign_iff _ hu0).mp hus) (polyWork n w)
  have hA₂ := lnGammaRatEncl_spec _ ((toRat_sign_iff _ ha0).mp has) (polyWork n w)
  have hA₁ := lnGammaRatEncl_spec (1 - q) (by rw [ha₁]; linarith) (polyWork n w)
  rw [hu] at hU
  rw [ha₂] at hA₂
  rw [ha₁] at hA₁
  have hGu := polygammaPosEncl_spec hn hU hw
  by_cases hsmall : m ≤ 2 ^ lnGammaShiftExp w
  · rw [ite_eq_left hsmall, Option.some.injEq] at h
    subst h
    have hT := ((isEncl0_ofAzNat (AzNat.factorial n)).mul (w := polyWork n w)
      (polyShiftSum_spec (by omega) h32 hA₂ m)).encloses
    rw [AzNat.toNat_factorial] at hT
    have hid := polygammaR_neg_sum hn hni m
    by_cases ho : n % 2 = 1
    · rw [ite_eq_left ho]
      have := hGu.add (w := w + 32) hT
      convert this using 1
      rw [hid, (Nat.even_iff.mpr (by omega : (n + 1) % 2 = 0)).neg_one_pow]
      ring
    · rw [ite_eq_right ho]
      have := hGu.sub (w := w + 32) hT
      convert this using 1
      rw [hid, (Nat.odd_iff.mpr (by omega : (n + 1) % 2 = 1)).neg_one_pow]
      ring
  · rw [ite_eq_right hsmall, Option.some.injEq] at h
    subst h
    have hG₁ := polygammaPosEncl_spec hn hA₁ hw
    have hG₂ := polygammaPosEncl_spec hn hA₂ hw
    have hD := hG₁.sub (w := w + 32) hG₂
    have hid := polygammaR_reflect hn hni m
    by_cases he : n % 2 = 0
    · rw [ite_eq_left he]
      have := hGu.add (w := w + 32) hD
      convert this using 1
      rw [hid, (Nat.even_iff.mpr he).neg_one_pow]
      ring
    · rw [ite_eq_right he]
      have := hGu.sub (w := w + 32) hD
      convert this using 1
      rw [hid, (Nat.odd_iff.mpr (by omega : n % 2 = 1)).neg_one_pow]
      ring

/-- **`polygammaRatEncl` encloses `ψ⁽ⁿ⁾(q)`**, for `q > 0` (`pos`) or `q < 0` not an integer. -/
theorem polygammaRatEncl_spec {n : ℕ} (hn : 1 ≤ n) (q : AzRat) {pos : Bool}
    (hpos : pos = true → 0 < ((AzRat.toRat q : ℚ) : ℝ))
    (hneg : pos = false → ((AzRat.toRat q : ℚ) : ℝ) < 0 ∧
      ∀ k : ℤ, ((AzRat.toRat q : ℚ) : ℝ) ≠ k) {w : ℕ} (hw : 64 ≤ w) {E : Encl}
    (h : polygammaRatEncl n q pos w = some E) :
    IsEncl E (polygammaR n ((AzRat.toRat q : ℚ) : ℝ)) := by
  unfold polygammaRatEncl at h
  obtain ⟨H, hH, rfl⟩ := Option.map_eq_some_iff.mp h
  have hHv : IsEncl H ((-1) ^ (n + 1) * polygammaR n ((AzRat.toRat q : ℚ) : ℝ)) := by
    cases pos with
    | true =>
      rw [ite_eq_left rfl, Option.some.injEq] at hH
      subst hH
      exact polygammaPosEncl_spec hn (lnGammaRatEncl_spec q (hpos rfl) _) hw
    | false =>
      rw [ite_eq_right (by simp)] at hH
      exact polygammaRatNegEncl_spec hn q (hneg rfl).1 (hneg rfl).2 hw hH
  by_cases ho : n % 2 = 1
  · rw [ite_eq_left ho]
    rwa [(Nat.even_iff.mpr (by omega : (n + 1) % 2 = 0)).neg_one_pow, one_mul] at hHv
  · rw [ite_eq_right ho]
    have := hHv.neg
    rwa [(Nat.odd_iff.mpr (by omega : (n + 1) % 2 = 1)).neg_one_pow, neg_one_mul, neg_neg]
      at this

/-- A tiny rational is at most `1/4` in absolute value. -/
theorem abs_le_quarter_of_polygammaRatIsTiny {n : ℕ} {q : AzRat} {e : AzInt} {p : ℕ}
    (h : polygammaRatIsTiny n q e p = true) : |((AzRat.toRat q : ℚ) : ℝ)| ≤ 1 / 4 := by
  unfold polygammaRatIsTiny at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨-, hC⟩, hF⟩ := h
  obtain ⟨l, hl, hl1, -⟩ := ofAzRatRound_floor_abs q 64
  obtain ⟨c, hc, hc1, -⟩ := ofAzRatRound_ceiling_abs q 64
  have hq : (one <<< AzInt.ofInt (-2)).toVal = some (((1 / 4 : ℝ) : ℝ) : EReal) := by
    rw [toVal_shiftLeft_of_toVal toVal_one' (AzInt.ofInt (-2)), AzInt.toInt_ofInt]
    norm_num
  have hnq : (-(one <<< AzInt.ofInt (-2))).toVal = some (((-(1 / 4) : ℝ) : ℝ) : EReal) := by
    rw [toVal_neg, hq, Option.map_some, EReal.coe_neg]
  have h1 := (le_eq_true_iff hc hq).mp hC
  have h2 := (le_eq_true_iff hnq hl).mp hF
  rw [abs_le]
  constructor <;> linarith

/-- The tiny-argument path of `ψ⁽ⁿ⁾(q)` answers with the rounding of `ψ⁽ⁿ⁾(q)`. -/
theorem polygammaRatTiny?_eq {n : ℕ} (hn : 1 ≤ n) (q : AzRat) (h0 : q.num ≠ 0) (e : AzInt)
    (p : ℕ) [NeZero p] (mode : RoundingMode) {r : AzFloat × Ordering}
    (h : polygammaRatTiny? n q e p mode = some r) :
    r = roundVal p mode (some ((polygammaR n ((AzRat.toRat q : ℚ) : ℝ) : ℝ) : EReal)) := by
  unfold polygammaRatTiny? at h
  by_cases hc : polygammaRatIsTiny n q e p = true
  swap
  · rw [ite_eq_right hc] at h
    exact absurd h (by simp)
  rw [ite_eq_left hc] at h
  have hx0 : ((AzRat.toRat q : ℚ) : ℝ) ≠ 0 := fun h' =>
    h0 ((AzRat.toRat_eq_zero_iff q).mp (by exact_mod_cast h'))
  have hpos : q.sign = true → 0 < ((AzRat.toRat q : ℚ) : ℝ) := (toRat_sign_iff q h0).mp
  have hneg : q.sign = false → ((AzRat.toRat q : ℚ) : ℝ) < 0 := toRat_neg_of_sign_false q h0
  have hXa : IsEnclPos (lnGammaRatEncl (if q.sign then q else -q) (p + zivGuardBits + 8))
      |((AzRat.toRat q : ℚ) : ℝ)| := by
    cases hs : q.sign with
    | true =>
      rw [ite_eq_left rfl, abs_of_pos (hpos hs)]
      exact lnGammaRatEncl_spec q (hpos hs) _
    | false =>
      have hv : ((AzRat.toRat (-q) : ℚ) : ℝ) = -((AzRat.toRat q : ℚ) : ℝ) := by
        rw [AzRat.toRat_neg, Rat.cast_neg]
      rw [ite_eq_right (by simp), abs_of_neg (hneg hs), ← hv]
      exact lnGammaRatEncl_spec (-q) (by rw [hv]; linarith [hneg hs]) _
  exact polygammaTinyOf_eq hn hx0 hXa (abs_le_quarter_of_polygammaRatIsTiny hc) hpos hneg p mode h

/-- **`ψ⁽ⁿ⁾` of a rational is correctly rounded unless the fuel runs out.** -/
theorem polygammaRatPrecRound_eq_or (n : ℕ) (q : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    polygammaRatPrecRound n q p mode
        = roundVal p mode (Spec.polygamma n (((AzRat.toRat q : ℚ) : ℝ) : EReal)) ∨
      polygammaRatPrecRound n q p mode = (nan, .eq) := by
  have hp := NeZero.ne p
  unfold polygammaRatPrecRound
  by_cases hn : n = 0
  · subst hn
    rw [ite_eq_left rfl, Spec.polygamma_zero]
    exact digammaRatPrecRound_eq_or q p mode
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  rw [ite_eq_right hn]
  by_cases h0 : q.num = 0
  · left
    rw [ite_eq_left h0, coe_toRat_eq_zero_of_num_eq_zero q h0, Spec.polygamma_coe_zero hn]
    by_cases ho : n % 2 = 1
    · rw [ite_eq_left ho, roundVal_top]; simp [ho]
    · rw [ite_eq_right ho, roundVal_bot]; simp [ho]
  rw [ite_eq_right h0]
  have hx0 : ((AzRat.toRat q : ℚ) : ℝ) ≠ 0 := fun h' =>
    h0 ((AzRat.toRat_eq_zero_iff q).mp (by exact_mod_cast h'))
  by_cases hpole : q.den = 1 ∧ q.sign = false
  · left
    obtain ⟨hneg, hk⟩ := gammaRat_pole h0 hpole
    rw [ite_eq_left hpole, Spec.polygamma_coe_of_pole hn hneg hk]
    by_cases ho : n % 2 = 1
    · rw [ite_eq_left ho, ite_eq_left ho, roundVal_top]
    · rw [ite_eq_right ho, ite_eq_right ho, roundVal_none]
  have hnp := gammaRat_not_pole h0 hpole
  rw [ite_eq_right hpole, ite_eq_right hp, Spec.polygamma_coe hn hx0 hnp]
  dsimp only
  split
  · rename_i r hr
    left
    exact polygammaRatTiny?_eq hn1 q h0 _ p mode hr
  · rcases eq_or_ne (zivLoop (polygammaRatApprox n q q.sign p) p mode (lnGammaFuel p)
      (polygammaStart n (gammaRatExp q) p)) (nan, .eq) with hz | hz
    · right; exact hz
    · left
      exact zivLoop_eq_of_ne_nan_or_none p mode _ _ 64
        (fun w hw => lnAbsGammaApproxOf_valid_or_none
          (fun _ hc => enclRefine_spec (fun _ hw' _ hE =>
            polygammaRatEncl_spec hn1 q (fun hs => (toRat_sign_iff q h0).mp hs)
              (fun hs => ⟨toRat_neg_of_sign_false q h0 hs,
                fun k hk => hnp ⟨toRat_neg_of_sign_false q h0 hs, k, hk⟩⟩) hw' hE) p hw hc)
          w p mode)
        _ _ (le_max_left _ _) hz

end Azurite.AzFloat
