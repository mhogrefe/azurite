/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.PolygammaRatBracket
import Azurite.AzFloat.Equiv.PolygammaCertificate
import Azurite.AzFloat.Equiv.GammaRatBracket
import Azurite.AzFloat.Equiv.GammaRat
import Azurite.AzFloat.Equiv.PowRat
import Azurite.AzFloat.Equiv.RatPowRat
import Azurite.AzRat.Equiv.Round
import Azurite.Rounding.Int

/-!
# The polygamma functions of a rational: convergence and the Ziv certificate

* `polygammaRatNegEncl_spec`, `polygammaRatEncl_spec`: the enclosures.
* `polygammaRatEncl_conv`, `polygammaRatApprox_bracketConv`: the bracket converges.
* `irrational_polygamma_of_ratSpecial`, `polygammaRatApprox_cert`: for an odd `n`, at a
  positive integer or a rational of denominator `2`, the value is irrational and Ziv's loop
  terminates.
-/

namespace Azurite.AzFloat

open Filter Topology

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

/-- **The bracket of `(−1)ⁿ⁺¹ ψ⁽ⁿ⁾(q)` converges at a negative rational that is not an
integer.** -/
theorem polygammaRatNegEncl_conv {n : ℕ} (hn : 1 ≤ n) (q : AzRat)
    (hlt : ((AzRat.toRat q : ℚ) : ℝ) < 0)
    (hni : ∀ k : ℤ, ((AzRat.toRat q : ℚ) : ℝ) ≠ k) :
    ∃ E : ℕ → ℝ, Tendsto E atTop (𝓝 0) ∧ ∀ᶠ w in atTop, ∃ H : Encl,
      polygammaRatNegEncl n q w = some H ∧
      AEncl H ((-1) ^ (n + 1) * polygammaR n ((AzRat.toRat q : ℚ) : ℝ)) (E w) := by
  obtain ⟨k, hkdef⟩ : ∃ k : AzInt, k = (q.round .Floor).1 := ⟨_, rfl⟩
  have hk : (k.toInt : ℝ) = (⌊((AzRat.toRat q : ℚ) : ℝ)⌋ : ℝ) := by
    have h := AzRat.toInt_round q .Floor
    rw [← hkdef] at h
    have e : (RoundingTarget.round RoundingTarget.intSet .Floor ((AzRat.toRat q : ℚ) : ℝ)).val
        = (RoundingTarget.roundFloor RoundingTarget.intSet ((AzRat.toRat q : ℚ) : ℝ)).val := rfl
    rw [e, RoundingTarget.val_roundFloor_intSet, EReal.coe_eq_coe_iff] at h
    exact h
  have hfl1 := Int.floor_le ((AzRat.toRat q : ℚ) : ℝ)
  have hfl2 := Int.lt_floor_add_one ((AzRat.toRat q : ℚ) : ℝ)
  have hflne : (⌊((AzRat.toRat q : ℚ) : ℝ)⌋ : ℝ) ≠ ((AzRat.toRat q : ℚ) : ℝ) :=
    fun h => hni _ h.symm
  have hfllt : (⌊((AzRat.toRat q : ℚ) : ℝ)⌋ : ℝ) < ((AzRat.toRat q : ℚ) : ℝ) :=
    lt_of_le_of_ne hfl1 hflne
  have hkneg : k.toInt < 0 := by
    have : (k.toInt : ℝ) < 0 := by rw [hk]; linarith
    exact_mod_cast this
  have hks : k.sign = false := by
    by_contra hs
    have := (AzInt.sign_eq_true_iff k).mp (by simpa using hs)
    omega
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = k.abs.toNat := ⟨_, rfl⟩
  have hmR : (m : ℝ) = -(k.toInt : ℝ) := by
    have h1 := AzInt.abs_toNat_eq k
    rw [abs_of_neg hkneg, ← hm] at h1
    exact_mod_cast h1
  have hm1 : 1 ≤ m := by
    have : (0 : ℝ) < m := by rw [hmR]; exact_mod_cast neg_pos.mpr hkneg
    exact_mod_cast this
  have hu : ((AzRat.toRat (q - k.toAzRat) : ℚ) : ℝ) = ((AzRat.toRat q : ℚ) : ℝ) + (m : ℕ) := by
    rw [AzRat.toRat_sub, AzRat.toRat_toAzRat_int]
    push_cast
    rw [hmR]
    ring
  have hu0 : 0 < ((AzRat.toRat q : ℚ) : ℝ) + (m : ℕ) := by rw [hmR, hk]; linarith
  have hu1 : ((AzRat.toRat q : ℚ) : ℝ) + (m : ℕ) < 1 := by rw [hmR, hk]; linarith
  have ha₂ : ((AzRat.toRat (1 - (q - k.toAzRat)) : ℚ) : ℝ)
      = 1 - ((AzRat.toRat q : ℚ) : ℝ) - (m : ℕ) := by
    rw [AzRat.toRat_sub, AzRat.toRat_one]
    push_cast
    rw [hu]
    ring
  have ha₂0 : 0 < 1 - ((AzRat.toRat q : ℚ) : ℝ) - (m : ℕ) := by linarith
  have hnum : ∀ r : AzRat, 0 < ((AzRat.toRat r : ℚ) : ℝ) → r.num ≠ 0 ∧ r.sign = true := by
    intro r hr
    have h0 : r.num ≠ 0 := fun h => by
      rw [coe_toRat_eq_zero_of_num_eq_zero r h] at hr
      exact lt_irrefl _ hr
    exact ⟨h0, (toRat_sign_iff r h0).mpr hr⟩
  obtain ⟨hun, hus⟩ := hnum _ (by rw [hu]; exact hu0)
  obtain ⟨han, has⟩ := hnum _ (by rw [ha₂]; exact ha₂0)
  obtain ⟨E, hE, hev⟩ := polyNegCore_conv hn hu0 ha₂0 hm1
  refine ⟨E, hE, ?_⟩
  filter_upwards [hev, eventually_ge_atTop (4 * m + 64)] with w hcore hw
  have hw64 : 64 ≤ w := by omega
  have hsmall : m ≤ 2 ^ lnGammaShiftExp w := by
    have := (two_pow_shiftExp (by omega : 4 ≤ w)).2
    omega
  have hVw : w ≤ polyWork n w := by unfold polyWork; omega
  have hlam : 6 * (1 / 2 : ℝ) ^ (polyWork n w + 32) ≤ 8 * (1 / 2 : ℝ) ^ w := by
    have : (1 / 2 : ℝ) ^ (polyWork n w + 32) ≤ (1 / 2 : ℝ) ^ w :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have h0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
    linarith
  have hUL := lnGammaRatEncl_L (q - k.toAzRat) (by rw [hu]; exact hu0) (polyWork n w)
  have hAL := lnGammaRatEncl_L (1 - (q - k.toAzRat)) (by rw [ha₂]; exact ha₂0) (polyWork n w)
  rw [hu] at hUL
  rw [ha₂] at hAL
  obtain ⟨v, hv⟩ := hcore _ _ _ _ hUL (by positivity) hlam hAL (by positivity) hlam
  have hsome : polygammaRatNegEncl n q w = some
      (if n % 2 = 1 then Encl.add (w + 32)
          (polygammaPosEncl n (lnGammaRatEncl (q - k.toAzRat) (polyWork n w)) w)
          (Encl.mul (polyWork n w) (Encl.exact (ofAzNat (AzNat.factorial n)))
            (polyShiftSum (polyWork n w)
              (lnGammaRatEncl (1 - (q - k.toAzRat)) (polyWork n w)) n m))
        else Encl.sub (w + 32)
          (polygammaPosEncl n (lnGammaRatEncl (q - k.toAzRat) (polyWork n w)) w)
          (Encl.mul (polyWork n w) (Encl.exact (ofAzNat (AzNat.factorial n)))
            (polyShiftSum (polyWork n w)
              (lnGammaRatEncl (1 - (q - k.toAzRat)) (polyWork n w)) n m))) := by
    unfold polygammaRatNegEncl
    dsimp only
    rw [← hkdef, ← hm, ite_eq_left ⟨hks, hun, hus, han, has⟩, ite_eq_left hsmall]
  exact ⟨_, hsome, hv.of_isEncl (polygammaRatNegEncl_spec hn q hlt hni hw64 hsome)⟩

/-- **The enclosure of `ψ⁽ⁿ⁾(q)` converges** at every rational that is positive (`pos`) or
negative and not an integer. -/
theorem polygammaRatEncl_conv {n : ℕ} (hn : 1 ≤ n) (q : AzRat) {pos : Bool}
    (hpos : pos = true → 0 < ((AzRat.toRat q : ℚ) : ℝ))
    (hneg : pos = false → ((AzRat.toRat q : ℚ) : ℝ) < 0 ∧
      ∀ k : ℤ, ((AzRat.toRat q : ℚ) : ℝ) ≠ k) :
    ∃ E : ℕ → ℝ, Tendsto E atTop (𝓝 0) ∧ ∀ᶠ w in atTop, ∃ En : Encl,
      polygammaRatEncl n q pos w = some En ∧
      AEncl En (polygammaR n ((AzRat.toRat q : ℚ) : ℝ)) (E w) := by
  have key : ∃ E : ℕ → ℝ, Tendsto E atTop (𝓝 0) ∧ ∀ᶠ w in atTop, ∃ H : Encl,
      (if pos = true then some (polygammaPosEncl n (lnGammaRatEncl q (polyWork n w)) w)
        else polygammaRatNegEncl n q w) = some H ∧
      AEncl H ((-1) ^ (n + 1) * polygammaR n ((AzRat.toRat q : ℚ) : ℝ)) (E w) := by
    cases pos with
    | true =>
      refine ⟨pgE n ((AzRat.toRat q : ℚ) : ℝ), tendsto_pgE n _, ?_⟩
      filter_upwards [polygammaPosEncl_conv hn (hpos rfl), eventually_ge_atTop 64] with w hw h64
      refine ⟨_, rfl, hw _ _ (lnGammaRatEncl_L q (hpos rfl) (polyWork n w)) (by positivity) ?_⟩
      have hVw : w ≤ polyWork n w := by unfold polyWork; omega
      have : (1 / 2 : ℝ) ^ (polyWork n w + 32) ≤ (1 / 2 : ℝ) ^ w :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      have h0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
      linarith
    | false =>
      obtain ⟨h0, hni⟩ := hneg rfl
      obtain ⟨E, hE, hev⟩ := polygammaRatNegEncl_conv hn q h0 hni
      exact ⟨E, hE, hev.mono fun w ⟨H, hH, hA⟩ => ⟨H, by simpa using hH, hA⟩⟩
  obtain ⟨E, hE, hev⟩ := key
  refine ⟨E, hE, ?_⟩
  filter_upwards [hev, eventually_ge_atTop 64] with w ⟨H, hH, hA⟩ hw
  have hsome : polygammaRatEncl n q pos w
      = some (if n % 2 = 1 then H else Encl.neg H) := by
    unfold polygammaRatEncl
    rw [hH]
    rfl
  refine ⟨_, hsome, ?_⟩
  have hspec := polygammaRatEncl_spec hn q hpos hneg hw hsome
  by_cases ho : n % 2 = 1
  · rw [ite_eq_left ho] at hspec ⊢
    exact hA.of_isEncl hspec
  · rw [ite_eq_right ho] at hspec ⊢
    exact hA.neg.of_isEncl hspec

/-- **The bracket of `ψ⁽ⁿ⁾(q)` converges.** -/
theorem polygammaRatApprox_bracketConv {n : ℕ} (hn : 1 ≤ n) (q : AzRat) {pos : Bool}
    (hpos : pos = true → 0 < ((AzRat.toRat q : ℚ) : ℝ))
    (hneg : pos = false → ((AzRat.toRat q : ℚ) : ℝ) < 0 ∧
      ∀ k : ℤ, ((AzRat.toRat q : ℚ) : ℝ) ≠ k) (p : ℕ) :
    BracketConv (polygammaRatApprox n q pos p) (polygammaR n ((AzRat.toRat q : ℚ) : ℝ)) :=
  lnAbsGammaApproxOf_bracketConv (enclRefine_conv (polygammaRatEncl_conv hn q hpos hneg) p)

/-- **`ψ⁽ⁿ⁾(q)` is irrational at the rationals recognized by `polygammaRatSpecial`**, off
`0` and the poles. -/
theorem irrational_polygamma_of_ratSpecial {n : ℕ} {q : AzRat} (h0 : q.num ≠ 0)
    (hpole : ¬ (q.den = 1 ∧ q.sign = false)) (hc : polygammaRatSpecial n q = true) :
    Irrational (polygammaR n ((AzRat.toRat q : ℚ) : ℝ)) := by
  unfold polygammaRatSpecial at hc
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨hn, hden⟩ := hc
  have hodd := Nat.odd_iff.mpr hn
  have hdenq : (AzRat.toRat q).den = q.den.toNat := rfl
  rcases hden with h1 | h2
  · -- a positive integer
    have hint := coe_toRat_eq_mkNorm_of_den_one q h1
    have hs : q.sign = true := by
      by_contra hs
      exact hpole ⟨h1, by simpa using hs⟩
    have hpos := (toRat_sign_iff q h0).mp hs
    rw [hint] at hpos ⊢
    have hNpos : 0 < (AzInt.mkNorm q.sign q.num).toInt := by exact_mod_cast hpos
    have := irrational_polygammaR_div_two hodd
      (N := 2 * (AzInt.mkNorm q.sign q.num).toInt) (Or.inr (by omega))
    convert this using 2
    push_cast
    ring
  · -- denominator `2`
    have hd2 : (AzRat.toRat q).den = 2 := by rw [hdenq, h2, AzNat.toNat_ofNat]
    have hred := (AzRat.toRat q).reduced
    rw [hd2, Nat.coprime_two_right] at hred
    have hNodd : (AzRat.toRat q).num % 2 = 1 := by
      have := Int.natAbs_odd.mp hred
      exact Int.odd_iff.mp this
    have hval : ((AzRat.toRat q : ℚ) : ℝ) = (((AzRat.toRat q).num : ℤ) : ℝ) / 2 := by
      have := Rat.num_div_den (AzRat.toRat q)
      rw [hd2] at this
      have h3 : ((AzRat.toRat q : ℚ) : ℝ) = ((((AzRat.toRat q).num : ℚ) / (2 : ℕ) : ℚ) : ℝ) := by
        rw [this]
      rw [h3]
      push_cast
      rfl
    rw [hval]
    exact irrational_polygammaR_div_two hodd (Or.inl hNodd)

/-- **The Ziv certificate of `ψ⁽ⁿ⁾(q)` at the rationals recognized by
`polygammaRatSpecial`**: some level `w₀ 2^f` is accepted. -/
theorem polygammaRatApprox_cert {n : ℕ} {q : AzRat} (h0 : q.num ≠ 0)
    (hpole : ¬ (q.den = 1 ∧ q.sign = false)) (hc : polygammaRatSpecial n q = true) (p : ℕ)
    [NeZero p] (mode : RoundingMode) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (polygammaRatApprox n q q.sign p (w₀ * 2 ^ f)).1
      (polygammaRatApprox n q q.sign p (w₀ * 2 ^ f)).2 p mode).isSome = true := by
  have hirr := irrational_polygamma_of_ratSpecial h0 hpole hc
  have hn : n % 2 = 1 := by
    unfold polygammaRatSpecial at hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact hc.1
  have hnp := gammaRat_not_pole h0 hpole
  have hconv := polygammaRatApprox_bracketConv (n := n) (by omega) q (pos := q.sign)
    (fun hs => (toRat_sign_iff q h0).mp hs)
    (fun hs => ⟨toRat_neg_of_sign_false q h0 hs,
      fun k hk => hnp ⟨toRat_neg_of_sign_false q h0 hs, k, hk⟩⟩) p
  exact hconv.exists_isSome hirr.ne_zero p (not_mem_floatSet_of_irrational p hirr) mode w₀ hw₀

end Azurite.AzFloat
