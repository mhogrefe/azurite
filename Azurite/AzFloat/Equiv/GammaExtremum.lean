/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.GammaExtremum
import Azurite.AzFloat.Equiv.GammaWidth
import Azurite.AzFloat.Equiv.BetaWidth
import Azurite.AzFloat.Equiv.PochhammerWidth

/-!
# Equivalence: the local extrema of the Gamma function

`gammaExtremumPrecRound n p mode` is the correct rounding of `Γ(psiZeroAt n)`, the value of
`Γ` at the `n`-th real zero of `ψ` (`Transcendental/PsiZero.lean`), or `(nan, .eq)` when the
fuel runs out (`gammaExtremumPrecRound_eq_or`); `gammaExtremumPrecRoundFuel_zivSpec` adds
that every large enough fuel gives the value wherever it is no rounding boundary.

The steps: `psiZeroEnclAt_spec` (the certified search returns an enclosure of the zero of
width `2^(−V)`), the relative widths of the three arguments (`gammaExtremum_lencl_zero`,
`gammaExtremum_lencl_one_sub`, `gammaExtremum_aencl_frac`), `gammaExtremumCore_spec`, and
the convergence `gammaExtremumCore_coreConv` from `coreConv_pos` and `coreConv_reflect`
(`Equiv/GammaWidth.lean`), with the sine of the reflection formula from
`gammaSinOfFrac_some'`.
-/

namespace Azurite.AzFloat

open Filter Topology

/-- **The tight enclosure of a zero of `ψ`**: it contains the zero and is at most `2^(−V)`
wide. -/
theorem psiZeroEnclAt_spec (n V : ℕ) :
    AEncl (psiZeroEnclAt n V) (psiZeroAt n) ((1 / 2 : ℝ) ^ V) := by
  obtain ⟨f, hf⟩ := searchCertified_eq (psiZeroTightAt n V) (max 64 V)
    (psiZeroTightAt_exists n V _ (Nat.lt_of_lt_of_le (by norm_num) (le_max_left 64 V)))
  unfold psiZeroTightAt at hf
  obtain ⟨hb, hnar⟩ := Option.filter_eq_some_iff.mp hf
  have hw : 40 ≤ max 64 V * 2 ^ f :=
    le_trans (by norm_num : 40 ≤ 64) ((le_max_left 64 V).trans
      (Nat.le_mul_of_pos_right _ (by positivity)))
  have := psiZeroNarrow_spec (psiZeroEncl_spec n hw hb) hnar
  rwa [Nat.mul_div_cancel_left V two_pos] at this

theorem psiZeroAt_zero_gt_one : 1 < psiZeroAt 0 := by
  rw [psiZeroAt_zero]
  exact psiZeroPos_spec.1

theorem psiZeroAt_mem {n : ℕ} (hn : n ≠ 0) :
    -(n : ℝ) < psiZeroAt n ∧ psiZeroAt n < -(n : ℝ) + 1 := by
  obtain ⟨h1, h2, -⟩ := psiZeroAt_facts n
  have hL : (psiZeroLo n : ℝ) = -(n : ℝ) := by simp [psiZeroLo, hn]
  rw [hL] at h1 h2
  exact ⟨h1, h2⟩

theorem half_pow_add_two (W k : ℕ) :
    (1 / 2 : ℝ) ^ (W + k + 2) = (1 / 2 : ℝ) ^ (W + k) / 4 := by
  rw [pow_add]
  norm_num
  ring

/-- The enclosure of `x₀` handed to `ln Γ`. -/
theorem gammaExtremum_lencl_zero (W : ℕ) :
    LEncl (psiZeroEnclAt 0 (W + 32)) (psiZeroAt 0) (6 * (1 / 2 : ℝ) ^ (W + 32)) := by
  have hx := psiZeroAt_zero_gt_one
  have hA := psiZeroEnclAt_spec 0 (W + 32)
  have hu0 : (0 : ℝ) < (1 / 2 : ℝ) ^ (W + 32) := by positivity
  have hu : (1 / 2 : ℝ) ^ (W + 32) ≤ 1 / 8 := half_pow_le_eighth (by omega)
  refine (LEncl.ofA hA (by linarith) (by linarith)).mono ?_
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- The enclosure of `1 − xₙ` handed to `ln Γ`, `n ≥ 1`. -/
theorem gammaExtremum_lencl_one_sub {n : ℕ} (hn : n ≠ 0) (W : ℕ) :
    LEncl (Encl.sub (W + 36) (Encl.exact one) (psiZeroEnclAt n (W + 34)))
      (-psiZeroAt n + 1) (6 * (1 / 2 : ℝ) ^ (W + 32)) := by
  obtain ⟨h1, h2⟩ := psiZeroAt_mem hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hA := psiZeroEnclAt_spec n (W + 34)
  have hu0 : (0 : ℝ) < (1 / 2 : ℝ) ^ (W + 32) := by positivity
  have hu : (1 / 2 : ℝ) ^ (W + 32) ≤ 1 / 8 := half_pow_le_eighth (by omega)
  have e34 : (1 / 2 : ℝ) ^ (W + 34) = (1 / 2 : ℝ) ^ (W + 32) / 4 := half_pow_add_two W 32
  have e36 : (1 / 2 : ℝ) ^ (W + 36) = (1 / 2 : ℝ) ^ (W + 32) / 16 := by
    rw [show W + 36 = W + 34 + 2 by omega, half_pow_add_two W 34, e34]
    ring
  have : NeZero (W + 36) := ⟨by omega⟩
  obtain ⟨x₁, hx₁⟩ : ∃ x₁ : ℝ, x₁ = -psiZeroAt n + 1 := ⟨_, rfl⟩
  have hx₁1 : 1 ≤ x₁ := by rw [hx₁]; linarith
  have hsub := (AEncl.exact toVal_one').sub (w := W + 36) hA (B := x₁ + 1) (by
    rw [show (1 : ℝ) - psiZeroAt n = x₁ by rw [hx₁]; ring, abs_of_pos (by linarith), e34]
    linarith)
  rw [show (1 : ℝ) - psiZeroAt n = x₁ by rw [hx₁]; ring, e34, e36] at hsub
  rw [← hx₁]
  refine (LEncl.ofA hsub (by nlinarith) (by linarith)).mono ?_
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- The enclosure of `xₙ + n ∈ (0, 1)` handed to the sine, `n ≥ 1`. -/
theorem gammaExtremum_aencl_frac {n : ℕ} (hn : n ≠ 0) (W : ℕ) :
    AEncl (Encl.add (W + 36) (psiZeroEnclAt n (W + 34)) (Encl.nat n)) (psiZeroAt n + n)
      ((1 / 2 : ℝ) ^ (W + 32)) := by
  obtain ⟨h1, h2⟩ := psiZeroAt_mem hn
  have hA := psiZeroEnclAt_spec n (W + 34)
  have hu0 : (0 : ℝ) < (1 / 2 : ℝ) ^ (W + 32) := by positivity
  have hu : (1 / 2 : ℝ) ^ (W + 32) ≤ 1 / 8 := half_pow_le_eighth (by omega)
  have e34 : (1 / 2 : ℝ) ^ (W + 34) = (1 / 2 : ℝ) ^ (W + 32) / 4 := half_pow_add_two W 32
  have e36 : (1 / 2 : ℝ) ^ (W + 36) = (1 / 2 : ℝ) ^ (W + 32) / 16 := by
    rw [show W + 36 = W + 34 + 2 by omega, half_pow_add_two W 34, e34]
    ring
  have : NeZero (W + 36) := ⟨by omega⟩
  have hadd := hA.add (w := W + 36) (AEncl.exact (toVal_ofAzNat_ofNat n)) (B := 2) (by
    rw [abs_of_pos (by linarith), e34]
    linarith)
  rw [e34, e36] at hadd
  exact hadd.mono (by linarith)

/-- **`gammaExtremumCore` answers with the sign and a positive enclosure of `|Γ(xₙ)|`.** -/
theorem gammaExtremumCore_spec (n : ℕ) {w : ℕ} (hw : 64 ≤ w) {neg : Bool} {b : Encl}
    (h : gammaExtremumCore n w = some (neg, b)) :
    IsEnclPos b ((if neg then -1 else 1) * Real.Gamma (psiZeroAt n)) := by
  unfold gammaExtremumCore at h
  by_cases hn : n = 0
  · subst hn
    rw [ite_eq_left rfl] at h
    dsimp only at h
    obtain ⟨b', hb', hbeq⟩ := Option.map_eq_some_iff.mp h
    rw [Prod.mk.injEq] at hbeq
    obtain ⟨rfl, rfl⟩ := hbeq
    have hx0 : 0 < psiZeroAt 0 := by linarith [psiZeroAt_zero_gt_one]
    have hL := lnGammaBracketEncl_spec
      (gammaExtremum_lencl_zero (w + gammaLnBits (AzInt.ofInt 1))).isEnclPos (AzInt.ofInt 1)
      (w := w + gammaLnBits (AzInt.ofInt 1)) (by omega)
    simpa [gammaVal] using gammaExpEncl_lnGamma (recip := false) hx0 hL hw hb'
  · rw [ite_eq_right hn] at h
    dsimp only at h
    obtain ⟨h1, h2⟩ := psiZeroAt_mem hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    obtain ⟨e', he'⟩ : ∃ e' : AzInt, e' = AzInt.ofInt ((n.log2 + 2 : ℕ) : ℤ) := ⟨_, rfl⟩
    rw [← he'] at h
    have := gammaReflect_spec (recip := false) (xv := psiZeroAt n) (by linarith) hw
      (fun G' hG => ?_) (fun neg' S' hS => ?_) h
    · simpa [gammaVal] using this
    · have hL := lnGammaBracketEncl_spec
        (gammaExtremum_lencl_one_sub hn (w + gammaLnBits e')).isEnclPos e'
        (w := w + gammaLnBits e') (by omega)
      have := gammaExpEncl_lnGamma (recip := false)
        (by linarith : (0 : ℝ) < -psiZeroAt n + 1) hL hw hG
      simpa [gammaVal] using this
    · split_ifs at hS with hc
      have hA := ((gammaExtremum_aencl_frac hn (w + gammaLnBits e')).isEncl).pos_of_lt hc
      refine gammaSinOfFrac_spec (σ := false) (k := AzInt.ofInt (-(n : ℤ))) ?_
        (by omega : 64 ≤ w + 16) hw hS
      rw [AzInt.toInt_ofInt]
      convert hA using 1
      push_cast
      simp

/-- **The core of `Γ(xₙ)` converges.** -/
theorem gammaExtremumCore_coreConv (n : ℕ) :
    CoreConv (gammaExtremumCore n) (Real.Gamma (psiZeroAt n)) := by
  by_cases hn : n = 0
  · subst hn
    have hx0 : 0 < psiZeroAt 0 := by linarith [psiZeroAt_zero_gt_one]
    have := coreConv_pos false hx0 (AzInt.ofInt 1) (gammaLnBits (AzInt.ofInt 1))
      (X := fun W => psiZeroEnclAt 0 (W + 32)) gammaExtremum_lencl_zero
    exact this.congr fun w => by simp [gammaExtremumCore]
  · obtain ⟨h1, h2⟩ := psiZeroAt_mem hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    obtain ⟨e', he'⟩ : ∃ e' : AzInt, e' = AzInt.ofInt ((n.log2 + 2 : ℕ) : ℤ) := ⟨_, rfl⟩
    obtain ⟨c, hc⟩ : ∃ c : ℕ, c = gammaLnBits e' := ⟨_, rfl⟩
    obtain ⟨u, hu⟩ : ∃ u : ℝ, u = psiZeroAt n + n := ⟨_, rfl⟩
    have hu0 : 0 < u := by rw [hu]; linarith
    have hu1 : u < 1 := by rw [hu]; linarith
    have hk1 : |psiZeroAt n - ((-(n : ℤ) : ℤ) : ℝ)| < 1 := by
      rw [show psiZeroAt n - ((-(n : ℤ) : ℤ) : ℝ) = u by rw [hu]; push_cast; ring,
        abs_of_pos hu0]
      exact hu1
    have hval := abs_sin_pi_mul (psiZeroAt n) (-(n : ℤ)) hk1
    rw [show psiZeroAt n - ((-(n : ℤ) : ℤ) : ℝ) = u by rw [hu]; push_cast; ring,
      abs_of_pos hu0] at hval
    have hs0 : 0 < Real.sin (u * Real.pi) :=
      Real.sin_pos_of_pos_of_lt_pi (mul_pos hu0 Real.pi_pos) (by nlinarith [Real.pi_pos])
    have hpow : Tendsto (fun w : ℕ => (1 / 2 : ℝ) ^ w) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hpow16 : Tendsto (fun w : ℕ => (1 / 2 : ℝ) ^ (w + 16)) atTop (𝓝 0) :=
      hpow.comp (tendsto_add_atTop_nat 16)
    have hlam : Tendsto (fun w : ℕ => 2 * (1 / 2 : ℝ) ^ w / u) atTop (𝓝 0) := by
      have := (hpow.const_mul 2).div_const u
      rwa [mul_zero, zero_div] at this
    have hE : Tendsto (fun w : ℕ => sinEnv w + 32 * (2 * (1 / 2 : ℝ) ^ w / u)
        + 304 * (1 / 2 : ℝ) ^ (w + 16)) atTop (𝓝 0) := by
      have := (tendsto_sinEnv.add (hlam.const_mul 32)).add (hpow16.const_mul 304)
      rwa [mul_zero, add_zero, mul_zero, add_zero] at this
    have hSc : SinConv (fun w =>
        if lt zero (Encl.add (w + c + 36) (psiZeroEnclAt n (w + c + 34)) (Encl.nat n)).1
        then gammaSinOfFrac false (AzInt.ofInt (-(n : ℤ)))
          (Encl.add (w + c + 36) (psiZeroEnclAt n (w + c + 34)) (Encl.nat n)) (w + 16) w
        else none) (psiZeroAt n) := by
      refine ⟨_, hE, ?_⟩
      filter_upwards [eventually_ge_atTop 64,
        tendsto_sinEnv.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1)),
        hlam.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 64)),
        hpow.eventually (ge_mem_nhds (by linarith : (0 : ℝ) < u / 2)),
        hE.eventually (gt_mem_nhds hs0)] with w hw henv hl64 hpu hsmall
      have hpw : (1 / 2 : ℝ) ^ (w + c + 32) ≤ (1 / 2 : ℝ) ^ w :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      have hA := (gammaExtremum_aencl_frac hn (w + c)).mono hpw
      rw [← hu] at hA
      have hL := LEncl.ofA hA (by linarith) hu0
      have hpos : lt zero (Encl.add (w + c + 36) (psiZeroEnclAt n (w + c + 34))
          (Encl.nat n)).1 = true := by
        obtain ⟨l, h, hl, -, hl0, -⟩ := hL
        exact (lt_eq_true_iff toVal_zero' hl).mpr hl0
      obtain ⟨S, hS, hSw⟩ := gammaSinOfFrac_some' (σ := false)
        (k := AzInt.ofInt (-(n : ℤ))) (by omega : 64 ≤ w + 16) hL (by positivity) hl64 hu1
        hw henv hsmall
      refine ⟨_, S, by rw [ite_eq_left hpos]; exact hS, ?_, ?_⟩
      · refine gammaSinOfFrac_spec (σ := false) (k := AzInt.ofInt (-(n : ℤ))) ?_
          (by omega : 64 ≤ w + 16) hw hS
        rw [AzInt.toInt_ofInt]
        convert hL.isEnclPos using 1
        rw [hu]
        push_cast
        simp
      · rw [hval]
        exact hSw
    have := coreConv_reflect false (by linarith : psiZeroAt n < 0) e' c
      (X := fun W => Encl.sub (W + 36) (Encl.exact one) (psiZeroEnclAt n (W + 34)))
      (gammaExtremum_lencl_one_sub hn) hSc
    refine this.congr fun w => ?_
    unfold gammaExtremumCore
    rw [ite_eq_right hn]
    dsimp only
    rw [← he', ← hc]

/-- The bracket of `Γ(xₙ)` is valid, or rejected. -/
theorem gammaExtremumApprox_valid_or_none (n : ℕ) {w : ℕ} (hw : 64 ≤ w) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    (∃ lv hv : ℝ, Rounds (gammaExtremumApprox n w).1 lv ∧
        Rounds (gammaExtremumApprox n w).2 hv ∧ lv ≤ Real.Gamma (psiZeroAt n) ∧
        Real.Gamma (psiZeroAt n) ≤ hv ∧
        (lv = Real.Gamma (psiZeroAt n) → hv = Real.Gamma (psiZeroAt n))) ∨
      roundingPossible (gammaExtremumApprox n w).1 (gammaExtremumApprox n w).2 p mode = none :=
  gammaApproxOf_valid_or_none (fun _ _ hc => gammaExtremumCore_spec n hw hc) w p mode

/-- **`gammaExtremumPrecRoundFuel` is a convergent loop.** -/
theorem gammaExtremumPrecRoundFuel_zivCases (n p : ℕ) [NeZero p] (mode : RoundingMode) :
    ZivCases (fun fuel => gammaExtremumPrecRoundFuel fuel n p mode)
      (some ((Real.Gamma (psiZeroAt n) : ℝ) : EReal)) p mode := by
  refine (ZivCases.of_core (gammaExtremumCore_coreConv n)
    (fun w hw neg b hc => gammaExtremumCore_spec n hw hc) p mode).congr fun fuel => ?_
  show gammaExtremumPrecRoundFuel fuel n p mode = _
  unfold gammaExtremumPrecRoundFuel
  rw [ite_eq_right (NeZero.ne p)]
  rfl

/-- **The specification of the extrema of `Γ`** (`ZivSpec`): sound at every fuel, and complete
in the limit of the fuel wherever the value is no rounding boundary.  Nothing is known about
the arithmetic nature of the extrema; the set of known values is empty (no extremum is
`0`). -/
theorem gammaExtremumPrecRoundFuel_zivSpec :
    ZivSpec (fun n : ℕ => some ((Real.Gamma (psiZeroAt n) : ℝ) : EReal))
      gammaExtremumPrecRoundFuel
      {n | ∀ v : ℝ, some ((Real.Gamma (psiZeroAt n) : ℝ) : EReal) = some (v : EReal) → v = 0}
      ∅ :=
  ZivSpec.of_zivCases fun n p _ mode => gammaExtremumPrecRoundFuel_zivCases n p mode

/-- **The extrema of `Γ` are correctly rounded, or the fuel ran out**, at every fuel. -/
theorem gammaExtremumPrecRoundFuel_eq_or (fuel n p : ℕ) [NeZero p] (mode : RoundingMode) :
    gammaExtremumPrecRoundFuel fuel n p mode
        = roundVal p mode (some ((Real.Gamma (psiZeroAt n) : ℝ) : EReal)) ∨
      gammaExtremumPrecRoundFuel fuel n p mode = (nan, .eq) :=
  (gammaExtremumPrecRoundFuel_zivCases n p mode).sound fuel

/-- **The extrema of `Γ` are correctly rounded, or the fuel ran out.** -/
theorem gammaExtremumPrecRound_eq_or (n p : ℕ) [NeZero p] (mode : RoundingMode) :
    gammaExtremumPrecRound n p mode
        = roundVal p mode (some ((Real.Gamma (psiZeroAt n) : ℝ) : EReal)) ∨
      gammaExtremumPrecRound n p mode = (nan, .eq) :=
  gammaExtremumPrecRoundFuel_eq_or (gammaFuel p) n p mode

/-- No extremum is `0`: `Γ` has no zeros. -/
theorem gamma_psiZeroAt_ne_zero (n : ℕ) : Real.Gamma (psiZeroAt n) ≠ 0 :=
  (gammaExtremumCore_coreConv n).ne_zero

end Azurite.AzFloat
