/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.EulerGamma
import Azurite.AzFloat.Equiv.LnBracket
import Azurite.AzFloat.Equiv.Ln2Bracket
import Azurite.AzInt.Equiv.SignedSplit

/-!
# Equivalence: Euler's constant

`eulerGammaBracket_spec` (a strict enclosure of `γ`: the exact partial sum of Sweeney's series
from `AzInt.sweeneyNumDen_eq`, bracketed by `seriesBracket_spec_of`; `ln n` from
`lnBracket_spec`; `E₁(n) ≤ e^(−n)/n ≤ 2^(−w−5)` from `expIntegralE1_le` and the choice of
`eulerGammaN`; the tail from `abs_tsum_sweeneyTerm_sub_sum_le`), `eulerGammaApprox_spec`, and
`eulerGammaPrecRound_eq_or`: `eulerGammaPrecRound p mode` is the correctly rounded `γ`
(`liftVal₀ (some γ)`) unless the fuel runs out (`(nan, .eq)`).  A termination certificate would
need `Irrational γ`, an open problem.
-/

namespace Azurite.AzFloat

open Finset Real

/-- `lnBracketOf x w` encloses `ln x` for a finite positive float `x` (`w ≥ 64`). -/
theorem lnBracketOf_spec {w : ℕ} (hw : 64 ≤ w) {x : AzFloat} {r : ℝ}
    (hx : x.toVal = some (r : EReal)) (hr : 0 < r) :
    ∃ lv hv : ℝ, (lnBracketOf x w).1.toVal = some (lv : EReal) ∧
      (lnBracketOf x w).2.toVal = some (hv : EReal) ∧ lv ≤ Real.log r ∧ Real.log r ≤ hv := by
  obtain ⟨e, q, m, hv, rfl, hval⟩ := eq_finite_true_of_toVal_pos hx hr
  obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ := lnBracket_spec hw e hv
  rw [hval] at hlo hhi
  exact ⟨lv, hv', hl, hh, hlo, hhi⟩

/-- The tail float `2^(−w−4)`. -/
theorem toVal_eulerGamma_tail (w : ℕ) :
    (powerOf2 (-(AzNat.ofNat (w + 4)).toAzInt)).toVal
      = some (((1 / 2 : ℝ) ^ (w + 4) : ℝ) : EReal) := by
  rw [toVal_powerOf2, AzInt.toInt_neg, AzNat.toInt_toAzInt, AzNat.toNat_ofNat, zpow_neg,
    zpow_natCast, one_div_pow, one_div]

theorem one_le_eulerGammaN (w : ℕ) : 1 ≤ eulerGammaN w := by
  unfold eulerGammaN; omega

/-- `e^(−n)/n ≤ 2^(−w−5)` for `n = eulerGammaN w`. -/
theorem exp_neg_eulerGammaN_div_le (w : ℕ) :
    Real.exp (-(eulerGammaN w : ℝ)) / (eulerGammaN w : ℝ) ≤ (1 / 2 : ℝ) ^ (w + 5) := by
  have hn1 : (1 : ℝ) ≤ eulerGammaN w := by exact_mod_cast one_le_eulerGammaN w
  have hn : (7 : ℝ) * (w + 5) / 10 ≤ eulerGammaN w := by
    have h' : 7 * (w + 5) < (7 * (w + 5) / 10 + 1) * 10 := by omega
    unfold eulerGammaN
    have : (7 * (w + 5) : ℝ) ≤ ((7 * (w + 5) / 10 + 1 : ℕ) : ℝ) * 10 := by exact_mod_cast h'.le
    linarith
  have hlog : (w + 5 : ℝ) * Real.log 2 ≤ eulerGammaN w := by
    have := Real.log_two_lt_d9
    have hw0 : (0 : ℝ) ≤ w + 5 := by positivity
    nlinarith
  calc Real.exp (-(eulerGammaN w : ℝ)) / (eulerGammaN w : ℝ) ≤ Real.exp (-(eulerGammaN w : ℝ)) :=
        div_le_self (Real.exp_pos _).le hn1
    _ ≤ Real.exp (-((w + 5 : ℝ) * Real.log 2)) := Real.exp_le_exp.mpr (by linarith)
    _ = (1 / 2 : ℝ) ^ (w + 5) := by
        have h2 : Real.exp ((w + 5 : ℝ) * Real.log 2) = 2 ^ (w + 5) := by
          rw [show ((w : ℝ) + 5) = ((w + 5 : ℕ) : ℝ) by push_cast; ring, Real.exp_nat_mul,
            Real.exp_log two_pos]
        rw [Real.exp_neg, h2, one_div_pow, one_div]

/-- The tail of Sweeney's series after `eulerGammaTerms w` terms is at most `2^(−w−8)`
(`w ≥ 64`). -/
theorem abs_tail_eulerGamma_le {w : ℕ} (hw : 64 ≤ w) :
    |∑' k, sweeneyTerm (eulerGammaN w : ℝ) k
        - ∑ k ∈ range (eulerGammaTerms w), sweeneyTerm (eulerGammaN w : ℝ) k|
      ≤ (1 / 2 : ℝ) ^ (w + 8) := by
  have h := abs_tsum_sweeneyTerm_sub_sum_le_of_le (one_le_eulerGammaN w) (q := eulerGammaQ w)
    (by unfold eulerGammaQ; omega)
  rw [← eulerGammaTerms] at h
  refine h.trans ?_
  have h16 : w + 9 ≤ 16 * eulerGammaQ w := by unfold eulerGammaQ eulerGammaN; omega
  calc 2 * (1 / 2 : ℝ) ^ (16 * eulerGammaQ w)
      = (1 / 2 : ℝ) ^ (16 * eulerGammaQ w - 1) := by
        obtain ⟨m, hm⟩ : ∃ m, 16 * eulerGammaQ w = m + 1 := ⟨16 * eulerGammaQ w - 1, by omega⟩
        rw [hm, Nat.add_sub_cancel, pow_succ]
        ring
    _ ≤ (1 / 2 : ℝ) ^ (w + 8) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

/-- `eulerGammaBracket w` encloses `γ`, strictly from below. -/
theorem eulerGammaBracket_spec {w : ℕ} (hw : 64 ≤ w) :
    ∃ lo hi : ℝ, (eulerGammaBracket w).1.toVal = some (lo : EReal) ∧
      (eulerGammaBracket w).2.toVal = some (hi : EReal) ∧
      lo < eulerMascheroniConstant ∧ eulerMascheroniConstant ≤ hi := by
  set n := eulerGammaN w with hn
  set N := eulerGammaTerms w with hN
  set k := eulerGammaBits w with hk
  have hk64 : 64 ≤ k := by rw [hk]; unfold eulerGammaBits; omega
  have : NeZero k := ⟨by omega⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast one_le_eulerGammaN w
  have hn0 : (0 : ℝ) < n := by linarith
  -- the exact value and the partial sum
  set S := ∑ i ∈ range N, sweeneyTerm (n : ℝ) i with hS
  have hγ := eulerMascheroni_eq_sweeney hn1
  have hE0 := expIntegralE1_nonneg hn0
  have hE1 := (expIntegralE1_le hn0).trans (exp_neg_eulerGammaN_div_le w)
  have htail := abs_tail_eulerGamma_le hw
  rw [← hn, ← hN, ← hS] at htail
  rw [abs_le] at htail
  have hγhalf := one_half_lt_eulerMascheroniConstant
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hpow : (0 : ℝ) < (1 / 2 : ℝ) ^ (w + 8) := by positivity
  have hpow5 : (1 / 2 : ℝ) ^ (w + 5) = 8 * (1 / 2 : ℝ) ^ (w + 8) := by
    rw [pow_add, pow_add]; ring
  have hpow4 : (1 / 2 : ℝ) ^ (w + 4) = 16 * (1 / 2 : ℝ) ^ (w + 8) := by
    rw [pow_add, pow_add]; ring
  have hpow_small : (1 / 2 : ℝ) ^ (w + 8) ≤ 1 / 2 := by
    have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      (by omega : 1 ≤ w + 8)
    rwa [pow_one] at this
  have hS0 : 0 ≤ S := by linarith [htail.2]
  -- the exact fraction
  have hfrac := AzInt.sweeneyNumDen_eq n N
  rw [← hS] at hfrac
  have hden := AzInt.sweeneyNumDen_den_pos n N
  have hden' : (0 : ℝ) < (AzInt.sweeneyNumDen n N).2.toNat := by exact_mod_cast hden
  have hT0 : 0 ≤ ((AzInt.sweeneyNumDen n N).1.toInt : ℝ) := by
    have := div_nonneg_iff.mp (hfrac ▸ hS0)
    rcases this with ⟨h, -⟩ | ⟨-, h⟩
    · exact h
    · linarith
  have habs : (((AzInt.sweeneyNumDen n N).1.natAbs.toNat : ℕ) : ℝ)
      = ((AzInt.sweeneyNumDen n N).1.toInt : ℝ) := by
    rw [AzInt.toNat_natAbs, Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg hT0]
  have hfrac' : (((AzInt.sweeneyNumDen n N).1.natAbs, (AzInt.sweeneyNumDen n N).2).1.toNat : ℝ)
      / ((AzInt.sweeneyNumDen n N).1.natAbs, (AzInt.sweeneyNumDen n N).2).2.toNat = S := by
    simp only
    rw [habs, hfrac]
  obtain ⟨sl, sh, hsl, hsh, -, hslS, -, hSsh, -⟩ :=
    seriesBracket_spec_of hfrac' hden hS0 (k := k) (by omega)
  -- the logarithm
  obtain ⟨ll, lh, hll, hlh, hllog, hlogh⟩ :=
    lnBracketOf_spec hk64 (toVal_ofAzNat_ofNat n) (by exact_mod_cast one_le_eulerGammaN w)
  -- the tail float
  have ht := toVal_eulerGamma_tail w
  -- the lower end
  obtain ⟨r₁, hr₁, hr₁le, -⟩ := subFloor_le hsl hlh k
  obtain ⟨r₂, hr₂, hr₂le, -⟩ := subFloor_le hr₁ ht k
  -- the upper end
  obtain ⟨r₃, hr₃, hr₃c⟩ := addCeiling_err hsh ht k (by linarith)
  have hγle : eulerMascheroniConstant ≤ r₃ - ll := by
    have := hr₃c.ge
    linarith
  obtain ⟨r₄, hr₄, hr₄c⟩ := subCeiling_err hr₃ hll k (by linarith)
  refine ⟨r₂, r₄, ?_, ?_, ?_, ?_⟩
  · simp only [eulerGammaBracket]
    rw [← hn, ← hN, ← hk]
    exact hr₂
  · simp only [eulerGammaBracket]
    rw [← hn, ← hN, ← hk]
    exact hr₄
  · linarith
  · linarith [hr₄c.ge]

theorem eulerGammaApprox_spec {w : ℕ} (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, Rounds (eulerGammaApprox w).1 lv ∧ Rounds (eulerGammaApprox w).2 hv ∧
      lv < eulerMascheroniConstant ∧ eulerMascheroniConstant ≤ hv := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2⟩ := eulerGammaBracket_spec hw
  refine ⟨lo, hi, ?_, ?_, h1, h2⟩
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hlo)
    rw [fval_of_toVal_coe hlo] at hR
    exact hR
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
    rw [fval_of_toVal_coe hhi] at hR
    exact hR

/-- **Euler's constant is correctly rounded unless the fuel runs out.** -/
theorem eulerGammaPrecRound_eq_or (p : ℕ) [NeZero p] (mode : RoundingMode) :
    eulerGammaPrecRound p mode = liftVal₀ (some ((eulerMascheroniConstant : ℝ) : EReal)) p mode ∨
      eulerGammaPrecRound p mode = (nan, .eq) := by
  unfold eulerGammaPrecRound liftVal₀
  rw [ite_eq_right (NeZero.ne p)]
  rcases eq_or_ne (zivLoop eulerGammaApprox p mode (eulerGammaFuel p) (p + zivGuardBits))
    (nan, .eq) with hz | hz
  · right; exact hz
  · left
    exact zivLoop_eq_of_ne_nan_threshold p mode eulerGammaApprox eulerMascheroniConstant 64
      (fun w hw => by
        obtain ⟨lv, hv, hl, hh, hlo, hhi⟩ := eulerGammaApprox_spec hw
        exact ⟨lv, hv, hl, hh, hlo.le, hhi, fun h => absurd h hlo.ne⟩)
      _ _ (by unfold zivGuardBits; omega) hz

end Azurite.AzFloat
