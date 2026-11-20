/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.EulerGamma
import Azurite.AzInt.Equiv.SweeneyHorner
import Azurite.AzFloat.Equiv.LnBracket
import Azurite.AzFloat.Equiv.Ln2Bracket
import Azurite.AzFloat.Equiv.LnSmooth

/-!
# Equivalence: Euler's constant

`eulerGammaBracket_spec` (a strict enclosure of `γ`: the partial sum of Sweeney's series
enclosed by `AzInt.sweeneyHornerEncl_spec`, its two fractions turned into floats by
`seriesBracket_spec_of`; `ln n` from `lnNatBracket_spec` — `lnSmoothBracket_spec` for the
integers with no prime factor above `7`, `lnBracket_spec` otherwise;
`E₁(n) ≤ e^(−n)/n ≤ 2^(−w−5)` from `expIntegralE1_le` and `eulerGammaN w ≤ n` (`exp_neg_div_le_of_eulerGammaN_le`); the tail from
`abs_tsum_sweeneyTerm_sub_sum_le_of_le` (`abs_tail_eulerGamma_le`)), `eulerGammaApprox_spec`,
and `eulerGammaPrecRound_eq_or`: `eulerGammaPrecRound p mode` is the correctly rounded `γ`
(`liftVal₀ (some γ)`) unless the fuel runs out (`(nan, .eq)`).  A termination certificate would
need `Irrational γ`, an open problem.  The width of the bracket, its convergence and the
specification as a fuel-bound function are in `Equiv/EulerGammaWidth.lean`.
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

/-- The argument is at least the least admissible one. -/
theorem eulerGammaN_le_arg (w : ℕ) : eulerGammaN w ≤ eulerGammaArg w := le_nextSmooth _

/-- `lnNatBracket n k` encloses `ln n` (`n ≥ 1`, `k ≥ 64`). -/
theorem lnNatBracket_spec {k : ℕ} (hk : 64 ≤ k) {n : ℕ} (hn : 1 ≤ n) :
    ∃ lv hv : ℝ, (lnNatBracket n k).1.toVal = some (lv : EReal) ∧
      (lnNatBracket n k).2.toVal = some (hv : EReal) ∧ lv ≤ Real.log n ∧ Real.log n ≤ hv := by
  unfold lnNatBracket
  dsimp only
  split_ifs with h
  · obtain ⟨lv, hv, hl, hh, hlo, hhi⟩ :=
      lnSmoothBracket_spec (smoothExps n).1 (smoothExps n).2.1 (smoothExps n).2.2.1
        (smoothExps n).2.2.2.1 (k := k) (by omega)
    have hlog : Real.log (n : ℝ) = (smoothExps n).1 * Real.log 2
        + (smoothExps n).2.1 * Real.log 3 + (smoothExps n).2.2.1 * Real.log 5
        + (smoothExps n).2.2.2.1 * Real.log 7 := by
      have hc : (n : ℝ) = (2 : ℝ) ^ (smoothExps n).1 * 3 ^ (smoothExps n).2.1
          * 5 ^ (smoothExps n).2.2.1 * 7 ^ (smoothExps n).2.2.2.1 := by exact_mod_cast h
      rw [hc, Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow,
        Real.log_pow]
    rw [hlog]
    exact ⟨lv, hv, hl, hh, hlo, hhi⟩
  · exact lnBracketOf_spec hk (toVal_ofAzNat_ofNat n) (by exact_mod_cast hn)

/-- `e^(−n)/n ≤ 2^(−w−5)` for `n ≥ eulerGammaN w`. -/
theorem exp_neg_div_le_of_eulerGammaN_le {w n : ℕ} (h : eulerGammaN w ≤ n) :
    Real.exp (-(n : ℝ)) / (n : ℝ) ≤ (1 / 2 : ℝ) ^ (w + 5) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (one_le_eulerGammaN w).trans h
  have hn : (7 : ℝ) * (w + 5) / 10 ≤ n := by
    have h' : 7 * (w + 5) < (7 * (w + 5) / 10 + 1) * 10 := by omega
    have h'' : 7 * (w + 5) ≤ n * 10 := by unfold eulerGammaN at h; omega
    have : (7 * (w + 5) : ℝ) ≤ (n : ℝ) * 10 := by exact_mod_cast h''
    linarith
  have hlog : (w + 5 : ℝ) * Real.log 2 ≤ n := by
    have := Real.log_two_lt_d9
    have hw0 : (0 : ℝ) ≤ w + 5 := by positivity
    nlinarith
  calc Real.exp (-(n : ℝ)) / (n : ℝ) ≤ Real.exp (-(n : ℝ)) :=
        div_le_self (Real.exp_pos _).le hn1
    _ ≤ Real.exp (-((w + 5 : ℝ) * Real.log 2)) := Real.exp_le_exp.mpr (by linarith)
    _ = (1 / 2 : ℝ) ^ (w + 5) := by
        have h2 : Real.exp ((w + 5 : ℝ) * Real.log 2) = 2 ^ (w + 5) := by
          rw [show ((w : ℝ) + 5) = ((w + 5 : ℕ) : ℝ) by push_cast; ring, Real.exp_nat_mul,
            Real.exp_log two_pos]
        rw [Real.exp_neg, h2, one_div_pow, one_div]

/-- The tail of Sweeney's series with argument `n ≥ eulerGammaN w` after `eulerGammaTermsOf n`
terms is at most `2^(−w−8)` (`w ≥ 64`). -/
theorem abs_tail_eulerGamma_le {w n : ℕ} (hw : 64 ≤ w) (h : eulerGammaN w ≤ n) :
    |∑' k, sweeneyTerm (n : ℝ) k - ∑ k ∈ range (eulerGammaTermsOf n), sweeneyTerm (n : ℝ) k|
      ≤ (1 / 2 : ℝ) ^ (w + 8) := by
  have hn1 : 1 ≤ n := (one_le_eulerGammaN w).trans h
  have h' := abs_tsum_sweeneyTerm_sub_sum_le_of_le hn1 (q := (n + 9) / 10) (by omega)
  rw [← eulerGammaTermsOf] at h'
  refine h'.trans ?_
  have h16 : w + 9 ≤ 16 * ((n + 9) / 10) := by unfold eulerGammaN at h; omega
  calc 2 * (1 / 2 : ℝ) ^ (16 * ((n + 9) / 10))
      = (1 / 2 : ℝ) ^ (16 * ((n + 9) / 10) - 1) := by
        obtain ⟨m, hm⟩ : ∃ m, 16 * ((n + 9) / 10) = m + 1 := ⟨16 * ((n + 9) / 10) - 1, by omega⟩
        rw [hm, Nat.add_sub_cancel, pow_succ]
        ring
    _ ≤ (1 / 2 : ℝ) ^ (w + 8) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

/-- `eulerGammaBracketAt w n` encloses `γ`, strictly from below (`n ≥ eulerGammaN w`). -/
theorem eulerGammaBracketAt_spec {w : ℕ} (hw : 64 ≤ w) {n : ℕ} (hnN : eulerGammaN w ≤ n) :
    ∃ lo hi : ℝ, (eulerGammaBracketAt w n).1.toVal = some (lo : EReal) ∧
      (eulerGammaBracketAt w n).2.toVal = some (hi : EReal) ∧
      lo < eulerMascheroniConstant ∧ eulerMascheroniConstant ≤ hi := by
  set N := eulerGammaTermsOf n with hN
  set k := eulerGammaBits w n with hk
  set V := eulerGammaWork w n with hVdef
  have hk64 : 64 ≤ k := by rw [hk]; exact le_max_left _ _
  have hV1 : 1 ≤ V := by rw [hVdef]; unfold eulerGammaWork; omega
  have : NeZero k := ⟨by omega⟩
  have hn1' : 1 ≤ n := (one_le_eulerGammaN w).trans hnN
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1'
  have hn0 : (0 : ℝ) < n := by linarith
  -- the exact value and the partial sum
  set S := ∑ i ∈ range N, sweeneyTerm (n : ℝ) i with hS
  have hγ := eulerMascheroni_eq_sweeney hn1
  have hE0 := expIntegralE1_nonneg hn0
  have hE1 := (expIntegralE1_le hn0).trans (exp_neg_div_le_of_eulerGammaN_le hnN)
  have htail := abs_tail_eulerGamma_le hw hnN
  rw [← hN, ← hS] at htail
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
  -- the enclosure of the partial sum
  set e := AzInt.sweeneyHornerEncl n N V (eulerGammaBlockBits V) with he
  obtain ⟨hden, hloS, hShi⟩ := AzInt.sweeneyHornerEncl_spec n N hV1 (eulerGammaBlockBits V) hS0
  rw [← he] at hden hloS hShi
  have hden' : (0 : ℝ) < e.2.2.toNat := by exact_mod_cast hden
  obtain ⟨sl, -, hsl, -, -, hslS, -, -, -⟩ :=
    seriesBracket_spec_of (s := (e.1, e.2.2)) rfl hden (by positivity) (k := k) (by omega)
  obtain ⟨-, sh, -, hsh, -, -, -, hSsh, -⟩ :=
    seriesBracket_spec_of (s := (e.2.1, e.2.2)) rfl hden (by positivity) (k := k) (by omega)
  have hsl' : (fracFloor e.1 e.2.2 k).toVal = some (sl : EReal) := hsl
  have hsh' : (fracCeil e.2.1 e.2.2 k).toVal = some (sh : EReal) := hsh
  have hslS' : sl ≤ S := hslS.trans hloS
  have hSsh' : S ≤ sh := hShi.trans hSsh
  -- the logarithm
  obtain ⟨ll, lh, hll, hlh, hllog, hlogh⟩ := lnNatBracket_spec hk64 hn1'
  -- the tail float
  have ht := toVal_eulerGamma_tail w
  -- the lower end
  obtain ⟨r₁, hr₁, hr₁le, -⟩ := subFloor_le hsl' hlh k
  obtain ⟨r₂, hr₂, hr₂le, -⟩ := subFloor_le hr₁ ht k
  -- the upper end
  have hsh0 : 0 ≤ sh := hS0.trans hSsh'
  obtain ⟨r₃, hr₃, hr₃c⟩ := addCeiling_err hsh' ht k (by linarith)
  have hγle : eulerMascheroniConstant ≤ r₃ - ll := by
    have := hr₃c.ge
    linarith
  obtain ⟨r₄, hr₄, hr₄c⟩ := subCeiling_err hr₃ hll k (by linarith)
  refine ⟨r₂, r₄, ?_, ?_, ?_, ?_⟩
  · simp only [eulerGammaBracketAt]
    rw [← hk, ← hVdef, ← hN, ← he]
    exact hr₂
  · simp only [eulerGammaBracketAt]
    rw [← hk, ← hVdef, ← hN, ← he]
    exact hr₄
  · linarith
  · linarith [hr₄c.ge]

/-- `eulerGammaBracket w` encloses `γ`, strictly from below. -/
theorem eulerGammaBracket_spec {w : ℕ} (hw : 64 ≤ w) :
    ∃ lo hi : ℝ, (eulerGammaBracket w).1.toVal = some (lo : EReal) ∧
      (eulerGammaBracket w).2.toVal = some (hi : EReal) ∧
      lo < eulerMascheroniConstant ∧ eulerMascheroniConstant ≤ hi :=
  eulerGammaBracketAt_spec hw (eulerGammaN_le_arg w)

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

/-- **Euler's constant with explicit fuel is correctly rounded unless the fuel runs out.** -/
theorem eulerGammaPrecRoundFuel_eq_or (fuel p : ℕ) [NeZero p] (mode : RoundingMode) :
    eulerGammaPrecRoundFuel fuel p mode
        = liftVal₀ (some ((eulerMascheroniConstant : ℝ) : EReal)) p mode ∨
      eulerGammaPrecRoundFuel fuel p mode = (nan, .eq) := by
  unfold eulerGammaPrecRoundFuel liftVal₀
  rw [ite_eq_right (NeZero.ne p)]
  rcases eq_or_ne (zivLoop eulerGammaApprox p mode fuel (max (p + 16) 64))
    (nan, .eq) with hz | hz
  · right; exact hz
  · left
    exact zivLoop_eq_of_ne_nan_threshold p mode eulerGammaApprox eulerMascheroniConstant 64
      (fun w hw => by
        obtain ⟨lv, hv, hl, hh, hlo, hhi⟩ := eulerGammaApprox_spec hw
        exact ⟨lv, hv, hl, hh, hlo.le, hhi, fun h => absurd h hlo.ne⟩)
      _ _ (le_max_right _ _) hz

/-- **Euler's constant is correctly rounded unless the fuel runs out.** -/
theorem eulerGammaPrecRound_eq_or (p : ℕ) [NeZero p] (mode : RoundingMode) :
    eulerGammaPrecRound p mode = liftVal₀ (some ((eulerMascheroniConstant : ℝ) : EReal)) p mode ∨
      eulerGammaPrecRound p mode = (nan, .eq) :=
  eulerGammaPrecRoundFuel_eq_or (eulerGammaFuel p) p mode

end Azurite.AzFloat
