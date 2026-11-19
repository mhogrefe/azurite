/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.PsiZero
import Azurite.AzFloat.Equiv.Digamma
import Azurite.Transcendental.PsiZero

/-!
# Equivalence: the real zeros of the digamma function

`psiZeroPrecRound_eq_or`: `psiZeroPrecRound n p mode` is the correct rounding of the `n`-th
real zero `psiZeroAt n` of `ψ` (`Transcendental/PsiZero.lean`), or `(nan, .eq)` when the fuel of
the Ziv loop runs out.  The steps: `psiZeroInside_zero`, `psiZeroInside_pos` (the float
comparisons place the candidate in the interval of the zero), `psiZeroAround_spec` (the
enclosure from the residual, whatever the candidate), `psiZeroEncl_spec`.
-/

namespace Azurite.AzFloat

open Set

theorem toVal_neg_ofNat (n : ℕ) :
    (-(ofAzNat (AzNat.ofNat n))).toVal = some ((-(n : ℝ) : ℝ) : EReal) := by
  rw [toVal_neg, toVal_ofAzNat_ofNat, Option.map_some, EReal.coe_neg]

/-- The comparisons for `n = 0`: `0 < c ≤ 2`. -/
theorem psiZeroInside_zero {c : AzFloat} {cv : ℝ} (hc : c.toVal = some (cv : EReal))
    (h : psiZeroInside 0 c = true) : 0 < cv ∧ cv ≤ 2 := by
  unfold psiZeroInside at h
  rw [ite_eq_left rfl, Bool.and_eq_true, lt_eq_true_iff toVal_zero' hc,
    le_eq_true_iff hc (toVal_ofAzNat_ofNat 2)] at h
  exact ⟨h.1, by exact_mod_cast h.2⟩

/-- The comparisons for `n ≥ 1`: `c ∈ (−n, −n + 1)`. -/
theorem psiZeroInside_pos {n : ℕ} (hn : 1 ≤ n) {c : AzFloat} {cv : ℝ}
    (hc : c.toVal = some (cv : EReal)) (h : psiZeroInside n c = true) :
    cv ∈ Ioo (-(n : ℝ)) (-(n : ℝ) + 1) := by
  unfold psiZeroInside at h
  rw [ite_eq_right (by omega), Bool.and_eq_true, lt_eq_true_iff (toVal_neg_ofNat n) hc,
    lt_eq_true_iff hc (toVal_neg_ofNat (n - 1))] at h
  refine ⟨h.1, ?_⟩
  have := h.2
  rw [Nat.cast_sub hn] at this
  push_cast at this
  linarith

/-- **The enclosure around a point of the interval contains the zero**, whatever the point. -/
theorem psiZeroAround_spec {n : ℕ} {c : AzFloat} {cv : ℝ} (hc : c.toVal = some (cv : EReal))
    (hin : psiZeroInside n c = true) {D : Encl} (hD : IsEncl D (DLMF.psiR cv)) {P : ℕ}
    [NeZero P] : IsEncl (psiZeroAround n c D P) (psiZeroAt n) := by
  obtain ⟨d₁, d₂, hd₁, hd₂, h1, h2⟩ := hD
  have hnD : (-D.1).toVal = some ((-d₁ : ℝ) : EReal) := by
    rw [toVal_neg, hd₁, Option.map_some, EReal.coe_neg]
  have hδ := toVal_maxOf hd₂ hnD
  have hδge : |DLMF.psiR cv| ≤ max d₂ (-d₁) := by
    rw [abs_le]
    constructor
    · linarith [le_max_right d₂ (-d₁)]
    · linarith [le_max_left d₂ (-d₁)]
  unfold psiZeroAround
  dsimp only
  have key : ∃ rv : ℝ, (if n = 0 then maxOf D.2 (-D.1) <<< AzInt.ofInt 2
      else maxOf D.2 (-D.1)).toVal = some (rv : EReal) ∧ |psiZeroAt n - cv| ≤ rv := by
    by_cases hn : n = 0
    · subst hn
      rw [ite_eq_left rfl]
      obtain ⟨h0, h2'⟩ := psiZeroInside_zero hc hin
      refine ⟨max d₂ (-d₁) * (2 : ℝ) ^ (2 : ℤ), ?_, ?_⟩
      · rw [toVal_shiftLeft_of_toVal hδ, AzInt.toInt_ofInt]
      · have := abs_psiZeroAt_zero_sub_le h0 h2' hδge
        norm_num
        linarith
    · rw [ite_eq_right hn]
      exact ⟨_, hδ, abs_psiZeroAt_sub_le (by omega)
        (psiZeroInside_pos (by omega) hc hin) hδge⟩
  obtain ⟨rv, hr, habs⟩ := key
  rw [abs_le] at habs
  obtain ⟨lo, hlo, hlo1, -⟩ := subFloor_abs hc hr P
  obtain ⟨hi, hhi, hhi1, -⟩ := addCeiling_abs hc hr P
  exact ⟨lo, hi, hlo, hhi, by linarith, by linarith⟩

/-- **Every answer of `psiZeroEncl` encloses `xₙ`** (`w ≥ 40`). -/
theorem psiZeroEncl_spec (n : ℕ) {w : ℕ} (hw : 40 ≤ w) {b : Encl}
    (h : psiZeroEncl n w = some b) : IsEncl b (psiZeroAt n) := by
  unfold psiZeroEncl at h
  dsimp only at h
  split_ifs at h with hc
  rw [Bool.and_eq_true] at hc
  obtain ⟨hfin, hin⟩ := hc
  obtain ⟨D, hD, rfl⟩ := Option.map_eq_some_iff.mp h
  have hcv := toVal_of_isFinite hfin
  have : NeZero (n.log2 + w + 64) := ⟨by omega⟩
  refine psiZeroAround_spec hcv hin (digammaEncl_spec hcv ?_ ?_ _ (by omega : 64 ≤ w + 24) hD)
  · intro hpos
    have hn : n = 0 := by simpa using hpos
    subst hn
    exact (psiZeroInside_zero hcv hin).1
  · intro hneg
    have hn : 1 ≤ n := by
      have : n ≠ 0 := by simpa using hneg
      omega
    have hmem := psiZeroInside_pos hn hcv hin
    have hn0 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact ⟨by linarith [hmem.2], DLMF.not_int_of_mem_Ioo hmem⟩

/-- **The zeros of `ψ` are correctly rounded, or the fuel ran out.** -/
theorem psiZeroPrecRound_eq_or (n p : ℕ) [NeZero p] (mode : RoundingMode) :
    psiZeroPrecRound n p mode = roundVal p mode (some ((psiZeroAt n : ℝ) : EReal)) ∨
      psiZeroPrecRound n p mode = (nan, .eq) := by
  unfold psiZeroPrecRound
  rw [ite_eq_right (NeZero.ne p)]
  rcases eq_or_ne (zivLoop (psiZeroApprox n) p mode (lnGammaFuel p) (max 64 (p + 32)))
    (nan, .eq) with hz | hz
  · right; exact hz
  · left
    exact zivLoop_eq_of_ne_nan_or_none p mode _ _ 64
      (fun w hw => lnAbsGammaApproxOf_valid_or_none
        (fun _ hc => psiZeroEncl_spec n (by omega) hc) w p mode)
      _ _ (le_max_left _ _) hz

end Azurite.AzFloat
