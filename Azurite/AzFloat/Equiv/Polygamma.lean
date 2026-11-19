/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Polygamma
import Azurite.AzFloat.Equiv.PolygammaBracket
import Azurite.AzFloat.Equiv.Digamma
import Azurite.AzFloat.Equiv.NegRound

/-!
# Equivalence: the polygamma functions

`Spec.polygamma n : EReal → Option EReal` is `ψ⁽ⁿ⁾` on the extended reals
(`polygammaR n x`, the real part of DLMF's `iteratedDeriv n digamma`, for `n ≥ 1`;
`Spec.digamma` for `n = 0`), and `polygammaPrecRound_eq_or` says that
`polygammaPrecRound n x p mode` is its correct rounding, or `(nan, .eq)` when the fuel of the
Ziv loop runs out.
-/

namespace Azurite.AzFloat

namespace Spec

open Classical in
/-- `ψ⁽ⁿ⁾` on the extended reals.  For `n ≥ 1`: `+∞ ↦ 0`; undefined at `−∞`; `0 ↦ (−1)ⁿ⁺¹ ∞`
(the limit from the right); at the negative integers `+∞` for an odd `n` (the limit from both
sides) and undefined for an even `n`. -/
noncomputable def polygamma (n : ℕ) (a : EReal) : Option EReal :=
  if n = 0 then digamma a
  else if a = ⊤ then some 0 else if a = ⊥ then none
  else if a.toReal = 0 then some (if n % 2 = 1 then ⊤ else ⊥)
  else if a.toReal < 0 ∧ ∃ k : ℤ, a.toReal = k then (if n % 2 = 1 then some ⊤ else none)
  else some ((polygammaR n a.toReal : ℝ) : EReal)

theorem polygamma_zero (a : EReal) : polygamma 0 a = digamma a := by simp [polygamma]

theorem polygamma_top {n : ℕ} (hn : n ≠ 0) : polygamma n ⊤ = some 0 := by
  simp [polygamma, hn]

theorem polygamma_bot {n : ℕ} (hn : n ≠ 0) : polygamma n ⊥ = none := by
  unfold polygamma
  rw [ite_eq_right hn, ite_eq_right bot_ne_top, ite_eq_left rfl]

theorem polygamma_coe_zero {n : ℕ} (hn : n ≠ 0) :
    polygamma n ((0 : ℝ) : EReal) = some (if n % 2 = 1 then ⊤ else ⊥) := by
  unfold polygamma
  rw [ite_eq_right hn, ite_eq_right (EReal.coe_ne_top _), ite_eq_right (EReal.coe_ne_bot _),
    EReal.toReal_coe, ite_eq_left rfl]

theorem polygamma_coe_of_pole {n : ℕ} (hn : n ≠ 0) {xv : ℝ} (h0 : xv < 0)
    (hk : ∃ k : ℤ, xv = k) :
    polygamma n (xv : EReal) = if n % 2 = 1 then some ⊤ else none := by
  unfold polygamma
  rw [ite_eq_right hn, ite_eq_right (EReal.coe_ne_top _), ite_eq_right (EReal.coe_ne_bot _),
    EReal.toReal_coe, ite_eq_right h0.ne, ite_eq_left ⟨h0, hk⟩]

theorem polygamma_coe {n : ℕ} (hn : n ≠ 0) {xv : ℝ} (h0 : xv ≠ 0)
    (hnp : ¬ (xv < 0 ∧ ∃ k : ℤ, xv = k)) :
    polygamma n (xv : EReal) = some ((polygammaR n xv : ℝ) : EReal) := by
  unfold polygamma
  rw [ite_eq_right hn, ite_eq_right (EReal.coe_ne_top _), ite_eq_right (EReal.coe_ne_bot _),
    EReal.toReal_coe, ite_eq_right h0, ite_eq_right hnp]

end Spec

/-- The one test of the tiny-argument path answers with the rounding of `ψ⁽ⁿ⁾(x)`. -/
theorem polygammaTinyOf_eq {n : ℕ} (hn : 1 ≤ n) {Xa : Encl} {xv : ℝ} (hx0 : xv ≠ 0)
    (hXa : IsEnclPos Xa |xv|) (hquarter : |xv| ≤ 1 / 4) {s : Bool} (hpos : s = true → 0 < xv)
    (hneg : s = false → xv < 0) (p : ℕ) [NeZero p] (mode : RoundingMode)
    {r : AzFloat × Ordering} (h : polygammaTinyOf n Xa s p mode = some r) :
    r = roundVal p mode (some ((polygammaR n xv : ℝ) : EReal)) := by
  unfold polygammaTinyOf at h
  dsimp only at h
  set W := p + zivGuardBits + 8 with hW
  have : NeZero W := ⟨by omega⟩
  have hW2 : 2 ≤ W := by omega
  obtain ⟨t, hH, ht0, htB⟩ := polygammaR_near_zero hn hx0 hquarter
  have hQ := (isEncl0_ofAzNat (AzNat.factorial n)).div (w := W) (hXa.powBin hW2 (n + 1))
  rw [AzNat.toNat_factorial] at hQ
  obtain ⟨ql, qh, hql, hqh, -, hq1, hq2⟩ := hQ
  have hB : (ofAzNat (AzNat.factorial (n + 1) <<< (n + 2))).toVal
      = some (((2 : ℝ) ^ (n + 2) * ((n + 1).factorial : ℝ) : ℝ) : EReal) := by
    rw [toVal_ofAzNat, AzNat.toNat_hShiftLeft, Nat.shiftLeft_eq, AzNat.toNat_factorial]
    push_cast
    rw [mul_comm]
  -- `A = n!/xⁿ⁺¹ = ± n!/|x|ⁿ⁺¹`
  set A := (n.factorial : ℝ) / xv ^ (n + 1) with hA
  set Av := (n.factorial : ℝ) / |xv| ^ (n + 1) with hAv
  have hsign : A = if (!s && n % 2 == 0) = true then -Av else Av := by
    cases s with
    | true =>
      have : 0 < xv := hpos rfl
      simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      rw [hA, hAv, abs_of_pos this]
    | false =>
      have hneg : xv < 0 := hneg rfl
      have hxabs : xv = -|xv| := by rw [abs_of_neg hneg, neg_neg]
      by_cases hev : n % 2 = 0
      · have : (!false && n % 2 == 0) = true := by simpa using hev
        rw [ite_eq_left this, hA, hAv]
        conv_lhs => rw [hxabs, (Nat.odd_iff.mpr (by omega : (n + 1) % 2 = 1)).neg_pow, div_neg]
      · have : ¬ (!false && n % 2 == 0) = true := by simpa using hev
        rw [ite_eq_right this, hA, hAv]
        conv_lhs => rw [hxabs, (Nat.even_iff.mpr (by omega : (n + 1) % 2 = 0)).neg_pow]
  -- the ends of the test
  obtain ⟨lv, uv, hlo, hup, hlv, huv⟩ : ∃ lv uv : ℝ,
      (if (!s && n % 2 == 0) = true then
          -(Encl.div W (Encl.exact (ofAzNat (AzNat.factorial n)))
            (Encl.powBin W Xa (n + 1))).2
        else (Encl.div W (Encl.exact (ofAzNat (AzNat.factorial n)))
            (Encl.powBin W Xa (n + 1))).1).toVal
        = some (lv : EReal) ∧
      (if (!s && n % 2 == 0) = true then
          -(Encl.div W (Encl.exact (ofAzNat (AzNat.factorial n)))
            (Encl.powBin W Xa (n + 1))).1
        else (Encl.div W (Encl.exact (ofAzNat (AzNat.factorial n)))
            (Encl.powBin W Xa (n + 1))).2).toVal
        = some (uv : EReal) ∧ lv ≤ A ∧ A ≤ uv := by
    by_cases hng : (!s && n % 2 == 0) = true
    · refine ⟨-qh, -ql, ?_, ?_, ?_, ?_⟩
      · rw [ite_eq_left hng, toVal_neg, hqh, Option.map_some, EReal.coe_neg]
      · rw [ite_eq_left hng, toVal_neg, hql, Option.map_some, EReal.coe_neg]
      · rw [hsign, ite_eq_left hng]; linarith
      · rw [hsign, ite_eq_left hng]; linarith
    · refine ⟨ql, qh, ?_, ?_, ?_, ?_⟩
      · rw [ite_eq_right hng, hql]
      · rw [ite_eq_right hng, hqh]
      · rw [hsign, ite_eq_right hng]; exact hq1
      · rw [hsign, ite_eq_right hng]; exact hq2
  obtain ⟨hi, hhi, hhi1⟩ := addCeiling_ge hup hB W
  have hR1 := rounds_setPrecRound (isFinite_of_toVal_coe hlo)
  rw [fval_of_toVal_coe hlo] at hR1
  have hR2 := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
  rw [fval_of_toVal_coe hhi] at hR2
  -- `lv ≤ A < H ≤ hi`
  have hHlo : lv < (-1) ^ (n + 1) * polygammaR n xv := by rw [hH]; linarith
  have hHhi : (-1) ^ (n + 1) * polygammaR n xv ≤ hi := by rw [hH]; linarith
  by_cases ho : n % 2 = 1
  · rw [ite_eq_left ho] at h
    rw [(Nat.even_iff.mpr (by omega : (n + 1) % 2 = 0)).neg_one_pow, one_mul] at hHlo hHhi
    exact roundingPossible_eq p mode hR1 hR2 hHlo.le hHhi (fun h' => absurd h' hHlo.ne) h
  · rw [ite_eq_right ho] at h
    obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp h
    rw [(Nat.odd_iff.mpr (by omega : (n + 1) % 2 = 1)).neg_one_pow, neg_one_mul] at hHlo hHhi
    have hr := roundingPossible_eq p (-mode) (v := -polygammaR n xv) hR1 hR2 hHlo.le hHhi
      (fun h' => absurd h' hHlo.ne) hr'
    rw [hr]
    have hneg := roundVal_neg p mode (-polygammaR n xv)
    rw [neg_neg] at hneg
    exact hneg.symm

/-- The tiny-argument path answers with the rounding of `ψ⁽ⁿ⁾(x)`. -/
theorem polygammaTiny?_eq {n : ℕ} (hn : 1 ≤ n) {s : Bool} {e : AzInt} {q : ℕ} {m : AzNat}
    (hv : FiniteValid q m) (p : ℕ) [NeZero p] (mode : RoundingMode) {r : AzFloat × Ordering}
    (h : polygammaTiny? n (finite s e q m hv) s e p mode = some r) :
    r = roundVal p mode (some ((polygammaR n (finiteVal s e m) : ℝ) : EReal)) := by
  unfold polygammaTiny? at h
  by_cases hc : e.sign = false ∧ 2 ≤ e.abs.toNat
      ∧ p + zivGuardBits + 10 + (n + 1).log2 ≤ (n + 1) * (e.abs.toNat - 2)
  swap
  · rw [ite_eq_right hc] at h
    exact absurd h (by simp)
  rw [ite_eq_left hc] at h
  obtain ⟨hs, he2, -⟩ := hc
  set xv := finiteVal s e m with hxv
  have hx : (finite s e q m hv).toVal = some (xv : EReal) := toVal_finite s e q m hv
  have hx0 : xv ≠ 0 := finiteVal_ne_zero s e hv
  -- `|x| < 2^e ≤ 1/4`
  have hquarter : |xv| ≤ 1 / 4 := by
    have hlt := (abs_finiteVal_bounds s e hv).2
    have hei : e.toInt ≤ -2 := by
      have htoInt : e.toInt = if e.sign then (e.abs.toNat : ℤ) else -(e.abs.toNat : ℤ) := rfl
      rw [htoInt, hs]
      simp only [Bool.false_eq_true, ↓reduceIte]
      omega
    have : (2 : ℝ) ^ e.toInt ≤ 2 ^ (-2 : ℤ) := zpow_le_zpow_right₀ (by norm_num) hei
    rw [← hxv] at hlt
    norm_num at this
    linarith
  have hxa : (finite s e q m hv).abs.toVal = some ((|xv| : ℝ) : EReal) := by
    rw [toVal_abs_of_isFinite (isFinite_of_toVal_coe hx), fval_of_toVal_coe hx]
  exact polygammaTinyOf_eq hn hx0 (isEnclPos_exact hxa (abs_pos.mpr hx0)) hquarter
    (fun hs' => by subst hs'; exact finiteVal_true_pos e hv)
    (fun hs' => by subst hs'; exact finiteVal_false_neg e hv) p mode h

/-- **`ψ⁽ⁿ⁾` is correctly rounded, or the fuel ran out.** -/
theorem polygammaPrecRound_eq_or (n : ℕ) (x : AzFloat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    polygammaPrecRound n x p mode = liftVal (Spec.polygamma n) x p mode ∨
      polygammaPrecRound n x p mode = (nan, .eq) := by
  have hp := NeZero.ne p
  by_cases hn : n = 0
  · subst hn
    have := digammaPrecRound_eq_or x p mode
    unfold polygammaPrecRound liftVal at *
    rw [ite_eq_left rfl]
    simpa only [Spec.polygamma_zero] using this
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  unfold polygammaPrecRound
  rw [ite_eq_right hn]
  cases x with
  | nan => left; simp [liftVal, toVal_nan]
  | infinity s =>
    left
    cases s
    · simp only [liftVal, toVal_infinity, Bool.false_eq_true, ↓reduceIte, Option.bind_some,
        Spec.polygamma_bot hn, roundVal_none]
    · simp only [liftVal, toVal_infinity, ↓reduceIte, Option.bind_some, Spec.polygamma_top hn,
        roundVal_zero]
  | zero =>
    left
    simp only [liftVal, toVal_zero, Option.bind_some]
    rw [← EReal.coe_zero, Spec.polygamma_coe_zero hn]
    by_cases ho : n % 2 = 1
    · rw [ite_eq_left ho, roundVal_top]; simp [ho]
    · rw [ite_eq_right ho, roundVal_bot]; simp [ho]
  | finite s e q m hv =>
    have hx := toVal_finite s e q m hv
    have hx0 : finiteVal s e m ≠ 0 := finiteVal_ne_zero s e hv
    simp only [liftVal, toVal_finite, Option.bind_some]
    by_cases hpole : (!s && isInteger (finite s e q m hv)) = true
    · left
      rw [ite_eq_left hpole]
      rw [Bool.and_eq_true, Bool.not_eq_true'] at hpole
      obtain ⟨hs, hi⟩ := hpole
      subst hs
      rw [Spec.polygamma_coe_of_pole hn (finiteVal_false_neg e hv)
        ((isInteger_finite false e hv).mp hi)]
      by_cases ho : n % 2 = 1
      · rw [ite_eq_left ho, ite_eq_left ho, roundVal_top]
      · rw [ite_eq_right ho, ite_eq_right ho, roundVal_none]
    · rw [ite_eq_right hpole, ite_eq_right hp]
      have hpos : s = true → 0 < finiteVal s e m := fun hs => by
        subst hs; exact finiteVal_true_pos e hv
      have hneg : s = false → ∀ k : ℤ, finiteVal s e m ≠ k := fun hs k hk => by
        subst hs
        refine hpole ?_
        rw [Bool.not_false, Bool.true_and]
        exact (isInteger_finite false e hv).mpr ⟨k, hk⟩
      have hnp : ¬ (finiteVal s e m < 0 ∧ ∃ k : ℤ, finiteVal s e m = k) := by
        rintro ⟨hlt, k, hk⟩
        cases s with
        | true => exact absurd (finiteVal_true_pos e hv) (not_lt.mpr hlt.le)
        | false => exact hneg rfl k hk
      rw [Spec.polygamma_coe hn hx0 hnp]
      split
      · next r hT => left; exact polygammaTiny?_eq hn1 hv p mode hT
      · rcases eq_or_ne (zivLoop (polygammaApprox n (finite s e q m hv) s p) p mode (lnGammaFuel p)
          (polygammaStart n e p)) (nan, .eq) with hz | hz
        · right; exact hz
        · left
          exact zivLoop_eq_of_ne_nan_or_none p mode _ _ 64
            (fun w hw => lnAbsGammaApproxOf_valid_or_none
              (fun _ hc => polygammaEnclFor_spec hn1 hx hpos hneg p hw hc) w p mode)
            _ _ (le_max_left _ _) hz

end Azurite.AzFloat
