/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LnGammaBracket
import Azurite.AzFloat.Equiv.DirectedRounding
import Azurite.AzFloat.Equiv.LnEncl
import Azurite.AzFloat.Equiv.PiBracket
import Azurite.AzFloat.Equiv.Compare
import Azurite.AzFloat.Equiv.Constants
import Azurite.AzNat.Equiv.TangentNumbers
import Azurite.AzNat.Equiv.Sub
import Azurite.AzNat.Equiv.ShiftLeft
import Azurite.Transcendental.LogGammaStirling
import Azurite.BrentZimmermann.Chapter4.StirlingLogGamma

/-!
# Equivalence: the bracket of `ln Γ`

`lnGammaBracket_spec`: for a positive float `x` and `w ≥ 64`, `lnGammaBracket x e w` encloses
`ln Γ(x)` — whatever the exponent argument `e`, which only chooses the shift
(`lnGammaBracketEncl_spec`: the same from any enclosure of `x` with a positive lower end).
The steps:
`risingEncl_spec` (the rising product), `stirlingTermEncl_spec` (a coefficient of Stirling's
series from a tangent number), `stirlingSumLoop_spec` (the partial sums, closed by the remainder
bound of `stirlingMu_eq_sum_add` at whatever term the loop stops), `stirlingMuEncl_spec`,
`lnGammaStirlingEncl_spec` (Stirling's formula for `y ≥ 1`), and the shift
`BZ.log_Gamma_eq_log_Gamma_add_sub`.
-/

namespace Azurite.AzFloat

open Finset Encl

/-! ### Enclosure helpers -/

theorem isEnclPos_exact {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (h : 0 < xv) :
    IsEnclPos (Encl.exact x) xv := ⟨xv, xv, hx, hx, h, le_rfl, le_rfl⟩

theorem isEncl0_nat (n : ℕ) : IsEncl0 (Encl.nat n) n :=
  ⟨n, n, toVal_ofAzNat_ofNat n, toVal_ofAzNat_ofNat n, Nat.cast_nonneg n, le_rfl, le_rfl⟩

theorem isEncl0_exact_zero : IsEncl (Encl.exact zero) 0 := by
  have h : zero.toVal = some ((0 : ℝ) : EReal) := by rw [toVal_zero, EReal.coe_zero]
  exact ⟨0, 0, h, h, le_rfl, le_rfl⟩

/-- Clamping the lower end at `0` keeps an enclosure of a nonnegative number. -/
theorem IsEncl.clamp0 {a : Encl} {x : ℝ} (ha : IsEncl a x) (hx : 0 ≤ x) :
    IsEncl0 (clampNonneg a.1, a.2) x := by
  obtain ⟨l, h, hl, hh, h1, h2⟩ := ha
  obtain ⟨c, hc, hc0, hcle, -⟩ := clampNonneg_spec hl
  exact ⟨c, h, hc, hh, hc0, hcle.trans (max_le h1 hx), h2⟩

/-- The rising product on enclosures. -/
theorem risingEncl_spec {V : ℕ} [NeZero V] (hV : 2 ≤ V) {X : Encl} {xv : ℝ}
    (hX : IsEnclPos X xv) : ∀ i : ℕ, IsEnclPos (risingEncl V X i) (∏ j ∈ range i, (xv + j))
  | 0 => by rw [prod_range_zero]; exact enclosesPos_one
  | i + 1 => by
    rw [prod_range_succ, risingEncl]
    exact (risingEncl_spec hV hX i).mul hV (hX.add hV (isEncl0_nat i))

/-! ### Stirling's series -/

/-- A term of Stirling's series without its sign, `a_k / y^(2k−1)`. -/
theorem stirlingTermEncl_spec {V : ℕ} [NeZero V] {M k : ℕ} (hk : 1 ≤ k) (hkM : k ≤ M) {p : Encl}
    {y : ℝ} (hp : IsEnclPos p (1 / y ^ (2 * k - 1))) :
    IsEncl0 (stirlingTermEncl V (AzNat.tangentNumbers M) k p)
      (stirlingCoeffT k / y ^ (2 * k - 1)) := by
  have hT := AzNat.toNat_tangentNumbers hk hkM
  have hTr : ((((AzNat.tangentNumbers M).getD (k - 1) 0).toNat : ℕ) : ℝ)
      = (BZ.tangentNumber k : ℝ) := by exact_mod_cast hT
  have hle : 2 ^ (2 * k) ≤ 2 ^ (4 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hD : ((AzNat.mulNat (((1 : AzNat) <<< (4 * k)) - ((1 : AzNat) <<< (2 * k)))
      (2 * k - 1)).toNat : ℝ) = (2 * k - 1) * ((4 : ℝ) ^ (2 * k) - 2 ^ (2 * k)) := by
    rw [AzNat.toNat_mulNat, AzNat.toNat_sub, AzNat.toNat_hShiftLeft, AzNat.toNat_hShiftLeft,
      Nat.shiftLeft_eq, Nat.shiftLeft_eq, AzNat.toNat_one, one_mul, one_mul]
    push_cast [Nat.cast_sub hle, Nat.cast_sub (by omega : 1 ≤ 2 * k)]
    rw [show (4 : ℝ) ^ (2 * k) = 2 ^ (4 * k) by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf]
    ring
  have hDpos : (0 : ℝ) < (2 * k - 1) * ((4 : ℝ) ^ (2 * k) - 2 ^ (2 * k)) := by
    have h1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    exact mul_pos (by linarith) (four_pow_sub_two_pow_pos hk)
  have hnum : IsEncl0 (Encl.exact (ofAzNat ((AzNat.tangentNumbers M).getD (k - 1) 0)))
      (BZ.tangentNumber k : ℝ) := by
    rw [← hTr]
    exact ⟨_, _, toVal_ofAzNat _, toVal_ofAzNat _, Nat.cast_nonneg _, le_rfl, le_rfl⟩
  have hden : IsEnclPos (Encl.exact (ofAzNat (AzNat.mulNat
      (((1 : AzNat) <<< (4 * k)) - ((1 : AzNat) <<< (2 * k))) (2 * k - 1))))
      ((2 * k - 1) * ((4 : ℝ) ^ (2 * k) - 2 ^ (2 * k))) := by
    rw [← hD]
    exact ⟨_, _, toVal_ofAzNat _, toVal_ofAzNat _, by rw [hD]; exact hDpos, le_rfl, le_rfl⟩
  have := (hnum.div (w := V) hden).mul (w := V) hp.encloses0
  unfold stirlingTermEncl
  convert this using 1
  rw [stirlingCoeffT]
  ring

/-- Closing the series at the term `k`: the remainder is between `0` and that term. -/
theorem stirlingClose_spec {V : ℕ} [NeZero V] {k : ℕ} {acc τ : Encl} {S r b μ : ℝ}
    (hacc : IsEncl acc S) (hτ : IsEncl0 τ b) (hμ : μ = S + r) (hsign : 0 ≤ (-1) ^ (k + 1) * r)
    (habs : |r| ≤ b) :
    IsEncl (if k % 2 = 1 then (acc.1, (addPrecRound acc.2 τ.2 V .Ceiling).1)
      else ((subPrecRound acc.1 τ.2 V .Floor).1, acc.2)) μ := by
  obtain ⟨l, h, hl, hh, h1, h2⟩ := hacc
  obtain ⟨tl, th, -, hth, -, -, h4⟩ := hτ
  rw [abs_le] at habs
  split_ifs with hk
  · rw [(Nat.even_iff.mpr (by omega : (k + 1) % 2 = 0)).neg_one_pow, one_mul] at hsign
    obtain ⟨u, hu, hu1⟩ := addCeiling_ge hh hth V
    exact ⟨l, u, hl, hu, by linarith, by linarith⟩
  · rw [(Nat.odd_iff.mpr (by omega : (k + 1) % 2 = 1)).neg_one_pow] at hsign
    obtain ⟨u, hu, hu1, -⟩ := subFloor_le hl hth V
    exact ⟨u, h, hu, hh, by linarith, by linarith⟩

/-- The loop encloses `μ(y)` wherever it stops. -/
theorem stirlingSumLoop_spec {V : ℕ} [NeZero V] (hV : 2 ≤ V) {M : ℕ} {inv2 : Encl} {y : ℝ}
    (hy : 0 < y) (hinv2 : IsEnclPos inv2 (1 / y ^ 2)) (tol : AzFloat) :
    ∀ (fuel k : ℕ) (p acc : Encl), 1 ≤ k → k + fuel ≤ M →
      IsEnclPos p (1 / y ^ (2 * k - 1)) →
      IsEncl acc (∑ i ∈ range (k - 1), stirlingTermT (i + 1) y) →
      IsEncl (stirlingSumLoop V (AzNat.tangentNumbers M) inv2 tol fuel k p acc)
        (DLMF.stirlingMu y)
  | 0, k, p, acc, hk, hkM, hp, hacc => by
    obtain ⟨r, hμ, hsign, habs⟩ := stirlingMu_eq_sum_add hk hy
    rw [stirlingSumLoop]
    exact stirlingClose_spec hacc (stirlingTermEncl_spec hk (by omega) hp) hμ hsign habs
  | fuel + 1, k, p, acc, hk, hkM, hp, hacc => by
    have hτ := stirlingTermEncl_spec (V := V) hk (by omega : k ≤ M) hp
    rw [stirlingSumLoop]
    split_ifs with hstop hodd hodd
    · obtain ⟨r, hμ, hsign, habs⟩ := stirlingMu_eq_sum_add hk hy
      have := stirlingClose_spec (V := V) hacc hτ hμ hsign habs
      rwa [ite_eq_left hodd] at this
    · obtain ⟨r, hμ, hsign, habs⟩ := stirlingMu_eq_sum_add hk hy
      have := stirlingClose_spec (V := V) hacc hτ hμ hsign habs
      rwa [ite_eq_right hodd] at this
    all_goals
      have hp' : IsEnclPos (Encl.mul V p inv2) (1 / y ^ (2 * (k + 1) - 1)) := by
        have := hp.mul hV hinv2
        convert this using 1
        rw [show 2 * (k + 1) - 1 = (2 * k - 1) + 2 by omega, pow_add]
        field_simp
      have hsum : ∑ i ∈ range (k + 1 - 1), stirlingTermT (i + 1) y
          = ∑ i ∈ range (k - 1), stirlingTermT (i + 1) y + stirlingTermT k y := by
        rw [show k + 1 - 1 = (k - 1) + 1 by omega, sum_range_succ,
          show k - 1 + 1 = k by omega]
      refine stirlingSumLoop_spec hV hy hinv2 tol fuel (k + 1) _ _ (by omega) (by omega) hp' ?_
      rw [hsum]
    · have : stirlingTermT k y = stirlingCoeffT k / y ^ (2 * k - 1) := by
        rw [stirlingTermT, (Nat.even_iff.mpr (by omega : (k + 1) % 2 = 0)).neg_one_pow, one_mul]
      rw [this]
      exact hacc.add hτ.encloses
    · have : ∑ i ∈ range (k - 1), stirlingTermT (i + 1) y + stirlingTermT k y
          = ∑ i ∈ range (k - 1), stirlingTermT (i + 1) y - stirlingCoeffT k / y ^ (2 * k - 1) := by
        rw [stirlingTermT, (Nat.odd_iff.mpr (by omega : (k + 1) % 2 = 1)).neg_one_pow]
        ring
      rw [this]
      exact hacc.sub hτ.encloses

/-- The enclosure of `μ(y)`. -/
theorem stirlingMuEncl_spec {V : ℕ} [NeZero V] (hV : 2 ≤ V) {M : ℕ} (hM : 1 ≤ M) {Y : Encl}
    {y : ℝ} (hY : IsEnclPos Y y) (tol : AzFloat) :
    IsEncl (stirlingMuEncl V M Y tol) (DLMF.stirlingMu y) := by
  have hy : 0 < y := by obtain ⟨l, h, -, -, h0, h1, -⟩ := hY; linarith
  have hinv : IsEnclPos (Encl.div V (Encl.exact one) Y) (1 / y) := enclosesPos_one.div hV hY
  have hinv2 : IsEnclPos (Encl.mul V (Encl.div V (Encl.exact one) Y)
      (Encl.div V (Encl.exact one) Y)) (1 / y ^ 2) := by
    have := hinv.mul hV hinv
    convert this using 1
    field_simp
  unfold stirlingMuEncl
  refine stirlingSumLoop_spec hV hy hinv2 tol (M - 1) 1 _ _ le_rfl (by omega) ?_ ?_
  · simpa using hinv
  · simpa using isEncl0_exact_zero

/-- Stirling's formula on enclosures, without the constant: `ln Γ(y) − ½ ln (2π)` for
`y ≥ 1`. -/
theorem lnGammaStirlingEncl_spec {V : ℕ} (hV : 64 ≤ V) {M : ℕ} (hM : 1 ≤ M) {Y : Encl} {y : ℝ}
    (hY : IsEnclPos Y y) (hy1 : 1 ≤ y) (tol : AzFloat) :
    IsEncl (lnGammaStirlingEncl V M Y tol)
      (Real.log (Real.Gamma y) - 1 / 2 * Real.log (2 * Real.pi)) := by
  have : NeZero V := ⟨by omega⟩
  have hV2 : 2 ≤ V := by omega
  have hμ := stirlingMuEncl_spec hV2 hM hY tol
  have hlnY := (lnOfEncl_pos hY hV).clamp0 (Real.log_nonneg hy1)
  have hhalf : IsEnclPos (Encl.div V (Encl.exact one) (Encl.nat 2)) (1 / 2 : ℝ) := by
    have := enclosesPos_one.div hV2 (enclosesPos_nat (n := 2) (by norm_num))
    simpa using this
  have hsub := hY.encloses0.encloses.subNonneg (w := V) hhalf.encloses0.encloses
    (by linarith : (1 / 2 : ℝ) ≤ y)
  have hA := hsub.mul (w := V) hlnY
  have := (hA.encloses.sub (w := V) hY.encloses0.encloses).add (w := V) hμ
  unfold lnGammaStirlingEncl
  convert this using 1
  rw [DLMF.stirlingMu]
  ring

/-- Halving an enclosure. -/
theorem IsEncl.half {a : Encl} {v : ℝ} (h : IsEncl a v) : IsEncl (Encl.half a) (v / 2) := by
  obtain ⟨l, u, hl, hu, h1, h2⟩ := h
  have e1 := toVal_shiftLeft_of_toVal hl (AzInt.ofInt (-1))
  have e2 := toVal_shiftLeft_of_toVal hu (AzInt.ofInt (-1))
  rw [AzInt.toInt_ofInt, zpow_neg_one, ← div_eq_mul_inv] at e1 e2
  exact ⟨l / 2, u / 2, e1, e2, by linarith, by linarith⟩

/-- The shift is `0` only for `x ≥ 1`. -/
theorem one_le_of_lnGammaShift_eq_zero {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    {e : AzInt} {L : ℕ} (h : lnGammaShift x e L = 0) : 1 ≤ xv := by
  unfold lnGammaShift at h
  dsimp only at h
  have h2 : (if le one x = true then 0 else 1) = 0 := by omega
  by_contra hcon
  rw [ite_eq_right (fun hle => hcon ((le_eq_true_iff toVal_one' hx).mp hle))] at h2
  omega

/-- **`lnGammaBracketEncl X e w` encloses `ln Γ(x)`** for an enclosure `X` of `x` with a
positive lower end (`w ≥ 64`). -/
theorem lnGammaBracketEncl_spec {X : Encl} {xv : ℝ} (hX : IsEnclPos X xv) (e : AzInt) {w : ℕ}
    (hw : 64 ≤ w) : IsEncl (lnGammaBracketEncl X e w) (Real.log (Real.Gamma xv)) := by
  set L := lnGammaShiftExp w with hL
  set V := w + 2 * L + 8 + 2 * w.log2 with hVdef
  have hV : 64 ≤ V := by omega
  have : NeZero V := ⟨by omega⟩
  obtain ⟨xl, xh, hxl, -, hxl0, hxl1, -⟩ := id hX
  have hpos : 0 < xv := by linarith
  have hV2 : 2 ≤ V := by omega
  have hM : ∀ E, 1 ≤ lnGammaTerms w E := fun E => by
    unfold lnGammaTerms; exact le_trans (by norm_num) (Nat.le_add_left 3 _)
  have h2π : IsEnclPos (Encl.mul V (Encl.nat 2) (Encl.pi V)) (2 * Real.pi) := by
    have := (enclosesPos_nat (n := 2) (by norm_num)).mul hV2 (enclosesPos_pi hV)
    simpa using this
  have hπ : 0 < 2 * Real.pi := by positivity
  unfold lnGammaBracketEncl
  simp only [← hL, ← hVdef]
  by_cases hδ : lnGammaShift X.1 e L = 0
  · rw [ite_eq_left hδ]
    have := (lnGammaStirlingEncl_spec hV
      (hM (max (L + 1) (if e.sign then e.abs.toNat else 0))) hX
      ((one_le_of_lnGammaShift_eq_zero hxl hδ).trans hxl1)
      (powerOf2 (-(AzNat.ofNat (w + 16)).toAzInt))).add (w := V) (lnOfEncl_pos h2π hV).half
    convert this using 1
    ring
  · rw [ite_eq_right hδ]
    have hδ1 : (1 : ℝ) ≤ (lnGammaShift X.1 e L : ℕ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hδ
    have hY : IsEnclPos (Encl.add V X (Encl.nat (lnGammaShift X.1 e L)))
        (xv + (lnGammaShift X.1 e L : ℕ)) := hX.add hV2 (isEncl0_nat _)
    have hS := lnGammaStirlingEncl_spec hV (hM (max (L + 1) (if e.sign then e.abs.toNat else 0)))
      hY (by linarith) (powerOf2 (-(AzNat.ofNat (w + 16)).toAzInt))
    have hP := risingEncl_spec hV2 hX (lnGammaShift X.1 e L)
    have hPpos : 0 < ∏ j ∈ range (lnGammaShift X.1 e L), (xv + j) :=
      prod_pos fun i _ => by
        have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
        linarith
    have hQ := lnOfEncl_pos (h2π.div hV2 (hP.mul hV2 hP)) hV
    have := hS.add (w := V) hQ.half
    convert this using 1
    rw [BZ.log_Gamma_eq_log_Gamma_add_sub hpos (lnGammaShift X.1 e L),
      Real.log_div hπ.ne' (mul_pos hPpos hPpos).ne', Real.log_mul hPpos.ne' hPpos.ne',
      Real.log_prod]
    · ring
    · intro i _
      have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      exact (by linarith : (0 : ℝ) < xv + i).ne'

/-- **`lnGammaBracket x e w` encloses `ln Γ(x)`** for a positive float `x` (`w ≥ 64`). -/
theorem lnGammaBracket_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hpos : 0 < xv) (e : AzInt) {w : ℕ} (hw : 64 ≤ w) :
    IsEncl (lnGammaBracket x e w) (Real.log (Real.Gamma xv)) :=
  lnGammaBracketEncl_spec (isEnclPos_exact hx hpos) e hw

/-- The directed roundings of a positive rational enclose it, with a positive lower end. -/
theorem lnGammaRatEncl_spec (q : AzRat) (hq : 0 < ((AzRat.toRat q : ℚ) : ℝ)) (w : ℕ) :
    IsEnclPos (lnGammaRatEncl q w) ((AzRat.toRat q : ℚ) : ℝ) := by
  have : NeZero (w + 32) := ⟨by omega⟩
  obtain ⟨l, hl, hl1, hl2⟩ := ofAzRatRound_floor_abs q (w + 32)
  obtain ⟨h, hh, hh1, -⟩ := ofAzRatRound_ceiling_abs q (w + 32)
  refine ⟨l, h, hl, hh, ?_, hl1, hh1⟩
  have hpow : (1 / 2 : ℝ) ^ (w + 32) ≤ 1 / 4 := by
    calc (1 / 2 : ℝ) ^ (w + 32) ≤ (1 / 2 : ℝ) ^ 2 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 4 := by norm_num
  rw [abs_of_pos hq] at hl2
  nlinarith

end Azurite.AzFloat
