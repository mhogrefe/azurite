/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.EnclWidth
import Azurite.Transcendental.StirlingTermBound

/-!
# The width of the bracket of `ln Γ`

`Equiv/LnGammaBracket.lean` proves that `lnGammaBracketEncl` encloses `ln Γ(x)`; here its width
is bounded, piece by piece, with the calculus of `Equiv/EnclWidth.lean`:

* `risingEncl_width`: the rising product, relative width `i (λ₀ + 12u)`;
* `stirlingTermEncl_width`, `stirlingSumLoop_width`, `stirlingMuEncl_width`: Stirling's series —
  every term added costs `2TΛ + 4Bu`, and the series is closed by a term that is below the
  tolerance or is the last of the table;
* `lnGammaStirlingEncl_width`: Stirling's formula.
-/

namespace Azurite.AzFloat

open Finset Encl

variable {V : ℕ}

/-- The rising product: relative width `i (λ₀ + 12 u)`. -/
theorem risingEncl_width [NeZero V] (hu : (1 / 2 : ℝ) ^ V ≤ 1 / 8) {X : Encl} {xv lam₀ : ℝ}
    (hX : LEncl X xv lam₀) (h0 : 0 ≤ lam₀) :
    ∀ i : ℕ, LEncl (risingEncl V X i) (∏ j ∈ range i, (xv + j))
      (i * (lam₀ + 12 * (1 / 2 : ℝ) ^ V))
  | 0 => by
    rw [prod_range_zero, risingEncl]
    simpa using LEncl.exact toVal_one' one_pos
  | i + 1 => by
    rw [prod_range_succ, risingEncl]
    have h1 := hX.add_exact (w := V) (b := Encl.nat i) hu h0 (toVal_ofAzNat_ofNat i)
      (toVal_ofAzNat_ofNat i) (Nat.cast_nonneg i)
    have h2 := (risingEncl_width hu hX h0 i).mul hu h1
    refine h2.mono (le_of_eq ?_)
    push_cast
    ring

/-- A term of Stirling's series: the relative width of the power, plus `12 u`. -/
theorem stirlingTermEncl_width [NeZero V] (hu : (1 / 2 : ℝ) ^ V ≤ 1 / 8) {M k : ℕ} (hk : 1 ≤ k)
    (hkM : k ≤ M) {p : Encl} {y lam : ℝ} (hp : LEncl p (1 / y ^ (2 * k - 1)) lam) :
    LEncl (stirlingTermEncl V (AzNat.tangentNumbers M) k p)
      (stirlingCoeffT k / y ^ (2 * k - 1)) (lam + 12 * (1 / 2 : ℝ) ^ V) := by
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
  have hTpos : (0 : ℝ) < (BZ.tangentNumber k : ℝ) := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    exact_mod_cast BZ.tangentNumber_pos j
  have hnum : LEncl (Encl.exact (ofAzNat ((AzNat.tangentNumbers M).getD (k - 1) 0)))
      (BZ.tangentNumber k : ℝ) 0 := by
    rw [← hTr]
    exact LEncl.exact (toVal_ofAzNat _) (by rw [hTr]; exact hTpos)
  have hden : LEncl (Encl.exact (ofAzNat (AzNat.mulNat
      (((1 : AzNat) <<< (4 * k)) - ((1 : AzNat) <<< (2 * k))) (2 * k - 1))))
      ((2 * k - 1) * ((4 : ℝ) ^ (2 * k) - 2 ^ (2 * k))) 0 := by
    rw [← hD]
    exact LEncl.exact (toVal_ofAzNat _) (by rw [hD]; exact hDpos)
  have := ((hnum.div (w := V) hu hden).mul (w := V) hu hp).mono
    (le_of_eq (by ring : (0 : ℝ) + 0 + 6 * (1 / 2 : ℝ) ^ V + lam + 6 * (1 / 2 : ℝ) ^ V
      = lam + 12 * (1 / 2 : ℝ) ^ V))
  unfold stirlingTermEncl
  convert this using 1
  rw [stirlingCoeffT]
  ring

theorem abs_stirlingTermT {k : ℕ} (hk : 1 ≤ k) {y : ℝ} (hy : 0 < y) :
    |stirlingTermT k y| = stirlingCoeffT k / y ^ (2 * k - 1) := by
  unfold stirlingTermT
  rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (stirlingCoeffT_pos hk), abs_of_pos (pow_pos hy _)]

theorem abs_sum_stirlingTermT_le {M : ℕ} {y T : ℝ} (hy : 0 < y)
    (hterm : ∀ k, 1 ≤ k → k ≤ M → stirlingCoeffT k / y ^ (2 * k - 1) ≤ T) {n : ℕ} (hn : n ≤ M) :
    |∑ i ∈ range n, stirlingTermT (i + 1) y| ≤ n * T := by
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i ∈ range n, |stirlingTermT (i + 1) y| ≤ ∑ _i ∈ range n, T :=
        sum_le_sum fun i hi => by
          rw [abs_stirlingTermT (by omega) hy]
          exact hterm (i + 1) (by omega) (by have := mem_range.mp hi; omega)
    _ = n * T := by rw [sum_const, card_range, nsmul_eq_mul]

/-- Closing the series, with the width. -/
theorem stirlingClose_width [NeZero V] {k : ℕ} {acc τ : Encl} {S r μ ε th B : ℝ}
    (hacc : AEncl acc S ε) (hτ : τ.2.toVal = some (th : EReal)) (hμ : μ = S + r)
    (hsign : 0 ≤ (-1) ^ (k + 1) * r) (habs : |r| ≤ th) (hB : |S| + ε + th ≤ B) :
    AEncl (if k % 2 = 1 then (acc.1, (addPrecRound acc.2 τ.2 V .Ceiling).1)
      else ((subPrecRound acc.1 τ.2 V .Floor).1, acc.2)) μ
      (ε + th + 2 * B * (1 / 2 : ℝ) ^ V) := by
  obtain ⟨l, h, hl, hh, h1, h2, h3⟩ := hacc
  have hu0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ V := by positivity
  have hS := abs_le.mp (le_refl |S|)
  have hr := abs_le.mp habs
  have hth0 : 0 ≤ th := (abs_nonneg r).trans habs
  split_ifs with hk
  · rw [(Nat.even_iff.mpr (by omega : (k + 1) % 2 = 0)).neg_one_pow, one_mul] at hsign
    obtain ⟨u, hu, hu1, hu2⟩ := addCeiling_abs hh hτ V
    have hb : |h + th| ≤ B := by
      rw [abs_le]
      constructor <;> linarith
    refine ⟨l, u, hl, hu, by linarith, by linarith, ?_⟩
    nlinarith [mul_le_mul_of_nonneg_right hb hu0]
  · rw [(Nat.odd_iff.mpr (by omega : (k + 1) % 2 = 1)).neg_one_pow] at hsign
    obtain ⟨u, hu, hu1, hu2⟩ := subFloor_abs hl hτ V
    have hb : |l - th| ≤ B := by
      rw [abs_le]
      constructor <;> linarith
    refine ⟨u, h, hu, hh, by linarith, by linarith, ?_⟩
    nlinarith [mul_le_mul_of_nonneg_right hb hu0]

/-- The facts at one step of the loop: the term, its upper end, and the magnitudes. -/
theorem stirlingStep_facts [NeZero V] (hu : (1 / 2 : ℝ) ^ V ≤ 1 / 8) {M : ℕ} {y : ℝ}
    (hy : 0 < y) {Lam T B : ℝ} (hLam : Lam ≤ 1 / 2) (hT0 : 0 ≤ T)
    (hterm : ∀ k, 1 ≤ k → k ≤ M → stirlingCoeffT k / y ^ (2 * k - 1) ≤ T)
    (hBu : 4 * B * (1 / 2 : ℝ) ^ V ≤ 1)
    (hB : M * (T + 2 * T * Lam + 1) + 2 * T + 1 ≤ B) {k : ℕ} {p : Encl} {lam ε : ℝ}
    (hk : 1 ≤ k) (hkM : k ≤ M) (hp : LEncl p (1 / y ^ (2 * k - 1)) lam) (hlam : 0 ≤ lam)
    (hlamL : lam + 12 * (1 / 2 : ℝ) ^ V ≤ Lam)
    (hε : ε ≤ (k - 1 : ℕ) * (2 * T * Lam + 4 * B * (1 / 2 : ℝ) ^ V)) :
    0 ≤ Lam ∧ 0 ≤ B ∧ 2 * T * Lam ≤ T ∧ 0 ≤ 2 * T * Lam + 4 * B * (1 / 2 : ℝ) ^ V ∧
      (∃ th : ℝ, (stirlingTermEncl V (AzNat.tangentNumbers M) k p).2.toVal = some (th : EReal) ∧
        stirlingCoeffT k / y ^ (2 * k - 1) ≤ th ∧
        th ≤ 2 * (stirlingCoeffT k / y ^ (2 * k - 1))) ∧
      AEncl (stirlingTermEncl V (AzNat.tangentNumbers M) k p)
        (stirlingCoeffT k / y ^ (2 * k - 1)) (2 * T * Lam) ∧
      |∑ i ∈ range (k - 1), stirlingTermT (i + 1) y| + ε + 2 * T ≤ B := by
  have hu0 : (0 : ℝ) < (1 / 2 : ℝ) ^ V := by positivity
  have hLam0 : 0 ≤ Lam := by linarith
  have hTL0 : 0 ≤ T * Lam := mul_nonneg hT0 hLam0
  have hTL : 2 * T * Lam ≤ T := by nlinarith
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hB0 : 0 ≤ B := by
    have := mul_nonneg hM0 (by linarith : (0 : ℝ) ≤ T + 2 * T * Lam + 1)
    linarith
  have hD0 : 0 ≤ 2 * T * Lam + 4 * B * (1 / 2 : ℝ) ^ V := by
    have := mul_nonneg hB0 hu0.le
    linarith
  have hτ := (stirlingTermEncl_width hu hk hkM hp).mono hlamL
  have htk := hterm k hk hkM
  have htk0 : 0 < stirlingCoeffT k / y ^ (2 * k - 1) :=
    div_pos (stirlingCoeffT_pos hk) (pow_pos hy _)
  have hτA := (hτ.toA hLam0 hLam).toA
  obtain ⟨tl, th, htl, hth, p0, a1, b1, c1⟩ := hτ
  have hexp2 : Real.exp Lam ≤ 2 := by
    have := Real.exp_le_exp.mpr hLam
    have h2 : Real.exp (1 / 2) ≤ 2 := by
      have := Real.exp_one_lt_d9
      have hsq : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_pos (1 / 2 : ℝ)]
    linarith
  have hth2 : th ≤ 2 * (stirlingCoeffT k / y ^ (2 * k - 1)) := by
    calc th ≤ tl * Real.exp Lam := c1
      _ ≤ (stirlingCoeffT k / y ^ (2 * k - 1)) * 2 :=
          mul_le_mul a1 hexp2 (Real.exp_pos _).le htk0.le
      _ = _ := by ring
  have hsum := abs_sum_stirlingTermT_le hy hterm (n := k - 1) (by omega)
  have hk1 : ((k - 1 : ℕ) : ℝ) ≤ M := by exact_mod_cast (by omega : k - 1 ≤ M)
  refine ⟨hLam0, hB0, hTL, hD0, ⟨th, hth, b1, hth2⟩, hτA.mono ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_right htk hLam0
    linarith
  · have e1 : ((k - 1 : ℕ) : ℝ) * T ≤ M * T := mul_le_mul_of_nonneg_right hk1 hT0
    have e2 : ((k - 1 : ℕ) : ℝ) * (2 * T * Lam + 4 * B * (1 / 2 : ℝ) ^ V)
        ≤ M * (2 * T * Lam + 1) := mul_le_mul hk1 (by linarith) hD0 hM0
    linarith

/-- Adding a term to the partial sum. -/
theorem stirlingAcc_width [NeZero V] {M k : ℕ} (hk : 1 ≤ k) {p acc : Encl} {y ε εt T B : ℝ}
    (hy : 0 < y) (hacc : AEncl acc (∑ i ∈ range (k - 1), stirlingTermT (i + 1) y) ε)
    (hτ : AEncl (stirlingTermEncl V (AzNat.tangentNumbers M) k p)
      (stirlingCoeffT k / y ^ (2 * k - 1)) εt)
    (htk : stirlingCoeffT k / y ^ (2 * k - 1) ≤ T) (hεt : εt ≤ T)
    (hmag : |∑ i ∈ range (k - 1), stirlingTermT (i + 1) y| + ε + 2 * T ≤ B) :
    AEncl (if k % 2 = 1
        then Encl.add V acc (stirlingTermEncl V (AzNat.tangentNumbers M) k p)
        else Encl.sub V acc (stirlingTermEncl V (AzNat.tangentNumbers M) k p))
      (∑ i ∈ range (k + 1 - 1), stirlingTermT (i + 1) y)
      (ε + εt + 4 * B * (1 / 2 : ℝ) ^ V) := by
  have hsum : ∑ i ∈ range (k + 1 - 1), stirlingTermT (i + 1) y
      = ∑ i ∈ range (k - 1), stirlingTermT (i + 1) y + stirlingTermT k y := by
    rw [show k + 1 - 1 = (k - 1) + 1 by omega, sum_range_succ, show k - 1 + 1 = k by omega]
  have htk0 : 0 < stirlingCoeffT k / y ^ (2 * k - 1) :=
    div_pos (stirlingCoeffT_pos hk) (pow_pos hy _)
  rw [hsum]
  split_ifs with hodd
  · have e : stirlingTermT k y = stirlingCoeffT k / y ^ (2 * k - 1) := by
      rw [stirlingTermT, (Nat.even_iff.mpr (by omega : (k + 1) % 2 = 0)).neg_one_pow, one_mul]
    rw [e]
    refine hacc.add (w := V) hτ (B := B) ?_
    have h1 := abs_add_le (∑ i ∈ range (k - 1), stirlingTermT (i + 1) y)
      (stirlingCoeffT k / y ^ (2 * k - 1))
    rw [abs_of_pos htk0] at h1
    linarith
  · have e : ∑ i ∈ range (k - 1), stirlingTermT (i + 1) y + stirlingTermT k y
        = ∑ i ∈ range (k - 1), stirlingTermT (i + 1) y
          - stirlingCoeffT k / y ^ (2 * k - 1) := by
      rw [stirlingTermT, (Nat.odd_iff.mpr (by omega : (k + 1) % 2 = 1)).neg_one_pow]
      ring
    rw [e]
    refine hacc.sub (w := V) hτ (B := B) ?_
    have h1 := abs_sub (∑ i ∈ range (k - 1), stirlingTermT (i + 1) y)
      (stirlingCoeffT k / y ^ (2 * k - 1))
    rw [abs_of_pos htk0] at h1
    linarith

/-- **The width of the sum of Stirling's series.**  `Λ ≤ 1/2` bounds the relative widths of
all the terms, `T` the terms themselves, `B` the magnitudes; every term added costs
`2TΛ + 4Bu`, and the closing term is below `tol` or is the last one, of index `M`. -/
theorem stirlingSumLoop_width [NeZero V] (hu : (1 / 2 : ℝ) ^ V ≤ 1 / 8) {M : ℕ} {inv2 : Encl}
    {y lam₂ : ℝ} (hy : 0 < y) (hinv2 : LEncl inv2 (1 / y ^ 2) lam₂) {tol : AzFloat} {tolv : ℝ}
    (htol : tol.toVal = some (tolv : EReal)) {Lam T B : ℝ} (hLam : Lam ≤ 1 / 2) (hT0 : 0 ≤ T)
    (hterm : ∀ k, 1 ≤ k → k ≤ M → stirlingCoeffT k / y ^ (2 * k - 1) ≤ T)
    (hBu : 4 * B * (1 / 2 : ℝ) ^ V ≤ 1)
    (hB : M * (T + 2 * T * Lam + 1) + 2 * T + 1 ≤ B) :
    ∀ (fuel k : ℕ) (p acc : Encl) (lam ε : ℝ), 1 ≤ k → k + fuel = M →
      LEncl p (1 / y ^ (2 * k - 1)) lam → 0 ≤ lam →
      lam + fuel * (lam₂ + 6 * (1 / 2 : ℝ) ^ V) + 12 * (1 / 2 : ℝ) ^ V ≤ Lam →
      AEncl acc (∑ i ∈ range (k - 1), stirlingTermT (i + 1) y) ε →
      ε ≤ (k - 1 : ℕ) * (2 * T * Lam + 4 * B * (1 / 2 : ℝ) ^ V) →
      AEncl (stirlingSumLoop V (AzNat.tangentNumbers M) inv2 tol fuel k p acc)
        (DLMF.stirlingMu y)
        (ε + fuel * (2 * T * Lam + 4 * B * (1 / 2 : ℝ) ^ V)
          + max tolv (2 * (stirlingCoeffT M / y ^ (2 * M - 1))) + 2 * B * (1 / 2 : ℝ) ^ V) := by
  have hu0 : (0 : ℝ) < (1 / 2 : ℝ) ^ V := by positivity
  intro fuel
  induction fuel with
  | zero =>
    intro k p acc lam ε hk hkM hp hlam hlamL hacc hε
    have hkM' : k = M := by omega
    obtain ⟨hLam0, hB0, hTL, hD0, ⟨th, hth, hth1, hth2⟩, hτA, hmag⟩ :=
      stirlingStep_facts hu hy hLam hT0 hterm hBu hB hk (by omega) hp hlam
        (by simpa using hlamL) hε
    obtain ⟨r, hμ, hsign, habs⟩ := stirlingMu_eq_sum_add hk hy
    rw [stirlingSumLoop]
    have htkT := hterm k hk (by omega)
    have := stirlingClose_width (V := V) hacc hth hμ hsign (habs.trans hth1)
      (B := B) (by linarith)
    refine this.mono ?_
    have : th ≤ max tolv (2 * (stirlingCoeffT M / y ^ (2 * M - 1))) := by
      rw [← hkM']
      exact hth2.trans (le_max_right _ _)
    simp only [Nat.cast_zero, zero_mul, add_zero]
    linarith
  | succ fuel ih =>
    intro k p acc lam ε hk hkM hp hlam hlamL hacc hε
    have hf0 : (0 : ℝ) ≤ fuel := Nat.cast_nonneg fuel
    have hlam₂ : 0 ≤ lam₂ + 6 * (1 / 2 : ℝ) ^ V := by
      obtain ⟨l, h, -, -, p0, a1, b1, c1⟩ := hinv2
      by_contra hneg
      push Not at hneg
      have : Real.exp lam₂ < 1 := by
        have := Real.exp_lt_exp.mpr (by linarith : lam₂ < 0)
        rwa [Real.exp_zero] at this
      nlinarith
    push_cast at hlamL
    have hlamL' : lam + 12 * (1 / 2 : ℝ) ^ V ≤ Lam := by
      have := mul_nonneg hf0 hlam₂
      linarith
    obtain ⟨hLam0, hB0, hTL, hD0, ⟨th, hth, hth1, hth2⟩, hτA, hmag⟩ :=
      stirlingStep_facts hu hy hLam hT0 hterm hBu hB hk (by omega) hp hlam hlamL' hε
    have htkT := hterm k hk (by omega)
    rw [stirlingSumLoop]
    by_cases hstop : le (stirlingTermEncl V (AzNat.tangentNumbers M) k p).2 tol = true
    · simp only [hstop, ↓reduceIte]
      have hthtol : th ≤ tolv := (le_eq_true_iff hth htol).mp hstop
      obtain ⟨r, hμ, hsign, habs⟩ := stirlingMu_eq_sum_add hk hy
      have := stirlingClose_width (V := V) hacc hth hμ hsign (habs.trans hth1)
        (B := B) (by linarith)
      refine this.mono ?_
      have h1 : th ≤ max tolv (2 * (stirlingCoeffT M / y ^ (2 * M - 1))) :=
        hthtol.trans (le_max_left _ _)
      have h2 : (0 : ℝ) ≤ ((fuel + 1 : ℕ) : ℝ) * (2 * T * Lam + 4 * B * (1 / 2 : ℝ) ^ V) :=
        mul_nonneg (Nat.cast_nonneg _) hD0
      linarith
    · simp only [hstop, Bool.false_eq_true, ↓reduceIte]
      have hp' : LEncl (Encl.mul V p inv2) (1 / y ^ (2 * (k + 1) - 1))
          (lam + lam₂ + 6 * (1 / 2 : ℝ) ^ V) := by
        have := hp.mul hu hinv2
        convert this using 1
        rw [show 2 * (k + 1) - 1 = (2 * k - 1) + 2 by omega, pow_add]
        field_simp
      have hlam' : 0 ≤ lam + lam₂ + 6 * (1 / 2 : ℝ) ^ V := by linarith
      have hlamL'' : lam + lam₂ + 6 * (1 / 2 : ℝ) ^ V
          + (fuel : ℝ) * (lam₂ + 6 * (1 / 2 : ℝ) ^ V) + 12 * (1 / 2 : ℝ) ^ V ≤ Lam := by
        linarith
      have hε' : ε + 2 * T * Lam + 4 * B * (1 / 2 : ℝ) ^ V
          ≤ ((k + 1 - 1 : ℕ) : ℝ) * (2 * T * Lam + 4 * B * (1 / 2 : ℝ) ^ V) := by
        have e : ((k + 1 - 1 : ℕ) : ℝ) = ((k - 1 : ℕ) : ℝ) + 1 := by
          rw [show k + 1 - 1 = (k - 1) + 1 by omega]
          push_cast
          ring
        rw [e]
        linarith
      have hacc' := stirlingAcc_width (V := V) (M := M) (p := p) hk hy hacc hτA htkT hTL hmag
      have := ih (k + 1) _ _ _ _ (by omega) (by omega) hp' hlam' hlamL'' hacc' hε'
      refine this.mono (le_of_eq ?_)
      push_cast
      ring

/-- **The width of the enclosure of `μ(y)`**: `Λ = 2M (λ_Y + 12u)` bounds the relative widths
of the terms. -/
theorem stirlingMuEncl_width [NeZero V] (hu : (1 / 2 : ℝ) ^ V ≤ 1 / 8) {M : ℕ} (hM : 1 ≤ M)
    {Y : Encl} {y lamY : ℝ} (hY : LEncl Y y lamY) (hlamY : 0 ≤ lamY) {tol : AzFloat} {tolv : ℝ}
    (htol : tol.toVal = some (tolv : EReal)) {T B : ℝ} (hT0 : 0 ≤ T)
    (hterm : ∀ k, 1 ≤ k → k ≤ M → stirlingCoeffT k / y ^ (2 * k - 1) ≤ T)
    (hLam : 2 * M * (lamY + 12 * (1 / 2 : ℝ) ^ V) ≤ 1 / 2)
    (hBu : 4 * B * (1 / 2 : ℝ) ^ V ≤ 1)
    (hB : M * (T + 2 * T * (2 * M * (lamY + 12 * (1 / 2 : ℝ) ^ V)) + 1) + 2 * T + 1 ≤ B) :
    AEncl (stirlingMuEncl V M Y tol) (DLMF.stirlingMu y)
      (M * (2 * T * (2 * M * (lamY + 12 * (1 / 2 : ℝ) ^ V)) + 4 * B * (1 / 2 : ℝ) ^ V)
        + max tolv (2 * (stirlingCoeffT M / y ^ (2 * M - 1))) + 2 * B * (1 / 2 : ℝ) ^ V) := by
  have hy : 0 < y := hY.pos
  have hu0 : (0 : ℝ) < (1 / 2 : ℝ) ^ V := by positivity
  set Lam := 2 * M * (lamY + 12 * (1 / 2 : ℝ) ^ V) with hLamdef
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hLam0 : 0 ≤ Lam := by rw [hLamdef]; positivity
  have hinv : LEncl (Encl.div V (Encl.exact one) Y) (1 / y) (lamY + 6 * (1 / 2 : ℝ) ^ V) :=
    ((LEncl.exact toVal_one' one_pos).div hu hY).mono (by linarith)
  have hinv2 : LEncl (Encl.mul V (Encl.div V (Encl.exact one) Y)
      (Encl.div V (Encl.exact one) Y)) (1 / y ^ 2) (2 * lamY + 18 * (1 / 2 : ℝ) ^ V) := by
    have := (hinv.mul hu hinv).mono (le_of_eq (by ring :
      lamY + 6 * (1 / 2 : ℝ) ^ V + (lamY + 6 * (1 / 2 : ℝ) ^ V) + 6 * (1 / 2 : ℝ) ^ V
        = 2 * lamY + 18 * (1 / 2 : ℝ) ^ V))
    convert this using 1
    field_simp
  have hacc : AEncl (Encl.exact zero) (∑ i ∈ range (1 - 1), stirlingTermT (i + 1) y) 0 := by
    have h : zero.toVal = some ((0 : ℝ) : EReal) := by rw [toVal_zero, EReal.coe_zero]
    rw [Nat.sub_self, range_zero, sum_empty]
    exact ⟨0, 0, h, h, le_rfl, le_rfl, by simp⟩
  have hD0 : 0 ≤ 2 * T * Lam + 4 * B * (1 / 2 : ℝ) ^ V := by
    have hB0 : 0 ≤ B := by
      have := mul_nonneg (Nat.cast_nonneg (α := ℝ) M)
        (by nlinarith [mul_nonneg hT0 hLam0] : (0 : ℝ) ≤ T + 2 * T * Lam + 1)
      linarith
    have := mul_nonneg hB0 hu0.le
    nlinarith [mul_nonneg hT0 hLam0]
  have hcond : lamY + 6 * (1 / 2 : ℝ) ^ V
      + ((M - 1 : ℕ) : ℝ) * (2 * lamY + 18 * (1 / 2 : ℝ) ^ V + 6 * (1 / 2 : ℝ) ^ V)
      + 12 * (1 / 2 : ℝ) ^ V ≤ Lam := by
    rw [hLamdef, Nat.cast_sub hM]
    push_cast
    nlinarith
  have := stirlingSumLoop_width hu hy hinv2 htol hLam hT0 hterm hBu hB (M - 1) 1 _ _ _ 0
    le_rfl (by omega) (by simpa using hinv) (by linarith) hcond hacc (by simp)
  unfold stirlingMuEncl
  refine this.mono ?_
  have hM' : ((M - 1 : ℕ) : ℝ) ≤ M := by exact_mod_cast Nat.sub_le M 1
  have := mul_le_mul_of_nonneg_right hM' hD0
  linarith

/-- The main term `(y − ½) ln y` of Stirling's formula on enclosures. -/
theorem stirlingProd_width (hV : 64 ≤ V) {Y : Encl} {y lamY : ℝ} (hY : LEncl Y y lamY)
    (hlamY : 0 ≤ lamY) (hy1 : 1 ≤ y) {B : ℝ} (hB : y + 2 ≤ B) (hBlam : B * lamY ≤ 1 / 8)
    (hBu : B ^ 2 * (1 / 2 : ℝ) ^ V ≤ 1 / 16) (hεln : lnW B V + 5 * lamY ≤ 1) :
    AEncl0 (Encl.mul V (Encl.subNonneg V Y (Encl.div V (Encl.exact one) (Encl.nat 2)))
        (clampNonneg (lnOfEncl Y V).1, (lnOfEncl Y V).2))
      ((y - 1 / 2) * Real.log y)
      (2 * B ^ 2 * lamY + B * (lnW B V + 5 * lamY) + 10 * B ^ 2 * (1 / 2 : ℝ) ^ V) := by
  have : NeZero V := ⟨by omega⟩
  have hu : (1 / 2 : ℝ) ^ V ≤ 1 / 8 := by
    calc (1 / 2 : ℝ) ^ V ≤ (1 / 2 : ℝ) ^ 3 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 8 := by norm_num
  set u := (1 / 2 : ℝ) ^ V with hudef
  have hu0 : 0 < u := by positivity
  have hB3 : 3 ≤ B := by linarith
  have hB0 : 0 < B := by linarith
  have hlam24 : lamY ≤ 1 / 24 := by nlinarith
  have hylam : y * lamY ≤ 1 / 8 := (mul_le_mul_of_nonneg_right (by linarith) hlamY).trans hBlam
  have hBB : B ≤ B ^ 2 := by nlinarith
  have hBu' : B * u ≤ 1 / 16 := (mul_le_mul_of_nonneg_right hBB hu0.le).trans hBu
  have hu16 : u ≤ 1 / 144 := by nlinarith
  have hlogy0 : 0 ≤ Real.log y := Real.log_nonneg hy1
  have hlogy : Real.log y ≤ y - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hG : |Real.log y| ≤ B := by rw [abs_of_nonneg hlogy0]; linarith
  have hlnY := (hY.lnOfEncl hlamY (by linarith) hG hV).clamp0 hlogy0
  have hεln0 : 0 ≤ lnW B V + 5 * lamY := by
    have := lnW_nonneg hB0.le V
    linarith
  have hYA := (hY.toA hlamY (by linarith)).toA
  have hhalf : AEncl (Encl.div V (Encl.exact one) (Encl.nat 2)) (1 / 2 : ℝ) (6 * u) := by
    have h := ((LEncl.exact toVal_one' one_pos).div hu (LEncl.nat (n := 2) (by norm_num))).mono
      (le_of_eq (by ring : (0 : ℝ) + 0 + 6 * u = 6 * u))
    rw [Nat.cast_ofNat] at h
    exact (h.toA (by positivity) (by linarith)).toA.mono (le_of_eq (by ring))
  have hsub : AEncl0 (Encl.subNonneg V Y (Encl.div V (Encl.exact one) (Encl.nat 2)))
      (y - 1 / 2) (2 * y * lamY + 6 * u + 4 * B * u) :=
    hYA.subNonneg (w := V) hhalf (by linarith) (B := B) (by
      rw [abs_of_nonneg (by linarith)]
      linarith)
  have hεs : 2 * y * lamY + 6 * u + 4 * B * u ≤ 1 := by linarith
  have hA := hsub.mul (w := V) hlnY (B₁ := B) (B₂ := B) (by linarith) (by linarith)
  refine hA.mono ?_
  have e1 : 2 * y * lamY * B ≤ 2 * B ^ 2 * lamY := by
    have : y * lamY ≤ B * lamY := mul_le_mul_of_nonneg_right (by linarith) hlamY
    nlinarith
  have e3 : 6 * u * B ≤ 2 * B ^ 2 * u := by
    have := mul_le_mul_of_nonneg_right hB3 (mul_nonneg hB0.le hu0.le)
    nlinarith
  have e4 : (lnW B V + 5 * lamY) * B = B * (lnW B V + 5 * lamY) := by ring
  have e5 : (2 * y * lamY + 6 * u + 4 * B * u) * B
      = 2 * y * lamY * B + 6 * u * B + 4 * B ^ 2 * u := by ring
  have e6 : 4 * B * B * u = 4 * B ^ 2 * u := by ring
  rw [e5, e4, e6]
  linarith

/-- **The width of Stirling's formula on enclosures.**  `B ≥ y + 2` bounds the magnitudes; the
enclosure of `μ(y)` has width `εμ ≤ 1`. -/
theorem lnGammaStirlingEncl_width (hV : 64 ≤ V) {M : ℕ} {Y : Encl} {y lamY : ℝ}
    (hY : LEncl Y y lamY) (hlamY : 0 ≤ lamY) (hy1 : 1 ≤ y) {tol : AzFloat} {εμ B : ℝ}
    (hμ : AEncl (stirlingMuEncl V M Y tol) (DLMF.stirlingMu y) εμ) (hεμ : εμ ≤ 1)
    (hμ1 : |DLMF.stirlingMu y| ≤ 1) (hB : y + 2 ≤ B) (hBlam : B * lamY ≤ 1 / 8)
    (hBu : B ^ 2 * (1 / 2 : ℝ) ^ V ≤ 1 / 16) (hεln : lnW B V + 5 * lamY ≤ 1) :
    AEncl (lnGammaStirlingEncl V M Y tol)
      (Real.log (Real.Gamma y) - 1 / 2 * Real.log (2 * Real.pi))
      (3 * B ^ 2 * lamY + B * (lnW B V + 5 * lamY) + εμ + 42 * B ^ 2 * (1 / 2 : ℝ) ^ V) := by
  have : NeZero V := ⟨by omega⟩
  have hA := stirlingProd_width hV hY hlamY hy1 hB hBlam hBu hεln
  set u := (1 / 2 : ℝ) ^ V with hudef
  have hu0 : 0 < u := by positivity
  have hB3 : 3 ≤ B := by linarith
  have hB0 : 0 < B := by linarith
  have hB2 : 9 ≤ B ^ 2 := by nlinarith
  have hlam24 : lamY ≤ 1 / 24 := by nlinarith
  have hεμ0 : 0 ≤ εμ := by
    obtain ⟨l, h, -, -, h1, h2, h3⟩ := hμ
    linarith
  have hlnW0 := lnW_nonneg hB0.le V
  set εA := 2 * B ^ 2 * lamY + B * (lnW B V + 5 * lamY) + 10 * B ^ 2 * u with hεAdef
  have hεA0 : 0 ≤ εA := by rw [hεAdef]; positivity
  have hεA : εA ≤ 2 * B := by
    rw [hεAdef]
    have t1 : 2 * B ^ 2 * lamY ≤ B / 4 := by nlinarith
    have t2 : B * (lnW B V + 5 * lamY) ≤ B := by nlinarith
    linarith
  have hlogy0 : 0 ≤ Real.log y := Real.log_nonneg hy1
  have hlogy : Real.log y ≤ y - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hYA := (hY.toA hlamY (by linarith)).toA
  have hylam : 2 * y * lamY ≤ 1 / 4 := by
    have : y * lamY ≤ B * lamY := mul_le_mul_of_nonneg_right (by linarith) hlamY
    linarith
  have hval : |(y - 1 / 2) * Real.log y - y| ≤ B ^ 2 := by
    rw [abs_le]
    constructor
    · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ y - 1 / 2) hlogy0]
    · nlinarith [mul_le_mul_of_nonneg_left hlogy (by linarith : (0 : ℝ) ≤ y - 1 / 2)]
  have hS := hA.toA.sub (w := V) hYA (B := 4 * B ^ 2) (by nlinarith)
  have hμabs := abs_le.mp hμ1
  have hvalabs := abs_le.mp hval
  have h4u : 4 * (4 * B ^ 2) * u ≤ 1 := by linarith
  have hfin := hS.add (w := V) hμ (B := 4 * B ^ 2) (by
    have habs : |(y - 1 / 2) * Real.log y - y + DLMF.stirlingMu y| ≤ B ^ 2 + 1 := by
      rw [abs_le]
      constructor <;> linarith
    nlinarith)
  unfold lnGammaStirlingEncl
  have hvaleq : (y - 1 / 2) * Real.log y - y + DLMF.stirlingMu y
      = Real.log (Real.Gamma y) - 1 / 2 * Real.log (2 * Real.pi) := by
    rw [DLMF.stirlingMu]
    ring
  rw [← hvaleq]
  refine hfin.mono ?_
  have e2 : 2 * y * lamY ≤ B ^ 2 * lamY := by
    have h1 : y * lamY ≤ B * lamY := mul_le_mul_of_nonneg_right (by linarith) hlamY
    have h2 := mul_le_mul_of_nonneg_right hB3 (mul_nonneg hB0.le hlamY)
    nlinarith
  linarith

/-! ### The bracket of `ln Γ` -/

theorem toVal_lnGammaTol (w : ℕ) :
    (powerOf2 (-(AzNat.ofNat (w + 16)).toAzInt)).toVal
      = some (((1 / 2 : ℝ) ^ (w + 16) : ℝ) : EReal) := by
  rw [toVal_powerOf2, AzInt.toInt_neg, AzNat.toInt_toAzInt, AzNat.toNat_ofNat, zpow_neg,
    zpow_natCast, one_div_pow, one_div]

theorem abs_stirlingMu_le {y : ℝ} (hy : 0 < y) : |DLMF.stirlingMu y| ≤ stirlingCoeffT 1 / y := by
  obtain ⟨r, hμ, -, habs⟩ := stirlingMu_eq_sum_add (n := 1) le_rfl hy
  simp only [Nat.sub_self, range_zero, sum_empty, zero_add, mul_one] at hμ habs
  rw [show 2 - 1 = 1 by norm_num, pow_one] at habs
  rw [hμ]
  exact habs

/-- Stirling's formula on enclosures, with the terms bounded by `stirlingTerm_le`
(`M ≤ 2.7 y`). -/
theorem lnGammaStirlingEncl_width' (hV : 64 ≤ V) {M : ℕ} (hM : 1 ≤ M) {Y : Encl} {y lamY : ℝ}
    (hY : LEncl Y y lamY) (hlamY : 0 ≤ lamY) (hy1 : 1 ≤ y) (hky : (M : ℝ) ≤ 27 / 10 * y)
    {tol : AzFloat} {tolv : ℝ} (htol : tol.toVal = some (tolv : EReal)) {B : ℝ}
    (hB : y + 2 ≤ B) (hBM : 3 * (M : ℝ) + 3 ≤ B) (hBlam : B * lamY ≤ 1 / 8)
    (hBu : B ^ 2 * (1 / 2 : ℝ) ^ V ≤ 1 / 16)
    (hLam : 2 * M * (lamY + 12 * (1 / 2 : ℝ) ^ V) ≤ 1 / 2)
    (hεln : lnW B V + 5 * lamY ≤ 1)
    (hεμ : M * (2 * (2 * M * (lamY + 12 * (1 / 2 : ℝ) ^ V)) + 4 * B * (1 / 2 : ℝ) ^ V)
      + max tolv (2 * (9 / 10 : ℝ) ^ (2 * M - 1)) + 2 * B * (1 / 2 : ℝ) ^ V ≤ 1) :
    AEncl (lnGammaStirlingEncl V M Y tol)
      (Real.log (Real.Gamma y) - 1 / 2 * Real.log (2 * Real.pi))
      (3 * B ^ 2 * lamY + B * (lnW B V + 5 * lamY)
        + (M * (2 * (2 * M * (lamY + 12 * (1 / 2 : ℝ) ^ V)) + 4 * B * (1 / 2 : ℝ) ^ V)
          + max tolv (2 * (9 / 10 : ℝ) ^ (2 * M - 1)) + 2 * B * (1 / 2 : ℝ) ^ V)
        + 42 * B ^ 2 * (1 / 2 : ℝ) ^ V) := by
  have : NeZero V := ⟨by omega⟩
  have hu : (1 / 2 : ℝ) ^ V ≤ 1 / 8 := by
    calc (1 / 2 : ℝ) ^ V ≤ (1 / 2 : ℝ) ^ 3 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 8 := by norm_num
  have hu0 : (0 : ℝ) < (1 / 2 : ℝ) ^ V := by positivity
  have hy : 0 < y := by linarith
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hterm9 : ∀ k, 1 ≤ k → k ≤ M → stirlingCoeffT k / y ^ (2 * k - 1)
      ≤ (9 / 10 : ℝ) ^ (2 * k - 1) := fun k hk hkM =>
    stirlingTerm_le hk hy (le_trans (by exact_mod_cast hkM) hky)
  have hterm : ∀ k, 1 ≤ k → k ≤ M → stirlingCoeffT k / y ^ (2 * k - 1) ≤ 1 := fun k hk hkM =>
    (hterm9 k hk hkM).trans (pow_le_one₀ (by norm_num) (by norm_num))
  have hB3 : 3 ≤ B := by linarith
  have hLam0 : 0 ≤ 2 * M * (lamY + 12 * (1 / 2 : ℝ) ^ V) := by positivity
  have h4Bu : 4 * B * (1 / 2 : ℝ) ^ V ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hB3 (mul_nonneg (by linarith : (0 : ℝ) ≤ B) hu0.le)
    nlinarith
  have hμ := stirlingMuEncl_width hu hM hY hlamY htol (T := 1) (B := B) zero_le_one hterm
    hLam h4Bu (by nlinarith)
  have hμ' : AEncl (stirlingMuEncl V M Y tol) (DLMF.stirlingMu y)
      (M * (2 * (2 * M * (lamY + 12 * (1 / 2 : ℝ) ^ V)) + 4 * B * (1 / 2 : ℝ) ^ V)
        + max tolv (2 * (9 / 10 : ℝ) ^ (2 * M - 1)) + 2 * B * (1 / 2 : ℝ) ^ V) := by
    refine hμ.mono ?_
    have := hterm9 M hM le_rfl
    have hmax : max tolv (2 * (stirlingCoeffT M / y ^ (2 * M - 1)))
        ≤ max tolv (2 * (9 / 10 : ℝ) ^ (2 * M - 1)) := max_le_max le_rfl (by linarith)
    linarith
  have hμ1 : |DLMF.stirlingMu y| ≤ 1 := by
    have h1 := hterm 1 le_rfl hM
    simp only [mul_one, Nat.add_one_sub_one, pow_one] at h1
    exact (abs_stirlingMu_le hy).trans h1
  exact lnGammaStirlingEncl_width hV hY hlamY hy1 hμ' hεμ hμ1 hB hBlam hBu hεln

theorem abs_log_add_nat_le {xv : ℝ} (hxv : 0 < xv) {j δ : ℕ} (hj : j < δ) :
    |Real.log (xv + j)| ≤ |Real.log xv| + (xv + δ) := by
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hjδ : (j : ℝ) ≤ δ := by exact_mod_cast hj.le
  rcases le_or_gt 1 (xv + j) with h | h
  · rw [abs_of_nonneg (Real.log_nonneg h)]
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < xv + j)
    linarith [abs_nonneg (Real.log xv)]
  · have h1 : Real.log (xv + j) ≤ 0 := Real.log_nonpos (by linarith) h.le
    have h2 : Real.log xv ≤ Real.log (xv + j) := Real.log_le_log hxv (by linarith)
    rw [abs_of_nonpos h1]
    have := neg_abs_le (Real.log xv)
    linarith

theorem abs_log_two_pi_le : |Real.log (2 * Real.pi)| ≤ 3 := by
  have hπ := Real.pi_gt_three
  have h1 : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith)
  have h2 : Real.log (2 * Real.pi) ≤ Real.log 8 :=
    Real.log_le_log (by positivity) (by linarith [Real.pi_lt_d2])
  have h3 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  rw [abs_of_nonneg h1]
  linarith [Real.log_two_lt_d9]

/-- The constant `½ ln (2π)` on enclosures. -/
theorem lnGammaConst_width (hV : 64 ≤ V) :
    AEncl (Encl.half (lnOfEncl (Encl.mul V (Encl.nat 2) (Encl.pi V)) V))
      (Real.log (2 * Real.pi) / 2) ((lnW 3 V + 5 * (9 * (1 / 2 : ℝ) ^ V)) / 2) := by
  have : NeZero V := ⟨by omega⟩
  have hu : (1 / 2 : ℝ) ^ V ≤ 1 / 64 := by
    calc (1 / 2 : ℝ) ^ V ≤ (1 / 2 : ℝ) ^ 6 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 64 := by norm_num
  have hu0 : (0 : ℝ) < (1 / 2 : ℝ) ^ V := by positivity
  have h2π : LEncl (Encl.mul V (Encl.nat 2) (Encl.pi V)) (2 * Real.pi)
      (9 * (1 / 2 : ℝ) ^ V) := by
    have := ((LEncl.nat (n := 2) (by norm_num)).mul (w := V) (by linarith) (LEncl.pi hV)).mono
      (le_of_eq (by ring : (0 : ℝ) + 3 * (1 / 2 : ℝ) ^ V + 6 * (1 / 2 : ℝ) ^ V
        = 9 * (1 / 2 : ℝ) ^ V))
    simpa using this
  exact (h2π.lnOfEncl (by positivity) (by linarith) abs_log_two_pi_le hV).half

/-- The constant and the rising product together: `½ ln (2π / P²)`. -/
theorem lnGammaConstRising_width (hV : 64 ≤ V) {X : Encl} {xv lam₀ : ℝ} (hX : LEncl X xv lam₀)
    (h0 : 0 ≤ lam₀) (δ : ℕ) {GQ : ℝ}
    (hlamQ : 2 * δ * (lam₀ + 12 * (1 / 2 : ℝ) ^ V) + 21 * (1 / 2 : ℝ) ^ V ≤ 1 / 2)
    (hGQ : 3 + 2 * δ * (|Real.log xv| + (xv + δ)) ≤ GQ) :
    AEncl (Encl.half (lnOfEncl (Encl.div V (Encl.mul V (Encl.nat 2) (Encl.pi V))
        (Encl.mul V (risingEncl V X δ) (risingEncl V X δ))) V))
      (Real.log (2 * Real.pi / ((∏ j ∈ range δ, (xv + j)) * (∏ j ∈ range δ, (xv + j)))) / 2)
      ((lnW GQ V + 5 * (2 * δ * (lam₀ + 12 * (1 / 2 : ℝ) ^ V) + 21 * (1 / 2 : ℝ) ^ V)) / 2) := by
  have : NeZero V := ⟨by omega⟩
  have hu : (1 / 2 : ℝ) ^ V ≤ 1 / 64 := by
    calc (1 / 2 : ℝ) ^ V ≤ (1 / 2 : ℝ) ^ 6 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 64 := by norm_num
  have hu0 : (0 : ℝ) < (1 / 2 : ℝ) ^ V := by positivity
  have hxv : 0 < xv := hX.pos
  have h2π : LEncl (Encl.mul V (Encl.nat 2) (Encl.pi V)) (2 * Real.pi)
      (9 * (1 / 2 : ℝ) ^ V) := by
    have := ((LEncl.nat (n := 2) (by norm_num)).mul (w := V) (by linarith) (LEncl.pi hV)).mono
      (le_of_eq (by ring : (0 : ℝ) + 3 * (1 / 2 : ℝ) ^ V + 6 * (1 / 2 : ℝ) ^ V
        = 9 * (1 / 2 : ℝ) ^ V))
    simpa using this
  have hP := risingEncl_width (V := V) (by linarith) hX h0 δ
  have hQ := (h2π.div (w := V) (by linarith) (hP.mul (by linarith) hP)).mono (le_of_eq (by ring :
    9 * (1 / 2 : ℝ) ^ V + (δ * (lam₀ + 12 * (1 / 2 : ℝ) ^ V) + δ * (lam₀ + 12 * (1 / 2 : ℝ) ^ V)
      + 6 * (1 / 2 : ℝ) ^ V) + 6 * (1 / 2 : ℝ) ^ V
      = 2 * δ * (lam₀ + 12 * (1 / 2 : ℝ) ^ V) + 21 * (1 / 2 : ℝ) ^ V))
  have hPpos : 0 < ∏ j ∈ range δ, (xv + j) :=
    prod_pos fun i _ => by
      have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      linarith
  have hlogP : |Real.log (∏ j ∈ range δ, (xv + j))| ≤ δ * (|Real.log xv| + (xv + δ)) := by
    rw [Real.log_prod (fun i _ => by
      have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      exact (by linarith : (0 : ℝ) < xv + i).ne')]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i ∈ range δ, |Real.log (xv + i)| ≤ ∑ _i ∈ range δ, (|Real.log xv| + (xv + δ)) :=
          sum_le_sum fun i hi => abs_log_add_nat_le hxv (mem_range.mp hi)
      _ = δ * (|Real.log xv| + (xv + δ)) := by rw [sum_const, card_range, nsmul_eq_mul]
  have hG : |Real.log (2 * Real.pi / ((∏ j ∈ range δ, (xv + j)) * (∏ j ∈ range δ, (xv + j))))|
      ≤ GQ := by
    rw [Real.log_div (by positivity) (mul_pos hPpos hPpos).ne', Real.log_mul hPpos.ne' hPpos.ne']
    have h1 := abs_log_two_pi_le
    have h2 := abs_le.mp hlogP
    have h3 := abs_le.mp h1
    rw [abs_le]
    constructor <;> linarith
  have hlamQ0 : 0 ≤ 2 * δ * (lam₀ + 12 * (1 / 2 : ℝ) ^ V) + 21 * (1 / 2 : ℝ) ^ V := by positivity
  exact (hQ.lnOfEncl hlamQ0 hlamQ hG hV).half

theorem lnW_mono {G G' : ℝ} (hG : 0 ≤ G) (h : G ≤ G') (w : ℕ) : lnW G w ≤ lnW G' w := by
  unfold lnW
  have hw : (0 : ℝ) ≤ w := Nat.cast_nonneg w
  have hle : (w : ℝ) + 2 * G + 10 ≤ (w : ℝ) + 2 * G' + 10 := by linarith
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) hle 5) (by norm_num)) (by positivity)

/-- The bound for the width of `lnGammaBracketEncl`: Stirling's formula, the constant with the
rising product, and the last addition. -/
noncomputable def lnGammaWidthBound (lam₀ : ℝ) (w V δ M : ℕ) (B GQ Bf : ℝ) : ℝ :=
  (3 * B ^ 2 * (lam₀ + 6 * (1 / 2 : ℝ) ^ V)
      + B * (lnW B V + 5 * (lam₀ + 6 * (1 / 2 : ℝ) ^ V))
      + (M * (2 * (2 * M * (lam₀ + 6 * (1 / 2 : ℝ) ^ V + 12 * (1 / 2 : ℝ) ^ V))
          + 4 * B * (1 / 2 : ℝ) ^ V)
        + max ((1 / 2 : ℝ) ^ (w + 16)) (2 * (9 / 10 : ℝ) ^ (2 * M - 1))
        + 2 * B * (1 / 2 : ℝ) ^ V)
      + 42 * B ^ 2 * (1 / 2 : ℝ) ^ V)
    + (lnW GQ V + 5 * (2 * δ * (lam₀ + 12 * (1 / 2 : ℝ) ^ V) + 21 * (1 / 2 : ℝ) ^ V)) / 2
    + 4 * Bf * (1 / 2 : ℝ) ^ V

/-- **The width of the bracket of `ln Γ`**, under explicit smallness and magnitude
conditions. -/
theorem lnGammaBracketEncl_width {X : Encl} {xv lam₀ : ℝ} (hX : LEncl X xv lam₀)
    (h0 : 0 ≤ lam₀) (e : AzInt) {w : ℕ} (hw : 64 ≤ w) {L V δ M : ℕ}
    (hL : L = lnGammaShiftExp w) (hVd : V = w + 2 * L + 8 + 2 * w.log2)
    (hδ : δ = lnGammaShift X.1 e L)
    (hMd : M = lnGammaTerms w (max (L + 1) (if e.sign then e.abs.toNat else 0)))
    {B GQ Bf : ℝ} (hky : (M : ℝ) ≤ 27 / 10 * (xv + δ)) (hB : xv + δ + 2 ≤ B)
    (hBM : 3 * (M : ℝ) + 3 ≤ B) (hBlam : B * (lam₀ + 6 * (1 / 2 : ℝ) ^ V) ≤ 1 / 8)
    (hBu : B ^ 2 * (1 / 2 : ℝ) ^ V ≤ 1 / 16)
    (hLam : 2 * M * (lam₀ + 6 * (1 / 2 : ℝ) ^ V + 12 * (1 / 2 : ℝ) ^ V) ≤ 1 / 2)
    (hεln : lnW B V + 5 * (lam₀ + 6 * (1 / 2 : ℝ) ^ V) ≤ 1)
    (hεμ : M * (2 * (2 * M * (lam₀ + 6 * (1 / 2 : ℝ) ^ V + 12 * (1 / 2 : ℝ) ^ V))
        + 4 * B * (1 / 2 : ℝ) ^ V)
      + max ((1 / 2 : ℝ) ^ (w + 16)) (2 * (9 / 10 : ℝ) ^ (2 * M - 1))
      + 2 * B * (1 / 2 : ℝ) ^ V ≤ 1)
    (hlamQ : 2 * δ * (lam₀ + 12 * (1 / 2 : ℝ) ^ V) + 21 * (1 / 2 : ℝ) ^ V ≤ 1 / 2)
    (hGQ : 3 + 2 * δ * (|Real.log xv| + (xv + δ)) ≤ GQ)
    (hBf : |Real.log (Real.Gamma xv)| + lnGammaWidthBound lam₀ w V δ M B GQ Bf ≤ Bf) :
    AEncl (lnGammaBracketEncl X e w) (Real.log (Real.Gamma xv))
      (lnGammaWidthBound lam₀ w V δ M B GQ Bf) := by
  have hV : 64 ≤ V := by omega
  have : NeZero V := ⟨by omega⟩
  have hu : (1 / 2 : ℝ) ^ V ≤ 1 / 8 := by
    calc (1 / 2 : ℝ) ^ V ≤ (1 / 2 : ℝ) ^ 3 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 8 := by norm_num
  have hu0 : (0 : ℝ) < (1 / 2 : ℝ) ^ V := by positivity
  obtain ⟨xl, xh, hxl, -, hxl0, hxl1, -⟩ := id hX
  have hpos : 0 < xv := hX.pos
  have hM : 1 ≤ M := by
    rw [hMd]; unfold lnGammaTerms; exact le_trans (by norm_num) (Nat.le_add_left 3 _)
  have hδ0' : (0 : ℝ) ≤ δ := Nat.cast_nonneg δ
  have hGQ3 : 3 ≤ GQ := by
    have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hδ0')
      (by positivity : (0 : ℝ) ≤ |Real.log xv| + (xv + δ))
    linarith
  have hBf0 : 0 ≤ Bf := by
    have h1 := abs_nonneg (Real.log (Real.Gamma xv))
    have hB0 : 0 ≤ B := by linarith
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    have hlY : 0 ≤ lam₀ + 6 * (1 / 2 : ℝ) ^ V := by positivity
    have t1 : 0 ≤ 3 * B ^ 2 * (lam₀ + 6 * (1 / 2 : ℝ) ^ V) := by positivity
    have t2 : 0 ≤ B * (lnW B V + 5 * (lam₀ + 6 * (1 / 2 : ℝ) ^ V)) :=
      mul_nonneg hB0 (by linarith [lnW_nonneg hB0 V])
    have t3 : 0 ≤ M * (2 * (2 * M * (lam₀ + 6 * (1 / 2 : ℝ) ^ V + 12 * (1 / 2 : ℝ) ^ V))
        + 4 * B * (1 / 2 : ℝ) ^ V) := by
      have a1 : 0 ≤ 2 * (2 * M * (lam₀ + 6 * (1 / 2 : ℝ) ^ V + 12 * (1 / 2 : ℝ) ^ V)) := by
        positivity
      have a2 := mul_nonneg hB0 hu0.le
      exact mul_nonneg hM0 (by linarith)
    have t4 : (0 : ℝ) ≤ max ((1 / 2 : ℝ) ^ (w + 16)) (2 * (9 / 10 : ℝ) ^ (2 * M - 1)) :=
      le_trans (by positivity) (le_max_left _ _)
    have t5 := mul_nonneg hB0 hu0.le
    have t6 : 0 ≤ 42 * B ^ 2 * (1 / 2 : ℝ) ^ V := by positivity
    have t7 : 0 ≤ (lnW GQ V + 5 * (2 * δ * (lam₀ + 12 * (1 / 2 : ℝ) ^ V)
        + 21 * (1 / 2 : ℝ) ^ V)) / 2 := by
      have := lnW_nonneg (by linarith : (0 : ℝ) ≤ GQ) V
      have : 0 ≤ 5 * (2 * (δ : ℝ) * (lam₀ + 12 * (1 / 2 : ℝ) ^ V) + 21 * (1 / 2 : ℝ) ^ V) := by
        positivity
      linarith
    unfold lnGammaWidthBound at hBf
    by_contra hneg
    push Not at hneg
    have := mul_le_mul_of_nonpos_left hu hneg.le
    linarith
  have htol := toVal_lnGammaTol w
  unfold lnGammaBracketEncl
  simp only [← hL, ← hVd, ← hδ, ← hMd]
  rcases Nat.eq_zero_or_pos δ with hδ0 | hδpos
  · rw [ite_eq_left hδ0]
    have hy1 : 1 ≤ xv :=
      (one_le_of_lnGammaShift_eq_zero hxl (hδ.symm.trans hδ0)).trans hxl1
    rw [hδ0] at hky hB hlamQ hGQ hBf ⊢
    simp only [Nat.cast_zero, add_zero] at hky hB
    have hS := lnGammaStirlingEncl_width' hV hM (hX.mono (by linarith : lam₀ ≤ lam₀
      + 6 * (1 / 2 : ℝ) ^ V)) (by positivity) hy1 hky htol hB hBM hBlam hBu hLam hεln hεμ
    have hC := (lnGammaConst_width hV).mono (ε' := (lnW GQ V
        + 5 * (2 * ((0 : ℕ) : ℝ) * (lam₀ + 12 * (1 / 2 : ℝ) ^ V) + 21 * (1 / 2 : ℝ) ^ V)) / 2)
      (by
        have := lnW_mono (by norm_num) hGQ3 V
        simp only [Nat.cast_zero, mul_zero, zero_mul, zero_add]
        linarith)
    have hval : Real.log (Real.Gamma xv) - 1 / 2 * Real.log (2 * Real.pi)
        + Real.log (2 * Real.pi) / 2 = Real.log (Real.Gamma xv) := by ring
    have hfin := hS.add (w := V) hC (B := Bf) (by
      rw [hval]
      unfold lnGammaWidthBound at hBf
      have hC0 : 0 ≤ (lnW GQ V + 5 * (2 * ((0 : ℕ) : ℝ) * (lam₀ + 12 * (1 / 2 : ℝ) ^ V)
          + 21 * (1 / 2 : ℝ) ^ V)) / 2 := by
        have := lnW_nonneg (by linarith : (0 : ℝ) ≤ GQ) V
        positivity
      have : 0 ≤ 4 * Bf * (1 / 2 : ℝ) ^ V := by positivity
      linarith)
    rw [hval] at hfin
    exact hfin.mono (le_of_eq (by unfold lnGammaWidthBound; ring))
  · rw [ite_eq_right (by omega : δ ≠ 0)]
    have hδ1 : (1 : ℝ) ≤ δ := by exact_mod_cast hδpos
    have hY : LEncl (Encl.add V X (Encl.nat δ)) (xv + δ) (lam₀ + 6 * (1 / 2 : ℝ) ^ V) :=
      hX.add_exact (w := V) (b := Encl.nat δ) hu h0 (toVal_ofAzNat_ofNat δ)
        (toVal_ofAzNat_ofNat δ) hδ0'
    have hS := lnGammaStirlingEncl_width' hV hM hY (by positivity) (by linarith) hky htol hB
      hBM hBlam hBu hLam hεln hεμ
    have hC := lnGammaConstRising_width hV hX h0 δ hlamQ hGQ
    have hPpos : 0 < ∏ j ∈ range δ, (xv + j) :=
      prod_pos fun i _ => by
        have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
        linarith
    have hπ : 0 < 2 * Real.pi := by positivity
    have hval : Real.log (Real.Gamma (xv + δ)) - 1 / 2 * Real.log (2 * Real.pi)
        + Real.log (2 * Real.pi / ((∏ j ∈ range δ, (xv + j)) * (∏ j ∈ range δ, (xv + j)))) / 2
        = Real.log (Real.Gamma xv) := by
      rw [BZ.log_Gamma_eq_log_Gamma_add_sub hpos δ,
        Real.log_div hπ.ne' (mul_pos hPpos hPpos).ne', Real.log_mul hPpos.ne' hPpos.ne',
        Real.log_prod]
      · ring
      · intro i _
        have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
        exact (by linarith : (0 : ℝ) < xv + i).ne'
    have hfin := hS.add (w := V) hC (B := Bf) (by
      rw [hval]
      unfold lnGammaWidthBound at hBf
      have hC0 : 0 ≤ (lnW GQ V + 5 * (2 * (δ : ℝ) * (lam₀ + 12 * (1 / 2 : ℝ) ^ V)
          + 21 * (1 / 2 : ℝ) ^ V)) / 2 := by
        have := lnW_nonneg (by linarith : (0 : ℝ) ≤ GQ) V
        positivity
      have : 0 ≤ 4 * Bf * (1 / 2 : ℝ) ^ V := by positivity
      linarith)
    rw [hval] at hfin
    exact hfin.mono (le_of_eq (by unfold lnGammaWidthBound; ring))

end Azurite.AzFloat
