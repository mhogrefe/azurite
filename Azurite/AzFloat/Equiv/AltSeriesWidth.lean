/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.LnGammaWidth

/-!
# The width of an alternating asymptotic series summed on enclosures

The loops that sum the asymptotic series of `ln Γ`, `ψ` and `ψ⁽ⁿ⁾` on enclosures have one
shape: the term `k` is made from an enclosure `p` of a power of `1/y`, added to or subtracted
from the partial sum by the parity of `k`, the power is multiplied by an enclosure of `y⁻²`,
and the loop closes with a term below the tolerance, or the last one, as the bound of the
remainder.  `altSumLoop` is that loop with the term as a parameter, and `altSumLoop_width` is
the bound of its width: with `Λ ≤ 1/2` a bound of the relative widths of the terms, `T` of the
terms and `B` of the magnitudes, every term added costs `2TΛ + 4Bu`, and the closing term is
below `tol` or is the one of index `M`.
-/

namespace Azurite.AzFloat

open Finset

/-- The loop of an alternating series on enclosures, with the term as a parameter. -/
def altSumLoop (V : ℕ) (term : ℕ → Encl → Encl) (inv2 : Encl) (tol : AzFloat) :
    ℕ → ℕ → Encl → Encl → Encl
  | 0, k, p, acc =>
    if k % 2 = 1 then (acc.1, (addPrecRound acc.2 (term k p).2 V .Ceiling).1)
    else ((subPrecRound acc.1 (term k p).2 V .Floor).1, acc.2)
  | fuel + 1, k, p, acc =>
    if le (term k p).2 tol then
      if k % 2 = 1 then (acc.1, (addPrecRound acc.2 (term k p).2 V .Ceiling).1)
      else ((subPrecRound acc.1 (term k p).2 V .Floor).1, acc.2)
    else
      altSumLoop V term inv2 tol fuel (k + 1) (Encl.mul V p inv2)
        (if k % 2 = 1 then Encl.add V acc (term k p) else Encl.sub V acc (term k p))

/-- The partial sum of the signed terms before the index `k`. -/
noncomputable def altPartial (t : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ range (k - 1), (-1) ^ (i + 1 + 1) * t (i + 1)

variable {V : ℕ} {M : ℕ} {t q : ℕ → ℝ} {term : ℕ → Encl → Encl} {T B Lam c μ i2 : ℝ}

theorem altPartial_succ {k : ℕ} (hk : 1 ≤ k) :
    altPartial t (k + 1) = altPartial t k + (-1) ^ (k + 1) * t k := by
  unfold altPartial
  rw [show k + 1 - 1 = (k - 1) + 1 by omega, sum_range_succ, show k - 1 + 1 = k by omega]

theorem abs_altPartial_le (hpos : ∀ k, 1 ≤ k → k ≤ M → 0 < t k)
    (hterm : ∀ k, 1 ≤ k → k ≤ M → t k ≤ T) {k : ℕ} (hk : k - 1 ≤ M) :
    |altPartial t k| ≤ (k - 1 : ℕ) * T := by
  unfold altPartial
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i ∈ range (k - 1), |(-1 : ℝ) ^ (i + 1 + 1) * t (i + 1)|
      ≤ ∑ _i ∈ range (k - 1), T :=
        sum_le_sum fun i hi => by
          have hi' := mem_range.mp hi
          rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
            abs_of_pos (hpos (i + 1) (by omega) (by omega))]
          exact hterm (i + 1) (by omega) (by omega)
    _ = (k - 1 : ℕ) * T := by rw [sum_const, card_range, nsmul_eq_mul]

/-- The facts at one step of the loop: the term, its upper end, and the magnitudes. -/
theorem altStep_facts [NeZero V] (hLam : Lam ≤ 1 / 2) (hT0 : 0 ≤ T)
    (hpos : ∀ k, 1 ≤ k → k ≤ M → 0 < t k) (hterm : ∀ k, 1 ≤ k → k ≤ M → t k ≤ T)
    (hτ : ∀ k p lam, 1 ≤ k → k ≤ M → LEncl p (q k) lam →
      LEncl (term k p) (t k) (lam + c * (1 / 2 : ℝ) ^ V))
    (hBu : 4 * B * (1 / 2 : ℝ) ^ V ≤ 1)
    (hB : M * (T + 2 * T * Lam + 1) + 2 * T + 1 ≤ B) {k : ℕ} {p : Encl} {lam ε : ℝ}
    (hk : 1 ≤ k) (hkM : k ≤ M) (hp : LEncl p (q k) lam)
    (hlam0 : 0 ≤ lam + c * (1 / 2 : ℝ) ^ V) (hlamL : lam + c * (1 / 2 : ℝ) ^ V ≤ Lam)
    (hε : ε ≤ (k - 1 : ℕ) * (2 * T * Lam + 4 * B * (1 / 2 : ℝ) ^ V)) :
    0 ≤ Lam ∧ 0 ≤ B ∧ 2 * T * Lam ≤ T ∧ 0 ≤ 2 * T * Lam + 4 * B * (1 / 2 : ℝ) ^ V ∧
      (∃ th : ℝ, (term k p).2.toVal = some (th : EReal) ∧ t k ≤ th ∧ th ≤ 2 * t k) ∧
      AEncl (term k p) (t k) (2 * T * Lam) ∧ |altPartial t k| + ε + 2 * T ≤ B := by
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
  have hτ' := (hτ k p lam hk hkM hp).mono hlamL
  have htk := hterm k hk hkM
  have htk0 := hpos k hk hkM
  have hτA := (hτ'.toA hLam0 hLam).toA
  obtain ⟨tl, th, htl, hth, p0, a1, b1, c1⟩ := hτ'
  have hexp2 : Real.exp Lam ≤ 2 := by
    have := Real.exp_le_exp.mpr hLam
    have h2 : Real.exp (1 / 2) ≤ 2 := by
      have := Real.exp_one_lt_d9
      have hsq : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_pos (1 / 2 : ℝ)]
    linarith
  have hth2 : th ≤ 2 * t k := by
    calc th ≤ tl * Real.exp Lam := c1
      _ ≤ t k * 2 := mul_le_mul a1 hexp2 (Real.exp_pos _).le htk0.le
      _ = _ := by ring
  have hsum := abs_altPartial_le hpos hterm (k := k) (by omega)
  have hk1 : ((k - 1 : ℕ) : ℝ) ≤ M := by exact_mod_cast (by omega : k - 1 ≤ M)
  refine ⟨hLam0, hB0, hTL, hD0, ⟨th, hth, b1, hth2⟩, hτA.mono ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_right htk hLam0
    linarith
  · have e1 : ((k - 1 : ℕ) : ℝ) * T ≤ M * T := mul_le_mul_of_nonneg_right hk1 hT0
    have e2 : ((k - 1 : ℕ) : ℝ) * (2 * T * Lam + 4 * B * (1 / 2 : ℝ) ^ V)
        ≤ M * (2 * T * Lam + 1) := mul_le_mul hk1 (by linarith) hD0 hM0
    linarith

/-- Adding a term to the partial sum. -/
theorem altAcc_width [NeZero V] {k : ℕ} (hk : 1 ≤ k) {acc τ : Encl} {ε εt : ℝ}
    (htk0 : 0 < t k) (hacc : AEncl acc (altPartial t k) ε) (hτ : AEncl τ (t k) εt)
    (htk : t k ≤ T) (hεt : εt ≤ T) (hmag : |altPartial t k| + ε + 2 * T ≤ B) :
    AEncl (if k % 2 = 1 then Encl.add V acc τ else Encl.sub V acc τ) (altPartial t (k + 1))
      (ε + εt + 4 * B * (1 / 2 : ℝ) ^ V) := by
  rw [altPartial_succ hk]
  split_ifs with hodd
  · rw [(Nat.even_iff.mpr (by omega : (k + 1) % 2 = 0)).neg_one_pow, one_mul]
    refine hacc.add (w := V) hτ (B := B) ?_
    have h1 := abs_add_le (altPartial t k) (t k)
    rw [abs_of_pos htk0] at h1
    linarith
  · have e : altPartial t k + (-1) ^ (k + 1) * t k = altPartial t k - t k := by
      rw [(Nat.odd_iff.mpr (by omega : (k + 1) % 2 = 1)).neg_one_pow]
      ring
    rw [e]
    refine hacc.sub (w := V) hτ (B := B) ?_
    have h1 := abs_sub (altPartial t k) (t k)
    rw [abs_of_pos htk0] at h1
    linarith

/-- **The width of an alternating series summed on enclosures.** -/
theorem altSumLoop_width [NeZero V] (hu : (1 / 2 : ℝ) ^ V ≤ 1 / 8) {inv2 : Encl} {lam₂ : ℝ}
    (hinv2 : LEncl inv2 i2 lam₂) (hq : ∀ k, q (k + 1) = q k * i2) {tol : AzFloat} {tolv : ℝ}
    (htol : tol.toVal = some (tolv : EReal)) (hLam : Lam ≤ 1 / 2) (hT0 : 0 ≤ T) (hc : 0 ≤ c)
    (hpos : ∀ k, 1 ≤ k → k ≤ M → 0 < t k) (hterm : ∀ k, 1 ≤ k → k ≤ M → t k ≤ T)
    (hτ : ∀ k p lam, 1 ≤ k → k ≤ M → LEncl p (q k) lam →
      LEncl (term k p) (t k) (lam + c * (1 / 2 : ℝ) ^ V))
    (hμ : ∀ k, 1 ≤ k → k ≤ M → ∃ r : ℝ, μ = altPartial t k + r ∧ 0 ≤ (-1) ^ (k + 1) * r ∧
      |r| ≤ t k)
    (hBu : 4 * B * (1 / 2 : ℝ) ^ V ≤ 1)
    (hB : M * (T + 2 * T * Lam + 1) + 2 * T + 1 ≤ B) :
    ∀ (fuel k : ℕ) (p acc : Encl) (lam ε : ℝ), 1 ≤ k → k + fuel = M →
      LEncl p (q k) lam → 0 ≤ lam →
      lam + fuel * (lam₂ + 6 * (1 / 2 : ℝ) ^ V) + c * (1 / 2 : ℝ) ^ V ≤ Lam →
      AEncl acc (altPartial t k) ε →
      ε ≤ (k - 1 : ℕ) * (2 * T * Lam + 4 * B * (1 / 2 : ℝ) ^ V) →
      AEncl (altSumLoop V term inv2 tol fuel k p acc) μ
        (ε + fuel * (2 * T * Lam + 4 * B * (1 / 2 : ℝ) ^ V)
          + max tolv (2 * t M) + 2 * B * (1 / 2 : ℝ) ^ V) := by
  have hu0 : (0 : ℝ) < (1 / 2 : ℝ) ^ V := by positivity
  have hcu : 0 ≤ c * (1 / 2 : ℝ) ^ V := mul_nonneg hc hu0.le
  intro fuel
  induction fuel with
  | zero =>
    intro k p acc lam ε hk hkM hp hlam hlamL hacc hε
    have hkM' : k = M := by omega
    obtain ⟨hLam0, hB0, hTL, hD0, ⟨th, hth, hth1, hth2⟩, hτA, hmag⟩ :=
      altStep_facts hLam hT0 hpos hterm hτ hBu hB hk (by omega) hp (by linarith)
        (by simpa using hlamL) hε
    obtain ⟨r, hμr, hsign, habs⟩ := hμ k hk (by omega)
    rw [altSumLoop]
    have htkT := hterm k hk (by omega)
    have := stirlingClose_width (V := V) hacc hth hμr hsign (habs.trans hth1)
      (B := B) (by linarith)
    refine this.mono ?_
    have : th ≤ max tolv (2 * t M) := by
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
    have hlamL' : lam + c * (1 / 2 : ℝ) ^ V ≤ Lam := by
      have := mul_nonneg hf0 hlam₂
      linarith
    obtain ⟨hLam0, hB0, hTL, hD0, ⟨th, hth, hth1, hth2⟩, hτA, hmag⟩ :=
      altStep_facts hLam hT0 hpos hterm hτ hBu hB hk (by omega) hp (by linarith) hlamL' hε
    have htkT := hterm k hk (by omega)
    rw [altSumLoop]
    by_cases hstop : le (term k p).2 tol = true
    · simp only [hstop, ↓reduceIte]
      have hthtol : th ≤ tolv := (le_eq_true_iff hth htol).mp hstop
      obtain ⟨r, hμr, hsign, habs⟩ := hμ k hk (by omega)
      have := stirlingClose_width (V := V) hacc hth hμr hsign (habs.trans hth1)
        (B := B) (by linarith)
      refine this.mono ?_
      have h1 : th ≤ max tolv (2 * t M) := hthtol.trans (le_max_left _ _)
      have h2 : (0 : ℝ) ≤ ((fuel + 1 : ℕ) : ℝ) * (2 * T * Lam + 4 * B * (1 / 2 : ℝ) ^ V) :=
        mul_nonneg (Nat.cast_nonneg _) hD0
      linarith
    · simp only [hstop, Bool.false_eq_true, ↓reduceIte]
      have hp' : LEncl (Encl.mul V p inv2) (q (k + 1)) (lam + lam₂ + 6 * (1 / 2 : ℝ) ^ V) := by
        rw [hq]
        exact hp.mul hu hinv2
      have hlam' : 0 ≤ lam + lam₂ + 6 * (1 / 2 : ℝ) ^ V := by linarith
      have hlamL'' : lam + lam₂ + 6 * (1 / 2 : ℝ) ^ V
          + (fuel : ℝ) * (lam₂ + 6 * (1 / 2 : ℝ) ^ V) + c * (1 / 2 : ℝ) ^ V ≤ Lam := by
        linarith
      have hε' : ε + 2 * T * Lam + 4 * B * (1 / 2 : ℝ) ^ V
          ≤ ((k + 1 - 1 : ℕ) : ℝ) * (2 * T * Lam + 4 * B * (1 / 2 : ℝ) ^ V) := by
        have e : ((k + 1 - 1 : ℕ) : ℝ) = ((k - 1 : ℕ) : ℝ) + 1 := by
          rw [show k + 1 - 1 = (k - 1) + 1 by omega]
          push_cast
          ring
        rw [e]
        linarith
      have hacc' := altAcc_width (V := V) hk (hpos k hk (by omega)) hacc hτA htkT hTL hmag
      have := ih (k + 1) _ _ _ _ (by omega) (by omega) hp' hlam' hlamL'' hacc' hε'
      refine this.mono (le_of_eq ?_)
      push_cast
      ring

end Azurite.AzFloat
