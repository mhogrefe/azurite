/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.ExpBracket
import Azurite.AzFloat.Equiv.Ln2Bracket
import Azurite.AzFloat.Equiv.DirectedRounding
import Azurite.AzNat.Equiv.ExpSplit
import Azurite.AzNat.Equiv.ShiftRight
import Azurite.AzNat.Equiv.Sub

/-!
# Equivalence: brackets of `exp` at dyadic rationals

* `exp_tail_le`: the Taylor tail of `exp x` for `|x| ≤ 2^(−e)` with `expTermCount e w` terms is
  at most `2^(−w−1)`.
* `natQuotBracket_spec`: the float bracket of `n / d` has relative errors `6 · 2^(−k)` and
  `8 · 2^(−k)`.
* `expChunkBracket_spec`: `exp (p / 2^s)` is enclosed with width at most `2 · 2^(−w)`, lower end
  at least `1/2`.
* `expChunks_spec`: the chunks sum to `M / 2^(2^K)` and each is at most `2^(−e)`.
* `expDyadicBracket_spec`: `exp (M / 2^(2^K))` is enclosed with relative errors `(1 ± 8 · 2^(−w))`
  to the power `K + 1`; `pow_width_le` turns that into the width `24 (K + 1) · 2^(−w)`.
-/

namespace Azurite.AzFloat

open Finset

/-! ### The number of terms and the tail -/

theorem expTermCount_go_spec (e w : ℕ) (he : 1 ≤ e) :
    ∀ fuel n, 2 ≤ n → w + 2 ≤ (n + fuel) * e →
      2 ≤ expTermCount.go e w fuel n ∧
        w + 2 ≤ expTermCount.go e w fuel n * e
          + (expTermCount.go e w fuel n / 2) * Nat.log 2 (expTermCount.go e w fuel n / 2)
  | 0, n, hn, hfuel => by
    simp only [expTermCount.go]
    refine ⟨hn, ?_⟩
    simp only [add_zero] at hfuel
    omega
  | fuel + 1, n, hn, hfuel => by
    simp only [expTermCount.go]
    split_ifs with h
    · exact ⟨hn, h⟩
    · exact expTermCount_go_spec e w he fuel (n + 1) (by omega)
        (by rw [show n + 1 + fuel = n + (fuel + 1) by ring]; exact hfuel)

theorem expTermCount_spec (e w : ℕ) (he : 1 ≤ e) :
    2 ≤ expTermCount e w ∧
      w + 2 ≤ expTermCount e w * e + (expTermCount e w / 2) * Nat.log 2 (expTermCount e w / 2) :=
  expTermCount_go_spec e w he (w + 3) 2 le_rfl (by nlinarith)

/-- `(n/2)^(n/2) ≤ n!` for `n ≥ 2`. -/
theorem half_pow_half_le_factorial (n : ℕ) (hn : 2 ≤ n) : (n / 2) ^ (n / 2) ≤ n.factorial := by
  have h1 := Nat.factorial_mul_pow_sub_le_factorial (Nat.div_le_self n 2)
  have h2 : (n / 2) ^ (n / 2) ≤ (n / 2) ^ (n - n / 2) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  calc (n / 2) ^ (n / 2) ≤ (n / 2) ^ (n - n / 2) := h2
    _ ≤ (n / 2).factorial * (n / 2) ^ (n - n / 2) :=
        Nat.le_mul_of_pos_left _ (Nat.factorial_pos _)
    _ ≤ n.factorial := h1

/-- `2^(n e + (n/2) ⌊log₂ (n/2)⌋) ≤ 2^(n e) · n!` for `n ≥ 2`. -/
theorem two_pow_le_pow_mul_factorial (n e : ℕ) (hn : 2 ≤ n) :
    (2 : ℝ) ^ (n * e + (n / 2) * Nat.log 2 (n / 2)) ≤ (2 : ℝ) ^ (n * e) * n.factorial := by
  rw [pow_add]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [mul_comm, pow_mul]
  calc ((2 : ℝ) ^ Nat.log 2 (n / 2)) ^ (n / 2) ≤ ((n / 2 : ℕ) : ℝ) ^ (n / 2) := by
        apply pow_le_pow_left₀ (by positivity)
        exact_mod_cast Nat.pow_log_le_self 2 (by omega : n / 2 ≠ 0)
    _ ≤ (n.factorial : ℝ) := by exact_mod_cast half_pow_half_le_factorial n hn

/-- The tail of the exponential series with `expTermCount e w` terms. -/
theorem exp_tail_le {x : ℝ} {e : ℕ} (he : 1 ≤ e) (hx : |x| ≤ (1 / 2 : ℝ) ^ e) (w : ℕ) :
    |Real.exp x - ∑ m ∈ range (expTermCount e w), x ^ m / (m.factorial : ℝ)|
      ≤ (1 / 2 : ℝ) ^ (w + 1) := by
  obtain ⟨hn2, hcond⟩ := expTermCount_spec e w he
  set n := expTermCount e w with hn
  have hx1 : |x| ≤ 1 := hx.trans (pow_le_one₀ (by norm_num) (by norm_num))
  have hb := Real.exp_bound hx1 (by omega : 0 < n)
  refine hb.trans ?_
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn2r : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hsucc : ((n.succ : ℕ) : ℝ) / (n.factorial * n) ≤ 2 / n.factorial := by
    rw [div_le_div_iff₀ (by positivity) hfac]
    push_cast
    nlinarith
  have hpow : |x| ^ n ≤ (1 / 2 : ℝ) ^ (n * e) := by
    rw [mul_comm, pow_mul]
    exact pow_le_pow_left₀ (abs_nonneg x) hx n
  calc |x| ^ n * ((n.succ : ℕ) / (n.factorial * n) : ℝ)
      ≤ (1 / 2 : ℝ) ^ (n * e) * (2 / n.factorial) :=
        mul_le_mul hpow hsucc (by positivity) (by positivity)
    _ = 2 / ((2 : ℝ) ^ (n * e) * n.factorial) := by
        rw [one_div_pow, one_div]; field_simp
    _ ≤ 2 / (2 : ℝ) ^ (n * e + (n / 2) * Nat.log 2 (n / 2)) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        exact two_pow_le_pow_mul_factorial n e hn2
    _ ≤ 2 / (2 : ℝ) ^ (w + 2) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        exact pow_le_pow_right₀ (by norm_num) hcond
    _ = (1 / 2 : ℝ) ^ (w + 1) := by rw [one_div_pow, pow_succ]; field_simp

/-! ### The quotient bracket -/

/-- `natQuotBracket n d k` encloses `n / d` with relative errors `6 · 2^(−k)` below and
`8 · 2^(−k)` above (`k ≥ 4`). -/
theorem natQuotBracket_spec (n d : AzNat) (hd : 0 < d.toNat) {k : ℕ} (hk : 4 ≤ k) :
    ∃ lv hv : ℝ, (natQuotBracket n d k).1.toVal = some (lv : EReal) ∧
      (natQuotBracket n d k).2.toVal = some (hv : EReal) ∧
      0 ≤ lv ∧ lv ≤ (n.toNat : ℝ) / d.toNat ∧
      ((n.toNat : ℝ) / d.toNat) * (1 - 6 * (1 / 2 : ℝ) ^ k) ≤ lv ∧
      (n.toNat : ℝ) / d.toNat ≤ hv ∧
      hv ≤ ((n.toNat : ℝ) / d.toNat) * (1 + 8 * (1 / 2 : ℝ) ^ k) := by
  have : NeZero k := ⟨by omega⟩
  set S : ℝ := (n.toNat : ℝ) / d.toNat with hSdef
  set nr : ℝ := (n.toNat : ℝ) with hndef
  set dr : ℝ := (d.toNat : ℝ) with hddef
  have hd0 : 0 < dr := by rw [hddef]; exact_mod_cast hd
  have hn : nr = S * dr := by rw [hSdef]; field_simp
  have hn0 : 0 ≤ nr := by rw [hndef]; exact Nat.cast_nonneg _
  have hS0 : 0 ≤ S := div_nonneg hn0 hd0.le
  set x := (1 / 2 : ℝ) ^ k with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 / 16 := by
    calc x ≤ (1 / 2 : ℝ) ^ 4 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
      _ = 1 / 16 := by norm_num
  unfold natQuotBracket seriesBracket
  simp only []
  obtain ⟨n₁, hn₁, hfn₁⟩ := setPrecFloor_err (toVal_ofAzNat n) hn0 k
  obtain ⟨d₁, hd₁, hcd₁⟩ := setPrecCeiling_err (toVal_ofAzNat d) hd0.le k
  obtain ⟨n₂, hn₂, hcn₂⟩ := setPrecCeiling_err (toVal_ofAzNat n) hn0 k
  obtain ⟨d₂, hd₂, hfd₂⟩ := setPrecFloor_err (toVal_ofAzNat d) hd0.le k
  have hd₁0 : 0 < d₁ := lt_of_lt_of_le hd0 hcd₁.ge
  have hd₂0 : 0 < d₂ := by
    have h0 : dr ≤ d₂ + 2 * dr * x := hfd₂.ge
    have h1 : 2 * dr * x ≤ 2 * dr * (1 / 16) := mul_le_mul_of_nonneg_left hx1 (by positivity)
    linarith
  obtain ⟨lv, hlv, hfl⟩ := divFloor_err hn₁ hd₁ hd₁0 hfn₁.nonneg k
  obtain ⟨hv, hhv, hcl⟩ := divCeiling_err hn₂ hd₂ hd₂0 (hn0.trans hcn₂.ge) k
  have hq1 : n₁ / d₁ ≤ S := by
    rw [hSdef]; exact div_le_div₀ hn0 hfn₁.le hd0 hcd₁.ge
  have hq2 : S ≤ n₂ / d₂ := by
    rw [hSdef]; exact div_le_div₀ (hn0.trans hcn₂.ge) hcn₂.ge hd₂0 hfd₂.le
  have hq1' : S * (1 - 4 * x) ≤ n₁ / d₁ := by
    rw [le_div_iff₀ hd₁0]
    have hc : 0 ≤ S * (1 - 4 * x) := mul_nonneg hS0 (by linarith)
    have h0 : d₁ ≤ dr + 2 * dr * x := hcd₁.le
    have h1 : S * (1 - 4 * x) * d₁ ≤ S * (1 - 4 * x) * (dr + 2 * dr * x) :=
      mul_le_mul_of_nonneg_left h0 hc
    have h2 : S * (1 - 4 * x) * (dr + 2 * dr * x)
        = S * dr * (1 - 2 * x) - 8 * (S * dr * (x * x)) := by ring
    have h3 : 0 ≤ S * dr * (x * x) :=
      mul_nonneg (mul_nonneg hS0 hd0.le) (mul_nonneg hx0.le hx0.le)
    have h4 : nr ≤ n₁ + 2 * nr * x := hfn₁.ge
    rw [hn] at h4
    linarith
  have hq2' : n₂ / d₂ ≤ S * (1 + 5 * x) := by
    rw [div_le_iff₀ hd₂0]
    have h0 : dr ≤ d₂ + 2 * dr * x := hfd₂.ge
    have h1 : S * (1 + 5 * x) * (dr - 2 * dr * x) ≤ S * (1 + 5 * x) * d₂ :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hS0 (by linarith))
    have h2 : S * (1 + 5 * x) * (dr - 2 * dr * x)
        = S * dr * (1 + 2 * x) + S * dr * (x * (1 - 10 * x)) := by ring
    have h3 : 0 ≤ S * dr * (x * (1 - 10 * x)) :=
      mul_nonneg (mul_nonneg hS0 hd0.le) (mul_nonneg hx0.le (by linarith))
    have h4 : n₂ ≤ nr + 2 * nr * x := hcn₂.le
    rw [hn] at h4
    linarith
  have hfl1 := hfl.le
  have hfl2 : n₁ / d₁ ≤ lv + 2 * (n₁ / d₁) * x := hfl.ge
  have hcl1 := hcl.ge
  have hcl2 : hv ≤ n₂ / d₂ + 2 * (n₂ / d₂) * x := hcl.le
  refine ⟨lv, hv, hlv, hhv, hfl.nonneg, hfl1.trans hq1, ?_, hq2.trans hcl1, ?_⟩
  · have h1 : S * (1 - 4 * x) * (1 - 2 * x) ≤ n₁ / d₁ * (1 - 2 * x) :=
      mul_le_mul_of_nonneg_right hq1' (by linarith)
    have h2 : S * (1 - 4 * x) * (1 - 2 * x) = S * (1 - 6 * x) + 8 * (S * (x * x)) := by ring
    have h3 : 0 ≤ S * (x * x) := mul_nonneg hS0 (mul_nonneg hx0.le hx0.le)
    linarith
  · have h1 : n₂ / d₂ * (1 + 2 * x) ≤ S * (1 + 5 * x) * (1 + 2 * x) :=
      mul_le_mul_of_nonneg_right hq2' (by linarith)
    have h2 : S * (1 + 5 * x) * (1 + 2 * x) = S * (1 + 8 * x) - S * (x * (1 - 10 * x)) := by ring
    have h3 : 0 ≤ S * (x * (1 - 10 * x)) := mul_nonneg hS0 (mul_nonneg hx0.le (by linarith))
    linarith

/-! ### One chunk -/

set_option maxHeartbeats 400000 in
/-- `exp (p / 2^s)` is enclosed by `expChunkBracket` with width at most `2 · 2^(−w)` and lower end
at least `1/2`, for `p / 2^s ≤ 2^(−e)`, `e ≥ 1`, `w ≥ 8`. -/
theorem expChunkBracket_spec (p : AzNat) (s e w : ℕ) (he : 1 ≤ e) (hw : 8 ≤ w)
    (hx : (p.toNat : ℝ) / 2 ^ s ≤ (1 / 2 : ℝ) ^ e) :
    ∃ lo hi : ℝ, (expChunkBracket p s e w).1.toVal = some (lo : EReal) ∧
      (expChunkBracket p s e w).2.toVal = some (hi : EReal) ∧
      lo ≤ Real.exp ((p.toNat : ℝ) / 2 ^ s) ∧ Real.exp ((p.toNat : ℝ) / 2 ^ s) ≤ hi ∧
      hi - lo ≤ 2 * (1 / 2 : ℝ) ^ w ∧ 1 / 2 ≤ lo := by
  have : NeZero (w + 8) := ⟨by omega⟩
  set x : ℝ := (p.toNat : ℝ) / 2 ^ s with hxdef
  have hx0 : 0 ≤ x := by positivity
  have hxh : x ≤ 1 / 2 := hx.trans (pow_le_of_le_one (by norm_num) (by norm_num) (by omega))
  obtain ⟨hn2, -⟩ := expTermCount_spec e w he
  set n := expTermCount e w with hn
  -- the exact partial sum and the tail
  set S : ℝ := ∑ m ∈ range n, x ^ m / (m.factorial : ℝ) with hS
  have htail : |Real.exp x - S| ≤ (1 / 2 : ℝ) ^ (w + 1) :=
    exp_tail_le he (by rw [abs_of_nonneg hx0]; exact hx) w
  set t : ℝ := (1 / 2 : ℝ) ^ (w + 1) with ht
  set u : ℝ := (1 / 2 : ℝ) ^ w with hu
  have hu0 : 0 < u := by positivity
  have hu1 : u ≤ 1 / 256 := by
    calc u ≤ (1 / 2 : ℝ) ^ 8 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hw
      _ = 1 / 256 := by norm_num
  have htu : t = u / 2 := by rw [ht, hu, pow_succ]; ring
  have hS1 : 1 ≤ S := by
    have := single_le_sum (f := fun m : ℕ => x ^ m / (m.factorial : ℝ))
      (fun m _ => by positivity) (mem_range.mpr (by omega : 0 < n))
    simpa using this
  have hexp2 : Real.exp x ≤ 7 / 4 := by
    have := Real.abs_exp_sub_one_sub_id_le (by rw [abs_of_nonneg hx0]; linarith : |x| ≤ 1)
    rw [abs_le] at this
    nlinarith
  have hS2 : S ≤ 2 := by
    rw [abs_le] at htail
    linarith
  -- the exact fraction
  have hnd := AzNat.expNumDen_eq p s (n - 1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hnd
  have hden := AzNat.expNumDen_den_pos p s (n - 1)
  set num := (AzNat.expNumDen p s (n - 1)).1 with hnum
  set den := (AzNat.expNumDen p s (n - 1)).2 with hdenv
  set Q : ℝ := (2 : ℝ) ^ (s * (n - 1)) with hQ
  have hQ0 : 0 < Q := by positivity
  have hnd' : (num.toNat : ℝ) / (den.toNat * Q) = S := by rw [hS, hxdef]; exact hnd
  have hfrac : (num.toNat : ℝ) / den.toNat = S * Q := by
    rw [← hnd']; field_simp
  obtain ⟨lv, hv, hlv, hhv, -, hlv2, hlv1, hhv1, hhv2⟩ :=
    natQuotBracket_spec num den hden (k := w + 8) (by omega)
  rw [hfrac] at hlv1 hlv2 hhv1 hhv2
  set xk : ℝ := (1 / 2 : ℝ) ^ (w + 8) with hxk
  have hxk0 : 0 < xk := by positivity
  have h256 : ((1 : ℝ) / 2) ^ 8 = 1 / 256 := by norm_num
  have hxku : xk = u / 256 := by rw [hxk, hu, pow_add, h256]; ring
  -- the exact shift by `2^(−s(n−1))`
  have hsh : ((-(AzNat.ofNat (s * (n - 1))).toAzInt).toInt : ℤ) = -((s * (n - 1) : ℕ) : ℤ) := by
    rw [AzInt.toInt_neg, toInt_toAzInt, AzNat.toNat_ofNat]
  have hshv : (2 : ℝ) ^ ((-(AzNat.ofNat (s * (n - 1))).toAzInt).toInt) = 1 / Q := by
    rw [hsh, zpow_neg, zpow_natCast, one_div]
  have hlo₁ := toVal_shiftLeft_of_toVal hlv (-(AzNat.ofNat (s * (n - 1))).toAzInt)
  have hhi₁ := toVal_shiftLeft_of_toVal hhv (-(AzNat.ofNat (s * (n - 1))).toAzInt)
  rw [hshv] at hlo₁ hhi₁
  set lo₁ : ℝ := lv * (1 / Q) with hlo₁def
  set hi₁ : ℝ := hv * (1 / Q) with hhi₁def
  have hlo₁1 : S * (1 - 6 * xk) ≤ lo₁ := by
    rw [hlo₁def]
    calc S * (1 - 6 * xk) = S * Q * (1 - 6 * xk) * (1 / Q) := by field_simp
      _ ≤ lv * (1 / Q) := mul_le_mul_of_nonneg_right hlv1 (by positivity)
  have hlo₁2 : lo₁ ≤ S := by
    rw [hlo₁def]
    calc lv * (1 / Q) ≤ S * Q * (1 / Q) := mul_le_mul_of_nonneg_right hlv2 (by positivity)
      _ = S := by field_simp
  have hhi₁1 : S ≤ hi₁ := by
    rw [hhi₁def]
    calc S = S * Q * (1 / Q) := by field_simp
      _ ≤ hv * (1 / Q) := mul_le_mul_of_nonneg_right hhv1 (by positivity)
  have hhi₁2 : hi₁ ≤ S * (1 + 8 * xk) := by
    rw [hhi₁def]
    calc hv * (1 / Q) ≤ S * Q * (1 + 8 * xk) * (1 / Q) :=
          mul_le_mul_of_nonneg_right hhv2 (by positivity)
      _ = S * (1 + 8 * xk) := by field_simp
  -- the tail float
  have htailv : (powerOf2 (-(AzNat.ofNat (w + 1)).toAzInt)).toVal = some (t : EReal) := by
    rw [toVal_powerOf2, AzInt.toInt_neg, toInt_toAzInt, AzNat.toNat_ofNat, zpow_neg, zpow_natCast,
      ht, one_div_pow, one_div]
  unfold expChunkBracket
  simp only []
  rw [← hn, ← hnum, ← hdenv]
  obtain ⟨lo, hlo, hlo1, hlo2⟩ := subFloor_abs hlo₁ htailv (w + 8)
  obtain ⟨hi, hhi, hhi1, hhi2⟩ := addCeiling_abs hhi₁ htailv (w + 8)
  rw [abs_le] at htail
  have hSxk : S * xk ≤ 2 * xk := mul_le_mul_of_nonneg_right hS2 hxk0.le
  have hS6 : 1 * (1 - 6 * xk) ≤ S * (1 - 6 * xk) :=
    mul_le_mul_of_nonneg_right hS1 (by linarith)
  have hlt : 0 ≤ lo₁ - t := by linarith
  rw [abs_of_nonneg hlt] at hlo2
  rw [abs_of_nonneg (by linarith : 0 ≤ hi₁ + t)] at hhi2
  refine ⟨lo, hi, hlo, hhi, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · have h1 : hi₁ - lo₁ ≤ 28 * xk := by linarith
    have h2 : hi₁ + lo₁ ≤ 5 := by linarith
    have h3 : hi - lo ≤ (hi₁ - lo₁) + 2 * t + 2 * xk * (hi₁ + lo₁) := by linarith
    have h4 : 2 * xk * (hi₁ + lo₁) ≤ 2 * xk * 5 :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith
  · have hl1 : lo₁ - t ≤ 2 := by linarith
    have hl2 : (lo₁ - t) * xk ≤ 2 * xk := mul_le_mul_of_nonneg_right hl1 hxk0.le
    linarith

/-! ### The chunks -/

/-- The value of a chunk `(p, s, e)`: `p / 2^s`. -/
noncomputable def chunkVal (c : AzNat × ℕ × ℕ) : ℝ := (c.1.toNat : ℝ) / 2 ^ c.2.1

theorem expChunks_length (M : AzNat) : ∀ K, (expChunks M K).length = K + 1
  | 0 => rfl
  | K + 1 => by
    simp only [expChunks, List.length_append, List.length_singleton]
    rw [expChunks_length _ K]

/-- The chunks of `M / 2^(2^K)` sum to it, and each chunk `(p, s, e)` has `e ≥ 1` and value at
most `2^(−e)`. -/
theorem expChunks_spec : ∀ (K : ℕ) (M : AzNat), M.toNat < 2 ^ (2 ^ K) →
    ((expChunks M K).map chunkVal).sum = (M.toNat : ℝ) / 2 ^ (2 ^ K) ∧
      ∀ c ∈ expChunks M K, 1 ≤ c.2.2 ∧ chunkVal c ≤ (1 / 2 : ℝ) ^ c.2.2
  | 0, M, hM => by
    have hM1 : M.toNat ≤ 1 := by norm_num at hM; omega
    have h : (M.toNat : ℝ) ≤ 1 := by exact_mod_cast hM1
    refine ⟨?_, ?_⟩
    · simp [expChunks, chunkVal]
    · intro c hc
      simp only [expChunks, List.mem_singleton] at hc
      subst hc
      refine ⟨le_rfl, ?_⟩
      simp only [chunkVal, pow_one]
      linarith [div_le_div_of_nonneg_right h (by norm_num : (0 : ℝ) ≤ 2)]
  | K + 1, M, hM => by
    set h := 2 ^ K with hh
    set hi := M >>> h with hhi
    set lo := M - (hi <<< h) with hlo
    have hhiN : hi.toNat = M.toNat / 2 ^ h := by
      rw [hhi, AzNat.toNat_hShiftRight, Nat.shiftRight_eq_div_pow]
    have hloN : lo.toNat = M.toNat % 2 ^ h := by
      rw [hlo, AzNat.toNat_sub, AzNat.toNat_hShiftLeft, Nat.shiftLeft_eq, hhiN]
      have := Nat.div_add_mod' M.toNat (2 ^ h)
      omega
    have hpow : 2 ^ (2 ^ (K + 1)) = 2 ^ h * 2 ^ h := by
      rw [← pow_add, hh, ← two_mul, pow_succ, mul_comm]
    have hpowR : (2 : ℝ) ^ (2 ^ (K + 1)) = 2 ^ h * 2 ^ h := by
      rw [← pow_add, hh, ← two_mul, pow_succ, mul_comm]
    have hhi_lt : hi.toNat < 2 ^ (2 ^ K) := by
      rw [hhiN, Nat.div_lt_iff_lt_mul (by positivity), ← hh, ← hpow]
      exact hM
    have hlo_lt : lo.toNat < 2 ^ h := by rw [hloN]; exact Nat.mod_lt _ (by positivity)
    obtain ⟨ih1, ih2⟩ := expChunks_spec K hi hhi_lt
    simp only [expChunks]
    rw [← hhi, ← hlo]
    refine ⟨?_, ?_⟩
    · rw [List.map_append, List.sum_append, ih1]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, chunkVal]
      have hM' : (M.toNat : ℝ) = (hi.toNat : ℝ) * 2 ^ h + lo.toNat := by
        rw [hhiN, hloN]
        exact_mod_cast (Nat.div_add_mod' M.toNat (2 ^ h)).symm
      rw [hM', hpowR]
      field_simp
      ring
    · intro c hc
      rw [List.mem_append, List.mem_singleton] at hc
      rcases hc with hc | hc
      · exact ih2 c hc
      · subst hc
        refine ⟨Nat.one_le_two_pow, ?_⟩
        simp only [chunkVal]
        rw [hpowR, ← hh]
        have hlo' : (lo.toNat : ℝ) ≤ 2 ^ h := by exact_mod_cast hlo_lt.le
        calc (lo.toNat : ℝ) / ((2 : ℝ) ^ h * 2 ^ h)
            ≤ (2 : ℝ) ^ h / ((2 : ℝ) ^ h * 2 ^ h) :=
              div_le_div_of_nonneg_right hlo' (by positivity)
          _ = (1 / 2 : ℝ) ^ h := by rw [one_div_pow, one_div]; field_simp

/-! ### The product of the chunk brackets -/

/-- The product of chunk brackets encloses `exp (∑ values)` with relative errors `(1 ± 8u)` to
the power `length`, `u = 2^(−w)`. -/
theorem expChunksBracket_spec (w : ℕ) (hw : 8 ≤ w) : ∀ l : List (AzNat × ℕ × ℕ),
    (∀ c ∈ l, 1 ≤ c.2.2 ∧ chunkVal c ≤ (1 / 2 : ℝ) ^ c.2.2) →
    ∃ lo hi : ℝ, (expChunksBracket w l).1.toVal = some (lo : EReal) ∧
      (expChunksBracket w l).2.toVal = some (hi : EReal) ∧ 0 < lo ∧
      Real.exp (l.map chunkVal).sum * (1 - 8 * (1 / 2 : ℝ) ^ w) ^ l.length ≤ lo ∧
      lo ≤ Real.exp (l.map chunkVal).sum ∧ Real.exp (l.map chunkVal).sum ≤ hi ∧
      hi ≤ Real.exp (l.map chunkVal).sum * (1 + 8 * (1 / 2 : ℝ) ^ w) ^ l.length
  | [], _ => by
    refine ⟨1, 1, toVal_one', toVal_one', one_pos, ?_, ?_, ?_, ?_⟩ <;> simp
  | (p, s, e) :: rest, hl => by
    have : NeZero (w + 8) := ⟨by omega⟩
    obtain ⟨he, hc⟩ := hl (p, s, e) List.mem_cons_self
    obtain ⟨a, b, ha, hb, ha1, hb1, hab, ha2⟩ := expChunkBracket_spec p s e w he hw hc
    obtain ⟨lr, hr, hlr, hhr, hlr0, hlr1, hlr2, hhr1, hhr2⟩ :=
      expChunksBracket_spec w hw rest (fun c hc => hl c (List.mem_cons_of_mem _ hc))
    set u : ℝ := (1 / 2 : ℝ) ^ w with hu
    have hu0 : 0 < u := by positivity
    have hu1 : u ≤ 1 / 256 := by
      calc u ≤ (1 / 2 : ℝ) ^ 8 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hw
        _ = 1 / 256 := by norm_num
    set xk : ℝ := (1 / 2 : ℝ) ^ (w + 8) with hxk
    have hxk0 : 0 < xk := by positivity
    have h256 : ((1 : ℝ) / 2) ^ 8 = 1 / 256 := by norm_num
    have hxku : xk = u / 256 := by rw [hxk, hu, pow_add, h256]; ring
    set Ec : ℝ := Real.exp (chunkVal (p, s, e)) with hEc
    set Er : ℝ := Real.exp (rest.map chunkVal).sum with hEr
    have hEc1 : 1 ≤ Ec := by
      have hv0 : 0 ≤ chunkVal (p, s, e) := by unfold chunkVal; positivity
      have := Real.add_one_le_exp (chunkVal (p, s, e))
      linarith
    have hEr0 : 0 < Er := Real.exp_pos _
    have ha0 : 0 < a := by linarith
    have hpow0 : 0 ≤ (1 - 8 * u) ^ rest.length := pow_nonneg (by linarith) _
    have hb0 : 0 < b := by linarith
    have hhr0 : 0 < hr := by linarith
    obtain ⟨lo, hlo, hflo⟩ := mulFloor_err ha hlr (w + 8) (mul_pos ha0 hlr0).le
    obtain ⟨hi, hhi, hchi⟩ := mulCeiling_err hb hhr (w + 8) (mul_pos hb0 hhr0).le
    have hlo1 : a * lr * (1 - 2 * xk) ≤ lo := by have := hflo.ge; linarith
    have hhi1 : hi ≤ b * hr * (1 + 2 * xk) := by have := hchi.le; linarith
    have huEc : 2 * u * 1 ≤ 2 * u * Ec := mul_le_mul_of_nonneg_left hEc1 (by positivity)
    have ha1' : a ≤ Ec := ha1
    have hb1' : Ec ≤ b := hb1
    have ha3 : Ec * (1 - 2 * u) ≤ a := by linarith
    have hb3 : b ≤ Ec * (1 + 2 * u) := by linarith
    simp only [expChunksBracket, List.map_cons, List.sum_cons, List.length_cons, Real.exp_add,
      pow_succ]
    rw [← hEc, ← hEr]
    refine ⟨lo, hi, hlo, hhi, ?_, ?_, ?_, ?_, ?_⟩
    · have : 0 < a * lr * (1 - 2 * xk) := mul_pos (mul_pos ha0 hlr0) (by linarith)
      linarith
    · calc Ec * Er * ((1 - 8 * u) ^ rest.length * (1 - 8 * u))
          ≤ (Ec * (1 - 2 * u)) * (Er * (1 - 8 * u) ^ rest.length) * (1 - 2 * xk) := by
            have h1 : (1 - 8 * u) ≤ (1 - 2 * u) * (1 - 2 * xk) := by nlinarith
            have h2 : 0 ≤ Ec * Er * (1 - 8 * u) ^ rest.length := by positivity
            nlinarith
        _ ≤ a * lr * (1 - 2 * xk) := by
            apply mul_le_mul_of_nonneg_right _ (by linarith)
            exact mul_le_mul ha3 hlr1 (by positivity) ha0.le
        _ ≤ lo := hlo1
    · calc lo ≤ a * lr := hflo.le
        _ ≤ Ec * Er := mul_le_mul ha1 hlr2 hlr0.le (by linarith)
    · calc Ec * Er ≤ b * hr := mul_le_mul hb1 hhr1 hEr0.le (by linarith)
        _ ≤ hi := hchi.ge
    · calc hi ≤ b * hr * (1 + 2 * xk) := hhi1
        _ ≤ (Ec * (1 + 2 * u)) * (Er * (1 + 8 * u) ^ rest.length) * (1 + 2 * xk) := by
            apply mul_le_mul_of_nonneg_right _ (by linarith)
            exact mul_le_mul hb3 hhr2 (by linarith) (by positivity)
        _ ≤ Ec * Er * ((1 + 8 * u) ^ rest.length * (1 + 8 * u)) := by
            have h1 : (1 + 2 * u) * (1 + 2 * xk) ≤ 1 + 8 * u := by nlinarith
            have h2 : 0 ≤ Ec * Er * (1 + 8 * u) ^ rest.length := by positivity
            nlinarith

/-- `(1 + 8u)^n − (1 − 8u)^n ≤ 24 n u` for `8 n u ≤ 1`. -/
theorem pow_width_le (n : ℕ) {u : ℝ} (hu : 0 ≤ u) (hu8 : 8 * u ≤ 1) (hnu : 8 * n * u ≤ 1) :
    (1 + 8 * u) ^ n - (1 - 8 * u) ^ n ≤ 24 * n * u := by
  have hupper : (1 + 8 * u) ^ n ≤ 1 + 16 * n * u := by
    have h1 : (1 + 8 * u) ^ n ≤ Real.exp (8 * u) ^ n :=
      pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (8 * u)]) n
    rw [← Real.exp_nat_mul] at h1
    have h2 := Real.abs_exp_sub_one_sub_id_le (x := n * (8 * u))
      (by rw [abs_of_nonneg (by positivity)]; linarith)
    rw [abs_le] at h2
    have h3 : (n * (8 * u)) ^ 2 ≤ n * (8 * u) := by
      have : 0 ≤ n * (8 * u) := by positivity
      nlinarith
    nlinarith
  have hlower : 1 - 8 * n * u ≤ (1 - 8 * u) ^ n := by
    have := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ -(8 * u)) n
    have e1 : (1 : ℝ) + -(8 * u) = 1 - 8 * u := by ring
    rw [e1] at this
    linarith
  linarith

/-- `expDyadicBracket M K w` encloses `exp (M / 2^(2^K))` with relative errors `(1 ± 8 · 2^(−w))`
to the power `K + 1`. -/
theorem expDyadicBracket_spec (M : AzNat) (K w : ℕ) (hw : 8 ≤ w) (hM : M.toNat < 2 ^ (2 ^ K)) :
    ∃ lo hi : ℝ, (expDyadicBracket M K w).1.toVal = some (lo : EReal) ∧
      (expDyadicBracket M K w).2.toVal = some (hi : EReal) ∧ 0 < lo ∧
      Real.exp ((M.toNat : ℝ) / 2 ^ (2 ^ K)) * (1 - 8 * (1 / 2 : ℝ) ^ w) ^ (K + 1) ≤ lo ∧
      lo ≤ Real.exp ((M.toNat : ℝ) / 2 ^ (2 ^ K)) ∧
      Real.exp ((M.toNat : ℝ) / 2 ^ (2 ^ K)) ≤ hi ∧
      hi ≤ Real.exp ((M.toNat : ℝ) / 2 ^ (2 ^ K)) * (1 + 8 * (1 / 2 : ℝ) ^ w) ^ (K + 1) := by
  obtain ⟨hsum, hchunks⟩ := expChunks_spec K M hM
  obtain ⟨lo, hi, hlo, hhi, h0, h1, h2, h3, h4⟩ :=
    expChunksBracket_spec w hw (expChunks M K) hchunks
  rw [hsum] at h1 h2 h3 h4
  rw [expChunks_length] at h1 h4
  exact ⟨lo, hi, hlo, hhi, h0, h1, h2, h3, h4⟩

end Azurite.AzFloat
