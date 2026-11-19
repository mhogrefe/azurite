/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.LnGammaBracket
import Azurite.AzFloat.Equiv.LnGammaEventually
import Azurite.AzFloat.Equiv.ZivSpec
import Azurite.AzFloat.Equiv.GammaRatBracket
import Azurite.AzFloat.Equiv.LogBaseExact
import Azurite.AzFloat.Equiv.Pow
import Azurite.Transcendental.Exp

/-!
# Convergence of the brackets of `ln Γ`, and its Ziv certificate at the integers

* `lnGammaApproxOf_width`, `lnGammaApproxOf_bracketConv`: the pair of `Roundable`s made from an
  enclosure of width `ε w → 0` converges (`BracketConv`).  This serves every function whose
  bracket goes through `lnGammaApproxOf`.
* `lnGammaApprox_bracketConv`, `lnGammaRatApprox_bracketConv`: the brackets of `ln Γ(x)` at a
  positive float and at a positive rational converge.
* `irrational_log_gamma_nat`: `ln Γ(n) = ln (n − 1)!` is irrational for an integer `n ≥ 3`.
* `lnGammaApprox_cert_int`, `lnGammaRatApprox_cert_int`: the Ziv certificates there.
-/

namespace Azurite.AzFloat

open Filter Topology

/-- The width of the logarithm bracket tends to `0`. -/
theorem tendsto_lnW_add {G : ℝ} (hG : 0 ≤ G) (c : ℕ) :
    Tendsto (fun w : ℕ => lnW G (w + c)) atTop (𝓝 0) := by
  have hPB : PB fun w : ℕ => 2 ^ 42 * ((w : ℝ) + c + 2 * G + 10) ^ 5 :=
    ((((PB.natCast.add (PB.const c)).add (PB.const (2 * G))).add (PB.const 10)).pow 5).const_mul
      _
  refine squeeze_zero (fun w => lnW_nonneg hG _) (fun w => ?_) hPB.tendsto
  unfold lnW
  push_cast
  have h1 : (1 / 2 : ℝ) ^ (w + c) ≤ (1 / 2 : ℝ) ^ w :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

/-- A bracket as `Roundable`s encloses its value, strictly from below, with the width of the
enclosure and what lowering the lower end adds. -/
theorem lnGammaApproxOf_width {b : Encl} {v ε : ℝ} (hb : AEncl b v ε) (w : ℕ) :
    ∃ lv hv : ℝ, Rounds (lnGammaApproxOf b w).1 lv ∧ Rounds (lnGammaApproxOf b w).2 hv ∧
      lv < v ∧ v ≤ hv ∧
      hv - lv ≤ ε + (1 / 2 : ℝ) ^ (4 * w)
        + 2 * (|v| + ε + 1) * (1 / 2 : ℝ) ^ (2 * w + 64) := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, h3⟩ := hb
  have : NeZero (2 * w + 64) := ⟨by omega⟩
  have ht : (powerOf2 (-(AzNat.ofNat (4 * w)).toAzInt)).toVal
      = some (((1 / 2 : ℝ) ^ (4 * w) : ℝ) : EReal) := by
    rw [toVal_powerOf2, AzInt.toInt_neg, AzNat.toInt_toAzInt, AzNat.toNat_ofNat, zpow_neg,
      zpow_natCast, one_div_pow, one_div]
  obtain ⟨r, hr, hrle, hrge⟩ := subFloor_abs hlo ht (2 * w + 64)
  have hpow : (0 : ℝ) < (1 / 2 : ℝ) ^ (4 * w) := by positivity
  have hpow1 : (1 / 2 : ℝ) ^ (4 * w) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hu0 : (0 : ℝ) < (1 / 2 : ℝ) ^ (2 * w + 64) := by positivity
  have habs : |lo - (1 / 2 : ℝ) ^ (4 * w)| ≤ |v| + ε + 1 := by
    rw [abs_le]
    constructor
    · have := neg_abs_le v
      linarith
    · have := le_abs_self v
      linarith
  have hmul := mul_le_mul_of_nonneg_right habs hu0.le
  refine ⟨r, hi, ?_, ?_, by linarith, h2, by linarith⟩
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hr)
    rw [fval_of_toVal_coe hr] at hR
    exact hR
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
    rw [fval_of_toVal_coe hhi] at hR
    exact hR

/-- **Brackets made from enclosures whose widths tend to `0` converge.** -/
theorem lnGammaApproxOf_bracketConv {b : ℕ → Encl} {v : ℝ} {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (h : ∀ᶠ w in atTop, AEncl (b w) v (ε w)) :
    BracketConv (fun w => lnGammaApproxOf (b w) w) v := by
  obtain ⟨W₀, hW₀⟩ := eventually_atTop.mp h
  have hhalf := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  have hp4 : Tendsto (fun w : ℕ => (1 / 2 : ℝ) ^ (4 * w)) atTop (𝓝 0) :=
    hhalf.comp (tendsto_atTop_mono (fun w : ℕ => (by omega : w ≤ 4 * w)) tendsto_id)
  have hp2 : Tendsto (fun w : ℕ => (1 / 2 : ℝ) ^ (2 * w + 64)) atTop (𝓝 0) :=
    hhalf.comp (tendsto_atTop_mono (fun w : ℕ => (by omega : w ≤ 2 * w + 64)) tendsto_id)
  have hE : Tendsto (fun w => ε w + (1 / 2 : ℝ) ^ (4 * w)
      + 2 * (|v| + ε w + 1) * (1 / 2 : ℝ) ^ (2 * w + 64)) atTop (𝓝 0) := by
    have := (hε.add hp4).add ((((hε.const_add |v|).add_const 1).const_mul 2).mul hp2)
    simpa using this
  refine ⟨_, hE, W₀, fun w hw => ?_⟩
  obtain ⟨lv, hv, a1, a2, a3, a4, a5⟩ := lnGammaApproxOf_width (hW₀ w hw) w
  exact ⟨lv, hv, a1, a2, a3.le, a4, a5⟩

/-- **The bracket of `ln Γ(x)` converges** at a positive float. -/
theorem lnGammaApprox_bracketConv {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hpos : 0 < xv) (e : AzInt) :
    BracketConv (lnGammaApprox x e) (Real.log (Real.Gamma xv)) := by
  obtain ⟨W₀, hW₀⟩ := lnGammaBracketEncl_eventually hpos e
  exact lnGammaApproxOf_bracketConv (tendsto_lgEps xv e)
    (eventually_atTop.mpr ⟨W₀, fun w hw =>
      hW₀ w hw _ 0 (LEncl.exact hx hpos) le_rfl (by positivity)⟩)

/-- **The bracket of `ln Γ(q)` converges** at a positive rational.  (The exponent handed to
the bracket is that of the rounded argument, one of two values.) -/
theorem lnGammaRatApprox_bracketConv (q : AzRat) (hq : 0 < ((AzRat.toRat q : ℚ) : ℝ)) :
    BracketConv (lnGammaRatApprox q) (Real.log (Real.Gamma ((AzRat.toRat q : ℚ) : ℝ))) := by
  set xv := ((AzRat.toRat q : ℚ) : ℝ) with hxv
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow hq (by norm_num : (1 : ℝ) < 2)
  obtain ⟨W₁, hW₁⟩ := lnGammaBracketEncl_eventually hq (AzInt.ofInt (n + 1))
  obtain ⟨W₂, hW₂⟩ := lnGammaBracketEncl_eventually hq (AzInt.ofInt (n + 2))
  have hE := (tendsto_lgEps xv (AzInt.ofInt (n + 1))).max (tendsto_lgEps xv (AzInt.ofInt (n + 2)))
  rw [max_self] at hE
  refine lnGammaApproxOf_bracketConv hE ?_
  filter_upwards [eventually_ge_atTop W₁, eventually_ge_atTop W₂] with w h1 h2
  have hL := lnGammaRatEncl_L q hq w
  have : NeZero (w + 32) := ⟨by omega⟩
  obtain ⟨s, hs, hs1, hs2⟩ := ofAzRatRound_ceiling_abs q (w + 32)
  have hs' : (lnGammaRatEncl q w).2.toVal = some (s : EReal) := hs
  obtain ⟨e, q', m, hm, hfin⟩ := exists_finite_true_of_toVal_pos hs' (by linarith)
  have hb := abs_finiteVal_bounds true e hm
  have hsv : finiteVal true e m = s := by
    rw [hfin, toVal_finite, Option.some.injEq, EReal.coe_eq_coe_iff] at hs'
    exact hs'
  rw [hsv, abs_of_pos (by linarith)] at hb
  have hs2' : s ≤ 2 * xv := by
    rw [abs_of_pos hq] at hs2
    have h12 : (1 / 2 : ℝ) ^ (w + 32) ≤ 1 / 2 :=
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega : 1 ≤ w + 32)).trans
        (by norm_num)
    nlinarith
  have he1 : n + 1 ≤ e.toInt := by
    by_contra hlt
    push Not at hlt
    have : (2 : ℝ) ^ e.toInt ≤ 2 ^ n := zpow_le_zpow_right₀ (by norm_num) (by omega)
    linarith [hb.2]
  have he2 : e.toInt ≤ n + 2 := by
    by_contra hlt
    push Not at hlt
    have h3 : (2 : ℝ) ^ (n + 2) ≤ 2 ^ (e.toInt - 1) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h22 : (2 : ℝ) ^ (n + 2) = 2 ^ (n + 1) * 2 := by
      rw [show n + 2 = n + 1 + 1 by ring, zpow_add_one₀ (by norm_num)]
    linarith [hb.1]
  have hexp : (lnGammaRatEncl q w).2.exponent?.getD (AzInt.ofInt 0) = e := by
    rw [hfin]
    rfl
  have hcase : e = AzInt.ofInt (n + 1) ∨ e = AzInt.ofInt (n + 2) := by
    rcases (by omega : e.toInt = n + 1 ∨ e.toInt = n + 2) with h | h
    · left; rw [← AzInt.ofInt_toInt e, h]
    · right; rw [← AzInt.ofInt_toInt e, h]
  show AEncl (lnGammaRatBracket q w) _ _
  unfold lnGammaRatBracket
  rw [hexp]
  rcases hcase with h | h <;> rw [h]
  · exact (hW₁ w h1 _ _ hL (by positivity) (six_le_eight w)).mono (le_max_left _ _)
  · exact (hW₂ w h2 _ _ hL (by positivity) (six_le_eight w)).mono (le_max_right _ _)

/-! ### The integers -/

/-- `ln Γ(n) = ln (n − 1)!` is irrational for an integer `n ≥ 3`. -/
theorem irrational_log_gamma_nat {n : ℕ} (hn : 3 ≤ n) :
    Irrational (Real.log (Real.Gamma (n : ℝ))) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hG : Real.Gamma ((k + 1 : ℕ) : ℝ) = ((k.factorial : ℚ) : ℝ) := by
    push_cast
    exact Real.Gamma_nat_eq_factorial k
  rw [hG]
  have h2 : 2 ≤ k.factorial := le_trans (by omega) (Nat.self_le_factorial k)
  refine irrational_log_rat (by positivity) fun h => ?_
  have : k.factorial = 1 := by exact_mod_cast h
  omega

/-- A positive integer float other than `1` and `2` is an integer `n ≥ 3`. -/
theorem lnGammaInt_spec {e : AzInt} {q : ℕ} {m : AzNat} (hv : FiniteValid q m)
    (h12 : ¬ (eqIEEE (finite true e q m hv) one
      || eqIEEE (finite true e q m hv) (ofAzNat (AzNat.ofNat 2))) = true)
    (hI : isInteger (finite true e q m hv) = true) :
    ∃ n : ℕ, 3 ≤ n ∧ finiteVal true e m = n := by
  have hx := toVal_finite true e q m hv
  have hpos := finiteVal_true_pos e hv
  obtain ⟨k, hk⟩ := (isInteger_iff_of_toVal hx).mp hI
  have hk1 : 1 ≤ k := by
    have : (0 : ℝ) < k := hk ▸ hpos
    exact_mod_cast this
  rw [Bool.or_eq_true, not_or] at h12
  obtain ⟨hn1, hn2⟩ := h12
  have hk1' : k ≠ 1 := fun h => hn1 (by
    rw [eqIEEE_one_iff, hx, hk, h]
    simp)
  have hk2' : k ≠ 2 := fun h => hn2 (by
    rw [eqIEEE_iff]
    exact ⟨_, hx, by rw [toVal_ofAzNat_ofNat, hk, h]; simp⟩)
  exact ⟨k.toNat, by omega, by rw [hk]; exact_mod_cast (Int.toNat_of_nonneg (by omega)).symm⟩

/-- **The Ziv certificate of `ln Γ(n)` at an integer float `n ≥ 3`.** -/
theorem lnGammaApprox_cert_int {e : AzInt} {q : ℕ} {m : AzNat} (hv : FiniteValid q m)
    (h12 : ¬ (eqIEEE (finite true e q m hv) one
      || eqIEEE (finite true e q m hv) (ofAzNat (AzNat.ofNat 2))) = true)
    (hI : isInteger (finite true e q m hv) = true) (p : ℕ) [NeZero p] (mode : RoundingMode)
    (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (lnGammaApprox (finite true e q m hv) e (w₀ * 2 ^ f)).1
      (lnGammaApprox (finite true e q m hv) e (w₀ * 2 ^ f)).2 p mode).isSome = true := by
  obtain ⟨n, hn, hval⟩ := lnGammaInt_spec hv h12 hI
  have hirr := irrational_log_gamma_nat hn
  rw [← hval] at hirr
  exact (lnGammaApprox_bracketConv (toVal_finite true e q m hv) (finiteVal_true_pos e hv)
    e).exists_isSome hirr.ne_zero p (not_mem_floatSet_of_irrational p hirr) mode w₀ hw₀

/-- A positive integer rational other than `1` and `2` is an integer `n ≥ 3`. -/
theorem lnGammaRatInt_spec {q : AzRat} (h0 : q.num ≠ 0) (hs : q.sign = true)
    (h12 : ¬ ((q - 1).num = 0 ∨ (q - 1 - 1).num = 0)) (hI : q.den = 1) :
    ∃ n : ℕ, 3 ≤ n ∧ ((AzRat.toRat q : ℚ) : ℝ) = n := by
  have hval := toRat_eq_of_int_den_one q hs hI
  refine ⟨q.num.toNat, ?_, hval⟩
  rw [not_or] at h12
  obtain ⟨hn1, hn2⟩ := h12
  have e1 : q.num.toNat ≠ 1 := fun h => hn1 ((AzRat.toRat_eq_zero_iff (q - 1)).mp (by
    rw [AzRat.toRat_sub, AzRat.toRat_one]
    push_cast
    rw [hval, h]
    norm_num))
  have e2 : q.num.toNat ≠ 2 := fun h => hn2 ((AzRat.toRat_eq_zero_iff (q - 1 - 1)).mp (by
    rw [AzRat.toRat_sub, AzRat.toRat_sub, AzRat.toRat_one]
    push_cast
    rw [hval, h]
    norm_num))
  have e0 : q.num.toNat ≠ 0 := fun h =>
    h0 (AzNat.toNat_injective (by rw [h, AzNat.toNat_zero]))
  omega

/-- **The Ziv certificate of `ln Γ(n)` at an integer rational `n ≥ 3`.** -/
theorem lnGammaRatApprox_cert_int {q : AzRat} (h0 : q.num ≠ 0) (hs : q.sign = true)
    (h12 : ¬ ((q - 1).num = 0 ∨ (q - 1 - 1).num = 0)) (hI : q.den = 1) (p : ℕ) [NeZero p]
    (mode : RoundingMode) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (lnGammaRatApprox q (w₀ * 2 ^ f)).1
      (lnGammaRatApprox q (w₀ * 2 ^ f)).2 p mode).isSome = true := by
  obtain ⟨n, hn, hval⟩ := lnGammaRatInt_spec h0 hs h12 hI
  have hirr := irrational_log_gamma_nat hn
  rw [← hval] at hirr
  exact (lnGammaRatApprox_bracketConv q (by rw [hval]; positivity)).exists_isSome hirr.ne_zero p
    (not_mem_floatSet_of_irrational p hirr) mode w₀ hw₀

end Azurite.AzFloat
