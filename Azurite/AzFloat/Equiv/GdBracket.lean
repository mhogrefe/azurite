/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.GdBracket
import Azurite.AzFloat.Equiv.AtanRatBracket
import Azurite.AzFloat.Equiv.TanhBracket
import Azurite.Transcendental.Catalan
import Azurite.Transcendental.Gudermannian

/-!
# Equivalence: the bracket of the Gudermannian

* The identities `gd a = 2 arctan (tanh (a/2))` (`gd_eq_two_arctan_tanh`) and
  `gd a = π/2 − 2 arctan (e^(−a))` (`gd_eq_pi_div_two_sub`), oddness, and the bounds
  `a − a³ ≤ gd a < a` for the tiny-argument path.
* The alternating series of the arctangent: `arctan z = ∑_{k<n} (−1)^k z^(2k+1)/(2k+1) +
  (−1)^n ∫₀^z t^(2n)/(1 + t²) dt` (`arctan_eq_altSum_add`), so the partial sums and the next
  term enclose it (`arctan_altSum_bounds`); hence `atanAltLoop_spec`, `atanAlt_spec`: the loop
  encloses `arctan z` for every fuel and threshold.
* `enclNarrow?_spec` turns the measured width into a bound, so the series paths
  (`gdSmallSeries?_spec`, `gdLargeSeries?_spec`) come with width `2^(−w)` without any analysis
  of their convergence; `gdHuge_spec`; `gdCore_spec` through `atanWiden_spec_of_le_one` (the
  widening without an a priori bound on the width of the argument).
* `gdBracket_spec` (width `gdEps`, tending to `0`), `gdApprox_spec`,
  `gdApprox_isSome_exists` (the Ziv certificate, from `irrational_gd_rat`) and `gdTiny?_eq`.
-/

open Real

namespace Azurite.AzFloat

open Azurite.DLMF (gd)

/-! ### Identities and bounds -/

/-- `gd a = 2 arctan (tanh (a/2))`. -/
theorem gd_eq_two_arctan_tanh (a : ℝ) : gd a = 2 * arctan (Real.tanh (a / 2)) := by
  have he := exp_pos a
  have h := arctan_add (x := Real.exp a) (y := -1) (by linarith)
  rw [arctan_neg, arctan_one] at h
  have ht : Real.tanh (a / 2) = (Real.exp a + -1) / (1 - Real.exp a * -1) := by
    rw [tanh_eq_expm1, show 2 * (a / 2) = a by ring]
    ring
  rw [DLMF.gd_eq_arctan, ht, ← h]
  ring

/-- `gd a = π/2 − 2 arctan (e^(−a))`. -/
theorem gd_eq_pi_div_two_sub (a : ℝ) : gd a = π / 2 - 2 * arctan (Real.exp (-a)) := by
  rw [DLMF.gd_eq_arctan, exp_neg, arctan_inv_of_pos (exp_pos a)]
  ring

theorem gd_neg (a : ℝ) : gd (-a) = -gd a := by
  rw [gd_eq_two_arctan_tanh, gd_eq_two_arctan_tanh, neg_div, Real.tanh_neg, arctan_neg]
  ring

theorem gd_zero : gd 0 = 0 := by
  rw [gd_eq_two_arctan_tanh]
  simp

theorem gd_lt_self {a : ℝ} (ha : 0 < a) : gd a < a := by
  have h2 : 0 < a / 2 := by positivity
  have ht := tanh_lt_self h2
  have ht0 : 0 < Real.tanh (a / 2) := by
    rw [tanh_eq_sinh_div_cosh]
    exact div_pos (sinh_pos_iff.mpr h2) (cosh_pos _)
  have := arctan_lt_self ht0
  rw [gd_eq_two_arctan_tanh]
  linarith

theorem sub_cube_le_gd {a : ℝ} (ha : 0 < a) : a - a ^ 3 ≤ gd a := by
  have h2 : 0 < a / 2 := by positivity
  have ht0 : 0 < Real.tanh (a / 2) := by
    rw [tanh_eq_sinh_div_cosh]
    exact div_pos (sinh_pos_iff.mpr h2) (cosh_pos _)
  have ht1 := sub_cube_le_tanh h2
  have ht2 := tanh_lt_self h2
  have h3 := sub_cube_div_three_le_arctan ht0.le
  have hcube : Real.tanh (a / 2) ^ 3 ≤ (a / 2) ^ 3 := pow_le_pow_left₀ ht0.le ht2.le 3
  have ha3 : 0 < a ^ 3 := by positivity
  rw [gd_eq_two_arctan_tanh]
  nlinarith

theorem gd_pos {a : ℝ} (ha : 0 < a) : 0 < gd a := by
  have h2 : 0 < a / 2 := by positivity
  have ht0 : 0 < Real.tanh (a / 2) := by
    rw [tanh_eq_sinh_div_cosh]
    exact div_pos (sinh_pos_iff.mpr h2) (cosh_pos _)
  rw [gd_eq_two_arctan_tanh]
  have := arctan_pos.mpr ht0
  linarith

/-- `e^(−a) ≤ 2^(−N)` for a natural `N ≤ a`. -/
theorem exp_neg_le_half_pow {a : ℝ} {N : ℕ} (hN : (N : ℝ) ≤ a) :
    Real.exp (-a) ≤ (1 / 2 : ℝ) ^ N := by
  have h1 : Real.exp (-a) ≤ Real.exp (-(N : ℝ)) := exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (-(N : ℝ)) = Real.exp (-1) ^ N := by
    rw [← exp_nat_mul]; congr 1; ring
  have h3 : Real.exp (-1) ≤ 1 / 2 := by
    rw [exp_neg, one_div]
    exact inv_anti₀ (by norm_num) (by linarith [add_one_le_exp (1 : ℝ)])
  rw [h2] at h1
  exact h1.trans (pow_le_pow_left₀ (exp_pos _).le h3 N)

/-! ### The alternating series of the arctangent -/

/-- The sum of the first `n` terms of `z − z³/3 + z⁵/5 − ⋯`. -/
noncomputable def atanAltSum (n : ℕ) (z : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, (-1) ^ k * (z ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ))

theorem atanAltSum_succ (n : ℕ) (z : ℝ) :
    atanAltSum (n + 1) z
      = atanAltSum n z + (-1) ^ n * (z ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)) := by
  unfold atanAltSum
  rw [Finset.sum_range_succ]

/-- `arctan z = ∑_{k<n} (−1)^k z^(2k+1)/(2k+1) + (−1)^n ∫₀^z t^(2n)/(1 + t²) dt`. -/
theorem arctan_eq_altSum_add (z : ℝ) (n : ℕ) :
    arctan z = atanAltSum n z + (-1) ^ n * ∫ t in (0 : ℝ)..z, t ^ (2 * n) / (1 + t ^ 2) := by
  have h1 : ∫ t in (0 : ℝ)..z, 1 / (1 + t ^ 2) = arctan z := by
    rw [integral_one_div_one_add_sq, arctan_zero, sub_zero]
  have hr : Continuous fun t : ℝ => t ^ (2 * n) / (1 + t ^ 2) :=
    (continuous_pow _).div (by fun_prop) fun t => by positivity
  have hs : Continuous fun t : ℝ => ∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * t ^ (2 * k) := by
    fun_prop
  rw [← h1, intervalIntegral.integral_congr (g := fun t =>
      ∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * t ^ (2 * k) + (-1) ^ n * (t ^ (2 * n) / (1 + t ^ 2)))
      (fun t _ => inv_one_add_sq_eq_sum t n),
    intervalIntegral.integral_add
      (f := fun t => ∑ k ∈ Finset.range n, (-1 : ℝ) ^ k * t ^ (2 * k))
      (g := fun t => (-1 : ℝ) ^ n * (t ^ (2 * n) / (1 + t ^ 2)))
      (hs.intervalIntegrable _ _) ((continuous_const.mul hr).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum
      (f := fun k t => (-1 : ℝ) ^ k * t ^ (2 * k))
      (fun k _ => ((continuous_const.mul (continuous_pow _)).intervalIntegrable _ _))]
  congr 1
  unfold atanAltSum
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [intervalIntegral.integral_const_mul, integral_pow]
  push_cast
  simp

/-- The remainder integral lies in `[0, z^(2n+1)/(2n+1)]` for `z ≥ 0`. -/
theorem atanAlt_remainder_bounds {z : ℝ} (hz : 0 ≤ z) (n : ℕ) :
    0 ≤ ∫ t in (0 : ℝ)..z, t ^ (2 * n) / (1 + t ^ 2) ∧
      ∫ t in (0 : ℝ)..z, t ^ (2 * n) / (1 + t ^ 2) ≤ z ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ) := by
  have hr : Continuous fun t : ℝ => t ^ (2 * n) / (1 + t ^ 2) :=
    (continuous_pow _).div (by fun_prop) fun t => by positivity
  refine ⟨intervalIntegral.integral_nonneg hz fun t _ =>
    div_nonneg (by rw [pow_mul]; positivity) (by positivity), ?_⟩
  have hp : ∫ t in (0 : ℝ)..z, t ^ (2 * n) = z ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ) := by
    rw [integral_pow]
    push_cast
    simp
  rw [← hp]
  refine intervalIntegral.integral_mono_on hz (hr.intervalIntegrable _ _)
    ((continuous_pow _).intervalIntegrable _ _) fun t _ => ?_
  have h1 : (1 : ℝ) ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg t]
  have h0 : 0 ≤ t ^ (2 * n) := by
    rw [pow_mul]
    positivity
  exact div_le_self h0 h1

/-- **The partial sums of the alternating series enclose the arctangent**: from below after
an even number of terms, from above after an odd number, within the next term. -/
theorem arctan_altSum_bounds {z : ℝ} (hz : 0 ≤ z) (n : ℕ) :
    (n % 2 = 0 → atanAltSum n z ≤ arctan z ∧
      arctan z ≤ atanAltSum n z + z ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)) ∧
    (n % 2 ≠ 0 → atanAltSum n z - z ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ) ≤ arctan z ∧
      arctan z ≤ atanAltSum n z) := by
  obtain ⟨h0, h1⟩ := atanAlt_remainder_bounds hz n
  have h := arctan_eq_altSum_add z n
  refine ⟨fun hn => ?_, fun hn => ?_⟩
  · rw [(Nat.even_iff.mpr hn).neg_one_pow, one_mul] at h
    constructor <;> linarith
  · rw [(Nat.odd_iff.mpr (Nat.mod_two_ne_zero.mp hn)).neg_one_pow] at h
    constructor <;> linarith

/-- The end of the loop encloses the arctangent. -/
theorem atanAltClose_spec {V : ℕ} [NeZero V] {z : ℝ} (hz : 0 ≤ z) {k : ℕ} {acc term : Encl}
    (hacc : IsEncl acc (atanAltSum k z))
    (hterm : IsEncl0 term (z ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ))) :
    IsEncl (atanAltClose V k acc term) (arctan z) := by
  obtain ⟨al, ah, hal, hah, ha1, ha2⟩ := hacc
  obtain ⟨tl, th, htl, hth, -, -, ht2⟩ := hterm
  obtain ⟨he, ho⟩ := arctan_altSum_bounds hz k
  unfold atanAltClose
  split_ifs with hk
  · obtain ⟨r, hr, hr1⟩ := addCeiling_ge hah hth V
    obtain ⟨h1, h2⟩ := he hk
    exact ⟨al, r, hal, hr, by linarith, by linarith⟩
  · obtain ⟨r, hr, hr1, -⟩ := subFloor_le hal hth V
    obtain ⟨h1, h2⟩ := ho hk
    exact ⟨r, ah, hr, hah, by linarith, by linarith⟩

/-- **The alternating-series loop encloses `arctan z`**, for every fuel and threshold. -/
theorem atanAltLoop_spec {V : ℕ} [NeZero V] {z : ℝ} (hz : 0 ≤ z) {z2 : Encl}
    (hz2 : IsEncl0 z2 (z ^ 2)) (tau : AzFloat) (fuel : ℕ) :
    ∀ (k : ℕ) (p acc : Encl), IsEncl0 p (z ^ (2 * k + 1)) → IsEncl acc (atanAltSum k z) →
      IsEncl (atanAltLoop V z2 tau fuel k p acc) (arctan z) := by
  induction fuel with
  | zero =>
    intro k p acc hp hacc
    exact atanAltClose_spec hz hacc (hp.div (enclosesPos_nat (by omega)))
  | succ fuel ih =>
    intro k p acc hp hacc
    have hterm : IsEncl0 (Encl.div V p (Encl.nat (2 * k + 1)))
        (z ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ)) := hp.div (enclosesPos_nat (by omega))
    unfold atanAltLoop
    split_ifs with hstop hk
    · exact atanAltClose_spec hz hacc hterm
    · refine ih (k + 1) _ _ ?_ ?_
      · have := hp.mul (w := V) hz2
        rwa [show z ^ (2 * k + 1) * z ^ 2 = z ^ (2 * (k + 1) + 1) by ring] at this
      · rw [atanAltSum_succ, (Nat.even_iff.mpr hk).neg_one_pow, one_mul]
        exact hacc.add hterm.encloses
    · refine ih (k + 1) _ _ ?_ ?_
      · have := hp.mul (w := V) hz2
        rwa [show z ^ (2 * k + 1) * z ^ 2 = z ^ (2 * (k + 1) + 1) by ring] at this
      · rw [atanAltSum_succ, (Nat.odd_iff.mpr (Nat.mod_two_ne_zero.mp hk)).neg_one_pow,
          neg_one_mul, ← sub_eq_add_neg]
        exact hacc.sub hterm.encloses

/-- **`atanAlt` encloses `arctan z`** for an enclosure of `z ≥ 0`. -/
theorem atanAlt_spec {zE : Encl} {z : ℝ} (hzE : IsEncl zE z) (hz : 0 ≤ z) (K : ℕ) {V : ℕ}
    [NeZero V] (fuel : ℕ) : IsEncl (atanAlt zE K V fuel) (arctan z) := by
  obtain ⟨l, h, hl, hh, h1, h2⟩ := hzE
  obtain ⟨c, hc, hc0, hcle, -⟩ := clampNonneg_spec hl
  have hzz : IsEncl0 (clampNonneg zE.1, zE.2) z :=
    ⟨c, h, hc, hh, hc0, hcle.trans (max_le h1 hz), h2⟩
  unfold atanAlt
  refine atanAltLoop_spec hz ?_ _ _ 0 _ _ ?_ ?_
  · have := hzz.mul (w := V) hzz
    rwa [← sq] at this
  · simpa using hzz
  · exact ⟨0, 0, toVal_zero, toVal_zero, by simp [atanAltSum], by simp [atanAltSum]⟩

/-! ### Small tools -/

/-- A measured width: an enclosure accepted by `enclNarrow?` has width at most `2^(−j)`. -/
theorem enclNarrow?_spec {b r : Encl} {j : Int} {lo hi : ℝ} (h : enclNarrow? b j = some r)
    (hlo : b.1.toVal = some (lo : EReal)) (hhi : b.2.toVal = some (hi : EReal)) :
    r = b ∧ hi - lo ≤ (2 : ℝ) ^ (-j) := by
  unfold enclNarrow? at h
  split_ifs at h with hle
  rw [Option.some.injEq] at h
  obtain ⟨wv, hwv, hwge, -⟩ := subCeiling_abs hhi hlo 64
  have hc := toVal_shiftLeft_of_toVal toVal_one' (AzInt.ofInt (-j))
  rw [AzInt.toInt_ofInt, one_mul] at hc
  have := (le_eq_true_iff hwv hc).mp hle
  exact ⟨h.symm, by linarith⟩

theorem two_zpow_neg_sub_le {K w : ℕ} (h : w + 8 ≤ K) :
    (2 : ℝ) ^ (-((K : ℤ) - 8)) ≤ (1 / 2 : ℝ) ^ w := by
  have e : ((K - 8 : ℕ) : ℤ) = (K : ℤ) - 8 := by omega
  rw [← e, zpow_neg, zpow_natCast, ← one_div, ← one_div_pow]
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

/-- Doubling an enclosure. -/
theorem isEncl_double {A : Encl} {v : ℝ} (h : IsEncl A v) :
    IsEncl (A.1 <<< AzInt.ofInt 1, A.2 <<< AzInt.ofInt 1) (2 * v) := by
  obtain ⟨l, u, hl, hu, h1, h2⟩ := h
  have e1 := toVal_shiftLeft_of_toVal hl (AzInt.ofInt 1)
  have e2 := toVal_shiftLeft_of_toVal hu (AzInt.ofInt 1)
  rw [AzInt.toInt_ofInt, zpow_one] at e1 e2
  exact ⟨l * 2, u * 2, e1, e2, by linarith, by linarith⟩

/-- Halving a float. -/
theorem toVal_shiftLeft_neg_one {a : AzFloat} {av : ℝ} (ha : a.toVal = some (av : EReal)) :
    (a <<< AzInt.ofInt (-1)).toVal = some ((av / 2 : ℝ) : EReal) := by
  have h := toVal_shiftLeft_of_toVal ha (AzInt.ofInt (-1))
  rw [AzInt.toInt_ofInt, zpow_neg_one, ← div_eq_mul_inv] at h
  exact h

/-- The enclosure of `tanh (a/2)` used by the series path and by the general path. -/
theorem tanhHalf_spec {a : AzFloat} {av : ℝ} (ha : a.toVal = some (av : EReal)) (ha0 : 0 < av)
    (e : AzInt) (hae : av < (2 : ℝ) ^ e.toInt) {w : ℕ} (hw : 64 ≤ w) :
    IsEnclW (tanhBracket (a <<< AzInt.ofInt (-1)) (e + AzInt.ofInt (-1)) w)
      (Real.tanh (av / 2))
      (tanhWidth (expM1Eps (2 * (av / 2))
        (expM1Comp (e + AzInt.ofInt (-1) + AzInt.ofInt 1)) w) w) := by
  have hpos : 0 < av / 2 := by positivity
  have hlt : av / 2 < (2 : ℝ) ^ (e + AzInt.ofInt (-1)).toInt := by
    rw [AzInt.toInt_add, AzInt.toInt_ofInt, zpow_add₀ (by norm_num), zpow_neg_one]
    linarith
  exact tanhBracket_spec (toVal_shiftLeft_neg_one ha) hpos (e + AzInt.ofInt (-1)) hlt hw

theorem tanh_half_nonneg {av : ℝ} (ha0 : 0 < av) : 0 ≤ Real.tanh (av / 2) := by
  rw [tanh_eq_sinh_div_cosh]
  exact div_nonneg (sinh_nonneg_iff.mpr (by positivity)) (cosh_pos _).le

/-! ### The series paths -/

/-- The series step for a small argument, when it answers, encloses `gd a` with width at most
`2^(−w)` (`w + 8 ≤ K`). -/
theorem gdSmallOf_spec {t : Encl} {av : ℝ} (ht : IsEncl t (Real.tanh (av / 2))) (ha0 : 0 < av)
    {K w : ℕ} (hKw : w + 8 ≤ K) {b : Encl} (h : gdSmallOf t K = some b) :
    IsEnclW b (gd av) ((1 / 2 : ℝ) ^ w) := by
  unfold gdSmallOf at h
  dsimp only at h
  have : NeZero (K + 32) := ⟨by omega⟩
  have hA := atanAlt_spec ht (tanh_half_nonneg ha0) K (V := K + 32) gdSeriesTerms
  have hD := isEncl_double hA
  rw [← gd_eq_two_arctan_tanh] at hD
  obtain ⟨lo, hi, hlo, hhi, h1, h2⟩ := hD
  obtain ⟨rfl, hwd⟩ := enclNarrow?_spec h hlo hhi
  exact ⟨lo, hi, hlo, hhi, h1, h2, hwd.trans (two_zpow_neg_sub_le hKw)⟩

/-- The series step for a large argument, when it answers, encloses `gd a` with width at most
`2^(−w)`. -/
theorem gdLargeOf_spec {z : Encl} {av : ℝ} (hz : IsEncl z (Real.exp (-av))) {w : ℕ} {b : Encl}
    (h : gdLargeOf z w = some b) : IsEnclW b (gd av) ((1 / 2 : ℝ) ^ w) := by
  unfold gdLargeOf at h
  dsimp only at h
  have : NeZero (w + 8 + 56) := ⟨by omega⟩
  obtain ⟨al, ah, hal, hah, a1, a2⟩ := atanAlt_spec hz
    (exp_pos (-av)).le (w + 8) (V := w + 8 + 56) gdSeriesTerms
  obtain ⟨pl, ph, hpl, hph, -, p1, p2, -⟩ := piBracket_spec (w := w + 8 + 56) (by omega)
  have hal2 := toVal_shiftLeft_of_toVal hal (AzInt.ofInt 1)
  have hah2 := toVal_shiftLeft_of_toVal hah (AzInt.ofInt 1)
  rw [AzInt.toInt_ofInt, zpow_one] at hal2 hah2
  obtain ⟨r, hr, hr1, -⟩ := subFloor_le (toVal_shiftLeft_neg_one hpl) hah2 (w + 8 + 56)
  obtain ⟨s, hs, hs1⟩ := subCeiling_ge (toVal_shiftLeft_neg_one hph) hal2 (w + 8 + 56)
  obtain ⟨rfl, hwd⟩ := enclNarrow?_spec h hr hs
  refine ⟨r, s, hr, hs, ?_, ?_, hwd.trans (two_zpow_neg_sub_le (K := w + 8) le_rfl)⟩
  · rw [gd_eq_pi_div_two_sub]
    linarith
  · rw [gd_eq_pi_div_two_sub]
    linarith

/-- The series path for a small float argument. -/
theorem gdSmallSeries?_spec {a : AzFloat} {av : ℝ} (ha : a.toVal = some (av : EReal))
    (ha0 : 0 < av) (e : AzInt) (hae : av < (2 : ℝ) ^ e.toInt) {w : ℕ} {b : Encl}
    (h : gdSmallSeries? a e w = some b) : IsEnclW b (gd av) ((1 / 2 : ℝ) ^ w) := by
  unfold gdSmallSeries? at h
  dsimp only at h
  split_ifs at h with hgate
  obtain ⟨tl, th, htl, hth, t1, t2, -⟩ := tanhHalf_spec ha ha0 e hae (w := w + 64) (by omega)
  exact gdSmallOf_spec ⟨tl, th, htl, hth, t1, t2⟩ ha0 (by unfold atanWork; omega) h

/-- The series path for a large float argument. -/
theorem gdLargeSeries?_spec {a : AzFloat} {av : ℝ} (ha : a.toVal = some (av : EReal))
    (ha0 : 0 < av) (e : AzInt) (hae : av < (2 : ℝ) ^ e.toInt) {w : ℕ} {b : Encl}
    (h : gdLargeSeries? a e w = some b) : IsEnclW b (gd av) ((1 / 2 : ℝ) ^ w) := by
  unfold gdLargeSeries? at h
  dsimp only at h
  split_ifs at h with hgate
  have hneg : (-a).toVal = some ((-av : ℝ) : EReal) := by
    rw [toVal_neg, ha, Option.map_some, EReal.coe_neg]
  obtain ⟨zl, zh, hzl, hzh, z1, z2, -⟩ := expBracket_spec hneg e
    (by rw [abs_neg, abs_of_pos ha0]; exact hae)
    (w := max 64 (w + 8 + 24 - (truncToAzInt a).abs.toNat)) (le_max_left _ _)
  exact gdLargeOf_spec ⟨zl, zh, hzl, hzh, z1, z2⟩ h

/-! ### Huge arguments -/

/-- **`gdHuge N w` encloses `gd a`** for `a ≥ N ≥ w + 8`: width at most
`piEps (w + 72) + 2·2^(−w)`. -/
theorem gdHuge_spec {av : ℝ} {N w : ℕ} (hN : (N : ℝ) ≤ av) (hNw : w + 8 ≤ N) :
    IsEnclW (gdHuge N w) (gd av) (piEps (w + 72) + 2 * (1 / 2 : ℝ) ^ w) := by
  unfold gdHuge
  dsimp only
  have : NeZero (w + 72) := ⟨by omega⟩
  obtain ⟨pl, ph, hpl, hph, p0, p1, p2, pw⟩ := piBracket_spec (w := w + 72) (by omega)
  have hc := toVal_shiftLeft_of_toVal toVal_one' (AzInt.ofInt (1 - (N : Int)))
  rw [AzInt.toInt_ofInt, one_mul] at hc
  set u := (1 / 2 : ℝ) ^ w with hu
  have hu0 : 0 < u := by positivity
  have hcv : (2 : ℝ) ^ ((1 : ℤ) - N) = 2 * (1 / 2 : ℝ) ^ N := by
    rw [zpow_sub₀ (by norm_num), zpow_one, zpow_natCast, one_div_pow]
    ring
  rw [hcv] at hc
  have hNu : (1 / 2 : ℝ) ^ N ≤ u / 256 := by
    calc (1 / 2 : ℝ) ^ N ≤ (1 / 2 : ℝ) ^ (w + 8) :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hNw
      _ = u / 256 := by rw [pow_add, hu]; norm_num; ring
  have hN0 : (0 : ℝ) < (1 / 2 : ℝ) ^ N := by positivity
  obtain ⟨r, hr, hr1, hr2⟩ := subFloor_abs (toVal_shiftLeft_neg_one hpl) hc (w + 72)
  have hz := exp_neg_le_half_pow hN
  have hat := arctan_le_self (exp_pos (-av)).le
  have hat0 := arctan_pos.mpr (exp_pos (-av))
  have hV : (1 / 2 : ℝ) ^ (w + 72) ≤ u / 256 := by
    rw [pow_add, ← hu]
    have : (1 / 2 : ℝ) ^ 72 ≤ 1 / 256 := by norm_num
    nlinarith
  have hpi4 := pi_le_four
  have hu1 : u ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have habs : |pl / 2 - 2 * (1 / 2 : ℝ) ^ N| ≤ 2 := by
    rw [abs_le]
    constructor <;> linarith
  have m1 := mul_le_mul_of_nonneg_right habs (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (w + 72))
  refine ⟨r, ph / 2, hr, toVal_shiftLeft_neg_one hph, ?_, ?_, ?_⟩
  · rw [gd_eq_pi_div_two_sub]
    linarith
  · rw [gd_eq_pi_div_two_sub]
    linarith
  · linarith

/-! ### The general path -/

/-- **The widening without an a priori width**: for floats `0 ≤ r_lo ≤ t ≤ r_hi ≤ 1`,
`atanWiden` encloses `arctan t` with width at most
`(3/4) 2^(−K) + 2 (r_hi − r_lo) + 14·2^(−K−64)`. -/
theorem atanWiden_spec_of_le_one {rl rh : AzFloat} {rlv rhv t : ℝ}
    (hrl : rl.toVal = some (rlv : EReal)) (hrh : rh.toVal = some (rhv : EReal)) (h0 : 0 ≤ rlv)
    (h1 : rlv ≤ t) (h2 : t ≤ rhv) (h3 : rhv ≤ 1) (K : ℕ) :
    ∃ lo hi : ℝ, (atanWiden rl rh K (K + 64)).1.toVal = some (lo : EReal) ∧
      (atanWiden rl rh K (K + 64)).2.toVal = some (hi : EReal) ∧ lo ≤ arctan t ∧
      arctan t ≤ hi ∧
      hi - lo ≤ 3 / 4 * (1 / 2 : ℝ) ^ K + 2 * (rhv - rlv) + 14 * (1 / 2 : ℝ) ^ (K + 64) := by
  unfold atanWiden
  dsimp only
  have : NeZero (K + 64) := ⟨by omega⟩
  set u := (1 / 2 : ℝ) ^ (K + 64) with hu
  have hu0 : 0 ≤ u := by positivity
  have hK1 : (1 / 2 : ℝ) ^ K ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hK0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ K := by positivity
  obtain ⟨lb, hb, hlb, hhb, hb0, hb1, hb2, hbw⟩ :=
    atanLoop_spec hrl h0 (h1.trans (h2.trans h3)) K K
  have hbw' := hbw (by omega)
  obtain ⟨dv, hdv, hdv1, hdv2⟩ := subCeiling_abs hrh hrl 64
  obtain ⟨up, hup, hup1, hup2⟩ := addCeiling_abs hhb hdv (K + 64)
  rw [← hu] at hup2
  have hlip := arctan_sub_arctan_le h1
  have hrr : arctan rlv ≤ arctan t := arctan_strictMono.monotone h1
  have hat1 : arctan rlv ≤ 1 := (arctan_le_self h0).trans (h1.trans (h2.trans h3))
  have hdr0 : 0 ≤ rhv - rlv := by linarith
  have hdr1 : rhv - rlv ≤ 1 := by linarith
  have hdv3 : dv ≤ (rhv - rlv) + (rhv - rlv) / 2 := by
    have h64 : (1 / 2 : ℝ) ^ 64 ≤ 1 / 4 := by norm_num
    rw [abs_of_nonneg hdr0] at hdv2
    have := mul_le_mul_of_nonneg_left h64 hdr0
    linarith
  have habs1 : |hb + dv| ≤ 4 := by
    rw [abs_le]
    constructor <;> linarith
  have m1 := mul_le_mul_of_nonneg_right habs1 hu0
  exact ⟨lb, up, hlb, hup, hb1.trans hrr, by linarith, by linarith⟩

/-- **The general step**: from an enclosure of `tanh (a/2)` of width at most `TW`, at a level
`K ≥ w + 8`, `gdCoreOf` encloses `gd a` with width at most `2·2^(−w) + 4 TW`. -/
theorem gdCoreOf_spec {t : Encl} {av TW : ℝ} (ht : IsEnclW t (Real.tanh (av / 2)) TW)
    (ha0 : 0 < av) {K w : ℕ} (hKw : w + 8 ≤ K) :
    IsEnclW (gdCoreOf t K) (gd av) (2 * (1 / 2 : ℝ) ^ w + 4 * TW) := by
  unfold gdCoreOf
  dsimp only
  obtain ⟨tl, th, htl, hth, t1, t2, tw⟩ := ht
  have hT0 := tanh_half_nonneg ha0
  have hT1 := (Real.tanh_lt_one (av / 2)).le
  obtain ⟨c, hc, hc0, hcle, hceq⟩ := clampNonneg_spec htl
  have hcT : c ≤ Real.tanh (av / 2) := hcle.trans (max_le t1 hT0)
  have htc : tl ≤ c := by
    rcases le_or_gt 0 tl with h | h
    · rw [hceq h]
    · linarith
  have hm := toVal_minOf hth toVal_one'
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := atanWiden_spec_of_le_one hc hm hc0 hcT
    (le_min t2 hT1) (min_le_right _ _) K
  have hmin : min th 1 ≤ th := min_le_left _ _
  have e1 := toVal_shiftLeft_of_toVal hlo (AzInt.ofInt 1)
  have e2 := toVal_shiftLeft_of_toVal hhi (AzInt.ofInt 1)
  rw [AzInt.toInt_ofInt, zpow_one] at e1 e2
  have hKle : (1 / 2 : ℝ) ^ K ≤ (1 / 2 : ℝ) ^ w / 256 := by
    calc (1 / 2 : ℝ) ^ K ≤ (1 / 2 : ℝ) ^ (w + 8) :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hKw
      _ = (1 / 2 : ℝ) ^ w / 256 := by rw [pow_add]; norm_num; ring
  have hK64 : (1 / 2 : ℝ) ^ (K + 64) ≤ (1 / 2 : ℝ) ^ K := by
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hw0 : (0 : ℝ) < (1 / 2 : ℝ) ^ w := by positivity
  have hK0 : (0 : ℝ) < (1 / 2 : ℝ) ^ K := by positivity
  refine ⟨lo * 2, hi * 2, e1, e2, ?_, ?_, ?_⟩
  · rw [gd_eq_two_arctan_tanh]
    linarith
  · rw [gd_eq_two_arctan_tanh]
    linarith
  · linarith

/-- The width bound of `gdCore`. -/
noncomputable def gdCoreEps (av : ℝ) (e : AzInt) (w : ℕ) : ℝ :=
  2 * (1 / 2 : ℝ) ^ w + 4 * tanhWidth (expM1Eps (2 * (av / 2))
    (expM1Comp (e + AzInt.ofInt (-1) + AzInt.ofInt 1)) (w + 96)) (w + 96)

/-- **`gdCore` encloses `gd a`** for a float `0 < a < 2^e`. -/
theorem gdCore_spec {a : AzFloat} {av : ℝ} (ha : a.toVal = some (av : EReal)) (ha0 : 0 < av)
    (e : AzInt) (hae : av < (2 : ℝ) ^ e.toInt) (w : ℕ) :
    IsEnclW (gdCore a e w) (gd av) (gdCoreEps av e w) :=
  gdCoreOf_spec (tanhHalf_spec ha ha0 e hae (w := w + 96) (by omega)) ha0
    (by unfold atanWork; omega)

/-! ### The bracket -/

/-- The width bound of `gdBracket`. -/
noncomputable def gdEps (av : ℝ) (e : AzInt) (w : ℕ) : ℝ :=
  piEps (w + 72) + 2 * (1 / 2 : ℝ) ^ w + gdCoreEps av e w

theorem tendsto_gdEps (av : ℝ) (e : AzInt) :
    Filter.Tendsto (gdEps av e) Filter.atTop (nhds 0) := by
  have h1 := tendsto_piEps.comp (Filter.tendsto_add_atTop_nat 72)
  have h2 := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).const_mul 2
  have h3 := ((tendsto_tanhWidth (tendsto_expM1Eps (2 * (av / 2))
    (expM1Comp (e + AzInt.ofInt (-1) + AzInt.ofInt 1)))).comp
    (Filter.tendsto_add_atTop_nat 96)).const_mul 4
  have := (h1.add h2).add (h2.add h3)
  simp only [mul_zero, add_zero] at this
  exact this

theorem gdCoreEps_nonneg {av : ℝ} (ha0 : 0 < av) (e : AzInt) (w : ℕ) :
    0 ≤ gdCoreEps av e w := by
  unfold gdCoreEps tanhWidth expM1Eps
  positivity

/-- **`gdBracket a e w` encloses `gd a`** for a float `2^(e−1) ≤ a < 2^e`, with width at most
`gdEps a e w`. -/
theorem gdBracket_spec {a : AzFloat} {av : ℝ} (ha : a.toVal = some (av : EReal)) (ha0 : 0 < av)
    (e : AzInt) (hlo : (2 : ℝ) ^ (e.toInt - 1) ≤ av) (hae : av < (2 : ℝ) ^ e.toInt) (w : ℕ) :
    IsEnclW (gdBracket a e w) (gd av) (gdEps av e w) := by
  have hpi : 0 ≤ piEps (w + 72) := by unfold piEps; positivity
  have hw0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
  have hcore := gdCoreEps_nonneg ha0 e w
  unfold gdBracket gdEps
  split_ifs with hH hE
  · obtain ⟨lo, hi, h1, h2, h3, h4, h5⟩ := gdHuge_spec
      (floatAbsFloorN_le (xv := av) (by rw [abs_of_pos ha0]; exact hlo) |>.trans_eq
        (abs_of_pos ha0)) hH
    exact ⟨lo, hi, h1, h2, h3, h4, by linarith⟩
  · split
    · next b hb =>
      obtain ⟨lo, hi, h1, h2, h3, h4, h5⟩ := gdLargeSeries?_spec ha ha0 e hae hb
      exact ⟨lo, hi, h1, h2, h3, h4, by linarith⟩
    · obtain ⟨lo, hi, h1, h2, h3, h4, h5⟩ := gdCore_spec ha ha0 e hae w
      exact ⟨lo, hi, h1, h2, h3, h4, by linarith⟩
  · split
    · next b hb =>
      obtain ⟨lo, hi, h1, h2, h3, h4, h5⟩ := gdSmallSeries?_spec ha ha0 e hae hb
      exact ⟨lo, hi, h1, h2, h3, h4, by linarith⟩
    · obtain ⟨lo, hi, h1, h2, h3, h4, h5⟩ := gdCore_spec ha ha0 e hae w
      exact ⟨lo, hi, h1, h2, h3, h4, by linarith⟩

/-- `gd x = ± gd |x|` with the sign bit of `x`. -/
theorem gd_eq_of_neg_iff {neg : Bool} {xv : ℝ} (hneg : neg = true ↔ xv < 0) :
    gd xv = (if neg then -1 else 1) * gd |xv| := by
  cases neg with
  | true =>
    have h := hneg.mp rfl
    simp only [↓reduceIte]
    rw [abs_of_neg h, gd_neg]
    ring
  | false =>
    have h : 0 ≤ xv := not_lt.mp fun h => by simpa using hneg.mpr h
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    rw [abs_of_nonneg h]

/-- `gdApprox neg` as a pair of `Roundable`s bracketing `± gd |x|`. -/
theorem gdApprox_spec (neg : Bool) {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx0 : xv ≠ 0) (e : AzInt) (hlo : (2 : ℝ) ^ (e.toInt - 1) ≤ |xv|)
    (hxe : |xv| < (2 : ℝ) ^ e.toInt) (w : ℕ) :
    ∃ lv hv : ℝ, Rounds (gdApprox neg x e w).1 lv ∧ Rounds (gdApprox neg x e w).2 hv ∧
      lv ≤ (if neg then -1 else 1) * gd |xv| ∧
      (if neg then -1 else 1) * gd |xv| ≤ hv ∧ hv - lv ≤ gdEps |xv| e w := by
  have habs : x.abs.toVal = some ((|xv| : ℝ) : EReal) := by
    rw [toVal_abs, hx, Option.map_some, ← EReal.coe_neg]
    congr 1
  obtain ⟨lo, hi, hlo', hhi, h1, h2, hwid⟩ :=
    gdBracket_spec habs (abs_pos.mpr hx0) e hlo hxe w
  obtain ⟨lv, hv, hR1, hR2, hl, hh, he⟩ := enclApprox_spec neg hlo' hhi h1 h2
  exact ⟨lv, hv, hR1, hR2, hl, hh, by rw [he]; exact hwid⟩

/-- `gd x` is irrational for a nonzero finite float `x`. -/
theorem irrational_gd_of_toVal {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx0 : xv ≠ 0) : Irrational (gd xv) := by
  obtain ⟨q, hq⟩ := exists_rat_of_toVal hx
  have hq0 : q ≠ 0 := by
    rintro rfl
    apply hx0
    rw [hq, Rat.cast_zero]
  rw [hq]
  exact irrational_gd_rat hq0

/-- The Ziv certificate for `gd x`, `x` a finite nonzero float. -/
theorem gdApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (neg : Bool)
    {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (hx0 : xv ≠ 0) (e : AzInt)
    (hlo : (2 : ℝ) ^ (e.toInt - 1) ≤ |xv|) (hxe : |xv| < (2 : ℝ) ^ e.toInt)
    (hneg : neg = true ↔ xv < 0) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (gdApprox neg x e (w₀ * 2 ^ f)).1
      (gdApprox neg x e (w₀ * 2 ^ f)).2 p mode).isSome = true := by
  refine exists_isSome_of_irrational_threshold p mode (gdApprox neg x e)
    (v := (if neg then -1 else 1) * gd |xv|) ?_ (gdEps |xv| e) (tendsto_gdEps _ _) 0
    (fun w _ => gdApprox_spec neg hx hx0 e hlo hxe w) w₀ hw₀
  rw [← gd_eq_of_neg_iff hneg]
  exact irrational_gd_of_toVal hx hx0

/-! ### A rational argument -/

/-- The value of half a rational. -/
theorem toRat_half_abs (q : AzRat) :
    |((AzRat.toRat (q >>> (1 : ℕ)) : ℚ) : ℝ)| = |((AzRat.toRat q : ℚ) : ℝ)| / 2 := by
  rw [AzRat.toRat_shiftRight]
  push_cast
  rw [pow_one, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

theorem half_num_ne_zero (q : AzRat) (h0 : q.num ≠ 0) : (q >>> (1 : ℕ)).num ≠ 0 := by
  intro h
  have h1 := coe_toRat_eq_zero_of_num_eq_zero _ h
  have h2 := toRat_half_abs q
  rw [h1, abs_zero] at h2
  have hq0 : (AzRat.toRat q : ℝ) ≠ 0 := fun h => h0 ((AzRat.toRat_eq_zero_iff q).mp h)
  have := abs_pos.mpr hq0
  linarith

/-- The width bound of `gdRatBracket`. -/
noncomputable def gdRatEps (q : AzRat) (w : ℕ) : ℝ :=
  piEps (w + 72) + 2 * (1 / 2 : ℝ) ^ w
    + (2 * (1 / 2 : ℝ) ^ w + 4 * tanhRatEps (q >>> (1 : ℕ)) (w + 96))

theorem tendsto_gdRatEps (q : AzRat) :
    Filter.Tendsto (gdRatEps q) Filter.atTop (nhds 0) := by
  have h1 := tendsto_piEps.comp (Filter.tendsto_add_atTop_nat 72)
  have h2 := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).const_mul 2
  have h3 := ((tendsto_tanhRatEps (q >>> (1 : ℕ))).comp
    (Filter.tendsto_add_atTop_nat 96)).const_mul 4
  have := (h1.add h2).add (h2.add h3)
  simp only [mul_zero, add_zero] at this
  exact this

/-- **`gdRatBracket q w` encloses `gd |q|`** for a rational `q ≠ 0`, with width at most
`gdRatEps q w`. -/
theorem gdRatBracket_spec (q : AzRat) (h0 : q.num ≠ 0) (w : ℕ) :
    IsEnclW (gdRatBracket q w) (gd |((AzRat.toRat q : ℚ) : ℝ)|) (gdRatEps q w) := by
  set av := |((AzRat.toRat q : ℚ) : ℝ)| with hav
  have hq0 : (AzRat.toRat q : ℝ) ≠ 0 := fun h => h0 ((AzRat.toRat_eq_zero_iff q).mp h)
  have ha0 : 0 < av := abs_pos.mpr hq0
  have hh0 := half_num_ne_zero q h0
  have hhalf := toRat_half_abs q
  rw [← hav] at hhalf
  have hpi : 0 ≤ piEps (w + 72) := by unfold piEps; positivity
  have hw0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
  have htw : ∀ w' : ℕ, 64 ≤ w' →
      IsEnclW (tanhRatBracket (q >>> (1 : ℕ)) w') (Real.tanh (av / 2))
        (tanhRatEps (q >>> (1 : ℕ)) w') := fun w' hw' => by
    have := tanhRatBracket_spec hw' (q >>> (1 : ℕ)) hh0
    rwa [hhalf] at this
  have hTW : 0 ≤ tanhRatEps (q >>> (1 : ℕ)) (w + 96) := by
    obtain ⟨lo, hi, -, -, h1, h2, h3⟩ := htw (w + 96) (by omega)
    linarith
  have hKw : w + 8 ≤ atanWork (ratExpBound q) w := by unfold atanWork; omega
  have hcore := gdCoreOf_spec (htw (w + 96) (by omega)) ha0 hKw
  unfold gdRatBracket gdRatEps
  dsimp only
  split_ifs with hH hE hG hG
  · obtain ⟨lo, hi, h1, h2, h3, h4, h5⟩ := gdHuge_spec (ratAbsFloorN_le q) hH
    exact ⟨lo, hi, h1, h2, h3, h4, by linarith⟩
  · obtain ⟨lo, hi, h1, h2, h3, h4, h5⟩ := hcore
    exact ⟨lo, hi, h1, h2, h3, h4, by linarith⟩
  · split
    · next b hb =>
      have hz : IsEncl (expRatBracket (-q.abs)
          (max 64 (w + 8 + 24 - ratAbsFloorN q))) (Real.exp (-av)) := by
        obtain ⟨zl, zh, hzl, hzh, z1, z2, -⟩ := expRatBracket_spec
          (w := max 64 (w + 8 + 24 - ratAbsFloorN q)) (le_max_left _ _) (-q.abs)
        have e : ((AzRat.toRat (-q.abs) : ℚ) : ℝ) = -av := by
          rw [AzRat.toRat_neg, AzRat.toRat_abs]
          push_cast
          rfl
        rw [e] at z1 z2
        exact ⟨zl, zh, hzl, hzh, z1, z2⟩
      obtain ⟨lo, hi, h1, h2, h3, h4, h5⟩ := gdLargeOf_spec hz hb
      exact ⟨lo, hi, h1, h2, h3, h4, by linarith⟩
    · obtain ⟨lo, hi, h1, h2, h3, h4, h5⟩ := hcore
      exact ⟨lo, hi, h1, h2, h3, h4, by linarith⟩
  · obtain ⟨lo, hi, h1, h2, h3, h4, h5⟩ := hcore
    exact ⟨lo, hi, h1, h2, h3, h4, by linarith⟩
  · split
    · next b hb =>
      obtain ⟨tl, th, htl, hth, t1, t2, -⟩ := htw (w + 64) (by omega)
      obtain ⟨lo, hi, h1, h2, h3, h4, h5⟩ :=
        gdSmallOf_spec ⟨tl, th, htl, hth, t1, t2⟩ ha0 hKw hb
      exact ⟨lo, hi, h1, h2, h3, h4, by linarith⟩
    · obtain ⟨lo, hi, h1, h2, h3, h4, h5⟩ := hcore
      exact ⟨lo, hi, h1, h2, h3, h4, by linarith⟩

/-- `gdRatApprox` as a pair of `Roundable`s bracketing `gd q`. -/
theorem gdRatApprox_spec (q : AzRat) (h0 : q.num ≠ 0) (w : ℕ) :
    ∃ lv hv : ℝ, Rounds (gdRatApprox q w).1 lv ∧ Rounds (gdRatApprox q w).2 hv ∧
      lv ≤ gd (AzRat.toRat q : ℝ) ∧ gd (AzRat.toRat q : ℝ) ≤ hv ∧
      hv - lv ≤ gdRatEps q w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := gdRatBracket_spec q h0 w
  obtain ⟨lv, hv, hR1, hR2, hl, hh, he⟩ := enclApprox_spec (!q.sign) hlo hhi h1 h2
  rw [← gd_eq_of_neg_iff (toRat_neg_iff q h0)] at hl hh
  exact ⟨lv, hv, hR1, hR2, hl, hh, by rw [he]; exact hwid⟩

/-- `gd q` is irrational for a rational `q ≠ 0`. -/
theorem irrational_gd_toRat (q : AzRat) (h0 : q.num ≠ 0) :
    Irrational (gd (AzRat.toRat q : ℝ)) :=
  irrational_gd_rat (q := AzRat.toRat q)
    (fun h => h0 ((AzRat.toRat_eq_zero_iff q).mp (by rw [h, Rat.cast_zero])))

/-- The Ziv certificate for `gd q`. -/
theorem gdRatApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (q : AzRat)
    (h0 : q.num ≠ 0) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (gdRatApprox q (w₀ * 2 ^ f)).1
      (gdRatApprox q (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (gdRatApprox q) (irrational_gd_toRat q h0)
    (gdRatEps q) (tendsto_gdRatEps q) 0 (fun w _ => gdRatApprox_spec q h0 w) w₀ hw₀

end Azurite.AzFloat
