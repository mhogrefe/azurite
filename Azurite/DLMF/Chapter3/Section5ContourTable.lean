/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section5Contour
import Azurite.DLMF.Chapter3.Section5ComplexGaussTable
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# DLMF §3.5(ix): Table 3.5.20

The composite trapezoidal rule with step `h` for 3.5.45, `λ = 10` (`erfcTrap`; nodes
`kh ∈ (−π, π)`, `dlmf_table_3_5_20_nodes`; evenness `sum_Icc_even`), certified by exact rational
arithmetic in the kernel: dyadic outward rounding (`rdDown`, `rdUp`), `eˣ` by Taylor at `x/2ᵐ`
and `m` squarings (`expEncl_sound`, `Real.exp_bound`), `cos y` by Taylor through `(iy)ʲ`
(`cosEncl_sound`, `Complex.exp_bound`), `cos(θ/2) = 2cos²(θ/4) − 1`, `tan² = 1/cos² − 1`
(`gEncl_sound`), `π` from `Real.pi_gt_d20`/`pi_lt_d20` (`trapEncl_sound`).

* Rows `h = 0.15, 0.10` are correctly rounded (`dlmf_table_3_5_20`).
* **Erratum** (`dlmf_table_3_5_20_erratum`): rows `h = 0.25, 0.20` are off by one unit in the
  15th digit (`…96678 49…` printed `…96679`; `…34559 92…` printed `…34559`).
* Column `n` (`dlmf_table_3_5_20_n`): `5, 6, 8, 11` values `> 10⁻¹⁵`.
* "All digits shown in the approximation in the final row are correct" (`dlmf_table_3_5_20_erfc`):
  `erfc 10` from 20 terms of 7.12.1 with the remainder bound (`erfcEncl_sound`).
-/

open Finset Filter Topology

namespace Azurite.DLMF

/-! ### Dyadic outward rounding -/

/-- `⌊q 2ᵈ⌋/2ᵈ`. -/
def rdDown (d : ℕ) (q : ℚ) : ℚ := (⌊q * 2 ^ d⌋ : ℚ) / 2 ^ d

/-- `⌈q 2ᵈ⌉/2ᵈ`. -/
def rdUp (d : ℕ) (q : ℚ) : ℚ := (⌈q * 2 ^ d⌉ : ℚ) / 2 ^ d

theorem rdDown_le (d : ℕ) (q : ℚ) : rdDown d q ≤ q := by
  unfold rdDown
  rw [div_le_iff₀ (by positivity)]
  exact Int.floor_le _

theorem le_rdUp (d : ℕ) (q : ℚ) : q ≤ rdUp d q := by
  unfold rdUp
  rw [le_div_iff₀ (by positivity)]
  exact Int.le_ceil _

theorem rdDown_nonneg (d : ℕ) {q : ℚ} (hq : 0 ≤ q) : 0 ≤ rdDown d q := by
  unfold rdDown
  have : (0 : ℤ) ≤ ⌊q * 2 ^ d⌋ := Int.floor_nonneg.mpr (by positivity)
  positivity

/-! ### `exp` -/

/-- `∑_{i<n} yⁱ/i!`. -/
def expSumQ (y : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => expSumQ y n + y ^ n / n.factorial

theorem expSumQ_cast (y : ℚ) (n : ℕ) :
    (expSumQ y n : ℝ) = ∑ i ∈ range n, (y : ℝ) ^ i / i.factorial := by
  induction n with
  | zero => simp [expSumQ]
  | succ n ih => rw [expSumQ, sum_range_succ, ← ih]; push_cast; ring

/-- `m` outward-rounded squarings of an enclosure `[l, u]`, `0 ≤ l`. -/
def sqIter (d : ℕ) : ℕ → ℚ × ℚ → ℚ × ℚ
  | 0, p => p
  | m + 1, p => sqIter d m (rdDown d (p.1 ^ 2), rdUp d (p.2 ^ 2))

theorem sqIter_sound (d : ℕ) (m : ℕ) {p : ℚ × ℚ} {v : ℝ} (h0 : 0 ≤ p.1) (h1 : (p.1 : ℝ) ≤ v)
    (h2 : v ≤ p.2) : ((sqIter d m p).1 : ℝ) ≤ v ^ 2 ^ m ∧ v ^ 2 ^ m ≤ (sqIter d m p).2 := by
  induction m generalizing p v with
  | zero => simpa [sqIter] using ⟨h1, h2⟩
  | succ m ih =>
    rw [sqIter, show v ^ 2 ^ (m + 1) = (v ^ 2) ^ 2 ^ m by rw [← pow_mul, ← pow_succ']]
    have hv : 0 ≤ v := le_trans (by exact_mod_cast h0) h1
    refine ih (rdDown_nonneg d (by positivity)) ?_ ?_
    · calc ((rdDown d (p.1 ^ 2) : ℚ) : ℝ) ≤ ((p.1 ^ 2 : ℚ) : ℝ) := by
            exact_mod_cast rdDown_le d _
        _ ≤ v ^ 2 := by push_cast; gcongr
    · calc v ^ 2 ≤ ((p.2 ^ 2 : ℚ) : ℝ) := by push_cast; gcongr
        _ ≤ ((rdUp d (p.2 ^ 2) : ℚ) : ℝ) := by exact_mod_cast le_rdUp d _

/-- The Taylor error bound `|y|ⁿ (n + 1)/(n! n)`. -/
def expErrQ (y : ℚ) (n : ℕ) : ℚ := |y| ^ n * ((n + 1) / (n.factorial * n))

/-- An enclosure of `eˣ`: `n` Taylor terms at `x/2ᵐ` and `m` squarings at precision `2^{−d}`. -/
def expEncl (d m n : ℕ) (x : ℚ) : ℚ × ℚ :=
  let y := x / 2 ^ m
  sqIter d m (max (expSumQ y n - expErrQ y n) 0, expSumQ y n + expErrQ y n)

theorem expEncl_sound (d m : ℕ) {n : ℕ} (hn : 0 < n) {x : ℚ} (hx : |x| ≤ 2 ^ m) :
    ((expEncl d m n x).1 : ℝ) ≤ Real.exp x ∧ Real.exp x ≤ (expEncl d m n x).2 := by
  set y : ℚ := x / 2 ^ m
  have hy : |(y : ℝ)| ≤ 1 := by
    have : |y| ≤ 1 := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℚ) < 2 ^ m), div_le_one (by positivity)]
      exact hx
    exact_mod_cast this
  have hb := Real.exp_bound hy hn
  rw [← expSumQ_cast] at hb
  have hE : (|(y : ℝ)| ^ n * (n.succ / (n.factorial * n)) : ℝ) = (expErrQ y n : ℚ) := by
    simp [expErrQ]
  rw [hE] at hb
  have hlo := (abs_le.mp hb).1
  have hhi := (abs_le.mp hb).2
  have hxe : Real.exp x = Real.exp y ^ 2 ^ m := by
    rw [← Real.exp_nat_mul]
    congr 1
    simp only [y]; push_cast; field_simp
  rw [hxe]
  refine sqIter_sound d m (le_max_right _ _) ?_ ?_
  · push_cast
    exact max_le (by linarith) (Real.exp_pos _).le
  · push_cast; linarith

/-! ### `cos` -/

/-- `(iy)ʲ = (re, im)`. -/
def cisPow (y : ℚ) : ℕ → ℚ × ℚ
  | 0 => (1, 0)
  | j + 1 => (-(y * (cisPow y j).2), y * (cisPow y j).1)

theorem cisPow_spec (y : ℚ) (j : ℕ) :
    ((y : ℂ) * Complex.I) ^ j = ⟨(cisPow y j).1, (cisPow y j).2⟩ := by
  induction j with
  | zero => simp [cisPow]; rfl
  | succ j ih =>
    rw [pow_succ, ih]
    apply Complex.ext <;> simp [cisPow, Complex.mul_re, Complex.mul_im] <;> ring

/-- `∑_{j<n} ℜ(iy)ʲ/j!`. -/
def cosSumQ (y : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => cosSumQ y n + (cisPow y n).1 / n.factorial

theorem cosSumQ_cast (y : ℚ) (n : ℕ) :
    (cosSumQ y n : ℝ) = (∑ i ∈ range n, ((y : ℂ) * Complex.I) ^ i / i.factorial).re := by
  induction n with
  | zero => simp [cosSumQ]
  | succ n ih =>
    rw [cosSumQ, sum_range_succ, Complex.add_re, ← ih, cisPow_spec,
      show ((n.factorial : ℂ)) = ((n.factorial : ℝ) : ℂ) by push_cast; rfl, Complex.div_ofReal_re]
    push_cast
    ring

theorem cos_sub_cosSumQ_le {y : ℚ} (hy : |y| ≤ 1) {n : ℕ} (hn : 0 < n) :
    |Real.cos y - cosSumQ y n| ≤ (expErrQ y n : ℝ) := by
  have hz : ‖(y : ℂ) * Complex.I‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_ratCast]; exact_mod_cast hy
  have hb := Complex.exp_bound hz hn
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_ratCast] at hb
  have hre : Real.cos y - cosSumQ y n = (Complex.exp ((y : ℂ) * Complex.I) -
      ∑ i ∈ range n, ((y : ℂ) * Complex.I) ^ i / i.factorial).re := by
    rw [Complex.sub_re, ← cosSumQ_cast, show ((y : ℂ)) = ((y : ℝ) : ℂ) by push_cast; rfl,
      Complex.exp_ofReal_mul_I_re]
  rw [hre]
  refine (Complex.abs_re_le_norm _).trans (hb.trans (le_of_eq ?_))
  simp [expErrQ, div_eq_mul_inv]

/-- An enclosure `[S − E, S + E]` of `cos y`, `|y| ≤ 1`. -/
def cosEncl (n : ℕ) (y : ℚ) : ℚ × ℚ := (cosSumQ y n - expErrQ y n, cosSumQ y n + expErrQ y n)

theorem cosEncl_sound {n : ℕ} (hn : 0 < n) {y : ℚ} (hy : |y| ≤ 1) :
    ((cosEncl n y).1 : ℝ) ≤ Real.cos y ∧ Real.cos y ≤ (cosEncl n y).2 := by
  have h := abs_le.mp (cos_sub_cosSumQ_le hy hn)
  simp only [cosEncl]; push_cast
  constructor <;> linarith [h.1, h.2]

/-! ### The integrand `e^{−λ² tan²(θ/2)}` at `0 ≤ θ < π` -/

/-- An enclosure of `cos(θ/2) = 2 cos²(θ/4) − 1`. -/
def cosHalfEncl (d n : ℕ) (θ : ℚ) : ℚ × ℚ :=
  (rdDown d (2 * rdDown d (max (cosEncl n (θ / 4)).1 0) ^ 2 - 1),
    rdUp d (2 * rdUp d (cosEncl n (θ / 4)).2 ^ 2 - 1))

theorem cosHalfEncl_sound (d : ℕ) {n : ℕ} (hn : 0 < n) {θ : ℚ} (h0 : 0 ≤ θ) (h4 : θ ≤ 4)
    (hπ : (θ : ℝ) < Real.pi) :
    ((cosHalfEncl d n θ).1 : ℝ) ≤ Real.cos (θ / 2) ∧
      Real.cos ((θ : ℝ) / 2) ≤ (cosHalfEncl d n θ).2 := by
  have hy : |θ / 4| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]; linarith
  have hc := cosEncl_sound hn hy
  push_cast at hc
  have hθ0 : (0 : ℝ) ≤ θ := by exact_mod_cast h0
  have hcpos : 0 ≤ Real.cos ((θ : ℝ) / 4) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩
  have hdbl : Real.cos ((θ : ℝ) / 2) = 2 * Real.cos ((θ : ℝ) / 4) ^ 2 - 1 := by
    rw [← Real.cos_two_mul]; ring_nf
  set l := rdDown d (max (cosEncl n (θ / 4)).1 0)
  set u := rdUp d (cosEncl n (θ / 4)).2
  have hl0 : 0 ≤ l := rdDown_nonneg d (le_max_right _ _)
  have hl : (l : ℝ) ≤ Real.cos ((θ : ℝ) / 4) := by
    calc (l : ℝ) ≤ ((max (cosEncl n (θ / 4)).1 0 : ℚ) : ℝ) := by exact_mod_cast rdDown_le d _
      _ ≤ _ := by push_cast; exact max_le hc.1 hcpos
  have hu : Real.cos ((θ : ℝ) / 4) ≤ u :=
    hc.2.trans (by exact_mod_cast le_rdUp d _)
  simp only [cosHalfEncl]
  rw [hdbl]
  constructor
  · calc ((rdDown d (2 * l ^ 2 - 1) : ℚ) : ℝ) ≤ ((2 * l ^ 2 - 1 : ℚ) : ℝ) := by
          exact_mod_cast rdDown_le d _
      _ ≤ _ := by push_cast; gcongr
  · calc 2 * Real.cos ((θ : ℝ) / 4) ^ 2 - 1 ≤ ((2 * u ^ 2 - 1 : ℚ) : ℝ) := by
          push_cast; gcongr
      _ ≤ _ := by exact_mod_cast le_rdUp d _

/-- `tan² x = 1/cos² x − 1`. -/
theorem tan_sq_eq (x : ℝ) (hx : Real.cos x ≠ 0) : Real.tan x ^ 2 = 1 / Real.cos x ^ 2 - 1 := by
  rw [Real.tan_eq_sin_div_cos]
  have := Real.sin_sq_add_cos_sq x
  field_simp
  linarith

/-- An enclosure of `e^{−L tan²(θ/2)}` (`L = λ²`) with exponent bound `2ᵐ`. -/
def gEncl (d m n : ℕ) (L θ : ℚ) : ℚ × ℚ :=
  let c := cosHalfEncl d n θ
  let xl := rdDown d (-(L * (1 / c.1 ^ 2 - 1)))
  let xu := rdUp d (-(L * (1 / c.2 ^ 2 - 1)))
  (if 0 < c.1 ∧ |xl| ≤ 2 ^ m then (expEncl d m n xl).1 else 0,
    if 0 < c.2 ∧ |xu| ≤ 2 ^ m then (expEncl d m n xu).2 else 1)

theorem gEncl_sound (d m : ℕ) {n : ℕ} (hn : 0 < n) {L θ : ℚ} (hL : 0 ≤ L) (h0 : 0 ≤ θ)
    (h4 : θ ≤ 4) (hπ : (θ : ℝ) < Real.pi) {lam : ℝ} (hlam : lam ^ 2 = L) :
    ((gEncl d m n L θ).1 : ℝ) ≤ erfcPathIntegrand lam θ ∧
      erfcPathIntegrand lam θ ≤ (gEncl d m n L θ).2 := by
  have hc := cosHalfEncl_sound d hn h0 h4 hπ
  have hθ0 : (0 : ℝ) ≤ θ := by exact_mod_cast h0
  have hC : 0 < Real.cos ((θ : ℝ) / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have hg : erfcPathIntegrand lam θ = Real.exp (-((L : ℝ) * (1 / Real.cos ((θ : ℝ) / 2) ^ 2 - 1)))
      := by
    rw [erfcPathIntegrand, tan_sq_eq _ hC.ne', hlam]
  have hL' : (0 : ℝ) ≤ L := by exact_mod_cast hL
  set c := cosHalfEncl d n θ
  simp only [gEncl]
  constructor
  · split_ifs with h
    · rw [hg]
      refine (expEncl_sound d m hn h.2).1.trans (Real.exp_le_exp.mpr ?_)
      calc ((rdDown d (-(L * (1 / c.1 ^ 2 - 1))) : ℚ) : ℝ)
          ≤ ((-(L * (1 / c.1 ^ 2 - 1)) : ℚ) : ℝ) := by exact_mod_cast rdDown_le d _
        _ ≤ _ := by
          have h1 : (0 : ℝ) < c.1 := by exact_mod_cast h.1
          push_cast
          have : 1 / Real.cos ((θ : ℝ) / 2) ^ 2 ≤ 1 / (c.1 : ℝ) ^ 2 := by
            gcongr; exact hc.1
          nlinarith
    · push_cast; exact erfcPathIntegrand_nonneg _ _
  · split_ifs with h
    · rw [hg]
      refine (Real.exp_le_exp.mpr ?_).trans (expEncl_sound d m hn h.2).2
      calc -((L : ℝ) * (1 / Real.cos ((θ : ℝ) / 2) ^ 2 - 1))
          ≤ ((-(L * (1 / c.2 ^ 2 - 1)) : ℚ) : ℝ) := by
            push_cast
            have : 1 / (c.2 : ℝ) ^ 2 ≤ 1 / Real.cos ((θ : ℝ) / 2) ^ 2 := by
              gcongr; exact hc.2
            nlinarith
        _ ≤ _ := by exact_mod_cast le_rdUp d _
    · push_cast; exact erfcPathIntegrand_le_one _ _

/-! ### The composite trapezoidal rule for 3.5.45 -/

/-- The composite trapezoidal rule (3.5.2) with step `h` for the integral 3.5.45, nodes `kh`,
`|k| ≤ K` (with `Kh < π < (K + 1)h` these are all nodes in `(−π, π)`, `erfcTrap_nodes`; the
periodic extension vanishes at `±π`, `erfcPathExt_pi`):
`e^{−λ²}/(2π) · h ∑_{k=−K}^{K} e^{−λ² tan²(kh/2)}`. -/
noncomputable def erfcTrap (lam h : ℝ) (K : ℕ) : ℝ :=
  Real.exp (-lam ^ 2) / (2 * Real.pi) *
    (h * ∑ k ∈ Icc (-(K : ℤ)) K, erfcPathIntegrand lam (k * h))

theorem erfcTrap_nodes {h : ℝ} (hh : 0 < h) {K : ℕ} (hK : K * h < Real.pi)
    (hK' : Real.pi < (K + 1) * h) (k : ℤ) : |k * h| < Real.pi ↔ k ∈ Icc (-(K : ℤ)) K := by
  rw [mem_Icc, abs_lt]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · by_contra hk
      have : (k : ℝ) ≤ -((K : ℝ) + 1) := by exact_mod_cast (by omega : k ≤ -((K : ℤ) + 1))
      nlinarith
    · by_contra hk
      have : (K : ℝ) + 1 ≤ k := by exact_mod_cast (by omega : (K : ℤ) + 1 ≤ k)
      nlinarith
  · rintro ⟨h1, h2⟩
    have h1' : -(K : ℝ) ≤ k := by exact_mod_cast h1
    have h2' : (k : ℝ) ≤ K := by exact_mod_cast h2
    constructor <;> nlinarith

/-- "We exploit the fact that the integrand is even": `∑_{k=−K}^{K} f(kh) = f(0) + 2∑_{k=1}^{K}
f(kh)`. -/
theorem sum_Icc_even {f : ℤ → ℝ} (hf : ∀ k, f (-k) = f k) (K : ℕ) :
    ∑ k ∈ Icc (-(K : ℤ)) K, f k = f 0 + 2 * ∑ k ∈ range K, f (k + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
    have e : Icc (-((K + 1 : ℕ) : ℤ)) ((K + 1 : ℕ) : ℤ) =
        insert (-((K : ℤ) + 1)) (insert ((K : ℤ) + 1) (Icc (-(K : ℤ)) K)) := by
      ext k; simp only [mem_Icc, mem_insert]; push_cast; omega
    rw [e, sum_insert (by simp only [mem_insert, mem_Icc]; omega),
      sum_insert (by simp only [mem_Icc]; omega), ih, sum_range_succ, hf]
    ring

theorem erfcPathIntegrand_zero (lam : ℝ) : erfcPathIntegrand lam 0 = 1 := by
  simp [erfcPathIntegrand]

/-! ### Certified enclosures of the rule -/

/-- Enclosure of `∑_{k=1}^{K} e^{−L tan²(kh/2)}`. -/
def gSumEncl (d m n : ℕ) (L h : ℚ) : ℕ → ℚ × ℚ
  | 0 => (0, 0)
  | k + 1 => ((gSumEncl d m n L h k).1 + (gEncl d m n L ((k + 1) * h)).1,
      (gSumEncl d m n L h k).2 + (gEncl d m n L ((k + 1) * h)).2)

theorem gSumEncl_sound (d m : ℕ) {n : ℕ} (hn : 0 < n) {L h : ℚ} (hL : 0 ≤ L) (hh : 0 ≤ h)
    {lam : ℝ} (hlam : lam ^ 2 = L) {K : ℕ} (h4 : (K : ℚ) * h ≤ 4)
    (hπ : (K : ℝ) * h < Real.pi) :
    ((gSumEncl d m n L h K).1 : ℝ) ≤ ∑ k ∈ range K, erfcPathIntegrand lam (((k : ℝ) + 1) * h) ∧
      ∑ k ∈ range K, erfcPathIntegrand lam (((k : ℝ) + 1) * h) ≤ (gSumEncl d m n L h K).2 := by
  induction K with
  | zero => simp [gSumEncl]
  | succ K ih =>
    have hh' : (0 : ℝ) ≤ h := by exact_mod_cast hh
    push_cast at h4 hπ
    have hK4 : (K : ℚ) * h ≤ 4 := le_trans (by nlinarith) h4
    have hKπ : (K : ℝ) * h < Real.pi :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by linarith) hh') hπ
    obtain ⟨ih1, ih2⟩ := ih hK4 hKπ
    have hg := gEncl_sound d m hn (θ := ((K : ℚ) + 1) * h) hL (by positivity)
      h4 (by push_cast; exact hπ) hlam
    rw [sum_range_succ]
    simp only [gSumEncl]
    push_cast at hg ⊢
    constructor <;> linarith [hg.1, hg.2]

/-- `3.14159265358979323846 < π < 3.14159265358979323847`. -/
def piLoQ : ℚ := 314159265358979323846 / 10 ^ 20

def piHiQ : ℚ := 314159265358979323847 / 10 ^ 20

theorem piLoQ_lt : (piLoQ : ℝ) < Real.pi := by
  have := Real.pi_gt_d20; unfold piLoQ; push_cast; linarith

theorem pi_lt_piHiQ : Real.pi < piHiQ := by
  have := Real.pi_lt_d20; unfold piHiQ; push_cast; linarith

/-- The precision parameters: `2^{−320}`, exponents up to `2²⁴`, 30 Taylor terms. -/
def tD : ℕ := 320

def tM : ℕ := 24

def tN : ℕ := 30

/-- Enclosure of `erfcTrap λ h K` (`L = λ²`). -/
def trapEncl (L h : ℚ) (K : ℕ) : ℚ × ℚ :=
  let E := expEncl tD tM tN (-L)
  let S := gSumEncl tD tM tN L h K
  (E.1 / (2 * piHiQ) * (h * (1 + 2 * S.1)), E.2 / (2 * piLoQ) * (h * (1 + 2 * S.2)))

/-- The side conditions checked in the kernel. -/
def trapOK (L h : ℚ) (K : ℕ) : Bool :=
  decide (0 ≤ L) && decide (0 < h) && decide ((K : ℚ) * h ≤ 4) && decide ((K : ℚ) * h < piLoQ) &&
    decide (piHiQ < ((K : ℚ) + 1) * h) && decide (|-L| ≤ 2 ^ tM) &&
    decide (0 ≤ (expEncl tD tM tN (-L)).1) && decide (0 ≤ (gSumEncl tD tM tN L h K).1)

theorem trapEncl_sound {L h : ℚ} {K : ℕ} (hok : trapOK L h K = true) {lam : ℝ}
    (hlam : lam ^ 2 = L) :
    ((trapEncl L h K).1 : ℝ) ≤ erfcTrap lam h K ∧ erfcTrap lam h K ≤ (trapEncl L h K).2 := by
  simp only [trapOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨hL, hh⟩, h4⟩, hKlo⟩, hKhi⟩, hLm⟩, hE0⟩, hS0⟩ := hok
  have hπK : (K : ℝ) * h < Real.pi :=
    lt_trans (by exact_mod_cast hKlo) piLoQ_lt
  have hS := gSumEncl_sound tD tM (by decide : 0 < tN) hL hh.le hlam h4 hπK
  have hE := expEncl_sound tD tM (n := tN) (by decide) hLm
  have hEe : Real.exp (-lam ^ 2) = Real.exp ((-L : ℚ) : ℝ) := by rw [hlam]; push_cast; rfl
  have hsum : ∑ k ∈ Icc (-(K : ℤ)) K, erfcPathIntegrand lam (k * h) =
      1 + 2 * ∑ k ∈ range K, erfcPathIntegrand lam (((k : ℝ) + 1) * h) := by
    rw [sum_Icc_even (f := fun k : ℤ => erfcPathIntegrand lam (k * h)) (fun k => by
      simp only [Int.cast_neg, neg_mul]; exact erfcPathIntegrand_neg lam _)]
    simp only [Int.cast_zero, zero_mul, erfcPathIntegrand_zero]
    push_cast; rfl
  have hpl := piLoQ_lt
  have hph := pi_lt_piHiQ
  have hpl0 : (0 : ℝ) < piLoQ := by unfold piLoQ; norm_num
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hE0' : (0 : ℝ) ≤ (expEncl tD tM tN (-L)).1 := by exact_mod_cast hE0
  have hS0' : (0 : ℝ) ≤ (gSumEncl tD tM tN L h K).1 := by exact_mod_cast hS0
  unfold erfcTrap trapEncl
  rw [hsum, hEe]
  simp only
  push_cast
  constructor
  · calc ((expEncl tD tM tN (-L)).1 : ℝ) / (2 * piHiQ) *
          (h * (1 + 2 * ((gSumEncl tD tM tN L h K).1 : ℝ)))
        ≤ Real.exp ((-L : ℚ) : ℝ) / (2 * Real.pi) *
          (h * (1 + 2 * ∑ k ∈ range K, erfcPathIntegrand lam (((k : ℝ) + 1) * h))) := by
          gcongr
          · exact hE.1
          · exact hS.1
    _ = _ := by push_cast; ring
  · calc Real.exp (-(L : ℝ)) / (2 * Real.pi) *
          (h * (1 + 2 * ∑ k ∈ range K, erfcPathIntegrand lam (((k : ℝ) + 1) * h)))
        ≤ ((expEncl tD tM tN (-L)).2 : ℝ) / (2 * piLoQ) *
          (h * (1 + 2 * ((gSumEncl tD tM tN L h K).2 : ℝ))) := by
          have h1 : Real.exp (-(L : ℝ)) ≤ (expEncl tD tM tN (-L)).2 := by
            have := hE.2; push_cast at this; exact this
          have h2 : 0 ≤ ∑ k ∈ range K, erfcPathIntegrand lam (((k : ℝ) + 1) * h) :=
            sum_nonneg fun _ _ => erfcPathIntegrand_nonneg _ _
          have h3 : (0 : ℝ) ≤ (expEncl tD tM tN (-L)).2 := le_trans (Real.exp_pos _).le h1
          gcongr
          exact hS.2

/-! ### Rounding checks -/

/-- `[e₁, e₂]` lies within half a unit of `M · 10^{−d}`. -/
def enclRoundsOK (e : ℚ × ℚ) (M : ℤ) (d : ℕ) : Bool :=
  decide (|(e.1 + e.2) / 2 - M / 10 ^ d| + (e.2 - e.1) / 2 ≤ 5 / 10 ^ (d + 1))

/-- `[e₁, e₂]` lies more than half a unit from `M · 10^{−d}`. -/
def enclWrongOK (e : ℚ × ℚ) (M : ℤ) (d : ℕ) : Bool :=
  decide (5 / 10 ^ (d + 1) < |(e.1 + e.2) / 2 - M / 10 ^ d| - (e.2 - e.1) / 2)

theorem abs_sub_mid_le {v : ℝ} {e : ℚ × ℚ} (h1 : (e.1 : ℝ) ≤ v) (h2 : v ≤ e.2) :
    |v - (((e.1 + e.2) / 2 : ℚ) : ℝ)| ≤ (((e.2 - e.1) / 2 : ℚ) : ℝ) := by
  push_cast
  rw [abs_le]; constructor <;> linarith

theorem roundsTo_of_encl {v : ℝ} {e : ℚ × ℚ} {M : ℤ} {d : ℕ} (h1 : (e.1 : ℝ) ≤ v)
    (h2 : v ≤ e.2) (h : enclRoundsOK e M d = true) : RoundsTo v (M, d) := by
  simp only [enclRoundsOK, decide_eq_true_eq] at h
  exact roundsTo_of_le (abs_sub_mid_le h1 h2) h

theorem not_roundsTo_of_encl {v : ℝ} {e : ℚ × ℚ} {M : ℤ} {d : ℕ} (h1 : (e.1 : ℝ) ≤ v)
    (h2 : v ≤ e.2) (h : enclWrongOK e M d = true) : ¬ RoundsTo v (M, d) := by
  simp only [enclWrongOK, decide_eq_true_eq] at h
  have h' := (Rat.cast_lt (K := ℝ)).mpr h
  push_cast at h'
  have hm := abs_sub_mid_le h1 h2
  push_cast at hm
  unfold RoundsTo
  intro hr
  have := abs_sub_le (((e.1 + e.2) / 2 : ℝ)) v (M / 10 ^ d)
  rw [abs_sub_comm] at hm
  linarith

/-! ### The `n` column -/

/-- For `k ≤ K`: `e^{−L tan²(kh/2)} > 10^{−15}` exactly when `k < n`. -/
def countOK (L h : ℚ) (K n : ℕ) : Bool :=
  decide (n ≤ K + 1) && decide (∀ k : Fin (K + 1), if (k : ℕ) < n then
    1 / 10 ^ 15 < (gEncl tD tM tN L ((k : ℚ) * h)).1 else
    (gEncl tD tM tN L ((k : ℚ) * h)).2 ≤ 1 / 10 ^ 15)

theorem count_sound {L h : ℚ} {K n : ℕ} (hok : trapOK L h K = true) (hc : countOK L h K n = true)
    {lam : ℝ} (hlam : lam ^ 2 = L) :
    ((range (K + 1)).filter fun k : ℕ => (1 : ℝ) / 10 ^ 15 < erfcPathIntegrand lam (k * h)).card
      = n := by
  simp only [trapOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨hL, hh⟩, h4⟩, hKlo⟩, hKhi⟩, hLm⟩, hE0⟩, hS0⟩ := hok
  simp only [countOK, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨hnK, hc⟩ := hc
  suffices e : (range (K + 1)).filter (fun k : ℕ => (1 : ℝ) / 10 ^ 15 <
      erfcPathIntegrand lam (k * h)) = range n by rw [e, card_range]
  ext k
  simp only [mem_filter, mem_range]
  constructor
  · rintro ⟨hk, hlt⟩
    by_contra hkn
    have := hc ⟨k, hk⟩
    simp only [hkn, ↓reduceIte] at this
    have hkh4 : (k : ℚ) * h ≤ 4 :=
      le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.lt_succ_iff.mp hk) hh.le) h4
    have hKπ' : ((((K : ℚ) * h) : ℚ) : ℝ) < Real.pi :=
      lt_trans (by exact_mod_cast hKlo) piLoQ_lt
    have hkπ : (((k : ℚ) * h : ℚ) : ℝ) < Real.pi := by
      refine lt_of_le_of_lt ?_ hKπ'
      exact_mod_cast mul_le_mul_of_nonneg_right
        (by exact_mod_cast Nat.lt_succ_iff.mp hk : (k : ℚ) ≤ K) hh.le
    have hg := (gEncl_sound tD tM (by decide : 0 < tN) hL (by positivity) hkh4 hkπ hlam).2
    have : (((gEncl tD tM tN L ((k : ℚ) * h)).2 : ℚ) : ℝ) ≤ ((1 / 10 ^ 15 : ℚ) : ℝ) := by
      exact_mod_cast this
    push_cast at hg this
    linarith
  · intro hkn
    have hk : k < K + 1 := lt_of_lt_of_le hkn hnK
    refine ⟨hk, ?_⟩
    have := hc ⟨k, hk⟩
    simp only [hkn, ↓reduceIte] at this
    have hkh4 : (k : ℚ) * h ≤ 4 :=
      le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.lt_succ_iff.mp hk) hh.le) h4
    have hKπ' : ((((K : ℚ) * h) : ℚ) : ℝ) < Real.pi :=
      lt_trans (by exact_mod_cast hKlo) piLoQ_lt
    have hkπ : (((k : ℚ) * h : ℚ) : ℝ) < Real.pi := by
      refine lt_of_le_of_lt ?_ hKπ'
      exact_mod_cast mul_le_mul_of_nonneg_right
        (by exact_mod_cast Nat.lt_succ_iff.mp hk : (k : ℚ) ≤ K) hh.le
    have hg := (gEncl_sound tD tM (by decide : 0 < tN) hL (by positivity) hkh4 hkπ hlam).1
    have : ((1 / 10 ^ 15 : ℚ) : ℝ) < (((gEncl tD tM tN L ((k : ℚ) * h)).1 : ℚ) : ℝ) := by
      exact_mod_cast this
    push_cast at hg this
    linarith

/-! ### `erfc 10` from the asymptotic expansion 7.12.1 -/

/-- `(−1)ʲ cⱼ / x^{2j+1}`, `cⱼ = (2j)!/(j! 4ʲ)`. -/
def erfcTermQ (x : ℚ) (j : ℕ) : ℚ :=
  (-1) ^ j * ((2 * j).factorial / (j.factorial * 4 ^ j)) / x ^ (2 * j + 1)

def erfcAsymQ (x : ℚ) : ℕ → ℚ
  | 0 => 0
  | k + 1 => erfcAsymQ x k + erfcTermQ x k

theorem erfcTerm_eq (x : ℚ) (j : ℕ) :
    BZ.erfcTerm j x = Real.exp (-(x : ℝ) ^ 2) / √Real.pi * erfcTermQ x j := by
  unfold BZ.erfcTerm erfcTermQ BZ.erfcCoeff
  push_cast
  ring

theorem erfcAsymQ_eq (x : ℚ) (k : ℕ) :
    ∑ j ∈ range k, BZ.erfcTerm j x = Real.exp (-(x : ℝ) ^ 2) / √Real.pi * erfcAsymQ x k := by
  induction k with
  | zero => simp [erfcAsymQ]
  | succ k ih => rw [sum_range_succ, ih, erfcTerm_eq, erfcAsymQ]; push_cast; ring

def sqrtPiLoQ : ℚ := 17724538509055160272 / 10 ^ 19

def sqrtPiHiQ : ℚ := 17724538509055160274 / 10 ^ 19

theorem sqrtPiLoQ_lt : (sqrtPiLoQ : ℝ) < √Real.pi := by
  rw [Real.lt_sqrt (by unfold sqrtPiLoQ; positivity)]
  refine lt_trans ?_ piLoQ_lt
  exact_mod_cast (by unfold sqrtPiLoQ piLoQ; norm_num : sqrtPiLoQ ^ 2 < piLoQ)

theorem sqrt_pi_lt_sqrtPiHiQ : √Real.pi < sqrtPiHiQ := by
  rw [Real.sqrt_lt' (by unfold sqrtPiHiQ; positivity)]
  refine lt_trans pi_lt_piHiQ ?_
  exact_mod_cast (by unfold sqrtPiHiQ piHiQ; norm_num : piHiQ < sqrtPiHiQ ^ 2)

/-- Enclosure of `erfc x` from `k` terms of 7.12.1 (error at most the next term). -/
def erfcEncl (x : ℚ) (k : ℕ) : ℚ × ℚ :=
  let E := expEncl tD tM tN (-(x ^ 2))
  (E.1 / sqrtPiHiQ * (erfcAsymQ x k - |erfcTermQ x k|),
    E.2 / sqrtPiLoQ * (erfcAsymQ x k + |erfcTermQ x k|))

def erfcEnclOK (x : ℚ) (k : ℕ) : Bool :=
  decide (0 < x) && decide (|-(x ^ 2)| ≤ 2 ^ tM) && decide (0 ≤ (expEncl tD tM tN (-(x ^ 2))).1) &&
    decide (0 ≤ erfcAsymQ x k - |erfcTermQ x k|)

theorem erfcEncl_sound {x : ℚ} {k : ℕ} (hok : erfcEnclOK x k = true) :
    ((erfcEncl x k).1 : ℝ) ≤ BZ.erfc x ∧ BZ.erfc x ≤ (erfcEncl x k).2 := by
  simp only [erfcEnclOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨hx, hm⟩, hE0⟩, hS⟩ := hok
  have hx' : (0 : ℝ) < x := by exact_mod_cast hx
  have hE := expEncl_sound tD tM (n := tN) (by decide) hm
  push_cast at hE
  have hrem := BZ.abs_erfcRem_le_abs_term hx' k
  rw [erfcTerm_eq, abs_mul,
    abs_of_pos (div_pos (Real.exp_pos _) (Real.sqrt_pos.mpr Real.pi_pos))] at hrem
  have he := BZ.erfc_eq_sum_add_rem hx' k
  rw [erfcAsymQ_eq] at he
  have hb := abs_le.mp hrem
  have hsl := sqrtPiLoQ_lt
  have hsh := sqrt_pi_lt_sqrtPiHiQ
  have hsl0 : (0 : ℝ) < sqrtPiLoQ := by unfold sqrtPiLoQ; norm_num
  have hS' : (0 : ℝ) ≤ erfcAsymQ x k - |erfcTermQ x k| := by exact_mod_cast hS
  have hE0' : (0 : ℝ) ≤ (expEncl tD tM tN (-(x ^ 2))).1 := by exact_mod_cast hE0
  set A := Real.exp (-(x : ℝ) ^ 2) / √Real.pi
  have hA : 0 < A := div_pos (Real.exp_pos _) (Real.sqrt_pos.mpr Real.pi_pos)
  simp only [erfcEncl]
  push_cast
  rw [he]
  constructor
  · calc ((expEncl tD tM tN (-(x ^ 2))).1 : ℝ) / sqrtPiHiQ *
          ((erfcAsymQ x k : ℝ) - |(erfcTermQ x k : ℝ)|)
        ≤ A * ((erfcAsymQ x k : ℝ) - |(erfcTermQ x k : ℝ)|) := by
          gcongr
          · push_cast at hS'; exact hS'
          · unfold A; gcongr
            · exact hE.1.trans (le_of_eq (by ring_nf))
      _ ≤ A * erfcAsymQ x k + BZ.erfcRem k x := by
          rw [mul_sub]
          have : -(A * |(erfcTermQ x k : ℝ)|) ≤ BZ.erfcRem k x := by
            have := hb.1; linarith
          linarith
  · calc A * erfcAsymQ x k + BZ.erfcRem k x
        ≤ A * ((erfcAsymQ x k : ℝ) + |(erfcTermQ x k : ℝ)|) := by
          rw [mul_add]
          have := hb.2; linarith
      _ ≤ ((expEncl tD tM tN (-(x ^ 2))).2 : ℝ) / sqrtPiLoQ *
          ((erfcAsymQ x k : ℝ) + |(erfcTermQ x k : ℝ)|) := by
          have h0 : (0 : ℝ) ≤ (erfcAsymQ x k : ℝ) + |(erfcTermQ x k : ℝ)| := by
            push_cast at hS'; linarith [abs_nonneg (erfcTermQ x k : ℝ)]
          gcongr
          unfold A
          have hE2 : Real.exp (-(x : ℝ) ^ 2) ≤ (expEncl tD tM tN (-(x ^ 2))).2 :=
            le_trans (le_of_eq (by ring_nf)) hE.2
          have : (0 : ℝ) ≤ (expEncl tD tM tN (-(x ^ 2))).2 := le_trans (Real.exp_pos _).le hE2
          gcongr

/-! ### Table 3.5.20 -/

theorem trap_roundsTo {h : ℚ} {K : ℕ} {M : ℤ} (hok : trapOK 100 h K = true)
    (hr : enclRoundsOK (trapEncl 100 h K) M 59 = true) : RoundsTo (erfcTrap 10 h K) (M, 59) :=
  have hs := trapEncl_sound hok (lam := 10) (by norm_num)
  roundsTo_of_encl hs.1 hs.2 hr

theorem trap_not_roundsTo {h : ℚ} {K : ℕ} {M : ℤ} (hok : trapOK 100 h K = true)
    (hr : enclWrongOK (trapEncl 100 h K) M 59 = true) : ¬ RoundsTo (erfcTrap 10 h K) (M, 59) :=
  have hs := trapEncl_sound hok (lam := 10) (by norm_num)
  not_roundsTo_of_encl hs.1 hs.2 hr

/-- The rows of Table 3.5.20 use all nodes `kh ∈ (−π, π)`: `K = 12, 15, 20, 31` for
`h = 0.25, 0.20, 0.15, 0.10`. -/
theorem dlmf_table_3_5_20_nodes (k : ℤ) :
    (|k * (1 / 4 : ℝ)| < Real.pi ↔ k ∈ Icc (-12 : ℤ) 12) ∧
    (|k * (1 / 5 : ℝ)| < Real.pi ↔ k ∈ Icc (-15 : ℤ) 15) ∧
    (|k * (3 / 20 : ℝ)| < Real.pi ↔ k ∈ Icc (-20 : ℤ) 20) ∧
    (|k * (1 / 10 : ℝ)| < Real.pi ↔ k ∈ Icc (-31 : ℤ) 31) := by
  have h1 := Real.pi_gt_d2
  have h2 := Real.pi_lt_d2
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact erfcTrap_nodes (K := 12) (by norm_num) (by norm_num; linarith) (by norm_num; linarith) k
  · exact erfcTrap_nodes (K := 15) (by norm_num) (by norm_num; linarith) (by norm_num; linarith) k
  · exact erfcTrap_nodes (K := 20) (by norm_num) (by norm_num; linarith) (by norm_num; linarith) k
  · exact erfcTrap_nodes (K := 31) (by norm_num) (by norm_num; linarith) (by norm_num; linarith) k

/-- **Table 3.5.20**, rows `h = 0.15` and `h = 0.10`: the printed approximations
`0.20884 87588 72946 × 10⁻⁴⁴` and `0.20884 87583 76254 × 10⁻⁴⁴` are the correctly rounded values
of the composite trapezoidal rule for 3.5.45 with `λ = 10`. -/
theorem dlmf_table_3_5_20 :
    RoundsTo (erfcTrap 10 (3 / 20) 20) (208848758872946, 59) ∧
      RoundsTo (erfcTrap 10 (1 / 10) 31) (208848758376254, 59) := by
  constructor
  · have := trap_roundsTo (h := 3 / 20) (K := 20) (M := 208848758872946)
      (by decide +kernel) (by decide +kernel)
    push_cast at this; exact this
  · have := trap_roundsTo (h := 1 / 10) (K := 31) (M := 208848758376254)
      (by decide +kernel) (by decide +kernel)
    push_cast at this; exact this

/-- **Table 3.5.20, erratum**: the printed `h = 0.25` and `h = 0.20` approximations
`0.20949 49432 96679 × 10⁻⁴⁴` and `0.20886 11645 34559 × 10⁻⁴⁴` are off by one unit in the last
digit; the rule gives `0.20949 49432 96678 49… × 10⁻⁴⁴` and `0.20886 11645 34559 92… × 10⁻⁴⁴`,
which round to `…96678` and `…34560`. -/
theorem dlmf_table_3_5_20_erratum :
    ¬ RoundsTo (erfcTrap 10 (1 / 4) 12) (209494943296679, 59) ∧
      RoundsTo (erfcTrap 10 (1 / 4) 12) (209494943296678, 59) ∧
      ¬ RoundsTo (erfcTrap 10 (1 / 5) 15) (208861164534559, 59) ∧
      RoundsTo (erfcTrap 10 (1 / 5) 15) (208861164534560, 59) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := trap_not_roundsTo (h := 1 / 4) (K := 12) (M := 209494943296679)
      (by decide +kernel) (by decide +kernel)
    push_cast at this; exact this
  · have := trap_roundsTo (h := 1 / 4) (K := 12) (M := 209494943296678)
      (by decide +kernel) (by decide +kernel)
    push_cast at this; exact this
  · have := trap_not_roundsTo (h := 1 / 5) (K := 15) (M := 208861164534559)
      (by decide +kernel) (by decide +kernel)
    push_cast at this; exact this
  · have := trap_roundsTo (h := 1 / 5) (K := 15) (M := 208861164534560)
      (by decide +kernel) (by decide +kernel)
    push_cast at this; exact this

/-- **Table 3.5.20**, column `n`: the number of function values `e^{−λ² tan²(kh/2)}`,
`0 ≤ k ≤ K` (evenness), larger than `10⁻¹⁵` is `5, 6, 8, 11`. -/
theorem dlmf_table_3_5_20_n :
    ((range 13).filter fun k : ℕ => (1 : ℝ) / 10 ^ 15 < erfcPathIntegrand 10 (k * (1 / 4))).card
      = 5 ∧
    ((range 16).filter fun k : ℕ => (1 : ℝ) / 10 ^ 15 < erfcPathIntegrand 10 (k * (1 / 5))).card
      = 6 ∧
    ((range 21).filter fun k : ℕ => (1 : ℝ) / 10 ^ 15 < erfcPathIntegrand 10 (k * (3 / 20))).card
      = 8 ∧
    ((range 32).filter fun k : ℕ => (1 : ℝ) / 10 ^ 15 < erfcPathIntegrand 10 (k * (1 / 10))).card
      = 11 := by
  have hl : (10 : ℝ) ^ 2 = ((100 : ℚ) : ℝ) := by norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := count_sound (h := 1 / 4) (K := 12) (n := 5) (by decide +kernel) (by decide +kernel) hl
    push_cast at this; exact this
  · have := count_sound (h := 1 / 5) (K := 15) (n := 6) (by decide +kernel) (by decide +kernel) hl
    push_cast at this; exact this
  · have := count_sound (h := 3 / 20) (K := 20) (n := 8) (by decide +kernel) (by decide +kernel) hl
    push_cast at this; exact this
  · have := count_sound (h := 1 / 10) (K := 31) (n := 11) (by decide +kernel) (by decide +kernel)
      hl
    push_cast at this; exact this

/-- **Table 3.5.20**: "All digits shown in the approximation in the final row are correct":
`erfc 10` rounds to `0.20884 87583 76254 × 10⁻⁴⁴` (20 terms of 7.12.1, error at most the next
term), as does the `h = 0.10` row (`dlmf_table_3_5_20`). -/
theorem dlmf_table_3_5_20_erfc : RoundsTo (BZ.erfc 10) (208848758376254, 59) := by
  have hs := erfcEncl_sound (x := 10) (k := 20) (by decide +kernel)
  have := roundsTo_of_encl hs.1 hs.2 (M := 208848758376254) (d := 59) (by decide +kernel)
  push_cast at this; exact this

end Azurite.DLMF
