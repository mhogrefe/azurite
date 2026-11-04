/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section6Weber
import Azurite.DLMF.Chapter3.Section6OlverError
import Azurite.DLMF.Chapter3.Section5ContourTable
import Azurite.DLMF.Chapter3.Section5ComplexGaussExampleTable

/-!
# DLMF §3.6(vi), Table 3.6.1

The computation of Table 3.6.1 (Olver's algorithm for 3.6.14 from `w₀ = −0.56865 663`, `N = 16`)
in closed form: `eₙ = w₀ + (4/π)Sₙ`, `Sₙ = ∑_{j≤n, j odd} pⱼ` (`besS`, `olverE_weber`), and the back
substitution as a finite sum for any starting value (`olverW_eq_sum`, `olverW_zero_eq`). Every
printed quantity is `A + B/π` with exact rationals `A`, `B` (`olverE_weber_form`,
`olverT_weber_form`, `olverW_weber_form`), enclosed with `Real.pi_gt_d20`/`pi_lt_d20`
(`encAB`, `encMul`) and checked by `decide +kernel`.

* All printed `pₙ`, `eₙ`, `eₙ/(pₙp_{n+1})`, `wₙ` are the correctly rounded (8S) results of the
  computation (`dlmf_table_3_6_1`); the least `N ≥ 10` satisfying 3.6.9 is `16`
  (`dlmf_table_3_6_1_N`).
* The true values: `∫₀^π sin(sin θ) dθ` from 12 terms of its series (`integral_sin_sin_mem`),
  `𝐄₀(1) = −0.56865 663` (`dlmf_table_3_6_1_E0`), and `𝐄ₙ(1) = wₙ^{(30)}[𝐄₀(1)] + (𝐄₃₀(1)/p₃₀)pₙ`
  with `|𝐄₃₀(1)| ≤ 1` (`trueEnc_sound`).
* "The values of `wₙ` for `n = 1, …, 10` are the wanted values of `𝐄ₙ(1)`": true for
  `n = 2, …, 10` (`dlmf_table_3_6_1_wanted`). **Erratum**: not for `n = 1` — `𝐄₁(1) = 0.43816 2436…`
  rounds to `0.43816 244` (`dlmf_table_3_6_1_erratum_w1`; the starting value was itself rounded).
* The underlined digits for `n > 10` (`dlmf_table_3_6_1_digits`): consistent with the half-unit
  criterion for `n = 11, …, 14`; **erratum** for `n = 15`, where one more digit is in error.
-/

open Filter Topology Finset Real

namespace Azurite.DLMF

/-! ### Back substitution as a finite sum, for any starting value -/

/-- `wₙ^{(N)} = pₙ ∑_{s=n}^{N−1} eₛ/(pₛp_{s+1})` for `1 ≤ n ≤ N`, whatever `w₀` (no solution of
3.6.1 needed). -/
theorem olverW_eq_sum {a b c d : ℕ → ℂ} (w₀ : ℂ) {N : ℕ}
    (hp : ∀ n, 1 ≤ n → n ≤ N → olverP a b c n ≠ 0) {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ N) :
    olverW a b c d w₀ N n = olverP a b c n *
      ∑ s ∈ Ico n N, olverE a b c d w₀ s / (olverP a b c s * olverP a b c (s + 1)) := by
  have h310 := dlmf_3_6_10 (d := d) w₀ hp
  have key : ∀ k, k + 1 ≤ N → olverW a b c d w₀ N (N - k) = olverP a b c (N - k) *
      ∑ s ∈ Ico (N - k) N, olverE a b c d w₀ s / (olverP a b c s * olverP a b c (s + 1)) := by
    intro k
    induction k with
    | zero => intro _; simp [h310.1]
    | succ k ih =>
      intro hk
      have ih := ih (by omega)
      obtain ⟨m, hm⟩ : ∃ m, N - k = m + 1 := ⟨N - k - 1, by omega⟩
      have hNk : N - (k + 1) = m := by omega
      rw [hm] at ih
      rw [hNk]
      have e := h310.2 m (by omega)
      rw [ih] at e
      have hp1 := hp (m + 1) (by omega) (by omega)
      have hp0 := hp m (by omega) (by omega)
      rw [sum_eq_sum_Ico_succ_bot (by omega : m < N)]
      apply mul_left_cancel₀ hp1
      rw [e]
      field_simp
      ring
  have := key (N - n) (by omega)
  rwa [show N - (N - n) = n by omega] at this

/-- `w₀^{(N)} = w₀` (back substitution at `n = 0`, `p₀ = 0`, `p₁ = 1`). -/
theorem olverW_zero_eq {a b c d : ℕ → ℂ} (w₀ : ℂ) {N : ℕ} (hN : 1 ≤ N)
    (hp : ∀ n, 1 ≤ n → n ≤ N → olverP a b c n ≠ 0) : olverW a b c d w₀ N 0 = w₀ := by
  have := (dlmf_3_6_10 (d := d) w₀ hp).2 0 (by omega)
  simpa [olverE] using this

/-! ### The Weber computation in closed form -/

/-- `Sₙ = ∑_{j ≤ n, j odd} pⱼ`. -/
def besS : ℕ → ℤ
  | 0 => 0
  | m + 1 => besS m + if (m + 1) % 2 = 1 then besP (m + 1) else 0

/-- `eₙ = w₀ + (4/π) Sₙ` for 3.6.14 (3.6.8 with `dₙ = −(2/π)(1 − (−1)ⁿ)`). -/
theorem olverE_weber (w₀ : ℂ) (n : ℕ) :
    olverE besA besB besC weberD w₀ n = w₀ + 4 / π * (besS n : ℂ) := by
  induction n with
  | zero => simp [olverE, besS]
  | succ m ih =>
    simp only [olverE, besA, besC, one_mul, div_one, ih, besS, olverP_bes, weberD]
    rcases Nat.even_or_odd (m + 1) with h | h
    · have h2 : (m + 1) % 2 ≠ 1 := by rw [Nat.even_iff] at h; omega
      rw [h.neg_one_pow]
      simp only [h2, ↓reduceIte]
      push_cast; ring
    · have h2 : (m + 1) % 2 = 1 := Nat.odd_iff.mp h
      rw [h.neg_one_pow]
      simp only [h2, ↓reduceIte]
      push_cast; ring

/-! ### Exact rational forms `A + B/π` -/

/-- `∑_{j<m} f j` by structural recursion (for kernel evaluation). -/
def rsum (f : ℕ → ℚ) : ℕ → ℚ
  | 0 => 0
  | m + 1 => rsum f m + f m

theorem rsum_cast (f : ℕ → ℚ) (m : ℕ) : ((rsum f m : ℚ) : ℝ) = ∑ j ∈ range m, (f j : ℝ) := by
  induction m with
  | zero => simp [rsum]
  | succ m ih => rw [rsum, sum_range_succ, ← ih]; push_cast; ring

/-- The starting value `−0.56865 663` of Table 3.6.1. -/
def kQ : ℚ := -56865663 / 10 ^ 8

def pQ (n : ℕ) : ℚ := besP n

/-- `eₙ/(pₙp_{n+1}) = tAQ + tBQ/π`. -/
def tAQ (w : ℚ) (n : ℕ) : ℚ := w / (pQ n * pQ (n + 1))

def tBQ (n : ℕ) : ℚ := 4 * besS n / (pQ n * pQ (n + 1))

/-- `wₙ^{(N)} = wAQ + wBQ/π`. -/
def wAQ (w : ℚ) (N n : ℕ) : ℚ := pQ n * rsum (fun j => tAQ w (n + j)) (N - n)

def wBQ (N n : ℕ) : ℚ := pQ n * rsum (fun j => tBQ (n + j)) (N - n)

theorem olverE_weber_form (w : ℚ) (n : ℕ) :
    olverE besA besB besC weberD ((w : ℝ) : ℂ) n =
      (((w : ℝ) + ((4 * besS n : ℚ) : ℝ) * (1 / π) : ℝ) : ℂ) := by
  rw [olverE_weber]; push_cast; ring

theorem olverT_weber_form (w : ℚ) {n : ℕ} (hn : 1 ≤ n) :
    olverT besA besB besC weberD ((w : ℝ) : ℂ) n =
      ((((tAQ w n : ℚ) : ℝ) + ((tBQ n : ℚ) : ℝ) * (1 / π) : ℝ) : ℂ) := by
  have h1 : (besP n : ℂ) ≠ 0 := by rw [← olverP_bes]; exact olverP_bes_ne n hn
  have h2 : (besP (n + 1) : ℂ) ≠ 0 := by rw [← olverP_bes]; exact olverP_bes_ne _ (by omega)
  rw [olverT, olverE_weber, olverP_bes, olverP_bes]
  simp only [tAQ, tBQ, pQ]
  push_cast
  field_simp

theorem olverW_weber_form (w : ℚ) {N n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ N) :
    olverW besA besB besC weberD ((w : ℝ) : ℂ) N n =
      ((((wAQ w N n : ℚ) : ℝ) + ((wBQ N n : ℚ) : ℝ) * (1 / π) : ℝ) : ℂ) := by
  rw [olverW_eq_sum _ (fun k hk _ => olverP_bes_ne k hk) hn1 hn, sum_Ico_eq_sum_range]
  have hterm : ∀ j ∈ range (N - n), olverE besA besB besC weberD ((w : ℝ) : ℂ) (n + j) /
      (olverP besA besB besC (n + j) * olverP besA besB besC (n + j + 1)) =
      ((((tAQ w (n + j) : ℚ) : ℝ) + ((tBQ (n + j) : ℚ) : ℝ) * (1 / π) : ℝ) : ℂ) := fun j _ => by
    rw [← olverT, olverT_weber_form w (by omega)]
  rw [sum_congr rfl hterm, olverP_bes]
  simp only [wAQ, wBQ, Rat.cast_mul, rsum_cast, pQ, Rat.cast_intCast]
  push_cast
  rw [sum_add_distrib, ← sum_mul]
  ring

/-! ### Enclosures with `π` -/

def uLoQ : ℚ := 1 / piHiQ

def uHiQ : ℚ := 1 / piLoQ

theorem inv_pi_mem : ((uLoQ : ℚ) : ℝ) ≤ 1 / π ∧ 1 / π ≤ ((uHiQ : ℚ) : ℝ) := by
  have h1 := piLoQ_lt
  have h2 := pi_lt_piHiQ
  have h0 : (0 : ℝ) < piLoQ := by unfold piLoQ; norm_num
  simp only [uLoQ, uHiQ, Rat.cast_div, Rat.cast_one]
  exact ⟨one_div_le_one_div_of_le pi_pos h2.le, one_div_le_one_div_of_le h0 h1.le⟩

/-- An enclosure of `A + B u` for `u ∈ [uLo, uHi]`. -/
def encAB (A B : ℚ) : ℚ × ℚ :=
  (min (A + B * uLoQ) (A + B * uHiQ), max (A + B * uLoQ) (A + B * uHiQ))

theorem encAB_sound (A B : ℚ) :
    (((encAB A B).1 : ℚ) : ℝ) ≤ (A : ℝ) + (B : ℝ) * (1 / π) ∧
      (A : ℝ) + (B : ℝ) * (1 / π) ≤ (((encAB A B).2 : ℚ) : ℝ) := by
  obtain ⟨h1, h2⟩ := inv_pi_mem
  simp only [encAB]
  push_cast
  rcases le_total 0 (B : ℝ) with hB | hB
  · constructor
    · exact (min_le_left _ _).trans (by nlinarith)
    · exact le_trans (by nlinarith) (le_max_right _ _)
  · constructor
    · exact (min_le_right _ _).trans (by nlinarith)
    · exact le_trans (by nlinarith) (le_max_left _ _)

/-- An enclosure of a product `X u`, `X ∈ [x₁, x₂]`, `u ∈ [uLo, uHi]`, `uLo > 0`. -/
def encMul (x : ℚ × ℚ) : ℚ × ℚ :=
  (min (min (x.1 * uLoQ) (x.1 * uHiQ)) (min (x.2 * uLoQ) (x.2 * uHiQ)),
    max (max (x.1 * uLoQ) (x.1 * uHiQ)) (max (x.2 * uLoQ) (x.2 * uHiQ)))

theorem encMul_sound {x : ℚ × ℚ} {X : ℝ} (h1 : ((x.1 : ℚ) : ℝ) ≤ X) (h2 : X ≤ ((x.2 : ℚ) : ℝ)) :
    (((encMul x).1 : ℚ) : ℝ) ≤ X * (1 / π) ∧ X * (1 / π) ≤ (((encMul x).2 : ℚ) : ℝ) := by
  obtain ⟨hu1, hu2⟩ := inv_pi_mem
  have hu0 : 0 < 1 / π := by positivity
  simp only [encMul]
  push_cast
  -- `X u` lies between `x₁ u` and `x₂ u`, and each `xᵢ u` between `xᵢ uLo` and `xᵢ uHi`
  have hA : (x.1 : ℝ) * (1 / π) ≤ X * (1 / π) := mul_le_mul_of_nonneg_right h1 hu0.le
  have hB : X * (1 / π) ≤ (x.2 : ℝ) * (1 / π) := mul_le_mul_of_nonneg_right h2 hu0.le
  have e1 : min ((x.1 : ℝ) * uLoQ) ((x.1 : ℝ) * uHiQ) ≤ (x.1 : ℝ) * (1 / π) := by
    rcases le_total 0 (x.1 : ℝ) with h | h
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left hu1 h)
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left hu2 h)
  have e2 : (x.2 : ℝ) * (1 / π) ≤ max ((x.2 : ℝ) * uLoQ) ((x.2 : ℝ) * uHiQ) := by
    rcases le_total 0 (x.2 : ℝ) with h | h
    · exact (mul_le_mul_of_nonneg_left hu2 h).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonpos_left hu1 h).trans (le_max_left _ _)
  exact ⟨(min_le_left _ _).trans (e1.trans hA), hB.trans (e2.trans (le_max_right _ _))⟩

/-! ### Rounding to 8 significant figures -/

/-- `v` rounds to `M × 10^E` (half a unit of the last digit). -/
def RoundsSig (v : ℂ) (M E : ℤ) : Prop :=
  ‖v - (((M : ℝ) * (10 : ℝ) ^ E : ℝ) : ℂ)‖ ≤ (10 : ℝ) ^ E / 2

def roundsOK (e : ℚ × ℚ) (M E : ℤ) : Bool :=
  decide ((M : ℚ) * 10 ^ E - 10 ^ E / 2 ≤ e.1) && decide (e.2 ≤ (M : ℚ) * 10 ^ E + 10 ^ E / 2)

def roundsBad (e : ℚ × ℚ) (M E : ℤ) : Bool :=
  decide (e.2 < (M : ℚ) * 10 ^ E - 10 ^ E / 2) || decide ((M : ℚ) * 10 ^ E + 10 ^ E / 2 < e.1)

theorem roundsSig_of_ok {x : ℝ} {e : ℚ × ℚ} {M E : ℤ} (h1 : ((e.1 : ℚ) : ℝ) ≤ x)
    (h2 : x ≤ ((e.2 : ℚ) : ℝ)) (h : roundsOK e M E = true) : RoundsSig (x : ℂ) M E := by
  simp only [roundsOK, Bool.and_eq_true, decide_eq_true_eq] at h
  have h3 := (Rat.cast_le (K := ℝ)).mpr h.1
  have h4 := (Rat.cast_le (K := ℝ)).mpr h.2
  push_cast at h3 h4
  unfold RoundsSig
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith

theorem not_roundsSig_of_bad {x : ℝ} {e : ℚ × ℚ} {M E : ℤ} (h1 : ((e.1 : ℚ) : ℝ) ≤ x)
    (h2 : x ≤ ((e.2 : ℚ) : ℝ)) (h : roundsBad e M E = true) : ¬ RoundsSig (x : ℂ) M E := by
  simp only [roundsBad, Bool.or_eq_true, decide_eq_true_eq] at h
  unfold RoundsSig
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le, not_and_or]
  rcases h with h | h
  · have h3 := (Rat.cast_lt (K := ℝ)).mpr h
    push_cast at h3
    left; linarith
  · have h3 := (Rat.cast_lt (K := ℝ)).mpr h
    push_cast at h3
    right; linarith

/-! ### Table 3.6.1: the printed results of the computation -/

/-- The rows `n = 1, …, 16` of Table 3.6.1: `(n, pₙ, eₙ, eₙ/(pₙp_{n+1}), wₙ)`, each entry as
`(M, E)` meaning `M × 10^E` (8 significant figures). -/
def table361 : List (ℕ × (ℤ × ℤ) × (ℤ × ℤ) × (ℤ × ℤ) × (ℤ × ℤ)) :=
  [(1, (10000000, -7), (70458291, -8), (35229146, -8), (43816243, -8)),
   (2, (20000000, -7), (70458291, -8), (50327351, -9), (17174195, -8)),
   (3, (70000000, -7), (96172597, -7), (34347356, -9), (24880538, -8)),
   (4, (40000000, -6), (96172597, -7), (76815174, -11), (47850795, -9)),
   (5, (31300000, -5), (40814124, -5), (42199534, -11), (13400098, -8)),
   (6, (30900000, -4), (40814124, -5), (35924754, -13), (18919443, -9)),
   (7, (36767000, -3), (47221340, -3), (25102029, -13), (93032343, -9)),
   (8, (51164800, -2), (47221340, -3), (11324804, -15), (10293811, -9)),
   (9, (81496010, -1), (10423616, 0), (87496485, -16), (71668638, -9)),
   (10, (14618117, 1), (10423616, 0), (24457824, -18), (65021292, -10)),
   (11, (29154738, 2), (37225201, 2), (19952026, -18), (58373946, -9)),
   (12, (63994242, 3), (37225201, 2), (37946279, -21), (44851387, -10)),
   (13, (15329463, 5), (19555304, 5), (32057909, -21), (49269383, -9)),
   (14, (39792611, 6), (19555304, 5), (44167174, -24), (32792861, -10)),
   (15, (11126602, 8), (14186384, 8), (38242250, -24), (42550628, -9)),
   (16, (33340012, 9), (14186384, 8), (39924861, -27), (0, 0))]

def rowOK (r : ℕ × (ℤ × ℤ) × (ℤ × ℤ) × (ℤ × ℤ) × (ℤ × ℤ)) : Bool :=
  decide (1 ≤ r.1 ∧ r.1 ≤ 16) &&
  roundsOK (encAB (pQ r.1) 0) r.2.1.1 r.2.1.2 &&
  roundsOK (encAB kQ (4 * besS r.1)) r.2.2.1.1 r.2.2.1.2 &&
  roundsOK (encAB (tAQ kQ r.1) (tBQ r.1)) r.2.2.2.1.1 r.2.2.2.1.2 &&
  roundsOK (encAB (wAQ kQ 16 r.1) (wBQ 16 r.1)) r.2.2.2.2.1 r.2.2.2.2.2

theorem table361_ok : table361.all rowOK = true := by decide +kernel

/-- The computation of Table 3.6.1: Olver's algorithm (§3.6(v)) for 3.6.14 from
`w₀ = −0.56865 663`, with `N = 16`. -/
noncomputable abbrev tabW0 : ℂ := ((kQ : ℝ) : ℂ)

/-- **Table 3.6.1**: every printed `pₙ`, `eₙ`, `eₙ/(pₙp_{n+1})` and `wₙ` (`n = 1, …, 16`) is the
correctly rounded (8S) result of Olver's algorithm for 3.6.14 started from
`w₀ = −0.56865 663` with `N = 16`; row `0` is exact (`p₀ = 0`, `e₀ = w₀ = −0.56865 663`). -/
theorem dlmf_table_3_6_1 :
    (∀ r ∈ table361,
      RoundsSig (olverP besA besB besC r.1) r.2.1.1 r.2.1.2 ∧
      RoundsSig (olverE besA besB besC weberD tabW0 r.1) r.2.2.1.1 r.2.2.1.2 ∧
      RoundsSig (olverT besA besB besC weberD tabW0 r.1) r.2.2.2.1.1 r.2.2.2.1.2 ∧
      RoundsSig (olverW besA besB besC weberD tabW0 16 r.1) r.2.2.2.2.1 r.2.2.2.2.2) ∧
    olverP besA besB besC 0 = 0 ∧ olverE besA besB besC weberD tabW0 0 = tabW0 ∧
      olverW besA besB besC weberD tabW0 16 0 = tabW0 := by
  refine ⟨fun r hr => ?_, rfl, rfl, olverW_zero_eq _ (by norm_num) fun k hk _ => olverP_bes_ne k hk⟩
  have h := List.all_eq_true.mp table361_ok r hr
  simp only [rowOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h16⟩, hp⟩, he⟩, ht⟩, hw⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e := encAB_sound (pQ r.1) 0
    rw [olverP_bes]
    have : ((besP r.1 : ℂ)) = (((pQ r.1 : ℚ) : ℝ) + ((0 : ℚ) : ℝ) * (1 / π) : ℝ) := by
      simp [pQ]
    rw [this]
    exact roundsSig_of_ok e.1 e.2 hp
  · have e := encAB_sound kQ (4 * besS r.1)
    rw [olverE_weber_form]
    exact roundsSig_of_ok e.1 e.2 he
  · have e := encAB_sound (tAQ kQ r.1) (tBQ r.1)
    rw [olverT_weber_form _ h1]
    exact roundsSig_of_ok e.1 e.2 ht
  · have e := encAB_sound (wAQ kQ 16 r.1) (wBQ 16 r.1)
    rw [olverW_weber_form _ h1 h16]
    exact roundsSig_of_ok e.1 e.2 hw

/-! ### "The least value of `N` that satisfies (3.6.9) is found to be 16" -/

def tLo (n : ℕ) : ℚ := (encAB (tAQ kQ n) (tBQ n)).1

def tHi (n : ℕ) : ℚ := (encAB (tAQ kQ n) (tBQ n)).2

theorem norm_olverT_tab {n : ℕ} (hn : 1 ≤ n) (h0 : 0 ≤ tLo n) :
    ((tLo n : ℚ) : ℝ) ≤ ‖olverT besA besB besC weberD tabW0 n‖ ∧
      ‖olverT besA besB besC weberD tabW0 n‖ ≤ ((tHi n : ℚ) : ℝ) := by
  have e := encAB_sound (tAQ kQ n) (tBQ n)
  rw [olverT_weber_form _ hn, Complex.norm_real, Real.norm_eq_abs]
  have h0' : (0 : ℝ) ≤ ((tLo n : ℚ) : ℝ) := by exact_mod_cast h0
  rw [abs_of_nonneg (h0'.trans e.1)]
  exact e

/-- **DLMF §3.6(vi)**, Example 2: with `M = 10` and `ε = ½ × 10⁻⁸`, the least `N ≥ M` satisfying
3.6.9 `|e_N/(p_Np_{N+1})| ≤ ε min_{1≤n≤M} |eₙ/(pₙp_{n+1})|` is `N = 16`. -/
theorem dlmf_table_3_6_1_N :
    (∀ N, 10 ≤ N → N < 16 → (1 / 2 * 10 ^ (-8 : ℤ) : ℝ) *
        (Icc 1 10).inf' ⟨1, by simp⟩ (fun n => ‖olverT besA besB besC weberD tabW0 n‖) <
      ‖olverT besA besB besC weberD tabW0 N‖) ∧
    ‖olverT besA besB besC weberD tabW0 16‖ ≤ (1 / 2 * 10 ^ (-8 : ℤ) : ℝ) *
      (Icc 1 10).inf' ⟨1, by simp⟩ (fun n => ‖olverT besA besB besC weberD tabW0 n‖) := by
  have hpos : ∀ n, 1 ≤ n → n ≤ 16 → 0 ≤ tLo n := by
    intro n h1 h2
    interval_cases n <;> decide +kernel
  have hb : ∀ n, 1 ≤ n → n ≤ 16 → _ := fun n h1 h2 => norm_olverT_tab h1 (hpos n h1 h2)
  -- the minimum over `1 ≤ n ≤ 10` is attained at `n = 10`
  have hmin : (Icc 1 10).inf' ⟨1, by simp⟩ (fun n => ‖olverT besA besB besC weberD tabW0 n‖) =
      ‖olverT besA besB besC weberD tabW0 10‖ := by
    refine le_antisymm (inf'_le _ (by simp)) (le_inf' _ _ fun n hn => ?_)
    simp only [mem_Icc] at hn
    rcases eq_or_ne n 10 with rfl | h10
    · exact le_rfl
    have hle : tHi 10 ≤ tLo n := by
      obtain ⟨h1, h2⟩ := hn
      have h3 : n ≤ 9 := by omega
      interval_cases n <;> decide +kernel
    have := (Rat.cast_le (K := ℝ)).mpr hle
    exact ((hb 10 (by norm_num) (by norm_num)).2.trans this).trans (hb n hn.1 (by omega)).1
  rw [hmin]
  have hε : (1 / 2 * 10 ^ (-8 : ℤ) : ℝ) = ((1 / 2 * 10 ^ (-8 : ℤ) : ℚ) : ℝ) := by push_cast; rfl
  rw [hε]
  have h10 := hb 10 (by norm_num) (by norm_num)
  have hε0 : (0 : ℝ) ≤ ((1 / 2 * 10 ^ (-8 : ℤ) : ℚ) : ℝ) := by positivity
  refine ⟨fun N h1 h2 => ?_, ?_⟩
  · have hlt : 1 / 2 * 10 ^ (-8 : ℤ) * tHi 10 < tLo N := by
      interval_cases N <;> decide +kernel
    have := (Rat.cast_lt (K := ℝ)).mpr hlt
    push_cast at this
    calc ((1 / 2 * 10 ^ (-8 : ℤ) : ℚ) : ℝ) * ‖olverT besA besB besC weberD tabW0 10‖
        ≤ ((1 / 2 * 10 ^ (-8 : ℤ) : ℚ) : ℝ) * ((tHi 10 : ℚ) : ℝ) :=
          mul_le_mul_of_nonneg_left h10.2 hε0
      _ < ((tLo N : ℚ) : ℝ) := by push_cast; exact this
      _ ≤ _ := (hb N (by omega) (by omega)).1
  · have hle : tHi 16 ≤ 1 / 2 * 10 ^ (-8 : ℤ) * tLo 10 := by decide +kernel
    have := (Rat.cast_le (K := ℝ)).mpr hle
    calc ‖olverT besA besB besC weberD tabW0 16‖ ≤ ((tHi 16 : ℚ) : ℝ) :=
          (hb 16 (by norm_num) (by norm_num)).2
      _ ≤ ((1 / 2 * 10 ^ (-8 : ℤ) * tLo 10 : ℚ) : ℝ) := this
      _ ≤ _ := by
          push_cast
          exact mul_le_mul_of_nonneg_left h10.1 (by positivity)

/-! ### The true values `𝐄ₙ(1)` -/

/-- The terms of the series for `∫₀^π sin(sin θ) dθ`: `a₀ = 2`, `a_{k+1} = −aₖ/(2k + 3)²`. -/
def aQ : ℕ → ℚ
  | 0 => 2
  | k + 1 => -aQ k / (2 * k + 3) ^ 2

theorem weberE0Term_succ (k : ℕ) :
    weberE0Term (k + 1) = -weberE0Term k / (2 * (k : ℝ) + 3) ^ 2 := by
  unfold weberE0Term
  rw [prod_range_succ, show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 by ring, Nat.factorial_succ,
    Nat.factorial_succ]
  have h1 : (((2 * k + 1).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem weberE0Term_eq (k : ℕ) : weberE0Term k = ((aQ k : ℚ) : ℝ) := by
  induction k with
  | zero => simp [weberE0Term, aQ]
  | succ k ih => rw [weberE0Term_succ, ih, aQ]; push_cast; ring

def ILo : ℚ := rsum aQ 12 - 2 * |aQ 12|

def IHi : ℚ := rsum aQ 12 + 2 * |aQ 12|

/-- `∫₀^π sin(sin θ) dθ ∈ [ILo, IHi]` (12 terms; the terms decrease at least geometrically). -/
theorem integral_sin_sin_mem :
    ((ILo : ℚ) : ℝ) ≤ ∫ θ in (0 : ℝ)..π, sin (sin θ) ∧
      ∫ θ in (0 : ℝ)..π, sin (sin θ) ≤ ((IHi : ℚ) : ℝ) := by
  have hs := hasSum_weberE0Term
  have hr : ∀ j, 12 ≤ j → |weberE0Term (j + 1)| ≤ |weberE0Term j| / 2 := fun j _ => by
    rw [weberE0Term_succ, abs_div, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < (2 * j + 3) ^ 2)]
    gcongr
    have : (0 : ℝ) ≤ j := j.cast_nonneg
    nlinarith
  have h := abs_tsum_sub_sum_le hs.summable hr
  rw [hs.tsum_eq] at h
  have hsum : ∑ j ∈ range 12, weberE0Term j = ((rsum aQ 12 : ℚ) : ℝ) := by
    rw [rsum_cast]; exact sum_congr rfl fun j _ => weberE0Term_eq j
  rw [hsum, weberE0Term_eq] at h
  simp only [ILo, IHi]
  push_cast
  constructor <;> linarith [(abs_le.mp h).1, (abs_le.mp h).2]

/-- `𝐄₀(1) ∈ encMul (−IHi, −ILo)`. -/
theorem weberE_zero_mem :
    (((encMul (-IHi, -ILo)).1 : ℚ) : ℝ) ≤ weberE 0 1 ∧
      weberE 0 1 ≤ (((encMul (-IHi, -ILo)).2 : ℚ) : ℝ) := by
  obtain ⟨h1, h2⟩ := integral_sin_sin_mem
  have := encMul_sound (x := (-IHi, -ILo)) (X := -∫ θ in (0 : ℝ)..π, sin (sin θ))
    (by push_cast; linarith) (by push_cast; linarith)
  rw [weberE_zero_one, show -(1 / π) * ∫ θ in (0 : ℝ)..π, sin (sin θ) =
    (-∫ θ in (0 : ℝ)..π, sin (sin θ)) * (1 / π) by ring]
  exact this

theorem olverT_weber_form_real (x : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    olverT besA besB besC weberD (x : ℂ) n =
      ((x * ((tAQ 1 n : ℚ) : ℝ) + ((tBQ n : ℚ) : ℝ) * (1 / π) : ℝ) : ℂ) := by
  have h1 : (besP n : ℂ) ≠ 0 := by rw [← olverP_bes]; exact olverP_bes_ne n hn
  have h2 : (besP (n + 1) : ℂ) ≠ 0 := by rw [← olverP_bes]; exact olverP_bes_ne _ (by omega)
  rw [olverT, olverE_weber, olverP_bes, olverP_bes]
  simp only [tAQ, tBQ, pQ]
  push_cast
  field_simp

theorem olverW_weber_form_real (x : ℝ) {N n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ N) :
    olverW besA besB besC weberD (x : ℂ) N n =
      ((x * ((wAQ 1 N n : ℚ) : ℝ) + ((wBQ N n : ℚ) : ℝ) * (1 / π) : ℝ) : ℂ) := by
  rw [olverW_eq_sum _ (fun k hk _ => olverP_bes_ne k hk) hn1 hn, sum_Ico_eq_sum_range]
  have hterm : ∀ j ∈ range (N - n), olverE besA besB besC weberD (x : ℂ) (n + j) /
      (olverP besA besB besC (n + j) * olverP besA besB besC (n + j + 1)) =
      ((x * ((tAQ 1 (n + j) : ℚ) : ℝ) + ((tBQ (n + j) : ℚ) : ℝ) * (1 / π) : ℝ) : ℂ) :=
    fun j _ => by rw [← olverT, olverT_weber_form_real x (by omega)]
  rw [sum_congr rfl hterm, olverP_bes]
  simp only [wAQ, wBQ, Rat.cast_mul, rsum_cast, pQ, Rat.cast_intCast]
  push_cast
  rw [sum_add_distrib, ← sum_mul, ← mul_sum]
  ring

/-- The enclosure of `𝐄ₙ(1)` from `𝐄ₙ(1) = w_n^{(30)}[𝐄₀(1)] + (𝐄₃₀(1)/p₃₀) pₙ`, `|𝐄₃₀(1)| ≤ 1`. -/
def trueEnc (n : ℕ) : ℚ × ℚ :=
  let e := encMul (wBQ 30 n - IHi * wAQ 1 30 n, wBQ 30 n - ILo * wAQ 1 30 n)
  (e.1 - |pQ n| / |pQ 30|, e.2 + |pQ n| / |pQ 30|)

theorem trueEnc_sound {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 30) (hα : 0 ≤ wAQ 1 30 n) :
    (((trueEnc n).1 : ℚ) : ℝ) ≤ weberE n 1 ∧ weberE n 1 ≤ (((trueEnc n).2 : ℚ) : ℝ) := by
  have hW := olverW_eq besA_ne dlmf_3_6_14 (N := 30) (by norm_num)
    (fun k hk _ => olverP_bes_ne k hk) hn
  have h0 : weberW 0 = ((weberE 0 1 : ℝ) : ℂ) := by simp [weberW]
  rw [h0, olverW_weber_form_real _ hn1 hn] at hW
  obtain ⟨hI1, hI2⟩ := integral_sin_sin_mem
  have hα' : (0 : ℝ) ≤ ((wAQ 1 30 n : ℚ) : ℝ) := by exact_mod_cast hα
  -- `𝐄ₙ(1) = (β − Iα)/π + ρₙ`
  set I := ∫ θ in (0 : ℝ)..π, sin (sin θ)
  have hE0 : weberE 0 1 = (-I) * (1 / π) := by rw [weberE_zero_one]; ring
  have hX := encMul_sound (x := (wBQ 30 n - IHi * wAQ 1 30 n, wBQ 30 n - ILo * wAQ 1 30 n))
    (X := ((wBQ 30 n : ℚ) : ℝ) - I * ((wAQ 1 30 n : ℚ) : ℝ))
    (by push_cast; nlinarith) (by push_cast; nlinarith)
  have hp30 : (besP 30 : ℝ) ≠ 0 := by
    have := olverP_bes_ne 30 (by norm_num); rw [olverP_bes] at this; exact_mod_cast this
  have hW' : weberE 0 1 * ((wAQ 1 30 n : ℚ) : ℝ) + ((wBQ 30 n : ℚ) : ℝ) * (1 / π) =
      weberE n 1 - weberE 30 1 / besP 30 * besP n := by
    rw [olverP_bes, olverP_bes] at hW
    simp only [weberW] at hW
    exact_mod_cast hW
  have hreal : weberE n 1 = (((wBQ 30 n : ℚ) : ℝ) - I * ((wAQ 1 30 n : ℚ) : ℝ)) * (1 / π) +
      weberE 30 1 / besP 30 * besP n := by
    rw [hE0] at hW'
    linear_combination -hW'
  have hρ : |weberE 30 1 / besP 30 * besP n| ≤ |((pQ n : ℚ) : ℝ)| / |((pQ 30 : ℚ) : ℝ)| := by
    simp only [pQ, Rat.cast_intCast]
    rw [abs_mul, abs_div]
    have := abs_weberE_le 30 1
    calc |weberE 30 1| / |(besP 30 : ℝ)| * |(besP n : ℝ)|
        ≤ 1 / |(besP 30 : ℝ)| * |(besP n : ℝ)| := by
          gcongr
      _ = _ := by ring
  simp only [trueEnc]
  push_cast
  constructor
  · linarith [(abs_le.mp hρ).1, hX.1]
  · linarith [(abs_le.mp hρ).2, hX.2]

/-! ### DLMF's claims about the true values -/

/-- **DLMF §3.6(vi)**: the starting value `𝐄₀(1) = −0.56865 663` (8S), from the Maclaurin series. -/
theorem dlmf_table_3_6_1_E0 : RoundsSig (weberW 0) (-56865663) (-8) := by
  have h0 : weberW 0 = ((weberE 0 1 : ℝ) : ℂ) := by simp [weberW]
  rw [h0]
  exact roundsSig_of_ok (e := encMul (-IHi, -ILo)) weberE_zero_mem.1 weberE_zero_mem.2
    (by decide +kernel)

/-- **DLMF §3.6(vi)**: for `n = 2, …, 10` the printed `wₙ` are `𝐄ₙ(1)` to 8S. -/
theorem dlmf_table_3_6_1_wanted :
    ∀ r ∈ table361, 2 ≤ r.1 → r.1 ≤ 10 → RoundsSig (weberW r.1) r.2.2.2.2.1 r.2.2.2.2.2 := by
  intro r hr h2 h10
  have hα : 0 ≤ wAQ 1 30 r.1 := by
    simp only [table361, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;> first | omega | decide +kernel
  have hb := trueEnc_sound (n := r.1) (by omega) (by omega) hα
  refine roundsSig_of_ok hb.1 hb.2 ?_
  simp only [table361, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;> first | omega | decide +kernel

/-- **Erratum**: the printed `w₁ = 0.43816 243` is not `𝐄₁(1)` to 8S (`𝐄₁(1) = 0.43816 2436…`
rounds to `0.43816 244`): the starting value `𝐄₀(1)` was itself rounded to 8S. -/
theorem dlmf_table_3_6_1_erratum_w1 :
    ¬ RoundsSig (weberW 1) 43816243 (-8) ∧ RoundsSig (weberW 1) 43816244 (-8) := by
  have hb := trueEnc_sound (n := 1) le_rfl (by norm_num) (by decide +kernel)
  exact ⟨not_roundsSig_of_bad hb.1 hb.2 (by decide +kernel),
    roundsSig_of_ok hb.1 hb.2 (by decide +kernel)⟩

def closeOK (e : ℚ × ℚ) (P T : ℚ) : Bool := decide (P - T ≤ e.1) && decide (e.2 ≤ P + T)

def farOK (e : ℚ × ℚ) (P T : ℚ) : Bool := decide (e.2 < P - T) || decide (P + T < e.1)

theorem close_of_ok {x : ℝ} {e : ℚ × ℚ} {P T : ℚ} (h1 : ((e.1 : ℚ) : ℝ) ≤ x)
    (h2 : x ≤ ((e.2 : ℚ) : ℝ)) (h : closeOK e P T = true) : |x - P| ≤ T := by
  simp only [closeOK, Bool.and_eq_true, decide_eq_true_eq] at h
  have h3 := (Rat.cast_le (K := ℝ)).mpr h.1
  have h4 := (Rat.cast_le (K := ℝ)).mpr h.2
  push_cast at h3 h4
  rw [abs_le]; constructor <;> linarith

theorem far_of_ok {x : ℝ} {e : ℚ × ℚ} {P T : ℚ} (h1 : ((e.1 : ℚ) : ℝ) ≤ x)
    (h2 : x ≤ ((e.2 : ℚ) : ℝ)) (h : farOK e P T = true) : (T : ℝ) < |x - P| := by
  simp only [farOK, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · have h3 := (Rat.cast_lt (K := ℝ)).mpr h
    push_cast at h3
    exact lt_of_lt_of_le (by linarith) (neg_le_abs (x - P))
  · have h3 := (Rat.cast_lt (K := ℝ)).mpr h
    push_cast at h3
    exact lt_of_lt_of_le (by linarith) (le_abs_self (x - P))

/-- **DLMF §3.6(vi)** ("for `n > 10` … the underlined digits are in error"): a digit of the printed
`wₙ` is in error when `|wₙ − 𝐄ₙ(1)|` exceeds half a unit in its place. For `n = 11` all digits are
correct; for `n = 12, 13, 14` the correct digits end exactly where DLMF's underlining begins
(at `10⁻⁹`, `10⁻⁷`, `10⁻⁶`). **Erratum**: for `n = 15` the digit in the place `10⁻⁴` is
already in error (`|w₁₅ − 𝐄₁₅(1)| = 0.84 × 10⁻⁴`), whereas DLMF underlines only from `10⁻⁵`. -/
theorem dlmf_table_3_6_1_digits :
    |weberE 11 1 - ((58373946 / 10 ^ 9 : ℚ) : ℝ)| ≤ ((1 / 2 / 10 ^ 9 : ℚ) : ℝ) ∧
    (|weberE 12 1 - ((44851387 / 10 ^ 10 : ℚ) : ℝ)| ≤ ((1 / 2 / 10 ^ 8 : ℚ) : ℝ) ∧
      ((1 / 2 / 10 ^ 9 : ℚ) : ℝ) < |weberE 12 1 - ((44851387 / 10 ^ 10 : ℚ) : ℝ)|) ∧
    (|weberE 13 1 - ((49269383 / 10 ^ 9 : ℚ) : ℝ)| ≤ ((1 / 2 / 10 ^ 6 : ℚ) : ℝ) ∧
      ((1 / 2 / 10 ^ 7 : ℚ) : ℝ) < |weberE 13 1 - ((49269383 / 10 ^ 9 : ℚ) : ℝ)|) ∧
    (|weberE 14 1 - ((32792861 / 10 ^ 10 : ℚ) : ℝ)| ≤ ((1 / 2 / 10 ^ 5 : ℚ) : ℝ) ∧
      ((1 / 2 / 10 ^ 6 : ℚ) : ℝ) < |weberE 14 1 - ((32792861 / 10 ^ 10 : ℚ) : ℝ)|) ∧
    (|weberE 15 1 - ((42550628 / 10 ^ 9 : ℚ) : ℝ)| ≤ ((1 / 2 / 10 ^ 3 : ℚ) : ℝ) ∧
      ((1 / 2 / 10 ^ 4 : ℚ) : ℝ) < |weberE 15 1 - ((42550628 / 10 ^ 9 : ℚ) : ℝ)|) := by
  have b := fun n (h1 : 1 ≤ n) (h2 : n ≤ 30) (hα : 0 ≤ wAQ 1 30 n) => trueEnc_sound h1 h2 hα
  have b11 := b 11 (by norm_num) (by norm_num) (by decide +kernel)
  have b12 := b 12 (by norm_num) (by norm_num) (by decide +kernel)
  have b13 := b 13 (by norm_num) (by norm_num) (by decide +kernel)
  have b14 := b 14 (by norm_num) (by norm_num) (by decide +kernel)
  have b15 := b 15 (by norm_num) (by norm_num) (by decide +kernel)
  push_cast at b11 b12 b13 b14 b15
  refine ⟨close_of_ok b11.1 b11.2 (by decide +kernel),
    ⟨close_of_ok b12.1 b12.2 (by decide +kernel), far_of_ok b12.1 b12.2 (by decide +kernel)⟩,
    ⟨close_of_ok b13.1 b13.2 (by decide +kernel), far_of_ok b13.1 b13.2 (by decide +kernel)⟩,
    ⟨close_of_ok b14.1 b14.2 (by decide +kernel), far_of_ok b14.1 b14.2 (by decide +kernel)⟩,
    ⟨close_of_ok b15.1 b15.2 (by decide +kernel), far_of_ok b15.1 b15.2 (by decide +kernel)⟩⟩

end Azurite.DLMF
