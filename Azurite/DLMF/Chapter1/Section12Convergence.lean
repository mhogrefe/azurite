/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section12
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# DLMF §1.12(v): Convergence of Continued Fractions

Formalizations of <https://dlmf.nist.gov/1.12.v>.

* `CfConvergent`: the convergents tend to a finite limit.
* **Pringsheim's theorem** (1.12.25, `dlmf_1_12_25`). Assume `b₀ = 0` and `|bₙ| ≥ |aₙ| + 1`. Then
  no zero denominator occurs, `|Cₙ| < 1`, and `Cₙ → C` with `|C| ≤ 1`.
  * Proof: `|Bₙ| − |B_{n−1}| ≥ ∏ |a_k|` (`pringsheim_denom`), so
    `|C_{n+1} − Cₙ| ≤ 1/|Bₙ| − 1/|B_{n+1}|`, and the series telescopes.
* **Van Vleck's theorem, sector part** (1.12.26–1.12.27, `dlmf_1_12_27`). Assume
  `−π/2 + δ < ph bₙ < π/2 − δ`. Then the tails and convergents of `1/(b₁ + 1/(b₂ + ⋯))` stay in
  the sector.
  * Proof: the sector `VVSector δ` is closed under addition and inversion, and
    `arg_sector_iff` translates the phase condition into a linear one.
  * If the fraction converges, then `|ph C| ≤ π/2` (`dlmf_1_12_v_vanVleck_ph`).
* The convergence statements of Van Vleck's theorem (even and odd parts converge; 1.12.28,
  `∑ |bₙ| = ∞`) are proved in `Section12VanVleck` (`dlmf_1_12_28`).
-/

open Filter Topology Finset Complex
open scoped Real

namespace Azurite.DLMF

/-- DLMF §1.12(v): a continued fraction *converges* if its convergents `Cₙ` tend to a finite
limit. -/
def CfConvergent (a b : ℕ → ℂ) : Prop := ∃ C, CfConverges a b C

/-! ### Pringsheim's theorem -/

theorem cfNonzero_of_pringsheim {a b : ℕ → ℂ} (h : ∀ n ≥ 1, ‖a n‖ + 1 ≤ ‖b n‖) :
    ∀ n w, ‖w‖ < 1 → CfNonzero a b n w := by
  intro n
  induction n with
  | zero => intro w _; trivial
  | succ n ih =>
    intro w hw
    have hb := h (n + 1) (by omega)
    have hgt : ‖a (n + 1)‖ < ‖b (n + 1) + w‖ := by
      have := norm_sub_le (b (n + 1) + w) w
      rw [add_sub_cancel_right] at this
      linarith
    have hne : b (n + 1) + w ≠ 0 := norm_pos_iff.mp ((norm_nonneg _).trans_lt hgt)
    refine ⟨hne, ih _ ?_⟩
    rw [norm_div]
    exact (div_lt_one (norm_pos_iff.mpr hne)).mpr hgt

/-- Under Pringsheim's condition, `|Bₙ| − |B_{n−1}| ≥ ∏_{k=1}^{n} |a_k|`. -/
theorem pringsheim_denom {a b : ℕ → ℂ} (h : ∀ n ≥ 1, ‖a n‖ + 1 ≤ ‖b n‖) (n : ℕ) :
    ∏ k ∈ Icc 1 n, ‖a k‖ ≤ ‖cfQ a b (n + 1)‖ - ‖cfQ a b n‖ := by
  induction n with
  | zero => simp [cfQ]
  | succ n ih =>
    rw [prod_Icc_succ_top (by omega)]
    have hb := h (n + 1) (by omega)
    have hrec : cfQ a b (n + 2) = b (n + 1) * cfQ a b (n + 1) + a (n + 1) * cfQ a b n := rfl
    have htri : ‖b (n + 1) * cfQ a b (n + 1)‖ ≤ ‖cfQ a b (n + 2)‖ + ‖a (n + 1) * cfQ a b n‖ := by
      rw [hrec]
      have := norm_sub_le (b (n + 1) * cfQ a b (n + 1) + a (n + 1) * cfQ a b n)
        (a (n + 1) * cfQ a b n)
      rwa [add_sub_cancel_right] at this
    rw [norm_mul, norm_mul] at htri
    have hQ0 := norm_nonneg (cfQ a b n)
    have hQ1 := norm_nonneg (cfQ a b (n + 1))
    have ha0 := norm_nonneg (a (n + 1))
    have hp0 : 0 ≤ ∏ k ∈ Icc 1 n, ‖a k‖ := prod_nonneg fun _ _ => norm_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left ih ha0]

theorem pringsheim_denom_ge_one {a b : ℕ → ℂ} (h : ∀ n ≥ 1, ‖a n‖ + 1 ≤ ‖b n‖) (n : ℕ) :
    1 ≤ ‖cfB a b n‖ := by
  induction n with
  | zero => simp [cfB, cfQ]
  | succ n ih =>
    have := pringsheim_denom h (n + 1)
    have hp0 : 0 ≤ ∏ k ∈ Icc 1 (n + 1), ‖a k‖ := prod_nonneg fun _ _ => norm_nonneg _
    simp only [cfB] at ih ⊢
    linarith

/-- **Pringsheim's theorem** (DLMF 1.12.25): `a₁/(b₁ + a₂/(b₂ + ⋯))` (`b₀ = 0`) converges if
`|bₙ| ≥ |aₙ| + 1`, `n = 1, 2, …`; then the convergents satisfy `|Cₙ| < 1` and `Cₙ → C` with
`|C| ≤ 1`. (No zero denominator occurs: `CfNonzero`.) -/
theorem dlmf_1_12_25 {a b : ℕ → ℂ} (hb0 : b 0 = 0) (h : ∀ n ≥ 1, ‖a n‖ + 1 ≤ ‖b n‖) :
    (∀ n, CfNonzero a b n 0) ∧ (∀ n, ‖cfConv a b n‖ < 1) ∧
      ∃ C, CfConverges a b C ∧ ‖C‖ ≤ 1 := by
  have hnz : ∀ n, CfNonzero a b n 0 := fun n => cfNonzero_of_pringsheim h n 0 (by simp)
  have hB : ∀ n, 1 ≤ ‖cfB a b n‖ := pringsheim_denom_ge_one h
  have hB0 : ∀ n, cfB a b n ≠ 0 := fun n => norm_pos_iff.mp (by linarith [hB n])
  set C : ℕ → ℂ := fun n => cfA a b n / cfB a b n with hCdef
  have hconv : ∀ n, cfConv a b n = C n := fun n => dlmf_1_12_4 a b (hnz n)
  have hC0 : C 0 = 0 := by simp [hCdef, cfA, cfB, cfP, cfQ, hb0]
  -- `|C_{n+1} − C_n| ≤ 1/|B_n| − 1/|B_{n+1}|`
  have hdiff : ∀ n, ‖C (n + 1) - C n‖ ≤ 1 / ‖cfB a b n‖ - 1 / ‖cfB a b (n + 1)‖ := by
    intro n
    have h8 := dlmf_1_12_8 a b n (hB0 n) (hB0 (n + 1))
    simp only [hCdef]
    rw [h8, norm_div, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      norm_prod]
    have hp := pringsheim_denom h (n + 1)
    have h1 := hB n
    have h2 := hB (n + 1)
    simp only [cfB] at h1 h2 ⊢
    rw [div_le_iff₀ (by positivity)]
    field_simp
    linarith
  have hsum : ∀ n, ∑ k ∈ range n, ‖C (k + 1) - C k‖ ≤ 1 - 1 / ‖cfB a b n‖ := by
    intro n
    induction n with
    | zero => simp [cfB, cfQ]
    | succ n ih =>
      rw [sum_range_succ]
      linarith [hdiff n]
  have hinvpos : ∀ n, 0 < 1 / ‖cfB a b n‖ := fun n => one_div_pos.mpr (by linarith [hB n])
  have hsum1 : ∀ n, ∑ k ∈ range n, ‖C (k + 1) - C k‖ ≤ 1 := fun n =>
    (hsum n).trans (by linarith [hinvpos n])
  have htel : ∀ n, C n = ∑ k ∈ range n, (C (k + 1) - C k) := fun n => by
    rw [sum_range_sub, hC0, sub_zero]
  have hlt : ∀ n, ‖C n‖ < 1 := fun n => by
    rw [htel]
    exact (norm_sum_le _ _).trans_lt (by linarith [hsum n, hinvpos n])
  have hs : Summable fun k => C (k + 1) - C k :=
    Summable.of_norm (summable_of_sum_range_le (fun _ => norm_nonneg _) hsum1)
  have hlim : Tendsto C atTop (𝓝 (∑' k, (C (k + 1) - C k))) := by
    have := hs.hasSum.tendsto_sum_nat
    exact this.congr fun n => (htel n).symm
  refine ⟨hnz, fun n => by rw [hconv]; exact hlt n, ∑' k, (C (k + 1) - C k), ?_, ?_⟩
  · exact hlim.congr fun n => (hconv n).symm
  · exact le_of_tendsto' (continuous_norm.tendsto _ |>.comp hlim) fun n => (hlt n).le

/-! ### Van Vleck's theorem -/

/-- The open sector `|ph z| < π/2 − δ` as a linear condition. -/
def VVSector (δ : ℝ) : Set ℂ := {z | |z.im| * Real.sin δ < z.re * Real.cos δ}

theorem arg_sector_iff {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < π / 2) {z : ℂ} (hz : z ≠ 0) :
    (-(π / 2) + δ < arg z ∧ arg z < π / 2 - δ) ↔ z ∈ VVSector δ := by
  have hs : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ0 (by linarith)
  have hc : 0 < Real.cos δ := Real.cos_pos_of_mem_Ioo ⟨by linarith, hδ⟩
  have hnz : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hcosarc : Real.arcsin (Real.cos δ) = π / 2 - δ := by
    rw [← Real.sin_pi_div_two_sub, Real.arcsin_sin (by linarith) (by linarith)]
  have hsq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, normSq_apply]
    ring
  have hsc : Real.sin δ ^ 2 + Real.cos δ ^ 2 = 1 := Real.sin_sq_add_cos_sq δ
  have ht1 : |z.im / ‖z‖| ≤ 1 := by
    rw [abs_div, abs_norm, div_le_one hnz]
    exact abs_im_le_norm z
  -- `|Im z| < |z| cos δ` ↔ `|Im z| sin δ < Re z cos δ`, given `Re z > 0`
  have hkey : 0 < z.re → (|z.im| < ‖z‖ * Real.cos δ ↔ |z.im| * Real.sin δ < z.re * Real.cos δ) := by
    intro hre
    have e1 : |z.im| ^ 2 = z.im ^ 2 := sq_abs _
    have e2 : z.im ^ 2 * Real.sin δ ^ 2 = z.im ^ 2 - z.im ^ 2 * Real.cos δ ^ 2 := by
      linear_combination z.im ^ 2 * hsc
    constructor
    · intro h
      have h2 : |z.im| ^ 2 < (‖z‖ * Real.cos δ) ^ 2 :=
        pow_lt_pow_left₀ h (abs_nonneg _) two_ne_zero
      have h3 : (|z.im| * Real.sin δ) ^ 2 < (z.re * Real.cos δ) ^ 2 := by
        rw [mul_pow, hsq, e1] at h2
        rw [mul_pow, mul_pow, e1]
        nlinarith
      exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h3
    · intro h
      have h3 : (|z.im| * Real.sin δ) ^ 2 < (z.re * Real.cos δ) ^ 2 :=
        pow_lt_pow_left₀ h (by positivity) two_ne_zero
      have h2 : |z.im| ^ 2 < (‖z‖ * Real.cos δ) ^ 2 := by
        rw [mul_pow, mul_pow, e1] at h3
        rw [mul_pow, hsq, e1]
        nlinarith
      exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h2
  constructor
  · rintro ⟨h1, h2⟩
    have hre : 0 < z.re := by
      have : |arg z| < π / 2 := abs_lt.mpr ⟨by linarith, by linarith⟩
      rcases abs_arg_lt_pi_div_two_iff.mp this with h | h
      · exact h
      · exact absurd h hz
    rw [arg_of_re_nonneg hre.le] at h1 h2
    have hup : z.im / ‖z‖ < Real.cos δ := by
      by_contra hge
      push Not at hge
      have := Real.arcsin_le_arcsin hge
      rw [hcosarc] at this
      linarith
    have hlo : -Real.cos δ < z.im / ‖z‖ := by
      by_contra hge
      push Not at hge
      have := Real.arcsin_le_arcsin hge
      rw [Real.arcsin_neg, hcosarc] at this
      linarith
    have habs : |z.im| < ‖z‖ * Real.cos δ := by
      have : |z.im / ‖z‖| < Real.cos δ := abs_lt.mpr ⟨hlo, hup⟩
      rwa [abs_div, abs_norm, div_lt_iff₀ hnz, mul_comm] at this
    exact (hkey hre).mp habs
  · intro h
    have hre : 0 < z.re := by
      have : 0 ≤ |z.im| * Real.sin δ := by positivity
      exact (mul_pos_iff_of_pos_right hc).mp (lt_of_le_of_lt this h)
    have habs := (hkey hre).mpr h
    have ht : |z.im / ‖z‖| < Real.cos δ := by
      rw [abs_div, abs_norm, div_lt_iff₀ hnz, mul_comm]
      exact habs
    obtain ⟨hlo, hup⟩ := abs_lt.mp ht
    rw [arg_of_re_nonneg hre.le]
    have hb := abs_le.mp ht1
    constructor
    · have := Real.arcsin_lt_arcsin (by linarith [Real.cos_le_one δ]) hlo hb.2
      rw [Real.arcsin_neg, hcosarc] at this
      linarith
    · have := Real.arcsin_lt_arcsin hb.1 hup (by linarith [Real.cos_le_one δ])
      rwa [hcosarc] at this

theorem VVSector.add {δ : ℝ} {z w : ℂ} (hz : z ∈ VVSector δ) (hw : w ∈ VVSector δ)
    (hs : 0 ≤ Real.sin δ) : z + w ∈ VVSector δ := by
  simp only [VVSector, Set.mem_ofPred_eq, add_im, add_re] at hz hw ⊢
  calc |z.im + w.im| * Real.sin δ ≤ (|z.im| + |w.im|) * Real.sin δ :=
        mul_le_mul_of_nonneg_right (abs_add_le _ _) hs
    _ < (z.re + w.re) * Real.cos δ := by linarith

theorem VVSector.ne_zero {δ : ℝ} {z : ℂ} (hz : z ∈ VVSector δ) : z ≠ 0 := by
  rintro rfl
  simp [VVSector] at hz

theorem VVSector.inv {δ : ℝ} {z : ℂ} (hz : z ∈ VVSector δ) : z⁻¹ ∈ VVSector δ := by
  have hz0 := VVSector.ne_zero hz
  have hn : 0 < normSq z := normSq_pos.mpr hz0
  simp only [VVSector, Set.mem_ofPred_eq, inv_re, inv_im] at hz ⊢
  rw [neg_div, abs_neg, abs_div, abs_of_pos hn, div_mul_eq_mul_div, div_mul_eq_mul_div,
    div_lt_div_iff_of_pos_right hn]
  exact hz

/-- The tails of `1/(b₁ + 1/(b₂ + ⋯))` with `bₙ` in the sector stay in the sector. -/
theorem vanVleck_tails {b : ℕ → ℂ} {δ : ℝ} (hs : 0 ≤ Real.sin δ) (hb0 : b 0 = 0)
    (hb : ∀ n ≥ 1, b n ∈ VVSector δ) :
    ∀ n w, w ∈ VVSector δ → CfNonzero (fun _ => 1) b n w ∧ cfw (fun _ => 1) b n w ∈ VVSector δ := by
  intro n
  induction n with
  | zero => intro w hw; exact ⟨trivial, by simpa [cfw, hb0] using hw⟩
  | succ n ih =>
    intro w hw
    have hsum := VVSector.add (hb (n + 1) (by omega)) hw hs
    obtain ⟨h1, h2⟩ := ih (1 / (b (n + 1) + w)) (by rw [one_div]; exact VVSector.inv hsum)
    exact ⟨⟨VVSector.ne_zero hsum, h1⟩, h2⟩

/-- **Van Vleck's theorem** (DLMF 1.12.26–1.12.27), sector part: if the elements of
`1/(b₁ + 1/(b₂ + ⋯))` satisfy `−π/2 + δ < ph bₙ < π/2 − δ` (`bₙ ≠ 0`), then no zero denominator
occurs and the convergents satisfy `−π/2 + δ < ph Cₙ < π/2 − δ`, `n ≥ 1`. -/
theorem dlmf_1_12_27 {b : ℕ → ℂ} {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < π / 2) (hb0 : b 0 = 0)
    (hbne : ∀ n ≥ 1, b n ≠ 0)
    (hb : ∀ n ≥ 1, -(π / 2) + δ < arg (b n) ∧ arg (b n) < π / 2 - δ) (n : ℕ) (hn : 1 ≤ n) :
    CfNonzero (fun _ => 1) b n 0 ∧ cfConv (fun _ => 1) b n ≠ 0 ∧
      -(π / 2) + δ < arg (cfConv (fun _ => 1) b n) ∧ arg (cfConv (fun _ => 1) b n) < π / 2 - δ := by
  have hs : 0 ≤ Real.sin δ := (Real.sin_pos_of_pos_of_lt_pi hδ0 (by linarith)).le
  have hbS : ∀ k ≥ 1, b k ∈ VVSector δ := fun k hk =>
    (arg_sector_iff hδ0 hδ (hbne k hk)).mp (hb k hk)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hb1 := hbS (m + 1) (by omega)
  have hb1' : b (m + 1) + 0 ∈ VVSector δ := by simpa using hb1
  obtain ⟨h1, h2⟩ := vanVleck_tails hs hb0 hbS m (1 / (b (m + 1) + 0))
    (by rw [one_div]; exact VVSector.inv hb1')
  have hconv : cfConv (fun _ => 1) b (m + 1) ∈ VVSector δ := h2
  exact ⟨⟨VVSector.ne_zero hb1', h1⟩, VVSector.ne_zero hconv,
    (arg_sector_iff hδ0 hδ (VVSector.ne_zero hconv)).mpr hconv⟩

/-- DLMF §1.12(v): under the hypotheses of Van Vleck's theorem, if the continued fraction
converges to `C`, then `|ph C| ≤ π/2`. -/
theorem dlmf_1_12_v_vanVleck_ph {b : ℕ → ℂ} {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < π / 2)
    (hb0 : b 0 = 0) (hbne : ∀ n ≥ 1, b n ≠ 0)
    (hb : ∀ n ≥ 1, -(π / 2) + δ < arg (b n) ∧ arg (b n) < π / 2 - δ) {C : ℂ}
    (hC : CfConverges (fun _ => 1) b C) : |arg C| ≤ π / 2 := by
  have hs : 0 ≤ Real.sin δ := (Real.sin_pos_of_pos_of_lt_pi hδ0 (by linarith)).le
  have hc : 0 < Real.cos δ := Real.cos_pos_of_mem_Ioo ⟨by linarith, hδ⟩
  have hre : ∀ n, 0 ≤ (cfConv (fun _ => 1) b n).re := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [cfConv, cfw, hb0]
    · obtain ⟨-, hne, hS⟩ := dlmf_1_12_27 hδ0 hδ hb0 hbne hb n hn
      have hmem := (arg_sector_iff hδ0 hδ hne).mp hS
      simp only [VVSector, Set.mem_ofPred_eq] at hmem
      have : 0 ≤ |(cfConv (fun _ => 1) b n).im| * Real.sin δ := by positivity
      nlinarith
  rw [abs_arg_le_pi_div_two_iff]
  exact ge_of_tendsto' ((continuous_re.tendsto _).comp hC) hre

end Azurite.DLMF
