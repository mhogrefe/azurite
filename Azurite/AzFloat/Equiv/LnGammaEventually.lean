/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.LnGammaWidth
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The bracket of `ln Γ` converges

`lnGammaBracketEncl_eventually`: for a fixed `x > 0` the width of `lnGammaBracketEncl X e w`
tends to `0` as the Ziv level `w` grows, uniformly in the enclosures `X` of `x` of relative
width at most `8 · 2^(−w)`.

The ingredients: the size of the shift (`lnGammaShift_le`, `lnGammaShift_ge`,
`two_pow_shiftExp`), the number of terms (`lnGammaTerms_bounds`, which tends to infinity,
`lnGammaTerms_tendsto`), polynomially bounded sequences (`PB`, `PB.tendsto`), and
`lnGammaBracketEncl_width`.
-/

namespace Azurite.AzFloat

open Filter Topology

/-! ### The shift and the number of terms -/

theorem lnGammaShift_le (x : AzFloat) (e : AzInt) (L : ℕ) : lnGammaShift x e L ≤ 2 ^ L := by
  unfold lnGammaShift
  have h1 : 1 ≤ 2 ^ L := Nat.one_le_two_pow
  have hs : 2 ^ L - 2 ^ (e.abs.toNat - 1) ≤ 2 ^ L := Nat.sub_le _ _
  refine max_le ?_ (by split_ifs <;> omega)
  split_ifs <;> omega

theorem lnGammaShift_ge (x : AzFloat) (e : AzInt) {L : ℕ} (h : e.abs.toNat ≤ L) :
    2 ^ L - 2 ^ e.abs.toNat ≤ lnGammaShift x e L := by
  unfold lnGammaShift
  refine le_max_of_le_left ?_
  have hp : 2 ^ (e.abs.toNat - 1) ≤ 2 ^ e.abs.toNat :=
    Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
  have h1 : 2 ^ L - 2 ^ e.abs.toNat ≤ 2 ^ L := Nat.sub_le _ _
  have h2 : 2 ^ L - 2 ^ e.abs.toNat ≤ 2 ^ L - 2 ^ (e.abs.toNat - 1) :=
    Nat.sub_le_sub_left hp _
  split_ifs <;> omega

theorem two_pow_shiftExp {w : ℕ} (hw : 4 ≤ w) :
    2 ^ lnGammaShiftExp w ≤ w / 2 ∧ w / 4 < 2 ^ lnGammaShiftExp w := by
  unfold lnGammaShiftExp
  have h1 : 2 ^ (w / 4).log2 ≤ w / 4 := Nat.log2_self_le (by omega)
  have h2 : w / 4 < 2 ^ ((w / 4).log2 + 1) := Nat.lt_log2_self
  rw [pow_succ] at h2 ⊢
  omega

theorem shiftExp_le_log2 {w : ℕ} (hw : 4 ≤ w) : lnGammaShiftExp w ≤ w.log2 := by
  have h1 := (two_pow_shiftExp hw).1
  have h2 : w < 2 ^ (w.log2 + 1) := Nat.lt_log2_self
  have h3 : 2 ^ lnGammaShiftExp w < 2 ^ (w.log2 + 1) := by omega
  have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h3
  omega

theorem lnGammaTermsGo_spec (w E : ℕ) : ∀ fuel m : ℕ,
    m ≤ lnGammaTermsGo w E fuel m ∧ lnGammaTermsGo w E fuel m ≤ m + fuel ∧
      (lnGammaTermsGo w E fuel m = m + fuel ∨
        2 * (w + 24) ≤ lnGammaTermsGo w E fuel m * (4 * E + 7))
  | 0, m => by simp [lnGammaTermsGo]
  | fuel + 1, m => by
    rw [lnGammaTermsGo]
    split_ifs with h
    · refine ⟨le_rfl, by omega, Or.inr (h.trans (Nat.mul_le_mul_left m (Nat.sub_le _ _)))⟩
    · obtain ⟨h1, h2, h3⟩ := lnGammaTermsGo_spec w E fuel (m + 1)
      refine ⟨by omega, by omega, ?_⟩
      rcases h3 with h3 | h3
      · left; omega
      · right; exact h3

theorem lnGammaTerms_bounds (w E : ℕ) :
    4 ≤ lnGammaTerms w E ∧ lnGammaTerms w E ≤ w / 2 + 4 ∧
      (w / 2 + 4 ≤ lnGammaTerms w E ∨ 2 * (w + 24) ≤ lnGammaTerms w E * (4 * E + 7)) := by
  unfold lnGammaTerms
  obtain ⟨h1, h2, h3⟩ := lnGammaTermsGo_spec w E (w / 2) 1
  refine ⟨by omega, by omega, ?_⟩
  rcases h3 with h3 | h3
  · left; omega
  · right
    exact h3.trans (Nat.mul_le_mul_right _ (Nat.le_add_right _ 3))

/-- `log₂ w` is small compared with `w`. -/
theorem log2_small (C : ℕ) : ∃ W : ℕ, ∀ w, W ≤ w → C * (w.log2 + C) ≤ w := by
  set n₀ := max 4 (2 * C) with hn₀
  refine ⟨C * (n₀ + C) + 1, fun w hw => ?_⟩
  have hw0 : w ≠ 0 := by omega
  have hpow : 2 ^ w.log2 ≤ w := Nat.log2_self_le hw0
  rcases lt_or_ge w.log2 n₀ with h | h
  · calc C * (w.log2 + C) ≤ C * (n₀ + C) := Nat.mul_le_mul_left C (by omega)
      _ ≤ w := by omega
  · -- `2^n ≥ n² ≥ C (n + C)` for `n ≥ max 4 (2C)`
    have hn4 : 4 ≤ w.log2 := le_trans (le_max_left _ _) h
    have hnC : 2 * C ≤ w.log2 := le_trans (le_max_right _ _) h
    have hsq : w.log2 ^ 2 ≤ 2 ^ w.log2 := by
      have : ∀ n : ℕ, 4 ≤ n → n ^ 2 ≤ 2 ^ n := by
        intro n hn
        induction n, hn using Nat.le_induction with
        | base => norm_num
        | succ n hn ih =>
          have : (n + 1) ^ 2 ≤ 2 * n ^ 2 := by nlinarith
          calc (n + 1) ^ 2 ≤ 2 * n ^ 2 := this
            _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
            _ = 2 ^ (n + 1) := by ring
      exact this _ hn4
    have h3 : C * (w.log2 + C) ≤ w.log2 ^ 2 := by nlinarith
    omega

/-- **The number of terms tends to infinity.** -/
theorem lnGammaTerms_tendsto (a K : ℕ) :
    ∃ W : ℕ, ∀ w, W ≤ w → ∀ E, E ≤ w.log2 + a + 2 → K ≤ lnGammaTerms w E := by
  obtain ⟨W, hW⟩ := log2_small (4 * K + 4 * a + 15)
  refine ⟨max W (2 * K), fun w hw E hE => ?_⟩
  obtain ⟨-, -, h3⟩ := lnGammaTerms_bounds w E
  rcases h3 with h3 | h3
  · have := le_max_right W (2 * K)
    omega
  · by_contra hlt
    push Not at hlt
    have h4 := hW w (le_trans (le_max_left _ _) hw)
    have h5 : lnGammaTerms w E * (4 * E + 7) ≤ K * (4 * (w.log2 + a + 2) + 7) :=
      Nat.mul_le_mul hlt.le (by omega)
    have h6 : K * (4 * (w.log2 + a + 2) + 7)
        ≤ (4 * K + 4 * a + 15) * (w.log2 + (4 * K + 4 * a + 15)) := by nlinarith
    omega

/-! ### Polynomially bounded sequences -/

/-- `|f w| ≤ C (w + 1)^k`. -/
def PB (f : ℕ → ℝ) : Prop := ∃ (C : ℝ) (k : ℕ), ∀ w : ℕ, |f w| ≤ C * ((w : ℝ) + 1) ^ k

theorem PB.const (c : ℝ) : PB fun _ => c := ⟨|c|, 0, fun _ => by simp⟩

theorem PB.natCast : PB fun w : ℕ => (w : ℝ) :=
  ⟨1, 1, fun w => by
    rw [abs_of_nonneg (Nat.cast_nonneg w)]
    linarith⟩

theorem PB.of_abs_le {f g : ℕ → ℝ} (hf : PB f) (h : ∀ w, |g w| ≤ |f w|) : PB g := by
  obtain ⟨C, k, hC⟩ := hf
  exact ⟨C, k, fun w => (h w).trans (hC w)⟩

theorem PB.add {f g : ℕ → ℝ} (hf : PB f) (hg : PB g) : PB fun w => f w + g w := by
  obtain ⟨C₁, k₁, h₁⟩ := hf
  obtain ⟨C₂, k₂, h₂⟩ := hg
  refine ⟨|C₁| + |C₂|, max k₁ k₂, fun w => ?_⟩
  have hb : (1 : ℝ) ≤ (w : ℝ) + 1 := by
    have : (0 : ℝ) ≤ w := Nat.cast_nonneg w
    linarith
  have e1 : ((w : ℝ) + 1) ^ k₁ ≤ ((w : ℝ) + 1) ^ max k₁ k₂ :=
    pow_le_pow_right₀ hb (le_max_left _ _)
  have e2 : ((w : ℝ) + 1) ^ k₂ ≤ ((w : ℝ) + 1) ^ max k₁ k₂ :=
    pow_le_pow_right₀ hb (le_max_right _ _)
  have p1 : (0 : ℝ) ≤ ((w : ℝ) + 1) ^ k₁ := by positivity
  have p2 : (0 : ℝ) ≤ ((w : ℝ) + 1) ^ k₂ := by positivity
  calc |f w + g w| ≤ |f w| + |g w| := abs_add_le _ _
    _ ≤ C₁ * ((w : ℝ) + 1) ^ k₁ + C₂ * ((w : ℝ) + 1) ^ k₂ := add_le_add (h₁ w) (h₂ w)
    _ ≤ |C₁| * ((w : ℝ) + 1) ^ k₁ + |C₂| * ((w : ℝ) + 1) ^ k₂ :=
        add_le_add (mul_le_mul_of_nonneg_right (le_abs_self _) p1)
          (mul_le_mul_of_nonneg_right (le_abs_self _) p2)
    _ ≤ |C₁| * ((w : ℝ) + 1) ^ max k₁ k₂ + |C₂| * ((w : ℝ) + 1) ^ max k₁ k₂ :=
        add_le_add (mul_le_mul_of_nonneg_left e1 (abs_nonneg _))
          (mul_le_mul_of_nonneg_left e2 (abs_nonneg _))
    _ = _ := by ring

theorem PB.mul {f g : ℕ → ℝ} (hf : PB f) (hg : PB g) : PB fun w => f w * g w := by
  obtain ⟨C₁, k₁, h₁⟩ := hf
  obtain ⟨C₂, k₂, h₂⟩ := hg
  refine ⟨C₁ * C₂, k₁ + k₂, fun w => ?_⟩
  rw [abs_mul, pow_add]
  calc |f w| * |g w| ≤ (C₁ * ((w : ℝ) + 1) ^ k₁) * (C₂ * ((w : ℝ) + 1) ^ k₂) :=
        mul_le_mul (h₁ w) (h₂ w) (abs_nonneg _) ((abs_nonneg _).trans (h₁ w))
    _ = _ := by ring

theorem PB.pow {f : ℕ → ℝ} (hf : PB f) (n : ℕ) : PB fun w => f w ^ n := by
  induction n with
  | zero => simpa using PB.const 1
  | succ n ih =>
    have := ih.mul hf
    simpa [pow_succ] using this

theorem PB.const_mul {f : ℕ → ℝ} (hf : PB f) (c : ℝ) : PB fun w => c * f w :=
  (PB.const c).mul hf

theorem PB.div_const {f : ℕ → ℝ} (hf : PB f) (c : ℝ) : PB fun w => f w / c := by
  have := hf.const_mul c⁻¹
  refine this.of_abs_le fun w => le_of_eq ?_
  rw [div_eq_mul_inv, mul_comm]

/-- A polynomially bounded sequence times `2^(−w)` tends to `0`. -/
theorem PB.tendsto {f : ℕ → ℝ} (hf : PB f) :
    Tendsto (fun w : ℕ => f w * (1 / 2 : ℝ) ^ w) atTop (𝓝 0) := by
  obtain ⟨C, k, hC⟩ := hf
  have h0 := (tendsto_pow_const_mul_const_pow_of_abs_lt_one k
    (by norm_num : |(1 / 2 : ℝ)| < 1)).comp (tendsto_add_atTop_nat 1)
  have h1 : Tendsto (fun w : ℕ => 2 * C * (((w : ℝ) + 1) ^ k * (1 / 2 : ℝ) ^ (w + 1)))
      atTop (𝓝 0) := by
    have := h0.const_mul (2 * C)
    simpa using this
  refine squeeze_zero_norm (fun w => ?_) h1
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w)]
  calc |f w| * (1 / 2 : ℝ) ^ w ≤ C * ((w : ℝ) + 1) ^ k * (1 / 2 : ℝ) ^ w :=
        mul_le_mul_of_nonneg_right (hC w) (by positivity)
    _ = 2 * C * (((w : ℝ) + 1) ^ k * (1 / 2 : ℝ) ^ (w + 1)) := by
        rw [pow_succ]
        ring

/-! ### The arithmetic of the width bound -/

/-- `lnGammaWidthBound` with its small quantities as parameters. -/
noncomputable def lgBound (l u a q δ M B Bf mx : ℝ) : ℝ :=
  (3 * B ^ 2 * (l + 6 * u) + B * (a + 5 * (l + 6 * u))
      + (M * (2 * (2 * M * (l + 6 * u + 12 * u)) + 4 * B * u) + mx + 2 * B * u)
      + 42 * B ^ 2 * u)
    + (q + 5 * (2 * δ * (l + 12 * u) + 21 * u)) / 2 + 4 * Bf * u

theorem lnGammaWidthBound_eq (lam₀ : ℝ) (w V δ M : ℕ) (B GQ Bf : ℝ) :
    lnGammaWidthBound lam₀ w V δ M B GQ Bf
      = lgBound lam₀ ((1 / 2 : ℝ) ^ V) (lnW B V) (lnW GQ V) δ M B Bf
        (max ((1 / 2 : ℝ) ^ (w + 16)) (2 * (9 / 10 : ℝ) ^ (2 * M - 1))) := rfl

/-- The polynomial part of the final width. -/
noncomputable def lgPoly (pB pQ wr M B Bf : ℝ) : ℝ :=
  42 * B ^ 2 + B * (pB + 70) + M * (104 * M + 4 * B) + 2 * B + 42 * B ^ 2
    + (pQ + 5 * (40 * wr + 21)) / 2 + 4 * Bf

/-- All the smallness conditions of `lnGammaBracketEncl_width`, and the bound for the width,
from one inequality. -/
theorem lgBound_facts {l u U a q pB pQ δ wr M B Bf mx : ℝ} (hl0 : 0 ≤ l) (hl : l ≤ 8 * U)
    (hu0 : 0 ≤ u) (hu : u ≤ U) (hB : 3 ≤ B) (hBf : 0 ≤ Bf) (ha0 : 0 ≤ a) (ha : a ≤ pB * U)
    (hq0 : 0 ≤ q) (hq : q ≤ pQ * U) (hM : 1 ≤ M) (hδ0 : 0 ≤ δ) (hδ : δ ≤ wr) (hmx : 0 ≤ mx)
    (hsmall : lgPoly pB pQ wr M B Bf * U + mx ≤ 3 / 8) :
    B * (l + 6 * u) ≤ 1 / 8 ∧ B ^ 2 * u ≤ 1 / 16 ∧ 2 * M * (l + 6 * u + 12 * u) ≤ 1 / 2 ∧
      a + 5 * (l + 6 * u) ≤ 1 ∧
      M * (2 * (2 * M * (l + 6 * u + 12 * u)) + 4 * B * u) + mx + 2 * B * u ≤ 1 ∧
      2 * δ * (l + 12 * u) + 21 * u ≤ 1 / 2 ∧
      lgBound l u a q δ M B Bf mx ≤ lgPoly pB pQ wr M B Bf * U + mx := by
  have hU0 : 0 ≤ U := hu0.trans hu
  have hB0 : 0 ≤ B := by linarith
  have hM0 : 0 ≤ M := by linarith
  have hwr0 : 0 ≤ wr := hδ0.trans hδ
  have hpB : 0 ≤ pB * U := ha0.trans ha
  have hpQ : 0 ≤ pQ * U := hq0.trans hq
  have hBU : 0 ≤ B * U := mul_nonneg hB0 hU0
  have hB2U : 0 ≤ B ^ 2 * U := by positivity
  have hMU : 0 ≤ M * U := mul_nonneg hM0 hU0
  have hM2U : 0 ≤ M * M * U := by positivity
  have hMBU : 0 ≤ M * B * U := by positivity
  have hwU : 0 ≤ wr * U := mul_nonneg hwr0 hU0
  have hBfU : 0 ≤ Bf * U := mul_nonneg hBf hU0
  have hBpB : 0 ≤ B * (pB * U) := mul_nonneg hB0 hpB
  -- the seven pieces of `lgPoly · U`
  have hexp : lgPoly pB pQ wr M B Bf * U
      = 42 * (B ^ 2 * U) + (B * (pB * U) + 70 * (B * U)) + (104 * (M * M * U) + 4 * (M * B * U))
        + 2 * (B * U) + 42 * (B ^ 2 * U) + ((pQ * U) + 5 * (40 * (wr * U) + 21 * U)) / 2
        + 4 * (Bf * U) := by
    unfold lgPoly
    ring
  rw [hexp] at hsmall ⊢
  -- monotone facts
  have hlu : l + 6 * u ≤ 14 * U := by linarith only [hl, hu]
  have hlu0 : 0 ≤ l + 6 * u := by linarith only [hl0, hu0]
  have hlu18 : l + 6 * u + 12 * u ≤ 26 * U := by linarith only [hl, hu]
  have hlu12 : l + 12 * u ≤ 20 * U := by linarith only [hl, hu]
  have hlu12' : 0 ≤ l + 12 * u := by linarith only [hl0, hu0]
  have h3BU : 3 * (B * U) ≤ B ^ 2 * U :=
    (mul_le_mul_of_nonneg_right hB hBU).trans (le_of_eq (by ring))
  have hMMU : M * U ≤ M * M * U := by
    have := mul_le_mul_of_nonneg_right hM hMU
    calc M * U = 1 * (M * U) := (one_mul _).symm
      _ ≤ M * (M * U) := this
      _ = M * M * U := by ring
  have e1 : B * (l + 6 * u) ≤ 14 * (B * U) :=
    (mul_le_mul_of_nonneg_left hlu hB0).trans (le_of_eq (by ring))
  have e2 : B ^ 2 * u ≤ B ^ 2 * U := mul_le_mul_of_nonneg_left hu (by positivity)
  have e3 : M * (l + 6 * u + 12 * u) ≤ 26 * (M * U) :=
    (mul_le_mul_of_nonneg_left hlu18 hM0).trans (le_of_eq (by ring))
  have e4 : B * u ≤ B * U := mul_le_mul_of_nonneg_left hu hB0
  have e5 : M * (M * (l + 6 * u + 12 * u)) ≤ 26 * (M * M * U) :=
    (mul_le_mul_of_nonneg_left e3 hM0).trans (le_of_eq (by ring))
  have e6 : M * (B * u) ≤ M * B * U :=
    (mul_le_mul_of_nonneg_left e4 hM0).trans (le_of_eq (by ring))
  have e7 : δ * (l + 12 * u) ≤ 20 * (wr * U) :=
    ((mul_le_mul_of_nonneg_right hδ hlu12').trans
      (mul_le_mul_of_nonneg_left hlu12 hwr0)).trans (le_of_eq (by ring))
  have e8 : B ^ 2 * (l + 6 * u) ≤ 14 * (B ^ 2 * U) :=
    (mul_le_mul_of_nonneg_left hlu (by positivity : (0 : ℝ) ≤ B ^ 2)).trans (le_of_eq (by ring))
  have e9 : B * a ≤ B * (pB * U) := mul_le_mul_of_nonneg_left ha hB0
  have e10 : Bf * u ≤ Bf * U := mul_le_mul_of_nonneg_left hu hBf
  have e12 : a ≤ B * (pB * U) :=
    ha.trans (le_mul_of_one_le_left hpB (by linarith only [hB]))
  refine ⟨by linarith only [e1, h3BU, hsmall, hBpB, hBU, hM2U, hMBU, hpQ, hwU, hU0, hBfU, hmx,
      hB2U],
    by linarith only [e2, hsmall, hBpB, hBU, hM2U, hMBU, hpQ, hwU, hU0, hBfU, hmx, hB2U],
    by linarith only [e3, hMMU, hsmall, hBpB, hBU, hM2U, hMBU, hpQ, hwU, hU0, hBfU, hmx,
      hB2U],
    by linarith only [e12, hlu, h3BU, hsmall, hBpB, hBU, hM2U, hMBU, hpQ, hwU, hU0, hBfU, hmx,
      hB2U], ?_,
    by linarith only [e7, hu, hu0, hsmall, hBpB, hBU, hM2U, hMBU, hpQ, hwU, hU0, hBfU, hmx,
      hB2U], ?_⟩
  · have : M * (2 * (2 * M * (l + 6 * u + 12 * u)) + 4 * B * u)
        = 4 * (M * (M * (l + 6 * u + 12 * u))) + 4 * (M * (B * u)) := by ring
    rw [this]
    linarith only [e5, e6, e4, hsmall, hBpB, hBU, hM2U, hMBU, hpQ, hwU, hU0, hBfU, hmx, hB2U]
  · unfold lgBound
    have t3 : M * (2 * (2 * M * (l + 6 * u + 12 * u)) + 4 * B * u)
        = 4 * (M * (M * (l + 6 * u + 12 * u))) + 4 * (M * (B * u)) := by ring
    have t1 : 3 * B ^ 2 * (l + 6 * u) = 3 * (B ^ 2 * (l + 6 * u)) := by ring
    have t2 : B * (a + 5 * (l + 6 * u)) = B * a + 5 * (B * (l + 6 * u)) := by ring
    have t5 : 42 * B ^ 2 * u = 42 * (B ^ 2 * u) := by ring
    have t6 : 2 * δ * (l + 12 * u) = 2 * (δ * (l + 12 * u)) := by ring
    have t7 : 4 * Bf * u = 4 * (Bf * u) := by ring
    have t4 : 2 * B * u = 2 * (B * u) := by ring
    rw [t1, t2, t3, t5, t6, t7, t4]
    linarith only [e8, e9, e1, e5, e6, e4, e2, hq, e7, hu, e10]

theorem lnW_le {G : ℝ} (hG : 0 ≤ G) {w V : ℕ} (h1 : w ≤ V) (h2 : V ≤ 6 * w) :
    lnW G V ≤ 2 ^ 42 * (6 * (w : ℝ) + 2 * G + 10) ^ 5 * (1 / 2 : ℝ) ^ w := by
  unfold lnW
  have hV : (V : ℝ) ≤ 6 * w := by exact_mod_cast h2
  have hpow : (1 / 2 : ℝ) ^ V ≤ (1 / 2 : ℝ) ^ w :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) h1
  have hV0 : (0 : ℝ) ≤ V := Nat.cast_nonneg V
  have hbase : ((V : ℝ) + 2 * G + 10) ^ 5 ≤ (6 * (w : ℝ) + 2 * G + 10) ^ 5 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 5
  exact mul_le_mul (mul_le_mul_of_nonneg_left hbase (by norm_num)) hpow (by positivity)
    (by positivity)

/-! ### The convergence -/

/-- The number of terms of Stirling's series at Ziv level `w`. -/
def lgTerms (e : AzInt) (w : ℕ) : ℕ :=
  lnGammaTerms w (max (lnGammaShiftExp w + 1) (if e.sign then e.abs.toNat else 0))

/-- **The width of the bracket of `ln Γ(x)` at Ziv level `w`** (for `w` large enough). -/
noncomputable def lgEps (xv : ℝ) (e : AzInt) (w : ℕ) : ℝ :=
  lgPoly (2 ^ 42 * (6 * (w : ℝ) + 2 * (xv + 4 * w) + 10) ^ 5)
      (2 ^ 42 * (6 * (w : ℝ) + 2 * (3 + 2 * w * (|Real.log xv| + (xv + w))) + 10) ^ 5)
      w (lgTerms e w) (xv + 4 * w) (|Real.log (Real.Gamma xv)| + 1) * (1 / 2 : ℝ) ^ w
    + max ((1 / 2 : ℝ) ^ (w + 16)) (2 * (9 / 10 : ℝ) ^ (2 * lgTerms e w - 1))

theorem lgTerms_le (e : AzInt) (w : ℕ) : 4 ≤ lgTerms e w ∧ lgTerms e w ≤ w / 2 + 4 :=
  ⟨(lnGammaTerms_bounds w _).1, (lnGammaTerms_bounds w _).2.1⟩

theorem tendsto_lgTerms (e : AzInt) : Tendsto (fun w => 2 * lgTerms e w - 1) atTop atTop := by
  rw [tendsto_atTop]
  intro K
  obtain ⟨W, hW⟩ := lnGammaTerms_tendsto e.abs.toNat (K + 1)
  rw [eventually_atTop]
  refine ⟨max W 4, fun w hw => ?_⟩
  have hw4 : 4 ≤ w := le_trans (le_max_right _ _) hw
  have hL := shiftExp_le_log2 hw4
  have hE : max (lnGammaShiftExp w + 1) (if e.sign then e.abs.toNat else 0)
      ≤ w.log2 + e.abs.toNat + 2 := by
    refine max_le (by omega) ?_
    split_ifs <;> omega
  have := hW w (le_trans (le_max_left _ _) hw) _ hE
  unfold lgTerms
  omega

theorem tendsto_lgEps (xv : ℝ) (e : AzInt) : Tendsto (lgEps xv e) atTop (𝓝 0) := by
  have hw : PB fun w : ℕ => (w : ℝ) := PB.natCast
  have hM : PB fun w : ℕ => ((lgTerms e w : ℕ) : ℝ) := by
    refine (hw.add (PB.const 4)).of_abs_le fun w => ?_
    have h1 := (lgTerms_le e w).2
    have h2 : ((lgTerms e w : ℕ) : ℝ) ≤ (w : ℝ) + 4 := by
      have : lgTerms e w ≤ w + 4 := by omega
      exact_mod_cast this
    have h3 : (0 : ℝ) ≤ (w : ℝ) := Nat.cast_nonneg w
    rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (by linarith)]
    exact h2
  have hB : PB fun w : ℕ => xv + 4 * (w : ℝ) := (PB.const xv).add (hw.const_mul 4)
  have hpB : PB fun w : ℕ => (2 : ℝ) ^ 42 * (6 * (w : ℝ) + 2 * (xv + 4 * w) + 10) ^ 5 :=
    ((((hw.const_mul 6).add (hB.const_mul 2)).add (PB.const 10)).pow 5).const_mul _
  have hGQ : PB fun w : ℕ => 3 + 2 * (w : ℝ) * (|Real.log xv| + (xv + w)) :=
    (PB.const 3).add ((hw.const_mul 2).mul ((PB.const _).add ((PB.const xv).add hw)))
  have hpQ : PB fun w : ℕ => (2 : ℝ) ^ 42
      * (6 * (w : ℝ) + 2 * (3 + 2 * w * (|Real.log xv| + (xv + w))) + 10) ^ 5 :=
    ((((hw.const_mul 6).add (hGQ.const_mul 2)).add (PB.const 10)).pow 5).const_mul _
  have hpoly : PB fun w : ℕ => lgPoly (2 ^ 42 * (6 * (w : ℝ) + 2 * (xv + 4 * w) + 10) ^ 5)
      (2 ^ 42 * (6 * (w : ℝ) + 2 * (3 + 2 * w * (|Real.log xv| + (xv + w))) + 10) ^ 5)
      w (lgTerms e w) (xv + 4 * w) (|Real.log (Real.Gamma xv)| + 1) := by
    unfold lgPoly
    exact ((((((((hB.pow 2).const_mul 42).add (hB.mul (hpB.add (PB.const 70)))).add
      (hM.mul ((hM.const_mul 104).add (hB.const_mul 4)))).add (hB.const_mul 2)).add
      ((hB.pow 2).const_mul 42)).add
      ((hpQ.add ((((hw.const_mul 40).add (PB.const 21)).const_mul 5))).div_const 2)).add
      ((PB.const _).const_mul 4))
  have h1 := hpoly.tendsto
  have h2 : Tendsto (fun w : ℕ => (1 / 2 : ℝ) ^ (w + 16)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
      (tendsto_add_atTop_nat 16)
  have h3 : Tendsto (fun w : ℕ => 2 * (9 / 10 : ℝ) ^ (2 * lgTerms e w - 1)) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 9 / 10)
      (by norm_num)).comp (tendsto_lgTerms e)).const_mul 2
    simpa using this
  have h4 := h1.add (h2.max h3)
  rw [max_self, add_zero] at h4
  exact h4

theorem log2_le_self (w : ℕ) : w.log2 ≤ w := by
  rcases Nat.eq_zero_or_pos w with rfl | h
  · simp
  · have h1 : 2 ^ w.log2 ≤ w := Nat.log2_self_le (by omega)
    have h2 : w.log2 < 2 ^ w.log2 := Nat.lt_two_pow_self
    omega

/-- The bracket at level `w` under the numerical facts (the last step of
`lnGammaBracketEncl_eventually`). -/
theorem lnGammaBracketEncl_of_small {xv : ℝ} (hxv : 0 < xv) (e : AzInt) {w : ℕ}
    (hw : 64 ≤ w) (hwa : 64 * (2 ^ e.abs.toNat + 1) ≤ w) (hsmall : lgEps xv e w ≤ 3 / 8)
    {X : Encl} {lam₀ : ℝ} (hX : LEncl X xv lam₀) (h0 : 0 ≤ lam₀)
    (hlam : lam₀ ≤ 8 * (1 / 2 : ℝ) ^ w) :
    AEncl (lnGammaBracketEncl X e w) (Real.log (Real.Gamma xv)) (lgEps xv e w) := by
  set a := e.abs.toNat with ha
  set L := lnGammaShiftExp w with hL
  set V := w + 2 * L + 8 + 2 * w.log2 with hV
  set δ := lnGammaShift X.1 e L with hδ
  set M := lgTerms e w with hM
  have hLs := two_pow_shiftExp (by omega : 4 ≤ w)
  have hLlog := shiftExp_le_log2 (by omega : 4 ≤ w)
  rw [← hL] at hLs hLlog
  obtain ⟨hL1, hL2⟩ := hLs
  have hlogw := log2_le_self w
  have hV1 : w ≤ V := by omega
  have hV2 : V ≤ 6 * w := by omega
  have haL : a ≤ L := by
    have h1 : 2 ^ a < 2 ^ L := by omega
    exact ((Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h1).le
  have hδle : δ ≤ 2 ^ L := lnGammaShift_le _ _ _
  have hδge : 2 ^ L - 2 ^ a ≤ δ := lnGammaShift_ge _ _ haL
  have hMs := lgTerms_le e w
  rw [← hM] at hMs
  obtain ⟨hM4, hMle⟩ := hMs
  have hsub : 2 ^ L - 2 ^ a + 2 ^ a = 2 ^ L :=
    Nat.sub_add_cancel (Nat.pow_le_pow_right (by norm_num) haL)
  -- real versions
  have hwR : (64 : ℝ) ≤ w := by exact_mod_cast hw
  have hδw : (δ : ℝ) ≤ w := by exact_mod_cast (by omega : δ ≤ w)
  have hδhalf : (δ : ℝ) ≤ w / 2 := by
    have : 2 * δ ≤ w := by omega
    have : (2 : ℝ) * δ ≤ w := by exact_mod_cast this
    linarith
  have hδ0 : (0 : ℝ) ≤ δ := Nat.cast_nonneg δ
  have hMR : (M : ℝ) ≤ w / 2 + 4 := by
    have : 2 * M ≤ w + 8 := by omega
    have : (2 : ℝ) * M ≤ w + 8 := by exact_mod_cast this
    linarith
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (by omega : 1 ≤ M)
  have hδlow : (w : ℝ) / 4 - w / 64 ≤ δ := by
    have h1 : w + 4 * 2 ^ a ≤ 4 * δ + 4 * 2 ^ a + 4 * 2 ^ a := by omega
    have h2 : 64 * 2 ^ a ≤ w := by omega
    have h1' : (w : ℝ) + 4 * 2 ^ a ≤ 4 * δ + 4 * 2 ^ a + 4 * 2 ^ a := by exact_mod_cast h1
    have h2' : (64 : ℝ) * 2 ^ a ≤ w := by exact_mod_cast h2
    linarith
  set U := (1 / 2 : ℝ) ^ w with hU
  have hU0 : 0 < U := by positivity
  have hu0 : (0 : ℝ) < (1 / 2 : ℝ) ^ V := by positivity
  have hu : (1 / 2 : ℝ) ^ V ≤ U := pow_le_pow_of_le_one (by norm_num) (by norm_num) hV1
  set B := xv + 4 * (w : ℝ) with hB
  have hB3 : 3 ≤ B := by linarith
  have hB0 : 0 ≤ B := by linarith
  set GQ := 3 + 2 * (w : ℝ) * (|Real.log xv| + (xv + w)) with hGQ
  have hGQ0 : 0 ≤ GQ := by positivity
  set Bf := |Real.log (Real.Gamma xv)| + 1 with hBf
  have hBf0 : 0 ≤ Bf := by positivity
  have hmx : (0 : ℝ) ≤ max ((1 / 2 : ℝ) ^ (w + 16)) (2 * (9 / 10 : ℝ) ^ (2 * M - 1)) :=
    le_trans (by positivity) (le_max_left _ _)
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := lgBound_facts (l := lam₀) (u := (1 / 2 : ℝ) ^ V)
    (U := U) (a := lnW B V) (q := lnW GQ V) (δ := δ) (wr := w) (M := M) (B := B) (Bf := Bf)
    h0 hlam hu0.le hu hB3 hBf0 (lnW_nonneg hB0 V) (lnW_le hB0 hV1 hV2)
    (lnW_nonneg hGQ0 V) (lnW_le hGQ0 hV1 hV2) hM1 hδ0 hδw hmx hsmall
  have hGQle : 3 + 2 * (δ : ℝ) * (|Real.log xv| + (xv + δ)) ≤ GQ := by
    have h1 : |Real.log xv| + (xv + δ) ≤ |Real.log xv| + (xv + w) := by linarith
    have h2 : (δ : ℝ) * (|Real.log xv| + (xv + δ)) ≤ (w : ℝ) * (|Real.log xv| + (xv + w)) :=
      mul_le_mul hδw h1 (by positivity) (by positivity)
    rw [hGQ]
    linarith
  have hMd : M = lnGammaTerms w (max (L + 1) (if e.sign then e.abs.toNat else 0)) := rfl
  have hwidth := lnGammaBracketEncl_width hX h0 e hw (M := M) hL hV hδ hMd (B := B) (GQ := GQ)
    (Bf := Bf) (by linarith) (by linarith) (by linarith) f1 f2 f3 f4 f5 f6 hGQle
    (by
      rw [lnGammaWidthBound_eq]
      have : lgBound lam₀ ((1 / 2 : ℝ) ^ V) (lnW B V) (lnW GQ V) δ M B Bf
          (max ((1 / 2 : ℝ) ^ (w + 16)) (2 * (9 / 10 : ℝ) ^ (2 * M - 1))) ≤ 1 :=
        f7.trans (hsmall.trans (by norm_num))
      linarith)
  rw [lnGammaWidthBound_eq] at hwidth
  exact hwidth.mono f7

/-- **The bracket of `ln Γ(x)` converges**: for a fixed `x > 0`, the width of
`lnGammaBracketEncl X e w` is at most `lgEps x e w → 0` for all large `w`, uniformly in the
enclosures `X` of `x` of relative width at most `8 · 2^(−w)`. -/
theorem lnGammaBracketEncl_eventually {xv : ℝ} (hxv : 0 < xv) (e : AzInt) :
    ∃ W₀ : ℕ, ∀ w, W₀ ≤ w → ∀ (X : Encl) (lam₀ : ℝ), LEncl X xv lam₀ → 0 ≤ lam₀ →
      lam₀ ≤ 8 * (1 / 2 : ℝ) ^ w →
      AEncl (lnGammaBracketEncl X e w) (Real.log (Real.Gamma xv)) (lgEps xv e w) := by
  have hev := (tendsto_lgEps xv e).eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 3 / 8))
  obtain ⟨W₁, hW₁⟩ := eventually_atTop.mp hev
  refine ⟨max W₁ (64 * (2 ^ e.abs.toNat + 1)), fun w hw X lam₀ hX h0 hlam => ?_⟩
  have h1 : W₁ ≤ w := le_trans (le_max_left _ _) hw
  have h2 : 64 * (2 ^ e.abs.toNat + 1) ≤ w := le_trans (le_max_right _ _) hw
  have h3 : 64 ≤ w := by
    have : 1 ≤ 2 ^ e.abs.toNat := Nat.one_le_two_pow
    omega
  exact lnGammaBracketEncl_of_small hxv e h3 h2 (hW₁ w h1) hX h0 hlam

end Azurite.AzFloat
