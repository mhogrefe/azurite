/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.LnGammaBracket
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Widths of interval evaluations

`Equiv/Interval.lean` proves that the `Encl` operations preserve enclosures.  Here the widths
are followed as well, in two forms:

* `AEncl a x ε` (and `AEncl0`, with a nonnegative lower end): `a` encloses `x` and its width is
  at most `ε`;
* `LEncl a x λ`: `a` has a positive lower end `l`, encloses `x`, and its upper end is at most
  `l · exp λ` (a relative width, additive under `×` and `/`).

One operation at precision `w` adds `6 · 2^(−w)` to a relative width (`LEncl.mul`, `LEncl.div`,
`LEncl.add_exact`) and `4 B · 2^(−w)` to an absolute one, `B` a bound for the magnitudes
(`AEncl.add`, `AEncl.sub`, `AEncl0.mul`).  `lnOfEncl` turns a relative width `λ` into the
absolute width `lnW G w + 5λ` (`LEncl.lnOfEncl`).
-/

namespace Azurite.AzFloat

open Encl

/-- `a` encloses `x` with width at most `ε`. -/
def AEncl (a : Encl) (x ε : ℝ) : Prop :=
  ∃ l h : ℝ, a.1.toVal = some (l : EReal) ∧ a.2.toVal = some (h : EReal) ∧ l ≤ x ∧ x ≤ h ∧
    h - l ≤ ε

/-- `a` encloses `x` with a nonnegative lower end and width at most `ε`. -/
def AEncl0 (a : Encl) (x ε : ℝ) : Prop :=
  ∃ l h : ℝ, a.1.toVal = some (l : EReal) ∧ a.2.toVal = some (h : EReal) ∧ 0 ≤ l ∧ l ≤ x ∧
    x ≤ h ∧ h - l ≤ ε

/-- `a` encloses `x` with a positive lower end `l` and upper end at most `l · exp lam`. -/
def LEncl (a : Encl) (x lam : ℝ) : Prop :=
  ∃ l h : ℝ, a.1.toVal = some (l : EReal) ∧ a.2.toVal = some (h : EReal) ∧ 0 < l ∧ l ≤ x ∧
    x ≤ h ∧ h ≤ l * Real.exp lam

variable {a b : Encl} {x y ε ε₁ ε₂ lam lam₁ lam₂ : ℝ} {w : ℕ}

theorem AEncl.isEncl (h : AEncl a x ε) : IsEncl a x := by
  obtain ⟨l, u, hl, hu, h1, h2, -⟩ := h
  exact ⟨l, u, hl, hu, h1, h2⟩

theorem AEncl.mono (h : AEncl a x ε) {ε' : ℝ} (hε : ε ≤ ε') : AEncl a x ε' := by
  obtain ⟨l, u, hl, hu, h1, h2, h3⟩ := h
  exact ⟨l, u, hl, hu, h1, h2, h3.trans hε⟩

theorem AEncl0.toA (h : AEncl0 a x ε) : AEncl a x ε := by
  obtain ⟨l, u, hl, hu, -, h1, h2, h3⟩ := h
  exact ⟨l, u, hl, hu, h1, h2, h3⟩

theorem AEncl0.mono (h : AEncl0 a x ε) {ε' : ℝ} (hε : ε ≤ ε') : AEncl0 a x ε' := by
  obtain ⟨l, u, hl, hu, h0, h1, h2, h3⟩ := h
  exact ⟨l, u, hl, hu, h0, h1, h2, h3.trans hε⟩

theorem LEncl.isEnclPos (h : LEncl a x lam) : IsEnclPos a x := by
  obtain ⟨l, u, hl, hu, h0, h1, h2, -⟩ := h
  exact ⟨l, u, hl, hu, h0, h1, h2⟩

theorem LEncl.pos (h : LEncl a x lam) : 0 < x := by
  obtain ⟨l, u, -, -, h0, h1, -, -⟩ := h
  linarith

theorem LEncl.mono (h : LEncl a x lam) {lam' : ℝ} (hl : lam ≤ lam') : LEncl a x lam' := by
  obtain ⟨l, u, hl', hu, h0, h1, h2, h3⟩ := h
  exact ⟨l, u, hl', hu, h0, h1, h2,
    h3.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hl) h0.le)⟩

theorem LEncl.exact {t : AzFloat} {tv : ℝ} (ht : t.toVal = some (tv : EReal)) (h0 : 0 < tv) :
    LEncl (Encl.exact t) tv 0 :=
  ⟨tv, tv, ht, ht, h0, le_rfl, le_rfl, by simp⟩

theorem LEncl.nat {n : ℕ} (hn : 0 < n) : LEncl (Encl.nat n) n 0 :=
  LEncl.exact (toVal_ofAzNat_ofNat n) (by exact_mod_cast hn)

/-- The two directed roundings of positive bounds. -/
theorem round_pos_combine {L H u rl rh : ℝ} (hL : 0 < L) (hH : H ≤ L * Real.exp lam)
    (hu0 : 0 ≤ u) (hu : u ≤ 1 / 8) (h1 : L ≤ rl + 2 * L * u) (h2 : rh ≤ H + 2 * H * u) :
    0 < rl ∧ rh ≤ rl * Real.exp (lam + 6 * u) := by
  have hrl : L * (1 - 2 * u) ≤ rl := by linarith
  have hrl0 : 0 < rl := lt_of_lt_of_le (mul_pos hL (by linarith)) hrl
  refine ⟨hrl0, ?_⟩
  have e6 : 1 + 6 * u ≤ Real.exp (6 * u) := by linarith [Real.add_one_le_exp (6 * u)]
  have hq : 0 ≤ L * u * (2 - 12 * u) := mul_nonneg (mul_nonneg hL.le hu0) (by linarith)
  have hk : L * (1 + 2 * u) ≤ rl * (1 + 6 * u) := by
    have := mul_le_mul_of_nonneg_right hrl (by linarith : (0 : ℝ) ≤ 1 + 6 * u)
    nlinarith
  have hE : 0 < Real.exp lam := Real.exp_pos _
  calc rh ≤ H * (1 + 2 * u) := by linarith
    _ ≤ L * Real.exp lam * (1 + 2 * u) := mul_le_mul_of_nonneg_right hH (by linarith)
    _ = Real.exp lam * (L * (1 + 2 * u)) := by ring
    _ ≤ Real.exp lam * (rl * (1 + 6 * u)) := mul_le_mul_of_nonneg_left hk hE.le
    _ ≤ Real.exp lam * (rl * Real.exp (6 * u)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left e6 hrl0.le) hE.le
    _ = rl * Real.exp (lam + 6 * u) := by rw [Real.exp_add]; ring

theorem LEncl.mul [NeZero w] (hu : (1 / 2 : ℝ) ^ w ≤ 1 / 8) (ha : LEncl a x lam₁)
    (hb : LEncl b y lam₂) :
    LEncl (Encl.mul w a b) (x * y) (lam₁ + lam₂ + 6 * (1 / 2 : ℝ) ^ w) := by
  obtain ⟨l₁, h₁, hl₁, hh₁, p₁, a₁, b₁, c₁⟩ := ha
  obtain ⟨l₂, h₂, hl₂, hh₂, p₂, a₂, b₂, c₂⟩ := hb
  have hx : 0 < x := by linarith
  have hy : 0 < y := by linarith
  obtain ⟨r, hr, hfr⟩ := mulFloor_err hl₁ hl₂ w (by positivity)
  obtain ⟨s, hs, hcs⟩ := mulCeiling_err hh₁ hh₂ w (by nlinarith)
  have hH : h₁ * h₂ ≤ l₁ * l₂ * Real.exp (lam₁ + lam₂) := by
    rw [Real.exp_add]
    calc h₁ * h₂ ≤ (l₁ * Real.exp lam₁) * (l₂ * Real.exp lam₂) :=
          mul_le_mul c₁ c₂ (by linarith) (by positivity)
      _ = _ := by ring
  obtain ⟨hr0, hrs⟩ := round_pos_combine (mul_pos p₁ p₂) hH (by positivity) hu hfr.ge hcs.le
  exact ⟨r, s, hr, hs, hr0, hfr.le.trans (mul_le_mul a₁ a₂ p₂.le (by linarith)),
    (mul_le_mul b₁ b₂ hy.le (by linarith)).trans hcs.ge, hrs⟩

theorem LEncl.div [NeZero w] (hu : (1 / 2 : ℝ) ^ w ≤ 1 / 8) (ha : LEncl a x lam₁)
    (hb : LEncl b y lam₂) :
    LEncl (Encl.div w a b) (x / y) (lam₁ + lam₂ + 6 * (1 / 2 : ℝ) ^ w) := by
  obtain ⟨l₁, h₁, hl₁, hh₁, p₁, a₁, b₁, c₁⟩ := ha
  obtain ⟨l₂, h₂, hl₂, hh₂, p₂, a₂, b₂, c₂⟩ := hb
  have hx : 0 < x := by linarith
  have hy : 0 < y := by linarith
  have hh₂0 : 0 < h₂ := by linarith
  have hh₁0 : 0 < h₁ := by linarith
  obtain ⟨r, hr, hfr⟩ := divFloor_err hl₁ hh₂ hh₂0 p₁.le w
  obtain ⟨s, hs, hcs⟩ := divCeiling_err hh₁ hl₂ p₂ hh₁0.le w
  have hH : h₁ / l₂ ≤ l₁ / h₂ * Real.exp (lam₁ + lam₂) := by
    rw [Real.exp_add, div_le_iff₀ p₂]
    have h3 : h₁ * h₂ ≤ (l₁ * Real.exp lam₁) * (l₂ * Real.exp lam₂) :=
      mul_le_mul c₁ c₂ (by linarith) (by positivity)
    have e : l₁ / h₂ * (Real.exp lam₁ * Real.exp lam₂) * l₂
        = (l₁ * Real.exp lam₁) * (l₂ * Real.exp lam₂) / h₂ := by ring
    rw [e, le_div_iff₀ hh₂0]
    exact h3
  obtain ⟨hr0, hrs⟩ := round_pos_combine (div_pos p₁ hh₂0) hH (by positivity) hu hfr.ge hcs.le
  refine ⟨r, s, hr, hs, hr0, hfr.le.trans ?_, le_trans ?_ hcs.ge, hrs⟩
  · exact div_le_div₀ hx.le a₁ hy b₂
  · exact div_le_div₀ hh₁0.le b₁ p₂ a₂

/-- Adding an exact nonnegative number does not increase the relative width. -/
theorem LEncl.add_exact [NeZero w] (hu : (1 / 2 : ℝ) ^ w ≤ 1 / 8) (ha : LEncl a x lam)
    (hlam : 0 ≤ lam) {c : ℝ} (hb1 : b.1.toVal = some (c : EReal))
    (hb2 : b.2.toVal = some (c : EReal)) (hc : 0 ≤ c) :
    LEncl (Encl.add w a b) (x + c) (lam + 6 * (1 / 2 : ℝ) ^ w) := by
  obtain ⟨l₁, h₁, hl₁, hh₁, p₁, a₁, b₁, c₁⟩ := ha
  obtain ⟨r, hr, hfr⟩ := addFloor_err hl₁ hb1 w (by linarith)
  obtain ⟨s, hs, hcs⟩ := addCeiling_err hh₁ hb2 w (by linarith)
  have hE : 1 ≤ Real.exp lam := Real.one_le_exp hlam
  have hH : h₁ + c ≤ (l₁ + c) * Real.exp lam := by nlinarith
  obtain ⟨hr0, hrs⟩ := round_pos_combine (by linarith) hH (by positivity) hu hfr.ge hcs.le
  exact ⟨r, s, hr, hs, hr0, by linarith [hfr.le], by linarith [hcs.ge], hrs⟩

theorem LEncl.pi (hw : 64 ≤ w) : LEncl (Encl.pi w) Real.pi (3 * (1 / 2 : ℝ) ^ w) := by
  obtain ⟨lv, hv, hlv, hhv, -, hlo, hhi, hwid⟩ := piBracket_spec_width hw
  have hu : (1 / 2 : ℝ) ^ w ≤ 1 / 64 := by
    calc (1 / 2 : ℝ) ^ w ≤ (1 / 2 : ℝ) ^ 6 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 64 := by norm_num
  have hu0 : (0 : ℝ) < (1 / 2 : ℝ) ^ w := by positivity
  have h3 : (3 : ℝ) ≤ lv := by linarith [Real.pi_gt_d2]
  refine ⟨lv, hv, hlv, hhv, by linarith, hlo.le, hhi, ?_⟩
  have := Real.add_one_le_exp (3 * (1 / 2 : ℝ) ^ w)
  nlinarith

/-- A relative width as an absolute one. -/
theorem LEncl.toA (h : LEncl a x lam) (h0 : 0 ≤ lam) (h1 : lam ≤ 1 / 2) :
    AEncl0 a x (2 * x * lam) := by
  obtain ⟨l, u, hl, hu, p, a₁, b₁, c₁⟩ := h
  refine ⟨l, u, hl, hu, p.le, a₁, b₁, ?_⟩
  have hexp : Real.exp lam ≤ 1 + 2 * lam := by
    rcases h0.eq_or_lt with h | h
    · rw [← h]; simp
    · have h2 := (Real.exp_bound_div_one_sub_of_interval' h (by linarith)).le
      have h3 : 1 / (1 - lam) ≤ 1 + 2 * lam := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith
      linarith
  have : u ≤ l * (1 + 2 * lam) := c₁.trans (mul_le_mul_of_nonneg_left hexp p.le)
  nlinarith

/-! ### Absolute widths -/

theorem AEncl.add [NeZero w] (ha : AEncl a x ε₁) (hb : AEncl b y ε₂) {B : ℝ}
    (hB : |x + y| + ε₁ + ε₂ ≤ B) :
    AEncl (Encl.add w a b) (x + y) (ε₁ + ε₂ + 4 * B * (1 / 2 : ℝ) ^ w) := by
  obtain ⟨l₁, h₁, hl₁, hh₁, a₁, b₁, c₁⟩ := ha
  obtain ⟨l₂, h₂, hl₂, hh₂, a₂, b₂, c₂⟩ := hb
  obtain ⟨r, hr, hr1, hr2⟩ := addFloor_abs hl₁ hl₂ w
  obtain ⟨s, hs, hs1, hs2⟩ := addCeiling_abs hh₁ hh₂ w
  have hu0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
  have hxy := abs_le.mp (le_refl |x + y|)
  have hlB : |l₁ + l₂| ≤ B := by
    rw [abs_le]
    constructor <;> linarith
  have hhB : |h₁ + h₂| ≤ B := by
    rw [abs_le]
    constructor <;> linarith
  refine ⟨r, s, hr, hs, by linarith, by linarith, ?_⟩
  nlinarith [mul_le_mul_of_nonneg_right hlB hu0, mul_le_mul_of_nonneg_right hhB hu0]

theorem AEncl.sub [NeZero w] (ha : AEncl a x ε₁) (hb : AEncl b y ε₂) {B : ℝ}
    (hB : |x - y| + ε₁ + ε₂ ≤ B) :
    AEncl (Encl.sub w a b) (x - y) (ε₁ + ε₂ + 4 * B * (1 / 2 : ℝ) ^ w) := by
  obtain ⟨l₁, h₁, hl₁, hh₁, a₁, b₁, c₁⟩ := ha
  obtain ⟨l₂, h₂, hl₂, hh₂, a₂, b₂, c₂⟩ := hb
  obtain ⟨r, hr, hr1, hr2⟩ := subFloor_abs hl₁ hh₂ w
  obtain ⟨s, hs, hs1, hs2⟩ := subCeiling_abs hh₁ hl₂ w
  have hu0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
  have hxy := abs_le.mp (le_refl |x - y|)
  have hlB : |l₁ - h₂| ≤ B := by
    rw [abs_le]
    constructor <;> linarith
  have hhB : |h₁ - l₂| ≤ B := by
    rw [abs_le]
    constructor <;> linarith
  refine ⟨r, s, hr, hs, by linarith, by linarith, ?_⟩
  nlinarith [mul_le_mul_of_nonneg_right hlB hu0, mul_le_mul_of_nonneg_right hhB hu0]

theorem AEncl.subNonneg [NeZero w] (ha : AEncl a x ε₁) (hb : AEncl b y ε₂) (hxy : y ≤ x)
    {B : ℝ} (hB : |x - y| + ε₁ + ε₂ ≤ B) :
    AEncl0 (Encl.subNonneg w a b) (x - y) (ε₁ + ε₂ + 4 * B * (1 / 2 : ℝ) ^ w) := by
  obtain ⟨r, s, hr, hs, h1, h2, h3⟩ := ha.sub (w := w) hb hB
  obtain ⟨c, hc, hc0, hcle, hceq⟩ := clampNonneg_spec hr
  refine ⟨c, s, hc, hs, hc0, hcle.trans (max_le h1 (by linarith)), h2, ?_⟩
  rcases le_or_gt 0 r with h | h
  · rw [hceq h]; exact h3
  · linarith

/-- The product of two nonnegative enclosures. -/
theorem AEncl0.mul [NeZero w] (ha : AEncl0 a x ε₁) (hb : AEncl0 b y ε₂) {B₁ B₂ : ℝ}
    (hB₁ : x + ε₁ ≤ B₁) (hB₂ : y + ε₂ ≤ B₂) :
    AEncl0 (Encl.mul w a b) (x * y) (ε₁ * B₂ + ε₂ * B₁ + 4 * B₁ * B₂ * (1 / 2 : ℝ) ^ w) := by
  obtain ⟨l₁, h₁, hl₁, hh₁, p₁, a₁, b₁, c₁⟩ := ha
  obtain ⟨l₂, h₂, hl₂, hh₂, p₂, a₂, b₂, c₂⟩ := hb
  have hx : 0 ≤ x := by linarith
  have hy : 0 ≤ y := by linarith
  have hh₁0 : 0 ≤ h₁ := by linarith
  have hh₂0 : 0 ≤ h₂ := by linarith
  obtain ⟨r, hr, hfr⟩ := mulFloor_err hl₁ hl₂ w (by positivity)
  obtain ⟨s, hs, hcs⟩ := mulCeiling_err hh₁ hh₂ w (by positivity)
  have hu0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
  have hh₁B : h₁ ≤ B₁ := by linarith
  have hh₂B : h₂ ≤ B₂ := by linarith
  have hB₁0 : 0 ≤ B₁ := by linarith
  have hB₂0 : 0 ≤ B₂ := by linarith
  refine ⟨r, s, hr, hs, hfr.nonneg, hfr.le.trans (mul_le_mul a₁ a₂ p₂ hx),
    (mul_le_mul b₁ b₂ hy hh₁0).trans hcs.ge, ?_⟩
  have hprod : h₁ * h₂ ≤ B₁ * B₂ := mul_le_mul hh₁B hh₂B hh₂0 hB₁0
  have hlprod : l₁ * l₂ ≤ B₁ * B₂ := (mul_le_mul (by linarith) (by linarith) p₂ hh₁0).trans hprod
  have hdiff : h₁ * h₂ - l₁ * l₂ ≤ ε₁ * B₂ + ε₂ * B₁ := by
    have e : h₁ * h₂ - l₁ * l₂ = (h₁ - l₁) * h₂ + l₁ * (h₂ - l₂) := by ring
    rw [e]
    have t1 : (h₁ - l₁) * h₂ ≤ ε₁ * B₂ :=
      mul_le_mul c₁ hh₂B hh₂0 (by linarith)
    have t2 : l₁ * (h₂ - l₂) ≤ B₁ * ε₂ :=
      mul_le_mul (by linarith) c₂ (by linarith) hB₁0
    linarith
  have r1 := hfr.ge
  have r2 := hcs.le
  have e1 : 2 * (l₁ * l₂) * (1 / 2 : ℝ) ^ w ≤ 2 * (B₁ * B₂) * (1 / 2 : ℝ) ^ w := by gcongr
  have e2 : 2 * (h₁ * h₂) * (1 / 2 : ℝ) ^ w ≤ 2 * (B₁ * B₂) * (1 / 2 : ℝ) ^ w := by gcongr
  linarith

theorem AEncl.half (h : AEncl a x ε) : AEncl (Encl.half a) (x / 2) (ε / 2) := by
  obtain ⟨l, u, hl, hu, h1, h2, h3⟩ := h
  have e1 := toVal_shiftLeft_of_toVal hl (AzInt.ofInt (-1))
  have e2 := toVal_shiftLeft_of_toVal hu (AzInt.ofInt (-1))
  rw [AzInt.toInt_ofInt, zpow_neg_one, ← div_eq_mul_inv] at e1 e2
  exact ⟨l / 2, u / 2, e1, e2, by linarith, by linarith, by linarith⟩

theorem AEncl.clamp0 (ha : AEncl a x ε) (hx : 0 ≤ x) : AEncl0 (clampNonneg a.1, a.2) x ε := by
  obtain ⟨l, h, hl, hh, h1, h2, h3⟩ := ha
  obtain ⟨c, hc, hc0, hcle, hceq⟩ := clampNonneg_spec hl
  refine ⟨c, h, hc, hh, hc0, hcle.trans (max_le h1 hx), h2, ?_⟩
  rcases le_or_gt 0 l with h' | h'
  · rw [hceq h']; exact h3
  · linarith

/-! ### The logarithm of an enclosure -/

/-- The width of the logarithm bracket for arguments with `|ln y| ≤ G`. -/
noncomputable def lnW (G : ℝ) (w : ℕ) : ℝ :=
  2 ^ 42 * ((w : ℝ) + 2 * G + 10) ^ 5 * (1 / 2 : ℝ) ^ w

theorem lnW_nonneg {G : ℝ} (hG : 0 ≤ G) (w : ℕ) : 0 ≤ lnW G w := by
  unfold lnW
  positivity

/-- **The logarithm of an enclosure**: a relative width `lam` gives the absolute width
`lnW G w + 5 lam`. -/
theorem LEncl.lnOfEncl (h : LEncl a x lam) (h0 : 0 ≤ lam) (h1 : lam ≤ 1 / 2) {G : ℝ}
    (hG : |Real.log x| ≤ G) (hw : 64 ≤ w) :
    AEncl (lnOfEncl a w) (Real.log x) (lnW G w + 5 * lam) := by
  obtain ⟨l, u, hl, hu, p, a₁, b₁, c₁⟩ := h
  have hG0 : 0 ≤ G := (abs_nonneg _).trans hG
  obtain ⟨e, q, m, hm, heq⟩ := exists_finite_true_of_toVal_pos hl p
  have hyeq : a = (finite true e q m hm, a.2) := Prod.ext heq rfl
  rw [heq, toVal_finite, Option.some.injEq, EReal.coe_eq_coe_iff] at hl
  rw [hyeq]
  obtain ⟨lv, up, hlv, hup, k1, k2, k3⟩ := lnOfEncl_core hm hu (hl ▸ a₁) b₁ hw
  rw [hl] at k3
  refine ⟨lv, up, hlv, hup, k1, k2, k3.trans ?_⟩
  have hx : 0 < x := by linarith
  have hu0 : 0 < u := by linarith
  have hpw : (1 / 2 : ℝ) ^ w ≤ 1 / 8 := by
    calc (1 / 2 : ℝ) ^ w ≤ (1 / 2 : ℝ) ^ 3 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 8 := by norm_num
  have hpw0 : (0 : ℝ) < (1 / 2 : ℝ) ^ w := by positivity
  -- the relative width
  have hexp : Real.exp lam ≤ 1 + 2 * lam := by
    rcases h0.eq_or_lt with h | h
    · rw [← h]; simp
    · have h2 := (Real.exp_bound_div_one_sub_of_interval' h (by linarith)).le
      have h3 : 1 / (1 - lam) ≤ 1 + 2 * lam := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith
      linarith
  have hρ : (u - l) / l ≤ 2 * lam := by
    rw [div_le_iff₀ p]
    have : u ≤ l * (1 + 2 * lam) := c₁.trans (mul_le_mul_of_nonneg_left hexp p.le)
    linarith
  have hρ0 : 0 ≤ (u - l) / l := div_nonneg (by linarith) p.le
  -- `|ln l| ≤ G + lam`
  have hlogl : |Real.log l| ≤ G + lam := by
    have hG' := abs_le.mp hG
    have h1' : Real.log l ≤ Real.log x := Real.log_le_log p a₁
    have h2' : Real.log x ≤ Real.log u := Real.log_le_log hx b₁
    have h3' : Real.log u ≤ Real.log l + lam := by
      have := Real.log_le_log hu0 c₁
      rwa [Real.log_mul p.ne' (Real.exp_pos _).ne', Real.log_exp] at this
    rw [abs_le]
    constructor <;> linarith
  -- the exponent
  have hbd := abs_finiteVal_bounds true e hm
  rw [hl, abs_of_pos p] at hbd
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2' : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hlo : ((e.toInt : ℝ) - 1) * Real.log 2 ≤ Real.log l := by
    have := Real.log_le_log (by positivity) hbd.1
    rwa [Real.log_zpow, Int.cast_sub, Int.cast_one] at this
  have hhi : Real.log l < (e.toInt : ℝ) * Real.log 2 := by
    have := Real.log_lt_log p hbd.2
    rwa [Real.log_zpow] at this
  have he : |(e.toInt : ℝ)| ≤ 2 * G + 2 := by
    have habs := abs_le.mp hlogl
    rw [abs_le]
    constructor
    · -- `e ≥ −(2G + 2)`
      by_contra hcon
      push Not at hcon
      have hneg : (e.toInt : ℝ) < 0 := by linarith
      have : (e.toInt : ℝ) * Real.log 2 ≤ (e.toInt : ℝ) * (1 / 2) :=
        mul_le_mul_of_nonpos_left hlog2 hneg.le
      linarith
    · by_contra hcon
      push Not at hcon
      have hpos : (0 : ℝ) ≤ (e.toInt : ℝ) - 1 := by linarith
      have : ((e.toInt : ℝ) - 1) * (1 / 2) ≤ ((e.toInt : ℝ) - 1) * Real.log 2 :=
        mul_le_mul_of_nonneg_left hlog2 hpos
      linarith
  set E₀ : ℝ := 2 ^ 40 * ((w : ℝ) + 2 * G + 10) ^ 5 * (1 / 2 : ℝ) ^ w with hE₀
  have hbase : (1 : ℝ) ≤ (w : ℝ) + 2 * G + 10 := by
    have : (0 : ℝ) ≤ w := Nat.cast_nonneg w
    linarith
  have hE : lnEps e.toInt w ≤ E₀ := by
    unfold lnEps
    rw [hE₀]
    have hw0 : (0 : ℝ) ≤ w := Nat.cast_nonneg w
    have hle : (w : ℝ) + |((e.toInt : ℤ) : ℝ)| + 8 ≤ (w : ℝ) + 2 * G + 10 := by linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hle 5) (by norm_num)) hpw0.le
  have hE0 : 0 ≤ lnEps e.toInt w := by
    unfold lnEps
    positivity
  have hGE : 2 * (G + 1) * (1 / 2 : ℝ) ^ w ≤ E₀ := by
    rw [hE₀]
    have h5 : (w : ℝ) + 2 * G + 10 ≤ ((w : ℝ) + 2 * G + 10) ^ 5 :=
      le_self_pow₀ hbase (by norm_num)
    have h40 : (1 : ℝ) ≤ 2 ^ 40 := by norm_num
    have : 2 * (G + 1) ≤ 2 ^ 40 * ((w : ℝ) + 2 * G + 10) ^ 5 := by nlinarith
    exact mul_le_mul_of_nonneg_right this hpw0.le
  have hlnW : lnW G w = 4 * E₀ := by
    rw [lnW, hE₀]
    ring
  rw [hlnW]
  have hE₀0 : 0 ≤ E₀ := hE0.trans hE
  -- assemble
  have t1 : 2 * (|Real.log l| + lnEps e.toInt w + 2 * ((u - l) / l)) * (1 / 2 : ℝ) ^ w
      ≤ 2 * (G + 1) * (1 / 2 : ℝ) ^ w + E₀ / 4 + lam := by
    have s1 : |Real.log l| ≤ G + 1 := by linarith
    have s2 : 2 * (|Real.log l| + lnEps e.toInt w + 2 * ((u - l) / l)) * (1 / 2 : ℝ) ^ w
        ≤ 2 * ((G + 1) + E₀ + 4 * lam) * (1 / 2 : ℝ) ^ w := by
      have hsum : |Real.log l| + lnEps e.toInt w + 2 * ((u - l) / l)
          ≤ (G + 1) + E₀ + 4 * lam := by linarith
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum (by norm_num)) hpw0.le
    have s3 : 2 * ((G + 1) + E₀ + 4 * lam) * (1 / 2 : ℝ) ^ w
        = 2 * (G + 1) * (1 / 2 : ℝ) ^ w + (2 * E₀ + 8 * lam) * (1 / 2 : ℝ) ^ w := by ring
    have s4 : (2 * E₀ + 8 * lam) * (1 / 2 : ℝ) ^ w ≤ (2 * E₀ + 8 * lam) * (1 / 8) :=
      mul_le_mul_of_nonneg_left hpw (by linarith)
    linarith
  linarith

end Azurite.AzFloat
