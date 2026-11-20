/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.PolygammaWidth

/-!
# The bracket of the digamma function converges

The width of `digammaEncl x e pos w` tends to `0` with the Ziv level.

* `psiSumLoop_eq`, `digammaStirlingEncl_width`: the asymptotic series, an `altSumLoop`.
* `harmonicLoop_ratio`, `harmonicEncl_width`: the shift sum.
* `digammaPosEncl_conv`, `digammaCot_width`, `digammaEncl_conv`, `digammaApprox_bracketConv`.
-/

namespace Azurite.AzFloat

open Finset Filter Topology

/-! ### The asymptotic series -/

/-- The loop of `ψ` is the generic one. -/
theorem psiSumLoop_eq (V : ℕ) (T : Array AzNat) (inv2 : Encl) (tol : AzFloat) :
    ∀ (fuel k : ℕ) (p acc : Encl), psiSumLoop V T inv2 tol fuel k p acc
      = altSumLoop V (psiTermEncl V T) inv2 tol fuel k p acc
  | 0, k, p, acc => by rw [psiSumLoop, altSumLoop]
  | fuel + 1, k, p, acc => by
    rw [psiSumLoop, altSumLoop, psiSumLoop_eq V T inv2 tol fuel]

theorem polyT_zero (k : ℕ) (y : ℝ) : polyT 0 k y = psiCoeffT k / y ^ (2 * k) := by
  simp [polyT]

/-- **The width of the asymptotic series of `ψ` on enclosures**, for `y ≥ 1`: `T` bounds the
terms, `Lam` their relative widths, `εS` the width of the sum, `G` the logarithm, `C` the
magnitudes. -/
theorem digammaStirlingEncl_width {V : ℕ} (hV : 64 ≤ V) {M : ℕ} (hM : 1 ≤ M) {Y : Encl}
    {y lamY : ℝ} (hY : LEncl Y y lamY) (hlamY : 0 ≤ lamY) (hy1 : 1 ≤ y) {tol : AzFloat}
    {tolv : ℝ} (htol : tol.toVal = some (tolv : EReal)) {T B Lam εS G C : ℝ} (hT0 : 0 ≤ T)
    (hterm : ∀ k, 1 ≤ k → k ≤ M → polyT 0 k y ≤ T)
    (hLamge : (M + 1) * (2 * lamY + 24 * (1 / 2 : ℝ) ^ V) ≤ Lam) (hLam : Lam ≤ 1 / 2)
    (hBu : 4 * B * (1 / 2 : ℝ) ^ V ≤ 1)
    (hB : M * (T + 2 * T * Lam + 1) + 2 * T + 1 ≤ B)
    (hεSge : M * (2 * T * Lam + 4 * B * (1 / 2 : ℝ) ^ V) + max tolv (2 * polyT 0 M y)
      + 2 * B * (1 / 2 : ℝ) ^ V ≤ εS) (hεS : εS ≤ 1)
    (hG : |Real.log y| ≤ G) (hlnW : lnW G V + 5 * lamY ≤ 1)
    (hC : G + T + 5 ≤ C) (hCu : 4 * C * (1 / 2 : ℝ) ^ V ≤ 1)
    (hlam6 : lamY + 6 * (1 / 2 : ℝ) ^ V ≤ 1 / 2) :
    AEncl (digammaStirlingEncl V M Y tol) (DLMF.psiR y)
      (lnW G V + 5 * lamY + (lamY + 6 * (1 / 2 : ℝ) ^ V) + εS + 8 * C * (1 / 2 : ℝ) ^ V) := by
  have : NeZero V := ⟨by omega⟩
  have hu : (1 / 2 : ℝ) ^ V ≤ 1 / 8 := half_pow_le_eighth (by omega)
  have hu0 : (0 : ℝ) < (1 / 2 : ℝ) ^ V := by positivity
  have hy : 0 < y := by linarith
  have hinvle : 1 / y ≤ 1 := by rw [div_le_one hy]; exact hy1
  have hinv0 : 0 < 1 / y := by positivity
  have hinv : LEncl (Encl.div V (Encl.exact one) Y) (1 / y) (lamY + 6 * (1 / 2 : ℝ) ^ V) :=
    ((LEncl.exact toVal_one' one_pos).div hu hY).mono (by linarith)
  have hinv2 : LEncl (Encl.mul V (Encl.div V (Encl.exact one) Y)
      (Encl.div V (Encl.exact one) Y)) (1 / y ^ 2) (2 * lamY + 18 * (1 / 2 : ℝ) ^ V) := by
    have := (hinv.mul hu hinv).mono (le_of_eq (by ring :
      lamY + 6 * (1 / 2 : ℝ) ^ V + (lamY + 6 * (1 / 2 : ℝ) ^ V) + 6 * (1 / 2 : ℝ) ^ V
        = 2 * lamY + 18 * (1 / 2 : ℝ) ^ V))
    convert this using 1
    field_simp
  -- the sum
  have hμ : ∀ k, 1 ≤ k → k ≤ M → ∃ r : ℝ, -psiNu y = altPartial (fun k => polyT 0 k y) k + r ∧
      0 ≤ (-1) ^ (k + 1) * r ∧ |r| ≤ polyT 0 k y := by
    intro k hk _
    obtain ⟨r, hr, hsign, habs⟩ := psiNu_eq_sum_add hk hy
    refine ⟨-r, ?_, by rw [pow_succ]; linarith, by rw [abs_neg, polyT_zero]; exact habs⟩
    rw [hr]
    unfold altPartial
    have : ∑ i ∈ range (k - 1), (-1 : ℝ) ^ (i + 1 + 1) * polyT 0 (i + 1) y
        = -∑ i ∈ range (k - 1), psiTermT (i + 1) y := by
      rw [← sum_neg_distrib]
      refine sum_congr rfl fun i _ => ?_
      rw [polyT_zero, psiTermT, pow_succ]
      ring
    rw [this]
    ring
  have hacc : AEncl (Encl.exact zero) (altPartial (fun k => polyT 0 k y) 1) 0 := by
    have h : zero.toVal = some ((0 : ℝ) : EReal) := by rw [toVal_zero, EReal.coe_zero]
    unfold altPartial
    rw [Nat.sub_self, range_zero, sum_empty]
    exact ⟨0, 0, h, h, le_rfl, le_rfl, by simp⟩
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hLam0 : 0 ≤ Lam := le_trans (by positivity) hLamge
  have hB0 : 0 ≤ B := by
    have := mul_nonneg (Nat.cast_nonneg (α := ℝ) M)
      (by nlinarith [mul_nonneg hT0 hLam0] : (0 : ℝ) ≤ T + 2 * T * Lam + 1)
    linarith
  have hD0 : 0 ≤ 2 * T * Lam + 4 * B * (1 / 2 : ℝ) ^ V := by
    have := mul_nonneg hB0 hu0.le
    nlinarith [mul_nonneg hT0 hLam0]
  have hcond : 2 * lamY + 18 * (1 / 2 : ℝ) ^ V
      + ((M - 1 : ℕ) : ℝ) * (2 * lamY + 18 * (1 / 2 : ℝ) ^ V + 6 * (1 / 2 : ℝ) ^ V)
      + 12 * (1 / 2 : ℝ) ^ V ≤ Lam := by
    refine le_trans ?_ hLamge
    rw [Nat.cast_sub hM]
    push_cast
    nlinarith
  have hS := altSumLoop_width (V := V) (M := M) (t := fun k => polyT 0 k y)
    (q := fun k => 1 / y ^ (2 * k)) (term := psiTermEncl V (AzNat.tangentNumbers M))
    (c := 12) (μ := -psiNu y) (i2 := 1 / y ^ 2) hu hinv2
    (fun k => by
      show 1 / y ^ (2 * (k + 1)) = 1 / y ^ (2 * k) * (1 / y ^ 2)
      rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add]
      field_simp) htol hLam hT0 (by norm_num)
    (fun k hk _ => polyT_pos 0 hk hy) hterm
    (fun k p lam hk hkM hp => by
      show LEncl _ (polyT 0 k y) _
      rw [polyT_zero]
      exact psiTermEncl_width hu hk hkM hp) hμ hBu hB (M - 1) 1 _ _
    (2 * lamY + 18 * (1 / 2 : ℝ) ^ V) 0 le_rfl (by omega) (by simpa using hinv2)
    (by positivity) hcond hacc (by simp)
  rw [← psiSumLoop_eq] at hS
  have hS' := hS.mono (ε' := εS) (by
    have hM' : ((M - 1 : ℕ) : ℝ) ≤ M := by exact_mod_cast Nat.sub_le M 1
    have := mul_le_mul_of_nonneg_right hM' hD0
    linarith)
  have hnuT : |psiNu y| ≤ T := by
    obtain ⟨r, hr, -, habs⟩ := hμ 1 le_rfl hM
    have h0 : altPartial (fun k => polyT 0 k y) 1 = 0 := by
      unfold altPartial
      rw [Nat.sub_self, range_zero, sum_empty]
    rw [h0, zero_add] at hr
    rw [← abs_neg, hr]
    exact habs.trans (hterm 1 le_rfl hM)
  -- the logarithm and `1/(2y)`
  have hln := hY.lnOfEncl hlamY (by linarith) hG hV
  have hhalf := ((hinv.toA (by positivity) hlam6).toA.mono
    (ε' := 2 * (lamY + 6 * (1 / 2 : ℝ) ^ V)) (by
      have h2 : (0 : ℝ) ≤ lamY + 6 * (1 / 2 : ℝ) ^ V := by positivity
      nlinarith)).half
  have hGa := abs_le.mp hG
  have hnu := abs_le.mp hnuT
  have h1 := hln.sub (w := V) hhalf (B := C) (by
    have : |Real.log y - 1 / y / 2| ≤ G + 1 := by
      rw [abs_le]
      constructor <;> linarith
    linarith)
  have h2 := h1.sub (w := V) hS' (B := C) (by
    have : |Real.log y - 1 / y / 2 - -psiNu y| ≤ G + 1 + T := by
      rw [abs_le]
      constructor <;> linarith
    linarith)
  unfold digammaStirlingEncl
  have e : Real.log y - 1 / y / 2 - -psiNu y = DLMF.psiR y := by
    rw [psiNu]
    field_simp
    ring
  rw [e] at h2
  refine h2.mono (le_of_eq ?_)
  ring

/-! ### The shift sum -/

/-- The upper sum of `harmonicLoop` is the lower one within the factor
`((1 + E)/(1 − E))^m`, `E = 2^(1−V)`. -/
theorem harmonicLoop_ratio {V : ℕ} [NeZero V] (hV : 8 ≤ V) {bF : AzFloat} {b : ℝ}
    (hb : bF.toVal = some (b : EReal)) (hb0 : 0 < b) :
    ∀ (m i : ℕ) (lo up : AzFloat) (lov upv c : ℝ), lo.toVal = some (lov : EReal) →
      up.toVal = some (upv : EReal) → 0 ≤ lov → 0 ≤ upv → 1 ≤ c → upv ≤ lov * c →
      ∃ lo' up' : ℝ, (harmonicLoop V bF m i lo up).1.toVal = some (lo' : EReal) ∧
        (harmonicLoop V bF m i lo up).2.toVal = some (up' : EReal) ∧ 0 ≤ up' ∧
        up' ≤ lo' * (c * ((1 + 2 * (1 / 2 : ℝ) ^ V) / (1 - 2 * (1 / 2 : ℝ) ^ V)) ^ m)
  | 0, i, lo, up, lov, upv, c, hlo, hup, h0, h1, hc, h2 => by
    rw [harmonicLoop, pow_zero, mul_one]
    exact ⟨lov, upv, hlo, hup, h1, h2⟩
  | 1, i, lo, up, lov, upv, c, hlo, hup, h0, h1, hc, h2 => by
    obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = 2 * (1 / 2 : ℝ) ^ V := ⟨_, rfl⟩
    rw [← hEdef]
    have hE0 : 0 ≤ E := by rw [hEdef]; positivity
    have hE1 : E ≤ 1 / 64 := by
      have : (1 / 2 : ℝ) ^ V ≤ (1 / 2) ^ 8 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hV
      rw [hEdef]; norm_num at this ⊢; linarith
    have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    obtain ⟨y, hy, hy1, -⟩ := addCeiling_abs hb (toVal_ofAzNat_ofNat i) V
    have hy0 : 0 < y := by linarith
    obtain ⟨q, hq, -, hq2⟩ := divFloor_abs toVal_one' hy hy0.ne' V
    rw [abs_of_pos (by positivity)] at hq2
    have hq0 : 0 ≤ q := by
      have : 0 ≤ 1 / y * (1 - E) := mul_nonneg (by positivity) (by linarith)
      rw [hEdef] at this
      linarith
    obtain ⟨lo', hlo', -, hlo'2⟩ := addFloor_abs hlo hq V
    rw [abs_of_nonneg (by linarith)] at hlo'2
    obtain ⟨up', hup', hup'1, hup'2⟩ := addCeiling_abs hup hq V
    rw [abs_of_nonneg (by linarith)] at hup'2
    have hlo'ge : (lov + q) * (1 - E) ≤ lo' := by rw [hEdef]; linarith
    have hup'le : up' ≤ (upv + q) * (1 + E) := by rw [hEdef]; linarith
    have h1E : 0 < 1 - E := by linarith
    obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = (1 + E) / (1 - E) := ⟨_, rfl⟩
    rw [← hρ]
    have hρ0 : 0 ≤ ρ := by rw [hρ]; exact div_nonneg (by linarith) h1E.le
    have hρe : (1 - E) * ρ = 1 + E := by
      rw [hρ]
      field_simp
    rw [harmonicLoop, pow_one]
    refine ⟨lo', up', hlo', hup', by linarith, ?_⟩
    have a1 : upv + q ≤ (lov + q) * c := by nlinarith
    have a2 : (upv + q) * (1 + E) ≤ (lov + q) * c * (1 + E) :=
      mul_le_mul_of_nonneg_right a1 (by linarith)
    have a3 : (lov + q) * c * (1 + E) = (lov + q) * (1 - E) * (c * ρ) := by
      rw [← hρe]
      ring
    have a4 : (lov + q) * (1 - E) * (c * ρ) ≤ lo' * (c * ρ) :=
      mul_le_mul_of_nonneg_right hlo'ge (by positivity)
    linarith
  | m + 2, i, lo, up, lov, upv, c, hlo, hup, h0, h1, hc, h2 => by
    obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = 2 * (1 / 2 : ℝ) ^ V := ⟨_, rfl⟩
    rw [← hEdef]
    have hE0 : 0 ≤ E := by rw [hEdef]; positivity
    have hE1 : E ≤ 1 / 64 := by
      have : (1 / 2 : ℝ) ^ V ≤ (1 / 2) ^ 8 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hV
      rw [hEdef]; norm_num at this ⊢; linarith
    have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    obtain ⟨y, hy, hy1, -⟩ := addCeiling_abs hb (toVal_ofAzNat_ofNat i) V
    have hy0 : 0 < y := by linarith
    obtain ⟨yf, hyf, -, hyf2⟩ := addFloor_abs hy toVal_one' V
    rw [abs_of_pos (by linarith)] at hyf2
    obtain ⟨yc, hyc, hyc1, -⟩ := addCeiling_abs hy toVal_one' V
    have hu' : (1 / 2 : ℝ) ^ V ≤ 1 / 128 := by rw [hEdef] at hE1; linarith
    have hyf0 : 0 ≤ yf := by
      have := mul_le_mul_of_nonneg_left hu' (by linarith : (0 : ℝ) ≤ 2 * (y + 1))
      linarith
    obtain ⟨N, hN, -, hN2⟩ := addFloor_abs hy hyf V
    rw [abs_of_pos (by linarith)] at hN2
    obtain ⟨D, hD, hD1, -⟩ := mulCeiling_abs hy hyc V
    have hD0 : 0 < D := lt_of_lt_of_le (mul_pos hy0 (by linarith)) hD1
    have hN0 : 0 ≤ N := by
      have := mul_le_mul_of_nonneg_left hu' (by linarith : (0 : ℝ) ≤ 2 * (y + yf))
      linarith
    obtain ⟨q, hq, -, hq2⟩ := divFloor_abs hN hD hD0.ne' V
    rw [abs_of_nonneg (div_nonneg hN0 hD0.le)] at hq2
    have hq0 : 0 ≤ q := by
      have : 0 ≤ N / D * (1 - E) := mul_nonneg (div_nonneg hN0 hD0.le) (by linarith)
      rw [hEdef] at this
      linarith
    obtain ⟨lo', hlo', -, hlo'2⟩ := addFloor_abs hlo hq V
    rw [abs_of_nonneg (by linarith)] at hlo'2
    obtain ⟨up', hup', hup'1, hup'2⟩ := addCeiling_abs hup hq V
    rw [abs_of_nonneg (by linarith)] at hup'2
    have hlo'ge : (lov + q) * (1 - E) ≤ lo' := by rw [hEdef]; linarith
    have hup'le : up' ≤ (upv + q) * (1 + E) := by rw [hEdef]; linarith
    have hlo'0 : 0 ≤ lo' := le_trans (mul_nonneg (by linarith) (by linarith)) hlo'ge
    have h1E : 0 < 1 - E := by linarith
    obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = (1 + E) / (1 - E) := ⟨_, rfl⟩
    rw [← hρ]
    have hρ1 : 1 ≤ ρ := by
      rw [hρ, le_div_iff₀ h1E]
      linarith
    have hρe : (1 - E) * ρ = 1 + E := by
      rw [hρ]
      field_simp
    have hstep : up' ≤ lo' * (c * ρ) := by
      have a1 : upv + q ≤ (lov + q) * c := by nlinarith
      have a2 : (upv + q) * (1 + E) ≤ (lov + q) * c * (1 + E) :=
        mul_le_mul_of_nonneg_right a1 (by linarith)
      have a3 : (lov + q) * c * (1 + E) = (lov + q) * (1 - E) * (c * ρ) := by
        rw [← hρe]
        ring
      have a4 : (lov + q) * (1 - E) * (c * ρ) ≤ lo' * (c * ρ) :=
        mul_le_mul_of_nonneg_right hlo'ge (by positivity)
      linarith
    obtain ⟨lo'', up'', e1, e2, e3, e4⟩ :=
      harmonicLoop_ratio hV hb hb0 m (i + 2) _ _ lo' up' (c * ρ) hlo' hup' hlo'0
        (by linarith) (by nlinarith) hstep
    rw [← hEdef, ← hρ] at e4
    have hlo''0 : 0 ≤ lo'' := by
      by_contra hneg
      push Not at hneg
      have hc0 : 0 < c := by linarith
      have hρpos : 0 < ρ := by linarith
      have : lo'' * (c * ρ * ρ ^ m) < 0 := mul_neg_of_neg_of_pos hneg (by positivity)
      linarith
    rw [harmonicLoop]
    refine ⟨lo'', up'', e1, e2, e3, e4.trans ?_⟩
    refine mul_le_mul_of_nonneg_left ?_ hlo''0
    have hpos : 0 ≤ c * ρ ^ m * ρ := by positivity
    calc c * ρ * ρ ^ m = c * ρ ^ m * ρ * 1 := by ring
      _ ≤ c * ρ ^ m * ρ * ρ := mul_le_mul_of_nonneg_left hρ1 hpos
      _ = c * ρ ^ (m + 2) := by ring

/-- **The relative width of the harmonic shift sum.** -/
theorem harmonicEncl_width {V : ℕ} [NeZero V] (hV : 8 ≤ V) {X : Encl} {xv lam₀ : ℝ}
    (hX : LEncl X xv lam₀) {i : ℕ} (hi : 1 ≤ i) :
    LEncl (harmonicEncl V X i) (∑ j ∈ range i, 1 / (xv + j))
      (lam₀ + (80 + 6 * i) * (1 / 2 : ℝ) ^ V) := by
  obtain ⟨l₀, h₀, hl₀, hh₀, hspec1, hspec2⟩ := harmonicEncl_spec hV hX.isEnclPos i
  obtain ⟨a, b, ha, hb, ha0, hax, hxb, hba⟩ := hX
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (1 / 2 : ℝ) ^ V := ⟨_, rfl⟩
  rw [← hu]
  have hu0 : 0 < u := by rw [hu]; positivity
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = 2 * u := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by rw [hEdef]; positivity
  have hE1 : E ≤ 1 / 64 := by
    have : (1 / 2 : ℝ) ^ V ≤ (1 / 2) ^ 8 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hV
    rw [hEdef, hu]; norm_num at this ⊢; linarith
  have hb0 : 0 < b := by linarith
  have hexpE : 1 + E ≤ Real.exp E := by linarith [Real.add_one_le_exp E]
  obtain ⟨lo, up, hlo, hup, hup0, hratio⟩ := harmonicLoop_ratio hV hb hb0 i 0 zero zero 0 0 1
    toVal_zero' toVal_zero' le_rfl le_rfl le_rfl (by simp)
  rw [one_mul, ← hu, ← hEdef] at hratio
  have hρ : (1 + E) / (1 - E) ≤ Real.exp (3 * E) := by
    rw [div_le_iff₀ (by linarith)]
    have := Real.add_one_le_exp (3 * E)
    nlinarith [Real.exp_pos (3 * E)]
  have hρ0 : 0 ≤ (1 + E) / (1 - E) := div_nonneg (by linarith) (by linarith)
  have hρi : ((1 + E) / (1 - E)) ^ i ≤ Real.exp (3 * E * i) := by
    calc ((1 + E) / (1 - E)) ^ i ≤ Real.exp (3 * E) ^ i := pow_le_pow_left₀ hρ0 hρ i
      _ = Real.exp (3 * E * i) := by rw [← Real.exp_nat_mul]; ring_nf
  -- the factor
  obtain ⟨R, hR, hR1, hR2⟩ := divCeiling_abs hb ha ha0.ne' V
  have hba0 : 0 < b / a := div_pos hb0 ha0
  rw [abs_of_pos hba0, ← hu] at hR2
  have hR0 : 0 < R := lt_of_lt_of_le hba0 hR1
  have hbae : b / a ≤ Real.exp lam₀ := by
    rw [div_le_iff₀ ha0]
    linarith
  have hRe : R ≤ Real.exp (lam₀ + E) := by
    rw [Real.exp_add]
    calc R ≤ b / a * (1 + E) := by rw [hEdef]; linarith
      _ ≤ Real.exp lam₀ * Real.exp E := mul_le_mul hbae hexpE (by linarith) (Real.exp_pos _).le
  have hpow : (powerOf2 (AzInt.ofInt 6 - (AzNat.ofNat V).toAzInt)).toVal
      = some (((64 : ℝ) * u : ℝ) : EReal) := by
    rw [toVal_powerOf2, AzInt.toInt_sub, AzInt.toInt_ofInt, AzNat.toInt_toAzInt,
      AzNat.toNat_ofNat, zpow_sub₀ (by norm_num), zpow_natCast, hu, one_div_pow, one_div,
      div_eq_mul_inv]
    norm_num
  obtain ⟨o, ho, ho1, ho2⟩ := addCeiling_abs toVal_one' hpow V
  rw [abs_of_nonneg (by positivity), ← hu] at ho2
  have ho0 : 0 < o := by linarith
  have hoe : o ≤ Real.exp (64 * u + E) := by
    rw [Real.exp_add]
    calc o ≤ (1 + 64 * u) * (1 + E) := by rw [hEdef]; linarith
      _ ≤ Real.exp (64 * u) * Real.exp E :=
          mul_le_mul (by linarith [Real.add_one_le_exp (64 * u)]) hexpE (by linarith)
            (Real.exp_pos _).le
  obtain ⟨K, hK, hK1, hK2⟩ := mulCeiling_abs hR ho V
  rw [abs_of_pos (mul_pos hR0 ho0), ← hu] at hK2
  have hK0 : 0 < K := lt_of_lt_of_le (mul_pos hR0 ho0) hK1
  have hKe : K ≤ Real.exp (lam₀ + E + (64 * u + E) + E) := by
    rw [Real.exp_add, Real.exp_add (lam₀ + E)]
    calc K ≤ R * o * (1 + E) := by rw [hEdef]; linarith
      _ ≤ Real.exp (lam₀ + E) * Real.exp (64 * u + E) * Real.exp E :=
          mul_le_mul (mul_le_mul hRe hoe ho0.le (Real.exp_pos _).le) hexpE (by linarith)
            (by positivity)
  have hlo_eq : (harmonicEncl V X i).1.toVal = some (lo : EReal) := hlo
  rw [hl₀, Option.some.injEq, EReal.coe_eq_coe_iff] at hlo_eq
  subst hlo_eq
  obtain ⟨hi', hhi', hhi1, hhi2⟩ := mulCeiling_abs hup hK V
  rw [abs_of_nonneg (mul_nonneg hup0 hK0.le), ← hu] at hhi2
  have hhi_eq : (harmonicEncl V X i).2.toVal = some (hi' : EReal) := hhi'
  rw [hh₀, Option.some.injEq, EReal.coe_eq_coe_iff] at hhi_eq
  subst hhi_eq
  have hsumpos : 0 < ∑ j ∈ range i, 1 / (xv + (j : ℝ)) := by
    refine sum_pos (fun j _ => ?_) ⟨0, mem_range.mpr hi⟩
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hxv : 0 < xv := by linarith
    positivity
  have hl₀0 : 0 ≤ l₀ := by
    by_contra hneg
    push Not at hneg
    have : l₀ * ((1 + E) / (1 - E)) ^ i ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hneg.le (pow_nonneg hρ0 i)
    have h1 : h₀ ≤ 0 := by
      have : up ≤ 0 := by linarith
      have hup_eq : up = 0 := le_antisymm this hup0
      rw [hup_eq] at hhi2
      linarith
    linarith
  have hfinal : h₀ ≤ l₀ * Real.exp (lam₀ + (80 + 6 * i) * u) := by
    have s1 : up ≤ l₀ * Real.exp (3 * E * i) :=
      hratio.trans (mul_le_mul_of_nonneg_left hρi hl₀0)
    have s2 : h₀ ≤ up * K * (1 + E) := by rw [hEdef]; linarith
    have s3 : up * K * (1 + E) ≤ l₀ * Real.exp (3 * E * i)
        * Real.exp (lam₀ + E + (64 * u + E) + E) * Real.exp E :=
      mul_le_mul (mul_le_mul s1 hKe hK0.le (by positivity)) hexpE (by linarith) (by positivity)
    have s4 : l₀ * Real.exp (3 * E * i) * Real.exp (lam₀ + E + (64 * u + E) + E) * Real.exp E
        = l₀ * Real.exp (3 * E * i + (lam₀ + E + (64 * u + E) + E) + E) := by
      rw [Real.exp_add (3 * E * i + (lam₀ + E + (64 * u + E) + E)) E,
        Real.exp_add (3 * E * i) (lam₀ + E + (64 * u + E) + E)]
      ring
    have s5 : 3 * E * i + (lam₀ + E + (64 * u + E) + E) + E ≤ lam₀ + (80 + 6 * i) * u := by
      rw [hEdef]
      nlinarith
    calc h₀ ≤ _ := s2
      _ ≤ _ := s3
      _ = _ := s4
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr s5) hl₀0
  have hl₀pos : 0 < l₀ := by
    rcases hl₀0.eq_or_lt with h0 | h0
    · rw [← h0, zero_mul] at hfinal
      linarith
    · exact h0
  exact ⟨l₀, h₀, hl₀, hh₀, hl₀pos, hspec1, hspec2, hfinal⟩

/-! ### The width at level `w`, for a positive argument -/

noncomputable def dgTail (e : AzInt) (w : ℕ) : ℝ :=
  max ((1 / 2 : ℝ) ^ (w + 16))
    (2 * (((2 * lgTerms e w + 0 : ℕ) : ℝ) ^ (0 + 1) * (9 / 10 : ℝ) ^ (2 * lgTerms e w - 1)))

noncomputable def dgEpsS (e : AzInt) (w : ℕ) : ℝ :=
  2 * (pgMr w * pgT 0 w * pgLamP w * (1 / 2 : ℝ) ^ w) + 4 * (pgMr w * pgB 0 w * (1 / 2 : ℝ) ^ w)
    + dgTail e w + 2 * (pgB 0 w * (1 / 2 : ℝ) ^ w)

noncomputable def dgLnP (x : ℝ) (w : ℕ) : ℝ :=
  2 ^ 42 * (6 * (w : ℝ) + 2 * (x + w) + 10) ^ 5

noncomputable def dgC (x : ℝ) (w : ℕ) : ℝ := x + w + pgT 0 w + 5

noncomputable def dgWS (x : ℝ) (e : AzInt) (w : ℕ) : ℝ :=
  dgLnP x w * (1 / 2 : ℝ) ^ w + 90 * (1 / 2 : ℝ) ^ w + dgEpsS e w
    + 8 * (dgC x w * (1 / 2 : ℝ) ^ w)

noncomputable def dgLsh (w : ℕ) : ℝ := 88 + 6 * (w : ℝ)

noncomputable def dgHs (x : ℝ) (w : ℕ) : ℝ := (w : ℝ) / x

noncomputable def dgBf (x : ℝ) (w : ℕ) : ℝ := dgC x w + dgHs x w + 2

/-- **The width of the bracket of `ψ(x)`, `x > 0`, at level `w`** (for `w` large enough). -/
noncomputable def dgE (x : ℝ) (e : AzInt) (w : ℕ) : ℝ :=
  dgWS x e w + 2 * (dgHs x w * dgLsh w * (1 / 2 : ℝ) ^ w) + 4 * (dgBf x w * (1 / 2 : ℝ) ^ w)

theorem pb_dgLnP (x : ℝ) : PB (dgLnP x) :=
  ((((PB.natCast.const_mul 6).add (((PB.const x).add PB.natCast).const_mul 2)).add
    (PB.const 10)).pow 5).const_mul _

theorem pb_dgC (x : ℝ) : PB (dgC x) :=
  (((PB.const x).add PB.natCast).add (pb_pgT 0)).add (PB.const 5)

theorem pb_dgLsh : PB dgLsh := (PB.const 88).add (PB.natCast.const_mul 6)

theorem pb_dgHs (x : ℝ) : PB (dgHs x) := PB.natCast.div_const x

theorem pb_dgBf (x : ℝ) : PB (dgBf x) := ((pb_dgC x).add (pb_dgHs x)).add (PB.const 2)

theorem tendsto_lgTerms_atTop (e : AzInt) : Tendsto (lgTerms e) atTop atTop := by
  rw [tendsto_atTop]
  intro K
  filter_upwards [tendsto_atTop.mp (tendsto_lgTerms e) (2 * K)] with w hw
  omega

theorem tendsto_dgTail (e : AzInt) : Tendsto (dgTail e) atTop (𝓝 0) := by
  have h2 : Tendsto (fun w : ℕ => (1 / 2 : ℝ) ^ (w + 16)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
      (tendsto_add_atTop_nat 16)
  have h3 := ((tendsto_polyTail 0).comp (tendsto_lgTerms_atTop e)).const_mul 2
  rw [mul_zero] at h3
  have h4 := h2.max h3
  rw [max_self] at h4
  exact h4

theorem tendsto_dgEpsS (e : AzInt) : Tendsto (dgEpsS e) atTop (𝓝 0) := by
  have l1 := ((pb_pgMr.mul (pb_pgT 0)).mul pb_pgLamP).tendsto
  have l2 := (pb_pgMr.mul (pb_pgB 0)).tendsto
  have l3 := (pb_pgB 0).tendsto
  have := (((l1.const_mul 2).add (l2.const_mul 4)).add (tendsto_dgTail e)).add (l3.const_mul 2)
  convert this using 2
  · rfl
  · norm_num

theorem tendsto_dgWS (x : ℝ) (e : AzInt) : Tendsto (dgWS x e) atTop (𝓝 0) := by
  have l1 := (pb_dgLnP x).tendsto
  have l2 := (PB.const (90 : ℝ)).tendsto
  have l4 := (pb_dgC x).tendsto
  have := ((l1.add l2).add (tendsto_dgEpsS e)).add (l4.const_mul 8)
  convert this using 2
  · rfl
  · norm_num

theorem tendsto_dgE (x : ℝ) (e : AzInt) : Tendsto (dgE x e) atTop (𝓝 0) := by
  have l7 := ((pb_dgHs x).mul pb_dgLsh).tendsto
  have l8 := (pb_dgBf x).tendsto
  have := ((tendsto_dgWS x e).add (l7.const_mul 2)).add (l8.const_mul 4)
  convert this using 2
  · rfl
  · norm_num

/-- The size of `ψ(y)` for `y ≥ 1`. -/
theorem abs_psiR_le {y : ℝ} (hy1 : 1 ≤ y) : |DLMF.psiR y| ≤ y + 1 + polyT 0 1 y := by
  have hy : 0 < y := by linarith
  obtain ⟨r, hr, -, habs⟩ := psiNu_eq_sum_add (n := 1) le_rfl hy
  rw [Nat.sub_self, range_zero, sum_empty, zero_add] at hr
  rw [← polyT_zero] at habs
  have hr' := abs_le.mp habs
  have hlog0 : 0 ≤ Real.log y := Real.log_nonneg hy1
  have hlog1 : Real.log y ≤ y - 1 := Real.log_le_sub_one_of_pos hy
  have hinv : 1 / (2 * y) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have hinv0 : 0 ≤ 1 / (2 * y) := by positivity
  have e : DLMF.psiR y = Real.log y - 1 / (2 * y) + r := by
    rw [← hr, psiNu]
    ring
  rw [e, abs_le]
  constructor <;> linarith

/-- The width of the bracket of `ψ(x)` at level `w`, uniformly for `x ∈ [α, β]`. -/
noncomputable def dgEU (α β : ℝ) (e : AzInt) (w : ℕ) : ℝ :=
  dgWS β e w + 2 * (dgHs α w * dgLsh w * (1 / 2 : ℝ) ^ w)
    + 4 * ((dgC β w + dgHs α w + 2) * (1 / 2 : ℝ) ^ w)

theorem tendsto_dgEU (α β : ℝ) (e : AzInt) : Tendsto (dgEU α β e) atTop (𝓝 0) := by
  have l7 := ((pb_dgHs α).mul pb_dgLsh).tendsto
  have l8 := (((pb_dgC β).add (pb_dgHs α)).add (PB.const 2)).tendsto
  have := ((tendsto_dgWS β e).add (l7.const_mul 2)).add (l8.const_mul 4)
  convert this using 2
  · rfl
  · norm_num

/-- **The bracket of `ψ(x)` converges for `x > 0`, uniformly on `[α, β]`**: its width is at
most `dgEU α β e w → 0` for all large `w`, uniformly in `x ∈ [α, β]` and in the enclosures of
`x` of relative width at most `8 · 2^(−w)`. -/
theorem digammaPosEncl_conv_unif {α β : ℝ} (hα : 0 < α) (e : AzInt) :
    ∀ᶠ w in atTop, ∀ xv : ℝ, α ≤ xv → xv ≤ β → ∀ (X : Encl) (lam₀ : ℝ), LEncl X xv lam₀ →
      0 ≤ lam₀ → lam₀ ≤ 8 * (1 / 2 : ℝ) ^ w →
      AEncl (digammaPosEncl X e w) (DLMF.psiR xv) (dgEU α β e w) := by
  have t1 := pb_pgLamP.tendsto
  have t2 := (pb_pgB 0).tendsto
  have t4 := (pb_dgC β).tendsto
  have t5 := (pb_dgLnP β).tendsto
  have t6 := (PB.const (70 : ℝ)).tendsto
  have t7 := pb_dgLsh.tendsto
  have t8 := ((pb_dgHs α).mul pb_dgLsh).tendsto
  have t56 := t5.add t6
  rw [add_zero] at t56
  filter_upwards [t1.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    t2.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
    (tendsto_dgEpsS e).eventually (ge_mem_nhds one_pos),
    t4.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
    t56.eventually (ge_mem_nhds one_pos),
    t7.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    t8.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    (tendsto_dgWS β e).eventually (ge_mem_nhds one_pos),
    eventually_ge_atTop (64 * (2 ^ e.abs.toNat + 1))]
    with w e1 e2 e3 e4 e5 e7 e8 e9 hwa
  intro xv hxα hxβ X lam₀ hX h0 hlam
  have hxv : 0 < xv := lt_of_lt_of_le hα hxα
  have hw : 64 ≤ w := by
    have : 1 ≤ 2 ^ e.abs.toNat := Nat.one_le_two_pow
    omega
  suffices key : ∃ x : ℝ, AEncl (digammaPosEncl X e w) x (dgEU α β e w) by
    obtain ⟨x, hx⟩ := key
    exact hx.of_isEncl (digammaPosEncl_spec hX.isEnclPos e hw)
  obtain ⟨a, ha⟩ : ∃ a : ℕ, a = e.abs.toNat := ⟨_, rfl⟩
  rw [← ha] at hwa
  obtain ⟨L, hL⟩ : ∃ L : ℕ, L = lnGammaShiftExp w := ⟨_, rfl⟩
  obtain ⟨V, hVdef⟩ : ∃ V : ℕ, V = w + 2 * L + 8 + 2 * w.log2 := ⟨_, rfl⟩
  obtain ⟨hL1, hL2⟩ := two_pow_shiftExp (by omega : 4 ≤ w)
  have hLlog := shiftExp_le_log2 (by omega : 4 ≤ w)
  rw [← hL] at hL1 hL2 hLlog
  have hlogw := log2_le_self w
  have hV1 : w ≤ V := by omega
  have hV2 : V ≤ 6 * w := by omega
  have hV : 64 ≤ V := by omega
  have : NeZero V := ⟨by omega⟩
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = lgTerms e w := ⟨_, rfl⟩
  obtain ⟨hM4, hMle⟩ := lgTerms_le e w
  rw [← hM] at hM4 hMle
  obtain ⟨U, hU⟩ : ∃ U : ℝ, U = (1 / 2 : ℝ) ^ w := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (1 / 2 : ℝ) ^ V := ⟨_, rfl⟩
  have hU0 : 0 < U := by rw [hU]; positivity
  have hu0 : 0 < u := by rw [hu]; positivity
  have huU : u ≤ U := by
    rw [hu, hU]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hV1
  have hu8 : u ≤ 1 / 8 := by rw [hu]; exact half_pow_le_eighth (by omega)
  have hU64 : U ≤ 1 / 64 := by
    rw [hU]
    calc (1 / 2 : ℝ) ^ w ≤ (1 / 2 : ℝ) ^ 6 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 64 := by norm_num
  rw [← hU] at hlam e1 e2 e4 e5 e7 e8
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = pgT 0 w := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = pgB 0 w := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = dgC β w := ⟨_, rfl⟩
  obtain ⟨Mr, hMr⟩ : ∃ Mr : ℝ, Mr = pgMr w := ⟨_, rfl⟩
  have hwR : (64 : ℝ) ≤ w := by exact_mod_cast hw
  have hw0 : (0 : ℝ) ≤ w := by linarith
  have hTdef : T = (w : ℝ) + 8 := by rw [hT]; unfold pgT; simp
  have hT0 : 0 ≤ T := by rw [hTdef]; linarith
  have hMrdef : Mr = (w : ℝ) / 2 + 4 := by rw [hMr]; rfl
  have hMr0 : 0 ≤ Mr := by rw [hMrdef]; positivity
  have hMR : (M : ℝ) ≤ Mr := by
    have h1 : 2 * M ≤ w + 8 := by omega
    have h2 : (2 : ℝ) * M ≤ w + 8 := by exact_mod_cast h1
    rw [hMrdef]
    linarith
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hBdef : B = Mr * (2 * T + 1) + 2 * T + 1 := by rw [hB, hMr, hT]; rfl
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hCdef : C = β + w + T + 5 := by rw [hC, hT]; rfl
  have hβ0 : 0 < β := by linarith only [hxv, hxβ]
  have hC0 : 0 ≤ C := by rw [hCdef]; positivity
  rw [← hB] at e2
  rw [← hC] at e4
  obtain ⟨Lam, hLam⟩ : ∃ Lam : ℝ, Lam = pgLamP w * U := ⟨_, rfl⟩
  have hLamdef : Lam = (Mr + 1) * (52 * U) := by
    rw [hLam, hMr]
    unfold pgLamP
    ring
  rw [← hLam] at e1
  have hLam0 : 0 ≤ Lam := by rw [hLamdef]; positivity
  -- the shift
  obtain ⟨lo, hi, hlo, -, hlo0, hlox, -, -⟩ := id hX
  obtain ⟨δ, hδ⟩ : ∃ δ : ℕ, δ = lnGammaShift X.1 e L := ⟨_, rfl⟩
  have haL : a ≤ L := by
    have h1 : 2 ^ a < 2 ^ L := by omega
    exact ((Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h1).le
  have hδle : δ ≤ 2 ^ L := by rw [hδ]; exact lnGammaShift_le _ _ _
  have hδge : 2 ^ L - 2 ^ a ≤ δ := by
    rw [hδ, ha]
    exact lnGammaShift_ge _ _ (by rw [← ha]; exact haL)
  have hsub : 2 ^ L - 2 ^ a + 2 ^ a = 2 ^ L :=
    Nat.sub_add_cancel (Nat.pow_le_pow_right (by norm_num) haL)
  have hδpos : 1 ≤ δ := by omega
  have hδw : (δ : ℝ) ≤ w := by exact_mod_cast (by omega : δ ≤ w)
  have hδ0 : (0 : ℝ) ≤ δ := Nat.cast_nonneg δ
  have hδlow : (w : ℝ) / 4 - w / 64 ≤ δ := by
    have h1 : w + 4 * 2 ^ a ≤ 4 * δ + 4 * 2 ^ a + 4 * 2 ^ a := by omega
    have h2 : 64 * 2 ^ a ≤ w := by omega
    have h1' : (w : ℝ) + 4 * 2 ^ a ≤ 4 * δ + 4 * 2 ^ a + 4 * 2 ^ a := by exact_mod_cast h1
    have h2' : (64 : ℝ) * 2 ^ a ≤ w := by exact_mod_cast h2
    linarith only [h1', h2']
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = xv + (δ : ℕ) := ⟨_, rfl⟩
  have hyge : (w : ℝ) / 4 - w / 64 ≤ y := by rw [hy]; linarith only [hδlow, hxv]
  have hy1 : 1 ≤ y := by linarith only [hyge, hwR]
  have hyle : y ≤ xv + w := by rw [hy]; linarith only [hδw]
  have hky : ∀ k : ℕ, k ≤ M → (k : ℝ) ≤ 27 / 10 * y := fun k hk => by
    have : (k : ℝ) ≤ M := by exact_mod_cast hk
    rw [hMrdef] at hMR
    linarith only [this, hMR, hyge, hwR]
  have hterm : ∀ k, 1 ≤ k → k ≤ M → polyT 0 k y ≤ T := fun k hk hkM => by
    refine (polyT_le 0 hk hy1 (hky k hkM)).trans ?_
    have h9 : (9 / 10 : ℝ) ^ (2 * k - 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hbase : ((2 * k + 0 : ℕ) : ℝ) ≤ T := by
      have : (k : ℝ) ≤ M := by exact_mod_cast hkM
      rw [hMrdef] at hMR
      rw [hTdef]
      push_cast
      linarith only [this, hMR]
    have hb0 : (0 : ℝ) ≤ ((2 * k + 0 : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [zero_add, pow_one]
    calc ((2 * k + 0 : ℕ) : ℝ) * (9 / 10 : ℝ) ^ (2 * k - 1)
        ≤ ((2 * k + 0 : ℕ) : ℝ) * 1 := mul_le_mul_of_nonneg_left h9 hb0
      _ ≤ T := by rw [mul_one]; exact hbase
  have htail : max ((1 / 2 : ℝ) ^ (w + 16)) (2 * polyT 0 M y) ≤ dgTail e w := by
    unfold dgTail
    rw [← hM]
    exact max_le_max le_rfl
      (by linarith only [polyT_le 0 (by omega : 1 ≤ M) hy1 (hky M le_rfl)])
  have hG : |Real.log y| ≤ β + w := by
    have h1 : 0 ≤ Real.log y := Real.log_nonneg hy1
    have h2 := Real.log_le_sub_one_of_pos (by linarith only [hy1] : 0 < y)
    rw [abs_of_nonneg h1]
    linarith only [h2, hyle, hxβ]
  have hG0 : 0 ≤ β + (w : ℝ) := by linarith only [hβ0, hw0]
  have hlnWle : lnW (β + w) V ≤ dgLnP β w * U := by
    rw [hU]
    exact lnW_le hG0 hV1 hV2
  -- the series at `y`
  have hY : LEncl (Encl.add V X (Encl.nat δ)) y (lam₀ + 6 * u) := by
    rw [hu, hy]
    exact hX.add_exact (w := V) (b := Encl.nat δ) (by rw [← hu]; exact hu8) h0
      (toVal_ofAzNat_ofNat δ) (toVal_ofAzNat_ofNat δ) hδ0
  have hTL : T * Lam ≤ T / 2 := by
    have := mul_le_mul_of_nonneg_left e1 hT0
    linarith only [this]
  have hTL0 : 0 ≤ T * Lam := mul_nonneg hT0 hLam0
  have hBu : B * u ≤ B * U := mul_le_mul_of_nonneg_left huU hB0
  have hCu : C * u ≤ C * U := mul_le_mul_of_nonneg_left huU hC0
  have hLamge : ((M : ℝ) + 1) * (2 * (lam₀ + 6 * u) + 24 * u) ≤ Lam := by
    rw [hLamdef]
    exact mul_le_mul (by linarith only [hMR]) (by linarith only [hlam, huU]) (by positivity)
      (by linarith only [hMr0])
  have hBge : (M : ℝ) * (T + 2 * T * Lam + 1) + 2 * T + 1 ≤ B := by
    rw [hBdef]
    have : (M : ℝ) * (T + 2 * T * Lam + 1) ≤ Mr * (2 * T + 1) :=
      mul_le_mul hMR (by linarith only [hTL]) (by linarith only [hT0, hTL0]) hMr0
    linarith only [this]
  have hεSge : (M : ℝ) * (2 * T * Lam + 4 * B * u)
      + max ((1 / 2 : ℝ) ^ (w + 16)) (2 * polyT 0 M y) + 2 * B * u ≤ dgEpsS e w := by
    unfold dgEpsS
    rw [← hMr, ← hT, ← hB, ← hU]
    have p1 : (M : ℝ) * (T * Lam) ≤ Mr * (T * Lam) := mul_le_mul_of_nonneg_right hMR hTL0
    have p2 : (M : ℝ) * (B * u) ≤ Mr * (B * U) := mul_le_mul hMR hBu (by positivity) hMr0
    have p3 : Mr * (T * Lam) = Mr * T * pgLamP w * U := by rw [hLam]; ring
    have p4 : Mr * (B * U) = Mr * B * U := by ring
    have p5 : (M : ℝ) * (2 * T * Lam + 4 * B * u) = 2 * (M * (T * Lam)) + 4 * (M * (B * u)) := by
      ring
    rw [p5]
    linarith only [p1, p2, p3, p4, htail, hBu]
  have hW := digammaStirlingEncl_width hV (by omega : 1 ≤ M) hY (by positivity) hy1
    (toVal_lnGammaTol w) hT0 hterm (by rw [← hu]; exact hLamge) e1
    (by rw [← hu]; linarith only [hBu, e2]) hBge (by rw [← hu]; exact hεSge) e3 hG
    (by linarith only [hlnWle, e5, hlam, huU])
    (C := C) hCdef.ge (by rw [← hu]; linarith only [hCu, e4])
    (by rw [← hu]; linarith only [hlam, huU, hU64])
  rw [← hu] at hW
  have hWS : lnW (β + w) V + 5 * (lam₀ + 6 * u) + (lam₀ + 6 * u + 6 * u) + dgEpsS e w
      + 8 * C * u ≤ dgWS β e w := by
    unfold dgWS
    rw [← hC, ← hU]
    linarith only [hlnWle, hlam, huU, hCu]
  have hS := hW.mono hWS
  -- the shift sum
  have hSh := harmonicEncl_width (V := V) (by omega) hX hδpos
  rw [← hu] at hSh
  have hlamsh : lam₀ + (80 + 6 * (δ : ℝ)) * u ≤ dgLsh w * U := by
    unfold dgLsh
    have b2 : (80 + 6 * (δ : ℝ)) * u ≤ (80 + 6 * (w : ℝ)) * U :=
      mul_le_mul (by linarith only [hδw]) huU hu0.le (by linarith only [hw0])
    linarith only [b2, hlam]
  have hLsh0 : 0 ≤ dgLsh w * U := by
    unfold dgLsh
    positivity
  have hsum0 : 0 ≤ ∑ j ∈ range δ, 1 / (xv + (j : ℝ)) :=
    sum_nonneg fun j _ => by
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      positivity
  have hHs : ∑ j ∈ range δ, 1 / (xv + (j : ℝ)) ≤ dgHs α w := by
    unfold dgHs
    have h1 := sum_inv_pow_le hxv 1 δ
    simp only [pow_one] at h1
    have h2 : (δ : ℝ) * (1 / xv) ≤ w * (1 / xv) := mul_le_mul_of_nonneg_right hδw (by positivity)
    have h3 : (w : ℝ) * (1 / xv) ≤ w * (1 / α) :=
      mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hα hxα) hw0
    rw [div_eq_mul_one_div]
    exact h1.trans (h2.trans h3)
  have hShA := (((hSh.mono hlamsh).toA hLsh0 e7).toA).mono
    (ε' := 2 * (dgHs α w * dgLsh w * U)) (by
      have := mul_le_mul_of_nonneg_right hHs hLsh0
      linarith only [this])
  have hHy : |DLMF.psiR y| ≤ C := by
    have a := abs_psiR_le hy1
    have b := hterm 1 le_rfl (by omega)
    linarith only [a, b, hCdef, hyle, hxβ]
  obtain ⟨Bf, hBf⟩ : ∃ Bf : ℝ, Bf = C + dgHs α w + 2 := ⟨_, rfl⟩
  have hfin := hS.sub (w := V) hShA (B := Bf) (by
    have h1 := abs_sub (DLMF.psiR y) (∑ j ∈ range δ, 1 / (xv + (j : ℝ)))
    rw [abs_of_nonneg hsum0] at h1
    rw [hBf]
    linarith only [h1, hHy, hHs, e9, e8])
  rw [← hu] at hfin
  have hBf0 : 0 ≤ Bf := by
    rw [hBf]
    have : 0 ≤ dgHs α w := hsum0.trans hHs
    linarith only [this, hC0]
  have hBfu : Bf * u ≤ Bf * U := mul_le_mul_of_nonneg_left huU hBf0
  unfold digammaPosEncl
  simp only [← hL, ← hVdef]
  rw [show lnGammaTerms w (max (L + 1) (if e.sign then e.abs.toNat else 0)) = M by
    rw [hM, hL]; rfl, ← hδ, ite_eq_right (by omega : δ ≠ 0)]
  refine ⟨_, hfin.mono ?_⟩
  unfold dgEU
  rw [← hU, ← hC, ← hBf]
  linarith only [hBfu]

/-- **The bracket of `ψ(x)` converges for `x > 0`**: its width is at most `dgE x e w → 0` for
all large `w`, uniformly in the enclosures of `x` of relative width at most `8 · 2^(−w)`. -/
theorem digammaPosEncl_conv {xv : ℝ} (hxv : 0 < xv) (e : AzInt) :
    ∀ᶠ w in atTop, ∀ (X : Encl) (lam₀ : ℝ), LEncl X xv lam₀ → 0 ≤ lam₀ →
      lam₀ ≤ 8 * (1 / 2 : ℝ) ^ w →
      AEncl (digammaPosEncl X e w) (DLMF.psiR xv) (dgE xv e w) := by
  filter_upwards [digammaPosEncl_conv_unif (α := xv) (β := xv) hxv e] with w hw
  exact fun X lam₀ hX h0 hlam => hw xv le_rfl le_rfl X lam₀ hX h0 hlam

/-! ### The signed quotient and the cotangent -/

theorem div_sub_div_le {h l β₁ β₂ m εa εb Ba : ℝ} (hm : 0 < m) (h1 : m ≤ β₁) (h2 : m ≤ β₂)
    (hβ : |β₁ - β₂| ≤ εb) (hhl0 : 0 ≤ h - l) (hhl : h - l ≤ εa) (hl : |l| ≤ Ba) :
    h / β₂ - l / β₁ ≤ εa / m + Ba * εb / m ^ 2 := by
  have hβ₁ : 0 < β₁ := by linarith
  have hβ₂ : 0 < β₂ := by linarith
  have e : h / β₂ - l / β₁ = (h - l) / β₂ + l * (β₁ - β₂) / (β₁ * β₂) := by
    field_simp
    ring
  have a1 : (h - l) / β₂ ≤ εa / m := div_le_div₀ (by linarith) hhl hm h2
  have hBa0 : 0 ≤ Ba := (abs_nonneg l).trans hl
  have hεb0 : 0 ≤ εb := (abs_nonneg _).trans hβ
  have a2 : l * (β₁ - β₂) ≤ Ba * εb := by
    calc l * (β₁ - β₂) ≤ |l * (β₁ - β₂)| := le_abs_self _
      _ = |l| * |β₁ - β₂| := abs_mul _ _
      _ ≤ Ba * εb := mul_le_mul hl hβ (abs_nonneg _) hBa0
  have hm2 : m ^ 2 ≤ β₁ * β₂ := by nlinarith
  have a3 : l * (β₁ - β₂) / (β₁ * β₂) ≤ Ba * εb / m ^ 2 := by
    calc l * (β₁ - β₂) / (β₁ * β₂) ≤ Ba * εb / (β₁ * β₂) :=
          div_le_div_of_nonneg_right a2 (by positivity)
      _ ≤ Ba * εb / m ^ 2 := div_le_div_of_nonneg_left (by positivity) (by positivity) hm2
  rw [e]
  linarith

/-- The width of `[a] / [b]` for `[a]` of any sign and `[b]` above `m > 0`. -/
theorem AEncl.divPos {W : ℕ} [NeZero W] {a b : Encl} {x y εa εb Ba m : ℝ}
    (ha : AEncl a x εa) (hb : AEncl b y εb) (hm : 0 < m) (hmy : m ≤ y - εb)
    (hBa : |x| + εa ≤ Ba) :
    AEncl (Encl.divPos W a b) (x / y)
      (εa / m + Ba * εb / m ^ 2 + 4 * (Ba / m) * (1 / 2 : ℝ) ^ W) := by
  obtain ⟨l, h, hl, hh, h1, h2, h3⟩ := id ha
  obtain ⟨bl, bh, hbl, hbh, hb1, hb2, hb3⟩ := id hb
  have hblm : m ≤ bl := by linarith
  have hbl0 : 0 < bl := by linarith
  have hbh0 : 0 < bh := by linarith
  have hu0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ W := by positivity
  have hxa := abs_le.mp (le_refl |x|)
  have hBa0 : 0 ≤ Ba := by linarith [abs_nonneg x]
  have hlB : |l| ≤ Ba := by rw [abs_le]; constructor <;> linarith
  have hhB : |h| ≤ Ba := by rw [abs_le]; constructor <;> linarith
  have hquot : ∀ {s β : ℝ}, |s| ≤ Ba → m ≤ β → |s / β| ≤ Ba / m := fun {s β} hs hβ => by
    rw [abs_div, abs_of_pos (by linarith : 0 < β)]
    exact div_le_div₀ hBa0 hs hm hβ
  obtain ⟨r₁', r₂', t1, t2, s1, s2⟩ :=
    IsEncl.divPos (W := W) ha.isEncl (⟨bl, bh, hbl, hbh, hbl0, hb1, hb2⟩ : IsEnclPos b y)
  unfold Encl.divPos at t1 t2 ⊢
  have e1 : ∃ r β : ℝ, (divPrecRound a.1 (if lt a.1 zero = true then b.1 else b.2) W
      .Floor).1.toVal = some (r : EReal) ∧ bl ≤ β ∧ β ≤ bh ∧
      l / β ≤ r + 2 * (Ba / m) * (1 / 2 : ℝ) ^ W := by
    by_cases hc : lt a.1 zero = true
    · rw [ite_eq_left hc]
      obtain ⟨r, hr, -, hr2⟩ := divFloor_abs hl hbl hbl0.ne' W
      have := mul_le_mul_of_nonneg_right (hquot hlB hblm) hu0
      exact ⟨r, bl, hr, le_rfl, by linarith, by linarith⟩
    · rw [ite_eq_right hc]
      obtain ⟨r, hr, -, hr2⟩ := divFloor_abs hl hbh hbh0.ne' W
      have := mul_le_mul_of_nonneg_right (hquot hlB (by linarith : m ≤ bh)) hu0
      exact ⟨r, bh, hr, by linarith, le_rfl, by linarith⟩
  have e2 : ∃ r β : ℝ, (divPrecRound a.2 (if lt zero a.2 = true then b.1 else b.2) W
      .Ceiling).1.toVal = some (r : EReal) ∧ bl ≤ β ∧ β ≤ bh ∧
      r ≤ h / β + 2 * (Ba / m) * (1 / 2 : ℝ) ^ W := by
    by_cases hc : lt zero a.2 = true
    · rw [ite_eq_left hc]
      obtain ⟨r, hr, -, hr2⟩ := divCeiling_abs hh hbl hbl0.ne' W
      have := mul_le_mul_of_nonneg_right (hquot hhB hblm) hu0
      exact ⟨r, bl, hr, le_rfl, by linarith, by linarith⟩
    · rw [ite_eq_right hc]
      obtain ⟨r, hr, -, hr2⟩ := divCeiling_abs hh hbh hbh0.ne' W
      have := mul_le_mul_of_nonneg_right (hquot hhB (by linarith : m ≤ bh)) hu0
      exact ⟨r, bh, hr, by linarith, le_rfl, by linarith⟩
  obtain ⟨r₁, β₁, hr₁, c1, c2, c3⟩ := e1
  obtain ⟨r₂, β₂, hr₂, d1, d2, d3⟩ := e2
  rw [hr₁, Option.some.injEq, EReal.coe_eq_coe_iff] at t1
  rw [hr₂, Option.some.injEq, EReal.coe_eq_coe_iff] at t2
  subst t1 t2
  refine ⟨r₁, r₂, hr₁, hr₂, s1, s2, ?_⟩
  have hβ : |β₁ - β₂| ≤ εb := by
    rw [abs_le]
    constructor <;> linarith
  have := div_sub_div_le hm (by linarith : m ≤ β₁) (by linarith : m ≤ β₂) hβ
    (by linarith : 0 ≤ h - l) h3 hlB
  linarith

/-- The width of `π cot (π a)` from the widths of the sine and the cosine. -/
noncomputable def cotW (s εs u : ℝ) : ℝ :=
  4 * (2 * εs / s + 8 * εs / s ^ 2 + 16 * u / s) + 40 * (1 / s + 1) * u

/-- **The cotangent of the reflection formula**, with its width: `A` encloses `a ∈ (0, 1)`
with a small relative width, and the level `w` is large against `sin (π a)`. -/
theorem digammaCot_width {A : Encl} {a lamA : ℝ} {W : ℕ} (hW : 64 ≤ W)
    (hA : LEncl A a lamA) (hlam0 : 0 ≤ lamA) (hlam : lamA ≤ 1 / 64) (ha : a < 1) {w : ℕ}
    (hw : 64 ≤ w) (henv : sinEnv w ≤ 1)
    (hsmall : 2 * (sinEnv w + 32 * lamA + 304 * (1 / 2 : ℝ) ^ W) ≤ Real.sin (a * Real.pi))
    (hQ1 : 2 * (sinEnv w + 32 * lamA + 304 * (1 / 2 : ℝ) ^ W) / Real.sin (a * Real.pi)
      + 8 * (sinEnv w + 32 * lamA + 304 * (1 / 2 : ℝ) ^ W) / Real.sin (a * Real.pi) ^ 2
      + 16 * (1 / 2 : ℝ) ^ W / Real.sin (a * Real.pi) ≤ 1) :
    ∃ T : Encl, digammaCot A W w = some T ∧
      AEncl T (Real.cos (a * Real.pi) / Real.sin (a * Real.pi) * Real.pi)
        (cotW (Real.sin (a * Real.pi)) (sinEnv w + 32 * lamA + 304 * (1 / 2 : ℝ) ^ W)
          ((1 / 2 : ℝ) ^ W)) := by
  have : NeZero W := ⟨by omega⟩
  have hu := half_pow_le_of_64 hW
  obtain ⟨u, hudef⟩ : ∃ u : ℝ, u = (1 / 2 : ℝ) ^ W := ⟨_, rfl⟩
  rw [← hudef] at hu hsmall hQ1 ⊢
  have hu0 : 0 < u := by rw [hudef]; positivity
  have hu8 : u ≤ 1 / 8 := hu.trans (by norm_num)
  have hu' : u ≤ 1 / 576 := hu.trans (by norm_num)
  have ha0 := hA.pos
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sin (a * Real.pi) := ⟨_, rfl⟩
  obtain ⟨εs, hεs⟩ : ∃ εs : ℝ, εs = sinEnv w + 32 * lamA + 304 * u := ⟨_, rfl⟩
  rw [← hs, ← hεs] at hsmall hQ1 ⊢
  have hεs0 : 0 ≤ εs := by rw [hεs]; have := sinEnv_nonneg w; positivity
  have hs0 : 0 < s := by
    rw [hs]
    exact Real.sin_pos_of_pos_of_lt_pi (mul_pos ha0 Real.pi_pos) (by nlinarith [Real.pi_pos])
  have hs1 : s ≤ 1 := by rw [hs]; exact Real.sin_le_one _
  have hεs1 : εs ≤ 1 := by linarith
  have hY : LEncl (Encl.mul W A (Encl.pi W)) (a * Real.pi) (lamA + 9 * u) := by
    rw [hudef]
    exact (hA.mul (by rw [← hudef]; exact hu8) (LEncl.pi hW)).mono (by linarith)
  obtain ⟨tl, th, hl, hh, p, a1, a2, a3⟩ := hY.toA (by positivity) (by linarith)
  have hy4 : a * Real.pi ≤ 4 := by nlinarith [Real.pi_le_four, Real.pi_pos]
  have htl0 : 0 < tl := by
    obtain ⟨l', h', hl', -, hl0, -⟩ := id hY
    rw [hl, Option.some.injEq, EReal.coe_eq_coe_iff] at hl'
    rw [hl']
    exact hl0
  obtain ⟨hsb, hcb⟩ := sinCosBracket_spec hl (abs_lt_two_zpow_expOf hl)
    (Nat.le_add_right_of_le hw : 64 ≤ w + sinLostBits (Encl.mul W A (Encl.pi W)).1)
  rw [abs_of_pos htl0] at hsb
  have hsce : sinCosEps (expOf (Encl.mul W A (Encl.pi W)).1)
      (w + sinLostBits (Encl.mul W A (Encl.pi W)).1) ≤ sinEnv w :=
    sinEps_le_sinEnv _ (Nat.le_add_right w _)
  obtain ⟨r, hr, hr1, hr2⟩ := subCeiling_abs hh hl W
  rw [abs_of_nonneg (by linarith), ← hudef] at hr2
  have hwid : th - tl ≤ 8 * (lamA + 9 * u) := by nlinarith
  have hr3 : r ≤ 16 * (lamA + 9 * u) := by nlinarith
  have hE : IsEncl0W (Encl.exact (subPrecRound (Encl.mul W A (Encl.pi W)).2
      (Encl.mul W A (Encl.pi W)).1 W .Ceiling).1) r 0 :=
    ⟨r, r, hr, hr, by linarith, le_rfl, le_rfl, by simp⟩
  have hd : |a * Real.pi - tl| ≤ r := by rw [abs_of_nonneg (by linarith)]; linarith
  have hr_le1 : r ≤ 1 := by linarith
  have hwide : sinCosEps (expOf (Encl.mul W A (Encl.pi W)).1)
      (w + sinLostBits (Encl.mul W A (Encl.pi W)).1) + 2 * r + 2 * 0 + 8 * (1 + 1) * u ≤ εs := by
    rw [hεs]
    linarith
  have hS : AEncl (Encl.widen W (sinCosBracket (Encl.mul W A (Encl.pi W)).1
      (expOf (Encl.mul W A (Encl.pi W)).1)
      (w + sinLostBits (Encl.mul W A (Encl.pi W)).1)).1
      (Encl.exact (subPrecRound (Encl.mul W A (Encl.pi W)).2
        (Encl.mul W A (Encl.pi W)).1 W .Ceiling).1)) s εs := by
    obtain ⟨c, d, hc, hd', hc1, hd1, hcd⟩ := IsEnclW.widen0 (M := 1) hsb hE
      ((Real.abs_sin_sub_sin_le _ _).trans hd) (Real.abs_sin_le_one _) hr_le1
      (hsce.trans henv) (by norm_num) hW
    rw [← hudef] at hcd
    rw [hs]
    exact ⟨c, d, hc, hd', hc1, hd1, hcd.trans hwide⟩
  have hC : AEncl (Encl.widen W (sinCosBracket (Encl.mul W A (Encl.pi W)).1
      (expOf (Encl.mul W A (Encl.pi W)).1)
      (w + sinLostBits (Encl.mul W A (Encl.pi W)).1)).2
      (Encl.exact (subPrecRound (Encl.mul W A (Encl.pi W)).2
        (Encl.mul W A (Encl.pi W)).1 W .Ceiling).1))
      (Real.cos (a * Real.pi)) εs := by
    obtain ⟨c, d, hc, hd', hc1, hd1, hcd⟩ := IsEnclW.widen0 (M := 1) hcb hE
      ((Real.abs_cos_sub_cos_le _ _).trans hd) (Real.abs_cos_le_one _) hr_le1
      (hsce.trans henv) (by norm_num) hW
    rw [← hudef] at hcd
    exact ⟨c, d, hc, hd', hc1, hd1, hcd.trans hwide⟩
  have hSpos : lt zero (Encl.widen W (sinCosBracket (Encl.mul W A (Encl.pi W)).1
      (expOf (Encl.mul W A (Encl.pi W)).1)
      (w + sinLostBits (Encl.mul W A (Encl.pi W)).1)).1
      (Encl.exact (subPrecRound (Encl.mul W A (Encl.pi W)).2
        (Encl.mul W A (Encl.pi W)).1 W .Ceiling).1)).1 = true := by
    obtain ⟨c, d, hc, -, hc1, hd1, hcd⟩ := id hS
    exact (lt_eq_true_iff toVal_zero' hc).mpr (by linarith)
  have hcos1 := abs_le.mp (Real.abs_cos_le_one (a * Real.pi))
  have hQ := hC.divPos (W := W) hS (m := s / 2) (Ba := 2) (by positivity) (by linarith)
    (by
      have := Real.abs_cos_le_one (a * Real.pi)
      linarith)
  rw [← hudef] at hQ
  have hQeps : εs / (s / 2) + 2 * εs / (s / 2) ^ 2 + 4 * (2 / (s / 2)) * u
      = 2 * εs / s + 8 * εs / s ^ 2 + 16 * u / s := by
    field_simp
    ring
  rw [hQeps] at hQ
  have hπA : AEncl0 (Encl.pi W) Real.pi (24 * u) := by
    have h := (LEncl.pi hW).toA (by positivity) (by rw [← hudef]; linarith)
    rw [← hudef] at h
    refine h.mono ?_
    nlinarith [Real.pi_le_four, Real.pi_pos]
  have hcotabs : |Real.cos (a * Real.pi) / s| ≤ 1 / s := by
    rw [abs_div, abs_of_pos hs0]
    exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) hs0.le
  have hT := hQ.mulPos (W := W) hπA (Ba := 1 / s + 1) (Bb := 4)
    (by linarith only [hcotabs, hQ1]) (by linarith only [Real.pi_lt_d2, hu'])
  rw [← hudef] at hT
  refine ⟨_, ?_, hT.mono ?_⟩
  · unfold digammaCot
    dsimp only
    rw [ite_eq_left hSpos]
  · unfold cotW
    have h1s : 0 ≤ 1 / s + 1 := by positivity
    have := mul_nonneg h1s hu0.le
    linarith

/-! ### The reflection formula, and the bracket -/

theorem cotW_anti {s s' εs u : ℝ} (hs' : 0 < s') (hss : s' ≤ s) (hε : 0 ≤ εs) (hu : 0 ≤ u) :
    cotW s εs u ≤ cotW s' εs u ∧
      2 * εs / s + 8 * εs / s ^ 2 + 16 * u / s ≤ 2 * εs / s' + 8 * εs / s' ^ 2 + 16 * u / s' := by
  have hs : 0 < s := lt_of_lt_of_le hs' hss
  have h1 : 2 * εs / s ≤ 2 * εs / s' := div_le_div_of_nonneg_left (by positivity) hs' hss
  have h2 : 8 * εs / s ^ 2 ≤ 8 * εs / s' ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_left₀ hs'.le hss 2)
  have h3 : 16 * u / s ≤ 16 * u / s' := div_le_div_of_nonneg_left (by positivity) hs' hss
  have h4 : 1 / s ≤ 1 / s' := one_div_le_one_div_of_le hs' hss
  have h5 : (1 / s + 1) * u ≤ (1 / s' + 1) * u := mul_le_mul_of_nonneg_right (by linarith) hu
  refine ⟨?_, by linarith⟩
  unfold cotW
  linarith

/-- **The reflection formula converges, uniformly**: for every `a ∈ (0, 1)` with
`sin (π a) ≥ smin`, every value `|pv| ≤ Pmax` enclosed by `P` within `EP w`, and every `F`
that gives `a` with the relative width `6 · 2^(−w−16)`. -/
theorem digammaReflect_unif {smin Pmax : ℝ} (hsmin : 0 < smin) {EP : ℕ → ℝ}
    (hEP : Tendsto EP atTop (𝓝 0)) :
    ∃ E : ℕ → ℝ, Tendsto E atTop (𝓝 0) ∧ ∀ᶠ w in atTop, ∀ (a pv : ℝ) (P : Encl)
      (F : Option (Bool × Encl)), 0 < a → a < 1 → smin ≤ Real.sin (a * Real.pi) →
      |pv| ≤ Pmax → AEncl P pv (EP w) →
      (∃ (σ : Bool) (A : Encl), F = some (σ, A) ∧ LEncl A a (6 * (1 / 2 : ℝ) ^ (w + 16))) →
      ∃ (b : Encl) (v : ℝ), digammaReflect F P w = some b ∧ AEncl b v (E w) := by
  obtain ⟨Bc, hBc⟩ : ∃ Bc : ℝ, Bc = Pmax + 4 / smin + 2 := ⟨_, rfl⟩
  have hu : Tendsto (fun w : ℕ => (1 / 2 : ℝ) ^ (w + 16)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
      (tendsto_add_atTop_nat 16)
  have hεs : Tendsto (fun w : ℕ => sinEnv w + 32 * (6 * (1 / 2 : ℝ) ^ (w + 16))
      + 304 * (1 / 2 : ℝ) ^ (w + 16)) atTop (𝓝 0) := by
    have := (tendsto_sinEnv.add ((hu.const_mul 6).const_mul 32)).add (hu.const_mul 304)
    convert this using 2
    norm_num
  have hQt : Tendsto (fun w : ℕ => 2 * (sinEnv w + 32 * (6 * (1 / 2 : ℝ) ^ (w + 16))
        + 304 * (1 / 2 : ℝ) ^ (w + 16)) / smin
      + 8 * (sinEnv w + 32 * (6 * (1 / 2 : ℝ) ^ (w + 16)) + 304 * (1 / 2 : ℝ) ^ (w + 16))
        / smin ^ 2
      + 16 * (1 / 2 : ℝ) ^ (w + 16) / smin) atTop (𝓝 0) := by
    have := ((((hεs.const_mul 2).div_const smin).add
      ((hεs.const_mul 8).div_const (smin ^ 2))).add ((hu.const_mul 16).div_const smin))
    convert this using 2
    norm_num
  have hcot : Tendsto (fun w : ℕ => cotW smin (sinEnv w + 32 * (6 * (1 / 2 : ℝ) ^ (w + 16))
      + 304 * (1 / 2 : ℝ) ^ (w + 16)) ((1 / 2 : ℝ) ^ (w + 16))) atTop (𝓝 0) := by
    have := (hQt.const_mul 4).add (hu.const_mul (40 * (1 / smin + 1)))
    convert this using 2
    · rfl
    · norm_num
  have hE : Tendsto (fun w : ℕ => EP w
      + cotW smin (sinEnv w + 32 * (6 * (1 / 2 : ℝ) ^ (w + 16))
        + 304 * (1 / 2 : ℝ) ^ (w + 16)) ((1 / 2 : ℝ) ^ (w + 16))
      + 4 * Bc * (1 / 2 : ℝ) ^ (w + 16)) atTop (𝓝 0) := by
    have := (hEP.add hcot).add (hu.const_mul (4 * Bc))
    convert this using 2
    norm_num
  refine ⟨_, hE, ?_⟩
  filter_upwards [eventually_ge_atTop 64,
    hεs.eventually (ge_mem_nhds (half_pos hsmin)),
    hQt.eventually (ge_mem_nhds one_pos),
    tendsto_sinEnv.eventually (ge_mem_nhds one_pos),
    hEP.eventually (ge_mem_nhds one_pos), hcot.eventually (ge_mem_nhds one_pos)]
    with w hw e1 e2 e3 e4 e5
  intro a pv P F ha0 ha1 hsa hpvmax hPw hFw
  obtain ⟨σ, A, hFeq, hA⟩ := hFw
  have hW : 64 ≤ w + 16 := by omega
  have : NeZero (w + 16) := ⟨by omega⟩
  obtain ⟨u, hudef⟩ : ∃ u : ℝ, u = (1 / 2 : ℝ) ^ (w + 16) := ⟨_, rfl⟩
  rw [← hudef] at hA e1 e2 e5 ⊢
  have hu0 : 0 < u := by rw [hudef]; positivity
  have hu64 : u ≤ 1 / 2 ^ 64 := by rw [hudef]; exact half_pow_le_of_64 hW
  have hu' : 6 * u ≤ 1 / 64 := by
    have : (1 : ℝ) / 2 ^ 64 ≤ 1 / 384 := by norm_num
    linarith only [hu64, this]
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sin (a * Real.pi) := ⟨_, rfl⟩
  rw [← hs] at hsa
  have hs0 : 0 < s := lt_of_lt_of_le hsmin hsa
  obtain ⟨εs, hεsdef⟩ : ∃ εs : ℝ, εs = sinEnv w + 32 * (6 * u) + 304 * u := ⟨_, rfl⟩
  rw [← hεsdef] at e1 e2 e5
  have hεs0 : 0 ≤ εs := by rw [hεsdef]; have := sinEnv_nonneg w; positivity
  obtain ⟨hanti1, hanti2⟩ := cotW_anti hsmin hsa hεs0 hu0.le
  obtain ⟨T, hT, hTA⟩ := digammaCot_width (lamA := 6 * u) hW hA
    (by positivity) hu' ha1 hw e3
    (by rw [← hs, ← hudef, ← hεsdef]; linarith only [e1, hsa])
    (by rw [← hs, ← hudef, ← hεsdef]; linarith only [e2, hanti2])
  rw [← hs, ← hudef, ← hεsdef] at hTA
  have hTA' := hTA.mono hanti1
  have hcos := Real.abs_cos_le_one (a * Real.pi)
  have hvT : |Real.cos (a * Real.pi) / s * Real.pi| ≤ 4 / smin := by
    rw [abs_mul, abs_div, abs_of_pos hs0, abs_of_pos Real.pi_pos]
    have h1 : |Real.cos (a * Real.pi)| / s ≤ 1 / smin :=
      div_le_div₀ zero_le_one hcos hsmin hsa
    have h2 : |Real.cos (a * Real.pi)| / s * Real.pi ≤ 1 / smin * 4 :=
      mul_le_mul h1 Real.pi_le_four Real.pi_pos.le (by positivity)
    rw [show 4 / smin = 1 / smin * 4 by ring]
    exact h2
  have hpv := abs_le.mp hpvmax
  have hvT' := abs_le.mp hvT
  have hBcu0 : 0 ≤ Bc := by
    rw [hBc]
    have : 0 ≤ Pmax := (abs_nonneg pv).trans hpvmax
    positivity
  have hsome : digammaReflect F P w
      = some (if σ then Encl.add (w + 16) P T else Encl.sub (w + 16) P T) := by
    unfold digammaReflect
    rw [hFeq]
    show (digammaCot A (w + 16) w).map (fun T =>
      if σ then Encl.add (w + 16) P T else Encl.sub (w + 16) P T) = _
    rw [hT]
    rfl
  rw [hsome]
  cases σ with
  | true =>
    have hfin := hPw.add (w := w + 16) hTA' (B := Bc) (by
      have : |pv + Real.cos (a * Real.pi) / s * Real.pi| ≤ Pmax + 4 / smin := by
        rw [abs_le]
        constructor <;> linarith only [hpv.1, hpv.2, hvT'.1, hvT'.2]
      rw [hBc]
      linarith only [this, e4, e5])
    rw [← hudef, hεsdef] at hfin
    exact ⟨_, _, rfl, hfin⟩
  | false =>
    have hfin := hPw.sub (w := w + 16) hTA' (B := Bc) (by
      have : |pv - Real.cos (a * Real.pi) / s * Real.pi| ≤ Pmax + 4 / smin := by
        rw [abs_le]
        constructor <;> linarith only [hpv.1, hpv.2, hvT'.1, hvT'.2]
      rw [hBc]
      linarith only [this, e4, e5])
    rw [← hudef, hεsdef] at hfin
    exact ⟨_, _, rfl, hfin⟩

/-- **The reflection formula converges**: `P w` encloses a fixed value with widths tending to
`0`, and `F w` gives the distance `a ∈ (0, 1)` to an integer with relative width
`6 · 2^(−w−16)`. -/
theorem digammaReflect_conv {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {pv : ℝ} {P : ℕ → Encl}
    {EP : ℕ → ℝ} (hEP : Tendsto EP atTop (𝓝 0)) (hP : ∀ᶠ w in atTop, AEncl (P w) pv (EP w))
    {F : ℕ → Option (Bool × Encl)}
    (hF : ∀ᶠ w in atTop, ∃ (σ : Bool) (A : Encl), F w = some (σ, A) ∧
      LEncl A a (6 * (1 / 2 : ℝ) ^ (w + 16))) :
    ∃ E : ℕ → ℝ, Tendsto E atTop (𝓝 0) ∧ ∀ᶠ w in atTop, ∃ (b : Encl) (v : ℝ),
      digammaReflect (F w) (P w) w = some b ∧ AEncl b v (E w) := by
  have hs0 : 0 < Real.sin (a * Real.pi) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos ha0 Real.pi_pos) (by nlinarith [Real.pi_pos])
  obtain ⟨E, hE, hev⟩ := digammaReflect_unif (Pmax := |pv|) hs0 hEP
  refine ⟨E, hE, ?_⟩
  filter_upwards [hev, hP, hF] with w h1 h2 h3
  exact h1 a pv (P w) (F w) ha0 ha1 le_rfl le_rfl h2 h3

/-- **The enclosure of `ψ(x)` converges** at a negative float that is not an integer. -/
theorem digammaNegEncl_conv {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hneg : xv < 0) (hni : ∀ k : ℤ, xv ≠ k) (e : AzInt) :
    ∃ E : ℕ → ℝ, Tendsto E atTop (𝓝 0) ∧ ∀ᶠ w in atTop, ∃ b : Encl,
      digammaNegEncl x e w = some b ∧ AEncl b (DLMF.psiR xv) (E w) := by
  have hk1 := gammaNearInt_spec hx
  have hd : xv - ((gammaNearInt x).toInt : ℝ) ≠ 0 := fun h => hni _ (sub_eq_zero.mp h)
  have ha0 : 0 < |xv - ((gammaNearInt x).toInt : ℝ)| := abs_pos.mpr hd
  have hnx : (-x).toVal = some ((-xv : ℝ) : EReal) := by
    rw [toVal_neg, hx, Option.map_some, EReal.coe_neg]
  have hpos1 : 0 < -xv + 1 := by linarith
  obtain ⟨E, hE, hev⟩ := digammaReflect_conv ha0 hk1
    (P := fun w => digammaPosEncl (Encl.add (w + 32) (Encl.exact (-x)) (Encl.exact one))
      ((if e.sign then e else 0) + 1) w)
    (F := fun w => gammaFracEncl x (gammaNearInt x) (w + 16))
    (tendsto_dgE (-xv + 1) ((if e.sign then e else 0) + 1))
    (by
      filter_upwards [digammaPosEncl_conv hpos1 ((if e.sign then e else 0) + 1)] with w hw
      have : NeZero (w + 32) := ⟨by omega⟩
      have hu32 : (1 / 2 : ℝ) ^ (w + 32) ≤ 1 / 8 := half_pow_le_eighth (by omega)
      have hXL := LEncl.add_exact (w := w + 32) (b := Encl.exact one) hu32
        (LEncl.exact hnx (by linarith)) le_rfl toVal_one' toVal_one' zero_le_one
      rw [zero_add] at hXL
      exact hw _ _ hXL (by positivity) (six_le_eight w))
    (by
      filter_upwards [eventually_ge_atTop 64] with w hw
      have : NeZero (w + 16) := ⟨by omega⟩
      obtain ⟨σ, A, hF, hA⟩ := gammaFracEncl_some hx (gammaNearInt x) hd (W := w + 16)
        ((half_pow_le_of_64 (by omega : 64 ≤ w + 16)).trans (by norm_num))
      rw [sign_mul_eq_abs hA.pos] at hA
      exact ⟨σ, A, hF, hA⟩)
  refine ⟨E, hE, ?_⟩
  filter_upwards [hev, eventually_ge_atTop 64] with w ⟨b, v, hb, hA⟩ hw
  have hsome : digammaNegEncl x e w = some b := hb
  exact ⟨b, hsome, hA.of_isEncl (digammaNegEncl_spec hx hneg hni e hw hsome)⟩

/-- **The enclosure of `ψ(x)` converges** at every finite `x` that is positive (`pos`) or
negative and not an integer. -/
theorem digammaEncl_conv {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    {pos : Bool} (hpos : pos = true → 0 < xv) (hneg : pos = false → xv < 0 ∧ ∀ k : ℤ, xv ≠ k)
    (e : AzInt) :
    ∃ E : ℕ → ℝ, Tendsto E atTop (𝓝 0) ∧ ∀ᶠ w in atTop, ∃ b : Encl,
      digammaEncl x e pos w = some b ∧ AEncl b (DLMF.psiR xv) (E w) := by
  cases pos with
  | true =>
    refine ⟨dgE xv e, tendsto_dgE xv e, ?_⟩
    filter_upwards [digammaPosEncl_conv (hpos rfl) e] with w hw
    exact ⟨_, rfl, hw _ 0 (LEncl.exact hx (hpos rfl)) le_rfl (by positivity)⟩
  | false =>
    obtain ⟨h0, hni⟩ := hneg rfl
    obtain ⟨E, hE, hev⟩ := digammaNegEncl_conv hx h0 hni e
    exact ⟨E, hE, hev.mono fun w ⟨b, hb, hA⟩ => ⟨b, by simpa [digammaEncl] using hb, hA⟩⟩

/-- **The bracket of `ψ(x)` converges.** -/
theorem digammaApprox_bracketConv {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    {pos : Bool} (hpos : pos = true → 0 < xv) (hneg : pos = false → xv < 0 ∧ ∀ k : ℤ, xv ≠ k)
    (e : AzInt) :
    BracketConv (fun w => lnAbsGammaApproxOf (digammaEncl x e pos w) w) (DLMF.psiR xv) :=
  lnAbsGammaApproxOf_bracketConv (digammaEncl_conv hx hpos hneg e)

end Azurite.AzFloat
