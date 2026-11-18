/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.DigammaBracket
import Azurite.AzFloat.Equiv.GammaBracket
import Azurite.AzFloat.Equiv.SinCosBracket
import Azurite.Transcendental.DigammaStirling

/-!
# Equivalence: the bracket of the digamma function

* `IsEncl.mulPos`, `IsEncl.divPos`: the signed product and quotient of enclosures.
* `psiTermEncl_spec`, `psiSumLoop_spec` (the series of `−ν(y)`, closed by the remainder bound of
  `psiNu_eq_sum_add` at whatever term the loop stops), `digammaStirlingEncl_spec`,
  `harmonicEncl_spec`, **`digammaPosEncl_spec`**: the bracket for `x > 0`.
* `digammaCot_spec` (`π cot (π a)`), `digammaReflect_spec`, `digammaNegEncl_spec`: the
  reflection formula; **`digammaEncl_spec`**.
* `digammaTiny?_eq`: the tiny-argument path.
-/

namespace Azurite.AzFloat

open Finset Encl
open scoped Real

/-! ### Signed products and quotients -/

/-- The lower end of `x c` for `l ≤ x` and `0 ≤ c₁ ≤ c ≤ c₂`. -/
theorem mul_lower_of_nonneg {l x c c₁ c₂ : ℝ} (hl : l ≤ x) (h0 : 0 ≤ c₁) (h1 : c₁ ≤ c)
    (h2 : c ≤ c₂) : (if l < 0 then l * c₂ else l * c₁) ≤ x * c := by
  have hc : 0 ≤ c := h0.trans h1
  split_ifs with h
  · nlinarith [mul_le_mul_of_nonneg_right hl hc, mul_le_mul_of_nonpos_left h2 h.le]
  · push Not at h
    nlinarith [mul_le_mul_of_nonneg_right hl hc, mul_le_mul_of_nonneg_left h1 h]

/-- The upper end of `x c` for `x ≤ h` and `0 ≤ c₁ ≤ c ≤ c₂`. -/
theorem mul_upper_of_nonneg {h x c c₁ c₂ : ℝ} (hh : x ≤ h) (h0 : 0 ≤ c₁) (h1 : c₁ ≤ c)
    (h2 : c ≤ c₂) : x * c ≤ (if 0 < h then h * c₂ else h * c₁) := by
  have hc : 0 ≤ c := h0.trans h1
  split_ifs with hp
  · nlinarith [mul_le_mul_of_nonneg_right hh hc, mul_le_mul_of_nonneg_left h2 hp.le]
  · push Not at hp
    nlinarith [mul_le_mul_of_nonneg_right hh hc, mul_le_mul_of_nonpos_left h1 hp]

theorem IsEncl.mulPos {W : ℕ} [NeZero W] {a b : Encl} {x y : ℝ} (ha : IsEncl a x)
    (hb : IsEncl0 b y) : IsEncl (Encl.mulPos W a b) (x * y) := by
  obtain ⟨l, h, hl, hh, h1, h2⟩ := ha
  obtain ⟨bl, bh, hbl, hbh, hb0, hb1, hb2⟩ := hb
  have hlo := mul_lower_of_nonneg h1 hb0 hb1 hb2
  have hhi := mul_upper_of_nonneg h2 hb0 hb1 hb2
  unfold Encl.mulPos
  have e1 : ∃ r : ℝ, (mulPrecRound a.1 (if lt a.1 zero = true then b.2 else b.1) W
      .Floor).1.toVal = some (r : EReal) ∧ r ≤ (if l < 0 then l * bh else l * bl) := by
    by_cases hc : lt a.1 zero = true
    · rw [ite_eq_left hc, ite_eq_left ((lt_eq_true_iff hl toVal_zero').mp hc)]
      obtain ⟨r, hr, hr1, -⟩ := mulFloor_abs hl hbh W
      exact ⟨r, hr, hr1⟩
    · rw [ite_eq_right hc, ite_eq_right (fun h' => hc ((lt_eq_true_iff hl toVal_zero').mpr h'))]
      obtain ⟨r, hr, hr1, -⟩ := mulFloor_abs hl hbl W
      exact ⟨r, hr, hr1⟩
  have e2 : ∃ r : ℝ, (mulPrecRound a.2 (if lt zero a.2 = true then b.2 else b.1) W
      .Ceiling).1.toVal = some (r : EReal) ∧ (if 0 < h then h * bh else h * bl) ≤ r := by
    by_cases hc : lt zero a.2 = true
    · rw [ite_eq_left hc, ite_eq_left ((lt_eq_true_iff toVal_zero' hh).mp hc)]
      obtain ⟨r, hr, hr1, -⟩ := mulCeiling_abs hh hbh W
      exact ⟨r, hr, hr1⟩
    · rw [ite_eq_right hc, ite_eq_right (fun h' => hc ((lt_eq_true_iff toVal_zero' hh).mpr h'))]
      obtain ⟨r, hr, hr1, -⟩ := mulCeiling_abs hh hbl W
      exact ⟨r, hr, hr1⟩
  obtain ⟨r₁, hr₁, hr₁1⟩ := e1
  obtain ⟨r₂, hr₂, hr₂1⟩ := e2
  exact ⟨r₁, r₂, hr₁, hr₂, by linarith, by linarith⟩

theorem IsEncl.divPos {W : ℕ} [NeZero W] {a b : Encl} {x y : ℝ} (ha : IsEncl a x)
    (hb : IsEnclPos b y) : IsEncl (Encl.divPos W a b) (x / y) := by
  obtain ⟨l, h, hl, hh, h1, h2⟩ := ha
  obtain ⟨bl, bh, hbl, hbh, hb0, hb1, hb2⟩ := hb
  have hy : 0 < y := by linarith
  have hbh0 : 0 < bh := by linarith
  have c0 : (0 : ℝ) ≤ 1 / bh := by positivity
  have c1 : 1 / bh ≤ 1 / y := one_div_le_one_div_of_le hy hb2
  have c2 : 1 / y ≤ 1 / bl := one_div_le_one_div_of_le hb0 hb1
  have hlo := mul_lower_of_nonneg h1 c0 c1 c2
  have hhi := mul_upper_of_nonneg h2 c0 c1 c2
  rw [mul_one_div, mul_one_div, mul_one_div] at hlo hhi
  unfold Encl.divPos
  have e1 : ∃ r : ℝ, (divPrecRound a.1 (if lt a.1 zero = true then b.1 else b.2) W
      .Floor).1.toVal = some (r : EReal) ∧ r ≤ (if l < 0 then l / bl else l / bh) := by
    by_cases hc : lt a.1 zero = true
    · rw [ite_eq_left hc, ite_eq_left ((lt_eq_true_iff hl toVal_zero').mp hc)]
      obtain ⟨r, hr, hr1, -⟩ := divFloor_abs hl hbl hb0.ne' W
      exact ⟨r, hr, hr1⟩
    · rw [ite_eq_right hc, ite_eq_right (fun h' => hc ((lt_eq_true_iff hl toVal_zero').mpr h'))]
      obtain ⟨r, hr, hr1, -⟩ := divFloor_abs hl hbh hbh0.ne' W
      exact ⟨r, hr, hr1⟩
  have e2 : ∃ r : ℝ, (divPrecRound a.2 (if lt zero a.2 = true then b.1 else b.2) W
      .Ceiling).1.toVal = some (r : EReal) ∧ (if 0 < h then h / bl else h / bh) ≤ r := by
    by_cases hc : lt zero a.2 = true
    · rw [ite_eq_left hc, ite_eq_left ((lt_eq_true_iff toVal_zero' hh).mp hc)]
      obtain ⟨r, hr, hr1, -⟩ := divCeiling_abs hh hbl hb0.ne' W
      exact ⟨r, hr, hr1⟩
    · rw [ite_eq_right hc, ite_eq_right (fun h' => hc ((lt_eq_true_iff toVal_zero' hh).mpr h'))]
      obtain ⟨r, hr, hr1, -⟩ := divCeiling_abs hh hbh hbh0.ne' W
      exact ⟨r, hr, hr1⟩
  obtain ⟨r₁, hr₁, hr₁1⟩ := e1
  obtain ⟨r₂, hr₂, hr₂1⟩ := e2
  exact ⟨r₁, r₂, hr₁, hr₂, by linarith, by linarith⟩

/-! ### The series for `x > 0` -/

/-- A term of the series of `ψ` without its sign, `c_k / y^(2k)`. -/
theorem psiTermEncl_spec {V : ℕ} [NeZero V] {M k : ℕ} (hk : 1 ≤ k) (hkM : k ≤ M) {p : Encl}
    {y : ℝ} (hp : IsEnclPos p (1 / y ^ (2 * k))) :
    IsEncl0 (psiTermEncl V (AzNat.tangentNumbers M) k p) (psiCoeffT k / y ^ (2 * k)) := by
  have hT := AzNat.toNat_tangentNumbers hk hkM
  have hTr : ((((AzNat.tangentNumbers M).getD (k - 1) 0).toNat : ℕ) : ℝ)
      = (BZ.tangentNumber k : ℝ) := by exact_mod_cast hT
  have hle : 2 ^ (2 * k) ≤ 2 ^ (4 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hD : (((((1 : AzNat) <<< (4 * k)) - ((1 : AzNat) <<< (2 * k))).toNat : ℕ) : ℝ)
      = (4 : ℝ) ^ (2 * k) - 2 ^ (2 * k) := by
    rw [AzNat.toNat_sub, AzNat.toNat_hShiftLeft, AzNat.toNat_hShiftLeft,
      Nat.shiftLeft_eq, Nat.shiftLeft_eq, AzNat.toNat_one, one_mul, one_mul]
    push_cast [Nat.cast_sub hle]
    rw [show (4 : ℝ) ^ (2 * k) = 2 ^ (4 * k) by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf]
  have hDpos := four_pow_sub_two_pow_pos hk
  have hnum : IsEncl0 (Encl.exact (ofAzNat ((AzNat.tangentNumbers M).getD (k - 1) 0)))
      (BZ.tangentNumber k : ℝ) := by
    rw [← hTr]
    exact ⟨_, _, toVal_ofAzNat _, toVal_ofAzNat _, Nat.cast_nonneg _, le_rfl, le_rfl⟩
  have hden : IsEnclPos (Encl.exact (ofAzNat
      (((1 : AzNat) <<< (4 * k)) - ((1 : AzNat) <<< (2 * k)))))
      ((4 : ℝ) ^ (2 * k) - 2 ^ (2 * k)) := by
    rw [← hD]
    exact ⟨_, _, toVal_ofAzNat _, toVal_ofAzNat _, by rw [hD]; exact hDpos, le_rfl, le_rfl⟩
  have := (hnum.div (w := V) hden).mul (w := V) hp.encloses0
  unfold psiTermEncl
  convert this using 1
  rw [psiCoeffT]
  ring

/-- The loop encloses `−ν(y)` wherever it stops. -/
theorem psiSumLoop_spec {V : ℕ} [NeZero V] (hV : 2 ≤ V) {M : ℕ} {inv2 : Encl} {y : ℝ}
    (hy : 0 < y) (hinv2 : IsEnclPos inv2 (1 / y ^ 2)) (tol : AzFloat) :
    ∀ (fuel k : ℕ) (p acc : Encl), 1 ≤ k → k + fuel ≤ M →
      IsEnclPos p (1 / y ^ (2 * k)) →
      IsEncl acc (-∑ i ∈ range (k - 1), psiTermT (i + 1) y) →
      IsEncl (psiSumLoop V (AzNat.tangentNumbers M) inv2 tol fuel k p acc) (-psiNu y)
  | 0, k, p, acc, hk, hkM, hp, hacc => by
    obtain ⟨r, hν, hsign, habs⟩ := psiNu_eq_sum_add hk hy
    rw [psiSumLoop]
    exact stirlingClose_spec (r := -r) hacc (psiTermEncl_spec hk (by omega) hp)
      (by rw [hν]; ring) (by rw [pow_succ]; linarith) (by rwa [abs_neg])
  | fuel + 1, k, p, acc, hk, hkM, hp, hacc => by
    have hτ := psiTermEncl_spec (V := V) hk (by omega : k ≤ M) hp
    obtain ⟨r, hν, hsign, habs⟩ := psiNu_eq_sum_add hk hy
    have hclose := stirlingClose_spec (V := V) (r := -r) hacc hτ
      (show -psiNu y = _ by rw [hν]; ring) (by rw [pow_succ]; linarith) (by rwa [abs_neg])
    rw [psiSumLoop]
    split_ifs with hstop hodd hodd
    · rwa [ite_eq_left hodd] at hclose
    · rwa [ite_eq_right hodd] at hclose
    all_goals
      have hp' : IsEnclPos (Encl.mul V p inv2) (1 / y ^ (2 * (k + 1))) := by
        have := hp.mul hV hinv2
        convert this using 1
        rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add]
        field_simp
      have hsum : ∑ i ∈ range (k + 1 - 1), psiTermT (i + 1) y
          = ∑ i ∈ range (k - 1), psiTermT (i + 1) y + psiTermT k y := by
        rw [show k + 1 - 1 = (k - 1) + 1 by omega, sum_range_succ,
          show k - 1 + 1 = k by omega]
      refine psiSumLoop_spec hV hy hinv2 tol fuel (k + 1) _ _ (by omega) (by omega) hp' ?_
      rw [hsum]
    · have : -(∑ i ∈ range (k - 1), psiTermT (i + 1) y + psiTermT k y)
          = -∑ i ∈ range (k - 1), psiTermT (i + 1) y + psiCoeffT k / y ^ (2 * k) := by
        rw [psiTermT, (Nat.odd_iff.mpr hodd).neg_one_pow]
        ring
      rw [this]
      exact hacc.add hτ.encloses
    · have : -(∑ i ∈ range (k - 1), psiTermT (i + 1) y + psiTermT k y)
          = -∑ i ∈ range (k - 1), psiTermT (i + 1) y - psiCoeffT k / y ^ (2 * k) := by
        rw [psiTermT, (Nat.even_iff.mpr (by omega : k % 2 = 0)).neg_one_pow]
        ring
      rw [this]
      exact hacc.sub hτ.encloses

/-- The asymptotic series on enclosures: `ψ(y)` for `y > 0`. -/
theorem digammaStirlingEncl_spec {V : ℕ} (hV : 64 ≤ V) {M : ℕ} (hM : 1 ≤ M) {Y : Encl} {y : ℝ}
    (hY : IsEnclPos Y y) (tol : AzFloat) :
    IsEncl (digammaStirlingEncl V M Y tol) (DLMF.psiR y) := by
  have : NeZero V := ⟨by omega⟩
  have hV2 : 2 ≤ V := by omega
  have hy : 0 < y := by obtain ⟨l, h, -, -, h0, h1, -⟩ := hY; linarith
  have hinv : IsEnclPos (Encl.div V (Encl.exact one) Y) (1 / y) := enclosesPos_one.div hV2 hY
  have hinv2 : IsEnclPos (Encl.mul V (Encl.div V (Encl.exact one) Y)
      (Encl.div V (Encl.exact one) Y)) (1 / y ^ 2) := by
    have := hinv.mul hV2 hinv
    convert this using 1
    field_simp
  have hN := psiSumLoop_spec hV2 (M := M) hy hinv2 tol (M - 1) 1 _ _ le_rfl (by omega)
    (by simpa using hinv2) (by simpa using isEncl0_exact_zero)
  have := ((lnOfEncl_pos hY hV).sub (w := V) hinv.encloses0.encloses.half).sub (w := V) hN
  unfold digammaStirlingEncl
  convert this using 1
  rw [psiNu]
  field_simp
  ring

/-! #### The shift sum: one division for two terms -/

/-- `1/(x + j) ≤ (b/a) · 1/(b + j)` for `0 < a ≤ x ≤ b`, `j ≥ 0`. -/
theorem one_div_add_le_mul {a b x j : ℝ} (ha : 0 < a) (hax : a ≤ x) (hab : a ≤ b)
    (hj : 0 ≤ j) : 1 / (x + j) ≤ b / a * (1 / (b + j)) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  rw [div_mul_div_comm, mul_one, div_le_div_iff₀ (by linarith) (by positivity)]
  nlinarith [mul_nonneg hj (sub_nonneg.mpr hab), mul_nonneg hb.le (sub_nonneg.mpr hax)]

/-- `((1 + E)/(1 − E))³ ≤ 1 + 32 E` for `0 ≤ E ≤ 1/64`. -/
theorem gamma_cube_le {E : ℝ} (h0 : 0 ≤ E) (h1 : E ≤ 1 / 64) :
    ((1 + E) / (1 - E)) ^ 3 ≤ 1 + 32 * E := by
  have hg : (1 + E) / (1 - E) ≤ 1 + 3 * E := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hg0 : 0 ≤ (1 + E) / (1 - E) := div_nonneg (by linarith) (by linarith)
  calc ((1 + E) / (1 - E)) ^ 3 ≤ (1 + 3 * E) ^ 3 := pow_le_pow_left₀ hg0 hg 3
    _ ≤ 1 + 32 * E := by nlinarith [mul_nonneg h0 h0, mul_nonneg (mul_nonneg h0 h0) h0]

section Harmonic

variable {a b x E : ℝ}

/-- A single term from one quotient rounded down. -/
theorem harmonic_single (ha : 0 < a) (hax : a ≤ x) (hxb : x ≤ b) (hE0 : 0 ≤ E) (hE1 : E ≤ 1 / 64)
    {j y q : ℝ} (hj : 0 ≤ j) (hy1 : b + j ≤ y) (hy2 : y ≤ (b + j) * (1 + E))
    (hq1 : q ≤ 1 / y) (hq2 : 1 / y * (1 - E) ≤ q) :
    q ≤ 1 / (x + j) ∧ 1 / (x + j) ≤ b / a * ((1 + E) / (1 - E)) ^ 3 * q := by
  have hb : 0 < b := by linarith
  have hB : 0 < b + j := by linarith
  have hy : 0 < y := by linarith
  have hE : 0 < 1 - E := by linarith
  set g := (1 + E) / (1 - E) with hg
  have hg1 : 1 ≤ g := by rw [hg, le_div_iff₀ hE]; linarith
  have hq0 : 0 ≤ q := le_trans (mul_nonneg (by positivity) hE.le) hq2
  constructor
  · exact hq1.trans (one_div_le_one_div_of_le (by linarith) (by linarith))
  · have h1 := one_div_add_le_mul ha hax (hax.trans hxb) hj
    have h2 : 1 / (b + j) ≤ g * q := by
      have : 1 / (b + j) ≤ (1 + E) * (1 / y) := by
        rw [mul_one_div, div_le_div_iff₀ hB hy]
        linarith
      have h3 : (1 + E) * (1 / y) ≤ g * q := by
        rw [hg, div_mul_eq_mul_div, le_div_iff₀ hE]
        nlinarith [mul_le_mul_of_nonneg_left hq2 (by linarith : (0 : ℝ) ≤ 1 + E)]
      linarith
    have hba : 0 < b / a := div_pos hb ha
    have hgq : g * q ≤ g ^ 3 * q := by
      apply mul_le_mul_of_nonneg_right _ hq0
      nlinarith [mul_le_mul hg1 hg1 zero_le_one (by linarith)]
    calc 1 / (x + j) ≤ b / a * (1 / (b + j)) := h1
      _ ≤ b / a * (g ^ 3 * q) := mul_le_mul_of_nonneg_left (h2.trans hgq) hba.le
      _ = b / a * g ^ 3 * q := by ring

/-- Two consecutive terms from one quotient rounded down. -/
theorem harmonic_pair (ha : 0 < a) (hax : a ≤ x) (hxb : x ≤ b) (hE0 : 0 ≤ E) (hE1 : E ≤ 1 / 64)
    {j y yc yf N D q : ℝ} (hj : 0 ≤ j) (hy1 : b + j ≤ y) (hy2 : y ≤ (b + j) * (1 + E))
    (hc1 : y + 1 ≤ yc) (hc2 : yc ≤ (y + 1) * (1 + E)) (hf1 : yf ≤ y + 1)
    (hf2 : (y + 1) * (1 - E) ≤ yf) (hN1 : N ≤ y + yf) (hN2 : (y + yf) * (1 - E) ≤ N)
    (hD1 : y * yc ≤ D) (hD2 : D ≤ y * yc * (1 + E)) (hq1 : q ≤ N / D)
    (hq2 : N / D * (1 - E) ≤ q) :
    q ≤ 1 / (x + j) + 1 / (x + (j + 1)) ∧
      1 / (x + j) + 1 / (x + (j + 1)) ≤ b / a * ((1 + E) / (1 - E)) ^ 3 * q := by
  have hb : 0 < b := by linarith
  have hB : 0 < b + j := by linarith
  have hy : 0 < y := by linarith
  have hE : 0 < 1 - E := by linarith
  have hyy : 0 < y * (y + 1) := by positivity
  have hD : 0 < D := lt_of_lt_of_le (mul_pos hy (by linarith)) hD1
  have hN0 : 0 ≤ N := le_trans (mul_nonneg (by nlinarith) hE.le) hN2
  have hq0 : 0 ≤ q := le_trans (mul_nonneg (div_nonneg hN0 hD.le) hE.le) hq2
  set g := (1 + E) / (1 - E) with hg
  have hba : 0 < b / a := div_pos hb ha
  -- the exact value at `y`
  have hfy : 1 / y + 1 / (y + 1) = (2 * y + 1) / (y * (y + 1)) := by
    field_simp
    ring
  constructor
  · -- `q ≤ N/D ≤ (2y + 1)/(y (y + 1)) = 1/y + 1/(y + 1) ≤ 1/(x + j) + 1/(x + j + 1)`
    have h1 : N / D ≤ (2 * y + 1) / (y * (y + 1)) := by
      rw [div_le_div_iff₀ hD hyy]
      have : y * (y + 1) ≤ D := le_trans (mul_le_mul_of_nonneg_left hc1 hy.le) hD1
      nlinarith [mul_le_mul_of_nonneg_left this hN0, mul_nonneg hN0 hyy.le]
    have h2 : 1 / y ≤ 1 / (x + j) := one_div_le_one_div_of_le (by linarith) (by linarith)
    have h3 : 1 / (y + 1) ≤ 1 / (x + (j + 1)) :=
      one_div_le_one_div_of_le (by linarith) (by linarith)
    linarith
  · have t1 := one_div_add_le_mul ha hax (hax.trans hxb) hj
    have t2 := one_div_add_le_mul ha hax (hax.trans hxb) (by linarith : (0 : ℝ) ≤ j + 1)
    have s1 : 1 / (b + j) ≤ (1 + E) * (1 / y) := by
      rw [mul_one_div, div_le_div_iff₀ hB hy]
      linarith
    have s2 : 1 / (b + (j + 1)) ≤ (1 + E) * (1 / (y + 1)) := by
      rw [mul_one_div, div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    -- `(2y + 1)/(y (y + 1)) ≤ q (1 + E)² / (1 − E)³`
    have hNlow : (2 * y + 1) * (1 - E) ^ 2 ≤ N := by
      have : (2 * y + 1) * (1 - E) ≤ y + yf := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right this hE.le]
    have hDup : D ≤ y * (y + 1) * (1 + E) ^ 2 := by
      have : y * yc ≤ y * ((y + 1) * (1 + E)) := mul_le_mul_of_nonneg_left hc2 hy.le
      nlinarith [mul_le_mul_of_nonneg_right this (by linarith : (0 : ℝ) ≤ 1 + E)]
    have hND : (2 * y + 1) * (1 - E) ^ 2 / (y * (y + 1) * (1 + E) ^ 2) ≤ N / D :=
      div_le_div₀ hN0 hNlow hD hDup
    have hE2 : (0 : ℝ) ≤ (1 + E) ^ 2 := by positivity
    have hval : (2 * y + 1) / (y * (y + 1)) * (1 - E) ^ 3 ≤ (1 + E) ^ 2 * q := by
      have e : (2 * y + 1) * (1 - E) ^ 2 / (y * (y + 1) * (1 + E) ^ 2)
          = (2 * y + 1) / (y * (y + 1)) * (1 - E) ^ 2 / (1 + E) ^ 2 := by
        field_simp
      rw [e, div_le_iff₀ (by positivity)] at hND
      calc (2 * y + 1) / (y * (y + 1)) * (1 - E) ^ 3
          = (2 * y + 1) / (y * (y + 1)) * (1 - E) ^ 2 * (1 - E) := by ring
        _ ≤ N / D * (1 + E) ^ 2 * (1 - E) := mul_le_mul_of_nonneg_right hND hE.le
        _ = (1 + E) ^ 2 * (N / D * (1 - E)) := by ring
        _ ≤ (1 + E) ^ 2 * q := mul_le_mul_of_nonneg_left hq2 hE2
    have hfin : (1 + E) * ((2 * y + 1) / (y * (y + 1))) ≤ g ^ 3 * q := by
      rw [hg, div_pow, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      calc (1 + E) * ((2 * y + 1) / (y * (y + 1))) * (1 - E) ^ 3
          = (1 + E) * ((2 * y + 1) / (y * (y + 1)) * (1 - E) ^ 3) := by ring
        _ ≤ (1 + E) * ((1 + E) ^ 2 * q) :=
            mul_le_mul_of_nonneg_left hval (by linarith : (0 : ℝ) ≤ 1 + E)
        _ = (1 + E) ^ 3 * q := by ring
    calc 1 / (x + j) + 1 / (x + (j + 1))
        ≤ b / a * (1 / (b + j)) + b / a * (1 / (b + (j + 1))) := add_le_add t1 t2
      _ ≤ b / a * ((1 + E) * (1 / y + 1 / (y + 1))) := by
          rw [← mul_add]
          exact mul_le_mul_of_nonneg_left (by linarith) hba.le
      _ ≤ b / a * (g ^ 3 * q) := by
          rw [hfy]
          exact mul_le_mul_of_nonneg_left hfin hba.le
      _ = b / a * g ^ 3 * q := by ring

end Harmonic

/-- The loop keeps a lower sum and the sum of its quotients rounded up: every quotient is
below its terms and within the factor `K₀ = (b/a) ((1 + E)/(1 − E))³` of them. -/
theorem harmonicLoop_spec {V : ℕ} [NeZero V] (hV : 8 ≤ V) {bF : AzFloat} {a b xv : ℝ}
    (hb : bF.toVal = some (b : EReal)) (ha : 0 < a) (hax : a ≤ xv) (hxb : xv ≤ b) :
    ∀ (m i : ℕ) (lo up : AzFloat) (lov upv A : ℝ), lo.toVal = some (lov : EReal) →
      up.toVal = some (upv : EReal) → lov ≤ A →
      A ≤ b / a * ((1 + 2 * (1 / 2 : ℝ) ^ V) / (1 - 2 * (1 / 2 : ℝ) ^ V)) ^ 3 * upv → 0 ≤ upv →
      ∃ lo' up' : ℝ, (harmonicLoop V bF m i lo up).1.toVal = some (lo' : EReal) ∧
        (harmonicLoop V bF m i lo up).2.toVal = some (up' : EReal) ∧
        lo' ≤ A + ∑ j ∈ range m, 1 / (xv + ((i + j : ℕ) : ℝ)) ∧
        A + ∑ j ∈ range m, 1 / (xv + ((i + j : ℕ) : ℝ))
          ≤ b / a * ((1 + 2 * (1 / 2 : ℝ) ^ V) / (1 - 2 * (1 / 2 : ℝ) ^ V)) ^ 3 * up' ∧
        0 ≤ up'
  | 0, i, lo, up, lov, upv, A, hlo, hup, h1, h2, h3 => by
    rw [harmonicLoop, sum_range_zero, add_zero]
    exact ⟨lov, upv, hlo, hup, h1, h2, h3⟩
  | 1, i, lo, up, lov, upv, A, hlo, hup, h1, h2, h3 => by
    set E := 2 * (1 / 2 : ℝ) ^ V with hEdef
    have hE0 : 0 ≤ E := by positivity
    have hE1 : E ≤ 1 / 64 := by
      have : (1 / 2 : ℝ) ^ V ≤ (1 / 2) ^ 8 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hV
      rw [hEdef]; norm_num at this ⊢; linarith
    have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    have hbpos : 0 < b := by linarith
    obtain ⟨y, hy, hy1, hy2⟩ := addCeiling_abs hb (toVal_ofAzNat_ofNat i) V
    rw [abs_of_pos (by linarith)] at hy2
    have hy0 : 0 < y := by linarith
    obtain ⟨q, hq, hq1, hq2⟩ := divFloor_abs toVal_one' hy hy0.ne' V
    rw [abs_of_pos (by positivity)] at hq2
    obtain ⟨hA, hB⟩ := harmonic_single ha hax hxb hE0 hE1 hi0 hy1 (by rw [hEdef]; linarith)
      hq1 (by rw [hEdef]; linarith)
    have hq0 : 0 ≤ q := by
      have : 0 ≤ 1 / y * (1 - E) := mul_nonneg (by positivity) (by linarith)
      rw [hEdef] at this; linarith
    obtain ⟨lo', hlo', hlo'1, -⟩ := addFloor_abs hlo hq V
    obtain ⟨up', hup', hup'1, -⟩ := addCeiling_abs hup hq V
    have hK : 0 ≤ b / a * ((1 + E) / (1 - E)) ^ 3 := by
      have : 0 < 1 - E := by linarith
      positivity
    rw [harmonicLoop, sum_range_one, Nat.add_zero]
    refine ⟨lo', up', hlo', hup', by linarith, ?_, by linarith⟩
    calc A + 1 / (xv + (i : ℝ)) ≤ b / a * ((1 + E) / (1 - E)) ^ 3 * upv
          + b / a * ((1 + E) / (1 - E)) ^ 3 * q := add_le_add h2 hB
      _ = b / a * ((1 + E) / (1 - E)) ^ 3 * (upv + q) := by ring
      _ ≤ b / a * ((1 + E) / (1 - E)) ^ 3 * up' := mul_le_mul_of_nonneg_left hup'1 hK
  | m + 2, i, lo, up, lov, upv, A, hlo, hup, h1, h2, h3 => by
    set E := 2 * (1 / 2 : ℝ) ^ V with hEdef
    have hE0 : 0 ≤ E := by positivity
    have hE1 : E ≤ 1 / 64 := by
      have : (1 / 2 : ℝ) ^ V ≤ (1 / 2) ^ 8 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hV
      rw [hEdef]; norm_num at this ⊢; linarith
    have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    have hbpos : 0 < b := by linarith
    obtain ⟨y, hy, hy1, hy2⟩ := addCeiling_abs hb (toVal_ofAzNat_ofNat i) V
    rw [abs_of_pos (by linarith)] at hy2
    have hy0 : 0 < y := by linarith
    obtain ⟨yf, hyf, hyf1, hyf2⟩ := addFloor_abs hy toVal_one' V
    rw [abs_of_pos (by linarith)] at hyf2
    obtain ⟨yc, hyc, hyc1, hyc2⟩ := addCeiling_abs hy toVal_one' V
    rw [abs_of_pos (by linarith)] at hyc2
    have hyf0 : 0 ≤ yf := by nlinarith
    obtain ⟨N, hN, hN1, hN2⟩ := addFloor_abs hy hyf V
    rw [abs_of_pos (by linarith)] at hN2
    obtain ⟨D, hD, hD1, hD2⟩ := mulCeiling_abs hy hyc V
    rw [abs_of_pos (mul_pos hy0 (by linarith))] at hD2
    have hD0 : 0 < D := lt_of_lt_of_le (mul_pos hy0 (by linarith)) hD1
    have hN0 : 0 ≤ N := by nlinarith
    obtain ⟨q, hq, hq1, hq2⟩ := divFloor_abs hN hD hD0.ne' V
    rw [abs_of_nonneg (div_nonneg hN0 hD0.le)] at hq2
    obtain ⟨hA, hB⟩ := harmonic_pair ha hax hxb hE0 hE1 hi0 hy1 (by rw [hEdef]; linarith)
      hyc1 (by rw [hEdef]; linarith) hyf1 (by rw [hEdef]; linarith) hN1
      (by rw [hEdef]; linarith) hD1 (by rw [hEdef]; linarith) hq1 (by rw [hEdef]; linarith)
    have hq0 : 0 ≤ q := by
      have : 0 ≤ N / D * (1 - E) := mul_nonneg (div_nonneg hN0 hD0.le) (by linarith)
      rw [hEdef] at this; linarith
    obtain ⟨lo', hlo', hlo'1, -⟩ := addFloor_abs hlo hq V
    obtain ⟨up', hup', hup'1, -⟩ := addCeiling_abs hup hq V
    have hK : 0 ≤ b / a * ((1 + E) / (1 - E)) ^ 3 := by
      have : 0 < 1 - E := by linarith
      positivity
    have hstep : A + (1 / (xv + (i : ℝ)) + 1 / (xv + ((i : ℝ) + 1)))
        ≤ b / a * ((1 + E) / (1 - E)) ^ 3 * up' := by
      calc A + (1 / (xv + (i : ℝ)) + 1 / (xv + ((i : ℝ) + 1)))
          ≤ b / a * ((1 + E) / (1 - E)) ^ 3 * upv + b / a * ((1 + E) / (1 - E)) ^ 3 * q :=
            add_le_add h2 hB
        _ = b / a * ((1 + E) / (1 - E)) ^ 3 * (upv + q) := by ring
        _ ≤ b / a * ((1 + E) / (1 - E)) ^ 3 * up' := mul_le_mul_of_nonneg_left hup'1 hK
    obtain ⟨lo'', up'', k1, k2, k3, k4, k5⟩ := harmonicLoop_spec hV hb ha hax hxb m (i + 2) _ _
      lo' up' (A + (1 / (xv + (i : ℝ)) + 1 / (xv + ((i : ℝ) + 1)))) hlo' hup'
      (by linarith) hstep (by linarith)
    have hsum : ∑ j ∈ range (m + 2), 1 / (xv + ((i + j : ℕ) : ℝ))
        = (1 / (xv + (i : ℝ)) + 1 / (xv + ((i : ℝ) + 1)))
          + ∑ j ∈ range m, 1 / (xv + ((i + 2 + j : ℕ) : ℝ)) := by
      rw [sum_range_succ', sum_range_succ']
      simp only [Nat.add_zero, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, zero_add]
      have : ∀ j : ℕ, (i : ℝ) + ((j : ℝ) + 1 + 1) = (i : ℝ) + 2 + j := fun j => by ring
      simp only [this]
      ring
    rw [harmonicLoop, hsum, ← add_assoc]
    exact ⟨lo'', up'', k1, k2, k3, k4, k5⟩

/-- The sum `∑_{j<i} 1/(x + j)` on enclosures. -/
theorem harmonicEncl_spec {V : ℕ} [NeZero V] (hV : 8 ≤ V) {X : Encl} {xv : ℝ}
    (hX : IsEnclPos X xv) (i : ℕ) :
    IsEncl (harmonicEncl V X i) (∑ j ∈ range i, 1 / (xv + j)) := by
  obtain ⟨a, b, ha, hb, ha0, hax, hxb⟩ := hX
  set E := 2 * (1 / 2 : ℝ) ^ V with hEdef
  have hE0 : 0 ≤ E := by positivity
  have hE1 : E ≤ 1 / 64 := by
    have : (1 / 2 : ℝ) ^ V ≤ (1 / 2) ^ 8 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hV
    rw [hEdef]; norm_num at this ⊢; linarith
  have hb0 : 0 < b := by linarith
  have hK0 : 0 ≤ b / a * ((1 + E) / (1 - E)) ^ 3 := by
    have : 0 < 1 - E := by linarith
    positivity
  obtain ⟨lo, up, hlo, hup, h1, h2, h3⟩ := harmonicLoop_spec hV hb ha0 hax hxb i 0 zero zero
    0 0 0 toVal_zero' toVal_zero' le_rfl (by rw [mul_zero]) le_rfl
  simp only [zero_add] at h1 h2
  -- the factor
  obtain ⟨R, hR, hR1, -⟩ := divCeiling_abs hb ha ha0.ne' V
  have hpow : (powerOf2 (AzInt.ofInt 6 - (AzNat.ofNat V).toAzInt)).toVal
      = some (((64 : ℝ) * (1 / 2 : ℝ) ^ V : ℝ) : EReal) := by
    rw [toVal_powerOf2, AzInt.toInt_sub, AzInt.toInt_ofInt, AzNat.toInt_toAzInt,
      AzNat.toNat_ofNat, zpow_sub₀ (by norm_num), zpow_natCast, one_div_pow, one_div,
      div_eq_mul_inv]
    norm_num
  obtain ⟨o, ho, ho1, -⟩ := addCeiling_abs toVal_one' hpow V
  obtain ⟨K, hK, hK1, -⟩ := mulCeiling_abs hR ho V
  have hR0 : 0 < b / a := div_pos hb0 ha0
  have hKge : b / a * ((1 + E) / (1 - E)) ^ 3 ≤ K := by
    have hg := gamma_cube_le hE0 hE1
    have : (1 : ℝ) + 32 * E ≤ o := by rw [hEdef]; linarith
    calc b / a * ((1 + E) / (1 - E)) ^ 3 ≤ b / a * o :=
          mul_le_mul_of_nonneg_left (hg.trans this) hR0.le
      _ ≤ R * o := mul_le_mul_of_nonneg_right hR1 (by linarith)
      _ ≤ K := hK1
  obtain ⟨hi, hhi, hhi1, -⟩ := mulCeiling_abs hup hK V
  unfold harmonicEncl
  refine ⟨lo, hi, hlo, hhi, h1, ?_⟩
  calc ∑ j ∈ range i, 1 / (xv + (j : ℝ)) ≤ b / a * ((1 + E) / (1 - E)) ^ 3 * up := h2
    _ ≤ K * up := mul_le_mul_of_nonneg_right hKge h3
    _ = up * K := mul_comm _ _
    _ ≤ hi := hhi1

/-- **`digammaPosEncl X e w` encloses `ψ(x)`** for an enclosure `X` of `x` with a positive lower
end (`w ≥ 64`). -/
theorem digammaPosEncl_spec {X : Encl} {xv : ℝ} (hX : IsEnclPos X xv) (e : AzInt) {w : ℕ}
    (hw : 64 ≤ w) : IsEncl (digammaPosEncl X e w) (DLMF.psiR xv) := by
  set L := lnGammaShiftExp w with hL
  set V := w + 2 * L + 8 + 2 * w.log2 with hVdef
  have hV : 64 ≤ V := by omega
  have : NeZero V := ⟨by omega⟩
  have hV2 : 2 ≤ V := by omega
  have hpos : 0 < xv := by obtain ⟨l, h, -, -, h0, h1, -⟩ := hX; linarith
  have hM : ∀ E, 1 ≤ lnGammaTerms w E := fun E => by
    unfold lnGammaTerms; exact le_trans (by norm_num) (Nat.le_add_left 3 _)
  unfold digammaPosEncl
  simp only [← hL, ← hVdef]
  by_cases hδ : lnGammaShift X.1 e L = 0
  · rw [ite_eq_left hδ]
    exact digammaStirlingEncl_spec hV (hM _) hX _
  · rw [ite_eq_right hδ]
    have hY : IsEnclPos (Encl.add V X (Encl.nat (lnGammaShift X.1 e L)))
        (xv + (lnGammaShift X.1 e L : ℕ)) := hX.add hV2 (isEncl0_nat _)
    have hS := digammaStirlingEncl_spec hV (hM (max (L + 1) (if e.sign then e.abs.toNat else 0)))
      hY (powerOf2 (-(AzNat.ofNat (w + 16)).toAzInt))
    have := hS.sub (w := V) (harmonicEncl_spec (le_trans (by norm_num) hV) hX (lnGammaShift X.1 e L))
    convert this using 1
    have hnp : ∀ m : ℕ, xv ≠ -m := fun m hm => by
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    rw [DLMF.psiR_add_nat hnp]
    ring

/-! ### The reflection formula -/

/-- `cot (π x) = cot (π (x − k))` for an integer `k`. -/
theorem cot_pi_mul_sub_int (xv : ℝ) (k : ℤ) :
    Real.cot (π * xv) = Real.cot (π * (xv - k)) := by
  have h : π * xv = π * (xv - k) + k * π := by ring
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, h, Real.cos_add_int_mul_pi,
    Real.sin_add_int_mul_pi]
  have hne : ((-1 : ℝ)) ^ k ≠ 0 := zpow_ne_zero _ (by norm_num)
  rw [mul_div_mul_left _ _ hne]

/-- `digammaCot` encloses `π cot (π a)`. -/
theorem digammaCot_spec {A : Encl} {a : ℝ} (hA : IsEnclPos A a) {W : ℕ} (hW : 64 ≤ W) {w : ℕ}
    (hw : 64 ≤ w) {T : Encl} (h : digammaCot A W w = some T) :
    IsEncl T (π * Real.cot (π * a)) := by
  have : NeZero W := ⟨by omega⟩
  unfold digammaCot at h
  dsimp only at h
  split_ifs at h with hp
  rw [Option.some.injEq] at h
  subst h
  have hY := hA.mul (by omega : 2 ≤ W) (enclosesPos_pi hW)
  obtain ⟨tl, th, hl, hh, h0, h1, h2⟩ := hY
  obtain ⟨hs, hc⟩ := sinCosBracket_spec hl (abs_lt_two_zpow_expOf hl)
    (Nat.le_add_right_of_le hw : 64 ≤ w + sinLostBits (Encl.mul W A (Encl.pi W)).1)
  rw [abs_of_pos h0] at hs
  obtain ⟨slo, shi, hslo, hshi, hs1, hs2, -⟩ := hs
  obtain ⟨clo, chi, hclo, hchi, hc1, hc2, -⟩ := hc
  obtain ⟨r, hr, hrge⟩ := subCeiling_ge hh hl W
  have hE : IsEncl0 (Encl.exact (subPrecRound (Encl.mul W A (Encl.pi W)).2
      (Encl.mul W A (Encl.pi W)).1 W .Ceiling).1) r := ⟨r, r, hr, hr, by linarith, le_rfl, le_rfl⟩
  have hd : |a * π - tl| ≤ r := by rw [abs_of_nonneg (by linarith)]; linarith
  have hS : IsEncl _ (Real.sin (a * π)) :=
    IsEncl.widen (w := W) (x := Real.sin tl) ⟨slo, shi, hslo, hshi, hs1, hs2⟩ hE
      ((Real.abs_sin_sub_sin_le _ _).trans hd)
  have hC : IsEncl _ (Real.cos (a * π)) :=
    IsEncl.widen (w := W) (x := Real.cos tl) ⟨clo, chi, hclo, hchi, hc1, hc2⟩ hE
      ((Real.abs_cos_sub_cos_le _ _).trans hd)
  have hSpos := hS.pos_of_lt hp
  have := (hC.divPos (W := W) hSpos).mulPos (W := W) (enclosesPos_pi hW).encloses0
  convert this using 1
  rw [Real.cot_eq_cos_div_sin, mul_comm π a]
  ring

/-- **The reflection formula on enclosures** (`x` not an integer). -/
theorem digammaReflect_spec {xv : ℝ} (hni : ∀ n : ℤ, xv ≠ n) {w : ℕ} (hw : 64 ≤ w)
    {F : Option (Bool × Encl)} {k : ℤ}
    (hF : ∀ σ A, F = some (σ, A) → IsEnclPos A ((if σ then -1 else 1) * (xv - k)))
    {P : Encl} (hP : IsEncl P (DLMF.psiR (1 - xv))) {b : Encl}
    (h : digammaReflect F P w = some b) : IsEncl b (DLMF.psiR xv) := by
  have : NeZero (w + 16) := ⟨by omega⟩
  unfold digammaReflect at h
  split at h
  · exact absurd h (by simp)
  · rename_i σ A
    obtain ⟨T, hT, rfl⟩ := Option.map_eq_some_iff.mp h
    have hA := hF σ A rfl
    have hTe := digammaCot_spec hA (W := w + 16) (by omega) hw hT
    have href := DLMF.psiR_one_sub hni
    rw [cot_pi_mul_sub_int xv k] at href
    cases σ with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at hTe ⊢
      have := hP.sub (w := w + 16) hTe
      convert this using 1
      linarith
    | true =>
      simp only [↓reduceIte] at hTe ⊢
      have := hP.add (w := w + 16) hTe
      convert this using 1
      have hcot : Real.cot (π * (-1 * (xv - k))) = -Real.cot (π * (xv - k)) := by
        rw [show π * (-1 * (xv - k)) = -(π * (xv - k)) by ring, Real.cot_eq_cos_div_sin,
          Real.cot_eq_cos_div_sin, Real.cos_neg, Real.sin_neg, div_neg]
      rw [hcot]
      linarith

/-- **`digammaNegEncl` answers with an enclosure of `ψ(x)`**, `x < 0` not an integer. -/
theorem digammaNegEncl_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx0 : xv < 0) (hni : ∀ n : ℤ, xv ≠ n) (e : AzInt) {w : ℕ} (hw : 64 ≤ w) {b : Encl}
    (h : digammaNegEncl x e w = some b) : IsEncl b (DLMF.psiR xv) := by
  unfold digammaNegEncl at h
  dsimp only at h
  have : NeZero (w + 32) := ⟨by omega⟩
  have : NeZero (w + 16) := ⟨by omega⟩
  have hnx : (-x).toVal = some ((-xv : ℝ) : EReal) := by
    rw [toVal_neg, hx, Option.map_some, EReal.coe_neg]
  have hX₁ : IsEnclPos (Encl.add (w + 32) (Encl.exact (-x)) (Encl.exact one)) (-xv + 1) :=
    (isEnclPos_exact hnx (by linarith)).add (by omega) enclosesPos_one.encloses0
  have hP := digammaPosEncl_spec hX₁ ((if e.sign then e else 0) + 1) hw
  rw [show -xv + 1 = 1 - xv by ring] at hP
  exact digammaReflect_spec hni hw (k := (gammaNearInt x).toInt)
    (fun σ A hF => gammaFracEncl_spec hx (gammaNearInt x) hF) hP h

/-- **Every answer of `digammaEncl` encloses `ψ(x)`**, for `x > 0` (`pos`) or `x < 0` not an
integer. -/
theorem digammaEncl_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) {pos : Bool}
    (hpos : pos = true → 0 < xv) (hneg : pos = false → xv < 0 ∧ ∀ n : ℤ, xv ≠ n) (e : AzInt)
    {w : ℕ} (hw : 64 ≤ w) {b : Encl} (h : digammaEncl x e pos w = some b) :
    IsEncl b (DLMF.psiR xv) := by
  unfold digammaEncl at h
  cases pos with
  | true =>
    rw [ite_eq_left rfl, Option.some.injEq] at h
    subst h
    exact digammaPosEncl_spec (isEnclPos_exact hx (hpos rfl)) e hw
  | false =>
    rw [ite_eq_right (by simp)] at h
    exact digammaNegEncl_spec hx (hneg rfl).1 (hneg rfl).2 e hw h

/-! ### Tiny arguments -/

/-- The tiny-argument path answers with the rounding of `ψ(x)`. -/
theorem digammaTiny?_eq {s : Bool} {e : AzInt} {q : ℕ} {m : AzNat} (hv : FiniteValid q m) (p : ℕ)
    [NeZero p] (mode : RoundingMode) {r : AzFloat × Ordering}
    (h : digammaTiny? (finite s e q m hv) e p mode = some r) :
    r = roundVal p mode (some ((DLMF.psiR (finiteVal s e m) : ℝ) : EReal)) := by
  unfold digammaTiny? at h
  dsimp only at h
  split_ifs at h with hc
  obtain ⟨hs, he⟩ := hc
  obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp h
  set W := p + zivGuardBits + 8 with hW
  have : NeZero W := ⟨by omega⟩
  set xv := finiteVal s e m with hxv
  have hx : (finite s e q m hv).toVal = some (xv : EReal) := toVal_finite s e q m hv
  obtain ⟨hlt, h2e⟩ := abs_finiteVal_lt_of_tiny s hv hs he
  rw [← hxv] at hlt
  have hquarter : |xv| ≤ 1 / 4 := by
    have : (1 / 2 : ℝ) ^ (p + zivGuardBits + 8) ≤ 1 / 4 := by
      calc (1 / 2 : ℝ) ^ (p + zivGuardBits + 8) ≤ (1 / 2 : ℝ) ^ 2 :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        _ = 1 / 4 := by norm_num
    linarith
  have hx0 : xv ≠ 0 := finiteVal_ne_zero s e hv
  obtain ⟨hG1, hG2⟩ := psiR_near_zero hx0 hquarter
  obtain ⟨lo, hlo, hlo1, -⟩ := divFloor_abs toVal_one' hx hx0 W
  obtain ⟨c, hc, hc1, -⟩ := divCeiling_abs toVal_one' hx hx0 W
  obtain ⟨hi, hhi, hhi1⟩ := addCeiling_ge hc (toVal_ofAzNat_ofNat 2) W
  push_cast at hhi1
  have hR1 := rounds_setPrecRound (isFinite_of_toVal_coe hlo)
  rw [fval_of_toVal_coe hlo] at hR1
  have hR2 := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
  rw [fval_of_toVal_coe hhi] at hR2
  have hr := roundingPossible_eq p (-mode) (v := -DLMF.psiR xv) hR1 hR2 (by linarith)
    (by linarith) (fun h => absurd h (by linarith)) hr'
  rw [hr]
  have hneg := roundVal_neg p mode (-DLMF.psiR xv)
  rw [neg_neg] at hneg
  exact hneg.symm

end Azurite.AzFloat
