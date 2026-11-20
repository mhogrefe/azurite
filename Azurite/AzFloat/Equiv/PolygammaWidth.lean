/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.PolygammaBracket
import Azurite.AzFloat.Equiv.AltSeriesWidth
import Azurite.AzFloat.Equiv.LnGammaEventually
import Azurite.AzFloat.Equiv.BetaWidth
import Azurite.AzFloat.Equiv.LnGamma

/-!
# The bracket of the polygamma functions converges

The width of `polygammaEncl n x pos w` tends to `0` with the Ziv level.

* `LEncl.powBin`, `AEncl.mulPos`: powers by repeated squaring and the signed product.
* `polyTermEncl_width`, `polySumLoop_eq`: the series is an `altSumLoop`.
-/

namespace Azurite.AzFloat

open Finset Filter Topology

/-! ### Powers by repeated squaring -/

theorem Encl.powBinAux_zero (w : ℕ) (a : Encl) (fuel : ℕ) :
    Encl.powBinAux w a fuel 0 = Encl.exact one := by
  cases fuel <;> simp [Encl.powBinAux]

/-- The relative width of a power by repeated squaring, `n ≥ 1`. -/
theorem LEncl.powBinAux {w : ℕ} [NeZero w] (hu : (1 / 2 : ℝ) ^ w ≤ 1 / 8) {a : Encl}
    {x lam : ℝ} (ha : LEncl a x lam) :
    ∀ fuel n : ℕ, 1 ≤ n → n < 2 ^ fuel →
      LEncl (Encl.powBinAux w a fuel n) (x ^ n) (n * lam + (18 * n - 6) * (1 / 2 : ℝ) ^ w)
  | 0, n, hn1, hn => by
    rw [pow_zero, Nat.lt_one_iff] at hn
    omega
  | fuel + 1, n, hn1, hn => by
    rw [Encl.powBinAux, ite_eq_right (by omega : n ≠ 0)]
    dsimp only
    have hone : LEncl (Encl.exact one) (1 : ℝ) 0 := LEncl.exact toVal_one' one_pos
    by_cases h1 : n = 1
    · subst h1
      rw [show 1 / 2 = 0 by norm_num, Encl.powBinAux_zero, ite_eq_left (by norm_num)]
      have := ((hone.mul hu hone).mul hu ha).mono (le_of_eq (by ring :
        (0 : ℝ) + 0 + 6 * (1 / 2 : ℝ) ^ w + lam + 6 * (1 / 2 : ℝ) ^ w
          = ((1 : ℕ) : ℝ) * lam + (18 * ((1 : ℕ) : ℝ) - 6) * (1 / 2 : ℝ) ^ w))
      simpa using this
    have hm1 : 1 ≤ n / 2 := by omega
    have hh := LEncl.powBinAux hu ha fuel (n / 2) hm1 (by rw [pow_succ] at hn; omega)
    have hsq := hh.mul hu hh
    have hu0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
    by_cases ho : n % 2 = 1
    · rw [ite_eq_left ho]
      have hx : x ^ n = x ^ (n / 2) * x ^ (n / 2) * x := by
        conv_lhs => rw [← Nat.div_add_mod n 2, ho, pow_succ, pow_mul, pow_two]
        rw [mul_pow]
      rw [hx]
      refine (hsq.mul hu ha).mono ?_
      have hn' : (n : ℝ) = 2 * ((n / 2 : ℕ) : ℝ) + 1 := by
        have : n = 2 * (n / 2) + 1 := by omega
        exact_mod_cast this
      rw [hn']
      nlinarith
    · rw [ite_eq_right ho]
      have hx : x ^ n = x ^ (n / 2) * x ^ (n / 2) := by
        conv_lhs => rw [← Nat.div_add_mod n 2, show n % 2 = 0 by omega, add_zero, pow_mul,
          pow_two]
        rw [mul_pow]
      rw [hx]
      refine hsq.mono (le_of_eq ?_)
      have hn' : (n : ℝ) = 2 * ((n / 2 : ℕ) : ℝ) := by
        have : n = 2 * (n / 2) := by omega
        exact_mod_cast this
      rw [hn']
      ring

theorem LEncl.powBin {w : ℕ} [NeZero w] (hu : (1 / 2 : ℝ) ^ w ≤ 1 / 8) {a : Encl}
    {x lam : ℝ} (ha : LEncl a x lam) {n : ℕ} (hn : 1 ≤ n) :
    LEncl (Encl.powBin w a n) (x ^ n) (n * lam + 18 * n * (1 / 2 : ℝ) ^ w) :=
  (LEncl.powBinAux hu ha _ n hn Nat.lt_log2_self).mono (by
    have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
    linarith)

/-! ### The signed product -/

/-- The width of `[a] · [b]` for `[a]` of any sign and a nonnegative `[b]`. -/
theorem AEncl.mulPos {W : ℕ} [NeZero W] {a b : Encl} {x y εa εb Ba Bb : ℝ}
    (ha : AEncl a x εa) (hb : AEncl0 b y εb) (hBa : |x| + εa ≤ Ba) (hBb : y + εb ≤ Bb) :
    AEncl (Encl.mulPos W a b) (x * y)
      (εa * Bb + Ba * εb + 4 * Ba * Bb * (1 / 2 : ℝ) ^ W) := by
  obtain ⟨l, h, hl, hh, h1, h2, h3⟩ := ha
  obtain ⟨bl, bh, hbl, hbh, hb0, hb1, hb2, hb3⟩ := hb
  have hlo := mul_lower_of_nonneg h1 hb0 hb1 hb2
  have hhi := mul_upper_of_nonneg h2 hb0 hb1 hb2
  have hu0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ W := by positivity
  have hxa := abs_le.mp (le_refl |x|)
  have hεa : 0 ≤ εa := by linarith
  have hεb : 0 ≤ εb := by linarith
  have hBa0 : 0 ≤ Ba := by linarith [abs_nonneg x]
  have hlB : |l| ≤ Ba := by rw [abs_le]; constructor <;> linarith
  have hhB : |h| ≤ Ba := by rw [abs_le]; constructor <;> linarith
  have hbhB : bh ≤ Bb := by linarith
  have hbh0 : 0 ≤ bh := by linarith
  have hblB : |bl| ≤ Bb := by rw [abs_of_nonneg hb0]; linarith
  have hbhB' : |bh| ≤ Bb := by rw [abs_of_nonneg hbh0]; exact hbhB
  have hprod : ∀ {s β : ℝ}, |s| ≤ Ba → |β| ≤ Bb → |s * β| ≤ Ba * Bb := fun hs hβ => by
    rw [abs_mul]
    exact mul_le_mul hs hβ (abs_nonneg _) hBa0
  unfold Encl.mulPos
  have e1 : ∃ r : ℝ, (mulPrecRound a.1 (if lt a.1 zero = true then b.2 else b.1) W
      .Floor).1.toVal = some (r : EReal) ∧ r ≤ (if l < 0 then l * bh else l * bl) ∧
      (if l < 0 then l * bh else l * bl) ≤ r + 2 * (Ba * Bb) * (1 / 2 : ℝ) ^ W := by
    by_cases hc : lt a.1 zero = true
    · rw [ite_eq_left hc, ite_eq_left ((lt_eq_true_iff hl toVal_zero').mp hc)]
      obtain ⟨r, hr, hr1, hr2⟩ := mulFloor_abs hl hbh W
      have := mul_le_mul_of_nonneg_right (hprod hlB hbhB') hu0
      exact ⟨r, hr, hr1, by linarith⟩
    · rw [ite_eq_right hc, ite_eq_right (fun h' => hc ((lt_eq_true_iff hl toVal_zero').mpr h'))]
      obtain ⟨r, hr, hr1, hr2⟩ := mulFloor_abs hl hbl W
      have := mul_le_mul_of_nonneg_right (hprod hlB hblB) hu0
      exact ⟨r, hr, hr1, by linarith⟩
  have e2 : ∃ r : ℝ, (mulPrecRound a.2 (if lt zero a.2 = true then b.2 else b.1) W
      .Ceiling).1.toVal = some (r : EReal) ∧ (if 0 < h then h * bh else h * bl) ≤ r ∧
      r ≤ (if 0 < h then h * bh else h * bl) + 2 * (Ba * Bb) * (1 / 2 : ℝ) ^ W := by
    by_cases hc : lt zero a.2 = true
    · rw [ite_eq_left hc, ite_eq_left ((lt_eq_true_iff toVal_zero' hh).mp hc)]
      obtain ⟨r, hr, hr1, hr2⟩ := mulCeiling_abs hh hbh W
      have := mul_le_mul_of_nonneg_right (hprod hhB hbhB') hu0
      exact ⟨r, hr, hr1, by linarith⟩
    · rw [ite_eq_right hc, ite_eq_right (fun h' => hc ((lt_eq_true_iff toVal_zero' hh).mpr h'))]
      obtain ⟨r, hr, hr1, hr2⟩ := mulCeiling_abs hh hbl W
      have := mul_le_mul_of_nonneg_right (hprod hhB hblB) hu0
      exact ⟨r, hr, hr1, by linarith⟩
  obtain ⟨r₁, hr₁, a1, a2⟩ := e1
  obtain ⟨r₂, hr₂, c1, c2⟩ := e2
  refine ⟨r₁, r₂, hr₁, hr₂, a1.trans hlo, hhi.trans c1, ?_⟩
  -- the exact products differ by at most `εa Bb + Ba εb`
  have hdiff : (if 0 < h then h * bh else h * bl) - (if l < 0 then l * bh else l * bl)
      ≤ εa * Bb + Ba * εb := by
    have hl' := abs_le.mp hlB
    have p1 : (h - l) * bh ≤ εa * Bb :=
      mul_le_mul h3 hbhB hbh0 hεa
    have p2 : (h - l) * bl ≤ εa * Bb :=
      mul_le_mul h3 (by linarith) hb0 hεa
    by_cases c₁ : 0 < h <;> by_cases c₂ : l < 0
    · rw [ite_eq_left c₁, ite_eq_left c₂]
      nlinarith [mul_nonneg hBa0 hεb]
    · rw [ite_eq_left c₁, ite_eq_right c₂]
      have : l * (bh - bl) ≤ Ba * εb := mul_le_mul hl'.2 hb3 (by linarith) hBa0
      nlinarith
    · rw [ite_eq_right c₁, ite_eq_left c₂]
      have : (-l) * (bh - bl) ≤ Ba * εb := mul_le_mul (by linarith) hb3 (by linarith) hBa0
      nlinarith
    · rw [ite_eq_right c₁, ite_eq_right c₂]
      nlinarith [mul_nonneg hBa0 hεb]
  linarith

/-! ### The terms of the series -/

/-- A term of the series of `ψ`: the relative width of the power, plus `12 u`. -/
theorem psiTermEncl_width {V : ℕ} [NeZero V] (hu : (1 / 2 : ℝ) ^ V ≤ 1 / 8) {M k : ℕ}
    (hk : 1 ≤ k) (hkM : k ≤ M) {p : Encl} {y lam : ℝ} (hp : LEncl p (1 / y ^ (2 * k)) lam) :
    LEncl (psiTermEncl V (AzNat.tangentNumbers M) k p) (psiCoeffT k / y ^ (2 * k))
      (lam + 12 * (1 / 2 : ℝ) ^ V) := by
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
  have hTpos : (0 : ℝ) < (BZ.tangentNumber k : ℝ) := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    exact_mod_cast BZ.tangentNumber_pos j
  have hnum : LEncl (Encl.exact (ofAzNat ((AzNat.tangentNumbers M).getD (k - 1) 0)))
      (BZ.tangentNumber k : ℝ) 0 := by
    rw [← hTr]
    exact LEncl.exact (toVal_ofAzNat _) (by rw [hTr]; exact hTpos)
  have hden : LEncl (Encl.exact (ofAzNat
      (((1 : AzNat) <<< (4 * k)) - ((1 : AzNat) <<< (2 * k)))))
      ((4 : ℝ) ^ (2 * k) - 2 ^ (2 * k)) 0 := by
    rw [← hD]
    exact LEncl.exact (toVal_ofAzNat _) (by rw [hD]; exact hDpos)
  have := ((hnum.div (w := V) hu hden).mul (w := V) hu hp).mono
    (le_of_eq (by ring : (0 : ℝ) + 0 + 6 * (1 / 2 : ℝ) ^ V + lam + 6 * (1 / 2 : ℝ) ^ V
      = lam + 12 * (1 / 2 : ℝ) ^ V))
  unfold psiTermEncl
  convert this using 1
  rw [psiCoeffT]
  ring

/-- A term of the series of `ψ⁽ⁿ⁾`: the relative width of the power, plus `18 u`. -/
theorem polyTermEncl_width {V : ℕ} [NeZero V] (hu : (1 / 2 : ℝ) ^ V ≤ 1 / 8) {M k : ℕ}
    (hk : 1 ≤ k) (hkM : k ≤ M) (n : ℕ) {p : Encl} {y lam : ℝ}
    (hp : LEncl p (1 / y ^ (2 * k)) lam) :
    LEncl (polyTermEncl V (AzNat.tangentNumbers M) n k p)
      (psiCoeffT k * ((2 * k).ascFactorial n : ℝ) / y ^ (2 * k))
      (lam + 18 * (1 / 2 : ℝ) ^ V) := by
  have hq : (AzNat.factorialQuotient (2 * k + n - 1) (2 * k - 1)).toNat
      = (2 * k).ascFactorial n := by
    rw [AzNat.toNat_factorialQuotient _ _ (by omega)]
    exact Nat.div_eq_of_eq_mul_right (Nat.factorial_pos _)
      (Nat.factorial_mul_ascFactorial' (2 * k) n (by omega)).symm
  have hfac : LEncl (Encl.exact (ofAzNat (AzNat.factorialQuotient (2 * k + n - 1) (2 * k - 1))))
      ((2 * k).ascFactorial n : ℝ) 0 := by
    rw [← hq]
    exact LEncl.exact (toVal_ofAzNat _) (by
      rw [hq]
      have h0 := Nat.ascFactorial_pos (2 * k - 1) n
      rw [show 2 * k - 1 + 1 = 2 * k by omega] at h0
      exact_mod_cast h0)
  have := ((psiTermEncl_width hu hk hkM hp).mul (w := V) hu hfac).mono
    (le_of_eq (by ring : lam + 12 * (1 / 2 : ℝ) ^ V + 0 + 6 * (1 / 2 : ℝ) ^ V
      = lam + 18 * (1 / 2 : ℝ) ^ V))
  unfold polyTermEncl
  convert this using 1
  ring

/-- The loop of `ψ⁽ⁿ⁾` is the generic one. -/
theorem polySumLoop_eq (V : ℕ) (T : Array AzNat) (n : ℕ) (inv2 : Encl) (tol : AzFloat) :
    ∀ (fuel k : ℕ) (p acc : Encl), polySumLoop V T n inv2 tol fuel k p acc
      = altSumLoop V (polyTermEncl V T n) inv2 tol fuel k p acc
  | 0, k, p, acc => by rw [polySumLoop, altSumLoop]
  | fuel + 1, k, p, acc => by
    rw [polySumLoop, altSumLoop, polySumLoop_eq V T n inv2 tol fuel]

/-! ### The asymptotic series -/

/-- The term of index `k` of the scaled series, without its sign. -/
noncomputable def polyT (n k : ℕ) (y : ℝ) : ℝ :=
  psiCoeffT k * ((2 * k).ascFactorial n : ℝ) / y ^ (2 * k)

theorem polyT_pos (n : ℕ) {k : ℕ} (hk : 1 ≤ k) {y : ℝ} (hy : 0 < y) : 0 < polyT n k y := by
  have h0 := Nat.ascFactorial_pos (2 * k - 1) n
  rw [show 2 * k - 1 + 1 = 2 * k by omega] at h0
  have h1 : (0 : ℝ) < ((2 * k).ascFactorial n : ℝ) := by exact_mod_cast h0
  exact div_pos (mul_pos (psiCoeffT_pos hk) h1) (pow_pos hy _)

open Nat in
/-- **The width of the asymptotic series of `ψ⁽ⁿ⁾` on enclosures**, for `y ≥ 1`: `T` bounds
the terms, `Lam` their relative widths, `εS` the width of the sum, `C` the magnitudes. -/
theorem polyStirlingEncl_width {V : ℕ} (hV : 64 ≤ V) {M : ℕ} (hM : 1 ≤ M) {n : ℕ} (hn : 1 ≤ n)
    {Y : Encl} {y lamY : ℝ} (hY : LEncl Y y lamY) (hlamY : 0 ≤ lamY) (hy1 : 1 ≤ y)
    {tol : AzFloat} {tolv : ℝ} (htol : tol.toVal = some (tolv : EReal)) {T B Lam εS C : ℝ}
    (hT0 : 0 ≤ T) (hterm : ∀ k, 1 ≤ k → k ≤ M → polyT n k y ≤ T)
    (hLamge : (M + 1) * (2 * lamY + 24 * (1 / 2 : ℝ) ^ V) ≤ Lam) (hLam : Lam ≤ 1 / 2)
    (hBu : 4 * B * (1 / 2 : ℝ) ^ V ≤ 1)
    (hB : M * (T + 2 * T * Lam + 1) + 2 * T + 1 ≤ B)
    (hεSge : M * (2 * T * Lam + 4 * B * (1 / 2 : ℝ) ^ V) + max tolv (2 * polyT n M y)
      + 2 * B * (1 / 2 : ℝ) ^ V ≤ εS) (hεS : εS ≤ 1)
    (hC : ((n - 1)! : ℝ) + (n ! : ℝ) + T + 5 ≤ C) (hCu : 4 * C * (1 / 2 : ℝ) ^ V ≤ 1)
    (hfac : (n ! : ℝ) * (lamY + 12 * (1 / 2 : ℝ) ^ V) ≤ 1)
    (hlamP : n * lamY + 24 * n * (1 / 2 : ℝ) ^ V ≤ 1 / 2) :
    AEncl (polyStirlingEncl V M n Y tol) ((-1) ^ (n + 1) * polygammaR n y)
      (((n ! : ℝ) * (lamY + 12 * (1 / 2 : ℝ) ^ V) + εS + 8 * C * (1 / 2 : ℝ) ^ V) * 2
        + C * (2 * (n * lamY + 24 * n * (1 / 2 : ℝ) ^ V)) + 4 * C * 2 * (1 / 2 : ℝ) ^ V) := by
  have : NeZero V := ⟨by omega⟩
  have hu : (1 / 2 : ℝ) ^ V ≤ 1 / 8 := half_pow_le_eighth (by omega)
  have hu0 : (0 : ℝ) < (1 / 2 : ℝ) ^ V := by positivity
  have hy : 0 < y := by linarith
  have hfac1 : (1 : ℝ) ≤ (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hfac0 : (0 : ℝ) < ((n - 1)! : ℝ) := by exact_mod_cast Nat.factorial_pos (n - 1)
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
  have hμ : ∀ k, 1 ≤ k → k ≤ M → ∃ r : ℝ, polyNu n y = altPartial (fun k => polyT n k y) k + r ∧
      0 ≤ (-1) ^ (k + 1) * r ∧ |r| ≤ polyT n k y := fun k hk _ => polyNu_eq_sum_add hn hk hy
  have hacc : AEncl (Encl.exact zero) (altPartial (fun k => polyT n k y) 1) 0 := by
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
      + 18 * (1 / 2 : ℝ) ^ V ≤ Lam := by
    refine le_trans ?_ hLamge
    rw [Nat.cast_sub hM]
    push_cast
    nlinarith
  have hS := altSumLoop_width (V := V) (M := M) (t := fun k => polyT n k y)
    (q := fun k => 1 / y ^ (2 * k)) (term := polyTermEncl V (AzNat.tangentNumbers M) n)
    (c := 18) (μ := polyNu n y) (i2 := 1 / y ^ 2) hu hinv2
    (fun k => by
      show 1 / y ^ (2 * (k + 1)) = 1 / y ^ (2 * k) * (1 / y ^ 2)
      rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add]
      field_simp) htol hLam hT0 (by norm_num)
    (fun k hk _ => polyT_pos n hk hy) hterm
    (fun k p lam hk hkM hp => polyTermEncl_width hu hk hkM n hp) hμ hBu hB (M - 1) 1 _ _
    (2 * lamY + 18 * (1 / 2 : ℝ) ^ V) 0 le_rfl (by omega) (by simpa using hinv2)
    (by positivity) hcond hacc (by simp)
  rw [← polySumLoop_eq] at hS
  have hS' := hS.mono (ε' := εS) (by
    have hM' : ((M - 1 : ℕ) : ℝ) ≤ M := by exact_mod_cast Nat.sub_le M 1
    have := mul_le_mul_of_nonneg_right hM' hD0
    linarith)
  have hnuT : |polyNu n y| ≤ T := by
    obtain ⟨r, hr, -, habs⟩ := hμ 1 le_rfl hM
    have h0 : altPartial (fun k => polyT n k y) 1 = 0 := by
      unfold altPartial
      rw [Nat.sub_self, range_zero, sum_empty]
    rw [hr, h0, zero_add]
    exact habs.trans (hterm 1 le_rfl hM)
  -- the leading terms
  have hfacn : LEncl (Encl.exact (ofAzNat (AzNat.factorial n))) (n ! : ℝ) 0 := by
    have := LEncl.exact (toVal_ofAzNat (AzNat.factorial n))
      (by rw [AzNat.toNat_factorial]; linarith)
    rwa [AzNat.toNat_factorial] at this
  have hfacn1 : AEncl (Encl.exact (ofAzNat (AzNat.factorial (n - 1)))) ((n - 1)! : ℝ) 0 := by
    have := AEncl.exact (toVal_ofAzNat (AzNat.factorial (n - 1)))
    rwa [AzNat.toNat_factorial] at this
  have hlam12 : lamY + 12 * (1 / 2 : ℝ) ^ V ≤ 1 / 2 := by nlinarith
  have hmulL := (hfacn.mul hu hinv).mono (le_of_eq (by ring :
    0 + (lamY + 6 * (1 / 2 : ℝ) ^ V) + 6 * (1 / 2 : ℝ) ^ V = lamY + 12 * (1 / 2 : ℝ) ^ V))
  have hmulA := ((hmulL.toA (by positivity) hlam12).toA.mono
    (ε' := 2 * ((n ! : ℝ) * (lamY + 12 * (1 / 2 : ℝ) ^ V))) (by
      have h1 : (n ! : ℝ) * (1 / y) ≤ (n ! : ℝ) := by nlinarith
      have h2 : (0 : ℝ) ≤ lamY + 12 * (1 / 2 : ℝ) ^ V := by positivity
      nlinarith)).half
  have hval1 : (n ! : ℝ) * (1 / y) ≤ (n ! : ℝ) := by nlinarith
  have hval0 : 0 ≤ (n ! : ℝ) * (1 / y) := by positivity
  have hleadv0 : 0 ≤ ((n - 1)! : ℝ) + (n ! : ℝ) * (1 / y) / 2 := by positivity
  have habs1 : |((n - 1)! : ℝ) + (n ! : ℝ) * (1 / y) / 2 + polyNu n y|
      ≤ ((n - 1)! : ℝ) + (n ! : ℝ) + T := by
    have h1 := abs_add_le (((n - 1)! : ℝ) + (n ! : ℝ) * (1 / y) / 2) (polyNu n y)
    rw [abs_of_nonneg hleadv0] at h1
    linarith
  have hlead := hfacn1.add (w := V) hmulA (B := C) (by
    rw [abs_of_nonneg hleadv0]
    linarith)
  have hsum := hlead.add (w := V) hS' (B := C) (by linarith)
  -- the power
  have hpowL := (LEncl.powBin hu hinv hn).mono (le_of_eq (by ring :
    (n : ℝ) * (lamY + 6 * (1 / 2 : ℝ) ^ V) + 18 * n * (1 / 2 : ℝ) ^ V
      = n * lamY + 24 * n * (1 / 2 : ℝ) ^ V))
  have hpow1 : (1 / y) ^ n ≤ 1 := pow_le_one₀ hinv0.le hinvle
  have hpow0 : 0 < (1 / y) ^ n := pow_pos hinv0 n
  have hlamP0 : 0 ≤ (n : ℝ) * lamY + 24 * n * (1 / 2 : ℝ) ^ V := by positivity
  have hpowA := (hpowL.toA hlamP0 hlamP).mono
    (ε' := 2 * (n * lamY + 24 * n * (1 / 2 : ℝ) ^ V)) (by
      have := mul_le_mul_of_nonneg_right hpow1 hlamP0
      linarith)
  have hfin := hsum.mulPos (W := V) hpowA (Ba := C) (Bb := 2)
    (by linarith only [habs1, hfac, hCu, hεS, hC]) (by linarith only [hpow1, hlamP])
  unfold polyStirlingEncl
  have hyn : y ^ n ≠ 0 := (pow_pos hy n).ne'
  have e : ((n - 1)! : ℝ) + (n ! : ℝ) * (1 / y) / 2 + polyNu n y
      = y ^ n * ((-1) ^ (n + 1) * polygammaR n y) := by
    rw [polyNu]
    field_simp
    ring
  have e2 : (((n - 1)! : ℝ) + (n ! : ℝ) * (1 / y) / 2 + polyNu n y) * (1 / y) ^ n
      = (-1) ^ (n + 1) * polygammaR n y := by
    rw [e, one_div, inv_pow]
    field_simp
  rw [e2] at hfin
  refine hfin.mono (le_of_eq ?_)
  ring

/-! ### The shift sum -/

/-- The upper sum of `polyShiftLoop` is the lower one within the factor
`((1 + E)/(1 − E))^m`, `E = 2^(1−V)`. -/
theorem polyShiftLoop_ratio {V : ℕ} [NeZero V] (hV : 8 ≤ V) {bF : AzFloat} {b : ℝ}
    (hb : bF.toVal = some (b : EReal)) (hb0 : 0 < b) {k : ℕ} (hk : 1 ≤ k) :
    ∀ (m i : ℕ) (lo up : AzFloat) (lov upv c : ℝ), lo.toVal = some (lov : EReal) →
      up.toVal = some (upv : EReal) → 0 ≤ lov → 0 ≤ upv → 1 ≤ c → upv ≤ lov * c →
      ∃ lo' up' : ℝ, (polyShiftLoop V bF k m i lo up).1.toVal = some (lo' : EReal) ∧
        (polyShiftLoop V bF k m i lo up).2.toVal = some (up' : EReal) ∧
        up' ≤ lo' * (c * ((1 + 2 * (1 / 2 : ℝ) ^ V) / (1 - 2 * (1 / 2 : ℝ) ^ V)) ^ m)
  | 0, i, lo, up, lov, upv, c, hlo, hup, h0, h1, hc, h2 => by
    rw [polyShiftLoop, pow_zero, mul_one]
    exact ⟨lov, upv, hlo, hup, h2⟩
  | m + 1, i, lo, up, lov, upv, c, hlo, hup, h0, h1, hc, h2 => by
    obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = 2 * (1 / 2 : ℝ) ^ V := ⟨_, rfl⟩
    rw [← hEdef]
    have hE0 : 0 ≤ E := by rw [hEdef]; positivity
    have hE1 : E ≤ 1 / 64 := by
      have : (1 / 2 : ℝ) ^ V ≤ (1 / 2) ^ 8 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hV
      rw [hEdef]; norm_num at this ⊢; linarith
    have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    obtain ⟨y, hy, hy1, -⟩ := addCeiling_abs hb (toVal_ofAzNat_ofNat i) V
    have hy0 : 0 < y := by linarith
    obtain ⟨P, hP, hP1, -⟩ := powUp_spec (V := V) hy hy0 hk
    have hP0 : 0 < P := lt_of_lt_of_le (pow_pos hy0 k) hP1
    obtain ⟨q, hq, -, hq2⟩ := divFloor_abs toVal_one' hP hP0.ne' V
    rw [abs_of_pos (by positivity)] at hq2
    have hq0 : 0 ≤ q := by
      have : 0 ≤ 1 / P * (1 - E) := mul_nonneg (by positivity) (by linarith)
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
    obtain ⟨lo'', up'', e1, e2, e3⟩ :=
      polyShiftLoop_ratio hV hb hb0 hk m (i + 1) _ _ lo' up' (c * ρ) hlo' hup' hlo'0
        (by linarith) (by nlinarith) hstep
    rw [← hEdef, ← hρ] at e3
    rw [polyShiftLoop]
    refine ⟨lo'', up'', e1, e2, e3.trans (le_of_eq ?_)⟩
    rw [pow_succ]
    ring

/-- **The relative width of the shift sum.** -/
theorem polyShiftSum_width {V : ℕ} [NeZero V] (hV : 8 ≤ V) {n : ℕ} (h32 : 32 * (n + 1) ≤ 2 ^ V)
    {X : Encl} {xv lam₀ : ℝ} (hX : LEncl X xv lam₀) {i : ℕ} (hi : 1 ≤ i) :
    LEncl (polyShiftSum V X n i) (∑ j ∈ range i, 1 / (xv + j) ^ (n + 1))
      ((n + 1 : ℕ) * lam₀ + (80 * (n + 1 : ℕ) + 6 * i) * (1 / 2 : ℝ) ^ V) := by
  obtain ⟨l₀, h₀, hl₀, hh₀, hspec0, hspec1, hspec2⟩ := polyShiftSum_spec hV h32 hX.isEnclPos i
  obtain ⟨a, b, ha, hb, ha0, hax, hxb, hba⟩ := hX
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = n + 1 := ⟨_, rfl⟩
  rw [← hk] at hspec1 hspec2 ⊢
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (1 / 2 : ℝ) ^ V := ⟨_, rfl⟩
  rw [← hu]
  have hu0 : 0 < u := by rw [hu]; positivity
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = 2 * u := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by rw [hEdef]; positivity
  have hE1 : E ≤ 1 / 64 := by
    have : (1 / 2 : ℝ) ^ V ≤ (1 / 2) ^ 8 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hV
    rw [hEdef, hu]; norm_num at this ⊢; linarith
  have hb0 : 0 < b := by linarith
  have hk1 : 1 ≤ k := by omega
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hexpE : 1 + E ≤ Real.exp E := by linarith [Real.add_one_le_exp E]
  -- the two sums
  obtain ⟨lo, up, hlo, hup, hratio⟩ := polyShiftLoop_ratio hV hb hb0 hk1 i 0 zero zero 0 0 1
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
  obtain ⟨Pk, hPk, hPk1, hPk2⟩ := powUp_spec (V := V) hR hR0 (n := k) hk1
  rw [← hu, ← hEdef] at hPk2
  have hPk0 : 0 < Pk := lt_of_lt_of_le (pow_pos hR0 k) hPk1
  have hPke : Pk ≤ Real.exp (k * (lam₀ + E) + 4 * k * E) := by
    rw [Real.exp_add]
    refine hPk2.trans (mul_le_mul ?_ ?_ (by positivity) (Real.exp_pos _).le)
    · calc R ^ k ≤ Real.exp (lam₀ + E) ^ k := pow_le_pow_left₀ hR0.le hRe k
        _ = Real.exp (k * (lam₀ + E)) := by rw [← Real.exp_nat_mul]
    · calc (1 + E) ^ (4 * k) ≤ Real.exp E ^ (4 * k) :=
            pow_le_pow_left₀ (by linarith) hexpE _
        _ = Real.exp (4 * k * E) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
  obtain ⟨cb, hcb⟩ : ∃ cb : ℕ, cb = (32 * k).log2 + 1 := ⟨_, rfl⟩
  have hpow : (powerOf2 (AzInt.ofInt ((cb : ℕ) : ℤ) - (AzNat.ofNat V).toAzInt)).toVal
      = some ((((2 : ℝ) ^ cb) * u : ℝ) : EReal) := by
    rw [toVal_powerOf2, AzInt.toInt_sub, AzInt.toInt_ofInt, AzNat.toInt_toAzInt,
      AzNat.toNat_ofNat, zpow_sub₀ (by norm_num), zpow_natCast, zpow_natCast, hu, one_div_pow,
      one_div, div_eq_mul_inv]
  have hcbr : (2 : ℝ) ^ cb ≤ 64 * k := by
    have h1 : 2 ^ (32 * k).log2 ≤ 32 * k := Nat.log2_self_le (by omega)
    have h2 : 2 ^ cb ≤ 64 * k := by rw [hcb, pow_succ]; omega
    exact_mod_cast h2
  obtain ⟨o, ho, ho1, ho2⟩ := addCeiling_abs toVal_one' hpow V
  have hpc0 : (0 : ℝ) ≤ 2 ^ cb * u := by positivity
  rw [abs_of_nonneg (by linarith), ← hu] at ho2
  have ho0 : 0 < o := by linarith
  have hoe : o ≤ Real.exp (64 * k * u + E) := by
    rw [Real.exp_add]
    calc o ≤ (1 + 2 ^ cb * u) * (1 + E) := by rw [hEdef]; linarith
      _ ≤ Real.exp (64 * k * u) * Real.exp E := by
          refine mul_le_mul ?_ hexpE (by linarith) (Real.exp_pos _).le
          have := Real.add_one_le_exp (64 * k * u)
          nlinarith
  obtain ⟨K, hK, hK1, hK2⟩ := mulCeiling_abs hPk ho V
  rw [abs_of_pos (mul_pos hPk0 ho0), ← hu] at hK2
  have hK0 : 0 < K := lt_of_lt_of_le (mul_pos hPk0 ho0) hK1
  have hKe : K ≤ Real.exp (k * (lam₀ + E) + 4 * k * E + (64 * k * u + E) + E) := by
    rw [Real.exp_add, Real.exp_add]
    calc K ≤ Pk * o * (1 + E) := by rw [hEdef]; linarith
      _ ≤ Real.exp (k * (lam₀ + E) + 4 * k * E) * Real.exp (64 * k * u + E) * Real.exp E :=
          mul_le_mul (mul_le_mul hPke hoe ho0.le (Real.exp_pos _).le) hexpE (by linarith)
            (by positivity)
  -- the two ends, as the definition has them
  have hlo_eq : (polyShiftSum V X n i).1.toVal = some (lo : EReal) := by
    unfold polyShiftSum
    rw [← hk]
    exact hlo
  rw [hl₀, Option.some.injEq, EReal.coe_eq_coe_iff] at hlo_eq
  subst hlo_eq
  have hup0 : 0 ≤ up := by
    -- the upper sum is a ceiling of sums of nonnegative quotients; it is at least `l₀`
    by_contra hneg
    push Not at hneg
    have h1 : l₀ * ((1 + E) / (1 - E)) ^ i ≥ 0 := mul_nonneg hspec0 (pow_nonneg hρ0 i)
    have h2 := polyShiftLoop_spec hV hb ha0 hax hxb (k := k) hk1 i 0 zero zero 0 0 0
      toVal_zero' toVal_zero' le_rfl le_rfl (by rw [mul_zero]) le_rfl
    obtain ⟨lo2, up2, -, hup2, -, -, -, hup2nn⟩ := h2
    rw [hup, Option.some.injEq, EReal.coe_eq_coe_iff] at hup2
    linarith
  obtain ⟨hi', hhi', hhi1, hhi2⟩ := mulCeiling_abs hup hK V
  rw [abs_of_nonneg (mul_nonneg hup0 hK0.le), ← hu] at hhi2
  have hhi_eq : (polyShiftSum V X n i).2.toVal = some (hi' : EReal) := by
    unfold polyShiftSum
    dsimp only
    rw [← hk, ← hcb]
    exact hhi'
  rw [hh₀, Option.some.injEq, EReal.coe_eq_coe_iff] at hhi_eq
  subst hhi_eq
  have hfinal : h₀ ≤ l₀ * Real.exp ((k : ℝ) * lam₀ + (80 * k + 6 * i) * u) := by
    have s1 : up ≤ l₀ * Real.exp (3 * E * i) :=
      hratio.trans (mul_le_mul_of_nonneg_left hρi hspec0)
    have s2 : h₀ ≤ up * K * (1 + E) := by rw [hEdef]; linarith
    have s3 : up * K * (1 + E) ≤ l₀ * Real.exp (3 * E * i)
        * Real.exp (k * (lam₀ + E) + 4 * k * E + (64 * k * u + E) + E) * Real.exp E :=
      mul_le_mul (mul_le_mul s1 hKe hK0.le (by positivity)) hexpE (by linarith) (by positivity)
    have s4 : l₀ * Real.exp (3 * E * i)
        * Real.exp (k * (lam₀ + E) + 4 * k * E + (64 * k * u + E) + E) * Real.exp E
        = l₀ * Real.exp (3 * E * i + (k * (lam₀ + E) + 4 * k * E + (64 * k * u + E) + E)
          + E) := by
      rw [Real.exp_add (3 * E * i + (k * (lam₀ + E) + 4 * k * E + (64 * k * u + E) + E)) E,
        Real.exp_add (3 * E * i) (k * (lam₀ + E) + 4 * k * E + (64 * k * u + E) + E)]
      ring
    have s5 : 3 * E * i + (k * (lam₀ + E) + 4 * k * E + (64 * k * u + E) + E) + E
        ≤ (k : ℝ) * lam₀ + (80 * k + 6 * i) * u := by
      rw [hEdef]
      nlinarith
    calc h₀ ≤ _ := s2
      _ ≤ _ := s3
      _ = _ := s4
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr s5) hspec0
  have hsumpos : 0 < ∑ j ∈ range i, 1 / (xv + (j : ℝ)) ^ k := by
    refine sum_pos (fun j _ => ?_) ⟨0, mem_range.mpr hi⟩
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hxv : 0 < xv := by linarith
    positivity
  have hl₀pos : 0 < l₀ := by
    rcases hspec0.eq_or_lt with h0 | h0
    · rw [← h0, zero_mul] at hfinal
      linarith
    · exact h0
  exact ⟨l₀, h₀, hl₀, hh₀, hl₀pos, hspec1, hspec2, hfinal⟩

/-! ### The sizes at level `w` -/

/-- A term of the scaled series is below `(2k + n)^(n+1) (9/10)^(2k−1)` when `k ≤ 2.7 y`. -/
theorem polyT_le (n : ℕ) {k : ℕ} (hk : 1 ≤ k) {y : ℝ} (hy1 : 1 ≤ y)
    (hky : (k : ℝ) ≤ 27 / 10 * y) :
    polyT n k y ≤ ((2 * k + n : ℕ) : ℝ) ^ (n + 1) * (9 / 10 : ℝ) ^ (2 * k - 1) := by
  have hy : 0 < y := by linarith
  have hst := stirlingTerm_le hk hy hky
  have hst0 : 0 < stirlingCoeffT k / y ^ (2 * k - 1) :=
    div_pos (stirlingCoeffT_pos hk) (pow_pos hy _)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hasc : ((2 * k).ascFactorial n : ℝ) ≤ ((2 * k + n : ℕ) : ℝ) ^ n := by
    have h1 := Nat.ascFactorial_le_pow_add (2 * k - 1) n
    rw [show 2 * k - 1 + 1 = 2 * k by omega] at h1
    have h2 : (2 * k - 1 + n) ^ n ≤ (2 * k + n) ^ n := Nat.pow_le_pow_left (by omega) n
    exact_mod_cast h1.trans h2
  have hasc0 : (0 : ℝ) ≤ ((2 * k).ascFactorial n : ℝ) := Nat.cast_nonneg _
  have hkn : (2 * (k : ℝ) - 1) ≤ ((2 * k + n : ℕ) : ℝ) := by
    push_cast
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hkn0 : (0 : ℝ) ≤ ((2 * k + n : ℕ) : ℝ) := Nat.cast_nonneg _
  have e : polyT n k y = (2 * k - 1) * (stirlingCoeffT k / y ^ (2 * k - 1))
      * ((2 * k).ascFactorial n : ℝ) / y := by
    unfold polyT
    rw [psiCoeffT_eq hk, show 2 * k = (2 * k - 1) + 1 by omega, pow_succ,
      show 2 * k - 1 + 1 = 2 * k by omega]
    field_simp
  rw [e, div_le_iff₀ hy]
  have h9 : (0 : ℝ) ≤ (9 / 10 : ℝ) ^ (2 * k - 1) := by positivity
  calc (2 * (k : ℝ) - 1) * (stirlingCoeffT k / y ^ (2 * k - 1)) * ((2 * k).ascFactorial n : ℝ)
      ≤ ((2 * k + n : ℕ) : ℝ) * (9 / 10 : ℝ) ^ (2 * k - 1) * ((2 * k + n : ℕ) : ℝ) ^ n :=
        mul_le_mul (mul_le_mul hkn hst hst0.le hkn0) hasc hasc0 (by positivity)
    _ = ((2 * k + n : ℕ) : ℝ) ^ (n + 1) * (9 / 10 : ℝ) ^ (2 * k - 1) * 1 := by
        rw [pow_succ]
        ring
    _ ≤ ((2 * k + n : ℕ) : ℝ) ^ (n + 1) * (9 / 10 : ℝ) ^ (2 * k - 1) * y :=
        mul_le_mul_of_nonneg_left hy1 (by positivity)

/-- The closing term of the series tends to `0` with the number of terms. -/
theorem tendsto_polyTail (n : ℕ) :
    Tendsto (fun m : ℕ => ((2 * m + n : ℕ) : ℝ) ^ (n + 1) * (9 / 10 : ℝ) ^ (2 * m - 1)) atTop
      (𝓝 0) := by
  have h0 := tendsto_pow_const_mul_const_pow_of_abs_lt_one (n + 1)
    (show |(81 / 100 : ℝ)| < 1 by rw [abs_of_pos] <;> norm_num)
  have h1 := h0.const_mul (((2 + n : ℕ) : ℝ) ^ (n + 1) * (10 / 9))
  rw [mul_zero] at h1
  refine squeeze_zero' (Eventually.of_forall fun m => by positivity) ?_ h1
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hbase : ((2 * m + n : ℕ) : ℝ) ≤ ((2 + n : ℕ) : ℝ) * m := by
    push_cast
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hp : ((2 * m + n : ℕ) : ℝ) ^ (n + 1) ≤ (((2 + n : ℕ) : ℝ) * m) ^ (n + 1) :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hbase _
  have h9 : (9 / 10 : ℝ) ^ (2 * m - 1) = 10 / 9 * (81 / 100 : ℝ) ^ m := by
    have : (9 / 10 : ℝ) ^ (2 * m - 1) * (9 / 10) = (81 / 100 : ℝ) ^ m := by
      rw [← pow_succ, show 2 * m - 1 + 1 = 2 * m by omega, pow_mul]
      norm_num
    linarith
  rw [h9]
  calc ((2 * m + n : ℕ) : ℝ) ^ (n + 1) * (10 / 9 * (81 / 100 : ℝ) ^ m)
      ≤ (((2 + n : ℕ) : ℝ) * m) ^ (n + 1) * (10 / 9 * (81 / 100 : ℝ) ^ m) :=
        mul_le_mul_of_nonneg_right hp (by positivity)
    _ = ((2 + n : ℕ) : ℝ) ^ (n + 1) * (10 / 9) * ((m : ℝ) ^ (n + 1) * (81 / 100 : ℝ) ^ m) := by
        rw [mul_pow]
        ring

theorem polyShift_le (lo : AzFloat) (n L M : ℕ) :
    polyShift lo n L M ≤ 2 ^ L + 2 ^ L * n / (2 * M) + 1 := by
  unfold polyShift
  dsimp only
  split_ifs
  · exact Nat.zero_le _
  · exact Nat.sub_le _ _

theorem polyShift_ge {lo : AzFloat} {lov : ℝ} (hlo : lo.toVal = some (lov : EReal))
    (h0 : 0 ≤ lov) (n L M : ℕ) :
    ((2 ^ L + 2 ^ L * n / (2 * M) + 1 : ℕ) : ℝ) ≤ lov + (polyShift lo n L M : ℕ) := by
  unfold polyShift
  dsimp only
  by_cases hc : le (ofAzNat (AzNat.ofNat (2 ^ L + 2 ^ L * n / (2 * M) + 1))) lo = true
  · rw [ite_eq_left hc]
    have := (le_eq_true_iff (toVal_ofAzNat_ofNat _) hlo).mp hc
    simpa using this
  · rw [ite_eq_right hc]
    obtain ⟨ht, ht2⟩ := truncToAzInt_spec hlo
    have habs : (((truncToAzInt lo).abs.toNat : ℕ) : ℝ) = |((truncToAzInt lo).toInt : ℝ)| := by
      have := AzInt.abs_toNat_eq (truncToAzInt lo)
      rw [← Int.cast_abs, ← this]
      push_cast
      rfl
    rw [abs_of_nonneg h0] at ht2
    have hsub : 2 ^ L + 2 ^ L * n / (2 * M) + 1
        ≤ (2 ^ L + 2 ^ L * n / (2 * M) + 1 - (truncToAzInt lo).abs.toNat)
          + (truncToAzInt lo).abs.toNat := by omega
    have hsubR : ((2 ^ L + 2 ^ L * n / (2 * M) + 1 : ℕ) : ℝ)
        ≤ ((2 ^ L + 2 ^ L * n / (2 * M) + 1 - (truncToAzInt lo).abs.toNat : ℕ) : ℝ)
          + ((truncToAzInt lo).abs.toNat : ℕ) := by exact_mod_cast hsub
    rw [habs] at hsubR
    linarith

theorem sum_inv_pow_le {x : ℝ} (hx : 0 < x) (k δ : ℕ) :
    ∑ j ∈ range δ, 1 / (x + (j : ℝ)) ^ k ≤ δ * (1 / x ^ k) := by
  calc ∑ j ∈ range δ, 1 / (x + (j : ℝ)) ^ k ≤ ∑ _j ∈ range δ, 1 / x ^ k :=
        sum_le_sum fun j _ => by
          have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
          exact one_div_le_one_div_of_le (pow_pos hx k)
            (pow_le_pow_left₀ hx.le (by linarith) k)
    _ = δ * (1 / x ^ k) := by rw [sum_const, card_range, nsmul_eq_mul]

/-! ### The width at level `w`, for a positive argument -/

section Sizes

open Nat

/-- The number of terms at level `w`. -/
def pgM (w : ℕ) : ℕ := lnGammaTerms w (lnGammaShiftExp w + 1)

noncomputable def pgMr (w : ℕ) : ℝ := (w : ℝ) / 2 + 4

noncomputable def pgT (n w : ℕ) : ℝ := ((w : ℝ) + 8 + n) ^ (n + 1)

noncomputable def pgLamP (w : ℕ) : ℝ := (pgMr w + 1) * 52

noncomputable def pgB (n w : ℕ) : ℝ := pgMr w * (2 * pgT n w + 1) + 2 * pgT n w + 1

noncomputable def pgTail (n w : ℕ) : ℝ :=
  max ((1 / 2 : ℝ) ^ (w + 16))
    (2 * (((2 * pgM w + n : ℕ) : ℝ) ^ (n + 1) * (9 / 10 : ℝ) ^ (2 * pgM w - 1)))

noncomputable def pgEpsS (n w : ℕ) : ℝ :=
  2 * (pgMr w * pgT n w * pgLamP w * (1 / 2 : ℝ) ^ w) + 4 * (pgMr w * pgB n w * (1 / 2 : ℝ) ^ w)
    + pgTail n w + 2 * (pgB n w * (1 / 2 : ℝ) ^ w)

noncomputable def pgC (n w : ℕ) : ℝ := ((n - 1)! : ℝ) + (n ! : ℝ) + pgT n w + 5

noncomputable def pgWS (n w : ℕ) : ℝ :=
  ((n ! : ℝ) * 26 * (1 / 2 : ℝ) ^ w + pgEpsS n w + 8 * (pgC n w * (1 / 2 : ℝ) ^ w)) * 2
    + 2 * (pgC n w * (38 * n) * (1 / 2 : ℝ) ^ w) + 8 * (pgC n w * (1 / 2 : ℝ) ^ w)

noncomputable def pgDelta (n w : ℕ) : ℝ := ((n : ℝ) + 1) * w

noncomputable def pgLsh (n w : ℕ) : ℝ := 88 * ((n : ℝ) + 1) + 6 * pgDelta n w + 6

noncomputable def pgHs (n : ℕ) (x : ℝ) (w : ℕ) : ℝ := (n ! : ℝ) * pgDelta n w / x ^ (n + 1)

noncomputable def pgBf (n : ℕ) (x : ℝ) (w : ℕ) : ℝ := pgC n w + pgHs n x w + 2

/-- **The width of the bracket of `(−1)ⁿ⁺¹ ψ⁽ⁿ⁾(x)`, `x > 0`, at level `w`** (for `w` large
enough). -/
noncomputable def pgE (n : ℕ) (x : ℝ) (w : ℕ) : ℝ :=
  pgWS n w + 2 * (pgHs n x w * pgLsh n w * (1 / 2 : ℝ) ^ w) + 4 * (pgBf n x w * (1 / 2 : ℝ) ^ w)

theorem pb_pgMr : PB pgMr := (PB.natCast.div_const 2).add (PB.const 4)

theorem pb_pgT (n : ℕ) : PB (pgT n) := ((PB.natCast.add (PB.const 8)).add (PB.const n)).pow _

theorem pb_pgLamP : PB pgLamP := by
  have := (pb_pgMr.add (PB.const 1)).mul (PB.const 52)
  exact this

theorem pb_pgB (n : ℕ) : PB (pgB n) :=
  ((pb_pgMr.mul (((pb_pgT n).const_mul 2).add (PB.const 1))).add ((pb_pgT n).const_mul 2)).add
    (PB.const 1)

theorem pb_pgC (n : ℕ) : PB (pgC n) :=
  ((PB.const (((n - 1)! : ℝ) + (n ! : ℝ))).add (pb_pgT n)).add (PB.const 5)

theorem pb_pgDelta (n : ℕ) : PB (pgDelta n) := PB.natCast.const_mul _

theorem pb_pgLsh (n : ℕ) : PB (pgLsh n) :=
  ((PB.const _).add ((pb_pgDelta n).const_mul 6)).add (PB.const 6)

theorem pb_pgHs (n : ℕ) (x : ℝ) : PB (pgHs n x) := ((pb_pgDelta n).const_mul _).div_const _

theorem pb_pgBf (n : ℕ) (x : ℝ) : PB (pgBf n x) :=
  ((pb_pgC n).add (pb_pgHs n x)).add (PB.const 2)

theorem pgM_bounds (w : ℕ) : 4 ≤ pgM w ∧ pgM w ≤ w / 2 + 4 :=
  ⟨(lnGammaTerms_bounds w _).1, (lnGammaTerms_bounds w _).2.1⟩

theorem tendsto_pgM : Tendsto pgM atTop atTop := by
  rw [tendsto_atTop]
  intro K
  obtain ⟨W, hW⟩ := lnGammaTerms_tendsto 0 K
  rw [eventually_atTop]
  refine ⟨max W 4, fun w hw => ?_⟩
  have hL := shiftExp_le_log2 (le_trans (le_max_right _ _) hw)
  exact hW w (le_trans (le_max_left _ _) hw) _ (by omega)

theorem tendsto_pgTail (n : ℕ) : Tendsto (pgTail n) atTop (𝓝 0) := by
  have h2 : Tendsto (fun w : ℕ => (1 / 2 : ℝ) ^ (w + 16)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
      (tendsto_add_atTop_nat 16)
  have h3 := ((tendsto_polyTail n).comp tendsto_pgM).const_mul 2
  rw [mul_zero] at h3
  have h4 := h2.max h3
  rw [max_self] at h4
  exact h4

theorem tendsto_pgEpsS (n : ℕ) : Tendsto (pgEpsS n) atTop (𝓝 0) := by
  have l1 := ((pb_pgMr.mul (pb_pgT n)).mul pb_pgLamP).tendsto
  have l2 := (pb_pgMr.mul (pb_pgB n)).tendsto
  have l3 := (pb_pgB n).tendsto
  have := (((l1.const_mul 2).add (l2.const_mul 4)).add (tendsto_pgTail n)).add (l3.const_mul 2)
  convert this using 2
  · rfl
  · norm_num

theorem tendsto_pgWS (n : ℕ) : Tendsto (pgWS n) atTop (𝓝 0) := by
  have l4 := (pb_pgC n).tendsto
  have l5 := ((pb_pgC n).mul (PB.const (38 * (n : ℝ)))).tendsto
  have l6 := (PB.const ((n ! : ℝ) * 26)).tendsto
  have := ((((l6.add (tendsto_pgEpsS n)).add (l4.const_mul 8)).mul_const 2).add
    (l5.const_mul 2)).add (l4.const_mul 8)
  convert this using 2
  · rfl
  · norm_num

theorem tendsto_pgE (n : ℕ) (x : ℝ) : Tendsto (pgE n x) atTop (𝓝 0) := by
  have l7 := ((pb_pgHs n x).mul (pb_pgLsh n)).tendsto
  have l8 := (pb_pgBf n x).tendsto
  have := ((tendsto_pgWS n).add (l7.const_mul 2)).add (l8.const_mul 4)
  convert this using 2
  · rfl
  · norm_num

end Sizes

open Nat in
/-- The size of `(−1)ⁿ⁺¹ ψ⁽ⁿ⁾(y)` for `y ≥ 1`. -/
theorem abs_polyH_le {n : ℕ} (hn : 1 ≤ n) {y : ℝ} (hy1 : 1 ≤ y) :
    |(-1) ^ (n + 1) * polygammaR n y| ≤ ((n - 1)! : ℝ) + (n ! : ℝ) + polyT n 1 y := by
  have hy : 0 < y := by linarith
  obtain ⟨r, hr, -, habs⟩ := polyNu_eq_sum_add hn (N := 1) le_rfl hy
  rw [Nat.sub_self, range_zero, sum_empty, zero_add] at hr
  have hyn : 0 < y ^ n := pow_pos hy n
  have hyn1 : 1 ≤ y ^ n := one_le_pow₀ hy1
  have hfac0 : (0 : ℝ) ≤ ((n - 1)! : ℝ) := Nat.cast_nonneg _
  have hfacn : (0 : ℝ) ≤ (n ! : ℝ) := Nat.cast_nonneg _
  have e : (-1) ^ (n + 1) * polygammaR n y
      = (((n - 1)! : ℝ) + (n ! : ℝ) / (2 * y) + r) / y ^ n := by
    rw [← hr, polyNu]
    field_simp
    ring
  have hr' := abs_le.mp habs
  have hq : (n ! : ℝ) / (2 * y) ≤ (n ! : ℝ) := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hq0 : 0 ≤ (n ! : ℝ) / (2 * y) := by positivity
  have ht : polyT n 1 y = psiCoeffT 1 * ((2 * 1).ascFactorial n : ℝ) / y ^ (2 * 1) := rfl
  rw [← ht] at hr'
  have ht0 := (polyT_pos n le_rfl hy).le
  rw [e, abs_div, abs_of_pos hyn, div_le_iff₀ hyn]
  have hnum : |((n - 1)! : ℝ) + (n ! : ℝ) / (2 * y) + r|
      ≤ ((n - 1)! : ℝ) + (n ! : ℝ) + polyT n 1 y := by
    rw [abs_le]
    constructor <;> linarith
  calc |((n - 1)! : ℝ) + (n ! : ℝ) / (2 * y) + r|
      ≤ (((n - 1)! : ℝ) + (n ! : ℝ) + polyT n 1 y) * 1 := by rw [mul_one]; exact hnum
    _ ≤ (((n - 1)! : ℝ) + (n ! : ℝ) + polyT n 1 y) * y ^ n :=
        mul_le_mul_of_nonneg_left hyn1 (by positivity)

open Nat in
/-- **The bracket of `(−1)ⁿ⁺¹ ψ⁽ⁿ⁾(x)` converges for `x > 0`**: its width is at most
`pgE n x w → 0` for all large `w`, uniformly in the enclosures of `x` of relative width at
most `8 · 2^(−w)`. -/
theorem polygammaPosEncl_conv {n : ℕ} (hn : 1 ≤ n) {xv : ℝ} (hxv : 0 < xv) :
    ∀ᶠ w in atTop, ∀ (X : Encl) (lam₀ : ℝ), LEncl X xv lam₀ → 0 ≤ lam₀ →
      lam₀ ≤ 8 * (1 / 2 : ℝ) ^ w →
      AEncl (polygammaPosEncl n X w) ((-1) ^ (n + 1) * polygammaR n xv) (pgE n xv w) := by
  have t1 := pb_pgLamP.tendsto
  have t2 := (pb_pgB n).tendsto
  have t4 := (pb_pgC n).tendsto
  have t5 := (PB.const ((n ! : ℝ) * 26)).tendsto
  have t6 := (PB.const (38 * (n : ℝ))).tendsto
  have t7 := (pb_pgLsh n).tendsto
  have t8 := ((pb_pgHs n xv).mul (pb_pgLsh n)).tendsto
  filter_upwards [t1.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    t2.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
    (tendsto_pgEpsS n).eventually (ge_mem_nhds one_pos),
    t4.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
    t5.eventually (ge_mem_nhds one_pos),
    t6.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    t7.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    t8.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    (tendsto_pgWS n).eventually (ge_mem_nhds one_pos), eventually_ge_atTop 64]
    with w e1 e2 e3 e4 e5 e6 e7 e8 e9 hw
  intro X lam₀ hX h0 hlam
  suffices key : ∃ x : ℝ, AEncl (polygammaPosEncl n X w) x (pgE n xv w) by
    obtain ⟨x, hx⟩ := key
    exact hx.of_isEncl (polygammaPosEncl_spec hn hX.isEnclPos hw)
  obtain ⟨hV, h32⟩ := polyWork_bounds hn hw
  obtain ⟨L, hL⟩ : ∃ L : ℕ, L = lnGammaShiftExp w := ⟨_, rfl⟩
  obtain ⟨V, hVdef⟩ : ∃ V : ℕ, V = polyWork n w := ⟨_, rfl⟩
  rw [← hVdef] at hV h32
  have hVw : w ≤ V := by rw [hVdef]; unfold polyWork; omega
  have : NeZero V := ⟨by omega⟩
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = pgM w := ⟨_, rfl⟩
  obtain ⟨hM4, hMle⟩ := pgM_bounds w
  rw [← hM] at hM4 hMle
  obtain ⟨U, hU⟩ : ∃ U : ℝ, U = (1 / 2 : ℝ) ^ w := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (1 / 2 : ℝ) ^ V := ⟨_, rfl⟩
  have hU0 : 0 < U := by rw [hU]; positivity
  have hu0 : 0 < u := by rw [hu]; positivity
  have huU : u ≤ U := by
    rw [hu, hU]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hVw
  have hu8 : u ≤ 1 / 8 := by rw [hu]; exact half_pow_le_eighth (by omega)
  rw [← hU] at hlam
  -- the sizes
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = pgT n w := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = pgB n w := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = pgC n w := ⟨_, rfl⟩
  obtain ⟨Mr, hMr⟩ : ∃ Mr : ℝ, Mr = pgMr w := ⟨_, rfl⟩
  have hwR : (64 : ℝ) ≤ w := by exact_mod_cast hw
  have hw0 : (0 : ℝ) ≤ w := by linarith
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hT0 : 0 ≤ T := by rw [hT]; unfold pgT; positivity
  have hMr0 : 0 ≤ Mr := by rw [hMr]; unfold pgMr; positivity
  have hMR : (M : ℝ) ≤ Mr := by
    have h1 : 2 * M ≤ w + 8 := by omega
    have h2 : (2 : ℝ) * M ≤ w + 8 := by exact_mod_cast h1
    rw [hMr]
    unfold pgMr
    linarith
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (by omega : 1 ≤ M)
  have hB0 : 0 ≤ B := by rw [hB]; unfold pgB; rw [← hMr, ← hT]; positivity
  have hfac0 : (0 : ℝ) ≤ ((n - 1)! : ℝ) := Nat.cast_nonneg _
  have hfacn : (1 : ℝ) ≤ (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hCdef : C = ((n - 1)! : ℝ) + (n ! : ℝ) + T + 5 := by rw [hC, hT]; rfl
  have hC0 : 0 ≤ C := by rw [hCdef]; positivity
  have hBdef : B = Mr * (2 * T + 1) + 2 * T + 1 := by rw [hB, hMr, hT]; rfl
  have hLamdef : pgLamP w * U = (Mr + 1) * (52 * U) := by
    rw [hMr]
    unfold pgLamP
    ring
  rw [← hU] at e1 e2 e4 e5 e6 e7 e8
  rw [← hB] at e2
  rw [← hC] at e4
  obtain ⟨Lam, hLam⟩ : ∃ Lam : ℝ, Lam = pgLamP w * U := ⟨_, rfl⟩
  rw [← hLam] at e1 hLamdef
  have hLam0 : 0 ≤ Lam := by rw [hLamdef]; positivity
  -- the argument of the series
  obtain ⟨lo, hi, hlo, -, hlo0, hlox, -, -⟩ := id hX
  obtain ⟨δ, hδ⟩ : ∃ δ : ℕ, δ = polyShift X.1 n L M := ⟨_, rfl⟩
  have hδle : δ ≤ 2 ^ L + 2 ^ L * n / (2 * M) + 1 := by rw [hδ]; exact polyShift_le _ _ _ _
  have hδge : ((2 ^ L + 2 ^ L * n / (2 * M) + 1 : ℕ) : ℝ) ≤ lo + (δ : ℕ) := by
    rw [hδ]
    exact polyShift_ge hlo hlo0.le _ _ _
  obtain ⟨hL1, hL2⟩ := two_pow_shiftExp (by omega : 4 ≤ w)
  rw [← hL] at hL1 hL2
  have hδΔ : (δ : ℝ) ≤ pgDelta n w := by
    have h1 : 2 ^ L * n / (2 * M) ≤ 2 ^ L * n := Nat.div_le_self _ _
    have h2 : 2 ^ L * n ≤ w / 2 * n := Nat.mul_le_mul_right n hL1
    have h3 : w / 2 * n ≤ w * n := Nat.mul_le_mul_right n (Nat.div_le_self _ _)
    have h4 : δ ≤ w * n + w := by omega
    have h5 : (δ : ℝ) ≤ (w : ℝ) * n + w := by exact_mod_cast h4
    unfold pgDelta
    linarith
  have hΔ0 : 0 ≤ pgDelta n w := by unfold pgDelta; positivity
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = xv + (δ : ℕ) := ⟨_, rfl⟩
  have hyge : (w : ℝ) / 4 + 1 ≤ y := by
    have h1 : w ≤ 4 * 2 ^ L := by omega
    have h2 : (w : ℝ) ≤ 4 * 2 ^ L := by exact_mod_cast h1
    have h3 : ((2 ^ L : ℕ) : ℝ) + 1 ≤ ((2 ^ L + 2 ^ L * n / (2 * M) + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_le_add_right (Nat.le_add_right (2 ^ L) (2 ^ L * n / (2 * M))) 1
    have h4 := h3.trans hδge
    push_cast at h4
    rw [hy]
    linarith only [h2, h4, hlox]
  have hy1 : 1 ≤ y := by linarith
  have hky : ∀ k : ℕ, k ≤ M → (k : ℝ) ≤ 27 / 10 * y := fun k hk => by
    have : (k : ℝ) ≤ M := by exact_mod_cast hk
    rw [hMr] at hMR
    unfold pgMr at hMR
    linarith
  have hterm : ∀ k, 1 ≤ k → k ≤ M → polyT n k y ≤ T := fun k hk hkM => by
    refine (polyT_le n hk hy1 (hky k hkM)).trans ?_
    have h9 : (9 / 10 : ℝ) ^ (2 * k - 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hbase : ((2 * k + n : ℕ) : ℝ) ≤ (w : ℝ) + 8 + n := by
      have : (k : ℝ) ≤ M := by exact_mod_cast hkM
      rw [hMr] at hMR
      unfold pgMr at hMR
      push_cast
      linarith
    have hp : ((2 * k + n : ℕ) : ℝ) ^ (n + 1) ≤ T := by
      rw [hT]
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) hbase _
    calc ((2 * k + n : ℕ) : ℝ) ^ (n + 1) * (9 / 10 : ℝ) ^ (2 * k - 1)
        ≤ ((2 * k + n : ℕ) : ℝ) ^ (n + 1) * 1 := mul_le_mul_of_nonneg_left h9 (by positivity)
      _ ≤ T := by rw [mul_one]; exact hp
  have htail : max ((1 / 2 : ℝ) ^ (w + 16)) (2 * polyT n M y) ≤ pgTail n w := by
    unfold pgTail
    rw [← hM]
    exact max_le_max le_rfl (by linarith [polyT_le n (by omega : 1 ≤ M) hy1 (hky M le_rfl)])
  -- the series at an enclosure of `y` of relative width `lam₀ + 6u`
  have hStir : ∀ Y : Encl, LEncl Y y (lam₀ + 6 * u) →
      AEncl (polyStirlingEncl V M n Y (powerOf2 (-(AzNat.ofNat (w + 16)).toAzInt)))
        ((-1) ^ (n + 1) * polygammaR n y) (pgWS n w) := by
    intro Y hY
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
        + max ((1 / 2 : ℝ) ^ (w + 16)) (2 * polyT n M y) + 2 * B * u ≤ pgEpsS n w := by
      unfold pgEpsS
      rw [← hMr, ← hT, ← hB, ← hU]
      have p1 : (M : ℝ) * (T * Lam) ≤ Mr * (T * Lam) := mul_le_mul_of_nonneg_right hMR hTL0
      have p2 : (M : ℝ) * (B * u) ≤ Mr * (B * U) := mul_le_mul hMR hBu (by positivity) hMr0
      have p3 : Mr * (T * Lam) = Mr * T * pgLamP w * U := by rw [hLam]; ring
      have p4 : Mr * (B * U) = Mr * B * U := by ring
      have p5 : (M : ℝ) * (2 * T * Lam + 4 * B * u) = 2 * (M * (T * Lam)) + 4 * (M * (B * u)) := by
        ring
      rw [p5]
      linarith only [p1, p2, p3, p4, htail, hBu]
    have hfac : (n ! : ℝ) * (lam₀ + 6 * u + 12 * u) ≤ (n ! : ℝ) * 26 * U := by
      have := mul_le_mul_of_nonneg_left
        (by linarith only [hlam, huU] : lam₀ + 6 * u + 12 * u ≤ 26 * U)
        (by linarith only [hfacn] : (0 : ℝ) ≤ (n ! : ℝ))
      linarith only [this]
    have hlamPb : (n : ℝ) * (lam₀ + 6 * u) + 24 * n * u ≤ 38 * n * U := by
      have h1 : (n : ℝ) * (lam₀ + 6 * u) ≤ n * (14 * U) :=
        mul_le_mul_of_nonneg_left (by linarith only [hlam, huU]) (by linarith only [hnR])
      have h2 : (n : ℝ) * u ≤ n * U := mul_le_mul_of_nonneg_left huU (by linarith only [hnR])
      linarith only [h1, h2]
    have hW := polyStirlingEncl_width hV (by omega : 1 ≤ M) hn hY (by positivity) hy1
      (toVal_lnGammaTol w) hT0 hterm (by rw [← hu]; exact hLamge) e1
      (by rw [← hu]; linarith only [hBu, e2]) hBge (by rw [← hu]; exact hεSge) e3
      hCdef.ge (by rw [← hu]; linarith only [hCu, e4]) (by rw [← hu]; linarith only [hfac, e5])
      (by rw [← hu]; linarith only [hlamPb, e6])
    rw [← hu] at hW
    refine hW.mono ?_
    unfold pgWS
    rw [← hC, ← hU]
    have q1 : C * (2 * ((n : ℝ) * (lam₀ + 6 * u) + 24 * n * u)) ≤ 2 * (C * (38 * n) * U) := by
      have := mul_le_mul_of_nonneg_left hlamPb hC0
      linarith only [this]
    linarith only [hfac, hCu, q1]
  -- the two cases of the shift
  unfold polygammaPosEncl
  simp only [← hL, ← hVdef]
  rw [show lnGammaTerms w (L + 1) = M by rw [hM, hL]; rfl, ← hδ]
  have hWS0 : pgWS n w ≤ pgE n xv w := by
    unfold pgE
    have a1 : 0 ≤ pgHs n xv w * pgLsh n w * U := by
      unfold pgHs pgLsh
      positivity
    have a2 : 0 ≤ pgBf n xv w * U := by
      unfold pgBf pgHs
      rw [← hC]
      positivity
    rw [← hU]
    linarith only [a1, a2]
  by_cases hδ0 : δ = 0
  · rw [ite_eq_left hδ0]
    have hyx : y = xv := by rw [hy, hδ0]; simp
    rw [hyx] at hStir
    exact ⟨_, (hStir X (hX.mono (by linarith only [hu0]))).mono hWS0⟩
  · rw [ite_eq_right hδ0]
    have hδ1 : 1 ≤ δ := Nat.one_le_iff_ne_zero.mpr hδ0
    have hδR : (0 : ℝ) ≤ (δ : ℝ) := Nat.cast_nonneg δ
    have hY : LEncl (Encl.add V X (Encl.nat δ)) (xv + (δ : ℕ)) (lam₀ + 6 * u) := by
      rw [hu]
      exact hX.add_exact (w := V) (b := Encl.nat δ) (by rw [← hu]; exact hu8) h0
        (toVal_ofAzNat_ofNat δ) (toVal_ofAzNat_ofNat δ) hδR
    rw [← hy] at hY
    have hS := hStir _ hY
    -- the shift sum
    have hSh := polyShiftSum_width (V := V) (by omega) h32 hX hδ1
    rw [← hu] at hSh
    have hfacL : LEncl (Encl.exact (ofAzNat (AzNat.factorial n))) (n ! : ℝ) 0 := by
      have := LEncl.exact (toVal_ofAzNat (AzNat.factorial n))
        (by rw [AzNat.toNat_factorial]; linarith only [hfacn])
      rwa [AzNat.toNat_factorial] at this
    have hlamsh : 0 + (((n + 1 : ℕ) : ℝ) * lam₀ + (80 * ((n + 1 : ℕ) : ℝ) + 6 * δ) * u) + 6 * u
        ≤ pgLsh n w * U := by
      unfold pgLsh
      push_cast
      have b1 : ((n : ℝ) + 1) * lam₀ ≤ ((n : ℝ) + 1) * (8 * U) :=
        mul_le_mul_of_nonneg_left hlam (by linarith only [hnR])
      have b2 : (80 * ((n : ℝ) + 1) + 6 * δ) * u ≤ (80 * ((n : ℝ) + 1) + 6 * pgDelta n w) * U :=
        mul_le_mul (by linarith only [hδΔ]) huU hu0.le (by linarith only [hΔ0, hnR])
      linarith only [b1, b2, huU]
    have hTm := (hfacL.mul (w := V) (by rw [← hu]; exact hu8) hSh)
    rw [← hu] at hTm
    have hTm' := hTm.mono hlamsh
    have hsum0 : 0 ≤ ∑ j ∈ range δ, 1 / (xv + (j : ℝ)) ^ (n + 1) :=
      sum_nonneg fun j _ => by
        have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        positivity
    have hHs : (n ! : ℝ) * ∑ j ∈ range δ, 1 / (xv + (j : ℝ)) ^ (n + 1) ≤ pgHs n xv w := by
      unfold pgHs
      have h1 := sum_inv_pow_le hxv (n + 1) δ
      have h2 : (δ : ℝ) * (1 / xv ^ (n + 1)) ≤ pgDelta n w * (1 / xv ^ (n + 1)) :=
        mul_le_mul_of_nonneg_right hδΔ (by positivity)
      have h3 := mul_le_mul_of_nonneg_left (h1.trans h2)
        (by linarith only [hfacn] : (0 : ℝ) ≤ (n ! : ℝ))
      rw [mul_div_assoc]
      rw [div_eq_mul_one_div (pgDelta n w)]
      exact h3
    have hLsh0 : 0 ≤ pgLsh n w * U := by
      unfold pgLsh
      positivity
    have hTmA := ((hTm'.toA hLsh0 e7).toA).mono
      (ε' := 2 * (pgHs n xv w * pgLsh n w * U)) (by
        have := mul_le_mul_of_nonneg_right hHs hLsh0
        linarith only [this])
    have hHy : |(-1) ^ (n + 1) * polygammaR n y| ≤ C := by
      have a := abs_polyH_le hn hy1
      have b := hterm 1 le_rfl (by omega)
      linarith only [a, b, hCdef]
    have hHs0 : 0 ≤ (n ! : ℝ) * ∑ j ∈ range δ, 1 / (xv + (j : ℝ)) ^ (n + 1) :=
      mul_nonneg (by linarith only [hfacn]) hsum0
    have hBf : pgBf n xv w = C + pgHs n xv w + 2 := by rw [hC]; rfl
    have hfin := hS.add (w := V) hTmA (B := pgBf n xv w) (by
      have h1 := abs_add_le ((-1) ^ (n + 1) * polygammaR n y)
        ((n ! : ℝ) * ∑ j ∈ range δ, 1 / (xv + (j : ℝ)) ^ (n + 1))
      rw [abs_of_nonneg hHs0] at h1
      rw [hBf]
      linarith only [h1, hHy, hHs, e9, e8])
    rw [← hu] at hfin
    have hBf0 : 0 ≤ pgBf n xv w := by
      rw [hBf]
      have : 0 ≤ pgHs n xv w := hHs0.trans hHs
      linarith only [this, hC0]
    have hBfu : pgBf n xv w * u ≤ pgBf n xv w * U := mul_le_mul_of_nonneg_left huU hBf0
    refine ⟨_, hfin.mono ?_⟩
    unfold pgE
    rw [← hU]
    linarith only [hBfu]

/-! ### Negative arguments, and the bracket -/

/-- An enclosure of `x > 0` of width `4 x u` has the relative width `8 u`. -/
theorem LEncl.of_abs4 {a : Encl} {x u : ℝ} (h : AEncl a x (4 * x * u)) (hx : 0 < x)
    (hu : u ≤ 1 / 8) : LEncl a x (8 * u) := by
  refine (LEncl.ofA h (by nlinarith) hx).mono (le_of_eq ?_)
  field_simp
  ring

theorem AEncl.natEncl (m : ℕ) : AEncl (Encl.nat m) (m : ℝ) 0 :=
  ⟨m, m, toVal_ofAzNat_ofNat m, toVal_ofAzNat_ofNat m, le_rfl, le_rfl, by simp⟩

open Nat in
/-- **The bracket of `(−1)ⁿ⁺¹ ψ⁽ⁿ⁾(x)` converges at a negative `x` that is not an integer.** -/
theorem polygammaNegEncl_conv {n : ℕ} (hn : 1 ≤ n) {x : AzFloat} {xv : ℝ}
    (hx : x.toVal = some (xv : EReal)) (hneg : xv < 0) (hni : ∀ k : ℤ, xv ≠ k) :
    ∃ E : ℕ → ℝ, Tendsto E atTop (𝓝 0) ∧ ∀ᶠ w in atTop, ∃ H : Encl,
      polygammaNegEncl n x w = some H ∧
      AEncl H ((-1) ^ (n + 1) * polygammaR n xv) (E w) := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = (truncToAzInt x).abs.toNat + 1 := ⟨_, rfl⟩
  -- `0 < x + m < 1`
  obtain ⟨ht, ht2⟩ := truncToAzInt_spec hx
  obtain ⟨t, htdef⟩ : ∃ t : ℤ, t = (truncToAzInt x).toInt := ⟨_, rfl⟩
  rw [← htdef] at ht ht2
  have ht' := abs_lt.mp ht
  have ht0 : t ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have : (1 : ℝ) ≤ t := by exact_mod_cast hpos
    linarith
  have htR : (t : ℝ) ≤ 0 := by exact_mod_cast ht0
  rw [abs_of_nonpos htR, abs_of_neg hneg] at ht2
  have hmR : (m : ℝ) = -(t : ℝ) + 1 := by
    have h1 := AzInt.abs_toNat_eq (truncToAzInt x)
    rw [← htdef, abs_of_nonpos ht0] at h1
    have h2 : (m : ℤ) = -t + 1 := by rw [hm]; push_cast; rw [h1]
    exact_mod_cast h2
  have hne : xv ≠ t := hni t
  have hxm0 : 0 < xv + m := by rw [hmR]; linarith
  have hxm1 : xv + m < 1 := by
    rw [hmR]
    have : xv - t ≠ 0 := sub_ne_zero.mpr hne
    have : xv - t < 0 := lt_of_le_of_ne (by linarith) this
    linarith
  have hm1 : 1 ≤ m := by omega
  obtain ⟨a₂, ha₂⟩ : ∃ a₂ : ℝ, a₂ = 1 - xv - m := ⟨_, rfl⟩
  have ha₂0 : 0 < a₂ := by rw [ha₂]; linarith
  -- the constants
  obtain ⟨Hc, hHc⟩ : ∃ Hc : ℝ,
      Hc = (n ! : ℝ) * ∑ j ∈ range m, 1 / (a₂ + (j : ℝ)) ^ (n + 1) := ⟨_, rfl⟩
  have hHc0 : 0 ≤ Hc := by
    rw [hHc]
    refine mul_nonneg (Nat.cast_nonneg _) (sum_nonneg fun j _ => ?_)
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    positivity
  obtain ⟨K₂, hK₂⟩ : ∃ K₂ : ℝ, K₂ = 88 * ((n : ℝ) + 1) + 6 * m + 6 := ⟨_, rfl⟩
  have hK₂0 : 0 ≤ K₂ := by rw [hK₂]; positivity
  obtain ⟨Bc, hBc⟩ : ∃ Bc : ℝ, Bc = |(-1) ^ (n + 1) * polygammaR n (xv + m)| + Hc + 2 :=
    ⟨_, rfl⟩
  have hBc0 : 0 ≤ Bc := by rw [hBc]; positivity
  have hpow : Tendsto (fun w : ℕ => (1 / 2 : ℝ) ^ w) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hKU : Tendsto (fun w : ℕ => K₂ * (1 / 2 : ℝ) ^ w) atTop (𝓝 0) := by
    simpa using hpow.const_mul K₂
  have hTw : Tendsto (fun w : ℕ => 2 * Hc * (K₂ * (1 / 2 : ℝ) ^ w)) atTop (𝓝 0) := by
    simpa using hKU.const_mul (2 * Hc)
  have hE : Tendsto (fun w : ℕ => pgE n (xv + m) w + 2 * Hc * (K₂ * (1 / 2 : ℝ) ^ w)
      + 4 * Bc * (1 / 2 : ℝ) ^ w) atTop (𝓝 0) := by
    simpa using ((tendsto_pgE n (xv + m)).add hTw).add (hpow.const_mul (4 * Bc))
  refine ⟨_, hE, ?_⟩
  filter_upwards [polygammaPosEncl_conv hn hxm0, eventually_ge_atTop (4 * m + 64),
    hKU.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    (tendsto_pgE n (xv + m)).eventually (ge_mem_nhds one_pos),
    hTw.eventually (ge_mem_nhds one_pos)] with w hpos hw e1 e2 e3
  have hw64 : 64 ≤ w := by omega
  suffices key : ∃ H : Encl, polygammaNegEncl n x w = some H ∧ ∃ v : ℝ, AEncl H v
      (pgE n (xv + m) w + 2 * Hc * (K₂ * (1 / 2 : ℝ) ^ w) + 4 * Bc * (1 / 2 : ℝ) ^ w) by
    obtain ⟨H, hH, v, hv⟩ := key
    exact ⟨H, hH, hv.of_isEncl (polygammaNegEncl_spec hn hx hni hw64 hH)⟩
  obtain ⟨U, hU⟩ : ∃ U : ℝ, U = (1 / 2 : ℝ) ^ w := ⟨_, rfl⟩
  rw [← hU] at e1 e3 ⊢
  have hU0 : 0 < U := by rw [hU]; positivity
  have : NeZero (w + 32) := ⟨by omega⟩
  obtain ⟨uW, huW⟩ : ∃ uW : ℝ, uW = (1 / 2 : ℝ) ^ (w + 32) := ⟨_, rfl⟩
  have huW0 : 0 < uW := by rw [huW]; positivity
  have huWU : uW ≤ U := by
    rw [huW, hU]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_right _ _)
  have huW8 : uW ≤ 1 / 8 := by rw [huW]; exact half_pow_le_eighth (by omega)
  obtain ⟨hV, h32⟩ := polyWork_bounds hn hw64
  obtain ⟨V, hVdef⟩ : ∃ V : ℕ, V = polyWork n w := ⟨_, rfl⟩
  rw [← hVdef] at hV h32
  have hVw : w ≤ V := by rw [hVdef]; unfold polyWork; omega
  have : NeZero V := ⟨by omega⟩
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (1 / 2 : ℝ) ^ V := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hu]; positivity
  have huU : u ≤ U := by
    rw [hu, hU]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hVw
  have hu8 : u ≤ 1 / 8 := by rw [hu]; exact half_pow_le_eighth (by omega)
  -- the two arguments
  have hUA := (AEncl.exact hx).add (w := w + 32) (AEncl.natEncl m) (B := xv + m)
    (by rw [abs_of_pos hxm0]; linarith only [])
  rw [← huW] at hUA
  have hUL := LEncl.of_abs4 (hUA.mono (le_of_eq (by ring))) hxm0 huW8
  have hA₂A := ((AEncl.natEncl (m - 1)).neg).sub (w := w + 32) (AEncl.exact hx) (B := a₂) (by
    rw [Nat.cast_sub hm1, Nat.cast_one,
      show -((m : ℝ) - 1) - xv = a₂ by rw [ha₂]; ring, abs_of_pos ha₂0]
    linarith only [])
  rw [Nat.cast_sub hm1, Nat.cast_one,
    show -((m : ℝ) - 1) - xv = a₂ by rw [ha₂]; ring, ← huW] at hA₂A
  have hA₂L := LEncl.of_abs4 (hA₂A.mono (le_of_eq (by ring))) ha₂0 huW8
  have c1 : lt zero (Encl.add (w + 32) (Encl.exact x) (Encl.nat m)).1 = true := by
    obtain ⟨l, h, hl, -, hl0, -⟩ := id hUL
    exact (lt_eq_true_iff toVal_zero' hl).mpr hl0
  have c2 : lt zero (Encl.sub (w + 32) (Encl.neg (Encl.nat (m - 1))) (Encl.exact x)).1
      = true := by
    obtain ⟨l, h, hl, -, hl0, -⟩ := id hA₂L
    exact (lt_eq_true_iff toVal_zero' hl).mpr hl0
  have hsmall : m ≤ 2 ^ lnGammaShiftExp w := by
    have := (two_pow_shiftExp (by omega : 4 ≤ w)).2
    omega
  -- the evaluation at `x + m`
  have hG := hpos _ _ hUL (by positivity) (by rw [← hU]; linarith only [huWU])
  -- the sum of the recurrence
  have hSh := polyShiftSum_width (V := V) (by omega) h32 hA₂L hm1
  rw [← hu] at hSh
  have hfacL : LEncl (Encl.exact (ofAzNat (AzNat.factorial n))) (n ! : ℝ) 0 := by
    have hpos' : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
    have := LEncl.exact (toVal_ofAzNat (AzNat.factorial n))
      (by rw [AzNat.toNat_factorial]; exact hpos')
    rwa [AzNat.toNat_factorial] at this
  have hlamT : 0 + (((n + 1 : ℕ) : ℝ) * (8 * uW) + (80 * ((n + 1 : ℕ) : ℝ) + 6 * m) * u) + 6 * u
      ≤ K₂ * U := by
    rw [hK₂]
    push_cast
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have b1 : ((n : ℝ) + 1) * (8 * uW) ≤ ((n : ℝ) + 1) * (8 * U) :=
      mul_le_mul_of_nonneg_left (by linarith only [huWU]) (by linarith only [hn0])
    have b2 : (80 * ((n : ℝ) + 1) + 6 * m) * u ≤ (80 * ((n : ℝ) + 1) + 6 * m) * U :=
      mul_le_mul_of_nonneg_left huU (by positivity)
    linarith only [b1, b2, huU]
  have hTm := hfacL.mul (w := V) (by rw [← hu]; exact hu8) hSh
  rw [← hu, ← hHc] at hTm
  have hTmA := ((hTm.mono hlamT).toA (by positivity) e1).toA
  have hBcu : Bc * uW ≤ Bc * U := mul_le_mul_of_nonneg_left huWU hBc0
  have habsG := abs_le.mp (le_refl |(-1) ^ (n + 1) * polygammaR n (xv + m)|)
  unfold polygammaNegEncl
  dsimp only
  rw [← hm, ← hVdef, ite_eq_left hsmall, ite_eq_left (by rw [c1, c2]; rfl)]
  by_cases ho : n % 2 = 1
  · rw [ite_eq_left ho]
    have hfin := hG.add (w := w + 32) hTmA (B := Bc) (by
      have h1 := abs_add_le ((-1) ^ (n + 1) * polygammaR n (xv + m)) Hc
      rw [abs_of_nonneg hHc0] at h1
      rw [hBc]
      linarith only [h1, e2, e3])
    rw [← huW] at hfin
    exact ⟨_, rfl, _, hfin.mono (by linarith only [hBcu])⟩
  · rw [ite_eq_right ho]
    have hfin := hG.sub (w := w + 32) hTmA (B := Bc) (by
      have h1 := abs_sub ((-1) ^ (n + 1) * polygammaR n (xv + m)) Hc
      rw [abs_of_nonneg hHc0] at h1
      rw [hBc]
      linarith only [h1, e2, e3])
    rw [← huW] at hfin
    exact ⟨_, rfl, _, hfin.mono (by linarith only [hBcu])⟩

open Nat in
/-- **The recurrence in positive terms converges**, for arguments given by enclosures: `Ue`
of `u = x + m ∈ (0, 1)` and `A₂e` of `1 − u`, of relative widths at most `8 · 2^(−w)`. -/
theorem polyNegCore_conv {n : ℕ} (hn : 1 ≤ n) {uv a₂ : ℝ} (hu0 : 0 < uv) (ha₂0 : 0 < a₂)
    {m : ℕ} (hm1 : 1 ≤ m) :
    ∃ E : ℕ → ℝ, Tendsto E atTop (𝓝 0) ∧ ∀ᶠ w in atTop, ∀ (Ue A₂e : Encl) (lu la : ℝ),
      LEncl Ue uv lu → 0 ≤ lu → lu ≤ 8 * (1 / 2 : ℝ) ^ w →
      LEncl A₂e a₂ la → 0 ≤ la → la ≤ 8 * (1 / 2 : ℝ) ^ w →
      ∃ v : ℝ, AEncl
        (if n % 2 = 1 then Encl.add (w + 32) (polygammaPosEncl n Ue w)
            (Encl.mul (polyWork n w) (Encl.exact (ofAzNat (AzNat.factorial n)))
              (polyShiftSum (polyWork n w) A₂e n m))
          else Encl.sub (w + 32) (polygammaPosEncl n Ue w)
            (Encl.mul (polyWork n w) (Encl.exact (ofAzNat (AzNat.factorial n)))
              (polyShiftSum (polyWork n w) A₂e n m))) v (E w) := by
  obtain ⟨Hc, hHc⟩ : ∃ Hc : ℝ,
      Hc = (n ! : ℝ) * ∑ j ∈ range m, 1 / (a₂ + (j : ℝ)) ^ (n + 1) := ⟨_, rfl⟩
  have hHc0 : 0 ≤ Hc := by
    rw [hHc]
    refine mul_nonneg (Nat.cast_nonneg _) (sum_nonneg fun j _ => ?_)
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    positivity
  obtain ⟨K₂, hK₂⟩ : ∃ K₂ : ℝ, K₂ = 88 * ((n : ℝ) + 1) + 6 * m + 6 := ⟨_, rfl⟩
  have hK₂0 : 0 ≤ K₂ := by rw [hK₂]; positivity
  obtain ⟨Bc, hBc⟩ : ∃ Bc : ℝ, Bc = |(-1) ^ (n + 1) * polygammaR n uv| + Hc + 2 := ⟨_, rfl⟩
  have hBc0 : 0 ≤ Bc := by rw [hBc]; positivity
  have hpow : Tendsto (fun w : ℕ => (1 / 2 : ℝ) ^ w) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hKU : Tendsto (fun w : ℕ => K₂ * (1 / 2 : ℝ) ^ w) atTop (𝓝 0) := by
    simpa using hpow.const_mul K₂
  have hTw : Tendsto (fun w : ℕ => 2 * Hc * (K₂ * (1 / 2 : ℝ) ^ w)) atTop (𝓝 0) := by
    simpa using hKU.const_mul (2 * Hc)
  have hE : Tendsto (fun w : ℕ => pgE n uv w + 2 * Hc * (K₂ * (1 / 2 : ℝ) ^ w)
      + 4 * Bc * (1 / 2 : ℝ) ^ w) atTop (𝓝 0) := by
    simpa using ((tendsto_pgE n uv).add hTw).add (hpow.const_mul (4 * Bc))
  refine ⟨_, hE, ?_⟩
  filter_upwards [polygammaPosEncl_conv hn hu0, eventually_ge_atTop 64,
    hKU.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    (tendsto_pgE n uv).eventually (ge_mem_nhds one_pos),
    hTw.eventually (ge_mem_nhds one_pos)] with w hpos hw64 e1 e2 e3
  intro Ue A₂e lu la hUL hlu0 hlu hA₂L hla0 hla
  obtain ⟨U, hU⟩ : ∃ U : ℝ, U = (1 / 2 : ℝ) ^ w := ⟨_, rfl⟩
  rw [← hU] at e1 e3 hlu hla ⊢
  have hU0 : 0 < U := by rw [hU]; positivity
  have : NeZero (w + 32) := ⟨by omega⟩
  obtain ⟨uW, huW⟩ : ∃ uW : ℝ, uW = (1 / 2 : ℝ) ^ (w + 32) := ⟨_, rfl⟩
  have huWU : uW ≤ U := by
    rw [huW, hU]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_right _ _)
  obtain ⟨hV, h32⟩ := polyWork_bounds hn hw64
  obtain ⟨V, hVdef⟩ : ∃ V : ℕ, V = polyWork n w := ⟨_, rfl⟩
  rw [← hVdef] at hV h32 ⊢
  have hVw : w ≤ V := by rw [hVdef]; unfold polyWork; omega
  have : NeZero V := ⟨by omega⟩
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (1 / 2 : ℝ) ^ V := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hu]; positivity
  have huU : u ≤ U := by
    rw [hu, hU]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hVw
  have hu8 : u ≤ 1 / 8 := by rw [hu]; exact half_pow_le_eighth (by omega)
  have hG := hpos _ _ hUL hlu0 (by rw [← hU]; exact hlu)
  have hSh := polyShiftSum_width (V := V) (by omega) h32 hA₂L hm1
  rw [← hu] at hSh
  have hfacL : LEncl (Encl.exact (ofAzNat (AzNat.factorial n))) (n ! : ℝ) 0 := by
    have hpos' : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
    have := LEncl.exact (toVal_ofAzNat (AzNat.factorial n))
      (by rw [AzNat.toNat_factorial]; exact hpos')
    rwa [AzNat.toNat_factorial] at this
  have hlamT : 0 + (((n + 1 : ℕ) : ℝ) * la + (80 * ((n + 1 : ℕ) : ℝ) + 6 * m) * u) + 6 * u
      ≤ K₂ * U := by
    rw [hK₂]
    push_cast
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have b1 : ((n : ℝ) + 1) * la ≤ ((n : ℝ) + 1) * (8 * U) :=
      mul_le_mul_of_nonneg_left hla (by linarith only [hn0])
    have b2 : (80 * ((n : ℝ) + 1) + 6 * m) * u ≤ (80 * ((n : ℝ) + 1) + 6 * m) * U :=
      mul_le_mul_of_nonneg_left huU (by positivity)
    linarith only [b1, b2, huU]
  have hTm := hfacL.mul (w := V) (by rw [← hu]; exact hu8) hSh
  rw [← hu, ← hHc] at hTm
  have hTmA := ((hTm.mono hlamT).toA (by positivity) e1).toA
  have hBcu : Bc * uW ≤ Bc * U := mul_le_mul_of_nonneg_left huWU hBc0
  by_cases ho : n % 2 = 1
  · rw [ite_eq_left ho]
    have hfin := hG.add (w := w + 32) hTmA (B := Bc) (by
      have h1 := abs_add_le ((-1) ^ (n + 1) * polygammaR n uv) Hc
      rw [abs_of_nonneg hHc0] at h1
      rw [hBc]
      linarith only [h1, e2, e3])
    rw [← huW] at hfin
    exact ⟨_, hfin.mono (by linarith only [hBcu])⟩
  · rw [ite_eq_right ho]
    have hfin := hG.sub (w := w + 32) hTmA (B := Bc) (by
      have h1 := abs_sub ((-1) ^ (n + 1) * polygammaR n uv) Hc
      rw [abs_of_nonneg hHc0] at h1
      rw [hBc]
      linarith only [h1, e2, e3])
    rw [← huW] at hfin
    exact ⟨_, hfin.mono (by linarith only [hBcu])⟩

/-- **The enclosure of `ψ⁽ⁿ⁾(x)` converges** at every finite `x` that is positive (`pos`) or
negative and not an integer. -/
theorem polygammaEncl_conv {n : ℕ} (hn : 1 ≤ n) {x : AzFloat} {xv : ℝ}
    (hx : x.toVal = some (xv : EReal)) {pos : Bool} (hpos : pos = true → 0 < xv)
    (hneg : pos = false → xv < 0 ∧ ∀ k : ℤ, xv ≠ k) :
    ∃ E : ℕ → ℝ, Tendsto E atTop (𝓝 0) ∧ ∀ᶠ w in atTop, ∃ En : Encl,
      polygammaEncl n x pos w = some En ∧ AEncl En (polygammaR n xv) (E w) := by
  have key : ∃ E : ℕ → ℝ, Tendsto E atTop (𝓝 0) ∧ ∀ᶠ w in atTop, ∃ H : Encl,
      (if pos = true then some (polygammaPosEncl n (Encl.exact x) w)
        else polygammaNegEncl n x w) = some H ∧
      AEncl H ((-1) ^ (n + 1) * polygammaR n xv) (E w) := by
    cases pos with
    | true =>
      refine ⟨pgE n xv, tendsto_pgE n xv, ?_⟩
      filter_upwards [polygammaPosEncl_conv hn (hpos rfl)] with w hw
      exact ⟨_, rfl, hw _ 0 (LEncl.exact hx (hpos rfl)) le_rfl (by positivity)⟩
    | false =>
      obtain ⟨h0, hni⟩ := hneg rfl
      obtain ⟨E, hE, hev⟩ := polygammaNegEncl_conv hn hx h0 hni
      exact ⟨E, hE, hev.mono fun w ⟨H, hH, hA⟩ => ⟨H, by simpa using hH, hA⟩⟩
  obtain ⟨E, hE, hev⟩ := key
  refine ⟨E, hE, ?_⟩
  filter_upwards [hev, eventually_ge_atTop 64] with w ⟨H, hH, hA⟩ hw
  have hsome : polygammaEncl n x pos w
      = some (if n % 2 = 1 then H else Encl.neg H) := by
    unfold polygammaEncl
    rw [hH]
    rfl
  refine ⟨_, hsome, ?_⟩
  have hspec := polygammaEncl_spec hn hx hpos (fun h => (hneg h).2) hw hsome
  by_cases ho : n % 2 = 1
  · rw [ite_eq_left ho] at hspec ⊢
    exact hA.of_isEncl hspec
  · rw [ite_eq_right ho] at hspec ⊢
    exact hA.neg.of_isEncl hspec

/-- A sequence that tends to `0` has a bound of its tails that tends to `0`. -/
theorem exists_tail_bound {E : ℕ → ℝ} (hE : Tendsto E atTop (𝓝 0)) :
    ∃ E' : ℕ → ℝ, Tendsto E' atTop (𝓝 0) ∧ ∀ w w', w ≤ w' → E w' ≤ E' w := by
  have hbdd := hE.bddAbove_range
  have hb : ∀ w, BddAbove (E '' Set.Ici w) := fun w => hbdd.mono (Set.image_subset_range _ _)
  refine ⟨fun w => sSup (E '' Set.Ici w), ?_, fun w w' h => le_csSup (hb w) ⟨w', h, rfl⟩⟩
  rw [tendsto_order]
  constructor
  · intro a ha
    filter_upwards [hE.eventually (lt_mem_nhds ha)] with w hw
    exact lt_of_lt_of_le hw (le_csSup (hb w) ⟨w, Set.mem_Ici.mpr le_rfl, rfl⟩)
  · intro a ha
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hE.eventually (gt_mem_nhds (half_pos ha)))
    filter_upwards [eventually_ge_atTop N] with w hw
    refine lt_of_le_of_lt (csSup_le ⟨E w, w, Set.mem_Ici.mpr le_rfl, rfl⟩ ?_) (half_lt_self ha)
    rintro _ ⟨w', hw', rfl⟩
    exact (hN w' (le_trans hw hw')).le

/-- **`enclRefine` of a convergent family converges**: its answer is the one of the level, or
of a higher one. -/
theorem enclRefine_conv {f : ℕ → Option Encl} {v : ℝ}
    (h : ∃ E : ℕ → ℝ, Tendsto E atTop (𝓝 0) ∧ ∀ᶠ w in atTop, ∃ En : Encl,
      f w = some En ∧ AEncl En v (E w)) (p : ℕ) :
    ∃ E' : ℕ → ℝ, Tendsto E' atTop (𝓝 0) ∧ ∀ᶠ w in atTop, ∃ En : Encl,
      enclRefine f p w = some En ∧ AEncl En v (E' w) := by
  obtain ⟨E, hE, hev⟩ := h
  obtain ⟨E', hE', hle⟩ := exists_tail_bound hE
  obtain ⟨W₀, hW₀⟩ := eventually_atTop.mp hev
  refine ⟨E', hE', eventually_atTop.mpr ⟨W₀, fun w hw => ?_⟩⟩
  obtain ⟨E₀, hf₀, hA₀⟩ := hW₀ w hw
  unfold enclRefine
  rw [hf₀]
  dsimp only
  cases hacc : enclAccuracy E₀ with
  | none => exact ⟨E₀, rfl, hA₀.mono (hle w w le_rfl)⟩
  | some r =>
    dsimp only
    split_ifs with hd
    · exact ⟨E₀, rfl, hA₀.mono (hle w w le_rfl)⟩
    · obtain ⟨E₁, hf₁, hA₁⟩ := hW₀ (w + (((p + 8 : ℕ) : ℤ) - r).toNat + 8) (by omega)
      exact ⟨E₁, hf₁, hA₁.mono (hle w _ (by omega))⟩

/-- **The bracket of `ψ⁽ⁿ⁾(x)` converges** at every finite `x` that is positive or negative
and not an integer. -/
theorem polygammaApprox_bracketConv {n : ℕ} (hn : 1 ≤ n) {x : AzFloat} {xv : ℝ}
    (hx : x.toVal = some (xv : EReal)) {pos : Bool} (hpos : pos = true → 0 < xv)
    (hneg : pos = false → xv < 0 ∧ ∀ k : ℤ, xv ≠ k) (p : ℕ) :
    BracketConv (fun w => lnAbsGammaApproxOf (polygammaEnclFor n x pos p w) w)
      (polygammaR n xv) :=
  lnAbsGammaApproxOf_bracketConv (enclRefine_conv (polygammaEncl_conv hn hx hpos hneg) p)

end Azurite.AzFloat
