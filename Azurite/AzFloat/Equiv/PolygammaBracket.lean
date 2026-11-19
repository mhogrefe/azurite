/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.PolygammaBracket
import Azurite.AzFloat.Equiv.DigammaBracket
import Azurite.AzFloat.Equiv.Beta
import Azurite.AzNat.Equiv.RisingFallingFactorial
import Azurite.AzNat.Equiv.Factorial
import Azurite.Transcendental.PolygammaStirling

/-!
# Equivalence: the bracket of the polygamma functions

`polygammaEncl_spec`: for `n ≥ 1` and `w ≥ 64`, an answer of `polygammaEncl n x pos w` encloses
`ψ⁽ⁿ⁾(x)` (`polygammaR n x`).  The steps: `polyTermEncl_spec`, `polySumLoop_spec`,
`polyStirlingEncl_spec`, `polyShiftSum_spec`, `polygammaPosEncl_spec`, `polygammaNegEncl_spec`.
-/

namespace Azurite.AzFloat

open Finset
open scoped Nat

theorem isEncl0_ofAzNat (a : AzNat) : IsEncl0 (Encl.exact (ofAzNat a)) (a.toNat : ℝ) :=
  ⟨_, _, toVal_ofAzNat _, toVal_ofAzNat _, Nat.cast_nonneg _, le_rfl, le_rfl⟩

/-! ### Powers by repeated squaring -/

theorem IsEnclPos.powBinAux {w : ℕ} [NeZero w] (hw : 2 ≤ w) {a : Encl} {x : ℝ}
    (ha : IsEnclPos a x) :
    ∀ fuel n : ℕ, n < 2 ^ fuel → IsEnclPos (Encl.powBinAux w a fuel n) (x ^ n)
  | 0, n, hn => by
    rw [pow_zero, Nat.lt_one_iff] at hn
    subst hn
    rw [Encl.powBinAux, pow_zero]
    exact enclosesPos_one
  | fuel + 1, n, hn => by
    rw [Encl.powBinAux]
    by_cases h0 : n = 0
    · rw [ite_eq_left h0, h0, pow_zero]
      exact enclosesPos_one
    rw [ite_eq_right h0]
    have hh := IsEnclPos.powBinAux hw ha fuel (n / 2) (by rw [pow_succ] at hn; omega)
    have hsq := hh.mul hw hh
    by_cases ho : n % 2 = 1
    · rw [ite_eq_left ho]
      have := hsq.mul hw ha
      convert this using 1
      conv_lhs => rw [← Nat.div_add_mod n 2, ho, pow_succ, pow_mul, pow_two]
      rw [mul_pow]
    · rw [ite_eq_right ho]
      convert hsq using 1
      conv_lhs => rw [← Nat.div_add_mod n 2, show n % 2 = 0 by omega, add_zero, pow_mul, pow_two]
      rw [mul_pow]

theorem IsEnclPos.powBin {w : ℕ} [NeZero w] (hw : 2 ≤ w) {a : Encl} {x : ℝ}
    (ha : IsEnclPos a x) (n : ℕ) : IsEnclPos (Encl.powBin w a n) (x ^ n) :=
  IsEnclPos.powBinAux hw ha _ n Nat.lt_log2_self

/-! ### The series for `x > 0` -/

/-- A term of the scaled series without its sign, `c_k (2k) ⋯ (2k+n−1) / y^(2k)`. -/
theorem polyTermEncl_spec {V : ℕ} [NeZero V] {M k : ℕ} (hk : 1 ≤ k) (hkM : k ≤ M) (n : ℕ)
    {p : Encl} {y : ℝ} (hp : IsEnclPos p (1 / y ^ (2 * k))) :
    IsEncl0 (polyTermEncl V (AzNat.tangentNumbers M) n k p)
      (psiCoeffT k * ((2 * k).ascFactorial n : ℝ) / y ^ (2 * k)) := by
  have hq : (AzNat.factorialQuotient (2 * k + n - 1) (2 * k - 1)).toNat
      = (2 * k).ascFactorial n := by
    rw [AzNat.toNat_factorialQuotient _ _ (by omega)]
    exact Nat.div_eq_of_eq_mul_right (Nat.factorial_pos _)
      (Nat.factorial_mul_ascFactorial' (2 * k) n (by omega)).symm
  have h := (psiTermEncl_spec (V := V) hk hkM hp).mul (w := V)
    (isEncl0_ofAzNat (AzNat.factorialQuotient (2 * k + n - 1) (2 * k - 1)))
  rw [hq] at h
  unfold polyTermEncl
  convert h using 1
  ring

/-- The loop encloses `polyNu n y` wherever it stops. -/
theorem polySumLoop_spec {V : ℕ} [NeZero V] (hV : 2 ≤ V) {M n : ℕ} (hn : 1 ≤ n) {inv2 : Encl}
    {y : ℝ} (hy : 0 < y) (hinv2 : IsEnclPos inv2 (1 / y ^ 2)) (tol : AzFloat) :
    ∀ (fuel k : ℕ) (p acc : Encl), 1 ≤ k → k + fuel ≤ M →
      IsEnclPos p (1 / y ^ (2 * k)) →
      IsEncl acc (∑ i ∈ range (k - 1), polyVTerm n (i + 1) y) →
      IsEncl (polySumLoop V (AzNat.tangentNumbers M) n inv2 tol fuel k p acc) (polyNu n y)
  | 0, k, p, acc, hk, hkM, hp, hacc => by
    obtain ⟨r, hν, hsign, habs⟩ := polyNu_eq_sum_add hn hk hy
    rw [polySumLoop]
    exact stirlingClose_spec hacc (polyTermEncl_spec hk (by omega) n hp) hν hsign habs
  | fuel + 1, k, p, acc, hk, hkM, hp, hacc => by
    have hτ := polyTermEncl_spec (V := V) hk (by omega : k ≤ M) n hp
    obtain ⟨r, hν, hsign, habs⟩ := polyNu_eq_sum_add hn hk hy
    have hclose := stirlingClose_spec (V := V) hacc hτ hν hsign habs
    rw [polySumLoop]
    split_ifs with hstop hodd hodd
    · rwa [ite_eq_left hodd] at hclose
    · rwa [ite_eq_right hodd] at hclose
    all_goals
      have hp' : IsEnclPos (Encl.mul V p inv2) (1 / y ^ (2 * (k + 1))) := by
        have := hp.mul hV hinv2
        convert this using 1
        rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add]
        field_simp
      have hsum : ∑ i ∈ range (k + 1 - 1), polyVTerm n (i + 1) y
          = ∑ i ∈ range (k - 1), polyVTerm n (i + 1) y + polyVTerm n k y := by
        rw [show k + 1 - 1 = (k - 1) + 1 by omega, sum_range_succ,
          show k - 1 + 1 = k by omega]
      refine polySumLoop_spec hV hn hy hinv2 tol fuel (k + 1) _ _ (by omega) (by omega) hp' ?_
      rw [hsum]
    · have : polyVTerm n k y = psiCoeffT k * ((2 * k).ascFactorial n : ℝ) / y ^ (2 * k) := by
        rw [polyVTerm, (Nat.even_iff.mpr (by omega : (k + 1) % 2 = 0)).neg_one_pow, one_mul]
      rw [this]
      exact hacc.add hτ.encloses
    · have : ∑ i ∈ range (k - 1), polyVTerm n (i + 1) y + polyVTerm n k y
          = ∑ i ∈ range (k - 1), polyVTerm n (i + 1) y
            - psiCoeffT k * ((2 * k).ascFactorial n : ℝ) / y ^ (2 * k) := by
        rw [polyVTerm, (Nat.odd_iff.mpr (by omega : (k + 1) % 2 = 1)).neg_one_pow]
        ring
      rw [this]
      exact hacc.sub hτ.encloses

/-- The asymptotic series on enclosures: `(−1)ⁿ⁺¹ ψ⁽ⁿ⁾(y)` for `y > 0`. -/
theorem polyStirlingEncl_spec {V : ℕ} (hV : 64 ≤ V) {M : ℕ} (hM : 1 ≤ M) {n : ℕ} (hn : 1 ≤ n)
    {Y : Encl} {y : ℝ} (hY : IsEnclPos Y y) (tol : AzFloat) :
    IsEncl (polyStirlingEncl V M n Y tol) ((-1) ^ (n + 1) * polygammaR n y) := by
  have : NeZero V := ⟨by omega⟩
  have hV2 : 2 ≤ V := by omega
  have hy : 0 < y := by obtain ⟨l, h, -, -, h0, h1, -⟩ := hY; linarith
  have hinv : IsEnclPos (Encl.div V (Encl.exact one) Y) (1 / y) := enclosesPos_one.div hV2 hY
  have hinv2 : IsEnclPos (Encl.mul V (Encl.div V (Encl.exact one) Y)
      (Encl.div V (Encl.exact one) Y)) (1 / y ^ 2) := by
    have := hinv.mul hV2 hinv
    convert this using 1
    field_simp
  have hS := polySumLoop_spec hV2 (M := M) hn hy hinv2 tol (M - 1) 1 _ _ le_rfl (by omega)
    (by simpa using hinv2) (by simpa using isEncl0_exact_zero)
  have hlead := (isEncl0_ofAzNat (AzNat.factorial (n - 1))).encloses.add (w := V)
    (((isEncl0_ofAzNat (AzNat.factorial n)).mul (w := V) hinv.encloses0).encloses.half)
  rw [AzNat.toNat_factorial, AzNat.toNat_factorial] at hlead
  have := (hlead.add (w := V) hS).mulPos (W := V) ((hinv.powBin hV2 n).encloses0)
  unfold polyStirlingEncl
  convert this using 1
  have hyn : y ^ n ≠ 0 := (pow_pos hy n).ne'
  have e : ((n - 1)! : ℝ) + (n ! : ℝ) * (1 / y) / 2 + polyNu n y
      = y ^ n * ((-1) ^ (n + 1) * polygammaR n y) := by
    rw [polyNu]
    field_simp
    ring
  rw [e, one_div, inv_pow]
  field_simp

/-! #### The shift sum: every term once, rounded down -/

/-- `powUpAux` is an upper bound of the power within `(1 + ε)^(2^(fuel+1) − 2)`. -/
theorem powUpAux_spec {V : ℕ} [NeZero V] {y : AzFloat} {yv : ℝ}
    (hy : y.toVal = some (yv : EReal)) (hy0 : 0 < yv) :
    ∀ fuel n : ℕ, n < 2 ^ fuel → ∃ P : ℝ, (powUpAux V y fuel n).toVal = some (P : EReal) ∧
      yv ^ n ≤ P ∧ P ≤ yv ^ n * (1 + 2 * (1 / 2 : ℝ) ^ V) ^ (2 ^ (fuel + 1) - 2)
  | 0, n, hn => by
    rw [pow_zero, Nat.lt_one_iff] at hn
    subst hn
    exact ⟨1, toVal_one', by simp, by simp⟩
  | fuel + 1, n, hn => by
    set e := 1 + 2 * (1 / 2 : ℝ) ^ V with he
    have he1 : 1 ≤ e := by rw [he]; have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ V := by positivity
                           linarith
    have he0 : 0 < e := by linarith
    rw [powUpAux]
    by_cases h0 : n = 0
    · rw [ite_eq_left h0, h0]
      exact ⟨1, toVal_one', by simp, by rw [pow_zero, one_mul]; exact one_le_pow₀ he1⟩
    rw [ite_eq_right h0]
    obtain ⟨h, hh, h1, h2⟩ :=
      powUpAux_spec (V := V) hy hy0 fuel (n / 2) (by rw [pow_succ] at hn; omega)
    set A := yv ^ (n / 2) with hA
    set g := 2 ^ (fuel + 1) - 2 with hg
    have hA0 : 0 < A := pow_pos hy0 _
    have hh0 : 0 < h := lt_of_lt_of_le hA0 h1
    have hgg : 2 ^ (fuel + 1 + 1) - 2 = 2 * g + 2 := by
      have e1 : 2 ^ (fuel + 1 + 1) = 2 * 2 ^ (fuel + 1) := by ring
      have e2 : 2 ≤ 2 ^ (fuel + 1) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (fuel + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    obtain ⟨s, hs, hs1, hs2⟩ := mulCeiling_abs hh hh V
    rw [abs_of_pos (mul_pos hh0 hh0)] at hs2
    have hsq_lo : A * A ≤ s := le_trans (mul_le_mul h1 h1 hA0.le hh0.le) hs1
    have hsq_hi : s ≤ A * A * e ^ (2 * g + 1) := by
      have hG : (0 : ℝ) < e ^ g := pow_pos he0 g
      have h2' : h * h ≤ (A * e ^ g) * (A * e ^ g) :=
        mul_le_mul h2 h2 hh0.le (mul_pos hA0 hG).le
      calc s ≤ h * h * e := by rw [he]; linarith
        _ ≤ (A * e ^ g) * (A * e ^ g) * e := mul_le_mul_of_nonneg_right h2' he0.le
        _ = A * A * e ^ (2 * g + 1) := by rw [pow_succ, two_mul, pow_add]; ring
    have hs0 : 0 < s := lt_of_lt_of_le (mul_pos hA0 hA0) hsq_lo
    rw [hgg]
    by_cases ho : n % 2 = 1
    · rw [ite_eq_left ho]
      obtain ⟨P, hP, hP1, hP2⟩ := mulCeiling_abs hs hy V
      rw [abs_of_pos (mul_pos hs0 hy0)] at hP2
      have hn' : yv ^ n = A * A * yv := by
        conv_lhs => rw [← Nat.div_add_mod n 2, ho, pow_succ, pow_mul, pow_two]
        rw [mul_pow]
      refine ⟨P, hP, ?_, ?_⟩
      · rw [hn']
        exact le_trans (mul_le_mul_of_nonneg_right hsq_lo hy0.le) hP1
      · rw [hn']
        calc P ≤ s * yv * e := by rw [he]; linarith
          _ ≤ A * A * e ^ (2 * g + 1) * yv * e :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsq_hi hy0.le) he0.le
          _ = A * A * yv * e ^ (2 * g + 2) := by rw [pow_succ e (2 * g + 1)]; ring
    · rw [ite_eq_right ho]
      have hn' : yv ^ n = A * A := by
        conv_lhs => rw [← Nat.div_add_mod n 2, show n % 2 = 0 by omega, add_zero, pow_mul,
          pow_two]
        rw [mul_pow]
      refine ⟨s, hs, by rw [hn']; exact hsq_lo, ?_⟩
      rw [hn']
      exact hsq_hi.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ he1 (by omega)) (mul_pos hA0 hA0).le)

/-- `powUp V y n` is an upper bound of `yⁿ` within `(1 + ε)^(4n)`, `n ≥ 1`. -/
theorem powUp_spec {V : ℕ} [NeZero V] {y : AzFloat} {yv : ℝ}
    (hy : y.toVal = some (yv : EReal)) (hy0 : 0 < yv) {n : ℕ} (hn : 1 ≤ n) :
    ∃ P : ℝ, (powUp V y n).toVal = some (P : EReal) ∧ yv ^ n ≤ P ∧
      P ≤ yv ^ n * (1 + 2 * (1 / 2 : ℝ) ^ V) ^ (4 * n) := by
  obtain ⟨P, hP, h1, h2⟩ := powUpAux_spec (V := V) hy hy0 (n.log2 + 1) n Nat.lt_log2_self
  refine ⟨P, hP, h1, h2.trans (mul_le_mul_of_nonneg_left ?_ (pow_pos hy0 n).le)⟩
  have he1 : (1 : ℝ) ≤ 1 + 2 * (1 / 2 : ℝ) ^ V := by
    have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ V := by positivity
    linarith
  refine pow_le_pow_right₀ he1 ?_
  have hlog : 2 ^ n.log2 ≤ n := Nat.log2_self_le (by omega)
  have e1 : 2 ^ (n.log2 + 1 + 1) = 4 * 2 ^ n.log2 := by ring
  omega

section ShiftSum

variable {a b x E : ℝ}

/-- A single term `1/(x + j)^k` from one quotient rounded down. -/
theorem poly_single (ha : 0 < a) (hax : a ≤ x) (hxb : x ≤ b) (hE0 : 0 ≤ E) (hE1 : E ≤ 1 / 64)
    {j y P q : ℝ} (hj : 0 ≤ j) (hy1 : b + j ≤ y) (hy2 : y ≤ (b + j) * (1 + E)) (k : ℕ)
    (hP1 : y ^ k ≤ P) (hP2 : P ≤ y ^ k * (1 + E) ^ (4 * k)) (hq1 : q ≤ 1 / P)
    (hq2 : 1 / P * (1 - E) ≤ q) :
    q ≤ 1 / (x + j) ^ k ∧
      1 / (x + j) ^ k ≤ (b / a) ^ k * ((1 + E) ^ (5 * k) / (1 - E)) * q := by
  have hb : 0 < b := by linarith
  have hX : 0 < x + j := by linarith
  have hy : 0 < y := by linarith
  have hE : 0 < 1 - E := by linarith
  have he : 0 < 1 + E := by linarith
  have hXk : 0 < (x + j) ^ k := pow_pos hX k
  have hyk : (x + j) ^ k ≤ y ^ k := pow_le_pow_left₀ hX.le (by linarith) k
  have hP0 : 0 < P := lt_of_lt_of_le (pow_pos hy k) hP1
  have hba : 0 < b / a := div_pos hb ha
  constructor
  · exact hq1.trans (one_div_le_one_div_of_le hXk (hyk.trans hP1))
  · -- `y ≤ (b/a)(1 + E)(x + j)`
    have hbj : b + j ≤ b / a * (x + j) := by
      have h1 : b / a * (x + j) = b / a * x + b / a * j := by ring
      have h2 : b ≤ b / a * x := by
        rw [div_mul_eq_mul_div, le_div_iff₀ ha]
        nlinarith
      have h3 : j ≤ b / a * j := by
        have : 1 ≤ b / a := by rw [le_div_iff₀ ha]; linarith
        nlinarith
      linarith
    have hyle : y ≤ b / a * (1 + E) * (x + j) := by
      calc y ≤ (b + j) * (1 + E) := hy2
        _ ≤ b / a * (x + j) * (1 + E) := mul_le_mul_of_nonneg_right hbj he.le
        _ = b / a * (1 + E) * (x + j) := by ring
    have hyk2 : y ^ k ≤ (b / a) ^ k * (1 + E) ^ k * (x + j) ^ k := by
      have := pow_le_pow_left₀ hy.le hyle k
      rwa [mul_pow, mul_pow] at this
    set C := (b / a) ^ k * (1 + E) ^ (5 * k) with hC
    have hC0 : 0 < C := by positivity
    have hPC : P ≤ C * (x + j) ^ k := by
      calc P ≤ y ^ k * (1 + E) ^ (4 * k) := hP2
        _ ≤ (b / a) ^ k * (1 + E) ^ k * (x + j) ^ k * (1 + E) ^ (4 * k) :=
            mul_le_mul_of_nonneg_right hyk2 (by positivity)
        _ = C * (x + j) ^ k := by
            rw [hC, show 5 * k = k + 4 * k by ring, pow_add]; ring
    have h1 : 1 / (x + j) ^ k ≤ C * (1 / P) := by
      rw [mul_one_div, div_le_div_iff₀ hXk hP0]
      linarith
    have h2 : 1 / P ≤ q / (1 - E) := by
      rw [le_div_iff₀ hE]; exact hq2
    calc 1 / (x + j) ^ k ≤ C * (1 / P) := h1
      _ ≤ C * (q / (1 - E)) := mul_le_mul_of_nonneg_left h2 hC0.le
      _ = (b / a) ^ k * ((1 + E) ^ (5 * k) / (1 - E)) * q := by rw [hC]; ring

end ShiftSum

/-- `(1 + E)^(5k) / (1 − E) ≤ 1 + 2 (5k + 1) E` when `(5k + 1) E ≤ 1/2`. -/
theorem shift_factor_le {E : ℝ} (hE0 : 0 ≤ E) (k : ℕ) (hc : ((5 * k + 1 : ℕ) : ℝ) * E ≤ 1 / 2) :
    (1 + E) ^ (5 * k) / (1 - E) ≤ 1 + 2 * ((5 * k + 1 : ℕ) : ℝ) * E := by
  set c := 5 * k + 1 with hcdef
  have hc1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast (by omega : 1 ≤ c)
  have hE1 : E ≤ 1 / 2 := by nlinarith
  have hE : 0 < 1 - E := by linarith
  have hinv : 1 + E ≤ (1 - E)⁻¹ := by
    rw [le_inv_comm₀ (by linarith) hE]
    rw [inv_eq_one_div, le_div_iff₀ (by linarith)]
    nlinarith
  have h1 : (1 + E) ^ (5 * k) / (1 - E) ≤ ((1 - E)⁻¹) ^ c := by
    rw [hcdef, pow_succ, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) hinv _)
      (inv_nonneg.mpr hE.le)
  have hbern : 1 - (c : ℝ) * E ≤ (1 - E) ^ c := by
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ -E by linarith) c
    simpa [sub_eq_add_neg] using this
  have hpos : 0 < 1 - (c : ℝ) * E := by linarith
  have h2 : ((1 - E)⁻¹) ^ c ≤ (1 - (c : ℝ) * E)⁻¹ := by
    rw [inv_pow]
    exact inv_anti₀ hpos hbern
  have h3 : (1 - (c : ℝ) * E)⁻¹ ≤ 1 + 2 * (c : ℝ) * E := by
    have ht0 : 0 ≤ (c : ℝ) * E := mul_nonneg (by linarith) hE0
    rw [inv_le_iff_one_le_mul₀ hpos]
    nlinarith [mul_nonneg ht0 (by linarith : (0 : ℝ) ≤ 1 - 2 * ((c : ℝ) * E))]
  exact h1.trans (h2.trans h3)

/-- The loop: the lower sum is below the terms, and the terms are below the factor times the
upper sum. -/
theorem polyShiftLoop_spec {V : ℕ} [NeZero V] (hV : 8 ≤ V) {bF : AzFloat} {a b xv : ℝ}
    (hb : bF.toVal = some (b : EReal)) (ha : 0 < a) (hax : a ≤ xv) (hxb : xv ≤ b) {k : ℕ}
    (hk : 1 ≤ k) :
    ∀ (m i : ℕ) (lo up : AzFloat) (lov upv A : ℝ), lo.toVal = some (lov : EReal) →
      up.toVal = some (upv : EReal) → 0 ≤ lov → lov ≤ A →
      A ≤ (b / a) ^ k * ((1 + 2 * (1 / 2 : ℝ) ^ V) ^ (5 * k) / (1 - 2 * (1 / 2 : ℝ) ^ V)) * upv →
      0 ≤ upv →
      ∃ lo' up' : ℝ, (polyShiftLoop V bF k m i lo up).1.toVal = some (lo' : EReal) ∧
        (polyShiftLoop V bF k m i lo up).2.toVal = some (up' : EReal) ∧ 0 ≤ lo' ∧
        lo' ≤ A + ∑ j ∈ range m, 1 / (xv + ((i + j : ℕ) : ℝ)) ^ k ∧
        A + ∑ j ∈ range m, 1 / (xv + ((i + j : ℕ) : ℝ)) ^ k
          ≤ (b / a) ^ k * ((1 + 2 * (1 / 2 : ℝ) ^ V) ^ (5 * k) / (1 - 2 * (1 / 2 : ℝ) ^ V))
            * up' ∧
        0 ≤ up'
  | 0, i, lo, up, lov, upv, A, hlo, hup, h0, h1, h2, h3 => by
    rw [polyShiftLoop, sum_range_zero, add_zero]
    exact ⟨lov, upv, hlo, hup, h0, h1, h2, h3⟩
  | m + 1, i, lo, up, lov, upv, A, hlo, hup, h0, h1, h2, h3 => by
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
    obtain ⟨P, hP, hP1, hP2⟩ := powUp_spec (V := V) hy hy0 hk
    have hP0 : 0 < P := lt_of_lt_of_le (pow_pos hy0 k) hP1
    obtain ⟨q, hq, hq1, hq2⟩ := divFloor_abs toVal_one' hP hP0.ne' V
    rw [abs_of_pos (by positivity)] at hq2
    obtain ⟨hA, hB⟩ := poly_single ha hax hxb hE0 hE1 hi0 hy1 (by rw [hEdef]; linarith) k
      hP1 (by rw [hEdef]; exact hP2) hq1 (by rw [hEdef]; linarith)
    have hq0 : 0 ≤ q := by
      have : 0 ≤ 1 / P * (1 - E) := mul_nonneg (by positivity) (by linarith)
      rw [hEdef] at this; linarith
    obtain ⟨lo', hlo', hlo'1, hlo'2⟩ := addFloor_abs hlo hq V
    rw [abs_of_nonneg (by linarith)] at hlo'2
    obtain ⟨up', hup', hup'1, -⟩ := addCeiling_abs hup hq V
    have hK : 0 ≤ (b / a) ^ k * ((1 + E) ^ (5 * k) / (1 - E)) := by
      have : 0 < 1 - E := by linarith
      positivity
    have hlo'0 : 0 ≤ lo' := by
      have : (lov + q) * (1 - E) ≤ lo' := by rw [hEdef]; linarith
      exact le_trans (mul_nonneg (by linarith) (by linarith)) this
    obtain ⟨lo'', up'', e1, e2, e3, e4, e5, e6⟩ :=
      polyShiftLoop_spec hV hb ha hax hxb hk m (i + 1) _ _ lo' up' (A + 1 / (xv + (i : ℝ)) ^ k)
        hlo' hup' hlo'0 (by linarith)
        (by
          calc A + 1 / (xv + (i : ℝ)) ^ k
              ≤ (b / a) ^ k * ((1 + E) ^ (5 * k) / (1 - E)) * upv
                + (b / a) ^ k * ((1 + E) ^ (5 * k) / (1 - E)) * q := add_le_add h2 hB
            _ = (b / a) ^ k * ((1 + E) ^ (5 * k) / (1 - E)) * (upv + q) := by ring
            _ ≤ (b / a) ^ k * ((1 + E) ^ (5 * k) / (1 - E)) * up' :=
                mul_le_mul_of_nonneg_left hup'1 hK)
        (by linarith)
    have hsum : ∑ j ∈ range (m + 1), 1 / (xv + ((i + j : ℕ) : ℝ)) ^ k
        = 1 / (xv + (i : ℝ)) ^ k + ∑ j ∈ range m, 1 / (xv + ((i + 1 + j : ℕ) : ℝ)) ^ k := by
      rw [sum_range_succ', Nat.add_zero, add_comm]
      congr 1
      refine sum_congr rfl fun j _ => ?_
      rw [show i + (j + 1) = i + 1 + j by omega]
    rw [polyShiftLoop, hsum, ← add_assoc]
    exact ⟨lo'', up'', e1, e2, e3, e4, e5, e6⟩

/-- **The shift sum**: `polyShiftSum V X n i` encloses `∑_{j<i} (x + j)^{−n−1}`. -/
theorem polyShiftSum_spec {V : ℕ} [NeZero V] (hV : 8 ≤ V) {n : ℕ} (h32 : 32 * (n + 1) ≤ 2 ^ V)
    {X : Encl} {xv : ℝ} (hX : IsEnclPos X xv) (i : ℕ) :
    IsEncl0 (polyShiftSum V X n i) (∑ j ∈ range i, 1 / (xv + j) ^ (n + 1)) := by
  obtain ⟨a, b, ha, hb, ha0, hax, hxb⟩ := hX
  set k := n + 1 with hk
  set E := 2 * (1 / 2 : ℝ) ^ V with hEdef
  have hE0 : 0 ≤ E := by positivity
  have hE1 : E ≤ 1 / 64 := by
    have : (1 / 2 : ℝ) ^ V ≤ (1 / 2) ^ 8 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hV
    rw [hEdef]; norm_num at this ⊢; linarith
  have hb0 : 0 < b := by linarith
  obtain ⟨lo, up, hlo, hup, hlo0, h1, h2, h3⟩ := polyShiftLoop_spec hV hb ha0 hax hxb
    (k := k) (by omega) i 0 zero zero 0 0 0 toVal_zero' toVal_zero' le_rfl le_rfl
    (by rw [mul_zero]) le_rfl
  simp only [zero_add] at h1 h2
  -- the factor
  obtain ⟨R, hR, hR1, -⟩ := divCeiling_abs hb ha ha0.ne' V
  have hR0 : 0 < R := lt_of_lt_of_le (div_pos hb0 ha0) hR1
  obtain ⟨Pk, hPk, hPk1, -⟩ := powUp_spec (V := V) hR hR0 (n := k) (by omega)
  set cb := (32 * k).log2 + 1 with hcb
  have hpow : (powerOf2 (AzInt.ofInt ((cb : ℕ) : ℤ) - (AzNat.ofNat V).toAzInt)).toVal
      = some ((((2 : ℝ) ^ cb) * (1 / 2 : ℝ) ^ V : ℝ) : EReal) := by
    rw [toVal_powerOf2, AzInt.toInt_sub, AzInt.toInt_ofInt, AzNat.toInt_toAzInt,
      AzNat.toNat_ofNat, zpow_sub₀ (by norm_num), zpow_natCast, zpow_natCast, one_div_pow,
      one_div, div_eq_mul_inv]
  obtain ⟨o, ho, ho1, -⟩ := addCeiling_abs toVal_one' hpow V
  obtain ⟨K, hK, hK1, -⟩ := mulCeiling_abs hPk ho V
  -- `(1 + E)^(5k)/(1 − E) ≤ o`
  have h2V : ((2 : ℝ) ^ V) * (1 / 2 : ℝ) ^ V = 1 := by rw [← mul_pow]; norm_num
  have hhalf : (0 : ℝ) < (1 / 2 : ℝ) ^ V := by positivity
  have h32r : (32 : ℝ) * k ≤ 2 ^ V := by exact_mod_cast h32
  have hk1 : (1 : ℝ) ≤ k := by rw [hk]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hcE : ((5 * k + 1 : ℕ) : ℝ) * E ≤ 1 / 2 := by
    rw [hEdef]
    push_cast
    have : (5 * (k : ℝ) + 1) * 4 ≤ 2 ^ V := by linarith
    nlinarith
  have hfac := shift_factor_le hE0 k hcE
  have hcbr : (32 : ℝ) * k ≤ 2 ^ cb := by
    have : 32 * k < 2 ^ cb := Nat.lt_log2_self
    exact_mod_cast this.le
  have hG : (1 + E) ^ (5 * k) / (1 - E) ≤ o := by
    refine hfac.trans (le_trans ?_ ho1)
    rw [hEdef]
    push_cast
    have : 2 * (5 * (k : ℝ) + 1) * 2 ≤ 2 ^ cb := by linarith
    nlinarith
  have hG0 : 0 ≤ (1 + E) ^ (5 * k) / (1 - E) := by
    have : 0 < 1 - E := by linarith
    positivity
  have hba : (b / a) ^ k ≤ Pk :=
    le_trans (pow_le_pow_left₀ (div_pos hb0 ha0).le hR1 k) hPk1
  have hKge : (b / a) ^ k * ((1 + E) ^ (5 * k) / (1 - E)) ≤ K :=
    le_trans (mul_le_mul hba hG hG0 (le_trans (by positivity) hba)) hK1
  obtain ⟨hi, hhi, hhi1, -⟩ := mulCeiling_abs hup hK V
  unfold polyShiftSum
  refine ⟨lo, hi, hlo, hhi, hlo0, h1, ?_⟩
  calc ∑ j ∈ range i, 1 / (xv + (j : ℝ)) ^ k
      ≤ (b / a) ^ k * ((1 + E) ^ (5 * k) / (1 - E)) * up := h2
    _ ≤ K * up := mul_le_mul_of_nonneg_right hKge h3
    _ = up * K := mul_comm _ _
    _ ≤ hi := hhi1

theorem polyWork_bounds {n : ℕ} (hn : 1 ≤ n) {w : ℕ} (hw : 64 ≤ w) :
    64 ≤ polyWork n w ∧ 32 * (n + 1) ≤ 2 ^ polyWork n w := by
  unfold polyWork
  refine ⟨by omega, ?_⟩
  have h1 : n < 2 ^ (n.log2 + 1) := Nat.lt_log2_self
  have h2 : 2 ^ (n.log2 + 7) ≤ 2 ^ (w + 2 * lnGammaShiftExp w + 16 + 2 * w.log2 + 2 * n.log2) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have e : 2 ^ (n.log2 + 7) = 64 * 2 ^ (n.log2 + 1) := by ring
  omega

/-- **`polygammaPosEncl n X w` encloses `(−1)ⁿ⁺¹ ψ⁽ⁿ⁾(x)`** for an enclosure `X` of `x` with a
positive lower end (`n ≥ 1`, `w ≥ 64`). -/
theorem polygammaPosEncl_spec {n : ℕ} (hn : 1 ≤ n) {X : Encl} {xv : ℝ} (hX : IsEnclPos X xv)
    {w : ℕ} (hw : 64 ≤ w) :
    IsEncl (polygammaPosEncl n X w) ((-1) ^ (n + 1) * polygammaR n xv) := by
  set L := lnGammaShiftExp w with hL
  obtain ⟨hV, h32⟩ := polyWork_bounds hn hw
  set V := polyWork n w with hVdef
  have : NeZero V := ⟨by omega⟩
  have hV2 : 2 ≤ V := by omega
  have hpos : 0 < xv := by obtain ⟨l, h, -, -, h0, h1, -⟩ := hX; linarith
  have hM : 1 ≤ lnGammaTerms w (L + 1) := by
    unfold lnGammaTerms; exact le_trans (by norm_num) (Nat.le_add_left 3 _)
  unfold polygammaPosEncl
  simp only [← hL, ← hVdef]
  set δ := polyShift X.1 n L (lnGammaTerms w (L + 1))
  by_cases hδ : δ = 0
  · rw [ite_eq_left hδ]
    exact polyStirlingEncl_spec hV hM hn hX _
  · rw [ite_eq_right hδ]
    have hY : IsEnclPos (Encl.add V X (Encl.nat δ)) (xv + (δ : ℕ)) := hX.add hV2 (isEncl0_nat _)
    have hS := polyStirlingEncl_spec hV hM hn hY (powerOf2 (-(AzNat.ofNat (w + 16)).toAzInt))
    have hT := ((isEncl0_ofAzNat (AzNat.factorial n)).mul (w := V)
      (polyShiftSum_spec (by omega) h32 hX δ)).encloses
    rw [AzNat.toNat_factorial] at hT
    have := hS.add (w := V) hT
    convert this using 1
    have hnp : ∀ m : ℕ, xv ≠ -m := fun m hm => by
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    have hs : ((-1 : ℝ) ^ (n + 1)) * (-1) ^ (n + 1) = 1 := by rw [← mul_pow]; norm_num
    rw [polygammaR_add_nat hn hnp δ]
    linear_combination ((n ! : ℝ) * ∑ j ∈ range δ, 1 / (xv + j) ^ (n + 1)) * hs

/-! ### Negative arguments -/

/-- **`polygammaNegEncl n x w` encloses `(−1)ⁿ⁺¹ ψ⁽ⁿ⁾(x)`** for a finite `x` that is not an
integer. -/
theorem polygammaNegEncl_spec {n : ℕ} (hn : 1 ≤ n) {x : AzFloat} {xv : ℝ}
    (hx : x.toVal = some (xv : EReal)) (hni : ∀ k : ℤ, xv ≠ k) {w : ℕ} (hw : 64 ≤ w) {H : Encl}
    (h : polygammaNegEncl n x w = some H) :
    IsEncl H ((-1) ^ (n + 1) * polygammaR n xv) := by
  unfold polygammaNegEncl at h
  dsimp only at h
  set m := (truncToAzInt x).abs.toNat + 1 with hm
  have : NeZero (w + 32) := ⟨by omega⟩
  have hX : IsEncl (Encl.exact x) xv := ⟨xv, xv, hx, hx, le_rfl, le_rfl⟩
  have hU : IsEncl (Encl.add (w + 32) (Encl.exact x) (Encl.nat m)) (xv + (m : ℕ)) :=
    hX.add (isEncl0_nat m).encloses
  have hA₁ : IsEncl (Encl.sub (w + 32) (Encl.exact one) (Encl.exact x)) (1 - xv) :=
    enclosesPos_one.encloses0.encloses.sub hX
  have hA₂ : IsEncl (Encl.sub (w + 32) (Encl.neg (Encl.nat (m - 1))) (Encl.exact x))
      (1 - xv - (m : ℕ)) := by
    have := (isEncl0_nat (m - 1)).encloses.neg.sub (w := w + 32) hX
    convert this using 1
    rw [Nat.cast_sub (by omega : 1 ≤ m)]
    push_cast
    ring
  by_cases hsmall : m ≤ 2 ^ lnGammaShiftExp w
  · -- the recurrence in positive terms
    rw [ite_eq_left hsmall] at h
    by_cases hc : (lt zero (Encl.add (w + 32) (Encl.exact x) (Encl.nat m)).1
        && lt zero (Encl.sub (w + 32) (Encl.neg (Encl.nat (m - 1))) (Encl.exact x)).1) = true
    swap
    · rw [ite_eq_right hc] at h
      exact absurd h (by simp)
    rw [ite_eq_left hc, Option.some.injEq] at h
    rw [Bool.and_eq_true] at hc
    subst h
    obtain ⟨hV, h32⟩ := polyWork_bounds hn hw
    have : NeZero (polyWork n w) := ⟨by omega⟩
    have hGu := polygammaPosEncl_spec hn (hU.pos_of_lt hc.1) hw
    have hT := ((isEncl0_ofAzNat (AzNat.factorial n)).mul (w := polyWork n w)
      (polyShiftSum_spec (by omega) h32 (hA₂.pos_of_lt hc.2) m)).encloses
    rw [AzNat.toNat_factorial] at hT
    have hid := polygammaR_neg_sum hn hni m
    by_cases ho : n % 2 = 1
    · rw [ite_eq_left ho]
      have := hGu.add (w := w + 32) hT
      convert this using 1
      rw [hid, (Nat.even_iff.mpr (by omega : (n + 1) % 2 = 0)).neg_one_pow]
      ring
    · rw [ite_eq_right ho]
      have := hGu.sub (w := w + 32) hT
      convert this using 1
      rw [hid, (Nat.odd_iff.mpr (by omega : (n + 1) % 2 = 1)).neg_one_pow]
      ring
  · -- three positive arguments
    rw [ite_eq_right hsmall] at h
    by_cases hc : (lt zero (Encl.add (w + 32) (Encl.exact x) (Encl.nat m)).1
        && lt zero (Encl.sub (w + 32) (Encl.exact one) (Encl.exact x)).1
        && lt zero (Encl.sub (w + 32) (Encl.neg (Encl.nat (m - 1))) (Encl.exact x)).1) = true
    swap
    · rw [ite_eq_right hc] at h
      exact absurd h (by simp)
    rw [ite_eq_left hc, Option.some.injEq] at h
    rw [Bool.and_eq_true, Bool.and_eq_true] at hc
    subst h
    have hGu := polygammaPosEncl_spec hn (hU.pos_of_lt hc.1.1) hw
    have hG₁ := polygammaPosEncl_spec hn (hA₁.pos_of_lt hc.1.2) hw
    have hG₂ := polygammaPosEncl_spec hn (hA₂.pos_of_lt hc.2) hw
    have hD := hG₁.sub (w := w + 32) hG₂
    have hid := polygammaR_reflect hn hni m
    by_cases he : n % 2 = 0
    · rw [ite_eq_left he]
      have := hGu.add (w := w + 32) hD
      convert this using 1
      rw [hid, (Nat.even_iff.mpr he).neg_one_pow]
      ring
    · rw [ite_eq_right he]
      have := hGu.sub (w := w + 32) hD
      convert this using 1
      rw [hid, (Nat.odd_iff.mpr (by omega : n % 2 = 1)).neg_one_pow]
      ring

/-- **`polygammaEncl` encloses `ψ⁽ⁿ⁾(x)`** for a finite `x` that is positive (`pos`) or
negative and not an integer. -/
theorem polygammaEncl_spec {n : ℕ} (hn : 1 ≤ n) {x : AzFloat} {xv : ℝ}
    (hx : x.toVal = some (xv : EReal)) {pos : Bool} (hpos : pos = true → 0 < xv)
    (hneg : pos = false → ∀ k : ℤ, xv ≠ k) {w : ℕ} (hw : 64 ≤ w) {E : Encl}
    (h : polygammaEncl n x pos w = some E) : IsEncl E (polygammaR n xv) := by
  unfold polygammaEncl at h
  obtain ⟨H, hH, rfl⟩ := Option.map_eq_some_iff.mp h
  have hHv : IsEncl H ((-1) ^ (n + 1) * polygammaR n xv) := by
    cases pos with
    | true =>
      rw [ite_eq_left rfl, Option.some.injEq] at hH
      subst hH
      exact polygammaPosEncl_spec hn (isEnclPos_exact hx (hpos rfl)) hw
    | false =>
      rw [ite_eq_right (by simp)] at hH
      exact polygammaNegEncl_spec hn hx (hneg rfl) hw hH
  by_cases ho : n % 2 = 1
  · rw [ite_eq_left ho]
    rwa [(Nat.even_iff.mpr (by omega : (n + 1) % 2 = 0)).neg_one_pow, one_mul] at hHv
  · rw [ite_eq_right ho]
    have := hHv.neg
    rwa [(Nat.odd_iff.mpr (by omega : (n + 1) % 2 = 1)).neg_one_pow, neg_one_mul, neg_neg]
      at this

/-- **`enclRefine` answers with an enclosure of the family**, at the level `w` or at a higher
one. -/
theorem enclRefine_spec {f : ℕ → Option Encl} {v : ℝ} {w₀ : ℕ}
    (hf : ∀ w, w₀ ≤ w → ∀ E, f w = some E → IsEncl E v) (p : ℕ) {w : ℕ} (hw : w₀ ≤ w)
    {E : Encl} (h : enclRefine f p w = some E) : IsEncl E v := by
  unfold enclRefine at h
  split at h
  · exact absurd h (by simp)
  · next E₀ hE₀ =>
    have h₀ := hf w hw E₀ hE₀
    split at h
    · rw [Option.some.injEq] at h; exact h ▸ h₀
    · next r hr =>
      dsimp only at h
      split_ifs at h
      · rw [Option.some.injEq] at h; exact h ▸ h₀
      · exact hf _ (by omega) E h

/-- **`polygammaEnclFor` encloses `ψ⁽ⁿ⁾(x)`**. -/
theorem polygammaEnclFor_spec {n : ℕ} (hn : 1 ≤ n) {x : AzFloat} {xv : ℝ}
    (hx : x.toVal = some (xv : EReal)) {pos : Bool} (hpos : pos = true → 0 < xv)
    (hneg : pos = false → ∀ k : ℤ, xv ≠ k) (p : ℕ) {w : ℕ} (hw : 64 ≤ w) {E : Encl}
    (h : polygammaEnclFor n x pos p w = some E) : IsEncl E (polygammaR n xv) :=
  enclRefine_spec (fun _ hw' _ hE => polygammaEncl_spec hn hx hpos hneg hw' hE) p hw h

end Azurite.AzFloat
