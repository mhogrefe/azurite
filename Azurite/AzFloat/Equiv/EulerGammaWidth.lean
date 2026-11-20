/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.EulerGamma
import Azurite.AzFloat.Equiv.LnSmoothWidth
import Azurite.AzFloat.Equiv.EnclConv
import Azurite.AzInt.Equiv.SweeneyHornerWidth

/-!
# The bracket of Euler's constant converges

`eulerGammaBracket w` has width at most `1000 · 2^(−w)` (`eulerGammaBracket_width`, `w ≥ 64`):

* the truncated recurrence for the partial sum of Sweeney's series: its radius is at most
  `sweeneyU n V (N + 1)` (`AzInt/Equiv/SweeneyHornerWidth.lean`), and with
  `V = w + 16 + ⌊13 n / 9⌋ + 2 ⌊lg n⌋` bits that is at most `204 · 2^(−w)`
  (`sweeneyU_eulerGamma_le`: `e^n ≤ 2^(12 + ⌊13 n / 9⌋)`, since `e^9 ≤ 2^13`);
* the logarithm of the argument, which has no prime factor above `7`
  (`isSmooth_nextSmooth`): width `2^(−k)` (`lnNatBracket_width`);
* the roundings at `k ≥ w + 12 + ⌊lg n⌋` bits of numbers of size at most `n + 6`.

So the brackets converge (`eulerGammaApprox_bracketConv`), and `eulerGammaPrecRoundFuel` has
the specification of a fuel-bound function (`eulerGammaPrecRoundFuel_zivSpec`): sound, and
complete in the limit of the fuel wherever `γ` is no rounding boundary.  Whether `γ` is
rational is an open problem, so there is no precision at which this is known to hold.
-/

namespace Azurite.AzFloat

open Finset Real Filter Topology

/-- The bracket of `ln n` for an integer with no prime factor above `7`: width `2^(−k)`. -/
theorem lnNatBracket_width {n : ℕ} (hs : isSmooth n = true) {k : ℕ} (hk : 4 ≤ k) :
    AEncl (lnNatBracket n k) (Real.log n) ((1 / 2 : ℝ) ^ k) := by
  have hprod := isSmooth_spec hs
  have hlog : Real.log (n : ℝ) = (smoothExps n).1 * Real.log 2
      + (smoothExps n).2.1 * Real.log 3 + (smoothExps n).2.2.1 * Real.log 5
      + (smoothExps n).2.2.2.1 * Real.log 7 := by
    have hc : (n : ℝ) = (2 : ℝ) ^ (smoothExps n).1 * 3 ^ (smoothExps n).2.1
        * 5 ^ (smoothExps n).2.2.1 * 7 ^ (smoothExps n).2.2.2.1 := by exact_mod_cast hprod
    rw [hc, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow,
      Real.log_pow]
  unfold lnNatBracket
  dsimp only
  rw [ite_eq_left hprod, hlog]
  exact lnSmoothBracket_width _ _ _ _ hk

/-- `e^n ≤ 2^(12 + ⌊13 n / 9⌋)`. -/
theorem exp_nat_le_two_pow (n : ℕ) : Real.exp (n : ℝ) ≤ 4096 * (2 : ℝ) ^ (13 * n / 9) := by
  have he := Real.exp_one_lt_d9
  have he0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have he1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have h9 : Real.exp 1 ^ 9 ≤ 2 ^ 13 := by
    have := pow_le_pow_left₀ he0.le he.le 9
    refine this.trans ?_
    norm_num
  have h8 : Real.exp 1 ^ 8 ≤ 4096 := by
    have := pow_le_pow_left₀ he0.le he.le 8
    refine this.trans ?_
    norm_num
  rw [← Real.exp_one_pow]
  have hn := Nat.div_add_mod n 9
  have hb := Nat.mod_lt n (by norm_num : 0 < 9)
  have hq : 13 * (n / 9) ≤ 13 * n / 9 := by omega
  calc Real.exp 1 ^ n = (Real.exp 1 ^ 9) ^ (n / 9) * Real.exp 1 ^ (n % 9) := by
        rw [← pow_mul, ← pow_add, hn]
    _ ≤ (2 ^ 13) ^ (n / 9) * Real.exp 1 ^ 8 :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) h9 _)
          (pow_le_pow_right₀ he1 (by omega)) (by positivity) (by positivity)
    _ ≤ (2 : ℝ) ^ (13 * n / 9) * 4096 := by
        rw [← pow_mul]
        exact mul_le_mul (pow_le_pow_right₀ (by norm_num) hq) h8 (by positivity) (by positivity)
    _ = 4096 * (2 : ℝ) ^ (13 * n / 9) := mul_comm _ _

/-- **The radius of the partial sum at the working size of Euler's constant**: at most
`204 · 2^(−w)`. -/
theorem sweeneyU_eulerGamma_le {w : ℕ} (hw : 64 ≤ w) {n : ℕ} (hn : 1 ≤ n) :
    AzInt.sweeneyU n (eulerGammaWork w n) (eulerGammaTermsOf n + 1) ≤ 204 * (1 / 2 : ℝ) ^ w := by
  unfold AzInt.sweeneyU
  have hV : eulerGammaWork w n - 1 = w + 15 + 13 * n / 9 + 2 * n.log2 := by
    have : eulerGammaWork w n = w + 16 + 13 * n / 9 + 2 * n.log2 := rfl
    omega
  rw [hV]
  set m : ℝ := (2 : ℝ) ^ n.log2 with hm
  set Q : ℝ := (2 : ℝ) ^ (13 * n / 9) with hQ
  set A : ℝ := (2 : ℝ) ^ (w + 15) with hA
  have hm1 : 1 ≤ m := one_le_pow₀ (by norm_num)
  have hQ1 : 1 ≤ Q := one_le_pow₀ (by norm_num)
  have hA0 : 0 < A := by positivity
  have hP : (2 : ℝ) ^ (w + 15 + 13 * n / 9 + 2 * n.log2) = A * Q * (m * m) := by
    have h2 : (2 : ℝ) ^ (2 * n.log2) = m * m := by
      rw [hm, ← pow_add]
      congr 1
      omega
    rw [pow_add, pow_add, h2]
  rw [hP]
  have hnm : (n : ℝ) ≤ 2 * m := by
    have h := Nat.lt_log2_self (n := n)
    rw [pow_succ] at h
    have h' : (n : ℝ) < ((2 ^ n.log2 * 2 : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    rw [hm]
    linarith
  have hc : ((eulerGammaTermsOf n + 1 : ℕ) : ℝ) ≤ 37 * n := by
    have : eulerGammaTermsOf n + 1 ≤ 37 * n := by
      unfold eulerGammaTermsOf
      omega
    exact_mod_cast this
  have hc0 : (0 : ℝ) ≤ ((eulerGammaTermsOf n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hexp := exp_nat_le_two_pow n
  rw [← hQ] at hexp
  have hE0 : 0 < Real.exp (n : ℝ) := Real.exp_pos _
  have hPpos : 0 < A * Q * (m * m) := by positivity
  have hA79 : (2 : ℝ) ^ 79 ≤ A := by
    rw [hA]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hAw : A * (1 / 2 : ℝ) ^ w = 32768 := by
    rw [hA, pow_add, mul_right_comm, ← mul_pow]
    norm_num
  have hmm : m ≤ m * m := by nlinarith
  set c : ℝ := ((eulerGammaTermsOf n + 1 : ℕ) : ℝ) with hcdef
  have hc74 : c ≤ 74 * m := by linarith
  -- the main factor
  have h1 : c * (11 * Real.exp (n : ℝ) / (A * Q * (m * m))) ≤ 102 * (1 / 2 : ℝ) ^ w := by
    rw [← mul_div_assoc, div_le_iff₀ hPpos]
    have e : 102 * (1 / 2 : ℝ) ^ w * (A * Q * (m * m)) = 102 * 32768 * (Q * (m * m)) := by
      rw [← hAw]
      ring
    rw [e]
    have a1 : c * (11 * Real.exp (n : ℝ)) ≤ 74 * m * (11 * (4096 * Q)) :=
      mul_le_mul hc74 (by linarith) (by positivity) (by positivity)
    have a2 : 74 * m * (11 * (4096 * Q)) ≤ 102 * 32768 * (Q * (m * m)) := by
      have : Q * m ≤ Q * (m * m) := mul_le_mul_of_nonneg_left hmm (by positivity)
      nlinarith
    linarith
  -- the factor `(1 + a)^c ≤ 2`
  have hx0 : (0 : ℝ) ≤ 17 / (A * Q * (m * m)) := by positivity
  have h2 : (1 + 17 / (A * Q * (m * m))) ^ (eulerGammaTermsOf n + 1) ≤ 2 := by
    have hcx : c * (17 / (A * Q * (m * m))) ≤ 1 / 2 := by
      rw [← mul_div_assoc, div_le_iff₀ hPpos]
      have a1 : c * 17 ≤ 74 * m * 17 := by nlinarith
      have a2 : (2 : ℝ) ^ 79 * 1 * m ≤ A * Q * (m * m) :=
        mul_le_mul (mul_le_mul hA79 hQ1 (by norm_num) hA0.le) hmm (by positivity)
          (by positivity)
      have a3 : (2 : ℝ) ^ 79 ≥ 2516 := by norm_num
      nlinarith
    have hle : 1 + 17 / (A * Q * (m * m)) ≤ Real.exp (17 / (A * Q * (m * m))) := by
      have := Real.add_one_le_exp (17 / (A * Q * (m * m)))
      linarith
    calc (1 + 17 / (A * Q * (m * m))) ^ (eulerGammaTermsOf n + 1)
        ≤ Real.exp (17 / (A * Q * (m * m))) ^ (eulerGammaTermsOf n + 1) :=
          pow_le_pow_left₀ (by linarith) hle _
      _ = Real.exp (c * (17 / (A * Q * (m * m)))) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr (by
          have := Real.log_two_gt_d9
          linarith)
      _ = 2 := Real.exp_log (by norm_num)
  have h10 : 0 ≤ c * (11 * Real.exp (n : ℝ) / (A * Q * (m * m))) := by positivity
  calc c * (11 * Real.exp (n : ℝ) / (A * Q * (m * m)))
        * (1 + 17 / (A * Q * (m * m))) ^ (eulerGammaTermsOf n + 1)
      ≤ 102 * (1 / 2 : ℝ) ^ w * 2 := mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = 204 * (1 / 2 : ℝ) ^ w := by ring

set_option maxHeartbeats 400000 in
/-- **The width of the bracket of Euler's constant**: at most `1000 · 2^(−w)` (`w ≥ 64`). -/
theorem eulerGammaBracket_width {w : ℕ} (hw : 64 ≤ w) :
    AEncl (eulerGammaBracket w) eulerMascheroniConstant (1000 * (1 / 2 : ℝ) ^ w) := by
  obtain ⟨n, hndef⟩ : ∃ n, n = eulerGammaArg w := ⟨_, rfl⟩
  have hnN : eulerGammaN w ≤ n := hndef ▸ eulerGammaN_le_arg w
  have hsm : isSmooth n = true := hndef ▸ isSmooth_nextSmooth (one_le_eulerGammaN w)
  show AEncl (eulerGammaBracketAt w (eulerGammaArg w)) _ _
  rw [← hndef]
  set N := eulerGammaTermsOf n with hN
  set k := eulerGammaBits w n with hk
  set V := eulerGammaWork w n with hVdef
  have hk64 : 64 ≤ k := by rw [hk]; exact le_max_left _ _
  have hkw : w + 12 + n.log2 ≤ k := by
    rw [hk]
    unfold eulerGammaBits
    omega
  have hV1 : 1 ≤ V := by rw [hVdef]; unfold eulerGammaWork; omega
  have : NeZero k := ⟨by omega⟩
  have hn1' : 1 ≤ n := (one_le_eulerGammaN w).trans hnN
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1'
  have hn0 : (0 : ℝ) < n := by linarith
  -- the exact value and the partial sum
  set S := ∑ i ∈ range N, sweeneyTerm (n : ℝ) i with hS
  have hγ := eulerMascheroni_eq_sweeney hn1
  have hE0 := expIntegralE1_nonneg hn0
  have hE1 := (expIntegralE1_le hn0).trans (exp_neg_div_le_of_eulerGammaN_le hnN)
  have htail := abs_tail_eulerGamma_le hw hnN
  rw [← hN, ← hS] at htail
  rw [abs_le] at htail
  have hγhalf := one_half_lt_eulerMascheroniConstant
  have hγtt := eulerMascheroniConstant_lt_two_thirds
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hlogle : Real.log (n : ℝ) ≤ n - 1 := Real.log_le_sub_one_of_pos hn0
  set X := (1 / 2 : ℝ) ^ w with hX
  have hX0 : 0 < X := by positivity
  have hXs : X ≤ 1 / 2 ^ 64 := by
    rw [hX]
    exact (pow_le_pow_of_le_one (by norm_num) (by norm_num) hw).trans (by norm_num)
  have hpow8 : (1 / 2 : ℝ) ^ (w + 8) = X / 256 := by rw [pow_add, hX]; ring
  have hpow5 : (1 / 2 : ℝ) ^ (w + 5) = X / 32 := by rw [pow_add, hX]; ring
  have hpow4 : (1 / 2 : ℝ) ^ (w + 4) = X / 16 := by rw [pow_add, hX]; ring
  rw [hpow8] at htail
  rw [hpow5] at hE1
  have hS0 : 0 ≤ S := by linarith [htail.2]
  have hSn : S ≤ n + 1 := by linarith [htail.1]
  -- the precision of the floats
  set u := (1 / 2 : ℝ) ^ k with hu
  have hu0 : 0 < u := by positivity
  have huX : u ≤ X / 4096 := by
    have h1 : u ≤ (1 / 2 : ℝ) ^ (w + 12) := by
      rw [hu]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have h2 : (1 / 2 : ℝ) ^ (w + 12) = X / 4096 := by rw [pow_add, hX]; ring
    linarith
  have hnu : (n : ℝ) * u ≤ X / 2048 := by
    have h1 : u ≤ (1 / 2 : ℝ) ^ (w + 12 + n.log2) := by
      rw [hu]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hkw
    have h2 : (1 / 2 : ℝ) ^ (w + 12 + n.log2) = X / 4096 * (1 / 2 : ℝ) ^ n.log2 := by
      rw [pow_add, pow_add, hX]
      ring
    have h3 : (n : ℝ) < 2 * (2 : ℝ) ^ n.log2 := by
      have h := Nat.lt_log2_self (n := n)
      rw [pow_succ] at h
      have h' : (n : ℝ) < ((2 ^ n.log2 * 2 : ℕ) : ℝ) := by exact_mod_cast h
      push_cast at h'
      linarith
    have h4 : (2 : ℝ) ^ n.log2 * (1 / 2 : ℝ) ^ n.log2 = 1 := by
      rw [← mul_pow]
      norm_num
    have h5 : (0 : ℝ) < (1 / 2 : ℝ) ^ n.log2 := by positivity
    have h6 : (n : ℝ) * (1 / 2 : ℝ) ^ n.log2 ≤ 2 := by nlinarith
    calc (n : ℝ) * u ≤ n * (X / 4096 * (1 / 2 : ℝ) ^ n.log2) :=
          mul_le_mul_of_nonneg_left (h1.trans h2.le) hn0.le
      _ = X / 4096 * ((n : ℝ) * (1 / 2 : ℝ) ^ n.log2) := by ring
      _ ≤ X / 4096 * 2 := mul_le_mul_of_nonneg_left h6 (by positivity)
      _ = X / 2048 := by ring
  -- the enclosure of the partial sum, with its width
  set e := AzInt.sweeneyHornerEncl n N V (eulerGammaBlockBits V) with he
  obtain ⟨hden, hloS, hShi⟩ := AzInt.sweeneyHornerEncl_spec n N hV1 (eulerGammaBlockBits V) hS0
  have hwid := AzInt.sweeneyHornerEncl_width n N hV1 (eulerGammaBlockBits V) hS0
  have hU := sweeneyU_eulerGamma_le hw hn1'
  rw [← hVdef, ← hN, ← hX] at hU
  rw [← he] at hden hloS hShi hwid
  have hden' : (0 : ℝ) < e.2.2.toNat := by exact_mod_cast hden
  set a' : ℝ := (e.1.toNat : ℝ) / e.2.2.toNat with ha'
  set c' : ℝ := (e.2.1.toNat : ℝ) / e.2.2.toNat with hc'
  have ha0 : 0 ≤ a' := by rw [ha']; positivity
  have hc0 : 0 ≤ c' := by rw [hc']; positivity
  have hca : c' - a' ≤ 408 * X := by linarith
  obtain ⟨sl, -, hsl, -, hsl0, hslS, hsllo, -, -⟩ :=
    seriesBracket_spec_of (s := (e.1, e.2.2)) rfl hden ha0 (k := k) (by omega)
  obtain ⟨-, sh, -, hsh, -, -, -, hSsh, hshhi⟩ :=
    seriesBracket_spec_of (s := (e.2.1, e.2.2)) rfl hden hc0 (k := k) (by omega)
  rw [← hu] at hsllo hshhi
  have hsl' : (fracFloor e.1 e.2.2 k).toVal = some (sl : EReal) := hsl
  have hsh' : (fracCeil e.2.1 e.2.2 k).toVal = some (sh : EReal) := hsh
  -- the logarithm
  obtain ⟨ll, lh, hll, hlh, hllog, hlogh, hlw⟩ := lnNatBracket_width hsm (k := k) (by omega)
  rw [← hu] at hlw
  -- the tail float
  have ht := toVal_eulerGamma_tail w
  rw [hpow4] at ht
  -- the two ends
  obtain ⟨r₁, hr₁, hr₁le, hr₁ge⟩ := subFloor_abs hsl' hlh k
  obtain ⟨r₂, hr₂, hr₂le, hr₂ge⟩ := subFloor_abs hr₁ ht k
  obtain ⟨r₃, hr₃, hr₃ge, hr₃le⟩ := addCeiling_abs hsh' ht k
  obtain ⟨r₄, hr₄, hr₄ge, hr₄le⟩ := subCeiling_abs hr₃ hll k
  rw [← hu] at hr₁ge hr₂ge hr₃le hr₄le
  -- sizes
  have hus : u ≤ 1 / 2 ^ 64 := by linarith [div_le_self hX0.le (by norm_num : (1 : ℝ) ≤ 4096)]
  have hc'n : c' ≤ n + 2 := by linarith
  have hslle : sl ≤ n + 1 := by linarith
  have hshle : sh ≤ n + 3 := by
    have : c' * (8 * u) ≤ (n + 2) * (8 * u) := mul_le_mul_of_nonneg_right hc'n (by positivity)
    linarith
  have hsh0 : 0 ≤ sh := hc0.trans hSsh
  have b₁ : |sl - lh| ≤ n + 2 := by
    rw [abs_le]
    constructor <;> linarith
  have m₁ : 2 * |sl - lh| * u ≤ 2 * ((n : ℝ) + 2) * u :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left b₁ (by norm_num)) hu0.le
  have b₂ : |r₁ - X / 16| ≤ n + 4 := by
    rw [abs_le]
    constructor <;> linarith
  have m₂ : 2 * |r₁ - X / 16| * u ≤ 2 * ((n : ℝ) + 4) * u :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left b₂ (by norm_num)) hu0.le
  have b₃ : |sh + X / 16| ≤ n + 4 := by
    rw [abs_le]
    constructor <;> linarith
  have m₃ : 2 * |sh + X / 16| * u ≤ 2 * ((n : ℝ) + 4) * u :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left b₃ (by norm_num)) hu0.le
  have hr₃n : r₃ ≤ n + 5 := by linarith
  have b₄ : |r₃ - ll| ≤ n + 6 := by
    rw [abs_le]
    constructor <;> linarith
  have m₄ : 2 * |r₃ - ll| * u ≤ 2 * ((n : ℝ) + 6) * u :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left b₄ (by norm_num)) hu0.le
  have hshsl : sh - sl ≤ 408 * X + 14 * ((n : ℝ) + 2) * u := by
    have h1 : c' * (8 * u) ≤ ((n : ℝ) + 2) * (8 * u) :=
      mul_le_mul_of_nonneg_right hc'n (by positivity)
    have h2 : a' * (6 * u) ≤ ((n : ℝ) + 2) * (6 * u) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  refine ⟨r₂, r₄, ?_, ?_, ?_, ?_, ?_⟩
  · show (eulerGammaBracketAt w n).1.toVal = _
    simp only [eulerGammaBracketAt]
    rw [← hk, ← hVdef, ← hN, ← he]
    exact hr₂
  · show (eulerGammaBracketAt w n).2.toVal = _
    simp only [eulerGammaBracketAt]
    rw [← hk, ← hVdef, ← hN, ← he]
    exact hr₄
  · linarith [htail.2]
  · linarith [htail.1]
  · linarith

/-- **The bracket of Euler's constant converges.** -/
theorem eulerGammaApprox_bracketConv : BracketConv eulerGammaApprox eulerMascheroniConstant :=
  bracketConv_of_AEncl (a := eulerGammaBracket) (tendsto_const_mul_half_pow_add 1000 0)
    (eventually_atTop.mpr ⟨64, fun _ hw => eulerGammaBracket_width hw⟩)

/-- **The specification of Euler's constant** (`ZivSpec`): sound at every fuel, and complete
in the limit of the fuel at every precision at which `γ` is no rounding boundary.  The sets of
arguments with a known value are empty: whether `γ` is rational is an open problem. -/
theorem eulerGammaPrecRoundFuel_zivSpec :
    ZivSpec (fun _ : Unit => some ((eulerMascheroniConstant : ℝ) : EReal))
      (fun fuel _ p mode => eulerGammaPrecRoundFuel fuel p mode) ∅ ∅ where
  sound := fun fuel _ p _ mode => eulerGammaPrecRoundFuel_eq_or fuel p mode
  complete := fun _ p _ mode hB => by
    have hB' := hB _ rfl
    obtain ⟨F, hF⟩ := zivLoop_eventually_eq p mode eulerGammaApprox
      eulerGammaApprox_bracketConv (ne_zero_of_not_mem_floatSet hB') hB' (max (p + 16) 64)
      (by omega) (fun w hw => Or.inl (by
        obtain ⟨lv, hv, hl, hh, hlo, hhi⟩ := eulerGammaApprox_spec (le_trans (le_max_right _ _) hw)
        exact ⟨lv, hv, hl, hh, hlo.le, hhi⟩))
    refine ⟨F, fun fuel hfuel => ?_⟩
    show eulerGammaPrecRoundFuel fuel p mode = _
    unfold eulerGammaPrecRoundFuel
    rw [ite_eq_right (NeZero.ne p)]
    exact hF fuel hfuel
  dyadic := fun _ h => absurd h (Set.notMem_empty _)
  nondyadic := fun _ h => absurd h (Set.notMem_empty _)
  correct := fun _ h => by
    rcases h with h | h <;> exact absurd h (Set.notMem_empty _)

end Azurite.AzFloat
