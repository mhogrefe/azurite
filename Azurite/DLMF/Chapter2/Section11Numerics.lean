/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section11
import Azurite.AzFloat.Equiv.Interval

/-!
# DLMF §2.11(i): the numerical claims, computed by `AzFloat`

All numbers are computed by Azurite's own floating-point arithmetic: interval evaluation with
directed rounding at 64 bits (`AzFloat.Encl`), from the Brent–Salamin bracket of `π` and the
bracket of `e^{−10}`. The kernel evaluates the enclosures (`decide +kernel`, no `native_decide`)
and their decimal renderings, and the soundness lemmas of `AzFloat/Equiv/Interval.lean` turn the
computed endpoints into real bounds.

* "On rounding to 5D, `q₁(π) = −0.05318`, `q₂(π) = 0.04791`, `q₃(π) = −0.08985`"
  (`dlmf_2_11_i_q_decimals`, `dlmf_2_11_i_q_values`).
* 2.11.4: the terms `−0.0005318`, `0.0000048`, `−0.0000001` and their sum `−0.0005271` to 7D
  (`dlmf_2_11_4_decimals`, `dlmf_2_11_4`).
* "to 7D `I(10) = −0.0004558`" (`dlmf_2_11_i_I10_decimal`, `dlmf_2_11_i_I10`), from
  `I(10) = ½πe^{−10} + ∑_{s=1}^{3} q_s(π)/10^{2s} + E` with the remainder bound of
  `dlmf_2_11_i_shifted` (`|E| ≤ 8.93 × 10^{−9}`).
* "The error term is, in fact, approximately 700 times the last term obtained in (2.11.4)"
  (`dlmf_2_11_i_ratio`: `(I(10) + 0.0005271)/0.0000001 ∈ (713, 714)`).
-/

namespace Azurite.DLMF

open Azurite.AzFloat Encl
open scoped Real

/-! ### The enclosures (working precision `w`) -/

/-- `π`. -/
def s11Pi (w : Nat) : Encl := Encl.pi w
/-- `π²`. -/
def s11Sq (w : Nat) : Encl := Encl.mul w (s11Pi w) (s11Pi w)
/-- `π² + 1`. -/
def s11P2 (w : Nat) : Encl := Encl.add w (s11Sq w) (exact one)
/-- `|q₁(π)| = 2π/(π² + 1)²`. -/
def s11Q1 (w : Nat) : Encl := Encl.div w (Encl.mul w (nat 2) (s11Pi w)) (Encl.pow w (s11P2 w) 2)
/-- `q₂(π) = 24π(π² − 1)/(π² + 1)⁴`. -/
def s11Q2 (w : Nat) : Encl :=
  Encl.div w (Encl.mul w (Encl.mul w (nat 24) (s11Pi w)) (Encl.subNonneg w (s11Sq w) (exact one)))
    (Encl.pow w (s11P2 w) 4)
/-- `|q₃(π)| = 240π(3π² − 1)(π² − 3)/(π² + 1)⁶`. -/
def s11Q3 (w : Nat) : Encl :=
  Encl.div w (Encl.mul w (Encl.mul w (Encl.mul w (nat 240) (s11Pi w))
    (Encl.subNonneg w (Encl.mul w (nat 3) (s11Sq w)) (exact one)))
    (Encl.subNonneg w (s11Sq w) (nat 3)))
    (Encl.pow w (s11P2 w) 6)
/-- `|q₁(π)|/10²`. -/
def s11T1 (w : Nat) : Encl := Encl.div w (s11Q1 w) (nat 100)
/-- `q₂(π)/10⁴`. -/
def s11T2 (w : Nat) : Encl := Encl.div w (s11Q2 w) (nat 10000)
/-- `|q₃(π)|/10⁶`. -/
def s11T3 (w : Nat) : Encl := Encl.div w (s11Q3 w) (nat 1000000)
/-- The sum of the three terms of 2.11.4. -/
def s11S3 (w : Nat) : Encl := Encl.sub w (Encl.sub w (s11T2 w) (s11T1 w)) (s11T3 w)
/-- The remainder bound `7!/((π² + 1)⁴ 10⁸) + 7!/(π⁸ 10⁸)` of `dlmf_2_11_i_shifted`. -/
def s11Err (w : Nat) : Encl :=
  Encl.add w (Encl.div w (Encl.div w (nat 5040) (Encl.pow w (s11P2 w) 4)) (nat 100000000))
    (Encl.div w (Encl.div w (nat 5040) (Encl.pow w (s11Pi w) 8)) (nat 100000000))
/-- `½πe^{−10}` plus the sum of 2.11.4. -/
def s11Main (w : Nat) : Encl :=
  Encl.add w (Encl.mul w (Encl.div w (s11Pi w) (nat 2))
    (Encl.exp w (-(ofAzNat (AzNat.ofNat 10))))) (s11S3 w)
/-- `I(10)`. -/
def s11I10 (w : Nat) : Encl := Encl.widen w (s11Main w) (s11Err w)

/-! ### The kernel computations -/

set_option maxRecDepth 100000 in
/-- "On rounding to 5D, `q₁(π) = −0.05318`, `q₂(π) = 0.04791`, `q₃(π) = −0.08985`": both ends
of each enclosure round to the DLMF values. -/
theorem dlmf_2_11_i_q_decimals :
    (toDecimalPlaces (-(s11Q1 64).1) 5, toDecimalPlaces (-(s11Q1 64).2) 5,
      toDecimalPlaces (s11Q2 64).1 5, toDecimalPlaces (s11Q2 64).2 5,
      toDecimalPlaces (-(s11Q3 64).1) 5, toDecimalPlaces (-(s11Q3 64).2) 5) =
    (some "-0.05318", some "-0.05318", some "0.04791", some "0.04791", some "-0.08985",
      some "-0.08985") := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The terms of 2.11.4 to 7D: `−0.00053 18`, `0.00000 48`, `−0.00000 01`. -/
theorem dlmf_2_11_4_term_decimals :
    (toDecimalPlaces (-(s11T1 64).1) 7, toDecimalPlaces (-(s11T1 64).2) 7,
      toDecimalPlaces (s11T2 64).1 7, toDecimalPlaces (s11T2 64).2 7,
      toDecimalPlaces (-(s11T3 64).1) 7, toDecimalPlaces (-(s11T3 64).2) 7) =
    (some "-0.0005318", some "-0.0005318", some "0.0000048", some "0.0000048",
      some "-0.0000001", some "-0.0000001") := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The sum in 2.11.4 to 7D: `−0.00052 71`. -/
theorem dlmf_2_11_4_decimals :
    (toDecimalPlaces (s11S3 64).1 7, toDecimalPlaces (s11S3 64).2 7) =
      (some "-0.0005271", some "-0.0005271") := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- "to 7D `I(10) = −0.00045 58`". -/
theorem dlmf_2_11_i_I10_decimal :
    (toDecimalPlaces (s11I10 64).1 7, toDecimalPlaces (s11I10 64).2 7) =
      (some "-0.0004558", some "-0.0004558") := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem s11Q1_data :
    (valData (s11Q1 64).1, valData (s11Q1 64).2) =
      (some (true, 7848056145704434351, 147573952589676412928),
        some (true, 3924028072852217177, 73786976294838206464)) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem s11Q2_data :
    (valData (s11Q2 64).1, valData (s11Q2 64).2) =
      (some (true, 1767502877987745907, 36893488147419103232),
        some (true, 14140023023901967269, 295147905179352825856)) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem s11Q3_data :
    (valData (s11Q3 64).1, valData (s11Q3 64).2) =
      (some (true, 3314820174250714847, 36893488147419103232),
        some (true, 828705043562678713, 9223372036854775808)) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem s11S3_data :
    (valData (s11S3 64).1, valData (s11S3 64).2) =
      (some (false, 9956712907077919751, 18889465931478580854784),
        some (false, 9723352448318281, 18446744073709551616)) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem s11I10_data :
    (valData (s11I10 64).1, valData (s11I10 64).2) =
      (some (false, 8609797259565465849, 18889465931478580854784),
        some (false, 4304730093354988609, 9444732965739290427392)) := by
  decide +kernel

/-! ### Soundness -/

section Soundness

instance : NeZero (64 : ℕ) := ⟨by norm_num⟩

private theorem hw64 : 2 ≤ 64 := by norm_num

theorem isEncl_of_eq {a : Encl} {x y : ℝ} (h : IsEncl a x) (e : x = y) : IsEncl a y := e ▸ h

theorem isEncl0_of_eq {a : Encl} {x y : ℝ} (h : IsEncl0 a x) (e : x = y) : IsEncl0 a y := e ▸ h

theorem pi_mul_pi_ge_three : (3 : ℝ) ≤ π * π := by nlinarith [Real.pi_gt_three]

theorem s11Pi_encl : IsEnclPos (s11Pi 64) π := enclosesPos_pi (by norm_num)

theorem s11Sq_encl : IsEnclPos (s11Sq 64) (π * π) := s11Pi_encl.mul hw64 s11Pi_encl

theorem s11P2_encl : IsEnclPos (s11P2 64) (π * π + 1) :=
  s11Sq_encl.add hw64 enclosesPos_one.encloses0

theorem s11Q1_encl : IsEncl0 (s11Q1 64) (2 * π / (π * π + 1) ^ 2) :=
  ((enclosesPos_nat (n := 2) (by norm_num)).mul hw64 s11Pi_encl).encloses0.div
    (s11P2_encl.pow hw64 2)

theorem s11Q2_encl : IsEncl0 (s11Q2 64) (24 * π * (π * π - 1) / (π * π + 1) ^ 4) :=
  (((enclosesPos_nat (n := 24) (by norm_num)).mul hw64 s11Pi_encl).encloses0.mul
    (s11Sq_encl.encloses0.encloses.subNonneg enclosesPos_one.encloses0.encloses
      (by linarith [pi_mul_pi_ge_three]))).div (s11P2_encl.pow hw64 4)

theorem s11Q3_encl :
    IsEncl0 (s11Q3 64) (240 * π * (3 * (π * π) - 1) * (π * π - 3) / (π * π + 1) ^ 6) :=
  ((((enclosesPos_nat (n := 240) (by norm_num)).mul hw64 s11Pi_encl).encloses0.mul
    ((((enclosesPos_nat (n := 3) (by norm_num)).mul hw64 s11Sq_encl).encloses0.encloses.subNonneg
      enclosesPos_one.encloses0.encloses (by push_cast; linarith [pi_mul_pi_ge_three])))).mul
    (s11Sq_encl.encloses0.encloses.subNonneg
      (enclosesPos_nat (n := 3) (by norm_num)).encloses0.encloses
      (by push_cast; linarith [pi_mul_pi_ge_three]))).div (s11P2_encl.pow hw64 6)

theorem cosIntQ_one_pi : cosIntQ 1 π = -(2 * π / (π * π + 1) ^ 2) := by
  rw [(dlmf_2_11_3 π).1]; ring

theorem cosIntQ_two_pi : cosIntQ 2 π = 24 * π * (π * π - 1) / (π * π + 1) ^ 4 := by
  rw [(dlmf_2_11_3 π).2.1]; ring

theorem cosIntQ_three_pi :
    cosIntQ 3 π = -(240 * π * (3 * (π * π) - 1) * (π * π - 3) / (π * π + 1) ^ 6) := by
  rw [(dlmf_2_11_3 π).2.2]; ring

/-- The sum `∑_{s=1}^{3} q_s(π)/10^{2s}` of 2.11.4. -/
theorem s11S3_encl :
    IsEncl (s11S3 64) (∑ s ∈ Finset.range 3, cosIntQ (s + 1) π / (10 : ℝ) ^ (2 * (s + 1))) := by
  have h1 := s11Q1_encl.div (w := 64) (enclosesPos_nat (n := 100) (by norm_num))
  have h2 := s11Q2_encl.div (w := 64) (enclosesPos_nat (n := 10000) (by norm_num))
  have h3 := s11Q3_encl.div (w := 64) (enclosesPos_nat (n := 1000000) (by norm_num))
  refine isEncl_of_eq ((h2.encloses.sub (w := 64) h1.encloses).sub (w := 64) h3.encloses) ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.reduceAdd,
    Nat.reduceMul, cosIntQ_one_pi, cosIntQ_two_pi, cosIntQ_three_pi]
  push_cast
  ring

theorem s11Err_encl :
    IsEncl0 (s11Err 64)
      (5040 / (π * π + 1) ^ 4 / 100000000 + 5040 / π ^ 8 / 100000000) := by
  have h1 := ((enclosesPos_nat (n := 5040) (by norm_num)).encloses0.div (w := 64)
    (s11P2_encl.pow hw64 4)).div (w := 64) (enclosesPos_nat (n := 100000000) (by norm_num))
  have h2 := ((enclosesPos_nat (n := 5040) (by norm_num)).encloses0.div (w := 64)
    (s11Pi_encl.pow hw64 8)).div (w := 64) (enclosesPos_nat (n := 100000000) (by norm_num))
  refine isEncl0_of_eq (h1.add (w := 64) h2) ?_
  push_cast
  ring

theorem s11Main_encl :
    IsEncl (s11Main 64) (π / 2 * Real.exp (-10) +
      ∑ s ∈ Finset.range 3, cosIntQ (s + 1) π / (10 : ℝ) ^ (2 * (s + 1))) := by
  have hx : (-(ofAzNat (AzNat.ofNat 10))).toVal = some ((-10 : ℝ) : EReal) := by
    rw [toVal_neg, toVal_ofAzNat, AzNat.toNat_ofNat]
    simp
  have h1 := (s11Pi_encl.encloses0.div (w := 64) (enclosesPos_nat (n := 2) (by norm_num))).mul
    (w := 64) (encloses0_exp hx (w := 64) (by norm_num))
  refine isEncl_of_eq (h1.encloses.add (w := 64) s11S3_encl) ?_
  push_cast
  ring

theorem s11I10_encl : IsEncl (s11I10 64) (cosIntI 10) := by
  refine s11Main_encl.widen s11Err_encl ?_
  have h := (dlmf_2_11_i_shifted 3 (m := 10) (by norm_num))
  have hb := h.1.trans h.2
  simp only [Nat.cast_ofNat, show (-1 : ℝ) ^ 10 = 1 by norm_num, one_mul] at hb
  refine (le_of_eq_of_le ?_ hb).trans (le_of_eq ?_)
  · congr 1; ring
  · simp only [show (2 * 3 + 1).factorial = 5040 by rfl, show 3 + 1 = 4 by rfl,
      show 2 * 3 + 2 = 8 by rfl]
    push_cast
    ring

end Soundness

/-! ### The claims -/

theorem abs_sub_lt_of_bounds {x L U c e : ℝ} (hL : L ≤ x) (hU : x ≤ U) (h1 : c - e < L)
    (h2 : U < c + e) : |x - c| < e :=
  abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩

/-- **"On rounding to 5D, `q₁(π) = −0.05318`, `q₂(π) = 0.04791`, `q₃(π) = −0.08985`."** -/
theorem dlmf_2_11_i_q_values :
    |cosIntQ 1 π - (-0.05318)| < 0.000005 ∧ |cosIntQ 2 π - 0.04791| < 0.000005 ∧
      |cosIntQ 3 π - (-0.08985)| < 0.000005 := by
  obtain ⟨d1, d2⟩ := Prod.mk.inj s11Q1_data
  obtain ⟨e1, e2⟩ := Prod.mk.inj s11Q2_data
  obtain ⟨f1, f2⟩ := Prod.mk.inj s11Q3_data
  obtain ⟨l1, u1⟩ := s11Q1_encl.encloses.bounds d1 d2
  obtain ⟨l2, u2⟩ := s11Q2_encl.encloses.bounds e1 e2
  obtain ⟨l3, u3⟩ := s11Q3_encl.encloses.bounds f1 f2
  rw [cosIntQ_one_pi, cosIntQ_two_pi, cosIntQ_three_pi]
  refine ⟨abs_sub_lt_of_bounds (neg_le_neg u1) (neg_le_neg l1) ?_ ?_,
    abs_sub_lt_of_bounds l2 u2 ?_ ?_,
    abs_sub_lt_of_bounds (neg_le_neg u3) (neg_le_neg l3) ?_ ?_⟩ <;>
    norm_num [signedVal]

/-- **DLMF 2.11.4**: the first three terms of 2.11.2 at `m = 10` sum to `−0.00052 71` (7D). -/
theorem dlmf_2_11_4 :
    |(-1) ^ 10 * ∑ s ∈ Finset.range 3, cosIntQ (s + 1) π / (10 : ℝ) ^ (2 * (s + 1)) -
      (-0.0005271)| < 0.00000005 := by
  obtain ⟨d1, d2⟩ := Prod.mk.inj s11S3_data
  obtain ⟨l, u⟩ := s11S3_encl.bounds d1 d2
  rw [show (-1 : ℝ) ^ 10 = 1 by norm_num, one_mul]
  exact abs_sub_lt_of_bounds l u (by norm_num [signedVal]) (by norm_num [signedVal])

/-- **"But this answer is incorrect: to 7D `I(10) = −0.00045 58`."** -/
theorem dlmf_2_11_i_I10 : |cosIntI 10 - (-0.0004558)| < 0.00000005 := by
  obtain ⟨d1, d2⟩ := Prod.mk.inj s11I10_data
  obtain ⟨l, u⟩ := s11I10_encl.bounds d1 d2
  exact abs_sub_lt_of_bounds l u (by norm_num [signedVal]) (by norm_num [signedVal])

/-- **"The error term is, in fact, approximately 700 times the last term obtained in (2.11.4)"**:
`I(10) − (−0.00052 71)` is between `713` and `714` times `0.00000 01`. -/
theorem dlmf_2_11_i_ratio :
    713 < (cosIntI 10 - (-0.0005271)) / 0.0000001 ∧
      (cosIntI 10 - (-0.0005271)) / 0.0000001 < 714 := by
  obtain ⟨d1, d2⟩ := Prod.mk.inj s11I10_data
  obtain ⟨l, u⟩ := s11I10_encl.bounds d1 d2
  norm_num [signedVal] at l u
  constructor
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith

end Azurite.DLMF
