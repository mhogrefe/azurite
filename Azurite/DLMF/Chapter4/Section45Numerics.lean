/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section45
import Azurite.AzFloat.Equiv.Interval
import Azurite.AzFloat.Equiv.SqrtPiBracket
import Azurite.AzFloat.Equiv.Ln10Bracket

/-!
# DLMF §4.45(i): the numerical claims, computed by `AzFloat`

All numbers are computed by Azurite's own floating-point interval arithmetic at 64 bits
(`AzFloat.Encl`); the kernel evaluates the enclosures (`decide +kernel`, no `native_decide`) and
the soundness lemmas of `AzFloat/Equiv/Interval.lean` turn the endpoints into real bounds. DLMF's
"`…`" decimals are truncated, so each claim is `d ≤ value < d + 10⁻ᵏ`.

* 4.45.12 (`x = 9.47376`): `x₁ = 0.90000…`, `x₂ = 0.38373…`, `x₃ = 0.18528…`, `x₄ = 0.09185…`
  (`dlmf_4_45_12`), through enclosures of the step of 4.45.9 (square roots by
  `sqrtBracket`, `isEncl0_sqrtBracket`).
* "`arctan x₄ = 0.09160…`" (`dlmf_4_45_12_arctan`): `arctan` lies between the partial sums
  `S₄`, `S₅` of 4.24.3 (`arctan_alternating_bounds`, alternating series), evaluated on the
  enclosure of `x₄`.
* 4.45.13 `dlmf_4_45_13`: `arctan x = 16 arctan x₄ = 1.46563…`.
* 4.45.14 `dlmf_4_45_14`: `½π = 1.57079…`, `1/x = 0.10555…`, `1/(3x³) = 0.00039…`, and the series
  of 4.45.11 sums to `arctan x − ½π`.
* "`½ ln 10 = 1.15…`", "`½π = 1.57…`" (`dlmf_4_45_i_constants`), from the brackets `ln10Bracket`
  and `piBracket`.
-/

namespace Azurite.DLMF

open Azurite.AzFloat Encl
open scoped Real

/-! ### The enclosures (working precision `w`) -/

/-- `x = 9.47376`. -/
def e45X0 (w : Nat) : Encl := Encl.div w (nat 947376) (nat 100000)

/-- The step `t ↦ t/(1 + (1 + t²)^{1/2})` of 4.45.9. -/
def e45Step (w : Nat) (a : Encl) : Encl :=
  Encl.div w a (Encl.add w (exact one) (sqrtBracket (Encl.add w (exact one) (Encl.mul w a a)) w))

/-- `xₙ` of 4.45.12. -/
def e45X (w : Nat) : Nat → Encl
  | 0 => e45X0 w
  | n + 1 => e45Step w (e45X w n)

/-- `t^{2k+1}/(2k+1)` on an enclosure. -/
def e45Term (w : Nat) (a : Encl) : Nat → Encl
  | 0 => a
  | k + 1 => Encl.div w (Encl.mul w (Encl.mul w (e45Term w a k) (nat (2 * k + 1))) (Encl.mul w a a))
      (nat (2 * k + 3))

/-- `t − t³/3 + t⁵/5 − t⁷/7` at `t = x₄`. -/
def e45S4 (w : Nat) : Encl :=
  let a := e45X w 4
  Encl.sub w (Encl.add w (Encl.sub w (e45Term w a 0) (e45Term w a 1)) (e45Term w a 2))
    (e45Term w a 3)

/-- `t − t³/3 + t⁵/5 − t⁷/7 + t⁹/9` at `t = x₄`. -/
def e45S5 (w : Nat) : Encl := Encl.add w (e45S4 w) (e45Term w (e45X w 4) 4)

/-- `½π`, `1/x`, `1/(3x³)`, `½ ln 10`. -/
def e45HalfPi (w : Nat) : Encl := Encl.div w (Encl.pi w) (nat 2)
def e45InvX (w : Nat) : Encl := Encl.div w (exact one) (e45X0 w)
def e45Third (w : Nat) : Encl :=
  Encl.div w (exact one) (Encl.mul w (nat 3) (Encl.pow w (e45X0 w) 3))
def e45HalfLn10 (w : Nat) : Encl := Encl.div w (ln10Bracket w) (nat 2)

/-! ### The kernel computations -/

set_option maxRecDepth 100000 in
theorem e45X1_data :
    (valData (e45X 64 1).1, valData (e45X 64 1).2) =
      (some (true, 4150520902075770847, 4611686018427387904),
        some (true, 16602083608303083393, 18446744073709551616)) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem e45X2_data :
    (valData (e45X 64 2).1, valData (e45X 64 2).2) =
      (some (true, 3539342149425208043, 9223372036854775808),
        some (true, 14157368597700832179, 36893488147419103232)) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem e45X3_data :
    (valData (e45X 64 3).1, valData (e45X 64 3).2) =
      (some (true, 6835678642541460903, 36893488147419103232),
        some (true, 1708919660635365227, 9223372036854775808)) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem e45X4_data :
    (valData (e45X 64 4).1, valData (e45X 64 4).2) =
      (some (true, 13555997307737914861, 147573952589676412928),
        some (true, 13555997307737914875, 147573952589676412928)) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem e45HalfPi_data :
    (valData (e45HalfPi 64).1, valData (e45HalfPi 64).2) =
      (some (true, 3622009729038561421, 2305843009213693952),
        some (true, 14488038916154245685, 9223372036854775808)) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem e45InvX_data :
    (valData (e45InvX 64).1, valData (e45InvX 64).2) =
      (some (true, 3894281483531259313, 36893488147419103232),
        some (true, 7788562967062518627, 73786976294838206464)) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem e45Third_data :
    (valData (e45Third 64).1, valData (e45Third 64).2) =
      (some (true, 14810212318865944169, 37778931862957161709568),
        some (true, 925638269929121511, 2361183241434822606848)) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem e45HalfLn10_data :
    (valData (e45HalfLn10 64).1, valData (e45HalfLn10 64).2) =
      (some (true, 1327349934949994287, 1152921504606846976),
        some (true, 10618799479599967337, 9223372036854775808)) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem e45S4_data :
    valData (e45S4 64).1 = some (true, 105609846337198531, 1152921504606846976) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem e45S5_data :
    valData (e45S5 64).2 = some (true, 13518060338797362055, 147573952589676412928) := by
  decide +kernel


/-! ### Soundness -/

section Soundness

instance : NeZero (64 : ℕ) := ⟨by norm_num⟩

private theorem hw64' : 2 ≤ 64 := by norm_num

theorem isEncl0_of_eq' {a : Encl} {x y : ℝ} (h : IsEncl0 a x) (e : x = y) : IsEncl0 a y := e ▸ h

theorem isEncl_of_eq' {a : Encl} {x y : ℝ} (h : IsEncl a x) (e : x = y) : IsEncl a y := e ▸ h

/-- The outward-rounded square root of an enclosure encloses the square root. -/
theorem isEncl0_sqrtBracket {w : ℕ} [NeZero w] {a : Encl} {M : ℝ} (ha : IsEncl0 a M) :
    IsEncl0 (sqrtBracket a w) (√M) := by
  obtain ⟨l, h, hl, hh, h0, h1, h2⟩ := ha
  obtain ⟨r1, hr1, hf⟩ := sqrtFloor_err hl h0 w
  obtain ⟨r2, hr2, hc⟩ := sqrtCeiling_err hh (h0.trans (h1.trans h2)) w
  exact ⟨r1, r2, hr1, hr2, hf.1, hf.2.1.trans (Real.sqrt_le_sqrt h1),
    (Real.sqrt_le_sqrt h2).trans hc.1⟩

/-- `x = 9.47376`. -/
noncomputable def e45x : ℝ := 947376 / 100000

theorem e45X0_encl : IsEnclPos (e45X0 64) e45x := by
  have h := (enclosesPos_nat (n := 947376) (by norm_num)).div hw64'
    (enclosesPos_nat (n := 100000) (by norm_num))
  exact (by push_cast at h; exact h : IsEnclPos (e45X0 64) ((947376 : ℝ) / 100000))

theorem e45Step_encl {a : Encl} {t : ℝ} (ha : IsEncl0 a t) :
    IsEncl0 (e45Step 64 a) (t / (1 + √(1 + t ^ 2))) := by
  have h1 := enclosesPos_one.add hw64' (ha.mul (w := 64) ha)
  have h2 := enclosesPos_one.add hw64' (isEncl0_sqrtBracket (w := 64) h1.encloses0)
  exact isEncl0_of_eq' (ha.div (w := 64) h2) (by rw [sq])

theorem e45X_encl (n : ℕ) : IsEncl0 (e45X 64 n) (arctanSeq e45x n) := by
  induction n with
  | zero => exact e45X0_encl.encloses0
  | succ n ih => exact e45Step_encl ih

/-- `t^{2k+1}/(2k+1)`. -/
noncomputable def e45f (t : ℝ) (k : ℕ) : ℝ := t ^ (2 * k + 1) / (2 * k + 1)

theorem e45Term_encl {a : Encl} {t : ℝ} (ha : IsEncl0 a t) (k : ℕ) :
    IsEncl0 (e45Term 64 a k) (e45f t k) := by
  induction k with
  | zero => exact isEncl0_of_eq' ha (by simp [e45f])
  | succ k ih =>
    have h := ((ih.mul (w := 64) (enclosesPos_nat (n := 2 * k + 1) (by omega)).encloses0).mul
      (w := 64) (ha.mul (w := 64) ha)).div (w := 64) (enclosesPos_nat (n := 2 * k + 3) (by omega))
    refine isEncl0_of_eq' h ?_
    simp only [e45f]
    push_cast
    have : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring

/-- The partial sums `∑_{k<n} (−1)ᵏ t^{2k+1}/(2k+1)` bracket `arctan t` (`0 ≤ t < 1`). -/
theorem arctan_alternating_bounds {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) (k : ℕ) :
    ∑ i ∈ Finset.range (2 * k), (-1) ^ i * e45f t i ≤ Real.arctan t ∧
      Real.arctan t ≤ ∑ i ∈ Finset.range (2 * k + 1), (-1) ^ i * e45f t i := by
  have hz : ‖(t : ℂ)‖ < 1 := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
  have h := Complex.hasSum_arctan hz
  rw [← Complex.ofReal_arctan] at h
  have h' : HasSum (fun n : ℕ => (((-1) ^ n * e45f t n : ℝ) : ℂ)) ((Real.arctan t : ℝ) : ℂ) := by
    convert h using 1; funext n; simp only [e45f]; push_cast; ring
  have hs := (Complex.hasSum_ofReal.mp h').tendsto_sum_nat
  have ha : Antitone (e45f t) := antitone_nat_of_succ_le fun n => by
    simp only [e45f]
    have hp : t ^ (2 * (n + 1) + 1) ≤ t ^ (2 * n + 1) :=
      pow_le_pow_of_le_one h0 h1.le (by omega)
    have hd : (2 * (n : ℝ) + 1) ≤ 2 * ((n + 1 : ℕ) : ℝ) + 1 := by push_cast; linarith
    exact div_le_div₀ (pow_nonneg h0 _) hp (by positivity) hd
  exact ⟨ha.alternating_series_le_tendsto hs k, ha.tendsto_le_alternating_series hs k⟩

theorem e45S4_encl {a : Encl} {t : ℝ} (ha : IsEncl0 a t) :
    IsEncl (Encl.sub 64 (Encl.add 64 (Encl.sub 64 (e45Term 64 a 0) (e45Term 64 a 1))
      (e45Term 64 a 2)) (e45Term 64 a 3))
      (∑ i ∈ Finset.range (2 * 2), (-1) ^ i * e45f t i) := by
  have T := fun k => (e45Term_encl ha k).encloses
  refine isEncl_of_eq' ((((T 0).sub (w := 64) (T 1)).add (w := 64) (T 2)).sub (w := 64) (T 3)) ?_
  simp [Finset.sum_range_succ]; ring

theorem e45S5_encl {a : Encl} {t : ℝ} (ha : IsEncl0 a t) :
    IsEncl (Encl.add 64 (Encl.sub 64 (Encl.add 64 (Encl.sub 64 (e45Term 64 a 0) (e45Term 64 a 1))
      (e45Term 64 a 2)) (e45Term 64 a 3)) (e45Term 64 a 4))
      (∑ i ∈ Finset.range (2 * 2 + 1), (-1) ^ i * e45f t i) := by
  refine isEncl_of_eq' ((e45S4_encl ha).add (w := 64) (e45Term_encl ha 4).encloses) ?_
  simp [Finset.sum_range_succ]; ring

end Soundness

/-! ### The claims -/

theorem isEncl_lower_of_data {a : Encl} {x : ℝ} (h : IsEncl a x) {s : Bool} {n d : ℕ}
    (h₁ : valData a.1 = some (s, n, d)) : signedVal s n d ≤ x := by
  obtain ⟨l, u, hl, -, h1, -⟩ := h
  rw [toVal_of_valData h₁] at hl
  exact (EReal.coe_injective (Option.some_injective _ hl)) ▸ h1

theorem isEncl_upper_of_data {a : Encl} {x : ℝ} (h : IsEncl a x) {s : Bool} {n d : ℕ}
    (h₂ : valData a.2 = some (s, n, d)) : x ≤ signedVal s n d := by
  obtain ⟨l, u, -, hu, -, h2⟩ := h
  rw [toVal_of_valData h₂] at hu
  exact (EReal.coe_injective (Option.some_injective _ hu)) ▸ h2

/-- **DLMF 4.45.12**: for `x = 9.47376`, `x₁ = 0.90000…`, `x₂ = 0.38373…`, `x₃ = 0.18528…`,
`x₄ = 0.09185…` (truncated decimals). -/
theorem dlmf_4_45_12 :
    (0.90000 : ℝ) ≤ arctanSeq e45x 1 ∧ arctanSeq e45x 1 < 0.90001 ∧
      (0.38373 : ℝ) ≤ arctanSeq e45x 2 ∧ arctanSeq e45x 2 < 0.38374 ∧
      (0.18528 : ℝ) ≤ arctanSeq e45x 3 ∧ arctanSeq e45x 3 < 0.18529 ∧
      (0.09185 : ℝ) ≤ arctanSeq e45x 4 ∧ arctanSeq e45x 4 < 0.09186 := by
  obtain ⟨a1, b1⟩ := Prod.mk.inj e45X1_data
  obtain ⟨a2, b2⟩ := Prod.mk.inj e45X2_data
  obtain ⟨a3, b3⟩ := Prod.mk.inj e45X3_data
  obtain ⟨a4, b4⟩ := Prod.mk.inj e45X4_data
  obtain ⟨l1, u1⟩ := (e45X_encl 1).encloses.bounds a1 b1
  obtain ⟨l2, u2⟩ := (e45X_encl 2).encloses.bounds a2 b2
  obtain ⟨l3, u3⟩ := (e45X_encl 3).encloses.bounds a3 b3
  obtain ⟨l4, u4⟩ := (e45X_encl 4).encloses.bounds a4 b4
  norm_num [signedVal] at l1 u1 l2 u2 l3 u3 l4 u4
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- "From (4.24.3) `arctan x₄ = 0.09160…`". -/
theorem dlmf_4_45_12_arctan :
    (0.09160 : ℝ) ≤ Real.arctan (arctanSeq e45x 4) ∧ Real.arctan (arctanSeq e45x 4) < 0.09161 ∧
      (1.46563 : ℝ) ≤ 16 * Real.arctan (arctanSeq e45x 4) ∧
      16 * Real.arctan (arctanSeq e45x 4) < 1.46564 := by
  obtain ⟨a4, b4⟩ := Prod.mk.inj e45X4_data
  obtain ⟨l4, u4⟩ := (e45X_encl 4).encloses.bounds a4 b4
  norm_num [signedVal] at l4 u4
  obtain ⟨hlo, hhi⟩ := arctan_alternating_bounds (t := arctanSeq e45x 4) (by linarith)
    (by linarith) 2
  have hS4 := isEncl_lower_of_data (e45S4_encl (e45X_encl 4)) e45S4_data
  have hS5 := isEncl_upper_of_data (e45S5_encl (e45X_encl 4)) e45S5_data
  norm_num [signedVal] at hS4 hS5
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- **DLMF 4.45.13**: `arctan x = 16 arctan x₄ = 1.46563…` (`x = 9.47376`). -/
theorem dlmf_4_45_13 :
    Real.arctan e45x = 16 * Real.arctan (arctanSeq e45x 4) ∧
      (1.46563 : ℝ) ≤ Real.arctan e45x ∧ Real.arctan e45x < 1.46564 := by
  have h := (dlmf_4_45_9_10 e45x).1 4
  norm_num at h
  obtain ⟨-, -, h3, h4⟩ := dlmf_4_45_12_arctan
  exact ⟨h, by rw [h]; exact h3, by rw [h]; exact h4⟩

/-- **DLMF 4.45.14**: the check by 4.45.11, `arctan x = 1.57079… − 0.10555… + 0.00039… − ⋯
= 1.46563…`: the terms `½π`, `1/x`, `1/(3x³)` to 5D (truncated), and the sum of the series
(`dlmf_4_45_11`) is `arctan x − ½π`. -/
theorem dlmf_4_45_14 :
    ((1.57079 : ℝ) ≤ π / 2 ∧ π / 2 < 1.57080) ∧ ((0.10555 : ℝ) ≤ 1 / e45x ∧ 1 / e45x < 0.10556) ∧
      ((0.00039 : ℝ) ≤ 1 / (3 * e45x ^ 3) ∧ 1 / (3 * e45x ^ 3) < 0.00040) ∧
      HasSum (fun k : ℕ => (-1) ^ (k + 1) / ((2 * k + 1) * e45x ^ (2 * k + 1)))
        (Real.arctan e45x - π / 2) := by
  have hpi := (enclosesPos_pi (w := 64) (by norm_num)).div hw64'
    (enclosesPos_nat (n := 2) (by norm_num))
  have hinv := enclosesPos_one.div hw64' e45X0_encl
  have hthird := enclosesPos_one.div hw64'
    ((enclosesPos_nat (n := 3) (by norm_num)).mul hw64' (e45X0_encl.pow hw64' 3))
  obtain ⟨a1, b1⟩ := Prod.mk.inj e45HalfPi_data
  obtain ⟨a2, b2⟩ := Prod.mk.inj e45InvX_data
  obtain ⟨a3, b3⟩ := Prod.mk.inj e45Third_data
  obtain ⟨l1, u1⟩ := hpi.encloses0.encloses.bounds a1 b1
  obtain ⟨l2, u2⟩ := hinv.encloses0.encloses.bounds a2 b2
  obtain ⟨l3, u3⟩ := hthird.encloses0.encloses.bounds a3 b3
  push_cast at l1 u1 l3 u3
  norm_num [signedVal] at l1 u1 l2 u2 l3 u3
  have e2 : 1 / e45x = e45x⁻¹ := one_div _
  have e3 : 1 / (3 * e45x ^ 3) = (e45x ^ 3)⁻¹ * (1 / 3) := by ring
  rw [e2, e3]
  refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩,
    ?_⟩
  exact dlmf_4_45_11 (by norm_num [e45x])

/-- "`|y| ≤ ½ ln 10 = 1.15…`" (4.45.5) and "`|θ| ≤ ½π = 1.57…`" (4.45.7). -/
theorem dlmf_4_45_i_constants :
    ((1.15 : ℝ) ≤ 1 / 2 * Real.log 10 ∧ 1 / 2 * Real.log 10 < 1.16) ∧
      ((1.57 : ℝ) ≤ π / 2 ∧ π / 2 < 1.58) := by
  obtain ⟨lv, hv, hl, hh, h2, hlo, hhi, -⟩ := ln10Bracket_spec (w := 64) le_rfl
  have hln : IsEnclPos (ln10Bracket 64) (Real.log 10) := ⟨lv, hv, hl, hh, by linarith, hlo, hhi⟩
  have hhalf := hln.div hw64' (enclosesPos_nat (n := 2) (by norm_num))
  obtain ⟨a1, b1⟩ := Prod.mk.inj e45HalfLn10_data
  obtain ⟨l1, u1⟩ := hhalf.encloses0.encloses.bounds a1 b1
  norm_num [signedVal] at l1 u1
  obtain ⟨⟨p1, p2⟩, -⟩ := dlmf_4_45_14
  refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

end Azurite.DLMF
