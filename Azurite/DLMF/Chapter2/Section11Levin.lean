/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section11Euler
import Azurite.DLMF.Chapter1.Section9Series

/-!
# DLMF §2.11(vi): Levin's transformation of the expansion of `W_{κ,μ}(z)`

* **2.11.30** (`whitA`): the terms `a_n` of the expansion 2.11.29 of the Whittaker function.
  * At `z = 1`, `κ = 2.3`, `μ = 0.5`, `a_n = e^{−1/2} r_n` with exact rationals `r_n`
    (`whitR`, `whitA_example`).
* **2.11.32** (`levinD`): Levin's transformation, over any field. It is homogeneous
  (`levinD_const_mul`), so `d_n = e^{−1/2} · d_n(r)` (`levinD_example`), and likewise for the
  partial sums `s_n` (`partialSum_example`).
* **Table 2.11.1** (`dlmf_table_2_11_1_a`, `dlmf_table_2_11_1_s`, `dlmf_table_2_11_1_d`): all 33
  entries to 8D.
  * The rationals are evaluated exactly in the kernel and multiplied by the `AzFloat` enclosure of
    `e^{−1/2}` at 64 bits (`halfEncl`, sound by `isEncl_halfEncl`).
  * Both ends of every enclosure round to DLMF's value.
* The claims in the text, compared with the value `−0.83299 50268 27526` quoted in 2.11.31:
  * the numerically smallest term is `a₅` (`dlmf_2_11_vi_smallest_a`);
  * `s₄` is "correct to almost 3D": the error is between `0.0029` and `0.003`
    (`dlmf_2_11_vi_s4`);
  * `d₁₀` has 8 correct decimals (`dlmf_2_11_vi_d10`);
  * `d₂₀ = −0.83299 50268 27501 4` agrees to 13D (`dlmf_2_11_vi_d20`, `levin_d20_decimals`).

DEFERRED: the expansion 2.11.29 itself (§13.19) and the value 2.11.31 of `W_{2.3,0.5}(1)`, which
need the Whittaker functions of Chapter 13. The cautionary remarks on Stokes lines are not
formalized.
-/

open Filter Topology Set
open scoped Real

namespace Azurite.DLMF

/-! ### The terms 2.11.30 and Levin's transformation 2.11.32 -/

/-- **DLMF 2.11.30** (`z > 0`): `a_n = e^{−z/2}/(z^{n−κ} n!) ∏_{k=1}^{n} (μ² − (κ − k + ½)²)`. -/
noncomputable def whitA (κ μ z : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-z / 2) / (z ^ ((n : ℝ) - κ) * n.factorial) *
    ∏ k ∈ Finset.Icc 1 n, (μ ^ 2 - (κ - k + 1 / 2) ^ 2)

/-- The weights `(−1)^j C(n, j) (j + 1)^{n−1}` of 2.11.32. -/
def levinW {K : Type*} [Field K] (n j : ℕ) : K :=
  (-1) ^ j * (n.choose j : K) * ((j : K) + 1) ^ ((n : ℤ) - 1)

/-- **DLMF 2.11.32**, the variant of Levin's transformation:
`d_n = ∑_j w_{n,j} s_j/a_{j+1} / ∑_j w_{n,j}/a_{j+1}`. -/
def levinD {K : Type*} [Field K] (a : ℕ → K) (n : ℕ) : K :=
  (∑ j ∈ Finset.range (n + 1), levinW n j * partialSum a j / a (j + 1)) /
    (∑ j ∈ Finset.range (n + 1), levinW n j / a (j + 1))

theorem partialSum_const_mul {K : Type*} [Field K] (c : K) (a : ℕ → K) (n : ℕ) :
    partialSum (fun i => c * a i) n = c * partialSum a n := by
  simp [partialSum, Finset.mul_sum]

/-- The transformation is homogeneous: `d_n(ca) = c d_n(a)`. -/
theorem levinD_const_mul {K : Type*} [Field K] {c : K} (hc : c ≠ 0) (a : ℕ → K) (n : ℕ) :
    levinD (fun i => c * a i) n = c * levinD a n := by
  unfold levinD
  simp only [partialSum_const_mul]
  have h1 : ∀ j, levinW n j * (c * partialSum a j) / (c * a (j + 1)) =
      levinW n j * partialSum a j / a (j + 1) := fun j => by
    rw [mul_left_comm, mul_div_mul_left _ _ hc]
  have h2 : ∀ j, levinW n j / (c * a (j + 1)) = c⁻¹ * (levinW n j / a (j + 1)) := fun j => by
    rw [div_mul_eq_div_div_swap, div_eq_mul_inv _ c, mul_comm]
  simp only [h1, h2, ← Finset.mul_sum]
  rw [div_mul_eq_div_div_swap, div_inv_eq_mul, mul_comm]

theorem levinD_cast (a : ℕ → ℚ) (n : ℕ) :
    ((levinD a n : ℚ) : ℝ) = levinD (fun i => (a i : ℝ)) n := by
  simp [levinD, levinW, partialSum]

theorem partialSum_cast (a : ℕ → ℚ) (n : ℕ) :
    ((partialSum a n : ℚ) : ℝ) = partialSum (fun i => (a i : ℝ)) n := by
  simp [partialSum]

/-! ### The example `z = 1`, `κ = 2.3`, `μ = 0.5` -/

/-- `a_n = e^{−1/2} r_n` with `r_n = ∏_{k=1}^{n} (¼ − (2.8 − k)²)/n!`. -/
def whitR (n : ℕ) : ℚ :=
  (∏ k ∈ Finset.Icc 1 n, ((1 / 2 : ℚ) ^ 2 - (23 / 10 - k + 1 / 2) ^ 2)) / n.factorial

theorem whitA_example (n : ℕ) : whitA 2.3 0.5 1 n = Real.exp (-(1 / 2)) * (whitR n : ℝ) := by
  simp only [whitA, Real.one_rpow, one_mul, whitR]
  push_cast
  norm_num
  ring

/-! ### The AzFloat computation of Table 2.11.1 -/

section Numerics

open Azurite.AzFloat Encl

/-- `e^{−1/2}`. -/
def eHalf (w : Nat) : Encl := Encl.exp w (-oneHalf)

/-- The enclosure of `e^{−1/2} q` for a rational `q ≠ 0`. -/
def halfEncl (w : Nat) (q : ℚ) : Encl :=
  if 0 ≤ q then Encl.mul w (eHalf w) (ratEncl w q)
  else Encl.neg (Encl.mul w (eHalf w) (ratEncl w (-q)))

/-- The two ends of `e^{−1/2} q` to `k` decimals. -/
def halfDecimals (q : ℚ) (k : Nat) : Option String × Option String :=
  (toDecimalPlaces (halfEncl 64 q).1 k, toDecimalPlaces (halfEncl 64 q).2 k)

set_option maxRecDepth 100000 in
/-- **Table 2.11.1**, column `a_n` (8D): both ends of every enclosure. -/
theorem dlmf_table_2_11_1_a :
    (List.range 11).map (fun n => halfDecimals (whitR n) 8) =
      [(some "0.60653066", some "0.60653066"), (some "-1.81352667", some "-1.81352667"),
        (some "0.35363770", some "0.35363770"), (some "0.02475464", some "0.02475464"),
        (some "-0.00736451", some "-0.00736451"), (some "0.00676062", some "0.00676062"),
        (some "-0.01125643", some "-0.01125643"), (some "0.02796418", some "0.02796418"),
        (some "-0.09364504", some "-0.09364504"), (some "0.39736710", some "0.39736710"),
        (some "-2.05001686", some "-2.05001686")] := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **Table 2.11.1**, column `s_n` (8D). -/
theorem dlmf_table_2_11_1_s :
    (List.range 11).map (fun n => halfDecimals (partialSum whitR n) 8) =
      [(some "0.60653066", some "0.60653066"), (some "-1.20699601", some "-1.20699601"),
        (some "-0.85335831", some "-0.85335831"), (some "-0.82860367", some "-0.82860367"),
        (some "-0.83596818", some "-0.83596818"), (some "-0.82920756", some "-0.82920756"),
        (some "-0.84046399", some "-0.84046399"), (some "-0.81249981", some "-0.81249981"),
        (some "-0.90614485", some "-0.90614485"), (some "-0.50877775", some "-0.50877775"),
        (some "-2.55879461", some "-2.55879461")] := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **Table 2.11.1**, column `d_n` (8D). -/
theorem dlmf_table_2_11_1_d :
    (List.range 11).map (fun n => halfDecimals (levinD whitR n) 8) =
      [(some "0.60653066", some "0.60653066"), (some "-0.91106488", some "-0.91106488"),
        (some "-0.82413405", some "-0.82413405"), (some "-0.83323429", some "-0.83323429"),
        (some "-0.83303750", some "-0.83303750"), (some "-0.83298901", some "-0.83298901"),
        (some "-0.83299429", some "-0.83299429"), (some "-0.83299530", some "-0.83299530"),
        (some "-0.83299504", some "-0.83299504"), (some "-0.83299501", some "-0.83299501"),
        (some "-0.83299503", some "-0.83299503")] := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- `d₂₀` to 16D: `−0.83299 50268 27501 4`. -/
theorem levin_d20_decimals :
    halfDecimals (levinD whitR 20) 16 =
      (some "-0.8329950268275014", some "-0.8329950268275014") := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem levin_s4_data :
    (valData (halfEncl 64 (partialSum whitR 4)).1, valData (halfEncl 64 (partialSum whitR 4)).2) =
      (some (false, 15420891028329659133, 18446744073709551616),
        some (false, 3855222757082414781, 4611686018427387904)) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem levin_d10_data :
    (valData (halfEncl 64 (levinD whitR 10)).1, valData (halfEncl 64 (levinD whitR 10)).2) =
      (some (false, 3841511519908868673, 4611686018427387904),
        some (false, 3841511519908868671, 4611686018427387904)) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem levin_d20_data :
    (valData (halfEncl 64 (levinD whitR 20)).1, valData (halfEncl 64 (levinD whitR 20)).2) =
      (some (false, 15366046074559740841, 18446744073709551616),
        some (false, 480188939829991901, 576460752303423488)) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem levin_nonzero : partialSum whitR 4 ≠ 0 ∧ levinD whitR 10 ≠ 0 ∧ levinD whitR 20 ≠ 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem whitR_smallest : ∀ n < 11, n ≠ 5 → |whitR 5| < |whitR n| := by
  decide +kernel

/-! #### Soundness -/

theorem eHalf_encl : IsEncl0 (eHalf 64) (Real.exp (-(1 / 2))) := by
  have hx : (-oneHalf).toVal = some ((-(1 / 2) : ℝ) : EReal) := by
    rw [toVal_neg, toVal_oneHalf]; simp
  exact encloses0_exp hx (by norm_num)

theorem isEncl_halfEncl {q : ℚ} (hq : q ≠ 0) :
    IsEncl (halfEncl 64 q) (Real.exp (-(1 / 2)) * q) := by
  unfold halfEncl
  rcases lt_or_gt_of_ne hq with h | h
  · simp only [show ¬ (0 : ℚ) ≤ q from not_le.mpr h, ↓reduceIte]
    have h1 := IsEncl0.mul (w := 64) eHalf_encl
      (IsEnclPos.encloses0 (isEnclPos_ratEncl (neg_pos.mpr h)))
    refine isEncl_of_eq (IsEncl.neg (IsEncl0.encloses h1)) ?_
    push_cast; ring
  · simp only [h.le, ↓reduceIte]
    exact IsEncl0.encloses (IsEncl0.mul (w := 64) eHalf_encl
      (IsEnclPos.encloses0 (isEnclPos_ratEncl h)))

/-! #### The claims -/

theorem whitA_example_fun : whitA 2.3 0.5 1 = fun n => Real.exp (-(1 / 2)) * (whitR n : ℝ) :=
  funext whitA_example

theorem partialSum_example (n : ℕ) :
    partialSum (whitA 2.3 0.5 1) n = Real.exp (-(1 / 2)) * ((partialSum whitR n : ℚ) : ℝ) := by
  rw [whitA_example_fun, partialSum_const_mul, partialSum_cast]

theorem levinD_example (n : ℕ) :
    levinD (whitA 2.3 0.5 1) n = Real.exp (-(1 / 2)) * ((levinD whitR n : ℚ) : ℝ) := by
  rw [whitA_example_fun, levinD_const_mul (Real.exp_pos _).ne', levinD_cast]

/-- "Optimum truncation occurs just prior to the numerically smallest term, that is, at `s₄`":
`|a₅| < |a_n|` for every other `n ≤ 10`. -/
theorem dlmf_2_11_vi_smallest_a :
    ∀ n < 11, n ≠ 5 → |whitA 2.3 0.5 1 5| < |whitA 2.3 0.5 1 n| := by
  intro n hn h5
  rw [whitA_example, whitA_example, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
  have := whitR_smallest n hn h5
  have h' : |(whitR 5 : ℝ)| < |(whitR n : ℝ)| := by
    rw [← Rat.cast_abs, ← Rat.cast_abs]; exact_mod_cast this
  exact mul_lt_mul_of_pos_left h' (Real.exp_pos _)

/-- **"This direct estimate is correct to almost 3D"**: `s₄` differs from the value
`−0.83299 50268 27526` of 2.11.31 by between `0.0029` and `0.003`. -/
theorem dlmf_2_11_vi_s4 :
    0.0029 < |partialSum (whitA 2.3 0.5 1) 4 - (-0.832995026827526)| ∧
      |partialSum (whitA 2.3 0.5 1) 4 - (-0.832995026827526)| < 0.003 := by
  obtain ⟨d1, d2⟩ := Prod.mk.inj levin_s4_data
  obtain ⟨l, u⟩ := IsEncl.bounds (isEncl_halfEncl levin_nonzero.1) d1 d2
  rw [partialSum_example]
  norm_num [signedVal] at l u
  rw [abs_of_neg (by linarith)]
  constructor <;> linarith

/-- **"By `n = 10` we already have 8 correct decimals"**. -/
theorem dlmf_2_11_vi_d10 :
    |levinD (whitA 2.3 0.5 1) 10 - (-0.832995026827526)| < 0.000000005 := by
  obtain ⟨d1, d2⟩ := Prod.mk.inj levin_d10_data
  obtain ⟨l, u⟩ := IsEncl.bounds (isEncl_halfEncl levin_nonzero.2.1) d1 d2
  rw [levinD_example]
  norm_num [signedVal] at l u
  exact abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩

/-- **"`d₂₀` is found to agree with (2.11.31) to 13D"** (exact rational arithmetic and AzFloat in
place of double precision). -/
theorem dlmf_2_11_vi_d20 :
    |levinD (whitA 2.3 0.5 1) 20 - (-0.832995026827526)| < 0.00000000000005 := by
  obtain ⟨d1, d2⟩ := Prod.mk.inj levin_d20_data
  obtain ⟨l, u⟩ := IsEncl.bounds (isEncl_halfEncl levin_nonzero.2.2) d1 d2
  rw [levinD_example]
  norm_num [signedVal] at l u
  exact abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩

end Numerics

end Azurite.DLMF
