/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section7
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# DLMF §2.7(iv): Numerically Satisfactory Solutions, 2.7.35–2.7.37

* 2.7.35 (`isODESolution_exp`, …, `isODESolution_sinh`): `w₁ = e^z`, `w₂ = e^{−z}`, `w₃ = cosh z`,
  `w₄ = sinh z` solve `w″ = w` in `ℂ`; `wronskian_exp_pair = −2`, `wronskian_cosh_sinh = 1`.
* 2.7.36, 2.7.37 (`dlmf_2_7_36`, `dlmf_2_7_37`): both pairs are fundamental — every solution is
  `A e^z + B e^{−z}` and `C cosh z + D sinh z` (via §1.13 on the simply-connected domain `ℂ`,
  `isSCDomain_univ`); `exp_pair_eq_cosh_sinh` converts (`C = A + B`, `D = A − B`).
* Cancellation (`cancelRatio u v = |u + v| / (|u| + |v|)`, the fraction of the size of the terms
  that survives in the sum): for `C = D ≠ 0` the combination `C w₃ + D w₄` cancels severely as
  `ℜz → −∞` (`cosh_sinh_cancel`, ratio `→ 0`), while for `w₁, w₂` no cancellation occurs as
  `ℜz → ±∞` (`exp_pair_no_cancel_atBot/atTop`, ratio `→ 1` for every `(A, B) ≠ (0, 0)`).
* `w₁`, `w₂` are recessive and dominant as `ℜz → −∞`, and vice versa as `ℜz → +∞`
  (`exp_recessive_atBot`, `exp_neg_recessive_atTop`).

The remaining statements of §2.7(iv) (one member recessive near a singularity; the oscillatory
notion "same amplitude, ½π out of phase") are descriptive and are not formalized.
-/

open Filter Topology Set Complex

namespace Azurite.DLMF

/-! ### The domain `ℂ` -/

/-- `ℂ` is a simply-connected domain in the sense of §1.13(i): its complement in `ℂ ∪ {∞}` is
`{∞}`. -/
theorem isSCDomain_univ : IsSCDomain (univ : Set ℂ) where
  isOpen := isOpen_univ
  isConnected := isConnected_univ
  simplyConnected := by
    rw [IsSimplyConnectedDLMF, image_univ, OnePoint.compl_range_coe]
    exact isConnected_singleton

/-! ### 2.7.35: the four solutions -/

/-- **DLMF 2.7.35**: `w″ = w`, i.e. `w″ + 0·w′ + (−1) w = 0`. -/
abbrev IsSolW (w : ℂ → ℂ) : Prop := IsODESolution univ (fun _ => 0) (fun _ => -1) w

theorem isSolW_of_hasDerivAt {w w' : ℂ → ℂ} (h1 : ∀ z, HasDerivAt w (w' z) z)
    (h2 : ∀ z, HasDerivAt w' (w z) z) : IsSolW w :=
  isODESolution_of_hasDerivAt isOpen_univ fun z _ => ⟨h1 z, by simpa using h2 z⟩

theorem isODESolution_exp : IsSolW Complex.exp :=
  isSolW_of_hasDerivAt (w' := Complex.exp) (fun z => hasDerivAt_exp z) fun z => hasDerivAt_exp z

theorem hasDerivAt_exp_neg (z : ℂ) :
    HasDerivAt (fun z => Complex.exp (-z)) (-Complex.exp (-z)) z := by
  have := (hasDerivAt_exp (-z)).comp z (hasDerivAt_neg z)
  convert this using 1 <;> first | rfl | ring

theorem isODESolution_exp_neg : IsSolW fun z => Complex.exp (-z) :=
  isSolW_of_hasDerivAt (w' := fun z => -Complex.exp (-z)) hasDerivAt_exp_neg fun z => by
    have := (hasDerivAt_exp_neg z).neg
    convert this using 1
    ring

theorem isODESolution_cosh : IsSolW Complex.cosh :=
  isSolW_of_hasDerivAt (w' := Complex.sinh) (fun z => hasDerivAt_cosh z)
    fun z => hasDerivAt_sinh z

theorem isODESolution_sinh : IsSolW Complex.sinh :=
  isSolW_of_hasDerivAt (w' := Complex.cosh) (fun z => hasDerivAt_sinh z)
    fun z => hasDerivAt_cosh z

theorem wronskian_exp_pair (z : ℂ) :
    wronskian Complex.exp (fun z => Complex.exp (-z)) z = -2 := by
  rw [wronskian, (hasDerivAt_exp_neg z).deriv, Complex.deriv_exp]
  have : Complex.exp (-z) * Complex.exp z = 1 := by rw [← Complex.exp_add]; simp
  linear_combination (-2 : ℂ) * this

theorem wronskian_cosh_sinh (z : ℂ) : wronskian Complex.cosh Complex.sinh z = 1 := by
  rw [wronskian, (hasDerivAt_sinh z).deriv, (hasDerivAt_cosh z).deriv]
  linear_combination Complex.cosh_sq_sub_sinh_sq z

/-! ### 2.7.36, 2.7.37 -/

/-- **DLMF 2.7.36**: every solution of `w″ = w` is `w(z) = A e^z + B e^{−z}`. -/
theorem dlmf_2_7_36 :
    IsFundamentalPair univ (fun _ => 0) (fun _ => -1) Complex.exp fun z => Complex.exp (-z) :=
  isFundamentalPair_of_wronskian_ne_zero isSCDomain_univ (differentiableOn_const 0)
    (differentiableOn_const (-1)) (mem_univ 0) isODESolution_exp isODESolution_exp_neg
    (by rw [wronskian_exp_pair]; norm_num)

/-- **DLMF 2.7.37**: every solution of `w″ = w` is `w(z) = C cosh z + D sinh z`. -/
theorem dlmf_2_7_37 :
    IsFundamentalPair univ (fun _ => 0) (fun _ => -1) Complex.cosh Complex.sinh :=
  isFundamentalPair_of_wronskian_ne_zero isSCDomain_univ (differentiableOn_const 0)
    (differentiableOn_const (-1)) (mem_univ 0) isODESolution_cosh isODESolution_sinh
    (by rw [wronskian_cosh_sinh]; norm_num)

/-- The constants of 2.7.36 and 2.7.37 are related by `C = A + B`, `D = A − B`. -/
theorem exp_pair_eq_cosh_sinh (A B z : ℂ) :
    A * Complex.exp z + B * Complex.exp (-z) =
      (A + B) * Complex.cosh z + (A - B) * Complex.sinh z := by
  rw [Complex.cosh, Complex.sinh]
  ring

/-! ### Recessive and dominant solutions -/

theorem tendsto_exp_two_re_atBot :
    Tendsto (fun z : ℂ => Real.exp (2 * z.re)) (comap re atBot) (𝓝 0) :=
  Real.tendsto_exp_atBot.comp (tendsto_comap.const_mul_atBot two_pos)

theorem tendsto_neg_comap_re : Tendsto (fun z : ℂ => -z) (comap re atTop) (comap re atBot) := by
  rw [tendsto_comap_iff]
  have : Tendsto (fun z : ℂ => -z.re) (comap re atTop) atBot :=
    tendsto_neg_atTop_atBot.comp tendsto_comap
  simpa [Function.comp_def] using this

/-- **DLMF §2.7(iv)**: `w₁ = e^z` is recessive (and `w₂ = e^{−z}` dominant) as `ℜz → −∞`:
`w₁/w₂ → 0`. -/
theorem exp_recessive_atBot :
    Tendsto (fun z => Complex.exp z / Complex.exp (-z)) (comap re atBot) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine tendsto_exp_two_re_atBot.congr fun z => ?_
  rw [norm_div, Complex.norm_exp, Complex.norm_exp, ← Real.exp_sub, neg_re]
  ring_nf

/-- **DLMF §2.7(iv)**: and vice versa as `ℜz → +∞`: `w₂/w₁ → 0`. -/
theorem exp_neg_recessive_atTop :
    Tendsto (fun z => Complex.exp (-z) / Complex.exp z) (comap re atTop) (𝓝 0) := by
  have := exp_recessive_atBot.comp tendsto_neg_comap_re
  refine this.congr fun z => ?_
  simp

/-! ### Cancellation -/

/-- `|u + v| / (|u| + |v|)`: the proportion of the magnitude of the terms surviving in `u + v`
(small values mean severe numerical cancellation). -/
noncomputable def cancelRatio (u v : ℂ) : ℝ := ‖u + v‖ / (‖u‖ + ‖v‖)

theorem cancelRatio_nonneg (u v : ℂ) : 0 ≤ cancelRatio u v :=
  div_nonneg (norm_nonneg _) (by positivity)

theorem cancelRatio_le_one (u v : ℂ) : cancelRatio u v ≤ 1 := by
  rcases (add_nonneg (norm_nonneg u) (norm_nonneg v)).eq_or_lt with h | h
  · rw [cancelRatio, ← h, div_zero]; exact zero_le_one
  · exact (div_le_one h).mpr (norm_add_le u v)

/-- **DLMF §2.7(iv)**: with `C = D ≠ 0`, `C cosh z + D sinh z` suffers severe numerical
cancellation as `ℜz → −∞`: the cancellation ratio tends to `0`. -/
theorem cosh_sinh_cancel {C : ℂ} (hC : C ≠ 0) :
    Tendsto (fun z => cancelRatio (C * Complex.cosh z) (C * Complex.sinh z)) (comap re atBot)
      (𝓝 0) := by
  have hb : Tendsto (fun z : ℂ => 2 * Real.exp (2 * z.re) / (1 - Real.exp (2 * z.re)))
      (comap re atBot) (𝓝 0) := by
    have := (tendsto_exp_two_re_atBot.const_mul 2).div (tendsto_exp_two_re_atBot.const_sub 1)
      (by norm_num)
    rw [show (2 : ℝ) * 0 / (1 - 0) = 0 by norm_num] at this
    exact this
  refine squeeze_zero' (Eventually.of_forall fun z => cancelRatio_nonneg _ _) ?_ hb
  have hneg : ∀ᶠ z : ℂ in comap re atBot, z.re < 0 :=
    tendsto_comap.eventually (eventually_lt_atBot 0)
  filter_upwards [hneg] with z hz
  set x := z.re
  have hC0 : 0 < ‖C‖ := norm_pos_iff.mpr hC
  have hex : Real.exp x < Real.exp (-x) := Real.exp_lt_exp.mpr (by linarith)
  have h2x : Real.exp (2 * x) < 1 := by
    have := Real.exp_lt_exp.mpr (show 2 * x < 0 by linarith)
    rwa [Real.exp_zero] at this
  -- `|cosh z| ≥ (e^{−x} − e^{x})/2`
  have hcosh : (Real.exp (-x) - Real.exp x) / 2 ≤ ‖Complex.cosh z‖ := by
    rw [Complex.cosh, norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
    have := norm_sub_norm_le (Complex.exp (-z)) (-Complex.exp z)
    rw [norm_neg, sub_neg_eq_add, add_comm, Complex.norm_exp, Complex.norm_exp, neg_re] at this
    linarith
  have hnum : ‖C * Complex.cosh z + C * Complex.sinh z‖ = ‖C‖ * Real.exp x := by
    rw [← mul_add, Complex.cosh_add_sinh, norm_mul, Complex.norm_exp]
  have hden : ‖C‖ * ((Real.exp (-x) - Real.exp x) / 2) ≤
      ‖C * Complex.cosh z‖ + ‖C * Complex.sinh z‖ := by
    rw [norm_mul, norm_mul]
    nlinarith [norm_nonneg (Complex.sinh z), mul_le_mul_of_nonneg_left hcosh hC0.le]
  have hpos : 0 < ‖C‖ * ((Real.exp (-x) - Real.exp x) / 2) := by
    have : 0 < Real.exp (-x) - Real.exp x := by linarith
    positivity
  rw [cancelRatio, hnum]
  calc ‖C‖ * Real.exp x / (‖C * Complex.cosh z‖ + ‖C * Complex.sinh z‖)
      ≤ ‖C‖ * Real.exp x / (‖C‖ * ((Real.exp (-x) - Real.exp x) / 2)) :=
        div_le_div_of_nonneg_left (by positivity) hpos hden
    _ = 2 * Real.exp (2 * x) / (1 - Real.exp (2 * x)) := by
        have e1 : Real.exp (2 * x) = Real.exp x * Real.exp x := by
          rw [← Real.exp_add]; ring_nf
        have h1 : 1 - Real.exp (2 * x) ≠ 0 := by linarith
        have h3 : Real.exp (-x) - Real.exp x ≠ 0 := by linarith
        have hE : Real.exp x ≠ 0 := (Real.exp_pos x).ne'
        rw [Real.exp_neg] at h3 ⊢
        rw [e1] at h1 ⊢
        have h4 : (Real.exp x)⁻¹ - Real.exp x = (1 - Real.exp x * Real.exp x) / Real.exp x := by
          field_simp
        rw [h4]
        field_simp

/-- The dominant exponential takes over: for `P ≠ 0`,
`cancelRatio (P e^{−z}) (Q e^{z}) → 1` as `ℜz → −∞`. -/
theorem cancelRatio_exp_atBot {P : ℂ} (hP : P ≠ 0) (Q : ℂ) :
    Tendsto (fun z => cancelRatio (P * Complex.exp (-z)) (Q * Complex.exp z)) (comap re atBot)
      (𝓝 1) := by
  have hP0 : 0 < ‖P‖ := norm_pos_iff.mpr hP
  have hl : Tendsto (fun z : ℂ => (‖P‖ - ‖Q‖ * Real.exp (2 * z.re)) /
      (‖P‖ + ‖Q‖ * Real.exp (2 * z.re))) (comap re atBot) (𝓝 1) := by
    have := (tendsto_exp_two_re_atBot.const_mul ‖Q‖).const_sub ‖P‖ |>.div
      ((tendsto_exp_two_re_atBot.const_mul ‖Q‖).const_add ‖P‖) (by simp [hP0.ne'])
    rw [show (‖P‖ - ‖Q‖ * 0) / (‖P‖ + ‖Q‖ * 0) = 1 by simp [hP0.ne']] at this
    exact this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds (fun z => ?_)
    (fun z => cancelRatio_le_one _ _)
  set x := z.re
  have ee : Real.exp (2 * x) = Real.exp x * Real.exp x := by rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
  have hEx := Real.exp_pos x
  have hEm := Real.exp_pos (-x)
  have hlow : ‖P‖ * Real.exp (-x) - ‖Q‖ * Real.exp x ≤
      ‖P * Complex.exp (-z) + Q * Complex.exp z‖ := by
    have := norm_sub_norm_le (P * Complex.exp (-z)) (-(Q * Complex.exp z))
    rw [norm_neg, sub_neg_eq_add, norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp,
      neg_re] at this
    linarith
  have hden : ‖P * Complex.exp (-z)‖ + ‖Q * Complex.exp z‖ =
      ‖P‖ * Real.exp (-x) + ‖Q‖ * Real.exp x := by
    rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp, neg_re]
  have hdpos : 0 < ‖P‖ * Real.exp (-x) + ‖Q‖ * Real.exp x := by positivity
  rw [cancelRatio, hden]
  calc (‖P‖ - ‖Q‖ * Real.exp (2 * x)) / (‖P‖ + ‖Q‖ * Real.exp (2 * x))
      = (‖P‖ * Real.exp (-x) - ‖Q‖ * Real.exp x) /
          (‖P‖ * Real.exp (-x) + ‖Q‖ * Real.exp x) := by
        have hE : Real.exp x ≠ 0 := hEx.ne'
        rw [ee, Real.exp_neg]
        field_simp
    _ ≤ _ := div_le_div_of_nonneg_right hlow hdpos.le

/-- **DLMF §2.7(iv)**: no cancellation with the numerically satisfactory pair `w₁, w₂` as
`ℜz → −∞`: for `(A, B) ≠ (0, 0)`, `cancelRatio (A e^z) (B e^{−z}) → 1`. -/
theorem exp_pair_no_cancel_atBot {A B : ℂ} (hAB : A ≠ 0 ∨ B ≠ 0) :
    Tendsto (fun z => cancelRatio (A * Complex.exp z) (B * Complex.exp (-z))) (comap re atBot)
      (𝓝 1) := by
  by_cases hB : B = 0
  · have hA : A ≠ 0 := hAB.resolve_right (not_not.mpr hB)
    refine tendsto_const_nhds.congr fun z => ?_
    rw [cancelRatio, hB, zero_mul, add_zero, norm_zero, add_zero,
      div_self (norm_ne_zero_iff.mpr (mul_ne_zero hA (Complex.exp_ne_zero z)))]
  · refine (cancelRatio_exp_atBot hB A).congr fun z => ?_
    rw [cancelRatio, cancelRatio, add_comm, add_comm ‖B * _‖]

/-- **DLMF §2.7(iv)**: likewise as `ℜz → +∞`. -/
theorem exp_pair_no_cancel_atTop {A B : ℂ} (hAB : A ≠ 0 ∨ B ≠ 0) :
    Tendsto (fun z => cancelRatio (A * Complex.exp z) (B * Complex.exp (-z))) (comap re atTop)
      (𝓝 1) := by
  have := (exp_pair_no_cancel_atBot hAB.symm (A := B) (B := A)).comp tendsto_neg_comap_re
  refine this.congr fun z => ?_
  simp only [Function.comp_def, neg_neg, cancelRatio]
  rw [add_comm, add_comm ‖B * _‖]

end Azurite.DLMF
