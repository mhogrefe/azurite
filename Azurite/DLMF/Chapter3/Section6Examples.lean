/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section6Miller
import Azurite.DLMF.Chapter3.Section6Olver
import Azurite.BrentZimmermann.Chapter4.BesselRecurrence
import Azurite.BrentZimmermann.Chapter4.PowerSeriesEval
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# DLMF §3.6(vi), Example 1: Bessel functions

`Jₙ(1)` is `BZ.besselJNat n 1` (the series 10.2.2, from the Brent–Zimmermann chapter).

* **3.6.11** `w_{n+1} − 2n wₙ + w_{n−1} = 0` (`besA`, `besB`, `besC`) is satisfied by `Jₙ(1)`
  (`dlmf_3_6_11`, from 10.6.1 `BZ.besselJNat_recurrence`).
* **3.6.12** `Jₙ(1) ∼ (2πn)^{−1/2}(e/(2n))ⁿ` (`dlmf_3_6_12`):
  `|2ⁿ n! Jₙ(1) − 1| ≤ e^{1/(4(n+1))} − 1` (`abs_besselJNat_one_sub_le`) and Stirling (`Stirling.factorial_isEquivalent_stirling`); in
  particular `J₀(1) > 0` (`besselJNat_zero_one_pos`).
* The solution `pₙ` with `p₀ = 0`, `p₁ = 1` is an integer sequence with `pₙ ≥ n` (`besP`,
  `besP_ge`, `olverP_bes`). `Jₙ(1)` is recessive (`besJ1_isRecessive`), and every solution
  independent of it — such as `Yₙ(1)` — is dominant: `Jₙ(1)/wₙ → 0`, `|wₙ| → ∞`
  (`dlmf_3_6_vi_dominant`). "Thus `Yₙ(1)` is dominant and can be computed by forward recursion,
  whereas `Jₙ(1)` is recessive and has to be computed by backward recursion": Miller's algorithm
  (`dlmf_3_6_vi_miller`) and Olver's algorithm (`dlmf_3_6_vi_olver`) converge to `Jₙ(1)`.

Not formalized: **3.6.13** (`Yₙ(1) ∼ (2/(πn))^{1/2}(2n/e)ⁿ`) — `Yₙ` is only defined
(`BZ.besselY`, as a limit) and not yet developed; the dominance of `Yₙ(1)` is covered by
`dlmf_3_6_vi_dominant` for any solution independent of `Jₙ(1)`.
-/

open Filter Topology Finset Asymptotics

namespace Azurite.DLMF

/-! ### The difference equation 3.6.11 -/

/-- The coefficients of 3.6.11 `w_{n+1} − 2n wₙ + w_{n−1} = 0` in the form 3.6.3. -/
def besA : ℕ → ℂ := fun _ => 1

def besB : ℕ → ℂ := fun n => 2 * n

def besC : ℕ → ℂ := fun _ => 1

theorem besA_ne (n : ℕ) (_ : 1 ≤ n) : besA n ≠ 0 := one_ne_zero

theorem besC_ne (n : ℕ) (_ : 1 ≤ n) : besC n ≠ 0 := one_ne_zero

/-- `Jₙ(1)` (`BZ.besselJNat`, the series 10.2.2). -/
noncomputable def besJ1 (n : ℕ) : ℂ := (BZ.besselJNat n 1 : ℂ)

/-- **DLMF 3.6.11** is satisfied by `Jₙ(1)` (10.6.1). -/
theorem dlmf_3_6_11 : IsRec3 besA besB besC besJ1 := isRec3_of_shift fun m => by
  have h := BZ.besselJNat_recurrence m 1
  simp only [besA, besB, besC, besJ1, one_mul]
  have h' : (BZ.besselJNat m 1 : ℂ) + BZ.besselJNat (m + 2) 1 =
      2 * ((m : ℂ) + 1) * BZ.besselJNat (m + 1) 1 := by
    have := congrArg (fun t : ℝ => (t : ℂ)) h
    push_cast at this
    linear_combination 2 * this
  push_cast
  linear_combination h'

/-! ### The dominant solution `pₙ` (`p₀ = 0`, `p₁ = 1`) -/

/-- `pₙ` as integers: `p₀ = 0`, `p₁ = 1`, `p_{n+1} = 2n pₙ − p_{n−1}`. -/
def besPPair : ℕ → ℤ × ℤ
  | 0 => (0, 1)
  | m + 1 => ((besPPair m).2, 2 * (m + 1) * (besPPair m).2 - (besPPair m).1)

def besP (n : ℕ) : ℤ := (besPPair n).1

theorem besP_succ_succ (m : ℕ) : besP (m + 2) = 2 * (m + 1) * besP (m + 1) - besP m := by
  simp [besP, besPPair]

theorem besP_zero : besP 0 = 0 := rfl

theorem besP_one : besP 1 = 1 := rfl

/-- `1 ≤ pₙ ≤ p_{n+1}` for `n ≥ 1`. -/
theorem besP_mono (n : ℕ) (hn : 1 ≤ n) : 1 ≤ besP n ∧ besP n ≤ besP (n + 1) := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have e := besP_succ_succ n
    have hn' : (1 : ℤ) ≤ n := by exact_mod_cast hn
    refine ⟨ih.1.trans ih.2, ?_⟩
    rw [e]
    nlinarith [ih.1, ih.2]

/-- `pₙ ≥ n`. -/
theorem besP_ge (n : ℕ) : (n : ℤ) ≤ besP n := by
  rcases n with _ | _ | m
  · simp [besP_zero]
  · simp [besP_one]
  · rw [besP_succ_succ]
    push_cast
    rcases m with _ | m
    · simp [besP_zero, besP_one]
    · have h1 := besP_mono (m + 1) (by omega)
      have h2 : (1 : ℤ) ≤ besP (m + 1 + 1) := h1.1.trans h1.2
      push_cast
      nlinarith [h1.1, h1.2]

/-- The solution `pₙ` of 3.6.11 with `p₀ = 0`, `p₁ = 1` (`olverP` of §3.6(v)) is `besP`. -/
theorem olverP_bes (n : ℕ) : olverP besA besB besC n = besP n := by
  have hsol : IsRec3 besA besB besC fun n => (besP n : ℂ) := isRec3_of_shift fun m => by
    simp only [besA, besB, besC, one_mul, besP_succ_succ]
    push_cast; ring
  exact congrFun ((olverP_isRec3 besA_ne).eq_of_eq besA_ne hsol
    (by simp [besP_zero]) (by simp [besP_one])) n

theorem olverP_bes_ne (n : ℕ) (hn : 1 ≤ n) : olverP besA besB besC n ≠ 0 := by
  rw [olverP_bes]
  have := (besP_mono n hn).1
  exact_mod_cast (by omega : besP n ≠ 0)

theorem norm_olverP_bes_ge (n : ℕ) : (n : ℝ) ≤ ‖olverP besA besB besC n‖ := by
  rw [olverP_bes, Complex.norm_intCast]
  have := besP_ge n
  have h : (n : ℝ) ≤ (besP n : ℝ) := by exact_mod_cast this
  exact h.trans (le_abs_self _)

theorem tendsto_norm_olverP_bes : Tendsto (fun n => ‖olverP besA besB besC n‖) atTop atTop :=
  tendsto_atTop_mono norm_olverP_bes_ge tendsto_natCast_atTop_atTop

/-! ### `2ⁿ n! Jₙ(1) → 1`, `J₀(1) > 0` and 3.6.12 -/

/-- `|2ⁿ n! Jₙ(1) − 1| ≤ e^{1/(4(n+1))} − 1`. -/
theorem abs_besselJNat_one_sub_le (n : ℕ) :
    |2 ^ n * n.factorial * BZ.besselJNat n 1 - 1| ≤ Real.exp (1 / (4 * (n + 1))) - 1 := by
  set x : ℝ := 1 / (4 * (n + 1))
  have hs := BZ.summable_besselJNat_term n 1
  set c : ℕ → ℝ := fun j => 2 ^ n * n.factorial * (BZ.besselCoeff n j * (1 / 2 : ℝ) ^ (2 * j + n))
  have hc : HasSum c (2 ^ n * n.factorial * BZ.besselJNat n 1) := by
    exact HasSum.mul_left (2 ^ n * (n.factorial : ℝ)) hs.hasSum
  have hc0 : c 0 = 1 := by
    simp only [c, BZ.besselCoeff, pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul, add_zero,
      mul_zero, zero_add]
    have : (n.factorial : ℝ) ≠ 0 := by positivity
    rw [div_pow, one_pow]
    field_simp
  have hbound : ∀ j, |c (j + 1)| ≤ x ^ (j + 1) / (j + 1).factorial := by
    intro j
    have hfac : (n.factorial : ℝ) * ((n : ℝ) + 1) ^ (j + 1) ≤ (n + (j + 1)).factorial := by
      have h2 : (n + 1) ^ (j + 1) ≤ (n + 1).ascFactorial (j + 1) :=
        Nat.pow_succ_le_ascFactorial (n + 1) (j + 1)
      have : n.factorial * (n + 1) ^ (j + 1) ≤ (n + (j + 1)).factorial := by
        rw [← Nat.factorial_mul_ascFactorial]; exact Nat.mul_le_mul_left _ h2
      exact_mod_cast this
    have hcj : c (j + 1) = (-1) ^ (j + 1) *
        ((n.factorial : ℝ) / ((j + 1).factorial * (n + (j + 1)).factorial * 4 ^ (j + 1))) := by
      simp only [c, BZ.besselCoeff]
      rw [show (1 / 2 : ℝ) ^ (2 * (j + 1) + n) = 1 / (2 ^ n * 4 ^ (j + 1)) by
        rw [div_pow, one_pow, pow_add, pow_mul]; norm_num; ring]
      have h1 : ((j + 1).factorial : ℝ) ≠ 0 := by positivity
      have h2 : ((n + (j + 1)).factorial : ℝ) ≠ 0 := by positivity
      field_simp
    have hpos : (0 : ℝ) < (j + 1).factorial * (n + (j + 1)).factorial * 4 ^ (j + 1) := by
      positivity
    rw [hcj, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (by positivity)]
    simp only [x]
    rw [div_pow, one_pow, div_div, div_le_div_iff₀ hpos (by positivity)]
    have h4 : (0 : ℝ) < 4 ^ (j + 1) := by positivity
    calc (n.factorial : ℝ) * ((4 * ((n : ℝ) + 1)) ^ (j + 1) * (j + 1).factorial)
        = (j + 1).factorial * 4 ^ (j + 1) * ((n.factorial : ℝ) * ((n : ℝ) + 1) ^ (j + 1)) := by
          rw [mul_pow]; ring
      _ ≤ (j + 1).factorial * 4 ^ (j + 1) * (n + (j + 1)).factorial := by gcongr
      _ = _ := by ring
  -- `|∑_{j≥1} c_j| ≤ ∑_{j≥1} x^j/j! = e^x − 1`
  have hexp := BZ.hasSum_exp_series x
  have hexp1 : HasSum (fun j => x ^ (j + 1) / (j + 1).factorial) (Real.exp x - 1) := by
    have := (hasSum_nat_add_iff' 1).mpr hexp
    simpa using this
  have hc1 : HasSum (fun j => c (j + 1)) (2 ^ n * n.factorial * BZ.besselJNat n 1 - 1) := by
    have := (hasSum_nat_add_iff' 1).mpr hc
    simpa [hc0] using this
  have habs : Summable fun j => |c (j + 1)| :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hbound hexp1.summable
  rw [← hc1.tsum_eq, ← hexp1.tsum_eq]
  calc |∑' j, c (j + 1)| ≤ ∑' j, |c (j + 1)| := by
        have := norm_tsum_le_tsum_norm (f := fun j => c (j + 1))
          (by simpa only [Real.norm_eq_abs] using habs)
        simpa only [Real.norm_eq_abs] using this
    _ ≤ _ := habs.tsum_le_tsum hbound hexp1.summable

/-- `2ⁿ n! Jₙ(1) → 1`. -/
theorem tendsto_besselJNat_one : Tendsto (fun n : ℕ => 2 ^ n * n.factorial * BZ.besselJNat n 1)
    atTop (𝓝 1) := by
  have hx : Tendsto (fun n : ℕ => Real.exp (1 / (4 * ((n : ℝ) + 1))) - 1) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => 1 / (4 * ((n : ℝ) + 1))) atTop (𝓝 0) := by
      refine tendsto_const_nhds.div_atTop ?_
      exact (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).const_mul_atTop
        (by norm_num)
    have := ((Real.continuous_exp.tendsto 0).comp h1).sub_const 1
    simpa using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _) (fun n => by
    rw [Real.norm_eq_abs]; exact abs_besselJNat_one_sub_le n) hx

/-- `J₀(1) > 0` (in fact `|J₀(1) − 1| ≤ e^{1/4} − 1 < 1`). -/
theorem besselJNat_zero_one_pos : 0 < BZ.besselJNat 0 1 := by
  have h := abs_besselJNat_one_sub_le 0
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul, CharP.cast_eq_zero, zero_add,
    mul_one] at h
  have h2 : Real.exp (1 / 4) < 2 := by
    have := Real.log_two_gt_d9
    calc Real.exp (1 / 4) < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr (by linarith)
      _ = 2 := Real.exp_log (by norm_num)
  have := (abs_le.mp h).1
  linarith

theorem besJ1_ne_zero : besJ1 ≠ 0 := fun h => by
  have := congrFun h 0
  simp only [besJ1, Pi.zero_apply, Complex.ofReal_eq_zero] at this
  exact besselJNat_zero_one_pos.ne' this

/-- **DLMF 3.6.12**: `Jₙ(1) ∼ (2πn)^{−1/2} (e/(2n))ⁿ` as `n → ∞`. -/
theorem dlmf_3_6_12 : (fun n : ℕ => BZ.besselJNat n 1) ~[atTop]
    fun n => 1 / Real.sqrt (2 * Real.pi * n) * (Real.exp 1 / (2 * n)) ^ n := by
  -- `Jₙ(1) ∼ 1/(2ⁿ n!)`
  have h1 : (fun n : ℕ => BZ.besselJNat n 1) ~[atTop] fun n => 1 / (2 ^ n * (n.factorial : ℝ)) := by
    refine isEquivalent_of_tendsto_one ?_
    refine tendsto_besselJNat_one.congr fun n => ?_
    simp only [Pi.div_apply]
    have : (2 : ℝ) ^ n * n.factorial ≠ 0 := by positivity
    field_simp
  -- Stirling
  have h2 : (fun n : ℕ => 2 ^ n * (n.factorial : ℝ)) ~[atTop]
      fun n => 2 ^ n * (Real.sqrt (2 * n * Real.pi) * (n / Real.exp 1) ^ n) :=
    (IsEquivalent.refl).mul Stirling.factorial_isEquivalent_stirling
  have h4 : (fun n : ℕ => 1 / (2 ^ n * (n.factorial : ℝ))) ~[atTop]
      fun n => 1 / Real.sqrt (2 * Real.pi * n) * (Real.exp 1 / (2 * n)) ^ n := by
    refine (h2.inv.congr_left ?_).congr_right ?_
    · filter_upwards with n
      simp [one_div]
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      simp only [Pi.inv_apply, one_div]
      rw [show 2 * (n : ℝ) * Real.pi = 2 * Real.pi * n by ring, div_pow, div_pow, mul_pow]
      have : Real.sqrt (2 * Real.pi * n) ≠ 0 := by positivity
      field_simp
  exact h1.trans h4

/-! ### `Jₙ(1)` is recessive, every independent solution is dominant -/

theorem tendsto_besJ1_div_olverP :
    Tendsto (fun n => besJ1 n / olverP besA besB besC n) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero_norm' ?_ ((BZ.tendsto_besselJNat_atTop 1).norm.trans (by simp))
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [norm_norm, norm_div, besJ1, Complex.norm_real]
  have h1 : (1 : ℝ) ≤ ‖olverP besA besB besC n‖ := by
    have := norm_olverP_bes_ge n
    exact le_trans (by exact_mod_cast hn) this
  exact div_le_self (norm_nonneg _) h1

/-- **DLMF §3.6(vi)**: `Jₙ(1)` is a recessive solution of 3.6.11 (relative to `pₙ`). -/
theorem besJ1_isRecessive : IsRecessive besA besB besC besJ1 :=
  ⟨dlmf_3_6_11, besJ1_ne_zero, olverP besA besB besC, olverP_isRec3 besA_ne,
    (eventually_ge_atTop 1).mono fun n hn => olverP_bes_ne n hn, tendsto_besJ1_div_olverP⟩

/-- **DLMF §3.6(vi)**: every solution `w` of 3.6.11 independent of `Jₙ(1)` (such as `Yₙ(1)`) is
dominant: `Jₙ(1)/wₙ → 0` and `|wₙ| → ∞`. -/
theorem dlmf_3_6_vi_dominant {w : ℕ → ℂ} (hw : IsRec3 besA besB besC w)
    (hC : casoratian besJ1 w 0 ≠ 0) :
    Tendsto (fun n => besJ1 n / w n) atTop (𝓝 0) ∧ Tendsto (fun n => ‖w n‖) atTop atTop := by
  have hP := olverP_isRec3 (b := besB) (c := besC) besA_ne
  have hCp : casoratian besJ1 (olverP besA besB besC) 0 ≠ 0 := by
    simp only [casoratian, zero_add, olverP_one, olverP_zero, mul_one, mul_zero, sub_zero]
    exact fun h => besJ1_ne_zero (funext fun n => by
      exact absurd h (by simpa [besJ1] using besselJNat_zero_one_pos.ne'))
  obtain ⟨α, β, hαβ⟩ := IsRec3.eq_comb besA_ne dlmf_3_6_11 hP hw hCp
  have hβ : β ≠ 0 := by
    rintro rfl
    apply hC
    simp only [casoratian, zero_add, hαβ, zero_mul, add_zero]
    ring
  have hpN : ∀ᶠ n in atTop, olverP besA besB besC n ≠ 0 :=
    (eventually_ge_atTop 1).mono fun n hn => olverP_bes_ne n hn
  have hwp : Tendsto (fun n => w n / olverP besA besB besC n) atTop (𝓝 (α * 0 + β)) := by
    refine ((tendsto_besJ1_div_olverP.const_mul α).add_const β).congr' ?_
    filter_upwards [hpN] with n hn
    rw [hαβ]; field_simp
  rw [mul_zero, zero_add] at hwp
  refine ⟨?_, ?_⟩
  · have := tendsto_besJ1_div_olverP.div hwp hβ
    rw [zero_div] at this
    refine this.congr' ?_
    filter_upwards [hpN] with n hn
    simp only [Pi.div_apply]
    by_cases hw0 : w n = 0
    · simp [hw0]
    · field_simp
  · have h1 : Tendsto (fun n => ‖w n / olverP besA besB besC n‖) atTop (𝓝 ‖β‖) := hwp.norm
    have h2 := h1.pos_mul_atTop (norm_pos_iff.mpr hβ) tendsto_norm_olverP_bes
    refine h2.congr' ?_
    filter_upwards [hpN] with n hn
    rw [← norm_mul, div_mul_cancel₀ _ hn]

/-- **DLMF §3.6(vi)**: Miller's algorithm (§3.6(iii)) computes `Jₙ(1)`: the trial solutions from
`w_N = 1`, `w_{N+1} = 0`, normalized by `J₀(1)`, converge to `Jₙ(1)`. -/
theorem dlmf_3_6_vi_miller (n : ℕ) :
    Tendsto (fun N => millerNorm besA besB besC (besJ1 0) N n) atTop (𝓝 (besJ1 n)) := by
  obtain ⟨-, -, g, hg, hr⟩ := besJ1_isRecessive
  exact dlmf_3_6_iii_miller besA_ne besC_ne dlmf_3_6_11
    (by simpa [besJ1] using besselJNat_zero_one_pos.ne') hg hr n

/-- **DLMF §3.6(vi)**: Olver's algorithm (§3.6(v), `dₙ = 0`) computes `Jₙ(1)`. -/
theorem dlmf_3_6_vi_olver (n : ℕ) :
    Tendsto (fun N => olverW besA besB besC (fun _ => 0) (besJ1 0) N n) atTop (𝓝 (besJ1 n)) := by
  obtain ⟨-, -, g, hg, hr⟩ := besJ1_isRecessive
  exact dlmf_3_6_v_recessive besA_ne dlmf_3_6_11
    (by simpa [besJ1] using besselJNat_zero_one_pos.ne') hg hr (fun k hk => olverP_bes_ne k hk) n

end Azurite.DLMF
