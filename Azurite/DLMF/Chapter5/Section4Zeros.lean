/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section4Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Asymptotics.Defs

/-!
# DLMF §5.4(iii): the zeros of `ψ` on the negative axis, and 5.4.20

For `n ≥ 1`, `ψ` has exactly one zero `xₙ = psiZero n` in `(−n, −n + 1)` (`psiZero_spec`,
`psiR_strictMonoOn`: `ψ(x) = ψ(x + n) − ∑_{k<n} 1/(x + k)` is strictly increasing there;
`exists_psiR_zero`: the reflection formula `ψ(−n + u) = ψ(n + 1 − u) − π cot(πu)` and the
intermediate value theorem), these are all the zeros of `ψ` on the negative axis off the poles
(`dlmf_5_4_iii_all`), and `Γ′(xₙ) = ψ(xₙ) = 0` (the caption of Table 5.4.1, `dlmf_5_4_iii_zero`).

**5.4.20**: `xₙ = −n + π⁻¹ arctan(π/ln n) + O(1/(n (ln n)²))` (`dlmf_5_4_20`), with the explicit
bound `|xₙ − (−n + π⁻¹ arctan(π/ln n))| ≤ 4/(n (ln n)²)` for `n ≥ 3` (`dlmf_5_4_20_bound`).  As
DLMF suggests, `u = xₙ + n` solves `ψ(n + 1 − u) = π cot(πu)`; with `L = ψ(n + 1 − u)` this is
`u = π⁻¹ arctan(π/L)`, and `ln(n − 1) ≤ L ≤ ln(n + 1)`, `arctan` being `1`-Lipschitz
(`abs_arctan_sub_le`).
-/

open Complex Filter Topology Set Finset
open scoped Real

namespace Azurite.DLMF

theorem not_int_of_mem_Ioo {n : ℕ} {x : ℝ} (hx : x ∈ Ioo (-(n : ℝ)) (-(n : ℝ) + 1)) :
    ∀ k : ℤ, x ≠ k := by
  intro k hk
  rw [hk] at hx
  obtain ⟨h1, h2⟩ := hx
  have : (-(n : ℤ)) < k := by exact_mod_cast h1
  have : k < -(n : ℤ) + 1 := by exact_mod_cast h2
  omega

theorem not_neg_nat_of_mem_Ioo {n : ℕ} {x : ℝ} (hx : x ∈ Ioo (-(n : ℝ)) (-(n : ℝ) + 1)) :
    ∀ m : ℕ, x ≠ -m := fun m h => not_int_of_mem_Ioo hx (-m) (by push_cast; exact h)

/-- `ψ` is strictly increasing on `(−n, −n + 1)`, `n ≥ 1`. -/
theorem psiR_strictMonoOn {n : ℕ} (hn : 1 ≤ n) :
    StrictMonoOn psiR (Ioo (-(n : ℝ)) (-(n : ℝ) + 1)) := by
  intro x hx y hy hxy
  have ex := psiR_add_nat (not_neg_nat_of_mem_Ioo hx) n
  have ey := psiR_add_nat (not_neg_nat_of_mem_Ioo hy) n
  have hmono : psiR (x + n) ≤ psiR (y + n) :=
    psiR_mono (mem_Ioi.mpr (by linarith [hx.1])) (mem_Ioi.mpr (by linarith [hy.1]))
      (by linarith)
  have hsum : ∑ k ∈ range n, 1 / (y + k) < ∑ k ∈ range n, 1 / (x + k) := by
    apply sum_lt_sum_of_nonempty (nonempty_range_iff.mpr (by omega))
    intro k hk
    have hk1 : (k : ℝ) + 1 ≤ n := by exact_mod_cast mem_range.mp hk
    exact one_div_lt_one_div_of_neg_of_lt (by linarith [hy.2]) (by linarith)
  linarith

theorem cot_pi_mul_neg_nat_add (n : ℕ) (u : ℝ) :
    Real.cot (π * (-(n : ℝ) + u)) = Real.cot (π * u) := by
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin,
    show π * (-(n : ℝ) + u) = π * u - n * π by ring, Real.cos_sub_nat_mul_pi,
    Real.sin_sub_nat_mul_pi]
  exact mul_div_mul_left _ _ (pow_ne_zero _ (by norm_num))

/-- The reflection formula at `−n + u`: `ψ(−n + u) = ψ(n + 1 − u) − π cot(πu)`, `0 < u < 1`. -/
theorem psiR_neg_add {n : ℕ} {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    psiR (-(n : ℝ) + u) = psiR ((n : ℝ) + 1 - u) - π * Real.cot (π * u) := by
  have hx : -(n : ℝ) + u ∈ Ioo (-(n : ℝ)) (-(n : ℝ) + 1) := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have h := psiR_one_sub (not_int_of_mem_Ioo hx)
  rw [show 1 - (-(n : ℝ) + u) = n + 1 - u by ring, cot_pi_mul_neg_nat_add] at h
  linarith

theorem cot_arctan {t : ℝ} (ht : 0 < t) : Real.cot (Real.arctan t) = 1 / t := by
  rw [Real.cot_eq_cos_div_sin, Real.cos_arctan, Real.sin_arctan]
  have : 0 < √(1 + t ^ 2) := Real.sqrt_pos.mpr (by positivity)
  field_simp

/-- `ψ` has a zero in `(−n, −n + 1)`, `n ≥ 1`. -/
theorem exists_psiR_zero {n : ℕ} (hn : 1 ≤ n) :
    ∃ x ∈ Ioo (-(n : ℝ)) (-(n : ℝ) + 1), psiR x = 0 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set B := |psiR n| + |psiR (n + 1)| + 1 with hB
  have hB0 : 0 < B := by positivity
  set u₁ := Real.arctan (π / B) / π with hu₁
  have hat : 0 < Real.arctan (π / B) := Real.arctan_pos.mpr (by positivity)
  have hat2 := Real.arctan_lt_pi_div_two (π / B)
  have hu0 : 0 < u₁ := div_pos hat Real.pi_pos
  have hu1 : u₁ < 1 / 2 := by
    rw [hu₁, div_lt_iff₀ Real.pi_pos]; linarith
  have hπu : π * u₁ = Real.arctan (π / B) := by
    rw [hu₁]; field_simp
  have hcot1 : π * Real.cot (π * u₁) = B := by
    rw [hπu, cot_arctan (by positivity)]
    field_simp
  have hcot2 : π * Real.cot (π * (1 - u₁)) = -B := by
    rw [show π * (1 - u₁) = π - π * u₁ by ring, Real.cot_eq_cos_div_sin, Real.cos_pi_sub,
      Real.sin_pi_sub, neg_div, ← Real.cot_eq_cos_div_sin, mul_neg, hcot1]
  have hbd : ∀ y ∈ Icc (n : ℝ) (n + 1), |psiR y| < B := by
    intro y hy
    have h1 := psiR_mono (mem_Ioi.mpr hn0) (mem_Ioi.mpr (by linarith [hy.1])) hy.1
    have h2 := psiR_mono (mem_Ioi.mpr (by linarith [hy.1])) (mem_Ioi.mpr (by linarith)) hy.2
    rw [abs_lt]
    constructor
    · linarith [neg_abs_le (psiR n), abs_nonneg (psiR (n + 1))]
    · linarith [le_abs_self (psiR (n + 1)), abs_nonneg (psiR n)]
  have ha : psiR (-(n : ℝ) + u₁) < 0 := by
    rw [psiR_neg_add ⟨hu0, by linarith⟩, hcot1]
    have := abs_lt.mp (hbd ((n : ℝ) + 1 - u₁) ⟨by linarith, by linarith⟩)
    linarith
  have hb : 0 < psiR (-(n : ℝ) + (1 - u₁)) := by
    rw [psiR_neg_add ⟨by linarith, by linarith⟩, hcot2]
    have := abs_lt.mp (hbd ((n : ℝ) + 1 - (1 - u₁)) ⟨by linarith, by linarith⟩)
    linarith
  have hab : -(n : ℝ) + u₁ ≤ -(n : ℝ) + (1 - u₁) := by linarith
  have hcont : ContinuousOn psiR (Icc (-(n : ℝ) + u₁) (-(n : ℝ) + (1 - u₁))) := fun y hy =>
    (continuousAt_psiR (not_neg_nat_of_mem_Ioo (n := n)
      ⟨by linarith [hy.1], by linarith [hy.2]⟩)).continuousWithinAt
  obtain ⟨x, hx, hx0⟩ := intermediate_value_Icc hab hcont ⟨ha.le, hb.le⟩
  exact ⟨x, ⟨by linarith [hx.1], by linarith [hx.2]⟩, hx0⟩

/-- The zero `xₙ` of `ψ` (and of `Γ′`) in `(−n, −n + 1)`, `n ≥ 1` (junk `0` for `n = 0`). -/
noncomputable def psiZero (n : ℕ) : ℝ :=
  if h : 1 ≤ n then Classical.choose (exists_psiR_zero h) else 0

theorem psiZero_spec {n : ℕ} (hn : 1 ≤ n) :
    psiZero n ∈ Ioo (-(n : ℝ)) (-(n : ℝ) + 1) ∧ psiR (psiZero n) = 0 := by
  simp only [psiZero, hn, ↓reduceDIte]
  exact Classical.choose_spec (exists_psiR_zero hn)

theorem psiZero_unique {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : x ∈ Ioo (-(n : ℝ)) (-(n : ℝ) + 1))
    (h0 : psiR x = 0) : x = psiZero n := by
  obtain ⟨hmem, hz⟩ := psiZero_spec hn
  exact (psiR_strictMonoOn hn).injOn hx hmem (h0.trans hz.symm)

/-- **DLMF §5.4(iii)**, Table 5.4.1's `Γ′(xₙ) = ψ(xₙ) = 0`: `xₙ` is the only zero of `ψ` in
`(−n, −n + 1)`, and a zero of `Γ′`. -/
theorem dlmf_5_4_iii_zero {n : ℕ} (hn : 1 ≤ n) :
    digamma (psiZero n : ℂ) = 0 ∧ deriv Gamma (psiZero n : ℂ) = 0 ∧
      ∀ x ∈ Ioo (-(n : ℝ)) (-(n : ℝ) + 1), digamma (x : ℂ) = 0 → x = psiZero n := by
  obtain ⟨hmem, hz⟩ := psiZero_spec hn
  have hψ : digamma (psiZero n : ℂ) = 0 := by rw [digamma_ofReal, hz, ofReal_zero]
  refine ⟨hψ, ?_, fun x hx h0 => psiZero_unique hn hx ?_⟩
  · rw [deriv_Gamma_eq_mul_digamma (ofReal_not_mem_gammaPoles (not_neg_nat_of_mem_Ioo hmem)),
      hψ, mul_zero]
  · rw [digamma_ofReal] at h0
    exact_mod_cast h0

/-- **DLMF §5.4(iii)**: the zeros of `ψ` on the negative axis (off the poles) are exactly the
`xₙ`, `n ≥ 1`. -/
theorem dlmf_5_4_iii_all {x : ℝ} (hx : x < 0) (hp : ∀ m : ℕ, x ≠ -m) (h0 : digamma (x : ℂ) = 0) :
    ∃ n : ℕ, 1 ≤ n ∧ x = psiZero n := by
  set n := ⌊-x⌋₊ + 1 with hn
  have h1 : (⌊-x⌋₊ : ℝ) ≤ -x := Nat.floor_le (by linarith)
  have h2 : -x < (⌊-x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hne : x ≠ -(⌊-x⌋₊ : ℝ) := hp _
  have hmem : x ∈ Ioo (-(n : ℝ)) (-(n : ℝ) + 1) := by
    rw [hn]; push_cast
    constructor
    · linarith
    · rcases lt_or_eq_of_le h1 with h | h
      · linarith
      · exact absurd (by linarith) hne
  refine ⟨n, by omega, psiZero_unique (by omega) hmem ?_⟩
  rw [digamma_ofReal] at h0
  exact_mod_cast h0

/-! ### 5.4.20 -/

/-- `arctan` is `1`-Lipschitz. -/
theorem abs_arctan_sub_le (a b : ℝ) : |Real.arctan a - Real.arctan b| ≤ |a - b| := by
  have key : ∀ a b : ℝ, a < b → |Real.arctan b - Real.arctan a| ≤ |b - a| := by
    intro a b hab
    obtain ⟨c, -, hc⟩ := exists_deriv_eq_slope Real.arctan hab
      Real.continuous_arctan.continuousOn Real.differentiable_arctan.differentiableOn
    rw [Real.deriv_arctan] at hc
    have hba : 0 < b - a := by linarith
    have hd : Real.arctan b - Real.arctan a = (b - a) / (1 + c ^ 2) := by
      rw [eq_div_iff (by positivity)]
      field_simp at hc
      linarith
    rw [hd, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 1 + c ^ 2)]
    exact div_le_self (abs_nonneg _) (by nlinarith)
  rcases lt_trichotomy a b with h | h | h
  · rw [abs_sub_comm, abs_sub_comm a]; exact key a b h
  · simp [h]
  · exact key b a h

/-- `u = xₙ + n` satisfies `u = π⁻¹ arctan(π/L)` with `L = ψ(n + 1 − u) > 0`. -/
theorem psiZero_eq_arctan {n : ℕ} (hn : 1 ≤ n) (hL : 0 < psiR ((n : ℝ) + 1 - (psiZero n + n))) :
    π * (psiZero n + n) = Real.arctan (π / psiR ((n : ℝ) + 1 - (psiZero n + n))) := by
  obtain ⟨hmem, hz⟩ := psiZero_spec hn
  set u := psiZero n + n with hu
  set L := psiR ((n : ℝ) + 1 - u) with hLdef
  have hu01 : u ∈ Ioo (0 : ℝ) 1 := ⟨by rw [hu]; linarith [hmem.1], by rw [hu]; linarith [hmem.2]⟩
  have hrel := psiR_neg_add (n := n) hu01
  rw [show -(n : ℝ) + u = psiZero n by rw [hu]; ring, hz] at hrel
  have hcot : π * Real.cot (π * u) = L := by linarith
  have hs : 0 < Real.sin (π * u) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos, hu01.1])
      (by nlinarith [Real.pi_pos, hu01.2])
  have hc : 0 < Real.cos (π * u) := by
    rw [Real.cot_eq_cos_div_sin] at hcot
    have hq : 0 < Real.cos (π * u) / Real.sin (π * u) := by
      by_contra hq
      push Not at hq
      nlinarith [Real.pi_pos]
    exact (div_pos_iff_of_pos_right hs).mp hq
  have hlt : π * u < π / 2 := by
    by_contra h
    push Not at h
    have := Real.cos_nonpos_of_pi_div_two_le_of_le h (by nlinarith [Real.pi_pos, hu01.2])
    linarith
  have htan : Real.tan (π * u) = π / L := by
    rw [Real.tan_eq_sin_div_cos, ← hcot, Real.cot_eq_cos_div_sin]
    field_simp
  rw [← htan, Real.arctan_tan (by nlinarith [Real.pi_pos, hu01.1]) hlt]

/-- **DLMF 5.4.20**, explicit form: `|xₙ − (−n + π⁻¹ arctan(π/ln n))| ≤ 4/(n (ln n)²)`, `n ≥ 3`. -/
theorem dlmf_5_4_20_bound {n : ℕ} (hn : 3 ≤ n) :
    |psiZero n - (-(n : ℝ) + Real.arctan (π / Real.log n) / π)| ≤ 4 / (n * Real.log n ^ 2) := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hmem, hz⟩ := psiZero_spec hn1
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  set u := psiZero n + n with hu
  set L := psiR ((n : ℝ) + 1 - u) with hLdef
  set ℓ := Real.log n with hℓ
  have hu01 : u ∈ Ioo (0 : ℝ) 1 := ⟨by rw [hu]; linarith [hmem.1], by rw [hu]; linarith [hmem.2]⟩
  -- `ln(n − 1) ≤ L ≤ ln(n + 1)`
  obtain ⟨hLlo, hLhi⟩ := psiR_bracket (n := n - 1) (m := 1) (by omega) (y := (n : ℝ) + 1 - u)
    (by push_cast [Nat.cast_sub hn1]; linarith [hu01.2])
    (by push_cast [Nat.cast_sub hn1]; linarith [hu01.1])
  push_cast [Nat.cast_sub hn1] at hLlo hLhi
  rw [show (n : ℝ) - 1 + 1 + 1 = n + 1 by ring] at hLhi
  have hlog2 : 0 < Real.log ((n : ℝ) - 1) := Real.log_pos (by linarith)
  have hℓ0 : 0 < ℓ := Real.log_pos (by linarith)
  have hL0 : 0 < L := lt_of_lt_of_le hlog2 hLlo
  have hπu := psiZero_eq_arctan hn1 hL0
  -- `|L − ℓ| ≤ 1/(n − 1)`
  have e1 := log_sub_log_le (a := (n : ℝ) + 1) (b := n) (by linarith) (by linarith)
  have e2 := log_sub_log_le (a := (n : ℝ)) (b := (n : ℝ) - 1) (by linarith) (by linarith)
  have hdiff : |L - ℓ| ≤ 1 / ((n : ℝ) - 1) := by
    rw [abs_le]
    have h3 : ((n : ℝ) + 1 - n) / n ≤ 1 / ((n : ℝ) - 1) := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
    have h4 : ((n : ℝ) - (n - 1)) / (n - 1) = 1 / ((n : ℝ) - 1) := by ring
    constructor <;> linarith
  -- the main estimate
  have hgoal : psiZero n - (-(n : ℝ) + Real.arctan (π / ℓ) / π)
      = (Real.arctan (π / L) - Real.arctan (π / ℓ)) / π := by
    rw [← hπu]; field_simp; ring
  rw [hgoal, abs_div, abs_of_pos Real.pi_pos]
  have hlip := abs_arctan_sub_le (π / L) (π / ℓ)
  have hq : |π / L - π / ℓ| = π * |L - ℓ| / (L * ℓ) := by
    rw [show π / L - π / ℓ = π * (ℓ - L) / (L * ℓ) by field_simp, abs_div, abs_mul,
      abs_of_pos Real.pi_pos, abs_of_pos (mul_pos hL0 hℓ0), abs_sub_comm]
  rw [hq] at hlip
  have hstep : |Real.arctan (π / L) - Real.arctan (π / ℓ)| / π ≤ |L - ℓ| / (L * ℓ) := by
    rw [div_le_iff₀ Real.pi_pos]
    calc _ ≤ π * |L - ℓ| / (L * ℓ) := hlip
      _ = |L - ℓ| / (L * ℓ) * π := by ring
  refine hstep.trans ?_
  -- `|L − ℓ|/(Lℓ) ≤ (1/(n − 1))/(ln(n − 1) ℓ) ≤ 4/(n ℓ²)`
  have hlog_half : ℓ ≤ 2 * Real.log ((n : ℝ) - 1) := by
    rw [hℓ, ← Real.log_rpow (by linarith)]
    apply Real.log_le_log (by linarith)
    rw [show ((n : ℝ) - 1) ^ (2 : ℝ) = ((n : ℝ) - 1) ^ 2 by norm_cast]
    nlinarith
  rw [div_le_div_iff₀ (mul_pos hL0 hℓ0) (by positivity)]
  have hA : |L - ℓ| * (n * ℓ ^ 2) ≤ 1 / ((n : ℝ) - 1) * (n * ℓ ^ 2) :=
    mul_le_mul_of_nonneg_right hdiff (by positivity)
  have hB : 1 / ((n : ℝ) - 1) * (n * ℓ ^ 2) ≤ 4 * (L * ℓ) := by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by linarith)]
    have : (n : ℝ) * ℓ ≤ 4 * ((n : ℝ) - 1) * L := by nlinarith
    nlinarith
  linarith

/-- **DLMF 5.4.20**: `xₙ = −n + π⁻¹ arctan(π/ln n) + O(1/(n (ln n)²))` as `n → ∞`. -/
theorem dlmf_5_4_20 :
    (fun n : ℕ => psiZero n - (-(n : ℝ) + Real.arctan (π / Real.log n) / π)) =O[atTop]
      fun n : ℕ => 1 / (n * Real.log n ^ 2) := by
  refine Asymptotics.IsBigO.of_bound 4 ?_
  filter_upwards [eventually_ge_atTop 3] with n hn
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hℓ : 0 < Real.log n := Real.log_pos (by linarith)
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / (n * Real.log n ^ 2))]
  calc _ ≤ 4 / (n * Real.log n ^ 2) := dlmf_5_4_20_bound hn
    _ = 4 * (1 / (n * Real.log n ^ 2)) := by ring

end Azurite.DLMF
