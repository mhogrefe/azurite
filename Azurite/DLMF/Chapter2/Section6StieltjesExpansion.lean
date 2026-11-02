/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section6Stieltjes

/-!
# DLMF §2.6(ii): the expansion 2.6.27 and the remainder 2.6.30, `0 < α < 1`

* `integral_cpow_neg_div_add`: `∫₀^∞ τ^{−α}/(τ + z) dτ = (π/sin πα) z^{−α}` for `0 < α < 1`,
  `|ph z| < π` (the `s = 0` case of 2.6.23, and 2.6.4 with `α ↦ 1 − α`, `β ↦ α` for complex `x`),
  from the Mellin transform of `1/(1 + z⁻¹ t)` (Table 1.14.5).
* 2.6.30 (`stieltjesR`): `Rₙ(z) = ((−1)ⁿ/zⁿ) ∫₀^∞ τⁿ fₙ(τ)/(τ + z) dτ`.
* 2.6.27 (`dlmf_2_6_27`, `dlmf_2_6_27_Icc`): for `0 < α < 1` and `|ph z| < π`,
  `𝓢f(z) = (π/sin πα) ∑_{s<n} (−1)^s aₛ z^{−s−α} − ∑_{s=1}^n (s−1)! cₛ z^{−s} + Rₙ(z)`,
  with `cₛ` from 2.6.18. The proof is a direct induction on `n`: `fₙ = aₙ τ^{−n−α} + f_{n+1}` and
  `1/(τ + z) = 1/z − τ/(z(τ + z))` give
  `Rₙ(z) = (π/sin πα)(−1)ⁿ aₙ z^{−n−α} + (−1)ⁿ z^{−n−1} 𝓜f(n+1) + R_{n+1}(z)`
  (`stieltjesR_succ`), where `𝓜f(n+1) = ∫₀^∞ τⁿ f_{n+1}(τ) dτ` (`mellinCont_succ_eq`). DLMF
  obtains the same identity from the distributional identity 2.6.17 and the limits 2.6.23–2.6.26;
  the induction gives it without the distribution theory.
* `stieltjesR_isBigO`: for real `x → +∞`, `Rₙ(x) = O(x^{−n−α})`, so 2.6.27 is a genuine
  (generalized) asymptotic expansion along the positive axis.
-/

open MeasureTheory Filter Topology Set Complex Asymptotics
open scoped Real

namespace Azurite.DLMF

/-! ### The integral `∫₀^∞ τ^{−α}/(τ + z) dτ` -/

theorem inv_mem_slitPlane {z : ℂ} (hz : z ∈ slitPlane) : z⁻¹ ∈ slitPlane := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hn : 0 < normSq z := normSq_pos.mpr hz0
  rw [mem_slitPlane_iff] at hz ⊢
  rw [inv_re, inv_im]
  rcases hz with h | h
  · exact Or.inl (div_pos h hn)
  · exact Or.inr (div_ne_zero (neg_ne_zero.mpr h) hn.ne')

/-- `∫₀^∞ τ^{−α}/(τ + z) dτ = (π/sin πα) z^{−α}` for `0 < α < 1`, `|ph z| < π`. -/
theorem integral_cpow_neg_div_add {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {z : ℂ}
    (hz : z ∈ slitPlane) :
    (∫ τ in Ioi (0 : ℝ), (τ : ℂ) ^ (-(α : ℂ)) / (τ + z)) =
      π / Complex.sin (π * α) * z ^ (-(α : ℂ)) := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have h := mellin_one_div_one_add_mul (inv_mem_slitPlane hz) (s := 1 - α)
    (by simp; linarith) (by simp; linarith)
  have e1 : mellin (fun x : ℝ => 1 / (1 + z⁻¹ * x)) (1 - α) =
      z * ∫ τ in Ioi (0 : ℝ), (τ : ℂ) ^ (-(α : ℂ)) / (τ + z) := by
    rw [mellin, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun τ hτ => ?_
    have hτz : (τ : ℂ) + z ≠ 0 := ofReal_add_ne_zero hz (le_of_lt hτ)
    have e : (1 : ℂ) + z⁻¹ * τ = (τ + z) / z := by
      field_simp
      ring
    rw [show (1 - (α : ℂ)) - 1 = -(α : ℂ) by ring, smul_eq_mul, e, one_div_div]
    ring
  rw [e1, inv_cpow _ _ (slitPlane_arg_ne_pi hz), cpow_neg, inv_inv,
    show (π : ℂ) * (1 - α) = π - π * α by ring, Complex.sin_pi_sub,
    show (1 : ℂ) - α = 1 + -(α : ℂ) by ring, cpow_add _ _ hz0, cpow_one] at h
  have h' : z * (∫ τ in Ioi (0 : ℝ), (τ : ℂ) ^ (-(α : ℂ)) / (τ + z)) =
      z * (π / Complex.sin (π * α) * z ^ (-(α : ℂ))) := by
    rw [h]
    ring
  exact mul_left_cancel₀ hz0 h'

/-- The integrand of `integral_cpow_neg_div_add` is absolutely integrable. -/
theorem integrableOn_cpow_neg_div_add {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {z : ℂ}
    (hz : z ∈ slitPlane) :
    IntegrableOn (fun τ : ℝ => (τ : ℂ) ^ (-(α : ℂ)) / (τ + z)) (Ioi 0) := by
  obtain ⟨c, hc, hb⟩ := exists_mul_one_add_le_norm_add hz
  have hloc : LocallyIntegrableOn (fun τ : ℝ => (τ : ℂ) ^ (-(α : ℂ)) / (τ + z)) (Ioi 0) :=
    ((continuousOn_ofReal_cpow_Ioi _).div (continuous_ofReal.continuousOn.add continuousOn_const)
      fun _ ht => ofReal_add_ne_zero hz (le_of_lt ht)).locallyIntegrableOn measurableSet_Ioi
  have htop : (fun τ : ℝ => (τ : ℂ) ^ (-(α : ℂ)) / (τ + z)) =O[atTop] (· ^ (-(1 + α))) := by
    refine IsBigO.of_bound (1 / c) ?_
    filter_upwards [eventually_ge_atTop 1] with t ht
    have ht0 : 0 < t := by linarith
    have hpos : 0 < ‖(t : ℂ) + z‖ := lt_of_lt_of_le (by positivity) (hb t ht0.le)
    rw [norm_div, norm_cpow_eq_rpow_re_of_pos ht0, neg_re, ofReal_re,
      Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _), show -(1 + α) = -α - 1 by ring,
      Real.rpow_sub_one ht0.ne', div_le_iff₀ hpos]
    calc t ^ (-α) = t ^ (-α) / (c * t) * (c * t) := by field_simp
      _ ≤ t ^ (-α) / (c * t) * ‖(t : ℂ) + z‖ := by
        gcongr
        linarith [hb t ht0.le]
      _ = 1 / c * (t ^ (-α) / t) * ‖(t : ℂ) + z‖ := by field_simp
  have hbot : (fun τ : ℝ => (τ : ℂ) ^ (-(α : ℂ)) / (τ + z)) =O[𝓝[>] 0] (· ^ (-α)) := by
    refine IsBigO.of_bound (1 / c) ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : 0 < t := ht
    have hpos : 0 < ‖(t : ℂ) + z‖ := lt_of_lt_of_le (by positivity) (hb t ht0.le)
    rw [norm_div, norm_cpow_eq_rpow_re_of_pos ht0, neg_re, ofReal_re,
      Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _), div_le_iff₀ hpos]
    have hcle : c ≤ ‖(t : ℂ) + z‖ := by nlinarith [hb t ht0.le]
    calc t ^ (-α) = 1 / c * t ^ (-α) * c := by field_simp
      _ ≤ 1 / c * t ^ (-α) * ‖(t : ℂ) + z‖ := by gcongr
  have h := mellinConvergent_of_isBigO_rpow (a := 1 + α) (b := α) (s := 1) hloc htop
    (by simp; linarith) hbot (by simp; linarith)
  exact h.congr_fun (fun t _ => by simp) measurableSet_Ioi

/-- The real form: `∫₀^∞ τ^{−α}/(τ + x) dτ = (π/sin πα) x^{−α}` for `x > 0`. -/
theorem integral_rpow_neg_div_add {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {x : ℝ} (hx : 0 < x) :
    (∫ τ in Ioi (0 : ℝ), τ ^ (-α) / (τ + x)) = π / Real.sin (π * α) * x ^ (-α) := by
  have hxs : (x : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr hx
  have h := integral_cpow_neg_div_add hα0 hα1 hxs
  have e : ((∫ τ in Ioi (0 : ℝ), τ ^ (-α) / (τ + x) : ℝ) : ℂ) =
      ∫ τ in Ioi (0 : ℝ), (τ : ℂ) ^ (-(α : ℂ)) / (τ + x) := by
    rw [show ((∫ τ in Ioi (0 : ℝ), τ ^ (-α) / (τ + x) : ℝ) : ℂ) =
      @RCLike.ofReal ℂ _ (∫ τ in Ioi (0 : ℝ), τ ^ (-α) / (τ + x)) from rfl, ← integral_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun τ hτ => ?_
    change ((τ ^ (-α) / (τ + x) : ℝ) : ℂ) = _
    rw [ofReal_div, ofReal_add, ofReal_cpow (le_of_lt hτ), ofReal_neg]
  apply ofReal_injective
  rw [e, h, ofReal_mul, ofReal_div, ofReal_cpow hx.le, ofReal_neg, ofReal_sin, ofReal_mul]

/-! ### 2.6.30 -/

/-- **DLMF 2.6.30**: `Rₙ(z) = ((−1)ⁿ/zⁿ) ∫₀^∞ τⁿ fₙ(τ)/(τ + z) dτ`. -/
noncomputable def stieltjesR (f : ℝ → ℂ) (a : ℕ → ℂ) (α : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  (-1) ^ n / z ^ n * ∫ τ in Ioi (0 : ℝ), (τ : ℂ) ^ n * stieltjesRem f a α n τ / (τ + z)

namespace StieltjesSetup

variable {f : ℝ → ℂ} {a : ℕ → ℂ} {α : ℝ} (hS : StieltjesSetup f a α)
include hS

/-- `∫₀^∞ τⁿ f_{n+1}(τ) dτ` converges absolutely for `0 < α < 1` (integral form). -/
theorem integrableOn_pow_mul_rem_succ (hα : α < 1) (n : ℕ) :
    IntegrableOn (fun τ : ℝ => (τ : ℂ) ^ n * stieltjesRem f a α (n + 1) τ) (Ioi 0) := by
  refine (hS.mellinConvergent_rem_succ hα n).congr_fun (fun τ _ => ?_) measurableSet_Ioi
  simp only [add_sub_cancel_right, cpow_natCast, smul_eq_mul]

/-- **One step of 2.6.27**:
`Rₙ(z) = (π/sin πα)(−1)ⁿ aₙ z^{−n−α} − n! c_{n+1} z^{−n−1} + R_{n+1}(z)`. -/
theorem stieltjesR_succ (hα : α < 1) {z : ℂ} (hz : z ∈ slitPlane) (n : ℕ) :
    stieltjesR f a α n z =
      π / Complex.sin (π * α) * ((-1) ^ n * a n * z ^ (-((n : ℂ) + α))) -
        (Nat.factorial n : ℂ) * stieltjesC f a α (n + 1) / z ^ (n + 1) +
        stieltjesR f a α (n + 1) z := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hL := integrableOn_cpow_neg_div_add hS.α_pos hα hz
  have hIn1 := hS.integrableOn_pow_mul_rem_div hz (n + 1)
  have hM := hS.integrableOn_pow_mul_rem_succ hα n
  have hJ : IntegrableOn (fun τ : ℝ => (τ : ℂ) ^ n * stieltjesRem f a α (n + 1) τ / (τ + z))
      (Ioi 0) := by
    refine IntegrableOn.congr_fun ((hM.const_mul z⁻¹).sub (hIn1.const_mul z⁻¹)) (fun τ hτ => ?_)
      measurableSet_Ioi
    have hτz : (τ : ℂ) + z ≠ 0 := ofReal_add_ne_zero hz (le_of_lt hτ)
    simp only [Pi.sub_apply]
    field_simp
    ring
  have e1 : (∫ τ in Ioi (0 : ℝ), (τ : ℂ) ^ n * stieltjesRem f a α n τ / (τ + z)) =
      a n * (∫ τ in Ioi (0 : ℝ), (τ : ℂ) ^ (-(α : ℂ)) / (τ + z)) +
        ∫ τ in Ioi (0 : ℝ), (τ : ℂ) ^ n * stieltjesRem f a α (n + 1) τ / (τ + z) := by
    rw [← integral_const_mul, ← integral_add (hL.const_mul _) hJ]
    refine setIntegral_congr_fun measurableSet_Ioi fun τ hτ => ?_
    have hτ0 : (τ : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hτ)
    have e : (τ : ℂ) ^ n * (τ : ℂ) ^ (-((n : ℂ) + α)) = (τ : ℂ) ^ (-(α : ℂ)) := by
      rw [← cpow_natCast, ← cpow_add _ _ hτ0]
      congr 1
      ring
    rw [rem_eq_add_succ, ← e]
    ring
  have e2 : (∫ τ in Ioi (0 : ℝ), (τ : ℂ) ^ n * stieltjesRem f a α (n + 1) τ / (τ + z)) =
      z⁻¹ * (∫ τ in Ioi (0 : ℝ), (τ : ℂ) ^ n * stieltjesRem f a α (n + 1) τ) -
        z⁻¹ * ∫ τ in Ioi (0 : ℝ), (τ : ℂ) ^ (n + 1) * stieltjesRem f a α (n + 1) τ / (τ + z) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_sub (hM.const_mul _)
      (hIn1.const_mul _)]
    refine setIntegral_congr_fun measurableSet_Ioi fun τ hτ => ?_
    have hτz : (τ : ℂ) + z ≠ 0 := ofReal_add_ne_zero hz (le_of_lt hτ)
    field_simp
    ring
  have hpow : z ^ (-((n : ℂ) + α)) = (z ^ n)⁻¹ * z ^ (-(α : ℂ)) := by
    rw [← cpow_natCast, ← cpow_neg, ← cpow_add _ _ hz0]
    congr 1
    ring
  have hf0 : (Nat.factorial n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hzn : z ^ n ≠ 0 := pow_ne_zero n hz0
  have hzn1 : z ^ (n + 1) ≠ 0 := pow_ne_zero _ hz0
  simp only [stieltjesR, stieltjesC, Nat.add_sub_cancel, Nat.cast_succ]
  rw [e1, e2, integral_cpow_neg_div_add hS.α_pos hα hz, ← hS.mellinCont_succ_eq hα n, hpow]
  set K : ℂ := π / Complex.sin (π * α)
  set M := mellinCont f a α ((n : ℂ) + 1)
  set I := ∫ τ in Ioi (0 : ℝ), (τ : ℂ) ^ (n + 1) * stieltjesRem f a α (n + 1) τ / (τ + z)
  field_simp
  ring

/-- **DLMF 2.6.27** (with 2.6.30), `0 < α < 1`, `|ph z| < π`: for every `n`,
`𝓢f(z) = (π/sin πα) ∑_{s<n} (−1)^s aₛ z^{−s−α} − ∑_{s<n} s! c_{s+1} z^{−s−1} + Rₙ(z)`; the second
sum is `∑_{s=1}^n (s−1)! cₛ z^{−s}` reindexed (`dlmf_2_6_27_Icc`). -/
theorem dlmf_2_6_27 (hα : α < 1) {z : ℂ} (hz : z ∈ slitPlane) (n : ℕ) :
    stieltjesT f z =
      π / Complex.sin (π * α) * ∑ s ∈ Finset.range n, (-1) ^ s * a s * z ^ (-((s : ℂ) + α)) -
        ∑ s ∈ Finset.range n, (Nat.factorial s : ℂ) * stieltjesC f a α (s + 1) / z ^ (s + 1) +
        stieltjesR f a α n z := by
  induction n with
  | zero => simp [stieltjesR, stieltjesT, rem_zero]
  | succ n ih =>
    rw [ih, hS.stieltjesR_succ hα hz n, Finset.sum_range_succ, Finset.sum_range_succ]
    ring

/-- **DLMF 2.6.27** in DLMF's indexing: `∑_{s=1}^n (s−1)! cₛ/z^s`. -/
theorem dlmf_2_6_27_Icc (hα : α < 1) {z : ℂ} (hz : z ∈ slitPlane) (n : ℕ) :
    stieltjesT f z =
      π / Complex.sin (π * α) * ∑ s ∈ Finset.range n, (-1) ^ s * a s * z ^ (-((s : ℂ) + α)) -
        ∑ s ∈ Finset.Icc 1 n, (Nat.factorial (s - 1) : ℂ) * stieltjesC f a α s / z ^ s +
        stieltjesR f a α n z := by
  rw [hS.dlmf_2_6_27 hα hz n]
  congr 2
  rw [← Finset.Ico_succ_right_eq_Icc, Order.succ_eq_add_one, Finset.sum_Ico_eq_sum_range,
    Nat.add_sub_cancel]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [add_comm 1 s, Nat.add_sub_cancel]

/-! ### The remainder along the positive axis -/

/-- `Rₙ(x) = O(x^{−n−α})` as `x → +∞` through real values, `0 < α < 1`. -/
theorem stieltjesR_isBigO (hα : α < 1) (n : ℕ) :
    (fun x : ℝ => stieltjesR f a α n x) =O[atTop] fun x => x ^ (-(n + α)) := by
  obtain ⟨C, hC⟩ := (hS.rem_isBigO n).bound
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hC
  set T := max T₀ 1 with hT
  have hT1 : 1 ≤ T := le_max_right _ _
  have hT0 : 0 < T := by linarith
  -- the integrable majorant on `(0, T]`
  have hB : IntegrableOn (fun τ : ℝ => (τ : ℂ) ^ n * stieltjesRem f a α n τ) (Ioc 0 T) := by
    have h1 := hS.integrableOn_Ioc_pow_mul_rem n n (by linarith [hS.α_le])
    have h2 : IntegrableOn (fun τ : ℝ => (τ : ℂ) ^ n * stieltjesRem f a α n τ) (Icc 1 T) :=
      ((hS.locallyIntegrableOn_rem n).continuousOn_mul (continuous_ofReal.continuousOn.pow n)
        isOpen_Ioi.isLocallyClosed).integrableOn_compact_subset
        (fun τ hτ => lt_of_lt_of_le zero_lt_one hτ.1) isCompact_Icc
    have : Ioc 0 T ⊆ Ioc 0 1 ∪ Icc 1 T := fun τ hτ => by
      rcases le_or_gt τ 1 with h | h
      · exact Or.inl ⟨hτ.1, h⟩
      · exact Or.inr ⟨h.le, hτ.2⟩
    exact (h1.union h2).mono_set this
  set B : ℝ := ∫ τ in Ioc 0 T, ‖(τ : ℂ) ^ n * stieltjesRem f a α n τ‖
  have hB0 : 0 ≤ B := integral_nonneg fun _ => norm_nonneg _
  set K : ℝ := π / Real.sin (π * α)
  have hC0 : 0 ≤ C := by
    have := hT₀ T (le_max_left _ _)
    have h1 : 0 ≤ ‖T ^ (-(n + α))‖ := norm_nonneg _
    have h2 : 0 < ‖T ^ (-(n + α))‖ := by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg hT0.le _)]
      exact Real.rpow_pos_of_pos hT0 _
    nlinarith [norm_nonneg (stieltjesRem f a α n T)]
  have hK0 : 0 ≤ K := by
    have := Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hS.α_pos)
      (by nlinarith [Real.pi_pos, hS.α_pos] : π * α < π)
    positivity
  refine IsBigO.of_bound (B + C * K) ?_
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hx0 : 0 < x := by linarith
  have hxs : (x : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr hx0
  -- the integrand and its norm
  set G : ℝ → ℂ := fun τ => (τ : ℂ) ^ n * stieltjesRem f a α n τ / (τ + x) with hG
  have hGint : IntegrableOn G (Ioi 0) := hS.integrableOn_pow_mul_rem_div hxs n
  have hGnorm : ∀ τ : ℝ, 0 < τ → ‖G τ‖ = ‖(τ : ℂ) ^ n * stieltjesRem f a α n τ‖ / (τ + x) := by
    intro τ hτ
    rw [hG]
    simp only
    rw [norm_div, ← ofReal_add, norm_real, Real.norm_of_nonneg (by linarith)]
  -- split `∫₀^∞ ‖G‖` at `T`
  have hsplit : (∫ τ in Ioi (0 : ℝ), ‖G τ‖) =
      (∫ τ in Ioc 0 T, ‖G τ‖) + ∫ τ in Ioi T, ‖G τ‖ := by
    rw [← Ioc_union_Ioi_eq_Ioi hT0.le]
    exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (IntegrableOn.mono_set hGint.norm Ioc_subset_Ioi_self)
      (IntegrableOn.mono_set hGint.norm (Ioi_subset_Ioi hT0.le))
  -- piece 1: `∫₀^T ‖G‖ ≤ B/x`
  have hp1 : (∫ τ in Ioc 0 T, ‖G τ‖) ≤ B / x := by
    rw [div_eq_mul_inv, ← integral_mul_const]
    refine setIntegral_mono_on (IntegrableOn.mono_set hGint.norm Ioc_subset_Ioi_self)
      (hB.norm.mul_const _) measurableSet_Ioc fun τ hτ => ?_
    rw [hGnorm τ hτ.1, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ hx0 (by linarith [hτ.1])) (norm_nonneg _)
  -- piece 2: `∫_T^∞ ‖G‖ ≤ C K x^{−α}`
  have hreal : IntegrableOn (fun τ : ℝ => τ ^ (-α) / (τ + x)) (Ioi 0) := by
    refine IntegrableOn.congr_fun (integrableOn_cpow_neg_div_add hS.α_pos hα hxs).norm
      (fun τ hτ => ?_) measurableSet_Ioi
    have hτ0 : 0 < τ := hτ
    rw [norm_div, norm_cpow_eq_rpow_re_of_pos hτ0, neg_re, ofReal_re, ← ofReal_add, norm_real,
      Real.norm_of_nonneg (by linarith)]
  have hp2 : (∫ τ in Ioi T, ‖G τ‖) ≤ C * K * x ^ (-α) := by
    calc (∫ τ in Ioi T, ‖G τ‖) ≤ ∫ τ in Ioi T, C * (τ ^ (-α) / (τ + x)) := by
          refine setIntegral_mono_on (IntegrableOn.mono_set hGint.norm (Ioi_subset_Ioi hT0.le))
            (IntegrableOn.mono_set (hreal.const_mul C) (Ioi_subset_Ioi hT0.le)) measurableSet_Ioi
            fun τ hτ => ?_
          have hτ0 : 0 < τ := lt_trans hT0 hτ
          have hb := hT₀ τ (le_trans (le_max_left _ _) (le_of_lt hτ))
          rw [Real.norm_of_nonneg (Real.rpow_nonneg hτ0.le _)] at hb
          have e : τ ^ n * τ ^ (-(n + α)) = τ ^ (-α) := by
            rw [← Real.rpow_natCast, ← Real.rpow_add hτ0]
            congr 1
            ring
          rw [hGnorm τ hτ0, norm_mul, norm_pow, norm_real, Real.norm_of_nonneg hτ0.le,
            ← mul_div_assoc]
          refine div_le_div_of_nonneg_right ?_ (by linarith)
          calc τ ^ n * ‖stieltjesRem f a α n τ‖ ≤ τ ^ n * (C * τ ^ (-(n + α))) := by
                gcongr
            _ = C * τ ^ (-α) := by rw [← e]; ring
      _ ≤ ∫ τ in Ioi (0 : ℝ), C * (τ ^ (-α) / (τ + x)) := by
          refine setIntegral_mono_set (hreal.const_mul C) ?_
            (Ioi_subset_Ioi hT0.le).eventuallyLE
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
          have hτ0 : 0 < τ := hτ
          exact mul_nonneg hC0 (div_nonneg (Real.rpow_nonneg hτ0.le _) (by linarith))
      _ = C * K * x ^ (-α) := by
          rw [integral_const_mul, integral_rpow_neg_div_add hS.α_pos hα hx0]
          ring
  -- assemble
  have h2 : (∫ τ in Ioi (0 : ℝ), ‖G τ‖) ≤ (B + C * K) * x ^ (-α) := by
    rw [hsplit]
    have hx1 : B / x ≤ B * x ^ (-α) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx (by linarith)) hB0
    linarith
  have h1 : ‖∫ τ in Ioi (0 : ℝ), G τ‖ ≤ ∫ τ in Ioi (0 : ℝ), ‖G τ‖ :=
    norm_integral_le_integral_norm _
  have hbound : ‖stieltjesR f a α n x‖ ≤ (B + C * K) * x ^ (-(n + α)) := by
    show ‖(-1) ^ n / (x : ℂ) ^ n * ∫ τ in Ioi (0 : ℝ), G τ‖ ≤ _
    rw [norm_mul, norm_div, norm_pow, norm_neg, norm_one, one_pow, norm_pow, norm_real,
      Real.norm_of_nonneg hx0.le]
    calc 1 / x ^ n * ‖∫ τ in Ioi (0 : ℝ), G τ‖ ≤ 1 / x ^ n * ((B + C * K) * x ^ (-α)) := by
          gcongr
          exact h1.trans h2
      _ = (B + C * K) * x ^ (-(n + α)) := by
          rw [show -(n + α) = -(n : ℝ) + -α by ring, Real.rpow_add hx0,
            Real.rpow_neg hx0.le (n : ℝ), Real.rpow_natCast, Real.rpow_neg hx0.le]
          field_simp
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)]
  exact hbound

end StieltjesSetup

end Azurite.DLMF
