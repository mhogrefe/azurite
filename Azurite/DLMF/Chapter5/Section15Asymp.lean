/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section15
import Azurite.DLMF.Chapter5.Section11Psi

/-!
# DLMF 5.15.8–5.15.9: asymptotic expansions of the polygamma functions

On the slit plane, `ψ(z) = ln z + ∑_{s ≤ m+2} dₛ z^{−s} + Lₘ(z)` with the coefficients `dₛ` of
5.11.2 and the remainder `Lₘ(z) = ∫₀^∞ B̃_{m+2}(t)/(z + t)^{m+3} dt` (`Section11Psi.lean`). We
differentiate this identity `n` times: `dⁿ ln z = (−1)ⁿ⁻¹(n − 1)! z^{−n}`, `dⁿ z^{−s}` is explicit,
and differentiating under the integral sign gives
`dⁿ Lₘ = (−1)ⁿ (m + 3)⋯(m + n + 2) ∫₀^∞ B̃_{m+2}(t)/(z + t)^{m+n+3} dt = O(z^{−m−n−2})`
in `|ph z| ≤ π − δ`. The coefficients (`polygammaCoeff`) are identified with DLMF's
(`polygammaCoeff_self`, `polygammaCoeff_succ`, `polygammaCoeff_even`, `polygammaCoeff_odd`).
-/

open Complex Filter Topology Set MeasureTheory Finset
open scoped Real Nat

namespace Azurite.DLMF

/-- `∫₀^∞ B̃_{m+2}(t)/(z + t)^p dt`. -/
noncomputable def polyRem (m p : ℕ) (z : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), (periodicBernoulli (m + 2) t : ℂ) / (z + t) ^ p

theorem hasDerivAt_polyRem (m : ℕ) {p : ℕ} (hp : 2 ≤ p) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (polyRem m p) (-(p : ℂ) * polyRem m (p + 1) z) z := by
  obtain ⟨C, hC⟩ := periodicBernoulli_bound (m + 2)
  have h := hasDerivAt_integral_div_add_pow (measurable_periodicBernoulli (m + 2)) (C := C) hC hp hz
  refine h.congr_deriv ?_
  rw [polyRem, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  ring

theorem analyticOnNhd_polyRem (m : ℕ) {p : ℕ} (hp : 2 ≤ p) :
    AnalyticOnNhd ℂ (polyRem m p) slitPlane :=
  DifferentiableOn.analyticOnNhd (f := polyRem m p)
    (fun _ hz => (hasDerivAt_polyRem m hp hz).differentiableAt.differentiableWithinAt)
    isOpen_slitPlane

theorem iteratedDeriv_polyRem (m : ℕ) {p : ℕ} (hp : 2 ≤ p) :
    ∀ k, EqOn (iteratedDeriv k (polyRem m p))
      (fun z => (∏ i ∈ range k, (-(p : ℂ) - i)) * polyRem m (p + k) z) slitPlane
  | 0 => fun z _ => by simp
  | k + 1 => fun z hz => by
    have hev : iteratedDeriv k (polyRem m p) =ᶠ[𝓝 z]
        fun z => (∏ i ∈ range k, (-(p : ℂ) - i)) * polyRem m (p + k) z := by
      filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
      exact iteratedDeriv_polyRem m hp k hw
    rw [iteratedDeriv_succ, hev.deriv_eq,
      ((hasDerivAt_polyRem m (p := p + k) (by omega) hz).const_mul _).deriv, prod_range_succ]
    push_cast
    ring_nf

/-! ### The representation of `ψ⁽ⁿ⁾` -/

/-- The coefficients of the expansion of `ψ⁽ⁿ⁾` in powers of `1/z` (as produced by
differentiation; see `polygammaCoeff_self`, … for DLMF's form). -/
noncomputable def polygammaCoeff (n s : ℕ) : ℂ :=
  if s < n then 0 else if s = n then ∏ i ∈ range (n - 1), ((-1 : ℂ) - i)
  else psiCoeff (s - n) * ∏ i ∈ range n, ((-((s - n : ℕ) : ℤ) : ℂ) - i)

theorem digamma_eq_expansion {z : ℂ} (hz : z ∈ slitPlane) (m : ℕ) :
    digamma z = Complex.log z + ∑ s ∈ range (m + 3), psiCoeff s * z ^ (-(s : ℤ)) +
      polyRem m (m + 3) z := by
  rw [digamma_eq_log_sub_add_deriv hz, deriv_stirlingJ_eq hz m, sum_psiCoeff z m]
  have : stirlingL m z = polyRem m (m + 3) z := rfl
  rw [this]
  ring

theorem iteratedDeriv_log_eqOn {n : ℕ} (hn : 1 ≤ n) :
    EqOn (iteratedDeriv n Complex.log)
      (fun z => (∏ i ∈ range (n - 1), ((-1 : ℂ) - i)) * z ^ (-(n : ℤ))) slitPlane := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  intro z hz
  have hd : EqOn (deriv Complex.log) (fun z => z ^ (-1 : ℤ)) slitPlane := fun w hw => by
    simp [(hasDerivAt_log hw).deriv]
  rw [iteratedDeriv_succ', hd.iteratedDeriv_of_isOpen isOpen_slitPlane k hz,
    iteratedDeriv_eq_iterate, iter_deriv_zpow]
  simp only [Nat.add_sub_cancel]
  congr 2 <;> push_cast <;> ring

theorem contDiffAt_zpow' {z : ℂ} (hz : z ≠ 0) (s : ℤ) (k : ℕ) :
    ContDiffAt ℂ k (fun w : ℂ => w ^ s) z :=
  (((differentiableOn_zpow s {w | w ≠ 0} (Or.inl (by simp))).analyticOnNhd
    isOpen_ne) z hz).contDiffAt

/-- `ψ⁽ⁿ⁾(z) = ∑_{s < m+n+3} cₛ z^{−s} + (−1)ⁿ(m+3)⋯(m+n+2) ∫ B̃_{m+2}/(z + t)^{m+n+3}`. -/
theorem polygamma_eq_expansion {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z ∈ slitPlane) (m : ℕ) :
    polygamma n z = ∑ s ∈ range (n + (m + 3)), polygammaCoeff n s * z ^ (-(s : ℤ)) +
      (∏ i ∈ range n, (-((m + 3 : ℕ) : ℂ) - i)) * polyRem m (m + 3 + n) z := by
  have hz0 := slitPlane_ne_zero hz
  set E : ℂ → ℂ := fun w => Complex.log w + ∑ s ∈ range (m + 3), psiCoeff s * w ^ (-(s : ℤ)) +
    polyRem m (m + 3) w
  have heq : EqOn digamma E slitPlane := fun w hw => digamma_eq_expansion hw m
  have hp : polygamma n z = iteratedDeriv n E z := heq.iteratedDeriv_of_isOpen isOpen_slitPlane n hz
  have hlog : ContDiffAt ℂ n Complex.log z := (analyticAt_clog hz).contDiffAt
  have hpow : ∀ s ∈ range (m + 3), ContDiffAt ℂ n (fun w => psiCoeff s * w ^ (-(s : ℤ))) z :=
    fun s _ => contDiffAt_const.mul (contDiffAt_zpow' hz0 _ n)
  have hsum : ContDiffAt ℂ n (fun w => ∑ s ∈ range (m + 3), psiCoeff s * w ^ (-(s : ℤ))) z :=
    ContDiffAt.sum hpow
  have hrem : ContDiffAt ℂ n (polyRem m (m + 3)) z :=
    (analyticOnNhd_polyRem m (by omega) z hz).contDiffAt
  have hE : iteratedDeriv n E z = iteratedDeriv n Complex.log z +
      ∑ s ∈ range (m + 3), psiCoeff s * iteratedDeriv n (fun w => w ^ (-(s : ℤ))) z +
        iteratedDeriv n (polyRem m (m + 3)) z := by
    rw [show E = (Complex.log + fun w => ∑ s ∈ range (m + 3), psiCoeff s * w ^ (-(s : ℤ))) +
      polyRem m (m + 3) from rfl,
      iteratedDeriv_add (f := Complex.log + fun w => ∑ s ∈ range (m + 3),
        psiCoeff s * w ^ (-(s : ℤ))) (g := polyRem m (m + 3)) (hlog.add hsum) hrem,
      iteratedDeriv_add (f := Complex.log) hlog hsum, iteratedDeriv_finsetSum _ n hpow]
    congr 2
    refine sum_congr rfl fun s _ => ?_
    exact iteratedDeriv_const_mul _ (contDiffAt_zpow' hz0 _ n)
  rw [hp, hE, iteratedDeriv_log_eqOn hn hz, iteratedDeriv_polyRem m (by omega) n hz]
  simp only [iteratedDeriv_eq_iterate, iter_deriv_zpow]
  have hlow : ∑ s ∈ range n, polygammaCoeff n s * z ^ (-(s : ℤ)) = 0 :=
    sum_eq_zero fun s hs => by
      rw [polygammaCoeff, ite_eq_left_of_eq_true _ _ (eq_true (mem_range.mp hs)), zero_mul]
  have hterm : ∀ t : ℕ, polygammaCoeff n (n + t) * z ^ (-((n + t : ℕ) : ℤ)) =
      (if t = 0 then (∏ i ∈ range (n - 1), ((-1 : ℂ) - i)) * z ^ (-(n : ℤ)) else 0) +
        psiCoeff t * ((∏ i ∈ range n, (((-(t : ℤ) : ℤ) : ℂ) - i)) * z ^ (-(t : ℤ) - n)) := by
    intro t
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp [polygammaCoeff, psiCoeff]
    · rw [polygammaCoeff, ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
        ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
        ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
        show n + t - n = t by omega,
        show -((n + t : ℕ) : ℤ) = -(t : ℤ) - n by push_cast; ring]
      push_cast
      ring
  rw [sum_range_add (fun s => polygammaCoeff n s * z ^ (-(s : ℤ))) n (m + 3), hlow, zero_add,
    sum_congr rfl fun t _ => hterm t, sum_add_distrib, sum_ite_eq' (range (m + 3)) 0]
  simp only [Finset.mem_range, show 0 < m + 3 by omega, ↓reduceIte]

/-! ### The expansion -/

/-- **DLMF 5.15.9**: `ψ⁽ⁿ⁾(z) ∼ ∑ₛ cₛ z^{−s}` as `z → ∞` in `|ph z| ≤ π − δ`, `n ≥ 1`, with
`cₙ = (−1)ⁿ⁻¹(n − 1)!`, `cₙ₊₁ = (−1)ⁿ⁻¹ n!/2`, `c_{n+2k} = (−1)ⁿ⁻¹ (2k + n − 1)!/(2k)! B_{2k}`,
`c_{n+2k+1} = 0` (`k ≥ 1`), `cₛ = 0` (`s < n`); see `polygammaCoeff_self`, `polygammaCoeff_succ`,
`polygammaCoeff_even`, `polygammaCoeff_odd`. -/
theorem dlmf_5_15_9 {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ ≤ π) :
    IsAsympExpansionDLMF (closedSectorDLMF 0 (π - δ)) (polygamma n) (polygammaCoeff n) := by
  intro N hN
  set m := N
  set p := m + 3 + n
  obtain ⟨C, hC⟩ := periodicBernoulli_bound (m + 2)
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  set sδ := Real.sin (δ / 2)
  have hs0 : 0 < sδ := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  set c : ℂ := ∏ i ∈ range n, (-((m + 3 : ℕ) : ℂ) - i)
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (1 : ℝ) < p := by simp only [p]; push_cast; linarith [(N.cast_nonneg : (0:ℝ) ≤ N)]
    linarith
  refine isBoundedUnder_of_eventually_le (a := ∑ s ∈ Ico N (n + (m + 3)), ‖polygammaCoeff n s‖ +
    ‖c‖ * (C / (sδ ^ p * ((p : ℝ) - 1)))) ?_
  have hA : ∀ᶠ z in Bornology.cobounded ℂ ⊓ 𝓟 (closedSectorDLMF 0 (π - δ)), 1 ≤ ‖z‖ :=
    (tendsto_norm_cobounded_atTop.eventually_ge_atTop 1).filter_mono inf_le_left
  have hB : ∀ᶠ z in Bornology.cobounded ℂ ⊓ 𝓟 (closedSectorDLMF 0 (π - δ)),
      z ∈ closedSectorDLMF 0 (π - δ) := mem_inf_of_right (mem_principal_self _)
  filter_upwards [hA, hB] with z h1 hz
  obtain ⟨hz0, harg⟩ := hz
  simp only [ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, mul_one] at harg
  have hslit : z ∈ slitPlane := mem_slitPlane_iff_arg.mpr ⟨fun h => by
    rw [h, abs_of_pos Real.pi_pos] at harg; linarith, hz0⟩
  have hL := (integrableOn_div_add_pow (measurable_periodicBernoulli (m + 2)) (C := C) hC hz0 hδ
    hδπ harg (m := p) (by omega)).2
  have hLe : ‖polyRem m p z‖ ≤ C / (sδ ^ p * (((p : ℝ) - 1) * ‖z‖ ^ (p - 1))) := hL
  have hrep : polygamma n z - ∑ s ∈ range N, polygammaCoeff n s * z ^ (-(s : ℤ)) =
      ∑ s ∈ Ico N (n + (m + 3)), polygammaCoeff n s * z ^ (-(s : ℤ)) + c * polyRem m p z := by
    rw [polygamma_eq_expansion hn hslit m, ← sum_range_add_sum_Ico _ (show N ≤ n + (m + 3) by
      omega)]
    ring
  have hz1 : 0 < ‖z‖ := by linarith
  have hzN : ‖z ^ (-(m : ℤ))‖ = (‖z‖ ^ m)⁻¹ := by rw [norm_zpow, zpow_neg, zpow_natCast]
  rw [hrep, add_div]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_div, hzN, div_inv_eq_mul]
    calc ‖∑ s ∈ Ico m (n + (m + 3)), polygammaCoeff n s * z ^ (-(s : ℤ))‖ * ‖z‖ ^ m
        ≤ (∑ s ∈ Ico m (n + (m + 3)), ‖polygammaCoeff n s * z ^ (-(s : ℤ))‖) * ‖z‖ ^ m := by
          gcongr; exact norm_sum_le _ _
      _ = ∑ s ∈ Ico m (n + (m + 3)), ‖polygammaCoeff n s‖ * (‖z‖ ^ m / ‖z‖ ^ s) := by
          rw [sum_mul]
          refine sum_congr rfl fun s _ => ?_
          rw [norm_mul, norm_zpow, zpow_neg, zpow_natCast]
          field_simp
      _ ≤ ∑ s ∈ Ico m (n + (m + 3)), ‖polygammaCoeff n s‖ * 1 := by
          refine sum_le_sum fun s hs => ?_
          gcongr
          rw [div_le_one (by positivity)]
          exact pow_le_pow_right₀ h1 (mem_Ico.mp hs).1
      _ = _ := by simp; rfl
  · rw [norm_div, hzN, div_inv_eq_mul, norm_mul, mul_assoc]
    gcongr
    have hzp : ‖z‖ ^ m ≤ ‖z‖ ^ (p - 1) := pow_le_pow_right₀ h1 (by simp only [p, m]; omega)
    calc ‖polyRem m p z‖ * ‖z‖ ^ m
        ≤ C / (sδ ^ p * (((p : ℝ) - 1) * ‖z‖ ^ (p - 1))) * ‖z‖ ^ (p - 1) := by
          gcongr
      _ = C / (sδ ^ p * ((p : ℝ) - 1)) := by field_simp

/-! ### DLMF's form of the coefficients -/

theorem prod_neg_one_sub (k : ℕ) : ∏ i ∈ range k, ((-1 : ℂ) - i) = (-1) ^ k * (k ! : ℂ) := by
  induction k with
  | zero => simp
  | succ k ih => rw [prod_range_succ, ih, Nat.factorial_succ]; push_cast; ring

theorem prod_neg_natCast_sub (a k : ℕ) :
    ∏ i ∈ range k, (-((a : ℤ) : ℂ) - (i : ℂ)) = (-1) ^ k * ∏ i ∈ range k, ((a : ℂ) + i) := by
  have e : ∀ i ∈ range k, (-((a : ℤ) : ℂ) - (i : ℂ)) = (-1) * ((a : ℂ) + i) := fun i _ => by
    push_cast; ring
  rw [prod_congr rfl e, prod_mul_distrib, prod_const, card_range]

theorem factorial_mul_prod_add {a : ℕ} (ha : 1 ≤ a) (k : ℕ) :
    ((a - 1) ! : ℂ) * ∏ i ∈ range k, ((a : ℂ) + i) = ((a + k - 1) ! : ℂ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [prod_range_succ, ← mul_assoc, ih, show a + (k + 1) - 1 = (a + k - 1) + 1 by omega,
      Nat.factorial_succ]
    push_cast [show a + k - 1 + 1 = a + k by omega, Nat.cast_sub (show 1 ≤ a + k by omega)]
    ring

theorem polygammaCoeff_lt {n s : ℕ} (hs : s < n) : polygammaCoeff n s = 0 := by
  simp [polygammaCoeff, hs]

/-- `cₙ = (−1)ⁿ⁻¹ (n − 1)!`. -/
theorem polygammaCoeff_self (n : ℕ) : polygammaCoeff n n = (-1) ^ (n - 1) * ((n - 1) ! : ℂ) := by
  simp [polygammaCoeff, prod_neg_one_sub]

/-- `cₙ₊₁ = (−1)ⁿ⁻¹ n!/2`. -/
theorem polygammaCoeff_succ {n : ℕ} (hn : 1 ≤ n) :
    polygammaCoeff n (n + 1) = (-1) ^ (n - 1) * (n ! : ℂ) / 2 := by
  rw [polygammaCoeff, ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
    ite_eq_right_of_eq_false _ _ (eq_false (by omega)), show n + 1 - n = 1 by omega]
  have hf := factorial_mul_prod_add (a := 1) le_rfl n
  rw [prod_neg_natCast_sub, show 1 + n - 1 = n by omega] at *
  simp only [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, one_mul] at hf
  simp only [Nat.cast_one]
  rw [hf]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [psiCoeff, one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, pow_succ]
  ring

/-- `c_{n+2k} = (−1)ⁿ⁻¹ (2k + n − 1)!/(2k)! B_{2k}`, `k ≥ 1`. -/
theorem polygammaCoeff_even {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) :
    polygammaCoeff n (2 * k + n) =
      (-1) ^ (n - 1) * (((2 * k + n - 1) ! : ℂ) / ((2 * k) ! : ℂ)) * (bernoulli (2 * k) : ℂ) := by
  rw [polygammaCoeff, ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
    ite_eq_right_of_eq_false _ _ (eq_false (by omega)), show 2 * k + n - n = 2 * k by omega,
    psiCoeff_even hk, prod_neg_natCast_sub]
  have hfa := factorial_mul_prod_add (a := 2 * k) (by omega) n
  have h2k : ((2 * k) ! : ℂ) = (2 * k : ℂ) * ((2 * k - 1) ! : ℂ) := by
    obtain ⟨j, hj⟩ : ∃ j, 2 * k = j + 1 := ⟨2 * k - 1, by omega⟩
    have hjc : (2 * (k : ℂ)) = (j : ℂ) + 1 := by exact_mod_cast hj
    rw [hj, Nat.factorial_succ, Nat.add_sub_cancel]; push_cast
    linear_combination -((j ! : ℕ) : ℂ) * hjc
  have hf0 : ((2 * k - 1) ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hk0 : (2 * k : ℂ) ≠ 0 := by exact_mod_cast (show 2 * k ≠ 0 by omega)
  rw [show 2 * k + n - 1 = 2 * k + n - 1 from rfl, ← hfa, h2k]
  push_cast
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel, pow_succ]
  field_simp

/-- `c_{n+2k+1} = 0`, `k ≥ 1`. -/
theorem polygammaCoeff_odd {n k : ℕ} (hk : 1 ≤ k) : polygammaCoeff n (2 * k + 1 + n) = 0 := by
  rw [polygammaCoeff, ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
    ite_eq_right_of_eq_false _ _ (eq_false (by omega)), show 2 * k + 1 + n - n = 2 * k + 1 by omega,
    psiCoeff_odd hk, zero_mul]

/-- **DLMF 5.15.8**: `ψ′(z) ∼ 1/z + 1/(2z²) + ∑_{k≥1} B_{2k}/z^{2k+1}` as `z → ∞` in
`|ph z| ≤ π − δ` (coefficients `polygammaCoeff 1`: see `polygammaCoeff_one_one`,
`polygammaCoeff_one_two`, `polygammaCoeff_one_odd`, `polygammaCoeff_one_even`;
`ψ′ = polygamma 1`, `polygamma_one_eq_deriv`). -/
theorem dlmf_5_15_8 {δ : ℝ} (hδ : 0 < δ) (hδπ : δ ≤ π) :
    IsAsympExpansionDLMF (closedSectorDLMF 0 (π - δ)) (polygamma 1) (polygammaCoeff 1) :=
  dlmf_5_15_9 le_rfl hδ hδπ

theorem polygammaCoeff_one_one : polygammaCoeff 1 1 = 1 := by simp [polygammaCoeff_self]

theorem polygammaCoeff_one_two : polygammaCoeff 1 2 = 1 / 2 := by
  rw [polygammaCoeff_succ le_rfl]; simp

theorem polygammaCoeff_one_odd {k : ℕ} (hk : 1 ≤ k) :
    polygammaCoeff 1 (2 * k + 1) = (bernoulli (2 * k) : ℂ) := by
  rw [polygammaCoeff_even le_rfl hk]
  have : ((2 * k) ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  simp [this]

theorem polygammaCoeff_one_even {k : ℕ} (hk : 1 ≤ k) : polygammaCoeff 1 (2 * k + 2) = 0 :=
  polygammaCoeff_odd hk

end Azurite.DLMF
