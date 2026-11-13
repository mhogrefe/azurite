/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section15

/-!
# DLMF §5.16: Sums

Formalization of <https://dlmf.nist.gov/5.16>.

* 5.16.1: `∑_{k≥1} (−1)ᵏ ψ′(k) = −π²/8`. Since `ψ′(k) ~ 1/k` the series converges only
  conditionally (`not_summable_dlmf_5_16_1`), so it is stated as the limit of its partial sums
  (`dlmf_5_16_1`). Pairing consecutive terms gives `ψ′(2m + 2) − ψ′(2m + 1) = −1/(2m + 1)²`
  (5.15.5), and `∑ 1/(2m + 1)² = (1 − 2⁻²) ζ(2)`.
* 5.16.2: `∑_{k≥1} ψ′(k + 1)/k = ζ(3) = −ψ″(1)/2`. With `ψ′(k + 1) = ∑_{m≥1} 1/(k + m)²`
  the sum is `T = ∑_{k,m≥1} 1/(k(k + m)²)`. The symmetric double sum
  `S = ∑_{k,m≥1} 1/(km(k + m))` equals `2T` (split `1/(km) = (1/k + 1/m)/(k + m)`) and also
  `∑_k H_k/k² = T + ζ(3)` (telescoping over `m`, then regrouping by `k + m`), so `T = ζ(3)`.
-/

open Complex Filter Topology Finset
open scoped Real Nat

namespace Azurite.DLMF

/-- `∑_{j≥0} 1/(j + k + 2)²`, which is `ψ′(k + 2)` (`polygamma_one_nat_add_two`). -/
noncomputable def trigammaTail (k : ℕ) : ℝ := ∑' j : ℕ, 1 / ((j : ℝ) + k + 2) ^ 2

theorem hasSum_telescope_of_antitone {f : ℕ → ℝ} (hf : Antitone f)
    (h0 : Tendsto f atTop (𝓝 0)) : HasSum (fun n => f n - f (n + 1)) (f 0) := by
  refine (hasSum_iff_tendsto_nat_of_nonneg (fun n => sub_nonneg.2 (hf n.le_succ)) _).2 ?_
  simp_rw [Finset.sum_range_sub']
  simpa using (tendsto_const_nhds (x := f 0)).sub h0

theorem tendsto_one_div_natCast_add {c : ℝ} :
    Tendsto (fun m : ℕ => 1 / ((m : ℝ) + c)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

theorem antitone_one_div_natCast_add {c : ℝ} (hc : 0 < c) :
    Antitone fun m : ℕ => 1 / ((m : ℝ) + c) := fun a b hab => by
  have ha : (0 : ℝ) ≤ a := a.cast_nonneg
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  exact one_div_le_one_div_of_le (by linarith) (by linarith)

/-- `∑_{m≥0} (1/(m + c) − 1/(m + c + 1)) = 1/c`. -/
theorem hasSum_one_div_sub_one_div {c : ℝ} (hc : 0 < c) :
    HasSum (fun m : ℕ => 1 / ((m : ℝ) + c) - 1 / ((m : ℝ) + (c + 1))) (1 / c) := by
  have h := hasSum_telescope_of_antitone (antitone_one_div_natCast_add hc)
    tendsto_one_div_natCast_add
  convert h using 1
  · funext m; push_cast; ring_nf
  · simp

theorem hasSum_trigammaTail (k : ℕ) :
    HasSum (fun j : ℕ => 1 / ((j : ℝ) + k + 2) ^ 2) (trigammaTail k) := by
  refine Summable.hasSum ?_
  have h := (summable_nat_add_iff (k + 2)).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  convert h using 2 with j
  push_cast; ring

theorem trigammaTail_le (k : ℕ) : trigammaTail k ≤ 1 / ((k : ℝ) + 1) := by
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  have h := hasSum_one_div_sub_one_div (c := (k : ℝ) + 1) (by positivity)
  refine hasSum_le (fun j => ?_) (hasSum_trigammaTail k) h
  have hj : (0 : ℝ) ≤ j := j.cast_nonneg
  rw [div_sub_div _ _ (by positivity) (by positivity),
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem le_trigammaTail (k : ℕ) : 1 / ((k : ℝ) + 2) ≤ trigammaTail k := by
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  have h := hasSum_one_div_sub_one_div (c := (k : ℝ) + 2) (by positivity)
  refine hasSum_le (fun j => ?_) h (hasSum_trigammaTail k)
  have hj : (0 : ℝ) ≤ j := j.cast_nonneg
  rw [div_sub_div _ _ (by positivity) (by positivity),
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem trigammaTail_nonneg (k : ℕ) : 0 ≤ trigammaTail k :=
  (hasSum_trigammaTail k).nonneg fun j => by positivity

theorem tendsto_trigammaTail : Tendsto trigammaTail atTop (𝓝 0) :=
  squeeze_zero trigammaTail_nonneg trigammaTail_le tendsto_one_div_natCast_add

/-- `ψ′(k + 2) = ∑_{j≥0} 1/(j + k + 2)²`. -/
theorem polygamma_one_nat_add_two (k : ℕ) :
    polygamma 1 ((k : ℂ) + 2) = trigammaTail k := by
  have hz : (k : ℂ) + 2 ∉ gammaPoles := not_mem_gammaPoles_of_re_pos (by
    simp only [add_re, natCast_re, re_ofNat]; positivity)
  refine (dlmf_5_15_1 hz).unique ?_
  have h := Complex.hasSum_ofReal.mpr (hasSum_trigammaTail k)
  convert h using 1
  funext j; push_cast; ring

theorem tendsto_polygamma_one_nat :
    Tendsto (fun N : ℕ => polygamma 1 (N : ℂ)) atTop (𝓝 0) := by
  refine (tendsto_add_atTop_iff_nat 2).mp ?_
  have h := (Complex.continuous_ofReal.tendsto 0).comp tendsto_trigammaTail
  simp only [Complex.ofReal_zero] at h
  refine h.congr fun k => ?_
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_ofNat, polygamma_one_nat_add_two]

/-- `ψ′(z + 1) − ψ′(z) = −1/z²` at `z = 2m + 1`. -/
theorem polygamma_one_odd_succ (m : ℕ) :
    polygamma 1 (2 * (m : ℂ) + 2) - polygamma 1 (2 * (m : ℂ) + 1) =
      -(1 / (2 * (m : ℂ) + 1) ^ 2) := by
  have hz : 2 * (m : ℂ) + 1 ∉ gammaPoles := not_mem_gammaPoles_of_re_pos (by
    have : (2 * (m : ℂ) + 1).re = 2 * (m : ℝ) + 1 := by simp
    rw [this]; positivity)
  have h := dlmf_5_15_5 le_rfl hz
  rw [show 2 * (m : ℂ) + 1 + 1 = 2 * (m : ℂ) + 2 by ring] at h
  rw [h, show (-((1 : ℕ) : ℤ) - 1) = -2 by norm_num, zpow_neg, zpow_two]
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, mul_one]
  ring

/-- Partial sums `∑_{k=1}^{N} (−1)ᵏ ψ′(k)`. -/
noncomputable def altTrigammaSum (N : ℕ) : ℂ :=
  ∑ k ∈ range N, (-1 : ℂ) ^ (k + 1) * polygamma 1 ((k : ℂ) + 1)

theorem altTrigammaSum_two_mul (M : ℕ) :
    altTrigammaSum (2 * M) = -∑ m ∈ range M, 1 / (2 * (m : ℂ) + 1) ^ 2 := by
  induction M with
  | zero => simp [altTrigammaSum]
  | succ M ih =>
    have hs : altTrigammaSum (2 * (M + 1)) = altTrigammaSum (2 * M) +
        ((-1 : ℂ) ^ (2 * M + 1) * polygamma 1 (((2 * M : ℕ) : ℂ) + 1) +
          (-1 : ℂ) ^ (2 * M + 1 + 1) * polygamma 1 (((2 * M + 1 : ℕ) : ℂ) + 1)) := by
      rw [show 2 * (M + 1) = 2 * M + 1 + 1 by ring, altTrigammaSum, sum_range_succ,
        sum_range_succ, ← altTrigammaSum]
      ring
    have e1 : (-1 : ℂ) ^ (2 * M + 1) = -1 := by rw [pow_succ, pow_mul, neg_one_sq, one_pow]; ring
    have e2 : (-1 : ℂ) ^ (2 * M + 1 + 1) = 1 := by
      rw [pow_succ, e1]; ring
    rw [hs, ih, sum_range_succ, e1, e2]
    have h := polygamma_one_odd_succ M
    push_cast
    rw [show 2 * (M : ℂ) + 1 + 1 = 2 * (M : ℂ) + 2 by ring]
    linear_combination h

theorem altTrigammaSum_two_mul_add_one (M : ℕ) :
    altTrigammaSum (2 * M + 1) =
      altTrigammaSum (2 * M) - polygamma 1 ((2 * M + 1 : ℕ) : ℂ) := by
  rw [altTrigammaSum, sum_range_succ, ← altTrigammaSum, pow_succ, pow_mul, neg_one_sq,
    one_pow]
  push_cast; ring

/-- **DLMF 5.16.1**: `∑_{k=1}^∞ (−1)ᵏ ψ′(k) = −π²/8`, as the limit of the partial sums (the
series converges only conditionally, `not_summable_dlmf_5_16_1`). -/
theorem dlmf_5_16_1 : Tendsto altTrigammaSum atTop (𝓝 (-(π : ℂ) ^ 2 / 8)) := by
  have hodd := (hasSum_odd_inv_pow_zeta (n := 1) le_rfl).tendsto_sum_nat
  rw [show ((1 : ℕ) : ℂ) + 1 = 2 by norm_num, riemannZeta_two] at hodd
  have hE : Tendsto (fun M => altTrigammaSum (2 * M)) atTop (𝓝 (-(π : ℂ) ^ 2 / 8)) := by
    simp only [altTrigammaSum_two_mul]
    convert hodd.neg using 2
    norm_num; ring
  set c : ℕ → ℂ := fun N => if Even N then 0 else polygamma 1 (N : ℂ)
  have hc : Tendsto c atTop (𝓝 0) := by
    refine squeeze_zero_norm (f := c) (a := fun N : ℕ => ‖polygamma 1 (N : ℂ)‖) (fun N => ?_) ?_
    · simp only [c]; split_ifs <;> simp
    · simpa using tendsto_polygamma_one_nat.norm
  have heq : ∀ N, altTrigammaSum N = altTrigammaSum (2 * (N / 2)) - c N := by
    intro N
    obtain ⟨M, rfl | rfl⟩ := Nat.even_or_odd' N
    · simp [c, Nat.mul_div_cancel_left M two_pos]
    · rw [show (2 * M + 1) / 2 = M by omega, altTrigammaSum_two_mul_add_one]
      simp [c, Nat.not_even_bit1]
  have hdiv : Tendsto (fun N : ℕ => N / 2) atTop atTop := Nat.tendsto_div_const_atTop two_ne_zero
  simpa [← heq] using (hE.comp hdiv).sub hc

/-- The series 5.16.1 is not absolutely (unconditionally) convergent: `ψ′(k) ≥ 1/k`. -/
theorem not_summable_dlmf_5_16_1 :
    ¬ Summable fun k : ℕ => (-1 : ℂ) ^ (k + 1) * polygamma 1 ((k : ℂ) + 1) := by
  intro h
  have hn := ((summable_nat_add_iff 1).mpr h).norm
  have hb : Summable fun k : ℕ => 1 / ((k : ℝ) + 2) := by
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hn
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    rw [show (((k + 1 : ℕ) : ℂ) + 1) = (k : ℂ) + 2 by push_cast; ring,
      polygamma_one_nat_add_two, Complex.norm_real, Real.norm_of_nonneg (trigammaTail_nonneg k)]
    exact le_trigammaTail k
  have h2 := (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ)) 2).mp (by
    convert hb using 2 with k; push_cast; ring)
  exact Real.not_summable_one_div_natCast h2

/-! ### 5.16.2 -/

/-- `B(k, m) = 1/((k + 1)(k + m + 2)²)`; `∑_m B(k, m) = ψ′(k + 2)/(k + 1)`. -/
noncomputable def zetaThreeB (p : ℕ × ℕ) : ℝ := 1 / (((p.1 : ℝ) + 1) * ((p.1 : ℝ) + p.2 + 2) ^ 2)

/-- `A(k, m) = 1/((k + 1)(m + 1)(k + m + 2)) = B(k, m) + B(m, k)`. -/
noncomputable def zetaThreeA (p : ℕ × ℕ) : ℝ :=
  1 / (((p.1 : ℝ) + 1) * ((p.2 : ℝ) + 1) * ((p.1 : ℝ) + p.2 + 2))

/-- The harmonic numbers `Hₙ = ∑_{i<n} 1/(i + 1)` as reals. -/
noncomputable def harmonicReal (n : ℕ) : ℝ := ∑ i ∈ range n, 1 / ((i : ℝ) + 1)

theorem zetaThreeA_eq (p : ℕ × ℕ) : zetaThreeA p = zetaThreeB p + zetaThreeB p.swap := by
  have h1 : (0 : ℝ) ≤ p.1 := p.1.cast_nonneg
  have h2 : (0 : ℝ) ≤ p.2 := p.2.cast_nonneg
  simp only [zetaThreeA, zetaThreeB, Prod.fst_swap, Prod.snd_swap]
  field_simp
  ring

theorem hasSum_zetaThreeB_fiber (k : ℕ) :
    HasSum (fun m => zetaThreeB (k, m)) (trigammaTail k / ((k : ℝ) + 1)) := by
  convert (hasSum_trigammaTail k).mul_left (1 / ((k : ℝ) + 1)) using 1
  · funext m; simp only [zetaThreeB]
    rw [one_div_mul_one_div, add_comm (m : ℝ) (k : ℝ)]
  · ring

theorem summable_one_div_nat_add_one_sq :
    Summable fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2 := by
  have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  convert h using 2 with k
  push_cast; ring

theorem hasSum_zetaThreeB : HasSum zetaThreeB (∑' p, zetaThreeB p) := by
  refine Summable.hasSum ((summable_prod_of_nonneg (fun p => by
    simp only [Pi.zero_apply, zetaThreeB]; positivity)).2
    ⟨fun k => (hasSum_zetaThreeB_fiber k).summable, ?_⟩)
  simp only [fun k => (hasSum_zetaThreeB_fiber k).tsum_eq]
  refine Summable.of_nonneg_of_le (fun k => div_nonneg (trigammaTail_nonneg k) (by positivity))
    (fun k => ?_) summable_one_div_nat_add_one_sq
  have hk : (0 : ℝ) < k + 1 := by positivity
  calc trigammaTail k / ((k : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) / ((k : ℝ) + 1) :=
        div_le_div_of_nonneg_right (trigammaTail_le k) hk.le
    _ = 1 / ((k : ℝ) + 1) ^ 2 := by rw [div_div, sq]

/-- `∑_{m≥0} A(k, m) = H_{k+1}/(k + 1)²`, by telescoping. -/
theorem hasSum_zetaThreeA_fiber (k : ℕ) :
    HasSum (fun m => zetaThreeA (k, m)) (harmonicReal (k + 1) / ((k : ℝ) + 1) ^ 2) := by
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  have ht : HasSum (fun m : ℕ => 1 / ((m : ℝ) + 1) - 1 / ((m : ℝ) + ((k : ℝ) + 2)))
      (harmonicReal (k + 1)) := by
    have hs := hasSum_sum (s := range (k + 1))
      (f := fun (i : ℕ) (m : ℕ) =>
        1 / ((m : ℝ) + ((i : ℝ) + 1)) - 1 / ((m : ℝ) + ((i : ℝ) + 1 + 1)))
      (fun i _ => hasSum_one_div_sub_one_div (by positivity))
    rw [harmonicReal]
    convert hs using 1
    funext m
    have e := Finset.sum_range_sub' (fun i : ℕ => 1 / ((m : ℝ) + ((i : ℝ) + 1))) (k + 1)
    simp only [Nat.cast_add, Nat.cast_one] at e
    rw [show (fun i : ℕ => 1 / ((m : ℝ) + ((i : ℝ) + 1)) - 1 / ((m : ℝ) + ((i : ℝ) + 1 + 1))) =
      fun i : ℕ => 1 / ((m : ℝ) + ((i : ℝ) + 1)) - 1 / ((m : ℝ) + (((i : ℝ) + 1) + 1)) from rfl,
      e]
    push_cast; ring_nf
  convert ht.mul_left (1 / ((k : ℝ) + 1) ^ 2) using 1
  · funext m
    have hm : (0 : ℝ) ≤ m := m.cast_nonneg
    simp only [zetaThreeA]
    field_simp
    ring
  · ring

theorem hasSum_harmonicReal_div :
    HasSum (fun k : ℕ => harmonicReal k / ((k : ℝ) + 1) ^ 2) (∑' p, zetaThreeB p) := by
  have hσ := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)).hasSum_iff.mpr
    hasSum_zetaThreeB
  have h2 : HasSum (fun n : ℕ => harmonicReal (n + 1) / ((n : ℝ) + 2) ^ 2)
      (∑' p, zetaThreeB p) := by
    refine hσ.sigma fun n => ?_
    convert Finset.hasSum (antidiagonal n) zetaThreeB using 1
    · funext c; rfl
    have hc : ∀ p ∈ antidiagonal n, zetaThreeB p = 1 / ((p.1 : ℝ) + 1) * (1 / ((n : ℝ) + 2) ^ 2) :=
      fun p hp => by
        have e : (p.1 : ℝ) + p.2 = n := by exact_mod_cast Finset.mem_antidiagonal.mp hp
        simp only [zetaThreeB]
        rw [e, one_div_mul_one_div]
    rw [Finset.sum_congr rfl hc, ← Finset.sum_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, harmonicReal]
    ring
  refine (hasSum_nat_add_iff' 1).mp ?_
  simp only [range_one, sum_singleton, harmonicReal, range_zero, sum_empty, zero_div, sub_zero]
  convert h2 using 1
  funext n
  simp only [harmonicReal]
  push_cast; ring_nf

theorem hasSum_one_div_nat_add_one_cube :
    HasSum (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 3) (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 3) := by
  refine Summable.hasSum ?_
  have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr
    (show 1 < 3 by norm_num))
  convert h using 2 with k
  push_cast; ring

/-- `∑_{k≥1} ψ′(k + 1)/k = ζ(3)` in real form: `∑_{k≥0} ψ′(k + 2)/(k + 1) = ∑ 1/(k + 1)³`. -/
theorem hasSum_trigammaTail_div :
    HasSum (fun k : ℕ => trigammaTail k / ((k : ℝ) + 1)) (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 3) := by
  set T := ∑' p, zetaThreeB p
  have hz3 := hasSum_one_div_nat_add_one_cube
  have hT1 : HasSum (fun k : ℕ => trigammaTail k / ((k : ℝ) + 1)) T :=
    hasSum_zetaThreeB.prod_fiberwise hasSum_zetaThreeB_fiber
  have hA : HasSum zetaThreeA (T + T) := by
    have hs : HasSum (fun p : ℕ × ℕ => zetaThreeB p.swap) T :=
      (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hasSum_zetaThreeB
    convert hasSum_zetaThreeB.add hs using 1
    funext p; exact zetaThreeA_eq p
  have hT2 := hA.prod_fiberwise hasSum_zetaThreeA_fiber
  have hT3 : HasSum (fun k : ℕ => harmonicReal k / ((k : ℝ) + 1) ^ 2)
      (T + T - ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 3) := by
    convert hT2.sub hz3 using 1
    funext k
    have hk : (0 : ℝ) ≤ k := k.cast_nonneg
    simp only [harmonicReal, sum_range_succ]
    field_simp
    ring
  have hu := hT3.unique hasSum_harmonicReal_div
  rw [show T = ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 3 by linarith] at hT1
  exact hT1

/-- **DLMF 5.16.2**: `∑_{k=1}^∞ ψ′(k + 1)/k = ζ(3) = −ψ″(1)/2` (summation index shifted to
`k ≥ 0`). -/
theorem dlmf_5_16_2 :
    HasSum (fun k : ℕ => 1 / ((k : ℂ) + 1) * polygamma 1 ((k : ℂ) + 2)) (riemannZeta 3) ∧
      riemannZeta 3 = -(1 / 2) * polygamma 2 1 := by
  refine ⟨?_, ?_⟩
  · have hz := hasSum_inv_succ_pow_zeta (n := 2) (by norm_num)
    have hr := Complex.hasSum_ofReal.mpr hasSum_one_div_nat_add_one_cube
    have e : riemannZeta 3 = ((∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 3 : ℝ) : ℂ) := by
      rw [show (3 : ℂ) = ((2 : ℕ) : ℂ) + 1 by norm_num]
      refine hz.unique ?_
      convert hr using 1; funext k; push_cast; ring
    rw [e]
    convert Complex.hasSum_ofReal.mpr hasSum_trigammaTail_div using 1
    funext k
    push_cast
    rw [polygamma_one_nat_add_two]
    ring
  · rw [dlmf_5_15_2 (n := 2) (by norm_num)]
    norm_num [Nat.factorial]
    ring
