/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter6.Section5
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-!
# DLMF §6.6: power series

Formalizations of <https://dlmf.nist.gov/6.6>, equations 6.6.1–6.6.6.  Sums over `n ≥ 1` are
written over `n ≥ 0` with `n + 1` in place of `n`.

* 6.6.4 (`dlmf_6_6_4`, every `z`): the Brent–Zimmermann series of `Ein` (Ex. 4.16).
* 6.6.2 (`dlmf_6_6_2`, `z` off the cut) and 6.6.1 (`dlmf_6_6_1`, `x > 0`): from 6.2.4, 6.2.7.
* 6.6.5 (`dlmf_6_6_5`, every `z`) and 6.6.6 (`dlmf_6_6_6`, off the cut): the odd/even terms of
  `Ein(iz) ∓ Ein(−iz)` (`Function.Injective.hasSum_iff`, the other terms vanish).
* 6.6.3 (`dlmf_6_6_3`, off the cut): `ψ(n + 1) = Hₙ − γ` (`Complex.digamma_nat_add_one`) and
  `∑ Hₙ zⁿ/n! = e^z Ein(z)` (`BZ.hasSum_exp_mul_Ein`, Ex. 4.19); `dlmf_2_5_48_series` closes the
  verification of 2.5.48 deferred in §2.5(iii).
* "The series … converge for all finite values": `dlmf_6_6_summable` (6.6.3's series) and the
  unconditional `dlmf_6_6_4`, `dlmf_6_6_5`.
-/

open Complex Filter Topology Set
open scoped Real Nat

namespace Azurite.DLMF

local notation "γ" => Real.eulerMascheroniConstant

/-- **DLMF 6.6.4**: `Ein(z) = ∑_{n≥1} (−1)^{n−1} zⁿ/(n! n)`, for every `z`. -/
theorem dlmf_6_6_4 (z : ℂ) :
    HasSum (fun n : ℕ => (-1) ^ n * z ^ (n + 1) / (((n + 1)! : ℂ) * (n + 1))) (ein z) := by
  have h := (BZ.summable_EinTerm z).hasSum
  rw [← BZ.Ein, ← ein_eq] at h
  refine h.congr_fun fun n => ?_
  simp only [BZ.EinTerm]
  push_cast
  ring

/-- **DLMF 6.6.2**: `E₁(z) = −γ − ln z − ∑_{n≥1} (−1)ⁿ zⁿ/(n! n)`, `z` off the cut. -/
theorem dlmf_6_6_2 {z : ℂ} (hz : z ∈ slitPlane) :
    HasSum (fun n : ℕ => (-1) ^ (n + 1) * z ^ (n + 1) / (((n + 1)! : ℂ) * (n + 1)))
      (-γ - log z - expIntE₁ z) := by
  have h := (dlmf_6_6_4 z).neg
  rw [show -ein z = -γ - log z - expIntE₁ z by rw [dlmf_6_2_4 hz]; ring] at h
  refine h.congr_fun fun n => ?_
  ring

/-- **DLMF 6.6.1**: `Ei(x) = γ + ln x + ∑_{n≥1} xⁿ/(n! n)`, `x > 0`. -/
theorem dlmf_6_6_1 {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ => x ^ (n + 1) / ((n + 1)! * (n + 1 : ℝ))) (Ei x - γ - Real.log x) := by
  rw [← Complex.hasSum_ofReal]
  have h := (dlmf_6_6_4 (-(x : ℂ))).neg
  rw [show -ein (-(x : ℂ)) = ((Ei x - γ - Real.log x : ℝ) : ℂ) by
    rw [ofReal_sub, ofReal_sub, Ei_eq_ein hx]; ring] at h
  refine h.congr_fun fun n => ?_
  push_cast
  have h1 : ((-1 : ℂ)) ^ n * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
  rw [neg_pow (x : ℂ), pow_succ (-1 : ℂ) n]
  linear_combination (-((x : ℂ) ^ (n + 1) / (((n + 1)! : ℂ) * ((n : ℂ) + 1)))) * h1

theorem I_pow_two_mul (k : ℕ) : I ^ (2 * k) = (-1) ^ k := by rw [pow_mul, I_sq]

/-- **DLMF 6.6.5**: `Si(z) = ∑_{n≥0} (−1)ⁿ z^{2n+1}/((2n+1)!(2n+1))`, for every `z`. -/
theorem dlmf_6_6_5 (z : ℂ) :
    HasSum (fun n : ℕ => (-1) ^ n * z ^ (2 * n + 1) / (((2 * n + 1)! : ℂ) * (2 * n + 1)))
      (Si z) := by
  set f : ℕ → ℂ := fun m => ((-1) ^ m * (I * z) ^ (m + 1) / (((m + 1)! : ℂ) * (m + 1)) -
    (-1) ^ m * (-I * z) ^ (m + 1) / (((m + 1)! : ℂ) * (m + 1))) / (2 * I) with hf
  have hs : HasSum f (Si z) := by
    rw [Si_eq, SiF]
    exact ((dlmf_6_6_4 (I * z)).sub (dlmf_6_6_4 (-I * z))).div_const _
  have hg : Function.Injective fun k : ℕ => 2 * k := fun a b h => by simpa using h
  have hzero : ∀ m ∉ Set.range (fun k : ℕ => 2 * k), f m = 0 := by
    intro m hm
    obtain ⟨k, rfl⟩ : Odd m := by
      rcases Nat.even_or_odd m with ⟨k, rfl⟩ | h
      · exact absurd ⟨k, by ring⟩ hm
      · exact h
    simp only [hf]
    rw [show -I * z = -(I * z) by ring, show 2 * k + 1 + 1 = 2 * (k + 1) by ring,
      (even_two_mul (k + 1)).neg_pow]
    simp
  rw [← hg.hasSum_iff hzero] at hs
  refine hs.congr_fun fun k => ?_
  simp only [hf, Function.comp]
  rw [show -I * z = -(I * z) by ring, (odd_two_mul_add_one k).neg_pow, mul_pow, pow_succ I,
    I_pow_two_mul, pow_mul (-1 : ℂ) 2, neg_one_sq, one_pow]
  push_cast
  field_simp
  ring

/-- **DLMF 6.6.6**: `Ci(z) = γ + ln z + ∑_{n≥1} (−1)ⁿ z^{2n}/((2n)!(2n))`, `z` off the cut. -/
theorem dlmf_6_6_6 {z : ℂ} (hz : z ∈ slitPlane) :
    HasSum (fun n : ℕ =>
        (-1) ^ (n + 1) * z ^ (2 * (n + 1)) / (((2 * (n + 1))! : ℂ) * (2 * (n + 1))))
      (Ci z - γ - log z) := by
  set f : ℕ → ℂ := fun m => -(((-1) ^ m * (I * z) ^ (m + 1) / (((m + 1)! : ℂ) * (m + 1)) +
    (-1) ^ m * (-I * z) ^ (m + 1) / (((m + 1)! : ℂ) * (m + 1))) / 2) with hf
  have hs : HasSum f (Ci z - γ - log z) := by
    rw [(dlmf_6_2_13 hz).2, show -Cin z + log z + γ - γ - log z = -Cin z by ring, Cin_eq, CinF]
    exact (((dlmf_6_6_4 (I * z)).add (dlmf_6_6_4 (-I * z))).div_const _).neg
  have hg : Function.Injective fun k : ℕ => 2 * k + 1 := fun a b h => by simpa using h
  have hzero : ∀ m ∉ Set.range (fun k : ℕ => 2 * k + 1), f m = 0 := by
    intro m hm
    obtain ⟨k, rfl⟩ : Even m := by
      rcases Nat.even_or_odd m with h | ⟨k, rfl⟩
      · exact h
      · exact absurd ⟨k, rfl⟩ hm
    simp only [hf]
    rw [show -I * z = -(I * z) by ring, show k + k + 1 = 2 * k + 1 by ring,
      (odd_two_mul_add_one k).neg_pow]
    ring
  rw [← hg.hasSum_iff hzero] at hs
  refine hs.congr_fun fun k => ?_
  simp only [hf, Function.comp]
  rw [show -I * z = -(I * z) by ring, show 2 * k + 1 + 1 = 2 * (k + 1) by ring,
    (even_two_mul (k + 1)).neg_pow, mul_pow, I_pow_two_mul, pow_succ (-1 : ℂ) (2 * k),
    pow_mul (-1 : ℂ) 2, neg_one_sq, one_pow]
  push_cast
  have a1 : (2 * (k : ℂ) + 1 + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (2 * k + 1)
  have a2 : (2 * ((k : ℂ) + 1)) ≠ 0 := by exact_mod_cast (show 2 * (k + 1) ≠ 0 by omega)
  field_simp
  ring

/-- **DLMF 6.6.3**: `E₁(z) = −ln z + e^{−z} ∑_{n≥0} zⁿ ψ(n + 1)/n!`, `z` off the cut
(`ψ(n + 1) = Hₙ − γ`, and `∑ Hₙ zⁿ/n! = e^z Ein(z)`). -/
theorem dlmf_6_6_3 {z : ℂ} (hz : z ∈ slitPlane) :
    HasSum (fun n : ℕ => cexp (-z) * (z ^ n / (n ! : ℂ) * digamma (n + 1)))
      (expIntE₁ z + log z) := by
  have he : HasSum (fun n : ℕ => z ^ n / (n ! : ℂ)) (cexp z) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp z
  have hH := BZ.hasSum_exp_mul_Ein z
  have h := ((hH.sub (he.mul_left (γ : ℂ))).mul_left (cexp (-z)))
  have hee : cexp (-z) * cexp z = 1 := by rw [← exp_add, neg_add_cancel, exp_zero]
  rw [← ein_eq, show cexp (-z) * (cexp z * ein z - γ * cexp z) = expIntE₁ z + log z by
    rw [dlmf_6_2_4 hz]; linear_combination (ein z - γ) * hee] at h
  refine h.congr_fun fun n => ?_
  rw [digamma_nat_add_one]
  ring

/-- **DLMF §6.6**: the series converge for all finite `z` (6.6.3's series, the others being
`HasSum` statements for every `z`, `dlmf_6_6_4`, `dlmf_6_6_5`). -/
theorem dlmf_6_6_summable (z : ℂ) :
    Summable (fun n : ℕ => z ^ n / (n ! : ℂ) * digamma (n + 1)) := by
  have he : HasSum (fun n : ℕ => z ^ n / (n ! : ℂ)) (cexp z) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp z
  refine ((BZ.hasSum_exp_mul_Ein z).sub (he.mul_left (γ : ℂ))).summable.congr fun n => ?_
  rw [digamma_nat_add_one]
  ring

/-- **DLMF 2.5.48 verified by 6.6.3** (deferred from §2.5(iii)): the terms of the asymptotic
expansion 2.5.48 of `ℒh(ζ) = e^ζ E₁(ζ)` (2.5.49) form a convergent series with sum `ℒh(ζ)`:
`∑_{k≥0} (−ln ζ + ψ(k + 1)) ζᵏ/k! = e^ζ E₁(ζ)`, `ζ > 0`. -/
theorem dlmf_2_5_48_series {ζ : ℝ} (hζ : 0 < ζ) :
    HasSum (fun k : ℕ => (-(Real.log ζ : ℂ) + digamma (k + 1)) * (ζ : ℂ) ^ k / k !)
      (laplace oneDivOneAdd ζ) := by
  have hs : (ζ : ℂ) ∈ slitPlane := mem_slitPlane_of_re_pos (by simpa using hζ)
  have he : HasSum (fun n : ℕ => (ζ : ℂ) ^ n / (n ! : ℂ)) (cexp ζ) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp (ζ : ℂ)
  have h3 := (dlmf_6_6_3 hs).mul_left (cexp ζ)
  have hee : cexp (ζ : ℂ) * cexp (-(ζ : ℂ)) = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]
  have h := h3.add (he.mul_left (-(Real.log ζ : ℂ)))
  rw [dlmf_2_5_49 hζ, ofReal_mul, ofReal_exp, ← expIntE₁_eq_expIntegralE₁ hζ]
  rw [← ofReal_log hζ.le] at h
  convert h using 1
  · funext k
    linear_combination (-((ζ : ℂ) ^ k / k ! * digamma (k + 1))) * hee
  · ring

end Azurite.DLMF
