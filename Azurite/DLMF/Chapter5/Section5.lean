/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section4Gauss
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.RingTheory.RootsOfUnity.Lemmas

/-!
# DLMF §5.5: Functional Relations

Formalizations of <https://dlmf.nist.gov/5.5>.

* §5.5(i) Recurrence: 5.5.1 (`dlmf_5_5_1`, `z ≠ 0`: with Mathlib's junk value `Γ(0) = 0` it
  fails only at `z = 0`), 5.5.2 (`dlmf_5_5_2`, `z ≠ 0, −1, …`).
* §5.5(ii) Reflection: 5.5.3 (`dlmf_5_5_3`, every `z`, Mathlib's
  `Complex.Gamma_mul_Gamma_one_sub`), 5.5.4 (`dlmf_5_5_4`, `z ∉ ℤ`).
* §5.5(iii) Multiplication: the duplication formula 5.5.5 (`dlmf_5_5_5`, every `z`, from
  Mathlib's `Complex.Gamma_mul_Gamma_add_half`); Gauss's multiplication formula 5.5.6
  (`dlmf_5_5_6`, `nz ≠ 0, −1, …`) — on `(0, ∞)` by the Bohr–Mollerup theorem
  (`gauss_mul_real_aux`), with the constant 5.5.7 (`dlmf_5_5_7`:
  `∏_{k=1}^{n−1} Γ(k/n) = (2π)^{(n−1)/2} n^{−1/2}`, from the reflection formula and
  `∏_{k=1}^{n−1} 2 sin(πk/n) = n`, `prod_two_sin`), then on `ℂ` by the identity theorem; 5.5.8
  (`dlmf_5_5_8`, Mathlib's `Complex.digamma_two_mul`); 5.5.9 (`dlmf_5_5_9`, by taking logarithmic
  derivatives of 5.5.6).
* §5.5(iv) The Bohr–Mollerup theorem (`dlmf_5_5_iv`, Mathlib's `Real.eq_Gamma_of_log_convex`).
-/

open Complex Filter Topology Set Finset
open scoped Real

namespace Azurite.DLMF

/-! ### §5.5(i) Recurrence -/

/-- **DLMF 5.5.1**: `Γ(z + 1) = z Γ(z)` (`z ≠ 0`; Mathlib's `Complex.Gamma_add_one`). -/
theorem dlmf_5_5_1 {z : ℂ} (hz : z ≠ 0) : Gamma (z + 1) = z * Gamma z := Gamma_add_one z hz

/-- **DLMF 5.5.2**: `ψ(z + 1) = ψ(z) + 1/z` (`z ≠ 0, −1, …`). -/
theorem dlmf_5_5_2 {z : ℂ} (hz : z ∉ gammaPoles) : digamma (z + 1) = digamma z + 1 / z := by
  rw [digamma_apply_add_one z (not_mem_gammaPoles.mp hz), one_div]

/-! ### §5.5(ii) Reflection -/

/-- **DLMF 5.5.3**: `Γ(z) Γ(1 − z) = π / sin(πz)` (Mathlib's `Complex.Gamma_mul_Gamma_one_sub`,
which holds for every `z` with Mathlib's junk values). -/
theorem dlmf_5_5_3 (z : ℂ) : Gamma z * Gamma (1 - z) = π / sin (π * z) :=
  Gamma_mul_Gamma_one_sub z

/-- **DLMF 5.5.4**: `ψ(z) − ψ(1 − z) = −π / tan(πz)`, `z ≠ 0, ±1, …`. -/
theorem dlmf_5_5_4 {z : ℂ} (hz : ∀ n : ℤ, z ≠ n) :
    digamma z - digamma (1 - z) = -π / tan (π * z) := by
  rw [digamma_one_sub hz, cot_eq_cos_div_sin, tan_eq_sin_div_cos, div_div_eq_mul_div]
  ring

/-! ### §5.5(iii) Multiplication -/

theorem ofReal_pi_cpow_neg_half_mul_sqrt :
    (π : ℂ) ^ (-(1 / 2) : ℂ) * ((√π : ℝ) : ℂ) = 1 := by
  rw [Real.sqrt_eq_rpow, ofReal_cpow Real.pi_pos.le, ← cpow_add _ _ (ofReal_ne_zero.mpr
    Real.pi_ne_zero)]
  push_cast
  norm_num

/-- **DLMF 5.5.5** (duplication): `Γ(2z) = π^{−1/2} 2^{2z−1} Γ(z) Γ(z + ½)` (DLMF: `2z ≠ 0, −1, …`;
with Mathlib's junk values it holds for every `z`). -/
theorem dlmf_5_5_5 (z : ℂ) :
    Gamma (2 * z)
      = (π : ℂ) ^ (-(1 / 2) : ℂ) * (2 : ℂ) ^ (2 * z - 1) * Gamma z * Gamma (z + 1 / 2) := by
  have h := Gamma_mul_Gamma_add_half z
  have h2 : (2 : ℂ) ^ (2 * z - 1) * (2 : ℂ) ^ (1 - 2 * z) = 1 := by
    rw [← cpow_add _ _ two_ne_zero]; norm_num
  rw [mul_assoc _ (Gamma z), h, show (π : ℂ) ^ (-(1 / 2) : ℂ) * (2 : ℂ) ^ (2 * z - 1)
      * (Gamma (2 * z) * (2 : ℂ) ^ (1 - 2 * z) * ((√π : ℝ) : ℂ))
      = Gamma (2 * z) * ((π : ℂ) ^ (-(1 / 2) : ℂ) * ((√π : ℝ) : ℂ))
        * ((2 : ℂ) ^ (2 * z - 1) * (2 : ℂ) ^ (1 - 2 * z)) by ring,
    ofReal_pi_cpow_neg_half_mul_sqrt, h2, mul_one, mul_one]

/-! #### The sine product `∏_{k=1}^{n−1} 2 sin(πk/n) = n` -/

/-- `|1 − e^{iθ}| = 2 sin(θ/2)` for `0 < θ < 2π`. -/
theorem norm_one_sub_exp {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 2 * π) :
    ‖1 - cexp (θ * I)‖ = 2 * Real.sin (θ / 2) := by
  have hs : 0 < Real.sin (θ / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hcos2 := Real.cos_two_mul (θ / 2)
  have hsin2 := Real.sin_two_mul (θ / 2)
  rw [show 2 * (θ / 2) = θ by ring] at hcos2 hsin2
  have hpy := Real.sin_sq_add_cos_sq (θ / 2)
  have hsq : ‖1 - cexp (θ * I)‖ ^ 2 = (2 * Real.sin (θ / 2)) ^ 2 := by
    rw [Complex.sq_norm, normSq_apply]
    simp only [sub_re, one_re, exp_ofReal_mul_I_re, sub_im, one_im, exp_ofReal_mul_I_im]
    rw [hcos2, hsin2]
    linear_combination (4 * Real.cos (θ / 2) ^ 2 - 4) * hpy
  rw [← Real.sqrt_sq (norm_nonneg (1 - cexp (θ * I))), hsq, Real.sqrt_sq (by positivity)]

/-- `∏_{k=1}^{n−1} 2 sin(πk/n) = n`. -/
theorem prod_two_sin (m : ℕ) :
    ∏ k ∈ range m, (2 * Real.sin (π * (k + 1) / (m + 1))) = (m + 1 : ℝ) := by
  have hμ := Complex.isPrimitiveRoot_exp (m + 1) (Nat.succ_ne_zero m)
  have h := hμ.prod_one_sub_pow_eq_order
  have hn := congrArg norm h
  rw [norm_prod] at hn
  have hq : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  rw [show ((m : ℂ) + 1) = (((m + 1 : ℕ) : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity), hq] at hn
  refine (prod_congr rfl fun k hk => ?_).trans hn
  have hk := mem_range.mp hk
  have hθ0 : 0 < 2 * π * ((k + 1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) := by positivity
  have hθ1 : 2 * π * ((k + 1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) < 2 * π := by
    rw [div_lt_iff₀ (by positivity)]
    have : ((k + 1 : ℕ) : ℝ) < ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : k + 1 < m + 1)
    nlinarith [Real.pi_pos]
  rw [show cexp (2 * π * I / ((m + 1 : ℕ) : ℂ)) ^ (k + 1) = rootQ (m + 1) ^ (k + 1) from rfl,
    rootQ_pow, norm_one_sub_exp hθ0 hθ1]
  congr 2
  push_cast
  ring

/-! #### 5.5.7 -/

/-- **DLMF 5.5.7**: `∏_{k=1}^{n−1} Γ(k/n) = (2π)^{(n−1)/2} n^{−1/2}`, `n ≥ 1`. -/
theorem dlmf_5_5_7 {n : ℕ} (hn : 1 ≤ n) :
    ∏ k ∈ Ico 1 n, Real.Gamma (k / n)
      = (2 * π) ^ (((n : ℝ) - 1) / 2) * (n : ℝ) ^ (-(1 / 2) : ℝ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hn0 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  set P := ∏ k ∈ Ico 1 (m + 1), Real.Gamma (k / ((m + 1 : ℕ) : ℝ)) with hP
  have hPr : P = ∏ j ∈ range m, Real.Gamma ((j + 1) / ((m : ℝ) + 1)) := by
    rw [hP, prod_Ico_eq_prod_range, Nat.add_sub_cancel]
    refine prod_congr rfl fun j _ => ?_
    push_cast; ring_nf
  have hpos : 0 < P := by
    rw [hPr]; exact prod_pos fun j _ => Real.Gamma_pos_of_pos (by positivity)
  -- `P² = (2π)^m / n`
  have hrefl : P = ∏ j ∈ range m, Real.Gamma (1 - (j + 1) / ((m : ℝ) + 1)) := by
    rw [hPr, ← prod_range_reflect]
    refine prod_congr rfl fun j hj => ?_
    have hj := mem_range.mp hj
    congr 1
    rw [Nat.cast_sub (by omega : j ≤ m - 1), Nat.cast_sub (by omega : 1 ≤ m)]
    push_cast
    field_simp
    ring
  have hsq : P ^ 2 = ∏ j ∈ range m, (π / Real.sin (π * (j + 1) / ((m : ℝ) + 1))) := by
    rw [sq]
    nth_rewrite 1 [hPr]
    rw [hrefl, ← prod_mul_distrib]
    refine prod_congr rfl fun j _ => ?_
    rw [Real.Gamma_mul_Gamma_one_sub]
    congr 2
    ring
  have hsin := prod_two_sin m
  have hsinpos : ∀ j ∈ range m, 0 < Real.sin (π * (j + 1) / ((m : ℝ) + 1)) := by
    intro j hj
    have hj := mem_range.mp hj
    apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
    rw [div_lt_iff₀ hn0]
    have : (j : ℝ) + 1 < (m : ℝ) + 1 := by exact_mod_cast (by omega : j + 1 < m + 1)
    nlinarith [Real.pi_pos]
  have hS : ∏ j ∈ range m, Real.sin (π * (j + 1) / ((m : ℝ) + 1)) = ((m : ℝ) + 1) / 2 ^ m := by
    rw [prod_mul_distrib, prod_const, card_range] at hsin
    rw [eq_div_iff (by positivity)]
    linarith
  have hP2 : P ^ 2 = (2 * π) ^ m / ((m : ℝ) + 1) := by
    rw [hsq, prod_div_distrib, prod_const, card_range, hS, mul_pow]
    field_simp
  -- take the square root
  have hval : P = √((2 * π) ^ m / ((m : ℝ) + 1)) := by
    rw [← hP2, Real.sqrt_sq hpos.le]
  push_cast
  rw [show ((m : ℝ) + 1 - 1) / 2 = (m : ℝ) / 2 by ring, hval, Real.sqrt_eq_rpow,
    Real.div_rpow (by positivity) hn0.le, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
    Real.rpow_neg hn0.le, div_eq_mul_inv, show (m : ℝ) * (1 / 2) = m / 2 by ring]

/-! #### 5.5.6 on `(0, ∞)` by Bohr–Mollerup -/

theorem convexOn_comp_affine {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f) {c d : ℝ} (hc : 0 < c)
    (hd : 0 ≤ d) : ConvexOn ℝ (Ioi 0) (fun y => f (c * y + d)) := by
  refine ⟨convex_Ioi 0, fun x hx y hy a b ha hb hab => ?_⟩
  have hx' : c * x + d ∈ Ioi (0 : ℝ) := mem_Ioi.mpr (by have := mem_Ioi.mp hx; positivity)
  have hy' : c * y + d ∈ Ioi (0 : ℝ) := mem_Ioi.mpr (by have := mem_Ioi.mp hy; positivity)
  have h := hf.2 hx' hy' ha hb hab
  simp only [smul_eq_mul] at h ⊢
  convert h using 2
  linear_combination d * hab.symm

theorem convexOn_sum_range {g : ℕ → ℝ → ℝ} (hg : ∀ k, ConvexOn ℝ (Ioi 0) (g k)) (n : ℕ) :
    ConvexOn ℝ (Ioi 0) (fun y => ∑ k ∈ range n, g k y) := by
  induction n with
  | zero => simpa using convexOn_const (0 : ℝ) (convex_Ioi (0 : ℝ))
  | succ n ih =>
    refine (ih.add (hg n)).congr fun y _ => ?_
    simp [sum_range_succ]

/-- The normalizing constant `C = n ∏_{k<n} Γ((1 + k)/n)`. -/
noncomputable def gaussC (n : ℕ) : ℝ := n * ∏ k ∈ range n, Real.Gamma ((1 + k) / n)

/-- `f(y) = n^y ∏_{k<n} Γ((y + k)/n) / C`. -/
noncomputable def gaussF (n : ℕ) (y : ℝ) : ℝ :=
  (n : ℝ) ^ y * (∏ k ∈ range n, Real.Gamma ((y + k) / n)) / gaussC n

theorem gaussC_pos {n : ℕ} (hn : 1 ≤ n) : 0 < gaussC n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  exact mul_pos hn0 (prod_pos fun k _ => Real.Gamma_pos_of_pos (by positivity))

theorem prod_Gamma_shift {n : ℕ} (hn : 1 ≤ n) {y : ℝ} (hy : 0 < y) :
    ∏ k ∈ range n, Real.Gamma ((y + 1 + k) / n)
      = (∏ k ∈ range n, Real.Gamma ((y + k) / n)) * (y / n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 := prod_range_succ (fun k : ℕ => Real.Gamma ((y + k) / n)) n
  have h2 := prod_range_succ' (fun k : ℕ => Real.Gamma ((y + k) / n)) n
  simp only [Nat.cast_zero, add_zero, Nat.cast_succ] at h1 h2
  have hg0 : Real.Gamma (y / n) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hgn : Real.Gamma ((y + n) / n) = (y / n) * Real.Gamma (y / n) := by
    rw [show (y + n) / n = y / n + 1 by field_simp, Real.Gamma_add_one (by positivity)]
  have hsame : ∏ k ∈ range n, Real.Gamma ((y + 1 + k) / n)
      = ∏ k ∈ range n, Real.Gamma ((y + (k + 1)) / n) := by
    refine prod_congr rfl fun k _ => ?_; ring_nf
  rw [hsame]
  apply mul_right_cancel₀ hg0
  rw [← h2, h1, hgn]
  ring

theorem gaussF_add_one {n : ℕ} (hn : 1 ≤ n) {y : ℝ} (hy : 0 < y) :
    gaussF n (y + 1) = y * gaussF n y := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hC := (gaussC_pos hn).ne'
  unfold gaussF
  rw [prod_Gamma_shift hn hy, Real.rpow_add_one hn0.ne']
  field_simp

theorem gaussF_pos {n : ℕ} (hn : 1 ≤ n) {y : ℝ} (hy : 0 < y) : 0 < gaussF n y := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hp := prod_pos fun k (_ : k ∈ range n) =>
    Real.Gamma_pos_of_pos (show 0 < (y + k) / n by positivity)
  have := gaussC_pos hn
  unfold gaussF
  positivity

theorem gaussF_one {n : ℕ} (hn : 1 ≤ n) : gaussF n 1 = 1 := by
  unfold gaussF
  rw [Real.rpow_one, show (n : ℝ) * ∏ k ∈ range n, Real.Gamma ((1 + k) / n) = gaussC n from rfl,
    div_self (gaussC_pos hn).ne']

theorem convexOn_log_gaussF {n : ℕ} (hn : 1 ≤ n) : ConvexOn ℝ (Ioi 0) (Real.log ∘ gaussF n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hlin : ConvexOn ℝ (Ioi 0) (fun y : ℝ => y * Real.log n) := by
    refine ⟨convex_Ioi 0, fun x _ y _ a b _ _ _ => ?_⟩
    simp only [smul_eq_mul]
    exact le_of_eq (by ring)
  have hsum := convexOn_sum_range (g := fun k y => Real.log (Real.Gamma (1 / n * y + k / n)))
    (fun k => convexOn_comp_affine Real.convexOn_log_Gamma (by positivity) (by positivity)) n
  refine ((hlin.add hsum).add (convexOn_const (-Real.log (gaussC n)) (convex_Ioi 0))).congr ?_
  intro y hy
  have hy := mem_Ioi.mp hy
  have hprod : 0 < ∏ k ∈ range n, Real.Gamma ((y + k) / n) :=
    prod_pos fun k _ => Real.Gamma_pos_of_pos (by positivity)
  have hC := gaussC_pos hn
  show y * Real.log n + ∑ k ∈ range n, Real.log (Real.Gamma (1 / n * y + k / n))
      + -Real.log (gaussC n)
    = Real.log ((n : ℝ) ^ y * (∏ k ∈ range n, Real.Gamma ((y + k) / n)) / gaussC n)
  rw [Real.log_div (by positivity) hC.ne', Real.log_mul (by positivity) hprod.ne',
    Real.log_rpow hn0, Real.log_prod (fun k _ => (Real.Gamma_pos_of_pos (by positivity)).ne')]
  have : ∀ k ∈ range n, Real.log (Real.Gamma (1 / n * y + k / n))
      = Real.log (Real.Gamma ((y + k) / n)) := fun k _ => by congr 2; field_simp
  rw [sum_congr rfl this]
  ring

/-- Bohr–Mollerup applied to `gaussF n`. -/
theorem gaussF_eq_Gamma {n : ℕ} (hn : 1 ≤ n) {y : ℝ} (hy : 0 < y) :
    gaussF n y = Real.Gamma y :=
  Real.eq_Gamma_of_log_convex (convexOn_log_gaussF hn) (fun hy => gaussF_add_one hn hy)
    (fun hy => gaussF_pos hn hy) (gaussF_one hn) (mem_Ioi.mpr hy)

theorem gaussC_eq {n : ℕ} (hn : 1 ≤ n) :
    gaussC n = n * ((2 * π) ^ (((n : ℝ) - 1) / 2) * (n : ℝ) ^ (-(1 / 2) : ℝ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold gaussC
  congr 1
  have h1 : ∏ k ∈ range n, Real.Gamma ((1 + k) / n) = ∏ k ∈ Ico 1 (n + 1), Real.Gamma (k / n) := by
    rw [prod_Ico_eq_prod_range, Nat.add_sub_cancel]
    refine prod_congr rfl fun k _ => ?_; push_cast; ring_nf
  rw [h1, prod_Ico_succ_top (by omega), div_self hn0.ne', Real.Gamma_one, mul_one, dlmf_5_5_7 hn]

/-- **DLMF 5.5.6** on `(0, ∞)`. -/
theorem gauss_mul_real {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    Real.Gamma (n * x) = (2 * π) ^ ((1 - (n : ℝ)) / 2) * (n : ℝ) ^ ((n : ℝ) * x - 1 / 2)
      * ∏ k ∈ range n, Real.Gamma (x + k / n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnx : (0 : ℝ) < n * x := by positivity
  rw [← gaussF_eq_Gamma hn hnx]
  unfold gaussF
  rw [gaussC_eq hn]
  have hp : ∀ k ∈ range n, Real.Gamma ((n * x + k) / n) = Real.Gamma (x + k / n) := fun k _ => by
    congr 1; field_simp
  rw [prod_congr rfl hp]
  have h2 : (0 : ℝ) < 2 * π := by positivity
  have hsq : (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) = n := by
    rw [← Real.rpow_add hn0]; norm_num
  have h3 : (0 : ℝ) < (n : ℝ) ^ (1 / 2 : ℝ) := by positivity
  have h4 : (0 : ℝ) < (2 * π) ^ (((n : ℝ) - 1) / 2) := by positivity
  rw [Real.rpow_sub hn0, show (1 - (n : ℝ)) / 2 = -(((n : ℝ) - 1) / 2) by ring,
    Real.rpow_neg h2.le, Real.rpow_neg hn0.le]
  field_simp
  rw [sq]
  exact hsq

/-! #### 5.5.6 on `ℂ` -/

/-- The domain `nz ≠ 0, −1, −2, …`. -/
def mulPolesCompl (n : ℕ) : Set ℂ := {z | (n : ℂ) * z ∉ gammaPoles}

theorem isOpen_mulPolesCompl (n : ℕ) : IsOpen (mulPolesCompl n) :=
  isClosed_gammaPoles.isOpen_compl.preimage (continuous_const.mul continuous_id)

theorem isPreconnected_mulPolesCompl {n : ℕ} (hn : 1 ≤ n) : IsPreconnected (mulPolesCompl n) := by
  have hinj : Function.Injective fun z : ℂ => (n : ℂ) * z :=
    mul_right_injective₀ (by exact_mod_cast (show n ≠ 0 by omega))
  have hc : ((fun z : ℂ => (n : ℂ) * z) ⁻¹' gammaPoles).Countable :=
    (Set.countable_range _).preimage hinj
  exact (hc.isConnected_compl_of_one_lt_rank (by simp)).isPreconnected

theorem add_div_not_mem_gammaPoles {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z ∈ mulPolesCompl n)
    (k : ℕ) : z + k / n ∉ gammaPoles := by
  rintro ⟨m, hm⟩
  apply hz
  refine ⟨n * m + k, ?_⟩
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hz' : (n : ℂ) * z = n * (z + k / n) - k := by field_simp; ring
  simp only at hm
  rw [hz', ← hm]
  push_cast
  ring

/-- **DLMF 5.5.6** (Gauss's multiplication formula):
`Γ(nz) = (2π)^{(1−n)/2} n^{nz−1/2} ∏_{k=0}^{n−1} Γ(z + k/n)`, `nz ≠ 0, −1, −2, …`. -/
theorem dlmf_5_5_6 {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : (n : ℂ) * z ∉ gammaPoles) :
    Gamma (n * z) = ((2 * π : ℝ) : ℂ) ^ ((1 - (n : ℂ)) / 2) * (n : ℂ) ^ ((n : ℂ) * z - 1 / 2)
      * ∏ k ∈ range n, Gamma (z + k / n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnC : (n : ℂ) ∈ slitPlane := by
    rw [mem_slitPlane_iff]; left; simpa using hn0
  set F : ℂ → ℂ := fun z => Gamma (n * z) with hF
  set G : ℂ → ℂ := fun z => ((2 * π : ℝ) : ℂ) ^ ((1 - (n : ℂ)) / 2)
    * (n : ℂ) ^ ((n : ℂ) * z - 1 / 2) * ∏ k ∈ range n, Gamma (z + k / n) with hG
  have hFa : AnalyticOnNhd ℂ F (mulPolesCompl n) := fun w hw =>
    (dlmf_5_2_i_analytic _ hw).comp (f := fun z : ℂ => (n : ℂ) * z) (by fun_prop)
  have hGa : AnalyticOnNhd ℂ G (mulPolesCompl n) := by
    intro w hw
    have hprod : AnalyticAt ℂ (fun z => ∏ k ∈ range n, Gamma (z + k / n)) w :=
      Finset.analyticAt_fun_prod _ fun k _ =>
        (dlmf_5_2_i_analytic _ (add_div_not_mem_gammaPoles hn hw k)).comp
          (f := fun z : ℂ => z + k / n) (by fun_prop)
    have hcp : AnalyticAt ℂ (fun z : ℂ => (n : ℂ) ^ ((n : ℂ) * z - 1 / 2)) w :=
      analyticAt_const.cpow (by fun_prop) hnC
    exact (analyticAt_const.mul hcp).mul hprod
  -- agreement on `(0, ∞)`
  have hreal : ∀ x : ℝ, 0 < x → F x = G x := by
    intro x hx
    have h := congrArg (fun t : ℝ => (t : ℂ)) (gauss_mul_real hn hx)
    simp only [ofReal_mul, ofReal_prod] at h
    simp only [hF, hG]
    rw [show (n : ℂ) * x = ((n * x : ℝ) : ℂ) by push_cast; rfl, Complex.Gamma_ofReal, h,
      ofReal_cpow (by positivity), ofReal_cpow (by positivity)]
    congr 1
    · push_cast; ring_nf
    · refine prod_congr rfl fun k _ => ?_
      rw [← Complex.Gamma_ofReal]; push_cast; rfl
  have h1 : (1 : ℂ) ∈ mulPolesCompl n :=
    not_mem_gammaPoles_of_re_pos (by simpa using hn0)
  have hfreq : ∃ᶠ w in 𝓝[≠] (1 : ℂ), F w = G w := by
    have hlim : Tendsto (fun j : ℕ => (((1 : ℝ) + 1 / ((j : ℝ) + 1) : ℝ) : ℂ)) atTop
        (𝓝[≠] (1 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun j => ?_⟩
      · have h0 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add 1
        rw [add_zero] at h0
        have := (continuous_ofReal.tendsto 1).comp h0
        rw [ofReal_one] at this
        exact this
      · intro h
        have := ofReal_injective (h.trans ofReal_one.symm)
        have : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
        linarith
    exact hlim.frequently (Frequently.of_forall fun j => hreal _ (by positivity))
  exact hFa.eqOn_of_preconnected_of_frequently_eq hGa (isPreconnected_mulPolesCompl hn) h1
    hfreq hz

/-! #### 5.5.7, 5.5.8, 5.5.9 -/

/-- **DLMF 5.5.8**: `ψ(2z) = ½(ψ(z) + ψ(z + ½)) + ln 2` (`2z ≠ 0, −1, …`; Mathlib's
`Complex.digamma_two_mul`). -/
theorem dlmf_5_5_8 {z : ℂ} (hz : ∀ m : ℕ, 2 * z ≠ -(m : ℂ)) :
    digamma (2 * z) = 1 / 2 * (digamma z + digamma (z + 1 / 2)) + (Real.log 2 : ℂ) := by
  rw [digamma_two_mul hz, ofReal_log (by norm_num)]
  push_cast
  rfl

/-- **DLMF 5.5.9**: `ψ(nz) = (1/n) ∑_{k=0}^{n−1} ψ(z + k/n) + ln n`, `nz ≠ 0, −1, −2, …`. -/
theorem dlmf_5_5_9 {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : (n : ℂ) * z ∉ gammaPoles) :
    digamma (n * z) = 1 / n * ∑ k ∈ range n, digamma (z + k / n) + (Real.log n : ℂ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnC0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  set A : ℂ := ((2 * π : ℝ) : ℂ) ^ ((1 - (n : ℂ)) / 2) with hA
  have hA0 : A ≠ 0 := fun h =>
    (ofReal_ne_zero.mpr (by positivity : (0 : ℝ) < 2 * π).ne') ((cpow_eq_zero_iff _ _).mp h).1
  set B : ℂ → ℂ := fun w => (n : ℂ) ^ ((n : ℂ) * w - 1 / 2) with hB
  set P : ℂ → ℂ := fun w => ∏ k ∈ range n, Gamma (w + k / n) with hP
  have hB0 : B z ≠ 0 := fun h => hnC0 ((cpow_eq_zero_iff _ _).mp h).1
  have hP0 : P z ≠ 0 := prod_ne_zero_iff.mpr fun k _ =>
    dlmf_5_2_i_ne_zero (add_div_not_mem_gammaPoles hn hz k)
  have hBd : HasDerivAt B (B z * Complex.log n * (n * 1)) z :=
    (((hasDerivAt_id' z).const_mul (n : ℂ)).sub_const (1 / 2)).const_cpow (Or.inl hnC0)
  have hPd : DifferentiableAt ℂ P z :=
    (Finset.analyticAt_fun_prod _ fun k _ =>
      (dlmf_5_2_i_analytic _ (add_div_not_mem_gammaPoles hn hz k)).comp
        (f := fun w : ℂ => w + k / n) (by fun_prop)).differentiableAt
  have heq : (fun w => Gamma (n * w)) =ᶠ[𝓝 z] fun w => A * (B w * P w) := by
    filter_upwards [(isOpen_mulPolesCompl n).mem_nhds hz] with w hw
    rw [dlmf_5_5_6 hn hw]
    ring
  have hL : logDeriv (fun w => Gamma (n * w)) z = n * digamma (n * z) := by
    rw [((hasDerivAt_id' z).const_mul (n : ℂ)).logDeriv_Gamma (not_mem_gammaPoles.mp hz),
      mul_one]
  have hR : logDeriv (fun w => A * (B w * P w)) z
      = n * Complex.log n + ∑ k ∈ range n, digamma (z + k / n) := by
    rw [logDeriv_const_mul z A hA0, logDeriv_fun_mul z hB0 hP0 hBd.differentiableAt hPd]
    congr 1
    · rw [logDeriv_apply, hBd.deriv]
      field_simp
    · rw [hP, logDeriv_fun_prod (f := fun (k : ℕ) (w : ℂ) => Gamma (w + k / n))
        (fun k _ => dlmf_5_2_i_ne_zero (add_div_not_mem_gammaPoles hn hz k))
        (fun k _ => DifferentiableAt.comp (f := fun w : ℂ => w + (k : ℂ) / n) z
          (dlmf_5_2_i_analytic _ (add_div_not_mem_gammaPoles hn hz k)).differentiableAt
          (by fun_prop))]
      refine sum_congr rfl fun k _ => ?_
      rw [((hasDerivAt_id' z).add_const ((k : ℂ) / n)).logDeriv_Gamma
        (not_mem_gammaPoles.mp (add_div_not_mem_gammaPoles hn hz k)), one_mul]
  have key : (n : ℂ) * digamma (n * z)
      = n * Complex.log n + ∑ k ∈ range n, digamma (z + k / n) := by
    rw [← hL, ← hR, logDeriv_apply, logDeriv_apply, heq.deriv_eq, heq.eq_of_nhds]
  rw [show (Real.log n : ℂ) = Complex.log n by rw [ofReal_log hn0.le]; push_cast; rfl]
  have hinv : (n : ℂ) * (1 / n) = 1 := by field_simp
  linear_combination (1 / (n : ℂ)) * key - (digamma (n * z) - Complex.log n) * hinv

/-! ### §5.5(iv) The Bohr–Mollerup theorem -/

/-- **DLMF §5.5(iv)** (Bohr–Mollerup): "If a positive function `f(x)` on `(0, ∞)` satisfies
`f(x + 1) = x f(x)`, `f(1) = 1`, and `ln f(x)` is convex (see §1.4(viii)), then `f(x) = Γ(x)`"
(Mathlib's `Real.eq_Gamma_of_log_convex`). -/
theorem dlmf_5_5_iv {f : ℝ → ℝ} (hpos : ∀ x, 0 < x → 0 < f x)
    (hfeq : ∀ x, 0 < x → f (x + 1) = x * f x) (hone : f 1 = 1)
    (hconv : ConvexOn ℝ (Ioi 0) (Real.log ∘ f)) {x : ℝ} (hx : 0 < x) : f x = Real.Gamma x :=
  Real.eq_Gamma_of_log_convex hconv (fun hy => hfeq _ hy) (fun hy => hpos _ hy) hone
    (mem_Ioi.mpr hx)

end Azurite.DLMF
