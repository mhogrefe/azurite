/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BrentZimmermann.Chapter4.ThetaFunctions
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable

/-!
# Brent–Zimmermann §4.8.3 (continued): Jacobi's identity, the nome, Sasaki–Kanada

The remaining claims of §4.8.3: Jacobi's quartic identity `θ₂⁴ + θ₄⁴ = θ₃⁴`, so that the modulus
of the nome `q` is `k = θ₂²(q)/θ₃²(q)` with complement `k' = θ₄²(q)/θ₃²(q)` and
`K(k) = (π/2) θ₃²(q)` (4.77); the inverse nome formula

  `ln(1/q) = π K'(k)/K(k)`,                                                                  (4.78)

and Sasaki–Kanada's

  `ln(1/q) = π/AGM(θ₂²(q), θ₃²(q))`.                                                         (4.79)

What is formalized:

* `theta2Int q = ∑_{a∈ℤ} q^(a(a+1))` (so `θ₂(q) = q^(1/4) θ₂Int(q)`, `theta2_eq_rpow_mul`), and
  two more parity-split identities: `theta3_sq_sub_theta4_sq` (`θ₃² − θ₄² = 2q θ₂Int(q²)²`) and
  `theta2Int_sq` (`θ₂Int(q)² = 2 θ₃(q²) θ₂Int(q²)`); together with `(θ₃² + θ₄²)/2 = θ₃²(q²)`
  these give **Jacobi's identity** `theta2_pow_four_add_theta4_pow_four`: `θ₂⁴ + θ₄⁴ = θ₃⁴`
  (`0 ≤ q < 1`), hence `nomeK_sq_add_nomeK'_sq` (`k² + k'² = 1`), `theta2_le_theta3`, and (4.77)
  in the textbook form `ellipticK_nomeK`: `K(k) = (π/2) θ₃²(q)`.
* The bridge to Mathlib's `jacobiTheta₂`: with `q = nome s = exp(−πs)` and `τ = i s`,
  `θ₃(q) = ϑ(0, τ)`, `θ₄(q) = ϑ(1/2, τ)`, `θ₂(q) = e^(−πs/4) ϑ(τ/2, τ)` (`theta3_nome_eq`,
  `theta4_nome_eq`, `theta2_nome_eq`), and Jacobi's imaginary transformation from
  `jacobiTheta₂_functional_equation`: `θ₃(e^(−π/s)) = √s θ₃(e^(−πs))`,
  `θ₂(e^(−π/s)) = √s θ₄(e^(−πs))`, `θ₄(e^(−π/s)) = √s θ₂(e^(−πs))` (`theta3_nome_inv`,
  `theta2_nome_inv`, `theta4_nome_inv`); so `k'(q) = k(q')` for `q' = e^(−π/s)`
  (`nomeK'_nome_eq_nomeK_inv`).
* **(4.78)** `log_inv_nome`: `π K(k'(q))/K(k(q)) = ln(1/q)` for `q = e^(−πs)`, and
  **(4.79)** `sasaki_kanada`: `ln(1/q) = π/AGM(θ₂²(q), θ₃²(q))`.
-/

namespace Azurite

namespace BZ

open Filter Topology Set Complex

variable {q : ℝ}

/-! ### `θ₂` as a two-sided sum with integer exponents -/

/-- `∑_{a ∈ ℤ} q^(a(a+1))`, so that `θ₂(q) = q^(1/4) · theta2Int q`. -/
noncomputable def theta2Int (q : ℝ) : ℝ := ∑' a : ℤ, q ^ (a.natAbs * (a + 1).natAbs)

theorem int_mul_add_one_nonneg (x : ℤ) : 0 ≤ x * (x + 1) := by
  rcases le_or_gt 0 x with h | h
  · positivity
  · nlinarith

/-- `|a| |a+1| ≥ |a| − 1`, so the `θ₂Int` terms are dominated by `|q|^(|a| − 1)`. -/
theorem natAbs_mul_natAbs_add_one_ge (a : ℤ) : a.natAbs - 1 ≤ a.natAbs * (a + 1).natAbs := by
  rcases eq_or_ne a (-1) with rfl | h
  · simp
  · have : 1 ≤ (a + 1).natAbs := Nat.one_le_iff_ne_zero.mpr (by omega)
    calc a.natAbs - 1 ≤ a.natAbs := Nat.sub_le _ _
      _ = a.natAbs * 1 := (mul_one _).symm
      _ ≤ a.natAbs * (a + 1).natAbs := Nat.mul_le_mul_left _ this

theorem summable_abs_pow_natAbs_sub_one (hq : |q| < 1) :
    Summable fun a : ℤ => |q| ^ (a.natAbs - 1) := by
  have h := Summable.int_rec (f := fun n : ℕ => |q| ^ (n - 1)) (g := fun n : ℕ => |q| ^ n)
    (by
      have := (summable_nat_add_iff (f := fun n : ℕ => |q| ^ (n - 1)) 1).mpr
      exact (summable_nat_add_iff (f := fun n : ℕ => |q| ^ (n - 1)) 1).mp
        ((summable_geometric_of_lt_one (abs_nonneg q) hq).congr fun n => by simp))
    (summable_geometric_of_lt_one (abs_nonneg q) hq)
  refine h.congr fun m => ?_
  rcases m with n | n
  · rfl
  · show |q| ^ n = |q| ^ ((n + 1) - 1)
    rw [Nat.add_sub_cancel]

theorem summable_norm_theta2Int_term (hq : |q| < 1) :
    Summable fun a : ℤ => ‖q ^ (a.natAbs * (a + 1).natAbs)‖ :=
  (summable_abs_pow_natAbs_sub_one hq).of_nonneg_of_le (fun _ => norm_nonneg _) fun a => by
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_of_le_one (abs_nonneg q) hq.le (natAbs_mul_natAbs_add_one_ge a)

theorem summable_theta2Int_term (hq : |q| < 1) :
    Summable fun a : ℤ => q ^ (a.natAbs * (a + 1).natAbs) :=
  (summable_norm_theta2Int_term hq).of_norm

/-- `θ₂(q) = q^(1/4) · θ₂Int(q)` for `0 ≤ q < 1`. -/
theorem theta2_eq_rpow_mul (hq0 : 0 ≤ q) (hq1 : q < 1) :
    theta2 q = q ^ (1 / 4 : ℝ) * theta2Int q := by
  have hq : |q| < 1 := by rw [abs_of_nonneg hq0]; exact hq1
  have hf : Summable fun n : ℕ => q ^ (n * (n + 1)) :=
    (summable_theta2Int_term hq).comp_injective (i := fun n : ℕ => (n : ℤ)) Int.ofNat_injective
  have hg : Summable fun n : ℕ => q ^ ((n + 1) * n) := by
    refine hf.congr fun n => ?_
    rw [mul_comm]
  have heq : (fun a : ℤ => q ^ (a.natAbs * (a + 1).natAbs))
      = Int.rec (fun n : ℕ => q ^ (n * (n + 1))) (fun n : ℕ => q ^ ((n + 1) * n)) := by
    funext a
    rcases a with n | n
    · rfl
    · show q ^ ((Int.negSucc n).natAbs * (Int.negSucc n + 1).natAbs) = q ^ ((n + 1) * n)
      congr 2
      omega
  unfold theta2 theta2Int
  rw [heq, tsum_int_rec hf hg]
  have h2 : ∑' n : ℕ, q ^ ((n + 1) * n) = ∑' n : ℕ, q ^ (n * (n + 1)) :=
    tsum_congr fun n => by rw [mul_comm]
  rw [h2]
  ring

theorem two_le_theta2Int (hq0 : 0 ≤ q) (hq1 : q < 1) : 2 ≤ theta2Int q := by
  have hq : |q| < 1 := by rw [abs_of_nonneg hq0]; exact hq1
  unfold theta2Int
  have hs := summable_theta2Int_term hq
  have := hs.sum_le_tsum {0, -1} (fun a _ => by positivity)
  rw [Finset.sum_pair (by decide)] at this
  norm_num at this
  linarith

/-! ### Exponent identities -/

theorem natAbs_sq_add_one_add_sub (a b : ℤ) :
    (a + b + 1).natAbs ^ 2 + (a - b).natAbs ^ 2
      = 2 * (a.natAbs * (a + 1).natAbs) + 2 * (b.natAbs * (b + 1).natAbs) + 1 := by
  zify
  simp only [sq_abs]
  rw [← abs_mul, ← abs_mul, abs_of_nonneg (int_mul_add_one_nonneg a),
    abs_of_nonneg (int_mul_add_one_nonneg b)]
  ring

theorem natAbs_mul_even_split (c d : ℤ) :
    (c + d).natAbs * (c + d + 1).natAbs + (c - d).natAbs * (c - d + 1).natAbs
      = 2 * (c.natAbs * (c + 1).natAbs) + 2 * d.natAbs ^ 2 := by
  zify
  simp only [sq_abs]
  rw [← abs_mul, ← abs_mul, ← abs_mul, abs_of_nonneg (int_mul_add_one_nonneg (c + d)),
    abs_of_nonneg (int_mul_add_one_nonneg (c - d)), abs_of_nonneg (int_mul_add_one_nonneg c)]
  ring

theorem natAbs_mul_odd_split (c d : ℤ) :
    (c + d + 1).natAbs * (c + d + 1 + 1).natAbs + (c - d).natAbs * (c - d + 1).natAbs
      = 2 * (c + 1).natAbs ^ 2 + 2 * (d.natAbs * (d + 1).natAbs) := by
  zify
  simp only [sq_abs]
  rw [← abs_mul, ← abs_mul, ← abs_mul, abs_of_nonneg (int_mul_add_one_nonneg (c + d + 1)),
    abs_of_nonneg (int_mul_add_one_nonneg (c - d)), abs_of_nonneg (int_mul_add_one_nonneg d)]
  ring

/-! ### Two more Landen-type identities -/

/-- `θ₃(q)² − θ₄(q)² = 2 q θ₂Int(q²)²`. -/
theorem theta3_sq_sub_theta4_sq (hq : |q| < 1) :
    theta3 q ^ 2 - theta4 q ^ 2 = 2 * q * theta2Int (q ^ 2) ^ 2 := by
  have hq2 : |q ^ 2| < 1 := by rw [abs_pow]; exact pow_lt_one₀ (abs_nonneg q) hq two_ne_zero
  unfold theta3 theta4 theta2Int
  rw [sq, sq, sq, tsum_mul_tsum_of_summable_norm (summable_norm_theta3_term hq)
    (summable_norm_theta3_term hq), tsum_mul_tsum_of_summable_norm (summable_norm_theta4_term hq)
    (summable_norm_theta4_term hq), tsum_mul_tsum_of_summable_norm
    (summable_norm_theta2Int_term hq2) (summable_norm_theta2Int_term hq2)]
  have hs3 := summable_mul_of_summable_norm (summable_norm_theta3_term hq)
    (summable_norm_theta3_term hq)
  have hs4 := summable_mul_of_summable_norm (summable_norm_theta4_term hq)
    (summable_norm_theta4_term hq)
  rw [← hs3.tsum_sub hs4, tsum_prod_int_split (hs3.sub hs4)]
  have heven : ∑' p : ℤ × ℤ, (q ^ ((p.1 + p.2).natAbs ^ 2) * q ^ ((p.1 - p.2).natAbs ^ 2)
      - (-1) ^ (p.1 + p.2).natAbs * q ^ ((p.1 + p.2).natAbs ^ 2)
        * ((-1) ^ (p.1 - p.2).natAbs * q ^ ((p.1 - p.2).natAbs ^ 2))) = 0 := by
    refine (tsum_congr fun p => ?_).trans (tsum_zero (α := ℝ) (β := ℤ × ℤ))
    obtain ⟨a, b⟩ := p
    simp only
    have h := neg_one_pow_natAbs_mul (a + b) (a - b)
    rw [ite_eq_left ⟨a, by ring⟩] at h
    linear_combination (-(q ^ ((a + b).natAbs ^ 2) * q ^ ((a - b).natAbs ^ 2))) * h
  rw [heven, zero_add, ← tsum_mul_left]
  refine tsum_congr fun p => ?_
  obtain ⟨a, b⟩ := p
  simp only
  have h := neg_one_pow_natAbs_mul (a + b + 1) (a - b)
  rw [ite_eq_right (by rw [Int.not_even_iff_odd]; exact ⟨a, by ring⟩)] at h
  have hexp : q ^ ((a + b + 1).natAbs ^ 2) * q ^ ((a - b).natAbs ^ 2)
      = q * ((q ^ 2) ^ (a.natAbs * (a + 1).natAbs) * (q ^ 2) ^ (b.natAbs * (b + 1).natAbs)) := by
    rw [← pow_add, natAbs_sq_add_one_add_sub, ← pow_mul, ← pow_mul, ← pow_add, pow_succ]
    ring
  linear_combination (-(q ^ ((a + b + 1).natAbs ^ 2) * q ^ ((a - b).natAbs ^ 2))) * h
    + 2 * hexp

/-- `θ₂Int(q)² = 2 θ₃(q²) θ₂Int(q²)`. -/
theorem theta2Int_sq (hq : |q| < 1) : theta2Int q ^ 2 = 2 * theta3 (q ^ 2) * theta2Int (q ^ 2) := by
  have hq2 : |q ^ 2| < 1 := by rw [abs_pow]; exact pow_lt_one₀ (abs_nonneg q) hq two_ne_zero
  unfold theta3 theta2Int
  rw [sq, tsum_mul_tsum_of_summable_norm (summable_norm_theta2Int_term hq)
    (summable_norm_theta2Int_term hq), mul_assoc, tsum_mul_tsum_of_summable_norm
    (summable_norm_theta3_term hq2) (summable_norm_theta2Int_term hq2)]
  have hs := summable_mul_of_summable_norm (summable_norm_theta2Int_term hq)
    (summable_norm_theta2Int_term hq)
  rw [tsum_prod_int_split hs]
  have heven : ∑' p : ℤ × ℤ, q ^ ((p.1 + p.2).natAbs * (p.1 + p.2 + 1).natAbs)
      * q ^ ((p.1 - p.2).natAbs * (p.1 - p.2 + 1).natAbs)
      = ∑' z : ℤ × ℤ, (q ^ 2) ^ (z.1.natAbs ^ 2) * (q ^ 2) ^ (z.2.natAbs * (z.2 + 1).natAbs) := by
    -- swap the roles of the two coordinates: `(c, d) ↦ (d, c)`
    rw [← (Equiv.prodComm ℤ ℤ).tsum_eq
      (fun z : ℤ × ℤ => (q ^ 2) ^ (z.1.natAbs ^ 2) * (q ^ 2) ^ (z.2.natAbs * (z.2 + 1).natAbs))]
    refine tsum_congr fun p => ?_
    obtain ⟨c, d⟩ := p
    simp only [Equiv.prodComm_apply, Prod.swap]
    rw [← pow_add, natAbs_mul_even_split, ← pow_mul, ← pow_mul, ← pow_add]
    ring_nf
  have hodd : ∑' p : ℤ × ℤ, q ^ ((p.1 + p.2 + 1).natAbs * (p.1 + p.2 + 1 + 1).natAbs)
      * q ^ ((p.1 - p.2).natAbs * (p.1 - p.2 + 1).natAbs)
      = ∑' z : ℤ × ℤ, (q ^ 2) ^ (z.1.natAbs ^ 2) * (q ^ 2) ^ (z.2.natAbs * (z.2 + 1).natAbs) := by
    -- shift the first coordinate: `(c, d) ↦ (c + 1, d)`
    rw [← (Equiv.prodCongr (Equiv.addRight (1 : ℤ)) (Equiv.refl ℤ)).tsum_eq
      (fun z : ℤ × ℤ => (q ^ 2) ^ (z.1.natAbs ^ 2) * (q ^ 2) ^ (z.2.natAbs * (z.2 + 1).natAbs))]
    refine tsum_congr fun p => ?_
    obtain ⟨c, d⟩ := p
    simp only [Equiv.prodCongr_apply, Equiv.coe_addRight, Equiv.refl_apply, Prod.map]
    rw [← pow_add, natAbs_mul_odd_split, ← pow_mul, ← pow_mul, ← pow_add]
  rw [heven, hodd]
  ring

/-! ### Jacobi's identity and (4.77) -/

/-- Jacobi: `θ₂(q)⁴ + θ₄(q)⁴ = θ₃(q)⁴` for `0 ≤ q < 1`. -/
theorem theta2_pow_four_add_theta4_pow_four (hq0 : 0 ≤ q) (hq1 : q < 1) :
    theta2 q ^ 4 + theta4 q ^ 4 = theta3 q ^ 4 := by
  have hq : |q| < 1 := by rw [abs_of_nonneg hq0]; exact hq1
  have h1 := theta3_sq_add_theta4_sq hq
  have h2 := theta3_sq_sub_theta4_sq hq
  have h3 := theta2Int_sq hq
  rw [theta2_eq_rpow_mul hq0 hq1, mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul hq0,
    show (1 / 4 : ℝ) * ((4 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
  have : theta3 q ^ 4 - theta4 q ^ 4
      = (theta3 q ^ 2 + theta4 q ^ 2) * (theta3 q ^ 2 - theta4 q ^ 2) := by
    ring
  linear_combination q * (theta2Int q ^ 2 + 2 * theta3 (q ^ 2) * theta2Int (q ^ 2)) * h3
    - 4 * q * theta2Int (q ^ 2) ^ 2 * h1 - (theta3 q ^ 2 + theta4 q ^ 2) * h2

theorem theta2_nonneg (hq0 : 0 ≤ q) (hq1 : q < 1) : 0 ≤ theta2 q := by
  rw [theta2_eq_rpow_mul hq0 hq1]
  have := two_le_theta2Int hq0 hq1
  positivity

theorem theta2_pos (hq0 : 0 < q) (hq1 : q < 1) : 0 < theta2 q := by
  rw [theta2_eq_rpow_mul hq0.le hq1]
  have := two_le_theta2Int hq0.le hq1
  positivity

theorem theta2_le_theta3 (hq0 : 0 ≤ q) (hq1 : q < 1) : theta2 q ≤ theta3 q := by
  have h := theta2_pow_four_add_theta4_pow_four hq0 hq1
  have h4 : 0 ≤ theta4 q ^ 4 := by positivity
  have h3 := theta3_pos hq0 hq1
  have h2 := theta2_nonneg hq0 hq1
  exact le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0) h3.le (by linarith)

/-- `k² + k'² = 1`: `nomeK q ^ 2 + nomeK' q ^ 2 = 1`. -/
theorem nomeK_sq_add_nomeK'_sq (hq0 : 0 ≤ q) (hq1 : q < 1) : nomeK q ^ 2 + nomeK' q ^ 2 = 1 := by
  unfold nomeK nomeK'
  have h3 := theta3_pos hq0 hq1
  have h := theta2_pow_four_add_theta4_pow_four hq0 hq1
  field_simp
  linear_combination h

theorem nomeK_nonneg (hq0 : 0 ≤ q) (hq1 : q < 1) : 0 ≤ nomeK q := by
  unfold nomeK; have := theta2_nonneg hq0 hq1; positivity

theorem nomeK_pos (hq0 : 0 < q) (hq1 : q < 1) : 0 < nomeK q := by
  unfold nomeK
  have := theta2_pos hq0 hq1
  have := theta3_pos hq0.le hq1
  positivity

theorem nomeK_le_one (hq0 : 0 ≤ q) (hq1 : q < 1) : nomeK q ≤ 1 := by
  unfold nomeK
  have h3 := theta3_pos hq0 hq1
  rw [div_le_one (by positivity)]
  exact pow_le_pow_left₀ (theta2_nonneg hq0 hq1) (theta2_le_theta3 hq0 hq1) 2

theorem sqrt_one_sub_nomeK'_sq (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Real.sqrt (1 - nomeK' q ^ 2) = nomeK q := by
  rw [show 1 - nomeK' q ^ 2 = nomeK q ^ 2 by linarith [nomeK_sq_add_nomeK'_sq hq0 hq1],
    Real.sqrt_sq (nomeK_nonneg hq0 hq1)]

theorem sqrt_one_sub_nomeK_sq (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Real.sqrt (1 - nomeK q ^ 2) = nomeK' q := by
  rw [show 1 - nomeK q ^ 2 = nomeK' q ^ 2 by linarith [nomeK_sq_add_nomeK'_sq hq0 hq1],
    Real.sqrt_sq (nomeK'_pos hq0 hq1).le]

/-- (4.77): `K(k) = (π/2) θ₃²(q)` with `k = θ₂²(q)/θ₃²(q)`. -/
theorem ellipticK_nomeK (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ellipticK (nomeK q) = Real.pi / 2 * theta3 q ^ 2 := by
  rw [← sqrt_one_sub_nomeK'_sq hq0 hq1]
  exact ellipticK_nome hq0 hq1

/-! ### The bridge to Mathlib's `jacobiTheta₂` -/

/-- The nome `q = e^(−πs)` of the parameter `s > 0` (`τ = i s`). -/
noncomputable def nome (s : ℝ) : ℝ := Real.exp (-(Real.pi * s))

theorem nome_pos (s : ℝ) : 0 < nome s := Real.exp_pos _

theorem nome_lt_one {s : ℝ} (hs : 0 < s) : nome s < 1 :=
  Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])

/-- `((n.natAbs : ℕ) : ℂ) ^ 2 = (n : ℂ) ^ 2`. -/
theorem natAbs_cast_sq_complex (n : ℤ) : ((n.natAbs : ℕ) : ℂ) ^ 2 = (n : ℂ) ^ 2 := by
  rw [← Int.cast_natCast, ← Int.cast_pow, Int.natAbs_sq, Int.cast_pow]

/-- `θ₃(e^(−πs)) = ϑ(0, i s)`. -/
theorem theta3_nome_eq (s : ℝ) : (theta3 (nome s) : ℂ) = jacobiTheta₂ 0 (I * s) := by
  unfold theta3 jacobiTheta₂ nome
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  unfold jacobiTheta₂_term
  rw [Complex.ofReal_pow, Complex.ofReal_exp, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  rw [natAbs_cast_sq_complex]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- `θ₄(e^(−πs)) = ϑ(1/2, i s)`. -/
theorem theta4_nome_eq (s : ℝ) : (theta4 (nome s) : ℂ) = jacobiTheta₂ (1 / 2) (I * s) := by
  unfold theta4 jacobiTheta₂ nome
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  unfold jacobiTheta₂_term
  rw [Complex.exp_add, Complex.ofReal_mul]
  congr 1
  · rw [show 2 * ↑Real.pi * I * (n : ℂ) * (1 / 2) = n * (Real.pi * I) by ring, Complex.exp_int_mul,
      Complex.exp_pi_mul_I, Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one]
    rcases Int.even_or_odd n with h | h
    · rw [h.neg_one_zpow, (Int.natAbs_even.mpr h).neg_one_pow]
    · rw [h.neg_one_zpow, (Int.natAbs_odd.mpr h).neg_one_pow]
  · rw [Complex.ofReal_pow, Complex.ofReal_exp, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    rw [natAbs_cast_sq_complex]
    ring_nf
    rw [Complex.I_sq]
    ring

/-- `θ₂(e^(−πs)) = e^(−πs/4) ϑ(i s/2, i s)` for `s > 0`. -/
theorem theta2_nome_eq {s : ℝ} (hs : 0 < s) :
    (theta2 (nome s) : ℂ)
      = Complex.exp (-(Real.pi * s) / 4) * jacobiTheta₂ (I * s / 2) (I * s) := by
  rw [theta2_eq_tsum_int (nome_pos s) (nome_lt_one hs)]
  unfold jacobiTheta₂ nome
  rw [Complex.ofReal_tsum, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  unfold jacobiTheta₂_term
  rw [← Complex.exp_add, ← Real.exp_mul, Complex.ofReal_exp]
  congr 1
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- `ϑ(z, τ)` is even in `z`. -/
theorem jacobiTheta₂_neg_left' (z τ : ℂ) : jacobiTheta₂ (-z) τ = jacobiTheta₂ z τ := by
  unfold jacobiTheta₂
  rw [← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun n => ?_
  unfold jacobiTheta₂_term
  simp only [Equiv.neg_apply, Int.cast_neg]
  ring_nf

theorem neg_I_mul_I_mul (s : ℝ) : -I * (I * (s : ℂ)) = s := by
  ring_nf
  rw [Complex.I_sq]
  ring

theorem cpow_half_eq_sqrt {s : ℝ} (hs : 0 ≤ s) : ((s : ℂ)) ^ (1 / 2 : ℂ) = (Real.sqrt s : ℂ) := by
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hs]
  push_cast
  rfl

theorem neg_one_div_I_mul {s : ℝ} (hs : s ≠ 0) : (-1 : ℂ) / (I * s) = I * ((1 / s : ℝ) : ℂ) := by
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  have hs2 : (1 / (s : ℂ)) * s = 1 := one_div_mul_cancel hs'
  rw [div_eq_iff (mul_ne_zero I_ne_zero hs')]
  push_cast
  linear_combination hs2 - (1 / (s : ℂ) * s) * Complex.I_sq

theorem half_div_I_mul {s : ℝ} (hs : s ≠ 0) :
    (1 / 2 : ℂ) / (I * s) = -(I * ((1 / s : ℝ) : ℂ) / 2) := by
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  have hs2 : (1 / (s : ℂ)) * s = 1 := one_div_mul_cancel hs'
  rw [div_eq_iff (mul_ne_zero I_ne_zero hs')]
  push_cast
  linear_combination (-(1 / 2 : ℂ)) * hs2 + (1 / (s : ℂ) * s / 2) * Complex.I_sq

theorem neg_pi_I_quarter_div {s : ℝ} (hs : s ≠ 0) :
    -↑Real.pi * I * (1 / 2 : ℂ) ^ 2 / (I * s) = -(Real.pi * (1 / s : ℝ)) / 4 := by
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  have hs2 : (1 / (s : ℂ)) * s = 1 := one_div_mul_cancel hs'
  rw [div_eq_iff (mul_ne_zero I_ne_zero hs')]
  push_cast
  linear_combination (↑Real.pi * I / 4) * hs2

/-- Jacobi's imaginary transformation for `θ₃`: `θ₃(e^(−π/s)) = √s θ₃(e^(−πs))`. -/
theorem theta3_nome_inv {s : ℝ} (hs : 0 < s) :
    theta3 (nome (1 / s)) = Real.sqrt s * theta3 (nome s) := by
  have h := jacobiTheta₂_functional_equation 0 (I * s)
  rw [zero_div, zero_pow two_ne_zero, mul_zero, zero_div, Complex.exp_zero, mul_one,
    neg_I_mul_I_mul, cpow_half_eq_sqrt hs.le, neg_one_div_I_mul hs.ne'] at h
  have h3 := theta3_nome_eq s
  have h3' := theta3_nome_eq (1 / s)
  rw [← h3, ← h3'] at h
  have hsq : (Real.sqrt s : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hs).ne'
  have : (theta3 (nome (1 / s)) : ℂ) = Real.sqrt s * theta3 (nome s) := by
    rw [h]
    field_simp
  exact_mod_cast this

/-- Jacobi's imaginary transformation for `θ₂`/`θ₄`: `θ₂(e^(−π/s)) = √s θ₄(e^(−πs))`. -/
theorem theta2_nome_inv {s : ℝ} (hs : 0 < s) :
    theta2 (nome (1 / s)) = Real.sqrt s * theta4 (nome s) := by
  have h := jacobiTheta₂_functional_equation (1 / 2) (I * s)
  rw [neg_I_mul_I_mul, cpow_half_eq_sqrt hs.le, neg_one_div_I_mul hs.ne', half_div_I_mul hs.ne',
    jacobiTheta₂_neg_left', neg_pi_I_quarter_div hs.ne'] at h
  have h4 := theta4_nome_eq s
  have h2 := theta2_nome_eq (one_div_pos.mpr hs)
  rw [← h4, mul_assoc, ← h2] at h
  have hsq : (Real.sqrt s : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hs).ne'
  have : (theta2 (nome (1 / s)) : ℂ) = Real.sqrt s * theta4 (nome s) := by
    rw [h]
    field_simp
  exact_mod_cast this

/-- `θ₄(e^(−π/s)) = √s θ₂(e^(−πs))`. -/
theorem theta4_nome_inv {s : ℝ} (hs : 0 < s) :
    theta4 (nome (1 / s)) = Real.sqrt s * theta2 (nome s) := by
  have h := theta2_nome_inv (one_div_pos.mpr hs)
  rw [one_div_one_div] at h
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hsqinv : Real.sqrt (1 / s) = 1 / Real.sqrt s := by
    rw [Real.sqrt_div' _ hs.le, Real.sqrt_one]
  rw [hsqinv] at h
  rw [h]
  field_simp

/-- `k'(q) = k(q')` for `q = e^(−πs)`, `q' = e^(−π/s)`. -/
theorem nomeK'_nome_eq_nomeK_inv {s : ℝ} (hs : 0 < s) : nomeK' (nome s) = nomeK (nome (1 / s)) := by
  unfold nomeK nomeK'
  rw [theta2_nome_inv hs, theta3_nome_inv hs, mul_pow, mul_pow]
  have h3 := theta3_pos (nome_pos s).le (nome_lt_one hs)
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  field_simp

/-! ### (4.78) and (4.79) -/

/-- (4.78): `π K'(k)/K(k) = ln(1/q)` for `q = e^(−πs)`, `k = k(q)`, `K'(k) = K(k')`. -/
theorem log_inv_nome {s : ℝ} (hs : 0 < s) :
    Real.pi * ellipticK (nomeK' (nome s)) / ellipticK (nomeK (nome s)) = Real.log (1 / nome s) := by
  have hq0 := (nome_pos s).le
  have hq1 := nome_lt_one hs
  have hq0' := (nome_pos (1 / s)).le
  have hq1' := nome_lt_one (one_div_pos.mpr hs)
  rw [nomeK'_nome_eq_nomeK_inv hs, ellipticK_nomeK hq0' hq1', ellipticK_nomeK hq0 hq1,
    theta3_nome_inv hs, mul_pow, Real.sq_sqrt hs.le]
  have h3 := theta3_pos hq0 hq1
  have hlog : Real.log (1 / nome s) = Real.pi * s := by
    unfold nome
    rw [one_div, Real.log_inv, Real.log_exp, neg_neg]
  rw [hlog]
  field_simp

/-- Sasaki–Kanada (4.79): `ln(1/q) = π/AGM(θ₂²(q), θ₃²(q))` for `q = e^(−πs)`. -/
theorem sasaki_kanada {s : ℝ} (hs : 0 < s) :
    Real.log (1 / nome s) = Real.pi / AGM (theta2 (nome s) ^ 2) (theta3 (nome s) ^ 2) := by
  have hq0 := nome_pos s
  have hq1 := nome_lt_one hs
  have h2 := theta2_pos hq0 hq1
  have h3 := theta3_pos hq0.le hq1
  have hk := nomeK_pos hq0 hq1
  have hk1 := nomeK_le_one hq0.le hq1
  -- `AGM(θ₂², θ₃²) = θ₃² AGM(1, k)`
  have hAGM : AGM (theta2 (nome s) ^ 2) (theta3 (nome s) ^ 2)
      = theta3 (nome s) ^ 2 * AGM 1 (nomeK (nome s)) := by
    rw [AGM_comm, ← AGM_smul (by positivity) one_pos hk, mul_one]
    congr 2
    unfold nomeK
    field_simp
  -- Gauss: `1/AGM(1, k) = (2/π) K(k')`
  have hG := one_div_AGM_one hk hk1
  rw [sqrt_one_sub_nomeK_sq hq0.le hq1] at hG
  have hAGM1 : 0 < AGM 1 (nomeK (nome s)) :=
    lt_of_lt_of_le (lt_min one_pos hk) (min_le_AGM one_pos hk)
  have h78 := log_inv_nome hs
  rw [ellipticK_nomeK hq0.le hq1] at h78
  rw [hAGM, ← h78]
  have hK' : ellipticK (nomeK' (nome s)) = Real.pi / 2 * (1 / AGM 1 (nomeK (nome s))) := by
    rw [hG]
    field_simp
  rw [hK']
  field_simp

end BZ

end Azurite
