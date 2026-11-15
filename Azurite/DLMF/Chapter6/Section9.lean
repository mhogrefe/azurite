/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section10
import Azurite.DLMF.Chapter6.Section8

/-!
# DLMF §6.9: continued fraction

Formalization of <https://dlmf.nist.gov/6.9>, equation 6.9.1 (`dlmf_6_9_1`: on the full region
`|ph z| < π`, no zero denominators and convergence to `E₁(z)`).

Method: with `t = x²`, `eᶻE₁(z) = ∫_0^∞ e^{−t}/(z + t) dt` is `−G(ζ)/ζ` (`e1Weight_G`), `G` the
Cauchy transform of the even weight `|x| e^{−x²}` (`e1Weight`) and `ζ = i√z` (`e1Zeta`,
`ℑζ > 0`).  Its recurrence coefficients are `λ = 1, 1, 2, 2, 3, 3, …` (`e1Weight_P_lam`): the
recurrence polynomials `Rₙ` with these coefficients satisfy `T(2n, 2k) = n! k! C(k, n)`,
`T(2n+1, 2k+1) = n! (k+1)! C(k, n)` for `T(n, k) = L(Rₙ xᵏ)` (`e1T_closed`, from the moments
`m_{2j} = j!`), which vanish for `k < n`.  The J-fraction in `ζ` contracts to the S-fraction
6.9.1 in `z = −ζ²` (`e1CF_canonical`), and §5.10's `SymWeight` theory gives convergence since
`∑ 1/√λₙ = ∞`.  No zero denominators: invariant value regions (`e1CF_nonzero`).
-/

open Complex Filter Topology Set MeasureTheory Polynomial
open scoped Real Nat

namespace Azurite.DLMF

/-! ### The weight `|x| e^{−x²}` and its orthogonal polynomials -/

theorem integrable_pow_mul_abs_mul_exp_neg_sq (k : ℕ) :
    Integrable fun x : ℝ => x ^ k * (|x| * Real.exp (-x ^ 2)) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1) one_pos
    (show (-1 : ℝ) < ((k + 1 : ℕ) : ℝ) by
      have : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith)
  simp only [Real.rpow_natCast, neg_mul, one_mul] at h
  refine h.mono ((by fun_prop : Continuous fun x : ℝ => x ^ k * (|x| * Real.exp (-x ^ 2)))
    |>.aestronglyMeasurable) (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_abs, abs_pow, abs_pow,
    pow_succ]
  ring_nf
  exact le_rfl

/-- The even weight `w(x) = |x| e^{−x²}`: under `t = x²` its Cauchy transform is the Stieltjes
transform of `e^{−t}` on `(0, ∞)`. -/
noncomputable def e1Weight : SymWeight where
  w x := |x| * Real.exp (-x ^ 2)
  nonneg x := by positivity
  pos x hx := mul_pos (abs_pos.mpr hx) (Real.exp_pos _)
  even x := by simp [abs_neg]
  integrable := integrable_pow_mul_abs_mul_exp_neg_sq

theorem e1Weight_w (x : ℝ) : e1Weight.w x = |x| * Real.exp (-x ^ 2) := rfl

theorem e1Weight_mom_odd (j : ℕ) : e1Weight.mom (2 * j + 1) = 0 := by
  rw [← SymWeight.L_X_pow]
  refine e1Weight.L_odd ?_
  rw [X_pow_comp, (odd_two_mul_add_one j).neg_pow]

/-- `m_{2j} = ∫ x^{2j} |x| e^{−x²} dx = j!`. -/
theorem e1Weight_mom_even (j : ℕ) : e1Weight.mom (2 * j) = j ! := by
  have h1 : e1Weight.mom (2 * j) = ∫ x : ℝ, |x| ^ (2 * j + 1) * Real.exp (-|x| ^ 2) := by
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    have e1 : |x| ^ (2 * j + 1) = x ^ (2 * j) * |x| := by
      rw [pow_succ, pow_mul, sq_abs, ← pow_mul]
    show x ^ (2 * j) * (|x| * Real.exp (-x ^ 2)) = |x| ^ (2 * j + 1) * Real.exp (-|x| ^ 2)
    rw [e1, sq_abs]
    ring
  rw [h1, integral_comp_abs (f := fun y => y ^ (2 * j + 1) * Real.exp (-y ^ 2))]
  have h2 := _root_.integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := (2 * j + 1 : ℕ)) (b := 1)
    two_pos (by have : (0 : ℝ) ≤ ((2 * j + 1 : ℕ) : ℝ) := Nat.cast_nonneg _; linarith) one_pos
  have h3 : ∫ x in Ioi (0 : ℝ), x ^ (2 * j + 1) * Real.exp (-x ^ 2) =
      ∫ x in Ioi (0 : ℝ), x ^ ((2 * j + 1 : ℕ) : ℝ) * Real.exp (-1 * x ^ (2 : ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    rw [Real.rpow_natCast, Real.rpow_two, neg_one_mul]
  rw [h3, h2, Real.one_rpow, one_mul]
  have : (((2 * j + 1 : ℕ) : ℝ) + 1) / 2 = (j : ℝ) + 1 := by push_cast; ring
  rw [this, Real.Gamma_nat_eq_factorial]
  ring

/-- The candidate recurrence coefficients `c_m = ⌈m/2⌉`: `1, 1, 2, 2, 3, 3, …`. -/
def e1Lam (m : ℕ) : ℕ := (m + 1) / 2

/-- The polynomials of the recurrence `R_{m+2} = x R_{m+1} − c_{m+1} R_m`. -/
noncomputable def e1R : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X
  | n + 2 => X * e1R (n + 1) - Polynomial.C ((e1Lam (n + 1) : ℕ) : ℝ) * e1R n

/-- `T(n, k) = L(Rₙ xᵏ)`. -/
noncomputable def e1T (n k : ℕ) : ℝ := e1Weight.L (e1R n * X ^ k)

theorem e1T_succ_succ (n k : ℕ) :
    e1T (n + 2) k = e1T (n + 1) (k + 1) - (e1Lam (n + 1) : ℝ) * e1T n k := by
  simp only [e1T, e1R]
  rw [show (X * e1R (n + 1) - Polynomial.C ((e1Lam (n + 1) : ℕ) : ℝ) * e1R n) * X ^ k =
      e1R (n + 1) * X ^ (k + 1) - Polynomial.C ((e1Lam (n + 1) : ℕ) : ℝ) * (e1R n * X ^ k) by
    ring, SymWeight.L_sub, SymWeight.L_C_mul]

theorem e1T_zero (k : ℕ) : e1T 0 k = e1Weight.mom k := by
  simp [e1T, e1R, SymWeight.L_X_pow]

theorem e1T_one (k : ℕ) : e1T 1 k = e1Weight.mom (k + 1) := by
  simp only [e1T, e1R]
  rw [← pow_succ', SymWeight.L_X_pow]

/-- The closed forms `T(2n, 2k) = n! k! C(k, n)`, `T(2n+1, 2k+1) = n! (k+1)! C(k, n)`, and `0`
for mixed parities. -/
theorem e1T_closed : ∀ n k : ℕ,
    e1T (2 * n) (2 * k) = n ! * k ! * (k.choose n : ℝ) ∧ e1T (2 * n) (2 * k + 1) = 0 ∧
      e1T (2 * n + 1) (2 * k + 1) = n ! * (k + 1)! * (k.choose n : ℝ) ∧
      e1T (2 * n + 1) (2 * k) = 0 := by
  intro n
  induction n with
  | zero =>
    intro k
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [e1T_zero, e1Weight_mom_even]
    · simp [e1T_zero, e1Weight_mom_odd]
    · rw [mul_zero, e1T_one, show 2 * k + 1 + 1 = 2 * (k + 1) by ring, e1Weight_mom_even]
      simp
    · rw [mul_zero, e1T_one, e1Weight_mom_odd]
  | succ n ih =>
    have hc1 : (e1Lam (2 * n + 1) : ℝ) = n + 1 := by
      simp only [e1Lam]; rw [show (2 * n + 1 + 1) / 2 = n + 1 by omega]; push_cast; ring
    have hc2 : (e1Lam (2 * n + 2) : ℝ) = n + 1 := by
      simp only [e1Lam]; rw [show (2 * n + 2 + 1) / 2 = n + 1 by omega]; push_cast; ring
    have heven : ∀ k, e1T (2 * (n + 1)) (2 * k) = (n + 1)! * k ! * (k.choose (n + 1) : ℝ) := by
      intro k
      rw [show 2 * (n + 1) = 2 * n + 2 by ring, e1T_succ_succ, hc1,
        show 2 * k + 1 = 2 * k + 1 by rfl, (ih k).2.2.1, (ih k).1]
      have hch : (k.choose (n + 1) : ℝ) * (n + 1) = (k.choose n : ℝ) * (k - n) := by
        rcases lt_or_ge k n with hk | hk
        · rw [Nat.choose_eq_zero_of_lt hk, Nat.choose_eq_zero_of_lt (by omega)]
          simp
        · have := Nat.choose_succ_right_eq k n
          rw [← Nat.cast_sub hk]
          exact_mod_cast this
      rw [Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      linear_combination (-(n ! : ℝ) * k !) * hch
    have hoddeven : ∀ k, e1T (2 * (n + 1)) (2 * k + 1) = 0 := by
      intro k
      rw [show 2 * (n + 1) = 2 * n + 2 by ring, e1T_succ_succ, hc1,
        show 2 * k + 1 + 1 = 2 * (k + 1) by ring, (ih (k + 1)).2.2.2, (ih k).2.1]
      ring
    intro k
    refine ⟨heven k, hoddeven k, ?_, ?_⟩
    · rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 2 by ring, e1T_succ_succ,
        show 2 * n + 1 + 1 = 2 * n + 2 by ring, hc2,
        show 2 * n + 2 = 2 * (n + 1) by ring, show 2 * k + 1 + 1 = 2 * (k + 1) by ring,
        heven (k + 1), (ih k).2.2.1, Nat.choose_succ_succ]
      rw [Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      ring
    · rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 2 by ring, e1T_succ_succ,
        show 2 * n + 1 + 1 = 2 * n + 2 by ring, hc2,
        show 2 * n + 2 = 2 * (n + 1) by ring, hoddeven k, (ih k).2.2.2]
      ring

theorem e1T_diag (n : ℕ) :
    e1T (2 * n) (2 * n) = n ! * n ! ∧ e1T (2 * n + 1) (2 * n + 1) = n ! * (n + 1)! := by
  refine ⟨?_, ?_⟩
  · rw [(e1T_closed n n).1, Nat.choose_self]; simp
  · rw [(e1T_closed n n).2.2.1, Nat.choose_self]; simp

/-- **The recurrence coefficients of `|x| e^{−x²}`**: the orthogonal polynomials are the `Rₙ`,
and `λ_{m+1} = c_{m+1}` (`λ = 1, 1, 2, 2, 3, 3, …`). -/
theorem e1Weight_P_lam : ∀ n : ℕ, e1Weight.P n = e1R n ∧ e1Weight.P (n + 1) = e1R (n + 1) ∧
    e1Weight.lam (n + 1) = e1Lam (n + 1) := by
  have hT : ∀ m, e1Weight.P m = e1R m → e1Weight.h m = e1T m m := fun m h => by
    rw [SymWeight.h, h]; rfl
  have hlam : ∀ n, e1Weight.P n = e1R n → e1Weight.P (n + 1) = e1R (n + 1) →
      e1Weight.lam (n + 1) = e1Lam (n + 1) := by
    intro n h0 h1
    rw [SymWeight.lam, Nat.add_sub_cancel, hT _ h1, hT _ h0]
    rcases Nat.even_or_odd n with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [show j + j = 2 * j by ring, (e1T_diag j).2, (e1T_diag j).1]
      simp only [e1Lam]
      rw [show (2 * j + 1 + 1) / 2 = j + 1 by omega, Nat.factorial_succ]
      have : (j ! : ℝ) ≠ 0 := by positivity
      push_cast
      field_simp
    · rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring, (e1T_diag (j + 1)).1, (e1T_diag j).2]
      simp only [e1Lam]
      rw [show (2 * (j + 1) + 1) / 2 = j + 1 by omega, Nat.factorial_succ]
      have : (j ! : ℝ) ≠ 0 := by positivity
      push_cast
      field_simp
  intro n
  induction n with
  | zero =>
    have h0 : e1Weight.P 0 = e1R 0 := by rw [SymWeight.P_zero]; rfl
    have h1 : e1Weight.P 1 = e1R 1 := by rw [SymWeight.P_one]; rfl
    exact ⟨h0, h1, hlam 0 h0 h1⟩
  | succ n ih =>
    obtain ⟨h0, h1, hl⟩ := ih
    have h2 : e1Weight.P (n + 2) = e1R (n + 2) := by
      rw [SymWeight.P_succ_succ, h1, h0, hl]; rfl
    exact ⟨h1, h2, hlam (n + 1) h1 h2⟩

theorem e1Weight_lam (n : ℕ) : e1Weight.lam (n + 1) = ((n + 2) / 2 : ℕ) :=
  (e1Weight_P_lam n).2.2

theorem e1Weight_mom_zero : e1Weight.mom 0 = 1 := by
  have := e1Weight_mom_even 0
  simpa using this

/-! ### The bridge `G(ζ) = −ζ eᶻ E₁(z)`, `ζ = i √z` -/

/-- `ζ = i e^{(ln z)/2}`: `ζ² = −z`, and `ℑζ > 0` off the cut. -/
noncomputable def e1Zeta (z : ℂ) : ℂ := I * cexp (Complex.log z / 2)

theorem e1Zeta_sq {z : ℂ} (hz : z ≠ 0) : e1Zeta z ^ 2 = -z := by
  rw [e1Zeta, mul_pow, I_sq, ← exp_nat_mul]
  push_cast
  rw [show (2 : ℂ) * (Complex.log z / 2) = Complex.log z by ring, exp_log hz]
  ring

theorem e1Zeta_im_pos {z : ℂ} (hz : z ∈ slitPlane) : 0 < (e1Zeta z).im := by
  rw [e1Zeta, mul_im, I_re, I_im, zero_mul, one_mul, zero_add, exp_re]
  refine mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩)
  · have h := neg_pi_lt_arg z
    simp only [div_ofNat_im, log_im]
    linarith
  · have h1 := arg_le_pi z
    have h2 : z.arg ≠ π := ((mem_slitPlane_iff_arg).mp hz).1
    simp only [div_ofNat_im, log_im]
    have := lt_of_le_of_ne h1 h2
    linarith

theorem integrable_e1Weight : Integrable e1Weight.w := by
  simpa using e1Weight.integrable 0

/-- **The bridge**: the Cauchy transform of `|x| e^{−x²}` at `ζ = i√z` is `−ζ eᶻ E₁(z)` (pair `x`
with `−x`, then `t = x²`; 6.2.2). -/
theorem e1Weight_G {z : ℂ} (hz : z ∈ slitPlane) :
    e1Weight.G (e1Zeta z) = -(e1Zeta z * (cexp z * expIntE₁ z)) := by
  set ζ := e1Zeta z with hζdef
  have hz0 := slitPlane_ne_zero hz
  have hζim : ζ.im ≠ 0 := (e1Zeta_im_pos hz).ne'
  have hζ2 : ζ ^ 2 = -z := e1Zeta_sq hz0
  set f : ℝ → ℂ := fun x => (e1Weight.w x : ℂ) / (ζ - x) with hf
  have hfi : Integrable f := SymWeight.integrable_ofReal_div_sub integrable_e1Weight hζim
  -- `∫_ℝ f = ∫_0^∞ (f(x) + f(−x)) dx`
  have hsplit : ∫ x, f x = ∫ x in Ioi (0 : ℝ), (f x + f (-x)) := by
    rw [← intervalIntegral.integral_Iic_add_Ioi hfi.integrableOn hfi.integrableOn, add_comm,
      integral_add hfi.integrableOn (hfi.comp_neg.integrableOn)]
    congr 1
    rw [integral_comp_neg_Ioi, neg_zero]
  -- `f(x) + f(−x) = 2x e^{−x²} ζ/(ζ² − x²)` for `x > 0`
  have hpt : ∀ x : ℝ, 0 < x → f x + f (-x) =
      ζ * ((2 * x : ℝ) • (cexp (-((x ^ 2 : ℝ) : ℂ)) / (ζ ^ 2 - ((x ^ 2 : ℝ) : ℂ)))) := by
    intro x hx
    have h1 : ζ - x ≠ 0 := SymWeight.sub_ofReal_ne_zero hζim x
    have h2 : ζ + x ≠ 0 := by
      have := SymWeight.sub_ofReal_ne_zero hζim (-x)
      simpa [sub_neg_eq_add] using this
    have h3 : ζ ^ 2 - ((x ^ 2 : ℝ) : ℂ) ≠ 0 := by
      rw [show ζ ^ 2 - ((x ^ 2 : ℝ) : ℂ) = (ζ - x) * (ζ + x) by push_cast; ring]
      exact mul_ne_zero h1 h2
    simp only [hf, e1Weight_w, abs_neg, neg_sq, abs_of_pos hx, real_smul]
    push_cast
    rw [sub_neg_eq_add]
    push_cast at h3
    field_simp
    ring
  have hsub := integral_comp_rpow_Ioi
    (fun t : ℝ => cexp (-(t : ℂ)) / (ζ ^ 2 - (t : ℂ))) (p := 2) two_ne_zero
  have hcongr : ∫ x in Ioi (0 : ℝ), (f x + f (-x)) =
      ζ * ∫ x in Ioi (0 : ℝ), (|(2 : ℝ)| * x ^ ((2 : ℝ) - 1)) •
        (fun t : ℝ => cexp (-(t : ℂ)) / (ζ ^ 2 - (t : ℂ))) (x ^ (2 : ℝ)) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    rw [hpt x hx]
    simp only [abs_two, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two]
  rw [SymWeight.G, hsplit, hcongr, hsub, hζ2]
  -- `∫_0^∞ e^{−t}/(−z − t) dt = −eᶻ E₁(z)` (6.2.2)
  have h22 := dlmf_6_2_2 hz0 ((mem_slitPlane_iff_arg.mp hz).1 |> fun h =>
    lt_of_le_of_ne (abs_le.mpr ⟨(neg_pi_lt_arg z).le, arg_le_pi z⟩) (by
      intro habs
      rcases abs_eq (Real.pi_pos.le) |>.mp habs with h' | h'
      · exact h h'
      · linarith [neg_pi_lt_arg z]))
  have hee : cexp z * cexp (-z) = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]
  have hint : ∫ t in Ioi (0 : ℝ), cexp (-(t : ℂ)) / (-z - (t : ℂ)) =
      -∫ t in Ioi (0 : ℝ), cexp (-(t : ℂ)) / ((t : ℂ) + z) := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [show -z - (t : ℂ) = -((t : ℂ) + z) by ring, div_neg]
  rw [hint, h22]
  linear_combination (ζ * ∫ t in Ioi (0 : ℝ), cexp (-(t : ℂ)) / ((t : ℂ) + z)) * hee

/-! ### The continued fraction 6.9.1 -/

/-- The partial numerators of 6.9.1: `a₁ = e^{−z}`, `a_k = ⌊k/2⌋` (`1, 1, 2, 2, 3, …`) for
`k ≥ 2`. -/
noncomputable def e1CFa (z : ℂ) (k : ℕ) : ℂ :=
  if k = 0 then 0 else if k = 1 then cexp (-z) else ((k / 2 : ℕ) : ℂ)

/-- The partial denominators of 6.9.1: `b₀ = 0`, `b_k = z` for odd `k`, `1` for even `k ≥ 2`. -/
def e1CFb (z : ℂ) (k : ℕ) : ℂ := if k = 0 then 0 else if k % 2 = 1 then z else 1

theorem e1CFb_even (z : ℂ) (n : ℕ) : e1CFb z (2 * n + 2) = 1 := by
  simp [e1CFb, show (2 * n + 2) % 2 = 0 by omega]

theorem e1CFb_odd (z : ℂ) (n : ℕ) : e1CFb z (2 * n + 1) = z := by
  simp [e1CFb, show (2 * n + 1) % 2 = 1 by omega]

theorem e1CFa_even (z : ℂ) (n : ℕ) : e1CFa z (2 * n + 2) = n + 1 := by
  simp [e1CFa, show (2 * n + 2) / 2 = n + 1 by omega]

theorem e1CFa_odd (z : ℂ) (n : ℕ) : e1CFa z (2 * n + 3) = n + 1 := by
  simp [e1CFa, show (2 * n + 3) / 2 = n + 1 by omega, show 2 * n + 3 ≠ 1 by omega]

theorem e1Weight_lam_odd (n : ℕ) : (e1Weight.lam (2 * n + 1) : ℂ) = n + 1 := by
  rw [e1Weight_lam, show (2 * n + 2) / 2 = n + 1 by omega]; push_cast; ring

theorem e1Weight_lam_even (n : ℕ) : (e1Weight.lam (2 * n + 2) : ℂ) = n + 1 := by
  rw [show 2 * n + 2 = (2 * n + 1) + 1 by ring, e1Weight_lam,
    show (2 * n + 1 + 2) / 2 = n + 1 by omega]; push_cast; ring

/-- **The contraction**: the canonical denominators and numerators of 6.9.1 are, up to signs and
a factor `ζ`, `Pₙ(ζ)` and `e^{−z} Qₙ(ζ)` of the weight `|x| e^{−x²}`, `ζ² = −z`. -/
theorem e1CF_canonical (z ζ : ℂ) (hζ2 : ζ ^ 2 = -z) : ∀ n : ℕ,
    cfQ (e1CFa z) (e1CFb z) (2 * n + 1) = (-1) ^ n * e1Weight.pz (2 * n) ζ ∧
      cfQ (e1CFa z) (e1CFb z) (2 * n + 2) = (-1) ^ (n + 1) * ζ * e1Weight.pz (2 * n + 1) ζ ∧
      ζ * cfP (e1CFa z) (e1CFb z) (2 * n + 1) =
        (-1) ^ (n + 1) * cexp (-z) * e1Weight.qz (2 * n) ζ ∧
      cfP (e1CFa z) (e1CFb z) (2 * n + 2) = (-1) ^ n * cexp (-z) * e1Weight.qz (2 * n + 1) ζ := by
  have eQ : ∀ k, cfQ (e1CFa z) (e1CFb z) (k + 2) =
      e1CFb z (k + 1) * cfQ (e1CFa z) (e1CFb z) (k + 1) +
        e1CFa z (k + 1) * cfQ (e1CFa z) (e1CFb z) k := fun k => rfl
  have eP : ∀ k, cfP (e1CFa z) (e1CFb z) (k + 2) =
      e1CFb z (k + 1) * cfP (e1CFa z) (e1CFb z) (k + 1) +
        e1CFa z (k + 1) * cfP (e1CFa z) (e1CFb z) k := fun k => rfl
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [cfQ, SymWeight.pz_zero]
    · rw [eQ, SymWeight.pz_one]
      simp [cfQ, e1CFb, e1CFa]
      linear_combination hζ2
    · simp [cfP, e1CFb, SymWeight.qz_zero]
    · rw [eP]
      simp [cfP, e1CFb, e1CFa, SymWeight.qz_one, e1Weight_mom_zero]
  | succ n ih =>
    obtain ⟨q1, q2, p1, p2⟩ := ih
    have hQ3 : cfQ (e1CFa z) (e1CFb z) (2 * (n + 1) + 1) =
        (-1) ^ (n + 1) * e1Weight.pz (2 * (n + 1)) ζ := by
      rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring, eQ,
        show 2 * n + 1 + 1 = 2 * n + 2 by ring, e1CFb_even, e1CFa_even, q2,
        show 2 * n + 1 = 2 * n + 1 by rfl, q1, show 2 * (n + 1) = 2 * n + 2 by ring,
        show 2 * n + 2 = (2 * n) + 2 by rfl, SymWeight.pz_succ_succ, e1Weight_lam_odd]
      ring
    have hP3 : ζ * cfP (e1CFa z) (e1CFb z) (2 * (n + 1) + 1) =
        (-1) ^ (n + 1 + 1) * cexp (-z) * e1Weight.qz (2 * (n + 1)) ζ := by
      rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring, eP,
        show 2 * n + 1 + 1 = 2 * n + 2 by ring, e1CFb_even, e1CFa_even, p2,
        show 2 * (n + 1) = 2 * n + 2 by ring, SymWeight.qz_succ_succ, e1Weight_lam_odd]
      linear_combination (n + 1 : ℂ) * p1
    refine ⟨hQ3, ?_, hP3, ?_⟩
    · rw [show 2 * (n + 1) + 2 = (2 * n + 2) + 2 by ring, eQ,
        show 2 * n + 2 + 1 = 2 * (n + 1) + 1 by ring, e1CFb_odd,
        show 2 * (n + 1) + 1 = 2 * n + 3 by ring, e1CFa_odd,
        show 2 * n + 3 = 2 * (n + 1) + 1 by ring, hQ3, q2,
        show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring, SymWeight.pz_succ_succ,
        show 2 * n + 1 + 1 = 2 * n + 2 by ring, e1Weight_lam_even,
        show 2 * (n + 1) = 2 * n + 2 by ring]
      linear_combination ((-1) ^ (n + 1) * e1Weight.pz (2 * n + 2) ζ) * hζ2
    · rw [show 2 * (n + 1) + 2 = (2 * n + 2) + 2 by ring, eP,
        show 2 * n + 2 + 1 = 2 * (n + 1) + 1 by ring, e1CFb_odd,
        show 2 * (n + 1) + 1 = 2 * n + 3 by ring, e1CFa_odd, p2,
        show 2 * n + 3 = (2 * n + 1) + 2 by ring, SymWeight.qz_succ_succ,
        show 2 * n + 1 + 1 = 2 * n + 2 by ring, e1Weight_lam_even]
      rw [show 2 * (n + 1) + 1 = 2 * n + 3 by ring] at hP3
      rw [show 2 * (n + 1) = 2 * n + 2 by ring] at hP3
      rw [show 2 * n + 3 = (2 * n + 1) + 2 by ring] at hP3
      linear_combination (cfP (e1CFa z) (e1CFb z) (2 * n + 1 + 2)) * hζ2 + (-ζ) * hP3

/-! ### No zero denominators, and convergence -/

/-- `ℑ(c/v) = −c ℑv/|v|²` for real `c`. -/
theorem im_ofReal_div (c : ℝ) (v : ℂ) : ((c : ℂ) / v).im = -(c * v.im) / normSq v := by
  rw [div_im]
  simp only [ofReal_im, zero_mul, zero_div, ofReal_re, zero_sub]
  ring

/-- The value regions: `A` (entering a level with `b = z`) and `B` (entering `b = 1`), with
`σ = ℑz`. -/
def e1RegA (z : ℂ) : Set ℂ := {w | 0 < z.im * w.im ∨ (w.im = 0 ∧ 0 ≤ w.re)}

def e1RegB (z : ℂ) : Set ℂ := {w | z.im * w.im < 0 ∨ (w.im = 0 ∧ 0 ≤ w.re)}

theorem e1CF_nonzero_aux {z : ℂ} (hz : z ∈ slitPlane) : ∀ n : ℕ, ∀ w : ℂ,
    (if n % 2 = 1 then w ∈ e1RegA z else w ∈ e1RegB z) →
      CfNonzero (e1CFa z) (e1CFb z) n w := by
  have hzc : 0 < z.im * z.im ∨ (z.im = 0 ∧ 0 < z.re) := by
    rcases (mem_slitPlane_iff.mp hz) with h | h
    · rcases eq_or_ne z.im 0 with h' | h'
      · exact Or.inr ⟨h', h⟩
      · exact Or.inl (mul_self_pos.mpr h')
    · exact Or.inl (mul_self_pos.mpr h)
  intro n
  induction n with
  | zero => intro _ _; trivial
  | succ n ih =>
    intro w hw
    rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · -- level `n + 1 = 2m + 1` is odd: `b = z`, `w ∈ A`
      have hb : e1CFb z (m + m + 1) = z := by rw [← two_mul, e1CFb_odd]
      have hwA : w ∈ e1RegA z := by
        simpa [show (m + m + 1) % 2 = 1 by omega] using hw
      have hsum : z + w ≠ 0 ∧ (0 < z.im * (z + w).im ∨ ((z + w).im = 0 ∧ 0 < (z + w).re)) := by
        rcases hwA with h | ⟨h1, h2⟩ <;> rcases hzc with hc | ⟨hc1, hc2⟩
        · have : 0 < z.im * (z + w).im := by rw [add_im]; nlinarith
          exact ⟨fun h0 => by rw [h0] at this; simp at this, Or.inl this⟩
        · rw [hc1] at h; simp at h
        · have : 0 < z.im * (z + w).im := by rw [add_im, h1, add_zero]; exact hc
          exact ⟨fun h0 => by rw [h0] at this; simp at this, Or.inl this⟩
        · have hre : 0 < (z + w).re := by rw [add_re]; linarith
          exact ⟨fun h0 => by rw [h0] at hre; simp at hre,
            Or.inr ⟨by rw [add_im, hc1, h1, add_zero], hre⟩⟩
      refine ⟨by rw [hb]; exact hsum.1, ?_⟩
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · trivial
      · refine ih _ ?_
        rw [ite_eq_right (by omega)]
        have ha : e1CFa z (m + m + 1) = ((m : ℝ) : ℂ) := by
          have : m + m + 1 = 2 * (m - 1) + 3 := by omega
          rw [this, e1CFa_odd]
          push_cast
          rw [Nat.cast_sub hm]
          ring
        rw [ha, hb]
        set v := z + w
        have hns : 0 < normSq v := normSq_pos.mpr hsum.1
        have hm' : (0 : ℝ) < m := by exact_mod_cast hm
        rcases hsum.2 with h | ⟨h1, h2⟩
        · left
          rw [im_ofReal_div, mul_div_assoc', div_neg_iff]
          right
          exact ⟨by nlinarith, hns⟩
        · right
          refine ⟨by rw [im_ofReal_div, h1]; simp, ?_⟩
          rw [div_re]
          simp only [ofReal_re, ofReal_im, zero_mul, zero_div, add_zero]
          positivity
    · -- level `n + 1 = 2m + 2` is even: `b = 1`, `w ∈ B`
      have hb : e1CFb z (2 * m + 1 + 1) = 1 := e1CFb_even z m
      have hwB : w ∈ e1RegB z := by
        simpa [show (2 * m + 1 + 1) % 2 = 0 by omega] using hw
      have ha : e1CFa z (2 * m + 1 + 1) = (((m + 1 : ℕ) : ℝ) : ℂ) := by
        rw [e1CFa_even]; push_cast; ring
      have hsum : 1 + w ≠ 0 ∧ (z.im * (1 + w).im < 0 ∨ ((1 + w).im = 0 ∧ 0 < (1 + w).re)) := by
        rcases hwB with h | ⟨h1, h2⟩
        · have him : (1 + w).im = w.im := by simp
          have hw0 : w.im ≠ 0 := fun h0 => by rw [h0, mul_zero] at h; exact lt_irrefl _ h
          exact ⟨fun h0 => hw0 (by rw [← him, h0, zero_im]), Or.inl (by rw [him]; exact h)⟩
        · have hre : 0 < (1 + w).re := by simp; linarith
          exact ⟨fun h0 => by rw [h0] at hre; simp at hre, Or.inr ⟨by simp [h1], hre⟩⟩
      refine ⟨by rw [hb]; exact hsum.1, ih _ ?_⟩
      rw [ite_eq_left (by omega), ha, hb]
      set v := 1 + w
      have hns : 0 < normSq v := normSq_pos.mpr hsum.1
      have hm' : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
      rcases hsum.2 with h | ⟨h1, h2⟩
      · left
        rw [im_ofReal_div, mul_div_assoc']
        exact div_pos (by nlinarith) hns
      · right
        refine ⟨by rw [im_ofReal_div, h1]; simp, ?_⟩
        rw [div_re]
        simp only [ofReal_re, ofReal_im, zero_mul, zero_div, add_zero]
        positivity

theorem e1CF_nonzero {z : ℂ} (hz : z ∈ slitPlane) (n : ℕ) :
    CfNonzero (e1CFa z) (e1CFb z) n 0 := by
  refine e1CF_nonzero_aux hz n 0 ?_
  split_ifs
  · exact Or.inr ⟨by simp, by simp⟩
  · exact Or.inr ⟨by simp, by simp⟩

theorem not_summable_e1Weight_lam : ¬Summable fun n => 1 / √(e1Weight.lam (n + 1)) := by
  intro hs
  have h0 : ¬Summable (fun n : ℕ => 1 / ((n : ℝ) ^ ((1 : ℝ) / 2))) := by
    rw [Real.summable_one_div_nat_rpow]; norm_num
  apply h0
  rw [← summable_nat_add_iff 1]
  refine hs.of_nonneg_of_le (fun n => by positivity) fun n => ?_
  rw [e1Weight_lam, ← Real.sqrt_eq_rpow]
  have hl : (0 : ℝ) < ((n + 2) / 2 : ℕ) := by
    have : 1 ≤ (n + 2) / 2 := by omega
    exact_mod_cast this
  refine one_div_le_one_div_of_le (Real.sqrt_pos.mpr hl) (Real.sqrt_le_sqrt ?_)
  have : (n + 2) / 2 ≤ n + 1 := by omega
  push_cast
  exact_mod_cast this

/-- **DLMF 6.9.1**: for `|ph z| < π` the continued fraction
`E₁(z) = e^{−z}/(z + 1/(1 + 1/(z + 2/(1 + 2/(z + ⋯)))))` has no zero denominators and converges
to `E₁(z)`. -/
theorem dlmf_6_9_1 {z : ℂ} (hz : z ∈ slitPlane) :
    (∀ n, CfNonzero (e1CFa z) (e1CFb z) n 0) ∧ CfConverges (e1CFa z) (e1CFb z) (expIntE₁ z) := by
  refine ⟨e1CF_nonzero hz, ?_⟩
  set ζ := e1Zeta z with hζdef
  have hz0 := slitPlane_ne_zero hz
  have hζim : ζ.im ≠ 0 := (e1Zeta_im_pos hz).ne'
  have hζ0 : ζ ≠ 0 := fun h => hζim (by rw [h, zero_im])
  have hζ2 : ζ ^ 2 = -z := e1Zeta_sq hz0
  -- every convergent is `−e^{−z} Qₙ(ζ)/(ζ Pₙ(ζ))`
  have hconv : ∀ n, cfConv (e1CFa z) (e1CFb z) n =
      -cexp (-z) * (e1Weight.qz n ζ / e1Weight.pz n ζ) / ζ := by
    intro n
    rw [dlmf_1_12_4 _ _ (e1CF_nonzero hz n), cfA, cfB]
    have hpz := e1Weight.pz_ne_zero hζim n
    rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · obtain ⟨q1, -, p1, -⟩ := e1CF_canonical z ζ hζ2 m
      rw [show m + m + 1 = 2 * m + 1 by ring, q1, show m + m = 2 * m by ring]
      have hP : cfP (e1CFa z) (e1CFb z) (2 * m + 1) =
          (-1) ^ (m + 1) * cexp (-z) * e1Weight.qz (2 * m) ζ / ζ := by
        rw [← p1]; field_simp
      rw [hP]
      have hs : ((-1 : ℂ)) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
      field_simp
      ring
    · obtain ⟨-, q2, -, p2⟩ := e1CF_canonical z ζ hζ2 m
      rw [show 2 * m + 1 + 1 = 2 * m + 2 by ring, q2, p2]
      have hs : ((-1 : ℂ)) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
      field_simp
      ring
  have hlim := ((e1Weight.tendsto_qz_div_pz_of_not_summable not_summable_e1Weight_lam
    hζim).const_mul (-cexp (-z))).div_const ζ
  rw [e1Weight_G hz, ← hζdef] at hlim
  have hval : -cexp (-z) * -(ζ * (cexp z * expIntE₁ z)) / ζ = expIntE₁ z := by
    have hee : cexp (-z) * cexp z = 1 := by rw [← exp_add, neg_add_cancel, exp_zero]
    field_simp
    linear_combination (expIntE₁ z) * hee
  rw [hval] at hlim
  exact hlim.congr fun n => (hconv n).symm

end Azurite.DLMF
