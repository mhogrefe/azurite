/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section5GaussLegendre
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.ChebyshevGauss
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality

/-!
# DLMF §3.5(v): the Gauss–Chebyshev formulas

Formulas 3.5.22–3.5.25.

* General tools: `gauss_rule_eq` (`n` distinct zeros of `p_n` plus weights exact on degree `< n`
  are the Gauss nodes and Christoffel numbers), `eq_zero_of_T` (a linear functional vanishing on
  `T₀, …, T_{n−1}` vanishes on degree `< n`), `integral_cos_int_mul`, `integral_cos_mul_cos`,
  `sum_range_cos_two_pi`, `circ_exact`, `trap_exact` (aliasing-free trapezoidal sums).
* The weights `chebWeight g = g(x)/√(1 − x²)` with `g = 1, 1 − x², 1 − x, 1 + x`
  (`chebWeight_eq_rpow`: the DLMF forms `(1 − x)^α (1 + x)^β`, `|α| = |β| = ½`),
  `wInt_chebWeight` (`x = cos θ`, via Mathlib's `integral_measureT_eq_integral_cos`),
  `isGaussWeight_chebWeight`.
* The monic orthogonal polynomials `gcT = 2^{1−n}T_n`, `gcU = 2^{−n}U_n`,
  `gcW = 2^{−n}(U_n + U_{n−1})`, `gcV = 2^{−n}(U_n − U_{n−1})` (`isOrthMonic_gcT` …), from the
  identities `cheb_U_identity`, `cheb_W_identity`, `cheb_V_identity`.
* 3.5.22: `dlmf_3_5_22`; 3.5.23: `dlmf_3_5_23` (exactness from Mathlib's `integral_eq_sumZeroes`).
* 3.5.24: `dlmf_3_5_24` (nodes `gcNodesU`, weights), `dlmf_3_5_24_gamma`.
* 3.5.25: `dlmf_3_5_25_W` (`α = ½`, nodes `+cos(2kπ/(2n+1))`), `dlmf_3_5_25_V` (`α = −½`, nodes
  `−cos(2kπ/(2n+1))`), `dlmf_3_5_25_gamma_W`, `dlmf_3_5_25_gamma_V`.
-/

open Polynomial Finset Set MeasureTheory intervalIntegral Real Polynomial.Chebyshev

namespace Azurite.DLMF

/-! ### Identifying a Gauss rule -/

/-- A Gauss rule is determined by `n` distinct zeros of `p_n` and weights that integrate every
polynomial of degree `< n` exactly: these are the nodes and the Christoffel numbers. -/
theorem gauss_rule_eq {I : Set ℝ} {w : ℝ → ℝ} (hw : IsGaussWeight I w) {n : ℕ} {p : ℝ[X]}
    (hp : IsOrthMonic I w n p) {S : Finset ℝ} (hS : #S = n) (hz : ∀ x ∈ S, p.eval x = 0)
    {c : ℝ → ℝ} (hc : ∀ q : ℝ[X], q.degree < n → wInt I w q = ∑ x ∈ S, c x * q.eval x) :
    p.roots.toFinset = S ∧ ∀ x ∈ S, christoffel I w p x = c x := by
  classical
  obtain ⟨hnodup, hcard, -⟩ := hp.roots_spec hw
  have hsub : S ⊆ p.roots.toFinset := fun x hx =>
    Multiset.mem_toFinset.mpr ((mem_roots hp.1.ne_zero).mpr (hz x hx))
  have heq : p.roots.toFinset = S :=
    (eq_of_subset_of_card_le hsub (by rw [Multiset.toFinset_card_of_nodup hnodup, hcard, hS])).symm
  refine ⟨heq, fun x hx => ?_⟩
  have hk : x ∈ p.roots.toFinset := heq ▸ hx
  have hinj : Set.InjOn (id : ℝ → ℝ) (S : Set ℝ) := Function.injective_id.injOn
  rw [christoffel_eq_wInt_basis hw hp hk, heq, hc _ (by
    rw [Lagrange.degree_basis hinj hx, hS]
    exact_mod_cast Nat.sub_lt (hS ▸ card_pos.mpr ⟨x, hx⟩) one_pos)]
  rw [sum_eq_single_of_mem x hx fun y hy hyx => by
    rw [show (Lagrange.basis S id x).eval y = 0 from Lagrange.eval_basis_of_ne (v := id)
      (Ne.symm hyx) hy, mul_zero],
    show (Lagrange.basis S id x).eval x = 1 from Lagrange.eval_basis_self (v := id) hinj hx,
    mul_one]

/-- A linear functional that vanishes on `T₀, …, T_{n−1}` vanishes on all polynomials of degree
`< n`. -/
theorem eq_zero_of_T {F : ℝ[X] → ℝ} (hadd : ∀ p q, F (p + q) = F p + F q)
    (hsmul : ∀ (c : ℝ) p, F (C c * p) = c * F p) {n : ℕ} (hT : ∀ m < n, F (T ℝ m) = 0)
    {q : ℝ[X]} (hq : q.degree < n) : F q = 0 := by
  have hF0 : F 0 = 0 := by simpa using hsmul 0 0
  have hmem : q ∈ degreeLT ℝ n := mem_degreeLT.mpr hq
  rw [← Sequence.span_degreeLT (chebyshevTsequence ℝ) (by simp)] at hmem
  clear hq
  induction hmem using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    exact hT m hm
  | zero => exact hF0
  | add x y _ _ hx hy => rw [hadd, hx, hy, add_zero]
  | smul c x _ hx => rw [smul_eq_C_mul, hsmul, hx, mul_zero]

/-! ### Trigonometric integrals and sums -/

theorem integral_cos_int_mul (a : ℤ) :
    ∫ θ in (0 : ℝ)..π, Real.cos (a * θ) = if a = 0 then π else 0 := by
  split_ifs with ha
  · simp [ha]
  · have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) ha', integral_cos,
      mul_zero, Real.sin_zero, sub_zero, Real.sin_int_mul_pi, smul_zero]

/-- `∑_{k<M} cos(2πak/M) = M` if `M ∣ a` and `0` otherwise. -/
theorem sum_range_cos_two_pi {M : ℕ} (hM : 0 < M) (a : ℤ) :
    ∑ k ∈ range M, Real.cos (2 * π * a * k / M) = if (M : ℤ) ∣ a then (M : ℝ) else 0 := by
  have hM0 : (M : ℝ) ≠ 0 := by positivity
  split_ifs with h
  · obtain ⟨t, rfl⟩ := h
    rw [sum_congr rfl fun (k : ℕ) _ => show Real.cos (2 * π * ((M * t : ℤ) : ℝ) * k / M) = 1 by
      rw [show 2 * π * ((M * t : ℤ) : ℝ) * k / M = ((t * k : ℤ) : ℝ) * (2 * π) by
        push_cast; field_simp]
      exact Real.cos_int_mul_two_pi _]
    simp
  · set ζ := Complex.exp (2 * π * a / M * Complex.I)
    have hM0' : (M : ℂ) ≠ 0 := by exact_mod_cast hM0
    have hζ : ζ ≠ 1 := by
      intro h1
      obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp h1
      apply h
      refine ⟨m, ?_⟩
      have : (a : ℂ) = M * m := by
        have := hm
        field_simp at this
        linear_combination this
      exact_mod_cast this
    have hζn : ζ ^ M = 1 := by
      rw [← Complex.exp_nat_mul, show (M : ℂ) * (2 * π * a / M * Complex.I) =
        (a : ℂ) * (2 * π * Complex.I) by field_simp]
      exact Complex.exp_int_mul_two_pi_mul_I a
    have hterm : ∀ k : ℕ, Real.cos (2 * π * a * k / M) = (ζ ^ k).re := fun k => by
      rw [← Complex.exp_nat_mul, ← Complex.exp_ofReal_mul_I_re]
      congr 2
      push_cast; ring
    rw [sum_congr rfl fun k _ => hterm k, ← Complex.re_sum, geom_sum_eq hζ, hζn]
    simp

/-- The trapezoidal rule with `M` points on the circle integrates `cos(aθ)` over `[0, π]` exactly
for `|a| < M`. -/
theorem circ_exact {M : ℕ} (hM : 0 < M) {a : ℤ} (ha : |a| < M) :
    π / M * ∑ k ∈ range M, Real.cos (2 * π * a * k / M) =
      ∫ θ in (0 : ℝ)..π, Real.cos (a * θ) := by
  rw [sum_range_cos_two_pi hM, integral_cos_int_mul]
  have hiff : (M : ℤ) ∣ a ↔ a = 0 := by
    constructor
    · intro h; exact Int.eq_zero_of_abs_lt_dvd h ha
    · rintro rfl; exact dvd_zero _
  by_cases h0 : a = 0
  · simp only [h0, dvd_zero, ↓reduceIte]; field_simp
  · simp [h0, mt hiff.mp h0]

/-- The trapezoidal rule with `N` panels on `[0, π]` (weights `g_k`) integrates `cos(aθ)`
exactly for `|a| < 2N`. -/
theorem trap_exact {N : ℕ} (hN : 0 < N) {a : ℤ} (ha : |a| < 2 * N) :
    π / (2 * N) * ∑ k ∈ range (N + 1), ccG N k * Real.cos (a * k * π / N) =
      ∫ θ in (0 : ℝ)..π, Real.cos (a * θ) := by
  rw [sum_ccG_mul_cos hN, integral_cos_int_mul]
  have hiff : (2 * N : ℤ) ∣ a ↔ a = 0 := by
    constructor
    · intro h; exact Int.eq_zero_of_abs_lt_dvd h (by exact_mod_cast ha)
    · rintro rfl; exact dvd_zero _
  by_cases h0 : a = 0
  · simp only [h0, dvd_zero, ↓reduceIte]
    have : (N : ℝ) ≠ 0 := by positivity
    field_simp
  · simp [h0, mt hiff.mp h0]

theorem integral_cos_mul_cos (a b : ℤ) :
    ∫ θ in (0 : ℝ)..π, Real.cos (a * θ) * Real.cos (b * θ) =
      π / 2 * ((if a + b = 0 then 1 else 0) + (if a - b = 0 then 1 else 0)) := by
  have h : ∀ θ : ℝ, Real.cos (a * θ) * Real.cos (b * θ) =
      1 / 2 * Real.cos (((a + b : ℤ) : ℝ) * θ) + 1 / 2 * Real.cos (((a - b : ℤ) : ℝ) * θ) := by
    intro θ
    push_cast
    rw [add_mul, sub_mul, Real.cos_add, Real.cos_sub]; ring
  simp_rw [h]
  rw [intervalIntegral.integral_add ((Continuous.intervalIntegrable (by fun_prop)) _ _)
    ((Continuous.intervalIntegrable (by fun_prop)) _ _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_cos_int_mul, integral_cos_int_mul]
  split_ifs <;> ring

/-! ### The weights `g(x)/√(1 − x²)` -/

/-- The weight `g(x)/√(1 − x²)` on `(−1, 1)` for a polynomial `g`. -/
noncomputable def chebWeight (g : ℝ[X]) (x : ℝ) : ℝ := g.eval x * (√(1 - x ^ 2))⁻¹

/-- The substitution `x = cos θ`: `∫₋₁¹ p(x) g(x)/√(1 − x²) dx = ∫₀^π p(cos θ) g(cos θ) dθ`. -/
theorem wInt_chebWeight (g p : ℝ[X]) :
    wInt (Ioo (-1) 1) (chebWeight g) p = ∫ θ in (0 : ℝ)..π, (p * g).eval (Real.cos θ) := by
  rw [show (∫ θ in (0 : ℝ)..π, (p * g).eval (Real.cos θ)) =
      ∫ x, (p * g).eval x ∂measureT from
        (integral_measureT_eq_integral_cos (f := fun x => (p * g).eval x)).symm,
    integral_measureT, wInt, ← integral_Ioc_eq_integral_Ioo, ← integral_of_le (by norm_num)]
  congr 1; ext x
  simp only [chebWeight, eval_mul, Real.sqrt_inv]; ring

theorem isGaussWeight_chebWeight {g : ℝ[X]} (hg : ∀ x ∈ Ioo (-1 : ℝ) 1, 0 < g.eval x) :
    IsGaussWeight (Ioo (-1) 1) (chebWeight g) where
  isOpen := isOpen_Ioo
  ordConnected := ordConnected_Ioo
  nonempty := ⟨0, by norm_num, by norm_num⟩
  pos := fun x hx => by
    have : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    exact mul_pos (hg x hx) (inv_pos.mpr (Real.sqrt_pos.mpr this))
  integrableOn := fun k => by
    have h := intervalIntegrable_sqrt_one_sub_sq_inv.continuousOn_mul
      (g := fun x => x ^ k * g.eval x) (by fun_prop)
    rw [intervalIntegrable_iff, Set.uIoc_of_le (by norm_num)] at h
    refine (h.mono_set Ioo_subset_Ioc_self).congr_fun (fun x _ => ?_) measurableSet_Ioo
    simp only [chebWeight, Real.sqrt_inv]; ring

/-- The weights in DLMF form: on `(−1, 1)`, `g(x)/√(1 − x²) = (1 − x)^α (1 + x)^β` with
`g = 1, 1 − x², 1 − x, 1 + x` for `(α, β) = (−½, −½), (½, ½), (½, −½), (−½, ½)`. -/
theorem chebWeight_eq_rpow {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    chebWeight 1 x = (1 - x) ^ (-(1 / 2) : ℝ) * (1 + x) ^ (-(1 / 2) : ℝ) ∧
    chebWeight (1 - X ^ 2) x = (1 - x) ^ (1 / 2 : ℝ) * (1 + x) ^ (1 / 2 : ℝ) ∧
    chebWeight (1 - X) x = (1 - x) ^ (1 / 2 : ℝ) * (1 + x) ^ (-(1 / 2) : ℝ) ∧
    chebWeight (1 + X) x = (1 - x) ^ (-(1 / 2) : ℝ) * (1 + x) ^ (1 / 2 : ℝ) := by
  have h1 : 0 < 1 - x := by linarith [hx.2]
  have h2 : 0 < 1 + x := by linarith [hx.1]
  have hs : √(1 - x ^ 2) = √(1 - x) * √(1 + x) := by
    rw [← Real.sqrt_mul h1.le]; ring_nf
  have ha := Real.sq_sqrt h1.le
  have hb := Real.sq_sqrt h2.le
  have ha0 := Real.sqrt_pos.mpr h1
  have hb0 := Real.sqrt_pos.mpr h2
  simp only [Real.rpow_neg h1.le, Real.rpow_neg h2.le, ← Real.sqrt_eq_rpow, chebWeight, hs,
    eval_one, eval_sub, eval_add, eval_pow, eval_X]
  refine ⟨by ring, ?_, ?_, ?_⟩
  · rw [show 1 - x ^ 2 = √(1 - x) ^ 2 * √(1 + x) ^ 2 by rw [ha, hb]; ring]; field_simp
  · nth_rewrite 1 [← ha]; field_simp
  · nth_rewrite 1 [← hb]; field_simp

/-! ### Chebyshev polynomial identities -/

theorem cheb_W_identity (n : ℤ) :
    (U ℝ n + U ℝ (n - 1)) * (1 - X) = T ℝ n - T ℝ (n + 1) := by
  have h1 := T_eq_U_sub_X_mul_U ℝ n
  have h2 := T_eq_U_sub_X_mul_U ℝ (n + 1)
  have h3 := U_add_two ℝ (n - 1)
  rw [show n - 1 + 2 = n + 1 by ring, show n - 1 + 1 = n by ring] at h3
  rw [show n + 1 - 1 = n by ring] at h2
  linear_combination h2 - h1 + h3

theorem cheb_V_identity (n : ℤ) :
    (U ℝ n - U ℝ (n - 1)) * (1 + X) = T ℝ n + T ℝ (n + 1) := by
  have h1 := T_eq_U_sub_X_mul_U ℝ n
  have h2 := T_eq_U_sub_X_mul_U ℝ (n + 1)
  have h3 := U_add_two ℝ (n - 1)
  rw [show n - 1 + 2 = n + 1 by ring, show n - 1 + 1 = n by ring] at h3
  rw [show n + 1 - 1 = n by ring] at h2
  linear_combination -h2 - h1 - h3

theorem cheb_U_identity (n : ℤ) : U ℝ n * (1 - X ^ 2) * 2 = T ℝ n - T ℝ (n + 2) := by
  have h1 := T_eq_U_sub_X_mul_U ℝ n
  have h2 := T_eq_U_sub_X_mul_U ℝ (n + 2)
  have h3 := U_add_two ℝ n
  have h4 := U_add_two ℝ (n - 1)
  rw [show n - 1 + 2 = n + 1 by ring, show n - 1 + 1 = n by ring] at h4
  rw [show n + 2 - 1 = n + 1 by ring] at h2
  linear_combination h2 - h1 + h3 + X * h4

/-! ### The monic orthogonal polynomials -/

/-- `2^{1−n} T_n` (monic for `n ≥ 1`). -/
noncomputable def gcT (n : ℕ) : ℝ[X] := C ((2 : ℝ) ^ (n - 1))⁻¹ * T ℝ n
/-- `2^{−n} U_n`. -/
noncomputable def gcU (n : ℕ) : ℝ[X] := C ((2 : ℝ) ^ n)⁻¹ * U ℝ n
/-- `2^{−n} W_n`, `W_n = U_n + U_{n−1}` (fourth kind). -/
noncomputable def gcW (n : ℕ) : ℝ[X] := C ((2 : ℝ) ^ n)⁻¹ * (U ℝ n + U ℝ ((n : ℤ) - 1))
/-- `2^{−n} V_n`, `V_n = U_n − U_{n−1}` (third kind). -/
noncomputable def gcV (n : ℕ) : ℝ[X] := C ((2 : ℝ) ^ n)⁻¹ * (U ℝ n - U ℝ ((n : ℤ) - 1))

theorem degree_U_pred_lt (n : ℕ) : (U ℝ ((n : ℤ) - 1)).degree < (U ℝ n).degree := by
  rw [degree_U_natCast]
  rcases n with _ | m
  · simp
  · rw [show ((m + 1 : ℕ) : ℤ) - 1 = (m : ℕ) by push_cast; ring, degree_U_natCast]
    exact_mod_cast (by omega : m < m + 1)

theorem gcT_monic (n : ℕ) : (gcT n).Monic := by
  rw [Monic, gcT, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_T, Int.natAbs_natCast]
  exact inv_mul_cancel₀ (by positivity)

theorem gcU_monic (n : ℕ) : (gcU n).Monic := by
  rw [Monic, gcU, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_U_natCast]
  exact inv_mul_cancel₀ (by positivity)

theorem gcW_monic (n : ℕ) : (gcW n).Monic := by
  rw [Monic, gcW, leadingCoeff_mul, leadingCoeff_C,
    leadingCoeff_add_of_degree_lt' (degree_U_pred_lt n), leadingCoeff_U_natCast]
  exact inv_mul_cancel₀ (by positivity)

theorem gcV_monic (n : ℕ) : (gcV n).Monic := by
  rw [Monic, gcV, leadingCoeff_mul, leadingCoeff_C, sub_eq_add_neg,
    leadingCoeff_add_of_degree_lt' (by rw [degree_neg]; exact degree_U_pred_lt n),
    leadingCoeff_U_natCast]
  exact inv_mul_cancel₀ (by positivity)

theorem natDegree_gcT (n : ℕ) : (gcT n).natDegree = n := by
  rw [gcT, natDegree_C_mul (by positivity), natDegree_T, Int.natAbs_natCast]

theorem natDegree_gcU (n : ℕ) : (gcU n).natDegree = n := by
  rw [gcU, natDegree_C_mul (by positivity), natDegree_U_natCast]

theorem natDegree_gcW (n : ℕ) : (gcW n).natDegree = n := by
  rw [gcW, natDegree_C_mul (by positivity), natDegree_add_eq_left_of_degree_lt
    (degree_U_pred_lt n), natDegree_U_natCast]

theorem natDegree_gcV (n : ℕ) : (gcV n).natDegree = n := by
  rw [gcV, natDegree_C_mul (by positivity), sub_eq_add_neg, natDegree_add_eq_left_of_degree_lt
    (by rw [degree_neg]; exact degree_U_pred_lt n), natDegree_U_natCast]

/-! ### Orthogonality and `γ_n` -/

theorem integral_cos_mul_cos_nat (a b : ℕ) :
    ∫ θ in (0 : ℝ)..π, Real.cos (a * θ) * Real.cos (b * θ) =
      if a = b then (if a = 0 then π else π / 2) else 0 := by
  have h := integral_cos_mul_cos a b
  push_cast at h
  rw [h]
  split_ifs <;> first | (exfalso; omega) | ring

/-- `∫ (C c * R * T_m) w` for `w = g/√(1 − x²)` and `R g = Q`. -/
theorem wInt_chebWeight_mul_T (g R Q : ℝ[X]) (c : ℝ) (hQ : R * g = Q) (m : ℕ) :
    wInt (Ioo (-1) 1) (chebWeight g) (C c * R * T ℝ m) =
      c * ∫ θ in (0 : ℝ)..π, Q.eval (Real.cos θ) * Real.cos (m * θ) := by
  rw [wInt_chebWeight, show C c * R * T ℝ m * g = C c * (R * g) * T ℝ m by ring, hQ,
    ← intervalIntegral.integral_const_mul]
  congr 1; ext θ
  rw [eval_mul, eval_mul, eval_C, T_real_cos]
  push_cast; ring

theorem integral_T_sub_T_mul_cos (a b m : ℕ) (s : ℝ) :
    ∫ θ in (0 : ℝ)..π, (T ℝ a + C s * T ℝ b).eval (Real.cos θ) * Real.cos (m * θ) =
      (if a = m then (if a = 0 then π else π / 2) else 0) +
        s * (if b = m then (if b = 0 then π else π / 2) else 0) := by
  simp only [eval_add, eval_mul, eval_C, T_real_cos]
  push_cast
  simp_rw [add_mul, mul_assoc]
  rw [intervalIntegral.integral_add ((Continuous.intervalIntegrable (by fun_prop)) _ _)
    ((Continuous.intervalIntegrable (by fun_prop)) _ _), intervalIntegral.integral_const_mul,
    integral_cos_mul_cos_nat, integral_cos_mul_cos_nat]

theorem isOrthMonic_of_cheb {g R Q : ℝ[X]} {c : ℝ} {n : ℕ}
    (hg : ∀ x ∈ Ioo (-1 : ℝ) 1, 0 < g.eval x) (hmon : (C c * R).Monic)
    (hdeg : (C c * R).natDegree = n) (hQ : R * g = Q)
    (horth : ∀ m < n, ∫ θ in (0 : ℝ)..π, Q.eval (Real.cos θ) * Real.cos (m * θ) = 0) :
    IsOrthMonic (Ioo (-1) 1) (chebWeight g) n (C c * R) := by
  have hw := isGaussWeight_chebWeight hg
  refine ⟨hmon, hdeg, fun q hq => ?_⟩
  refine eq_zero_of_T (F := fun q => wInt (Ioo (-1) 1) (chebWeight g) (C c * R * q))
    (fun p q => by rw [mul_add, wInt_add hw])
    (fun a p => by rw [mul_left_comm, wInt_C_mul]) (fun m hm => ?_) hq
  rw [wInt_chebWeight_mul_T g R Q c hQ m, horth m hm, mul_zero]

/-- `γ_n = c κ ∫ p_n T_n w` when `p_n = c R` and `R − κ T_n` has degree `< n`. -/
theorem gaussGamma_of_cheb {g R : ℝ[X]} {c κ : ℝ} {n : ℕ}
    (hp : IsOrthMonic (Ioo (-1) 1) (chebWeight g) n (C c * R))
    (hg : ∀ x ∈ Ioo (-1 : ℝ) 1, 0 < g.eval x) (hdeg : (R - C κ * T ℝ n).degree < n) :
    gaussGamma (Ioo (-1) 1) (chebWeight g) (C c * R) =
      c * κ * wInt (Ioo (-1) 1) (chebWeight g) (C c * R * T ℝ n) := by
  have hw := isGaussWeight_chebWeight hg
  rw [gaussGamma, show C c * R * (C c * R) = C c * (C κ * (C c * R * T ℝ n)) +
      C c * (C c * R * (R - C κ * T ℝ n)) by ring, wInt_add hw, wInt_C_mul, wInt_C_mul,
    wInt_C_mul, hp.wInt_mul_eq_zero hdeg]
  ring

theorem degree_sub_two_mul_T_lt {R : ℝ[X]} {n : ℕ} (hn : 1 ≤ n) (hR : R.natDegree = n)
    (hlc : R.leadingCoeff = 2 ^ n) : (R - C 2 * T ℝ n).degree < (n : WithBot ℕ) := by
  have hT : (C 2 * T ℝ n).natDegree = n := by
    rw [natDegree_C_mul (by norm_num), natDegree_T, Int.natAbs_natCast]
  have hR0 : R ≠ 0 := by
    intro h; rw [h, leadingCoeff_zero] at hlc; exact absurd hlc.symm (by positivity)
  have h := degree_sub_lt_left (p := R) (q := C 2 * T ℝ n)
    (by rw [degree_eq_natDegree hR0, degree_eq_natDegree (by
      intro h; rw [h, natDegree_zero] at hT; omega), hR, hT]) hR0
    (by rw [hlc, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_T, Int.natAbs_natCast,
      ← pow_succ']; congr 1; omega)
  rwa [degree_eq_natDegree hR0, hR] at h

/-- **3.5.22**: `2^{1−n} T_n` is the monic orthogonal polynomial of `w = (1 − x²)^{−1/2}`. -/
theorem isOrthMonic_gcT (n : ℕ) : IsOrthMonic (Ioo (-1) 1) (chebWeight 1) n (gcT n) := by
  refine isOrthMonic_of_cheb (R := T ℝ n) (Q := T ℝ n + C 0 * T ℝ n)
    (fun _ _ => by simp) (gcT_monic n) (natDegree_gcT n) (by simp) fun m hm => ?_
  rw [integral_T_sub_T_mul_cos]
  simp [show n ≠ m by omega]

theorem gcU_eq (n : ℕ) : gcU n = C ((2 : ℝ) ^ n)⁻¹ * C (1 / 2) * (C 2 * U ℝ n) := by
  rw [gcU, mul_assoc, ← mul_assoc (C (1 / 2 : ℝ)), ← Polynomial.C_mul]; norm_num

theorem isOrthMonic_gcU (n : ℕ) :
    IsOrthMonic (Ioo (-1) 1) (chebWeight (1 - X ^ 2)) n (gcU n) := by
  rw [gcU_eq, ← Polynomial.C_mul]
  refine isOrthMonic_of_cheb (R := C 2 * U ℝ n) (Q := T ℝ n + C (-1) * T ℝ (n + 2))
    (fun x hx => by
      simp only [eval_sub, eval_one, eval_pow, eval_X]; nlinarith [hx.1, hx.2])
    (by rw [Polynomial.C_mul, ← gcU_eq]; exact gcU_monic n)
    (by rw [Polynomial.C_mul, ← gcU_eq]; exact natDegree_gcU n) ?_ fun m hm => ?_
  · rw [Polynomial.C_neg, Polynomial.C_1, neg_one_mul, ← sub_eq_add_neg]
    have := cheb_U_identity n
    rw [← this, show (C 2 : ℝ[X]) = 2 by rfl]; ring
  · have := integral_T_sub_T_mul_cos n (n + 2) m (-1)
    push_cast at this
    rw [this]
    simp [show n ≠ m by omega, show n + 2 ≠ m by omega]

theorem isOrthMonic_gcW (n : ℕ) :
    IsOrthMonic (Ioo (-1) 1) (chebWeight (1 - X)) n (gcW n) := by
  refine isOrthMonic_of_cheb (R := U ℝ n + U ℝ ((n : ℤ) - 1)) (Q := T ℝ n + C (-1) * T ℝ (n + 1))
    (fun x hx => by simp only [eval_sub, eval_one, eval_X]; linarith [hx.2]) (gcW_monic n)
    (natDegree_gcW n) ?_ fun m hm => ?_
  · rw [cheb_W_identity, Polynomial.C_neg, Polynomial.C_1, neg_one_mul, ← sub_eq_add_neg]
  · have := integral_T_sub_T_mul_cos n (n + 1) m (-1)
    push_cast at this
    rw [this]
    simp [show n ≠ m by omega, show n + 1 ≠ m by omega]

theorem isOrthMonic_gcV (n : ℕ) :
    IsOrthMonic (Ioo (-1) 1) (chebWeight (1 + X)) n (gcV n) := by
  refine isOrthMonic_of_cheb (R := U ℝ n - U ℝ ((n : ℤ) - 1)) (Q := T ℝ n + C 1 * T ℝ (n + 1))
    (fun x hx => by simp only [eval_add, eval_one, eval_X]; linarith [hx.1]) (gcV_monic n)
    (natDegree_gcV n) ?_ fun m hm => ?_
  · rw [cheb_V_identity, Polynomial.C_1, one_mul]
  · have := integral_T_sub_T_mul_cos n (n + 1) m 1
    push_cast at this
    rw [this]
    simp [show n ≠ m by omega, show n + 1 ≠ m by omega]

theorem integral_T_mul_cos_self {n : ℕ} (hn : 1 ≤ n) (s : ℝ) (b : ℕ) (hb : b ≠ n) :
    ∫ θ in (0 : ℝ)..π, (T ℝ n + C s * T ℝ b).eval (Real.cos θ) * Real.cos (n * θ) = π / 2 := by
  rw [integral_T_sub_T_mul_cos]
  simp [show n ≠ 0 by omega, hb]

theorem leadingCoeff_U_add_U (n : ℕ) : (U ℝ n + U ℝ ((n : ℤ) - 1)).leadingCoeff = 2 ^ n := by
  rw [leadingCoeff_add_of_degree_lt' (degree_U_pred_lt n), leadingCoeff_U_natCast]

theorem leadingCoeff_U_sub_U (n : ℕ) : (U ℝ n - U ℝ ((n : ℤ) - 1)).leadingCoeff = 2 ^ n := by
  rw [sub_eq_add_neg, leadingCoeff_add_of_degree_lt' (by rw [degree_neg]; exact degree_U_pred_lt n),
    leadingCoeff_U_natCast]

/-- **DLMF 3.5.22**: `γ_n = π/2^{2n−1}` for `w = (1 − x²)^{−1/2}`, `n ≥ 1`. -/
theorem dlmf_3_5_22 {n : ℕ} (hn : 1 ≤ n) :
    gaussGamma (Ioo (-1) 1) (chebWeight 1) (gcT n) = π / 2 ^ (2 * n - 1) := by
  rw [gcT, gaussGamma_of_cheb (κ := 1) (isOrthMonic_gcT n) (fun _ _ => by simp)
    (by rw [Polynomial.C_1, one_mul, sub_self, degree_zero]; exact WithBot.bot_lt_coe _),
    wInt_chebWeight_mul_T 1 (T ℝ n) (T ℝ n + C 0 * T ℝ ((n + 1 : ℕ) : ℤ)) _ (by simp),
    integral_T_mul_cos_self hn _ (n + 1) (by omega)]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega, show k + 1 - 1 = k by omega]
  field_simp
  ring

/-- **DLMF 3.5.24**, `γ_n = π/2^{2n+1}` for `w = (1 − x²)^{1/2}` (`α = β = ½`), `n ≥ 1`. -/
theorem dlmf_3_5_24_gamma {n : ℕ} (hn : 1 ≤ n) :
    gaussGamma (Ioo (-1) 1) (chebWeight (1 - X ^ 2)) (gcU n) = π / 2 ^ (2 * n + 1) := by
  have hQ : U ℝ n * (1 - X ^ 2) = C (1 / 2) * (T ℝ n + C (-1) * T ℝ ((n + 2 : ℕ) : ℤ)) := by
    have := cheb_U_identity n
    rw [Polynomial.C_neg, Polynomial.C_1, neg_one_mul, ← sub_eq_add_neg]
    push_cast
    rw [← this, mul_comm (C (1 / 2 : ℝ)), mul_assoc, ← Polynomial.C_ofNat, ← Polynomial.C_mul]
    norm_num
  rw [gcU, gaussGamma_of_cheb (κ := 2) (by rw [← gcU]; exact isOrthMonic_gcU n)
    (fun x hx => by simp only [eval_sub, eval_one, eval_pow, eval_X]; nlinarith [hx.1, hx.2])
    (degree_sub_two_mul_T_lt hn (natDegree_U_natCast ℝ n) (leadingCoeff_U_natCast ℝ n)),
    wInt_chebWeight_mul_T _ (U ℝ n) _ _ hQ]
  simp only [eval_mul, eval_C]
  simp_rw [mul_assoc]
  rw [intervalIntegral.integral_const_mul, integral_T_mul_cos_self hn _ (n + 2) (by omega)]
  field_simp
  ring

/-- **DLMF 3.5.25**, `γ_n = π/2^{2n}` for `w = (1 − x)^{1/2} (1 + x)^{−1/2}` (`α = ½`),
`n ≥ 1`. -/
theorem dlmf_3_5_25_gamma_W {n : ℕ} (hn : 1 ≤ n) :
    gaussGamma (Ioo (-1) 1) (chebWeight (1 - X)) (gcW n) = π / 2 ^ (2 * n) := by
  rw [gcW, gaussGamma_of_cheb (κ := 2) (by rw [← gcW]; exact isOrthMonic_gcW n)
    (fun x hx => by simp only [eval_sub, eval_one, eval_X]; linarith [hx.2])
    (degree_sub_two_mul_T_lt hn (by rw [natDegree_add_eq_left_of_degree_lt (degree_U_pred_lt n),
      natDegree_U_natCast]) (leadingCoeff_U_add_U n)),
    wInt_chebWeight_mul_T _ _ (T ℝ n + C (-1) * T ℝ ((n + 1 : ℕ) : ℤ)) _ (by
      rw [cheb_W_identity, Polynomial.C_neg, Polynomial.C_1, neg_one_mul, ← sub_eq_add_neg]
      push_cast; rfl),
    integral_T_mul_cos_self hn _ (n + 1) (by omega)]
  field_simp
  rw [← pow_mul, mul_comm, pow_mul]

/-- **DLMF 3.5.25**, `γ_n = π/2^{2n}` for `w = (1 − x)^{−1/2} (1 + x)^{1/2}` (`α = −½`),
`n ≥ 1`. -/
theorem dlmf_3_5_25_gamma_V {n : ℕ} (hn : 1 ≤ n) :
    gaussGamma (Ioo (-1) 1) (chebWeight (1 + X)) (gcV n) = π / 2 ^ (2 * n) := by
  rw [gcV, gaussGamma_of_cheb (κ := 2) (by rw [← gcV]; exact isOrthMonic_gcV n)
    (fun x hx => by simp only [eval_add, eval_one, eval_X]; linarith [hx.1])
    (degree_sub_two_mul_T_lt hn (by rw [sub_eq_add_neg, natDegree_add_eq_left_of_degree_lt
      (by rw [degree_neg]; exact degree_U_pred_lt n), natDegree_U_natCast])
      (leadingCoeff_U_sub_U n)),
    wInt_chebWeight_mul_T _ _ (T ℝ n + C 1 * T ℝ ((n + 1 : ℕ) : ℤ)) _ (by
      rw [cheb_V_identity, Polynomial.C_1, one_mul]
      push_cast; rfl),
    integral_T_mul_cos_self hn _ (n + 1) (by omega)]
  field_simp
  rw [← pow_mul, mul_comm, pow_mul]

/-! ### Nodes and weights -/

theorem card_image_cos {n : ℕ} {θ : ℕ → ℝ} (hθ : ∀ i < n, θ i ∈ Icc 0 π)
    (hinj : ∀ i < n, ∀ j < n, θ i = θ j → i = j) :
    #((range n).image fun i => Real.cos (θ i)) = n := by
  rw [card_image_of_injOn, card_range]
  intro i hi j hj h
  simp only [coe_range, Set.mem_Iio] at hi hj
  exact hinj i hi j hj (Real.injOn_cos (hθ i hi) (hθ j hj) h)

theorem sum_image_cos {n : ℕ} {θ : ℕ → ℝ} (hθ : ∀ i < n, θ i ∈ Icc 0 π)
    (hinj : ∀ i < n, ∀ j < n, θ i = θ j → i = j) (f : ℝ → ℝ) :
    ∑ x ∈ (range n).image (fun i => Real.cos (θ i)), f x = ∑ i ∈ range n, f (Real.cos (θ i)) := by
  rw [sum_image]
  intro i hi j hj h
  simp only [coe_range, Set.mem_Iio] at hi hj
  exact hinj i hi j hj (Real.injOn_cos (hθ i (by simpa using hi)) (hθ j (by simpa using hj)) h)

theorem mem_Icc_of_lt_div {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : 0 < b) :
    a / b * π ∈ Icc 0 π :=
  ⟨by positivity, by
    calc a / b * π ≤ 1 * π := mul_le_mul_of_nonneg_right ((div_le_one hb).mpr hab) pi_pos.le
      _ = π := one_mul π⟩

/-- The nodes of the `n`-point Gauss–Chebyshev rule of the first kind, `cos((2k − 1)π/(2n))`,
`k = 1, …, n` (indexed by `i = k − 1`). -/
noncomputable def gcNodesT (n : ℕ) : Finset ℝ :=
  (range n).image fun i : ℕ => Real.cos ((2 * (i : ℝ) + 1) / (2 * n) * π)

/-- **DLMF 3.5.23**: the nodes of the Gauss–Chebyshev rule (`w = (1 − x²)^{−1/2}`) are
`x_k = cos((2k − 1)π/(2n))` and the weights are `w_k = π/n`, `k = 1, …, n`. -/
theorem dlmf_3_5_23 {n : ℕ} (hn : 1 ≤ n) :
    (gcT n).roots.toFinset = gcNodesT n ∧
      ∀ x ∈ gcNodesT n, christoffel (Ioo (-1) 1) (chebWeight 1) (gcT n) x = π / n := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hθ : ∀ i < n, (2 * (i : ℝ) + 1) / (2 * n) * π ∈ Icc 0 π := fun i hi =>
    mem_Icc_of_lt_div (by positivity)
      (by
        have : (i : ℝ) + 1 ≤ n := by exact_mod_cast hi
        linarith) (by positivity)
  have hinj : ∀ i < n, ∀ j < n, (2 * (i : ℝ) + 1) / (2 * n) * π =
      (2 * (j : ℝ) + 1) / (2 * n) * π → i = j := fun i _ j _ h => by
    have : (i : ℝ) = j := by
      have h' := mul_right_cancel₀ pi_ne_zero h
      field_simp at h'
      linarith
    exact_mod_cast this
  unfold gcNodesT
  refine gauss_rule_eq (isGaussWeight_chebWeight (fun _ _ => by simp)) (isOrthMonic_gcT n)
    (card_image_cos hθ hinj) (fun x hx => ?_) (fun q hq => ?_)
  · obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    rw [gcT, eval_mul, eval_C, T_real_cos]
    rw [show ((n : ℤ) : ℝ) * ((2 * i + 1) / (2 * n) * π) = (i : ℝ) * π + π / 2 by
      push_cast; field_simp, Real.cos_add_pi_div_two, Real.sin_nat_mul_pi]
    simp
  · have h2n : (n : WithBot ℕ) < 2 * (n : WithBot ℕ) := by norm_cast; omega
    rw [wInt_chebWeight, mul_one, ← integral_measureT_eq_integral_cos (f := fun x => q.eval x),
      integral_eq_sumZeroes (by omega) (hq.trans h2n),
      sumZeroes, sum_image_cos hθ hinj (fun x => π / n * q.eval x), mul_sum]

/-- The nodes `cos(kπ/(n + 1))`, `k = 1, …, n`, of the second kind (`α = β = ½`). -/
noncomputable def gcNodesU (n : ℕ) : Finset ℝ :=
  (range n).image fun i : ℕ => Real.cos (((i : ℝ) + 1) / (n + 1) * π)

theorem sin_sq_mul_cos (m : ℤ) (x : ℝ) :
    (1 - Real.cos x ^ 2) * Real.cos (m * x) = 1 / 2 * Real.cos (m * x) -
      1 / 4 * Real.cos (((m + 2 : ℤ) : ℝ) * x) - 1 / 4 * Real.cos (((m - 2 : ℤ) : ℝ) * x) := by
  push_cast
  rw [show ((m : ℝ) + 2) * x = m * x + 2 * x by ring,
    show ((m : ℝ) - 2) * x = m * x - 2 * x by ring,
    Real.cos_add, Real.cos_sub, Real.cos_two_mul]
  ring

/-- The trapezoidal sum with `N = n + 1` panels of a function vanishing at both ends. -/
theorem sum_range_eq_half_ccG (n : ℕ) (f : ℕ → ℝ) (h0 : f 0 = 0) (hN : f (n + 1) = 0) :
    ∑ i ∈ range n, f (i + 1) = 1 / 2 * ∑ k ∈ range (n + 1 + 1), ccG (n + 1) k * f k := by
  rw [sum_range_succ, sum_range_succ', hN, h0]
  have : ∀ i ∈ range n, ccG (n + 1) (i + 1) * f (i + 1) = 2 * f (i + 1) := fun i hi => by
    have := mem_range.mp hi
    simp only [ccG, show ¬ (i + 1 = 0 ∨ i + 1 = n + 1) by omega, ↓reduceIte]
  rw [sum_congr rfl this, ← mul_sum]
  ring

/-- **DLMF 3.5.24**: for `w = (1 − x²)^{1/2}` (`α = β = ½`) the nodes are `cos(kπ/(n + 1))` and
the weights `π/(n + 1) sin²(kπ/(n + 1))`, `k = 1, …, n`. -/
theorem dlmf_3_5_24 {n : ℕ} (hn : 1 ≤ n) :
    (gcU n).roots.toFinset = gcNodesU n ∧
      ∀ i < n, christoffel (Ioo (-1) 1) (chebWeight (1 - X ^ 2)) (gcU n)
        (Real.cos ((i + 1) / (n + 1) * π)) =
          π / (n + 1) * Real.sin ((i + 1) / (n + 1) * π) ^ 2 := by
  set N : ℕ := n + 1 with hN
  have hN0 : (0 : ℝ) < N := by positivity
  have hθ : ∀ i < n, ((i : ℝ) + 1) / (n + 1) * π ∈ Icc 0 π := fun i hi =>
    mem_Icc_of_lt_div (by positivity)
      (by
        have : (i : ℝ) + 1 ≤ n := by exact_mod_cast hi
        linarith) (by positivity)
  have hinj : ∀ i < n, ∀ j < n, ((i : ℝ) + 1) / (n + 1) * π =
      ((j : ℝ) + 1) / (n + 1) * π → i = j := fun i _ j _ h => by
    have : (i : ℝ) = j := by
      have h' := mul_right_cancel₀ pi_ne_zero h
      field_simp at h'
      linarith
    exact_mod_cast this
  have hg : ∀ x ∈ Ioo (-1 : ℝ) 1, 0 < (1 - X ^ 2 : ℝ[X]).eval x := fun x hx => by
    simp only [eval_sub, eval_one, eval_pow, eval_X]; nlinarith [hx.1, hx.2]
  have hw := isGaussWeight_chebWeight hg
  have key := gauss_rule_eq hw (isOrthMonic_gcU n) (card_image_cos hθ hinj)
    (c := fun x => π / (n + 1) * (1 - x ^ 2)) (fun x hx => ?_) (fun q hq => ?_)
  · refine ⟨by rw [key.1, gcNodesU], fun i hi => ?_⟩
    rw [key.2 _ (mem_image.mpr ⟨i, mem_range.mpr hi, rfl⟩), Real.sin_sq]
  · -- the zeros
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    have hi' := mem_range.mp hi
    set θ : ℝ := ((i : ℝ) + 1) / (n + 1) * π
    have hsin : Real.sin θ ≠ 0 := by
      have h1 : 0 < θ := by positivity
      have h2 : θ < π := by
        have : ((i : ℝ) + 1) / (n + 1) < 1 := by
          rw [div_lt_one (by positivity)]; exact_mod_cast (by omega : i + 1 < n + 1)
        calc θ < 1 * π := mul_lt_mul_of_pos_right this pi_pos
          _ = π := one_mul π
      exact (Real.sin_pos_of_pos_of_lt_pi h1 h2).ne'
    have hU := U_real_cos θ (n : ℤ)
    rw [show ((n : ℤ) : ℝ) + 1 = n + 1 by push_cast; ring,
      show ((n : ℝ) + 1) * θ = ((i + 1 : ℕ) : ℝ) * π by simp only [θ]; push_cast; field_simp,
      Real.sin_nat_mul_pi] at hU
    rw [gcU, eval_mul, eval_C, (mul_eq_zero.mp hU).resolve_right hsin, mul_zero]
  · -- exactness on polynomials of degree `< n`
    have hNr : (N : ℝ) = n + 1 := by rw [hN]; push_cast; ring
    set Sset := (range n).image fun i : ℕ => Real.cos (((i : ℝ) + 1) / (n + 1) * π)
    suffices h0 : wInt (Ioo (-1) 1) (chebWeight (1 - X ^ 2)) q -
        ∑ x ∈ Sset, π / (n + 1) * (1 - x ^ 2) * q.eval x = 0 by linarith
    refine eq_zero_of_T (F := fun q => wInt (Ioo (-1) 1) (chebWeight (1 - X ^ 2)) q -
        ∑ x ∈ Sset, π / (n + 1) * (1 - x ^ 2) * q.eval x) ?_ ?_ ?_ hq
    · intro p q
      simp only [wInt_add hw, eval_add, mul_add, sum_add_distrib]; ring
    · intro a p
      simp only [wInt_C_mul, eval_mul, eval_C, mul_sub, mul_sum]
      congr 1
      exact sum_congr rfl fun x _ => by ring
    · intro m hm
      -- `I(a) = ∫₀^π cos(aθ)`, `S(a)` the trapezoidal sum
      set I : ℤ → ℝ := fun a => ∫ θ in (0 : ℝ)..π, Real.cos (a * θ)
      set Sa : ℤ → ℝ := fun a => ∑ k ∈ range (N + 1), ccG N k * Real.cos (a * k * π / N)
      have htrap : ∀ a : ℤ, |a| < 2 * N → π / (2 * N) * Sa a = I a := fun a ha =>
        trap_exact (by omega) ha
      have hint : wInt (Ioo (-1) 1) (chebWeight (1 - X ^ 2)) (T ℝ m) =
          1 / 2 * I m - 1 / 4 * I (m + 2) - 1 / 4 * I (m - 2) := by
        rw [wInt_chebWeight]
        have e : ∀ θ : ℝ, (T ℝ m * (1 - X ^ 2)).eval (Real.cos θ) = 1 / 2 * Real.cos ((m : ℤ) * θ) -
            1 / 4 * Real.cos (((m + 2 : ℤ) : ℝ) * θ) -
              1 / 4 * Real.cos (((m - 2 : ℤ) : ℝ) * θ) := by
          intro θ
          rw [← sin_sq_mul_cos, eval_mul, T_real_cos]
          simp only [eval_sub, eval_one, eval_pow, eval_X]; ring
        simp_rw [e]
        rw [intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
            (by apply Continuous.intervalIntegrable; fun_prop),
          intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
            (by apply Continuous.intervalIntegrable; fun_prop),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
      have hsum : ∑ x ∈ Sset, π / (n + 1) * (1 - x ^ 2) * (T ℝ m).eval x =
          π / (2 * N) * (1 / 2 * Sa m - 1 / 4 * Sa (m + 2) - 1 / 4 * Sa (m - 2)) := by
        rw [sum_image_cos hθ hinj]
        set f : ℕ → ℝ := fun k => π / (n + 1) * (1 - Real.cos (k * π / N) ^ 2) *
          Real.cos ((m : ℤ) * (k * π / N))
        have hf : ∀ i ∈ range n, π / (n + 1) * (1 - Real.cos (((i : ℝ) + 1) / (n + 1) * π) ^ 2) *
            (T ℝ m).eval (Real.cos (((i : ℝ) + 1) / (n + 1) * π)) = f (i + 1) := fun i _ => by
          simp only [f, T_real_cos, hNr]; push_cast; ring_nf
        rw [sum_congr rfl hf, sum_range_eq_half_ccG n f (by simp [f])
          (by simp only [f, hNr]; push_cast
              rw [show ((n : ℝ) + 1) * π / (n + 1) = π by field_simp, Real.cos_pi]; ring)]
        simp only [Sa, mul_sum, ← sum_sub_distrib]
        rw [← hN]
        refine sum_congr rfl fun k _ => ?_
        simp only [f]
        rw [mul_assoc (π / ((n : ℝ) + 1)), sin_sq_mul_cos]
        have hc : ∀ a : ℝ, Real.cos (a * (k * π / N)) = Real.cos (a * k * π / N) := fun a => by
          ring_nf
        rw [hc, hc, hc, hNr]
        field_simp
      rw [hint, hsum, ← htrap m (by rw [abs_lt]; constructor <;> omega),
        ← htrap (m + 2) (by rw [abs_lt]; constructor <;> omega),
        ← htrap (m - 2) (by rw [abs_lt]; constructor <;> omega)]
      ring

/-! ### The rules for `α = −β = ±½` (3.5.25) -/

/-- `φ_k = 2kπ/(2n + 1)`, `k = i + 1`. -/
noncomputable def gcPhi (n i : ℕ) : ℝ := 2 * ((i : ℝ) + 1) / (2 * n + 1) * π

theorem gcPhi_mem {n i : ℕ} (hi : i < n) : 0 < gcPhi n i ∧ gcPhi n i < π := by
  unfold gcPhi
  refine ⟨by positivity, ?_⟩
  have : 2 * ((i : ℝ) + 1) / (2 * n + 1) < 1 := by
    rw [div_lt_one (by positivity)]
    have : (i : ℝ) + 1 ≤ n := by exact_mod_cast hi
    linarith
  calc _ < 1 * π := mul_lt_mul_of_pos_right this pi_pos
    _ = π := one_mul π

theorem gcPhi_inj {n : ℕ} : ∀ i < n, ∀ j < n, gcPhi n i = gcPhi n j → i = j := fun i _ j _ h => by
  have : (i : ℝ) = j := by
    have h' := mul_right_cancel₀ pi_ne_zero h
    field_simp at h'
    linarith
  exact_mod_cast this

/-- The nodes `cos(2kπ/(2n + 1))` (`α = ½`). -/
noncomputable def gcNodesW (n : ℕ) : Finset ℝ := (range n).image fun i => Real.cos (gcPhi n i)
/-- The nodes `−cos(2kπ/(2n + 1))` (`α = −½`). -/
noncomputable def gcNodesV (n : ℕ) : Finset ℝ := (range n).image fun i => -Real.cos (gcPhi n i)

theorem one_sub_cos_mul_cos (m : ℤ) (x : ℝ) :
    (1 - Real.cos x) * Real.cos (m * x) = Real.cos (m * x) -
      1 / 2 * Real.cos (((m + 1 : ℤ) : ℝ) * x) - 1 / 2 * Real.cos (((m - 1 : ℤ) : ℝ) * x) := by
  push_cast
  rw [show ((m : ℝ) + 1) * x = m * x + x by ring, show ((m : ℝ) - 1) * x = m * x - x by ring,
    Real.cos_add, Real.cos_sub]
  ring

/-- Half of the sum over the `2n + 1` points of the circle of a function that vanishes at `0` and is
symmetric. -/
theorem sum_range_eq_half_circ (n : ℕ) (f : ℕ → ℝ) (h0 : f 0 = 0)
    (hsym : ∀ j < n, f (n + 1 + j) = f (n - j)) :
    ∑ i ∈ range n, f (i + 1) = 1 / 2 * ∑ k ∈ range (2 * n + 1), f k := by
  rw [sum_range_succ', h0, add_zero, two_mul, sum_range_add]
  have h2 : ∑ j ∈ range n, f (n + j + 1) = ∑ j ∈ range n, f (j + 1) := by
    rw [← sum_range_reflect (fun j => f (j + 1)) n]
    refine sum_congr rfl fun j hj => ?_
    have := mem_range.mp hj
    rw [show n + j + 1 = n + 1 + j by ring, hsym j this]
    congr 1; omega
  rw [h2]; ring

theorem circ_sum_W {n m : ℕ} (hm : m < n) :
    ∑ i ∈ range n, 2 * π / (2 * n + 1) * (1 - Real.cos (gcPhi n i)) *
        Real.cos (m * gcPhi n i) =
      (∫ θ in (0 : ℝ)..π, Real.cos ((m : ℤ) * θ)) -
        1 / 2 * (∫ θ in (0 : ℝ)..π, Real.cos (((m + 1 : ℤ) : ℝ) * θ)) -
        1 / 2 * (∫ θ in (0 : ℝ)..π, Real.cos (((m - 1 : ℤ) : ℝ) * θ)) := by
  set M : ℕ := 2 * n + 1 with hM
  have hMr : (M : ℝ) = 2 * n + 1 := by rw [hM]; push_cast; ring
  have hM0 : 0 < M := by omega
  set f : ℕ → ℝ := fun k => (1 - Real.cos (2 * π * k / M)) * Real.cos (m * (2 * π * k / M))
  have hf : ∀ i ∈ range n, 2 * π / (2 * n + 1) * (1 - Real.cos (gcPhi n i)) *
      Real.cos (m * gcPhi n i) = 2 * π / M * f (i + 1) := fun i _ => by
    simp only [f, gcPhi, hMr]; push_cast; ring_nf
  have hsym : ∀ j < n, f (n + 1 + j) = f (n - j) := fun j hj => by
    simp only [f]
    have e : 2 * π * ((n + 1 + j : ℕ) : ℝ) / M = ((1 : ℕ) : ℝ) * (2 * π) -
        2 * π * ((n - j : ℕ) : ℝ) / M := by
      rw [Nat.cast_sub hj.le, hMr]; push_cast; field_simp; ring
    rw [e, Real.cos_nat_mul_two_pi_sub, mul_sub, show (m : ℝ) * (((1 : ℕ) : ℝ) * (2 * π)) =
      ((m : ℕ) : ℝ) * (2 * π) by push_cast; ring, Real.cos_nat_mul_two_pi_sub]
  rw [sum_congr rfl hf, ← mul_sum, sum_range_eq_half_circ n f (by simp [f]) hsym]
  have hexp : ∀ k ∈ range M, f k = Real.cos (2 * π * ((m : ℤ) : ℝ) * k / M) -
      1 / 2 * Real.cos (2 * π * ((m + 1 : ℤ) : ℝ) * k / M) -
      1 / 2 * Real.cos (2 * π * ((m - 1 : ℤ) : ℝ) * k / M) := fun k _ => by
    simp only [f]
    rw [show (m : ℝ) = ((m : ℤ) : ℝ) by push_cast; rfl, one_sub_cos_mul_cos]
    push_cast; ring_nf
  rw [← hM, sum_congr rfl hexp, sum_sub_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum,
    ← circ_exact hM0 (a := m) (by rw [abs_lt]; constructor <;> omega),
    ← circ_exact hM0 (a := m + 1) (by rw [abs_lt]; constructor <;> omega),
    ← circ_exact hM0 (a := m - 1) (by rw [abs_lt]; constructor <;> omega)]
  have : (M : ℝ) ≠ 0 := by positivity
  field_simp

theorem integral_W_T (m : ℕ) :
    ∫ θ in (0 : ℝ)..π, (T ℝ m * (1 - X)).eval (Real.cos θ) =
      (∫ θ in (0 : ℝ)..π, Real.cos ((m : ℤ) * θ)) -
        1 / 2 * (∫ θ in (0 : ℝ)..π, Real.cos (((m + 1 : ℤ) : ℝ) * θ)) -
        1 / 2 * (∫ θ in (0 : ℝ)..π, Real.cos (((m - 1 : ℤ) : ℝ) * θ)) := by
  have e : ∀ θ : ℝ, (T ℝ m * (1 - X)).eval (Real.cos θ) = Real.cos ((m : ℤ) * θ) -
      1 / 2 * Real.cos (((m + 1 : ℤ) : ℝ) * θ) - 1 / 2 * Real.cos (((m - 1 : ℤ) : ℝ) * θ) := by
    intro θ
    rw [← one_sub_cos_mul_cos, eval_mul, T_real_cos]
    simp only [eval_sub, eval_one, eval_X]; ring
  simp_rw [e]
  rw [intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

theorem integral_V_T (m : ℕ) :
    ∫ θ in (0 : ℝ)..π, (T ℝ m * (1 + X)).eval (Real.cos θ) =
      (-1) ^ m * ∫ θ in (0 : ℝ)..π, (T ℝ m * (1 - X)).eval (Real.cos θ) := by
  have h := intervalIntegral.integral_comp_sub_left
    (fun θ => (T ℝ m * (1 + X)).eval (Real.cos θ)) π (a := 0) (b := π)
  simp only [sub_self, sub_zero] at h
  rw [← intervalIntegral.integral_const_mul, ← h]
  congr 1; ext θ
  simp only [eval_mul, eval_add, eval_sub, eval_one, eval_X]
  rw [T_real_cos, T_real_cos, Real.cos_pi_sub, show ((m : ℤ) : ℝ) * (π - θ) =
    (m : ℕ) * π - m * θ by push_cast; ring, Real.cos_nat_mul_pi_sub]
  push_cast; ring

theorem one_sub_cos_ne_zero {n i : ℕ} (hi : i < n) : 1 - Real.cos (gcPhi n i) ≠ 0 := by
  obtain ⟨h1, h2⟩ := gcPhi_mem hi
  have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl h2.le h1
  rw [Real.cos_zero] at this
  linarith

theorem gc_weight_eq (n i : ℕ) :
    2 * π / (2 * n + 1) * (1 - Real.cos (gcPhi n i)) =
      4 * π / (2 * n + 1) * Real.sin (((i : ℝ) + 1) / (2 * n + 1) * π) ^ 2 := by
  rw [gcPhi, show 2 * ((i : ℝ) + 1) / (2 * n + 1) * π = 2 * (((i : ℝ) + 1) / (2 * n + 1) * π) by
    ring, Real.cos_two_mul, Real.sin_sq]
  ring

/-- **DLMF 3.5.25** (`α = −β = ½`, `w = (1 − x)^{1/2} (1 + x)^{−1/2}`): the nodes are
`x_k = cos(2kπ/(2n + 1))` and the weights `w_k = 4π/(2n + 1) sin²(kπ/(2n + 1))`, `k = 1, …, n`. -/
theorem dlmf_3_5_25_W {n : ℕ} (hn : 1 ≤ n) :
    (gcW n).roots.toFinset = gcNodesW n ∧
      ∀ i < n, christoffel (Ioo (-1) 1) (chebWeight (1 - X)) (gcW n) (Real.cos (gcPhi n i)) =
        4 * π / (2 * n + 1) * Real.sin (((i : ℝ) + 1) / (2 * n + 1) * π) ^ 2 := by
  have hθ : ∀ i < n, gcPhi n i ∈ Icc 0 π := fun i hi => ⟨(gcPhi_mem hi).1.le, (gcPhi_mem hi).2.le⟩
  have hg : ∀ x ∈ Ioo (-1 : ℝ) 1, 0 < (1 - X : ℝ[X]).eval x := fun x hx => by
    simp only [eval_sub, eval_one, eval_X]; linarith [hx.2]
  have hw := isGaussWeight_chebWeight hg
  have key := gauss_rule_eq hw (isOrthMonic_gcW n) (card_image_cos hθ gcPhi_inj)
    (c := fun x => 2 * π / (2 * n + 1) * (1 - x)) (fun x hx => ?_) (fun q hq => ?_)
  · refine ⟨by rw [key.1, gcNodesW], fun i hi => ?_⟩
    rw [key.2 _ (mem_image.mpr ⟨i, mem_range.mpr hi, rfl⟩), gc_weight_eq]
  · obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    have hi' := mem_range.mp hi
    have hid := congrArg (eval (Real.cos (gcPhi n i))) (cheb_W_identity n)
    simp only [eval_mul, eval_sub, eval_add, eval_one, eval_X, T_real_cos] at hid
    have hz : Real.cos (((n : ℤ) : ℝ) * gcPhi n i) =
        Real.cos ((((n : ℤ) + 1 : ℤ) : ℝ) * gcPhi n i) := by
      rw [show (((n : ℤ) + 1 : ℤ) : ℝ) * gcPhi n i = ((i + 1 : ℕ) : ℝ) * (2 * π) -
          ((n : ℤ) : ℝ) * gcPhi n i by
        simp only [gcPhi]; push_cast; field_simp; ring, Real.cos_nat_mul_two_pi_sub]
    rw [hz, sub_self] at hid
    rw [gcW, eval_mul, eval_C, eval_add,
      (mul_eq_zero.mp hid).resolve_right (one_sub_cos_ne_zero hi'), mul_zero]
  · have hS := sum_image_cos hθ gcPhi_inj
    suffices h0 : wInt (Ioo (-1) 1) (chebWeight (1 - X)) q - ∑ x ∈ (range n).image
        (fun i => Real.cos (gcPhi n i)), 2 * π / (2 * n + 1) * (1 - x) * q.eval x = 0 by linarith
    refine eq_zero_of_T (F := fun q => wInt (Ioo (-1) 1) (chebWeight (1 - X)) q -
      ∑ x ∈ (range n).image (fun i => Real.cos (gcPhi n i)),
        2 * π / (2 * n + 1) * (1 - x) * q.eval x) ?_ ?_ ?_ hq
    · intro p q
      simp only [wInt_add hw, eval_add, mul_add, sum_add_distrib]; ring
    · intro a p
      simp only [wInt_C_mul, eval_mul, eval_C, mul_sub, mul_sum]
      congr 1
      exact sum_congr rfl fun x _ => by ring
    · intro m hm
      rw [wInt_chebWeight, integral_W_T, hS, ← circ_sum_W hm, sub_eq_zero]
      exact sum_congr rfl fun i _ => by rw [T_real_cos]; push_cast; ring

/-- **DLMF 3.5.25** (`α = −β = −½`, `w = (1 − x)^{−1/2} (1 + x)^{1/2}`): the nodes are
`x_k = −cos(2kπ/(2n + 1))` and the weights `w_k = 4π/(2n + 1) sin²(kπ/(2n + 1))`. -/
theorem dlmf_3_5_25_V {n : ℕ} (hn : 1 ≤ n) :
    (gcV n).roots.toFinset = gcNodesV n ∧
      ∀ i < n, christoffel (Ioo (-1) 1) (chebWeight (1 + X)) (gcV n) (-Real.cos (gcPhi n i)) =
        4 * π / (2 * n + 1) * Real.sin (((i : ℝ) + 1) / (2 * n + 1) * π) ^ 2 := by
  have hψ : ∀ i < n, π - gcPhi n i ∈ Icc 0 π := fun i hi =>
    ⟨by linarith [(gcPhi_mem hi).2], by linarith [(gcPhi_mem hi).1]⟩
  have hinj : ∀ i < n, ∀ j < n, π - gcPhi n i = π - gcPhi n j → i = j := fun i hi j hj h =>
    gcPhi_inj i hi j hj (by linarith)
  have hV : gcNodesV n = (range n).image fun i => Real.cos (π - gcPhi n i) := by
    simp only [gcNodesV, Real.cos_pi_sub]
  have hg : ∀ x ∈ Ioo (-1 : ℝ) 1, 0 < (1 + X : ℝ[X]).eval x := fun x hx => by
    simp only [eval_add, eval_one, eval_X]; linarith [hx.1]
  have hw := isGaussWeight_chebWeight hg
  have key := gauss_rule_eq hw (isOrthMonic_gcV n) (card_image_cos hψ hinj)
    (c := fun x => 2 * π / (2 * n + 1) * (1 + x)) (fun x hx => ?_) (fun q hq => ?_)
  · refine ⟨by rw [key.1, hV], fun i hi => ?_⟩
    rw [← Real.cos_pi_sub, key.2 _ (mem_image.mpr ⟨i, mem_range.mpr hi, rfl⟩), Real.cos_pi_sub,
      ← gc_weight_eq]
    ring
  · obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    have hi' := mem_range.mp hi
    have hid := congrArg (eval (Real.cos (π - gcPhi n i))) (cheb_V_identity n)
    simp only [eval_mul, eval_sub, eval_add, eval_one, eval_X, T_real_cos] at hid
    have hz : Real.cos ((((n : ℤ) + 1 : ℤ) : ℝ) * (π - gcPhi n i)) =
        -Real.cos (((n : ℤ) : ℝ) * (π - gcPhi n i)) := by
      rw [show (((n : ℤ) + 1 : ℤ) : ℝ) * (π - gcPhi n i) = ((2 * (n - i - 1) + 1 : ℕ) : ℝ) * π -
          ((n : ℤ) : ℝ) * (π - gcPhi n i) by
        have hc : ((n - i - 1 : ℕ) : ℝ) = (n : ℝ) - i - 1 := by
          rw [Nat.sub_sub, Nat.cast_sub (by omega)]; push_cast; ring
        simp only [gcPhi]; push_cast; rw [hc]; field_simp; ring,
        Real.cos_nat_mul_pi_sub, pow_succ, pow_mul]
      norm_num
    rw [hz, add_neg_cancel] at hid
    have hne : 1 + Real.cos (π - gcPhi n i) ≠ 0 := by
      rw [Real.cos_pi_sub, ← sub_eq_add_neg]; exact one_sub_cos_ne_zero hi'
    rw [gcV, eval_mul, eval_C, eval_sub, (mul_eq_zero.mp hid).resolve_right hne, mul_zero]
  · have hS := sum_image_cos hψ hinj
    suffices h0 : wInt (Ioo (-1) 1) (chebWeight (1 + X)) q - ∑ x ∈ (range n).image
        (fun i => Real.cos (π - gcPhi n i)), 2 * π / (2 * n + 1) * (1 + x) * q.eval x = 0 by
      linarith
    refine eq_zero_of_T (F := fun q => wInt (Ioo (-1) 1) (chebWeight (1 + X)) q -
      ∑ x ∈ (range n).image (fun i => Real.cos (π - gcPhi n i)),
        2 * π / (2 * n + 1) * (1 + x) * q.eval x) ?_ ?_ ?_ hq
    · intro p q
      simp only [wInt_add hw, eval_add, mul_add, sum_add_distrib]; ring
    · intro a p
      simp only [wInt_C_mul, eval_mul, eval_C, mul_sub, mul_sum]
      congr 1
      exact sum_congr rfl fun x _ => by ring
    · intro m hm
      rw [wInt_chebWeight, integral_V_T, integral_W_T, hS, ← circ_sum_W hm, mul_sum, sub_eq_zero]
      refine sum_congr rfl fun i _ => ?_
      rw [T_real_cos, Real.cos_pi_sub, show ((m : ℤ) : ℝ) * (π - gcPhi n i) =
        (m : ℕ) * π - m * gcPhi n i by push_cast; ring, Real.cos_nat_mul_pi_sub]
      ring

end Azurite.DLMF
