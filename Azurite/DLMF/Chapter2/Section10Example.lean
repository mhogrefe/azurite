/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section10Tail
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# DLMF §2.10(i): the Example 2.10.3–2.10.5 and the expansion 2.10.8

* 2.10.3 (`exS`): `S(n) = ∑_{j=1}^{n} j ln j`.
* 2.10.4–2.10.5 (`dlmf_2_10_4`): there is a constant `C` such that for every `m ≥ 2` and `n ≥ 1`,
  `S(n) = ½n² ln n − ¼n² + ½n ln n + (1/12) ln n + C
    + ∑_{s=2}^{m−1} (−B_{2s})/(2s(2s−1)(2s−2)) n^{2−2s} + R_m(n)`,
  `R_m(n) = ∫_n^∞ (B̃_{2m}(x) − B_{2m})/(2m(2m−1)x^{2m−1}) dx` (`jlogR`).
* `dlmf_2_10_5_bound`: `R_m(n)` has the sign `(−1)^m`, `R_m(n) − R_{m+1}(n)` is the term `s = m`
  of 2.10.4, and `R_m(n)` is bounded in absolute value by this term and has the same sign.
* 2.10.8 (`dlmf_2_10_8`): `∑_{j=1}^{n−1} 1/j = ln n + γ − 1/(2n) − ∑_{s=1}^{m−1} B_{2s}/(2s n^{2s})
  + R_m(n)` with `0 ≤ (−1)^m R_m(n) ≤ (−1)^m (−B_{2m}/(2m n^{2m}))` (`dlmf_2_10_8_bound`): the
  remainder is bounded in absolute value by the first neglected term and has the same sign.

Not formalized here: 2.10.6 (`C = (γ + ln 2π)/12 − ζ′(2)/(2π²) = 1/12 − ζ′(−1)`, via the
Abel–Plana formula 2.10.2) and 2.10.7 (`∑ j^α`, whose constant `ζ(−α)` needs the analytic
continuation of the Euler–Maclaurin constant).
-/

open Filter Topology Set MeasureTheory intervalIntegral Finset
open scoped Nat

namespace Azurite.DLMF

theorem sum_Icc_int_one (f : ℝ → ℝ) (n : ℕ) :
    ∑ j ∈ Finset.Icc (1 : ℤ) n, f j = ∑ j ∈ Finset.Icc 1 n, f j := by
  rcases n with _ | N
  · simp
  · rw [show ((N + 1 : ℕ) : ℤ) = 1 + N by push_cast; ring,
      sum_Icc_int_eq (fun j : ℤ => f j) 1 N, sum_Icc_one_eq_sum_range_real]
    refine sum_congr rfl fun i _ => ?_
    push_cast
    ring_nf

/-- `x ↦ (−1)^k k!/x^{k+1}` has derivative `(−1)^{k+1}(k+1)!/x^{k+2}`. -/
theorem hasDerivAt_inv_pow_fact (k : ℕ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun x : ℝ => (-1) ^ k * (k ! : ℝ) / x ^ (k + 1))
      ((-1) ^ (k + 1) * ((k + 1)! : ℝ) / x ^ (k + 1 + 1)) x := by
  have h := ((hasDerivAt_pow (k + 1) x).inv (pow_ne_zero _ hx)).const_mul ((-1) ^ k * (k ! : ℝ))
  convert h using 1
  · funext y
    simp [div_eq_mul_inv]
  · rw [Nat.factorial_succ, Nat.add_sub_cancel]
    push_cast
    field_simp
    ring

theorem integrableOn_inv_pow_Ioi {k : ℕ} (hk : 1 ≤ k) (c : ℝ) :
    IntegrableOn (fun x : ℝ => c / x ^ (k + 1)) (Ioi 1) := by
  have hk' : -((k + 1 : ℕ) : ℝ) < -1 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    push_cast
    linarith
  have h := (integrableOn_Ioi_rpow_of_lt hk' one_pos).const_mul c
  refine IntegrableOn.congr_fun h (fun x hx => ?_) measurableSet_Ioi
  have hx : (0 : ℝ) < x := lt_trans one_pos hx
  rw [Real.rpow_neg hx.le, Real.rpow_natCast, div_eq_mul_inv]

/-! ### 2.10.3–2.10.5 -/

/-- The derivatives of `x ln x`. -/
noncomputable def xlogD : ℕ → ℝ → ℝ
  | 0 => fun x => x * Real.log x
  | 1 => fun x => Real.log x + 1
  | k + 2 => fun x => (-1) ^ k * (k ! : ℝ) / x ^ (k + 1)

theorem xlogD_deriv (k : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (xlogD k) (xlogD (k + 1) x) x := by
  match k with
  | 0 => exact Real.hasDerivAt_mul_log hx.ne'
  | 1 =>
    have := (Real.hasDerivAt_log hx.ne').add_const 1
    convert this using 1
    · rfl
    · show (-1) ^ 0 * ((0 : ℕ)! : ℝ) / x ^ (0 + 1) = x⁻¹
      simp
  | k + 2 => exact hasDerivAt_inv_pow_fact k hx.ne'

theorem xlogD_two_mul {m : ℕ} (hm : 1 ≤ m) (x : ℝ) :
    xlogD (2 * m) x = ((2 * m - 2)! : ℝ) / x ^ (2 * m - 1) := by
  obtain ⟨q, rfl⟩ : ∃ q, m = q + 1 := ⟨m - 1, by omega⟩
  rw [show 2 * (q + 1) = 2 * q + 2 by ring, show 2 * q + 2 - 2 = 2 * q by omega,
    show 2 * q + 2 - 1 = 2 * q + 1 by omega]
  simp only [xlogD, pow_mul, neg_one_sq, one_pow, one_mul]

theorem xlogD_integrable {m : ℕ} (hm : 2 ≤ m) : IntegrableOn (xlogD (2 * m)) (Ioi 1) := by
  have h := integrableOn_inv_pow_Ioi (k := 2 * m - 2) (by omega) ((2 * m - 2)! : ℝ)
  refine IntegrableOn.congr_fun h (fun x _ => ?_) measurableSet_Ioi
  rw [xlogD_two_mul (by omega), show 2 * m - 1 = 2 * m - 2 + 1 by omega]

/-- **DLMF 2.10.3**: `S(n) = ∑_{j=1}^{n} j ln j`. -/
noncomputable def exS (n : ℕ) : ℝ := ∑ j ∈ Finset.Icc 1 n, (j : ℝ) * Real.log j

/-- **DLMF 2.10.5**: `R_m(n) = ∫_n^∞ (B̃_{2m}(x) − B_{2m})/(2m(2m−1)x^{2m−1}) dx`. -/
noncomputable def jlogR (m : ℕ) (n : ℝ) : ℝ :=
  ∫ x in Ioi n, (periodicBernoulli (2 * m) x - bernoulli (2 * m)) /
    ((2 * m : ℝ) * (2 * m - 1) * x ^ (2 * m - 1))

/-- The summand of 2.10.4: `(−B_{2s})/(2s(2s−1)(2s−2)) n^{2−2s}`. -/
noncomputable def exTerm (s : ℕ) (n : ℝ) : ℝ :=
  -(bernoulli (2 * s) : ℝ) / ((2 * s : ℝ) * (2 * s - 1) * (2 * s - 2)) / n ^ (2 * s - 2)

theorem emRem_xlog {m : ℕ} (hm : 1 ≤ m) (n : ℝ) : emRem m xlogD n = jlogR m n := by
  rw [emRem, jlogR]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  rw [xlogD_two_mul hm]
  obtain ⟨q, rfl⟩ : ∃ q, m = q + 1 := ⟨m - 1, by omega⟩
  rw [show 2 * (q + 1) - 2 = 2 * q by omega, show 2 * (q + 1) = 2 * q + 1 + 1 by ring,
    Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  have : ((2 * q)! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have h1 : (2 * ((q : ℝ) + 1) - 1) ≠ 0 := by linarith
  have h2 : (2 * (q : ℝ) + 1) ≠ 0 := by linarith
  rcases eq_or_ne x 0 with hx | hx
  · subst hx
    simp
  · field_simp
    ring

theorem xlog_odd_term {s : ℕ} (hs : 2 ≤ s) {n : ℝ} (hn : n ≠ 0) :
    (bernoulli (2 * s) : ℝ) / ((2 * s)! : ℝ) * xlogD (2 * s - 1) n = exTerm s n := by
  obtain ⟨r, rfl⟩ : ∃ r, s = r + 2 := ⟨s - 2, by omega⟩
  have e1 : xlogD (2 * (r + 2) - 1) n = -((2 * r + 1)! : ℝ) / n ^ (2 * r + 2) := by
    rw [show 2 * (r + 2) - 1 = (2 * r + 1) + 2 by omega]
    simp only [xlogD]
    rw [pow_succ, pow_mul, neg_one_sq, one_pow, one_mul, show 2 * r + 1 + 1 = 2 * r + 2 by ring]
    ring
  have hf : ((2 * (r + 2))! : ℝ) =
      (2 * r + 4) * (2 * r + 3) * (2 * r + 2) * ((2 * r + 1)! : ℝ) := by
    rw [show 2 * (r + 2) = 2 * r + 1 + 1 + 1 + 1 by ring]
    simp only [Nat.factorial_succ]
    push_cast
    ring
  rw [e1, exTerm, show 2 * (r + 2) - 2 = 2 * r + 2 by omega, hf]
  have : ((2 * r + 1)! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have h1 : (2 * ((r : ℝ) + 2) - 1) ≠ 0 := by linarith
  have h2 : (2 * ((r : ℝ) + 2) - 2) ≠ 0 := by linarith
  have h3 : (2 * (r : ℝ) + 3) ≠ 0 := by linarith
  have h4 : ((r : ℝ) + 1) ≠ 0 := by linarith
  have h5 : (1 + (r : ℝ)) ≠ 0 := by linarith
  have h6 : (2 * (r : ℝ) + 2) ≠ 0 := by linarith
  have h7 : (2 * (r : ℝ) + 4) ≠ 0 := by linarith
  push_cast
  rw [show (2 * ((r : ℝ) + 2) - 1) = 2 * r + 3 by ring,
    show (2 * ((r : ℝ) + 2) - 2) = 2 * r + 2 by ring, show 2 * ((r : ℝ) + 2) = 2 * r + 4 by ring]
  have hP : n ^ (2 * r + 2) ≠ 0 := pow_ne_zero _ hn
  field_simp

theorem integral_xlog {n : ℝ} (hn : 1 ≤ n) :
    ∫ x in (1 : ℝ)..n, x * Real.log x = n ^ 2 / 2 * Real.log n - n ^ 2 / 4 + 1 / 4 := by
  have hd : ∀ x ∈ uIcc (1 : ℝ) n, HasDerivAt (fun x => x ^ 2 / 2 * Real.log x - x ^ 2 / 4)
      (x * Real.log x) x := by
    intro x hx
    rw [Set.uIcc_of_le hn] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    have h := (((hasDerivAt_pow 2 x).div_const 2).mul (Real.hasDerivAt_log hx0)).sub
      ((hasDerivAt_pow 2 x).div_const 4)
    convert h using 1
    field_simp
    ring
  rw [integral_eq_sub_of_hasDerivAt hd (ContinuousOn.intervalIntegrable (fun x hx =>
    ((Real.hasDerivAt_mul_log (by rw [Set.uIcc_of_le hn] at hx; linarith [hx.1])).continuousAt
      ).continuousWithinAt))]
  simp

/-- `C_m`: the constant produced by Euler–Maclaurin of order `2m` on `[1, n]`. -/
noncomputable def exC (m : ℕ) : ℝ := emConst 1 m xlogD + 1 / 4 + 1 / 12

theorem exS_eq {m : ℕ} (hm : 2 ≤ m) {n : ℕ} (hn : 1 ≤ n) :
    exS n = (n : ℝ) ^ 2 / 2 * Real.log n - (n : ℝ) ^ 2 / 4 + (n : ℝ) / 2 * Real.log n +
      1 / 12 * Real.log n + exC m + ∑ s ∈ Finset.Icc 2 (m - 1), exTerm s n + jlogR m n := by
  have h := em_tail (a := 1) (D := xlogD) (m := m) (by omega)
    (fun k _ x hx => xlogD_deriv k (by push_cast at hx; linarith)) (by
      have := xlogD_integrable hm; push_cast; exact this) (n := n) (by exact_mod_cast hn)
  push_cast at h
  rw [sum_Icc_int_one (xlogD 0) n, show (∫ x in (1 : ℝ)..(n : ℝ), xlogD 0 x) =
    ∫ x in (1 : ℝ)..(n : ℝ), x * Real.log x from rfl, integral_xlog (by exact_mod_cast hn),
    emRem_xlog (by omega)] at h
  have hsplit : ∑ s ∈ Finset.Icc 1 (m - 1), (bernoulli (2 * s) : ℝ) / ((2 * s)! : ℝ) *
      xlogD (2 * s - 1) n = (Real.log n + 1) / 12 + ∑ s ∈ Finset.Icc 2 (m - 1), exTerm s n := by
    rw [← Finset.insert_Icc_add_one_left_eq_Icc (show 1 ≤ m - 1 by omega),
      sum_insert (by simp)]
    congr 1
    · simp [xlogD, bernoulli_two]
      ring
    · have hn0 : (n : ℝ) ≠ 0 := by
        have : (0 : ℝ) < n := by exact_mod_cast hn
        exact this.ne'
      exact sum_congr rfl fun s hs => xlog_odd_term (Finset.mem_Icc.mp hs).1 hn0
  rw [hsplit] at h
  rw [exS, exC, show (∑ j ∈ Finset.Icc 1 n, (j : ℝ) * Real.log j) =
    ∑ j ∈ Finset.Icc 1 n, xlogD 0 (j : ℝ) from rfl, h]
  simp only [xlogD]
  ring

theorem exC_succ {m : ℕ} (hm : 2 ≤ m) : exC m = exC (m + 1) := by
  have hrel : ∀ᶠ n : ℕ in atTop, exC m + jlogR m n = exC (m + 1) + (exTerm m n + jlogR (m + 1) n) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have h1 := exS_eq hm hn
    have h2 := exS_eq (show 2 ≤ m + 1 by omega) hn
    rw [show m + 1 - 1 = m - 1 + 1 by omega, Finset.sum_Icc_succ_top (by omega),
      show m - 1 + 1 = m by omega] at h2
    linarith
  refine const_eq_of_tendsto hrel ?_ ?_
  · have := tendsto_emRem (a := 1) (D := xlogD) (m := m) (xlogD_integrable hm)
    simpa only [emRem_xlog (show 1 ≤ m by omega)] using this
  · have hR := tendsto_emRem (a := 1) (D := xlogD) (m := m + 1)
      (xlogD_integrable (by omega))
    simp only [emRem_xlog (show 1 ≤ m + 1 by omega)] at hR
    have hT : Tendsto (fun n : ℕ => exTerm m n) atTop (𝓝 0) := by
      simp only [exTerm, div_eq_mul_inv]
      have := (tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (by omega : 2 * m - 2 ≠ 0)).comp
        tendsto_natCast_atTop_atTop)).const_mul
        (-(bernoulli (2 * m) : ℝ) * ((2 * m : ℝ) * (2 * m - 1) * (2 * m - 2))⁻¹)
      rw [mul_zero] at this
      exact this
    simpa using hT.add hR

/-- **DLMF 2.10.4–2.10.5**: there is a constant `C` such that for every `m ≥ 2` and `n ≥ 1`,
`S(n) = ½n² ln n − ¼n² + ½n ln n + (1/12) ln n + C + ∑_{s=2}^{m−1} (−B_{2s})/(2s(2s−1)(2s−2))
n^{2−2s} + R_m(n)`. -/
theorem dlmf_2_10_4 : ∃ C : ℝ, ∀ m, 2 ≤ m → ∀ n : ℕ, 1 ≤ n →
    exS n = (n : ℝ) ^ 2 / 2 * Real.log n - (n : ℝ) ^ 2 / 4 + (n : ℝ) / 2 * Real.log n +
      1 / 12 * Real.log n + C + ∑ s ∈ Finset.Icc 2 (m - 1), exTerm s n + jlogR m n := by
  have hC : ∀ m, 2 ≤ m → exC m = exC 2 := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => rfl
    | succ m hm ih => rw [← exC_succ hm, ih]
  exact ⟨exC 2, fun m hm n hn => by rw [← hC m hm]; exact exS_eq hm hn⟩

/-- **DLMF §2.10(i)**, after 2.10.5: `R_m(n)` has the sign `(−1)^m`, `R_m(n) = (s = m term) +
R_{m+1}(n)`, and `R_m(n)` is bounded in absolute value by the term `s = m` and has its sign. -/
theorem dlmf_2_10_5_bound {m : ℕ} (hm : 2 ≤ m) {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ (-1) ^ m * jlogR m n ∧ jlogR m n = exTerm m n + jlogR (m + 1) n ∧
      (-1) ^ m * jlogR m n ≤ (-1) ^ m * exTerm m n ∧ |jlogR m n| ≤ |exTerm m n| := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsign : ∀ m', 1 ≤ m' → 0 ≤ (-1) ^ m' * jlogR m' n := by
    intro m' hm'
    rw [← emRem_xlog hm']
    refine emRem_sign (by omega) fun x hx => ?_
    rw [xlogD_two_mul hm']
    have : 0 < x := lt_trans hn0 hx
    positivity
  have hrel : jlogR m n = exTerm m n + jlogR (m + 1) n := by
    have h1 := exS_eq hm hn
    have h2 := exS_eq (show 2 ≤ m + 1 by omega) hn
    rw [show m + 1 - 1 = m - 1 + 1 by omega, Finset.sum_Icc_succ_top (by omega),
      show m - 1 + 1 = m by omega, ← exC_succ hm] at h2
    linarith
  have hb := remainder_bound hrel (hsign m (by omega)) (hsign (m + 1) (by omega))
  exact ⟨hb.1, hrel, hb.2, (remainder_bound_abs hb).1⟩

/-! ### 2.10.8 -/

/-- The derivatives of `1/x`. -/
noncomputable def invD (k : ℕ) (x : ℝ) : ℝ := (-1) ^ k * (k ! : ℝ) / x ^ (k + 1)

theorem invD_integrable {m : ℕ} (hm : 1 ≤ m) : IntegrableOn (invD (2 * m)) (Ioi 1) := by
  have h := integrableOn_inv_pow_Ioi (k := 2 * m) (by omega) ((-1) ^ (2 * m) * ((2 * m)! : ℝ))
  exact h

/-- `R_m(n)` for 2.10.8. -/
noncomputable def harmR (m : ℕ) (n : ℝ) : ℝ := emRem m invD n

theorem harm_eq_aux {m : ℕ} (hm : 1 ≤ m) {n : ℕ} (hn : 1 ≤ n) :
    ∑ j ∈ Finset.Icc 1 n, (1 / (j : ℝ)) = Real.log n + 1 / (2 * n) + emConst 1 m invD -
      ∑ s ∈ Finset.Icc 1 (m - 1), (bernoulli (2 * s) : ℝ) / (2 * s) / (n : ℝ) ^ (2 * s) +
      harmR m n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h := em_tail (a := 1) (D := invD) (m := m) (by omega)
    (fun k _ x hx => hasDerivAt_inv_pow_fact k (by push_cast at hx; linarith))
    (by have := invD_integrable hm; push_cast; exact this) (n := n) (by exact_mod_cast hn)
  push_cast at h
  rw [sum_Icc_int_one (invD 0) n] at h
  have hint : ∫ x in (1 : ℝ)..n, invD 0 x = Real.log n := by
    simp only [invD, pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul, zero_add, pow_one]
    rw [integral_one_div_of_pos one_pos hn0, div_one]
  have hterm : ∀ s ∈ Finset.Icc 1 (m - 1), (bernoulli (2 * s) : ℝ) / ((2 * s)! : ℝ) *
      invD (2 * s - 1) n = -((bernoulli (2 * s) : ℝ) / (2 * s) / (n : ℝ) ^ (2 * s)) := by
    intro s hs
    obtain ⟨r, rfl⟩ : ∃ r, s = r + 1 := ⟨s - 1, by have := (Finset.mem_Icc.mp hs).1; omega⟩
    rw [show 2 * (r + 1) - 1 = 2 * r + 1 by omega, show 2 * (r + 1) = 2 * r + 1 + 1 by ring,
      invD, Nat.factorial_succ (2 * r + 1)]
    simp only [pow_succ, pow_mul]
    push_cast
    have : ((2 * r + 1)! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp
    ring
  rw [hint, sum_congr rfl hterm, sum_neg_distrib] at h
  have e : ∑ j ∈ Finset.Icc 1 n, invD 0 (j : ℝ) = ∑ j ∈ Finset.Icc 1 n, (1 / (j : ℝ)) :=
    sum_congr rfl fun j _ => by simp [invD]
  rw [e] at h
  rw [h, harmR]
  simp only [invD, pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul, zero_add, pow_one]
  ring

/-- The Euler–Maclaurin constant for `1/x` is Euler's constant `γ`. -/
theorem emConst_inv_eq_gamma {m : ℕ} (hm : 1 ≤ m) :
    emConst 1 m invD = Real.eulerMascheroniConstant := by
  have hlim := Real.tendsto_harmonic_sub_log
  have hR := tendsto_emRem (a := 1) (D := invD) (m := m) (invD_integrable hm)
  have h2n : Tendsto (fun n : ℕ => 1 / (2 * (n : ℝ))) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul (1 / 2 : ℝ)
    rw [mul_zero] at this
    refine this.congr fun n => ?_
    simp only [Function.comp_apply]
    ring
  have hsum : Tendsto (fun n : ℕ => ∑ s ∈ Finset.Icc 1 (m - 1),
      (bernoulli (2 * s) : ℝ) / (2 * s) / (n : ℝ) ^ (2 * s)) atTop (𝓝 0) := by
    rw [show (0 : ℝ) = ∑ s ∈ Finset.Icc 1 (m - 1), 0 by simp]
    refine tendsto_finsetSum _ fun s hs => ?_
    have hs1 : 2 * s ≠ 0 := by have := (Finset.mem_Icc.mp hs).1; omega
    have := (tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop hs1).comp
      tendsto_natCast_atTop_atTop)).const_mul ((bernoulli (2 * s) : ℝ) / (2 * s))
    rw [mul_zero] at this
    refine this.congr fun n => ?_
    simp only [Function.comp_apply, div_eq_mul_inv]
  have hK : Tendsto (fun n : ℕ => (harmonic n : ℝ) - Real.log n) atTop
      (𝓝 (0 + emConst 1 m invD - 0 + 0)) := by
    refine (((h2n.add_const _).sub hsum).add hR).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hh := harm_eq_aux hm hn
    rw [harmonic_eq_sum_Icc]
    push_cast
    simp only [one_div] at hh ⊢
    rw [harmR] at hh
    linarith
  simp only [zero_add, sub_zero, add_zero] at hK
  exact tendsto_nhds_unique hK hlim

/-- **DLMF 2.10.8**: `∑_{j=1}^{n−1} 1/j = ln n + γ − 1/(2n) − ∑_{s=1}^{m−1} B_{2s}/(2s n^{2s})
+ R_m(n)` for `m ≥ 1`, `n ≥ 1`. -/
theorem dlmf_2_10_8 {m : ℕ} (hm : 1 ≤ m) {n : ℕ} (hn : 1 ≤ n) :
    ∑ j ∈ Finset.Icc 1 (n - 1), (1 / (j : ℝ)) = Real.log n + Real.eulerMascheroniConstant -
      1 / (2 * n) - ∑ s ∈ Finset.Icc 1 (m - 1), (bernoulli (2 * s) : ℝ) / (2 * s) /
        (n : ℝ) ^ (2 * s) + harmR m n := by
  have h := harm_eq_aux hm hn
  rw [emConst_inv_eq_gamma hm] at h
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  rw [Finset.sum_Icc_succ_top (by omega)] at h
  rw [Nat.add_sub_cancel]
  push_cast at h ⊢
  have hN : (N : ℝ) + 1 ≠ 0 := by positivity
  have e : (1 : ℝ) / ((N : ℝ) + 1) = 2 * (1 / (2 * ((N : ℝ) + 1))) := by
    field_simp
  linarith

/-- **DLMF §2.10(i)**, after 2.10.8: the remainder of 2.10.8 is bounded in absolute value by the
first neglected term `−B_{2m}/(2m n^{2m})` and has the same sign. -/
theorem dlmf_2_10_8_bound {m : ℕ} (hm : 1 ≤ m) {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ (-1) ^ m * harmR m n ∧
      (-1) ^ m * harmR m n ≤ (-1) ^ m * (-((bernoulli (2 * m) : ℝ) / (2 * m) / (n : ℝ) ^ (2 * m))) ∧
      |harmR m n| ≤ |(bernoulli (2 * m) : ℝ) / (2 * m) / (n : ℝ) ^ (2 * m)| := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsign : ∀ m', 0 ≤ (-1) ^ m' * harmR m' n := by
    intro m'
    rcases Nat.eq_zero_or_pos m' with rfl | hm'
    · simp only [pow_zero, one_mul, harmR, emRem, mul_zero, Nat.factorial_zero, Nat.cast_one,
        div_one]
      refine setIntegral_nonneg measurableSet_Ioi fun x hx => ?_
      have : periodicBernoulli 0 x = 1 := by simp [periodicBernoulli]
      simp [this]
    · refine emRem_sign (by omega) fun x hx => ?_
      have : 0 < x := lt_trans hn0 hx
      simp only [invD, pow_mul, neg_one_sq, one_pow, one_mul]
      positivity
  have hrel : harmR m n = -((bernoulli (2 * m) : ℝ) / (2 * m) / (n : ℝ) ^ (2 * m)) +
      harmR (m + 1) n := by
    have h1 := dlmf_2_10_8 hm hn
    have h2 := dlmf_2_10_8 (show 1 ≤ m + 1 by omega) hn
    rw [show m + 1 - 1 = m - 1 + 1 by omega, Finset.sum_Icc_succ_top (by omega),
      show m - 1 + 1 = m by omega] at h2
    linarith
  have hb := remainder_bound hrel (hsign m) (hsign (m + 1))
  refine ⟨hb.1, hb.2, ?_⟩
  rw [← abs_neg ((bernoulli (2 * m) : ℝ) / (2 * m) / (n : ℝ) ^ (2 * m))]
  exact (remainder_bound_abs hb).1

end Azurite.DLMF
