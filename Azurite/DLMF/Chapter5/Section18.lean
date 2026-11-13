/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# DLMF §5.18(i): `q`-Factorials

Formalization of <https://dlmf.nist.gov/5.18>, subsection (i).

* 5.18.1: the `q`-Pochhammer symbol `(a; q)ₙ = ∏_{k<n} (1 − aqᵏ)` (`qPochhammer`, definition).
* 5.18.2: the `q`-factorial `n!_q = 1 (1 + q) ⋯ (1 + q + ⋯ + q^{n−1})` (`qFactorial`, DLMF's
  defining product) equals `(q; q)ₙ (1 − q)^{−n}` for `q ≠ 1` (`dlmf_5_18_2`); at `q = 1` it is
  `n!` (`qFactorial_one`).
* 5.18.3: `(a; q)_∞ = ∏_{k≥0} (1 − aqᵏ)` (`qPochhammerInf`). For `|q| < 1` the product converges
  unconditionally, it is the limit of `(a; q)ₙ` (`dlmf_5_18_3`), and it vanishes only when one of
  its factors does (`qPochhammerInf_ne_zero`).
-/

open Complex Filter Topology Finset

namespace Azurite.DLMF

/-- DLMF 5.18.1: the `q`-Pochhammer symbol `(a; q)ₙ = ∏_{k=0}^{n−1} (1 − aqᵏ)`. -/
def qPochhammer (a q : ℂ) (n : ℕ) : ℂ := ∏ k ∈ range n, (1 - a * q ^ k)

/-- DLMF 5.18.2 (defining product): `n!_q = 1 (1 + q) ⋯ (1 + q + ⋯ + q^{n−1})`. -/
def qFactorial (q : ℂ) (n : ℕ) : ℂ := ∏ k ∈ range n, ∑ j ∈ range (k + 1), q ^ j

/-- DLMF 5.18.3: `(a; q)_∞ = ∏_{k≥0} (1 − aqᵏ)`. -/
noncomputable def qPochhammerInf (a q : ℂ) : ℂ := ∏' k : ℕ, (1 - a * q ^ k)

theorem dlmf_5_18_1 (a q : ℂ) (n : ℕ) :
    qPochhammer a q n = ∏ k ∈ range n, (1 - a * q ^ k) := rfl

@[simp] theorem qPochhammer_zero (a q : ℂ) : qPochhammer a q 0 = 1 := by simp [qPochhammer]

theorem qPochhammer_succ (a q : ℂ) (n : ℕ) :
    qPochhammer a q (n + 1) = qPochhammer a q n * (1 - a * q ^ n) := by
  simp [qPochhammer, prod_range_succ]

@[simp] theorem qFactorial_zero (q : ℂ) : qFactorial q 0 = 1 := by simp [qFactorial]

theorem qFactorial_succ (q : ℂ) (n : ℕ) :
    qFactorial q (n + 1) = qFactorial q n * ∑ j ∈ range (n + 1), q ^ j := by
  simp [qFactorial, prod_range_succ]

/-- At `q = 1` the `q`-factorial is the ordinary factorial. -/
theorem qFactorial_one (n : ℕ) : qFactorial 1 n = n.factorial := by
  induction n with
  | zero => simp
  | succ n ih => rw [qFactorial_succ, ih, Nat.factorial_succ]; simp [mul_comm]

/-- DLMF 5.18.2: `n!_q = (q; q)ₙ (1 − q)^{−n}` (for `q ≠ 1`). -/
theorem dlmf_5_18_2 {q : ℂ} (hq : q ≠ 1) (n : ℕ) :
    qFactorial q n = qPochhammer q q n * (1 - q) ^ (-(n : ℤ)) := by
  have h1 : (1 : ℂ) - q ≠ 0 := sub_ne_zero.2 hq.symm
  have hk : ∀ k : ℕ, ∑ j ∈ range (k + 1), q ^ j = (1 - q * q ^ k) / (1 - q) := by
    intro k
    rw [geom_sum_eq hq, eq_div_iff h1, ← pow_succ']
    field_simp [sub_ne_zero.2 hq]
    ring
  simp only [qFactorial, qPochhammer, hk, zpow_neg, zpow_natCast]
  rw [prod_div_distrib, prod_const, card_range, div_eq_mul_inv]

/-- For `|q| < 1`, `∑ ‖aqᵏ‖` converges. -/
theorem summable_norm_mul_pow {a q : ℂ} (hq : ‖q‖ < 1) :
    Summable fun k : ℕ => ‖a * q ^ k‖ := by
  simpa [norm_mul, norm_pow] using
    (summable_geometric_of_lt_one (norm_nonneg q) hq).mul_left ‖a‖

theorem multipliable_qPochhammer {a q : ℂ} (hq : ‖q‖ < 1) :
    Multipliable fun k : ℕ => 1 - a * q ^ k := by
  have hs : Summable fun k : ℕ => -(a * q ^ k) :=
    (summable_norm_mul_pow hq).of_norm.neg
  simpa [sub_eq_add_neg] using Complex.multipliable_one_add_of_summable hs

/-- DLMF 5.18.3: for `|q| < 1` the infinite product `(a; q)_∞` converges (unconditionally) and
is the limit of the finite products `(a; q)ₙ`. -/
theorem dlmf_5_18_3 {a q : ℂ} (hq : ‖q‖ < 1) :
    HasProd (fun k : ℕ => 1 - a * q ^ k) (qPochhammerInf a q) ∧
      Tendsto (fun n => qPochhammer a q n) atTop (𝓝 (qPochhammerInf a q)) := by
  have h := (multipliable_qPochhammer (a := a) hq).hasProd
  exact ⟨h, h.tendsto_prod_nat⟩

/-- For `|q| < 1`, `(a; q)_∞ ≠ 0` as long as no factor `1 − aqᵏ` vanishes. -/
theorem qPochhammerInf_ne_zero {a q : ℂ} (hq : ‖q‖ < 1) (h : ∀ k : ℕ, 1 - a * q ^ k ≠ 0) :
    qPochhammerInf a q ≠ 0 := by
  have hs : Summable fun k : ℕ => -(a * q ^ k) :=
    (summable_norm_mul_pow hq).of_norm.neg
  have hl := Complex.summable_log_one_add_of_summable hs
  have hf : ∀ k : ℕ, 1 + -(a * q ^ k) ≠ 0 := fun k => by simpa [sub_eq_add_neg] using h k
  have he := Complex.cexp_tsum_eq_tprod hf hl
  rw [qPochhammerInf]
  simp only [← sub_eq_add_neg] at he
  rw [← he]
  exact Complex.exp_ne_zero _

/-- The product vanishes if some factor does. -/
theorem qPochhammerInf_eq_zero {a q : ℂ} (hq : ‖q‖ < 1) {k : ℕ} (hk : 1 - a * q ^ k = 0) :
    qPochhammerInf a q = 0 := by
  have h := (dlmf_5_18_3 (a := a) hq).2
  have hz : ∀ n ≥ k + 1, qPochhammer a q n = 0 := fun n hn =>
    prod_eq_zero (mem_range.2 (by omega)) hk
  exact tendsto_nhds_unique h
    (tendsto_const_nhds.congr' (eventually_atTop.2 ⟨k + 1, fun n hn => (hz n hn).symm⟩))

/-- For `|q| < 1`: `(a; q)_∞ = 0` iff `aqᵏ = 1` for some `k`. -/
theorem qPochhammerInf_eq_zero_iff {a q : ℂ} (hq : ‖q‖ < 1) :
    qPochhammerInf a q = 0 ↔ ∃ k : ℕ, 1 - a * q ^ k = 0 := by
  constructor
  · intro h0
    by_contra hne
    push Not at hne
    exact qPochhammerInf_ne_zero hq hne h0
  · rintro ⟨k, hk⟩
    exact qPochhammerInf_eq_zero hq hk

end Azurite.DLMF
