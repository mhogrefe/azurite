/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section18Limit

/-!
# The `q`-gamma function on the real line

For the computation of `Γ_q(x)` (`DLMF.qGamma`, DLMF §5.18) at a real `x` and a real base:

* `qPochR a p = ∏_{k ≥ 0} (1 − a pᵏ)`, the real `q`-Pochhammer symbol `(a; p)_∞`, for
  `0 < p < 1`: `qPochR_split` (the first `K` factors and `(a p^K; p)_∞`) and `qPochR_bounds`
  (`1 − a/(1 − p) ≤ (a; p)_∞ ≤ 1` for `0 ≤ a ≤ 1`);
* `qGammaR p x = (p; p)_∞ (1 − p)^(1−x) / (p^x; p)_∞`, the function of DLMF 5.18.4 for
  `0 < p < 1` at a real `x` (`qGamma_ofReal_eq`), and its product of `K` factors with the two
  tails, `qGammaR_eq_trunc`;
* `qGammaReal q x`, **the function for every base `q > 0`**: `Γ(x)` at `q = 1`, and
  `Γ_q(x) = Γ_{1/q}(x) q^((x−1)(x−2)/2)` for `q > 1` (the usual continuation in the base:
  it keeps `Γ_q(x + 1) = (q^x − 1)/(q − 1) Γ_q(x)`, `Γ_q(1) = 1`);
* `qGammaReal_nat`: `Γ_q(n + 1) = ∏_{k<n} (1 + q + ⋯ + q^k)`, the `q`-factorial, for every
  base `q > 0`, `q ≠ 1`.
-/

open Filter Topology Finset

namespace Azurite.DLMF

/-- `(a; p)_∞ = ∏_{k ≥ 0} (1 − a pᵏ)` for real `a` and `p`. -/
noncomputable def qPochR (a p : ℝ) : ℝ := ∏' k : ℕ, (1 - a * p ^ k)

/-- `Γ_p(x) = (p; p)_∞ (1 − p)^(1−x) / (p^x; p)_∞` for `0 < p < 1` and a real `x`. -/
noncomputable def qGammaR (p x : ℝ) : ℝ := qPochR p p * (1 - p) ^ (1 - x) / qPochR (p ^ x) p

/-- **`Γ_q(x)` for a real `x` and every base `q > 0`**: DLMF 5.18.4 for `q < 1`, `Γ(x)` at
`q = 1`, and `Γ_{1/q}(x) q^((x−1)(x−2)/2)` for `q > 1`. -/
noncomputable def qGammaReal (q x : ℝ) : ℝ :=
  if q < 1 then qGammaR q x else if q = 1 then Real.Gamma x
  else qGammaR q⁻¹ x * q ^ ((x - 1) * (x - 2) / 2)

theorem qGammaReal_of_lt_one {q : ℝ} (hq : q < 1) (x : ℝ) : qGammaReal q x = qGammaR q x := by
  unfold qGammaReal
  rw [ite_eq_left hq]

theorem qGammaReal_of_one_lt {q : ℝ} (hq : 1 < q) (x : ℝ) :
    qGammaReal q x = qGammaR q⁻¹ x * q ^ ((x - 1) * (x - 2) / 2) := by
  unfold qGammaReal
  rw [ite_eq_right (not_lt.mpr hq.le), ite_eq_right hq.ne']

section Base

variable {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
include hp0 hp1

theorem multipliable_qPochR (a : ℝ) : Multipliable fun k : ℕ => 1 - a * p ^ k := by
  have hs : Summable fun k : ℕ => -(a * p ^ k) :=
    ((summable_geometric_of_lt_one hp0.le hp1).mul_left a).neg
  simpa [sub_eq_add_neg] using Real.multipliable_one_add_of_summable hs

/-- `(a; p)_∞ = (a; p)_K (a p^K; p)_∞`. -/
theorem qPochR_split (a : ℝ) (K : ℕ) :
    qPochR a p = (∏ k ∈ range K, (1 - a * p ^ k)) * qPochR (a * p ^ K) p := by
  have hm : Multipliable fun n : ℕ => 1 - a * p ^ (n + K) :=
    (multipliable_qPochR hp0 hp1 (a * p ^ K)).congr fun k => by rw [pow_add]; ring
  unfold qPochR
  rw [← Multipliable.prod_mul_tprod_nat_mul' (f := fun k => 1 - a * p ^ k) (k := K) hm]
  congr 1
  refine tprod_congr fun k => ?_
  rw [pow_add]
  ring

omit hp1 in
/-- `1 − a ∑_{k<n} pᵏ ≤ ∏_{k<n} (1 − a pᵏ) ≤ 1` for `0 ≤ a ≤ 1`, `p ≤ 1`. -/
theorem prod_one_sub_bounds (hp1' : p ≤ 1) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ) :
    0 ≤ ∏ k ∈ range n, (1 - a * p ^ k) ∧ ∏ k ∈ range n, (1 - a * p ^ k) ≤ 1 ∧
      1 - a * ∑ k ∈ range n, p ^ k ≤ ∏ k ∈ range n, (1 - a * p ^ k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    have ht0 : 0 ≤ a * p ^ n := by positivity
    have ht1 : a * p ^ n ≤ 1 := by
      have : p ^ n ≤ 1 := pow_le_one₀ hp0.le hp1'
      nlinarith
    rw [prod_range_succ, sum_range_succ]
    refine ⟨mul_nonneg h0 (by linarith), ?_, ?_⟩
    · nlinarith
    · nlinarith

/-- `1 − a/(1 − p) ≤ (a; p)_∞ ≤ 1` for `0 ≤ a ≤ 1`. -/
theorem qPochR_bounds {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    1 - a / (1 - p) ≤ qPochR a p ∧ qPochR a p ≤ 1 := by
  have ht := (multipliable_qPochR hp0 hp1 a).hasProd.tendsto_prod_nat
  have h1p : 0 < 1 - p := by linarith
  refine ⟨ge_of_tendsto' ht fun n => ?_, le_of_tendsto' ht fun n => ?_⟩
  · obtain ⟨-, -, h⟩ := prod_one_sub_bounds hp0 hp1.le ha0 ha1 n
    have hs : ∑ k ∈ range n, p ^ k ≤ 1 / (1 - p) := by
      rw [le_div_iff₀ h1p]
      have := geom_sum_mul_neg p n
      have hpn : 0 ≤ p ^ n := by positivity
      linarith
    have : a * ∑ k ∈ range n, p ^ k ≤ a / (1 - p) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hs ha0
    linarith
  · exact (prod_one_sub_bounds hp0 hp1.le ha0 ha1 n).2.1

/-- `(a; p)_∞` in the complex numbers, for real `a` and `p`. -/
theorem qPochhammerInf_ofReal (a : ℝ) :
    qPochhammerInf (a : ℂ) (p : ℂ) = ((qPochR a p : ℝ) : ℂ) := by
  have h := ((multipliable_qPochR hp0 hp1 a).hasProd.map Complex.ofRealHom
    Complex.continuous_ofReal)
  have h' : HasProd (fun k : ℕ => ((1 - a * p ^ k : ℝ) : ℂ)) ((qPochR a p : ℝ) : ℂ) := h
  rw [qPochhammerInf, ← h'.tprod_eq]
  refine tprod_congr fun k => ?_
  push_cast
  ring

/-- **`Γ_p` of DLMF 5.18.4 at a real argument is `qGammaR`.** -/
theorem qGamma_ofReal_eq (x : ℝ) : qGamma p (x : ℂ) = ((qGammaR p x : ℝ) : ℂ) := by
  unfold qGamma qGammaR
  rw [qPochhammerInf_ofReal hp0 hp1, ← Complex.ofReal_cpow hp0.le,
    qPochhammerInf_ofReal hp0 hp1,
    show (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (by linarith)]
  push_cast
  ring

/-- `(p; p)_∞ = ∏_{k<K} (1 − p^(k+1)) · (p^(K+1); p)_∞`. -/
theorem qPochR_self_split (K : ℕ) :
    qPochR p p = (∏ k ∈ range K, (1 - p ^ (k + 1))) * qPochR (p ^ (K + 1)) p := by
  rw [qPochR_split hp0 hp1 p K]
  have e1 : ∀ k : ℕ, p * p ^ k = p ^ (k + 1) := fun k => by rw [pow_succ]; ring
  simp only [e1]

/-- `(p^x; p)_∞ = ∏_{k<K} (1 − p^(x+k)) · (p^(x+K); p)_∞`. -/
theorem qPochR_rpow_split (x : ℝ) (K : ℕ) :
    qPochR (p ^ x) p = (∏ k ∈ range K, (1 - p ^ (x + k))) * qPochR (p ^ (x + K)) p := by
  rw [qPochR_split hp0 hp1 (p ^ x) K]
  have e2 : ∀ k : ℕ, p ^ x * p ^ k = p ^ (x + k) := fun k => by
    rw [Real.rpow_add hp0, Real.rpow_natCast]
  simp only [e2]

/-- **The product of `K` factors and the two tails**: `Γ_p(x) = (1 − p)^(1−x)
∏_{k<K} (1 − p^(k+1)) · (p^(K+1); p)_∞ / (∏_{k<K} (1 − p^(x+k)) · (p^(x+K); p)_∞)`. -/
theorem qGammaR_eq_trunc (x : ℝ) (K : ℕ) :
    qGammaR p x = (1 - p) ^ (1 - x) *
      ((∏ k ∈ range K, (1 - p ^ (k + 1))) * qPochR (p ^ (K + 1)) p) /
      ((∏ k ∈ range K, (1 - p ^ (x + k))) * qPochR (p ^ (x + K)) p) := by
  unfold qGammaR
  rw [qPochR_self_split hp0 hp1 K, qPochR_rpow_split hp0 hp1 x K]
  ring

/-- `Γ_p(n + 1)` is the `p`-factorial. -/
theorem qGammaR_nat (n : ℕ) :
    qGammaR p (n + 1) = ∏ k ∈ range n, ∑ j ∈ range (k + 1), p ^ j := by
  have h := dlmf_5_18_6 hp0 hp1 n
  rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
    qGamma_ofReal_eq hp0 hp1] at h
  unfold qFactorial at h
  have h' : ((∏ k ∈ range n, ∑ j ∈ range (k + 1), p ^ j : ℝ) : ℂ)
      = ((qGammaR p (n + 1) : ℝ) : ℂ) := by
    rw [← h]
    push_cast
    rfl
  exact_mod_cast h'.symm

end Base

/-- **`Γ_q(n + 1) = ∏_{k<n} (1 + q + ⋯ + q^k)`** for every base `q > 0`, `q ≠ 1`. -/
theorem qGammaReal_nat {q : ℝ} (hq0 : 0 < q) (hq1 : q ≠ 1) (n : ℕ) :
    qGammaReal q (n + 1) = ∏ k ∈ range n, ∑ j ∈ range (k + 1), q ^ j := by
  rcases lt_or_gt_of_ne hq1 with h | h
  · rw [qGammaReal_of_lt_one h, qGammaR_nat hq0 h]
  · rw [qGammaReal_of_one_lt h, qGammaR_nat (inv_pos.mpr hq0) (inv_lt_one_of_one_lt₀ h)]
    have hexp : (((n : ℝ) + 1 - 1) * ((n : ℝ) + 1 - 2) / 2) = ((∑ k ∈ range n, k : ℕ) : ℝ) := by
      have h2 := Finset.sum_range_id_mul_two n
      have h3 : ((∑ k ∈ range n, k : ℕ) : ℝ) * 2 = (n : ℝ) * ((n : ℝ) - 1) := by
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp
        · have : (((∑ k ∈ range n, k) * 2 : ℕ) : ℝ) = ((n * (n - 1) : ℕ) : ℝ) := by rw [h2]
          rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hn] at this
          simpa using this
      linarith
    rw [hexp, Real.rpow_natCast, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Finset.sum_mul, ← Finset.sum_range_reflect (fun j => q ^ j) (k + 1)]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjk : j ≤ k := by have := Finset.mem_range.mp hj; omega
    rw [show k + 1 - 1 - j = k - j by omega, inv_pow, pow_sub₀ q hq0.ne' hjk]
    ring

end Azurite.DLMF
