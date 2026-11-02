/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section9SeriesExp
import Azurite.DLMF.Chapter2.Section9Coincident

/-!
# DLMF §2.9(ii): Coincident Characteristic Values — the case `2g₁ ≠ f₀f₁`, 2.9.9–2.9.10

The roots of 2.9.5 coincide (`f₀² = 4g₀`, `ρ = −f₀/2`) and `2g₁ ≠ f₀f₁`. The formal solutions
are `ρⁿ e^{±κ√n} n^α ∑ (±1)ˢ cₛ/n^{s/2}`, expansions in `t = n^{−1/2}` (`sqrtInv`).

* The residual (`sqrtTrunc_residual`): for `w_N(n) = ρⁿ e^{κ√n} n^α ∑_{s≤N} cₛ/n^{s/2}`
  (`sqrtTrunc`), `w_N(n+2) + f(n) w_N(n+1) + g(n) w_N(n) = ρⁿ e^{κ√n} n^α ∑_{s≤N} cₛ tˢ Bₛ(n)` with
  `Bₛ = ρ² e^{κ(√(n+2)−√n)} (1 + 2t²)^{α−s/2} + ρ f(n) e^{κ(√(n+1)−√n)} (1 + t²)^{α−s/2} + g(n)`
  (`sqBracket`), whose expansion in `t` has coefficients `T(s, j)` (`sqT`, `sqBracket_series`).
* 2.9.10 (`dlmf_2_9_10`): `T(s, 0) = T(s, 1) = 0`, and `T(s, 2) = 0` iff `g₀κ² = 2f₀f₁ − 4g₁`
  (`√g₀ κ = √(2f₀f₁ − 4g₁)`); then `T(0, 3) = 0` iff `4g₀α = g₀ + 2g₁`; and `T(s, 3) = −κg₀s/2`
  (`sqT_three_eq`).
* "Higher coefficients are determined by formal substitution": `c₀ = 1`,
  `(κg₀m/2) c_m = ∑_{s<m} cₛ T(s, m+3−s)` (`sqCoeff`), so that `∑_{s≤d} cₛ T(s, d−s) = 0` for all
  `d` (`sqCoeff_vanish`).
* 2.9.9 (`dlmf_2_9_9`): with these coefficients every truncation satisfies 2.9.1 up to
  `ρⁿ e^{κ√n} n^α O(n^{−(N+4)/2})`; for `κⱼ = (−1)ʲκ` the coefficients are `(−1)^{js} cₛ`
  (`sqCoeff_neg`, `dlmf_2_9_9_pair`).

Not formalized: the existence of the solutions `w_j` (Wong and Li 1992b) and error bounds.
-/

open Filter Topology Asymptotics Finset Complex

namespace Azurite.DLMF

/-! ### The variable `t = n^{−1/2}` -/

/-- `n^{−1/2}`. -/
noncomputable def sqrtInv (n : ℕ) : ℂ := ((Real.sqrt n)⁻¹ : ℝ)

theorem sqrtInv_sq (n : ℕ) : sqrtInv n ^ 2 = (n : ℂ)⁻¹ := by
  rw [sqrtInv, ← ofReal_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg n), ofReal_inv,
    ofReal_natCast]

theorem tendsto_sqrtInv : Tendsto sqrtInv atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have := (continuous_ofReal.tendsto 0).comp h
  rw [ofReal_zero] at this
  exact this

theorem eventually_sqrtInv_ne_zero : ∀ᶠ n : ℕ in atTop, sqrtInv n ≠ 0 := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  exact ofReal_ne_zero.mpr (inv_ne_zero (Real.sqrt_pos.mpr hn0).ne')

/-- The binomial coefficients of `(1 + kX)^β`. -/
noncomputable def binX (k β : ℂ) (j : ℕ) : ℂ := Ring.choose β j * k ^ j

theorem binY_series (k β : ℂ) :
    HasAsympSeries atTop sqrtInv (fun n => (1 + k * sqrtInv n ^ 2) ^ β) (evenSpread (binX k β)) :=
  ((hasAsympSeries_one_add_cpow tendsto_natInv k β).congr_fun
    (Eventually.of_forall fun n => by rw [sqrtInv_sq])).evenSpread_var tendsto_sqrtInv
    fun n => (sqrtInv_sq n).symm

theorem IsAsympSeqDLMF.sqrt_series {f fc : ℕ → ℂ} (hf : IsAsympSeqDLMF f fc) :
    HasAsympSeries atTop sqrtInv f (evenSpread fc) :=
  ((isAsympSeqDLMF_iff f fc).mp hf).evenSpread_var tendsto_sqrtInv fun n => (sqrtInv_sq n).symm

/-! ### `κ(√(n+k) − √n)` -/

/-- The coefficients of `κ((1 + kt²)^{1/2} − 1)/t`. -/
noncomputable def uCoeff (κ k : ℂ) (j : ℕ) : ℂ := κ * evenSpread (binX k (1 / 2)) (j + 1)

/-- `κ((1 + kt²)^{1/2} − 1)/t`, which is `κ(√(n+k) − √n)` (`sqrt_shift_term`). -/
noncomputable def uFun (κ k : ℂ) (n : ℕ) : ℂ :=
  κ * (((1 + k * sqrtInv n ^ 2) ^ (1 / 2 : ℂ) - 1) / sqrtInv n)

theorem uFun_series (κ k : ℂ) : HasAsympSeries atTop sqrtInv (uFun κ k) (uCoeff κ k) := by
  have hc := (binY_series k (1 / 2)).add ((hasAsympSeries_pow tendsto_sqrtInv 0).const_mul (-1))
  have hd := hc.div_var eventually_sqrtInv_ne_zero (by simp [evenSpread, binX])
  refine ((hd.const_mul κ).congr_fun (Eventually.of_forall fun n => ?_)).congr_coeff
    fun j => ?_
  · simp only [uFun, pow_zero]
    ring
  · simp [uCoeff]

theorem uCoeff_vals (κ k : ℂ) : uCoeff κ k 0 = 0 ∧ uCoeff κ k 1 = κ * k / 2 ∧
    uCoeff κ k 2 = 0 ∧ uCoeff κ k 3 = -(κ * k ^ 2 / 8) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [uCoeff, evenSpread, binX, choose_two_eq] <;> ring

theorem uCoeff_neg (κ k : ℂ) : uCoeff (-κ) k = twist (uCoeff κ k) := by
  funext j
  simp only [uCoeff, twist, evenSpread]
  rcases Nat.even_or_odd j with hj | hj
  · simp only [show ¬(j + 1) % 2 = 0 by rcases hj with ⟨r, rfl⟩; omega, ↓reduceIte]
    ring
  · rw [Odd.neg_one_pow hj]
    ring

/-! ### The bracket and its coefficients -/

/-- `ρ² e^{u₂}(1 + 2t²)^{α−s/2} + ρ f(n) e^{u₁}(1 + t²)^{α−s/2} + g(n)`. -/
noncomputable def sqBracket (f g : ℕ → ℂ) (ρ κ α : ℂ) (s n : ℕ) : ℂ :=
  ρ ^ 2 * (Complex.exp (uFun κ 2 n) * (1 + 2 * sqrtInv n ^ 2) ^ (α - s / 2)) +
    ρ * (f n * (Complex.exp (uFun κ 1 n) * (1 + sqrtInv n ^ 2) ^ (α - s / 2))) + g n

/-- The coefficients `T(s, j)` of `sqBracket` in powers of `t = n^{−1/2}`. -/
noncomputable def sqT (fc gc : ℕ → ℂ) (ρ κ α : ℂ) (s : ℕ) (j : ℕ) : ℂ :=
  ρ ^ 2 * seqConv (expCoeff (uCoeff κ 2)) (evenSpread (binX 2 (α - s / 2))) j +
    ρ * seqConv (evenSpread fc)
      (seqConv (expCoeff (uCoeff κ 1)) (evenSpread (binX 1 (α - s / 2)))) j + evenSpread gc j

theorem sqBracket_series {f g fc gc : ℕ → ℂ} (hf : IsAsympSeqDLMF f fc)
    (hg : IsAsympSeqDLMF g gc) (ρ κ α : ℂ) (s : ℕ) :
    HasAsympSeries atTop sqrtInv (sqBracket f g ρ κ α s) (sqT fc gc ρ κ α s) := by
  have E2 := (uFun_series κ 2).cexp tendsto_sqrtInv (uCoeff_vals κ 2).1
  have E1 := (uFun_series κ 1).cexp tendsto_sqrtInv (uCoeff_vals κ 1).1
  have B2 := binY_series 2 (α - s / 2)
  have B1 := binY_series 1 (α - s / 2)
  have h := (((E2.mul tendsto_sqrtInv B2).const_mul (ρ ^ 2)).add
    (((hf.sqrt_series).mul tendsto_sqrtInv (E1.mul tendsto_sqrtInv B1)).const_mul ρ)).add
    hg.sqrt_series
  exact h.congr_fun (Eventually.of_forall fun n => by simp only [sqBracket, one_mul])

theorem evenSpread_low (c : ℕ → ℂ) :
    evenSpread c 0 = c 0 ∧ evenSpread c 1 = 0 ∧ evenSpread c 2 = c 1 ∧ evenSpread c 3 = 0 := by
  simp [evenSpread]

theorem binX_low (k β : ℂ) : binX k β 0 = 1 ∧ binX k β 1 = β * k := by
  simp [binX]

section Values

variable (fc gc : ℕ → ℂ) (ρ κ α : ℂ) (s : ℕ)

theorem sqT_zero : sqT fc gc ρ κ α s 0 = ρ ^ 2 + fc 0 * ρ + gc 0 := by
  simp [sqT, seqConv, (expCoeff_low (uCoeff_vals κ 2).1).1, (expCoeff_low (uCoeff_vals κ 1).1).1,
    evenSpread, binX]
  ring

theorem sqT_one : sqT fc gc ρ κ α s 1 = κ * ρ * (fc 0 + 2 * ρ) / 2 := by
  obtain ⟨u0, u1, u2, u3⟩ := uCoeff_vals κ 2
  obtain ⟨v0, v1, v2, v3⟩ := uCoeff_vals κ 1
  obtain ⟨e0, e1, e2, e3⟩ := expCoeff_low u0
  obtain ⟨f0, f1, f2, f3⟩ := expCoeff_low v0
  simp only [sqT, seqConv, sum_range_succ, sum_range_zero, zero_add,
    Nat.sub_self, Nat.sub_zero, e0, e1, f0, f1, u1, v1, (evenSpread_low _).1,
    (evenSpread_low _).2.1, (binX_low _ _).1]
  ring

variable {fc gc ρ}

theorem sqT_two (hρ : ρ ^ 2 + fc 0 * ρ + gc 0 = 0) (hfr : fc 0 + 2 * ρ = 0) :
    sqT fc gc ρ κ α s 2 = (gc 0 * κ ^ 2 - 2 * fc 0 * fc 1 + 4 * gc 1) / 4 := by
  obtain ⟨u0, u1, u2, u3⟩ := uCoeff_vals κ 2
  obtain ⟨v0, v1, v2, v3⟩ := uCoeff_vals κ 1
  obtain ⟨e0, e1, e2, e3⟩ := expCoeff_low u0
  obtain ⟨f0, f1, f2, f3⟩ := expCoeff_low v0
  simp only [sqT, seqConv, sum_range_succ, sum_range_zero, zero_add, Nat.reduceSub,
    Nat.sub_self, Nat.sub_zero, e0, e1, e2, f0, f1, f2, u1, u2, v1, v2, (evenSpread_low _).1,
    (evenSpread_low _).2.1, (evenSpread_low _).2.2.1, (binX_low _ _).1, (binX_low _ _).2]
  set β : ℂ := α - s / 2
  linear_combination (3 * ρ * κ ^ 2 / 8 + ρ * β + fc 1 / 2) * hfr - (κ ^ 2 / 4) * hρ

theorem sqT_three (hρ : ρ ^ 2 + fc 0 * ρ + gc 0 = 0) (hfr : fc 0 + 2 * ρ = 0) :
    sqT fc gc ρ κ α s 3 =
      κ * (gc 0 * κ ^ 2 / 8 - gc 0 / 4 + gc 0 * (α - s / 2) - fc 0 * fc 1 / 4) := by
  obtain ⟨u0, u1, u2, u3⟩ := uCoeff_vals κ 2
  obtain ⟨v0, v1, v2, v3⟩ := uCoeff_vals κ 1
  obtain ⟨e0, e1, e2, e3⟩ := expCoeff_low u0
  obtain ⟨f0, f1, f2, f3⟩ := expCoeff_low v0
  simp only [sqT, seqConv, sum_range_succ, sum_range_zero, zero_add, Nat.reduceSub,
    Nat.sub_self, Nat.sub_zero, e0, e1, e2, e3, f0, f1, f2, f3, u1, u2, u3, v1, v2, v3,
    (evenSpread_low _).1, (evenSpread_low _).2.1, (evenSpread_low _).2.2.1,
    (evenSpread_low _).2.2.2, (binX_low _ _).1, (binX_low _ _).2]
  set β : ℂ := α - s / 2
  linear_combination (ρ * (-3 * κ / 4 + 7 * κ ^ 3 / 24 + 3 * κ * β) / 2 + κ * fc 1 / 4) * hfr -
    κ * (κ ^ 2 / 8 - 1 / 4 + β) * hρ

end Values

/-! ### 2.9.10 -/

section Relations

variable {fc gc : ℕ → ℂ} {ρ κ α : ℂ}

/-- **DLMF 2.9.10**, as forced by formal substitution: for a double root `ρ` of 2.9.5, the
coefficients of `t⁰` and `t¹` vanish automatically; that of `t²` vanishes iff
`g₀κ² = 2f₀f₁ − 4g₁` (`√g₀ κ = √(2f₀f₁ − 4g₁)`); given this and `κ ≠ 0`, that of `t³` for `s = 0`
vanishes iff `4g₀α = g₀ + 2g₁`. -/
theorem dlmf_2_9_10 (hρ : ρ ^ 2 + fc 0 * ρ + gc 0 = 0) (hdouble : fc 0 ^ 2 = 4 * gc 0)
    (s : ℕ) :
    sqT fc gc ρ κ α s 0 = 0 ∧ sqT fc gc ρ κ α s 1 = 0 ∧
      (sqT fc gc ρ κ α s 2 = 0 ↔ gc 0 * κ ^ 2 = 2 * fc 0 * fc 1 - 4 * gc 1) ∧
      (gc 0 * κ ^ 2 = 2 * fc 0 * fc 1 - 4 * gc 1 → κ ≠ 0 →
        (sqT fc gc ρ κ α 0 3 = 0 ↔ 4 * gc 0 * α = gc 0 + 2 * gc 1)) := by
  have hfr := coinc_fr hρ hdouble
  refine ⟨by rw [sqT_zero, hρ], by rw [sqT_one, hfr, mul_zero, zero_div], ?_, ?_⟩
  · rw [sqT_two κ α s hρ hfr]
    constructor
    · intro h
      linear_combination 4 * h
    · intro h
      linear_combination h / 4
  · intro hκ hκ0
    rw [sqT_three κ α 0 hρ hfr, Nat.cast_zero, zero_div, sub_zero]
    constructor
    · intro h
      have h' : gc 0 * κ ^ 2 / 8 - gc 0 / 4 + gc 0 * α - fc 0 * fc 1 / 4 = 0 :=
        (mul_eq_zero.mp h).resolve_left hκ0
      linear_combination 4 * h' - hκ / 2
    · intro h
      linear_combination (κ / 8) * hκ + (κ / 4) * h

theorem kappa_ne_zero (hκ : gc 0 * κ ^ 2 = 2 * fc 0 * fc 1 - 4 * gc 1)
    (hne : 2 * gc 1 ≠ fc 0 * fc 1) : κ ≠ 0 := by
  rintro rfl
  apply hne
  linear_combination hκ / 2

variable (hρ : ρ ^ 2 + fc 0 * ρ + gc 0 = 0) (hdouble : fc 0 ^ 2 = 4 * gc 0)
  (hκ : gc 0 * κ ^ 2 = 2 * fc 0 * fc 1 - 4 * gc 1) (hα : 4 * gc 0 * α = gc 0 + 2 * gc 1)
include hρ hdouble hκ

theorem sqT_low (s j : ℕ) (hj : j ≤ 2) : sqT fc gc ρ κ α s j = 0 := by
  obtain ⟨h0, h1, h2, -⟩ := dlmf_2_9_10 (κ := κ) (α := α) hρ hdouble s
  interval_cases j
  · exact h0
  · exact h1
  · exact h2.mpr hκ

include hα in
theorem sqT_three_eq (s : ℕ) : sqT fc gc ρ κ α s 3 = -(κ * gc 0 * s / 2) := by
  rw [sqT_three κ α s hρ (coinc_fr hρ hdouble)]
  linear_combination (κ / 8) * hκ + (κ / 4) * hα

end Relations

/-! ### The coefficients `cₛ` -/

/-- `c₀ = 1`, `(κg₀(m+1)/2) c_{m+1} = ∑_{i≤m} cᵢ T(i, m+4−i)`. -/
noncomputable def sqCoeff (fc gc : ℕ → ℂ) (ρ κ α : ℂ) : ℕ → ℂ
  | 0 => 1
  | m + 1 => (∑ i : Fin (m + 1), sqCoeff fc gc ρ κ α i * sqT fc gc ρ κ α i (m + 4 - i)) /
      (κ * gc 0 * ((m + 1 : ℕ) : ℂ) / 2)

theorem sqCoeff_succ (fc gc : ℕ → ℂ) (ρ κ α : ℂ) (hD : κ * gc 0 ≠ 0) (m : ℕ) :
    -(κ * gc 0 * ((m + 1 : ℕ) : ℂ) / 2) * sqCoeff fc gc ρ κ α (m + 1) +
      ∑ i ∈ range (m + 1), sqCoeff fc gc ρ κ α i * sqT fc gc ρ κ α i (m + 4 - i) = 0 := by
  have hm : ((m + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
  have hκ0 : κ ≠ 0 := left_ne_zero_of_mul hD
  have hg0 : gc 0 ≠ 0 := right_ne_zero_of_mul hD
  rw [sqCoeff, ← Finset.sum_range (fun i => sqCoeff fc gc ρ κ α i *
    sqT fc gc ρ κ α i (m + 4 - i))]
  field_simp
  ring

section Vanish

variable {fc gc : ℕ → ℂ} {ρ κ α : ℂ} (hρ : ρ ^ 2 + fc 0 * ρ + gc 0 = 0)
  (hdouble : fc 0 ^ 2 = 4 * gc 0) (hκ : gc 0 * κ ^ 2 = 2 * fc 0 * fc 1 - 4 * gc 1)
  (hα : 4 * gc 0 * α = gc 0 + 2 * gc 1) (hD : κ * gc 0 ≠ 0)
include hρ hdouble hκ hα hD

/-- The coefficient identities `∑_{s≤d} cₛ T(s, d−s) = 0` for every `d`. -/
theorem sqCoeff_vanish (d : ℕ) :
    ∑ s ∈ range (d + 1), sqCoeff fc gc ρ κ α s * sqT fc gc ρ κ α s (d - s) = 0 := by
  rcases Nat.lt_or_ge d 3 with hd | hd
  · exact sum_eq_zero fun s _ => by rw [sqT_low hρ hdouble hκ s (d - s) (by omega), mul_zero]
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 3 := ⟨d - 3, by omega⟩
  rw [← sum_range_add_sum_Ico _ (show m + 1 ≤ m + 3 + 1 by omega),
    sum_eq_zero (s := Ico (m + 1) (m + 3 + 1)) fun s hs => by
      rw [sqT_low hρ hdouble hκ s _ (by have := mem_Ico.mp hs; omega), mul_zero], add_zero,
    sum_range_succ, show m + 3 - m = 3 by omega, sqT_three_eq hρ hdouble hκ hα]
  rcases m with _ | k
  · simp
  · have hs := sqCoeff_succ fc gc ρ κ α hD k
    have e : ∑ s ∈ range (k + 1), sqCoeff fc gc ρ κ α s * sqT fc gc ρ κ α s (k + 1 + 3 - s) =
        ∑ i ∈ range (k + 1), sqCoeff fc gc ρ κ α i * sqT fc gc ρ κ α i (k + 4 - i) := rfl
    rw [e]
    linear_combination hs

end Vanish

/-! ### The residual identity -/

/-- `ρⁿ e^{κ√n} n^α ∑_{s≤N} cₛ/n^{s/2}`. -/
noncomputable def sqrtTrunc (ρ κ α : ℂ) (c : ℕ → ℂ) (N n : ℕ) : ℂ :=
  ρ ^ n * Complex.exp (κ * (Real.sqrt n : ℂ)) * (n : ℂ) ^ α *
    ∑ s ∈ range (N + 1), c s / ((Real.sqrt n : ℝ) : ℂ) ^ s

/-- `e^{κ√(n+k)} (n+k)^α / (n+k)^{s/2}
  = e^{κ√n} n^α e^{κ(√(n+k)−√n)} n^{−s/2} (1 + k/n)^{α−s/2}`. -/
theorem sqrt_shift_term (κ α c : ℂ) {n : ℕ} (hn : 1 ≤ n) (k s : ℕ) :
    Complex.exp (κ * (Real.sqrt ((n + k : ℕ) : ℝ) : ℂ)) * ((n + k : ℕ) : ℂ) ^ α *
        (c / ((Real.sqrt ((n + k : ℕ) : ℝ) : ℝ) : ℂ) ^ s) =
      Complex.exp (κ * (Real.sqrt n : ℂ)) * (n : ℂ) ^ α * (Complex.exp (uFun κ k n) *
        (c * (sqrtInv n ^ s * (1 + (k : ℂ) * sqrtInv n ^ 2) ^ (α - s / 2)))) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hr0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hy0 : (0 : ℝ) < 1 + k / n := by positivity
  have hq0 : 0 < Real.sqrt (1 + k / n) := Real.sqrt_pos.mpr hy0
  have hnk : ((n + k : ℕ) : ℝ) = n * (1 + k / n) := by
    push_cast
    field_simp
  have hsq : Real.sqrt ((n + k : ℕ) : ℝ) = Real.sqrt n * Real.sqrt (1 + k / n) := by
    rw [hnk, Real.sqrt_mul hn0.le]
  have hY2 : (1 + (k : ℂ) * sqrtInv n ^ 2) = (((1 + k / n : ℝ)) : ℂ) := by
    rw [sqrtInv_sq]
    push_cast
    ring
  have hyhalf : (((1 + k / n : ℝ)) : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt (1 + k / n) : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, ofReal_cpow hy0.le]
    norm_num
  have hu : uFun κ k n = κ * (((Real.sqrt n * Real.sqrt (1 + k / n) : ℝ) : ℂ) -
      ((Real.sqrt n : ℝ) : ℂ)) := by
    rw [uFun, hY2, hyhalf, sqrtInv]
    push_cast
    field_simp
  have hpow : ((n + k : ℕ) : ℂ) ^ α = (n : ℂ) ^ α * (((1 + k / n : ℝ)) : ℂ) ^ α := by
    rw [← ofReal_natCast (n + k), hnk, ofReal_mul, mul_cpow_ofReal_nonneg hn0.le hy0.le,
      ofReal_natCast]
  have hyC : (((1 + k / n : ℝ)) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy0.ne'
  have hsub : (((1 + k / n : ℝ)) : ℂ) ^ (α - s / 2) =
      (((1 + k / n : ℝ)) : ℂ) ^ α / ((Real.sqrt (1 + k / n) : ℝ) : ℂ) ^ s := by
    rw [cpow_sub _ _ hyC, show (s : ℂ) / 2 = (s : ℂ) * (1 / 2) by ring, cpow_nat_mul, hyhalf]
  have hexp : Complex.exp (κ * ((Real.sqrt n * Real.sqrt (1 + k / n) : ℝ) : ℂ)) =
      Complex.exp (κ * ((Real.sqrt n : ℝ) : ℂ)) * Complex.exp (κ *
        (((Real.sqrt n * Real.sqrt (1 + k / n) : ℝ) : ℂ) - ((Real.sqrt n : ℝ) : ℂ))) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [hsq, hpow, hu, hY2, hsub, hexp, sqrtInv]
  have hr : ((Real.sqrt n : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr0.ne'
  have hq : ((Real.sqrt (1 + k / n) : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hq0.ne'
  push_cast
  field_simp
  rw [mul_pow, one_div_pow]
  field_simp

section Residual

variable {ρ κ α : ℂ} {c : ℕ → ℂ} {N : ℕ}

theorem sqrtTrunc_eq (n : ℕ) : sqrtTrunc ρ κ α c N n = ρ ^ n *
    Complex.exp (κ * (Real.sqrt n : ℂ)) * (n : ℂ) ^ α *
      ∑ s ∈ range (N + 1), c s * sqrtInv n ^ s := by
  simp only [sqrtTrunc, sqrtInv, div_eq_mul_inv, ofReal_inv, inv_pow]

theorem sqrtTrunc_add {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    sqrtTrunc ρ κ α c N (n + k) = ρ ^ n * Complex.exp (κ * (Real.sqrt n : ℂ)) * (n : ℂ) ^ α *
      (ρ ^ k * ∑ s ∈ range (N + 1), c s * (Complex.exp (uFun κ k n) *
        (sqrtInv n ^ s * (1 + (k : ℂ) * sqrtInv n ^ 2) ^ (α - s / 2)))) := by
  simp only [sqrtTrunc, mul_sum]
  refine sum_congr rfl fun s _ => ?_
  rw [show ρ ^ (n + k) * Complex.exp (κ * (Real.sqrt ((n + k : ℕ) : ℝ) : ℂ)) *
      ((n + k : ℕ) : ℂ) ^ α * (c s / ((Real.sqrt ((n + k : ℕ) : ℝ) : ℝ) : ℂ) ^ s) =
    ρ ^ n * ρ ^ k * (Complex.exp (κ * (Real.sqrt ((n + k : ℕ) : ℝ) : ℂ)) *
      ((n + k : ℕ) : ℂ) ^ α * (c s / ((Real.sqrt ((n + k : ℕ) : ℝ) : ℝ) : ℂ) ^ s)) by ring,
    sqrt_shift_term κ α (c s) hn k s]
  ring

/-- The residual of a truncation. -/
theorem sqrtTrunc_residual (f g : ℕ → ℂ) {n : ℕ} (hn : 1 ≤ n) :
    sqrtTrunc ρ κ α c N (n + 2) + f n * sqrtTrunc ρ κ α c N (n + 1) +
        g n * sqrtTrunc ρ κ α c N n =
      ρ ^ n * Complex.exp (κ * (Real.sqrt n : ℂ)) * (n : ℂ) ^ α *
        ∑ s ∈ range (N + 1), c s * (sqrtInv n ^ s * sqBracket f g ρ κ α s n) := by
  rw [sqrtTrunc_add hn 2, sqrtTrunc_add hn 1, sqrtTrunc_eq n]
  simp only [Nat.cast_ofNat, Nat.cast_one, one_mul, pow_one, mul_sum, sqBracket,
    ← sum_add_distrib]
  refine sum_congr rfl fun s _ => ?_
  ring

end Residual

/-! ### 2.9.9 -/

/-- **DLMF 2.9.9** (formal solutions): for `f`, `g` as in 2.9.3, a double root `ρ` of 2.9.5
(`f₀² = 4g₀`, `g₀ ≠ 0`), `2g₁ ≠ f₀f₁`, `κ`, `α` from 2.9.10 and `cₛ = sqCoeff` (`c₀ = 1`), each
truncation `w_N(n) = ρⁿ e^{κ√n} n^α ∑_{s≤N} cₛ/n^{s/2}` satisfies
`w_N(n+2) + f(n) w_N(n+1) + g(n) w_N(n) = ρⁿ e^{κ√n} n^α B_N(n)` with
`B_N(n) = O(n^{−(N+4)/2})`. -/
theorem dlmf_2_9_9 {f g fc gc : ℕ → ℂ} (hf : IsAsympSeqDLMF f fc) (hg : IsAsympSeqDLMF g gc)
    {ρ κ α : ℂ} (hρ : ρ ^ 2 + fc 0 * ρ + gc 0 = 0) (hdouble : fc 0 ^ 2 = 4 * gc 0)
    (hg0 : gc 0 ≠ 0) (hne : 2 * gc 1 ≠ fc 0 * fc 1)
    (hκ : gc 0 * κ ^ 2 = 2 * fc 0 * fc 1 - 4 * gc 1) (hα : 4 * gc 0 * α = gc 0 + 2 * gc 1)
    (N : ℕ) :
    ∃ B : ℕ → ℂ, IsBigODLMF atTop B (fun n => (((Real.sqrt n : ℝ) : ℂ) ^ (N + 4))⁻¹) ∧
      ∀ n, 1 ≤ n → sqrtTrunc ρ κ α (sqCoeff fc gc ρ κ α) N (n + 2) +
        f n * sqrtTrunc ρ κ α (sqCoeff fc gc ρ κ α) N (n + 1) +
        g n * sqrtTrunc ρ κ α (sqCoeff fc gc ρ κ α) N n =
        ρ ^ n * Complex.exp (κ * (Real.sqrt n : ℂ)) * (n : ℂ) ^ α * B n := by
  have hD : κ * gc 0 ≠ 0 := mul_ne_zero (kappa_ne_zero hκ hne) hg0
  set c := sqCoeff fc gc ρ κ α with hc
  set B : ℕ → ℂ := fun n => ∑ s ∈ range (N + 1), c s * (sqrtInv n ^ s * sqBracket f g ρ κ α s n)
    with hB
  refine ⟨B, ?_, fun n hn => sqrtTrunc_residual f g hn⟩
  have hser : HasAsympSeries atTop sqrtInv B
      (fun d => ∑ s ∈ range (N + 1), c s * if s ≤ d then sqT fc gc ρ κ α s (d - s) else 0) :=
    HasAsympSeries.sum _ fun s _ =>
      (((sqBracket_series hf hg ρ κ α s).pow_mul tendsto_sqrtInv s).const_mul (c s))
  have hzero : ∀ d < N + 4,
      ∑ s ∈ range (N + 1), c s * (if s ≤ d then sqT fc gc ρ κ α s (d - s) else 0) = 0 := by
    intro d hd
    have hv := sqCoeff_vanish hρ hdouble hκ hα hD d
    rcases Nat.lt_or_ge d (N + 1) with hdN | hdN
    · rw [← sum_range_add_sum_Ico _ (show d + 1 ≤ N + 1 by omega)]
      have h1 : ∑ s ∈ range (d + 1), c s * (if s ≤ d then sqT fc gc ρ κ α s (d - s) else 0) =
          0 := by
        rw [← hv]
        refine sum_congr rfl fun s hs => ?_
        simp only [show s ≤ d from Nat.lt_succ_iff.mp (mem_range.mp hs), ↓reduceIte]
        rfl
      have h2 : ∑ s ∈ Ico (d + 1) (N + 1),
          c s * (if s ≤ d then sqT fc gc ρ κ α s (d - s) else 0) = 0 := by
        refine sum_eq_zero fun s hs => ?_
        simp only [show ¬s ≤ d by have := (mem_Ico.mp hs).1; omega, ↓reduceIte, mul_zero]
      rw [h1, h2, add_zero]
    · rw [← sum_range_add_sum_Ico _ (show N + 1 ≤ d + 1 by omega),
        sum_eq_zero (s := Ico (N + 1) (d + 1)) fun s hs => by
          rw [sqT_low hρ hdouble hκ s _ (by have := mem_Ico.mp hs; omega), mul_zero],
        add_zero] at hv
      rw [← hv]
      refine sum_congr rfl fun s hs => ?_
      simp only [show s ≤ d by have := mem_range.mp hs; omega, ↓reduceIte]
      rfl
  have hO : B =O[atTop] fun n => sqrtInv n ^ (N + 4) := by
    refine (hser (N + 4)).congr_left fun n => ?_
    rw [sum_eq_zero fun d hd => by simp only [hzero d (mem_range.mp hd), zero_mul], sub_zero]
  have hne0 : ∀ᶠ n : ℕ in atTop, (((Real.sqrt n : ℝ) : ℂ) ^ (N + 4))⁻¹ ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    exact inv_ne_zero (pow_ne_zero _ (ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hn0).ne'))
  refine (dlmf_2_1_3 hne0).mpr ?_
  refine hO.congr_right fun n => ?_
  rw [sqrtInv, ofReal_inv, inv_pow]

/-! ### The two solutions: `κⱼ = (−1)ʲκ`, coefficients `(−1)^{js} cₛ` -/

theorem sqT_neg (fc gc : ℕ → ℂ) (ρ κ α : ℂ) (s : ℕ) :
    sqT fc gc ρ (-κ) α s = twist (sqT fc gc ρ κ α s) := by
  have e1 : seqConv (expCoeff (uCoeff (-κ) 2)) (evenSpread (binX 2 (α - s / 2))) =
      twist (seqConv (expCoeff (uCoeff κ 2)) (evenSpread (binX 2 (α - s / 2)))) := by
    rw [uCoeff_neg, expCoeff_twist, ← seqConv_twist, twist_evenSpread]
  have e2 : seqConv (evenSpread fc)
      (seqConv (expCoeff (uCoeff (-κ) 1)) (evenSpread (binX 1 (α - s / 2)))) =
      twist (seqConv (evenSpread fc)
        (seqConv (expCoeff (uCoeff κ 1)) (evenSpread (binX 1 (α - s / 2))))) := by
    rw [uCoeff_neg, expCoeff_twist, ← seqConv_twist, ← seqConv_twist]
    simp only [twist_evenSpread]
  funext j
  have e3 := congrFun (twist_evenSpread gc) j
  simp only [sqT, e1, e2]
  simp only [twist, sqT] at e3 ⊢
  linear_combination -e3

theorem sqCoeff_neg (fc gc : ℕ → ℂ) (ρ κ α : ℂ) (m : ℕ) :
    sqCoeff fc gc ρ (-κ) α m = (-1) ^ m * sqCoeff fc gc ρ κ α m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases m with _ | m
    · simp [sqCoeff]
    · have hsum : ∑ i : Fin (m + 1), sqCoeff fc gc ρ (-κ) α i * sqT fc gc ρ (-κ) α i (m + 4 - i) =
          (-1) ^ m * ∑ i : Fin (m + 1), sqCoeff fc gc ρ κ α i * sqT fc gc ρ κ α i (m + 4 - i) := by
        rw [mul_sum]
        refine sum_congr rfl fun i _ => ?_
        rw [ih i (by omega), sqT_neg]
        simp only [twist]
        have hpow : ((-1 : ℂ)) ^ (i : ℕ) * (-1) ^ (m + 4 - i) = (-1) ^ m := by
          rw [← pow_add, show (i : ℕ) + (m + 4 - i) = m + 4 by omega, pow_add]
          norm_num
        linear_combination (sqCoeff fc gc ρ κ α i * sqT fc gc ρ κ α i (m + 4 - i)) * hpow
      rw [sqCoeff, sqCoeff, hsum, pow_succ]
      by_cases hD : κ * gc 0 = 0
      · have : κ * gc 0 * ((m + 1 : ℕ) : ℂ) / 2 = 0 := by rw [hD, zero_mul, zero_div]
        have h' : -κ * gc 0 * ((m + 1 : ℕ) : ℂ) / 2 = 0 := by
          rw [neg_mul, neg_mul, neg_div, this, neg_zero]
        rw [this, h', div_zero, div_zero, mul_zero]
      · have hm : ((m + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
        field_simp

/-- **DLMF 2.9.9**: the two formal solutions `ρⁿ e^{(−1)ʲκ√n} n^α ∑ (−1)^{js} cₛ/n^{s/2}`,
`j = 1, 2`. -/
theorem dlmf_2_9_9_pair {f g fc gc : ℕ → ℂ} (hf : IsAsympSeqDLMF f fc)
    (hg : IsAsympSeqDLMF g gc) {ρ κ α : ℂ} (hρ : ρ ^ 2 + fc 0 * ρ + gc 0 = 0)
    (hdouble : fc 0 ^ 2 = 4 * gc 0) (hg0 : gc 0 ≠ 0) (hne : 2 * gc 1 ≠ fc 0 * fc 1)
    (hκ : gc 0 * κ ^ 2 = 2 * fc 0 * fc 1 - 4 * gc 1) (hα : 4 * gc 0 * α = gc 0 + 2 * gc 1)
    (N : ℕ) (j : ℕ) (hj : j = 1 ∨ j = 2) :
    ∃ B : ℕ → ℂ, IsBigODLMF atTop B (fun n => (((Real.sqrt n : ℝ) : ℂ) ^ (N + 4))⁻¹) ∧
      ∀ n, 1 ≤ n →
        sqrtTrunc ρ ((-1) ^ j * κ) α (fun s => (-1) ^ (j * s) * sqCoeff fc gc ρ κ α s) N
            (n + 2) +
          f n * sqrtTrunc ρ ((-1) ^ j * κ) α
            (fun s => (-1) ^ (j * s) * sqCoeff fc gc ρ κ α s) N (n + 1) +
          g n * sqrtTrunc ρ ((-1) ^ j * κ) α
            (fun s => (-1) ^ (j * s) * sqCoeff fc gc ρ κ α s) N n =
        ρ ^ n * Complex.exp ((-1) ^ j * κ * (Real.sqrt n : ℂ)) * (n : ℂ) ^ α * B n := by
  rcases hj with rfl | rfl
  · have hκ' : gc 0 * (-κ) ^ 2 = 2 * fc 0 * fc 1 - 4 * gc 1 := by rw [neg_sq]; exact hκ
    have e : (fun s => (-1) ^ (1 * s) * sqCoeff fc gc ρ κ α s) = sqCoeff fc gc ρ (-κ) α := by
      funext s
      rw [one_mul, sqCoeff_neg]
    rw [e, pow_one, neg_one_mul]
    exact dlmf_2_9_9 hf hg hρ hdouble hg0 hne hκ' hα N
  · have e : (fun s => (-1) ^ (2 * s) * sqCoeff fc gc ρ κ α s) = sqCoeff fc gc ρ κ α := by
      funext s
      rw [pow_mul, neg_one_sq, one_pow, one_mul]
    rw [e, neg_one_sq, one_mul]
    exact dlmf_2_9_9 hf hg hρ hdouble hg0 hne hκ hα N

end Azurite.DLMF
