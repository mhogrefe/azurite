/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Airy functions: the Maclaurin series, the differential equation, `Ai` and `Bi`

The Airy functions are the two standard solutions of `y″ = xy` (DLMF §9.2–9.4):

  `Ai(x) = c₁ f(x) − c₂ g(x)`,  `Bi(x) = √3 (c₁ f(x) + c₂ g(x))`,

where `f(x) = ∑_k x^(3k)/d_k` with `d_k = ∏_{j<k} (3j+2)(3j+3)` (`1 + x³/3! + 1·4x⁶/6! + ⋯`),
`g(x) = ∑_k x^(3k+1)/e_k` with `e_k = ∏_{j<k} (3j+3)(3j+4)` (`x + 2x⁴/4! + 2·5x⁷/7! + ⋯`), and
`c₁ = Ai(0) = 3^(−2/3)/Γ(2/3)`, `c₂ = −Ai′(0) = 3^(−1/3)/Γ(1/3)`.  This module is the foundation
of the planned `AzFloat` implementation of `Ai`, `Bi`, `Ai′`, `Bi′` (ledger: `docs/azfloat_plan.md`,
section "Airy functions").

What is formalized (all proven):

* The denominators `fDen`, `gDen`: recurrences, `(2k)! ≤ d_k`, `(2k+1)! ≤ e_k`, divisibility.
* The series `f`, `g` (`fTerm`, `gTerm`, `summable_fTerm`, `summable_gTerm`), the term ratios
  `t_{k+1}/t_k = x³/((3k+2)(3k+3))`, `u_{k+1}/u_k = x³/((3k+3)(3k+4))` (`fTerm_succ`,
  `gTerm_succ`), the growth bounds `|f(x)| ≤ cosh(|x|^(3/2))`, `|g(x)| ≤ |x| cosh(|x|^(3/2))`
  (`abs_f_le`, `abs_g_le`, via `d_k ≥ (2k)!`), `f(0) = 1`, `g(0) = 0`, `f ≥ 1`, `g ≥ x` on `x ≥ 0`.
* Truncation: once `|x|³ ≤ (3K+2)(3K+3)/2` the terms halve (`abs_fTerm_add_le`), so
  `|f(x) − ∑_{k<K} t_k| ≤ 2|t_K|` (`abs_f_sub_sum_le`), likewise `g` (`abs_g_sub_sum_le`);
  `K ≥ |x|^(3/2)` suffices (`halving_of_le`).
* Exact rational partial sums at `x = m/q`: `∑_{k<K} t_k = fPartialNum/fPartialDen` with
  `fPartialDen = q^(3K) d_K` (`sum_fTerm_div_eq`), likewise `g` (`sum_gTerm_div_eq`) — what a
  binary-splitting evaluation computes exactly.
* Derivatives: `f′ = fD`, `g′ = gD` termwise (`hasDerivAt_f`, `hasDerivAt_g` via
  `hasDerivAt_tsum_of_isPreconnected` with the bounds `|d/dx t_{k+1}| ≤ R² t_k(R)`), the
  equation term by term `d²/dx² t_{k+1} = x t_k` (`fDDTerm_succ`, `gDDTerm_succ`), hence
  `f″ = xf`, `g″ = xg` (`f_ode`, `g_ode`), and the Wronskian `f g′ − f′ g = 1`
  (`wronskianFG_eq_one`: zero derivative, value at `0`).
* `c₁`, `c₂` positive, `c₁ c₂ = 1/(2√3 π)` (`c₁_mul_c₂`, Euler's reflection `Γ(1/3)Γ(2/3) =
  2π/√3`); `Ai`, `Bi`, `AiD = Ai′`, `BiD = Bi′`, their values at `0`, `Ai″ = x Ai`, `Bi″ = x Bi`
  (`Ai_ode`, `Bi_ode`) and the Wronskian `Ai Bi′ − Ai′ Bi = 1/π` (`wronskian_Ai_Bi`).

Not formalized (next, see the ledger): the Bessel-integral representations and the asymptotic
expansions with remainder bounds for large `|x|`, and the `AzFloat` algorithm itself.
-/

namespace Azurite

namespace Airy

open Finset Filter Topology

/-! ### The denominators -/

/-- `d_k = ∏_{j<k} (3j+2)(3j+3)`, so that `f(x) = ∑_k x^(3k)/d_k`
(`d_k = (3k)!/(1·4·7⋯(3k−2))`). -/
def fDen (k : ℕ) : ℕ := ∏ j ∈ range k, ((3 * j + 2) * (3 * j + 3))

/-- `e_k = ∏_{j<k} (3j+3)(3j+4)`, so that `g(x) = ∑_k x^(3k+1)/e_k`
(`e_k = (3k+1)!/(2·5·8⋯(3k−1))`). -/
def gDen (k : ℕ) : ℕ := ∏ j ∈ range k, ((3 * j + 3) * (3 * j + 4))

@[simp] theorem fDen_zero : fDen 0 = 1 := rfl

@[simp] theorem gDen_zero : gDen 0 = 1 := rfl

theorem fDen_succ (k : ℕ) : fDen (k + 1) = fDen k * ((3 * k + 2) * (3 * k + 3)) :=
  prod_range_succ _ _

theorem gDen_succ (k : ℕ) : gDen (k + 1) = gDen k * ((3 * k + 3) * (3 * k + 4)) :=
  prod_range_succ _ _

theorem fDen_pos (k : ℕ) : 0 < fDen k := prod_pos fun j _ => by positivity

theorem gDen_pos (k : ℕ) : 0 < gDen k := prod_pos fun j _ => by positivity

/-- `(2k)! ≤ d_k`. -/
theorem factorial_two_mul_le_fDen (k : ℕ) : (2 * k).factorial ≤ fDen k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [fDen_succ, show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    calc (2 * k + 1 + 1) * ((2 * k + 1) * (2 * k).factorial)
        = (2 * k).factorial * ((2 * k + 1) * (2 * k + 2)) := by ring
      _ ≤ fDen k * ((3 * k + 2) * (3 * k + 3)) :=
        Nat.mul_le_mul ih (Nat.mul_le_mul (by omega) (by omega))

/-- `(2k+1)! ≤ e_k`. -/
theorem factorial_two_mul_add_one_le_gDen (k : ℕ) : (2 * k + 1).factorial ≤ gDen k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [gDen_succ, show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring, Nat.factorial_succ,
      Nat.factorial_succ]
    calc (2 * k + 1 + 1 + 1) * ((2 * k + 1 + 1) * (2 * k + 1).factorial)
        = (2 * k + 1).factorial * ((2 * k + 2) * (2 * k + 3)) := by ring
      _ ≤ gDen k * ((3 * k + 3) * (3 * k + 4)) :=
        Nat.mul_le_mul ih (Nat.mul_le_mul (by omega) (by omega))

/-- `d_k ∣ d_K` for `k ≤ K`. -/
theorem fDen_dvd {k K : ℕ} (h : k ≤ K) : fDen k ∣ fDen K :=
  prod_dvd_prod_of_subset _ _ _ (range_subset_range.mpr h)

theorem gDen_dvd {k K : ℕ} (h : k ≤ K) : gDen k ∣ gDen K :=
  prod_dvd_prod_of_subset _ _ _ (range_subset_range.mpr h)

/-! ### The series `f` and `g` -/

/-- The `k`-th term of `f`: `x^(3k)/d_k`. -/
noncomputable def fTerm (x : ℝ) (k : ℕ) : ℝ := x ^ (3 * k) / fDen k

/-- The `k`-th term of `g`: `x^(3k+1)/e_k`. -/
noncomputable def gTerm (x : ℝ) (k : ℕ) : ℝ := x ^ (3 * k + 1) / gDen k

/-- `f(x) = ∑_k x^(3k)/d_k = 1 + x³/3! + 1·4 x⁶/6! + ⋯` (DLMF 9.4.1, the even-type solution of
`y″ = xy` with `f(0) = 1`, `f′(0) = 0`). -/
noncomputable def f (x : ℝ) : ℝ := ∑' k : ℕ, fTerm x k

/-- `g(x) = ∑_k x^(3k+1)/e_k = x + 2x⁴/4! + 2·5 x⁷/7! + ⋯` (the solution with `g(0) = 0`,
`g′(0) = 1`). -/
noncomputable def g (x : ℝ) : ℝ := ∑' k : ℕ, gTerm x k

variable {x : ℝ}

theorem fTerm_zero (x : ℝ) : fTerm x 0 = 1 := by simp [fTerm]

theorem gTerm_zero (x : ℝ) : gTerm x 0 = x := by simp [gTerm]

/-- The term ratio `t_{k+1}/t_k = x³/((3k+2)(3k+3))`. -/
theorem fTerm_succ (x : ℝ) (k : ℕ) :
    fTerm x (k + 1) = fTerm x k * (x ^ 3 / ((3 * k + 2) * (3 * k + 3))) := by
  unfold fTerm
  rw [fDen_succ, show 3 * (k + 1) = 3 * k + 3 by ring, pow_add]
  push_cast
  field_simp

/-- The term ratio `t_{k+1}/t_k = x³/((3k+3)(3k+4))`. -/
theorem gTerm_succ (x : ℝ) (k : ℕ) :
    gTerm x (k + 1) = gTerm x k * (x ^ 3 / ((3 * k + 3) * (3 * k + 4))) := by
  unfold gTerm
  rw [gDen_succ, show 3 * (k + 1) + 1 = 3 * k + 1 + 3 by ring, pow_add]
  push_cast
  field_simp

/-- `|x|^(3k) = (√|x|³)^(2k)`. -/
theorem abs_pow_three_mul (x : ℝ) (k : ℕ) : |x| ^ (3 * k) = (Real.sqrt |x| ^ 3) ^ (2 * k) := by
  rw [← pow_mul, show 3 * (2 * k) = 2 * (3 * k) by ring, pow_mul (Real.sqrt |x|) 2,
    Real.sq_sqrt (abs_nonneg x)]

/-- `|t_k(x)| ≤ (√|x|³)^(2k)/(2k)!`, a term of the `cosh` series. -/
theorem abs_fTerm_le (x : ℝ) (k : ℕ) :
    |fTerm x k| ≤ (Real.sqrt |x| ^ 3) ^ (2 * k) / (2 * k).factorial := by
  rw [fTerm, abs_div, abs_pow, Nat.abs_cast, abs_pow_three_mul]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (by exact_mod_cast factorial_two_mul_le_fDen k)

/-- `|u_k(x)| ≤ |x| (√|x|³)^(2k)/(2k)!`. -/
theorem abs_gTerm_le (x : ℝ) (k : ℕ) :
    |gTerm x k| ≤ |x| * ((Real.sqrt |x| ^ 3) ^ (2 * k) / (2 * k).factorial) := by
  rw [gTerm, abs_div, abs_pow, Nat.abs_cast, pow_succ, mul_comm (|x| ^ (3 * k)), mul_div_assoc,
    abs_pow_three_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg x)
  refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
  calc ((2 * k).factorial : ℝ) ≤ (2 * k + 1).factorial := by
        exact_mod_cast Nat.factorial_le (by omega)
    _ ≤ gDen k := by exact_mod_cast factorial_two_mul_add_one_le_gDen k

theorem summable_cosh_term (y : ℝ) : Summable fun k : ℕ => y ^ (2 * k) / ((2 * k).factorial : ℝ) :=
  (Real.hasSum_cosh y).summable

theorem summable_fTerm (x : ℝ) : Summable (fTerm x) :=
  (summable_cosh_term _).of_norm_bounded fun k => by
    rw [Real.norm_eq_abs]; exact abs_fTerm_le x k

theorem summable_gTerm (x : ℝ) : Summable (gTerm x) :=
  ((summable_cosh_term _).mul_left |x|).of_norm_bounded fun k => by
    rw [Real.norm_eq_abs]; exact abs_gTerm_le x k

/-- `|f(x)| ≤ cosh(|x|^(3/2))`. -/
theorem abs_f_le (x : ℝ) : |f x| ≤ Real.cosh (Real.sqrt |x| ^ 3) := by
  rw [← (Real.hasSum_cosh _).tsum_eq]
  exact (norm_tsum_le_tsum_norm ((summable_fTerm x).norm)).trans
    ((summable_fTerm x).norm.tsum_le_tsum (fun k => by
      rw [Real.norm_eq_abs]; exact abs_fTerm_le x k) (summable_cosh_term _))

/-- `|g(x)| ≤ |x| cosh(|x|^(3/2))`. -/
theorem abs_g_le (x : ℝ) : |g x| ≤ |x| * Real.cosh (Real.sqrt |x| ^ 3) := by
  rw [← (Real.hasSum_cosh _).tsum_eq, ← tsum_mul_left]
  exact (norm_tsum_le_tsum_norm ((summable_gTerm x).norm)).trans
    ((summable_gTerm x).norm.tsum_le_tsum (fun k => by
      rw [Real.norm_eq_abs]; exact abs_gTerm_le x k) ((summable_cosh_term _).mul_left _))

/-- For `x ≥ 0` all terms are nonnegative, so `f(x) ≥ 1` and `g(x) ≥ x`. -/
theorem fTerm_nonneg (hx : 0 ≤ x) (k : ℕ) : 0 ≤ fTerm x k := by unfold fTerm; positivity

theorem gTerm_nonneg (hx : 0 ≤ x) (k : ℕ) : 0 ≤ gTerm x k := by unfold gTerm; positivity

theorem one_le_f (hx : 0 ≤ x) : 1 ≤ f x :=
  calc (1 : ℝ) = fTerm x 0 := (fTerm_zero x).symm
    _ ≤ f x := (summable_fTerm x).le_tsum 0 fun k _ => fTerm_nonneg hx k

theorem le_g (hx : 0 ≤ x) : x ≤ g x :=
  calc x = gTerm x 0 := (gTerm_zero x).symm
    _ ≤ g x := (summable_gTerm x).le_tsum 0 fun k _ => gTerm_nonneg hx k

@[simp] theorem f_zero : f 0 = 1 := by
  rw [f, tsum_eq_single 0 fun k hk => ?_, fTerm_zero]
  simp [fTerm, hk]

@[simp] theorem g_zero : g 0 = 0 := by
  rw [g, tsum_eq_single 0 fun k hk => ?_, gTerm_zero]
  simp [gTerm]

/-! ### Truncation -/

/-- Once `|x|³ ≤ (3K+2)(3K+3)/2`, the terms of `f` from `K` on halve at least:
`|t_{K+i}| ≤ |t_K|/2^i`. -/
theorem abs_fTerm_add_le {K : ℕ} (hK : |x| ^ 3 ≤ (3 * K + 2) * (3 * K + 3) / 2) (i : ℕ) :
    |fTerm x (K + i)| ≤ |fTerm x K| / 2 ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [← add_assoc, fTerm_succ, abs_mul, abs_div, abs_pow,
      show |fTerm x K| / 2 ^ (i + 1) = |fTerm x K| / 2 ^ i * (1 / 2) by rw [pow_succ]; ring]
    refine mul_le_mul ih ?_ (by positivity) (by positivity)
    rw [abs_of_pos (by positivity : (0 : ℝ) < (3 * (K + i : ℕ) + 2) * (3 * (K + i : ℕ) + 3)),
      div_le_div_iff₀ (by positivity) (by norm_num)]
    have hKi : (K : ℝ) ≤ ((K + i : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right K i
    have h1 : (3 * (K : ℝ) + 2) * (3 * (K : ℝ) + 3)
        ≤ (3 * ((K + i : ℕ) : ℝ) + 2) * (3 * ((K + i : ℕ) : ℝ) + 3) := by
      nlinarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
    linarith

/-- Once `|x|³ ≤ (3K+3)(3K+4)/2`, the terms of `g` from `K` on halve at least. -/
theorem abs_gTerm_add_le {K : ℕ} (hK : |x| ^ 3 ≤ (3 * K + 3) * (3 * K + 4) / 2) (i : ℕ) :
    |gTerm x (K + i)| ≤ |gTerm x K| / 2 ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [← add_assoc, gTerm_succ, abs_mul, abs_div, abs_pow,
      show |gTerm x K| / 2 ^ (i + 1) = |gTerm x K| / 2 ^ i * (1 / 2) by rw [pow_succ]; ring]
    refine mul_le_mul ih ?_ (by positivity) (by positivity)
    rw [abs_of_pos (by positivity : (0 : ℝ) < (3 * (K + i : ℕ) + 3) * (3 * (K + i : ℕ) + 4)),
      div_le_div_iff₀ (by positivity) (by norm_num)]
    have hKi : (K : ℝ) ≤ ((K + i : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right K i
    have h1 : (3 * (K : ℝ) + 3) * (3 * (K : ℝ) + 4)
        ≤ (3 * ((K + i : ℕ) : ℝ) + 3) * (3 * ((K + i : ℕ) : ℝ) + 4) := by
      nlinarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
    linarith

/-- A geometric tail: if `|a (K + i)| ≤ |a K|/2^i` for all `i` and `a` is summable, then
`|∑_{k≥K} a k| ≤ 2 |a K|`. -/
theorem abs_tsum_add_le_two_mul {a : ℕ → ℝ} (ha : Summable a) (K : ℕ)
    (h : ∀ i, |a (K + i)| ≤ |a K| / 2 ^ i) : |∑' i : ℕ, a (i + K)| ≤ 2 * |a K| := by
  have hs : Summable fun i => a (i + K) := (summable_nat_add_iff K).mpr ha
  have hg : Summable fun i : ℕ => |a K| / 2 ^ i := by
    simpa [div_eq_mul_inv, inv_pow] using
      (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).mul_left |a K|
  calc |∑' i : ℕ, a (i + K)| ≤ ∑' i : ℕ, |a (i + K)| := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' i : ℕ, |a K| / 2 ^ i :=
        hs.norm.tsum_le_tsum (fun i => by rw [add_comm]; exact h i) hg
    _ = |a K| * ∑' i : ℕ, (1 / 2 : ℝ) ^ i := by
        rw [← tsum_mul_left]; exact tsum_congr fun i => by rw [one_div_pow, div_eq_mul_one_div]
    _ = 2 * |a K| := by
        rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num; ring

/-- **Truncation of `f`**: if `|x|³ ≤ (3K+2)(3K+3)/2`, then `|f(x) − ∑_{k<K} t_k| ≤ 2 |t_K|`. -/
theorem abs_f_sub_sum_le {K : ℕ} (hK : |x| ^ 3 ≤ (3 * K + 2) * (3 * K + 3) / 2) :
    |f x - ∑ k ∈ range K, fTerm x k| ≤ 2 * |fTerm x K| := by
  rw [f, ← (summable_fTerm x).sum_add_tsum_nat_add K, add_sub_cancel_left]
  exact abs_tsum_add_le_two_mul (summable_fTerm x) K (abs_fTerm_add_le hK)

/-- **Truncation of `g`**: if `|x|³ ≤ (3K+3)(3K+4)/2`, then `|g(x) − ∑_{k<K} u_k| ≤ 2 |u_K|`. -/
theorem abs_g_sub_sum_le {K : ℕ} (hK : |x| ^ 3 ≤ (3 * K + 3) * (3 * K + 4) / 2) :
    |g x - ∑ k ∈ range K, gTerm x k| ≤ 2 * |gTerm x K| := by
  rw [g, ← (summable_gTerm x).sum_add_tsum_nat_add K, add_sub_cancel_left]
  exact abs_tsum_add_le_two_mul (summable_gTerm x) K (abs_gTerm_add_le hK)

/-- `K ≥ |x|^(3/2)` puts the series in the halving regime (both conditions hold). -/
theorem halving_of_le {K : ℕ} (hK : Real.sqrt |x| ^ 3 ≤ K) :
    |x| ^ 3 ≤ (3 * K + 2) * (3 * K + 3) / 2 ∧ |x| ^ 3 ≤ (3 * K + 3) * (3 * K + 4) / 2 := by
  have h0 : 0 ≤ Real.sqrt |x| ^ 3 := by positivity
  have hsq : (Real.sqrt |x| ^ 3) ^ 2 = |x| ^ 3 := by
    rw [← pow_mul, show 3 * 2 = 2 * 3 by ring, pow_mul, Real.sq_sqrt (abs_nonneg x)]
  have hK2 : |x| ^ 3 ≤ (K : ℝ) ^ 2 := by rw [← hsq]; exact pow_le_pow_left₀ h0 hK 2
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  constructor <;> nlinarith

/-! ### Exact rational partial sums -/

/-- The common denominator of `∑_{k<K} t_k(m/q)`: `q^(3K) d_K`. -/
def fPartialDen (q K : ℕ) : ℕ := q ^ (3 * K) * fDen K

/-- The numerator of `∑_{k<K} t_k(m/q)`: `∑_{k<K} m^(3k) q^(3(K−k)) (d_K/d_k)`. -/
def fPartialNum (m : ℤ) (q K : ℕ) : ℤ :=
  ∑ k ∈ range K, m ^ (3 * k) * (q : ℤ) ^ (3 * (K - k)) * ((fDen K / fDen k : ℕ) : ℤ)

/-- The common denominator of `∑_{k<K} u_k(m/q)`: `q^(3K+1) e_K`. -/
def gPartialDen (q K : ℕ) : ℕ := q ^ (3 * K + 1) * gDen K

/-- The numerator of `∑_{k<K} u_k(m/q)`: `∑_{k<K} m^(3k+1) q^(3(K−k)) (e_K/e_k)`. -/
def gPartialNum (m : ℤ) (q K : ℕ) : ℤ :=
  ∑ k ∈ range K, m ^ (3 * k + 1) * (q : ℤ) ^ (3 * (K - k)) * ((gDen K / gDen k : ℕ) : ℤ)

theorem fPartialDen_pos {q : ℕ} (hq : 0 < q) (K : ℕ) : 0 < fPartialDen q K := by
  unfold fPartialDen; have := fDen_pos K; positivity

theorem gPartialDen_pos {q : ℕ} (hq : 0 < q) (K : ℕ) : 0 < gPartialDen q K := by
  unfold gPartialDen; have := gDen_pos K; positivity

/-- The partial sum of `f` at a rational point is the rational `fPartialNum/fPartialDen`. -/
theorem sum_fTerm_div_eq {m : ℤ} {q : ℕ} (hq : 0 < q) (K : ℕ) :
    ∑ k ∈ range K, fTerm ((m : ℝ) / q) k = (fPartialNum m q K : ℝ) / fPartialDen q K := by
  unfold fPartialNum fPartialDen
  have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hD : (fDen K : ℝ) ≠ 0 := by exact_mod_cast (fDen_pos K).ne'
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_natCast, Nat.cast_mul,
    Nat.cast_pow]
  rw [sum_div]
  refine sum_congr rfl fun k hk => ?_
  rw [mem_range] at hk
  have hdk : (fDen k : ℝ) ≠ 0 := by exact_mod_cast (fDen_pos k).ne'
  rw [Nat.cast_div (fDen_dvd hk.le) hdk, fTerm, div_pow,
    show 3 * K = 3 * k + 3 * (K - k) by omega, pow_add]
  field_simp

/-- The partial sum of `g` at a rational point is the rational `gPartialNum/gPartialDen`. -/
theorem sum_gTerm_div_eq {m : ℤ} {q : ℕ} (hq : 0 < q) (K : ℕ) :
    ∑ k ∈ range K, gTerm ((m : ℝ) / q) k = (gPartialNum m q K : ℝ) / gPartialDen q K := by
  unfold gPartialNum gPartialDen
  have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hD : (gDen K : ℝ) ≠ 0 := by exact_mod_cast (gDen_pos K).ne'
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_natCast, Nat.cast_mul,
    Nat.cast_pow]
  rw [sum_div]
  refine sum_congr rfl fun k hk => ?_
  rw [mem_range] at hk
  have hdk : (gDen k : ℝ) ≠ 0 := by exact_mod_cast (gDen_pos k).ne'
  rw [Nat.cast_div (gDen_dvd hk.le) hdk, gTerm, div_pow,
    show 3 * K + 1 = (3 * k + 1) + 3 * (K - k) by omega, pow_add]
  field_simp
  ring

/-! ### Derivatives and the differential equation `y″ = xy` -/

/-- `d/dx t_k = 3k x^(3k−1)/d_k`. -/
noncomputable def fDTerm (x : ℝ) (k : ℕ) : ℝ := (3 * k : ℝ) * x ^ (3 * k - 1) / fDen k

/-- `d/dx u_k = (3k+1) x^(3k)/e_k`. -/
noncomputable def gDTerm (x : ℝ) (k : ℕ) : ℝ := (3 * k + 1 : ℝ) * x ^ (3 * k) / gDen k

/-- `d²/dx² t_k = 3k(3k−1) x^(3k−2)/d_k`. -/
noncomputable def fDDTerm (x : ℝ) (k : ℕ) : ℝ :=
  (3 * k : ℝ) * (3 * k - 1 : ℝ) * x ^ (3 * k - 2) / fDen k

/-- `d²/dx² u_k = (3k+1)(3k) x^(3k−1)/e_k`. -/
noncomputable def gDDTerm (x : ℝ) (k : ℕ) : ℝ :=
  (3 * k + 1 : ℝ) * (3 * k : ℝ) * x ^ (3 * k - 1) / gDen k

/-- `f′(x) = ∑_k 3k x^(3k−1)/d_k`. -/
noncomputable def fD (x : ℝ) : ℝ := ∑' k : ℕ, fDTerm x k

/-- `g′(x) = ∑_k (3k+1) x^(3k)/e_k`. -/
noncomputable def gD (x : ℝ) : ℝ := ∑' k : ℕ, gDTerm x k

@[simp] theorem fDTerm_zero (x : ℝ) : fDTerm x 0 = 0 := by simp [fDTerm]

@[simp] theorem gDTerm_zero (x : ℝ) : gDTerm x 0 = 1 := by simp [gDTerm]

@[simp] theorem fDDTerm_zero (x : ℝ) : fDDTerm x 0 = 0 := by simp [fDDTerm]

@[simp] theorem gDDTerm_zero (x : ℝ) : gDDTerm x 0 = 0 := by simp [gDDTerm]

/-- `d/dx t_{k+1} = x^(3k+2)/(d_k (3k+2))`. -/
theorem fDTerm_succ (x : ℝ) (k : ℕ) :
    fDTerm x (k + 1) = x ^ (3 * k + 2) / (fDen k * (3 * k + 2)) := by
  rw [fDTerm, fDen_succ, show 3 * (k + 1) - 1 = 3 * k + 2 by omega]
  push_cast
  field_simp

/-- `d/dx u_{k+1} = x^(3k+3)/(e_k (3k+3))`. -/
theorem gDTerm_succ (x : ℝ) (k : ℕ) :
    gDTerm x (k + 1) = x ^ (3 * k + 3) / (gDen k * (3 * k + 3)) := by
  rw [gDTerm, gDen_succ, show 3 * (k + 1) = 3 * k + 3 by omega]
  push_cast
  field_simp
  ring

/-- The equation `y″ = xy` term by term: `d²/dx² t_{k+1} = x t_k`. -/
theorem fDDTerm_succ (x : ℝ) (k : ℕ) : fDDTerm x (k + 1) = x * fTerm x k := by
  rw [fDDTerm, fTerm, fDen_succ, show 3 * (k + 1) - 2 = 3 * k + 1 by omega]
  push_cast
  field_simp
  ring

/-- `d²/dx² u_{k+1} = x u_k`. -/
theorem gDDTerm_succ (x : ℝ) (k : ℕ) : gDDTerm x (k + 1) = x * gTerm x k := by
  rw [gDDTerm, gTerm, gDen_succ, show 3 * (k + 1) - 1 = 3 * k + 2 by omega]
  push_cast
  field_simp
  ring

theorem hasDerivAt_fTerm (x : ℝ) (k : ℕ) : HasDerivAt (fun y => fTerm y k) (fDTerm x k) x := by
  have h := (hasDerivAt_pow (3 * k) x).div_const (fDen k : ℝ)
  refine h.congr_deriv ?_
  rw [fDTerm]; push_cast; ring

theorem hasDerivAt_gTerm (x : ℝ) (k : ℕ) : HasDerivAt (fun y => gTerm y k) (gDTerm x k) x := by
  have h := (hasDerivAt_pow (3 * k + 1) x).div_const (gDen k : ℝ)
  refine h.congr_deriv ?_
  rw [gDTerm]; push_cast; ring

theorem hasDerivAt_fDTerm (x : ℝ) (k : ℕ) :
    HasDerivAt (fun y => fDTerm y k) (fDDTerm x k) x := by
  rcases k with _ | k
  · have e : (fun y : ℝ => fDTerm y 0) = fun _ => 0 := by funext y; simp
    rw [e, fDDTerm_zero]
    exact hasDerivAt_const x 0
  · have e : (fun y : ℝ => fDTerm y (k + 1))
        = fun y : ℝ => y ^ (3 * k + 2) / ((fDen k : ℝ) * (3 * k + 2)) := by
      funext y; exact fDTerm_succ y k
    rw [e, fDDTerm_succ]
    have h := (hasDerivAt_pow (3 * k + 2) x).div_const ((fDen k : ℝ) * (3 * k + 2))
    refine h.congr_deriv ?_
    have hD : (fDen k : ℝ) ≠ 0 := by exact_mod_cast (fDen_pos k).ne'
    rw [fTerm]; push_cast; field_simp; ring

theorem hasDerivAt_gDTerm (x : ℝ) (k : ℕ) :
    HasDerivAt (fun y => gDTerm y k) (gDDTerm x k) x := by
  rcases k with _ | k
  · have e : (fun y : ℝ => gDTerm y 0) = fun _ => 1 := by funext y; simp
    rw [e, gDDTerm_zero]
    exact hasDerivAt_const x 1
  · have e : (fun y : ℝ => gDTerm y (k + 1))
        = fun y : ℝ => y ^ (3 * k + 3) / ((gDen k : ℝ) * (3 * k + 3)) := by
      funext y; exact gDTerm_succ y k
    rw [e, gDDTerm_succ]
    have h := (hasDerivAt_pow (3 * k + 3) x).div_const ((gDen k : ℝ) * (3 * k + 3))
    refine h.congr_deriv ?_
    have hD : (gDen k : ℝ) ≠ 0 := by exact_mod_cast (gDen_pos k).ne'
    rw [gTerm]; push_cast; field_simp; ring

/-- Monotonicity of the terms in `|x|`. -/
theorem abs_fTerm_le_fTerm {y R : ℝ} (h : |y| ≤ R) (k : ℕ) : |fTerm y k| ≤ fTerm R k := by
  rw [fTerm, fTerm, abs_div, abs_pow, Nat.abs_cast]
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg y) h _) (by positivity)

theorem abs_gTerm_le_gTerm {y R : ℝ} (h : |y| ≤ R) (k : ℕ) : |gTerm y k| ≤ gTerm R k := by
  rw [gTerm, gTerm, abs_div, abs_pow, Nat.abs_cast]
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg y) h _) (by positivity)

/-- `|d/dx t_{k+1}| ≤ R² t_k(R)` for `|y| ≤ R`. -/
theorem abs_fDTerm_succ_le {y R : ℝ} (h : |y| ≤ R) (k : ℕ) :
    |fDTerm y (k + 1)| ≤ R ^ 2 * fTerm R k := by
  have hR : 0 ≤ R := (abs_nonneg y).trans h
  have hD : (0 : ℝ) < fDen k := by exact_mod_cast fDen_pos k
  have hpos : (0 : ℝ) < fDen k * (3 * k + 2) := mul_pos hD (by positivity)
  rw [fDTerm_succ, abs_div, abs_pow, fTerm, ← mul_div_assoc, ← pow_add, abs_of_pos hpos,
    show 2 + 3 * k = 3 * k + 2 by ring]
  refine div_le_div₀ (by positivity) (pow_le_pow_left₀ (abs_nonneg y) h _) hD ?_
  have : (1 : ℝ) ≤ 3 * k + 2 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  nlinarith

/-- `|d/dx u_{k+1}| ≤ R² u_k(R)` for `|y| ≤ R`. -/
theorem abs_gDTerm_succ_le {y R : ℝ} (h : |y| ≤ R) (k : ℕ) :
    |gDTerm y (k + 1)| ≤ R ^ 2 * gTerm R k := by
  have hR : 0 ≤ R := (abs_nonneg y).trans h
  have hD : (0 : ℝ) < gDen k := by exact_mod_cast gDen_pos k
  have hpos : (0 : ℝ) < gDen k * (3 * k + 3) := mul_pos hD (by positivity)
  rw [gDTerm_succ, abs_div, abs_pow, gTerm, ← mul_div_assoc, ← pow_add, abs_of_pos hpos,
    show 2 + (3 * k + 1) = 3 * k + 3 by ring]
  refine div_le_div₀ (by positivity) (pow_le_pow_left₀ (abs_nonneg y) h _) hD ?_
  have : (1 : ℝ) ≤ 3 * k + 3 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  nlinarith

/-- A bound family indexed like the terms: `0` at `k = 0`, `C · v (k−1)` after. -/
noncomputable def shiftBound (c₀ : ℝ) (C : ℝ) (v : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k = 0 then c₀ else C * v (k - 1)

theorem summable_shiftBound {c₀ C : ℝ} {v : ℕ → ℝ} (hv : Summable v) :
    Summable (shiftBound c₀ C v) := by
  rw [← summable_nat_add_iff 1]
  refine (hv.mul_left C).congr fun k => ?_
  simp [shiftBound]

theorem summable_fDTerm (x : ℝ) : Summable (fDTerm x) :=
  (summable_shiftBound (c₀ := 0) (C := |x| ^ 2) (summable_fTerm |x|)).of_norm_bounded fun k => by
    rcases k with _ | k
    · simp [shiftBound]
    · rw [Real.norm_eq_abs]
      simpa [shiftBound] using abs_fDTerm_succ_le (le_refl |x|) k

theorem summable_gDTerm (x : ℝ) : Summable (gDTerm x) :=
  (summable_shiftBound (c₀ := 1) (C := |x| ^ 2) (summable_gTerm |x|)).of_norm_bounded fun k => by
    rcases k with _ | k
    · simp [shiftBound]
    · rw [Real.norm_eq_abs]
      simpa [shiftBound] using abs_gDTerm_succ_le (le_refl |x|) k

theorem hasDerivAt_f (x : ℝ) : HasDerivAt f (fD x) x := by
  set R : ℝ := |x| + 1 with hR
  have hR0 : 0 ≤ R := by positivity
  have hu : Summable (shiftBound 0 (R ^ 2) (fTerm R)) :=
    summable_shiftBound (summable_fTerm R)
  have hg' : ∀ k (y : ℝ), y ∈ Metric.ball (0 : ℝ) R →
      ‖fDTerm y k‖ ≤ shiftBound 0 (R ^ 2) (fTerm R) k := by
    intro k y hy
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hy
    rcases k with _ | k
    · simp [shiftBound]
    · rw [Real.norm_eq_abs]
      simpa [shiftBound] using abs_fDTerm_succ_le hy.le k
  have hx : x ∈ Metric.ball (0 : ℝ) R := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]; linarith
  have h0 : (0 : ℝ) ∈ Metric.ball (0 : ℝ) R := Metric.mem_ball_self (by positivity)
  exact hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    (convex_ball (0 : ℝ) R).isPreconnected (fun k y _ => hasDerivAt_fTerm y k) hg' h0
    (summable_fTerm 0) hx

theorem hasDerivAt_g (x : ℝ) : HasDerivAt g (gD x) x := by
  set R : ℝ := |x| + 1 with hR
  have hR0 : 0 ≤ R := by positivity
  have hu : Summable (shiftBound 1 (R ^ 2) (gTerm R)) :=
    summable_shiftBound (summable_gTerm R)
  have hg' : ∀ k (y : ℝ), y ∈ Metric.ball (0 : ℝ) R →
      ‖gDTerm y k‖ ≤ shiftBound 1 (R ^ 2) (gTerm R) k := by
    intro k y hy
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hy
    rcases k with _ | k
    · simp [shiftBound]
    · rw [Real.norm_eq_abs]
      simpa [shiftBound] using abs_gDTerm_succ_le hy.le k
  have hx : x ∈ Metric.ball (0 : ℝ) R := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]; linarith
  have h0 : (0 : ℝ) ∈ Metric.ball (0 : ℝ) R := Metric.mem_ball_self (by positivity)
  exact hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    (convex_ball (0 : ℝ) R).isPreconnected (fun k y _ => hasDerivAt_gTerm y k) hg' h0
    (summable_gTerm 0) hx

/-- `∑_k d²/dx² t_k = x f(x)`. -/
theorem tsum_fDDTerm (x : ℝ) : ∑' k : ℕ, fDDTerm x k = x * f x := by
  have hs : Summable (fDDTerm x) := by
    rw [← summable_nat_add_iff 1]
    refine ((summable_fTerm x).mul_left x).congr fun k => ?_
    simp [fDDTerm_succ]
  rw [hs.tsum_eq_zero_add, fDDTerm_zero, zero_add, f, ← tsum_mul_left]
  exact tsum_congr fun k => fDDTerm_succ x k

theorem tsum_gDDTerm (x : ℝ) : ∑' k : ℕ, gDDTerm x k = x * g x := by
  have hs : Summable (gDDTerm x) := by
    rw [← summable_nat_add_iff 1]
    refine ((summable_gTerm x).mul_left x).congr fun k => ?_
    simp [gDDTerm_succ]
  rw [hs.tsum_eq_zero_add, gDDTerm_zero, zero_add, g, ← tsum_mul_left]
  exact tsum_congr fun k => gDDTerm_succ x k

/-- `f′` is differentiable with `f″(x) = x f(x)`. -/
theorem hasDerivAt_fD (x : ℝ) : HasDerivAt fD (x * f x) x := by
  rw [← tsum_fDDTerm]
  set R : ℝ := |x| + 1 with hR
  have hR0 : 0 ≤ R := by positivity
  have hu : Summable (shiftBound 0 R (fTerm R)) := summable_shiftBound (summable_fTerm R)
  have hg' : ∀ k (y : ℝ), y ∈ Metric.ball (0 : ℝ) R →
      ‖fDDTerm y k‖ ≤ shiftBound 0 R (fTerm R) k := by
    intro k y hy
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hy
    rcases k with _ | k
    · simp [shiftBound]
    · rw [Real.norm_eq_abs, fDDTerm_succ, abs_mul]
      simp only [shiftBound, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
      exact mul_le_mul hy.le (abs_fTerm_le_fTerm hy.le k) (abs_nonneg _) hR0
  have hx : x ∈ Metric.ball (0 : ℝ) R := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]; linarith
  have h0 : (0 : ℝ) ∈ Metric.ball (0 : ℝ) R := Metric.mem_ball_self (by positivity)
  exact hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    (convex_ball (0 : ℝ) R).isPreconnected (fun k y _ => hasDerivAt_fDTerm y k) hg' h0
    (summable_fDTerm 0) hx

/-- `g′` is differentiable with `g″(x) = x g(x)`. -/
theorem hasDerivAt_gD (x : ℝ) : HasDerivAt gD (x * g x) x := by
  rw [← tsum_gDDTerm]
  set R : ℝ := |x| + 1 with hR
  have hR0 : 0 ≤ R := by positivity
  have hu : Summable (shiftBound 0 R (gTerm R)) := summable_shiftBound (summable_gTerm R)
  have hg' : ∀ k (y : ℝ), y ∈ Metric.ball (0 : ℝ) R →
      ‖gDDTerm y k‖ ≤ shiftBound 0 R (gTerm R) k := by
    intro k y hy
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hy
    rcases k with _ | k
    · simp [shiftBound]
    · rw [Real.norm_eq_abs, gDDTerm_succ, abs_mul]
      simp only [shiftBound, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
      exact mul_le_mul hy.le (abs_gTerm_le_gTerm hy.le k) (abs_nonneg _) hR0
  have hx : x ∈ Metric.ball (0 : ℝ) R := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]; linarith
  have h0 : (0 : ℝ) ∈ Metric.ball (0 : ℝ) R := Metric.mem_ball_self (by positivity)
  exact hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    (convex_ball (0 : ℝ) R).isPreconnected (fun k y _ => hasDerivAt_gDTerm y k) hg' h0
    (summable_gDTerm 0) hx

theorem deriv_f : deriv f = fD := funext fun x => (hasDerivAt_f x).deriv

theorem deriv_g : deriv g = gD := funext fun x => (hasDerivAt_g x).deriv

/-- The Airy equation for `f`: `f″(x) = x f(x)`. -/
theorem f_ode (x : ℝ) : deriv (deriv f) x = x * f x := by
  rw [deriv_f]; exact (hasDerivAt_fD x).deriv

theorem g_ode (x : ℝ) : deriv (deriv g) x = x * g x := by
  rw [deriv_g]; exact (hasDerivAt_gD x).deriv

@[simp] theorem fD_zero : fD 0 = 0 := by
  have e : fDTerm 0 = fun _ => 0 := by
    funext k
    rcases k with _ | k
    · simp
    · simp [fDTerm_succ]
  rw [fD, e, tsum_zero]

@[simp] theorem gD_zero : gD 0 = 1 := by
  rw [gD, tsum_eq_single 0 fun k hk => ?_, gDTerm_zero]
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp [gDTerm_succ]

/-! ### The Wronskian -/

/-- `W(f, g)(x) = f g′ − f′ g`. -/
noncomputable def wronskianFG (x : ℝ) : ℝ := f x * gD x - fD x * g x

theorem hasDerivAt_wronskianFG (x : ℝ) : HasDerivAt wronskianFG 0 x := by
  have h := ((hasDerivAt_f x).mul (hasDerivAt_gD x)).sub ((hasDerivAt_fD x).mul (hasDerivAt_g x))
  refine h.congr_deriv ?_
  ring

/-- `W(f, g) = 1`. -/
theorem wronskianFG_eq_one (x : ℝ) : wronskianFG x = 1 := by
  have hconst := is_const_of_deriv_eq_zero (fun y => (hasDerivAt_wronskianFG y).differentiableAt)
    (fun y => (hasDerivAt_wronskianFG y).deriv) x 0
  rw [hconst, wronskianFG, f_zero, g_zero, fD_zero, gD_zero]
  ring

/-! ### `Ai` and `Bi` -/

/-- `c₁ = Ai(0) = 3^(−2/3)/Γ(2/3) ≈ 0.355028` (DLMF 9.2.3). -/
noncomputable def c₁ : ℝ := (3 : ℝ) ^ (-(2 / 3 : ℝ)) / Real.Gamma (2 / 3)

/-- `c₂ = −Ai′(0) = 3^(−1/3)/Γ(1/3) ≈ 0.258819` (DLMF 9.2.4). -/
noncomputable def c₂ : ℝ := (3 : ℝ) ^ (-(1 / 3 : ℝ)) / Real.Gamma (1 / 3)

theorem c₁_pos : 0 < c₁ := div_pos (Real.rpow_pos_of_pos (by norm_num) _)
  (Real.Gamma_pos_of_pos (by norm_num))

theorem c₂_pos : 0 < c₂ := div_pos (Real.rpow_pos_of_pos (by norm_num) _)
  (Real.Gamma_pos_of_pos (by norm_num))

/-- `c₁ c₂ = 1/(2√3 π)`, by Euler's reflection formula `Γ(1/3) Γ(2/3) = 2π/√3`. -/
theorem c₁_mul_c₂ : c₁ * c₂ = 1 / (2 * Real.sqrt 3 * Real.pi) := by
  have hΓ := Real.Gamma_mul_Gamma_one_sub (1 / 3)
  rw [show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num, show Real.pi * (1 / 3) = Real.pi / 3 by ring,
    Real.sin_pi_div_three] at hΓ
  have h3 : (3 : ℝ) ^ (-(2 / 3 : ℝ)) * (3 : ℝ) ^ (-(1 / 3 : ℝ)) = 1 / 3 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3), show -(2 / 3 : ℝ) + -(1 / 3) = -1 by norm_num,
      Real.rpow_neg_one, one_div]
  have hG1 : 0 < Real.Gamma (1 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  have hG2 : 0 < Real.Gamma (2 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  have hs3 : (0 : ℝ) < Real.sqrt 3 := by positivity
  have hs3sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [c₁, c₂, div_mul_div_comm, h3, mul_comm (Real.Gamma (2 / 3)), hΓ]
  field_simp
  nlinarith [hs3sq, Real.pi_pos]

/-- The Airy function `Ai(x) = c₁ f(x) − c₂ g(x)` (DLMF 9.4.1). -/
noncomputable def Ai (x : ℝ) : ℝ := c₁ * f x - c₂ * g x

/-- The Airy function `Bi(x) = √3 (c₁ f(x) + c₂ g(x))` (DLMF 9.4.3). -/
noncomputable def Bi (x : ℝ) : ℝ := Real.sqrt 3 * (c₁ * f x + c₂ * g x)

/-- `Ai′(x) = c₁ f′(x) − c₂ g′(x)`. -/
noncomputable def AiD (x : ℝ) : ℝ := c₁ * fD x - c₂ * gD x

/-- `Bi′(x) = √3 (c₁ f′(x) + c₂ g′(x))`. -/
noncomputable def BiD (x : ℝ) : ℝ := Real.sqrt 3 * (c₁ * fD x + c₂ * gD x)

@[simp] theorem Ai_zero : Ai 0 = c₁ := by simp [Ai]

@[simp] theorem Bi_zero : Bi 0 = Real.sqrt 3 * c₁ := by simp [Bi]

@[simp] theorem AiD_zero : AiD 0 = -c₂ := by simp [AiD]

@[simp] theorem BiD_zero : BiD 0 = Real.sqrt 3 * c₂ := by simp [BiD]

theorem hasDerivAt_Ai (x : ℝ) : HasDerivAt Ai (AiD x) x :=
  ((hasDerivAt_f x).const_mul c₁).sub ((hasDerivAt_g x).const_mul c₂)

theorem hasDerivAt_Bi (x : ℝ) : HasDerivAt Bi (BiD x) x :=
  (((hasDerivAt_f x).const_mul c₁).add ((hasDerivAt_g x).const_mul c₂)).const_mul (Real.sqrt 3)

theorem hasDerivAt_AiD (x : ℝ) : HasDerivAt AiD (x * Ai x) x := by
  have h := ((hasDerivAt_fD x).const_mul c₁).sub ((hasDerivAt_gD x).const_mul c₂)
  refine h.congr_deriv ?_
  rw [Ai]; ring

theorem hasDerivAt_BiD (x : ℝ) : HasDerivAt BiD (x * Bi x) x := by
  have h := (((hasDerivAt_fD x).const_mul c₁).add ((hasDerivAt_gD x).const_mul c₂)).const_mul
    (Real.sqrt 3)
  refine h.congr_deriv ?_
  rw [Bi]; ring

theorem deriv_Ai : deriv Ai = AiD := funext fun x => (hasDerivAt_Ai x).deriv

theorem deriv_Bi : deriv Bi = BiD := funext fun x => (hasDerivAt_Bi x).deriv

/-- **The Airy equation**: `Ai″(x) = x Ai(x)`. -/
theorem Ai_ode (x : ℝ) : deriv (deriv Ai) x = x * Ai x := by
  rw [deriv_Ai]; exact (hasDerivAt_AiD x).deriv

/-- `Bi″(x) = x Bi(x)`. -/
theorem Bi_ode (x : ℝ) : deriv (deriv Bi) x = x * Bi x := by
  rw [deriv_Bi]; exact (hasDerivAt_BiD x).deriv

/-- **The Wronskian** `W(Ai, Bi) = Ai Bi′ − Ai′ Bi = 1/π` (DLMF 9.2.7). -/
theorem wronskian_Ai_Bi (x : ℝ) : Ai x * BiD x - AiD x * Bi x = 1 / Real.pi := by
  have hW := wronskianFG_eq_one x
  rw [wronskianFG] at hW
  have hc := c₁_mul_c₂
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hπ : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hs : Real.sqrt 3 ≠ 0 := by positivity
  have e : Ai x * BiD x - AiD x * Bi x
      = 2 * Real.sqrt 3 * (c₁ * c₂) * (f x * gD x - fD x * g x) := by
    unfold Ai Bi AiD BiD; ring
  rw [e, hW, hc]
  field_simp

end Airy

end Azurite
