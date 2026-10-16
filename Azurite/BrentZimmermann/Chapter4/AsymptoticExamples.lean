/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BrentZimmermann.Chapter4.AsymptoticExpansion
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Brent–Zimmermann §4.5: Euler's constant and the Riemann zeta function

Asymptotic expansions serve `erfc`, `Γ`, Bessel functions, …, and arise when the Euler–Maclaurin
sum formula accelerates a series: for `f` smooth and integers `a ≤ b`,

  `∑_{a≤k≤b} f(k) − ∫_a^b f ~ (f(a) + f(b))/2 + ∑_{k≥1} B_{2k}/(2k)! (f^(2k−1)(b) − f^(2k−1)(a))`.

**Euler's constant** `γ = lim (H_N − ln N)` (4.31) converges slowly; splitting `H_N` at `p` and
applying Euler–Maclaurin to `f(x) = 1/x` gives `γ ~ H_p − ln p + ∑_{k≥1} B_{2k}/(2k) p^(−2k)`
(4.32).

**The zeta function** `ζ(s) = ∑_{j≥1} j^(−s)` (4.33) is computed from the Euler–Maclaurin formula
(4.34) `ζ(s) = ∑_{j<p} j^(−s) + p^(−s)/2 + p^(1−s)/(s−1) + ∑_{k=1}^m T_{k,p}(s) + E_{m,p}(s)` with
`T_{k,p}(s) = B_{2k}/(2k)! p^(1−s−2k) ∏_{j=0}^{2k−2} (s+j)` (4.35) and
`|E_{m,p}(s)| < |T_{m+1,p}(s) (s+2m+1)/(σ+2m+1)|` (4.36).  For precision `n` in polynomial time both
`m` and `p` must grow with `n`, so the Bernoulli numbers cannot be tabulated once and for all; an
expansion whose coefficients are known (like (4.38) for `ln Γ`) is simpler than one whose
coefficients are not (Stirling's for `Γ`).

What is formalized:

* (4.31) `tendsto_harmonic_sub_log'` from Mathlib, and the slowness of the convergence
  `harmonic_sub_log_sub_gamma_bounds`: `0 < H_N − ln N − γ ≤ 1/N`, from Mathlib's bracket
  `H_N − ln(N+1) < γ < H_N − ln N`.
* `zetaReal s = ∑' n, (n^s)⁻¹` for real `s > 1`, `zetaReal_eq_riemannZeta` (it is Mathlib's
  `riemannZeta` on the real axis), the tail `zetaTail s p = ∑' j, ((j + p)^s)⁻¹` with the
  integral bracket `zetaTail_bounds`: `p^(1−s)/(s−1) ≤ ∑_{j≥p} j^(−s) ≤ p^(1−s)/(s−1) + p^(−s)`.
* (4.34) at `m = 0`: `zetaReal_eq_sum_add_tail` and `abs_zetaReal_sub_euler_maclaurin_zero_le` —
  `|ζ(s) − (∑_{j<p} j^(−s) + p^(−s)/2 + p^(1−s)/(s−1))| ≤ p^(−s)/2`; `zeta_tail_le_of_pow` — with
  `m` fixed, `p ≥ 2^(n/s)` is what precision `n` requires (`p` exponential in `n`).
* `zetaEMTerm k p s` — the terms (4.35) with Mathlib's Bernoulli numbers; `zetaEMTerm_one`
  (`T_{1,p}(s) = s p^(−s−1)/12`).

Not formalized: the Euler–Maclaurin formula itself and hence (4.32), (4.34) for `m ≥ 1`, (4.36);
the analytic continuation of `ζ`; the `erfc`, `Γ`, Bessel examples (later sections).
-/

namespace Azurite

namespace BZ

open Real Filter Topology Finset MeasureTheory Set

/-! ### Euler's constant, (4.31) -/

/-- (4.31): `γ = lim (H_N − ln N)`. -/
theorem tendsto_harmonic_sub_log' :
    Tendsto (fun N : ℕ => (harmonic N : ℝ) - Real.log N) atTop (𝓝 eulerMascheroniConstant) :=
  Real.tendsto_harmonic_sub_log

/-- The convergence of (4.31) is slow: `0 < H_N − ln N − γ ≤ 1/N`. -/
theorem harmonic_sub_log_sub_gamma_bounds {N : ℕ} (hN : 1 ≤ N) :
    0 < (harmonic N : ℝ) - Real.log N - eulerMascheroniConstant ∧
      (harmonic N : ℝ) - Real.log N - eulerMascheroniConstant ≤ 1 / N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hlo := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant N
  have hhi := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' N
  rw [Real.eulerMascheroniSeq'] at hhi
  rw [ite_eq_right (by omega)] at hhi
  rw [Real.eulerMascheroniSeq] at hlo
  constructor
  · linarith
  · have hlog : Real.log ((N : ℝ) + 1) - Real.log N ≤ 1 / N := by
      rw [← Real.log_div (by positivity) hN0.ne', add_div, div_self hN0.ne']
      have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + 1 / N)
      linarith
    linarith

/-! ### The zeta function, (4.33) -/

/-- `ζ(s) = ∑ n^(−s)` for real `s > 1` (the `n = 0` term is `0`). -/
noncomputable def zetaReal (s : ℝ) : ℝ := ∑' n : ℕ, ((n : ℝ) ^ s)⁻¹

/-- `zetaReal` is Mathlib's `riemannZeta` on the real axis `s > 1`. -/
theorem zetaReal_eq_riemannZeta {s : ℝ} (hs : 1 < s) : (zetaReal s : ℂ) = riemannZeta s := by
  rw [zeta_eq_tsum_one_div_nat_cpow (by simpa using hs), zetaReal, Complex.ofReal_tsum]
  congr 1
  funext n
  rw [one_div, Complex.ofReal_inv, Complex.ofReal_cpow (Nat.cast_nonneg n)]
  push_cast
  rfl

/-- The tail `∑_{j≥p} j^(−s)`. -/
noncomputable def zetaTail (s : ℝ) (p : ℕ) : ℝ := ∑' j : ℕ, (((j + p : ℕ) : ℝ) ^ s)⁻¹

theorem summable_zetaTail {s : ℝ} (hs : 1 < s) (p : ℕ) :
    Summable (fun j : ℕ => (((j + p : ℕ) : ℝ) ^ s)⁻¹) :=
  (Real.summable_nat_rpow_inv.mpr hs).comp_injective (add_left_injective p)

/-- Splitting the series at `p`: `ζ(s) = ∑_{j<p} j^(−s) + ∑_{j≥p} j^(−s)`. -/
theorem zetaReal_eq_sum_add_tail {s : ℝ} (hs : 1 < s) (p : ℕ) :
    zetaReal s = ∑ j ∈ range p, ((j : ℝ) ^ s)⁻¹ + zetaTail s p := by
  unfold zetaReal zetaTail
  exact (Summable.sum_add_tsum_nat_add' (f := fun n : ℕ => ((n : ℝ) ^ s)⁻¹) (k := p)
    (summable_zetaTail hs p)).symm

/-- `x ↦ x^(−s)` is antitone on the positive reals. -/
theorem antitoneOn_rpow_neg {s : ℝ} (hs : 0 ≤ s) : AntitoneOn (fun x : ℝ => x ^ (-s)) (Ioi 0) :=
  fun x hx _ _ hxy => Real.rpow_le_rpow_of_nonpos hx hxy (by linarith)

/-- `∫_p^∞ x^(−s) dx = p^(1−s)/(s−1)`. -/
theorem integral_Ioi_rpow_neg {s : ℝ} (hs : 1 < s) {p : ℝ} (hp : 0 < p) :
    ∫ x in Ioi p, x ^ (-s) = p ^ (1 - s) / (s - 1) := by
  rw [integral_Ioi_rpow_of_lt (by linarith) hp]
  rw [show -s + 1 = 1 - s by ring, neg_div, ← div_neg, neg_sub]

/-- The integral bracket for the tail: `p^(1−s)/(s−1) ≤ ∑_{j≥p} j^(−s) ≤ p^(1−s)/(s−1) + p^(−s)`,
for `s > 1`, `p ≥ 1`. -/
theorem zetaTail_bounds {s : ℝ} (hs : 1 < s) {p : ℕ} (hp : 1 ≤ p) :
    (p : ℝ) ^ (1 - s) / (s - 1) ≤ zetaTail s p ∧
      zetaTail s p ≤ (p : ℝ) ^ (1 - s) / (s - 1) + ((p : ℝ) ^ s)⁻¹ := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  set f : ℝ → ℝ := fun x => x ^ (-s) with hf
  have hfval : ∀ j : ℕ, f (p + j) = (((j + p : ℕ) : ℝ) ^ s)⁻¹ := fun j => by
    rw [hf]; push_cast; rw [Real.rpow_neg (by positivity), add_comm]
  have hanti : ∀ a : ℕ, AntitoneOn f (Icc (p : ℝ) (p + a)) := fun a =>
    (antitoneOn_rpow_neg (by linarith)).mono fun x hx => lt_of_lt_of_le hp0 hx.1
  -- the finite comparisons
  have hup : ∀ a : ℕ, ∫ x in (p : ℝ)..(p + a), f x ≤ ∑ i ∈ range a, (((i + p : ℕ) : ℝ) ^ s)⁻¹ := by
    intro a
    have h := (hanti a).integral_le_sum
    refine h.trans (le_of_eq (sum_congr rfl fun i _ => ?_))
    exact hfval i
  have hlow : ∀ a : ℕ,
      ∑ i ∈ range a, (((i + 1 + p : ℕ) : ℝ) ^ s)⁻¹ ≤ ∫ x in (p : ℝ)..(p + a), f x := by
    intro a
    have h := (hanti a).sum_le_integral
    refine le_trans (le_of_eq (sum_congr rfl fun i _ => ?_)) h
    rw [← hfval (i + 1)]
  -- the limits
  have hint : Tendsto (fun a : ℕ => ∫ x in (p : ℝ)..(p + a), f x) atTop
      (𝓝 ((p : ℝ) ^ (1 - s) / (s - 1))) := by
    rw [← integral_Ioi_rpow_neg hs hp0]
    exact intervalIntegral_tendsto_integral_Ioi (p : ℝ)
      (integrableOn_Ioi_rpow_of_lt (by linarith) hp0)
      (tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop)
  have hsum1 : Tendsto (fun a : ℕ => ∑ i ∈ range a, (((i + p : ℕ) : ℝ) ^ s)⁻¹) atTop
      (𝓝 (zetaTail s p)) := (summable_zetaTail hs p).hasSum.tendsto_sum_nat
  have hsum2 : Tendsto (fun a : ℕ => ∑ i ∈ range a, (((i + 1 + p : ℕ) : ℝ) ^ s)⁻¹) atTop
      (𝓝 (zetaTail s p - ((p : ℝ) ^ s)⁻¹)) := by
    have h := (summable_zetaTail hs (p + 1)).hasSum.tendsto_sum_nat
    have hsplit := Summable.sum_add_tsum_nat_add' (f := fun j : ℕ => (((j + p : ℕ) : ℝ) ^ s)⁻¹)
      (k := 1) (by
        have := summable_zetaTail hs (p + 1)
        refine this.congr fun j => ?_
        congr 3; omega)
    simp only [sum_range_one, Nat.zero_add] at hsplit
    have heq : zetaTail s p - ((p : ℝ) ^ s)⁻¹ = ∑' j : ℕ, (((j + (p + 1) : ℕ) : ℝ) ^ s)⁻¹ := by
      unfold zetaTail
      rw [← hsplit]
      simp only [add_sub_cancel_left]
      congr 1
      funext j; congr 3; omega
    rw [heq]
    refine h.congr fun a => sum_congr rfl fun i _ => ?_
    congr 3; omega
  constructor
  · exact le_of_tendsto_of_tendsto hint hsum1 (Eventually.of_forall hup)
  · have := le_of_tendsto_of_tendsto hsum2 hint (Eventually.of_forall hlow)
    linarith

/-- (4.34) at `m = 0`: `|ζ(s) − (∑_{j<p} j^(−s) + p^(−s)/2 + p^(1−s)/(s−1))| ≤ p^(−s)/2`. -/
theorem abs_zetaReal_sub_euler_maclaurin_zero_le {s : ℝ} (hs : 1 < s) {p : ℕ} (hp : 1 ≤ p) :
    |zetaReal s - (∑ j ∈ range p, ((j : ℝ) ^ s)⁻¹ + ((p : ℝ) ^ s)⁻¹ / 2
      + (p : ℝ) ^ (1 - s) / (s - 1))| ≤ ((p : ℝ) ^ s)⁻¹ / 2 := by
  rw [zetaReal_eq_sum_add_tail hs p]
  obtain ⟨h1, h2⟩ := zetaTail_bounds hs hp
  rw [abs_le]
  constructor <;> linarith

/-- With `m` fixed, precision `n` needs `p` exponential in `n`: `p ≥ 2^(n/s)` gives
`p^(−s) ≤ 2^(−n)`. -/
theorem zeta_tail_le_of_pow {s : ℝ} (hs : 1 < s) {n : ℕ} {p : ℝ}
    (hp : (2 : ℝ) ^ ((n : ℝ) / s) ≤ p) :
    (p ^ s)⁻¹ ≤ (2 : ℝ) ^ (-(n : ℝ)) := by
  have h2 : (0 : ℝ) < 2 ^ ((n : ℝ) / s) := by positivity
  have hp0 : 0 < p := lt_of_lt_of_le h2 hp
  rw [← Real.rpow_neg hp0.le]
  calc p ^ (-s) ≤ ((2 : ℝ) ^ ((n : ℝ) / s)) ^ (-s) :=
        Real.rpow_le_rpow_of_nonpos h2 hp (by linarith)
    _ = (2 : ℝ) ^ (-(n : ℝ)) := by
        rw [← Real.rpow_mul (by norm_num)]
        congr 1
        field_simp

/-! ### The Euler–Maclaurin terms (4.35) -/

/-- `T_{k,p}(s) = B_{2k}/(2k)! · p^(1−s−2k) · ∏_{j=0}^{2k−2} (s + j)`, with Mathlib's Bernoulli
numbers (`bernoulli (2k)` agrees with the classical `B_{2k}`). -/
noncomputable def zetaEMTerm (k p : ℕ) (s : ℝ) : ℝ :=
  (bernoulli (2 * k) : ℝ) / (2 * k).factorial * (p : ℝ) ^ (1 - s - 2 * k)
    * ∏ j ∈ range (2 * k - 1), (s + j)

/-- `T_{1,p}(s) = s · p^(−s−1) / 12`. -/
theorem zetaEMTerm_one (p : ℕ) (s : ℝ) : zetaEMTerm 1 p s = s * (p : ℝ) ^ (-s - 1) / 12 := by
  unfold zetaEMTerm
  norm_num [bernoulli_two, Nat.factorial]
  ring_nf

end BZ

end Azurite
