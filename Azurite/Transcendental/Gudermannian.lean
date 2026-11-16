/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section23Gudermannian
import Azurite.Transcendental.Cos

/-!
# The Gudermannian of a nonzero rational is irrational

If `gd x = r` then `cos r · cosh x = 1` (`cos (gd x) = sech x`), that is

  `e^{x + ir} + e^{x − ir} + e^{−x + ir} + e^{−x − ir} = 4`,

a linear relation between the exponentials of the four numbers `(±a ± ib)/N` (`x = a/N`,
`r = b/N`) and `1`.  The Hermite–Lindemann argument of `Transcendental/Cos.lean` excludes it,
from Mathlib's analytic lemma `LindemannWeierstrass.exp_polynomial_approx` applied to

  `f = N⁴ X⁴ − 2 N² (a² − b²) X² + (a² + b²)² ∈ ℤ[X]`,

whose roots are those four numbers:

* For every large prime `p` there are `nₚ ∈ ℤ` with `p ∤ nₚ` and `gₚ ∈ ℤ[X]` of degree below
  `4p` with `|nₚ e^α − p gₚ(α)| ≤ c^p/(p−1)!` at the four roots `α`.
* `f` is not monic, so the sum of `gₚ` over the roots is not an integer, but `N^{4p}` times it
  is: the power sums of the Gaussian integers `±a ± ib` are integers
  (`exists_int_pow_sum`, `exists_int_scaled_aeval_sum`).
* So the integer `E = 4 nₚ N^{4p} − p M` has `|E| ≤ 4 (N⁴ c)^p/(p−1)! < 1`, hence `E = 0` and
  `p ∣ 4 nₚ N^{4p}`, impossible for a prime `p > max 4 N` not dividing `nₚ`
  (`cos_mul_cosh_ne_one`).

Hence `irrational_gd_rat`: with it the Ziv loop of the Gudermannian of `AzFloat` needs no fuel.
-/

namespace Azurite

open Polynomial Finset Filter Topology
open scoped Nat

/-- Powers of a Gaussian integer and of its conjugate. -/
theorem exists_int_gaussian_pow (a b : ℤ) (k : ℕ) :
    ∃ c d : ℤ, ((a : ℂ) + b * Complex.I) ^ k = c + d * Complex.I ∧
      ((a : ℂ) - b * Complex.I) ^ k = c - d * Complex.I := by
  induction k with
  | zero => exact ⟨1, 0, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨c, d, h1, h2⟩ := ih
    refine ⟨c * a - d * b, c * b + d * a, ?_, ?_⟩
    · rw [pow_succ, h1]
      push_cast
      linear_combination ((d : ℂ) * b) * Complex.I_sq
    · rw [pow_succ, h2]
      push_cast
      linear_combination ((d : ℂ) * b) * Complex.I_sq

/-- The `k`-th power sum of the four Gaussian integers `±a ± ib` is an integer. -/
theorem exists_int_pow_sum (a b : ℤ) (k : ℕ) :
    ∃ m : ℤ, ((a : ℂ) + b * Complex.I) ^ k + ((a : ℂ) - b * Complex.I) ^ k
      + (-(a : ℂ) + b * Complex.I) ^ k + (-(a : ℂ) - b * Complex.I) ^ k = m := by
  obtain ⟨c, d, h1, h2⟩ := exists_int_gaussian_pow a b k
  have e3 : (-(a : ℂ) + b * Complex.I) = -((a : ℂ) - b * Complex.I) := by ring
  have e4 : (-(a : ℂ) - b * Complex.I) = -((a : ℂ) + b * Complex.I) := by ring
  rw [e3, e4, neg_pow ((a : ℂ) - _), neg_pow ((a : ℂ) + _), h1, h2]
  refine ⟨2 * c + (-1) ^ k * (2 * c), ?_⟩
  push_cast
  ring

/-- `N^D` times the sum of `g ∈ ℤ[X]` over the four numbers `(±a ± ib)/N` is an integer when
`deg g ≤ D`. -/
theorem exists_int_scaled_aeval_sum (a b : ℤ) {N : ℤ} (hN : N ≠ 0) (g : ℤ[X]) {D : ℕ}
    (hD : g.natDegree ≤ D) :
    ∃ M : ℤ, (N : ℂ) ^ D * (aeval (((a : ℂ) + b * Complex.I) / N) g
      + aeval (((a : ℂ) - b * Complex.I) / N) g + aeval ((-(a : ℂ) + b * Complex.I) / N) g
      + aeval ((-(a : ℂ) - b * Complex.I) / N) g) = M := by
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  choose m hm using exists_int_pow_sum a b
  refine ⟨∑ i ∈ range (D + 1), g.coeff i * N ^ (D - i) * m i, ?_⟩
  simp only [aeval_eq_sum_range' (Nat.lt_succ_of_le hD), ← sum_add_distrib, mul_sum]
  push_cast
  refine sum_congr rfl fun i hi => ?_
  have hi' : i ≤ D := Nat.lt_succ_iff.mp (mem_range.mp hi)
  have hpow : (N : ℂ) ^ D = N ^ (D - i) * N ^ i := by rw [← pow_add, Nat.sub_add_cancel hi']
  rw [← hm i, hpow]
  simp only [zsmul_eq_mul, div_pow]
  field_simp

/-- The quartic satisfied by `A + iB`. -/
theorem gaussian_quartic (A B : ℂ) :
    (A + B * Complex.I) ^ 4 - 2 * (A ^ 2 - B ^ 2) * (A + B * Complex.I) ^ 2
      + (A ^ 2 + B ^ 2) ^ 2 = 0 := by
  linear_combination
    (4 * A ^ 2 * B ^ 2 + 4 * A * B ^ 3 * Complex.I + B ^ 4 * (Complex.I ^ 2 + 1)) * Complex.I_sq

/-- The polynomial `N⁴ X⁴ − 2 N² (a² − b²) X² + (a² + b²)²` with the roots `(±a ± ib)/N`. -/
noncomputable def gdPoly (a b N : ℤ) : ℤ[X] :=
  C (N ^ 4) * X ^ 4 - C (2 * N ^ 2 * (a ^ 2 - b ^ 2)) * X ^ 2 + C ((a ^ 2 + b ^ 2) ^ 2)

theorem gdPoly_eval_zero (a b N : ℤ) : (gdPoly a b N).eval 0 = (a ^ 2 + b ^ 2) ^ 2 := by
  simp [gdPoly]

theorem gdPoly_natDegree_le (a b N : ℤ) : (gdPoly a b N).natDegree ≤ 4 := by
  unfold gdPoly
  compute_degree

/-- `(A + iB)/N` is a root of `gdPoly a b N` whenever `A² = a²`, `B² = b²`. -/
theorem div_mem_aroots_gdPoly {a b N : ℤ} (ha : a ≠ 0) (hN : N ≠ 0) {A B : ℤ}
    (hA : A ^ 2 = a ^ 2) (hB : B ^ 2 = b ^ 2) :
    ((A : ℂ) + B * Complex.I) / N ∈ (gdPoly a b N).aroots ℂ := by
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  rw [mem_aroots]
  refine ⟨fun h => ?_, ?_⟩
  · have h0 := congrArg (fun P : ℤ[X] => P.eval 0) h
    simp only [gdPoly_eval_zero, eval_zero] at h0
    have : 0 < a ^ 2 := by positivity
    nlinarith [sq_nonneg b, sq_nonneg (a ^ 2 + b ^ 2)]
  · have hA' : (a : ℂ) ^ 2 = (A : ℂ) ^ 2 := by exact_mod_cast hA.symm
    have hB' : (b : ℂ) ^ 2 = (B : ℂ) ^ 2 := by exact_mod_cast hB.symm
    have hq := gaussian_quartic (A : ℂ) (B : ℂ)
    have hev : aeval (((A : ℂ) + B * Complex.I) / N) (gdPoly a b N)
        = (N : ℂ) ^ 4 * (((A : ℂ) + B * Complex.I) / N) ^ 4
          - 2 * (N : ℂ) ^ 2 * ((a : ℂ) ^ 2 - (b : ℂ) ^ 2) * (((A : ℂ) + B * Complex.I) / N) ^ 2
          + ((a : ℂ) ^ 2 + (b : ℂ) ^ 2) ^ 2 := by
      rw [gdPoly]
      simp only [map_add, map_sub, map_mul, aeval_C, aeval_X_pow]
      simp only [algebraMap_int_eq, eq_intCast]
      push_cast
      ring
    rw [hev, hA', hB', div_pow, div_pow]
    field_simp
    linear_combination hq

/-- The four exponentials add up to `4 cos r cosh x`. -/
theorem exp_gaussian_sum (x r : ℝ) :
    Complex.exp ((x : ℂ) + r * Complex.I) + Complex.exp ((x : ℂ) - r * Complex.I)
      + Complex.exp (-(x : ℂ) + r * Complex.I) + Complex.exp (-(x : ℂ) - r * Complex.I)
      = ((4 * (Real.cos r * Real.cosh x) : ℝ) : ℂ) := by
  have hc := Complex.two_cos (x := (r : ℂ))
  have hh := Complex.two_cosh (x := (x : ℂ))
  rw [neg_mul] at hc
  push_cast
  rw [Complex.exp_add, Complex.exp_add, sub_eq_add_neg, sub_eq_add_neg, Complex.exp_add,
    Complex.exp_add]
  linear_combination (-(Complex.exp (x : ℂ) + Complex.exp (-(x : ℂ)))) * hc
    - 2 * Complex.cos (r : ℂ) * hh

/-- **Hermite–Lindemann at `(±a ± ib)/N`**: `cos (b/N) · cosh (a/N) ≠ 1` for integers `a ≠ 0`,
`b` and `N > 0`. -/
theorem cos_mul_cosh_ne_one {a b N : ℤ} (ha : a ≠ 0) (hN : 0 < N)
    (h : Real.cos ((b : ℝ) / N) * Real.cosh ((a : ℝ) / N) = 1) : False := by
  have hN0 : N ≠ 0 := hN.ne'
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN0
  set f : ℤ[X] := gdPoly a b N with hf
  have hf0 : f.eval 0 ≠ 0 := by
    rw [hf, gdPoly_eval_zero]
    have : 0 < a ^ 2 := by positivity
    nlinarith [sq_nonneg b, sq_nonneg (a ^ 2 + b ^ 2)]
  obtain ⟨cst, hcst⟩ := LindemannWeierstrass.exp_polynomial_approx f hf0
  set K : ℝ := (N : ℝ) ^ 4 * cst with hK
  -- `4 K^p/(p−1)! → 0`
  have hlim : Tendsto (fun p : ℕ => (4 : ℝ) * (K ^ p / ((p - 1)! : ℝ))) atTop (𝓝 0) := by
    have h2 : Tendsto (fun p : ℕ => K ^ (p - 1) / ((p - 1)! : ℝ)) atTop (𝓝 0) :=
      (FloorSemiring.tendsto_pow_div_factorial_atTop K).comp (tendsto_sub_atTop_nat 1)
    have h3 : Tendsto (fun p : ℕ => (4 : ℝ) * K * (K ^ (p - 1) / ((p - 1)! : ℝ))) atTop
        (𝓝 0) := by
      simpa using h2.const_mul ((4 : ℝ) * K)
    refine h3.congr' (eventually_atTop.mpr ⟨1, fun p hp => ?_⟩)
    obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
    simp only [Nat.add_sub_cancel, pow_succ]
    ring
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds one_pos))
  -- a large prime
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes
    (max N₀ (max (f.eval 0).natAbs (max 4 N.natAbs)) + 1)
  obtain ⟨nₚ, hnp, gₚ, hdeg, hbound⟩ := hcst p (by omega) hp
  have hdeg' : gₚ.natDegree ≤ 4 * p := by
    have := gdPoly_natDegree_le a b N
    rw [← hf] at this
    calc gₚ.natDegree ≤ p * f.natDegree - 1 := hdeg
      _ ≤ p * f.natDegree := Nat.sub_le _ _
      _ ≤ p * 4 := Nat.mul_le_mul_left p this
      _ = 4 * p := Nat.mul_comm _ _
  have hb₁ := hbound (div_mem_aroots_gdPoly ha hN0 (A := a) (B := b) rfl rfl)
  have hb₂ := hbound (div_mem_aroots_gdPoly ha hN0 (A := a) (B := -b) rfl (by ring))
  have hb₃ := hbound (div_mem_aroots_gdPoly ha hN0 (A := -a) (B := b) (by ring) rfl)
  have hb₄ := hbound (div_mem_aroots_gdPoly ha hN0 (A := -a) (B := -b) (by ring) (by ring))
  rw [zsmul_eq_mul, nsmul_eq_mul] at hb₁ hb₂ hb₃ hb₄
  push_cast at hb₂ hb₃ hb₄
  rw [neg_mul, ← sub_eq_add_neg] at hb₂ hb₄
  obtain ⟨M, hM⟩ := exists_int_scaled_aeval_sum a b hN0 gₚ hdeg'
  -- the four exponentials add up to `4`
  have hsum : Complex.exp (((a : ℂ) + b * Complex.I) / N)
      + Complex.exp (((a : ℂ) - b * Complex.I) / N)
      + Complex.exp ((-(a : ℂ) + b * Complex.I) / N)
      + Complex.exp ((-(a : ℂ) - b * Complex.I) / N) = 4 := by
    have := exp_gaussian_sum ((a : ℝ) / N) ((b : ℝ) / N)
    rw [h, mul_one] at this
    push_cast at this
    rw [show ((a : ℂ) + b * Complex.I) / N = (a : ℂ) / N + (b : ℂ) / N * Complex.I by ring,
      show ((a : ℂ) - b * Complex.I) / N = (a : ℂ) / N - (b : ℂ) / N * Complex.I by ring,
      show (-(a : ℂ) + b * Complex.I) / N = -((a : ℂ) / N) + (b : ℂ) / N * Complex.I by ring,
      show (-(a : ℂ) - b * Complex.I) / N = -((a : ℂ) / N) - (b : ℂ) / N * Complex.I by ring]
    exact this
  -- the integer `E`
  set E : ℤ := 4 * nₚ * N ^ (4 * p) - p * M with hEdef
  have hE : (E : ℂ) = (N : ℂ) ^ (4 * p)
      * ((nₚ * Complex.exp (((a : ℂ) + b * Complex.I) / N)
          - p * aeval (((a : ℂ) + b * Complex.I) / N) gₚ)
        + (nₚ * Complex.exp (((a : ℂ) - b * Complex.I) / N)
          - p * aeval (((a : ℂ) - b * Complex.I) / N) gₚ)
        + (nₚ * Complex.exp ((-(a : ℂ) + b * Complex.I) / N)
          - p * aeval ((-(a : ℂ) + b * Complex.I) / N) gₚ)
        + (nₚ * Complex.exp ((-(a : ℂ) - b * Complex.I) / N)
          - p * aeval ((-(a : ℂ) - b * Complex.I) / N) gₚ)) := by
    rw [hEdef]
    push_cast
    linear_combination (-(nₚ : ℂ) * (N : ℂ) ^ (4 * p)) * hsum + (p : ℂ) * hM
  have hEle : ‖(E : ℂ)‖ ≤ (4 : ℝ) * (K ^ p / ((p - 1)! : ℝ)) := by
    rw [hE, norm_mul, norm_pow, Complex.norm_intCast, abs_of_pos (by exact_mod_cast hN)]
    have h4 := (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add ((norm_add_le _ _).trans (add_le_add hb₁ hb₂)) hb₃)) hb₄)
    have hNp : (0 : ℝ) ≤ (N : ℝ) ^ (4 * p) := by positivity
    calc (N : ℝ) ^ (4 * p) * ‖_‖
        ≤ (N : ℝ) ^ (4 * p) * (cst ^ p / ((p - 1)! : ℝ) + cst ^ p / ((p - 1)! : ℝ)
          + cst ^ p / ((p - 1)! : ℝ) + cst ^ p / ((p - 1)! : ℝ)) :=
          mul_le_mul_of_nonneg_left h4 hNp
      _ = (4 : ℝ) * (K ^ p / ((p - 1)! : ℝ)) := by
          rw [hK, mul_pow, ← pow_mul]
          ring
  have hlt : ‖(E : ℂ)‖ < 1 := hEle.trans_lt (hN₀ p (by omega))
  have hE0 : E = 0 := by
    rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs, ← Int.cast_abs] at hlt
    exact Int.abs_lt_one_iff.mp (by exact_mod_cast hlt)
  -- `p ∣ 4 nₚ N^{4p}`, impossible
  have hpZ := Nat.prime_iff_prime_int.mp hp
  have hdvd : (p : ℤ) ∣ 4 * nₚ * N ^ (4 * p) := ⟨M, by linear_combination hE0⟩
  rcases hpZ.dvd_or_dvd hdvd with h2 | h2
  · rcases hpZ.dvd_or_dvd h2 with h3 | h3
    · have h5 : p ∣ 4 := by
        have := Int.natAbs_dvd_natAbs.mpr h3
        simpa using this
      have := Nat.le_of_dvd (by norm_num) h5
      omega
    · exact hnp h3
  · have h3 := hpZ.dvd_of_dvd_pow h2
    have h5 : p ∣ N.natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr h3
      simpa using this
    have := Nat.le_of_dvd (Int.natAbs_pos.mpr hN0) h5
    omega

/-- `cos r · cosh x ≠ 1` for rationals `r` and `x ≠ 0`. -/
theorem cos_rat_mul_cosh_rat_ne_one (r : ℚ) {x : ℚ} (hx : x ≠ 0) :
    Real.cos r * Real.cosh x ≠ 1 := by
  intro h
  have hrd : (0 : ℤ) < r.den := by exact_mod_cast r.den_pos
  have hxd : (0 : ℤ) < x.den := by exact_mod_cast x.den_pos
  refine cos_mul_cosh_ne_one (a := x.num * r.den) (b := r.num * x.den) (N := r.den * x.den)
    (mul_ne_zero (Rat.num_ne_zero.mpr hx) hrd.ne') (mul_pos hrd hxd) ?_
  have hr' : (r : ℝ) = ((r.num * x.den : ℤ) : ℝ) / ((r.den * x.den : ℤ) : ℝ) := by
    have hxd' : (x.den : ℝ) ≠ 0 := by exact_mod_cast x.den_pos.ne'
    have hrd' : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_pos.ne'
    rw [Rat.cast_def r]
    push_cast
    field_simp
  have hx' : (x : ℝ) = ((x.num * r.den : ℤ) : ℝ) / ((r.den * x.den : ℤ) : ℝ) := by
    have hxd' : (x.den : ℝ) ≠ 0 := by exact_mod_cast x.den_pos.ne'
    have hrd' : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_pos.ne'
    rw [Rat.cast_def x]
    push_cast
    field_simp
  rw [← hr', ← hx']
  exact h

/-- **The Gudermannian of a nonzero rational is irrational.** -/
theorem irrational_gd_rat {q : ℚ} (hq : q ≠ 0) : Irrational (DLMF.gd q) := by
  rintro ⟨r, hr⟩
  apply cos_rat_mul_cosh_rat_ne_one r hq
  rw [hr, (DLMF.gd_trig q).2.2]
  exact one_div_mul_cancel (Real.cosh_pos _).ne'

end Azurite
