/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Transcendental.DigammaStirling
import Azurite.DLMF.Chapter5.Section15Asymp

/-!
# The polygamma functions on the real line: series, recurrence, asymptotic series

`polygammaR n x` is `ψ⁽ⁿ⁾(x)` for a real `x` (the real part of `DLMF.polygamma n x`, which is
real off the poles: `polygamma_ofReal`).  For `n ≥ 1`:

* `hasSum_polygammaR` (DLMF 5.15.1): `ψ⁽ⁿ⁾(x) = (−1)ⁿ⁺¹ n! ∑_{k≥0} (k + x)^{−n−1}`;
* `polygammaR_add_nat` (DLMF 5.15.5):
  `ψ⁽ⁿ⁾(x) = ψ⁽ⁿ⁾(x + K) + (−1)ⁿ⁺¹ n! ∑_{j<K} (x + j)^{−n−1}`;
* `polygammaR_eq_sum_add` (DLMF 5.15.8–5.15.9 with a remainder): for `x > 0` and `N ≥ 1`,

    `(−1)ⁿ⁺¹ ψ⁽ⁿ⁾(x) = (n − 1)!/xⁿ + n!/(2 xⁿ⁺¹) + ∑_{k=1}^{N−1} u_k(x) + r`,
    `u_k(x) = (−1)^(k+1) c_k (2k)(2k + 1) ⋯ (2k + n − 1) / x^(2k+n)`,

  with the coefficients `c_k = T_k/(4^(2k) − 2^(2k)) = |B_{2k}|/(2k)` of the series of `ψ`
  (`psiCoeffT`), and a remainder `r` that has the sign of the first omitted term and is at
  most that term in magnitude.  The remainder is `DLMF.polygamma_eq_expansion`'s integral of
  the periodic Bernoulli function, rewritten with `B̃_{2N} − B_{2N}`, which has a constant
  sign (`DLMF.bernDIntegral_nonneg`), as for `ψ` in `DLMF/Chapter5/Section11Bounds.lean`.
-/

namespace Azurite

open Finset
open scoped Nat

/-- `ψ⁽ⁿ⁾(x)` for a real `x`. -/
noncomputable def polygammaR (n : ℕ) (x : ℝ) : ℝ := (DLMF.polygamma n (x : ℂ)).re

theorem not_mem_gammaPoles_ofReal {x : ℝ} (hx : ∀ m : ℕ, x ≠ -m) :
    (x : ℂ) ∉ DLMF.gammaPoles := by
  rw [DLMF.not_mem_gammaPoles]
  intro m hm
  exact hx m (by exact_mod_cast hm)

/-- **DLMF 5.15.1** on the real line: `ψ⁽ⁿ⁾(x) = (−1)ⁿ⁺¹ n! ∑_{k≥0} (k + x)^{−n−1}`. -/
theorem hasSum_polygammaR {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : ∀ m : ℕ, x ≠ -m) :
    HasSum (fun k : ℕ => (-1) ^ (n + 1) * (n ! : ℝ) / ((k : ℝ) + x) ^ (n + 1))
      (polygammaR n x) := by
  have h := Complex.hasSum_re (DLMF.hasSum_polygamma hn (not_mem_gammaPoles_ofReal hx))
  have e : (fun k : ℕ => (-1) ^ (n + 1) * (n ! : ℝ) / ((k : ℝ) + x) ^ (n + 1))
      = fun k : ℕ => ((-1) ^ (n + 1) * (n ! : ℂ) / ((k : ℂ) + (x : ℂ)) ^ (n + 1)).re := by
    funext k
    rw [show (-1) ^ (n + 1) * (n ! : ℂ) / ((k : ℂ) + (x : ℂ)) ^ (n + 1)
      = (((-1) ^ (n + 1) * (n ! : ℝ) / ((k : ℝ) + x) ^ (n + 1) : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_re]
  rw [e]
  exact h

/-- `ψ⁽ⁿ⁾` is real on the real line, off the poles. -/
theorem polygamma_ofReal {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : ∀ m : ℕ, x ≠ -m) :
    DLMF.polygamma n (x : ℂ) = (polygammaR n x : ℂ) := by
  have h := DLMF.hasSum_polygamma hn (not_mem_gammaPoles_ofReal hx)
  have h' := Complex.hasSum_ofReal.mpr (hasSum_polygammaR hn hx)
  refine h.unique ?_
  convert h' using 1
  funext k
  push_cast
  ring

/-- **DLMF 5.15.5** on the real line. -/
theorem polygammaR_add_one {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : ∀ m : ℕ, x ≠ -m) :
    polygammaR n x = polygammaR n (x + 1) + (-1) ^ (n + 1) * (n ! : ℝ) / x ^ (n + 1) := by
  have hx1 : ∀ m : ℕ, x + 1 ≠ -m := fun m hm => hx (m + 1) (by push_cast; linarith)
  have h := hasSum_polygammaR hn hx
  have h1 := hasSum_polygammaR hn hx1
  have h' := (hasSum_nat_add_iff' 1).mpr h
  rw [sum_range_one] at h'
  have : polygammaR n (x + 1)
      = polygammaR n x - (-1) ^ (n + 1) * (n ! : ℝ) / (((0 : ℕ) : ℝ) + x) ^ (n + 1) := by
    refine h1.unique ?_
    convert h' using 1
    funext k
    push_cast
    ring_nf
  rw [this, Nat.cast_zero, zero_add]
  ring

/-- **The recurrence, `K` steps**:
`ψ⁽ⁿ⁾(x) = ψ⁽ⁿ⁾(x + K) + (−1)ⁿ⁺¹ n! ∑_{j<K} (x + j)^{−n−1}`. -/
theorem polygammaR_add_nat {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : ∀ m : ℕ, x ≠ -m) (K : ℕ) :
    polygammaR n x = polygammaR n (x + K)
      + (-1) ^ (n + 1) * (n ! : ℝ) * ∑ j ∈ range K, 1 / (x + j) ^ (n + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hxK : ∀ m : ℕ, x + K ≠ -m := fun m hm => hx (m + K) (by push_cast; linarith)
    rw [ih, polygammaR_add_one hn hxK, sum_range_succ]
    push_cast
    ring_nf

/-- **Negative arguments without a reflection formula**: for `x` not an integer and `m : ℕ`,
`ψ⁽ⁿ⁾(x) = ψ⁽ⁿ⁾(x + m) + (−1)ⁿ (ψ⁽ⁿ⁾(1 − x) − ψ⁽ⁿ⁾(1 − x − m))` — the two finite sums of the
recurrence at `x` and at `1 − x − m` are the same up to the sign `(−1)ⁿ⁺¹`.  (The combination
`(−1)ⁿ ψ⁽ⁿ⁾(1 − x) − ψ⁽ⁿ⁾(x)` has period `1`: it is `π dⁿ cot(πx)/dxⁿ` up to sign, DLMF
5.15.6.)  With `x + m`, `1 − x` and `1 − x − m` positive, it reduces a negative argument to
three positive ones at a cost that does not depend on `|x|`. -/
theorem polygammaR_reflect {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : ∀ k : ℤ, x ≠ k) (m : ℕ) :
    polygammaR n x = polygammaR n (x + m)
      + (-1) ^ n * (polygammaR n (1 - x) - polygammaR n (1 - x - m)) := by
  have hx1 : ∀ k : ℕ, x ≠ -k := fun k hk => hx (-(k : ℤ)) (by push_cast; exact hk)
  have hx2 : ∀ k : ℕ, 1 - x - m ≠ -k := fun k hk =>
    hx ((1 : ℤ) - m + k) (by push_cast; linarith)
  have h1 := polygammaR_add_nat hn hx1 m
  have h2 := polygammaR_add_nat hn hx2 m
  rw [show 1 - x - (m : ℝ) + m = 1 - x by ring] at h2
  have hsum : ∑ j ∈ range m, 1 / (1 - x - m + (j : ℝ)) ^ (n + 1)
      = (-1) ^ (n + 1) * ∑ j ∈ range m, 1 / (x + j) ^ (n + 1) := by
    rw [← sum_range_reflect, mul_sum]
    refine sum_congr rfl fun j hj => ?_
    have hjm : j + 1 ≤ m := mem_range.mp hj
    rw [Nat.sub_sub, Nat.cast_sub (by omega : 1 + j ≤ m),
      show 1 - x - (m : ℝ) + ((m : ℝ) - ((1 + j : ℕ) : ℝ)) = -(x + j) by push_cast; ring, neg_pow]
    have hne : (x + (j : ℝ)) ^ (n + 1) ≠ 0 := pow_ne_zero _ fun h0 =>
      hx1 j (by linarith)
    have hs : ((-1 : ℝ) ^ (n + 1)) * (-1) ^ (n + 1) = 1 := by rw [← mul_pow]; norm_num
    field_simp
    linear_combination -hs
  rw [hsum] at h2
  have he : ((-1 : ℝ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
  generalize ∑ j ∈ range m, 1 / (x + (j : ℝ)) ^ (n + 1) = S at h1 h2
  rw [pow_succ] at h1 h2
  linear_combination h1 + (-1) ^ n * h2 + (-1) ^ n * (n ! : ℝ) * S * he

/-- **Negative arguments by the recurrence, in positive terms**: for `x` not an integer,
`ψ⁽ⁿ⁾(x) = ψ⁽ⁿ⁾(x + m) + n! ∑_{j<m} (1 − x − m + j)^{−n−1}` — the recurrence at `x`, whose
terms `(x + j)^{−n−1}` are those at `1 − x − m` reversed, up to the sign `(−1)ⁿ⁺¹`. -/
theorem polygammaR_neg_sum {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : ∀ k : ℤ, x ≠ k) (m : ℕ) :
    polygammaR n x = polygammaR n (x + m)
      + (n ! : ℝ) * ∑ j ∈ range m, 1 / (1 - x - m + (j : ℝ)) ^ (n + 1) := by
  have hx1 : ∀ k : ℕ, x ≠ -k := fun k hk => hx (-(k : ℤ)) (by push_cast; exact hk)
  have h1 := polygammaR_add_nat hn hx1 m
  have hsum : ∑ j ∈ range m, 1 / (1 - x - m + (j : ℝ)) ^ (n + 1)
      = (-1) ^ (n + 1) * ∑ j ∈ range m, 1 / (x + j) ^ (n + 1) := by
    rw [← sum_range_reflect, mul_sum]
    refine sum_congr rfl fun j hj => ?_
    have hjm : j + 1 ≤ m := mem_range.mp hj
    rw [Nat.sub_sub, Nat.cast_sub (by omega : 1 + j ≤ m),
      show 1 - x - (m : ℝ) + ((m : ℝ) - ((1 + j : ℕ) : ℝ)) = -(x + j) by push_cast; ring, neg_pow]
    have hne : (x + (j : ℝ)) ^ (n + 1) ≠ 0 := pow_ne_zero _ fun h0 =>
      hx1 j (by linarith)
    have hs : ((-1 : ℝ) ^ (n + 1)) * (-1) ^ (n + 1) = 1 := by rw [← mul_pow]; norm_num
    field_simp
    linear_combination -hs
  rw [hsum]
  linear_combination h1

/-! ### The asymptotic series with its remainder -/

/-- The remainder of the expansion of `ψ⁽ⁿ⁾` after the powers `z^{−s}`, `s < n + 2N`. -/
noncomputable def polyStirRem (n N : ℕ) (z : ℂ) : ℂ :=
  DLMF.polygamma n z - ∑ s ∈ range (n + 2 * N), DLMF.polygammaCoeff n s * z ^ (-(s : ℤ))

/-- `(2N + 1)(2N + 2) ⋯ (2N + n)`. -/
noncomputable def polyRemFactor (n N : ℕ) : ℝ := ((2 * N + 1).ascFactorial n : ℝ)

theorem polyRemFactor_pos (n N : ℕ) : 0 < polyRemFactor n N := by
  unfold polyRemFactor
  exact_mod_cast Nat.ascFactorial_pos _ _

theorem prod_neg_sub_eq (n N : ℕ) :
    ∏ i ∈ range n, (-((2 * N + 1 : ℕ) : ℂ) - i) = (-1) ^ n * (polyRemFactor n N : ℂ) := by
  have e : ∀ i ∈ range n, (-((2 * N + 1 : ℕ) : ℂ) - i) = (-1) * (((2 * N + 1 + i : ℕ) : ℂ)) :=
    fun i _ => by push_cast; ring
  rw [prod_congr rfl e, prod_mul_distrib, prod_const, card_range, polyRemFactor,
    Nat.ascFactorial_eq_prod_range]
  push_cast
  rfl

/-- `(2N + n − 1)!/(2N)! · (2N + n) = (2N + 1) ⋯ (2N + n)`. -/
theorem factorial_div_mul_eq {n : ℕ} (hn : 1 ≤ n) (N : ℕ) :
    ((2 * N + n - 1)! : ℝ) / ((2 * N)! : ℝ) * (2 * N + n) = polyRemFactor n N := by
  have h := Nat.factorial_mul_ascFactorial (2 * N) n
  have h2 : (2 * N + n)! = (2 * N + n) * (2 * N + n - 1)! := by
    conv_lhs => rw [show 2 * N + n = (2 * N + n - 1) + 1 by omega, Nat.factorial_succ]
    rw [show 2 * N + n - 1 + 1 = 2 * N + n by omega]
  have hf : ((2 * N)! : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hr : ((2 * N)! : ℝ) * polyRemFactor n N = (2 * N + n) * ((2 * N + n - 1)! : ℝ) := by
    unfold polyRemFactor
    exact_mod_cast h.trans h2
  field_simp
  linarith

/-- **The remainder as an integral of `B̃_{2N} − B_{2N}`**:
`(−1)ⁿ (2N+1) ⋯ (2N+n) ∫₀^∞ (B̃_{2N}(t) − B_{2N})/(z + t)^{2N+1+n} dt`. -/
theorem polyStirRem_eq {n : ℕ} (hn : 1 ≤ n) {N : ℕ} (hN : 1 ≤ N) {z : ℂ}
    (hz : z ∈ Complex.slitPlane) :
    polyStirRem n N z = (-1) ^ n * (polyRemFactor n N : ℂ) *
      ∫ t in Set.Ioi (0 : ℝ), (DLMF.bernD N t : ℂ) / (z + t) ^ (2 * N + 1 + n) := by
  have hz0 := Complex.slitPlane_ne_zero hz
  obtain ⟨m, hm⟩ : ∃ m, 2 * N = m + 2 := ⟨2 * N - 2, by omega⟩
  have hE := DLMF.polygamma_eq_expansion hn hz m
  rw [show n + (m + 3) = n + 2 * N + 1 by omega, sum_range_succ, show m + 3 = 2 * N + 1 by omega,
    prod_neg_sub_eq, show n + 2 * N = 2 * N + n by omega, DLMF.polygammaCoeff_even hn hN] at hE
  have hR : DLMF.polyRem m (2 * N + 1 + n) z
      = ∫ t in Set.Ioi (0 : ℝ),
        (DLMF.periodicBernoulli (2 * N) t : ℂ) / (z + t) ^ (2 * N + 1 + n) := by
    rw [DLMF.polyRem, hm]
  have hfac := factorial_div_mul_eq hn N
  have hpn : (-1 : ℂ) ^ (n - 1) = -(-1) ^ n := by
    conv_rhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
    ring
  have hzp : z ^ (2 * N + n) ≠ 0 := pow_ne_zero _ hz0
  have hc : (((2 * N + 1 + n : ℕ) : ℂ) - 1) ≠ 0 := by
    have : (0 : ℝ) < ((2 * N + 1 + n : ℕ) : ℝ) - 1 := by
      rw [show ((2 * N + 1 + n : ℕ) : ℝ) - 1 = 2 * (N : ℝ) + n by push_cast; ring]
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN
      positivity
    exact_mod_cast this.ne'
  have hfacC : ((2 * N + n - 1)! : ℂ) / ((2 * N)! : ℂ) * (((2 * N + 1 + n : ℕ) : ℂ) - 1)
      = (polyRemFactor n N : ℂ) := by
    rw [← hfac]
    push_cast
    ring
  rw [polyStirRem, DLMF.integral_div_add_pow_split N hz (by omega), ← hR, hE,
    show n + 2 * N = 2 * N + n by omega, show 2 * N + 1 + n - 1 = 2 * N + n by omega, hpn,
    zpow_neg, zpow_natCast, ← hfacC]
  generalize ((2 * N + n - 1)! : ℂ) / ((2 * N)! : ℂ) = F
  generalize (((2 * N + 1 + n : ℕ) : ℂ) - 1) = c at hc ⊢
  generalize z ^ (2 * N + n) = Z at hzp ⊢
  generalize DLMF.polyRem m (2 * N + 1 + n) z = I
  generalize (bernoulli (2 * N) : ℂ) = B
  generalize (-1 : ℂ) ^ n = e
  field_simp
  ring

/-- The term of index `k ≥ 1` of the series of `(−1)ⁿ⁺¹ ψ⁽ⁿ⁾`:
`(−1)^(k+1) c_k (2k)(2k+1) ⋯ (2k+n−1) / x^(2k+n)`. -/
noncomputable def polyTermT (n k : ℕ) (x : ℝ) : ℝ :=
  (-1) ^ (k + 1) * psiCoeffT k * ((2 * k).ascFactorial n : ℝ) / x ^ (2 * k + n)

/-- `(2k + n − 1)!/(2k)! · 2k = (2k)(2k + 1) ⋯ (2k + n − 1)`. -/
theorem factorial_div_mul_two {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    ((2 * k + n - 1)! : ℝ) / ((2 * k)! : ℝ) * (2 * k) = ((2 * k).ascFactorial n : ℝ) := by
  have h := Nat.factorial_mul_ascFactorial' (2 * k) n (by omega)
  have h2 : (2 * k)! = 2 * k * (2 * k - 1)! := by
    conv_lhs => rw [show 2 * k = (2 * k - 1) + 1 by omega, Nat.factorial_succ]
    rw [show 2 * k - 1 + 1 = 2 * k by omega]
  have hf : ((2 * k)! : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hf1 : ((2 * k - 1)! : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have h' : ((2 * k - 1)! : ℝ) * ((2 * k).ascFactorial n : ℝ) = ((2 * k + n - 1)! : ℝ) := by
    exact_mod_cast h
  have h2' : ((2 * k)! : ℝ) = 2 * k * ((2 * k - 1)! : ℝ) := by exact_mod_cast h2
  rw [← h', h2']
  field_simp

/-- The term of the expansion at `s = 2k + n`, on the real line. -/
theorem polygammaCoeff_mul_ofReal {n : ℕ} (hn : 1 ≤ n) {k : ℕ} (hk : 1 ≤ k) (x : ℝ) :
    DLMF.polygammaCoeff n (2 * k + n) * (x : ℂ) ^ (-((2 * k + n : ℕ) : ℤ))
      = (((-1) ^ (n + 1) * polyTermT n k x : ℝ) : ℂ) := by
  have hb := bernoulli_div_eq_psiCoeffT hk
  have hk0 : (2 * (k : ℝ)) ≠ 0 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hB : (bernoulli (2 * k) : ℝ) = (-1) ^ (k + 1) * psiCoeffT k * (2 * k) := by
    rw [← hb]; field_simp
  have hpn : (-1 : ℝ) ^ (n - 1) = (-1) ^ (n + 1) := by
    conv_rhs => rw [show n + 1 = (n - 1) + 2 by omega, pow_add]
    norm_num
  rw [DLMF.polygammaCoeff_even hn hk, zpow_neg, zpow_natCast]
  rw [show ((-1 : ℂ) ^ (n - 1) * (((2 * k + n - 1)! : ℂ) / ((2 * k)! : ℂ))
      * (bernoulli (2 * k) : ℂ) * ((x : ℂ) ^ (2 * k + n))⁻¹)
    = (((-1 : ℝ) ^ (n - 1) * (((2 * k + n - 1)! : ℝ) / ((2 * k)! : ℝ))
      * (bernoulli (2 * k) : ℝ) * (x ^ (2 * k + n))⁻¹ : ℝ) : ℂ) by push_cast; ring]
  congr 1
  rw [hB, hpn, polyTermT, ← factorial_div_mul_two hk n]
  ring

theorem polyStirRem_succ (n : ℕ) {N : ℕ} (hN : 1 ≤ N) (z : ℂ) :
    polyStirRem n N z = DLMF.polygammaCoeff n (2 * N + n) * z ^ (-((2 * N + n : ℕ) : ℤ))
      + polyStirRem n (N + 1) z := by
  rw [polyStirRem, polyStirRem, show n + 2 * (N + 1) = 2 * N + n + 1 + 1 by omega,
    sum_range_succ, sum_range_succ, show 2 * N + n + 1 = 2 * N + 1 + n by omega,
    DLMF.polygammaCoeff_odd hN, show n + 2 * N = 2 * N + n by omega]
  ring

theorem polyStirRem_ofReal {n : ℕ} (hn : 1 ≤ n) {N : ℕ} (hN : 1 ≤ N) {x : ℝ} (hx : 0 < x) :
    polyStirRem n N x = (((-1) ^ (n + N) * polyRemFactor n N
      * DLMF.bernDIntegral N (2 * N + 1 + n) x : ℝ) : ℂ) := by
  rw [polyStirRem_eq hn hN (DLMF.ofReal_mem_slitPlane' hx), DLMF.integral_bernD_ofReal]
  push_cast
  ring

/-- The remainder after the two leading terms. -/
theorem polyStirRem_one {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    polyStirRem n 1 x = ((polygammaR n x - (-1) ^ (n + 1)
      * (((n - 1)! : ℝ) / x ^ n + (n ! : ℝ) / (2 * x ^ (n + 1))) : ℝ) : ℂ) := by
  have hxp : ∀ m : ℕ, x ≠ -m := fun m hm => by
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hlow : ∑ s ∈ range n, DLMF.polygammaCoeff n s * (x : ℂ) ^ (-(s : ℤ)) = 0 :=
    sum_eq_zero fun s hs => by rw [DLMF.polygammaCoeff_lt (mem_range.mp hs), zero_mul]
  have hpn : (-1 : ℂ) ^ (n - 1) = (-1) ^ (n + 1) := by
    conv_rhs => rw [show n + 1 = (n - 1) + 2 by omega, pow_add]
    norm_num
  rw [polyStirRem, show n + 2 * 1 = n + 1 + 1 by omega, sum_range_succ, sum_range_succ, hlow,
    DLMF.polygammaCoeff_self, DLMF.polygammaCoeff_succ hn, polygamma_ofReal hn hxp, hpn,
    zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
  push_cast
  ring

/-- **The asymptotic series of `ψ⁽ⁿ⁾` with its remainder**: for `x > 0`, `n ≥ 1`, `N ≥ 1`,
`(−1)ⁿ⁺¹ ψ⁽ⁿ⁾(x) = (n−1)!/xⁿ + n!/(2xⁿ⁺¹) + ∑_{i<N−1} u_{i+1}(x) + r` with
`0 ≤ (−1)^(N+1) r` and `|r| ≤ c_N (2N) ⋯ (2N+n−1) / x^(2N+n)`. -/
theorem polygammaR_eq_sum_add {n : ℕ} (hn : 1 ≤ n) {N : ℕ} (hN : 1 ≤ N) {x : ℝ} (hx : 0 < x) :
    ∃ r : ℝ, (-1) ^ (n + 1) * polygammaR n x
        = ((n - 1)! : ℝ) / x ^ n + (n ! : ℝ) / (2 * x ^ (n + 1))
          + ∑ i ∈ range (N - 1), polyTermT n (i + 1) x + r ∧
      0 ≤ (-1) ^ (N + 1) * r ∧
      |r| ≤ psiCoeffT N * ((2 * N).ascFactorial n : ℝ) / x ^ (2 * N + n) := by
  have hsq : ∀ k : ℕ, ((-1 : ℝ) ^ k) * (-1) ^ k = 1 := fun k => by rw [← mul_pow]; norm_num
  -- the remainder as a real number, by induction on `N`
  have hrem : ∀ N : ℕ, 1 ≤ N → polyStirRem n N x = (((-1) ^ (n + 1) * ((-1) ^ (n + 1)
      * polygammaR n x - (((n - 1)! : ℝ) / x ^ n + (n ! : ℝ) / (2 * x ^ (n + 1))
        + ∑ i ∈ range (N - 1), polyTermT n (i + 1) x)) : ℝ) : ℂ) := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base =>
      rw [polyStirRem_one hn hx, Nat.sub_self, range_zero, sum_empty, add_zero]
      congr 1
      linear_combination (polygammaR n x) * (hsq (n + 1)).symm
    | succ N hN ih =>
      have hs := polyStirRem_succ n hN (x : ℂ)
      rw [ih, polygammaCoeff_mul_ofReal hn hN] at hs
      have e : polyStirRem n (N + 1) x = (((-1) ^ (n + 1) * ((-1) ^ (n + 1)
          * polygammaR n x - (((n - 1)! : ℝ) / x ^ n + (n ! : ℝ) / (2 * x ^ (n + 1))
            + ∑ i ∈ range (N - 1), polyTermT n (i + 1) x)) : ℝ) : ℂ)
          - (((-1) ^ (n + 1) * polyTermT n N x : ℝ) : ℂ) := by
        rw [hs]; ring
      rw [e, ← Complex.ofReal_sub, show N + 1 - 1 = (N - 1) + 1 by omega, sum_range_succ,
        show N - 1 + 1 = N by omega]
      congr 1
      ring
  have hR := hrem N hN
  have hR' := hrem (N + 1) (by omega)
  have hI := DLMF.bernDIntegral_nonneg hN (2 * N + 1 + n) hx
  have hI' := DLMF.bernDIntegral_nonneg (n := N + 1) (by omega) (2 * (N + 1) + 1 + n) hx
  have hPi := polyRemFactor_pos n N
  have hPi' := polyRemFactor_pos n (N + 1)
  rw [polyStirRem_ofReal hn hN hx, Complex.ofReal_inj] at hR
  rw [polyStirRem_ofReal hn (by omega) hx, Complex.ofReal_inj, show N + 1 - 1 = (N - 1) + 1 by
    omega, sum_range_succ, show N - 1 + 1 = N by omega] at hR'
  set S := ((n - 1)! : ℝ) / x ^ n + (n ! : ℝ) / (2 * x ^ (n + 1))
    + ∑ i ∈ range (N - 1), polyTermT n (i + 1) x with hS
  set r := (-1) ^ (n + 1) * polygammaR n x - S with hr
  set A := polyRemFactor n N * DLMF.bernDIntegral N (2 * N + 1 + n) x with hA
  set A' := polyRemFactor n (N + 1) * DLMF.bernDIntegral (N + 1) (2 * (N + 1) + 1 + n) x with hA'
  have hA0 : 0 ≤ A := mul_nonneg hPi.le hI
  have hA0' : 0 ≤ A' := mul_nonneg hPi'.le hI'
  -- `r = (−1)^(N+1) A` and `r − u_N = (−1)^N A'`
  have h1 : r = (-1) ^ (N + 1) * A := by
    have : (-1 : ℝ) ^ (n + 1) * ((-1) ^ (n + N) * A) = (-1) ^ (N + 1) * A := by
      rw [← mul_assoc, ← pow_add, show n + 1 + (n + N) = 2 * n + (N + 1) by ring, pow_add,
        pow_mul]
      norm_num
    rw [← this, show (-1 : ℝ) ^ (n + N) * A = (-1) ^ (n + N) * polyRemFactor n N
      * DLMF.bernDIntegral N (2 * N + 1 + n) x by rw [hA]; ring, hR]
    linear_combination (-(r)) * (hsq (n + 1))
  have h2 : r - polyTermT n N x = (-1) ^ N * A' := by
    have : (-1 : ℝ) ^ (n + 1) * ((-1) ^ (n + (N + 1)) * A') = (-1) ^ N * A' := by
      rw [← mul_assoc, ← pow_add, show n + 1 + (n + (N + 1)) = 2 * (n + 1) + N by ring, pow_add,
        pow_mul]
      norm_num
    rw [← this, show (-1 : ℝ) ^ (n + (N + 1)) * A' = (-1) ^ (n + (N + 1)) * polyRemFactor n (N + 1)
      * DLMF.bernDIntegral (N + 1) (2 * (N + 1) + 1 + n) x by rw [hA']; ring, hR']
    linear_combination (-(r - polyTermT n N x)) * (hsq (n + 1))
  have hc := psiCoeffT_pos hN
  have hasc : (0 : ℝ) < ((2 * N).ascFactorial n : ℝ) := by
    have := Nat.ascFactorial_pos (2 * N - 1) n
    rw [show 2 * N - 1 + 1 = 2 * N by omega] at this
    exact Nat.cast_pos.mpr this
  have hq : 0 < psiCoeffT N * ((2 * N).ascFactorial n : ℝ) / x ^ (2 * N + n) :=
    div_pos (mul_pos hc hasc) (pow_pos hx _)
  have hu : polyTermT n N x
      = (-1) ^ (N + 1) * (psiCoeffT N * ((2 * N).ascFactorial n : ℝ) / x ^ (2 * N + n)) := by
    rw [polyTermT]; ring
  refine ⟨r, by rw [hr]; ring, ?_, ?_⟩
  · rw [h1, ← mul_assoc, hsq, one_mul]
    exact hA0
  · -- `(−1)^(N+1) r = A ≥ 0` and `(−1)^(N+1) (r − u_N) = −A' ≤ 0`
    have e1 : (-1 : ℝ) ^ (N + 1) * r = A := by rw [h1, ← mul_assoc, hsq, one_mul]
    have e2 : (-1 : ℝ) ^ (N + 1) * (r - polyTermT n N x) = -A' := by
      rw [h2, pow_succ, show (-1 : ℝ) ^ N * -1 * ((-1) ^ N * A') = -((-1) ^ N * (-1) ^ N * A') by
        ring, hsq, one_mul]
    rw [hu, mul_sub, ← mul_assoc, hsq, one_mul] at e2
    have habs : |r| = A := by
      rw [h1, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg hA0]
    rw [habs]
    linarith

/-! ### The scaled form used by the enclosures -/

/-- `xⁿ (−1)ⁿ⁺¹ ψ⁽ⁿ⁾(x) − (n − 1)! − n!/(2x)`: what the series of `polyVTerm` sums to. -/
noncomputable def polyNu (n : ℕ) (x : ℝ) : ℝ :=
  x ^ n * ((-1) ^ (n + 1) * polygammaR n x) - ((n - 1)! : ℝ) - (n ! : ℝ) / (2 * x)

/-- The term of index `k ≥ 1` of the series of `polyNu`:
`(−1)^(k+1) c_k (2k) ⋯ (2k+n−1) / x^(2k)`. -/
noncomputable def polyVTerm (n k : ℕ) (x : ℝ) : ℝ :=
  (-1) ^ (k + 1) * (psiCoeffT k * ((2 * k).ascFactorial n : ℝ) / x ^ (2 * k))

/-- **The scaled series with its remainder**: `polyNu n x = ∑_{i<N−1} v_{i+1}(x) + r` with
`0 ≤ (−1)^(N+1) r` and `|r| ≤ c_N (2N) ⋯ (2N+n−1) / x^(2N)`. -/
theorem polyNu_eq_sum_add {n : ℕ} (hn : 1 ≤ n) {N : ℕ} (hN : 1 ≤ N) {x : ℝ} (hx : 0 < x) :
    ∃ r : ℝ, polyNu n x = ∑ i ∈ range (N - 1), polyVTerm n (i + 1) x + r ∧
      0 ≤ (-1) ^ (N + 1) * r ∧
      |r| ≤ psiCoeffT N * ((2 * N).ascFactorial n : ℝ) / x ^ (2 * N) := by
  obtain ⟨r, hr, hsign, habs⟩ := polygammaR_eq_sum_add hn hN hx
  have hxn : 0 < x ^ n := pow_pos hx n
  have hterm : ∀ k : ℕ, x ^ n * polyTermT n k x = polyVTerm n k x := fun k => by
    have h1 : x ^ (2 * k + n) = x ^ (2 * k) * x ^ n := pow_add x _ _
    have h2 : x ^ (2 * k) ≠ 0 := (pow_pos hx _).ne'
    rw [polyTermT, polyVTerm, h1]
    field_simp
  refine ⟨x ^ n * r, ?_, ?_, ?_⟩
  · rw [polyNu, hr, ← sum_congr rfl (fun i _ => hterm (i + 1)), ← mul_sum]
    rw [pow_succ x n]
    field_simp
    ring
  · rw [show (-1 : ℝ) ^ (N + 1) * (x ^ n * r) = x ^ n * ((-1) ^ (N + 1) * r) by ring]
    exact mul_nonneg hxn.le hsign
  · rw [abs_mul, abs_of_pos hxn]
    calc x ^ n * |r| ≤ x ^ n * (psiCoeffT N * ((2 * N).ascFactorial n : ℝ) / x ^ (2 * N + n)) :=
          mul_le_mul_of_nonneg_left habs hxn.le
      _ = psiCoeffT N * ((2 * N).ascFactorial n : ℝ) / x ^ (2 * N) := by
          have h1 : x ^ (2 * N + n) = x ^ (2 * N) * x ^ n := pow_add x _ _
          have h2 : x ^ (2 * N) ≠ 0 := (pow_pos hx _).ne'
          rw [h1]; field_simp

/-! ### Next to the pole at `0` -/

/-- **`ψ⁽ⁿ⁾` at its pole `0`**: for `0 < |x| ≤ 1/4`,
`(−1)ⁿ⁺¹ ψ⁽ⁿ⁾(x) = n!/xⁿ⁺¹ + t` with `0 < t ≤ 2ⁿ⁺² (n + 1)!` — `t = (−1)ⁿ⁺¹ ψ⁽ⁿ⁾(x + 1)`, bounded
by the first terms of its asymptotic series. -/
theorem polygammaR_near_zero {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx0 : x ≠ 0) (hx : |x| ≤ 1 / 4) :
    ∃ t : ℝ, (-1) ^ (n + 1) * polygammaR n x = (n ! : ℝ) / x ^ (n + 1) + t ∧
      0 < t ∧ t ≤ 2 ^ (n + 2) * ((n + 1)! : ℝ) := by
  obtain ⟨hx1, hx2⟩ := abs_le.mp hx
  have hnp : ∀ m : ℕ, x ≠ -m := fun m hm => by
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · exact hx0 (by simpa using hm)
    · have : (1 : ℝ) ≤ m := by exact_mod_cast hm0
      linarith
  have hy : (0 : ℝ) < x + 1 := by linarith
  obtain ⟨r, hr, hsign, habs⟩ := polygammaR_eq_sum_add hn (N := 1) le_rfl hy
  rw [Nat.sub_self, range_zero, sum_empty, add_zero] at hr
  rw [show (-1 : ℝ) ^ (1 + 1) = 1 by norm_num, one_mul] at hsign
  have hasc : ((2 * 1).ascFactorial n : ℝ) = ((n + 1)! : ℝ) := by
    have := Nat.factorial_mul_ascFactorial 1 n
    rw [Nat.factorial_one, one_mul, show 1 + n = n + 1 by omega] at this
    exact_mod_cast this
  rw [psiCoeffT_one, hasc, abs_of_nonneg hsign] at habs
  have hs : ((-1 : ℝ) ^ (n + 1)) * (-1) ^ (n + 1) = 1 := by rw [← mul_pow]; norm_num
  refine ⟨(-1) ^ (n + 1) * polygammaR n (x + 1), ?_, ?_, ?_⟩
  · rw [polygammaR_add_one hn hnp]
    linear_combination ((n ! : ℝ) / x ^ (n + 1)) * hs
  · rw [hr]
    have h1 : (0 : ℝ) < ((n - 1)! : ℝ) / (x + 1) ^ n :=
      div_pos (by exact_mod_cast Nat.factorial_pos _) (pow_pos hy _)
    have h2 : (0 : ℝ) < (n ! : ℝ) / (2 * (x + 1) ^ (n + 1)) :=
      div_pos (by exact_mod_cast Nat.factorial_pos _) (by positivity)
    linarith
  · rw [hr]
    -- `u = 1/(x + 1) ≤ 4/3 ≤ 2`
    set u := 1 / (x + 1) with hu
    have hu0 : 0 < u := by positivity
    have hu2 : u ≤ 2 := by
      rw [hu, div_le_iff₀ hy]; linarith
    have hpow : ∀ k : ℕ, u ^ k ≤ 2 ^ k := fun k => pow_le_pow_left₀ hu0.le hu2 k
    have hupow : ∀ k : ℕ, 0 < u ^ k := fun k => pow_pos hu0 k
    have ha0 : (0 : ℝ) < ((n - 1)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hb : (n ! : ℝ) = n * ((n - 1)! : ℝ) := by
      have : n ! = n * (n - 1)! := by
        conv_lhs => rw [show n = (n - 1) + 1 by omega, Nat.factorial_succ]
        rw [show n - 1 + 1 = n by omega]
      exact_mod_cast this
    have hF : ((n + 1)! : ℝ) = (n + 1) * (n ! : ℝ) := by
      exact_mod_cast Nat.factorial_succ n
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hb0 : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hab : ((n - 1)! : ℝ) ≤ (n ! : ℝ) := by rw [hb]; nlinarith
    have hbF : 2 * (n ! : ℝ) ≤ ((n + 1)! : ℝ) := by rw [hF]; nlinarith
    have hF0 : (0 : ℝ) < ((n + 1)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have e1 : ((n - 1)! : ℝ) / (x + 1) ^ n = ((n - 1)! : ℝ) * u ^ n := by
      rw [hu, one_div, inv_pow, div_eq_mul_inv]
    have e2 : (n ! : ℝ) / (2 * (x + 1) ^ (n + 1)) = (n ! : ℝ) / 2 * u ^ (n + 1) := by
      rw [hu, one_div, inv_pow]; field_simp
    have e3 : (1 : ℝ) / 12 * ((n + 1)! : ℝ) / (x + 1) ^ (2 * 1 + n)
        = ((n + 1)! : ℝ) / 12 * u ^ (n + 2) := by
      rw [show 2 * 1 + n = n + 2 by omega, hu, one_div_pow]; field_simp
    rw [e3] at habs
    rw [e1, e2]
    have t1 : ((n - 1)! : ℝ) * u ^ n ≤ ((n + 1)! : ℝ) / 2 * 2 ^ n :=
      mul_le_mul (by linarith) (hpow n) (hupow n).le (by linarith)
    have t2 : (n ! : ℝ) / 2 * u ^ (n + 1) ≤ ((n + 1)! : ℝ) / 4 * 2 ^ (n + 1) :=
      mul_le_mul (by linarith) (hpow (n + 1)) (hupow (n + 1)).le (by linarith)
    have t3 : ((n + 1)! : ℝ) / 12 * u ^ (n + 2) ≤ ((n + 1)! : ℝ) / 12 * 2 ^ (n + 2) :=
      mul_le_mul_of_nonneg_left (hpow (n + 2)) (by linarith)
    have hp : (0 : ℝ) < 2 ^ n := by positivity
    have hprod : (0 : ℝ) < ((n + 1)! : ℝ) * 2 ^ n := mul_pos hF0 hp
    have p1 : (2 : ℝ) ^ (n + 1) = 2 ^ n * 2 := pow_succ _ _
    have p2 : (2 : ℝ) ^ (n + 2) = 2 ^ n * 4 := by rw [pow_add]; norm_num
    rw [p1] at t2
    rw [p2] at t3 ⊢
    have hsum : ((n + 1)! : ℝ) / 2 * 2 ^ n + ((n + 1)! : ℝ) / 4 * (2 ^ n * 2)
        + ((n + 1)! : ℝ) / 12 * (2 ^ n * 4) ≤ 2 ^ n * 4 * ((n + 1)! : ℝ) := by
      nlinarith [hprod]
    linarith

end Azurite
