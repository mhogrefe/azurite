/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BrentZimmermann.Chapter4.LegendreRelation

/-!
# Brent–Zimmermann §4.8.2 (continued): Gauss's formula for `E` along the AGM

The ingredient of the Brent–Salamin algorithm for `π` that the text leaves implicit: with the
AGM iteration `(a_j, b_j)` started at `(a, b)`, `0 < b ≤ a`, and `c_j² = a_j² − b_j²`, the
second-kind integral `J(a, b) = ∫_0^{π/2} √(a² cos²θ + b² sin²θ) dθ` is

  `J(a, b) = (a² − ∑_{j≥0} 2^(j−1) c_j²) · π/(2 AGM(a, b))`     (`agmJ_eq_tsum`),

so for `a = 1`, `b = k' = √(1 − k²)`: `E(k) = (1 − ∑_{j≥0} 2^(j−1) c_j²) K(k)`
(`ellipticE_eq_AGM_sum`).  Combined with the Legendre relation at `k = 1/√2`
(`legendre_relation_sqrt_half`) and Gauss's theorem (`one_div_AGM_one`) this gives Salamin's
formula `π = 4 AGM(1, 1/√2)²/(1 − ∑_{j≥1} 2^(j+1) c_j²)`.

The proof avoids a second change of variables.  Write `f(x) = I(1, x)`, `g(x) = J(1, x)` for the
one-parameter integrals (`agmK`, `agmE`); for `x ∈ (0, 1)` they are `K(√(1 − x²))`,
`E(√(1 − x²))`, and the identity `k k'² K'(k) = E − k'² K` of `LegendreRelation.lean` becomes
`g(x) = x² f(x) − (1 − x²) x f'(x)` (`agmE_eq_sub_deriv`).  Gauss's theorem makes `f(x) =
π/(2 AGM(1, x))`, so the AGM step and homogeneity give the Landen identity
`f(x) = (2/(1 + x)) f(2√x/(1 + x))` (`agmK_landen`, `landenMap`); differentiating it and
substituting into the two expressions for `g` gives the Landen step for `g`,
`g(x) = (1 + x) g(ℓ(x)) − x f(x)` (`agmE_landen`), hence by scaling
`J(a, b) = 2 J((a+b)/2, √(ab)) − ab · π/(2 AGM(a, b))` (`agmJ_landen`).  With the deficit
`E_n = J(a_n, b_n) − a_n² · π/(2 AGM)` this reads `E_n = 2 E_{n+1} − (c_n²/2) · π/(2 AGM)`
(`agmDeficit_succ`), which unrolls to `E_0 = 2^n E_n − (∑_{j<n} 2^(j−1) c_j²) · π/(2 AGM)`
(`agmDeficit_zero_eq`).  Finally `−(π/2)(1 + a_1/b_1)(a_n − b_n) ≤ E_n ≤ 0`
(`agmDeficit_bounds`, from `(π/2) b_n ≤ J(a_n, b_n) ≤ (π/2) a_n` and `b_n ≤ AGM ≤ a_n`) and
`2^n (a_n − b_n) → 0` (`tendsto_two_pow_mul_agm_gap`: once the gap is below `2 b_1` it shrinks
by a factor `4` per step, `agm_gap_succ_le_quarter`), so `2^n E_n → 0`, the series converges
(`summable_agm_c_sq`) and the formula follows.

Not formalized: the Brent–Salamin iterate and its error bound (next), the general `J(a, b)` with
`b > a` (use symmetry `J(a, b) = J(b, a)`), and the derivative of `f` at `x = 1` or `x > 1`
(not needed: the Landen step is used with `x = b/a < 1`).
-/

namespace Azurite

namespace BZ

open Real MeasureTheory Set Filter Topology
open scoped Interval

/-! ### The one-parameter integrals `I(1, x)` and `J(1, x)` -/

/-- `f(x) = ∫_0^{π/2} dθ/√(cos²θ + x² sin²θ)`, the first-kind integral `I(1, x)`. -/
noncomputable def agmK (x : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..(π / 2), (Real.sqrt (Real.cos θ ^ 2 + x ^ 2 * Real.sin θ ^ 2))⁻¹

/-- `g(x) = ∫_0^{π/2} √(cos²θ + x² sin²θ) dθ`, the second-kind integral `J(1, x)`. -/
noncomputable def agmE (x : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..(π / 2), Real.sqrt (Real.cos θ ^ 2 + x ^ 2 * Real.sin θ ^ 2)

variable {x : ℝ}

/-- `cos²θ + x² sin²θ = 1 − k² sin²θ` for `k = √(1 − x²)`, `x² ≤ 1`. -/
theorem cos_sq_add_mul_sin_sq (hx : x ^ 2 ≤ 1) (θ : ℝ) :
    Real.cos θ ^ 2 + x ^ 2 * Real.sin θ ^ 2
      = 1 - Real.sqrt (1 - x ^ 2) ^ 2 * Real.sin θ ^ 2 := by
  rw [Real.sq_sqrt (by linarith)]
  linear_combination Real.cos_sq_add_sin_sq θ

theorem agmK_eq_ellipticK (hx : x ^ 2 ≤ 1) : agmK x = ellipticK (Real.sqrt (1 - x ^ 2)) :=
  intervalIntegral.integral_congr fun θ _ => by rw [cos_sq_add_mul_sin_sq hx]

theorem agmE_eq_ellipticE (hx : x ^ 2 ≤ 1) : agmE x = ellipticE (Real.sqrt (1 - x ^ 2)) :=
  intervalIntegral.integral_congr fun θ _ => by rw [cos_sq_add_mul_sin_sq hx]

/-- Gauss's theorem for `f`: `f(x) = π/(2 AGM(1, x))`. -/
theorem agmK_eq_pi_div_AGM (hx : 0 < x) : agmK x = π / (2 * AGM 1 x) := by
  have h := integral_inv_sqrt_eq_pi_div_AGM one_pos hx
  simp only [one_pow, one_mul] at h
  exact h

/-! ### The Landen transformation of `f` -/

/-- The Landen map `ℓ(x) = 2√x/(1 + x)`. -/
noncomputable def landenMap (x : ℝ) : ℝ := 2 * Real.sqrt x / (1 + x)

theorem landenMap_pos (hx : 0 < x) : 0 < landenMap x := by unfold landenMap; positivity

theorem landenMap_lt_one (hx0 : 0 < x) (hx1 : x ≠ 1) : landenMap x < 1 := by
  unfold landenMap
  rw [div_lt_one (by linarith)]
  have hs := Real.sq_sqrt hx0.le
  have hne : Real.sqrt x - 1 ≠ 0 := fun h => hx1 (by rw [← hs, sub_eq_zero.mp h, one_pow])
  nlinarith [sq_pos_of_ne_zero hne]

theorem AGM_one_pos (hx : 0 < x) : 0 < AGM 1 x :=
  lt_of_lt_of_le (lt_min one_pos hx) (min_le_AGM one_pos hx)

/-- Landen: `f(x) = (2/(1 + x)) f(2√x/(1 + x))`, from the AGM step and homogeneity. -/
theorem agmK_landen (hx : 0 < x) : agmK x = 2 / (1 + x) * agmK (landenMap x) := by
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h1x : 0 < 1 + x := by linarith
  have hM : 0 < AGM ((1 + x) / 2) (Real.sqrt x) :=
    lt_of_lt_of_le (lt_min (by positivity) hs0) (min_le_AGM (by positivity) hs0)
  rw [agmK_eq_pi_div_AGM hx, agmK_eq_pi_div_AGM (landenMap_pos hx), AGM_step one_pos hx, one_mul]
  have e : AGM 1 (landenMap x) = 2 / (1 + x) * AGM ((1 + x) / 2) (Real.sqrt x) := by
    rw [← AGM_smul (by positivity) (by positivity) hs0]
    congr 1
    · field_simp
    · unfold landenMap; ring
  rw [e]
  field_simp

/-! ### `g` through `f` and its derivative -/

/-- On `(0, 1)`, `f` is differentiable and `g(x) = x² f(x) − (1 − x²) x f'(x)` (the identity
`k k'² K'(k) = E − k'² K` of `LegendreRelation.lean` with `k = √(1 − x²)`). -/
theorem agmE_eq_sub_deriv (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt agmK (deriv agmK x) x ∧
      agmE x = x ^ 2 * agmK x - (1 - x ^ 2) * x * deriv agmK x := by
  have hx2 : x ^ 2 < 1 := by nlinarith
  set k := Real.sqrt (1 - x ^ 2) with hkdef
  have hk2 : k ^ 2 = 1 - x ^ 2 := Real.sq_sqrt (by linarith)
  have hk0 : 0 < k := Real.sqrt_pos.mpr (by linarith)
  have hk1 : k ^ 2 < 1 := by rw [hk2]; nlinarith
  have hs : HasDerivAt (fun y : ℝ => Real.sqrt (1 - y ^ 2)) (-x / k) x := by
    have h := ((hasDerivAt_pow 2 x).const_sub 1).sqrt (by nlinarith : (1 : ℝ) - x ^ 2 ≠ 0)
    refine h.congr_deriv ?_
    rw [← hkdef]
    field_simp
    ring
  have hK := (hasDerivAt_ellipticK hk1).comp x hs
  have hEq : agmK =ᶠ[𝓝 x] fun y => ellipticK (Real.sqrt (1 - y ^ 2)) := by
    filter_upwards [Ioo_mem_nhds (show -1 < x by linarith) hx1] with y hy
    exact agmK_eq_ellipticK (by nlinarith [hy.1, hy.2])
  have hD := hK.congr_of_eventuallyEq hEq
  refine ⟨hD.differentiableAt.hasDerivAt, ?_⟩
  rw [hD.deriv, agmE_eq_ellipticE hx2.le, agmK_eq_ellipticK hx2.le, ← hkdef]
  set D := ∫ θ in (0 : ℝ)..(π / 2), k * Real.sin θ ^ 2 / Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2) ^ 3
    with hDdef
  have hid := ellipticK_deriv_identity hk1
  rw [← hDdef, hk2] at hid
  have hid' : k * x ^ 2 * D = ellipticE k - x ^ 2 * ellipticK k := by linear_combination hid
  have hk0' : k ≠ 0 := hk0.ne'
  have e : (1 - x ^ 2) * x * (D * (-x / k)) = -(k * x ^ 2 * D) := by
    rw [← hk2]; field_simp
  rw [e, hid']
  ring

/-- The Landen step for `g` on `(0, 1)`: `g(x) = (1 + x) g(ℓ(x)) − x f(x)`, by differentiating
the Landen identity for `f`. -/
theorem agmE_landen (hx0 : 0 < x) (hx1 : x < 1) :
    agmE x = (1 + x) * agmE (landenMap x) - x * agmK x := by
  obtain ⟨s, hs0, rfl⟩ : ∃ s : ℝ, 0 < s ∧ x = s ^ 2 :=
    ⟨Real.sqrt x, Real.sqrt_pos.mpr hx0, (Real.sq_sqrt hx0.le).symm⟩
  have hs1 : s < 1 := by nlinarith
  have hℓ : landenMap (s ^ 2) = 2 * s / (1 + s ^ 2) := by rw [landenMap, Real.sqrt_sq hs0.le]
  have hℓ0 : 0 < 2 * s / (1 + s ^ 2) := by positivity
  have hℓ1 : 2 * s / (1 + s ^ 2) < 1 := by
    rw [div_lt_one (by positivity)]; nlinarith [sq_nonneg (1 - s)]
  have h1s : (1 : ℝ) + s ^ 2 ≠ 0 := by positivity
  obtain ⟨hF, hE1⟩ := agmE_eq_sub_deriv hx0 hx1
  obtain ⟨hG, hE2⟩ := agmE_eq_sub_deriv hℓ0 hℓ1
  have hG' : HasDerivAt agmK (deriv agmK (landenMap (s ^ 2))) (landenMap (s ^ 2)) := by
    rw [hℓ]; exact hG
  -- the derivative of the Landen map at `s²`
  have hℓd : HasDerivAt landenMap
      ((2 * (1 / (2 * Real.sqrt (s ^ 2))) * (1 + s ^ 2) - 2 * Real.sqrt (s ^ 2) * 1)
        / (1 + s ^ 2) ^ 2) (s ^ 2) :=
    ((Real.hasDerivAt_sqrt (by positivity)).const_mul 2).div ((hasDerivAt_id _).const_add 1) h1s
  -- the derivative of the right-hand side `2/(1 + y) · f(ℓ(y))`
  have hR := ((hasDerivAt_const (s ^ 2) (2 : ℝ)).div ((hasDerivAt_id _).const_add 1) h1s).mul
    (hG'.comp (s ^ 2) hℓd)
  have hEq : agmK =ᶠ[𝓝 (s ^ 2)] fun y => 2 / (1 + y) * agmK (landenMap y) := by
    filter_upwards [Ioi_mem_nhds hx0] with y hy
    exact agmK_landen hy
  have hF' := (hR.congr_of_eventuallyEq hEq).deriv
  have hL := agmK_landen hx0
  simp only [Function.comp_apply, Pi.div_apply, id, zero_mul, zero_sub, mul_one] at hF'
  rw [hℓ] at hF' hL ⊢
  rw [hE1, hE2, hF', hL, Real.sqrt_sq hs0.le]
  field_simp
  ring

/-! ### The two-parameter integral `J(a, b)` and its Landen step -/

/-- `J(a, b) = ∫_0^{π/2} √(a² cos²θ + b² sin²θ) dθ`. -/
noncomputable def agmJ (a b : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..(π / 2), Real.sqrt (a ^ 2 * Real.cos θ ^ 2 + b ^ 2 * Real.sin θ ^ 2)

variable {a b : ℝ}

theorem continuous_agmJ_integrand (a b : ℝ) :
    Continuous fun θ : ℝ => Real.sqrt (a ^ 2 * Real.cos θ ^ 2 + b ^ 2 * Real.sin θ ^ 2) :=
  Real.continuous_sqrt.comp (by fun_prop)

/-- Scaling: `J(a, b) = a · g(b/a)` for `a > 0`. -/
theorem agmJ_eq_mul_agmE (ha : 0 < a) (b : ℝ) : agmJ a b = a * agmE (b / a) := by
  unfold agmJ agmE
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  rw [show a ^ 2 * Real.cos θ ^ 2 + b ^ 2 * Real.sin θ ^ 2
      = a ^ 2 * (Real.cos θ ^ 2 + (b / a) ^ 2 * Real.sin θ ^ 2) by field_simp,
    Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha.le]

theorem agmJ_self (ha : 0 ≤ a) : agmJ a a = π / 2 * a := by
  unfold agmJ
  have : ∀ θ : ℝ, Real.sqrt (a ^ 2 * Real.cos θ ^ 2 + a ^ 2 * Real.sin θ ^ 2) = a := fun θ => by
    rw [← mul_add, Real.cos_sq_add_sin_sq, mul_one, Real.sqrt_sq ha]
  simp only [this, intervalIntegral.integral_const, sub_zero, smul_eq_mul]

/-- `(π/2) b ≤ J(a, b) ≤ (π/2) a` for `0 < b ≤ a`. -/
theorem agmJ_bounds (hb : 0 < b) (hab : b ≤ a) :
    π / 2 * b ≤ agmJ a b ∧ agmJ a b ≤ π / 2 * a := by
  have ha : 0 < a := hb.trans_le hab
  have hint : IntervalIntegrable
      (fun θ : ℝ => Real.sqrt (a ^ 2 * Real.cos θ ^ 2 + b ^ 2 * Real.sin θ ^ 2)) volume 0 (π / 2) :=
    (continuous_agmJ_integrand a b).intervalIntegrable _ _
  have hc : ∀ c : ℝ, IntervalIntegrable (fun _ : ℝ => c) volume 0 (π / 2) := fun c =>
    continuous_const.intervalIntegrable _ _
  have hsq : b ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hb.le hab 2
  constructor
  · calc π / 2 * b = ∫ _ in (0 : ℝ)..(π / 2), b := by simp
      _ ≤ agmJ a b := by
        refine intervalIntegral.integral_mono_on Real.pi_div_two_pos.le (hc b) hint fun θ _ => ?_
        calc b = Real.sqrt (b ^ 2) := (Real.sqrt_sq hb.le).symm
          _ ≤ Real.sqrt (a ^ 2 * Real.cos θ ^ 2 + b ^ 2 * Real.sin θ ^ 2) :=
            Real.sqrt_le_sqrt (by nlinarith [Real.cos_sq_add_sin_sq θ,
              mul_le_mul_of_nonneg_right hsq (sq_nonneg (Real.cos θ))])
  · calc agmJ a b ≤ ∫ _ in (0 : ℝ)..(π / 2), a := by
          refine intervalIntegral.integral_mono_on Real.pi_div_two_pos.le hint (hc a)
            fun θ _ => ?_
          calc Real.sqrt (a ^ 2 * Real.cos θ ^ 2 + b ^ 2 * Real.sin θ ^ 2) ≤ Real.sqrt (a ^ 2) :=
                Real.sqrt_le_sqrt (by nlinarith [Real.cos_sq_add_sin_sq θ,
                  mul_le_mul_of_nonneg_right hsq (sq_nonneg (Real.sin θ))])
            _ = a := Real.sqrt_sq ha.le
      _ = π / 2 * a := by simp

/-- The Landen step for `J`: `J(a, b) = 2 J((a+b)/2, √(ab)) − ab · π/(2 AGM(a, b))` for
`0 < b ≤ a`. -/
theorem agmJ_landen (hb : 0 < b) (hab : b ≤ a) :
    agmJ a b = 2 * agmJ ((a + b) / 2) (Real.sqrt (a * b)) - a * b * (π / (2 * AGM a b)) := by
  have ha : 0 < a := hb.trans_le hab
  rcases hab.lt_or_eq with hlt | heq
  · set x := b / a with hx
    have hx0 : 0 < x := by positivity
    have hx1 : x < 1 := by rw [hx, div_lt_one ha]; exact hlt
    have hax : a * x = b := by rw [hx]; field_simp
    have hsq : Real.sqrt (a * b) = a * Real.sqrt x := by
      rw [← hax, ← mul_assoc, ← sq, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha.le]
    have hM : AGM a b = a * AGM 1 x := by
      rw [← AGM_smul ha one_pos hx0, mul_one, hax]
    have ha1 : 0 < (a + b) / 2 := by positivity
    have hI : a * b * (π / (2 * AGM a b)) = b * agmK x := by
      rw [agmK_eq_pi_div_AGM hx0, hM]
      field_simp
    have hℓ : Real.sqrt (a * b) / ((a + b) / 2) = landenMap x := by
      rw [hsq, landenMap, ← hax]
      field_simp
    rw [agmJ_eq_mul_agmE ha, agmJ_eq_mul_agmE ha1, hI, hℓ, ← hx, agmE_landen hx0 hx1]
    linear_combination (agmE (landenMap x) - agmK x) * hax
  · subst heq
    rw [agmJ_self hb.le, show (b + b) / 2 = b by ring, Real.sqrt_mul_self hb.le, agmJ_self hb.le,
      AGM_self hb.le]
    field_simp
    ring

/-! ### Telescoping along the AGM sequence -/

/-- The AGM is constant along its own iteration. -/
theorem AGM_agmSeq (ha : 0 < a) (hb : 0 < b) (j : ℕ) : AGM (agmA a b j) (agmB a b j) = AGM a b := by
  induction j with
  | zero => rfl
  | succ j ih =>
    obtain ⟨hA, hB⟩ := agm_pos ha hb j
    rw [agmA_succ, agmB_succ, ← AGM_step hA hB, ih]

theorem agmB_le_agmA' (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a) (n : ℕ) :
    agmB a b n ≤ agmA a b n := by
  rcases n with _ | n
  · exact hab
  · exact agmB_le_agmA_succ ha hb n

/-- The deficit `E_n = J(a_n, b_n) − a_n² · π/(2 AGM(a, b))`. -/
noncomputable def agmDeficit (a b : ℝ) (n : ℕ) : ℝ :=
  agmJ (agmA a b n) (agmB a b n) - agmA a b n ^ 2 * (π / (2 * AGM a b))

/-- `E_n = 2 E_{n+1} − (c_n²/2) · π/(2 AGM)` with `c_n² = a_n² − b_n²`. -/
theorem agmDeficit_succ (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a) (n : ℕ) :
    agmDeficit a b n = 2 * agmDeficit a b (n + 1)
      - (agmA a b n ^ 2 - agmB a b n ^ 2) / 2 * (π / (2 * AGM a b)) := by
  obtain ⟨hA, hB⟩ := agm_pos ha hb n
  have h := agmJ_landen hB (agmB_le_agmA' ha hb hab n)
  rw [AGM_agmSeq ha hb] at h
  unfold agmDeficit
  rw [h, agmA_succ, agmB_succ]
  ring

/-- Unrolled: `E_0 = 2^n E_n − (∑_{j<n} 2^(j−1) c_j²) · π/(2 AGM)`. -/
theorem agmDeficit_zero_eq (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a) (n : ℕ) :
    agmDeficit a b 0 = 2 ^ n * agmDeficit a b n
      - (∑ j ∈ Finset.range n, 2 ^ j / 2 * (agmA a b j ^ 2 - agmB a b j ^ 2))
        * (π / (2 * AGM a b)) := by
  induction n with
  | zero => simp
  | succ n ih => rw [ih, agmDeficit_succ ha hb hab n, Finset.sum_range_succ]; ring

/-- `−(π/2)(1 + a_1/b_1)(a_n − b_n) ≤ E_n ≤ 0` for `n ≥ 1`. -/
theorem agmDeficit_bounds (ha : 0 < a) (hb : 0 < b) {n : ℕ} (hn : 1 ≤ n) :
    -(π / 2 * (1 + agmA a b 1 / agmB a b 1) * (agmA a b n - agmB a b n)) ≤ agmDeficit a b n ∧
      agmDeficit a b n ≤ 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨hA, hB⟩ := agm_pos ha hb (m + 1)
  obtain ⟨hA1, hB1⟩ := agm_pos ha hb 1
  have hle := agmB_le_agmA_succ ha hb m
  have hM0 : 0 < AGM a b := lt_of_lt_of_le (lt_min ha hb) (min_le_AGM ha hb)
  have hMle := AGM_le_agmA ha hb hn
  have hleM := agmB_le_AGM ha hb hn
  have hB1M := agmB_le_AGM ha hb le_rfl
  have hAn : agmA a b (m + 1) ≤ agmA a b 1 := by simpa using agmA_antitone ha hb (Nat.zero_le m)
  obtain ⟨hJl, hJu⟩ := agmJ_bounds hB hle
  have hg0 : 0 ≤ agmA a b (m + 1) - agmB a b (m + 1) := sub_nonneg.mpr hle
  have hr : 1 ≤ AGM a b / agmB a b 1 := by rw [le_div_iff₀ hB1, one_mul]; exact hB1M
  unfold agmDeficit
  constructor
  · -- `a_n² π/(2M) ≤ (π/2)(a_n + a_1 (a_n − b_n)/b_1)`
    have h1 : agmA a b (m + 1) ^ 2 / AGM a b
        ≤ agmA a b (m + 1) + agmA a b 1 / agmB a b 1 * (agmA a b (m + 1) - agmB a b (m + 1)) := by
      rw [div_le_iff₀ hM0]
      have e2 : (agmA a b (m + 1) + agmA a b 1 / agmB a b 1 * (agmA a b (m + 1) - agmB a b (m + 1)))
          * AGM a b = agmA a b (m + 1) * AGM a b
            + agmA a b 1 * (agmA a b (m + 1) - agmB a b (m + 1)) * (AGM a b / agmB a b 1) := by
        ring
      rw [e2]
      nlinarith [mul_le_mul_of_nonneg_left hr
        (by positivity : 0 ≤ agmA a b 1 * (agmA a b (m + 1) - agmB a b (m + 1))),
        mul_le_mul_of_nonneg_left (sub_le_sub_left hleM (agmA a b (m + 1))) hA.le,
        mul_le_mul_of_nonneg_right hAn hg0]
    have e : agmA a b (m + 1) ^ 2 * (π / (2 * AGM a b))
        = π / 2 * (agmA a b (m + 1) ^ 2 / AGM a b) := by ring
    rw [e]
    have hπ : 0 ≤ π / 2 := by positivity
    have h1' : π / 2 * (agmA a b (m + 1) ^ 2 / AGM a b) ≤ π / 2 * agmA a b (m + 1)
        + π / 2 * (agmA a b 1 / agmB a b 1) * (agmA a b (m + 1) - agmB a b (m + 1)) := by
      calc _ ≤ _ := mul_le_mul_of_nonneg_left h1 hπ
        _ = _ := by ring
    linarith
  · have h2 : agmA a b (m + 1) ≤ agmA a b (m + 1) ^ 2 / AGM a b := by
      rw [le_div_iff₀ hM0]; nlinarith
    have e : agmA a b (m + 1) ^ 2 * (π / (2 * AGM a b))
        = π / 2 * (agmA a b (m + 1) ^ 2 / AGM a b) := by ring
    rw [e]
    have hπ : 0 ≤ π / 2 := by positivity
    have h2' := mul_le_mul_of_nonneg_left h2 hπ
    linarith

/-! ### The gap `2^n (a_n − b_n) → 0` -/

/-- Once `a_j − b_j ≤ 2 b_1` (`j ≥ 1`), the gap shrinks by a factor `4` per step. -/
theorem agm_gap_succ_le_quarter (ha : 0 < a) (hb : 0 < b) {j : ℕ} (hj : 1 ≤ j)
    (h : agmA a b j - agmB a b j ≤ 2 * agmB a b 1) :
    agmA a b (j + 1) - agmB a b (j + 1) ≤ (agmA a b j - agmB a b j) / 4 := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  obtain ⟨hA, hB⟩ := agm_pos ha hb (m + 1)
  have hBj : agmB a b 1 ≤ agmB a b (m + 1) := by simpa using agmB_monotone ha hb (Nat.zero_le m)
  have hg0 : 0 ≤ agmA a b (m + 1) - agmB a b (m + 1) := sub_nonneg.mpr (agmB_le_agmA ha hb hj)
  refine (agm_gap_succ_le_sq ha hb hj).trans ?_
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have h2 : agmA a b (m + 1) - agmB a b (m + 1) ≤ 2 * agmB a b (m + 1) :=
    h.trans (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left h2 hg0]

/-- Some `a_m − b_m ≤ 2 b_1` with `m ≥ 1`. -/
theorem exists_agm_gap_le (ha : 0 < a) (hb : 0 < b) :
    ∃ m, 1 ≤ m ∧ agmA a b m - agmB a b m ≤ 2 * agmB a b 1 := by
  obtain ⟨hA1, hB1⟩ := agm_pos ha hb 1
  obtain ⟨N, hN⟩ := exists_nat_ge ((agmA a b 1 - agmB a b 1) / (2 * agmB a b 1))
  refine ⟨N + 1, by omega, (agm_gap_le_half_pow ha hb N).trans ?_⟩
  rw [div_le_iff₀ (by positivity)]
  rw [div_le_iff₀ (by positivity)] at hN
  have h2 : (N : ℝ) ≤ 2 ^ N := by exact_mod_cast Nat.lt_two_pow_self.le
  nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 * agmB a b 1)]

/-- From such an `m` on, `a_{m+k} − b_{m+k} ≤ (a_m − b_m)/4^k`. -/
theorem agm_gap_add_le (ha : 0 < a) (hb : 0 < b) {m : ℕ} (hm : 1 ≤ m)
    (h : agmA a b m - agmB a b m ≤ 2 * agmB a b 1) (k : ℕ) :
    agmA a b (m + k) - agmB a b (m + k) ≤ (agmA a b m - agmB a b m) / 4 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hg0 : 0 ≤ agmA a b m - agmB a b m := sub_nonneg.mpr (agmB_le_agmA ha hb hm)
    have hk : agmA a b (m + k) - agmB a b (m + k) ≤ 2 * agmB a b 1 :=
      ih.trans ((div_le_self hg0 (one_le_pow₀ (by norm_num))).trans h)
    rw [← add_assoc]
    refine (agm_gap_succ_le_quarter ha hb (by omega) hk).trans ?_
    rw [pow_succ, ← div_div]
    exact div_le_div_of_nonneg_right ih (by norm_num)

/-- `2^(m+k) (a_{m+k} − b_{m+k}) ≤ 2^m (a_m − b_m) (1/2)^k`. -/
theorem two_pow_mul_agm_gap_le (ha : 0 < a) (hb : 0 < b) {m : ℕ} (hm : 1 ≤ m)
    (h : agmA a b m - agmB a b m ≤ 2 * agmB a b 1) (k : ℕ) :
    2 ^ (k + m) * (agmA a b (k + m) - agmB a b (k + m))
      ≤ 2 ^ m * (agmA a b m - agmB a b m) * (1 / 2 : ℝ) ^ k := by
  rw [add_comm k m]
  have := agm_gap_add_le ha hb hm h k
  have h4 : (4 : ℝ) ^ k = 2 ^ k * 2 ^ k := by rw [← mul_pow]; norm_num
  calc 2 ^ (m + k) * (agmA a b (m + k) - agmB a b (m + k))
      ≤ 2 ^ (m + k) * ((agmA a b m - agmB a b m) / 4 ^ k) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = 2 ^ m * (agmA a b m - agmB a b m) * (1 / 2 : ℝ) ^ k := by
        rw [pow_add, h4, one_div_pow]; field_simp

/-- `2^n (a_n − b_n) → 0`. -/
theorem tendsto_two_pow_mul_agm_gap (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun n => 2 ^ n * (agmA a b n - agmB a b n)) atTop (𝓝 0) := by
  obtain ⟨m, hm, h⟩ := exists_agm_gap_le ha hb
  rw [← tendsto_add_atTop_iff_nat m]
  have hlim : Tendsto (fun k : ℕ => 2 ^ m * (agmA a b m - agmB a b m) * (1 / 2 : ℝ) ^ k) atTop
      (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul (2 ^ m * (agmA a b m - agmB a b m))
  refine squeeze_zero (fun k => ?_) (fun k => two_pow_mul_agm_gap_le ha hb hm h k) hlim
  exact mul_nonneg (by positivity) (sub_nonneg.mpr (agmB_le_agmA ha hb (by omega)))

/-- `∑ 2^n (a_n − b_n)` converges. -/
theorem summable_two_pow_mul_agm_gap (ha : 0 < a) (hb : 0 < b) :
    Summable fun n => 2 ^ n * (agmA a b n - agmB a b n) := by
  obtain ⟨m, hm, h⟩ := exists_agm_gap_le ha hb
  rw [← summable_nat_add_iff m]
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => two_pow_mul_agm_gap_le ha hb hm h k)
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _)
  exact mul_nonneg (by positivity) (sub_nonneg.mpr (agmB_le_agmA ha hb (by omega)))

/-- `∑ 2^j/2 · c_j²` converges (`c_j² = (a_j − b_j)(a_j + b_j) ≤ 2 a_1 (a_j − b_j)`). -/
theorem summable_agm_c_sq (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a) :
    Summable fun j : ℕ => 2 ^ j / 2 * (agmA a b j ^ 2 - agmB a b j ^ 2) := by
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_)
    ((summable_two_pow_mul_agm_gap ha hb).mul_left a)
  · obtain ⟨hA, hB⟩ := agm_pos ha hb j
    have := agmB_le_agmA' ha hb hab j
    have : agmB a b j ^ 2 ≤ agmA a b j ^ 2 := pow_le_pow_left₀ hB.le this 2
    positivity
  · obtain ⟨hA, hB⟩ := agm_pos ha hb j
    have hle := agmB_le_agmA' ha hb hab j
    have hAj : agmA a b j ≤ a := by
      rcases j with _ | j
      · exact le_rfl
      · calc agmA a b (j + 1) ≤ agmA a b 1 := by simpa using agmA_antitone ha hb (Nat.zero_le j)
          _ = (a + b) / 2 := agmA_succ 0
          _ ≤ a := by linarith
    have h2 : (0 : ℝ) ≤ 2 ^ j := by positivity
    have hsum : agmA a b j + agmB a b j ≤ 2 * a := by linarith
    nlinarith [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr hle)) h2]

/-! ### Gauss's formula -/

/-- **Gauss's formula for the second-kind integral along the AGM**: for `0 < b ≤ a`,
`J(a, b) = (a² − ∑_{j≥0} 2^(j−1) (a_j² − b_j²)) · π/(2 AGM(a, b))`. -/
theorem agmJ_eq_tsum (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a) :
    agmJ a b = (a ^ 2 - ∑' j : ℕ, 2 ^ j / 2 * (agmA a b j ^ 2 - agmB a b j ^ 2))
      * (π / (2 * AGM a b)) := by
  obtain ⟨hA1, hB1⟩ := agm_pos ha hb 1
  set I := π / (2 * AGM a b) with hI
  set C := π / 2 * (1 + agmA a b 1 / agmB a b 1) with hC
  have hC0 : 0 ≤ C := by positivity
  -- `2^n E_n → 0`
  have h1 : Tendsto (fun n => 2 ^ n * agmDeficit a b n) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n => C * (2 ^ n * (agmA a b n - agmB a b n))) atTop (𝓝 0) := by
      simpa using (tendsto_two_pow_mul_agm_gap ha hb).const_mul C
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with n hn
    obtain ⟨hl, hu⟩ := agmDeficit_bounds ha hb hn
    have hg0 : 0 ≤ agmA a b n - agmB a b n := sub_nonneg.mpr (agmB_le_agmA ha hb hn)
    have habs : |agmDeficit a b n| ≤ C * (agmA a b n - agmB a b n) :=
      abs_le.mpr ⟨by rw [hC]; linarith, by have := mul_nonneg hC0 hg0; linarith⟩
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ n)]
    calc 2 ^ n * |agmDeficit a b n| ≤ 2 ^ n * (C * (agmA a b n - agmB a b n)) :=
          mul_le_mul_of_nonneg_left habs (by positivity)
      _ = C * (2 ^ n * (agmA a b n - agmB a b n)) := by ring
  -- partial sums → the series
  have hS := summable_agm_c_sq ha hb hab
  have h2 := hS.hasSum.tendsto_sum_nat
  have h3 : Tendsto (fun n => 2 ^ n * agmDeficit a b n
      - (∑ j ∈ Finset.range n, 2 ^ j / 2 * (agmA a b j ^ 2 - agmB a b j ^ 2)) * I) atTop
      (𝓝 (0 - (∑' j : ℕ, 2 ^ j / 2 * (agmA a b j ^ 2 - agmB a b j ^ 2)) * I)) :=
    h1.sub (h2.mul_const I)
  have h4 : Tendsto (fun n => 2 ^ n * agmDeficit a b n
      - (∑ j ∈ Finset.range n, 2 ^ j / 2 * (agmA a b j ^ 2 - agmB a b j ^ 2)) * I) atTop
      (𝓝 (agmDeficit a b 0)) := by
    refine tendsto_const_nhds.congr fun n => ?_
    rw [agmDeficit_zero_eq ha hb hab n]
  have h5 := tendsto_nhds_unique h4 h3
  unfold agmDeficit at h5
  rw [agmA_zero, agmB_zero] at h5
  linear_combination h5

/-- Gauss's formula for `E`: for `0 < k < 1`, with the AGM started at `(1, k')`,
`E(k) = (1 − ∑_{j≥0} 2^(j−1) c_j²) K(k)`, `c_j² = a_j² − b_j²`. -/
theorem ellipticE_eq_AGM_sum {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    ellipticE k
      = (1 - ∑' j : ℕ, 2 ^ j / 2 * (agmA 1 (Real.sqrt (1 - k ^ 2)) j ^ 2
          - agmB 1 (Real.sqrt (1 - k ^ 2)) j ^ 2)) * ellipticK k := by
  set k' := Real.sqrt (1 - k ^ 2) with hk'
  have hk2 : k ^ 2 < 1 := by nlinarith
  have hk'0 : 0 < k' := Real.sqrt_pos.mpr (by linarith)
  have hk'1 : k' ≤ 1 := by
    rw [hk', Real.sqrt_le_one]; nlinarith
  have hk'2 : k' ^ 2 = 1 - k ^ 2 := Real.sq_sqrt (by linarith)
  have hkk : Real.sqrt (1 - k' ^ 2) = k := by
    rw [hk'2, sub_sub_cancel, Real.sqrt_sq hk0.le]
  have hJ : agmJ 1 k' = ellipticE k := by
    rw [agmJ_eq_mul_agmE one_pos, div_one, one_mul, agmE_eq_ellipticE (by nlinarith), hkk]
  have hK : π / (2 * AGM 1 k') = ellipticK k := by
    have h := one_div_AGM_one hk'0 hk'1
    rw [hkk] at h
    have hM : 0 < AGM 1 k' := AGM_one_pos hk'0
    field_simp at h ⊢
    linarith
  rw [← hJ, ← hK, agmJ_eq_tsum one_pos hk'0 hk'1, one_pow]

end BZ

end Azurite
