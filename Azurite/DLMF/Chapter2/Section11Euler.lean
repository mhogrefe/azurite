/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section11Numerics
import Azurite.AzRat.Equiv.RingEquiv

/-!
# DLMF §2.11(vi): Euler's transformation of the expansion of `e^x E₁(x)`

The exponential integral is `E₁(x) = ∫_x^∞ e^{−t}/t dt` (6.2.1, `expIntE1`).

* **2.11.24** (`dlmf_2_11_24`, from the exact `expIntE1_expansion`):
  `e^x E₁(x) ∼ ∑ (−1)^s s!/x^{s+1}`.
  The remainder after `n` terms has the sign `(−1)^n` and modulus at most `n!/x^{n+1}`; it is
  obtained by repeated integration by parts (`expIntJ_succ`).
* **2.11.25** (`dlmf_2_11_25_decimals`): the terms at `x = 5`, rounded to 5D.
  * The smallest terms are the 5th and 6th (`dlmf_2_11_vi_smallest`).
  * Truncation after 5 terms gives exactly `0.17408` (`dlmf_2_11_vi_trunc5`).
* **2.11.26** (`dlmf_2_11_26`): `e⁵E₁(5) = 0.17042…`, computed by `AzFloat`: in fact
  `0.17042 21463 ≤ e⁵E₁(5) ≤ 0.17042 21770`.
  * The computation needs no Euler constant. `E₁(5) = E₁(20) + ∫_5^{20} e^{−t}/t dt`.
  * The integral is `ln 4 + ∑_{k=1}^{80} (−1)^k (20^k − 5^k)/(k·k!)` with an error of at most
    `20^{81}/(81·81!)` (`integral_exp_neg_div_approx`, by the Taylor bound
    `abs_exp_neg_sub_taylor_le`).
  * `0 ≤ E₁(20) ≤ e^{−20}/20`.
  * The sum is an exact rational (`e1Q`, evaluated in the kernel). `ln 2` comes from the AGM-free
    bracket `ln2Bracket`, and `e^{−20}`, `e⁵` from `Encl.exp`, all at 64 bits (`e1Scaled`).
* **2.11.27** (`dlmf_2_11_27_decimals`, `dlmf_2_11_27`): the forward differences of the rounded
  moduli of the first six neglected terms.
* **2.11.28** (`dlmf_2_11_28_decimals`, `dlmf_2_11_28`): the products `(−1)^j 2^{−j−1} Δ^j` and the
  sum `0.00363` of their rounded values.
  * `−0.00154/4 = −0.000385` is a tie, and DLMF's `−0.00038` is the round-half-even value. The
    unrounded sum is `0.00362 21875`.
  * `0.17408 − 0.00363 = 0.17045` lies within `0.00003` of `e⁵E₁(5)`
    (`dlmf_2_11_vi_euler_estimate`).

The decimal strings are produced by `AzRat.toSci` (exact rationals) and `AzFloat.toDecimalPlaces`
(enclosure ends), both evaluated by `decide +kernel`. The equivalence with a re-expansion in powers
of `1/(x + 5)` and the other acceleration methods (Aitken, Wynn) are not formalized.
-/

open Filter Topology Set MeasureTheory
open scoped Real Interval

namespace Azurite.DLMF

/-! ### The exponential integral and the expansion 2.11.24 -/

/-- **DLMF 6.2.1** for `x > 0`: `E₁(x) = ∫_x^∞ e^{−t}/t dt`. -/
noncomputable def expIntE1 (x : ℝ) : ℝ := ∫ t in Ioi x, Real.exp (-t) / t

/-- `J_n(x) = ∫_x^∞ e^{−t}/t^{n+1} dt` (`J₀ = E₁`). -/
noncomputable def expIntJ (n : ℕ) (x : ℝ) : ℝ := ∫ t in Ioi x, Real.exp (-t) / t ^ (n + 1)

theorem expIntE1_eq_J (x : ℝ) : expIntE1 x = expIntJ 0 x := by
  simp [expIntE1, expIntJ]

theorem integrableOn_exp_neg_Ioi' (x : ℝ) : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi x) :=
  IntegrableOn.congr_fun (exp_neg_integrableOn_Ioi x one_pos) (fun t _ => by simp)
    measurableSet_Ioi

theorem integrableOn_expIntJ (n : ℕ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => Real.exp (-t) / t ^ (n + 1)) (Ioi x) := by
  have hb : IntegrableOn (fun t : ℝ => (x ^ (n + 1))⁻¹ * Real.exp (-t)) (Ioi x) :=
    Integrable.const_mul (integrableOn_exp_neg_Ioi' x) _
  refine hb.mono' (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  have ht' : x < t := ht
  have ht0 : 0 < t := hx.trans ht'
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_eq_mul_inv, mul_comm]
  gcongr

theorem expIntJ_nonneg (n : ℕ) {x : ℝ} (hx : 0 < x) : 0 ≤ expIntJ n x :=
  setIntegral_nonneg measurableSet_Ioi fun t ht => by
    have : (0 : ℝ) < t := hx.trans ht
    positivity

theorem expIntJ_le (n : ℕ) {x : ℝ} (hx : 0 < x) :
    expIntJ n x ≤ Real.exp (-x) / x ^ (n + 1) := by
  calc expIntJ n x ≤ ∫ t in Ioi x, (x ^ (n + 1))⁻¹ * Real.exp (-t) :=
        setIntegral_mono_on (integrableOn_expIntJ n hx)
          (Integrable.const_mul (integrableOn_exp_neg_Ioi' x) _) measurableSet_Ioi
          fun t ht => by
            have ht' : x < t := ht
            have ht0 : 0 < t := hx.trans ht'
            rw [div_eq_mul_inv, mul_comm]
            gcongr
    _ = _ := by rw [integral_const_mul, integral_exp_neg_Ioi]; ring

/-- Integration by parts: `J_n(x) = e^{−x}/x^{n+1} − (n + 1) J_{n+1}(x)`. -/
theorem expIntJ_succ (n : ℕ) {x : ℝ} (hx : 0 < x) :
    expIntJ n x = Real.exp (-x) / x ^ (n + 1) - (n + 1) * expIntJ (n + 1) x := by
  set F : ℝ → ℝ := fun t => -Real.exp (-t) * (t ^ (n + 1))⁻¹
  set F' : ℝ → ℝ := fun t =>
    Real.exp (-t) / t ^ (n + 1) + (n + 1) * (Real.exp (-t) / t ^ (n + 1 + 1))
  have hderiv : ∀ t ∈ Ioi x, HasDerivAt F (F' t) t := by
    intro t ht
    have ht0 : 0 < t := hx.trans ht
    have h1 : HasDerivAt (fun t : ℝ => Real.exp (-t)) (Real.exp (-t) * (-1)) t :=
      (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)
    have h2 := (hasDerivAt_pow (n + 1) t).inv (pow_ne_zero (n + 1) ht0.ne')
    convert h1.neg.mul h2 using 1
    simp only [F', Pi.neg_apply, Pi.inv_apply, Nat.add_sub_cancel]
    field_simp
    push_cast
    ring
  have hint : IntegrableOn F' (Ioi x) :=
    (integrableOn_expIntJ n hx).add (Integrable.const_mul (integrableOn_expIntJ (n + 1) hx) _)
  have hcont : ContinuousWithinAt F (Ici x) x := by
    refine ContinuousAt.continuousWithinAt ?_
    have : x ^ (n + 1) ≠ 0 := pow_ne_zero _ hx.ne'
    simp only [F]
    fun_prop (disch := assumption)
  have hlim : Tendsto F atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => (t ^ (n + 1))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (Nat.succ_ne_zero n))
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.neg).mul h1
    simpa [F] using this
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
  rw [integral_add (integrableOn_expIntJ n hx)
    (Integrable.const_mul (integrableOn_expIntJ (n + 1) hx) _), integral_const_mul] at h
  simp only [F] at h
  unfold expIntJ
  rw [div_eq_mul_inv]
  linarith

/-- **DLMF 2.11.24**, exactly: `e^x E₁(x) = ∑_{s<n} (−1)^s s!/x^{s+1} + (−1)^n n! e^x J_n(x)`. -/
theorem expIntE1_expansion (n : ℕ) {x : ℝ} (hx : 0 < x) :
    Real.exp x * expIntE1 x = ∑ s ∈ Finset.range n, (-1) ^ s * (s.factorial : ℝ) / x ^ (s + 1) +
      (-1) ^ n * n.factorial * (Real.exp x * expIntJ n x) := by
  induction n with
  | zero => simp [expIntE1_eq_J]
  | succ n ih =>
    rw [ih, Finset.sum_range_succ, expIntJ_succ n hx]
    have he : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    linear_combination (-1) ^ n * n.factorial * he

/-- **DLMF 2.11.24**: `e^x E₁(x) ∼ ∑ (−1)^s s!/x^{s+1}` as `x → +∞`. The remainder after `n`
terms has the sign `(−1)^n` and is at most the first neglected term `n!/x^{n+1}` in modulus. -/
theorem dlmf_2_11_24 (n : ℕ) {x : ℝ} (hx : 0 < x) :
    0 ≤ (-1) ^ n * (Real.exp x * expIntE1 x -
        ∑ s ∈ Finset.range n, (-1) ^ s * (s.factorial : ℝ) / x ^ (s + 1)) ∧
      |Real.exp x * expIntE1 x - ∑ s ∈ Finset.range n, (-1) ^ s * (s.factorial : ℝ) / x ^ (s + 1)|
        ≤ n.factorial / x ^ (n + 1) := by
  rw [expIntE1_expansion n hx, add_sub_cancel_left]
  have hJ0 := expIntJ_nonneg n hx
  have hJ1 := expIntJ_le n hx
  have he : Real.exp x * (Real.exp (-x) / x ^ (n + 1)) = 1 / x ^ (n + 1) := by
    rw [mul_div_assoc', ← Real.exp_add]; simp
  have hE0 : 0 ≤ Real.exp x * expIntJ n x := mul_nonneg (Real.exp_pos x).le hJ0
  have hE1 : Real.exp x * expIntJ n x ≤ 1 / x ^ (n + 1) :=
    he ▸ mul_le_mul_of_nonneg_left hJ1 (Real.exp_pos x).le
  constructor
  · have h1 : (-1 : ℝ) ^ n * (-1) ^ n = 1 := by rw [← mul_pow]; simp
    rw [show (-1 : ℝ) ^ n * ((-1) ^ n * n.factorial * (Real.exp x * expIntJ n x)) =
      ((-1) ^ n * (-1) ^ n) * n.factorial * (Real.exp x * expIntJ n x) by ring, h1, one_mul]
    positivity
  · rw [mul_assoc, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_mul,
      Nat.abs_cast, abs_of_nonneg hE0]
    calc (n.factorial : ℝ) * (Real.exp x * expIntJ n x) ≤ n.factorial * (1 / x ^ (n + 1)) :=
          mul_le_mul_of_nonneg_left hE1 (by positivity)
      _ = _ := by ring

/-! ### A convergent evaluation of `E₁(a) − E₁(b)` -/

/-- `T_K(t) = ∑_{k≤K} (−t)^k/k!`. -/
noncomputable def expNegTaylor (K : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (K + 1), (-t) ^ k / k.factorial

theorem hasDerivAt_expNegTaylor (K : ℕ) (t : ℝ) :
    HasDerivAt (expNegTaylor (K + 1)) (-expNegTaylor K t) t := by
  induction K with
  | zero =>
    have : expNegTaylor 1 = fun t => 1 - t := by
      funext t; simp [expNegTaylor, Finset.sum_range_succ]; ring
    rw [this]
    simpa [expNegTaylor] using (hasDerivAt_id t).const_sub (1 : ℝ)
  | succ K ih =>
    have e : expNegTaylor (K + 2) =
        fun t => expNegTaylor (K + 1) t + (-t) ^ (K + 2) / (K + 2).factorial := by
      funext t; simp only [expNegTaylor]; rw [Finset.sum_range_succ (n := K + 2)]
    rw [e]
    have h2 : HasDerivAt (fun t : ℝ => (-t) ^ (K + 2) / (K + 2).factorial)
        ((K + 2 : ℕ) * (-t) ^ (K + 1) * (-1) / (K + 2).factorial) t := by
      have := ((hasDerivAt_neg t).pow (K + 2)).div_const ((K + 2).factorial : ℝ)
      convert this using 1
      rw [show K + 2 - 1 = K + 1 from rfl]
    convert ih.add h2 using 1
    simp only [expNegTaylor]
    rw [Finset.sum_range_succ (n := K + 1), Nat.factorial_succ (K + 1)]
    push_cast
    field_simp
    ring

/-- `|e^{−t} − T_K(t)| ≤ t^{K+1}/(K+1)!` for `t ≥ 0`. -/
theorem abs_exp_neg_sub_taylor_le (K : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    |Real.exp (-t) - expNegTaylor K t| ≤ t ^ (K + 1) / (K + 1).factorial := by
  induction K generalizing t with
  | zero =>
    simp only [expNegTaylor, zero_add, Finset.range_one, Finset.sum_singleton, pow_zero,
      Nat.factorial_zero, Nat.cast_one, div_one, pow_one, Nat.factorial_one]
    rw [abs_le]
    constructor
    · linarith [Real.add_one_le_exp (-t)]
    · linarith [Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)]
  | succ K ih =>
    set f : ℝ → ℝ := fun s => Real.exp (-s) - expNegTaylor (K + 1) s
    have hf : ∀ s, HasDerivAt f (-(Real.exp (-s) - expNegTaylor K s)) s := fun s => by
      have h1 : HasDerivAt (fun t : ℝ => Real.exp (-t)) (Real.exp (-s) * (-1)) s :=
        (Real.hasDerivAt_exp (-s)).comp s (hasDerivAt_neg s)
      convert h1.sub (hasDerivAt_expNegTaylor K s) using 1
      ring
    set c := ((K + 1 + 1).factorial : ℝ)
    have hc : 0 < c := by positivity
    have hp : ∀ s, HasDerivAt (fun s : ℝ => s ^ (K + 2) / c) (s ^ (K + 1) / (K + 1).factorial) s :=
      fun s => by
        have := (hasDerivAt_pow (K + 2) s).div_const c
        convert this using 1
        simp only [c]
        rw [Nat.factorial_succ (K + 1)]
        push_cast
        field_simp
        ring
    have f0 : f 0 = 0 := by simp [f, expNegTaylor, Finset.sum_range_succ']
    have mono : ∀ σ : ℝ, σ = 1 ∨ σ = -1 →
        MonotoneOn (fun s => s ^ (K + 2) / c - σ * f s) (Ici 0) := by
      intro σ hσ
      have hd : ∀ s, HasDerivAt (fun s => s ^ (K + 2) / c - σ * f s)
          (s ^ (K + 1) / (K + 1).factorial + σ * (Real.exp (-s) - expNegTaylor K s)) s :=
        fun s => by convert (hp s).sub ((hf s).const_mul σ) using 1; ring
      refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
        (fun s _ => (hd s).continuousAt.continuousWithinAt)
        (fun s _ => (hd s).differentiableAt.differentiableWithinAt) fun s hs => ?_
      rw [interior_Ici] at hs
      rw [(hd s).deriv]
      have := abs_le.mp (ih (le_of_lt hs))
      rcases hσ with rfl | rfl <;> linarith
    have g1 := mono 1 (Or.inl rfl) (mem_Ici.mpr le_rfl) ht ht
    have g2 := mono (-1) (Or.inr rfl) (mem_Ici.mpr le_rfl) ht ht
    simp only [f0, mul_zero, sub_zero, one_mul, neg_mul, sub_neg_eq_add,
      zero_pow (show K + 2 ≠ 0 by omega), zero_div] at g1 g2
    rw [abs_le, show K + 1 + 1 = K + 2 from rfl]
    constructor <;> simp only [f] at g1 g2 <;> linarith

/-- **`E₁(a) − E₁(b)` by a terminating series**: for `0 < a ≤ b`,
`∫_a^b e^{−t}/t dt = ln(b/a) + ∑_{k=1}^{K} (−1)^k (b^k − a^k)/(k·k!) + E`,
`|E| ≤ b^{K+1}/((K+1)(K+1)!)` (the convergent expansion of 6.6.2, without Euler's constant). -/
theorem integral_exp_neg_div_approx (K : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    |(∫ t in a..b, Real.exp (-t) / t) - (Real.log (b / a) + ∑ k ∈ Finset.range K,
        (-1) ^ (k + 1) * (b ^ (k + 1) - a ^ (k + 1)) / ((k + 1) * (k + 1).factorial))| ≤
      b ^ (K + 1) / ((K + 1) * (K + 1).factorial) := by
  have hb : 0 < b := ha.trans_le hab
  have hpos : ∀ t ∈ uIcc a b, 0 < t := fun t ht => by
    rw [uIcc_of_le hab] at ht; exact ha.trans_le ht.1
  -- the integral of `T_K(t)/t`
  have hT : ∀ t : ℝ, t ≠ 0 → expNegTaylor K t / t =
      t⁻¹ + ∑ k ∈ Finset.range K, (-1) ^ (k + 1) / (k + 1).factorial * t ^ k := by
    intro t ht
    simp only [expNegTaylor]
    rw [Finset.sum_range_succ', add_div, Finset.sum_div]
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_div]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [neg_pow, pow_succ]
    field_simp
    ring
  have hint_inv : IntervalIntegrable (fun t : ℝ => t⁻¹) volume a b :=
    intervalIntegral.intervalIntegrable_inv (fun t ht => (hpos t ht).ne')
      continuousOn_id
  have hint_poly : IntervalIntegrable (fun t : ℝ => ∑ k ∈ Finset.range K,
      (-1) ^ (k + 1) / ((k + 1).factorial : ℝ) * t ^ k) volume a b :=
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  have hTint : (∫ t in a..b, expNegTaylor K t / t) = Real.log (b / a) + ∑ k ∈ Finset.range K,
      (-1) ^ (k + 1) * (b ^ (k + 1) - a ^ (k + 1)) / ((k + 1) * (k + 1).factorial) := by
    rw [intervalIntegral.integral_congr (g := fun t => t⁻¹ + ∑ k ∈ Finset.range K,
      (-1) ^ (k + 1) / ((k + 1).factorial : ℝ) * t ^ k) fun t ht => hT t (hpos t ht).ne',
      intervalIntegral.integral_add hint_inv hint_poly, integral_inv_of_pos ha hb,
      intervalIntegral.integral_finsetSum fun k _ => (Continuous.intervalIntegrable
        (by fun_prop) _ _)]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [intervalIntegral.integral_const_mul, integral_pow]
    field_simp
  -- the remainder
  have hcont_e : ContinuousOn (fun t : ℝ => Real.exp (-t) / t) (uIcc a b) :=
    fun t ht => ((by fun_prop : Continuous fun t : ℝ => Real.exp (-t)).continuousAt.div
      continuousAt_id (hpos t ht).ne').continuousWithinAt
  have hcont_T : ContinuousOn (fun t : ℝ => expNegTaylor K t / t) (uIcc a b) :=
    fun t ht => ((by unfold expNegTaylor; fun_prop : Continuous (expNegTaylor K)).continuousAt.div
      continuousAt_id (hpos t ht).ne').continuousWithinAt
  rw [← hTint, ← intervalIntegral.integral_sub hcont_e.intervalIntegrable
    hcont_T.intervalIntegrable]
  have hbound : ‖∫ t in a..b, (Real.exp (-t) / t - expNegTaylor K t / t)‖ ≤
      ∫ t in a..b, t ^ K / (K + 1).factorial := by
    refine intervalIntegral.norm_integral_le_of_norm_le hab (Eventually.of_forall fun t ht => ?_)
      (Continuous.intervalIntegrable (by fun_prop) _ _)
    have ht0 : 0 < t := ha.trans ht.1
    rw [← sub_div, Real.norm_eq_abs, abs_div, abs_of_pos ht0, div_le_iff₀ ht0]
    calc _ ≤ t ^ (K + 1) / (K + 1).factorial := abs_exp_neg_sub_taylor_le K ht0.le
      _ = _ := by rw [pow_succ]; ring
  rw [Real.norm_eq_abs, intervalIntegral.integral_div, integral_pow] at hbound
  refine hbound.trans ?_
  have hak : 0 ≤ a ^ (K + 1) := by positivity
  rw [div_div]
  gcongr
  linarith

theorem expIntE1_sub {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    expIntE1 a - expIntE1 b = ∫ t in a..b, Real.exp (-t) / t := by
  have hint := integrableOn_expIntJ 0 ha
  simp only [zero_add, pow_one] at hint
  unfold expIntE1
  rw [← Ioc_union_Ioi_eq_Ioi hab, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi hab)),
    intervalIntegral.integral_of_le hab]
  ring

theorem expIntE1_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ expIntE1 x := by
  rw [expIntE1_eq_J]; exact expIntJ_nonneg 0 hx

theorem expIntE1_le {x : ℝ} (hx : 0 < x) : expIntE1 x ≤ Real.exp (-x) / x := by
  rw [expIntE1_eq_J]; simpa using expIntJ_le 0 hx

/-! ### The AzFloat computation of `e⁵E₁(5)` -/

section Numerics

open Azurite.AzFloat Encl

/-- The enclosure `[|num|/den]` of a positive rational. -/
def ratEncl (w : Nat) (q : ℚ) : Encl := Encl.div w (nat q.num.natAbs) (nat q.den)

/-- `∑_{k=1}^{K} (−1)^k (20^k − 5^k)/(k·k!)`, exactly. -/
def e1Q (K : Nat) : ℚ :=
  ∑ k ∈ Finset.range K, (-1) ^ (k + 1) * ((20 : ℚ) ^ (k + 1) - 5 ^ (k + 1)) /
    (((k + 1 : Nat) : ℚ) * ((k + 1).factorial : ℚ))

/-- The truncation bound `20^{K+1}/((K+1)(K+1)!)`. -/
def e1Tail (K : Nat) : ℚ :=
  (20 : ℚ) ^ (K + 1) / (((K + 1 : Nat) : ℚ) * ((K + 1).factorial : ℚ))

/-- `ln 4 + ∑_{k=1}^{80} ⋯ = E₁(5) − E₁(20) + O(10^{−17})`. -/
def e1Main (w : Nat) : Encl := Encl.sub w (Encl.mul w (nat 2) (ln2Bracket w)) (ratEncl w (-e1Q 80))

/-- The error: the truncation bound plus `E₁(20) ≤ e^{−20}/20`. -/
def e1Err (w : Nat) : Encl :=
  Encl.add w (ratEncl w (e1Tail 80))
    (Encl.div w (Encl.exp w (-(ofAzNat (AzNat.ofNat 20)))) (nat 20))

/-- `E₁(5)`. -/
def e1Five (w : Nat) : Encl := Encl.widen w (e1Main w) (e1Err w)

/-- `e⁵E₁(5)`. -/
def e1Scaled (w : Nat) : Encl := Encl.mul w (Encl.exp w (ofAzNat (AzNat.ofNat 5))) (e1Five w)

/-- The fixed-point decimal rendering of an exact rational, rounded to nearest (ties to even) at
`k` places, by `AzRat.toSci`. -/
def ratDecimalPlaces (q : ℚ) (k : Nat) : Option String :=
  (AzRat.ofRat q).toSci
    (SciOptions.mk 10 .Nearest (.scale k) (SciFormat.mk (-64) true true false true))

/-- The terms `(−1)^s s!/5^{s+1}` of 2.11.25. -/
def euTerm (s : Nat) : ℚ := (-1) ^ s * (s.factorial : ℚ) / (5 : ℚ) ^ (s + 1)

/-- The moduli of the first six neglected terms, rounded to 5D as in 2.11.25. -/
def euRounded : List ℚ := [768, 922, 1290, 2064, 3716, 7432].map fun n => (n : ℚ) / 100000

/-- The `j`th forward difference of a list at its head. -/
def fwdDiff (l : List ℚ) (j : Nat) : ℚ :=
  ∑ i ∈ Finset.range (j + 1), (-1) ^ (j - i) * (j.choose i : ℚ) * l.getD i 0

set_option maxRecDepth 100000 in
theorem e1Five_data :
    (valData (e1Five 64).1, valData (e1Five 64).2) =
      (some (true, 10845343323039770895, 9444732965739290427392),
        some (true, 10845345269744427761, 9444732965739290427392)) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem e1Scaled_data :
    (valData (e1Scaled 64).1, valData (e1Scaled 64).2) =
      (some (true, 6287467437985813913, 36893488147419103232),
        some (true, 12574937133132471311, 73786976294838206464)) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The two ends of the enclosure of `e⁵E₁(5)` to 10D: `0.17042 21464`, `0.17042 21770`. -/
theorem e1Scaled_decimals :
    (toDecimalPlaces (e1Scaled 64).1 10, toDecimalPlaces (e1Scaled 64).2 10) =
      (some "0.1704221464", some "0.1704221770") := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem e1Q_pos : 0 < -e1Q 80 ∧ 0 < e1Tail 80 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **DLMF 2.11.25**: the terms of 2.11.24 at `x = 5`, rounded to 5D. -/
theorem dlmf_2_11_25_decimals :
    (List.range 11).map (fun s => ratDecimalPlaces (euTerm s) 5) =
      [some "0.20000", some "-0.04000", some "0.01600", some "-0.00960", some "0.00768",
        some "-0.00768", some "0.00922", some "-0.01290", some "0.02064", some "-0.03716",
        some "0.07432"] := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **DLMF 2.11.27**: the forward differences of the rounded moduli of the first six neglected
terms. -/
theorem dlmf_2_11_27_decimals :
    (List.range 6).map (fun j => ratDecimalPlaces (fwdDiff euRounded j) 5) =
      [some "0.00768", some "0.00154", some "0.00214", some "0.00192", some "0.00280",
        some "0.00434"] := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **DLMF 2.11.28**: the differences times `(−1)^j 2^{−j−1}`, rounded to 5D (to nearest, ties
to even: `−0.00154/4 = −0.000385` becomes `−0.00038`). -/
theorem dlmf_2_11_28_decimals :
    (List.range 6).map (fun j =>
        ratDecimalPlaces ((-1) ^ j * fwdDiff euRounded j / (2 : ℚ) ^ (j + 1)) 5) =
      [some "0.00384", some "-0.00038", some "0.00027", some "-0.00012", some "0.00009",
        some "-0.00007"] := by
  decide +kernel

/-! #### Soundness -/

private theorem hw64' : 2 ≤ 64 := by norm_num

theorem isEnclPos_ratEncl {q : ℚ} (hq : 0 < q) : IsEnclPos (ratEncl 64 q) (q : ℝ) := by
  have hn : 0 < q.num := Rat.num_pos.mpr hq
  have h := (enclosesPos_nat (n := q.num.natAbs) (by omega)).div (w := 64) hw64'
    (enclosesPos_nat q.den_pos)
  have e : ((q.num.natAbs : ℕ) : ℝ) / (q.den : ℝ) = (q : ℝ) := by
    rw [Rat.cast_def, ← Int.cast_natCast, Int.natAbs_of_nonneg hn.le]
  rwa [e] at h

theorem IsEncl.encloses0_of_valData {a : Encl} {x : ℝ} (h : IsEncl a x) {n d : ℕ}
    (h₁ : valData a.1 = some (true, n, d)) : IsEncl0 a x := by
  obtain ⟨l, u, hl, hu, h1, h2⟩ := h
  have e := toVal_of_valData h₁
  rw [hl] at e
  have e' := EReal.coe_injective (Option.some_injective _ e)
  refine ⟨l, u, hl, hu, ?_, h1, h2⟩
  rw [e', signedVal]
  simp only [ite_true]
  positivity

theorem e1Q_cast (K : ℕ) : ((e1Q K : ℚ) : ℝ) = ∑ k ∈ Finset.range K,
    (-1) ^ (k + 1) * ((20 : ℝ) ^ (k + 1) - 5 ^ (k + 1)) / ((k + 1) * (k + 1).factorial) := by
  simp [e1Q]

theorem e1Tail_cast (K : ℕ) : ((e1Tail K : ℚ) : ℝ) =
    (20 : ℝ) ^ (K + 1) / ((K + 1) * (K + 1).factorial) := by
  simp [e1Tail]

theorem e1Main_encl : IsEncl (e1Main 64) (Real.log (20 / 5) + ∑ k ∈ Finset.range 80,
    (-1) ^ (k + 1) * ((20 : ℝ) ^ (k + 1) - 5 ^ (k + 1)) / ((k + 1) * (k + 1).factorial)) := by
  obtain ⟨hq, -⟩ := e1Q_pos
  obtain ⟨lv, hv, hl, hh, h1, h2, -, h5⟩ := ln2Bracket_spec 64
  have hln : IsEnclPos (ln2Bracket 64) (Real.log 2) :=
    ⟨lv, hv, hl, hh, by linarith [h5 (by norm_num)], h1, h2⟩
  have h2 : IsEnclPos (Encl.mul 64 (nat 2) (ln2Bracket 64)) (2 * Real.log 2) := by
    have := IsEnclPos.mul (w := 64) hw64' (enclosesPos_nat (n := 2) (by norm_num)) hln
    simpa using this
  have h := IsEncl.sub (w := 64) (IsEncl0.encloses (IsEnclPos.encloses0 h2))
    (IsEncl0.encloses (IsEnclPos.encloses0 (isEnclPos_ratEncl hq)))
  refine isEncl_of_eq h ?_
  rw [Rat.cast_neg, e1Q_cast, show (20 : ℝ) / 5 = 2 ^ 2 by norm_num,
    Real.log_pow]
  push_cast
  ring

theorem e1Err_encl : IsEncl0 (e1Err 64)
    ((20 : ℝ) ^ (80 + 1) / ((80 + 1) * (80 + 1).factorial) + Real.exp (-20) / 20) := by
  obtain ⟨-, hq⟩ := e1Q_pos
  have hx : (-(ofAzNat (AzNat.ofNat 20))).toVal = some ((-20 : ℝ) : EReal) := by
    rw [toVal_neg, toVal_ofAzNat, AzNat.toNat_ofNat]
    simp
  have h1 := IsEnclPos.encloses0 (isEnclPos_ratEncl hq)
  have h2 := (encloses0_exp hx (w := 64) (by norm_num)).div (w := 64)
    (enclosesPos_nat (n := 20) (by norm_num))
  refine isEncl0_of_eq (h1.add (w := 64) h2) ?_
  rw [e1Tail_cast]
  push_cast
  ring

theorem e1Five_encl : IsEncl (e1Five 64) (expIntE1 5) := by
  refine e1Main_encl.widen e1Err_encl ?_
  have h := integral_exp_neg_div_approx 80 (a := 5) (b := 20) (by norm_num) (by norm_num)
  have hE := expIntE1_sub (a := 5) (b := 20) (by norm_num) (by norm_num)
  have h0 := expIntE1_nonneg (x := 20) (by norm_num)
  have h1 := expIntE1_le (x := 20) (by norm_num)
  rw [← hE] at h
  push_cast at h ⊢
  rw [abs_le] at h ⊢
  constructor <;> linarith [h.1, h.2]

theorem e1Scaled_encl : IsEncl0 (e1Scaled 64) (Real.exp 5 * expIntE1 5) := by
  have hx : (ofAzNat (AzNat.ofNat 5)).toVal = some ((5 : ℝ) : EReal) := by
    rw [toVal_ofAzNat, AzNat.toNat_ofNat]; simp
  have h5 := IsEncl.encloses0_of_valData e1Five_encl (Prod.mk.inj e1Five_data).1
  exact (encloses0_exp hx (w := 64) (by norm_num)).mul (w := 64) h5

/-! #### The claims -/

/-- **DLMF 2.11.26**: `e⁵E₁(5) = 0.17042…` (in fact `0.17042 21463 ≤ e⁵E₁(5) ≤ 0.17042 21770`). -/
theorem dlmf_2_11_26 :
    0.1704221463 ≤ Real.exp 5 * expIntE1 5 ∧ Real.exp 5 * expIntE1 5 ≤ 0.1704221770 := by
  obtain ⟨d1, d2⟩ := Prod.mk.inj e1Scaled_data
  obtain ⟨l, u⟩ := IsEncl.bounds (IsEncl0.encloses e1Scaled_encl) d1 d2
  norm_num [signedVal] at l u
  constructor <;> linarith

theorem euTerm_cast (s : ℕ) :
    ((euTerm s : ℚ) : ℝ) = (-1) ^ s * (s.factorial : ℝ) / 5 ^ (s + 1) := by
  simp [euTerm]

/-- "The numerically smallest terms are the 5th and 6th" (`s = 4, 5`): `4!/5⁵ = 5!/5⁶`, and every
term of 2.11.24 at `x = 5` is at least as large in modulus. -/
theorem dlmf_2_11_vi_smallest :
    ((4 : ℕ).factorial : ℝ) / 5 ^ 5 = ((5 : ℕ).factorial : ℝ) / 5 ^ 6 ∧
      ∀ s : ℕ, ((4 : ℕ).factorial : ℝ) / 5 ^ 5 ≤ (s.factorial : ℝ) / 5 ^ (s + 1) := by
  refine ⟨by norm_num [Nat.factorial], fun s => ?_⟩
  rcases le_or_gt s 4 with hs | hs
  · interval_cases s <;> norm_num [Nat.factorial]
  · obtain ⟨k, rfl⟩ : ∃ k, s = k + 5 := ⟨s - 5, by omega⟩
    induction k with
    | zero => norm_num [Nat.factorial]
    | succ k ih =>
      refine (ih (by omega)).trans ?_
      have e : ((k + 1 + 5).factorial : ℝ) / 5 ^ (k + 1 + 5 + 1) =
          (((k : ℝ) + 6) / 5) * ((k + 5).factorial / 5 ^ (k + 5 + 1)) := by
        rw [show k + 1 + 5 = (k + 5) + 1 by ring, Nat.factorial_succ, pow_succ]
        push_cast
        field_simp
        ring
      rw [e]
      exact le_mul_of_one_le_left (by positivity) (by
        rw [le_div_iff₀ (by norm_num)]; linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)])

/-- "Truncation after 5 terms yields 0.17408": the exact sum. -/
theorem dlmf_2_11_vi_trunc5 :
    ∑ s ∈ Finset.range 5, (-1) ^ s * (s.factorial : ℝ) / 5 ^ (s + 1) = 0.17408 := by
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- The rounded moduli of the first six neglected terms (2.11.25). -/
noncomputable def euR (i : ℕ) : ℝ := [0.00768, 0.00922, 0.01290, 0.02064, 0.03716, 0.07432].getD i 0

/-- `Δ^j` of a sequence at `0`. -/
noncomputable def fwdDiffR (r : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (j + 1), (-1) ^ (j - i) * (j.choose i : ℝ) * r i

/-- **DLMF 2.11.27**, exactly. -/
theorem dlmf_2_11_27 :
    fwdDiffR euR 0 = 0.00768 ∧ fwdDiffR euR 1 = 0.00154 ∧ fwdDiffR euR 2 = 0.00214 ∧
      fwdDiffR euR 3 = 0.00192 ∧ fwdDiffR euR 4 = 0.00280 ∧ fwdDiffR euR 5 = 0.00434 := by
  simp only [fwdDiffR, euR, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose]

/-- **DLMF 2.11.28**: the exact products `(−1)^j 2^{−j−1} Δ^j`, and the sum `0.00363` of their
values rounded to 5D (the exact sum is `0.00362 21875`). -/
theorem dlmf_2_11_28 :
    (List.range 6).map (fun j => (-1) ^ j * fwdDiffR euR j / 2 ^ (j + 1)) =
        [0.00384, -0.000385, 0.0002675, -0.00012, 0.0000875, -0.0000678125] ∧
      (0.00384 : ℝ) - 0.00038 + 0.00027 - 0.00012 + 0.00009 - 0.00007 = 0.00363 ∧
      (0.00384 : ℝ) - 0.000385 + 0.0002675 - 0.00012 + 0.0000875 - 0.0000678125 =
        0.0036221875 := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := dlmf_2_11_27
  refine ⟨?_, by norm_num, by norm_num⟩
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons,
    List.map_nil, List.cons_append, h0, h1, h2, h3, h4, h5]
  norm_num

/-- "Subtraction of this result from the sum of the first 5 terms in (2.11.25) yields 0.17045,
which is much closer to the true value": `0.17408 − 0.00363 = 0.17045`, within `0.00003` of
`e⁵E₁(5)`, against `0.00365` for the truncated sum. -/
theorem dlmf_2_11_vi_euler_estimate :
    (0.17408 : ℝ) - 0.00363 = 0.17045 ∧ |Real.exp 5 * expIntE1 5 - 0.17045| < 0.00003 ∧
      0.00365 < |Real.exp 5 * expIntE1 5 - 0.17408| := by
  obtain ⟨l, u⟩ := dlmf_2_11_26
  refine ⟨by norm_num, abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩, ?_⟩
  rw [abs_sub_comm, abs_of_pos (by linarith)]
  linarith

end Numerics

end Azurite.DLMF
