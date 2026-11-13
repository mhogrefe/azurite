/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section18
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.Order

/-!
# DLMF §5.18(ii): the `q`-Gamma function

Formalization of <https://dlmf.nist.gov/5.18>, subsection (ii), except 5.18.10
(`Section18Limit.lean`). Throughout `0 < q < 1` (real) and `z` is complex.

* 5.18.4: `Γ_q(z) = (q; q)_∞ (1 − q)^{1−z} / (q^z; q)_∞` (`qGamma`, definition). Where
  `(q^z; q)_∞ = 0`, i.e. at the poles `z = −n + 2πik/ln q`, Lean's division gives `0`.
* 5.18.5: `Γ_q(1) = Γ_q(2) = 1` (`dlmf_5_18_5`).
* 5.18.6: `n!_q = Γ_q(n + 1)` (`dlmf_5_18_6`).
* 5.18.7: `Γ_q(z + 1) = (1 − q^z)/(1 − q) Γ_q(z)` for `q^z ≠ 1` (`dlmf_5_18_7`); at `q^z = 1`
  the right side is `0` while `Γ_q(z + 1)` is a finite nonzero number in general.
* "`ln Γ_q(x)` is convex for `x > 0`": on `(0, ∞)`, `Γ_q(x) = exp(lnGammaQ q x)`
  (`qGamma_ofReal`), with `lnGammaQ q x = ∑_k (ln(1 − q^{k+1}) − ln(1 − q^{x+k})) +
  (1 − x) ln(1 − q)` strictly convex (`strictConvexOn_lnGammaQ`), since
  `t ↦ −ln(1 − e^{−ct})` has second derivative `(w / sinh w)² / t² > 0`, `w = ct/2`;
  `dlmf_5_18_ii_convex`.
* "the analog of the Bohr–Mollerup theorem holds" (`dlmf_5_18_ii_bohr_mollerup`): a positive `f`
  on `(0, ∞)` with `f(x + 1) = (1 − q^x)/(1 − q) f(x)`, `f(1) = 1` and `ln f` convex is `Γ_q`.
  Proof by the convexity squeeze `eq_of_convexOn_of_add_one`.
* 5.18.8, 5.18.9: for `0 < q < r < 1`, `Γ_q(x) < Γ_r(x)` on `(0, 1) ∪ (2, ∞)` and `Γ_q(x) >
  Γ_r(x)` on `(1, 2)` (in `ℂ`'s partial order; both sides are real). The difference
  `ln Γ_r − ln Γ_q` is strictly convex, because `w / sinh w` is strictly decreasing, and it
  vanishes at `1` and `2`.
-/

open Complex Filter Topology Finset
open scoped ComplexOrder

namespace Azurite.DLMF

/-- DLMF 5.18.4: `Γ_q(z) = (q; q)_∞ (1 − q)^{1−z} / (q^z; q)_∞` (for `0 < q < 1`). -/
noncomputable def qGamma (q : ℝ) (z : ℂ) : ℂ :=
  qPochhammerInf q q * ((1 - q : ℝ) : ℂ) ^ (1 - z) / qPochhammerInf ((q : ℂ) ^ z) q

theorem dlmf_5_18_4 (q : ℝ) (z : ℂ) :
    qGamma q z =
      qPochhammerInf q q * ((1 - q : ℝ) : ℂ) ^ (1 - z) / qPochhammerInf ((q : ℂ) ^ z) q := rfl

section Basic

variable {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
include hq0 hq1

theorem norm_ofReal_lt_one_of_pos : ‖(q : ℂ)‖ < 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq0]; exact hq1

omit hq0 in
theorem one_sub_ofReal_ne_zero : (1 : ℂ) - q ≠ 0 := by
  rw [sub_ne_zero]
  intro h
  have : (1 : ℝ) = q := by exact_mod_cast h
  linarith

theorem qPochhammerInf_self_ne_zero : qPochhammerInf q q ≠ 0 := by
  apply qPochhammerInf_ne_zero (norm_ofReal_lt_one_of_pos hq0 hq1)
  intro k h
  have e : (q : ℂ) * (q : ℂ) ^ k = ((q ^ (k + 1) : ℝ) : ℂ) := by push_cast; ring
  rw [e, sub_eq_zero] at h
  have h' : q ^ (k + 1) = 1 := by exact_mod_cast h.symm
  have : q ^ (k + 1) < 1 := pow_lt_one₀ hq0.le hq1 (by omega)
  linarith

theorem qPochhammerInf_cpow_succ (z : ℂ) :
    qPochhammerInf ((q : ℂ) ^ z) q =
      (1 - (q : ℂ) ^ z) * qPochhammerInf ((q : ℂ) ^ (z + 1)) q := by
  have hq : (q : ℂ) ≠ 0 := ofReal_ne_zero.2 hq0.ne'
  have hpow : (q : ℂ) ^ (z + 1) = (q : ℂ) ^ z * q := by rw [cpow_add _ _ hq, cpow_one]
  have hm : Multipliable fun k : ℕ => 1 - (q : ℂ) ^ (z + 1) * (q : ℂ) ^ k :=
    multipliable_qPochhammer (norm_ofReal_lt_one_of_pos hq0 hq1)
  unfold qPochhammerInf
  rw [tprod_eq_zero_mul' ?_]
  · simp only [pow_zero, mul_one]
    congr 1
    refine tprod_congr fun k => ?_
    rw [hpow, pow_succ]; ring
  · refine hm.congr fun k => ?_
    rw [hpow, pow_succ]; ring

/-- DLMF 5.18.7: `Γ_q(z + 1) = (1 − q^z)/(1 − q) Γ_q(z)` (for `q^z ≠ 1`). -/
theorem dlmf_5_18_7 {z : ℂ} (hz : (q : ℂ) ^ z ≠ 1) :
    qGamma q (z + 1) = (1 - (q : ℂ) ^ z) / (1 - q) * qGamma q z := by
  have h1 := one_sub_ofReal_ne_zero hq1
  have hz' : (1 : ℂ) - (q : ℂ) ^ z ≠ 0 := sub_ne_zero.2 (Ne.symm hz)
  have h1' : ((1 - q : ℝ) : ℂ) ≠ 0 := by push_cast; exact h1
  have hc : ((1 - q : ℝ) : ℂ) ^ (1 - z) = ((1 - q : ℝ) : ℂ) ^ (1 - (z + 1)) * (1 - q) := by
    rw [show (1 : ℂ) - z = (1 - (z + 1)) + 1 by ring, cpow_add _ _ h1', cpow_one]
    push_cast; ring
  unfold qGamma
  rw [qPochhammerInf_cpow_succ hq0 hq1 z, hc]
  by_cases hD : qPochhammerInf ((q : ℂ) ^ (z + 1)) q = 0
  · simp [hD]
  · field_simp

theorem qGamma_one : qGamma q 1 = 1 := by
  unfold qGamma
  rw [cpow_one, sub_self, cpow_zero, mul_one, div_self (qPochhammerInf_self_ne_zero hq0 hq1)]

/-- DLMF 5.18.5: `Γ_q(1) = Γ_q(2) = 1`. -/
theorem dlmf_5_18_5 : qGamma q 1 = 1 ∧ qGamma q 2 = 1 := by
  refine ⟨qGamma_one hq0 hq1, ?_⟩
  have hq1' : (q : ℂ) ^ (1 : ℂ) ≠ 1 := by
    rw [cpow_one]; exact_mod_cast hq1.ne
  have h := dlmf_5_18_7 hq0 hq1 hq1'
  rw [show (1 : ℂ) + 1 = 2 by norm_num, qGamma_one hq0 hq1, cpow_one] at h
  rw [h, div_self (one_sub_ofReal_ne_zero hq1), one_mul]

/-- DLMF 5.18.6: `n!_q = Γ_q(n + 1)`. -/
theorem dlmf_5_18_6 (n : ℕ) : qFactorial q n = qGamma q (n + 1) := by
  have hq' : (q : ℂ) ≠ 1 := by exact_mod_cast hq1.ne
  induction n with
  | zero => simp [qGamma_one hq0 hq1]
  | succ n ih =>
    have hpow : (q : ℂ) ^ ((n : ℂ) + 1) = (q : ℂ) ^ (n + 1) := by
      rw [show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by push_cast; ring, cpow_natCast]
    have hn : (q : ℂ) ^ ((n : ℂ) + 1) ≠ 1 := by
      rw [hpow]
      have : q ^ (n + 1) < 1 := pow_lt_one₀ hq0.le hq1 (by omega)
      exact_mod_cast this.ne
    have hgeom : ∑ j ∈ range (n + 1), (q : ℂ) ^ j = (1 - (q : ℂ) ^ (n + 1)) / (1 - q) := by
      rw [geom_sum_eq hq', ← neg_div_neg_eq]; ring_nf
    rw [qFactorial_succ, ih, show ((n + 1 : ℕ) : ℂ) + 1 = ((n : ℂ) + 1) + 1 by push_cast; ring,
      dlmf_5_18_7 hq0 hq1 hn, hpow, hgeom, mul_comm]

end Basic

/-! ### Real arguments: `Γ_q(x) = exp(lnGammaQ q x)` -/

/-- `ln Γ_q(x) = ∑_k (ln(1 − q^{k+1}) − ln(1 − q^{x+k})) + (1 − x) ln(1 − q)` for `x > 0`. -/
noncomputable def lnGammaQ (q x : ℝ) : ℝ :=
  ∑' k : ℕ, (Real.log (1 - q ^ (k + 1)) - Real.log (1 - q ^ (x + k))) +
    (1 - x) * Real.log (1 - q)

section Real

variable {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
include hq0 hq1

theorem rpow_add_natCast_lt_one {x : ℝ} (hx : 0 < x) (k : ℕ) : q ^ (x + k) < 1 :=
  Real.rpow_lt_one hq0.le hq1 (by positivity)

theorem summable_log_one_sub_pow_succ :
    Summable fun k : ℕ => Real.log (1 - q ^ (k + 1)) := by
  have hs : Summable fun k : ℕ => -(q ^ (k + 1)) := by
    have := (summable_geometric_of_lt_one hq0.le hq1).mul_left q
    exact (this.congr fun k => by ring).neg
  simpa [sub_eq_add_neg] using Real.summable_log_one_add_of_summable hs

theorem summable_log_one_sub_rpow (x : ℝ) :
    Summable fun k : ℕ => Real.log (1 - q ^ (x + k)) := by
  have hs : Summable fun k : ℕ => -(q ^ (x + k)) := by
    have := (summable_geometric_of_lt_one hq0.le hq1).mul_left (q ^ x)
    refine (this.congr fun k => ?_).neg
    rw [Real.rpow_add hq0, Real.rpow_natCast]
  simpa [sub_eq_add_neg] using Real.summable_log_one_add_of_summable hs

/-- For `x > 0`, `Γ_q(x) = exp(lnGammaQ q x)` (in particular `Γ_q(x)` is real and positive). -/
theorem qGamma_ofReal {x : ℝ} (hx : 0 < x) :
    qGamma q x = (Real.exp (lnGammaQ q x) : ℂ) := by
  have hpos1 : ∀ k : ℕ, 0 < 1 - q ^ (k + 1) := fun k =>
    sub_pos.2 (pow_lt_one₀ hq0.le hq1 (by omega))
  have hpos2 : ∀ k : ℕ, 0 < 1 - q ^ (x + k) := fun k =>
    sub_pos.2 (rpow_add_natCast_lt_one hq0 hq1 hx k)
  have hs1 := summable_log_one_sub_pow_succ hq0 hq1
  have hs2 := summable_log_one_sub_rpow hq0 hq1 x
  have hA := (Real.hasProd_of_hasSum_log hpos1 hs1.hasSum).map Complex.ofRealHom
    Complex.continuous_ofReal
  have hB := (Real.hasProd_of_hasSum_log hpos2 hs2.hasSum).map Complex.ofRealHom
    Complex.continuous_ofReal
  have hA' : HasProd (fun k : ℕ => ((1 - q ^ (k + 1) : ℝ) : ℂ))
      (Real.exp (∑' k : ℕ, Real.log (1 - q ^ (k + 1))) : ℂ) := hA
  have hB' : HasProd (fun k : ℕ => ((1 - q ^ (x + k) : ℝ) : ℂ))
      (Real.exp (∑' k : ℕ, Real.log (1 - q ^ (x + k))) : ℂ) := hB
  have e1 : qPochhammerInf q q = (Real.exp (∑' k : ℕ, Real.log (1 - q ^ (k + 1))) : ℂ) := by
    rw [qPochhammerInf, ← hA'.tprod_eq]
    refine tprod_congr fun k => ?_
    push_cast; ring
  have e2 : qPochhammerInf ((q : ℂ) ^ (x : ℂ)) q =
      (Real.exp (∑' k : ℕ, Real.log (1 - q ^ (x + k))) : ℂ) := by
    rw [qPochhammerInf, ← hB'.tprod_eq]
    refine tprod_congr fun k => ?_
    rw [Real.rpow_add hq0, Real.rpow_natCast, ← Complex.ofReal_cpow hq0.le]
    push_cast; ring
  have e3 : ((1 - q : ℝ) : ℂ) ^ (1 - (x : ℂ)) = (Real.exp ((1 - x) * Real.log (1 - q)) : ℂ) := by
    rw [show (1 : ℂ) - x = ((1 - x : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (by linarith), Real.rpow_def_of_pos (by linarith), mul_comm]
  unfold qGamma lnGammaQ
  rw [e1, e2, e3, hs1.tsum_sub hs2, ← ofReal_mul, ← ofReal_div]
  congr 1
  rw [Real.exp_add, Real.exp_sub]
  ring

theorem lnGammaQ_one : lnGammaQ q 1 = 0 := by
  have h := qGamma_ofReal hq0 hq1 one_pos
  rw [ofReal_one, qGamma_one hq0 hq1] at h
  have h' : Real.exp (lnGammaQ q 1) = 1 := by exact_mod_cast h.symm
  simpa using h'

theorem lnGammaQ_two : lnGammaQ q 2 = 0 := by
  have h := qGamma_ofReal hq0 hq1 two_pos
  rw [show ((2 : ℝ) : ℂ) = 2 by norm_num, (dlmf_5_18_5 hq0 hq1).2] at h
  have h' : Real.exp (lnGammaQ q 2) = 1 := by exact_mod_cast h.symm
  simpa using h'

theorem lnGammaQ_add_one {x : ℝ} (hx : 0 < x) :
    lnGammaQ q (x + 1) = lnGammaQ q x + Real.log ((1 - q ^ x) / (1 - q)) := by
  have hqx : q ^ x < 1 := Real.rpow_lt_one hq0.le hq1 hx
  have hz : (q : ℂ) ^ (x : ℂ) ≠ 1 := by
    rw [← Complex.ofReal_cpow hq0.le]; exact_mod_cast hqx.ne
  have h := dlmf_5_18_7 hq0 hq1 hz
  rw [← ofReal_one, ← ofReal_add, qGamma_ofReal hq0 hq1 (by linarith),
    qGamma_ofReal hq0 hq1 hx, ← Complex.ofReal_cpow hq0.le] at h
  have h' : Real.exp (lnGammaQ q (x + 1)) =
      (1 - q ^ x) / (1 - q) * Real.exp (lnGammaQ q x) := by exact_mod_cast h
  have hpos : 0 < (1 - q ^ x) / (1 - q) := div_pos (by linarith) (by linarith)
  have := congrArg Real.log h'
  rw [Real.log_exp, Real.log_mul hpos.ne' (Real.exp_pos _).ne', Real.log_exp] at this
  linarith

end Real

/-! ### Convexity -/

/-- `φ_c(t) = −ln(1 − e^{−ct})`. -/
noncomputable def qPhi (c t : ℝ) : ℝ := -Real.log (1 - Real.exp (-(c * t)))

theorem exp_neg_mul_lt_one {c t : ℝ} (hc : 0 < c) (ht : 0 < t) : Real.exp (-(c * t)) < 1 :=
  Real.exp_lt_one_iff.2 (by nlinarith)

theorem hasDerivAt_qPhi {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    HasDerivAt (qPhi c) (-(c * Real.exp (-(c * t))) / (1 - Real.exp (-(c * t)))) t := by
  have hE : HasDerivAt (fun t => Real.exp (-(c * t))) (Real.exp (-(c * t)) * -(c * 1)) t :=
    (((hasDerivAt_id t).const_mul c).neg).exp
  have hne : 1 - Real.exp (-(c * t)) ≠ 0 := (sub_pos.2 (exp_neg_mul_lt_one hc ht)).ne'
  have h := ((hasDerivAt_const t (1 : ℝ)).sub hE).log hne
  convert h.neg using 1
  · funext y; simp [qPhi]
  · simp only [Pi.sub_apply]; field_simp; ring

theorem hasDerivAt_qPhi_deriv {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    HasDerivAt (fun t => -(c * Real.exp (-(c * t))) / (1 - Real.exp (-(c * t))))
      (c ^ 2 * Real.exp (-(c * t)) / (1 - Real.exp (-(c * t))) ^ 2) t := by
  have hE : HasDerivAt (fun t => Real.exp (-(c * t))) (Real.exp (-(c * t)) * -(c * 1)) t :=
    (((hasDerivAt_id t).const_mul c).neg).exp
  have hne : 1 - Real.exp (-(c * t)) ≠ 0 := (sub_pos.2 (exp_neg_mul_lt_one hc ht)).ne'
  have h := ((hE.const_mul c).neg).div ((hasDerivAt_const t (1 : ℝ)).sub hE) hne
  convert h using 1
  simp only [Pi.sub_apply, Pi.neg_apply]; field_simp; ring

/-- `e^{−2w}/(1 − e^{−2w})² = 1/(4 sinh² w)`. -/
theorem exp_neg_two_mul_div_sq {w : ℝ} (hw : 0 < w) :
    Real.exp (-(2 * w)) / (1 - Real.exp (-(2 * w))) ^ 2 = 1 / (4 * Real.sinh w ^ 2) := by
  set y := Real.exp (-w) with hy
  have hy0 : 0 < y := Real.exp_pos _
  have hy1 : y < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have h2 : Real.exp (-(2 * w)) = y ^ 2 := by
    rw [hy, ← Real.exp_nat_mul]; ring_nf
  have hs : Real.sinh w = (y⁻¹ - y) / 2 := by
    rw [Real.sinh_eq, hy, Real.exp_neg, inv_inv]
  have hy2 : 1 - y ^ 2 ≠ 0 := by nlinarith
  have hyy : y⁻¹ - y ≠ 0 := by
    have : 1 < y⁻¹ := (one_lt_inv₀ hy0).2 hy1
    linarith
  rw [h2, hs]
  field_simp
  ring

/-- `c² e^{−ct}/(1 − e^{−ct})² = (w / sinh w)² / t²` with `w = ct/2`. -/
theorem qPhi_deriv2_eq {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    c ^ 2 * Real.exp (-(c * t)) / (1 - Real.exp (-(c * t))) ^ 2 =
      ((c * t / 2) / Real.sinh (c * t / 2)) ^ 2 / t ^ 2 := by
  have hw : 0 < c * t / 2 := by positivity
  have h := exp_neg_two_mul_div_sq hw
  rw [show 2 * (c * t / 2) = c * t by ring] at h
  have hs : Real.sinh (c * t / 2) ≠ 0 := (Real.sinh_pos_iff.2 hw).ne'
  rw [mul_div_assoc, h]
  field_simp
  ring

theorem strictConvexOn_sinh : StrictConvexOn ℝ (Set.Ici 0) Real.sinh := by
  apply strictConvexOn_of_deriv2_pos (convex_Ici 0) Real.continuous_sinh.continuousOn
  intro x hx
  rw [interior_Ici, Set.mem_Ioi] at hx
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id,
    Real.deriv_sinh, Real.deriv_cosh]
  exact Real.sinh_pos_iff.2 hx

/-- `sinh w / w` is strictly increasing on `(0, ∞)`. -/
theorem sinh_div_self_lt {v u : ℝ} (hv : 0 < v) (hvu : v < u) :
    Real.sinh v / v < Real.sinh u / u := by
  have h := strictConvexOn_sinh.secant_strict_mono (a := 0) (x := v) (y := u)
    (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hv.le) (Set.mem_Ici.2 (hv.trans hvu).le) hv.ne'
    (hv.trans hvu).ne' hvu
  simpa using h

/-- `w / sinh w` is strictly decreasing on `(0, ∞)`. -/
theorem div_sinh_lt {v u : ℝ} (hv : 0 < v) (hvu : v < u) : u / Real.sinh u < v / Real.sinh v := by
  have hu : 0 < u := hv.trans hvu
  have h := sinh_div_self_lt hv hvu
  have hsv : 0 < Real.sinh v / v := div_pos (Real.sinh_pos_iff.2 hv) hv
  have := one_div_lt_one_div_of_lt hsv h
  simpa [one_div_div] using this

/-- A function with positive second derivative on `(a, ∞)` is strictly convex there. -/
theorem strictConvexOn_Ioi_of_hasDerivAt2 {f f' f'' : ℝ → ℝ} {a : ℝ}
    (h1 : ∀ x, a < x → HasDerivAt f (f' x) x) (h2 : ∀ x, a < x → HasDerivAt f' (f'' x) x)
    (hpos : ∀ x, a < x → 0 < f'' x) : StrictConvexOn ℝ (Set.Ioi a) f := by
  apply strictConvexOn_of_deriv2_pos (convex_Ioi a)
  · exact fun x hx => (h1 x hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi, Set.mem_Ioi] at hx
    have heq : deriv f =ᶠ[𝓝 x] f' := by
      filter_upwards [Ioi_mem_nhds hx] with y hy using (h1 y hy).deriv
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
    rw [heq.deriv_eq, (h2 x hx).deriv]
    exact hpos x hx

/-- `x ↦ A + φ_c(x + s)` is strictly convex on `(0, ∞)` (`c > 0`, `s ≥ 0`). -/
theorem strictConvexOn_qPhi_shift {c s : ℝ} (hc : 0 < c) (hs : 0 ≤ s) (A : ℝ) :
    StrictConvexOn ℝ (Set.Ioi 0) fun x => A + qPhi c (x + s) := by
  refine strictConvexOn_Ioi_of_hasDerivAt2
    (f' := fun x => -(c * Real.exp (-(c * (x + s)))) / (1 - Real.exp (-(c * (x + s)))))
    (f'' := fun x => c ^ 2 * Real.exp (-(c * (x + s))) / (1 - Real.exp (-(c * (x + s)))) ^ 2)
    (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_)
  · exact ((hasDerivAt_qPhi hc (by linarith)).comp_add_const x s).const_add A
  · exact (hasDerivAt_qPhi_deriv hc (by linarith)).comp_add_const x s
  · have hne : 1 - Real.exp (-(c * (x + s))) ≠ 0 :=
      (sub_pos.2 (exp_neg_mul_lt_one hc (by linarith))).ne'
    positivity

/-- For `0 < c₂ < c₁`, `x ↦ A + φ_{c₂}(x + s) − φ_{c₁}(x + s)` is strictly convex on `(0, ∞)`. -/
theorem strictConvexOn_qPhi_sub_shift {c₁ c₂ s : ℝ} (hc₂ : 0 < c₂) (hc : c₂ < c₁) (hs : 0 ≤ s)
    (A : ℝ) : StrictConvexOn ℝ (Set.Ioi 0) fun x => A + (qPhi c₂ (x + s) - qPhi c₁ (x + s)) := by
  have hc₁ : 0 < c₁ := hc₂.trans hc
  refine strictConvexOn_Ioi_of_hasDerivAt2
    (f' := fun x => -(c₂ * Real.exp (-(c₂ * (x + s)))) / (1 - Real.exp (-(c₂ * (x + s)))) -
      -(c₁ * Real.exp (-(c₁ * (x + s)))) / (1 - Real.exp (-(c₁ * (x + s)))))
    (f'' := fun x => c₂ ^ 2 * Real.exp (-(c₂ * (x + s))) / (1 - Real.exp (-(c₂ * (x + s)))) ^ 2 -
      c₁ ^ 2 * Real.exp (-(c₁ * (x + s))) / (1 - Real.exp (-(c₁ * (x + s)))) ^ 2)
    (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_)
  · exact (((hasDerivAt_qPhi hc₂ (by linarith)).comp_add_const x s).sub
      ((hasDerivAt_qPhi hc₁ (by linarith)).comp_add_const x s)).const_add A
  · exact ((hasDerivAt_qPhi_deriv hc₂ (by linarith)).comp_add_const x s).sub
      ((hasDerivAt_qPhi_deriv hc₁ (by linarith)).comp_add_const x s)
  · have ht : 0 < x + s := by linarith
    rw [qPhi_deriv2_eq hc₂ ht, qPhi_deriv2_eq hc₁ ht, sub_pos]
    have hw₂ : 0 < c₂ * (x + s) / 2 := by positivity
    have hlt : c₂ * (x + s) / 2 < c₁ * (x + s) / 2 := by
      have := mul_lt_mul_of_pos_right hc ht; linarith
    have h := div_sinh_lt hw₂ hlt
    have h0 : 0 < c₁ * (x + s) / 2 / Real.sinh (c₁ * (x + s) / 2) :=
      div_pos (hw₂.trans hlt) (Real.sinh_pos_iff.2 (hw₂.trans hlt))
    have ht2 : 0 < (x + s) ^ 2 := by positivity
    exact div_lt_div_of_pos_right (pow_lt_pow_left₀ h h0.le two_ne_zero) ht2

/-- A `tsum` of strictly convex functions is strictly convex. -/
theorem strictConvexOn_tsum {s : Set ℝ} (hs : Convex ℝ s) {f : ℕ → ℝ → ℝ}
    (hf : ∀ k, StrictConvexOn ℝ s (f k)) (hsum : ∀ x ∈ s, Summable fun k => f k x) :
    StrictConvexOn ℝ s fun x => ∑' k, f k x := by
  refine ⟨hs, fun x hx y hy hxy a b ha hb hab => ?_⟩
  have hxy' := hs hx hy ha.le hb.le hab
  have hsx := hsum x hx
  have hsy := hsum y hy
  simp only [smul_eq_mul] at *
  rw [← tsum_mul_left, ← tsum_mul_left, ← (hsx.mul_left a).tsum_add (hsy.mul_left b)]
  refine hasSum_lt (i := 0) (fun k => ((hf k).2 hx hy hxy ha hb hab).le) ((hf 0).2 hx hy hxy ha hb
    hab) (hsum _ hxy').hasSum ((hsx.mul_left a).add (hsy.mul_left b)).hasSum

theorem convexOn_affine (A B : ℝ) : ConvexOn ℝ (Set.Ioi 0) fun x : ℝ => A + B * x :=
  ⟨convex_Ioi 0, fun x _ y _ a b _ _ hab => le_of_eq (by
    simp only [smul_eq_mul]; linear_combination A * hab.symm)⟩

/-- A strictly convex `D` on `(0, ∞)` with `D(1) = D(2) = 0` is negative on `(1, 2)` and positive
on `(0, 1) ∪ (2, ∞)`. -/
theorem strictConvexOn_one_two {D : ℝ → ℝ} (h : StrictConvexOn ℝ (Set.Ioi 0) D) (h1 : D 1 = 0)
    (h2 : D 2 = 0) :
    (∀ x, 1 < x → x < 2 → D x < 0) ∧ (∀ x, 0 < x → x < 1 → 0 < D x) ∧
      (∀ x, 2 < x → 0 < D x) := by
  have m1 : (1 : ℝ) ∈ Set.Ioi 0 := Set.mem_Ioi.2 one_pos
  have m2 : (2 : ℝ) ∈ Set.Ioi 0 := Set.mem_Ioi.2 two_pos
  refine ⟨fun x hx1 hx2 => ?_, fun x hx0 hx1 => ?_, fun x hx2 => ?_⟩
  · have := h.2 m1 m2 (by norm_num) (show 0 < 2 - x by linarith) (show 0 < x - 1 by linarith)
      (by ring)
    simp only [smul_eq_mul, h1, h2, mul_zero, add_zero] at this
    rwa [show (2 - x) * 1 + (x - 1) * 2 = x by ring] at this
  · have hx : x ∈ Set.Ioi 0 := hx0
    have h2x : (2 : ℝ) - x ≠ 0 := by linarith
    have := h.2 hx m2 (by linarith) (show 0 < 1 / (2 - x) by
      apply div_pos one_pos; linarith) (show 0 < (1 - x) / (2 - x) by
      apply div_pos <;> linarith) (by field_simp; ring)
    have e : 1 / (2 - x) * x + (1 - x) / (2 - x) * 2 = 1 := by
      field_simp; ring
    simp only [smul_eq_mul, h2, mul_zero, add_zero] at this
    rw [e, h1] at this
    exact (pos_iff_pos_of_mul_pos (by linarith [this] : 0 < 1 / (2 - x) * D x)).1
      (div_pos one_pos (by linarith)) |> fun h => by
        rcases lt_trichotomy (D x) 0 with hd | hd | hd
        · nlinarith [div_pos one_pos (show (0 : ℝ) < 2 - x by linarith)]
        · rw [hd] at this; simp at this
        · exact hd
  · have hx : x ∈ Set.Ioi 0 := Set.mem_Ioi.2 (by linarith)
    have hx1 : x - 1 ≠ 0 := by linarith
    have := h.2 m1 hx (by linarith) (show 0 < (x - 2) / (x - 1) by
      apply div_pos <;> linarith) (show 0 < 1 / (x - 1) by
      apply div_pos one_pos; linarith) (by field_simp; ring)
    have e : (x - 2) / (x - 1) * 1 + 1 / (x - 1) * x = 2 := by
      field_simp; ring
    simp only [smul_eq_mul, h1, mul_zero, zero_add] at this
    rw [e, h2] at this
    have hp : 0 < 1 / (x - 1) := div_pos one_pos (by linarith)
    rcases lt_trichotomy (D x) 0 with hd | hd | hd
    · nlinarith
    · rw [hd] at this; simp at this
    · exact hd

section Convexity

variable {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
include hq0 hq1

omit hq1 in
theorem rpow_eq_exp_qPhi (y : ℝ) : q ^ y = Real.exp (-(-Real.log q * y)) := by
  rw [Real.rpow_def_of_pos hq0]; ring_nf

omit hq1 in
theorem lnGammaQ_term_eq (k : ℕ) (x : ℝ) :
    Real.log (1 - q ^ (k + 1)) - Real.log (1 - q ^ (x + k)) =
      Real.log (1 - q ^ (k + 1)) + qPhi (-Real.log q) (x + k) := by
  rw [qPhi, ← rpow_eq_exp_qPhi hq0]; ring

theorem neg_log_pos : 0 < -Real.log q := neg_pos.2 (Real.log_neg hq0 hq1)

/-- `ln Γ_q` is strictly convex on `(0, ∞)`. -/
theorem strictConvexOn_lnGammaQ : StrictConvexOn ℝ (Set.Ioi 0) (lnGammaQ q) := by
  have hc := neg_log_pos hq0 hq1
  have hT : StrictConvexOn ℝ (Set.Ioi 0) fun x : ℝ =>
      ∑' k : ℕ, (Real.log (1 - q ^ (k + 1)) - Real.log (1 - q ^ (x + k))) := by
    refine strictConvexOn_tsum (convex_Ioi (0 : ℝ)) (fun k => ?_) (fun x _ =>
      (summable_log_one_sub_pow_succ hq0 hq1).sub (summable_log_one_sub_rpow hq0 hq1 x))
    have := strictConvexOn_qPhi_shift hc (by positivity : (0 : ℝ) ≤ k)
      (Real.log (1 - q ^ (k + 1)))
    exact this.congr fun x _ => (lnGammaQ_term_eq hq0 k x).symm
  have hL := convexOn_affine (Real.log (1 - q)) (-Real.log (1 - q))
  refine (hT.add_convexOn hL).congr fun x _ => ?_
  simp only [Pi.add_apply, lnGammaQ]
  ring

/-- "`ln Γ_q(x)` is convex for `x > 0`." -/
theorem dlmf_5_18_ii_convex :
    ConvexOn ℝ (Set.Ioi 0) fun x : ℝ => Real.log (qGamma q x).re := by
  refine (strictConvexOn_lnGammaQ hq0 hq1).convexOn.congr fun x hx => ?_
  rw [qGamma_ofReal hq0 hq1 hx, ofReal_re, Real.log_exp]

end Convexity

/-! ### The `q`-Bohr–Mollerup theorem -/

/-- Two convex functions on `(0, ∞)` with the same increments `F(x + 1) − F(x) = λ(x)`, the same
value at `1`, and `λ(n + 1) − λ(n) → 0`, coincide on `(0, ∞)`. -/
theorem eq_of_convexOn_of_add_one {F G lam : ℝ → ℝ} (hF : ConvexOn ℝ (Set.Ioi 0) F)
    (hG : ConvexOn ℝ (Set.Ioi 0) G) (hFe : ∀ x, 0 < x → F (x + 1) = F x + lam x)
    (hGe : ∀ x, 0 < x → G (x + 1) = G x + lam x) (h1 : F 1 = G 1)
    (hlam : Tendsto (fun n : ℕ => lam ((n : ℝ) + 1) - lam n) atTop (𝓝 0)) {x : ℝ}
    (hx : 0 < x) : F x = G x := by
  -- periodicity of the difference
  have hper : ∀ y, 0 < y → ∀ m : ℕ, F (y + m) - G (y + m) = F y - G y := by
    intro y hy m
    induction m with
    | zero => simp
    | succ m ih =>
      have hym : 0 < y + m := by positivity
      rw [Nat.cast_succ, ← add_assoc, hFe _ hym, hGe _ hym, ← ih]; ring
  -- the convexity squeeze
  have hsq : ∀ {H : ℝ → ℝ}, ConvexOn ℝ (Set.Ioi 0) H → (∀ x, 0 < x → H (x + 1) = H x + lam x) →
      ∀ y, 0 < y → y < 1 → ∀ n : ℕ, 1 ≤ n →
        lam n * y ≤ H (n + 1 + y) - H (n + 1) ∧ H (n + 1 + y) - H (n + 1) ≤ lam (n + 1) * y := by
    intro H hH hHe y hy0 hy1 n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have m0 : (n : ℝ) ∈ Set.Ioi 0 := hn0
    have m1 : (n : ℝ) + 1 ∈ Set.Ioi 0 := Set.mem_Ioi.2 (by linarith)
    have my : (n : ℝ) + 1 + y ∈ Set.Ioi 0 := Set.mem_Ioi.2 (by linarith)
    have m2 : (n : ℝ) + 1 + 1 ∈ Set.Ioi 0 := Set.mem_Ioi.2 (by linarith)
    have lo := hH.secant_mono m1 m0 my (by linarith) (by linarith) (by linarith)
    have hi := hH.secant_mono m1 my m2 (by linarith) (by linarith) (by linarith)
    have e0 : (H n - H (n + 1)) / ((n : ℝ) - (n + 1)) = lam n := by
      rw [hHe _ hn0, show (n : ℝ) - (n + 1) = -1 by ring]; ring
    have e1 : (H (n + 1 + 1) - H (n + 1)) / ((n : ℝ) + 1 + 1 - (n + 1)) = lam (n + 1) := by
      rw [hHe _ (by linarith : (0 : ℝ) < n + 1), show (n : ℝ) + 1 + 1 - (n + 1) = 1 by ring]
      ring
    rw [e0, show (n : ℝ) + 1 + y - (n + 1) = y by ring, le_div_iff₀ hy0] at lo
    rw [e1, show (n : ℝ) + 1 + y - (n + 1) = y by ring, div_le_iff₀ hy0] at hi
    exact ⟨lo, hi⟩
  -- the fractional case
  have hfrac : ∀ y, 0 < y → y < 1 → F y = G y := by
    intro y hy0 hy1
    have hb : ∀ n : ℕ, 1 ≤ n → |F y - G y| ≤ |lam ((n : ℝ) + 1) - lam n| := by
      intro n hn
      obtain ⟨a1, a2⟩ := hsq hF hFe y hy0 hy1 n hn
      obtain ⟨b1, b2⟩ := hsq hG hGe y hy0 hy1 n hn
      have e1 := hper y hy0 (n + 1)
      have e2 := hper 1 one_pos n
      push_cast at e1 e2
      rw [h1, sub_self] at e2
      have hd : F y - G y = (F (n + 1 + y) - F (n + 1)) - (G (n + 1 + y) - G (n + 1)) := by
        rw [← e1, show y + (n + 1) = (n : ℝ) + 1 + y by ring,
          show (n : ℝ) + 1 = 1 + n by ring]
        linarith
      rw [hd, abs_le]
      have hl : lam (n : ℝ) ≤ lam ((n : ℝ) + 1) ∨ lam ((n : ℝ) + 1) < lam n := le_or_gt _ _
      constructor
      · have : -(|lam ((n : ℝ) + 1) - lam n|) ≤ -(lam ((n : ℝ) + 1) - lam n) * y := by
          rcases hl with hl | hl
          · rw [abs_of_nonneg (by linarith)]; nlinarith
          · rw [abs_of_neg (by linarith)]; nlinarith
        nlinarith
      · have : (lam ((n : ℝ) + 1) - lam n) * y ≤ |lam ((n : ℝ) + 1) - lam n| := by
          rcases hl with hl | hl
          · rw [abs_of_nonneg (by linarith)]; nlinarith
          · rw [abs_of_neg (by linarith)]; nlinarith
        nlinarith
    have ht : Tendsto (fun n : ℕ => |lam ((n : ℝ) + 1) - lam n|) atTop (𝓝 0) := by
      simpa using hlam.abs
    have : |F y - G y| ≤ 0 :=
      ge_of_tendsto ht (eventually_atTop.2 ⟨1, fun n hn => hb n hn⟩)
    have := abs_nonpos_iff.1 this
    linarith
  -- general `x`
  set m := ⌊x⌋₊ with hm
  have hmx : (m : ℝ) ≤ x := Nat.floor_le hx.le
  have hxm : x < m + 1 := Nat.lt_floor_add_one x
  rcases eq_or_lt_of_le hmx with he | hlt
  · have hm1 : 1 ≤ m := by
      by_contra h
      push Not at h
      have : m = 0 := by omega
      rw [this] at he; simp at he; linarith
    have e := hper 1 one_pos (m - 1)
    rw [Nat.cast_sub hm1, Nat.cast_one, show (1 : ℝ) + (m - 1) = m by ring, h1] at e
    rw [← he]
    linarith
  · have hy0 : 0 < x - m := by linarith
    have e := hper (x - m) hy0 m
    rw [sub_add_cancel] at e
    have := hfrac (x - m) hy0 (by linarith)
    linarith

section BohrMollerup

variable {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
include hq0 hq1

theorem tendsto_log_one_sub_pow_div :
    Tendsto (fun n : ℕ => Real.log ((1 - q ^ (n : ℝ)) / (1 - q))) atTop
      (𝓝 (Real.log (1 / (1 - q)))) := by
  have h : Tendsto (fun n : ℕ => (1 - q ^ n) / (1 - q)) atTop (𝓝 ((1 - 0) / (1 - q))) :=
    ((tendsto_const_nhds.sub (tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1)).div_const _)
  rw [sub_zero] at h
  have hc := (Real.continuousAt_log (by
    have : 0 < 1 / (1 - q) := div_pos one_pos (by linarith)
    exact this.ne')).tendsto.comp h
  refine hc.congr fun n => ?_
  simp [Real.rpow_natCast]

/-- DLMF §5.18(ii), "the analog of the Bohr–Mollerup theorem (§5.5(iv)) holds": a positive
function `f` on `(0, ∞)` with `f(x + 1) = (1 − q^x)/(1 − q) f(x)`, `f(1) = 1` and `ln f` convex is
`Γ_q`. -/
theorem dlmf_5_18_ii_bohr_mollerup {f : ℝ → ℝ} (hpos : ∀ x, 0 < x → 0 < f x)
    (hfeq : ∀ x, 0 < x → f (x + 1) = (1 - q ^ x) / (1 - q) * f x) (hone : f 1 = 1)
    (hconv : ConvexOn ℝ (Set.Ioi 0) (Real.log ∘ f)) {x : ℝ} (hx : 0 < x) :
    (f x : ℂ) = qGamma q x := by
  set lam : ℝ → ℝ := fun x => Real.log ((1 - q ^ x) / (1 - q)) with hlam_def
  have hFe : ∀ x, 0 < x → (Real.log ∘ f) (x + 1) = (Real.log ∘ f) x + lam x := by
    intro x hx
    have hp : 0 < (1 - q ^ x) / (1 - q) :=
      div_pos (sub_pos.2 (Real.rpow_lt_one hq0.le hq1 hx)) (by linarith)
    simp only [Function.comp_apply, hfeq x hx, hlam_def]
    rw [Real.log_mul hp.ne' (hpos x hx).ne', add_comm]
  have hGe : ∀ x, 0 < x → lnGammaQ q (x + 1) = lnGammaQ q x + lam x :=
    fun x hx => lnGammaQ_add_one hq0 hq1 hx
  have h1 : (Real.log ∘ f) 1 = lnGammaQ q 1 := by
    simp [hone, lnGammaQ_one hq0 hq1]
  have hl := tendsto_log_one_sub_pow_div hq0 hq1
  have hl1 : Tendsto (fun n : ℕ => lam ((n : ℝ) + 1)) atTop (𝓝 (Real.log (1 / (1 - q)))) := by
    have := hl.comp (tendsto_add_atTop_nat 1)
    refine this.congr fun n => ?_
    simp only [Function.comp_apply, hlam_def, Nat.cast_add, Nat.cast_one]
  have hlam : Tendsto (fun n : ℕ => lam ((n : ℝ) + 1) - lam n) atTop (𝓝 0) := by
    have := hl1.sub hl
    rw [sub_self] at this
    exact this
  have h := eq_of_convexOn_of_add_one hconv (strictConvexOn_lnGammaQ hq0 hq1).convexOn hFe hGe h1
    hlam hx
  rw [qGamma_ofReal hq0 hq1 hx, ← h]
  simp [Real.exp_log (hpos x hx)]

end BohrMollerup

/-! ### 5.18.8 and 5.18.9 -/

section Comparison

variable {q r : ℝ} (hq0 : 0 < q) (hqr : q < r) (hr1 : r < 1)
include hq0 hqr hr1

/-- `ln Γ_r − ln Γ_q` is strictly convex on `(0, ∞)` for `0 < q < r < 1`. -/
theorem strictConvexOn_lnGammaQ_sub :
    StrictConvexOn ℝ (Set.Ioi 0) fun x => lnGammaQ r x - lnGammaQ q x := by
  have hq1 : q < 1 := hqr.trans hr1
  have hr0 : 0 < r := hq0.trans hqr
  have hcr := neg_log_pos hr0 hr1
  have hc : -Real.log r < -Real.log q := neg_lt_neg (Real.log_lt_log hq0 hqr)
  have hT : StrictConvexOn ℝ (Set.Ioi 0) fun x : ℝ =>
      ∑' k : ℕ, ((Real.log (1 - r ^ (k + 1)) - Real.log (1 - r ^ (x + k))) -
        (Real.log (1 - q ^ (k + 1)) - Real.log (1 - q ^ (x + k)))) := by
    refine strictConvexOn_tsum (convex_Ioi (0 : ℝ)) (fun k => ?_) (fun x _ =>
      ((summable_log_one_sub_pow_succ hr0 hr1).sub (summable_log_one_sub_rpow hr0 hr1 x)).sub
      ((summable_log_one_sub_pow_succ hq0 hq1).sub (summable_log_one_sub_rpow hq0 hq1 x)))
    have := strictConvexOn_qPhi_sub_shift hcr hc (by positivity : (0 : ℝ) ≤ k)
      (Real.log (1 - r ^ (k + 1)) - Real.log (1 - q ^ (k + 1)))
    refine this.congr fun x _ => ?_
    simp only
    rw [lnGammaQ_term_eq hr0, lnGammaQ_term_eq hq0]; ring
  have hL := convexOn_affine (Real.log (1 - r) - Real.log (1 - q))
    (-(Real.log (1 - r) - Real.log (1 - q)))
  refine (hT.add_convexOn hL).congr fun x _ => ?_
  simp only [Pi.add_apply, lnGammaQ]
  rw [((summable_log_one_sub_pow_succ hr0 hr1).sub (summable_log_one_sub_rpow hr0 hr1 x)).tsum_sub
    ((summable_log_one_sub_pow_succ hq0 hq1).sub (summable_log_one_sub_rpow hq0 hq1 x))]
  ring

theorem lnGammaQ_sub_props :
    (∀ x, 1 < x → x < 2 → lnGammaQ r x - lnGammaQ q x < 0) ∧
      (∀ x, 0 < x → x < 1 → 0 < lnGammaQ r x - lnGammaQ q x) ∧
      (∀ x, 2 < x → 0 < lnGammaQ r x - lnGammaQ q x) := by
  have hq1 : q < 1 := hqr.trans hr1
  have hr0 : 0 < r := hq0.trans hqr
  exact strictConvexOn_one_two (strictConvexOn_lnGammaQ_sub hq0 hqr hr1)
    (by rw [lnGammaQ_one hr0 hr1, lnGammaQ_one hq0 hq1, sub_self])
    (by rw [lnGammaQ_two hr0 hr1, lnGammaQ_two hq0 hq1, sub_self])

/-- DLMF 5.18.8: `Γ_q(x) < Γ_r(x)` for `0 < q < r < 1` and `0 < x < 1` or `x > 2`. -/
theorem dlmf_5_18_8 {x : ℝ} (hx : (0 < x ∧ x < 1) ∨ 2 < x) : qGamma q x < qGamma r x := by
  have hq1 : q < 1 := hqr.trans hr1
  have hr0 : 0 < r := hq0.trans hqr
  have hx0 : 0 < x := by rcases hx with h | h; exacts [h.1, by linarith]
  have hd : 0 < lnGammaQ r x - lnGammaQ q x := by
    rcases hx with h | h
    · exact (lnGammaQ_sub_props hq0 hqr hr1).2.1 x h.1 h.2
    · exact (lnGammaQ_sub_props hq0 hqr hr1).2.2 x h
  rw [qGamma_ofReal hq0 hq1 hx0, qGamma_ofReal hr0 hr1 hx0, Complex.real_lt_real]
  exact Real.exp_lt_exp.2 (by linarith)

/-- DLMF 5.18.9: `Γ_q(x) > Γ_r(x)` for `0 < q < r < 1` and `1 < x < 2`. -/
theorem dlmf_5_18_9 {x : ℝ} (hx1 : 1 < x) (hx2 : x < 2) : qGamma r x < qGamma q x := by
  have hq1 : q < 1 := hqr.trans hr1
  have hr0 : 0 < r := hq0.trans hqr
  have hd := (lnGammaQ_sub_props hq0 hqr hr1).1 x hx1 hx2
  rw [qGamma_ofReal hq0 hq1 (by linarith), qGamma_ofReal hr0 hr1 (by linarith),
    Complex.real_lt_real]
  exact Real.exp_lt_exp.2 (by linarith)

end Comparison

end Azurite.DLMF
