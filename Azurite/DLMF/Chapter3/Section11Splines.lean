/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Polynomial.Bernstein
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Module

/-!
# DLMF §3.11(vi): Splines

Formalizations of <https://dlmf.nist.gov/3.11.vi>.

* "on each subinterval `[x_k, x_{k+1}]` … a low-degree polynomial is defined with coefficients
  determined by, for example, values `f_k` and `f′_k` of a function `f` and its derivative at the
  nodes": Hermite interpolation on an interval, with derivatives of orders `≤ r` prescribed at both
  ends, has a unique solution of degree `≤ 2r + 1` (`hermite_exists`, `hermite_unique`).
* "The set of all the polynomials defines a function, the spline, on `[a, b]`": `splineFn`
  (`splineFn_eq_piece`: it is the `k`th polynomial on `[x_k, x_{k+1})`).
* "By taking more derivatives into account, the smoothness of the spline will increase": pieces
  whose derivatives of orders `≤ r` agree at the interior nodes give a `C^r` spline
  (`splineFn_contDiff`, via the truncated pieces `cutPoly`); the Hermite spline built from the
  values of `f, f′, …, f^{(r)}` at the nodes is `C^r` (`dlmf_3_11_vi_hermite_spline`); the cubic
  case with the values `f_k`, `f′_k` is `C¹` (`dlmf_3_11_vi_cubic`).
* Cubic Bézier curves (`bezier3`): the endpoints are `(x₀, y₀)` and `(x₃, y₃)`
  (`bezier3_zero`, `bezier3_one`); the tangent at `(x₀, y₀)` is along the line to `(x₁, y₁)` and the
  tangent at `(x₃, y₃)` along the line from `(x₂, y₂)` (`dlmf_3_11_vi_bezier_tangent`); `x(t)` and
  `y(t)` are cubic polynomials (`dlmf_3_11_vi_bezier_cubic`, Bernstein form `bezier3_bernstein`);
  "A complete spline results by composing several Bézier curves": two curves joined end to end are
  continuous, and `C¹` when the control points at the joint are collinear in the matching ratio
  (`dlmf_3_11_vi_bezier_join`).

Not formalized: §24.17(ii) splines based on Bernoulli and Euler polynomials (cross-reference); the
comparison with Lagrange interpolation, multivariate splines and the typography application are
prose; de Boor (2001), Chui (1988), Schumaker (1981), Knuth (1986) are references.
-/

open Polynomial Finset Filter Topology

namespace Azurite.DLMF

/-! ### Hermite interpolation on an interval -/

/-- A polynomial of degree `< 2r + 2` whose derivatives of orders `≤ r` vanish at two distinct
points is zero. -/
theorem hermite_zero {c d : ℝ} (hcd : c ≠ d) {r : ℕ} {p : ℝ[X]}
    (hdeg : p.degree < (2 * r + 2 : ℕ))
    (hc : ∀ i ≤ r, (derivative^[i] p).eval c = 0) (hd : ∀ i ≤ r, (derivative^[i] p).eval d = 0) :
    p = 0 := by
  by_contra hp
  have h1 : (X - C c) ^ (r + 1) ∣ p :=
    (pow_dvd_pow _ (lt_rootMultiplicity_of_isRoot_iterate_derivative hp hc)).trans
      (pow_rootMultiplicity_dvd p c)
  have h2 : (X - C d) ^ (r + 1) ∣ p :=
    (pow_dvd_pow _ (lt_rootMultiplicity_of_isRoot_iterate_derivative hp hd)).trans
      (pow_rootMultiplicity_dvd p d)
  have hcop : IsCoprime ((X - C c) ^ (r + 1)) ((X - C d) ^ (r + 1)) :=
    (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hcd).isUnit).pow
  have h3 := natDegree_le_of_dvd (hcop.mul_dvd h1 h2) hp
  rw [natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero c)) (pow_ne_zero _ (X_sub_C_ne_zero d)),
    natDegree_pow, natDegree_pow, natDegree_X_sub_C, natDegree_X_sub_C] at h3
  have := (natDegree_lt_iff_degree_lt hp).mpr hdeg
  omega

/-- The polynomial with coefficients `a`. -/
noncomputable def coeffPoly {m : ℕ} (a : Fin m → ℝ) : ℝ[X] := ∑ i : Fin m, C (a i) * X ^ (i : ℕ)

/-- The Hermite data map: derivatives of orders `≤ r` at `c` (first `r + 1` slots) and at `d`. -/
noncomputable def hermiteData (c d : ℝ) (r : ℕ) (p : ℝ[X]) : Fin (2 * r + 2) → ℝ := fun i =>
  if (i : ℕ) ≤ r then (derivative^[i] p).eval c else (derivative^[(i : ℕ) - (r + 1)] p).eval d

theorem coeffPoly_add {m : ℕ} (a b : Fin m → ℝ) :
    coeffPoly (a + b) = coeffPoly a + coeffPoly b := by
  simp [coeffPoly, add_mul, sum_add_distrib]

theorem coeffPoly_smul {m : ℕ} (s : ℝ) (a : Fin m → ℝ) :
    coeffPoly (s • a) = C s * coeffPoly a := by
  simp [coeffPoly, Finset.mul_sum, mul_assoc]

/-- **DLMF §3.11(vi)**: Hermite interpolation: for distinct `c, d` and any prescribed values
`u i`, `v i` (`i ≤ r`) there is a polynomial of degree `< 2r + 2` with
`p^{(i)}(c) = u i`, `p^{(i)}(d) = v i`. -/
theorem hermite_exists {c d : ℝ} (hcd : c ≠ d) (r : ℕ) (u v : ℕ → ℝ) :
    ∃ p : ℝ[X], p.degree < (2 * r + 2 : ℕ) ∧
      ∀ i ≤ r, (derivative^[i] p).eval c = u i ∧ (derivative^[i] p).eval d = v i := by
  let L : (Fin (2 * r + 2) → ℝ) →ₗ[ℝ] (Fin (2 * r + 2) → ℝ) :=
    { toFun := fun a => hermiteData c d r (coeffPoly a)
      map_add' := fun a b => by
        funext i; simp only [hermiteData, coeffPoly_add, iterate_map_add, eval_add,
          Pi.add_apply]; split_ifs <;> rfl
      map_smul' := fun s a => by
        funext i; simp only [hermiteData, coeffPoly_smul, iterate_derivative_C_mul, eval_mul,
          eval_C, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> rfl }
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    have hp : coeffPoly a = 0 := by
      refine hermite_zero hcd (degree_sum_fin_lt a) (fun i hi => ?_) (fun i hi => ?_)
      · have := congrFun ha ⟨i, by omega⟩
        simpa [L, hermiteData, hi] using this
      · have := congrFun ha ⟨i + (r + 1), by omega⟩
        simpa [L, hermiteData, show ¬ i + (r + 1) ≤ r by omega] using this
    funext k
    have := congrArg (fun q => q.coeff k) hp
    simpa [coeffPoly, finsetSum_coeff, coeff_C_mul_X_pow, Fin.val_inj] using this
  obtain ⟨a, ha⟩ := (LinearMap.injective_iff_surjective.mp hinj)
    (fun i => if (i : ℕ) ≤ r then u i else v ((i : ℕ) - (r + 1)))
  refine ⟨coeffPoly a, degree_sum_fin_lt a, fun i hi => ⟨?_, ?_⟩⟩
  · have := congrFun ha ⟨i, by omega⟩
    simpa [L, hermiteData, hi] using this
  · have := congrFun ha ⟨i + (r + 1), by omega⟩
    simpa [L, hermiteData, show ¬ i + (r + 1) ≤ r by omega] using this

/-- **DLMF §3.11(vi)**: the Hermite interpolant of degree `< 2r + 2` is unique. -/
theorem hermite_unique {c d : ℝ} (hcd : c ≠ d) {r : ℕ} {p q : ℝ[X]}
    (hp : p.degree < (2 * r + 2 : ℕ)) (hq : q.degree < (2 * r + 2 : ℕ))
    (hc : ∀ i ≤ r, (derivative^[i] p).eval c = (derivative^[i] q).eval c)
    (hd : ∀ i ≤ r, (derivative^[i] p).eval d = (derivative^[i] q).eval d) : p = q := by
  have := hermite_zero hcd (r := r) (p := p - q)
    ((degree_sub_le p q).trans_lt (max_lt hp hq))
    (fun i hi => by rw [iterate_derivative_sub, eval_sub, hc i hi, sub_self])
    (fun i hi => by rw [iterate_derivative_sub, eval_sub, hd i hi, sub_self])
  exact sub_eq_zero.mp this

/-! ### Truncated pieces and smoothness -/

/-- `t ↦ q(t)` for `t ≥ c`, `0` for `t < c`. -/
noncomputable def cutPoly (c : ℝ) (q : ℝ[X]) (t : ℝ) : ℝ := if c ≤ t then q.eval t else 0

theorem cutPoly_continuous {c : ℝ} {q : ℝ[X]} (hq : q.eval c = 0) :
    Continuous (cutPoly c q) := by
  unfold cutPoly
  exact Continuous.if_le (f := fun _ => c) (g := fun t => t) q.differentiable.continuous
    continuous_const continuous_const continuous_id fun x hx => by rw [← hx, hq]

theorem cutPoly_hasDerivAt {c : ℝ} {q : ℝ[X]} (hq : q.eval c = 0)
    (hq' : (derivative q).eval c = 0) (t : ℝ) :
    HasDerivAt (cutPoly c q) (cutPoly c (derivative q) t) t := by
  refine hasDerivAt_of_hasDerivAt_of_ne' (x := c) (fun y hy => ?_)
    (cutPoly_continuous hq).continuousAt (cutPoly_continuous hq').continuousAt t
  rcases lt_or_gt_of_ne hy with h | h
  · have e : cutPoly c q =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds h] with z hz
      simp [cutPoly, not_le.mpr (show z < c from hz)]
    rw [show cutPoly c (derivative q) y = 0 by simp [cutPoly, not_le.mpr h]]
    exact (hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq e
  · have e : cutPoly c q =ᶠ[𝓝 y] fun z => q.eval z := by
      filter_upwards [Ioi_mem_nhds h] with z hz
      simp [cutPoly, (show c < z from hz).le]
    rw [show cutPoly c (derivative q) y = (derivative q).eval y by simp [cutPoly, h.le]]
    exact (q.hasDerivAt y).congr_of_eventuallyEq e

/-- A truncated polynomial piece whose derivatives of orders `≤ r` vanish at the cut is `C^r`. -/
theorem cutPoly_contDiff {c : ℝ} (r : ℕ) :
    ∀ q : ℝ[X], (∀ i ≤ r, (derivative^[i] q).eval c = 0) → ContDiff ℝ r (cutPoly c q) := by
  induction r with
  | zero =>
    intro q hq
    exact contDiff_zero.mpr (cutPoly_continuous (by simpa using hq 0 le_rfl))
  | succ r ih =>
    intro q hq
    have hd : ∀ t, HasDerivAt (cutPoly c q) (cutPoly c (derivative q) t) t :=
      cutPoly_hasDerivAt (by simpa using hq 0 (by omega)) (by simpa using hq 1 (by omega))
    have hderiv : deriv (cutPoly c q) = cutPoly c (derivative q) :=
      funext fun t => (hd t).deriv
    rw [show ((r + 1 : ℕ) : WithTop ℕ∞) = (r : WithTop ℕ∞) + 1 by push_cast; rfl,
      contDiff_succ_iff_deriv]
    refine ⟨fun t => (hd t).differentiableAt, by simp, ?_⟩
    rw [hderiv]
    exact ih _ fun i hi => by
      rw [← Function.iterate_succ_apply]; exact hq (i + 1) (by omega)

/-! ### Splines -/

/-- The spline with nodes `x₀ < x₁ < ⋯ < xₙ` and pieces `P₀, …, P_{n−1}`: `P₀` plus the
truncated jumps `P_k − P_{k−1}` from `x_k` on. -/
noncomputable def splineFn (x : ℕ → ℝ) (P : ℕ → ℝ[X]) (n : ℕ) (t : ℝ) : ℝ :=
  (P 0).eval t + ∑ k ∈ Ico 1 n, cutPoly (x k) (P k - P (k - 1)) t

theorem sum_Ico_telescope (g : ℕ → ℝ) (k : ℕ) :
    ∑ j ∈ Ico 1 (k + 1), (g j - g (j - 1)) = g k - g 0 := by
  induction k with
  | zero => simp
  | succ k ih => rw [sum_Ico_succ_top (by omega), ih]; simp

/-- **DLMF §3.11(vi)**: on `[x_k, x_{k+1})` the spline is the `k`th polynomial. -/
theorem splineFn_eq_piece {x : ℕ → ℝ} (hx : StrictMono x) (P : ℕ → ℝ[X]) {n k : ℕ} (hk : k < n)
    {t : ℝ} (ht : t ∈ Set.Ico (x k) (x (k + 1))) : splineFn x P n t = (P k).eval t := by
  rw [splineFn, ← sum_Ico_consecutive _ (show 1 ≤ k + 1 by omega) (show k + 1 ≤ n by omega)]
  have h2 : ∑ j ∈ Ico (k + 1) n, cutPoly (x j) (P j - P (j - 1)) t = 0 :=
    sum_eq_zero fun j hj => by
      have : t < x j := ht.2.trans_le (hx.monotone (mem_Ico.mp hj).1)
      simp [cutPoly, not_le.mpr this]
  have h1 : ∑ j ∈ Ico 1 (k + 1), cutPoly (x j) (P j - P (j - 1)) t =
      ∑ j ∈ Ico 1 (k + 1), ((P j).eval t - (P (j - 1)).eval t) :=
    sum_congr rfl fun j hj => by
      have : x j ≤ t := (hx.monotone (by have := (mem_Ico.mp hj).2; omega)).trans ht.1
      simp [cutPoly, this]
  rw [h2, h1, sum_Ico_telescope (fun j => (P j).eval t)]
  ring

/-- **DLMF §3.11(vi)**: if consecutive pieces agree to order `r` at the interior nodes, the spline
is `C^r`. -/
theorem splineFn_contDiff (x : ℕ → ℝ) (P : ℕ → ℝ[X]) (n r : ℕ)
    (hmatch : ∀ k ∈ Ico 1 n, ∀ i ≤ r,
      (derivative^[i] (P k)).eval (x k) = (derivative^[i] (P (k - 1))).eval (x k)) :
    ContDiff ℝ r (splineFn x P n) := by
  unfold splineFn
  refine ContDiff.add ((P 0).contDiff_aeval r)
    (ContDiff.sum fun k hk => cutPoly_contDiff r _ fun i hi => ?_)
  rw [iterate_derivative_sub, eval_sub, hmatch k hk i hi, sub_self]

/-- **DLMF §3.11(vi)**: the Hermite spline of order `r`: on each `[x_k, x_{k+1}]` the polynomial of
degree `≤ 2r + 1` taking the prescribed values `D k i` (`= f^{(i)}(x_k)`) of the derivatives of
orders `i ≤ r` at both ends. The spline is `C^r` on `ℝ` (so on `[a, b] = [x₀, xₙ]`) and is the `k`th
polynomial on `[x_k, x_{k+1})`; the pieces are unique. -/
theorem dlmf_3_11_vi_hermite_spline {x : ℕ → ℝ} (hx : StrictMono x) (n r : ℕ) (D : ℕ → ℕ → ℝ) :
    ∃ P : ℕ → ℝ[X], (∀ k, (P k).degree < (2 * r + 2 : ℕ)) ∧
      (∀ k, ∀ i ≤ r, (derivative^[i] (P k)).eval (x k) = D k i ∧
        (derivative^[i] (P k)).eval (x (k + 1)) = D (k + 1) i) ∧
      ContDiff ℝ r (splineFn x P n) ∧
      ∀ k < n, ∀ t ∈ Set.Ico (x k) (x (k + 1)), splineFn x P n t = (P k).eval t := by
  have h := fun k => hermite_exists (hx (Nat.lt_succ_self k)).ne r (D k) (D (k + 1))
  choose P hdeg hval using h
  refine ⟨P, hdeg, fun k i hi => hval k i hi, splineFn_contDiff x P n r fun k hk i hi => ?_,
    fun k hk t ht => splineFn_eq_piece hx P hk ht⟩
  have hk1 : k - 1 + 1 = k := by have := (mem_Ico.mp hk).1; omega
  have := (hval (k - 1) i hi).2
  rw [Nat.succ_eq_add_one, hk1] at this
  rw [(hval k i hi).1, this]

/-- **DLMF §3.11(vi)**: the cubic spline determined by the values `f_k` and `f′_k` at the nodes:
cubic pieces with `P_k(x_k) = f_k`, `P_k′(x_k) = f′_k`, `P_k(x_{k+1}) = f_{k+1}`,
`P_k′(x_{k+1}) = f′_{k+1}`; the spline is `C¹`. -/
theorem dlmf_3_11_vi_cubic {x : ℕ → ℝ} (hx : StrictMono x) (n : ℕ) (f f' : ℕ → ℝ) :
    ∃ P : ℕ → ℝ[X], (∀ k, (P k).degree < 4) ∧
      (∀ k, (P k).eval (x k) = f k ∧ (derivative (P k)).eval (x k) = f' k ∧
        (P k).eval (x (k + 1)) = f (k + 1) ∧ (derivative (P k)).eval (x (k + 1)) = f' (k + 1)) ∧
      ContDiff ℝ 1 (splineFn x P n) ∧
      ∀ k < n, ∀ t ∈ Set.Ico (x k) (x (k + 1)), splineFn x P n t = (P k).eval t := by
  obtain ⟨P, hdeg, hval, hC, hpiece⟩ :=
    dlmf_3_11_vi_hermite_spline hx n 1 fun k i => if i = 0 then f k else f' k
  refine ⟨P, hdeg, fun k => ?_, by exact_mod_cast hC, hpiece⟩
  have h0 := hval k 0 (by norm_num)
  have h1 := hval k 1 le_rfl
  simp only [Function.iterate_zero, id, Function.iterate_one, ite_true, one_ne_zero,
    ite_false] at h0 h1
  exact ⟨h0.1, h1.1, h0.2, h1.2⟩

/-! ### Cubic Bézier curves -/

section Bezier

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The cubic Bézier curve with endpoints `P 0`, `P 3` and control points `P 1`, `P 2`,
`t ∈ [0, 1]`. -/
def bezier3 (P : Fin 4 → E) (t : ℝ) : E :=
  (1 - t) ^ 3 • P 0 + (3 * (1 - t) ^ 2 * t) • P 1 + (3 * (1 - t) * t ^ 2) • P 2 + t ^ 3 • P 3

theorem bezier3_zero (P : Fin 4 → E) : bezier3 P 0 = P 0 := by simp [bezier3]

theorem bezier3_one (P : Fin 4 → E) : bezier3 P 1 = P 3 := by simp [bezier3]

/-- The derivative of the cubic Bézier curve. -/
noncomputable def bezier3Deriv (P : Fin 4 → E) (t : ℝ) : E :=
  (3 * (1 - t) ^ 2) • (P 1 - P 0) + (6 * (1 - t) * t) • (P 2 - P 1) + (3 * t ^ 2) • (P 3 - P 2)

theorem bezier3_hasDerivAt (P : Fin 4 → E) (t : ℝ) :
    HasDerivAt (bezier3 P) (bezier3Deriv P t) t := by
  have h : ∀ (q : ℝ[X]) (v : E), HasDerivAt (fun s => q.eval s • v) ((derivative q).eval t • v) t :=
    fun q v => (q.hasDerivAt t).smul_const v
  have := (((h ((1 - X) ^ 3) (P 0)).add (h (3 * (1 - X) ^ 2 * X) (P 1))).add
    (h (3 * (1 - X) * X ^ 2) (P 2))).add (h (X ^ 3) (P 3))
  convert this using 1
  · funext s; simp [bezier3]
  · simp only [bezier3Deriv, derivative_mul, derivative_pow, derivative_sub, derivative_one,
      derivative_X, derivative_ofNat, eval_add, eval_mul, eval_pow, eval_sub, eval_one, eval_X,
      eval_ofNat, eval_zero, Nat.cast_ofNat, eval_C]
    module

/-- **DLMF §3.11(vi)**: "The slope of the curve at `(x₀, y₀)` is tangent to the line between
`(x₀, y₀)` and `(x₁, y₁)`; similarly the slope at `(x₃, y₃)` is tangent to the line between
`x₂, y₂` and `x₃, y₃`": `B′(0) = 3(P₁ − P₀)`, `B′(1) = 3(P₃ − P₂)`. -/
theorem dlmf_3_11_vi_bezier_tangent (P : Fin 4 → E) :
    HasDerivAt (bezier3 P) ((3 : ℝ) • (P 1 - P 0)) 0 ∧
      HasDerivAt (bezier3 P) ((3 : ℝ) • (P 3 - P 2)) 1 := by
  constructor
  · convert bezier3_hasDerivAt P 0 using 1; simp [bezier3Deriv]
  · convert bezier3_hasDerivAt P 1 using 1; simp [bezier3Deriv]

/-- The Bernstein form `B(t) = ∑ᵢ bᵢ,₃(t) Pᵢ`. -/
theorem bezier3_bernstein (P : Fin 4 → E) (t : ℝ) :
    bezier3 P t = ∑ i : Fin 4, (bernsteinPolynomial ℝ 3 i).eval t • P i := by
  simp [bezier3, Fin.sum_univ_four, bernsteinPolynomial, Nat.choose]
  module

end Bezier

/-- **DLMF §3.11(vi)**: "The curve is described by `x(t)` and `y(t)`, which are cubic
polynomials with `t ∈ [0, 1]`". -/
theorem dlmf_3_11_vi_bezier_cubic (P : Fin 4 → ℝ × ℝ) :
    ∃ px py : ℝ[X], px.natDegree ≤ 3 ∧ py.natDegree ≤ 3 ∧
      ∀ t, bezier3 P t = (px.eval t, py.eval t) := by
  refine ⟨C (P 0).1 * (1 - X) ^ 3 + C (3 * (P 1).1) * ((1 - X) ^ 2 * X) +
      C (3 * (P 2).1) * ((1 - X) * X ^ 2) + C (P 3).1 * X ^ 3,
    C (P 0).2 * (1 - X) ^ 3 + C (3 * (P 1).2) * ((1 - X) ^ 2 * X) +
      C (3 * (P 2).2) * ((1 - X) * X ^ 2) + C (P 3).2 * X ^ 3, by compute_degree, by compute_degree,
    fun t => ?_⟩
  ext <;> simp [bezier3] <;> ring

section Join

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Two cubic Bézier curves traversed one after the other, `t ∈ [0, 2]`. -/
noncomputable def bezierJoin (P Q : Fin 4 → E) (t : ℝ) : E :=
  if t ≤ 1 then bezier3 P t else bezier3 Q (t - 1)

theorem bezier3_continuous (P : Fin 4 → E) : Continuous (bezier3 P) :=
  continuous_iff_continuousAt.mpr fun t => (bezier3_hasDerivAt P t).continuousAt

theorem bezier3Deriv_continuous (P : Fin 4 → E) : Continuous (bezier3Deriv P) := by
  unfold bezier3Deriv; fun_prop

/-- **DLMF §3.11(vi)**: "A complete spline results by composing several Bézier curves": joined at a
common endpoint (`Q₀ = P₃`) the curves form a continuous curve, and it is `C¹` when moreover
`Q₁ − Q₀ = P₃ − P₂` (the control points `P₂, P₃ = Q₀, Q₁` collinear with equal spacing). -/
theorem dlmf_3_11_vi_bezier_join (P Q : Fin 4 → E) (h0 : Q 0 = P 3) :
    Continuous (bezierJoin P Q) ∧ (Q 1 - Q 0 = P 3 - P 2 → ContDiff ℝ 1 (bezierJoin P Q)) := by
  have hc : Continuous (bezierJoin P Q) := by
    unfold bezierJoin
    exact Continuous.if_le (f := fun t => t) (g := fun _ => (1 : ℝ)) (bezier3_continuous P)
      ((bezier3_continuous Q).comp (continuous_id.sub continuous_const)) continuous_id
      continuous_const fun t ht => by rw [ht, bezier3_one, sub_self, bezier3_zero, h0]
  refine ⟨hc, fun h1 => ?_⟩
  set g : ℝ → E := fun t => if t ≤ 1 then bezier3Deriv P t else bezier3Deriv Q (t - 1)
  have hg : Continuous g :=
    Continuous.if_le (f := fun t => t) (g := fun _ => (1 : ℝ)) (bezier3Deriv_continuous P)
      ((bezier3Deriv_continuous Q).comp (continuous_id.sub continuous_const)) continuous_id
      continuous_const fun t ht => by simp [ht, bezier3Deriv, h1]
  have hd : ∀ t, HasDerivAt (bezierJoin P Q) (g t) t := by
    refine hasDerivAt_of_hasDerivAt_of_ne' (x := 1) (fun y hy => ?_) hc.continuousAt
      hg.continuousAt
    rcases lt_or_gt_of_ne hy with h | h
    · have e : bezierJoin P Q =ᶠ[𝓝 y] bezier3 P := by
        filter_upwards [Iio_mem_nhds h] with z hz
        simp [bezierJoin, (show z < 1 from hz).le]
      rw [show g y = bezier3Deriv P y by simp [g, h.le]]
      exact (bezier3_hasDerivAt P y).congr_of_eventuallyEq e
    · have e : bezierJoin P Q =ᶠ[𝓝 y] fun z => bezier3 Q (z - 1) := by
        filter_upwards [Ioi_mem_nhds h] with z hz
        simp [bezierJoin, not_le.mpr (show 1 < z from hz)]
      rw [show g y = bezier3Deriv Q (y - 1) by simp [g, not_le.mpr h]]
      have := (bezier3_hasDerivAt Q (y - 1)).scomp y ((hasDerivAt_id y).sub_const 1)
      simpa using this.congr_of_eventuallyEq e
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => (hd t).differentiableAt, ?_⟩
  rw [show deriv (bezierJoin P Q) = g from funext fun t => (hd t).deriv]
  exact hg

end Join

end Azurite.DLMF
