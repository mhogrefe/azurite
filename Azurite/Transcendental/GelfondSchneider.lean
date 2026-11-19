/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Feldman.Hermite
import Mathlib.NumberTheory.SiegelsLemma
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.Real.Irrational

/-!
# The Gelfond–Schneider theorem for a quadratic exponent and rational values

For a quadratic irrational algebraic integer `β` (`β² = uβ + v` with integers `u`, `v`) and a
complex number `ℓ ≠ 0`, the numbers `e^ℓ` and `e^{βℓ}` are not both rational
(`not_rational_exp_pair`).  This is the case of the Gelfond–Schneider theorem (`α^β` is
transcendental for algebraic `α ≠ 0, 1` and algebraic irrational `β`) in which `α = e^ℓ` is
rational, `β` is a quadratic integer and only the irrationality of `α^β = e^{βℓ}` is asked
for.  It gives the irrationality of

* `e^π = (−1)^{−i}` (Gelfond's constant, `irrational_exp_pi`),
* `2^√2` (the Gelfond–Schneider constant, `irrational_two_rpow_sqrt_two`),
* `e^{π√n}` for every positive integer `n` (`irrational_exp_pi_sqrt`), such as Ramanujan's
  constant `e^{π√163}`.

The proof is Gelfond's (A. O. Gelfond, *Sur le septième problème de Hilbert*, Izv. Akad. Nauk
SSSR 7 (1934), 623–630), in the form found in the textbooks (for example I. Niven,
*Irrational Numbers*, Carus Monograph 11, Chapter 10).  Suppose `e^ℓ = a/d` and
`e^{βℓ} = r/d` with integers `a`, `r`, `d`.

* **The auxiliary function** `F(z) = ∑_{i,j<q} c_{ij} e^{(i + jβ)z}` with integers `c_{ij}`.
  Its derivatives at the points `kℓ` are `∑ c_{ij} (i + jβ)^t (a/d)^{ik} (r/d)^{jk}`: after
  multiplication by `d^{2qk}`, elements `X + Yβ` of `ℤ[β]` whose two coordinates are integer
  linear forms in the `c_{ij}` (`deriv_node`).
* **Siegel's lemma** (`exists_coeffs`): with `q² = 4mT` unknowns and `2mT` equations there are
  `c_{ij}`, not all `0`, of size at most `q² (2Kq)^T H^{2qm}`, with `F⁽ᵗ⁾(kℓ) = 0` for `t < T`,
  `k < m`.
* **The arithmetic lower bound** (`one_le_norm_deriv_mul`): a nonzero `X + Yβ` times its
  conjugate is a nonzero integer, so `|X + Yβ| ≥ 1/((|X| + |Y|)(1 + |u| + |β|))`.
* **The analytic upper bound** (`norm_iteratedDeriv_mul_le_of_zeros`): if `F` vanishes to order
  `s` at the `m` points, Schwarz's lemma on a circle of radius `R` (`norm_le_of_zeros` of
  `Feldman/Hermite.lean`) and Cauchy's estimate bound `F⁽ˢ⁾(kℓ)` by
  `s! (Λ/(R − m|ℓ|))^{ms} max_{|w| = R} |F|`.
* **The induction** (`Data.false`): with `m = 7` points, `q = 14κ`, `T = 7κ²`, `R = ⌊√s⌋` and
  `κ` large the two bounds contradict each other for every `s ≥ T` (`final_ineq`), so all
  derivatives of `F` vanish at `0`; the frequencies `i + jβ` are distinct, and a Vandermonde
  determinant gives `c = 0`.
-/

namespace Azurite.GelfondSchneider

open Complex Finset

/-- A hypothetical pair of rational values `e^ℓ = a/d`, `e^{βℓ} = r/d` for a quadratic
irrational integer `β` (`β² = uβ + v`) and `ℓ ≠ 0`.  There is none (`Data.false`). -/
structure Data where
  /-- The exponent. -/
  β : ℂ
  /-- The trace of `β`. -/
  u : ℤ
  /-- Minus the norm of `β`. -/
  v : ℤ
  hβ : β ^ 2 = u * β + v
  hirr : ∀ x y : ℤ, (x : ℂ) + y * β = 0 → x = 0 ∧ y = 0
  /-- The logarithm. -/
  ℓ : ℂ
  hℓ : ℓ ≠ 0
  /-- The numerator of `e^ℓ`. -/
  a : ℤ
  /-- The numerator of `e^{βℓ}`. -/
  r : ℤ
  /-- The common denominator. -/
  d : ℕ
  hd : 0 < d
  ha : Complex.exp ℓ = a / d
  hr : Complex.exp (β * ℓ) = r / d

namespace Data

variable (D : Data)

/-! ### The ring `ℤ[β]` in coordinates -/

/-- `x + yβ` for a pair of integers. -/
def zb (p : ℤ × ℤ) : ℂ := p.1 + p.2 * D.β

/-- The product in `ℤ[β]`, in coordinates. -/
def mul (p p' : ℤ × ℤ) : ℤ × ℤ :=
  (p.1 * p'.1 + D.v * (p.2 * p'.2), p.1 * p'.2 + p.2 * p'.1 + D.u * (p.2 * p'.2))

theorem zb_mul (p p' : ℤ × ℤ) : D.zb (D.mul p p') = D.zb p * D.zb p' := by
  unfold zb mul
  push_cast
  linear_combination (-(p.2 : ℂ) * p'.2) * D.hβ

/-- The powers in `ℤ[β]`, in coordinates. -/
def pw (p : ℤ × ℤ) : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | t + 1 => D.mul (pw p t) p

theorem zb_pw (p : ℤ × ℤ) (t : ℕ) : D.zb (D.pw p t) = D.zb p ^ t := by
  induction t with
  | zero => simp [pw, zb]
  | succ t ih => rw [pw, zb_mul, ih, pow_succ]

/-- The size `|x| + |y|` of a pair. -/
def sz (p : ℤ × ℤ) : ℤ := |p.1| + |p.2|

theorem sz_nonneg (p : ℤ × ℤ) : 0 ≤ sz p := add_nonneg (abs_nonneg _) (abs_nonneg _)

/-- The constant of the multiplication: `sz (p p') ≤ K sz p sz p'`. -/
def K : ℤ := 1 + |D.u| + |D.v|

theorem one_le_K : 1 ≤ D.K := by
  unfold K
  have := abs_nonneg D.u
  have := abs_nonneg D.v
  linarith

theorem sz_mul_le (p p' : ℤ × ℤ) : sz (D.mul p p') ≤ D.K * (sz p * sz p') := by
  unfold sz mul K
  dsimp only
  have h1 := abs_add_le (p.1 * p'.1) (D.v * (p.2 * p'.2))
  have h2 := abs_add_le (p.1 * p'.2 + p.2 * p'.1) (D.u * (p.2 * p'.2))
  have h3 := abs_add_le (p.1 * p'.2) (p.2 * p'.1)
  simp only [abs_mul] at h1 h2 h3
  set A := |p.1| with hA
  set B := |p.2| with hB
  set A' := |p'.1| with hA'
  set B' := |p'.2| with hB'
  set U := |D.u| with hU
  set V := |D.v| with hV
  have a0 : 0 ≤ A := abs_nonneg _
  have b0 : 0 ≤ B := abs_nonneg _
  have a0' : 0 ≤ A' := abs_nonneg _
  have b0' : 0 ≤ B' := abs_nonneg _
  have u0 : 0 ≤ U := abs_nonneg _
  have v0 : 0 ≤ V := abs_nonneg _
  have e : (1 + U + V) * ((A + B) * (A' + B'))
      = (A * A' + V * (B * B') + (A * B' + B * A') + U * (B * B'))
        + (B * B' + U * (A * A' + A * B' + B * A') + V * (A * A' + A * B' + B * A')) := by
    ring
  have hpos : 0 ≤ B * B' + U * (A * A' + A * B' + B * A') + V * (A * A' + A * B' + B * A') := by
    positivity
  linarith

theorem sz_pw_le (p : ℤ × ℤ) (t : ℕ) : sz (D.pw p t) ≤ (D.K * sz p) ^ t := by
  induction t with
  | zero => simp [pw, sz]
  | succ t ih =>
    have hK := D.one_le_K
    calc sz (D.pw p (t + 1)) ≤ D.K * (sz (D.pw p t) * sz p) := D.sz_mul_le _ _
      _ ≤ D.K * ((D.K * sz p) ^ t * sz p) := by
          have := mul_le_mul_of_nonneg_right ih (sz_nonneg p)
          exact mul_le_mul_of_nonneg_left this (by linarith)
      _ = (D.K * sz p) ^ (t + 1) := by ring

theorem abs_fst_le_sz (p : ℤ × ℤ) : |p.1| ≤ sz p := by
  unfold sz
  have := abs_nonneg p.2
  linarith

theorem abs_snd_le_sz (p : ℤ × ℤ) : |p.2| ≤ sz p := by
  unfold sz
  have := abs_nonneg p.1
  linarith

/-- The conjugate `x + yβ′`, `β′ = u − β`. -/
def zbc (p : ℤ × ℤ) : ℂ := p.1 + p.2 * (D.u - D.β)

/-- The norm `x² + uxy − vy²`. -/
def nrm (p : ℤ × ℤ) : ℤ := p.1 ^ 2 + D.u * (p.1 * p.2) - D.v * p.2 ^ 2

theorem zb_mul_zbc (p : ℤ × ℤ) : D.zb p * D.zbc p = D.nrm p := by
  unfold zb zbc nrm
  push_cast
  linear_combination (-(p.2 : ℂ) ^ 2) * D.hβ

theorem zb_ne_zero {p : ℤ × ℤ} (hp : p ≠ 0) : D.zb p ≠ 0 := fun h =>
  hp (Prod.ext (D.hirr _ _ h).1 (D.hirr _ _ h).2)

theorem zbc_ne_zero {p : ℤ × ℤ} (hp : p ≠ 0) : D.zbc p ≠ 0 := by
  intro h
  have h' : ((p.1 + p.2 * D.u : ℤ) : ℂ) + ((-p.2 : ℤ) : ℂ) * D.β = 0 := by
    unfold zbc at h
    push_cast
    linear_combination h
  obtain ⟨h1, h2⟩ := D.hirr _ _ h'
  have h3 : p.2 = 0 := by omega
  rw [h3] at h1
  exact hp (Prod.ext (by simpa using h1) h3)

/-- The bound `1 + |u| + |β|` for the conjugate. -/
noncomputable def Bc : ℝ := 1 + |(D.u : ℝ)| + ‖D.β‖

theorem one_le_Bc : 1 ≤ D.Bc := by
  unfold Bc
  have := abs_nonneg (D.u : ℝ)
  have := norm_nonneg D.β
  linarith

theorem norm_zbc_le (p : ℤ × ℤ) : ‖D.zbc p‖ ≤ (sz p : ℝ) * D.Bc := by
  unfold zbc sz Bc
  have h1 : ‖(p.1 : ℂ) + p.2 * (D.u - D.β)‖ ≤ ‖(p.1 : ℂ)‖ + ‖(p.2 : ℂ) * (D.u - D.β)‖ :=
    norm_add_le _ _
  have h2 : ‖(D.u : ℂ) - D.β‖ ≤ ‖(D.u : ℂ)‖ + ‖D.β‖ := norm_sub_le _ _
  rw [norm_mul, Complex.norm_intCast, Complex.norm_intCast] at h1
  rw [Complex.norm_intCast] at h2
  push_cast
  have a0 := abs_nonneg (p.1 : ℝ)
  have b0 := abs_nonneg (p.2 : ℝ)
  have u0 := abs_nonneg (D.u : ℝ)
  have n0 := norm_nonneg D.β
  have h3 : |(p.2 : ℝ)| * ‖(D.u : ℂ) - D.β‖ ≤ |(p.2 : ℝ)| * (|(D.u : ℝ)| + ‖D.β‖) :=
    mul_le_mul_of_nonneg_left h2 b0
  nlinarith [mul_nonneg a0 u0, mul_nonneg a0 n0]

/-- **The arithmetic lower bound**: a nonzero element of `ℤ[β]` is not small. -/
theorem one_le_norm_zb_mul {p : ℤ × ℤ} (hp : p ≠ 0) : 1 ≤ ‖D.zb p‖ * ((sz p : ℝ) * D.Bc) := by
  have hn : D.nrm p ≠ 0 := by
    intro h
    have := D.zb_mul_zbc p
    rw [h, Int.cast_zero, mul_eq_zero] at this
    exact this.elim (D.zb_ne_zero hp) (D.zbc_ne_zero hp)
  have h1 : (1 : ℝ) ≤ ‖D.zb p‖ * ‖D.zbc p‖ := by
    rw [← norm_mul, zb_mul_zbc, Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs hn
  exact h1.trans (mul_le_mul_of_nonneg_left (D.norm_zbc_le p) (norm_nonneg _))

/-! ### The auxiliary function -/

variable (q : ℕ)

/-- The frequency `i + jβ`. -/
def om (ij : Fin q × Fin q) : ℂ := D.zb (((ij.1 : ℕ) : ℤ), ((ij.2 : ℕ) : ℤ))

/-- The auxiliary function `F(z) = ∑ c_{ij} e^{(i + jβ)z}`. -/
noncomputable def F (c : Fin q × Fin q → ℤ) (z : ℂ) : ℂ :=
  ∑ ij, (c ij : ℂ) * Complex.exp (D.om q ij * z)

theorem differentiable_F (c : Fin q × Fin q → ℤ) : Differentiable ℂ (D.F q c) := by
  unfold F
  fun_prop

theorem iteratedDeriv_F (c : Fin q × Fin q → ℤ) (t : ℕ) :
    iteratedDeriv t (D.F q c)
      = fun z => ∑ ij, (c ij : ℂ) * (D.om q ij ^ t * Complex.exp (D.om q ij * z)) := by
  induction t with
  | zero =>
    funext z
    simp [F]
  | succ t ih =>
    rw [iteratedDeriv_succ, ih]
    funext z
    have h : ∀ ij ∈ (Finset.univ : Finset (Fin q × Fin q)),
        HasDerivAt (fun z => (c ij : ℂ) * (D.om q ij ^ t * Complex.exp (D.om q ij * z)))
          ((c ij : ℂ) * (D.om q ij ^ (t + 1) * Complex.exp (D.om q ij * z))) z := by
      intro ij _
      have h1 : HasDerivAt (fun z : ℂ => D.om q ij * z) (D.om q ij) z := by
        simpa using (hasDerivAt_id z).const_mul (D.om q ij)
      have h2 := ((h1.cexp).const_mul (D.om q ij ^ t)).const_mul (c ij : ℂ)
      convert h2 using 1
      ring
    exact (HasDerivAt.fun_sum h).deriv

/-- The height of the values: `max(|a|, |r|, d)`. -/
def H : ℤ := max (max |D.a| |D.r|) D.d

theorem one_le_H : 1 ≤ D.H := by
  unfold H
  have : (1 : ℤ) ≤ D.d := by exact_mod_cast D.hd
  exact le_max_of_le_right this

/-- `d^{2qk} e^{(i + jβ) kℓ}` as an integer. -/
def E (ij : Fin q × Fin q) (k : ℕ) : ℤ :=
  D.a ^ ((ij.1 : ℕ) * k) * D.r ^ ((ij.2 : ℕ) * k) * (D.d : ℤ) ^ ((2 * q - ij.1 - ij.2) * k)

theorem split_exp (ij : Fin q × Fin q) (k : ℕ) :
    2 * q * k = (ij.1 : ℕ) * k + (ij.2 : ℕ) * k + (2 * q - ij.1 - ij.2) * k := by
  have h1 := ij.1.isLt
  have h2 := ij.2.isLt
  rw [← Nat.add_mul, ← Nat.add_mul]
  congr 1
  omega

theorem d_pow_mul_exp (ij : Fin q × Fin q) (k : ℕ) :
    (D.d : ℂ) ^ (2 * q * k) * Complex.exp (D.om q ij * (k * D.ℓ)) = (D.E q ij k : ℂ) := by
  have hd0 : (D.d : ℂ) ≠ 0 := by exact_mod_cast D.hd.ne'
  have hexp : Complex.exp (D.om q ij * (k * D.ℓ))
      = ((D.a : ℂ) / D.d) ^ ((ij.1 : ℕ) * k) * ((D.r : ℂ) / D.d) ^ ((ij.2 : ℕ) * k) := by
    rw [← D.ha, ← D.hr, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    unfold om zb
    push_cast
    ring
  rw [hexp, split_exp q ij k, pow_add, pow_add, div_pow, div_pow]
  unfold E
  push_cast
  field_simp

theorem abs_E_le (ij : Fin q × Fin q) (k : ℕ) : |D.E q ij k| ≤ D.H ^ (2 * q * k) := by
  have hH := D.one_le_H
  have ha : |D.a| ≤ D.H := le_trans (le_max_left _ _) (le_max_left _ _)
  have hr : |D.r| ≤ D.H := le_trans (le_max_right _ _) (le_max_left _ _)
  have hd : |(D.d : ℤ)| ≤ D.H := by
    rw [abs_of_nonneg (by positivity)]
    exact le_max_right _ _
  unfold E
  rw [abs_mul, abs_mul, abs_pow, abs_pow, abs_pow, split_exp q ij k, pow_add, pow_add]
  have h1 := pow_le_pow_left₀ (abs_nonneg D.a) ha ((ij.1 : ℕ) * k)
  have h2 := pow_le_pow_left₀ (abs_nonneg D.r) hr ((ij.2 : ℕ) * k)
  have h3 := pow_le_pow_left₀ (abs_nonneg (D.d : ℤ)) hd ((2 * q - ij.1 - ij.2) * k)
  exact mul_le_mul (mul_le_mul h1 h2 (by positivity) (by positivity)) h3 (by positivity)
    (by positivity)

/-- The coordinates of `d^{2qk} F⁽ᵗ⁾(kℓ)` in `ℤ[β]`: two integer linear forms in `c`. -/
def L (c : Fin q × Fin q → ℤ) (t k : ℕ) : ℤ × ℤ :=
  (∑ ij, c ij * (D.E q ij k * (D.pw (((ij.1 : ℕ) : ℤ), ((ij.2 : ℕ) : ℤ)) t).1),
    ∑ ij, c ij * (D.E q ij k * (D.pw (((ij.1 : ℕ) : ℤ), ((ij.2 : ℕ) : ℤ)) t).2))

/-- **The derivatives at the points `kℓ` lie in `d^{−2qk} ℤ[β]`.** -/
theorem deriv_node (c : Fin q × Fin q → ℤ) (t k : ℕ) :
    (D.d : ℂ) ^ (2 * q * k) * iteratedDeriv t (D.F q c) (k * D.ℓ) = D.zb (D.L q c t k) := by
  rw [iteratedDeriv_F, Finset.mul_sum]
  unfold zb L
  dsimp only
  push_cast
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ij _ => ?_
  have h1 := D.d_pow_mul_exp q ij k
  have h2 := D.zb_pw (((ij.1 : ℕ) : ℤ), ((ij.2 : ℕ) : ℤ)) t
  unfold zb at h2
  dsimp only at h2
  have h3 : D.om q ij = ((ij.1 : ℕ) : ℤ) + ((ij.2 : ℕ) : ℤ) * D.β := rfl
  rw [h3]
  rw [h3] at h1
  linear_combination ((c ij : ℂ) * ((ij.1 : ℕ) + (ij.2 : ℕ) * D.β) ^ t) * h1
    - ((c ij : ℂ) * D.E q ij k) * h2

theorem sz_om_le (ij : Fin q × Fin q) : sz (((ij.1 : ℕ) : ℤ), ((ij.2 : ℕ) : ℤ)) ≤ 2 * q := by
  unfold sz
  dsimp only
  have h1 := ij.1.isLt
  have h2 := ij.2.isLt
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  omega

theorem sz_pw_om_le (ij : Fin q × Fin q) (t : ℕ) :
    sz (D.pw (((ij.1 : ℕ) : ℤ), ((ij.2 : ℕ) : ℤ)) t) ≤ (D.K * (2 * q)) ^ t := by
  have hK := D.one_le_K
  exact (D.sz_pw_le _ t).trans (pow_le_pow_left₀
    (mul_nonneg (by linarith) (sz_nonneg _))
    (mul_le_mul_of_nonneg_left (sz_om_le q ij) (by linarith)) t)

/-- The size of the linear forms. -/
theorem sz_L_le (c : Fin q × Fin q → ℤ) {Cb : ℤ} (hCb : 0 ≤ Cb) (hc : ∀ ij, |c ij| ≤ Cb)
    (t k : ℕ) :
    sz (D.L q c t k)
      ≤ 2 * ((q * q : ℕ) * (Cb * (D.H ^ (2 * q * k) * (D.K * (2 * q)) ^ t))) := by
  have hK := D.one_le_K
  have hH := D.one_le_H
  have hH0 : 0 ≤ D.H ^ (2 * q * k) := pow_nonneg (by linarith) _
  have hterm : ∀ g : Fin q × Fin q → ℤ, (∀ ij, |g ij| ≤ (D.K * (2 * q)) ^ t) →
      |∑ ij, c ij * (D.E q ij k * g ij)|
        ≤ (q * q : ℕ) * (Cb * (D.H ^ (2 * q * k) * (D.K * (2 * q)) ^ t)) := by
    intro g hg
    calc |∑ ij, c ij * (D.E q ij k * g ij)| ≤ ∑ ij, |c ij * (D.E q ij k * g ij)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ij : Fin q × Fin q, Cb * (D.H ^ (2 * q * k) * (D.K * (2 * q)) ^ t) := by
          refine Finset.sum_le_sum fun ij _ => ?_
          rw [abs_mul, abs_mul]
          exact mul_le_mul (hc ij) (mul_le_mul (D.abs_E_le q ij k) (hg ij) (abs_nonneg _) hH0)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hCb
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
            nsmul_eq_mul]
  have h1 := hterm (fun ij => (D.pw (((ij.1 : ℕ) : ℤ), ((ij.2 : ℕ) : ℤ)) t).1)
    (fun ij => (abs_fst_le_sz _).trans (D.sz_pw_om_le q ij t))
  have h2 := hterm (fun ij => (D.pw (((ij.1 : ℕ) : ℤ), ((ij.2 : ℕ) : ℤ)) t).2)
    (fun ij => (abs_snd_le_sz _).trans (D.sz_pw_om_le q ij t))
  unfold sz L
  dsimp only at h1 h2 ⊢
  linarith

theorem om_injective : Function.Injective (D.om q) := by
  intro ij ij' h
  unfold om zb at h
  dsimp only at h
  have h' : (((ij.1 : ℕ) - (ij'.1 : ℕ) : ℤ) : ℂ) + (((ij.2 : ℕ) - (ij'.2 : ℕ) : ℤ) : ℂ) * D.β
      = 0 := by
    push_cast
    linear_combination h
  obtain ⟨h1, h2⟩ := D.hirr _ _ h'
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

theorem norm_om_le (ij : Fin q × Fin q) : ‖D.om q ij‖ ≤ (q : ℝ) * (1 + ‖D.β‖) := by
  unfold om zb
  dsimp only
  have h1 : ((ij.1 : ℕ) : ℝ) ≤ q := by exact_mod_cast ij.1.isLt.le
  have h2 : ((ij.2 : ℕ) : ℝ) ≤ q := by exact_mod_cast ij.2.isLt.le
  have h3 := norm_add_le (((ij.1 : ℕ) : ℤ) : ℂ) ((((ij.2 : ℕ) : ℤ) : ℂ) * D.β)
  rw [norm_mul] at h3
  simp only [Int.cast_natCast, Complex.norm_natCast] at h3 ⊢
  have n0 := norm_nonneg D.β
  nlinarith [mul_le_mul_of_nonneg_right h2 n0]

/-- The auxiliary function on a circle. -/
theorem norm_F_le (c : Fin q × Fin q → ℤ) {Cb : ℝ} (hCb : 0 ≤ Cb)
    (hc : ∀ ij, |(c ij : ℝ)| ≤ Cb) (w : ℂ) :
    ‖D.F q c w‖ ≤ (q * q : ℕ) * (Cb * Real.exp ((q : ℝ) * (1 + ‖D.β‖) * ‖w‖)) := by
  unfold F
  calc ‖∑ ij, (c ij : ℂ) * Complex.exp (D.om q ij * w)‖
      ≤ ∑ ij, ‖(c ij : ℂ) * Complex.exp (D.om q ij * w)‖ := norm_sum_le _ _
    _ ≤ ∑ _ij : Fin q × Fin q, Cb * Real.exp ((q : ℝ) * (1 + ‖D.β‖) * ‖w‖) := by
        refine Finset.sum_le_sum fun ij _ => ?_
        rw [norm_mul, Complex.norm_intCast]
        refine mul_le_mul (hc ij) ?_ (norm_nonneg _) hCb
        refine (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (D.norm_om_le q ij) (norm_nonneg _)
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          nsmul_eq_mul]

theorem zb_zero : D.zb 0 = 0 := by simp [zb]

/-- **The arithmetic lower bound for a derivative that does not vanish.** -/
theorem one_le_norm_deriv_mul (c : Fin q × Fin q → ℤ) {Cb : ℤ} (hCb : 0 ≤ Cb)
    (hc : ∀ ij, |c ij| ≤ Cb) (t k : ℕ) (hne : iteratedDeriv t (D.F q c) (k * D.ℓ) ≠ 0) :
    1 ≤ ‖iteratedDeriv t (D.F q c) (k * D.ℓ)‖ * ((D.d : ℝ) ^ (2 * q * k)
      * (2 * ((q * q : ℕ) * ((Cb : ℝ) * ((D.H : ℝ) ^ (2 * q * k)
        * ((D.K : ℝ) * (2 * q)) ^ t))) * D.Bc)) := by
  have hnode := D.deriv_node q c t k
  have hd0 : (D.d : ℂ) ^ (2 * q * k) ≠ 0 := pow_ne_zero _ (by exact_mod_cast D.hd.ne')
  have hL : D.L q c t k ≠ 0 := by
    intro h
    rw [h, zb_zero] at hnode
    exact hne ((mul_eq_zero.mp hnode).resolve_left hd0)
  have h1 := D.one_le_norm_zb_mul hL
  rw [← hnode, norm_mul, norm_pow, Complex.norm_natCast] at h1
  have h2 : (sz (D.L q c t k) : ℝ) ≤ 2 * ((q * q : ℕ) * ((Cb : ℝ) * ((D.H : ℝ) ^ (2 * q * k)
      * ((D.K : ℝ) * (2 * q)) ^ t))) := by
    exact_mod_cast D.sz_L_le q c hCb hc t k
  have hBc := D.one_le_Bc
  calc (1 : ℝ) ≤ (D.d : ℝ) ^ (2 * q * k) * ‖iteratedDeriv t (D.F q c) (k * D.ℓ)‖
        * ((sz (D.L q c t k) : ℝ) * D.Bc) := h1
    _ ≤ (D.d : ℝ) ^ (2 * q * k) * ‖iteratedDeriv t (D.F q c) (k * D.ℓ)‖
        * (2 * ((q * q : ℕ) * ((Cb : ℝ) * ((D.H : ℝ) ^ (2 * q * k)
          * ((D.K : ℝ) * (2 * q)) ^ t))) * D.Bc) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 (by linarith)) ?_
        positivity
    _ = _ := by ring

/-! ### Siegel's lemma -/

attribute [local instance] Matrix.seminormedAddCommGroup in
/-- **The coefficients**: integers `c_{ij}`, not all `0` and not too large, such that `F`
vanishes to order `T` at the `m` points `kℓ`, `k < m`. -/
theorem exists_coeffs {q T m : ℕ} (hq : q * q = 4 * (T * m)) (hT : 0 < T) (hm : 0 < m) :
    ∃ c : Fin q × Fin q → ℤ, c ≠ 0 ∧
      (∀ t < T, ∀ k : ℕ, k < m → iteratedDeriv t (D.F q c) (k * D.ℓ) = 0) ∧
      ∀ ij, |c ij| ≤ (q * q : ℕ) * ((D.K * (2 * q)) ^ T * D.H ^ (2 * q * m)) := by
  classical
  have hK := D.one_le_K
  have hH := D.one_le_H
  have hTm : 0 < T * m := Nat.mul_pos hT hm
  have hq0 : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · rw [h] at hq
      omega
    · exact h
  let A : Matrix ((Fin T × Fin m) × Bool) (Fin q × Fin q) ℤ := fun x ij =>
    D.E q ij x.1.2 * (if x.2 then (D.pw (((ij.1 : ℕ) : ℤ), ((ij.2 : ℕ) : ℤ)) x.1.1).1
      else (D.pw (((ij.1 : ℕ) : ℤ), ((ij.2 : ℕ) : ℤ)) x.1.1).2)
  have hcardα : Fintype.card ((Fin T × Fin m) × Bool) = T * m * 2 := by simp
  have hcardβ : Fintype.card (Fin q × Fin q) = q * q := by simp
  have hn : Fintype.card ((Fin T × Fin m) × Bool) < Fintype.card (Fin q × Fin q) := by
    rw [hcardα, hcardβ, hq]
    omega
  have hm' : 0 < Fintype.card ((Fin T × Fin m) × Bool) := by
    rw [hcardα]
    omega
  obtain ⟨c, hc0, hAc, hnorm⟩ := Int.Matrix.exists_ne_zero_int_vec_norm_le A hn hm'
  refine ⟨c, hc0, ?_, ?_⟩
  · intro t ht k hk
    have hL : D.L q c t k = 0 := by
      have h1 := congrFun hAc ((⟨t, ht⟩, ⟨k, hk⟩), true)
      have h2 := congrFun hAc ((⟨t, ht⟩, ⟨k, hk⟩), false)
      simp only [Matrix.mulVec, dotProduct, A, Pi.zero_apply, ite_true, Bool.false_eq_true,
        ite_false] at h1 h2
      refine Prod.ext ?_ ?_
      · show ∑ ij, c ij * (D.E q ij k * (D.pw (((ij.1 : ℕ) : ℤ), ((ij.2 : ℕ) : ℤ)) t).1) = 0
        rw [← h1]
        exact Finset.sum_congr rfl fun ij _ => by ring
      · show ∑ ij, c ij * (D.E q ij k * (D.pw (((ij.1 : ℕ) : ℤ), ((ij.2 : ℕ) : ℤ)) t).2) = 0
        rw [← h2]
        exact Finset.sum_congr rfl fun ij _ => by ring
    have hnode := D.deriv_node q c t k
    rw [hL, zb_zero] at hnode
    exact (mul_eq_zero.mp hnode).resolve_left
      (pow_ne_zero _ (by exact_mod_cast D.hd.ne'))
  · intro ij
    have hent : ∀ x ij', |A x ij'| ≤ (D.K * (2 * q)) ^ T * D.H ^ (2 * q * m) := by
      intro x ij'
      have hk : (x.1.2 : ℕ) < m := x.1.2.isLt
      have ht : (x.1.1 : ℕ) < T := x.1.1.isLt
      have hE := (D.abs_E_le q ij' x.1.2).trans (pow_le_pow_right₀ hH
        (Nat.mul_le_mul_left (2 * q) hk.le))
      have hKq : 1 ≤ D.K * (2 * q) := by
        have : (1 : ℤ) ≤ q := by exact_mod_cast hq0
        nlinarith
      have hg : |if x.2 then (D.pw (((ij'.1 : ℕ) : ℤ), ((ij'.2 : ℕ) : ℤ)) x.1.1).1
          else (D.pw (((ij'.1 : ℕ) : ℤ), ((ij'.2 : ℕ) : ℤ)) x.1.1).2|
          ≤ (D.K * (2 * q)) ^ T := by
        refine le_trans ?_ (pow_le_pow_right₀ hKq ht.le)
        split_ifs
        · exact (abs_fst_le_sz _).trans (D.sz_pw_om_le q ij' _)
        · exact (abs_snd_le_sz _).trans (D.sz_pw_om_le q ij' _)
      show |D.E q ij' x.1.2 * _| ≤ _
      rw [abs_mul, mul_comm]
      exact mul_le_mul hg hE (abs_nonneg _) (by positivity)
    set Ab : ℝ := (((D.K * (2 * q)) ^ T * D.H ^ (2 * q * m) : ℤ) : ℝ) with hAb
    have hAb1 : 1 ≤ Ab := by
      have : (1 : ℤ) ≤ (D.K * (2 * q)) ^ T * D.H ^ (2 * q * m) := by
        have h1 : (1 : ℤ) ≤ (D.K * (2 * q)) ^ T := one_le_pow₀ (by
          have : (1 : ℤ) ≤ q := by exact_mod_cast hq0
          nlinarith)
        have h2 : (1 : ℤ) ≤ D.H ^ (2 * q * m) := one_le_pow₀ hH
        exact one_le_mul_of_one_le_of_one_le h1 h2
      rw [hAb]
      exact_mod_cast this
    have hA : ‖A‖ ≤ Ab := by
      rw [Matrix.norm_le_iff (by linarith)]
      intro x ij'
      rw [Int.norm_eq_abs, hAb]
      exact_mod_cast hent x ij'
    have hexp : (Fintype.card ((Fin T × Fin m) × Bool) : ℝ)
        / ((Fintype.card (Fin q × Fin q) : ℝ) - Fintype.card ((Fin T × Fin m) × Bool)) = 1 := by
      rw [hcardα, hcardβ, hq]
      have hne : ((T * m * 2 : ℕ) : ℝ) ≠ 0 := by
        have : 0 < T * m * 2 := by omega
        exact_mod_cast this.ne'
      rw [div_eq_one_iff_eq (by
        push_cast at hne ⊢
        intro h
        apply hne
        linarith)]
      push_cast
      ring
    rw [hexp, Real.rpow_one] at hnorm
    have h1 : ‖c ij‖ ≤ ‖c‖ := norm_le_pi_norm c ij
    rw [Int.norm_eq_abs] at h1
    have h2 : ‖c‖ ≤ (q * q : ℕ) * Ab := by
      refine hnorm.trans ?_
      rw [hcardβ]
      exact mul_le_mul_of_nonneg_left (max_le hAb1 hA) (by positivity)
    have h3 : ((|c ij| : ℤ) : ℝ)
        ≤ (((q * q : ℕ) * ((D.K * (2 * q)) ^ T * D.H ^ (2 * q * m)) : ℤ) : ℝ) := by
      push_cast
      rw [hAb] at h2
      push_cast at h2
      exact h1.trans h2
    exact_mod_cast h3

/-- **The frequencies are distinct**: if all derivatives of `F` vanish at `0`, the
coefficients are `0` (Vandermonde). -/
theorem coeffs_eq_zero (c : Fin q × Fin q → ℤ)
    (h : ∀ t : ℕ, ∑ ij, (c ij : ℂ) * D.om q ij ^ t = 0) : c = 0 := by
  classical
  let e := Fintype.equivFin (Fin q × Fin q)
  have hinj : Function.Injective
      (fun i : Fin (Fintype.card (Fin q × Fin q)) => D.om q (e.symm i)) :=
    fun i j hij => e.symm.injective (D.om_injective q hij)
  have hv := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hinj
    (v := fun i => (c (e.symm i) : ℂ)) (fun t => by
      have := h t
      rw [← Equiv.sum_comp e.symm] at this
      exact this)
  funext ij
  have := congrFun hv (e ij)
  simpa using this

end Data

/-! ### The analytic upper bound -/

theorem prod_map_le_pow_card {α : Type*} (s : Multiset α) (f : α → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hf0 : ∀ a, 0 ≤ f a) (hf : ∀ a ∈ s, f a ≤ c) : (s.map f).prod ≤ c ^ Multiset.card s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ, mul_comm]
    exact mul_le_mul (ih fun b hb => hf b (Multiset.mem_cons_of_mem hb))
      (hf a (Multiset.mem_cons_self a s)) (hf0 a) (pow_nonneg hc _)

/-- Vanishing derivatives of order `< s` give a zero of order at least `s`. -/
theorem le_analyticOrderAt_of_iteratedDeriv_eq_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {a : ℂ} {s : ℕ} (h : ∀ t < s, iteratedDeriv t f a = 0) :
    (s : ℕ∞) ≤ analyticOrderAt f a := by
  obtain ⟨R, hR, e⟩ := Feldman.exists_taylor_remainder (hf.analyticAt a) s
  have h0 : ∀ z, Feldman.taylorAt f a s z = 0 := fun z => by
    unfold Feldman.taylorAt
    exact Finset.sum_eq_zero fun i hi => by rw [h i (Finset.mem_range.mp hi), mul_zero]
  exact (natCast_le_analyticOrderAt (hf.analyticAt a)).mpr
    ⟨R, hR, Filter.Eventually.of_forall fun z => by rw [e z, h0 z, zero_add, smul_eq_mul]⟩

/-- **Schwarz's lemma for a derivative**: an entire function that vanishes to order `s` at the
points of `nodes` has a small derivative of order `s` at each of them. -/
theorem norm_iteratedDeriv_mul_le_of_zeros {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (nodes : Finset ℂ) {s : ℕ} (hzero : ∀ b ∈ nodes, ∀ t < s, iteratedDeriv t f b = 0)
    {R M Λ δ : ℝ} (hδ : 0 < δ) (hΛ0 : 0 ≤ Λ)
    (hM : ∀ w ∈ Metric.sphere (0 : ℂ) R, ‖f w‖ ≤ M)
    (hdist : ∀ w ∈ Metric.sphere (0 : ℂ) R, ∀ b ∈ nodes, δ ≤ ‖w - b‖) {b₀ : ℂ}
    (hΛ : ∀ b ∈ nodes, ‖b₀ - b‖ + 1 ≤ Λ) (hR : ‖b₀‖ + 1 ≤ R) :
    ‖iteratedDeriv s f b₀‖ * δ ^ (nodes.card * s)
      ≤ s.factorial * (Λ ^ (nodes.card * s) * M) := by
  classical
  set S : Multiset ℂ := s • nodes.val with hS
  have hcard : Multiset.card S = nodes.card * s := by
    rw [hS, Multiset.card_nsmul, Finset.card_val, mul_comm]
  have hmem : ∀ b ∈ S, b ∈ nodes := fun b hb => by
    have := Multiset.mem_of_mem_nsmul hb
    simpa using this
  have hord : ∀ c, (S.count c : ℕ∞) ≤ analyticOrderAt f c := by
    intro c
    rw [hS, Multiset.count_nsmul]
    by_cases hc : c ∈ nodes
    · rw [Multiset.count_eq_one_of_mem nodes.nodup hc, mul_one]
      exact le_analyticOrderAt_of_iteratedDeriv_eq_zero hf (hzero c hc)
    · rw [Multiset.count_eq_zero_of_notMem hc, mul_zero]
      simp
  have hδpow : 0 < δ ^ (nodes.card * s) := by positivity
  have hR0 : 0 ≤ R := by
    have := norm_nonneg b₀
    linarith
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM (R : ℂ) (by
    rw [mem_sphere_zero_iff_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR0]))
  have hsphere : ∀ z ∈ Metric.sphere b₀ 1,
      ‖f z‖ ≤ Λ ^ (nodes.card * s) * M / δ ^ (nodes.card * s) := by
    intro z hz
    have hz1 : ‖z - b₀‖ = 1 := mem_sphere_iff_norm.mp hz
    have hzR : ‖z‖ ≤ R := by
      have := norm_add_le (z - b₀) b₀
      rw [sub_add_cancel] at this
      linarith
    have h1 := Feldman.norm_le_of_zeros hf S hord hδ hM
      (fun w hw b hb => hdist w hw b (hmem b hb)) hzR
    have h2 : (S.map fun b => ‖z - b‖).prod ≤ Λ ^ Multiset.card S :=
      prod_map_le_pow_card S _ hΛ0 (fun b => norm_nonneg _) (fun b hb => by
        have h3 := hΛ b (hmem b hb)
        have h4 : ‖z - b‖ ≤ ‖z - b₀‖ + ‖b₀ - b‖ := by
          have := norm_add_le (z - b₀) (b₀ - b)
          rwa [sub_add_sub_cancel] at this
        linarith)
    rw [hcard] at h1 h2
    rw [le_div_iff₀ hδpow]
    exact h1.trans (mul_le_mul_of_nonneg_right h2 hM0)
  have hC := norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le s one_pos (c := b₀)
    hf.diffContOnCl hsphere
  rw [one_pow, div_one] at hC
  calc ‖iteratedDeriv s f b₀‖ * δ ^ (nodes.card * s)
      ≤ (s.factorial * (Λ ^ (nodes.card * s) * M / δ ^ (nodes.card * s)))
        * δ ^ (nodes.card * s) := mul_le_mul_of_nonneg_right hC hδpow.le
    _ = s.factorial * (Λ ^ (nodes.card * s) * M) := by
        field_simp

/-! ### The final inequality -/

/-- The two bounds contradict each other: an inequality between real numbers. -/
theorem final_ineq {Λ K H E Bc : ℝ} (hΛ : 1 ≤ Λ) (hK : 1 ≤ K) (hH : 1 ≤ H) (hE : 1 ≤ E)
    (hBc : 1 ≤ Bc) {q T s R : ℕ} (hq1 : 1 ≤ q) (hqR : q ≤ 11 * R) (hTs : T ≤ s) (hs9 : 9 ≤ s)
    (hR2 : R * R ≤ s) (hsR : s < 4 * (R * R))
    (hbig : 4 * (Λ ^ 7 * (22 * K) ^ 4 * H ^ 616 * E ^ 11 * 128) * Bc ≤ R) :
    (s.factorial : ℝ) * (Λ ^ (7 * s) * ((q * q : ℕ)
        * (((q * q : ℕ) : ℝ) * ((K * (2 * q)) ^ T * H ^ (14 * q)) * E ^ (q * R))))
      * (H ^ (14 * q) * (2 * ((q * q : ℕ) * (((q * q : ℕ) : ℝ)
        * ((K * (2 * q)) ^ T * H ^ (14 * q)) * (H ^ (14 * q) * (K * (2 * q)) ^ s))) * Bc))
      < ((R : ℝ) / 2) ^ (7 * s) := by
  have hΛ0 : 0 < Λ := by linarith
  have hK0 : 0 < K := by linarith
  have hH0 : 0 < H := by linarith
  have hE0 : 0 < E := by linarith
  have hBc0 : 0 < Bc := by linarith
  set X : ℝ := K * (2 * q) with hX
  set C : ℝ := Λ ^ 7 * (22 * K) ^ 4 * H ^ 616 * E ^ 11 with hC
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hC1 : 1 ≤ C := by
    have h1 : (1 : ℝ) ≤ Λ ^ 7 := one_le_pow₀ hΛ
    have h2 : (1 : ℝ) ≤ (22 * K) ^ 4 := one_le_pow₀ (by linarith)
    have h3 : (1 : ℝ) ≤ H ^ 616 := one_le_pow₀ hH
    have h4 : (1 : ℝ) ≤ E ^ 11 := one_le_pow₀ hE
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le h1 h2) h3) h4
  have hC0 : 0 < C := by linarith
  have hCB : 1 ≤ C * Bc := one_le_mul_of_one_le_of_one_le hC1 hBc
  have hR512 : (512 : ℝ) ≤ R := by nlinarith
  have hR0 : (0 : ℝ) < R := by linarith
  have hR1 : 1 ≤ R := by
    have : (1 : ℝ) ≤ R := by linarith
    exact_mod_cast this
  have hRs : R ≤ s := (Nat.le_mul_self R).trans hR2
  have hX2 : 2 ≤ X := by rw [hX]; nlinarith
  have hXq : (q : ℝ) ≤ X := by rw [hX]; nlinarith
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 < X := by linarith
  have hXR : X ≤ 22 * K * R := by
    rw [hX]
    have : (q : ℝ) ≤ 11 * R := by exact_mod_cast hqR
    nlinarith
  have hLHS : (s.factorial : ℝ) * (Λ ^ (7 * s) * ((q * q : ℕ)
        * (((q * q : ℕ) : ℝ) * (X ^ T * H ^ (14 * q)) * E ^ (q * R))))
      * (H ^ (14 * q) * (2 * ((q * q : ℕ) * (((q * q : ℕ) : ℝ)
        * (X ^ T * H ^ (14 * q)) * (H ^ (14 * q) * X ^ s))) * Bc))
      = (s.factorial : ℝ) * Λ ^ (7 * s) * (2 * (q : ℝ) ^ 8 * X ^ (2 * T + s))
        * H ^ (56 * q) * E ^ (q * R) * Bc := by
    push_cast
    ring
  rw [hLHS]
  have ha : (s.factorial : ℝ) ≤ (s : ℝ) ^ s := by exact_mod_cast Nat.factorial_le_pow s
  have hb : Λ ^ (7 * s) = (Λ ^ 7) ^ s := by rw [pow_mul]
  have hc : 2 * (q : ℝ) ^ 8 * X ^ (2 * T + s) ≤ ((22 * K) ^ 4 * (R : ℝ) ^ 4) ^ s := by
    calc 2 * (q : ℝ) ^ 8 * X ^ (2 * T + s) ≤ X ^ 9 * X ^ (2 * T + s) := by
          have h8 : 2 * (q : ℝ) ^ 8 ≤ X * X ^ 8 :=
            mul_le_mul hX2 (pow_le_pow_left₀ (by positivity) hXq 8) (by positivity)
              (by linarith)
          have h9 : X ^ 9 = X * X ^ 8 := by ring
          rw [h9]
          exact mul_le_mul_of_nonneg_right h8 (by positivity)
      _ = X ^ (2 * T + s + 9) := by ring
      _ ≤ X ^ (4 * s) := pow_le_pow_right₀ hX1 (by omega)
      _ ≤ (22 * K * R) ^ (4 * s) := pow_le_pow_left₀ (by linarith) hXR _
      _ = ((22 * K) ^ 4 * (R : ℝ) ^ 4) ^ s := by rw [pow_mul, mul_pow]
  have hd : H ^ (56 * q) ≤ (H ^ 616) ^ s := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ hH (by omega)
  have he : E ^ (q * R) ≤ (E ^ 11) ^ s := by
    rw [← pow_mul]
    refine pow_le_pow_right₀ hE ?_
    calc q * R ≤ 11 * R * R := Nat.mul_le_mul_right R hqR
      _ = 11 * (R * R) := by ring
      _ ≤ 11 * s := Nat.mul_le_mul_left 11 hR2
  have hf : Bc ≤ Bc ^ s := le_self_pow₀ hBc (by omega)
  have hs0 : (0 : ℝ) ≤ s := by positivity
  calc (s.factorial : ℝ) * Λ ^ (7 * s) * (2 * (q : ℝ) ^ 8 * X ^ (2 * T + s))
        * H ^ (56 * q) * E ^ (q * R) * Bc
      ≤ (s : ℝ) ^ s * (Λ ^ 7) ^ s * ((22 * K) ^ 4 * (R : ℝ) ^ 4) ^ s * (H ^ 616) ^ s
        * (E ^ 11) ^ s * Bc ^ s := by
        rw [hb]
        gcongr
    _ = ((s : ℝ) * Λ ^ 7 * ((22 * K) ^ 4 * (R : ℝ) ^ 4) * H ^ 616 * E ^ 11 * Bc) ^ s := by
        simp only [mul_pow]
    _ < ((R : ℝ) / 2) ^ (7 * s) := by
        rw [show ((R : ℝ) / 2) ^ (7 * s) = (((R : ℝ) / 2) ^ 7) ^ s from by rw [pow_mul]]
        refine pow_lt_pow_left₀ ?_ (by positivity) (by omega)
        have hs4 : (s : ℝ) < 4 * ((R : ℝ) * R) := by exact_mod_cast hsR
        have e1 : (s : ℝ) * Λ ^ 7 * ((22 * K) ^ 4 * (R : ℝ) ^ 4) * H ^ 616 * E ^ 11 * Bc
            = (s : ℝ) * (C * Bc * (R : ℝ) ^ 4) := by
          rw [hC]
          ring
        have e2 : ((R : ℝ) / 2) ^ 7 = (R : ℝ) ^ 7 / 128 := by
          rw [div_pow]
          norm_num
        rw [e1, e2, lt_div_iff₀ (by norm_num)]
        have hpos : 0 < C * Bc * (R : ℝ) ^ 4 := by positivity
        calc (s : ℝ) * (C * Bc * (R : ℝ) ^ 4) * 128
            < 4 * ((R : ℝ) * R) * (C * Bc * (R : ℝ) ^ 4) * 128 := by
              have := mul_lt_mul_of_pos_right hs4 hpos
              linarith
          _ = (R : ℝ) ^ 6 * (4 * (C * 128) * Bc) := by ring
          _ ≤ (R : ℝ) ^ 6 * R := mul_le_mul_of_nonneg_left hbig (by positivity)
          _ = (R : ℝ) ^ 7 := by ring

namespace Data

variable (D : Data)

/-- **The extrapolation step**: once `F` vanishes to order `s ≥ T` at the seven points, its
derivative of order `s` vanishes there too. -/
theorem step_false {κ q T : ℕ} (hκ1 : 1 ≤ κ) (hq : q = 14 * κ) (hT : T = 7 * (κ * κ))
    (hκℓ : 14 * ‖D.ℓ‖ + 2 ≤ κ)
    (hκbig : 4 * ((14 * ‖D.ℓ‖ + 1) ^ 7 * (22 * (D.K : ℝ)) ^ 4 * (D.H : ℝ) ^ 616
      * (Real.exp (1 + ‖D.β‖)) ^ 11 * 128) * D.Bc ≤ κ)
    (c : Fin q × Fin q → ℤ)
    (hcb : ∀ ij, |c ij| ≤ (q * q : ℕ) * ((D.K * (2 * q)) ^ T * D.H ^ (2 * q * 7)))
    {s : ℕ} (hs : T ≤ s)
    (hzero : ∀ t < s, ∀ k : ℕ, k < 7 → iteratedDeriv t (D.F q c) (k * D.ℓ) = 0)
    {k₀ : ℕ} (hk₀ : k₀ < 7) (hne : iteratedDeriv s (D.F q c) (k₀ * D.ℓ) ≠ 0) : False := by
  classical
  have hK : (1 : ℝ) ≤ D.K := by exact_mod_cast D.one_le_K
  have hH : (1 : ℝ) ≤ D.H := by exact_mod_cast D.one_le_H
  have hBc := D.one_le_Bc
  have hK0 : (0 : ℝ) < D.K := by linarith
  have hH0 : (0 : ℝ) < D.H := by linarith
  have hBc0 : 0 < D.Bc := by linarith
  have hℓ0 := norm_nonneg D.ℓ
  have hq1 : 1 ≤ q := by omega
  set R := Nat.sqrt s with hRdef
  have hR2 : R * R ≤ s := Nat.sqrt_le s
  have hsR' : s < (R + 1) * (R + 1) := Nat.lt_succ_sqrt s
  have hκκ : κ * κ ≤ s := by
    rw [hT] at hs
    omega
  have hκR : κ ≤ R := Nat.le_sqrt.mpr hκκ
  have hR1 : 1 ≤ R := hκ1.trans hκR
  have hsR : s < 4 * (R * R) := by
    calc s < (R + 1) * (R + 1) := hsR'
      _ ≤ (R + R) * (R + R) := Nat.mul_le_mul (by omega) (by omega)
      _ = 4 * (R * R) := by ring
  have hqR : q ≤ 11 * R := by
    by_contra h
    push Not at h
    have h1 : (11 * R + 1) * (11 * R + 1) ≤ q * q := Nat.mul_le_mul h h
    have h2 : q * q = 28 * T := by rw [hq, hT]; ring
    have h3 : (11 * R + 1) * (11 * R + 1) = 121 * (R * R) + 22 * R + 1 := by ring
    omega
  have hs9 : 9 ≤ s := by
    have : (14 * ‖D.ℓ‖ + 2 : ℝ) ≤ κ := hκℓ
    have h2 : (2 : ℝ) ≤ κ := by linarith
    have h2' : 2 ≤ κ := by exact_mod_cast h2
    have : 4 ≤ κ * κ := Nat.mul_le_mul h2' h2'
    rw [hT] at hs
    omega
  have hκRr : (κ : ℝ) ≤ R := by exact_mod_cast hκR
  have hRℓ : 14 * ‖D.ℓ‖ + 2 ≤ (R : ℝ) := hκℓ.trans hκRr
  -- the nodes
  set nodes : Finset ℂ := (Finset.range 7).image fun k : ℕ => (k : ℂ) * D.ℓ with hnodes
  have hcard : nodes.card = 7 := by
    rw [hnodes, Finset.card_image_of_injective _ (fun a b h => by
      have := mul_right_cancel₀ D.hℓ h
      exact_mod_cast this), Finset.card_range]
  have hnode_norm : ∀ k : ℕ, k < 7 → ‖(k : ℂ) * D.ℓ‖ ≤ 7 * ‖D.ℓ‖ := by
    intro k hk
    rw [norm_mul, Complex.norm_natCast]
    have : (k : ℝ) ≤ 7 := by exact_mod_cast hk.le
    exact mul_le_mul_of_nonneg_right this hℓ0
  have hCbz : (0 : ℤ) ≤ (q * q : ℕ) * ((D.K * (2 * q)) ^ T * D.H ^ (2 * q * 7)) := by
    have h1 := D.one_le_K
    have h2 := D.one_le_H
    have : (0 : ℤ) ≤ D.K * (2 * q) := by positivity
    positivity
  set Cb : ℝ := ((q * q : ℕ) : ℝ) * (((D.K : ℝ) * (2 * q)) ^ T * (D.H : ℝ) ^ (14 * q))
    with hCb
  have hCbcast : (((q * q : ℕ) * ((D.K * (2 * q)) ^ T * D.H ^ (2 * q * 7)) : ℤ) : ℝ) = Cb := by
    rw [hCb, show 2 * q * 7 = 14 * q by ring]
    push_cast
    ring
  have hCb0 : 0 ≤ Cb := by
    rw [← hCbcast]
    exact_mod_cast hCbz
  have hcr : ∀ ij, |(c ij : ℝ)| ≤ Cb := fun ij => by
    rw [← hCbcast]
    exact_mod_cast hcb ij
  -- the analytic bound
  have hana := norm_iteratedDeriv_mul_le_of_zeros (D.differentiable_F q c) nodes (s := s)
    (fun b hb t ht => by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hb
      exact hzero t ht k (Finset.mem_range.mp hk))
    (R := R) (M := (q * q : ℕ) * (Cb * Real.exp ((q : ℝ) * (1 + ‖D.β‖) * R)))
    (Λ := 14 * ‖D.ℓ‖ + 1) (δ := (R : ℝ) / 2) (by linarith) (by linarith)
    (fun w hw => by
      have := D.norm_F_le q c hCb0 hcr w
      rwa [mem_sphere_zero_iff_norm.mp hw] at this)
    (fun w hw b hb => by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hb
      have h1 := hnode_norm k (Finset.mem_range.mp hk)
      have h2 := norm_sub_norm_le w ((k : ℂ) * D.ℓ)
      rw [mem_sphere_zero_iff_norm.mp hw] at h2
      linarith)
    (b₀ := (k₀ : ℂ) * D.ℓ)
    (fun b hb => by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hb
      have h1 := hnode_norm k (Finset.mem_range.mp hk)
      have h2 := hnode_norm k₀ hk₀
      have h3 := norm_sub_le ((k₀ : ℂ) * D.ℓ) ((k : ℂ) * D.ℓ)
      linarith)
    (by
      have h2 := hnode_norm k₀ hk₀
      linarith)
  rw [hcard] at hana
  -- the arithmetic bound
  have hari := D.one_le_norm_deriv_mul q c hCbz hcb s k₀ hne
  rw [hCbcast] at hari
  set γ := ‖iteratedDeriv s (D.F q c) (k₀ * D.ℓ)‖ with hγ
  have hγ0 : 0 ≤ γ := norm_nonneg _
  have hk14 : 2 * q * k₀ ≤ 14 * q := by
    calc 2 * q * k₀ ≤ 2 * q * 7 := Nat.mul_le_mul_left _ hk₀.le
      _ = 14 * q := by ring
  have hd_le : (D.d : ℝ) ^ (2 * q * k₀) ≤ (D.H : ℝ) ^ (14 * q) := by
    have hdH : (D.d : ℝ) ≤ D.H := by
      have : (D.d : ℤ) ≤ D.H := le_max_right _ _
      exact_mod_cast this
    exact (pow_le_pow_left₀ (by positivity) hdH _).trans (pow_le_pow_right₀ hH hk14)
  have hH_le : (D.H : ℝ) ^ (2 * q * k₀) ≤ (D.H : ℝ) ^ (14 * q) := pow_le_pow_right₀ hH hk14
  have hKq0 : (0 : ℝ) ≤ (D.K : ℝ) * (2 * q) := by positivity
  have hY : (D.d : ℝ) ^ (2 * q * k₀) * (2 * ((q * q : ℕ) * (Cb * ((D.H : ℝ) ^ (2 * q * k₀)
        * ((D.K : ℝ) * (2 * q)) ^ s))) * D.Bc)
      ≤ (D.H : ℝ) ^ (14 * q) * (2 * ((q * q : ℕ) * (Cb * ((D.H : ℝ) ^ (14 * q)
        * ((D.K : ℝ) * (2 * q)) ^ s))) * D.Bc) := by
    gcongr
  have hexp : Real.exp ((q : ℝ) * (1 + ‖D.β‖) * R) = Real.exp (1 + ‖D.β‖) ^ (q * R) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hexp] at hana
  have hfin := final_ineq (Λ := 14 * ‖D.ℓ‖ + 1) (K := D.K) (H := D.H)
    (E := Real.exp (1 + ‖D.β‖)) (Bc := D.Bc) (by linarith) hK hH
    (Real.one_le_exp (by positivity)) hBc hq1 hqR hs hs9 hR2 hsR (hκbig.trans hκRr)
  rw [← hCb] at hfin
  have hδ0 : (0 : ℝ) < ((R : ℝ) / 2) ^ (7 * s) := by positivity
  have hY0 : 0 ≤ (D.d : ℝ) ^ (2 * q * k₀) * (2 * ((q * q : ℕ) * (Cb * ((D.H : ℝ) ^ (2 * q * k₀)
        * ((D.K : ℝ) * (2 * q)) ^ s))) * D.Bc) := by positivity
  have hchain : ((R : ℝ) / 2) ^ (7 * s)
      ≤ (s.factorial : ℝ) * ((14 * ‖D.ℓ‖ + 1) ^ (7 * s) * ((q * q : ℕ)
          * (Cb * Real.exp (1 + ‖D.β‖) ^ (q * R))))
        * ((D.H : ℝ) ^ (14 * q) * (2 * ((q * q : ℕ) * (Cb * ((D.H : ℝ) ^ (14 * q)
          * ((D.K : ℝ) * (2 * q)) ^ s))) * D.Bc)) := by
    calc ((R : ℝ) / 2) ^ (7 * s) = ((R : ℝ) / 2) ^ (7 * s) * 1 := (mul_one _).symm
      _ ≤ ((R : ℝ) / 2) ^ (7 * s) * (γ * ((D.d : ℝ) ^ (2 * q * k₀) * (2 * ((q * q : ℕ)
            * (Cb * ((D.H : ℝ) ^ (2 * q * k₀) * ((D.K : ℝ) * (2 * q)) ^ s))) * D.Bc))) :=
          mul_le_mul_of_nonneg_left hari hδ0.le
      _ = (γ * ((R : ℝ) / 2) ^ (7 * s)) * ((D.d : ℝ) ^ (2 * q * k₀) * (2 * ((q * q : ℕ)
            * (Cb * ((D.H : ℝ) ^ (2 * q * k₀) * ((D.K : ℝ) * (2 * q)) ^ s))) * D.Bc)) := by
          ring
      _ ≤ _ := mul_le_mul hana hY hY0 (by positivity)
  exact absurd hfin (not_lt.mpr hchain)

/-- **There is no such data.** -/
theorem false (D : Data) : False := by
  obtain ⟨κ, hκ⟩ := exists_nat_ge (max (14 * ‖D.ℓ‖ + 2)
    (4 * ((14 * ‖D.ℓ‖ + 1) ^ 7 * (22 * (D.K : ℝ)) ^ 4 * (D.H : ℝ) ^ 616
      * (Real.exp (1 + ‖D.β‖)) ^ 11 * 128) * D.Bc))
  have hκℓ := (le_max_left _ _).trans hκ
  have hκbig := (le_max_right _ _).trans hκ
  have hκ1 : 1 ≤ κ := by
    have : (1 : ℝ) ≤ κ := by
      have := norm_nonneg D.ℓ
      linarith
    exact_mod_cast this
  have hTpos : 0 < 7 * (κ * κ) := by positivity
  obtain ⟨c, hc0, hvan, hcb⟩ := D.exists_coeffs (q := 14 * κ) (T := 7 * (κ * κ)) (m := 7)
    (by ring) hTpos (by norm_num)
  have hall : ∀ s, ∀ t < s, ∀ k : ℕ, k < 7 →
      iteratedDeriv t (D.F (14 * κ) c) (k * D.ℓ) = 0 := by
    intro s
    induction s with
    | zero => intro t ht; omega
    | succ s ih =>
      intro t ht k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp ht with h | rfl
      · exact ih t h k hk
      · by_cases htT : t < 7 * (κ * κ)
        · exact hvan t htT k hk
        · by_contra hne
          exact D.step_false hκ1 rfl rfl hκℓ hκbig c hcb (not_lt.mp htT) ih hk hne
  refine hc0 (D.coeffs_eq_zero (14 * κ) c fun t => ?_)
  have h := hall (t + 1) t (Nat.lt_succ_self t) 0 (by norm_num)
  rw [iteratedDeriv_F] at h
  simpa using h

end Data

/-- **Gelfond–Schneider for a quadratic integer exponent and rational values**: for a
quadratic irrational integer `β` and `ℓ ≠ 0`, the numbers `e^ℓ` and `e^{βℓ}` are not both
rational. -/
theorem not_rational_exp_pair {β ℓ : ℂ} {u v : ℤ} (hβ : β ^ 2 = u * β + v)
    (hirr : ∀ x y : ℤ, (x : ℂ) + y * β = 0 → x = 0 ∧ y = 0) (hℓ : ℓ ≠ 0) (a b : ℚ)
    (ha : Complex.exp ℓ = a) (hb : Complex.exp (β * ℓ) = b) : False := by
  have had : (a.den : ℂ) ≠ 0 := by exact_mod_cast a.den_ne_zero
  have hbd : (b.den : ℂ) ≠ 0 := by exact_mod_cast b.den_ne_zero
  refine Data.false ⟨β, u, v, hβ, hirr, ℓ, hℓ, a.num * b.den, b.num * a.den, a.den * b.den,
    Nat.mul_pos a.den_pos b.den_pos, ?_, ?_⟩
  · rw [ha, Rat.cast_def a]
    push_cast
    field_simp
  · rw [hb, Rat.cast_def b]
    push_cast
    field_simp

end Azurite.GelfondSchneider

namespace Azurite

open Real

/-- **Gelfond's constant `e^π` is irrational** (Gelfond, 1929): `e^π = (−1)^{−i}`. -/
theorem irrational_exp_pi : Irrational (Real.exp π) := by
  rintro ⟨b, hb⟩
  refine GelfondSchneider.not_rational_exp_pair (β := -Complex.I) (ℓ := π * Complex.I)
    (u := 0) (v := -1) (by simp) (fun x y h => ?_) (by simp [Real.pi_ne_zero]) (-1) b
    (by rw [Complex.exp_pi_mul_I]; simp) ?_
  · have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp at h1 h2
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  · have : -Complex.I * (π * Complex.I) = ((π : ℝ) : ℂ) := by
      rw [show -Complex.I * (π * Complex.I) = -(Complex.I * Complex.I) * π by ring,
        Complex.I_mul_I]
      simp
    rw [this, ← Complex.ofReal_exp, ← hb]
    simp

/-- **`e^{π√n}` is irrational** for every positive integer `n`: `e^{π√n} = (−1)^{−i√n}`.  For
`n = 163` this is Ramanujan's constant. -/
theorem irrational_exp_pi_sqrt {n : ℕ} (hn : 0 < n) : Irrational (Real.exp (π * √(n : ℝ))) := by
  rintro ⟨b, hb⟩
  have hs0 : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hsq : ((√(n : ℝ) : ℝ) : ℂ) ^ 2 = (n : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg n)
  refine GelfondSchneider.not_rational_exp_pair (β := -Complex.I * (√(n : ℝ) : ℝ))
    (ℓ := π * Complex.I) (u := 0) (v := -(n : ℤ)) ?_ (fun x y h => ?_)
    (by simp [Real.pi_ne_zero]) (-1) b (by rw [Complex.exp_pi_mul_I]; simp) ?_
  · rw [mul_pow, hsq]
    simp
  · have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp at h1 h2
    refine ⟨by exact_mod_cast h1, ?_⟩
    rcases h2 with h2 | h2
    · exact_mod_cast h2
    · exact absurd h2 (by positivity)
  · have : -Complex.I * (√(n : ℝ) : ℝ) * (π * Complex.I) = ((π * √(n : ℝ) : ℝ) : ℂ) := by
      rw [show -Complex.I * (√(n : ℝ) : ℝ) * (π * Complex.I)
        = -(Complex.I * Complex.I) * (π * (√(n : ℝ) : ℝ)) by ring, Complex.I_mul_I]
      push_cast
      ring
    rw [this, ← Complex.ofReal_exp, ← hb]
    simp

/-- **The Gelfond–Schneider constant `2^√2` is irrational.** -/
theorem irrational_two_rpow_sqrt_two : Irrational ((2 : ℝ) ^ (√2 : ℝ)) := by
  rintro ⟨b, hb⟩
  have hsq : ((√2 : ℝ) : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  refine GelfondSchneider.not_rational_exp_pair (β := ((√2 : ℝ) : ℂ))
    (ℓ := ((Real.log 2 : ℝ) : ℂ)) (u := 0) (v := 2) (by rw [hsq]; simp) (fun x y h => ?_)
    (by exact_mod_cast hlog) 2 b ?_ ?_
  · have h' : (x : ℝ) + y * √2 = 0 := by exact_mod_cast h
    by_cases hy : y = 0
    · rw [hy] at h'
      simp at h'
      exact ⟨by exact_mod_cast h', hy⟩
    · exfalso
      have hy' : (y : ℝ) ≠ 0 := by exact_mod_cast hy
      refine irrational_sqrt_two ⟨-(x : ℚ) / y, ?_⟩
      push_cast
      field_simp
      linarith
  · rw [← Complex.ofReal_exp, Real.exp_log (by norm_num)]
    simp
  · rw [← Complex.ofReal_mul, ← Complex.ofReal_exp, mul_comm, ← Real.rpow_def_of_pos
      (by norm_num), ← hb]
    simp

end Azurite
