/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.Matrix.LDL
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# DLMF §3.11(v): Least squares approximations

Formalizations of <https://dlmf.nist.gov/3.11.v> (first part; the discrete Fourier transform is in
`Section11DFT.lean`).

* 3.11.31–3.11.35: `lsApprox` (`Φₙ = ∑ aₖφₖ`), `lsSum` (the weighted sum of squares 3.11.32),
  `gramX` (`X_{kℓ}`), `gramF` (`F_k`); `lsSum_add` (exact quadratic expansion).
* "From the equations `∂S/∂a_k = 0` we derive the normal equations": `dlmf_3_11_v_partial`
  (`∂S/∂a_k = 2((Xa)_k − F_k)`), and `dlmf_3_11_33` (`a` minimizes 3.11.32 iff 3.11.33 holds, for a
  nonnegative weight); "the matrix is again symmetric" (`gramX_symm`).
* 3.11.36 (`LinIndepOn`): "then the approximation `Φₙ(x)` is determined uniquely"
  (`dlmf_3_11_v_unique`, existence and uniqueness of the minimizing coefficients); the Gram matrix
  is positive definite (`gramX_posDef`).
* Orthogonal `φₖ`: "the system (3.11.33) is diagonal" (`dlmf_3_11_v_orthogonal`,
  `aₖ = Fₖ/Xₖₖ`); "can always be orthogonalized … by the Gram–Schmidt procedure"
  (`dlmf_3_11_v_gram_schmidt`).
* The polynomial case 3.11.27–3.11.30 (`φₖ = xᵏ`, `w = 1`): `momX`, `momF`, `dlmf_3_11_29`;
  "The matrix is symmetric and positive definite" for `J ≥ n + 1` distinct points
  (`dlmf_3_11_29_posDef`); unique least squares polynomial (`dlmf_3_11_v_poly_unique`); "If
  `J = n + 1`, then `pₙ(x)` is the Lagrange interpolation polynomial" (`dlmf_3_11_v_lagrange`).

"the system is ill-conditioned when `n` is large because the lower rows of the matrix are
approximately proportional to one another" and "well-conditioned" are qualitative and not
formalized; Gautschi (1997a) and Björck (1996) are references.
-/

open Finset

namespace Azurite.DLMF

variable {J n : ℕ}

/-! ### Weighted least squares -/

/-- **DLMF 3.11.31**: `Φₙ(x) = aₙφₙ(x) + ⋯ + a₀φ₀(x)`. -/
noncomputable def lsApprox (φ : Fin (n + 1) → ℝ → ℝ) (a : Fin (n + 1) → ℝ) (t : ℝ) : ℝ :=
  ∑ k, a k * φ k t

/-- **DLMF 3.11.32**: `∑_j w(x_j)(f(x_j) − Φₙ(x_j))²`. -/
noncomputable def lsSum (x : Fin J → ℝ) (w f : ℝ → ℝ) (φ : Fin (n + 1) → ℝ → ℝ)
    (a : Fin (n + 1) → ℝ) : ℝ :=
  ∑ j, w (x j) * (f (x j) - lsApprox φ a (x j)) ^ 2

/-- **DLMF 3.11.34**: `X_{kℓ} = ∑_j w(x_j)φₖ(x_j)φ_ℓ(x_j)`. -/
noncomputable def gramX (x : Fin J → ℝ) (w : ℝ → ℝ) (φ : Fin (n + 1) → ℝ → ℝ)
    (k l : Fin (n + 1)) : ℝ :=
  ∑ j, w (x j) * φ k (x j) * φ l (x j)

/-- **DLMF 3.11.35**: `F_k = ∑_j w(x_j)f(x_j)φₖ(x_j)`. -/
noncomputable def gramF (x : Fin J → ℝ) (w f : ℝ → ℝ) (φ : Fin (n + 1) → ℝ → ℝ)
    (k : Fin (n + 1)) : ℝ :=
  ∑ j, w (x j) * f (x j) * φ k (x j)

/-- "Since `X_{kℓ} = X_{ℓk}`, the matrix is again symmetric." -/
theorem gramX_symm (x : Fin J → ℝ) (w : ℝ → ℝ) (φ : Fin (n + 1) → ℝ → ℝ) (k l : Fin (n + 1)) :
    gramX x w φ k l = gramX x w φ l k := by
  simp only [gramX]; exact sum_congr rfl fun _ _ => by ring

section Expansion

variable (x : Fin J → ℝ) (w f : ℝ → ℝ) (φ : Fin (n + 1) → ℝ → ℝ)

theorem sum_lin_resid (a h : Fin (n + 1) → ℝ) :
    ∑ j, w (x j) * lsApprox φ h (x j) * (f (x j) - lsApprox φ a (x j)) =
      ∑ k, h k * (gramF x w f φ k - ∑ l, gramX x w φ k l * a l) := by
  simp only [lsApprox, gramF, gramX, mul_sub, sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
  congr 1
  · rw [Finset.sum_comm]; exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
  · conv_rhs => enter [2, k]; rw [Finset.sum_comm]
    conv_lhs => enter [2, j]; rw [Finset.sum_comm]
    conv_lhs => rw [Finset.sum_comm]
    exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

theorem sum_quad (h : Fin (n + 1) → ℝ) :
    ∑ j, w (x j) * lsApprox φ h (x j) ^ 2 = ∑ k, ∑ l, h k * gramX x w φ k l * h l := by
  simp only [lsApprox, gramX, sq, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  exact sum_congr rfl fun l _ => sum_congr rfl fun j _ => by ring

/-- The exact expansion `S(a + h) = S(a) − 2∑ₖ hₖ(Fₖ − (Xa)ₖ) + hᵀXh`. -/
theorem lsSum_add (a h : Fin (n + 1) → ℝ) :
    lsSum x w f φ (a + h) = lsSum x w f φ a -
      2 * ∑ k, h k * (gramF x w f φ k - ∑ l, gramX x w φ k l * a l) +
        ∑ k, ∑ l, h k * gramX x w φ k l * h l := by
  rw [← sum_lin_resid, ← sum_quad]
  simp only [lsSum, Finset.mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  have : lsApprox φ (a + h) (x j) = lsApprox φ a (x j) + lsApprox φ h (x j) := by
    simp only [lsApprox, Pi.add_apply, add_mul, sum_add_distrib]
  rw [this]
  ring

theorem quad_nonneg (hw : ∀ j, 0 ≤ w (x j)) (h : Fin (n + 1) → ℝ) :
    0 ≤ ∑ k, ∑ l, h k * gramX x w φ k l * h l := by
  rw [← sum_quad]
  exact sum_nonneg fun j _ => mul_nonneg (hw j) (sq_nonneg _)

theorem lsSum_add_single (a : Fin (n + 1) → ℝ) (k : Fin (n + 1)) (t : ℝ) :
    lsSum x w f φ (a + t • Pi.single k 1) = lsSum x w f φ a -
      2 * t * (gramF x w f φ k - ∑ l, gramX x w φ k l * a l) + t ^ 2 * gramX x w φ k k := by
  rw [lsSum_add]
  have h1 : ∀ c : Fin (n + 1) → ℝ, ∑ l, (t • Pi.single k (1 : ℝ) : Fin (n + 1) → ℝ) l * c l =
      t * c k := fun c => by
    rw [Finset.sum_eq_single k (fun b _ hb => by simp [hb]) (by simp)]; simp
  rw [h1]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, ite_mul, mul_one, mul_zero,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

/-- **DLMF §3.11(v)**: `∂S/∂a_k = 2((Xa)_k − F_k)`. -/
theorem dlmf_3_11_v_partial (a : Fin (n + 1) → ℝ) (k : Fin (n + 1)) :
    HasDerivAt (fun t : ℝ => lsSum x w f φ (a + t • Pi.single k 1))
      (2 * (∑ l, gramX x w φ k l * a l - gramF x w f φ k)) 0 := by
  simp only [lsSum_add_single]
  have h1 := HasDerivAt.const_sub (lsSum x w f φ a)
    (hasDerivAt_mul_const (x := (0 : ℝ)) (2 * (gramF x w f φ k - ∑ l, gramX x w φ k l * a l)))
  have h2 := HasDerivAt.mul_const (hasDerivAt_pow 2 (0 : ℝ)) (gramX x w φ k k)
  convert HasDerivAt.add h1 h2 using 1
  · funext t; simp only [Pi.add_apply]; ring
  · simp; ring

/-- **DLMF 3.11.33**: for a nonnegative weight, `a` minimizes 3.11.32 iff it solves the normal
equations `∑_ℓ X_{kℓ} a_ℓ = F_k`. -/
theorem dlmf_3_11_33 (hw : ∀ j, 0 ≤ w (x j)) (a : Fin (n + 1) → ℝ) :
    (∀ b, lsSum x w f φ a ≤ lsSum x w f φ b) ↔
      ∀ k, ∑ l, gramX x w φ k l * a l = gramF x w f φ k := by
  constructor
  · intro hmin k
    by_contra hne
    have hX : 0 ≤ gramX x w φ k k := by
      simp only [gramX]
      exact sum_nonneg fun j _ => by nlinarith [hw j, sq_nonneg (φ k (x j))]
    generalize hg : gramF x w f φ k - ∑ l, gramX x w φ k l * a l = g
    have hg0 : g ≠ 0 := fun h0 => hne (by linarith)
    have hmt := hmin (a + (g / (gramX x w φ k k + 1)) • Pi.single k 1)
    rw [lsSum_add_single, hg] at hmt
    generalize ht : g / (gramX x w φ k k + 1) = t at hmt
    have hgt : g = t * (gramX x w φ k k + 1) := by
      rw [← ht]; field_simp
    have ht0 : t ≠ 0 := by rintro rfl; exact hg0 (by simpa using hgt)
    rw [hgt] at hmt
    nlinarith [pow_pos (sq_pos_of_ne_zero ht0) 1]
  · intro hn b
    have e : b = a + (b - a) := by abel
    rw [e, lsSum_add]
    have : ∑ k, (b - a) k * (gramF x w f φ k - ∑ l, gramX x w φ k l * a l) = 0 :=
      sum_eq_zero fun k _ => by rw [hn k, sub_self, mul_zero]
    rw [this]
    linarith [quad_nonneg x w φ hw (b - a)]

end Expansion

/-- **DLMF 3.11.36**: the `φₖ` are linearly independent on `x₁, …, x_J`. -/
def LinIndepOn (x : Fin J → ℝ) (φ : Fin (n + 1) → ℝ → ℝ) : Prop :=
  ∀ c : Fin (n + 1) → ℝ, (∀ j, ∑ k, c k * φ k (x j) = 0) → c = 0

theorem quad_eq_zero {x : Fin J → ℝ} {w : ℝ → ℝ} {φ : Fin (n + 1) → ℝ → ℝ}
    (hw : ∀ j, 0 < w (x j)) (hind : LinIndepOn x φ) {h : Fin (n + 1) → ℝ}
    (h0 : ∑ k, ∑ l, h k * gramX x w φ k l * h l = 0) : h = 0 := by
  rw [← sum_quad] at h0
  have hall := (sum_eq_zero_iff_of_nonneg fun j _ =>
    mul_nonneg (hw j).le (sq_nonneg (lsApprox φ h (x j)))).mp h0
  refine hind h fun j => ?_
  have := hall j (mem_univ j)
  rcases mul_eq_zero.mp this with h1 | h1
  · exact absurd h1 (hw j).ne'
  · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1

/-- The Gram matrix is positive definite when the `φₖ` are independent on the points. -/
theorem gramX_posDef {x : Fin J → ℝ} {w : ℝ → ℝ} {φ : Fin (n + 1) → ℝ → ℝ}
    (hw : ∀ j, 0 < w (x j)) (hind : LinIndepOn x φ) :
    (Matrix.of fun k l => gramX x w φ k l).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun h hh => ?_
  · ext k l; simp [Matrix.conjTranspose_apply, gramX_symm]
  · have e : dotProduct (star h) (Matrix.mulVec (Matrix.of fun k l => gramX x w φ k l) h) =
        ∑ k, ∑ l, h k * gramX x w φ k l * h l := by
      simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    rw [e]
    exact lt_of_le_of_ne (quad_nonneg x w φ (fun j => (hw j).le) h)
      fun h0 => hh (quad_eq_zero hw hind h0.symm)

/-- **DLMF §3.11(v)**: "If the functions `φₖ(x)` are linearly independent on the set … then the
approximation `Φₙ(x)` is determined uniquely": there is exactly one coefficient vector minimizing
3.11.32 (`w > 0`). -/
theorem dlmf_3_11_v_unique {x : Fin J → ℝ} {w : ℝ → ℝ} (f : ℝ → ℝ) {φ : Fin (n + 1) → ℝ → ℝ}
    (hw : ∀ j, 0 < w (x j)) (hind : LinIndepOn x φ) :
    ∃! a : Fin (n + 1) → ℝ, ∀ b, lsSum x w f φ a ≤ lsSum x w f φ b := by
  set M := Matrix.of fun k l => gramX x w φ k l
  have hinj : Function.Injective M.mulVec := by
    intro u v huv
    have hd : M.mulVec (u - v) = 0 := by rw [Matrix.mulVec_sub, huv, sub_self]
    have : u - v = 0 := quad_eq_zero hw hind (by
      have := congrArg (fun z => (u - v) ⬝ᵥ z) hd
      simp only [dotProduct_zero] at this
      rw [← this]
      simp [M, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_comm, mul_left_comm])
    exact sub_eq_zero.mp this
  have hsurj : Function.Surjective M.mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr (Matrix.mulVec_injective_iff_isUnit.mp hinj)
  obtain ⟨a, ha⟩ := hsurj (gramF x w f φ)
  have hn : ∀ k, ∑ l, gramX x w φ k l * a l = gramF x w f φ k := fun k => by
    have := congrFun ha k
    simpa [M, Matrix.mulVec, dotProduct] using this
  refine ⟨a, (dlmf_3_11_33 x w f φ (fun j => (hw j).le) a).mpr hn, fun b hb => ?_⟩
  have hb' := (dlmf_3_11_33 x w f φ (fun j => (hw j).le) b).mp hb
  apply hinj
  funext k
  simp only [M, Matrix.mulVec, dotProduct, Matrix.of_apply]
  rw [hb' k, hn k]

/-- **DLMF §3.11(v)**: if the `φₖ` are orthogonal on the points (`X_{kℓ} = 0` for `k ≠ ℓ`), "the
system (3.11.33) is diagonal": the minimizing coefficients are `aₖ = Fₖ/Xₖₖ`. -/
theorem dlmf_3_11_v_orthogonal {x : Fin J → ℝ} {w : ℝ → ℝ} (f : ℝ → ℝ)
    {φ : Fin (n + 1) → ℝ → ℝ} (hw : ∀ j, 0 < w (x j)) (hind : LinIndepOn x φ)
    (horth : ∀ k l, k ≠ l → gramX x w φ k l = 0) :
    ∀ b, lsSum x w f φ (fun k => gramF x w f φ k / gramX x w φ k k) ≤ lsSum x w f φ b := by
  have hXpos : ∀ k, 0 < gramX x w φ k k := fun k => by
    simpa using (gramX_posDef hw hind).diag_pos (i := k)
  refine (dlmf_3_11_33 x w f φ (fun j => (hw j).le) _).mpr fun k => ?_
  rw [Finset.sum_eq_single k (fun l _ hl => by rw [horth k l (Ne.symm hl), zero_mul])
    (by simp)]
  field_simp [(hXpos k).ne']

/-! ### Gram–Schmidt -/

theorem gramX_lin (x : Fin J → ℝ) (w : ℝ → ℝ) (φ : Fin (n + 1) → ℝ → ℝ)
    (r : Fin (n + 1) → Fin (n + 1) → ℝ) (k l : Fin (n + 1)) :
    gramX x w (fun i t => ∑ m, r i m * φ m t) k l =
      ∑ a, ∑ b, r k a * gramX x w φ a b * r l b := by
  simp only [gramX, Finset.mul_sum, Finset.sum_mul]
  conv_rhs => enter [2, a]; rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

/-- **DLMF §3.11(v)**: "A set of functions `φ₀(x), …, φₙ(x)` that is linearly independent on the
set `x₁, …, x_J` … can always be orthogonalized … by the Gram–Schmidt procedure": there are
`ψₖ = ∑_{ℓ ≤ k} r_{kℓ}φ_ℓ`, orthogonal with respect to weighted summation and again independent
(the LDL factorization of the positive definite Gram matrix). -/
theorem dlmf_3_11_v_gram_schmidt {x : Fin J → ℝ} {w : ℝ → ℝ} {φ : Fin (n + 1) → ℝ → ℝ}
    (hw : ∀ j, 0 < w (x j)) (hind : LinIndepOn x φ) :
    ∃ r : Fin (n + 1) → Fin (n + 1) → ℝ, (∀ k l, k < l → r k l = 0) ∧
      (∀ k l, k ≠ l → gramX x w (fun i t => ∑ m, r i m * φ m t) k l = 0) ∧
      LinIndepOn x (fun i t => ∑ m, r i m * φ m t) := by
  have hS := gramX_posDef hw hind
  set R := LDL.lowerInv hS
  refine ⟨fun k l => R k l, fun k l hkl => LDL.isLowerTriangular_lowerInv hS hkl,
    fun k l hkl => ?_, fun c hc => ?_⟩
  · have h := congrFun (congrFun (LDL.diag_eq_lowerInv_conj hS) k) l
    rw [LDL.diag, Matrix.diagonal_apply_ne _ hkl] at h
    rw [gramX_lin, h]
    simp [Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  · -- `cᵀR` annihilates the `φ`, hence vanishes; `R` is invertible
    have h1 : Matrix.vecMul c R = 0 := hind _ fun j => by
      rw [← hc j]
      simp only [Matrix.vecMul, dotProduct, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
    have : c = Matrix.vecMul (Matrix.vecMul c R) ⅟R := by
      rw [Matrix.vecMul_vecMul, mul_invOf_self, Matrix.vecMul_one]
    rw [this, h1, Matrix.zero_vecMul]

/-! ### The polynomial case 3.11.27–3.11.30 -/

/-- **DLMF 3.11.30**: `X_k = ∑_j x_j^k`. -/
noncomputable def momX (x : Fin J → ℝ) (k : ℕ) : ℝ := ∑ j, x j ^ k

/-- **DLMF 3.11.30**: `F_k = ∑_j f(x_j) x_j^k`. -/
noncomputable def momF (x : Fin J → ℝ) (f : ℝ → ℝ) (k : ℕ) : ℝ := ∑ j, f (x j) * x j ^ k

/-- The monomials `φₖ(x) = xᵏ`. -/
def monoBasis (n : ℕ) : Fin (n + 1) → ℝ → ℝ := fun k t => t ^ (k : ℕ)

theorem gramX_mono (x : Fin J → ℝ) (k l : Fin (n + 1)) :
    gramX x (fun _ => 1) (monoBasis n) k l = momX x (k + l) := by
  simp only [gramX, monoBasis, momX, one_mul, pow_add]

theorem gramF_mono (x : Fin J → ℝ) (f : ℝ → ℝ) (k : Fin (n + 1)) :
    gramF x (fun _ => 1) f (monoBasis n) k = momF x f k := by
  simp only [gramF, monoBasis, momF, one_mul]

/-- **DLMF 3.11.27–3.11.29**: `pₙ = ∑ aₖxᵏ` minimizes `S = ∑_j (f(x_j) − pₙ(x_j))²` iff the
normal equations `∑_ℓ X_{k+ℓ} a_ℓ = F_k` hold. -/
theorem dlmf_3_11_29 (x : Fin J → ℝ) (f : ℝ → ℝ) (a : Fin (n + 1) → ℝ) :
    (∀ b, lsSum x (fun _ => 1) f (monoBasis n) a ≤ lsSum x (fun _ => 1) f (monoBasis n) b) ↔
      ∀ k : Fin (n + 1), ∑ l : Fin (n + 1), momX x (k + l) * a l = momF x f k := by
  rw [dlmf_3_11_33 x _ f _ (fun _ => zero_le_one)]
  simp only [gramX_mono, gramF_mono]

/-- The polynomial `∑ₖ aₖxᵏ`. -/
noncomputable def lsPoly (a : Fin (n + 1) → ℝ) : Polynomial ℝ :=
  ∑ k : Fin (n + 1), Polynomial.C (a k) * Polynomial.X ^ (k : ℕ)

theorem lsPoly_eval (a : Fin (n + 1) → ℝ) (t : ℝ) :
    (lsPoly a).eval t = lsApprox (monoBasis n) a t := by
  simp [lsPoly, Polynomial.eval_finsetSum, lsApprox, monoBasis]

theorem lsPoly_degree (a : Fin (n + 1) → ℝ) : (lsPoly a).degree < (n + 1 : ℕ) :=
  Polynomial.degree_sum_fin_lt a

/-- `J ≥ n + 1` distinct points: the monomials are independent on them. -/
theorem linIndepOn_mono {x : Fin J → ℝ} (hx : Function.Injective x) (hJ : n + 1 ≤ J) :
    LinIndepOn x (monoBasis n) := by
  intro c hc
  have hP : lsPoly c = 0 := by
    refine Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero (s := Finset.univ)
      (fun i _ j _ h => hx h) ((lsPoly_degree c).trans_le ?_) fun j _ => ?_
    · simp; exact_mod_cast hJ
    · rw [lsPoly_eval]; exact hc j
  funext k
  have := congrArg (fun p => Polynomial.coeff p k) hP
  simpa [lsPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Fin.val_inj]
    using this

/-- **DLMF §3.11(v)**: "The matrix is symmetric and positive definite" (`J ≥ n + 1` distinct
points). -/
theorem dlmf_3_11_29_posDef {x : Fin J → ℝ} (hx : Function.Injective x) (hJ : n + 1 ≤ J) :
    (Matrix.of fun k l : Fin (n + 1) => momX x (k + l)).PosDef := by
  have := gramX_posDef (w := fun _ => 1) (fun _ => one_pos) (linIndepOn_mono hx hJ)
  simpa [gramX_mono] using this

/-- **DLMF §3.11(v)**: for `J ≥ n + 1` distinct points the least squares polynomial is unique. -/
theorem dlmf_3_11_v_poly_unique {x : Fin J → ℝ} (hx : Function.Injective x) (hJ : n + 1 ≤ J)
    (f : ℝ → ℝ) : ∃! a : Fin (n + 1) → ℝ,
      ∀ b, lsSum x (fun _ => 1) f (monoBasis n) a ≤ lsSum x (fun _ => 1) f (monoBasis n) b :=
  dlmf_3_11_v_unique f (fun _ => one_pos) (linIndepOn_mono hx hJ)

/-- **DLMF §3.11(v)**: "If `J = n + 1`, then `pₙ(x)` is the Lagrange interpolation polynomial for
the set `x₁, …, x_J` (§3.3(i))". -/
theorem dlmf_3_11_v_lagrange {x : Fin (n + 1) → ℝ} (hx : Function.Injective x) (f : ℝ → ℝ)
    {a : Fin (n + 1) → ℝ}
    (ha : ∀ b, lsSum x (fun _ => 1) f (monoBasis n) a ≤ lsSum x (fun _ => 1) f (monoBasis n) b) :
    lsPoly a = Lagrange.interpolate Finset.univ x (fun j => f (x j)) := by
  have hinj : Set.InjOn x (Finset.univ : Finset (Fin (n + 1))) := fun i _ j _ h => hx h
  set L := Lagrange.interpolate Finset.univ x (fun j => f (x j))
  have hLdeg : L.degree < (n + 1 : ℕ) := by
    simpa [L] using Lagrange.degree_interpolate_lt (r := fun j => f (x j)) hinj
  have hL : lsPoly (n := n) (fun k => L.coeff k) = L := by
    ext i
    simp only [lsPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    by_cases hi : i < n + 1
    · rw [Finset.sum_eq_single ⟨i, hi⟩ (fun b _ hb => by
        rw [ite_eq_right_iff]; intro h; exact absurd (Fin.ext h.symm) hb) (by simp)]
      simp
    · rw [Finset.sum_eq_zero fun b _ => by
        rw [ite_eq_right_iff]; intro h; exact absurd (h ▸ b.isLt) hi]
      exact (Polynomial.coeff_eq_zero_of_degree_lt (hLdeg.trans_le (by
        exact_mod_cast not_lt.mp hi))).symm
  have h0 : lsSum x (fun _ => 1) f (monoBasis n) (fun k => L.coeff k) = 0 := by
    refine sum_eq_zero fun j _ => ?_
    rw [← lsPoly_eval, hL, Lagrange.eval_interpolate_at_node _ hinj (mem_univ j)]
    simp
  have hle := ha (fun k => L.coeff k)
  rw [h0] at hle
  have hall := (sum_eq_zero_iff_of_nonneg fun j _ => by positivity).mp
    (le_antisymm hle (sum_nonneg fun j _ => by positivity))
  refine Lagrange.eq_interpolate_of_eval_eq _ hinj (by simpa using lsPoly_degree a)
    fun j _ => ?_
  have := hall j (mem_univ j)
  rw [one_mul, sq_eq_zero_iff, sub_eq_zero] at this
  rw [lsPoly_eval, ← this]

end Azurite.DLMF
