/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section9Shanks
import Azurite.DLMF.Chapter1.Section14TableLaplace
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.FieldTheory.RatFunc.Basic

/-!
# DLMF §3.11(iv): Padé approximations

Formalizations of <https://dlmf.nist.gov/3.11.iv>, over any field `K`; `f` is a formal power
series (3.11.20) and the approximants live in `RatFunc K`.

* 3.11.21–3.11.22 `IsPadeForm p q f N D` (`deg N ≤ p`, `deg D ≤ q`, `D ≠ 0`,
  `N − fD = O(z^{p+q+1})`); 3.11.23 `dlmf_3_11_23` (the linear equations for the coefficients,
  `c_j = 0` for `j < 0`); "if `b₀ ≠ 0`, then the Maclaurin expansion of (3.11.21) agrees with
  (3.11.20) up to, and including, the term in `z^{p+q}`" (`dlmf_3_11_iv_maclaurin`).
* `[p/q]_f` (`pade`): a Padé form always exists (`exists_isPadeForm`, a nonzero solution of the
  `q` homogeneous equations in `q + 1` unknowns) and the rational function `N/D` does not depend on
  the form (`isPadeForm_cross`), so `[p/q]_f` is well defined (`pade_eq`).
* 3.11.24 the Padé table `padeTable`; its first column is the Taylor polynomials
  (`pade_zero_right`), and `[p/q]_f = 1/[q/p]_{1/f}` (`pade_inv`) gives its first row
  (`pade_zero_left`).
* Shanks: `[(n + k)/k]_f = t_{n,2k} = ε_{2k}^{(n)}` for the partial sums `sₙ` of `f`
  (`pade_eq_shanks`, `pade_eq_wynnEps`) — the remark after 3.9.11 and "For the recursive
  computation of `[n+k/k]_f` by Wynn's epsilon algorithm, see (3.9.11)".
* 3.11.25 Wynn's cross rule `(N − C)⁻¹ + (S − C)⁻¹ = (W − C)⁻¹ + (E − C)⁻¹`: in the lower part
  of the table (`dlmf_3_11_25`), on the first column with `[n/−1] = ∞` (`dlmf_3_11_25_border`), and
  in the upper part via `[p/q]_f = 1/[q/p]_{1/f}` (`dlmf_3_11_25_upper`; the first row with
  `[−1/n] = 0`, `dlmf_3_11_25_upper_border`). The hypotheses are the nonvanishing Hankel
  determinants of §3.9 (a normal table). Proof: the rhombus rule of the ε-algorithm
  (`wynn_cross_rule`), then the identification with Padé approximants.
* 3.11.26 `dlmf_3_11_26` (the Laplace transform of §1.14); "approximate `F` by a rational function
  `R` (vanishing at infinity) and then approximate `f` by `r = ℒ⁻¹R`": `dlmf_3_11_iv_laplace`
  inverts every `R = ∑ Aᵢ/(s − aᵢ)^{mᵢ+1}`.

Baker and Graves-Morris (1996), Brezinski (1980), Lorentzen and Waadeland (1992), Luke (1969b),
and the connections with continued fractions and Gaussian quadrature are not formalized.
-/

open Polynomial PowerSeries

namespace Azurite.DLMF

variable {K : Type*} [Field K]

/-! ### Padé forms -/

/-- **DLMF 3.11.21–3.11.22**: `N/D` is a Padé form of type `[p/q]` at zero of `f`:
`N_{p,q}(z) − f(z) D_{p,q}(z) = O(z^{p+q+1})`. -/
def IsPadeForm (p q : ℕ) (f : K⟦X⟧) (N D : K[X]) : Prop :=
  N.natDegree ≤ p ∧ D.natDegree ≤ q ∧ D ≠ 0 ∧
    ∀ k ≤ p + q, PowerSeries.coeff k ((N : K⟦X⟧) - f * (D : K⟦X⟧)) = 0

theorem coeff_mul_poly (f : K⟦X⟧) (D : K[X]) (k : ℕ) :
    PowerSeries.coeff k (f * (D : K⟦X⟧)) =
      ∑ j ∈ Finset.range (k + 1), PowerSeries.coeff (k - j) f * D.coeff j := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i f * PowerSeries.coeff j (D : K⟦X⟧))]
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  have := Finset.mem_range.mp hj
  rw [Polynomial.coeff_coe, show k + 1 - 1 - j = k - j by omega, show k - (k - j) = j by omega]

/-- **DLMF 3.11.23**: the Padé conditions are the linear equations
`a_k = c_k b₀ + c_{k−1} b₁ + ⋯` (`k ≤ p`) and `0 = c_k b₀ + ⋯ + c_{k−q} b_q` (`p < k ≤ p + q`),
with `c_j = 0` for `j < 0`. -/
theorem dlmf_3_11_23 {p q : ℕ} {f : K⟦X⟧} {N D : K[X]} :
    IsPadeForm p q f N D ↔ N.natDegree ≤ p ∧ D.natDegree ≤ q ∧ D ≠ 0 ∧
      (∀ k ≤ p, N.coeff k =
        ∑ j ∈ Finset.range (k + 1), PowerSeries.coeff (k - j) f * D.coeff j) ∧
      ∀ k, p < k → k ≤ p + q →
        0 = ∑ j ∈ Finset.range (k + 1), PowerSeries.coeff (k - j) f * D.coeff j := by
  constructor
  · rintro ⟨hN, hD, hD0, h⟩
    refine ⟨hN, hD, hD0, fun k hk => ?_, fun k hk1 hk2 => ?_⟩
    · have := h k (by omega)
      rw [map_sub, Polynomial.coeff_coe, coeff_mul_poly, sub_eq_zero] at this
      exact this
    · have := h k hk2
      rw [map_sub, Polynomial.coeff_coe, coeff_mul_poly,
        coeff_eq_zero_of_natDegree_lt (by omega), zero_sub, neg_eq_zero] at this
      exact this.symm
  · rintro ⟨hN, hD, hD0, h1, h2⟩
    refine ⟨hN, hD, hD0, fun k hk => ?_⟩
    rw [map_sub, Polynomial.coeff_coe, coeff_mul_poly]
    by_cases hkp : k ≤ p
    · rw [h1 k hkp, sub_self]
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), ← h2 k (by omega) hk, sub_zero]

theorem X_pow_dvd_of_isPadeForm {p q : ℕ} {f : K⟦X⟧} {N D : K[X]} (h : IsPadeForm p q f N D) :
    (PowerSeries.X : K⟦X⟧) ^ (p + q + 1) ∣ (N : K⟦X⟧) - f * (D : K⟦X⟧) :=
  PowerSeries.X_pow_dvd_iff.mpr fun m hm => h.2.2.2 m (by omega)

/-- **DLMF §3.11(iv)**: "if `b₀ ≠ 0`, then the Maclaurin expansion of (3.11.21) agrees with
(3.11.20) up to, and including, the term in `z^{p+q}`". -/
theorem dlmf_3_11_iv_maclaurin {p q : ℕ} {f : K⟦X⟧} {N D : K[X]} (h : IsPadeForm p q f N D)
    (hb : D.coeff 0 ≠ 0) : ∀ k ≤ p + q,
      PowerSeries.coeff k ((N : K⟦X⟧) * (D : K⟦X⟧)⁻¹) = PowerSeries.coeff k f := by
  have hc : PowerSeries.constantCoeff (D : K⟦X⟧) ≠ 0 := by
    rwa [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe]
  have e : (N : K⟦X⟧) * (D : K⟦X⟧)⁻¹ - f = ((N : K⟦X⟧) - f * D) * (D : K⟦X⟧)⁻¹ := by
    rw [sub_mul, mul_assoc, PowerSeries.mul_inv_cancel _ hc, mul_one]
  have hdvd : (PowerSeries.X : K⟦X⟧) ^ (p + q + 1) ∣ (N : K⟦X⟧) * (D : K⟦X⟧)⁻¹ - f := by
    rw [e]; exact (X_pow_dvd_of_isPadeForm h).mul_right _
  intro k hk
  have := PowerSeries.X_pow_dvd_iff.mp hdvd k (by omega)
  rwa [map_sub, sub_eq_zero] at this

/-- Two Padé forms of the same type give the same rational function: `N₁D₂ = N₂D₁`. -/
theorem isPadeForm_cross {p q : ℕ} {f : K⟦X⟧} {N₁ D₁ N₂ D₂ : K[X]}
    (h₁ : IsPadeForm p q f N₁ D₁) (h₂ : IsPadeForm p q f N₂ D₂) : N₁ * D₂ = N₂ * D₁ := by
  have hdeg : (N₁ * D₂ - N₂ * D₁).natDegree ≤ p + q :=
    (natDegree_sub_le _ _).trans (max_le (natDegree_mul_le.trans
      (by have := h₁.1; have := h₂.2.1; omega))
      (natDegree_mul_le.trans (by have := h₂.1; have := h₁.2.1; omega)))
  have hdvd : (PowerSeries.X : K⟦X⟧) ^ (p + q + 1) ∣ ((N₁ * D₂ - N₂ * D₁ : K[X]) : K⟦X⟧) := by
    have e : ((N₁ * D₂ - N₂ * D₁ : K[X]) : K⟦X⟧) =
        ((N₁ : K⟦X⟧) - f * D₁) * D₂ - ((N₂ : K⟦X⟧) - f * D₂) * D₁ := by
      push_cast; ring
    rw [e]
    exact dvd_sub ((X_pow_dvd_of_isPadeForm h₁).mul_right _)
      ((X_pow_dvd_of_isPadeForm h₂).mul_right _)
  rw [← sub_eq_zero]
  ext m
  rw [coeff_zero]
  by_cases hm : m ≤ p + q
  · rw [← Polynomial.coeff_coe]; exact PowerSeries.X_pow_dvd_iff.mp hdvd m (by omega)
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

/-- The polynomial `∑ b_j X^j` of a coefficient vector. -/
noncomputable def vecPoly {q : ℕ} (b : Fin (q + 1) → K) : K[X] :=
  ∑ j : Fin (q + 1), Polynomial.C (b j) * Polynomial.X ^ (j : ℕ)

theorem vecPoly_coeff {q : ℕ} (b : Fin (q + 1) → K) (j : Fin (q + 1)) :
    (vecPoly b).coeff j = b j := by
  simp [vecPoly, Polynomial.finsetSum_coeff, Fin.val_inj]

theorem vecPoly_natDegree {q : ℕ} (b : Fin (q + 1) → K) : (vecPoly b).natDegree ≤ q := by
  refine natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [natDegree_X_pow]; exact Nat.lt_succ_iff.mp j.isLt

theorem natDegree_trunc_le (n : ℕ) (φ : K⟦X⟧) : (PowerSeries.trunc (n + 1) φ).natDegree ≤ n := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro m hm
  rw [PowerSeries.coeff_trunc, ite_eq_right (by
    have : n < m := by exact_mod_cast hm
    omega)]

/-- A Padé form of every type exists. -/
theorem exists_isPadeForm (p q : ℕ) (f : K⟦X⟧) : ∃ N D : K[X], IsPadeForm p q f N D := by
  -- the `q` homogeneous equations for `b₀, …, b_q`
  let L : (Fin (q + 1) → K) →ₗ[K] (Fin q → K) :=
    { toFun := fun b i => PowerSeries.coeff (p + 1 + i) (f * ((vecPoly b : K[X]) : K⟦X⟧))
      map_add' := fun b b' => by
        funext i
        simp [vecPoly, Finset.sum_add_distrib, add_mul, mul_add]
      map_smul' := fun r b => by
        funext i
        simp only [vecPoly, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Pi.smul_apply]
        rw [show (∑ j : Fin (q + 1), Polynomial.C (r * b j) * Polynomial.X ^ (j : ℕ) : K[X]) =
          Polynomial.C r * ∑ j : Fin (q + 1), Polynomial.C (b j) * Polynomial.X ^ (j : ℕ) by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by rw [C_mul]; ring]
        rw [Polynomial.coe_mul, Polynomial.coe_C, mul_left_comm, ← PowerSeries.smul_eq_C_mul,
          map_smul, smul_eq_mul] }
  have hker : LinearMap.ker L ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simp)
  obtain ⟨b, hbL, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  set D := vecPoly b
  have hD0 : D ≠ 0 := by
    intro h0
    apply hb0
    funext j
    rw [← vecPoly_coeff b j, show vecPoly b = D from rfl, h0, coeff_zero]
    rfl
  refine ⟨PowerSeries.trunc (p + 1) (f * (D : K⟦X⟧)), D, natDegree_trunc_le p _,
    vecPoly_natDegree b, hD0, fun k hk => ?_⟩
  rw [map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  split_ifs with hkp
  · exact sub_self _
  · have := congrFun (LinearMap.mem_ker.mp hbL) ⟨k - (p + 1), by omega⟩
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at this
    rw [show p + 1 + (k - (p + 1)) = k by omega] at this
    rw [this, sub_zero]

/-! ### The approximant `[p/q]_f` -/

/-- **DLMF §3.11(iv)**: the Padé approximant `[p/q]_f` as a rational function. -/
noncomputable def pade (p q : ℕ) (f : K⟦X⟧) : RatFunc K :=
  algebraMap K[X] (RatFunc K) (exists_isPadeForm p q f).choose /
    algebraMap K[X] (RatFunc K) (exists_isPadeForm p q f).choose_spec.choose

/-- `[p/q]_f = N/D` for every Padé form `N/D`. -/
theorem pade_eq {p q : ℕ} {f : K⟦X⟧} {N D : K[X]} (h : IsPadeForm p q f N D) :
    pade p q f = algebraMap K[X] (RatFunc K) N / algebraMap K[X] (RatFunc K) D := by
  have h0 := (exists_isPadeForm p q f).choose_spec.choose_spec
  have hc := isPadeForm_cross h0 h
  have hinj : Function.Injective (algebraMap K[X] (RatFunc K)) :=
    IsFractionRing.injective K[X] (RatFunc K)
  rw [pade, div_eq_div_iff (fun h' => h0.2.2.1 (hinj (by rw [h', map_zero])))
    (fun h' => h.2.2.1 (hinj (by rw [h', map_zero]))), ← map_mul, ← map_mul, hc]

/-- **DLMF 3.11.24**: the Padé table `([p/q]_f)_{p,q ≥ 0}` (rows `p`, columns `q`). -/
noncomputable def padeTable (f : K⟦X⟧) : ℕ → ℕ → RatFunc K := fun p q => pade p q f

theorem dlmf_3_11_24 (f : K⟦X⟧) (p q : ℕ) : padeTable f p q = pade p q f := rfl

/-- The partial sums `sₙ = c₀ + ⋯ + cₙzⁿ` as rational functions. -/
noncomputable def padePsum (f : K⟦X⟧) (n : ℕ) : RatFunc K :=
  algebraMap K[X] (RatFunc K) (PowerSeries.trunc (n + 1) f)

/-- The first column: `[n/0]_f = sₙ`. -/
theorem pade_zero_right (n : ℕ) (f : K⟦X⟧) : pade n 0 f = padePsum f n := by
  have h : IsPadeForm n 0 f (PowerSeries.trunc (n + 1) f) 1 := by
    refine ⟨natDegree_trunc_le n f, by simp, one_ne_zero, fun k hk => ?_⟩
    rw [Polynomial.coe_one, mul_one, map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc,
      ite_eq_left (by omega), sub_self]
  rw [pade_eq h, map_one, div_one, padePsum]

/-- Duality: if `c₀ ≠ 0`, then `D/N` is a Padé form of type `[q/p]` of `1/f`. -/
theorem isPadeForm_inv {p q : ℕ} {f : K⟦X⟧} {N D : K[X]} (h : IsPadeForm p q f N D)
    (hf : PowerSeries.constantCoeff f ≠ 0) : IsPadeForm q p f⁻¹ D N := by
  have hff : f * f⁻¹ = 1 := PowerSeries.mul_inv_cancel f hf
  have e : (D : K⟦X⟧) - f⁻¹ * N = -f⁻¹ * ((N : K⟦X⟧) - f * D) := by
    linear_combination (-(D : K⟦X⟧)) * hff
  have hdvd : (PowerSeries.X : K⟦X⟧) ^ (q + p + 1) ∣ (D : K⟦X⟧) - f⁻¹ * N := by
    rw [e, show q + p + 1 = p + q + 1 by ring]
    exact (X_pow_dvd_of_isPadeForm h).mul_left _
  have hN0 : N ≠ 0 := by
    intro hN
    have h2 : (PowerSeries.X : K⟦X⟧) ^ (p + q + 1) ∣ (D : K⟦X⟧) := by
      have := (X_pow_dvd_of_isPadeForm h).mul_left (-f⁻¹)
      have e2 : -(-f⁻¹ * (f * (D : K⟦X⟧))) = D := by
        rw [neg_mul, neg_neg, ← mul_assoc, mul_comm f⁻¹ f, hff, one_mul]
      rw [hN, Polynomial.coe_zero, zero_sub, mul_neg, e2] at this
      exact this
    apply h.2.2.1
    ext m
    rw [coeff_zero]
    by_cases hm : m ≤ q
    · rw [← Polynomial.coeff_coe]; exact PowerSeries.X_pow_dvd_iff.mp h2 m (by omega)
    · exact coeff_eq_zero_of_natDegree_lt (by have := h.2.1; omega)
  exact ⟨h.2.1, h.1, hN0, fun k hk => PowerSeries.X_pow_dvd_iff.mp hdvd k (by omega)⟩

/-- `[p/q]_f = 1/[q/p]_{1/f}` (`c₀ ≠ 0`). -/
theorem pade_inv (p q : ℕ) {f : K⟦X⟧} (hf : PowerSeries.constantCoeff f ≠ 0) :
    pade q p f⁻¹ = (pade p q f)⁻¹ := by
  obtain ⟨N, D, h⟩ := exists_isPadeForm p q f
  rw [pade_eq h, pade_eq (isPadeForm_inv h hf), inv_div]

/-- The first row: `[0/n]_f = 1/(Taylor polynomial of 1/f)` (`c₀ ≠ 0`). -/
theorem pade_zero_left (n : ℕ) {f : K⟦X⟧} (hf : PowerSeries.constantCoeff f ≠ 0) :
    pade 0 n f = (padePsum f⁻¹ n)⁻¹ := by
  have hf' : PowerSeries.constantCoeff f⁻¹ ≠ 0 := by
    rw [PowerSeries.constantCoeff_inv]; exact inv_ne_zero hf
  have hinv : f⁻¹⁻¹ = f :=
    ((PowerSeries.eq_inv_iff_mul_eq_one hf').mpr (PowerSeries.mul_inv_cancel f hf)).symm
  rw [← pade_zero_right, ← pade_inv n 0 hf', hinv]

/-! ### Shanks: `[(n + k)/k]_f = t_{n,2k}` -/

theorem fwdDiff_psum (f : K⟦X⟧) (m : ℕ) :
    fwdDiff 1 (padePsum f) m = algebraMap K[X] (RatFunc K)
      (Polynomial.monomial (m + 1) (PowerSeries.coeff (m + 1) f)) := by
  simp only [fwdDiff, padePsum]
  rw [← map_sub, show m + 1 + 1 = (m + 1).succ from rfl, PowerSeries.trunc_succ,
    add_sub_cancel_left]

/-- The determinant of a bordered matrix is affine in the last row. -/
theorem det_bordMat_sub {F : Type*} [Field F] (m : ℕ) (g : ℕ → ℕ → F) (r : ℕ → F) (e : F) :
    (bordMat m g fun j => r j - e).det =
      (bordMat m g r).det - e * (bordMat m g fun _ => 1).det := by
  have hupd : ∀ r' : ℕ → F, bordMat m g r' =
      (bordMat m g fun _ => 1).updateRow (Fin.last m) fun j => r' j := fun r' => by
    ext i j
    by_cases hi : i = Fin.last m
    · subst hi; simp [bordMat]
    · have : (i : ℕ) < m := by
        have := i.isLt; have : (i : ℕ) ≠ m := fun h => hi (Fin.ext h); omega
      simp [bordMat, Matrix.updateRow_ne hi, this]
  rw [hupd, hupd r, show (fun j : Fin (m + 1) => r j - e) =
    (fun j : Fin (m + 1) => r j) + (-e) • fun _ => 1 by funext j; simp; ring,
    Matrix.det_updateRow_add, Matrix.det_updateRow_smul]
  have : ((bordMat m g fun _ => 1).updateRow (Fin.last m) fun _ => (1 : F)) =
      bordMat m g fun _ => 1 := (hupd fun _ => 1).symm
  rw [this]
  ring

/-- **Shanks**: `[(n + k)/k]_f = t_{n,2k}` for the partial sums `sₙ` of `f`, provided
`H_k(Δ²sₙ) ≠ 0` (the remark after DLMF 3.9.11). -/
theorem pade_eq_shanks (n k : ℕ) (f : K⟦X⟧)
    (hH : hankel (fwdDiff 1 (fwdDiff 1 (padePsum f))) k n ≠ 0) :
    pade (n + k) k f = shanks k (padePsum f) n := by
  obtain ⟨N, D, h⟩ := exists_isPadeForm (n + k) k f
  set φ := algebraMap K[X] (RatFunc K)
  have hinj : Function.Injective φ := IsFractionRing.injective K[X] (RatFunc K)
  have hφD : φ D ≠ 0 := fun h0 => h.2.2.1 (hinj (by rw [h0, map_zero]))
  set e := φ N / φ D
  rw [pade_eq h]
  obtain ⟨hN, hD, -, h1, h2⟩ := dlmf_3_11_23.mp h
  set c : ℕ → K := fun t => PowerSeries.coeff t f
  -- `∑_{j ≤ t} c_{t−j} b_j = ∑_{l ≤ k} [l ≤ t] b_l c_{t−l}`
  have hconv : ∀ t, ∑ j ∈ Finset.range (t + 1), c (t - j) * D.coeff j =
      ∑ l ∈ Finset.range (k + 1), if l ≤ t then D.coeff l * c (t - l) else 0 := by
    intro t
    rw [← Finset.sum_filter]
    refine (Finset.sum_subset_zero_on_sdiff (fun l hl => ?_) (fun l hl => ?_) (fun l hl => ?_)).symm
    · simp only [Finset.mem_filter, Finset.mem_range] at hl ⊢
      omega
    · simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range] at hl
      have : k < l := by omega
      rw [coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
    · simp only [Finset.mem_filter, Finset.mem_range] at hl
      ring
  -- (A) `∑_l b_l X^l = D`
  have hA : ∑ l ∈ Finset.range (k + 1), Polynomial.C (D.coeff l) * Polynomial.X ^ l = D :=
    (as_sum_range_C_mul_X_pow' D (by omega : D.natDegree < k + 1)).symm
  -- (B) `∑_l b_l X^l s_{n+k−l} = N`
  have hB : ∑ l ∈ Finset.range (k + 1), Polynomial.C (D.coeff l) * Polynomial.X ^ l *
      PowerSeries.trunc (n + k - l + 1) f = N := by
    ext t
    rw [Polynomial.finsetSum_coeff]
    have hterm : ∀ l ∈ Finset.range (k + 1), (Polynomial.C (D.coeff l) * Polynomial.X ^ l *
        PowerSeries.trunc (n + k - l + 1) f).coeff t =
        if t ≤ n + k then (if l ≤ t then D.coeff l * c (t - l) else 0) else 0 := by
      intro l hl
      have hl' := Finset.mem_range.mp hl
      rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul', PowerSeries.coeff_trunc]
      split_ifs <;> first | rfl | (exfalso; omega) | simp
    rw [Finset.sum_congr rfl hterm]
    by_cases ht : t ≤ n + k
    · simp only [ht, ↓reduceIte]
      rw [← hconv, h1 t ht]
    · simp only [ht, ↓reduceIte, Finset.sum_const_zero]
      exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm
  -- (C) `∑_l b_l X^l Δs_{n+k−l+i} = 0` for `i < k`
  have hC : ∀ i < k, ∑ l ∈ Finset.range (k + 1), Polynomial.C (D.coeff l) * Polynomial.X ^ l *
      Polynomial.monomial (n + k - l + i + 1) (c (n + k - l + i + 1)) = 0 := by
    intro i hi
    have hz := h2 (n + k + i + 1) (by omega) (by omega)
    rw [hconv] at hz
    have hterm : ∀ l ∈ Finset.range (k + 1), Polynomial.C (D.coeff l) * Polynomial.X ^ l *
        Polynomial.monomial (n + k - l + i + 1) (c (n + k - l + i + 1)) =
        Polynomial.monomial (n + k + i + 1)
          (if l ≤ n + k + i + 1 then D.coeff l * c (n + k + i + 1 - l) else 0) := by
      intro l hl
      have hl' := Finset.mem_range.mp hl
      rw [ite_eq_left (by omega), show n + k + i + 1 - l = n + k - l + i + 1 by omega, mul_assoc,
        Polynomial.X_pow_mul_monomial, show n + k - l + i + 1 + l = n + k + i + 1 by omega,
        Polynomial.C_mul_monomial]
    rw [Finset.sum_congr rfl hterm, ← map_sum, ← hz, map_zero]
  -- the vector `v_j = b_{k−j} X^{k−j}`
  set v : Fin (k + 1) → RatFunc K :=
    fun j => φ (Polynomial.C (D.coeff (k - j)) * Polynomial.X ^ (k - (j : ℕ)))
  have hrefl : ∀ G : ℕ → RatFunc K, ∑ j : Fin (k + 1), G (k - j) =
      ∑ l ∈ Finset.range (k + 1), G l := fun G => by
    rw [Fin.sum_univ_eq_sum_range (fun j => G (k - j)), ← Finset.sum_range_reflect G (k + 1)]
    exact Finset.sum_congr rfl fun j hj => by
      rw [show k + 1 - 1 - j = k - j by omega]
  have hvsum : ∑ j, v j = φ D := by
    rw [hrefl (fun l => φ (Polynomial.C (D.coeff l) * Polynomial.X ^ l)), ← map_sum, hA]
  have hB' : ∑ l ∈ Finset.range (k + 1), φ (Polynomial.C (D.coeff l) * Polynomial.X ^ l *
      PowerSeries.trunc (n + k - l + 1) f) = φ N := by rw [← map_sum, hB]
  have hC' : ∀ i < k, ∑ l ∈ Finset.range (k + 1), φ (Polynomial.C (D.coeff l) * Polynomial.X ^ l *
      Polynomial.monomial (n + k - l + i + 1) (c (n + k - l + i + 1))) = 0 := fun i hi => by
    rw [← map_sum, hC i hi, map_zero]
  have hvN : ∑ j : Fin (k + 1), padePsum f (n + j) * v j = φ N := by
    have := hrefl (fun l => φ (Polynomial.C (D.coeff l) * Polynomial.X ^ l *
      PowerSeries.trunc (n + k - l + 1) f))
    rw [hB'] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hj := j.isLt
    simp only [v, padePsum, map_mul]
    rw [show n + k - (k - (j : ℕ)) + 1 = n + j + 1 by omega]
    ring
  have hvC : ∀ i < k, ∑ j : Fin (k + 1), fwdDiff 1 (padePsum f) (n + i + j) * v j = 0 := by
    intro i hi
    have := hrefl (fun l => φ (Polynomial.C (D.coeff l) * Polynomial.X ^ l *
      Polynomial.monomial (n + k - l + i + 1) (c (n + k - l + i + 1))))
    rw [hC' i hi] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hj := j.isLt
    simp only [v, fwdDiff_psum, map_mul]
    rw [show n + k - (k - (j : ℕ)) + i + 1 = n + i + j + 1 by omega]
    ring
  -- Cramer: the matrix with last row `s_{n+k+j} − e` is singular
  set g : ℕ → ℕ → RatFunc K := fun i j => fwdDiff 1 (padePsum f) (n + i + j)
  have hsing : (bordMat k g fun j => padePsum f (n + k + j) - e).det = 0 := by
    refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, fun hv => ?_, ?_⟩
    · have : ∑ j, v j = 0 := by rw [hv]; simp
      exact hφD (hvsum ▸ this)
    · funext i
      simp only [Matrix.mulVec, dotProduct, bordMat, Matrix.of_apply, Pi.zero_apply]
      by_cases hi : (i : ℕ) < k
      · simp only [hi, ↓reduceIte, g]
        exact hvC i hi
      · simp only [hi, ↓reduceIte]
        -- `s_{n+k+j} = s_{n+j} + ∑_{i<k} Δs_{n+i+j}`
        have htel : ∀ j : ℕ, padePsum f (n + k + j) =
            padePsum f (n + j) + ∑ i ∈ Finset.range k, fwdDiff 1 (padePsum f) (n + i + j) := by
          intro j
          rw [show ∑ i ∈ Finset.range k, fwdDiff 1 (padePsum f) (n + i + j) =
            ∑ i ∈ Finset.range k, (padePsum f (n + j + (i + 1)) - padePsum f (n + j + i)) from
            Finset.sum_congr rfl fun i _ => by simp only [fwdDiff]; ring_nf,
            Finset.sum_range_sub (fun i => padePsum f (n + j + i))]
          ring_nf
        simp only [sub_mul, Finset.sum_sub_distrib, htel, add_mul, Finset.sum_add_distrib,
          Finset.sum_mul]
        rw [Finset.sum_comm, Finset.sum_eq_zero fun i hi' => hvC i (Finset.mem_range.mp hi'),
          hvN, ← Finset.mul_sum, hvsum, add_zero]
        simp only [e]
        field_simp
        ring
  rw [det_bordMat_sub, sub_eq_zero] at hsing
  -- the bordered determinants are `±` Hankel determinants
  have hS := det_rowDiff (padePsum f) k n
  have h1' := det_onesRow k g
  have hΔ : (Matrix.of fun i j : Fin k => g i (j + 1) - g i j) =
      Matrix.of fun i j : Fin k => fwdDiff 1 (fwdDiff 1 (padePsum f)) (n + i + j) := by
    ext i j
    simp only [g, Matrix.of_apply, fwdDiff]
    ring_nf
  rw [hΔ, ← hankel] at h1'
  simp only [g] at hsing h1'
  rw [hS, h1'] at hsing
  have hsign : ((-1 : RatFunc K) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [shanks, eq_div_iff hH]
  have := hsing
  rw [show e * ((-1) ^ k * hankel (fwdDiff 1 (fwdDiff 1 (padePsum f))) k n) =
    (-1) ^ k * (e * hankel (fwdDiff 1 (fwdDiff 1 (padePsum f))) k n) by ring] at this
  exact (mul_left_cancel₀ hsign this).symm

/-- **DLMF 3.9.11 with §3.11(iv)**: `ε_{2k}^{(n)} = [(n + k)/k]_f` (Wynn's epsilon algorithm
computes the Padé table), under the Hankel conditions of `dlmf_3_9_11`. -/
theorem pade_eq_wynnEps (f : K⟦X⟧) (K₀ : ℕ)
    (hD : ∀ k ≤ K₀, ∀ n, hankel (fwdDiff 1 (fwdDiff 1 (padePsum f))) k n ≠ 0)
    (hQ : ∀ k ≤ K₀, ∀ n, hankel (fwdDiff 1 (padePsum f)) k n ≠ 0) :
    ∀ k ≤ K₀, ∀ n, wynnEps (padePsum f) (2 * k + 1) n = pade (n + k) k f := fun k hk n => by
  rw [((dlmf_3_9_11 (padePsum f) K₀ hD hQ) k hk).1 n, pade_eq_shanks n k f (hD k hk n)]

/-! ### Wynn's cross rule -/

/-- The cross rule for the even entries of the ε-table, from the rhombus rule: with
`C = ε_{2k+2}^{(n+1)}`, `N = ε_{2k+2}^{(n)}`, `S = ε_{2k+2}^{(n+2)}`, `W = ε_{2k}^{(n+2)}`,
`E = ε_{2k+4}^{(n)}`. -/
theorem wynn_cross_rule {F : Type*} [Field F] (s : ℕ → F) (k n : ℕ) :
    (wynnEps s (2 * k + 3) n - wynnEps s (2 * k + 3) (n + 1))⁻¹ +
      (wynnEps s (2 * k + 3) (n + 2) - wynnEps s (2 * k + 3) (n + 1))⁻¹ =
    (wynnEps s (2 * k + 1) (n + 2) - wynnEps s (2 * k + 3) (n + 1))⁻¹ +
      (wynnEps s (2 * k + 5) n - wynnEps s (2 * k + 3) (n + 1))⁻¹ := by
  set C := wynnEps s (2 * k + 3) (n + 1)
  set N := wynnEps s (2 * k + 3) n
  set S := wynnEps s (2 * k + 3) (n + 2)
  set a := wynnEps s (2 * k + 4) n
  set b := wynnEps s (2 * k + 4) (n + 1)
  set c := wynnEps s (2 * k + 2) (n + 1)
  set d := wynnEps s (2 * k + 2) (n + 2)
  have ha : a = c + 1 / (C - N) := wynnEps_succ_succ s (2 * k + 2) n
  have hb : b = d + 1 / (S - C) := wynnEps_succ_succ s (2 * k + 2) (n + 1)
  have hE : wynnEps s (2 * k + 5) n = C + 1 / (b - a) := wynnEps_succ_succ s (2 * k + 3) n
  have hC : C = wynnEps s (2 * k + 1) (n + 2) + 1 / (d - c) :=
    wynnEps_succ_succ s (2 * k + 1) (n + 1)
  rw [hE, add_sub_cancel_left, one_div, inv_inv]
  rw [show wynnEps s (2 * k + 1) (n + 2) - C = -(1 / (d - c)) by rw [hC]; ring, inv_neg, one_div,
    inv_inv]
  rw [show N - C = -(C - N) by ring, inv_neg, show (C - N)⁻¹ = a - c by rw [ha]; ring,
    show (S - C)⁻¹ = b - d by rw [hb]; ring]
  ring

/-- The cross rule on the first column of the ε-table (`ε_{−2} = ∞`): with `C = sₙ₊₁`. -/
theorem wynn_cross_rule_border {F : Type*} [Field F] (s : ℕ → F) (n : ℕ) :
    (wynnEps s 1 n - wynnEps s 1 (n + 1))⁻¹ + (wynnEps s 1 (n + 2) - wynnEps s 1 (n + 1))⁻¹ =
      (wynnEps s 3 n - wynnEps s 1 (n + 1))⁻¹ := by
  have ha : wynnEps s 2 n = 0 + 1 / (wynnEps s 1 (n + 1) - wynnEps s 1 n) :=
    wynnEps_succ_succ s 0 n
  have hb : wynnEps s 2 (n + 1) = 0 + 1 / (wynnEps s 1 (n + 2) - wynnEps s 1 (n + 1)) :=
    wynnEps_succ_succ s 0 (n + 1)
  have hE : wynnEps s 3 n = wynnEps s 1 (n + 1) + 1 / (wynnEps s 2 (n + 1) - wynnEps s 2 n) :=
    wynnEps_succ_succ s 1 n
  rw [hE, add_sub_cancel_left, one_div, inv_inv, ha, hb]
  rw [show wynnEps s 1 n - wynnEps s 1 (n + 1) = -(wynnEps s 1 (n + 1) - wynnEps s 1 n) by ring,
    inv_neg]
  simp only [zero_add, one_div]
  ring

/-- **DLMF 3.11.25** (Wynn's cross rule, lower part of the table): for `1 ≤ q < p`, with
`C = [p/q]`, `N = [p−1/q]`, `S = [p+1/q]`, `W = [p/q−1]`, `E = [p/q+1]`,
`(N − C)⁻¹ + (S − C)⁻¹ = (W − C)⁻¹ + (E − C)⁻¹`, provided the Hankel determinants of the partial
sums do not vanish up to order `q + 1` (a normal table). -/
theorem dlmf_3_11_25 (f : K⟦X⟧) {p q : ℕ} (hq : 1 ≤ q) (hpq : q < p)
    (hD : ∀ k ≤ q + 1, ∀ n, hankel (fwdDiff 1 (fwdDiff 1 (padePsum f))) k n ≠ 0)
    (hQ : ∀ k ≤ q + 1, ∀ n, hankel (fwdDiff 1 (padePsum f)) k n ≠ 0) :
    (pade (p - 1) q f - pade p q f)⁻¹ + (pade (p + 1) q f - pade p q f)⁻¹ =
      (pade p (q - 1) f - pade p q f)⁻¹ + (pade p (q + 1) f - pade p q f)⁻¹ := by
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n, p = n + k + 2 := ⟨p - k - 2, by omega⟩
  have hW := pade_eq_wynnEps f (k + 2) hD hQ
  have e1 := hW (k + 1) (by omega) (n + 1)
  have e2 := hW (k + 1) (by omega) n
  have e3 := hW (k + 1) (by omega) (n + 2)
  have e4 := hW k (by omega) (n + 2)
  have e5 := hW (k + 2) le_rfl n
  rw [show 2 * (k + 1) + 1 = 2 * k + 3 by ring] at e1 e2 e3
  rw [show 2 * (k + 2) + 1 = 2 * k + 5 by ring] at e5
  rw [show n + k + 2 - 1 = n + (k + 1) by omega, show n + k + 2 + 1 = n + 2 + (k + 1) by omega,
    show k + 1 - 1 = k by omega, show n + k + 2 = n + 1 + (k + 1) by omega, ← e1, ← e2, ← e3,
    show n + 1 + (k + 1) = n + 2 + k by omega, ← e4, show n + 2 + k = n + (k + 2) by omega,
    show k + 1 + 1 = k + 2 by omega, ← e5]
  exact wynn_cross_rule (padePsum f) k n

/-- **DLMF 3.11.25** on the first column, "initializing the preceding column by `[n/−1] = ∞`":
`(N − C)⁻¹ + (S − C)⁻¹ = (E − C)⁻¹` for `C = [p/0]`, `p ≥ 1`. -/
theorem dlmf_3_11_25_border (f : K⟦X⟧) {p : ℕ} (hp : 1 ≤ p)
    (hD : ∀ k ≤ 1, ∀ n, hankel (fwdDiff 1 (fwdDiff 1 (padePsum f))) k n ≠ 0)
    (hQ : ∀ k ≤ 1, ∀ n, hankel (fwdDiff 1 (padePsum f)) k n ≠ 0) :
    (pade (p - 1) 0 f - pade p 0 f)⁻¹ + (pade (p + 1) 0 f - pade p 0 f)⁻¹ =
      (pade p 1 f - pade p 0 f)⁻¹ := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  have hW := pade_eq_wynnEps f 1 hD hQ
  have e1 := hW 0 (by omega) (n + 1)
  have e2 := hW 0 (by omega) n
  have e3 := hW 0 (by omega) (n + 2)
  have e5 := hW 1 le_rfl n
  simp only [mul_zero, zero_add, add_zero, mul_one] at e1 e2 e3 e5
  rw [show n + 1 - 1 = n by omega, ← e1, ← e2, ← e3, show n + 1 = n + 1 from rfl, ← e5]
  exact wynn_cross_rule_border (padePsum f) n

/-- `(X⁻¹ − C⁻¹)⁻¹ = −C − C²(X − C)⁻¹`. -/
theorem inv_sub_inv_inv {F : Type*} [Field F] {X C : F} (hX : X ≠ 0) (hC : C ≠ 0)
    (hXC : X ≠ C) : (X⁻¹ - C⁻¹)⁻¹ = -C - C ^ 2 * (X - C)⁻¹ := by
  have h1 : X - C ≠ 0 := sub_ne_zero.mpr hXC
  have h2 : C - X ≠ 0 := sub_ne_zero.mpr hXC.symm
  rw [inv_sub_inv hX hC, inv_div]
  field_simp
  ring

/-- **DLMF 3.11.25** in the upper part of the table (`1 ≤ p < q`), from the lower part for `1/f`
(`[p/q]_f = 1/[q/p]_{1/f}`), for a normal table (the entries do not vanish and differ from `C`). -/
theorem dlmf_3_11_25_upper (f : K⟦X⟧) (hf : PowerSeries.constantCoeff f ≠ 0) {p q : ℕ}
    (hp : 1 ≤ p) (hpq : p < q)
    (hD : ∀ k ≤ p + 1, ∀ n, hankel (fwdDiff 1 (fwdDiff 1 (padePsum f⁻¹))) k n ≠ 0)
    (hQ : ∀ k ≤ p + 1, ∀ n, hankel (fwdDiff 1 (padePsum f⁻¹)) k n ≠ 0)
    (hC : pade p q f ≠ 0)
    (hX : ∀ X ∈ [pade (p - 1) q f, pade (p + 1) q f, pade p (q - 1) f, pade p (q + 1) f],
      X ≠ 0 ∧ X ≠ pade p q f) :
    (pade (p - 1) q f - pade p q f)⁻¹ + (pade (p + 1) q f - pade p q f)⁻¹ =
      (pade p (q - 1) f - pade p q f)⁻¹ + (pade p (q + 1) f - pade p q f)⁻¹ := by
  have hg := dlmf_3_11_25 f⁻¹ hp hpq hD hQ
  simp only [pade_inv _ _ hf] at hg
  obtain ⟨hN0, hNC⟩ := hX (pade (p - 1) q f) (by simp)
  obtain ⟨hS0, hSC⟩ := hX (pade (p + 1) q f) (by simp)
  obtain ⟨hW0, hWC⟩ := hX (pade p (q - 1) f) (by simp)
  obtain ⟨hE0, hEC⟩ := hX (pade p (q + 1) f) (by simp)
  rw [inv_sub_inv_inv hW0 hC hWC, inv_sub_inv_inv hE0 hC hEC, inv_sub_inv_inv hN0 hC hNC,
    inv_sub_inv_inv hS0 hC hSC] at hg
  have h2 : pade p q f ^ 2 ≠ 0 := pow_ne_zero 2 hC
  have : pade p q f ^ 2 * ((pade (p - 1) q f - pade p q f)⁻¹ +
      (pade (p + 1) q f - pade p q f)⁻¹) = pade p q f ^ 2 *
      ((pade p (q - 1) f - pade p q f)⁻¹ + (pade p (q + 1) f - pade p q f)⁻¹) := by
    linear_combination hg
  exact mul_left_cancel₀ h2 this

/-- **DLMF 3.11.25** on the first row, "initializing `[−1/n] = 0`": for `C = [0/q]`, `q ≥ 1`,
`(0 − C)⁻¹ + (S − C)⁻¹ = (W − C)⁻¹ + (E − C)⁻¹`. -/
theorem dlmf_3_11_25_upper_border (f : K⟦X⟧) (hf : PowerSeries.constantCoeff f ≠ 0) {q : ℕ}
    (hq : 1 ≤ q)
    (hD : ∀ k ≤ 1, ∀ n, hankel (fwdDiff 1 (fwdDiff 1 (padePsum f⁻¹))) k n ≠ 0)
    (hQ : ∀ k ≤ 1, ∀ n, hankel (fwdDiff 1 (padePsum f⁻¹)) k n ≠ 0)
    (hC : pade 0 q f ≠ 0)
    (hX : ∀ X ∈ [pade 1 q f, pade 0 (q - 1) f, pade 0 (q + 1) f], X ≠ 0 ∧ X ≠ pade 0 q f) :
    (0 - pade 0 q f)⁻¹ + (pade 1 q f - pade 0 q f)⁻¹ =
      (pade 0 (q - 1) f - pade 0 q f)⁻¹ + (pade 0 (q + 1) f - pade 0 q f)⁻¹ := by
  have hg := dlmf_3_11_25_border f⁻¹ hq hD hQ
  simp only [pade_inv _ _ hf] at hg
  obtain ⟨hS0, hSC⟩ := hX (pade 1 q f) (by simp)
  obtain ⟨hW0, hWC⟩ := hX (pade 0 (q - 1) f) (by simp)
  obtain ⟨hE0, hEC⟩ := hX (pade 0 (q + 1) f) (by simp)
  rw [inv_sub_inv_inv hW0 hC hWC, inv_sub_inv_inv hE0 hC hEC, inv_sub_inv_inv hS0 hC hSC] at hg
  have h2 : pade 0 q f ^ 2 ≠ 0 := pow_ne_zero 2 hC
  have : pade 0 q f ^ 2 * ((0 - pade 0 q f)⁻¹ + (pade 1 q f - pade 0 q f)⁻¹) =
      pade 0 q f ^ 2 * ((pade 0 (q - 1) f - pade 0 q f)⁻¹ +
        (pade 0 (q + 1) f - pade 0 q f)⁻¹) := by
    rw [zero_sub, inv_neg, mul_add, mul_neg, show pade 0 q f ^ 2 * (pade 0 q f)⁻¹ = pade 0 q f by
      field_simp]
    linear_combination hg
  exact mul_left_cancel₀ h2 this

/-! ### Laplace transform inversion -/

open MeasureTheory Set in
/-- **DLMF 3.11.26**: `F(s) = ℒf(s) = ∫₀^∞ e^{−st} f(t) dt` (`laplace`, §1.14(iii)). -/
theorem dlmf_3_11_26 (f : ℝ → ℂ) (s : ℂ) :
    laplace f s = ∫ t in Ioi (0 : ℝ), Complex.exp (-(s * t)) * f t := rfl

open MeasureTheory Set in
/-- **DLMF §3.11(iv)**, "approximate `F` by a rational function `R` (vanishing at infinity) and
then approximate `f` by `r = ℒ⁻¹R`": for `R(s) = ∑ᵢ Aᵢ/(s − aᵢ)^{mᵢ+1}`,
`r(t) = ∑ᵢ Aᵢ t^{mᵢ} e^{aᵢt}/mᵢ!` has `ℒr = R` for `ℜs > max ℜaᵢ`. -/
theorem dlmf_3_11_iv_laplace {ι : Type*} (I : Finset ι) (A a : ι → ℂ) (m : ι → ℕ) {s : ℂ}
    (hs : ∀ i ∈ I, 0 < (s - a i).re) :
    laplace (fun t => ∑ i ∈ I, A i / (m i).factorial * ((t : ℂ) ^ m i * Complex.exp (a i * t))) s =
      ∑ i ∈ I, A i / (s - a i) ^ (m i + 1) := by
  unfold laplace
  simp only [Finset.mul_sum]
  rw [integral_finsetSum _ fun i hi => ?_]
  · refine Finset.sum_congr rfl fun i hi => ?_
    have h := laplace_pow_mul_cexp (hs i hi) (m i)
    unfold laplace at h
    rw [show (fun t : ℝ => Complex.exp (-(s * t)) * (A i / (m i).factorial *
        ((t : ℂ) ^ m i * Complex.exp (a i * t)))) = fun t : ℝ => A i / (m i).factorial *
        (Complex.exp (-(s * t)) * ((t : ℂ) ^ m i * Complex.exp (a i * t))) by
      funext t; ring, integral_const_mul, h]
    have hf : ((m i).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp
  · exact IntegrableOn.congr_fun ((integrableOn_laplace_pow_mul_cexp (hs i hi) (m i)).const_mul
      (A i / (m i).factorial)) (fun t _ => by ring) measurableSet_Ioi

end Azurite.DLMF
