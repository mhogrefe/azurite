/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Chudnovsky.AuxFunction
import Azurite.Chudnovsky.Rep
import Azurite.Feldman.Dirichlet

/-!
# The arithmetic of the auxiliary function

`CMData`: a lattice `ℤ + ℤτ` with complex multiplication by the imaginary quadratic integer
`τ` (`|τ| = 1`, `|Re τ| ≤ 1/2`, `τ² = pτ − q`), with `η(τ) = (u + vτ) η(1)`, `u + vτ ≠ τ` and
`g₂ = 2c e²`,
`e = ℘(1/2)`, `ϖ = η(1)`.

At the points `w = 1/2 + m + nτ` the functions `2z, ℘, ℘′, 2ζ` take the values
`1 + 2m + 2nτ`, `e`, `0`, `ϖ(1 + 2m + 2n(u + vτ))` (`pt_wpt`), all of the form
`A(ϖ, e) + τA′(ϖ, e)` (`rep_ptH`).  For integers `a(i, j, k, l)` the polynomial `polyQ`
represents the auxiliary function `PhiC` with coefficients `coefC = ∑_l a(i,j,k,l) ϖ^l`
(`aeval_polyQ`); its derivatives at the points `w` are values of integer polynomials
(`iteratedDeriv_PhiC_wpt`), hence representable with controlled sizes (`rep_value`), and
Dirichlet's box principle makes them all small for a suitable nonzero `a` (`exists_start`).
-/

namespace Azurite.Chudnovsky

open MvPolynomial UpperHalfPlane

/-- A lattice `ℤ + ℤτ` with complex multiplication, and the algebraic data of its
quasi-periods and invariants. -/
structure CMData where
  /-- the second period -/
  τ : ℍ
  /-- `τ² = pτ − q` -/
  p : ℤ
  /-- `τ² = pτ − q` -/
  q : ℤ
  /-- `η(τ) = (u + vτ) η(1)` -/
  u : ℤ
  /-- `η(τ) = (u + vτ) η(1)` -/
  v : ℤ
  /-- `g₂ = 2c e²` -/
  c : ℤ
  hn : ‖(τ : ℂ)‖ = 1
  hr : |(τ : ℂ).re| ≤ 1 / 2
  hsq : (τ : ℂ) ^ 2 = p * τ - q
  hp : |p| ≤ 1
  hq : |q| ≤ 1
  hη : quasiPeriod (pairOf τ) τ = (u + v * τ) * quasiPeriod (pairOf τ) 1
  hu : |u| ≤ 1
  hv : |v| ≤ 1
  hg : (pairOf τ).g₂ = 2 * c * halfValue (pairOf τ) ^ 2
  hc : |c| ≤ 2
  hα : (u : ℂ) + v * τ ≠ τ

namespace CMData

variable (D : CMData)

/-- The lattice. -/
noncomputable abbrev L : PeriodPair := pairOf D.τ

/-- The quasi-period `η(1)`. -/
noncomputable def ϖ : ℂ := quasiPeriod D.L 1

/-- `e = ℘(1/2)`. -/
noncomputable def e : ℂ := halfValue D.L

/-- The points `1/2 + m + nτ`. -/
noncomputable def wpt (m n : ℤ) : ℂ := 1 / 2 + m + n * D.τ

/-- The values of `(2z, ℘, ℘′, 2ζ, e, ϖ)` at `1/2 + m + nτ`. -/
noncomputable def ptH (m n : ℤ) : Fin 6 → ℂ :=
  ![1 + 2 * m + 2 * n * D.τ, D.e, 0, D.ϖ * (1 + 2 * m + 2 * n * (D.u + D.v * D.τ)), D.e, D.ϖ]

theorem lat_mem (m n : ℤ) : (m : ℂ) + n * D.τ ∈ D.L.lattice :=
  mem_lattice_pairOf.mpr ⟨m, n, rfl⟩

theorem wpt_far (m n : ℤ) : ∀ l ∈ D.L.lattice, 3 / 8 ≤ ‖D.wpt m n - l‖ :=
  half_far D.hn D.hr m n

theorem wpt_notMem (m n : ℤ) : D.wpt m n ∉ D.L.lattice := fun h => by
  have := D.wpt_far m n _ h
  rw [sub_self, norm_zero] at this
  norm_num at this

theorem pt_wpt (m n : ℤ) : pt D.L D.e D.ϖ (D.wpt m n) = D.ptH m n := by
  have hw : D.wpt m n = D.L.ω₁ / 2 + ((⟨_, D.lat_mem m n⟩ : D.L.lattice) : ℂ) := by
    simp only [wpt, L, pairOf_ω₁]
    ring
  funext i
  fin_cases i
  · show 2 * D.wpt m n = 1 + 2 * m + 2 * n * D.τ
    rw [wpt]
    ring
  · show D.L.weierstrassP (D.wpt m n) = D.e
    rw [hw, weierstrassP_half_add]
    rfl
  · show D.L.derivWeierstrassP (D.wpt m n) = 0
    rw [hw, derivWeierstrassP_half_add]
  · show 2 * weierstrassZeta D.L (D.wpt m n)
      = D.ϖ * (1 + 2 * m + 2 * n * (D.u + D.v * D.τ))
    have h := weierstrassZeta_half_add D.L m n
    simp only [L, pairOf_ω₁, pairOf_ω₂, mul_one] at h
    have hw' : D.wpt m n = 1 / 2 + ((m : ℂ) + n * D.τ) := by rw [wpt]; ring
    rw [hw']
    simp only [L]
    rw [h, D.hη]
    simp only [ϖ, L]
    ring
  · rfl
  · rfl

theorem norm_wpt_le {m n : ℤ} {H : ℝ} (hm : |(m : ℝ)| ≤ H) (hn : |(n : ℝ)| ≤ H) :
    ‖D.wpt m n‖ ≤ 1 / 2 + 2 * H := by
  unfold wpt
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖(1 / 2 + m : ℂ)‖ ≤ 1 / 2 + |(m : ℝ)| := by
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_intCast]
    norm_num
  rw [norm_mul, D.hn, mul_one, Complex.norm_intCast]
  linarith

end CMData

/-! ### Representability of the coordinates -/

theorem ml1_C_le {σ : Type*} (a : ℤ) : ml1 (C a : MvPolynomial σ ℤ) ≤ |(a : ℝ)| := by
  simpa [C_apply] using ml1_monomial_le (σ := σ) 0 a

theorem ml1_X_le {σ : Type*} (i : σ) : ml1 (X i : MvPolynomial σ ℤ) ≤ 1 :=
  (ml1_monomial_le (Finsupp.single i 1) 1).trans (by norm_num)

theorem ml1_X_pow_le {σ : Type*} (i : σ) (n : ℕ) : ml1 (X i ^ n : MvPolynomial σ ℤ) ≤ 1 := by
  rw [X_pow_eq_monomial]
  exact (ml1_monomial_le _ 1).trans (by norm_num)

theorem ml1_C_mul_X_le {σ : Type*} (a : ℤ) (i : σ) :
    ml1 (C a * X i : MvPolynomial σ ℤ) ≤ |(a : ℝ)| := by
  refine (ml1_mul_le _ _).trans ?_
  have h1 := ml1_C_le (σ := σ) a
  have h2 := ml1_X_le i
  have h0 := ml1_nonneg (C a : MvPolynomial σ ℤ)
  nlinarith [ml1_nonneg (X i : MvPolynomial σ ℤ)]

namespace CMData

variable (D : CMData)

theorem rep_ptH (m n : ℤ) (i : Fin 6) :
    Rep D.ϖ D.e D.τ 1 (3 * (1 + 2 * |(m : ℝ)| + 2 * |(n : ℝ)|)) (D.ptH m n i) := by
  have huR : |(D.u : ℝ)| ≤ 1 := by exact_mod_cast D.hu
  have hvR : |(D.v : ℝ)| ≤ 1 := by exact_mod_cast D.hv
  have hm0 := abs_nonneg (m : ℝ)
  have hn0 := abs_nonneg (n : ℝ)
  have hnu : |(n : ℝ) * D.u| ≤ |(n : ℝ)| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right hn0 huR
  have hnv : |(n : ℝ) * D.v| ≤ |(n : ℝ)| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right hn0 hvR
  have hdC : ∀ a : ℤ, (C a : MvPolynomial (Fin 2) ℤ).totalDegree ≤ 1 := fun a => by
    rw [totalDegree_C]; omega
  have hdX : ∀ j : Fin 2, (X j : MvPolynomial (Fin 2) ℤ).totalDegree ≤ 1 := fun j => by
    rw [totalDegree_X]
  have hdCX : ∀ (a : ℤ) (j : Fin 2), (C a * X j : MvPolynomial (Fin 2) ℤ).totalDegree ≤ 1 :=
    fun a j => (totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X])
  have hd0 : (0 : MvPolynomial (Fin 2) ℤ).totalDegree ≤ 1 := by simp
  have hX1 : Rep D.ϖ D.e D.τ 1 (3 * (1 + 2 * |(m : ℝ)| + 2 * |(n : ℝ)|)) D.e := by
    have h := Rep.of_pair (ϖ := D.ϖ) (e := D.e) (τ := D.τ) (X 1) 0 (d := 1)
      (B := 3 * (1 + 2 * |(m : ℝ)| + 2 * |(n : ℝ)|)) (hdX 1) hd0
      (by have := ml1_X_le (1 : Fin 2); linarith) (by simp; linarith)
    simpa [pt2] using h
  have hX0 : Rep D.ϖ D.e D.τ 1 (3 * (1 + 2 * |(m : ℝ)| + 2 * |(n : ℝ)|)) D.ϖ := by
    have h := Rep.of_pair (ϖ := D.ϖ) (e := D.e) (τ := D.τ) (X 0) 0 (d := 1)
      (B := 3 * (1 + 2 * |(m : ℝ)| + 2 * |(n : ℝ)|)) (hdX 0) hd0
      (by have := ml1_X_le (0 : Fin 2); linarith) (by simp; linarith)
    simpa [pt2] using h
  fin_cases i
  · show Rep D.ϖ D.e D.τ 1 _ (1 + 2 * m + 2 * n * D.τ)
    have h := Rep.of_pair (ϖ := D.ϖ) (e := D.e) (τ := D.τ) (C (1 + 2 * m)) (C (2 * n)) (d := 1)
      (B := 3 * (1 + 2 * |(m : ℝ)| + 2 * |(n : ℝ)|)) (hdC _) (hdC _)
      (by
        have := ml1_C_le (σ := Fin 2) (1 + 2 * m)
        have h2 : |((1 + 2 * m : ℤ) : ℝ)| ≤ 1 + 2 * |(m : ℝ)| := by
          push_cast
          refine (abs_add_le _ _).trans ?_
          rw [abs_one, abs_mul, abs_two]
        linarith)
      (by
        have := ml1_C_le (σ := Fin 2) (2 * n)
        have h2 : |((2 * n : ℤ) : ℝ)| = 2 * |(n : ℝ)| := by
          push_cast
          rw [abs_mul, abs_two]
        linarith)
    have e1 : aeval (pt2 D.ϖ D.e) (C (1 + 2 * m) : MvPolynomial (Fin 2) ℤ)
        + D.τ * aeval (pt2 D.ϖ D.e) (C (2 * n) : MvPolynomial (Fin 2) ℤ)
        = 1 + 2 * m + 2 * n * D.τ := by
      simp
      ring
    rwa [e1] at h
  · exact hX1
  · exact Rep.zero 1 (by positivity)
  · show Rep D.ϖ D.e D.τ 1 _ (D.ϖ * (1 + 2 * m + 2 * n * (D.u + D.v * D.τ)))
    have h := Rep.of_pair (ϖ := D.ϖ) (e := D.e) (τ := D.τ) (C (1 + 2 * m + 2 * n * D.u) * X 0)
      (C (2 * n * D.v) * X 0) (d := 1)
      (B := 3 * (1 + 2 * |(m : ℝ)| + 2 * |(n : ℝ)|)) (hdCX _ _) (hdCX _ _)
      (by
        have := ml1_C_mul_X_le (1 + 2 * m + 2 * n * D.u) (0 : Fin 2)
        have h2 : |((1 + 2 * m + 2 * n * D.u : ℤ) : ℝ)| ≤ 1 + 2 * |(m : ℝ)| + 2 * |(n : ℝ)| := by
          push_cast
          refine (abs_add_three _ _ _).trans ?_
          rw [abs_one, abs_mul, abs_two, mul_assoc, abs_mul, abs_two]
          linarith
        linarith)
      (by
        have := ml1_C_mul_X_le (2 * n * D.v) (0 : Fin 2)
        have h2 : |((2 * n * D.v : ℤ) : ℝ)| ≤ 2 * |(n : ℝ)| := by
          push_cast
          rw [mul_assoc, abs_mul, abs_two]
          linarith
        linarith)
    have e1 : aeval (pt2 D.ϖ D.e) (C (1 + 2 * m + 2 * n * D.u) * X 0 : MvPolynomial (Fin 2) ℤ)
        + D.τ * aeval (pt2 D.ϖ D.e) (C (2 * n * D.v) * X 0 : MvPolynomial (Fin 2) ℤ)
        = D.ϖ * (1 + 2 * m + 2 * n * (D.u + D.v * D.τ)) := by
      simp [pt2]
      ring
    rwa [e1] at h
  · exact hX1
  · exact hX0

theorem norm_ptH_le {m n : ℤ} {H W : ℝ} (hH : 1 ≤ H) (hW : 1 ≤ W) (hm : |(m : ℝ)| ≤ H)
    (hn : |(n : ℝ)| ≤ H) (hϖ : ‖D.ϖ‖ ≤ W) (he : ‖D.e‖ ≤ W) (i : Fin 6) :
    ‖D.ptH m n i‖ ≤ 7 * H * W := by
  have huR : |(D.u : ℝ)| ≤ 1 := by exact_mod_cast D.hu
  have hvR : |(D.v : ℝ)| ≤ 1 := by exact_mod_cast D.hv
  have hHW : H ≤ H * W := le_mul_of_one_le_right (by linarith) hW
  have hWH : W ≤ H * W := le_mul_of_one_le_left (by linarith) hH
  have h0 : ‖(1 + 2 * m + 2 * n * D.τ : ℂ)‖ ≤ 1 + 2 * H + 2 * H := by
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans ?_) ?_)
    · rw [norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_intCast]
      linarith
    · rw [norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_intCast, D.hn]
      linarith
  fin_cases i
  · show ‖(1 + 2 * m + 2 * n * D.τ : ℂ)‖ ≤ _
    linarith
  · show ‖D.e‖ ≤ _
    linarith
  · show ‖(0 : ℂ)‖ ≤ _
    rw [norm_zero]
    positivity
  · show ‖D.ϖ * (1 + 2 * m + 2 * n * (D.u + D.v * D.τ))‖ ≤ _
    rw [norm_mul]
    have h3 : ‖(1 + 2 * m + 2 * n * (D.u + D.v * D.τ) : ℂ)‖ ≤ 1 + 2 * H + 2 * H * 2 := by
      refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans ?_) ?_)
      · rw [norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_intCast]
        linarith
      · rw [norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_intCast]
        have : ‖(D.u + D.v * D.τ : ℂ)‖ ≤ 2 := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, D.hn, Complex.norm_intCast, Complex.norm_intCast]
          linarith
        have hn0 := abs_nonneg (n : ℝ)
        nlinarith
    calc ‖D.ϖ‖ * ‖(1 + 2 * m + 2 * n * (D.u + D.v * D.τ) : ℂ)‖ ≤ W * (1 + 2 * H + 2 * H * 2) :=
          mul_le_mul hϖ h3 (norm_nonneg _) (by linarith)
      _ ≤ 7 * H * W := by nlinarith
  · show ‖D.e‖ ≤ _
    linarith
  · show ‖D.ϖ‖ ≤ _
    linarith

end CMData

/-! ### The polynomial of the auxiliary function -/

/-- The index set of the unknowns. -/
def idx (Lc J : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  Finset.range Lc ×ˢ Finset.range Lc ×ˢ Finset.range Lc ×ˢ Finset.range J

theorem card_idx (Lc J : ℕ) : (idx Lc J).card = Lc ^ 3 * J := by
  simp only [idx, Finset.card_product, Finset.card_range]
  ring

/-- The monomial `Z^i P^j T^k W^l`. -/
noncomputable def monoQ (x : ℕ × ℕ × ℕ × ℕ) : MvPolynomial (Fin 6) ℤ :=
  X 0 ^ x.1 * X 1 ^ x.2.1 * X 3 ^ x.2.2.1 * X 5 ^ x.2.2.2

/-- The polynomial `∑ a(i,j,k,l) Z^i P^j T^k W^l`. -/
noncomputable def polyQ (Lc J : ℕ) (a : ℕ × ℕ × ℕ × ℕ → ℤ) : MvPolynomial (Fin 6) ℤ :=
  ∑ x ∈ idx Lc J, a x • monoQ x

/-- The coefficients `∑_l a(i,j,k,l) ϖ^l` of the auxiliary function. -/
noncomputable def coefC (ϖ : ℂ) (J : ℕ) (a : ℕ × ℕ × ℕ × ℕ → ℤ) (i j k : ℕ) : ℂ :=
  ∑ l ∈ Finset.range J, (a (i, j, k, l) : ℂ) * ϖ ^ l

theorem aeval_monoQ (L : PeriodPair) (e ϖ z : ℂ) (x : ℕ × ℕ × ℕ × ℕ) :
    aeval (pt L e ϖ z) (monoQ x) = (2 * z) ^ x.1 * L.weierstrassP z ^ x.2.1
      * (2 * weierstrassZeta L z) ^ x.2.2.1 * ϖ ^ x.2.2.2 := by
  simp only [monoQ, map_mul, map_pow, aeval_X]
  rfl

theorem aeval_polyQ (L : PeriodPair) (e ϖ z : ℂ) (Lc J : ℕ) (a : ℕ × ℕ × ℕ × ℕ → ℤ) :
    aeval (pt L e ϖ z) (polyQ Lc J a) = PhiC L Lc (coefC ϖ J a) z := by
  simp only [polyQ, PhiC, coefC, idx, map_sum, Finset.sum_product, map_zsmul,
    aeval_monoQ, Finset.sum_mul]
  simp only [zsmul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem totalDegree_monoQ_le (x : ℕ × ℕ × ℕ × ℕ) :
    (monoQ x).totalDegree ≤ x.1 + x.2.1 + x.2.2.1 + x.2.2.2 := by
  unfold monoQ
  refine (totalDegree_mul _ _).trans (add_le_add ((totalDegree_mul _ _).trans
    (add_le_add ((totalDegree_mul _ _).trans (add_le_add ?_ ?_)) ?_)) ?_) <;>
  exact (totalDegree_X_pow _ _).le

theorem ml1_mul_le_one {σ : Type*} {P Q : MvPolynomial σ ℤ} (hP : ml1 P ≤ 1) (hQ : ml1 Q ≤ 1) :
    ml1 (P * Q) ≤ 1 :=
  (ml1_mul_le P Q).trans ((mul_le_mul hP hQ (ml1_nonneg Q) zero_le_one).trans_eq (one_mul 1))

theorem ml1_monoQ_le (x : ℕ × ℕ × ℕ × ℕ) : ml1 (monoQ x) ≤ 1 :=
  ml1_mul_le_one (ml1_mul_le_one (ml1_mul_le_one (ml1_X_pow_le _ _) (ml1_X_pow_le _ _))
    (ml1_X_pow_le _ _)) (ml1_X_pow_le _ _)

theorem mem_idx {Lc J : ℕ} {x : ℕ × ℕ × ℕ × ℕ} :
    x ∈ idx Lc J ↔ x.1 < Lc ∧ x.2.1 < Lc ∧ x.2.2.1 < Lc ∧ x.2.2.2 < J := by
  simp [idx]

theorem totalDegree_polyQ_le (Lc J : ℕ) (a : ℕ × ℕ × ℕ × ℕ → ℤ) :
    (polyQ Lc J a).totalDegree ≤ 3 * Lc + J := by
  unfold polyQ
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun x hx => ?_)
  have := mem_idx.mp hx
  have := totalDegree_monoQ_le x
  refine (totalDegree_smul_le _ _).trans ?_
  omega

theorem ml1_polyQ_le (Lc J : ℕ) {a : ℕ × ℕ × ℕ × ℕ → ℤ} {Am : ℝ}
    (ha : ∀ x, |(a x : ℝ)| ≤ Am) : ml1 (polyQ Lc J a) ≤ Lc ^ 3 * J * Am := by
  have hAm : 0 ≤ Am := (abs_nonneg _).trans (ha (0, 0, 0, 0))
  unfold polyQ
  refine (ml1_sum_le _ _).trans ?_
  calc ∑ x ∈ idx Lc J, ml1 (a x • monoQ x) ≤ ∑ _x ∈ idx Lc J, Am :=
        Finset.sum_le_sum fun x _ => (ml1_smul_le _ _).trans (by
          have := ml1_monoQ_le x
          have h2 := ha x
          nlinarith [ml1_nonneg (monoQ x), abs_nonneg (a x : ℝ)])
    _ = Lc ^ 3 * J * Am := by
        rw [Finset.sum_const, card_idx, nsmul_eq_mul]
        push_cast
        ring

theorem norm_coefC_le {ϖ : ℂ} {W : ℝ} (hW1 : 1 ≤ W) (hW : ‖ϖ‖ ≤ W) (J : ℕ)
    {a : ℕ × ℕ × ℕ × ℕ → ℤ} {Am : ℝ} (ha : ∀ x, |(a x : ℝ)| ≤ Am) (i j k : ℕ) :
    ‖coefC ϖ J a i j k‖ ≤ J * (Am * W ^ J) := by
  have hAm : 0 ≤ Am := (abs_nonneg _).trans (ha (0, 0, 0, 0))
  unfold coefC
  refine (norm_sum_le _ _).trans ?_
  calc ∑ l ∈ Finset.range J, ‖(a (i, j, k, l) : ℂ) * ϖ ^ l‖ ≤ ∑ _l ∈ Finset.range J, Am * W ^ J :=
        Finset.sum_le_sum fun l hl => by
          rw [norm_mul, norm_pow, Complex.norm_intCast]
          exact mul_le_mul (ha _) ((pow_le_pow_left₀ (norm_nonneg _) hW l).trans
            (pow_le_pow_right₀ hW1 (Finset.mem_range.mp hl).le)) (by positivity) hAm
    _ = J * (Am * W ^ J) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The iterates of the derivation are linear in the unknowns. -/
theorem iterate_polyQ (c : ℤ) (n Lc J : ℕ) (a : ℕ × ℕ × ℕ × ℕ → ℤ) :
    (dD c)^[n] (polyQ Lc J a) = ∑ x ∈ idx Lc J, a x • (dD c)^[n] (monoQ x) := by
  have h : ∀ P, (dD c)^[n] P
      = (((dD c : MvPolynomial (Fin 6) ℤ →ₗ[ℤ] MvPolynomial (Fin 6) ℤ)) ^ n) P := fun P =>
    (Module.End.pow_apply _ n P).symm
  simp only [h, polyQ, map_sum, map_zsmul]

theorem norm_aeval_le_ml1 {σ : Type*} [Fintype σ] {x : σ → ℂ} {Xb : ℝ} (hX1 : 1 ≤ Xb)
    (hx : ∀ i, ‖x i‖ ≤ Xb) (P : MvPolynomial σ ℤ) {d : ℕ} (hd : P.totalDegree ≤ d) :
    ‖aeval x P‖ ≤ ml1 P * Xb ^ d := by
  rw [aeval_def, eval₂_eq', ml1, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s hs => ?_)
  rw [norm_mul, norm_prod]
  have h1 : ‖algebraMap ℤ ℂ (P.coeff s)‖ = |(P.coeff s : ℝ)| := by
    rw [eq_intCast, Complex.norm_intCast]
  have hdeg : ∑ i, s i ≤ d := by
    have := (mdeg_le_totalDegree hs).trans hd
    unfold mdeg at this
    rwa [Finsupp.sum_fintype _ _ (fun _ => rfl)] at this
  have h2 : ∏ i, ‖x i ^ s i‖ ≤ Xb ^ d := by
    calc ∏ i, ‖x i ^ s i‖ ≤ ∏ i, Xb ^ s i :=
          Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => by
            rw [norm_pow]
            exact pow_le_pow_left₀ (norm_nonneg _) (hx i) _
      _ = Xb ^ ∑ i, s i := Finset.prod_pow_eq_pow_sum _ _ _
      _ ≤ Xb ^ d := pow_le_pow_right₀ hX1 hdeg
  rw [h1]
  exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)

namespace CMData

variable (D : CMData)

theorem hg' : D.L.g₂ = 2 * D.c * D.e ^ 2 := D.hg

/-- **The derivatives of the auxiliary function at the points `1/2 + m + nτ`** are values of
integer polynomials. -/
theorem iteratedDeriv_PhiC_wpt (Lc J : ℕ) (a : ℕ × ℕ × ℕ × ℕ → ℤ) (n : ℕ) (m n' : ℤ) :
    iteratedDeriv n (PhiC D.L Lc (coefC D.ϖ J a)) (D.wpt m n')
      = aeval (D.ptH m n') ((dD D.c)^[n] (polyQ Lc J a)) := by
  have hfun : PhiC D.L Lc (coefC D.ϖ J a)
      = fun z => aeval (pt D.L D.e D.ϖ z) (polyQ Lc J a) :=
    funext fun z => (aeval_polyQ D.L D.e D.ϖ z Lc J a).symm
  rw [hfun, iteratedDeriv_aeval D.hg' _ n (D.wpt_notMem m n'), pt_wpt]

/-- The sizes of these values. -/
theorem rep_value (Lc J : ℕ) {a : ℕ × ℕ × ℕ × ℕ → ℤ} {Am : ℝ} (ha : ∀ x, |(a x : ℝ)| ≤ Am)
    (n : ℕ) (m n' : ℤ) :
    Rep D.ϖ D.e D.τ (3 * Lc + J + n)
      (3 * ((8 * (3 * Lc + J + n : ℕ)) ^ n * (Lc ^ 3 * J * Am)
        * (3 * (1 + 2 * |(m : ℝ)| + 2 * |(n' : ℝ)|)) ^ (3 * Lc + J + n)))
      (aeval (D.ptH m n') ((dD D.c)^[n] (polyQ Lc J a))) := by
  have hdeg := (totalDegree_dD_iterate_le D.c (polyQ Lc J a) n).trans
    (Nat.add_le_add_right (totalDegree_polyQ_le Lc J a) n)
  have hB : (1 : ℝ) ≤ 3 * (1 + 2 * |(m : ℝ)| + 2 * |(n' : ℝ)|) := by
    have := abs_nonneg (m : ℝ)
    have := abs_nonneg (n' : ℝ)
    linarith
  have h := Rep_aeval D.hsq D.hp D.hq hB (D.rep_ptH m n') _ hdeg
  refine h.mono le_rfl ?_
  have h1 := ml1_dD_iterate_le D.hc (polyQ Lc J a) n
  have h2 : (8 * (((polyQ Lc J a).totalDegree + n : ℕ) : ℝ)) ^ n
      ≤ (8 * ((3 * Lc + J + n : ℕ) : ℝ)) ^ n :=
    pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr
      (Nat.add_le_add_right (totalDegree_polyQ_le Lc J a) n)) (by norm_num)) n
  have hml : ml1 ((dD D.c)^[n] (polyQ Lc J a))
      ≤ (8 * ((3 * Lc + J + n : ℕ) : ℝ)) ^ n * (Lc ^ 3 * J * Am) :=
    h1.trans (mul_le_mul h2 (ml1_polyQ_le Lc J ha) (ml1_nonneg _) (by positivity))
  have hpos : (0 : ℝ) ≤ (3 * (1 + 2 * |(m : ℝ)| + 2 * |(n' : ℝ)|)) ^ (3 * Lc + J + n) := by
    positivity
  have := mul_le_mul_of_nonneg_right hml hpos
  linarith

/-- **The start**: by Dirichlet's box principle there are integers `a`, not all zero, of
absolute value `≤ 2^ζ`, for which all the values `Φ⁽ⁿ⁾(1/2 + m + n′τ)`, `n < N₀`,
`m, n′ < H₀`, are small. -/
theorem exists_start (Lc J N₀ H₀ ζ ν γ : ℕ)
    (hcount : ν * (N₀ * (H₀ * H₀) * 2) < ζ * (Lc ^ 3 * J)) (hH : 1 ≤ H₀)
    (hϖ : ‖D.ϖ‖ ≤ 2 ^ γ) (he : ‖D.e‖ ≤ 2 ^ γ) :
    ∃ a : ℕ × ℕ × ℕ × ℕ → ℤ, (∃ x ∈ idx Lc J, a x ≠ 0) ∧ (∀ x, |(a x : ℝ)| ≤ 2 ^ ζ) ∧
      ∀ n < N₀, ∀ m < H₀, ∀ n' < H₀,
        ‖aeval (D.ptH (m : ℤ) (n' : ℤ)) ((dD D.c)^[n] (polyQ Lc J a))‖ * 2 ^ ν
          ≤ 4 * (Lc ^ 3 * J * 2 ^ ζ * ((8 * (3 * Lc + J + N₀ : ℕ)) ^ N₀
            * (7 * H₀ * 2 ^ γ) ^ (3 * Lc + J + N₀))) := by
  classical
  set d := 3 * Lc + J + N₀ with hd
  set Acoef : ℝ := (8 * (d : ℝ)) ^ N₀ * (7 * H₀ * 2 ^ γ) ^ d with hAcoef
  set F : Finset ((ℕ × ℕ × ℕ) × Bool) :=
    (Finset.range N₀ ×ˢ Finset.range H₀ ×ˢ Finset.range H₀) ×ˢ Finset.univ with hF
  set val : (ℕ × ℕ × ℕ) → (ℕ × ℕ × ℕ × ℕ) → ℂ := fun i x =>
    aeval (D.ptH (i.2.1 : ℤ) (i.2.2 : ℤ)) ((dD D.c)^[i.1] (monoQ x)) with hval
  set am : (ℕ × ℕ × ℕ) × Bool → (ℕ × ℕ × ℕ × ℕ) → ℝ := fun i x =>
    if i.2 then (val i.1 x).re else (val i.1 x).im with ham
  have hH' : (1 : ℝ) ≤ H₀ := by exact_mod_cast hH
  have h2γ : (1 : ℝ) ≤ 2 ^ γ := one_le_pow₀ one_le_two
  have hXb : (1 : ℝ) ≤ 7 * H₀ * 2 ^ γ := by nlinarith
  -- the coefficients of the forms
  have hvalb : ∀ i ∈ Finset.range N₀ ×ˢ Finset.range H₀ ×ˢ Finset.range H₀, ∀ x ∈ idx Lc J,
      ‖val i x‖ ≤ Acoef := by
    intro i hi x hx
    simp only [Finset.mem_product, Finset.mem_range] at hi
    have hx' := mem_idx.mp hx
    have hdegm := totalDegree_monoQ_le x
    have hdeg : ((dD D.c)^[i.1] (monoQ x)).totalDegree ≤ d :=
      (totalDegree_dD_iterate_le D.c (monoQ x) i.1).trans (by omega)
    have hd1 : (1 : ℝ) ≤ 8 * (d : ℝ) := by
      have : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
      linarith
    have hpt : ∀ j, ‖D.ptH (i.2.1 : ℤ) (i.2.2 : ℤ) j‖ ≤ 7 * H₀ * 2 ^ γ := fun j =>
      D.norm_ptH_le hH' h2γ
        (by rw [Int.cast_natCast, Nat.abs_cast]; exact_mod_cast hi.2.1.le)
        (by rw [Int.cast_natCast, Nat.abs_cast]; exact_mod_cast hi.2.2.le) hϖ he j
    refine (norm_aeval_le_ml1 hXb hpt _ hdeg).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    refine (ml1_dD_iterate_le D.hc (monoQ x) i.1).trans ?_
    have hb : (8 * (((monoQ x).totalDegree + i.1 : ℕ) : ℝ)) ^ i.1 ≤ (8 * (d : ℝ)) ^ N₀ :=
      (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left
        (Nat.cast_le.mpr (by omega)) (by norm_num)) i.1).trans (pow_le_pow_right₀ hd1 hi.1.le)
    calc (8 * (((monoQ x).totalDegree + i.1 : ℕ) : ℝ)) ^ i.1 * ml1 (monoQ x)
        ≤ (8 * (d : ℝ)) ^ N₀ * 1 :=
          mul_le_mul hb (ml1_monoQ_le x) (ml1_nonneg _) (by positivity)
      _ = (8 * (d : ℝ)) ^ N₀ := mul_one _
  have hamb : ∀ i ∈ F, ∀ x ∈ idx Lc J, |am i x| ≤ Acoef := by
    intro i hi x hx
    have hi' := (Finset.mem_product.mp hi).1
    have := hvalb i.1 hi' x hx
    simp only [ham]
    split_ifs
    · exact (Complex.abs_re_le_norm _).trans this
    · exact (Complex.abs_im_le_norm _).trans this
  have hAc0 : 0 ≤ Acoef := by positivity
  have hz1 : 2 ^ ζ - 1 + 1 = 2 ^ ζ := Nat.sub_add_cancel Nat.one_le_two_pow
  obtain ⟨x, hx0, hxz, hx⟩ :=
    Azurite.Feldman.dirichlet_box_finset F (idx Lc J) am (2 ^ ζ - 1) (2 ^ ν)
    (Lc ^ 3 * J * 2 ^ ζ * Acoef) (by positivity)
    (by
      rw [hz1, ← pow_mul, ← pow_mul]
      refine Nat.pow_lt_pow_right (by norm_num) ?_
      have hcF : F.card = N₀ * (H₀ * H₀) * 2 := by
        simp [hF, Finset.card_product]
      rw [hcF, card_idx]
      exact hcount)
    (by
      intro y hy i hi
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ j ∈ idx Lc J, |am i j * (y j : ℝ)| ≤ ∑ _j ∈ idx Lc J, Acoef * 2 ^ ζ :=
            Finset.sum_le_sum fun j hj => by
              rw [abs_mul, Nat.abs_cast]
              refine mul_le_mul (hamb i hi j hj) ?_ (by positivity) hAc0
              have := hy j
              exact_mod_cast (by omega : y j ≤ 2 ^ ζ)
        _ = Lc ^ 3 * J * 2 ^ ζ * Acoef := by
            rw [Finset.sum_const, card_idx, nsmul_eq_mul]
            push_cast
            ring)
  refine ⟨x, hx0, fun j => ?_, fun n hn m hm n' hn' => ?_⟩
  · have := hxz j
    have h2 : |x j| ≤ ((2 ^ ζ : ℕ) : ℤ) := this.trans (by exact_mod_cast Nat.sub_le _ _)
    have h3 : (|x j| : ℝ) ≤ ((2 ^ ζ : ℕ) : ℝ) := by exact_mod_cast h2
    simpa using h3
  · -- the value is the linear form
    have hV : aeval (D.ptH (m : ℤ) (n' : ℤ)) ((dD D.c)^[n] (polyQ Lc J x))
        = ∑ j ∈ idx Lc J, (x j : ℂ) * val (n, m, n') j := by
      rw [iterate_polyQ, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_zsmul, zsmul_eq_mul]
    have hmem : ∀ b : Bool, ((n, m, n'), b) ∈ F := fun b => by
      simp [hF, hn, hm, hn']
    have hre := hx _ (hmem true)
    have him := hx _ (hmem false)
    have ere : (∑ j ∈ idx Lc J, (x j : ℂ) * val (n, m, n') j).re
        = ∑ j ∈ idx Lc J, am ((n, m, n'), true) j * (x j : ℝ) := by
      rw [Complex.re_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [ham, mul_comm]
    have eim : (∑ j ∈ idx Lc J, (x j : ℂ) * val (n, m, n') j).im
        = ∑ j ∈ idx Lc J, am ((n, m, n'), false) j * (x j : ℝ) := by
      rw [Complex.im_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [ham, mul_comm]
    rw [← ere] at hre
    rw [← eim] at him
    rw [hV]
    have hnorm := Complex.norm_le_abs_re_add_abs_im (∑ j ∈ idx Lc J, (x j : ℂ) * val (n, m, n') j)
    have h2ν : (0 : ℝ) < ((2 ^ ν : ℕ) : ℝ) := by positivity
    have hsum : ‖∑ j ∈ idx Lc J, (x j : ℂ) * val (n, m, n') j‖
        ≤ 4 * (Lc ^ 3 * J * 2 ^ ζ * Acoef) / ((2 ^ ν : ℕ) : ℝ) := by
      have e4 : 4 * (Lc ^ 3 * J * 2 ^ ζ * Acoef) / ((2 ^ ν : ℕ) : ℝ)
          = 2 * (Lc ^ 3 * J * 2 ^ ζ * Acoef) / ((2 ^ ν : ℕ) : ℝ)
            + 2 * (Lc ^ 3 * J * 2 ^ ζ * Acoef) / ((2 ^ ν : ℕ) : ℝ) := by ring
      rw [e4]
      linarith
    rw [le_div_iff₀ h2ν] at hsum
    simpa using hsum

end CMData

end Azurite.Chudnovsky
