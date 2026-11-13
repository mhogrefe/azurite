/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section14Dixon

/-!
# DLMF §5.14: Anderson's double counting

Anderson's proof of Selberg's integral (Forrester–Warnaar, *The importance of the Selberg
integral*, §2): the integral `K` of
`∏ xᵢ^{α−1}(1 − xᵢ)^{β−1} ∏ᵢⱼ |yᵢ − xⱼ|^{γ−1} ∏_{i<j}|yᵢ − yⱼ| ∏_{i<j}|xᵢ − xⱼ|` over
`1 > x₀ > y₀ > x₁ > ⋯ > y_{n−1} > xₙ > 0` is computed by integrating first over `y` and first over
`x`, each time with the Dixon–Anderson integral. This file sets up the region in its two
descriptions (`kRegion_iff`).
-/

open Finset

namespace Azurite.DLMF

variable {n : ℕ}

/-- The ordered region `1 > x₀ > x₁ > ⋯ > x_{m−1} > 0`. -/
def orderedOpen (m : ℕ) : Set (Fin m → ℝ) :=
  {x | (∀ i, 0 < x i ∧ x i < 1) ∧ ∀ i j, i < j → x j < x i}

/-- The nodes `(1, y₀, …, y_{n−1}, 0)`. -/
noncomputable def andersonNodes (y : Fin n → ℝ) : Fin (n + 2) → ℝ :=
  Fin.cons 1 (Fin.snoc y 0)

@[simp] theorem andersonNodes_zero (y : Fin n → ℝ) : andersonNodes y 0 = 1 := rfl

@[simp] theorem andersonNodes_succ_castSucc (y : Fin n → ℝ) (k : Fin n) :
    andersonNodes y k.castSucc.succ = y k := by
  simp [andersonNodes]

@[simp] theorem andersonNodes_last (y : Fin n → ℝ) : andersonNodes y (Fin.last (n + 1)) = 0 := by
  rw [show Fin.last (n + 1) = (Fin.last n).succ from rfl]
  simp [andersonNodes]

theorem andersonNodes_strictAnti {y : Fin n → ℝ} (hy : y ∈ orderedOpen n) :
    StrictAnti (andersonNodes y) := by
  intro i j hij
  -- write both indices as `0`, `k.castSucc.succ`, or `last`
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => exact absurd hij (lt_irrefl _)
    | succ j =>
      induction j using Fin.lastCases with
      | last => simp only [andersonNodes_zero]; rw [show (Fin.last n).succ = Fin.last (n + 1) from
          rfl, andersonNodes_last]; norm_num
      | cast k => rw [andersonNodes_succ_castSucc, andersonNodes_zero]; exact (hy.1 k).2
  | succ i =>
    induction j using Fin.cases with
    | zero => exact absurd hij (Fin.not_lt_zero _)
    | succ j =>
      rw [Fin.succ_lt_succ_iff] at hij
      induction i using Fin.lastCases with
      | last => exact absurd hij (not_lt.mpr (Fin.le_last _))
      | cast k =>
        induction j using Fin.lastCases with
        | last => rw [andersonNodes_succ_castSucc, show (Fin.last n).succ = Fin.last (n + 1) from
            rfl, andersonNodes_last]; exact (hy.1 k).1
        | cast l =>
          rw [andersonNodes_succ_castSucc, andersonNodes_succ_castSucc]
          exact hy.2 k l (Fin.castSucc_lt_castSucc_iff.mp hij)

/-- The region `1 > x₀ > y₀ > x₁ > ⋯ > y_{n−1} > xₙ > 0`. -/
def kRegion (n : ℕ) : Set ((Fin (n + 1) → ℝ) × (Fin n → ℝ)) :=
  {p | p.1 ∈ orderedOpen (n + 1) ∧ p.2 ∈ dixonRegion p.1}

theorem andersonNodes_castSucc_succ (y : Fin n → ℝ) (k : Fin n) :
    andersonNodes y k.succ.castSucc = y k := by
  rw [← Fin.succ_castSucc, andersonNodes_succ_castSucc]

theorem andersonNodes_castSucc_zero (y : Fin n → ℝ) :
    andersonNodes y (0 : Fin (n + 1)).castSucc = 1 := rfl

theorem andersonNodes_succ_last (y : Fin n → ℝ) :
    andersonNodes y (Fin.last n).succ = 0 := andersonNodes_last y

theorem andersonNodes_mem_Icc {y : Fin n → ℝ} (hy : y ∈ orderedOpen n) (i : Fin (n + 2)) :
    0 ≤ andersonNodes y i ∧ andersonNodes y i ≤ 1 := by
  have h := andersonNodes_strictAnti hy
  constructor
  · rw [← andersonNodes_last y]; exact h.antitone (Fin.le_last i)
  · rw [← andersonNodes_zero y]; exact h.antitone (Fin.zero_le i)

/-- The two descriptions of the region. -/
theorem mem_kRegion_iff {p : (Fin (n + 1) → ℝ) × (Fin n → ℝ)} :
    p ∈ kRegion n ↔ p.2 ∈ orderedOpen n ∧ p.1 ∈ dixonRegion (andersonNodes p.2) := by
  obtain ⟨x, y⟩ := p
  simp only [kRegion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hx1, hx2⟩, hy⟩
    have hyo : y ∈ orderedOpen n := by
      refine ⟨fun k => ⟨?_, ?_⟩, fun i j hij => ?_⟩
      · linarith [(hy k).1, (hx1 k.succ).1]
      · linarith [(hy k).2, (hx1 k.castSucc).2]
      · have h1 : i.succ ≤ j.castSucc := by rw [Fin.le_iff_val_le_val]; simp; omega
        have h2 : x j.castSucc ≤ x i.succ := by
          rcases h1.lt_or_eq with h | h
          · exact (hx2 _ _ h).le
          · rw [h]
        linarith [(hy j).2, (hy i).1]
    refine ⟨hyo, fun i => ⟨?_, ?_⟩⟩
    · induction i using Fin.lastCases with
      | last => rw [andersonNodes_succ_last]; exact (hx1 _).1
      | cast k => rw [andersonNodes_succ_castSucc]; exact (hy k).2
    · induction i using Fin.cases with
      | zero => rw [andersonNodes_castSucc_zero]; exact (hx1 0).2
      | succ k => rw [andersonNodes_castSucc_succ]; exact (hy k).1
  · rintro ⟨hyo, hx⟩
    have hn := andersonNodes_strictAnti hyo
    have hx1 : ∀ i, 0 < x i ∧ x i < 1 := fun i => by
      have := andersonNodes_mem_Icc hyo i.succ
      have := andersonNodes_mem_Icc hyo i.castSucc
      exact ⟨by linarith [(hx i).1], by linarith [(hx i).2]⟩
    refine ⟨⟨hx1, fun i j hij => ?_⟩, fun k => ⟨?_, ?_⟩⟩
    · have h1 : i.succ ≤ j.castSucc := by rw [Fin.le_iff_val_le_val]; simp; omega
      linarith [(hx j).2, (hx i).1, hn.antitone h1]
    · have := (hx k.succ).2; rwa [andersonNodes_castSucc_succ] at this
    · have := (hx k.castSucc).1; rwa [andersonNodes_succ_castSucc] at this

/-! ### The integrands -/

/-- The exponents `(β, γ, …, γ, α)` for the nodes `(1, y₀, …, y_{n−1}, 0)`. -/
noncomputable def andersonS (n : ℕ) (α β γ : ℂ) : Fin (n + 2) → ℂ :=
  Fin.cons β (Fin.snoc (fun _ : Fin n => γ) α)

@[simp] theorem andersonS_zero (α β γ : ℂ) : andersonS n α β γ 0 = β := rfl

@[simp] theorem andersonS_succ_castSucc (α β γ : ℂ) (k : Fin n) :
    andersonS n α β γ k.castSucc.succ = γ := by simp [andersonS]

@[simp] theorem andersonS_succ_last (α β γ : ℂ) : andersonS n α β γ (Fin.last n).succ = α := by
  simp [andersonS]

/-- `∏ xᵢ^{α−1}(1 − xᵢ)^{β−1}`. -/
noncomputable def jacobiWeight {m : ℕ} (α β : ℂ) (x : Fin m → ℝ) : ℂ :=
  ∏ i, (x i : ℂ) ^ (α - 1) * ((1 - x i : ℝ) : ℂ) ^ (β - 1)

/-- `∏_{i<j} (xᵢ − xⱼ)`. -/
noncomputable def vandermondeC {m : ℕ} (x : Fin m → ℝ) : ℂ :=
  ∏ i, ∏ j ∈ Ioi i, ((x i - x j : ℝ) : ℂ)

/-- Anderson's integrand on `kRegion`, integrated first over `y`. -/
noncomputable def andersonK (n : ℕ) (α β γ : ℂ) (p : (Fin (n + 1) → ℝ) × (Fin n → ℝ)) : ℂ :=
  jacobiWeight α β p.1 * vandermondeC p.1 * dixonIntegrand p.1 (fun _ => γ) p.2

/-- The same integrand, integrated first over `x`. -/
theorem andersonK_eq {α β γ : ℂ} {p : (Fin (n + 1) → ℝ) × (Fin n → ℝ)} (hp : p ∈ kRegion n) :
    andersonK n α β γ p = vandermondeC p.2 * dixonIntegrand (andersonNodes p.2)
      (andersonS n α β γ) p.1 := by
  obtain ⟨x, y⟩ := p
  have hx := hp.1.1
  simp only [andersonK, dixonIntegrand, jacobiWeight, vandermondeC]
  have hrow : ∀ i : Fin (n + 1), ∏ j : Fin (n + 2), ((|x i - andersonNodes y j| : ℝ) : ℂ) ^
      (andersonS n α β γ j - 1) = ((x i : ℂ) ^ (α - 1) * ((1 - x i : ℝ) : ℂ) ^ (β - 1)) *
        ∏ k : Fin n, ((|y k - x i| : ℝ) : ℂ) ^ (γ - 1) := fun i => by
    rw [Fin.prod_univ_succ, Fin.prod_univ_castSucc]
    simp only [andersonNodes_zero, andersonS_zero, andersonNodes_succ_castSucc,
      andersonS_succ_castSucc, andersonS_succ_last, andersonNodes_succ_last, sub_zero]
    rw [abs_of_pos (hx i).1, abs_sub_comm, abs_of_pos (by linarith [(hx i).2])]
    have : ∀ k : Fin n, |x i - y k| = |y k - x i| := fun k => abs_sub_comm _ _
    simp_rw [this]
    ring
  simp_rw [hrow, prod_mul_distrib]
  rw [prod_comm (s := (univ : Finset (Fin (n + 1)))) (t := (univ : Finset (Fin n)))]
  ring

/-! ### Products over pairs -/

theorem prod_Ioi_eq_prod_ite {M : Type*} [CommMonoid M] {m : ℕ} (i : Fin m) (g : Fin m → M) :
    ∏ k ∈ Ioi i, g k = ∏ k, if i < k then g k else 1 := by
  rw [← prod_filter]; congr 1; ext k; simp

/-- Splitting off the first index of `∏_{i<k}`. -/
theorem prod_pairs_succ {M : Type*} [CommMonoid M] {m : ℕ} (h : Fin (m + 1) → Fin (m + 1) → M) :
    ∏ i, ∏ k ∈ Ioi i, h i k =
      (∏ k : Fin m, h 0 k.succ) * ∏ i : Fin m, ∏ k ∈ Ioi i, h i.succ k.succ := by
  rw [Fin.prod_univ_succ]
  congr 1
  · rw [prod_Ioi_eq_prod_ite, Fin.prod_univ_succ]
    simp [Fin.succ_pos]
  · refine prod_congr rfl fun i _ => ?_
    rw [prod_Ioi_eq_prod_ite, prod_Ioi_eq_prod_ite, Fin.prod_univ_succ]
    simp [Fin.succ_lt_succ_iff]

/-- Splitting off the last index of `∏_{i<k}`. -/
theorem prod_pairs_castSucc {M : Type*} [CommMonoid M] {m : ℕ}
    (h : Fin (m + 1) → Fin (m + 1) → M) :
    ∏ i, ∏ k ∈ Ioi i, h i k =
      (∏ j : Fin m, ∏ k ∈ Ioi j, h j.castSucc k.castSucc) *
        ∏ j : Fin m, h j.castSucc (Fin.last m) := by
  have hlast : Ioi (Fin.last m) = ∅ := by ext k; simp [Fin.le_last]
  rw [Fin.prod_univ_castSucc, hlast, prod_empty, mul_one, ← prod_mul_distrib]
  refine prod_congr rfl fun j _ => ?_
  rw [prod_Ioi_eq_prod_ite, prod_Ioi_eq_prod_ite, Fin.prod_univ_castSucc]
  simp only [Fin.castSucc_lt_castSucc_iff, Fin.castSucc_lt_last, ↓reduceIte]

/-! ### The inner integrals -/

/-- The ordered Selberg integrand `∏ xᵢ^{α−1}(1 − xᵢ)^{β−1} ∏_{i<j}(xᵢ − xⱼ)^{2γ}`. -/
noncomputable def selbergOrdF {m : ℕ} (α β γ : ℂ) (x : Fin m → ℝ) : ℂ :=
  jacobiWeight α β x * ∏ i, ∏ j ∈ Ioi i, ((x i - x j : ℝ) : ℂ) ^ (2 * γ)

theorem orderedOpen_strictAnti {m : ℕ} {x : Fin m → ℝ} (hx : x ∈ orderedOpen m) : StrictAnti x :=
  fun i j hij => hx.2 i j hij

theorem vandermonde_mul_pow {m : ℕ} {x : Fin m → ℝ} (hx : x ∈ orderedOpen m) (γ : ℂ) :
    vandermondeC x * ∏ i, ∏ k ∈ Ioi i, ((x i - x k : ℝ) : ℂ) ^ (γ + γ - 1) =
      ∏ i, ∏ k ∈ Ioi i, ((x i - x k : ℝ) : ℂ) ^ (2 * γ) := by
  rw [vandermondeC, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  rw [← prod_mul_distrib]
  refine prod_congr rfl fun k hk => ?_
  have hpos : (0 : ℝ) < x i - x k := sub_pos.mpr (hx.2 i k (mem_Ioi.mp hk))
  have h0 : ((x i - x k : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpos.ne'
  rw [show 2 * γ = 1 + (γ + γ - 1) by ring, Complex.cpow_add _ _ h0, Complex.cpow_one]

/-- Integrating over `y` first. -/
theorem integral_y_andersonK {α β γ : ℂ} (hγ : 0 < γ.re) {x : Fin (n + 1) → ℝ}
    (hx : x ∈ orderedOpen (n + 1)) :
    ∫ y in dixonRegion x, andersonK n α β γ (x, y) =
      Complex.Gamma γ ^ (n + 1) / Complex.Gamma ((n + 1 : ℕ) * γ) * selbergOrdF α β γ x := by
  simp only [andersonK]
  rw [MeasureTheory.integral_const_mul, dixon_anderson (orderedOpen_strictAnti hx) _
    (fun _ => hγ), prod_const, card_univ, Fintype.card_fin, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul, selbergOrdF, ← vandermonde_mul_pow hx γ, dixonConst]
  ring

theorem dixonConst_anderson (y : Fin n → ℝ) (α β γ : ℂ) :
    dixonConst (andersonNodes y) (andersonS n α β γ) =
      jacobiWeight (α + γ) (β + γ) y * ∏ i, ∏ k ∈ Ioi i, ((y i - y k : ℝ) : ℂ) ^ (γ + γ - 1) := by
  rw [dixonConst, prod_pairs_succ, Fin.prod_univ_castSucc, prod_pairs_castSucc]
  simp only [andersonNodes_zero, andersonS_zero, andersonNodes_succ_castSucc,
    andersonS_succ_castSucc, andersonS_succ_last, andersonNodes_succ_last, sub_zero]
  rw [Complex.ofReal_one, Complex.one_cpow, mul_one, jacobiWeight,
    prod_mul_distrib]
  have e1 : ∏ x : Fin n, ((1 - y x : ℝ) : ℂ) ^ (β + γ - 1) =
      ∏ i : Fin n, ((1 - y i : ℝ) : ℂ) ^ (β + γ - 1) := rfl
  have e2 : ∏ j : Fin n, ((y j : ℝ) : ℂ) ^ (γ + α - 1) = ∏ i : Fin n, (y i : ℂ) ^ (α + γ - 1) :=
    prod_congr rfl fun j _ => by rw [add_comm γ α]
  rw [e2]
  ring

/-- Integrating over `x` first. -/
theorem integral_x_andersonK {α β γ : ℂ} (hα : 0 < α.re) (hβ : 0 < β.re) (hγ : 0 < γ.re)
    {y : Fin n → ℝ} (hy : y ∈ orderedOpen n) :
    ∫ x in dixonRegion (andersonNodes y), andersonK n α β γ (x, y) =
      Complex.Gamma β * Complex.Gamma γ ^ n * Complex.Gamma α /
        Complex.Gamma (β + (n * γ + α)) * selbergOrdF (α + γ) (β + γ) γ y := by
  have hS : ∀ j, 0 < (andersonS n α β γ j).re := fun j => by
    induction j using Fin.cases with
    | zero => exact hβ
    | succ j =>
      induction j using Fin.lastCases with
      | last => rw [andersonS_succ_last]; exact hα
      | cast k => rw [andersonS_succ_castSucc]; exact hγ
  rw [MeasureTheory.setIntegral_congr_fun (isOpen_dixonRegion _).measurableSet
    (fun x hx => andersonK_eq (mem_kRegion_iff.mpr ⟨hy, hx⟩))]
  dsimp only
  rw [MeasureTheory.integral_const_mul,
    dixon_anderson (andersonNodes_strictAnti hy) _ hS, dixonConst_anderson y, selbergOrdF,
    ← vandermonde_mul_pow hy γ, Fin.prod_univ_succ, Fin.prod_univ_castSucc, Fin.sum_univ_succ,
    Fin.sum_univ_castSucc]
  simp only [andersonS_zero, andersonS_succ_castSucc, andersonS_succ_last, prod_const, card_univ,
    Fintype.card_fin, sum_const, nsmul_eq_mul]
  ring

/-! ### Norms: complex parameters are dominated by their real parts -/

theorem norm_ofReal_cpow_re {r : ℝ} (hr : 0 < r) (w : ℂ) :
    ‖(r : ℂ) ^ w‖ = ‖(r : ℂ) ^ ((w.re : ℝ) : ℂ)‖ := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hr, Complex.norm_cpow_eq_rpow_re_of_pos hr,
    Complex.ofReal_re]

/-- On the region, `‖K(α, β, γ)‖ = ‖K(ℜα, ℜβ, ℜγ)‖`. -/
theorem norm_andersonK_re {α β γ : ℂ} {p : (Fin (n + 1) → ℝ) × (Fin n → ℝ)}
    (hp : p ∈ kRegion n) :
    ‖andersonK n α β γ p‖ = ‖andersonK n (α.re : ℂ) (β.re : ℂ) (γ.re : ℂ) p‖ := by
  obtain ⟨x, y⟩ := p
  have hx := hp.1.1
  have hy := hp.2
  have hxy : ∀ (i : Fin n) (j : Fin (n + 1)), 0 < |y i - x j| := fun i j =>
    abs_pos.mpr (sub_ne_zero.mpr fun h => node_ne_point (orderedOpen_strictAnti hp.1) hy j i h.symm)
  simp only [andersonK, jacobiWeight, dixonIntegrand, norm_mul, norm_prod]
  congr 1
  · congr 1
    refine prod_congr rfl fun i _ => ?_
    rw [norm_ofReal_cpow_re (hx i).1, norm_ofReal_cpow_re (show (0 : ℝ) < 1 - x i by
      linarith [(hx i).2]) (β - 1), norm_ofReal_cpow_re (hx i).1 ((α.re : ℂ) - 1),
      norm_ofReal_cpow_re (show (0 : ℝ) < 1 - x i by linarith [(hx i).2]) ((β.re : ℂ) - 1)]
    simp
  · congr 1
    refine prod_congr rfl fun i _ => prod_congr rfl fun j _ => ?_
    rw [norm_ofReal_cpow_re (hxy i j), norm_ofReal_cpow_re (hxy i j) ((γ.re : ℂ) - 1)]
    simp

section ComplexOrder

open scoped ComplexOrder

theorem cpow_real_nonneg {r : ℝ} (hr : 0 < r) (t : ℝ) : 0 ≤ (r : ℂ) ^ (t : ℂ) := by
  rw [← Complex.ofReal_cpow hr.le]; exact Complex.zero_le_real.mpr (Real.rpow_nonneg hr.le t)

/-- With real parameters the integrand is a nonnegative real number. -/
theorem andersonK_real_nonneg {a b c : ℝ} {p : (Fin (n + 1) → ℝ) × (Fin n → ℝ)}
    (hp : p ∈ kRegion n) : 0 ≤ andersonK n a b c p := by
  obtain ⟨x, y⟩ := p
  have hx : ∀ i, 0 < x i ∧ x i < 1 := hp.1.1
  have hxo : ∀ i j, i < j → x j < x i := hp.1.2
  have hy : y ∈ dixonRegion x := hp.2
  have hxa : StrictAnti x := fun i j h => hxo i j h
  have hxy : ∀ (i : Fin n) (j : Fin (n + 1)), 0 < |y i - x j| := fun i j =>
    abs_pos.mpr (sub_ne_zero.mpr fun h => node_ne_point hxa hy j i h.symm)
  have e : ∀ t : ℝ, (t : ℂ) - 1 = ((t - 1 : ℝ) : ℂ) := fun t => by push_cast; ring
  simp only [andersonK, jacobiWeight, dixonIntegrand, vandermondeC, e]
  refine mul_nonneg (mul_nonneg (prod_nonneg fun i _ => mul_nonneg
    (cpow_real_nonneg (hx i).1 _) (cpow_real_nonneg (by linarith [(hx i).2]) _))
    (prod_nonneg fun i _ => prod_nonneg fun j hj => Complex.zero_le_real.mpr
      (sub_pos.mpr (hxo i j (mem_Ioi.mp hj))).le))
    (mul_nonneg (prod_nonneg fun i _ => prod_nonneg fun j hj => Complex.zero_le_real.mpr
      (sub_pos.mpr (point_order hxa hy (mem_Ioi.mp hj))).le)
    (prod_nonneg fun i _ => prod_nonneg fun j _ => cpow_real_nonneg (hxy i j) _))

theorem andersonK_real_eq_norm {a b c : ℝ} {p : (Fin (n + 1) → ℝ) × (Fin n → ℝ)}
    (hp : p ∈ kRegion n) : andersonK n a b c p = (‖andersonK n a b c p‖ : ℂ) :=
  Complex.eq_coe_norm_of_nonneg (andersonK_real_nonneg hp)

end ComplexOrder

/-! ### Measurability -/

open MeasureTheory

theorem measurableSet_orderedOpen (m : ℕ) : MeasurableSet (orderedOpen m) := by
  have : orderedOpen m = (⋂ i, {x : Fin m → ℝ | 0 < x i ∧ x i < 1}) ∩
      ⋂ i, ⋂ j, {x : Fin m → ℝ | i < j → x j < x i} := by
    ext x; simp [orderedOpen]
  rw [this]
  refine (MeasurableSet.iInter fun i =>
    (measurableSet_lt measurable_const (measurable_pi_apply i)).inter
    (measurableSet_lt (measurable_pi_apply i) measurable_const)).inter
    (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_)
  by_cases h : i < j
  · simp only [h, true_implies]
    exact measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply i)
  · simp [h]

theorem measurableSet_kRegion (n : ℕ) : MeasurableSet (kRegion n) := by
  have : kRegion n = (Prod.fst ⁻¹' orderedOpen (n + 1)) ∩
      ⋂ i : Fin n, {p : (Fin (n + 1) → ℝ) × (Fin n → ℝ) |
        p.1 i.succ < p.2 i ∧ p.2 i < p.1 i.castSucc} := by
    ext p; simp [kRegion, dixonRegion]
  rw [this]
  refine (measurable_fst (measurableSet_orderedOpen _)).inter (MeasurableSet.iInter fun i => ?_)
  exact (measurableSet_lt (f := fun p : (Fin (n + 1) → ℝ) × (Fin n → ℝ) => p.1 i.succ)
    (g := fun p => p.2 i) (by fun_prop) (by fun_prop)).inter
    (measurableSet_lt (f := fun p : (Fin (n + 1) → ℝ) × (Fin n → ℝ) => p.2 i)
    (g := fun p => p.1 i.castSucc) (by fun_prop) (by fun_prop))

theorem measurable_andersonK (α β γ : ℂ) : Measurable (andersonK n α β γ) := by
  unfold andersonK jacobiWeight vandermondeC dixonIntegrand; fun_prop

theorem measurable_selbergOrdF {m : ℕ} (α β γ : ℂ) : Measurable (selbergOrdF (m := m) α β γ) := by
  unfold selbergOrdF jacobiWeight; fun_prop

/-! ### The recursion -/

theorem andersonK_slice_x {α β γ : ℂ} (x : Fin (n + 1) → ℝ) (y : Fin n → ℝ) :
    (kRegion n).indicator (andersonK n α β γ) (x, y) =
      (orderedOpen (n + 1)).indicator (fun x => (dixonRegion x).indicator
        (fun y => andersonK n α β γ (x, y)) y) x := by
  by_cases hx : x ∈ orderedOpen (n + 1)
  · rw [Set.indicator_of_mem hx]
    by_cases hy : y ∈ dixonRegion x
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (show (x, y) ∈ kRegion n from ⟨hx, hy⟩)]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem (fun h => hy h.2)]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx h.1)]

theorem andersonK_slice_y {α β γ : ℂ} (x : Fin (n + 1) → ℝ) (y : Fin n → ℝ) :
    (kRegion n).indicator (andersonK n α β γ) (x, y) =
      (orderedOpen n).indicator (fun y => (dixonRegion (andersonNodes y)).indicator
        (fun x => vandermondeC y * dixonIntegrand (andersonNodes y) (andersonS n α β γ) x) x)
          y := by
  by_cases hy : y ∈ orderedOpen n
  · rw [Set.indicator_of_mem hy]
    by_cases hx : x ∈ dixonRegion (andersonNodes y)
    · have hp : (x, y) ∈ kRegion n := mem_kRegion_iff.mpr ⟨hy, hx⟩
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hp, andersonK_eq hp]
    · rw [Set.indicator_of_notMem hx,
        Set.indicator_of_notMem (fun h => hx (mem_kRegion_iff.mp h).2)]
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem (fun h => hy (mem_kRegion_iff.mp h).1)]

theorem integral_slice_x {α β γ : ℂ} (hγ : 0 < γ.re) (x : Fin (n + 1) → ℝ) :
    ∫ y, (kRegion n).indicator (andersonK n α β γ) (x, y) =
      (orderedOpen (n + 1)).indicator (fun x => Complex.Gamma γ ^ (n + 1) /
        Complex.Gamma ((n + 1 : ℕ) * γ) * selbergOrdF α β γ x) x := by
  simp only [andersonK_slice_x]
  by_cases hx : x ∈ orderedOpen (n + 1)
  · simp only [Set.indicator_of_mem hx]
    rw [integral_indicator (isOpen_dixonRegion x).measurableSet, integral_y_andersonK hγ hx]
  · simp only [Set.indicator_of_notMem hx, integral_zero]

theorem integral_slice_y {α β γ : ℂ} (hα : 0 < α.re) (hβ : 0 < β.re) (hγ : 0 < γ.re)
    (y : Fin n → ℝ) :
    ∫ x, (kRegion n).indicator (andersonK n α β γ) (x, y) =
      (orderedOpen n).indicator (fun y => Complex.Gamma β * Complex.Gamma γ ^ n *
        Complex.Gamma α / Complex.Gamma (β + (n * γ + α)) * selbergOrdF (α + γ) (β + γ) γ y) y := by
  by_cases hy : y ∈ orderedOpen n
  · rw [Set.indicator_of_mem hy, ← integral_x_andersonK hα hβ hγ hy,
      ← integral_indicator (isOpen_dixonRegion _).measurableSet]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    dsimp only
    by_cases hx : x ∈ dixonRegion (andersonNodes y)
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show (x, y) ∈ kRegion n from
        mem_kRegion_iff.mpr ⟨hy, hx⟩)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show (x, y) ∉ kRegion n from
        fun h => hx (mem_kRegion_iff.mp h).2)]
  · rw [Set.indicator_of_notMem hy]
    refine (integral_congr_ae (ae_of_all _ fun x => ?_)).trans (integral_zero _ ℂ)
    exact Set.indicator_of_notMem (show (x, y) ∉ kRegion n from
      fun h => hy (mem_kRegion_iff.mp h).1) _

/-- **Anderson's recursion** for the ordered Selberg integral. -/
theorem anderson_recursion {α β γ : ℂ} (hα : 0 < α.re) (hβ : 0 < β.re) (hγ : 0 < γ.re)
    (hintR : IntegrableOn (selbergOrdF (((α + γ).re : ℝ) : ℂ) (((β + γ).re : ℝ) : ℂ)
      ((γ.re : ℝ) : ℂ)) (orderedOpen n)) :
    IntegrableOn (selbergOrdF α β γ) (orderedOpen (n + 1)) ∧
      Complex.Gamma γ ^ (n + 1) / Complex.Gamma ((n + 1 : ℕ) * γ) *
          ∫ x in orderedOpen (n + 1), selbergOrdF α β γ x =
        Complex.Gamma β * Complex.Gamma γ ^ n * Complex.Gamma α /
          Complex.Gamma (β + (n * γ + α)) *
            ∫ y in orderedOpen n, selbergOrdF (α + γ) (β + γ) γ y := by
  set F := (kRegion n).indicator (andersonK n α β γ)
  set c₁ := Complex.Gamma γ ^ (n + 1) / Complex.Gamma ((n + 1 : ℕ) * γ)
  set c₂ := Complex.Gamma β * Complex.Gamma γ ^ n * Complex.Gamma α /
    Complex.Gamma (β + (n * γ + α))
  set α' : ℂ := ((α.re : ℝ) : ℂ)
  set β' : ℂ := ((β.re : ℝ) : ℂ)
  set γ' : ℂ := ((γ.re : ℝ) : ℂ)
  have hα' : 0 < α'.re := by simpa [α'] using hα
  have hβ' : 0 < β'.re := by simpa [β'] using hβ
  have hγ' : 0 < γ'.re := by simpa [γ'] using hγ
  set c₂' := Complex.Gamma β' * Complex.Gamma γ' ^ n * Complex.Gamma α' /
    Complex.Gamma (β' + (n * γ' + α'))
  have hFm : AEStronglyMeasurable F (volume.prod volume) :=
    ((measurable_andersonK α β γ).indicator (measurableSet_kRegion n)).aestronglyMeasurable
  -- the inner `x`-integral of the norm
  have hnormx : ∀ y ∈ orderedOpen n, ∫ x, ‖F (x, y)‖ =
      (c₂' * selbergOrdF (α' + γ') (β' + γ') γ' y).re := by
    intro y hy
    have h1 : (fun x => ‖F (x, y)‖) = (dixonRegion (andersonNodes y)).indicator
        (fun x => ‖andersonK n α' β' γ' (x, y)‖) := by
      funext x
      by_cases hx : x ∈ dixonRegion (andersonNodes y)
      · have hp : (x, y) ∈ kRegion n := mem_kRegion_iff.mpr ⟨hy, hx⟩
        rw [Set.indicator_of_mem hx, show F (x, y) = andersonK n α β γ (x, y) from
          Set.indicator_of_mem hp _, norm_andersonK_re hp]
      · rw [Set.indicator_of_notMem hx, show F (x, y) = 0 from
          Set.indicator_of_notMem (fun h => hx (mem_kRegion_iff.mp h).2) _, norm_zero]
    rw [h1, integral_indicator (isOpen_dixonRegion _).measurableSet,
      ← integral_x_andersonK hα' hβ' hγ' hy]
    have h2 : ∫ x in dixonRegion (andersonNodes y), andersonK n α' β' γ' (x, y) =
        ((∫ x in dixonRegion (andersonNodes y), ‖andersonK n α' β' γ' (x, y)‖ : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      exact setIntegral_congr_fun (isOpen_dixonRegion _).measurableSet fun x hx =>
        andersonK_real_eq_norm (mem_kRegion_iff.mpr ⟨hy, hx⟩)
    rw [h2, Complex.ofReal_re]
  -- integrability of `F`
  have hFi : Integrable F (volume.prod volume) := by
    rw [integrable_prod_iff' hFm]
    constructor
    · refine ae_of_all _ fun y => ?_
      simp_rw [F, andersonK_slice_y]
      by_cases hy : y ∈ orderedOpen n
      · simp only [Set.indicator_of_mem hy]
        exact (integrable_indicator_iff (isOpen_dixonRegion _).measurableSet).mpr
          ((integrableOn_dixonIntegrand (andersonNodes_strictAnti hy) _ fun j => by
            induction j using Fin.cases with
            | zero => exact hβ
            | succ j =>
              induction j using Fin.lastCases with
              | last => rw [andersonS_succ_last]; exact hα
              | cast k => rw [andersonS_succ_castSucc]; exact hγ).const_mul _)
      · simp only [Set.indicator_of_notMem hy]; exact integrable_zero _ _ _
    · have hR : IntegrableOn (fun y => (c₂' * selbergOrdF (α' + γ') (β' + γ') γ' y).re)
          (orderedOpen n) := by
        have : selbergOrdF (m := n) (α' + γ') (β' + γ') γ' = selbergOrdF (((α + γ).re : ℝ) : ℂ)
            (((β + γ).re : ℝ) : ℂ) ((γ.re : ℝ) : ℂ) := by
          simp only [α', β', γ', Complex.add_re]; push_cast; rfl
        rw [this]
        exact (hintR.const_mul c₂').re
      refine ((integrable_indicator_iff (measurableSet_orderedOpen n)).mpr hR).congr
        (ae_of_all _ fun y => ?_)
      by_cases hy : y ∈ orderedOpen n
      · rw [Set.indicator_of_mem hy]
        dsimp only
        rw [hnormx y hy]
      · simp only [Set.indicator_of_notMem hy]
        rw [show (fun x => ‖F (x, y)‖) = fun _ => 0 from funext fun x => by
          simp only [F, andersonK_slice_y, Set.indicator_of_notMem hy, norm_zero], integral_zero]
  -- integrating over `y` first
  have hW1 : ∫ p, F p ∂(volume.prod volume) =
      c₁ * ∫ x in orderedOpen (n + 1), selbergOrdF α β γ x := by
    rw [integral_prod F hFi, ← integral_const_mul,
      ← integral_indicator (measurableSet_orderedOpen _)]
    exact integral_congr_ae (ae_of_all _ fun x => integral_slice_x hγ x)
  -- integrating over `x` first
  have hW2 : ∫ p, F p ∂(volume.prod volume) =
      c₂ * ∫ y in orderedOpen n, selbergOrdF (α + γ) (β + γ) γ y := by
    rw [integral_prod_symm F hFi, ← integral_const_mul,
      ← integral_indicator (measurableSet_orderedOpen _)]
    exact integral_congr_ae (ae_of_all _ fun y => integral_slice_y hα hβ hγ y)
  -- integrability of the `(n+1)`-point integrand
  have hc₁ : c₁ ≠ 0 := div_ne_zero (pow_ne_zero _ (Complex.Gamma_ne_zero_of_re_pos hγ))
    (Complex.Gamma_ne_zero_of_re_pos (by simp; positivity))
  have hI : IntegrableOn (selbergOrdF α β γ) (orderedOpen (n + 1)) := by
    obtain ⟨-, hFx⟩ := (integrable_prod_iff hFm).mp hFi
    rw [← integrable_indicator_iff (measurableSet_orderedOpen _)]
    refine (hFx.const_mul ‖c₁‖⁻¹).mono' ((measurable_selbergOrdF α β γ).indicator
      (measurableSet_orderedOpen _)).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    by_cases hx : x ∈ orderedOpen (n + 1)
    · rw [Set.indicator_of_mem hx]
      have h1 : ∫ y, F (x, y) = c₁ * selbergOrdF α β γ x := by
        rw [integral_slice_x hγ x, Set.indicator_of_mem hx]
      have h2 := norm_integral_le_integral_norm (μ := volume) (fun y => F (x, y))
      rw [h1, norm_mul] at h2
      rw [le_inv_mul_iff₀ (norm_pos_iff.mpr hc₁)]
      exact h2
    · rw [Set.indicator_of_notMem hx, norm_zero]
      exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (integral_nonneg fun y => norm_nonneg _)
  exact ⟨hI, hW1.symm.trans hW2⟩

/-! ### The closed form -/

/-- `∏_{j<m} Γ(α + jγ)Γ(β + jγ)Γ(1 + (j+1)γ) / (Γ(α + β + (m + j − 1)γ) Γ(1 + γ)) / m!`. -/
noncomputable def osClosed (m : ℕ) (α β γ : ℂ) : ℂ :=
  (∏ j ∈ range m, Complex.Gamma (α + j * γ)) * (∏ j ∈ range m, Complex.Gamma (β + j * γ)) *
    (∏ j ∈ range m, Complex.Gamma (1 + (j + 1) * γ)) /
    ((∏ j ∈ range m, Complex.Gamma (α + β + (m + j - 1) * γ)) * Complex.Gamma (1 + γ) ^ m *
      (m.factorial : ℂ))

theorem Gamma_ne_zero_of_re {z : ℂ} (hz : 0 < z.re) : Complex.Gamma z ≠ 0 :=
  Complex.Gamma_ne_zero_of_re_pos hz

/-- The closed form satisfies Anderson's recursion. -/
theorem osClosed_succ {α β γ : ℂ} (hα : 0 < α.re) (hβ : 0 < β.re) (hγ : 0 < γ.re) :
    Complex.Gamma γ ^ (n + 1) / Complex.Gamma ((n + 1 : ℕ) * γ) * osClosed (n + 1) α β γ =
      Complex.Gamma β * Complex.Gamma γ ^ n * Complex.Gamma α /
        Complex.Gamma (β + (n * γ + α)) * osClosed n (α + γ) (β + γ) γ := by
  have hre : ∀ (j : ℕ) (z : ℂ), 0 < z.re → 0 < (z + j * γ).re := fun j z hz => by
    simp; positivity
  have hn1 : ((n + 1 : ℕ) : ℂ) * γ ≠ 0 := mul_ne_zero (by exact_mod_cast Nat.succ_ne_zero n)
    (fun h => by rw [h] at hγ; simp at hγ)
  have hγ0 : γ ≠ 0 := fun h => by rw [h] at hγ; simp at hγ
  have hG1 : Complex.Gamma (1 + ((n + 1 : ℕ) : ℂ) * γ) =
      ((n + 1 : ℕ) : ℂ) * γ * Complex.Gamma (((n + 1 : ℕ) : ℂ) * γ) := by
    rw [add_comm, Complex.Gamma_add_one _ hn1]
  have hG2 : Complex.Gamma (1 + γ) = γ * Complex.Gamma γ := by
    rw [add_comm, Complex.Gamma_add_one _ hγ0]
  simp only [osClosed]
  rw [prod_range_succ' (fun j => Complex.Gamma (α + j * γ)),
    prod_range_succ' (fun j => Complex.Gamma (β + j * γ)),
    prod_range_succ (fun j => Complex.Gamma (1 + (j + 1) * γ)),
    prod_range_succ' (fun j => Complex.Gamma (α + β + ((n + 1 : ℕ) + j - 1) * γ))]
  have e1 : ∀ j : ℕ, Complex.Gamma (α + ((j + 1 : ℕ) : ℂ) * γ) = Complex.Gamma (α + γ + j * γ) :=
    fun j => by congr 1; push_cast; ring
  have e2 : ∀ j : ℕ, Complex.Gamma (β + ((j + 1 : ℕ) : ℂ) * γ) = Complex.Gamma (β + γ + j * γ) :=
    fun j => by congr 1; push_cast; ring
  have e3 : ∀ j : ℕ, Complex.Gamma (α + β + (((n + 1 : ℕ) : ℂ) + ((j + 1 : ℕ) : ℂ) - 1) * γ) =
      Complex.Gamma (α + γ + (β + γ) + ((n : ℂ) + j - 1) * γ) := fun j => by
        congr 1; push_cast; ring
  simp_rw [e1, e2, e3]
  have e4 : Complex.Gamma (α + β + (((n + 1 : ℕ) : ℂ) + ((0 : ℕ) : ℂ) - 1) * γ) =
      Complex.Gamma (β + (n * γ + α)) := by congr 1; push_cast; ring
  have e5 : (n : ℂ) + 1 = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
  rw [e4]
  simp only [Nat.cast_zero, zero_mul, add_zero, e5, hG1, hG2]
  have hP1 : ∏ j ∈ range n, Complex.Gamma (α + γ + (β + γ) + ((n : ℂ) + j - 1) * γ) ≠ 0 :=
    prod_ne_zero_iff.mpr fun j _ => Gamma_ne_zero_of_re (by
      have : (0 : ℝ) ≤ ((n : ℝ) + j - 1) * γ.re + γ.re := by
        have : (1 : ℝ) ≤ n + j + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n),
          (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
        nlinarith
      simp; nlinarith)
  have hGa := Gamma_ne_zero_of_re hα
  have hGb := Gamma_ne_zero_of_re hβ
  have hGg := Gamma_ne_zero_of_re hγ
  have hGn := Gamma_ne_zero_of_re (show 0 < (((n + 1 : ℕ) : ℂ) * γ).re by simp; positivity)
  have hGs := Gamma_ne_zero_of_re (show 0 < (β + (n * γ + α)).re by simp; positivity)
  set G := Complex.Gamma (((n + 1 : ℕ) : ℂ) * γ)
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- **The ordered Selberg integral** for `ℜα, ℜβ, ℜγ > 0`:
`∫_{1>x₁>⋯>xₘ>0} ∏ xᵢ^{α−1}(1 − xᵢ)^{β−1} ∏_{i<j}(xᵢ − xⱼ)^{2γ} dx = osClosed m α β γ`. -/
theorem ordered_selberg (m : ℕ) : ∀ α β γ : ℂ, 0 < α.re → 0 < β.re → 0 < γ.re →
    IntegrableOn (selbergOrdF α β γ) (orderedOpen m) ∧
      ∫ x in orderedOpen m, selbergOrdF α β γ x = osClosed m α β γ := by
  induction m with
  | zero =>
    intro α β γ _ _ _
    have h1 : ∀ x : Fin 0 → ℝ, selbergOrdF α β γ x = 1 := fun x => by
      simp [selbergOrdF, jacobiWeight]
    have hU : orderedOpen 0 = Set.univ := by ext x; simp [orderedOpen]
    refine ⟨?_, ?_⟩
    · rw [show selbergOrdF (m := 0) α β γ = fun _ => 1 from funext h1, hU]
      exact integrableOn_const (by simp) |>.mono_set (Set.subset_univ _)
    · simp_rw [h1, hU]
      rw [setIntegral_const, measureReal_def, volume_pi, Measure.pi_univ]
      simp [osClosed]
  | succ n ih =>
    intro α β γ hα hβ hγ
    have hR := ih (((α + γ).re : ℝ) : ℂ) (((β + γ).re : ℝ) : ℂ) ((γ.re : ℝ) : ℂ)
      (by simp; linarith) (by simp; linarith) (by simpa using hγ)
    obtain ⟨hI, heq⟩ := anderson_recursion hα hβ hγ hR.1
    refine ⟨hI, ?_⟩
    have hval := (ih (α + γ) (β + γ) γ (by simp; linarith) (by simp; linarith) hγ).2
    rw [hval, ← osClosed_succ hα hβ hγ] at heq
    have hc₁ : Complex.Gamma γ ^ (n + 1) / Complex.Gamma ((n + 1 : ℕ) * γ) ≠ 0 :=
      div_ne_zero (pow_ne_zero _ (Gamma_ne_zero_of_re hγ)) (Gamma_ne_zero_of_re (by
        simp; positivity))
    exact mul_left_cancel₀ hc₁ heq

end Azurite.DLMF
