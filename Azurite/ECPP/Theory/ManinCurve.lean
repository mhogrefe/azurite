/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.ECPP.Theory.Hasse
import Azurite.ECPP.Theory.ManinHeight

/-!
# Manin's proof of the Hasse bound: the curve over the function field

After Knapp, *Elliptic Curves*, §X.3.  For `E : y² = x³ + ax + b` over a field `F` the cubic
(10.13) over `F(x)`, `λ Y² = X³ + aX + b` with `λ = x³ + ax + b`, is here in Weierstrass form:

  `twist a b : y′² = x′³ + aλ² x′ + bλ³`,  `x′ = λX`, `y′ = λ²Y`,

so that Mathlib's group law applies.  `basePt` is the point `(x, 1)`, i.e. `(λx, λ²)`;
`ptX Z = x′/λ` is Knapp's `X`-coordinate of a point and `ptHeight Z` its height (`0` at the
point at infinity).

* `twist_sum_prod`: the identities (10.19), (10.20) for the coordinates of `Z ± (x, 1)`, as
  identities in a field.
* `rfHeight_div_of_coprime`: the height of a quotient of coprime polynomials.
-/

namespace Azurite.ECPP.Manin

open Polynomial WeierstrassCurve

section Identities

variable {K : Type*} [Field K]

/-- **Knapp's (10.20) and (10.19)**: the product and the sum of the `X`-coordinates of
`Z + (x, 1)` and `Z − (x, 1)` in terms of that of `Z = (x′, y′)`, on the curve
`y′² = x′³ + aλ² x′ + bλ³`, `λ = t³ + at + b`. -/
theorem twist_sum_prod {a b t lam x' y' : K} (hlam : lam = t ^ 3 + a * t + b) (hlam0 : lam ≠ 0)
    (hx : x' ≠ lam * t) (hE : y' ^ 2 = x' ^ 3 + a * lam ^ 2 * x' + b * lam ^ 3) :
    ((((y' - lam ^ 2) / (x' - lam * t)) ^ 2 - x' - lam * t) / lam) *
        ((((y' + lam ^ 2) / (x' - lam * t)) ^ 2 - x' - lam * t) / lam)
      = ((x' / lam * t - a) ^ 2 - 4 * b * (t + x' / lam)) / (x' / lam - t) ^ 2 ∧
    ((((y' - lam ^ 2) / (x' - lam * t)) ^ 2 - x' - lam * t) / lam) +
        ((((y' + lam ^ 2) / (x' - lam * t)) ^ 2 - x' - lam * t) / lam)
      = 2 * (x' / lam * t ^ 2 + (x' / lam) ^ 2 * t + a * t + 2 * b + a * (x' / lam)) /
        (x' / lam - t) ^ 2 := by
  have hb : b = lam - t ^ 3 - a * t := by rw [hlam]; ring
  have hd : x' - lam * t ≠ 0 := sub_ne_zero.mpr hx
  have hd2 : x' / lam - t ≠ 0 := by
    intro h0
    apply hd
    have : x' = t * lam := by
      field_simp at h0
      linear_combination h0
    rw [this]
    ring
  have hS : ((y' - lam ^ 2) / (x' - lam * t)) ^ 2 + ((y' + lam ^ 2) / (x' - lam * t)) ^ 2
      = (2 * (x' ^ 3 + a * lam ^ 2 * x' + b * lam ^ 3) + 2 * lam ^ 4) / (x' - lam * t) ^ 2 := by
    field_simp
    linear_combination 2 * hE
  have hPr : ((y' - lam ^ 2) / (x' - lam * t)) ^ 2 * ((y' + lam ^ 2) / (x' - lam * t)) ^ 2
      = ((x' ^ 3 + a * lam ^ 2 * x' + b * lam ^ 3) - lam ^ 4) ^ 2 / (x' - lam * t) ^ 4 := by
    field_simp
    linear_combination
      (y' ^ 2 + (x' ^ 3 + a * lam ^ 2 * x' + b * lam ^ 3) - 2 * lam ^ 4) * hE
  obtain ⟨p, hp⟩ : ∃ p, p = ((y' - lam ^ 2) / (x' - lam * t)) ^ 2 := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, m = ((y' + lam ^ 2) / (x' - lam * t)) ^ 2 := ⟨_, rfl⟩
  rw [← hp, ← hm] at hS hPr ⊢
  have hd3 : x' - t * lam ≠ 0 := by rwa [mul_comm]
  constructor
  · have e : (p - x' - lam * t) / lam * ((m - x' - lam * t) / lam)
        = (p * m - (p + m) * (x' + lam * t) + (x' + lam * t) ^ 2) / lam ^ 2 := by
      field_simp
      ring
    rw [e, hPr, hS, hb]
    field_simp
    ring
  · have e : (p - x' - lam * t) / lam + (m - x' - lam * t) / lam
        = ((p + m) - 2 * (x' + lam * t)) / lam := by
      field_simp
      ring
    rw [e, hS, hb]
    field_simp
    ring

end Identities

variable {k : Type*} [Field k]

/-- **The height of a quotient of coprime polynomials** is the larger of their degrees. -/
theorem rfHeight_div_of_coprime {p q : k[X]} (hpq : IsCoprime p q) (hq : q ≠ 0) :
    rfHeight (algebraMap k[X] (RatFunc k) p / algebraMap k[X] (RatFunc k) q)
      = max p.natDegree q.natDegree := by
  obtain ⟨r, hr⟩ : ∃ r, r = algebraMap k[X] (RatFunc k) p / algebraMap k[X] (RatFunc k) q :=
    ⟨_, rfl⟩
  rw [← hr]
  have hrel : r.num * q = p * r.denom := (RatFunc.num_mul_eq_mul_denom_iff hq).mpr hr
  have hcop := r.isCoprime_num_denom
  have hd0 := r.denom_ne_zero
  -- the denominators divide each other
  have h1 : q ∣ r.denom := hpq.symm.dvd_of_dvd_mul_left ⟨r.num, by rw [← hrel]; ring⟩
  have h2 : r.denom ∣ q := hcop.symm.dvd_of_dvd_mul_left ⟨p, by rw [hrel]; ring⟩
  have hden : r.denom.natDegree = q.natDegree :=
    le_antisymm (natDegree_le_of_dvd h2 hq) (natDegree_le_of_dvd h1 hd0)
  -- the numerators divide each other
  have h3 : p ∣ r.num := hpq.dvd_of_dvd_mul_right ⟨r.denom, hrel⟩
  have h4 : r.num ∣ p := hcop.dvd_of_dvd_mul_right ⟨q, hrel.symm⟩
  have hnum : r.num.natDegree = p.natDegree := by
    by_cases hp0 : p = 0
    · have : r.num = 0 := zero_dvd_iff.mp (hp0 ▸ h3)
      rw [this, hp0]
    · have hn0 : r.num ≠ 0 := fun h => hp0 (zero_dvd_iff.mp (h ▸ h4))
      exact le_antisymm (natDegree_le_of_dvd h4 hp0) (natDegree_le_of_dvd h3 hn0)
  unfold rfHeight
  rw [hnum, hden]

section Doubling

variable {K : Type*} [Field K]

/-- The `X`-coordinate of `2 (x, 1)`: `((x² − a)² − 8bx)/(4λ)`. -/
theorem twist_dbl {a b t lam : K} (hlam : lam = t ^ 3 + a * t + b) (hlam0 : lam ≠ 0)
    (h2 : (2 : K) ≠ 0) :
    (((3 * (lam * t) ^ 2 + a * lam ^ 2) / (lam ^ 2 - -lam ^ 2)) ^ 2 - lam * t - lam * t) / lam
      = ((t ^ 2 - a) ^ 2 - 8 * b * t) / (4 * lam) := by
  have hb : b = lam - t ^ 3 - a * t := by rw [hlam]; ring
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2
  have hden : lam ^ 2 - -lam ^ 2 = 2 * lam ^ 2 := by ring
  rw [hden, hb]
  field_simp
  ring

end Doubling

/-- `(x² − a)² − 8bx` and `4(x³ + ax + b)` are coprime when `4a³ + 27b² ≠ 0`. -/
theorem isCoprime_dbl (a b : k) (h2 : (2 : k) ≠ 0) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) :
    IsCoprime ((X ^ 2 - C a) ^ 2 - 8 * C b * X : k[X]) (4 * (X ^ 3 + C a * X + C b)) := by
  have hid : (3 * X ^ 2 + 4 * C a) * ((X ^ 2 - C a) ^ 2 - 8 * C b * X)
      - (3 * X ^ 3 - 5 * C a * X - 27 * C b) * (X ^ 3 + C a * X + C b)
      = C (4 * a ^ 3 + 27 * b ^ 2) := by
    simp only [C_add, C_mul, C_pow, C_ofNat]
    ring
  have h4 : (4 : k) ≠ 0 := by
    have : (4 : k) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2
  have e4 : C (4 : k)⁻¹ * (4 : k[X]) = 1 := by
    have : (4 : k[X]) = C 4 := (map_ofNat C 4).symm
    rw [this, ← C_mul, inv_mul_cancel₀ h4, C_1]
  have eΔ : C (4 * a ^ 3 + 27 * b ^ 2)⁻¹ * C (4 * a ^ 3 + 27 * b ^ 2) = (1 : k[X]) := by
    rw [← C_mul, inv_mul_cancel₀ hΔ, C_1]
  refine ⟨C (4 * a ^ 3 + 27 * b ^ 2)⁻¹ * (3 * X ^ 2 + 4 * C a),
    -(C (4 * a ^ 3 + 27 * b ^ 2)⁻¹ * C (4 : k)⁻¹ * (3 * X ^ 3 - 5 * C a * X - 27 * C b)), ?_⟩
  linear_combination C (4 * a ^ 3 + 27 * b ^ 2)⁻¹ * hid + eΔ
    - (C (4 * a ^ 3 + 27 * b ^ 2)⁻¹ * (3 * X ^ 3 - 5 * C a * X - 27 * C b)
      * (X ^ 3 + C a * X + C b)) * e4

section Curve

variable {F : Type*} [Field F] (a b : F)

/-- `λ = x³ + ax + b` in `F(x)`. -/
noncomputable def lam : RatFunc F := RatFunc.X ^ 3 + RatFunc.C a * RatFunc.X + RatFunc.C b

theorem lam_eq : lam a b = algebraMap F[X] (RatFunc F) (X ^ 3 + C a * X + C b) := by
  simp [lam, RatFunc.algebraMap_X, RatFunc.algebraMap_C]

theorem lam_ne_zero : lam a b ≠ 0 := by
  rw [lam_eq]
  refine RatFunc.algebraMap_ne_zero fun h => ?_
  have := congrArg (fun p : F[X] => p.coeff 3) h
  simp at this

/-- **The twisted curve** `λ Y² = X³ + aX + b` over `F(x)`, in Weierstrass form:
`y′² = x′³ + aλ² x′ + bλ³` with `x′ = λX`, `y′ = λ²Y`. -/
noncomputable def twist : WeierstrassCurve (RatFunc F) :=
  shortW (RatFunc.C a * lam a b ^ 2) (RatFunc.C b * lam a b ^ 3)

theorem twist_equation_iff (x y : RatFunc F) : (twist a b).toAffine.Equation x y ↔
    y ^ 2 = x ^ 3 + RatFunc.C a * lam a b ^ 2 * x + RatFunc.C b * lam a b ^ 3 := by
  rw [Affine.equation_iff]
  simp [twist, shortW]

theorem ratFunc_two_ne_zero (h2 : (2 : F) ≠ 0) : (2 : RatFunc F) ≠ 0 := by
  have : (2 : RatFunc F) = RatFunc.C 2 := (map_ofNat RatFunc.C 2).symm
  rw [this]
  exact (_root_.map_ne_zero RatFunc.C).mpr h2

theorem twist_Δ_ne_zero (h2 : (2 : F) ≠ 0) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) :
    (twist a b).Δ ≠ 0 := by
  rw [twist, shortW_Δ]
  have e : 4 * (RatFunc.C a * lam a b ^ 2) ^ 3 + 27 * (RatFunc.C b * lam a b ^ 3) ^ 2
      = RatFunc.C (4 * a ^ 3 + 27 * b ^ 2) * lam a b ^ 6 := by
    simp only [map_add, map_mul, map_pow, map_ofNat]
    ring
  rw [e]
  have h16 : (-16 : RatFunc F) ≠ 0 := by
    have : (-16 : RatFunc F) = -(2 * 2 * 2 * 2) := by norm_num
    rw [this]
    have := ratFunc_two_ne_zero h2
    exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (mul_ne_zero this this) this) this)
  exact mul_ne_zero h16
    (mul_ne_zero ((_root_.map_ne_zero RatFunc.C).mpr hΔ) (pow_ne_zero 6 (lam_ne_zero a b)))

end Curve

section Points

open Classical

variable {F : Type*} [Field F] {a b : F}

/-- The points `(x, ±1)`, i.e. `(λx, ±λ²)`, satisfy the equation. -/
theorem basePt_equation {ε : RatFunc F} (hε : ε ^ 2 = 1) :
    (twist a b).toAffine.Equation (lam a b * RatFunc.X) (ε * lam a b ^ 2) := by
  rw [twist_equation_iff]
  have hl : lam a b = RatFunc.X ^ 3 + RatFunc.C a * RatFunc.X + RatFunc.C b := rfl
  linear_combination (lam a b) ^ 4 * hε + (lam a b) ^ 3 * hl

/-- **The height of a point** of the twisted curve: that of its `X`-coordinate `x′/λ`, and `0`
at the point at infinity. -/
noncomputable def ptHeight (Z : (twist a b).toAffine.Point) : ℕ :=
  match Z with
  | .zero => 0
  | .some x _ _ => rfHeight (x / lam a b)

theorem ptHeight_zero : ptHeight (0 : (twist a b).toAffine.Point) = 0 := rfl

theorem ptHeight_neg (Z : (twist a b).toAffine.Point) : ptHeight (-Z) = ptHeight Z := by
  cases Z with
  | zero => rfl
  | some x y h => rfl

variable (h2 : (2 : F) ≠ 0) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0)
include h2 hΔ

theorem twist_nonsingular {x y : RatFunc F} (h : (twist a b).toAffine.Equation x y) :
    (twist a b).toAffine.Nonsingular x y :=
  (Affine.equation_iff_nonsingular_of_Δ_ne_zero (twist_Δ_ne_zero a b h2 hΔ)).mp h

/-- **The point `(x, 1)`** of the twisted curve. -/
noncomputable def basePt : (twist a b).toAffine.Point :=
  .some (lam a b * RatFunc.X) (lam a b ^ 2)
    (twist_nonsingular h2 hΔ (by simpa using basePt_equation (a := a) (b := b) (one_pow 2)))

/-- The point `(x, −1)`. -/
noncomputable def negBasePt : (twist a b).toAffine.Point :=
  .some (lam a b * RatFunc.X) (-lam a b ^ 2)
    (twist_nonsingular h2 hΔ (by
      simpa using basePt_equation (a := a) (b := b) (ε := -1) (by norm_num)))

theorem neg_basePt : -basePt h2 hΔ = negBasePt h2 hΔ := by
  unfold basePt negBasePt
  rw [Affine.Point.neg_some]
  simp [Affine.negY, twist, shortW]

theorem ptHeight_basePt : ptHeight (basePt h2 hΔ) = 1 := by
  show rfHeight (lam a b * RatFunc.X / lam a b) = 1
  rw [mul_div_cancel_left₀ _ (lam_ne_zero a b)]
  unfold rfHeight
  rw [RatFunc.num_X, RatFunc.denom_X]
  simp

theorem ptHeight_add_basePt {x y : RatFunc F} (h : (twist a b).toAffine.Nonsingular x y)
    (hx : x ≠ lam a b * RatFunc.X) :
    ptHeight (Affine.Point.some x y h + basePt h2 hΔ)
      = rfHeight ((((y - lam a b ^ 2) / (x - lam a b * RatFunc.X)) ^ 2 - x
        - lam a b * RatFunc.X) / lam a b) := by
  unfold basePt
  rw [Affine.Point.add_of_X_ne hx]
  show rfHeight (_ / lam a b) = rfHeight (_ / lam a b)
  rw [Affine.slope_of_X_ne hx]
  simp [Affine.addX, twist, shortW]

theorem ptHeight_add_negBasePt {x y : RatFunc F} (h : (twist a b).toAffine.Nonsingular x y)
    (hx : x ≠ lam a b * RatFunc.X) :
    ptHeight (Affine.Point.some x y h + negBasePt h2 hΔ)
      = rfHeight ((((y + lam a b ^ 2) / (x - lam a b * RatFunc.X)) ^ 2 - x
        - lam a b * RatFunc.X) / lam a b) := by
  unfold negBasePt
  rw [Affine.Point.add_of_X_ne hx]
  show rfHeight (_ / lam a b) = rfHeight (_ / lam a b)
  rw [Affine.slope_of_X_ne hx]
  simp [Affine.addX, twist, shortW]

/-- `2 (x, 1)` has height `4`. -/
theorem ptHeight_dbl_basePt : ptHeight (basePt h2 hΔ + basePt h2 hΔ) = 4 := by
  have h2K := ratFunc_two_ne_zero h2
  have hl0 := lam_ne_zero a b
  have hy : lam a b ^ 2 ≠ (twist a b).toAffine.negY (lam a b * RatFunc.X) (lam a b ^ 2) := by
    simp only [Affine.negY, twist, shortW]
    intro h
    have : 2 * lam a b ^ 2 = 0 := by linear_combination h
    exact mul_ne_zero h2K (pow_ne_zero 2 hl0) this
  unfold basePt
  rw [Affine.Point.add_self_of_Y_ne hy]
  show rfHeight (_ / lam a b) = 4
  rw [Affine.slope_of_Y_ne rfl hy]
  have e := twist_dbl (a := RatFunc.C a) (b := RatFunc.C b) (t := RatFunc.X) (lam := lam a b)
    rfl hl0 h2K
  have hA : (twist a b).toAffine.addX (lam a b * RatFunc.X) (lam a b * RatFunc.X)
        ((3 * (lam a b * RatFunc.X) ^ 2 + 2 * (twist a b).toAffine.a₂ * (lam a b * RatFunc.X)
          + (twist a b).toAffine.a₄ - (twist a b).toAffine.a₁ * lam a b ^ 2) /
          (lam a b ^ 2 - (twist a b).toAffine.negY (lam a b * RatFunc.X) (lam a b ^ 2)))
        / lam a b
      = algebraMap F[X] (RatFunc F) ((X ^ 2 - C a) ^ 2 - 8 * C b * X)
        / algebraMap F[X] (RatFunc F) (4 * (X ^ 3 + C a * X + C b)) := by
    have e' : algebraMap F[X] (RatFunc F) ((X ^ 2 - C a) ^ 2 - 8 * C b * X)
        / algebraMap F[X] (RatFunc F) (4 * (X ^ 3 + C a * X + C b))
        = ((RatFunc.X ^ 2 - RatFunc.C a) ^ 2 - 8 * RatFunc.C b * RatFunc.X) / (4 * lam a b) := by
      rw [lam_eq]
      simp only [map_sub, map_mul, map_pow, map_add, map_ofNat, RatFunc.algebraMap_X,
        RatFunc.algebraMap_C]
    rw [e', ← e]
    simp [Affine.addX, Affine.negY, twist, shortW]
  rw [hA, rfHeight_div_of_coprime (isCoprime_dbl a b h2 hΔ)]
  · have h4 : (4 : F) ≠ 0 := by
      have : (4 : F) = 2 * 2 := by norm_num
      rw [this]
      exact mul_ne_zero h2 h2
    have d1 : ((X ^ 2 - C a) ^ 2 - 8 * C b * X : F[X]).natDegree = 4 := by
      compute_degree!
    have d2 : (4 * (X ^ 3 + C a * X + C b) : F[X]).natDegree = 3 := by
      compute_degree!
    rw [d1, d2]
    rfl
  · intro h
    have := congrArg (fun p : F[X] => p.coeff 3) h
    simp at this
    have h4 : (4 : F) ≠ 0 := by
      have : (4 : F) = 2 * 2 := by norm_num
      rw [this]
      exact mul_ne_zero h2 h2
    exact h4 this

/-- **The Basic Identity** (Knapp, Lemma 10.8) for every point `Z` of the twisted curve:
`h(Z − (x, 1)) + h(Z + (x, 1)) = 2 h(Z) + 2`. -/
theorem ptHeight_sub_add (Z : (twist a b).toAffine.Point) :
    ptHeight (Z - basePt h2 hΔ) + ptHeight (Z + basePt h2 hΔ) = 2 * ptHeight Z + 2 := by
  have hl0 := lam_ne_zero a b
  cases Z with
  | zero =>
    have e1 : (Affine.Point.zero : (twist a b).toAffine.Point) - basePt h2 hΔ
        = -basePt h2 hΔ := zero_sub _
    have e2 : (Affine.Point.zero : (twist a b).toAffine.Point) + basePt h2 hΔ
        = basePt h2 hΔ := zero_add _
    rw [e1, e2, ptHeight_neg, ptHeight_basePt]
    rfl
  | some x y h =>
    have hE := (twist_equation_iff a b x y).mp h.left
    by_cases hx : x = lam a b * RatFunc.X
    · -- `Z = ±(x, 1)`
      have hy : (y - lam a b ^ 2) * (y + lam a b ^ 2) = 0 := by
        have hl : lam a b = RatFunc.X ^ 3 + RatFunc.C a * RatFunc.X + RatFunc.C b := rfl
        rw [hx] at hE
        linear_combination hE - (lam a b) ^ 3 * hl
      rcases mul_eq_zero.mp hy with hy1 | hy1
      · have hZ : Affine.Point.some x y h = basePt h2 hΔ := by
          obtain rfl : x = lam a b * RatFunc.X := hx
          obtain rfl : y = lam a b ^ 2 := sub_eq_zero.mp hy1
          rfl
        rw [hZ, sub_self, ptHeight_zero, ptHeight_dbl_basePt, ptHeight_basePt]
      · have hZ : Affine.Point.some x y h = -basePt h2 hΔ := by
          rw [neg_basePt]
          obtain rfl : x = lam a b * RatFunc.X := hx
          obtain rfl : y = -lam a b ^ 2 := eq_neg_of_add_eq_zero_left hy1
          rfl
        have e1 : -basePt h2 hΔ - basePt h2 hΔ = -(basePt h2 hΔ + basePt h2 hΔ) := by abel
        rw [hZ, e1, neg_add_cancel, ptHeight_neg, ptHeight_neg, ptHeight_zero,
          ptHeight_dbl_basePt, ptHeight_basePt]
    · -- the generic case
      obtain ⟨hprod, hsum⟩ := twist_sum_prod (a := RatFunc.C a) (b := RatFunc.C b)
        (t := RatFunc.X) (lam := lam a b) rfl hl0 hx hE
      have hZ : x / lam a b ≠ RatFunc.X := by
        intro h0
        apply hx
        rw [← h0, mul_div_cancel₀ _ hl0]
      rw [sub_eq_add_neg, neg_basePt, ptHeight_add_negBasePt h2 hΔ h hx,
        ptHeight_add_basePt h2 hΔ h hx, add_comm]
      exact rfHeight_add_of_relations a b h2 hΔ hZ hprod hsum

end Points

end Azurite.ECPP.Manin
