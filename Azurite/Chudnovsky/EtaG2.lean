/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Chudnovsky.QuasiPeriod
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform

/-!
# The quasi-period `η₁` of the lattice `ℤ + ℤτ` is the Eisenstein series `G₂(τ)`

For `τ` in the upper half-plane, `pairOf τ` is the period pair `(1, τ)`, and

  `η(1) = G₂(τ)`   (`quasiPeriod_one_eq_G2`),

Mathlib's `EisensteinSeries.G2`, the conditionally convergent `∑_m ∑_n (mτ + n)⁻²`.  This is
the form in which the Legendre relation is used: the transformation `G₂(−1/τ) = τ² G₂(τ) − 2πiτ`
(Mathlib's `G2_S_transform`) at a fixed point of the modular group gives `η₁` in terms of `π`,
with no contour integral.

Proof: `η(1) = ζ(τ/2 + 1) − ζ(τ/2) = ∑_l [1/(τ/2 + 1 − l) − 1/(τ/2 − l) + 1/l²]`, absolutely
convergent.  With `w = mτ + n`, Mathlib's `aux_identity` writes `1/w²` as its absolutely
convergent `G2Term` plus `1/w − 1/(w + 1)`; so the summand is
`G2Term + [1/w − 1/(w+1)] + [1/(τ/2 + 1 − w) − 1/(τ/2 − w)]`, and both brackets telescope to `0`
in `n` for every `m` (`tsum_symmetricIco_linear_sub_linear_add_one_eq_zero`, the second one at
the point `τ/2` with the odd multiple `1 − 2m`).
-/

open UpperHalfPlane hiding I
open EisensteinSeries SummationFilter Filter

namespace Azurite.Chudnovsky

/-- The period pair `(1, τ)`. -/
noncomputable def pairOf (τ : ℍ) : PeriodPair where
  ω₁ := 1
  ω₂ := τ
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have him := congrArg Complex.im h
    simp only [Complex.real_smul, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.one_im, mul_zero, Complex.ofReal_im, Complex.one_re, zero_mul, add_zero,
      Complex.zero_im, zero_add] at him
    have ht : t = 0 := by
      rcases mul_eq_zero.mp him with h1 | h1
      · exact h1
      · exact absurd h1 (ne_of_gt τ.im_pos)
    subst ht
    have hre := congrArg Complex.re h
    simpa using hre

@[simp] theorem pairOf_ω₁ (τ : ℍ) : (pairOf τ).ω₁ = 1 := rfl
@[simp] theorem pairOf_ω₂ (τ : ℍ) : (pairOf τ).ω₂ = τ := rfl

theorem hasSum_weierstrassZeta (L : PeriodPair) (z : ℂ) :
    HasSum (fun l : L.lattice => zetaTerm l z) (weierstrassZeta L z) := by
  have h := hasSum_zetaExcept L (L.ω₁ / 2) z
  rw [zetaExcept_of_notMem L _ L.ω₁_div_two_notMem_lattice] at h
  refine h.congr_fun fun l => ?_
  rw [ite_eq_right]
  intro hEq
  exact L.ω₁_div_two_notMem_lattice (hEq ▸ l.2)

/-- `τ/2` as a point of the upper half-plane. -/
noncomputable def halfPoint (τ : ℍ) : ℍ := ⟨(τ : ℂ) / 2, by
  have := τ.im_pos
  simp only [Complex.div_ofNat_im]
  exact div_pos this (by norm_num)⟩

@[simp] theorem coe_halfPoint (τ : ℍ) : ((halfPoint τ : ℍ) : ℂ) = (τ : ℂ) / 2 := rfl

/-- The telescoping sums `∑_n [1/(mτ + n) − 1/(mτ + n + 1)] = 0`. -/
theorem tsum_telescope (τ : ℍ) (m : ℤ) :
    ∑' n : ℤ, (1 / ((m : ℂ) * τ + n) - 1 / (m * τ + n + 1)) = 0 := by
  rw [← tsum_eq_of_summable_unconditional (L := symmetricIco ℤ)
    (summable_right_one_div_linear_sub_one_div_linear_succ τ m)]
  exact tsum_symmetricIco_linear_sub_linear_add_one_eq_zero τ m

/-- **`η(1) = G₂(τ)`** for the lattice `ℤ + ℤτ`. -/
theorem quasiPeriod_one_eq_G2 (τ : ℍ) : quasiPeriod (pairOf τ) 1 = G2 τ := by
  set L := pairOf τ with hL
  set z₀ : ℂ := (τ : ℂ) / 2 with hz₀
  have hz₀L : z₀ ∉ L.lattice := L.ω₂_div_two_notMem_lattice
  have h1mem : (1 : ℂ) ∈ L.lattice := L.ω₁_mem_lattice
  -- `η = ζ(z₀ + 1) − ζ(z₀)` as a sum over the lattice
  have hη := weierstrassZeta_add_coe L ⟨1, h1mem⟩ hz₀L
  have hsum : HasSum (fun l : L.lattice => zetaTerm l (z₀ + 1) - zetaTerm l z₀)
      (quasiPeriod L 1) := by
    have := (hasSum_weierstrassZeta L (z₀ + 1)).sub (hasSum_weierstrassZeta L z₀)
    rwa [show weierstrassZeta L (z₀ + 1) - weierstrassZeta L z₀ = quasiPeriod L 1 by
      rw [show (z₀ + 1 : ℂ) = z₀ + ((⟨1, h1mem⟩ : L.lattice) : ℂ) from rfl, hη]; ring] at this
  -- reindex by `(m, n)`, `l = mτ + n`
  let e : ℤ × ℤ ≃ L.lattice := (Equiv.prodComm ℤ ℤ).trans L.latticeEquivProd.symm.toEquiv
  have he : ∀ p : ℤ × ℤ, ((e p : L.lattice) : ℂ) = (p.1 : ℂ) * τ + p.2 := by
    intro p
    have := L.latticeEquiv_symm_apply (p.2, p.1)
    simp only [e, Equiv.trans_apply, Equiv.prodComm_apply, Prod.swap, LinearEquiv.coe_toEquiv]
    rw [this]
    simp [hL]
    ring
  have hsum' : HasSum (fun p : ℤ × ℤ => zetaTerm (e p) (z₀ + 1) - zetaTerm (e p) z₀)
      (quasiPeriod L 1) := (e.hasSum_iff (f := fun l : L.lattice =>
        zetaTerm l (z₀ + 1) - zetaTerm l z₀)).mpr hsum
  -- the telescoping part
  let B : ℤ × ℤ → ℂ := fun p =>
    1 / (z₀ + 1 - ((p.1 : ℂ) * τ + p.2)) - 1 / (z₀ - ((p.1 : ℂ) * τ + p.2))
  have hterm : ∀ p : ℤ × ℤ, zetaTerm (e p) (z₀ + 1) - zetaTerm (e p) z₀
      = eisSummand 2 ![p.1, p.2] τ + B p := by
    intro p
    simp only [zetaTerm, he, B, eisSummand, Matrix.cons_val_zero, Matrix.cons_val_one]
    have e1 : (z₀ + 1) / ((p.1 : ℂ) * τ + p.2) ^ 2 - z₀ / ((p.1 : ℂ) * τ + p.2) ^ 2
        = ((p.1 : ℂ) * τ + p.2) ^ (-2 : ℤ) := by
      rw [← sub_div, add_sub_cancel_left, one_div, zpow_neg, zpow_ofNat]
    linear_combination e1
  have hsumT : Summable fun p : ℤ × ℤ => eisSummand 2 ![p.1, p.2] τ + B p :=
    hsum'.summable.congr hterm
  have hBeq : ∀ (m n : ℤ), B (m, n) = -(1 / (((1 - 2 * m : ℤ) : ℂ) * (halfPoint τ : ℍ) + (-n : ℤ))
      - 1 / (((1 - 2 * m : ℤ) : ℂ) * (halfPoint τ : ℍ) + (-n : ℤ) + 1)) := by
    intro m n
    simp only [B, coe_halfPoint, hz₀]
    push_cast
    rw [neg_sub]
    congr 2 <;> ring
  have hFs : ∀ m : ℤ, Summable fun n : ℤ =>
      1 / (((1 - 2 * m : ℤ) : ℂ) * (halfPoint τ : ℍ) + n)
        - 1 / (((1 - 2 * m : ℤ) : ℂ) * (halfPoint τ : ℍ) + n + 1) := fun m =>
    summable_right_one_div_linear_sub_one_div_linear_succ (halfPoint τ) (1 - 2 * m)
  have hBs : ∀ m : ℤ, Summable fun n : ℤ => B (m, n) := fun m => by
    have := ((Equiv.neg ℤ).summable_iff.mpr (hFs m)).neg
    refine this.congr fun n => ?_
    rw [hBeq m n]
    simp
  have hB0 : ∀ m : ℤ, ∑' n : ℤ, B (m, n) = 0 := fun m => by
    have h1 := tsum_telescope (halfPoint τ) (1 - 2 * m)
    have h2 := (Equiv.neg ℤ).tsum_eq (fun n : ℤ =>
      1 / (((1 - 2 * m : ℤ) : ℂ) * (halfPoint τ : ℍ) + n)
        - 1 / (((1 - 2 * m : ℤ) : ℂ) * (halfPoint τ : ℍ) + n + 1))
    rw [h1] at h2
    have h3 : ∑' n : ℤ, B (m, n) = -∑' n : ℤ,
        (1 / (((1 - 2 * m : ℤ) : ℂ) * (halfPoint τ : ℍ) + ((Equiv.neg ℤ) n : ℤ))
          - 1 / (((1 - 2 * m : ℤ) : ℂ) * (halfPoint τ : ℍ) + ((Equiv.neg ℤ) n : ℤ) + 1)) := by
      rw [← tsum_neg]
      exact tsum_congr fun n => by rw [hBeq m n]; rfl
    rw [h3, h2, neg_zero]
  -- the inner sums are the `e2Summand`s
  have hinner : ∀ m : ℤ, ∑' n : ℤ, (eisSummand 2 ![m, n] τ + B (m, n)) = e2Summand m τ := by
    intro m
    rw [(e2Summand_summable m τ).tsum_add (hBs m), hB0, add_zero]
    rfl
  have htot : quasiPeriod L 1 = ∑' m : ℤ, e2Summand m τ := by
    rw [← (hsum'.congr_fun fun p => (hterm p).symm).tsum_eq,
      hsumT.tsum_prod' (fun m => (e2Summand_summable m τ).add (hBs m))]
    exact tsum_congr hinner
  have hsummable : Summable fun m : ℤ => e2Summand m τ := by
    have := hsumT.prod
    exact this.congr hinner
  rw [htot, G2, tsum_eq_of_summable_unconditional (L := symmetricIcc ℤ) hsummable]

end Azurite.Chudnovsky
