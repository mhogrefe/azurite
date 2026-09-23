/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter4.Section4_5.Lemma_4_90
import Azurite.BasuPollackRoy.Chapter4.Section4_5.Theorem_4_86
import Azurite.BasuPollackRoy.Chapter4.Section4_5.Definition_4_89
import Azurite.BasuPollackRoy.Chapter4.Section4_5.Lemma_4_87
import Azurite.BasuPollackRoy.Chapter4.Section4_4.Theorem_4_72
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.Algebra.CharP.Algebra

/-!
# BPR §4.5, Proposition 4.92: a complete set of orthogonal idempotents indexed by the zeros

Let `K` be a field of characteristic zero, `C` an algebraically closed field extension of `K`,
and `𝒫` a finite subset of `K[X₁, …, X_k]` with `Zer(𝒫, Cᵏ)` finite. Then there is a family
`(e_x)_{x ∈ Zer(𝒫, Cᵏ)}` of elements of `Ā = C[X]/Ideal(𝒫, C)` that is a complete set of
orthogonal idempotents (`∑ e_x = 1`, `e_x e_y = 0` for `x ≠ y`, `e_x² = e_x`), and such that
`e_x` evaluates to `1` at `x` and to `0` at every other zero `y`.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial
open scoped Classical

variable {k : ℕ} {K : Type*} [Field K]

/-- Evaluating the image of a constant `c ∈ C` in `Ā` returns `c`. -/
theorem evalBar_algebraMap {C : Type*} [Field C] [Algebra K C]
    (Ps : Finset (MvPolynomial (Fin k) K)) (z : Fin k → C) (hz : z ∈ zerOfFinset C Ps) (c : C) :
    evalBar C Ps z hz (algebraMap C (quotPolysExt C Ps) c) = c := by
  rw [← Ideal.Quotient.mk_algebraMap, evalBar_mk]
  show MvPolynomial.aeval z (MvPolynomial.C c) = c
  rw [MvPolynomial.aeval_C]
  rfl

/-- **Nilpotency criterion.** If `w ∈ Ā` evaluates to `0` at every zero of `𝒫`, then `w` is
nilpotent. -/
theorem nilpotent_of_eval_zero {C : Type*} [Field C] [IsAlgClosed C] [Algebra K C]
    (Ps : Finset (MvPolynomial (Fin k) K)) (w : quotPolysExt C Ps)
    (h : ∀ (z : Fin k → C) (hz : z ∈ zerOfFinset C Ps), evalBar C Ps z hz w = 0) :
    IsNilpotent w := by
  obtain ⟨W, hW⟩ := Ideal.Quotient.mk_surjective w
  have hWvanish : ∀ z ∈ zerOfFinset C Ps, MvPolynomial.aeval z W = 0 := by
    intro z hz
    have := h z hz
    rw [← hW, evalBar_mk] at this
    exact this
  have hWrad : W ∈ (idealOfPolysExt C Ps).radical := by
    have hmem : W ∈ MvPolynomial.vanishingIdeal C (zerOfFinset C Ps) :=
      MvPolynomial.mem_vanishingIdeal_iff.mpr hWvanish
    rw [zerOfFinset_eq_zeroLocus, MvPolynomial.vanishingIdeal_zeroLocus_eq_radical] at hmem
    exact hmem
  obtain ⟨m, hm⟩ := Ideal.mem_radical_iff.mp hWrad
  refine ⟨m, ?_⟩
  rw [← hW, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact hm

/-- **BPR Proposition 4.92.** With `K` of characteristic zero, `C` algebraically closed, and
`Zer(𝒫, Cᵏ)` finite, there is a complete set of orthogonal idempotents `(e_x)` in `Ā` indexed by
the zeros, with `e_x(x) = 1` and `e_x(y) = 0` for `y ≠ x`. -/
theorem proposition_4_92 [CharZero K] {C : Type*} [Field C] [IsAlgClosed C] [Algebra K C] {k : ℕ}
    (Ps : Finset (MvPolynomial (Fin k) K)) (hfin : (zerOfFinset C Ps).Finite) :
    ∃ e : (Fin k → C) → quotPolysExt C Ps,
      (∑ x ∈ hfin.toFinset, e x = 1) ∧
      (∀ x ∈ hfin.toFinset, ∀ y ∈ hfin.toFinset, x ≠ y → e x * e y = 0) ∧
      (∀ x ∈ hfin.toFinset, e x ^ 2 = e x) ∧
      (∀ (x : Fin k → C) (hx : x ∈ zerOfFinset C Ps), evalBar C Ps x hx (e x) = 1) ∧
      (∀ (x : Fin k → C) (_hx : x ∈ zerOfFinset C Ps) (y : Fin k → C) (hy : y ∈ zerOfFinset C Ps),
        x ≠ y → evalBar C Ps y hy (e x) = 0) := by
  have : CharZero C := charZero_of_injective_algebraMap (algebraMap K C).injective
  classical
  set T := hfin.toFinset with hT
  have memT : ∀ {x : Fin k → C}, x ∈ T ↔ x ∈ zerOfFinset C Ps := by
    intro x; rw [hT]; exact hfin.mem_toFinset
  -- Step 0: a separating value function.
  obtain ⟨i, _, hsep⟩ := lemma_4_90 C Ps hfin
  let b : quotPolysExt C Ps := inclExt C Ps (Ideal.Quotient.mk _ (linearForm (K := K) i))
  have evalb_eq : ∀ (z : Fin k → C) (hz : z ∈ zerOfFinset C Ps),
      evalBar C Ps z hz b
        = valueAt C Ps (Ideal.Quotient.mk _ (linearForm (K := K) i)) z hz :=
    fun z hz => rfl
  -- A total value function; on `T` it agrees with `evalBar … b` for any proof (proof irrelevance).
  let val : (Fin k → C) → C := fun x =>
    if h : x ∈ zerOfFinset C Ps then evalBar C Ps x h b else 0
  have val_eq : ∀ (x : Fin k → C) (hx : x ∈ zerOfFinset C Ps), val x = evalBar C Ps x hx b := by
    intro x hx; simp only [val, dite_eq_left hx]
  -- injectivity of `val` on zeros via separation.
  have valinj : ∀ (x : Fin k → C) (hx : x ∈ zerOfFinset C Ps) (y : Fin k → C)
      (hy : y ∈ zerOfFinset C Ps), val x = val y → x = y := by
    intro x hx y hy h
    rw [val_eq x hx, val_eq y hy, evalb_eq x hx, evalb_eq y hy] at h
    exact hsep x hx y hy h
  have valne : ∀ (x : Fin k → C) (hx : x ∈ zerOfFinset C Ps) (y : Fin k → C)
      (hy : y ∈ zerOfFinset C Ps), x ≠ y → val x - val y ≠ 0 := by
    intro x hx y hy hxy hsub
    exact hxy (valinj x hx y hy (sub_eq_zero.mp hsub))
  -- `evalBar z b = val z` for `z` a zero.
  have evalb_val : ∀ (z : Fin k → C) (hz : z ∈ zerOfFinset C Ps),
      evalBar C Ps z hz b = val z := fun z hz => (val_eq z hz).symm
  -- Step 1: Lagrange candidates `s_x`.
  let s : (Fin k → C) → quotPolysExt C Ps := fun x =>
    ∏ y ∈ T.erase x,
      algebraMap C (quotPolysExt C Ps) (val x - val y)⁻¹ * (b - algebraMap C (quotPolysExt C Ps) (val y))
  -- `evalBar z (s x)` for `z` a zero.
  have evalBar_s : ∀ (x : Fin k → C) (z : Fin k → C) (hz : z ∈ zerOfFinset C Ps),
      evalBar C Ps z hz (s x)
        = ∏ y ∈ T.erase x, (val x - val y)⁻¹ * (val z - val y) := by
    intro x z hz
    rw [show s x = ∏ y ∈ T.erase x,
        algebraMap C (quotPolysExt C Ps) (val x - val y)⁻¹
          * (b - algebraMap C (quotPolysExt C Ps) (val y)) from rfl, map_prod]
    refine Finset.prod_congr rfl fun y _ => ?_
    rw [map_mul, map_sub, evalBar_algebraMap, evalBar_algebraMap, evalb_val z hz]
  -- `evalBar x (s x) = 1`
  have evalBar_s_self : ∀ (x : Fin k → C) (hx : x ∈ zerOfFinset C Ps),
      evalBar C Ps x hx (s x) = 1 := by
    intro x hx
    rw [evalBar_s x x hx]
    refine Finset.prod_eq_one fun y hy => ?_
    have hyT : y ∈ T := Finset.mem_of_mem_erase hy
    have hyne : x ≠ y := fun h => (Finset.mem_erase.mp hy).1 h.symm
    have hyz : y ∈ zerOfFinset C Ps := memT.mp hyT
    rw [inv_mul_cancel₀ (valne x hx y hyz hyne)]
  -- `evalBar z (s x) = 0` for `z ∈ T`, `z ≠ x`
  have evalBar_s_other : ∀ (x : Fin k → C) (z : Fin k → C) (hz : z ∈ zerOfFinset C Ps),
      z ∈ T → z ≠ x → evalBar C Ps z hz (s x) = 0 := by
    intro x z hz hzT hzx
    rw [evalBar_s x z hz]
    refine Finset.prod_eq_zero (i := z) (Finset.mem_erase.mpr ⟨hzx, hzT⟩) ?_
    rw [sub_self, mul_zero]
  -- Step 2: `s x * s y` is nilpotent for `x ≠ y` in `T`.
  have nilp : ∀ (x : Fin k → C), x ∈ T → ∀ (y : Fin k → C), y ∈ T → x ≠ y →
      IsNilpotent (s x * s y) := by
    intro x hxT y hyT hxy
    refine nilpotent_of_eval_zero Ps (s x * s y) ?_
    intro z hz
    rw [map_mul]
    have hzT : z ∈ T := memT.mpr hz
    by_cases hzx : z = x
    · -- then `z ≠ y`, so `evalBar z (s y) = 0`
      have hzy : z ≠ y := by rw [hzx]; exact hxy
      rw [evalBar_s_other y z hz hzT hzy, mul_zero]
    · -- `evalBar z (s x) = 0`
      rw [evalBar_s_other x z hz hzT hzx, zero_mul]
  -- Step 3: a uniform power `M`.
  -- per-pair nilpotency exponent (junk `0` off the diagonal of distinct pairs in `T`).
  let expOf : (Fin k → C) × (Fin k → C) → ℕ := fun p =>
    if h : p.1 ∈ T ∧ p.2 ∈ T ∧ p.1 ≠ p.2 then Classical.choose (nilp p.1 h.1 p.2 h.2.1 h.2.2) else 0
  -- the chosen exponent kills the product
  have expOf_spec : ∀ (x : Fin k → C) (hxT : x ∈ T) (y : Fin k → C) (hyT : y ∈ T) (hxy : x ≠ y),
      (s x * s y) ^ (expOf (x, y)) = 0 := by
    intro x hxT y hyT hxy
    have hdif : expOf (x, y) = Classical.choose (nilp x hxT y hyT hxy) := by
      simp only [expOf, dite_eq_left (⟨hxT, hyT, hxy⟩ : (x, y).1 ∈ T ∧ (x, y).2 ∈ T ∧ (x, y).1 ≠ (x, y).2)]
    rw [hdif]
    exact Classical.choose_spec (nilp x hxT y hyT hxy)
  let M : ℕ := 1 + (T ×ˢ T).sup expOf
  have hM1 : 1 ≤ M := Nat.le_add_right 1 _
  have hMge : ∀ (x : Fin k → C), x ∈ T → ∀ (y : Fin k → C), y ∈ T →
      expOf (x, y) ≤ M := by
    intro x hxT y hyT
    have hmem : (x, y) ∈ T ×ˢ T := Finset.mem_product.mpr ⟨hxT, hyT⟩
    exact le_trans (Finset.le_sup hmem) (Nat.le_add_left _ 1)
  -- cross products vanish at the uniform power
  have crossM : ∀ (x : Fin k → C), x ∈ T → ∀ (y : Fin k → C), y ∈ T → x ≠ y →
      (s x * s y) ^ M = 0 := by
    intro x hxT y hyT hxy
    have hm := expOf_spec x hxT y hyT hxy
    have hle := hMge x hxT y hyT
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    rw [hd, pow_add, hm, zero_mul]
  -- Step 3 def: `t x = (s x)^M`.
  let t : (Fin k → C) → quotPolysExt C Ps := fun x => (s x) ^ M
  have t_mul : ∀ (x : Fin k → C), x ∈ T → ∀ (y : Fin k → C), y ∈ T → x ≠ y →
      t x * t y = 0 := by
    intro x hxT y hyT hxy
    show (s x) ^ M * (s y) ^ M = 0
    rw [← mul_pow]
    exact crossM x hxT y hyT hxy
  have evalBar_t_self : ∀ (x : Fin k → C) (hx : x ∈ zerOfFinset C Ps),
      evalBar C Ps x hx (t x) = 1 := by
    intro x hx
    show evalBar C Ps x hx ((s x) ^ M) = 1
    rw [map_pow, evalBar_s_self x hx, one_pow]
  have evalBar_t_other : ∀ (x : Fin k → C) (z : Fin k → C) (hz : z ∈ zerOfFinset C Ps),
      z ∈ T → z ≠ x → evalBar C Ps z hz (t x) = 0 := by
    intro x z hz hzT hzx
    show evalBar C Ps z hz ((s x) ^ M) = 0
    rw [map_pow, evalBar_s_other x z hz hzT hzx, zero_pow (by omega : M ≠ 0)]
  -- Step 4: `∑ t_x r_x = 1` via weak Nullstellensatz over `C`.
  -- lifts of `t x`
  let Tlift : (Fin k → C) → MvPolynomial (Fin k) C := fun x =>
    Classical.choose (Ideal.Quotient.mk_surjective (t x))
  have Tlift_spec : ∀ (x : Fin k → C),
      Ideal.Quotient.mk (idealOfPolysExt C Ps) (Tlift x) = t x :=
    fun x => Classical.choose_spec (Ideal.Quotient.mk_surjective (t x))
  -- the combined finset over which we apply Nullstellensatz, all over base field `C`
  let G : Finset (MvPolynomial (Fin k) C) :=
    (Ps.image (MvPolynomial.map (algebraMap K C))) ∪ (T.image Tlift)
  -- `zerOfFinset C G = ∅`
  have hGempty : zerOfFinset (K := C) C G = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    -- `z ∈ zerOfFinset C Ps`
    have hzPs : z ∈ zerOfFinset C Ps := by
      intro P hP
      have hmem : MvPolynomial.map (algebraMap K C) P ∈ G :=
        Finset.mem_union_left _ (Finset.mem_image_of_mem _ hP)
      have := hz _ hmem
      rwa [MvPolynomial.aeval_map_algebraMap] at this
    have hzT : z ∈ T := memT.mpr hzPs
    -- `aeval z (Tlift z) = evalBar z (t z) = 1`, contradicting being a zero of `G`
    have hmem : Tlift z ∈ G := Finset.mem_union_right _ (Finset.mem_image_of_mem _ hzT)
    have h0 : MvPolynomial.aeval z (Tlift z) = 0 := hz _ hmem
    have h1 : MvPolynomial.aeval z (Tlift z) = 1 := by
      have := evalBar_t_self z hzPs
      rw [← Tlift_spec z, evalBar_mk] at this
      exact this
    rw [h0] at h1
    exact one_ne_zero h1.symm
  -- apply Theorem 4.72 with base field `C` (self-algebra)
  obtain ⟨A, hA⟩ := (theorem_4_72 (K := C) (C := C) G).mp hGempty
  -- apply `mk J` to `∑ g, A g * g = 1`
  let mkJ : MvPolynomial (Fin k) C →+* quotPolysExt C Ps :=
    Ideal.Quotient.mk (idealOfPolysExt C Ps)
  have hsum1' : ∑ g ∈ G, mkJ (A g) * mkJ g = 1 := by
    have h2 : ∑ g ∈ G, mkJ (A g * g) = 1 := by
      have := congrArg mkJ hA
      rwa [map_sum, map_one] at this
    rw [← h2]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_mul]
  -- terms coming from `Ps`-image are zero (those `g ∈ J`)
  have hPs_zero : ∀ g ∈ Ps.image (MvPolynomial.map (algebraMap K C)), mkJ (A g) * mkJ g = 0 := by
    intro g hg
    have hgJ : g ∈ idealOfPolysExt C Ps := Ideal.subset_span (Finset.mem_coe.mpr hg)
    have : mkJ g = 0 := by
      show Ideal.Quotient.mk _ g = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]; exact hgJ
    rw [this, mul_zero]
  -- reduce the sum over `G` to the sum over `T.image Tlift`
  have hsub : T.image Tlift ⊆ G := Finset.subset_union_right
  have hsum2 : ∑ g ∈ T.image Tlift, mkJ (A g) * mkJ g = 1 := by
    rw [← hsum1']
    refine Finset.sum_subset hsub ?_
    intro g hgG hgnot
    -- `g ∈ G` but `g ∉ T.image Tlift`, so `g ∈ Ps.image …`
    rw [Finset.mem_union] at hgG
    rcases hgG with hgPs | hgT
    · exact hPs_zero g hgPs
    · exact absurd hgT hgnot
  -- `t` is injective on `T`: distinct zeros separate `t`.
  have t_inj : ∀ x ∈ T, ∀ y ∈ T, t x = t y → x = y := by
    intro x hxT y hyT hxy
    by_contra hne
    have hxz : x ∈ zerOfFinset C Ps := memT.mp hxT
    have h1 : evalBar C Ps x hxz (t x) = 1 := evalBar_t_self x hxz
    have h0 : evalBar C Ps x hxz (t y) = 0 :=
      evalBar_t_other y x hxz hxT hne
    rw [hxy, h0] at h1
    exact one_ne_zero h1.symm
  -- hence `Tlift` is injective on `T`.
  have Tlift_inj : Set.InjOn Tlift T := by
    intro x hx y hy hxy
    have : t x = t y := by rw [← Tlift_spec x, ← Tlift_spec y, hxy]
    exact t_inj x hx y hy this
  -- define `r x := mkJ (A (Tlift x))`.
  let r : (Fin k → C) → quotPolysExt C Ps := fun x => mkJ (A (Tlift x))
  -- `∑ x ∈ T, r x * t x = 1`
  have hsumT : ∑ x ∈ T, r x * t x = 1 := by
    rw [← hsum2, Finset.sum_image (fun x hx y hy h => Tlift_inj hx hy h)]
    refine Finset.sum_congr rfl fun x hx => ?_
    show mkJ (A (Tlift x)) * t x = mkJ (A (Tlift x)) * mkJ (Tlift x)
    rw [Tlift_spec x]
  -- Step 5: `e x := t x * r x`.
  let e : (Fin k → C) → quotPolysExt C Ps := fun x => t x * r x
  -- `∑ y ∈ T, e y = 1`
  have hsumE : ∑ y ∈ T, e y = 1 := by
    show ∑ y ∈ T, t y * r y = 1
    rw [← hsumT]
    exact Finset.sum_congr rfl fun y _ => mul_comm _ _
  -- products `e x * e y = 0` for `x ≠ y`
  have eMul : ∀ (x : Fin k → C), x ∈ T → ∀ (y : Fin k → C), y ∈ T → x ≠ y → e x * e y = 0 := by
    intro x hxT y hyT hxy
    show (t x * r x) * (t y * r y) = 0
    have hrw : (t x * r x) * (t y * r y) = (t x * t y) * (r x * r y) := by ring
    rw [hrw, t_mul x hxT y hyT hxy, zero_mul]
  refine ⟨e, hsumE, eMul, ?_, ?_, ?_⟩
  · -- `e x ^ 2 = e x`
    intro x hxT
    have hsplit : e x = ∑ y ∈ T, e x * e y := by
      conv_lhs => rw [← mul_one (e x), ← hsumE, Finset.mul_sum]
    have hsingle : ∑ y ∈ T, e x * e y = e x * e x := by
      refine Finset.sum_eq_single x ?_ ?_
      · intro y hyT hyx
        exact eMul x hxT y hyT (fun h => hyx h.symm)
      · intro hxnot; exact absurd hxT hxnot
    rw [sq]
    conv_rhs => rw [hsplit, hsingle]
  · -- `evalBar x (e x) = 1`
    intro x hx
    have hxT : x ∈ T := memT.mpr hx
    -- apply `evalBar x hx` to `∑ y ∈ T, e y = 1`
    have key : ∑ y ∈ T, evalBar C Ps x hx (e y) = 1 := by
      have hev : evalBar C Ps x hx (∑ y ∈ T, e y) = 1 := by rw [hsumE, map_one]
      rwa [map_sum] at hev
    rw [Finset.sum_eq_single x] at key
    · -- the surviving term equals the goal
      exact key
    · intro y hyT hyx
      show evalBar C Ps x hx (t y * r y) = 0
      rw [map_mul, evalBar_t_other y x hx hxT (fun h => hyx h.symm), zero_mul]
    · intro hxnot; exact absurd hxT hxnot
  · -- `evalBar y (e x) = 0` for `x ≠ y`
    intro x hx y hy hxy
    show evalBar C Ps y hy (t x * r x) = 0
    rw [map_mul, evalBar_t_other x y hy (memT.mpr hy) (fun h => hxy h.symm), zero_mul]
