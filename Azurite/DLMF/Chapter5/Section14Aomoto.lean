/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section14Selberg
import Azurite.DLMF.Chapter5.Section12Holo

/-!
# DLMF 5.14.4: Aomoto's factor `t₁⋯tₘ`

Aomoto's integral `A_k = ∫_{[0,1]ᴺ} t₁⋯t_k Φ(t) dt`, with `Φ` the Selberg integrand, satisfies
`(a + (N − k)c) A_{k−1} = (a + b + (2N − k − 1)c) A_k` (Forrester–Warnaar §2). The proof
integrates `∂/∂t₁ (t₁(1 − t₁) t₂⋯t_k Φ(t))` over the cube: the integral vanishes (fundamental
theorem of calculus in `t₁`, off the finitely many points `t₁ = tⱼ`), and the terms
`t₁(1 − t₁)/(t₁ − tⱼ)` are evaluated by symmetrizing under the transposition `t₁ ↔ tⱼ`.

For `ℜc ≥ 1/2` every integrand is dominated by the Jacobi weight `∏ tᵢ^{a−1}(1 − tᵢ)^{b−1}`;
the recursion then extends to `ℜc > 0` by analytic continuation in `c`. With Selberg's integral
(`dlmf_5_14_4_selberg`) this gives DLMF 5.14.4 for `0 ≤ m ≤ n`, `ℜa, ℜb, ℜc > 0`.
-/

open Finset MeasureTheory

namespace Azurite.DLMF

variable {n : ℕ}

/-! ### Monomials and Aomoto's integral -/

/-- `∏_{i<k} tᵢ` (0-based). -/
noncomputable def initProd {N : ℕ} (k : ℕ) (t : Fin N → ℝ) : ℂ :=
  ∏ i ∈ univ.filter (fun i : Fin N => (i : ℕ) < k), (t i : ℂ)

/-- `∏_{0<i<k} tᵢ` (0-based). -/
noncomputable def midProd {N : ℕ} (k : ℕ) (t : Fin N → ℝ) : ℂ :=
  ∏ i ∈ univ.filter (fun i : Fin N => 0 < (i : ℕ) ∧ (i : ℕ) < k), (t i : ℂ)

/-- Aomoto's integral `A_k = ∫_{[0,1]ᴺ} t₁⋯t_k Φ(t) dt`. -/
noncomputable def aomotoA (N k : ℕ) (a b c : ℂ) : ℂ :=
  ∫ t in Set.Icc (0 : Fin N → ℝ) 1, initProd k t * selbergF a b c t

theorem initProd_eq_mul {k : ℕ} (hk : 0 < k) (t : Fin (n + 1) → ℝ) :
    initProd k t = (t 0 : ℂ) * midProd k t := by
  have hS : univ.filter (fun i : Fin (n + 1) => (i : ℕ) < k) =
      insert 0 (univ.filter (fun i : Fin (n + 1) => 0 < (i : ℕ) ∧ (i : ℕ) < k)) := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff, Fin.val_zero]
    omega
  rw [initProd, midProd, hS, prod_insert (by simp)]

theorem initProd_comp {N k : ℕ} (σ : Equiv.Perm (Fin N))
    (hσ : ∀ i : Fin N, (i : ℕ) < k ↔ ((σ i : Fin N) : ℕ) < k) (t : Fin N → ℝ) :
    initProd k (t ∘ σ) = initProd k t :=
  prod_equiv σ (fun i => by simp [hσ i]) fun _ _ => rfl

theorem midProd_comp {N k : ℕ} (σ : Equiv.Perm (Fin N))
    (hσ : ∀ i : Fin N, (0 < (i : ℕ) ∧ (i : ℕ) < k) ↔
      (0 < ((σ i : Fin N) : ℕ) ∧ ((σ i : Fin N) : ℕ) < k))
    (t : Fin N → ℝ) : midProd k (t ∘ σ) = midProd k t :=
  prod_equiv σ (fun i => by simp [hσ i]) fun _ _ => rfl

/-- `∏_{0<i<k} tᵢ` is `∏_{i<k−1}` of the rotated tuple. -/
theorem midProd_eq_initProd_rotate {k : ℕ} (hk : 0 < k) (hkn : k ≤ n + 1)
    (t : Fin (n + 1) → ℝ) : midProd k t = initProd (k - 1) (t ∘ finRotate (n + 1)) := by
  rw [initProd, midProd]
  symm
  refine prod_equiv (finRotate (n + 1)) (fun i => ?_) fun _ _ => rfl
  simp only [mem_filter, mem_univ, true_and]
  rw [coe_finRotate]
  split_ifs with h
  · subst h; simp; omega
  · omega

/-! ### Coordinate permutations of the cube -/

theorem permMap_preimage_cube {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    permMap σ ⁻¹' Set.Icc (0 : Fin N → ℝ) 1 = Set.Icc 0 1 := by
  ext t
  simp only [Set.mem_preimage, permMap_apply, Set.mem_Icc, Pi.le_def, Pi.zero_apply,
    Pi.one_apply, Function.comp]
  constructor
  · rintro ⟨h0, h1⟩
    exact ⟨fun i => by simpa using h0 (σ.symm i), fun i => by simpa using h1 (σ.symm i)⟩
  · rintro ⟨h0, h1⟩; exact ⟨fun i => h0 _, fun i => h1 _⟩

theorem integral_cube_comp {N : ℕ} (σ : Equiv.Perm (Fin N)) (g : (Fin N → ℝ) → ℂ) :
    ∫ t in Set.Icc (0 : Fin N → ℝ) 1, g (t ∘ σ) = ∫ t in Set.Icc (0 : Fin N → ℝ) 1, g t := by
  have h := (measurePreserving_permMap σ).setIntegral_preimage_emb
    (permMap σ).measurableEmbedding g (Set.Icc 0 1)
  rw [permMap_preimage_cube] at h
  simpa only [permMap_apply] using h

theorem integrableOn_cube_comp {N : ℕ} (σ : Equiv.Perm (Fin N)) {g : (Fin N → ℝ) → ℂ}
    (hg : IntegrableOn g (Set.Icc (0 : Fin N → ℝ) 1)) :
    IntegrableOn (fun t => g (t ∘ σ)) (Set.Icc (0 : Fin N → ℝ) 1) := by
  have h := ((measurePreserving_permMap σ).integrableOn_comp_preimage
    (permMap σ).measurableEmbedding (s := Set.Icc 0 1) (f := g)).mpr hg
  rw [permMap_preimage_cube] at h
  simpa only [Function.comp_def, permMap_apply] using h

/-! ### Bounds on the cube -/

theorem abs_sub_le_one_of_mem {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |x - y| ≤ 1 := by
  rw [abs_le]; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

theorem prod_abs_sub_le_one {N : ℕ} {t : Fin N → ℝ} (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) 1)
    (i : Fin N) (s : Finset (Fin N)) : ∏ j ∈ s, |t i - t j| ≤ 1 :=
  prod_le_one₀ (fun _ _ => abs_nonneg _) fun j _ => abs_sub_le_one_of_mem (ht i) (ht j)

theorem abs_vandermondeDelta_le_one {N : ℕ} {t : Fin N → ℝ}
    (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) 1) : |vandermondeDelta t| ≤ 1 := by
  rw [vandermondeDelta, abs_prod]
  exact prod_le_one₀ (fun _ _ => abs_nonneg _) fun i _ => by
    rw [abs_prod]; exact prod_abs_sub_le_one ht i _

theorem abs_vandermondeDelta_le_sub {N : ℕ} {t : Fin N → ℝ}
    (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) 1) {i j : Fin N} (hij : i < j) :
    |vandermondeDelta t| ≤ |t i - t j| := by
  classical
  rw [vandermondeDelta, abs_prod, ← mul_prod_erase _ _ (mem_univ i), abs_prod,
    ← mul_prod_erase _ _ (mem_Ioi.mpr hij)]
  have h2 : ∏ x ∈ univ.erase i, |∏ y ∈ Ioi x, (t x - t y)| ≤ 1 :=
    prod_le_one₀ (fun _ _ => abs_nonneg _) fun x _ => by
      rw [abs_prod]; exact prod_abs_sub_le_one ht x _
  have h1 := prod_abs_sub_le_one ht i ((Ioi i).erase j)
  calc _ ≤ |t i - t j| * ∏ x ∈ (Ioi i).erase j, |t i - t x| :=
        mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (prod_nonneg fun _ _ => abs_nonneg _)) h2
    _ ≤ |t i - t j| := mul_le_of_le_one_right (abs_nonneg _) h1

theorem mem_cube_iff {N : ℕ} {t : Fin N → ℝ} :
    t ∈ Set.Icc (0 : Fin N → ℝ) 1 ↔ ∀ i, t i ∈ Set.Icc (0 : ℝ) 1 := by
  simp only [Set.mem_Icc, Pi.le_def, Pi.zero_apply, Pi.one_apply]
  exact ⟨fun h i => ⟨h.1 i, h.2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩

theorem norm_initProd_le {N k : ℕ} {t : Fin N → ℝ} (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) 1) :
    ‖initProd k t‖ ≤ 1 := by
  rw [initProd, norm_prod]
  exact prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ht i).1]; exact (ht i).2

theorem norm_midProd_le {N k : ℕ} {t : Fin N → ℝ} (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) 1) :
    ‖midProd k t‖ ≤ 1 := by
  rw [midProd, norm_prod]
  exact prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ht i).1]; exact (ht i).2

theorem norm_selbergF {N : ℕ} {a b c : ℂ} (hc : 0 < c.re) (t : Fin N → ℝ) :
    ‖selbergF a b c t‖ = ‖jacobiWeight a b t‖ * |vandermondeDelta t| ^ (2 * c.re) := by
  rw [selbergF, norm_mul, Complex.norm_cpow_eq_rpow_re_of_nonneg (abs_nonneg _)
    (by simp; positivity)]
  simp

theorem norm_selbergF_le {N : ℕ} {a b c : ℂ} (hc : 0 < c.re) {t : Fin N → ℝ}
    (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) 1) : ‖selbergF a b c t‖ ≤ ‖jacobiWeight a b t‖ := by
  rw [norm_selbergF hc]
  exact mul_le_of_le_one_right (norm_nonneg _)
    (Real.rpow_le_one (abs_nonneg _) (abs_vandermondeDelta_le_one ht) (by positivity))

theorem norm_selbergF_le_sub {N : ℕ} {a b c : ℂ} (hc : 1 / 2 ≤ c.re) {t : Fin N → ℝ}
    (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) 1) {i j : Fin N} (hij : i < j) :
    ‖selbergF a b c t‖ ≤ ‖jacobiWeight a b t‖ * |t i - t j| := by
  rw [norm_selbergF (by linarith)]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc |vandermondeDelta t| ^ (2 * c.re) ≤ |vandermondeDelta t| ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge' (abs_nonneg _) (abs_vandermondeDelta_le_one ht)
          zero_le_one (by linarith)
    _ ≤ |t i - t j| := by rw [Real.rpow_one]; exact abs_vandermondeDelta_le_sub ht hij

theorem selbergF_eq_zero {N : ℕ} {a b c : ℂ} (hc : c ≠ 0) {t : Fin N → ℝ} {i j : Fin N}
    (hij : i < j) (h : t i = t j) : selbergF a b c t = 0 := by
  have hD : vandermondeDelta t = 0 :=
    prod_eq_zero (mem_univ i) (prod_eq_zero (mem_Ioi.mpr hij) (by rw [h, sub_self]))
  rw [selbergF, hD, abs_zero, Complex.ofReal_zero,
    Complex.zero_cpow (mul_ne_zero two_ne_zero hc), mul_zero]

/-! ### Integrability -/

theorem integrableOn_jacobiWeight {N : ℕ} {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    IntegrableOn (jacobiWeight a b) (Set.Icc (0 : Fin N → ℝ) 1) := by
  have h1 : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (a - 1) * ((1 - x : ℝ) : ℂ) ^ (b - 1))
      (Set.Icc 0 1) := by
    have h := Complex.betaIntegral_convergent ha hb
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one,
      ← integrableOn_Icc_iff_integrableOn_Ioc] at h
    refine h.congr_fun (fun x _ => ?_) measurableSet_Icc
    push_cast; ring
  unfold IntegrableOn jacobiWeight
  rw [← Set.pi_univ_Icc, volume_pi, Measure.restrict_pi_pi]
  exact Integrable.fintype_prod
    (f := fun _ (x : ℝ) => (x : ℂ) ^ (a - 1) * ((1 - x : ℝ) : ℂ) ^ (b - 1)) fun _ => h1

theorem integrableOn_cube_of_le {N : ℕ} {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    {f : (Fin N → ℝ) → ℂ} (hf : Measurable f)
    (hle : ∀ t, (∀ i, t i ∈ Set.Icc (0 : ℝ) 1) → ‖f t‖ ≤ ‖jacobiWeight a b t‖) :
    IntegrableOn f (Set.Icc (0 : Fin N → ℝ) 1) :=
  Integrable.mono' (integrableOn_jacobiWeight ha hb).norm hf.aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Icc).mpr
      (ae_of_all _ fun t ht => hle t (mem_cube_iff.mp ht)))

theorem measurable_initProd {N : ℕ} (k : ℕ) : Measurable (initProd (N := N) k) := by
  unfold initProd; fun_prop

theorem measurable_midProd {N : ℕ} (k : ℕ) : Measurable (midProd (N := N) k) := by
  unfold midProd; fun_prop

theorem measurable_selbergF {N : ℕ} (a b c : ℂ) : Measurable (selbergF (n := N) a b c) := by
  unfold selbergF jacobiWeight vandermondeDelta; fun_prop

/-! ### The first coordinate -/

theorem jacobiWeight_cons {a b : ℂ} (x : ℝ) (s : Fin n → ℝ) :
    jacobiWeight a b (Fin.cons x s : Fin (n + 1) → ℝ) =
      (x : ℂ) ^ (a - 1) * ((1 - x : ℝ) : ℂ) ^ (b - 1) * jacobiWeight a b s := by
  simp only [jacobiWeight, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem vandermondeDelta_cons (x : ℝ) (s : Fin n → ℝ) :
    vandermondeDelta (Fin.cons x s : Fin (n + 1) → ℝ) =
      (∏ i, (x - s i)) * vandermondeDelta s := by
  rw [vandermondeDelta, prod_pairs_succ]; simp only [Fin.cons_zero, Fin.cons_succ]; rfl

/-- The `t₀`-dependent factor `∏ⱼ |t₀ − sⱼ|^{2c}` of `|Δ|^{2c}`. -/
noncomputable def consE (c : ℂ) (s : Fin n → ℝ) (x : ℝ) : ℂ :=
  ∏ i, ((|x - s i| : ℝ) : ℂ) ^ (2 * c)

theorem selbergF_cons {a b c : ℂ} (x : ℝ) (s : Fin n → ℝ) :
    selbergF a b c (Fin.cons x s : Fin (n + 1) → ℝ) =
      (x : ℂ) ^ (a - 1) * ((1 - x : ℝ) : ℂ) ^ (b - 1) * consE c s x * selbergF a b c s := by
  rw [selbergF, selbergF, jacobiWeight_cons, vandermondeDelta_cons, abs_mul, abs_prod,
    Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (prod_nonneg fun _ _ => abs_nonneg _)
      (abs_nonneg _), ofReal_prod_cpow _ (fun _ _ => abs_nonneg _), consE]
  ring

theorem midProd_cons (k : ℕ) (x : ℝ) (s : Fin n → ℝ) :
    midProd k (Fin.cons x s : Fin (n + 1) → ℝ) = midProd k (Fin.cons 0 s : Fin (n + 1) → ℝ) := by
  refine prod_congr rfl fun i hi => ?_
  have h0 : i ≠ 0 := by
    rintro rfl; simp at hi
  obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr h0
  simp only [Fin.cons_succ]

/-! ### Derivatives in `t₀` -/

theorem cpow_sub_one_eq {z : ℂ} (hz : z ≠ 0) (w : ℂ) : z ^ (w - 1) = z ^ w / z := by
  rw [Complex.cpow_sub _ _ hz, Complex.cpow_one]

theorem hasDerivAt_affine_cpow {p q x : ℝ} (h : 0 < p + q * x) (w : ℂ) :
    HasDerivAt (fun y : ℝ => ((p + q * y : ℝ) : ℂ) ^ w)
      (w * ((p + q * x : ℝ) : ℂ) ^ (w - 1) * q) x := by
  have hsl : ((p : ℂ) + q * (x : ℂ)) ∈ Complex.slitPlane := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_add]; exact Complex.ofReal_mem_slitPlane.mpr h
  have h1 : HasDerivAt (fun z : ℂ => (p : ℂ) + q * z) q (x : ℂ) := by
    simpa using ((hasDerivAt_id (x : ℂ)).const_mul (q : ℂ)).const_add (p : ℂ)
  have h2 := (h1.cpow_const (c := w) hsl).comp_ofReal
  push_cast
  exact h2

/-- `d/dx |x − s|^w = w |x − s|^w / (x − s)` for `x ≠ s`. -/
theorem hasDerivAt_abs_sub_cpow {x s : ℝ} (hxs : x ≠ s) (w : ℂ) :
    HasDerivAt (fun y : ℝ => ((|y - s| : ℝ) : ℂ) ^ w)
      (w / (x - s) * ((|x - s| : ℝ) : ℂ) ^ w) x := by
  have hne : (x : ℂ) - s ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hxs)
  rcases lt_or_gt_of_ne hxs with h | h
  · have hd := hasDerivAt_affine_cpow (p := s) (q := -1) (x := x) (by linarith) w
    have hev : (fun y : ℝ => ((|y - s| : ℝ) : ℂ) ^ w) =ᶠ[nhds x]
        fun y : ℝ => ((s + -1 * y : ℝ) : ℂ) ^ w := by
      filter_upwards [eventually_lt_nhds h] with y hy
      rw [abs_of_neg (by linarith)]; congr 2; ring
    refine (hd.congr_of_eventuallyEq hev).congr_deriv ?_
    have hne' : ((s + -1 * x : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]; linarith
    rw [cpow_sub_one_eq hne', abs_of_neg (by linarith : x - s < 0)]
    have he : ((-(x - s) : ℝ) : ℂ) = ((s + -1 * x : ℝ) : ℂ) := by congr 1; ring
    rw [he]
    have he2 : ((s + -1 * x : ℝ) : ℂ) = -((x : ℂ) - s) := by push_cast; ring
    rw [he2]
    field_simp
    push_cast
    ring
  · have hd := hasDerivAt_affine_cpow (p := -s) (q := 1) (x := x) (by linarith) w
    have hev : (fun y : ℝ => ((|y - s| : ℝ) : ℂ) ^ w) =ᶠ[nhds x]
        fun y : ℝ => ((-s + 1 * y : ℝ) : ℂ) ^ w := by
      filter_upwards [eventually_gt_nhds h] with y hy
      rw [abs_of_pos (by linarith)]; congr 2; ring
    refine (hd.congr_of_eventuallyEq hev).congr_deriv ?_
    have hne' : ((-s + 1 * x : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]; linarith
    rw [cpow_sub_one_eq hne', abs_of_pos (by linarith : 0 < x - s)]
    have he : ((x - s : ℝ) : ℂ) = ((-s + 1 * x : ℝ) : ℂ) := by congr 1; ring
    rw [he]
    have he2 : ((-s + 1 * x : ℝ) : ℂ) = (x : ℂ) - s := by push_cast; ring
    rw [he2]
    field_simp
    push_cast
    ring

theorem hasDerivAt_consE {c : ℂ} {s : Fin n → ℝ} {x : ℝ} (hx : ∀ i, x ≠ s i) :
    HasDerivAt (consE c s) (consE c s x * ∑ i, 2 * c / (x - s i)) x := by
  classical
  have h := HasDerivAt.finsetProd (u := univ)
    (f := fun i (y : ℝ) => ((|y - s i| : ℝ) : ℂ) ^ (2 * c))
    (fun i _ => hasDerivAt_abs_sub_cpow (hx i) (2 * c))
  have hfun : (∏ i ∈ univ, fun y : ℝ => ((|y - s i| : ℝ) : ℂ) ^ (2 * c)) = consE c s := by
    ext y; simp [consE, Finset.prod_apply]
  rw [hfun] at h
  refine h.congr_deriv ?_
  rw [mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul, consE, ← mul_prod_erase _ _ (mem_univ i)]
  ring

/-- Aomoto's primitive in `t₀`: `x^a (1 − x)^b ∏ⱼ |x − sⱼ|^{2c}`. -/
noncomputable def aomotoU (a b c : ℂ) (s : Fin n → ℝ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ a * ((1 - x : ℝ) : ℂ) ^ b * consE c s x

theorem hasDerivAt_aomotoU {a b c : ℂ} {s : Fin n → ℝ} {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (hxs : ∀ i, x ≠ s i) :
    HasDerivAt (aomotoU a b c s)
      ((x : ℂ) ^ (a - 1) * ((1 - x : ℝ) : ℂ) ^ (b - 1) * consE c s x *
        (a * (1 - x) - b * x + 2 * c * ∑ i, (x : ℂ) * (1 - x) / (x - s i))) x := by
  have hX : HasDerivAt (fun y : ℝ => (y : ℂ) ^ a) (a * (x : ℂ) ^ (a - 1)) x := by
    simpa using hasDerivAt_affine_cpow (p := 0) (q := 1) (x := x) (by linarith) a
  have hY : HasDerivAt (fun y : ℝ => ((1 - y : ℝ) : ℂ) ^ b)
      (-(b * ((1 - x : ℝ) : ℂ) ^ (b - 1))) x := by
    have h := hasDerivAt_affine_cpow (p := 1) (q := -1) (x := x) (by linarith) b
    have he : (fun y : ℝ => ((1 + -1 * y : ℝ) : ℂ) ^ b) = fun y : ℝ => ((1 - y : ℝ) : ℂ) ^ b :=
      funext fun y => by congr 2; ring
    rw [he, show (1 : ℝ) + -1 * x = 1 - x by ring] at h
    refine h.congr_deriv ?_
    push_cast; ring
  have h := (hX.mul hY).mul (hasDerivAt_consE (c := c) hxs)
  simp only [Pi.mul_apply] at h
  refine h.congr_deriv ?_
  have hx0' : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0.ne'
  have hx1' : ((1 - x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have hXe : (x : ℂ) ^ a = (x : ℂ) ^ (a - 1) * x := by
    rw [cpow_sub_one_eq hx0', div_mul_cancel₀ _ hx0']
  have hYe : ((1 - x : ℝ) : ℂ) ^ b = ((1 - x : ℝ) : ℂ) ^ (b - 1) * ((1 - x : ℝ) : ℂ) := by
    rw [cpow_sub_one_eq hx1', div_mul_cancel₀ _ hx1']
  have hS1 : ∑ i, 2 * c / ((x : ℂ) - s i) = 2 * c * ∑ i, 1 / ((x : ℂ) - s i) := by
    rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
  have hS2 : ∑ i, (x : ℂ) * (1 - x) / (x - s i) = x * (1 - x) * ∑ i, 1 / ((x : ℂ) - s i) := by
    rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
  rw [hS1, hS2, hXe, hYe]
  push_cast
  ring

/-! ### The integrand `∂/∂t₀ (t₀(1 − t₀) ∏_{0<i<k} tᵢ Φ)` and its vanishing integral -/

/-- `∏_{0<i<k} tᵢ Φ(t) (a(1 − t₀) − b t₀ + 2c ∑_{j>0} t₀(1 − t₀)/(t₀ − tⱼ))`. -/
noncomputable def aomotoD (k : ℕ) (a b c : ℂ) (t : Fin (n + 1) → ℝ) : ℂ :=
  midProd k t * selbergF a b c t * (a * (1 - t 0) - b * t 0 +
    2 * c * ∑ j : Fin n, (t 0 : ℂ) * (1 - t 0) / (t 0 - t j.succ))

theorem aomotoD_cons (k : ℕ) (a b c : ℂ) (x : ℝ) (s : Fin n → ℝ) :
    aomotoD k a b c (Fin.cons x s) = midProd k (Fin.cons 0 s : Fin (n + 1) → ℝ) *
      ((x : ℂ) ^ (a - 1) * ((1 - x : ℝ) : ℂ) ^ (b - 1) * consE c s x *
        (a * (1 - x) - b * x + 2 * c * ∑ i, (x : ℂ) * (1 - x) / (x - s i))) *
      selbergF a b c s := by
  rw [aomotoD, midProd_cons, selbergF_cons]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring

theorem integral_aomotoD_slice {k : ℕ} {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (hc : 0 < c.re) (s : Fin n → ℝ)
    (hi : Integrable (fun x => aomotoD k a b c (Fin.cons x s)) (volume.restrict (Set.Icc 0 1))) :
    ∫ x in Set.Icc (0 : ℝ) 1, aomotoD k a b c (Fin.cons x s) = 0 := by
  set M := midProd k (Fin.cons 0 s : Fin (n + 1) → ℝ)
  set R := selbergF a b c s
  have hpow : ∀ w : ℂ, 0 < w.re → Continuous fun x : ℝ => (x : ℂ) ^ w := fun w hw =>
    continuous_iff_continuousAt.mpr fun x => Complex.continuousAt_ofReal_cpow_const x w (Or.inl hw)
  have hcont : Continuous (aomotoU a b c s) := by
    have hc2 : 0 < (2 * c).re := by simp; positivity
    unfold aomotoU consE
    exact ((hpow a ha).mul ((hpow b hb).comp (continuous_const.sub continuous_id))).mul
      (continuous_finsetProd _ fun i _ =>
        (hpow _ hc2).comp (continuous_id.sub continuous_const).abs)
  have hFTC := integral_eq_of_hasDerivAt_off_countable_of_le
    (fun x => M * aomotoU a b c s x * R) (fun x => aomotoD k a b c (Fin.cons x s)) zero_le_one
    (Set.finite_range s).countable
    ((continuous_const.mul hcont).mul continuous_const).continuousOn
    (fun x hx => by
      obtain ⟨⟨hx0, hx1⟩, hxs⟩ := hx
      have hxs' : ∀ i, x ≠ s i := fun i h => hxs ⟨i, h.symm⟩
      rw [aomotoD_cons]
      exact ((hasDerivAt_aomotoU hx0 hx1 hxs').const_mul M).mul_const R)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
      ((show IntegrableOn (fun x => aomotoD k a b c (Fin.cons x s : Fin (n + 1) → ℝ))
        (Set.Icc (0 : ℝ) 1) volume from by unfold IntegrableOn; exact hi).mono_set
          Set.Ioc_subset_Icc_self))
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one, hFTC]
  have ha0 : a ≠ 0 := fun h => by rw [h] at ha; simp at ha
  have hb0 : b ≠ 0 := fun h => by rw [h] at hb; simp at hb
  simp [aomotoU, Complex.zero_cpow ha0, Complex.zero_cpow hb0]

/-- `∫_{[0,1]^{n+1}} ∂/∂t₀(…) = 0`, by Fubini and the slice computation. -/
theorem integral_aomotoD {k : ℕ} {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 < c.re)
    (hint : IntegrableOn (aomotoD k a b c) (Set.Icc (0 : Fin (n + 1) → ℝ) 1)) :
    ∫ t in Set.Icc (0 : Fin (n + 1) → ℝ) 1, aomotoD k a b c t = 0 := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have hmp : MeasurePreserving e.symm (volume.prod volume) volume :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm _
  have he : ∀ p : ℝ × (Fin n → ℝ), e.symm p = Fin.cons p.1 p.2 := fun p => by
    simp [e, MeasurableEquiv.piFinSuccAbove]; rfl
  have hpre : e.symm ⁻¹' Set.Icc (0 : Fin (n + 1) → ℝ) 1 =
      Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : Fin n → ℝ) 1 := by
    ext ⟨x, s⟩
    simp only [Set.mem_preimage, he, Set.mem_Icc, Set.mem_prod, Pi.le_def, Fin.forall_fin_succ,
      Fin.cons_zero, Fin.cons_succ, Pi.zero_apply, Pi.one_apply]
    tauto
  have hint' := (hmp.integrableOn_comp_preimage e.symm.measurableEmbedding).mpr hint
  rw [hpre, IntegrableOn, ← Measure.prod_restrict] at hint'
  have hint'' : Integrable (fun p => aomotoD k a b c (e.symm p))
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume.restrict (Set.Icc (0 : Fin n → ℝ) 1))) :=
    hint'
  rw [← hmp.setIntegral_preimage_emb e.symm.measurableEmbedding, hpre, ← Measure.prod_restrict,
    integral_prod_symm _ hint'']
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hint''.prod_left_ae] with s hs
  simp only [he] at hs ⊢
  exact integral_aomotoD_slice ha hb hc s hs

/-! ### Integrability for `ℜc ≥ 1/2` -/

theorem integrableOn_initProd_mul {N k : ℕ} {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (hc : 0 < c.re) :
    IntegrableOn (fun t => initProd k t * selbergF a b c t) (Set.Icc (0 : Fin N → ℝ) 1) :=
  integrableOn_cube_of_le ha hb ((measurable_initProd k).mul (measurable_selbergF a b c))
    fun _ ht => by
      rw [norm_mul]
      exact (mul_le_mul (norm_initProd_le ht) (norm_selbergF_le hc ht) (norm_nonneg _)
        zero_le_one).trans (one_mul _).le

theorem integrableOn_midProd_mul {N k : ℕ} {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (hc : 0 < c.re) :
    IntegrableOn (fun t => midProd k t * selbergF a b c t) (Set.Icc (0 : Fin N → ℝ) 1) :=
  integrableOn_cube_of_le ha hb ((measurable_midProd k).mul (measurable_selbergF a b c))
    fun _ ht => by
      rw [norm_mul]
      exact (mul_le_mul (norm_midProd_le ht) (norm_selbergF_le hc ht) (norm_nonneg _)
        zero_le_one).trans (one_mul _).le

/-- `∏_{0<i<k} tᵢ · Φ(t) · t₀(1 − t₀)/(t₀ − t_{j+1})`. -/
noncomputable def aomotoH (k : ℕ) (a b c : ℂ) (j : Fin n) (t : Fin (n + 1) → ℝ) : ℂ :=
  midProd k t * selbergF a b c t * ((t 0 : ℂ) * (1 - t 0) / (t 0 - t j.succ))

theorem norm_quot_mul_le {u v : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    ‖(u : ℂ) * (1 - u) / (u - v)‖ * |u - v| ≤ 1 := by
  have he : (u : ℂ) * (1 - u) / (u - v) = ((u * (1 - u) / (u - v) : ℝ) : ℂ) := by push_cast; ring
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_div]
  rcases eq_or_ne (u - v) 0 with h | h
  · rw [h]; simp
  · rw [div_mul_cancel₀ _ (abs_ne_zero.mpr h), abs_mul, abs_of_nonneg hu.1,
      abs_of_nonneg (by linarith [hu.2] : 0 ≤ 1 - u)]
    nlinarith [hu.1, hu.2]

theorem integrableOn_aomotoH {k : ℕ} {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (hc : 1 / 2 ≤ c.re) (j : Fin n) :
    IntegrableOn (aomotoH k a b c j) (Set.Icc (0 : Fin (n + 1) → ℝ) 1) := by
  refine integrableOn_cube_of_le ha hb (by unfold aomotoH; exact
    ((measurable_midProd k).mul (measurable_selbergF a b c)).mul (by fun_prop)) fun t ht => ?_
  have hq := norm_quot_mul_le (v := t j.succ) (ht 0)
  have hΦ := norm_selbergF_le_sub (a := a) (b := b) hc ht (Fin.succ_pos j)
  rw [aomotoH, norm_mul, norm_mul]
  calc ‖midProd k t‖ * ‖selbergF a b c t‖ * ‖(t 0 : ℂ) * (1 - t 0) / (t 0 - t j.succ)‖
      ≤ 1 * (‖jacobiWeight a b t‖ * |t 0 - t j.succ|) *
          ‖(t 0 : ℂ) * (1 - t 0) / (t 0 - t j.succ)‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul (norm_midProd_le ht) hΦ (norm_nonneg _)
          zero_le_one) (norm_nonneg _)
    _ = ‖jacobiWeight a b t‖ * (‖(t 0 : ℂ) * (1 - t 0) / (t 0 - t j.succ)‖ *
          |t 0 - t j.succ|) := by ring
    _ ≤ ‖jacobiWeight a b t‖ * 1 := mul_le_mul_of_nonneg_left hq (norm_nonneg _)
    _ = ‖jacobiWeight a b t‖ := mul_one _

theorem aomotoD_eq {k : ℕ} (hk : 0 < k) (a b c : ℂ) (t : Fin (n + 1) → ℝ) :
    aomotoD k a b c t = a * (midProd k t * selbergF a b c t) -
      (a + b) * (initProd k t * selbergF a b c t) + 2 * c * ∑ j, aomotoH k a b c j t := by
  rw [aomotoD, initProd_eq_mul hk]
  simp only [aomotoH, mul_add, mul_sum]
  have : ∀ j : Fin n, midProd k t * selbergF a b c t *
      (2 * c * ((t 0 : ℂ) * (1 - t 0) / (t 0 - t j.succ))) =
      2 * c * (midProd k t * selbergF a b c t * ((t 0 : ℂ) * (1 - t 0) / (t 0 - t j.succ))) :=
    fun j => by ring
  simp only [this]
  ring

/-! ### Symmetrization under `t₀ ↔ tⱼ` -/

theorem swap_apply_val_zero (j : Fin n) :
    (((Equiv.swap (0 : Fin (n + 1)) j.succ) 0 : Fin (n + 1)) : ℕ) = (j : ℕ) + 1 := by
  rw [Equiv.swap_apply_left, Fin.val_succ]

theorem pair_sum_eq {u v : ℂ} (h : u ≠ v) :
    u * (1 - u) / (u - v) + v * (1 - v) / (v - u) = 1 - u - v := by
  have h1 : u - v ≠ 0 := sub_ne_zero.mpr h
  have h2 : v - u ≠ 0 := sub_ne_zero.mpr h.symm
  field_simp
  ring

theorem pair_sum_eq' {u v : ℂ} (h : u ≠ v) :
    (1 - u) / (u - v) + (1 - v) / (v - u) = -1 := by
  have h1 : u - v ≠ 0 := sub_ne_zero.mpr h
  have h2 : v - u ≠ 0 := sub_ne_zero.mpr h.symm
  field_simp
  ring

/-- For `j + 1 ≥ k`: `H(t) + H(t ∘ σ) = ∏_{0<i<k} tᵢ Φ − t₀∏ Φ − (t₀∏ Φ)∘σ`. -/
theorem aomotoH_add_swap_ge {k : ℕ} (hk : 0 < k) {a b c : ℂ} (hc : c ≠ 0) {j : Fin n}
    (hj : k ≤ (j : ℕ) + 1) (t : Fin (n + 1) → ℝ) :
    aomotoH k a b c j t + aomotoH k a b c j (t ∘ Equiv.swap 0 j.succ) =
      midProd k t * selbergF a b c t - initProd k t * selbergF a b c t -
        initProd k (t ∘ Equiv.swap 0 j.succ) * selbergF a b c (t ∘ Equiv.swap 0 j.succ) := by
  set σ := Equiv.swap (0 : Fin (n + 1)) j.succ
  have hmid : midProd k (t ∘ σ) = midProd k t := by
    refine midProd_comp σ (fun i => ?_) t
    by_cases h0 : i = 0
    · subst h0; simp [σ, Equiv.swap_apply_left]; omega
    by_cases h1 : i = j.succ
    · subst h1; simp [σ, Equiv.swap_apply_right]; omega
    · rw [show σ i = i from Equiv.swap_apply_of_ne_of_ne h0 h1]
  have hΦ : selbergF a b c (t ∘ σ) = selbergF a b c t := selbergF_comp σ t
  have h0 : (t ∘ σ) 0 = t j.succ := by simp [σ]
  have hs : (t ∘ σ) j.succ = t 0 := by simp [σ]
  rw [initProd_eq_mul hk, initProd_eq_mul hk, hmid, hΦ, h0]
  simp only [aomotoH, hmid, hΦ, h0, hs]
  by_cases he : t 0 = t j.succ
  · rw [selbergF_eq_zero hc (Fin.succ_pos j) he]; ring
  · have := pair_sum_eq (u := (t 0 : ℂ)) (v := (t j.succ : ℂ)) (by exact_mod_cast he)
    linear_combination midProd k t * selbergF a b c t * this

/-- For `j + 1 < k`: `H(t) + H(t ∘ σ) = −t₀⋯t_{k−1} Φ`. -/
theorem aomotoH_add_swap_lt {k : ℕ} (hk : 0 < k) {a b c : ℂ} (hc : c ≠ 0) {j : Fin n}
    (hj : (j : ℕ) + 1 < k) (t : Fin (n + 1) → ℝ) :
    aomotoH k a b c j t + aomotoH k a b c j (t ∘ Equiv.swap 0 j.succ) =
      -(initProd k t * selbergF a b c t) := by
  set σ := Equiv.swap (0 : Fin (n + 1)) j.succ
  have hinit : initProd k (t ∘ σ) = initProd k t := by
    refine initProd_comp σ (fun i => ?_) t
    by_cases h0 : i = 0
    · subst h0; simp [σ, Equiv.swap_apply_left]; omega
    by_cases h1 : i = j.succ
    · subst h1; simp [σ, Equiv.swap_apply_right]; omega
    · rw [show σ i = i from Equiv.swap_apply_of_ne_of_ne h0 h1]
  have hΦ : selbergF a b c (t ∘ σ) = selbergF a b c t := selbergF_comp σ t
  have h0 : (t ∘ σ) 0 = t j.succ := by simp [σ]
  have hs : (t ∘ σ) j.succ = t 0 := by simp [σ]
  have hm : (t j.succ : ℂ) * midProd k (t ∘ σ) = t 0 * midProd k t := by
    rw [← h0, ← initProd_eq_mul hk, ← initProd_eq_mul hk, hinit]
  simp only [aomotoH, hΦ, h0, hs]
  rw [initProd_eq_mul hk]
  by_cases he : t 0 = t j.succ
  · rw [selbergF_eq_zero hc (Fin.succ_pos j) he]; ring
  · have := pair_sum_eq' (u := (t 0 : ℂ)) (v := (t j.succ : ℂ)) (by exact_mod_cast he)
    have e1 : midProd k (t ∘ σ) * selbergF a b c t * ((t j.succ : ℂ) * (1 - t j.succ) /
        (t j.succ - t 0)) = (t 0 * midProd k t) * selbergF a b c t *
          ((1 - t j.succ) / (t j.succ - t 0)) := by
      rw [← hm]; ring
    rw [e1]
    linear_combination (t 0 * midProd k t) * selbergF a b c t * this

/-! ### The recursion for `ℜc ≥ 1/2` -/

theorem integral_aomotoH {k : ℕ} (hk : 0 < k) {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (hc : 1 / 2 ≤ c.re) (j : Fin n) :
    ∫ t in Set.Icc (0 : Fin (n + 1) → ℝ) 1, aomotoH k a b c j t =
      if (j : ℕ) + 1 < k then -aomotoA (n + 1) k a b c / 2
      else (∫ t in Set.Icc (0 : Fin (n + 1) → ℝ) 1, midProd k t * selbergF a b c t) / 2 -
        aomotoA (n + 1) k a b c := by
  have hc0 : 0 < c.re := by linarith
  have hcne : c ≠ 0 := fun h => by rw [h] at hc0; simp at hc0
  set σ := Equiv.swap (0 : Fin (n + 1)) j.succ
  have hI := integrableOn_aomotoH (k := k) ha hb hc j
  have hsum : ∫ t in Set.Icc (0 : Fin (n + 1) → ℝ) 1,
      (aomotoH k a b c j t + aomotoH k a b c j (t ∘ σ)) =
        2 * ∫ t in Set.Icc (0 : Fin (n + 1) → ℝ) 1, aomotoH k a b c j t := by
    rw [integral_add hI (integrableOn_cube_comp σ hI), integral_cube_comp σ]; ring
  have hg1 := integrableOn_midProd_mul (N := n + 1) (k := k) ha hb hc0
  have hg2 := integrableOn_initProd_mul (N := n + 1) (k := k) ha hb hc0
  split_ifs with hj
  · rw [setIntegral_congr_fun measurableSet_Icc
      (fun t _ => aomotoH_add_swap_lt hk hcne hj t), integral_neg] at hsum
    unfold aomotoA
    linear_combination (-1 / 2 : ℂ) * hsum
  · rw [setIntegral_congr_fun measurableSet_Icc
      (fun t _ => aomotoH_add_swap_ge hk hcne (by omega) t)] at hsum
    have hcomp := integral_cube_comp σ (fun t => initProd k t * selbergF a b c t)
    have hd : IntegrableOn (fun t => midProd k t * selbergF a b c t -
        initProd k t * selbergF a b c t) (Set.Icc 0 1) := hg1.sub hg2
    have hd2 : IntegrableOn (fun t => initProd k (t ∘ σ) * selbergF a b c (t ∘ σ))
        (Set.Icc 0 1) := integrableOn_cube_comp σ hg2
    rw [integral_sub hd hd2, integral_sub hg1 hg2, hcomp] at hsum
    unfold aomotoA
    linear_combination (-1 / 2 : ℂ) * hsum

theorem sum_fin_ite_succ_lt {M : Type*} [AddCommMonoid M] {k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ n + 1) (X Y : M) :
    ∑ j : Fin n, (if (j : ℕ) + 1 < k then X else Y) = (k - 1) • X + (n + 1 - k) • Y := by
  rw [Fin.sum_univ_eq_sum_range (fun j => if j + 1 < k then X else Y), sum_ite, sum_const,
    sum_const]
  have h1 : (range n).filter (fun j => j + 1 < k) = range (k - 1) := by
    ext j; simp only [mem_filter, mem_range]; omega
  have h2 : (range n).filter (fun j => ¬ j + 1 < k) = Ico (k - 1) n := by
    ext j; simp only [mem_filter, mem_range, mem_Ico]; omega
  rw [h1, h2, card_range, Nat.card_Ico]
  congr 2
  omega

/-- **Aomoto's recursion** for `ℜc ≥ 1/2`:
`(a + (N − k)c) A_{k−1} = (a + b + (2N − k − 1)c) A_k`, `N = n + 1`. -/
theorem aomoto_recursion_half {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n + 1) {a b c : ℂ}
    (ha : 0 < a.re) (hb : 0 < b.re) (hc : 1 / 2 ≤ c.re) :
    (a + ((n : ℂ) + 1 - k) * c) * aomotoA (n + 1) (k - 1) a b c =
      (a + b + (2 * ((n : ℂ) + 1) - k - 1) * c) * aomotoA (n + 1) k a b c := by
  have hk0 : 0 < k := hk
  have hc0 : 0 < c.re := by linarith
  have hg1 := integrableOn_midProd_mul (N := n + 1) (k := k) ha hb hc0
  have hg2 := integrableOn_initProd_mul (N := n + 1) (k := k) ha hb hc0
  have hH := fun j : Fin n => integrableOn_aomotoH (k := k) ha hb hc j
  have hB : ∫ t in Set.Icc (0 : Fin (n + 1) → ℝ) 1, midProd k t * selbergF a b c t =
      aomotoA (n + 1) (k - 1) a b c := by
    have hcomp := integral_cube_comp (finRotate (n + 1))
      (fun t => initProd (k - 1) t * selbergF a b c t)
    rw [aomotoA, ← hcomp]
    refine setIntegral_congr_fun measurableSet_Icc fun t _ => ?_
    rw [midProd_eq_initProd_rotate hk0 hkn, selbergF_comp]
  have hDeq : ∀ t : Fin (n + 1) → ℝ, aomotoD k a b c t = a * (midProd k t * selbergF a b c t) -
      (a + b) * (initProd k t * selbergF a b c t) + 2 * c * ∑ j, aomotoH k a b c j t :=
    aomotoD_eq hk0 a b c
  have hS : IntegrableOn (fun t => ∑ j, aomotoH k a b c j t)
      (Set.Icc (0 : Fin (n + 1) → ℝ) 1) := integrable_finsetSum _ fun j _ => hH j
  have hA : IntegrableOn (fun t => a * (midProd k t * selbergF a b c t))
      (Set.Icc (0 : Fin (n + 1) → ℝ) 1) := hg1.const_mul a
  have hA2 : IntegrableOn (fun t => (a + b) * (initProd k t * selbergF a b c t))
      (Set.Icc (0 : Fin (n + 1) → ℝ) 1) := hg2.const_mul _
  have hC : IntegrableOn (fun t => 2 * c * ∑ j, aomotoH k a b c j t)
      (Set.Icc (0 : Fin (n + 1) → ℝ) 1) := hS.const_mul _
  have hAB : IntegrableOn (fun t => a * (midProd k t * selbergF a b c t) -
      (a + b) * (initProd k t * selbergF a b c t)) (Set.Icc (0 : Fin (n + 1) → ℝ) 1) :=
    hA.sub hA2
  have hDint : IntegrableOn (aomotoD k a b c) (Set.Icc (0 : Fin (n + 1) → ℝ) 1) :=
    (hAB.add hC).congr_fun (fun t _ => (hDeq t).symm) measurableSet_Icc
  have h0 := integral_aomotoD ha hb hc0 hDint
  rw [setIntegral_congr_fun measurableSet_Icc (fun t _ => hDeq t), integral_add hAB hC,
    integral_sub hA hA2, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_finsetSum _ fun j _ => hH j] at h0
  simp only [integral_aomotoH hk0 ha hb hc] at h0
  rw [sum_fin_ite_succ_lt hk hkn, hB, nsmul_eq_mul, nsmul_eq_mul, Nat.cast_sub hk,
    Nat.cast_sub hkn] at h0
  rw [← aomotoA] at h0
  push_cast at h0
  linear_combination h0

/-! ### Continuation to `ℜc > 0` -/

/-- `c ↦ A_k(a, b, c)` is holomorphic on `ℜc > 0`. -/
theorem differentiableOn_aomotoA {N k : ℕ} {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    DifferentiableOn ℂ (fun c => aomotoA N k a b c) {c : ℂ | 0 < c.re} := by
  unfold aomotoA
  refine differentiableOn_integral_of_holo
    (F := fun c t => initProd k t * selbergF a b c t)
    (F' := fun c t => initProd k t * (jacobiWeight a b t *
      (((|vandermondeDelta t| : ℝ) : ℂ) ^ (2 * c) *
        Complex.log ((|vandermondeDelta t| : ℝ) : ℂ) * 2))) ?_ ?_ ?_
  · intro z _
    exact ((measurable_initProd k).mul (measurable_selbergF a b z)).aestronglyMeasurable
  · intro z _
    refine ((measurable_initProd k).mul ?_).aestronglyMeasurable
    unfold jacobiWeight vandermondeDelta
    fun_prop
  · intro z₀ hz₀
    have hz₀' : 0 < z₀.re := hz₀
    have hre : ∀ z ∈ Metric.closedBall z₀ (2 * (z₀.re / 4)), z₀.re / 2 ≤ z.re := by
      intro z hz
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      have := Complex.abs_re_le_norm (z - z₀)
      rw [Complex.sub_re] at this
      have := (abs_le.mp (this.trans hz)).1
      linarith
    refine ⟨z₀.re / 4, by positivity, fun z hz => ?_, fun t => ‖jacobiWeight a b t‖,
      (integrableOn_jacobiWeight ha hb).norm, ae_of_all _ fun t z hz => ?_,
      (ae_restrict_iff' measurableSet_Icc).mpr (ae_of_all _ fun t ht z hz => ?_)⟩
    · have := hre z (Metric.ball_subset_closedBall
        (Metric.ball_subset_ball (by linarith) hz))
      show 0 < z.re
      linarith
    · have hz0 : 0 < z.re := by linarith [hre z hz]
      have hzne : z ≠ 0 := fun h => by rw [h] at hz0; simp at hz0
      simp only [selbergF]
      rcases eq_or_lt_of_le (abs_nonneg (vandermondeDelta t)) with hD | hD
      · rw [← hD]
        have hev : (fun c => initProd k t * (jacobiWeight a b t *
            (((0 : ℝ) : ℂ) ^ (2 * c)))) =ᶠ[nhds z] fun _ => 0 := by
          filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz0]
            with c hc
          have hc' : c ≠ 0 := fun h => by rw [h] at hc; simp at hc
          rw [Complex.ofReal_zero, Complex.zero_cpow (mul_ne_zero two_ne_zero hc')]; ring
        rw [Complex.ofReal_zero, Complex.zero_cpow (mul_ne_zero two_ne_zero hzne)]
        simpa using (hasDerivAt_const z (0 : ℂ)).congr_of_eventuallyEq
          (by simpa [Complex.ofReal_zero] using hev)
      · have h2 : HasDerivAt (fun c : ℂ => 2 * c) 2 z := by
          simpa using (hasDerivAt_id z).const_mul (2 : ℂ)
        have h3 := h2.const_cpow (c := ((|vandermondeDelta t| : ℝ) : ℂ))
          (Or.inl (Complex.ofReal_ne_zero.mpr hD.ne'))
        exact (h3.const_mul (jacobiWeight a b t)).const_mul (initProd k t)
    · have hz0 : 0 < z.re := by linarith [hre z hz]
      have ht' := mem_cube_iff.mp ht
      rw [norm_mul]
      exact (mul_le_mul (norm_initProd_le ht') (norm_selbergF_le hz0 ht') (norm_nonneg _)
        zero_le_one).trans (one_mul _).le

/-- **Aomoto's recursion** for `ℜa, ℜb, ℜc > 0`:
`(a + (N − k)c) A_{k−1} = (a + b + (2N − k − 1)c) A_k`, `N = n + 1`. -/
theorem aomoto_recursion {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n + 1) {a b c : ℂ}
    (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 < c.re) :
    (a + ((n : ℂ) + 1 - k) * c) * aomotoA (n + 1) (k - 1) a b c =
      (a + b + (2 * ((n : ℂ) + 1) - k - 1) * c) * aomotoA (n + 1) k a b c := by
  set U := {c : ℂ | 0 < c.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  set f : ℂ → ℂ := fun c => (a + ((n : ℂ) + 1 - k) * c) * aomotoA (n + 1) (k - 1) a b c -
    (a + b + (2 * ((n : ℂ) + 1) - k - 1) * c) * aomotoA (n + 1) k a b c with hfdef
  have hlin : ∀ p q : ℂ, DifferentiableOn ℂ (fun c : ℂ => p + q * c) U := fun p q =>
    ((differentiable_const p).add
      ((differentiable_const q).mul differentiable_id)).differentiableOn
  have hf : DifferentiableOn ℂ f U :=
    ((hlin _ _).mul (differentiableOn_aomotoA ha hb)).sub
      ((hlin _ _).mul (differentiableOn_aomotoA ha hb))
  have hz : f =ᶠ[nhds 1] 0 := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 / 2 : ℝ) < (1 : ℂ).re by norm_num)] with c hc'
    simp only [hfdef, Pi.zero_apply]
    rw [aomoto_recursion_half hk hkn ha hb (le_of_lt hc'), sub_self]
  have h := (hf.analyticOnNhd hU).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_halfSpace_re_gt 0).isPreconnected (show (1 : ℂ) ∈ U by simp [U]) hz hc
  exact sub_eq_zero.mp h

/-! ### DLMF 5.14.4 -/

theorem aomotoA_zero {N : ℕ} (a b c : ℂ) :
    aomotoA N 0 a b c = ∫ t in Set.Icc (0 : Fin N → ℝ) 1, selbergF a b c t := by
  simp [aomotoA, initProd]

theorem selbergRHS_succ (N k : ℕ) (a b c : ℂ) :
    selbergRHS N (k + 1) a b c = selbergRHS N k a b c *
      ((a + ((N : ℂ) - (k + 1)) * c) / (a + b + (2 * N - (k + 1) - 1) * c)) := by
  rw [selbergRHS, selbergRHS, prod_range_succ]; ring

theorem aomotoA_eq {k : ℕ} (hkn : k ≤ n + 1) {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (hc : 0 < c.re) : aomotoA (n + 1) k a b c = selbergRHS (n + 1) k a b c := by
  induction k with
  | zero => rw [aomotoA_zero, dlmf_5_14_4_selberg ha hb hc]
  | succ k ih =>
    have h := aomoto_recursion (k := k + 1) (by omega) hkn ha hb hc
    rw [Nat.add_sub_cancel, ih (by omega)] at h
    have hkn' : (k : ℝ) ≤ n := by exact_mod_cast (by omega : k ≤ n)
    have hden : a + b + (2 * ((n + 1 : ℕ) : ℂ) - ((k : ℂ) + 1) - 1) * c ≠ 0 := by
      intro h0
      have := congrArg Complex.re h0
      simp only [Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.natCast_re,
        Complex.natCast_im, Complex.one_re, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat,
        Complex.zero_re, Complex.sub_im, Complex.mul_im, Complex.add_im] at this
      push_cast at this
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * n - k) hc.le]
    rw [selbergRHS_succ]
    push_cast at h hden ⊢
    rw [mul_div_assoc', eq_div_iff hden]
    linear_combination -h

/-- **DLMF 5.14.4** (Selberg's integral with Aomoto's factor) for `0 ≤ m ≤ n`,
`ℜa, ℜb, ℜc > 0`: `∫_{[0,1]ⁿ} t₁⋯tₘ ∏ tₖ^{a−1}(1 − tₖ)^{b−1} |Δ(t)|^{2c} dt =
∏_{k=1}^m (a+(n−k)c)/(a+b+(2n−k−1)c) ·
∏_{k=1}^n Γ(a+(n−k)c)Γ(b+(n−k)c)Γ(1+kc)/(Γ(a+b+(2n−k−1)c)Γ(1+c))`. -/
theorem dlmf_5_14_4 {m : ℕ} (hm : m ≤ n) {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (hc : 0 < c.re) :
    ∫ t in Set.Icc (0 : Fin n → ℝ) 1,
      (∏ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < m), (t i : ℂ)) * selbergF a b c t =
        selbergRHS n m a b c := by
  cases n with
  | zero =>
    obtain rfl : m = 0 := by omega
    show aomotoA 0 0 a b c = _
    rw [aomotoA_zero, dlmf_5_14_4_selberg ha hb hc]
  | succ n => exact aomotoA_eq hm ha hb hc

end Azurite.DLMF
