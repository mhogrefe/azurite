/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# DLMF §3.5(x): cubature formulas

* **3.5.47** `dlmf_3_5_47` (`diskRem`, the disk `x² + y² ≤ h²`, `diskSet`) and **3.5.48**
  `dlmf_3_5_48` (`squareRem`, the square `|x|, |y| ≤ h`, `squareSet`); rules `(w, ξ, η)` with
  nodes `(ξh, ηh)` (`cubSum`, `cubRem`).
* The meaning of `R = O(hᵏ)` in Table 3.5.21: `cubRem_le_of_exact` — a rule exact for all
  monomials `xᵃyᵇ`, `a + b < k`, with nodes in the square of side `2h`, has `|R| ≤ C hᵏ` for every
  `f ∈ Cᵏ` (Taylor's formula with integral remainder, `map_add_eq_sum_add_integral_iteratedFDeriv`;
  the Taylor terms `D^j f(0)(y, …, y)` are combinations of monomials, `multilinear_diag_eq`);
  `diskRem_isBigO`, `squareRem_isBigO`.
* Moments: `∬_D xᵃyᵇ = h^{a+b+2}/(a+b+2) Θ(a, b)` in polar coordinates (`integral_diskSet_mono`)
  with `Θ(a, b) = ∫_{−π}^{π} cosᵃθ sinᵇθ dθ` (`trigMom`, odd cases by symmetry, `trigMom_swap`,
  values `trigMom_eq_thetaQ`), `∬_S xᵃyᵇ` as a product (`integral_squareSet_mono`); areas
  `volume_diskSet` (`πh²`), `volume_squareSet` (`4h²`).

Table 3.5.21: `Section5CubatureTable`; the Monte Carlo remark: `Section5MonteCarlo`.
-/

open Set Filter Topology MeasureTheory Finset

namespace Azurite.DLMF

/-! ### Rules and remainders -/

/-- A cubature rule: a list of `(w, ξ, η)`; applied at scale `h` it is `∑ w f(ξh, ηh)`. -/
def cubSum (r : List (ℝ × ℝ × ℝ)) (h : ℝ) (f : ℝ × ℝ → ℝ) : ℝ :=
  (r.map fun q => q.1 * f (q.2.1 * h, q.2.2 * h)).sum

/-- The remainder `R = c ∬_S f − ∑ w f(ξh, ηh)`. -/
noncomputable def cubRem (S : Set (ℝ × ℝ)) (c : ℝ) (r : List (ℝ × ℝ × ℝ)) (h : ℝ)
    (f : ℝ × ℝ → ℝ) : ℝ :=
  c * (∫ p in S, f p) - cubSum r h f

theorem cubSum_add (r : List (ℝ × ℝ × ℝ)) (h : ℝ) (f g : ℝ × ℝ → ℝ) :
    cubSum r h (f + g) = cubSum r h f + cubSum r h g := by
  induction r with
  | nil => simp [cubSum]
  | cons q r ih => simp only [cubSum, List.map_cons, List.sum_cons] at ih ⊢; rw [ih]; simp; ring

theorem cubSum_smul (r : List (ℝ × ℝ × ℝ)) (h a : ℝ) (f : ℝ × ℝ → ℝ) :
    cubSum r h (fun p => a * f p) = a * cubSum r h f := by
  induction r with
  | nil => simp [cubSum]
  | cons q r ih => simp only [cubSum, List.map_cons, List.sum_cons] at ih ⊢; rw [ih]; ring

theorem cubRem_add {S : Set (ℝ × ℝ)} {c : ℝ} {r : List (ℝ × ℝ × ℝ)} {h : ℝ} {f g : ℝ × ℝ → ℝ}
    (hf : IntegrableOn f S) (hg : IntegrableOn g S) :
    cubRem S c r h (f + g) = cubRem S c r h f + cubRem S c r h g := by
  unfold cubRem
  rw [cubSum_add, show (∫ p in S, (f + g) p) = ∫ p in S, f p + g p from rfl,
    integral_add hf hg]
  ring

theorem cubRem_smul (S : Set (ℝ × ℝ)) (c : ℝ) (r : List (ℝ × ℝ × ℝ)) (h a : ℝ)
    (f : ℝ × ℝ → ℝ) : cubRem S c r h (fun p => a * f p) = a * cubRem S c r h f := by
  unfold cubRem
  rw [cubSum_smul, integral_const_mul]
  ring

theorem cubRem_sum {S : Set (ℝ × ℝ)} {c : ℝ} {r : List (ℝ × ℝ × ℝ)} {h : ℝ} {ι : Type*}
    (s : Finset ι) {f : ι → ℝ × ℝ → ℝ} (hf : ∀ i ∈ s, IntegrableOn (f i) S) :
    cubRem S c r h (fun p => ∑ i ∈ s, f i p) = ∑ i ∈ s, cubRem S c r h (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    unfold cubRem cubSum
    simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, ← ih fun j hj => hf j (Finset.mem_insert_of_mem hj)]
    have e : (fun p => ∑ j ∈ insert i s, f j p) = f i + fun p => ∑ j ∈ s, f j p := by
      ext p; simp [Finset.sum_insert hi]
    rw [e, cubRem_add (hf i (Finset.mem_insert_self _ _))]
    exact integrable_finsetSum _ fun j hj => hf j (Finset.mem_insert_of_mem hj)

/-! ### Multilinear forms are combinations of monomials -/

/-- The coordinates `y ↦ y₁`, `y ↦ y₂`. -/
def coord (i : Fin 2) (y : ℝ × ℝ) : ℝ := if i = 0 then y.1 else y.2

/-- The unit vectors. -/
def coordVec (i : Fin 2) : ℝ × ℝ := if i = 0 then (1, 0) else (0, 1)

theorem sum_coord_smul (y : ℝ × ℝ) : ∑ i : Fin 2, coord i y • coordVec i = y := by
  simp [Fin.sum_univ_two, coord, coordVec]

theorem prod_coord {j : ℕ} (r : Fin j → Fin 2) (y : ℝ × ℝ) :
    ∏ m, coord (r m) y =
      y.1 ^ (univ.filter fun m => r m = 0).card * y.2 ^ (univ.filter fun m => r m = 1).card := by
  rw [← Finset.prod_fiberwise univ r (fun m => coord (r m) y), Fin.prod_univ_two]
  congr 1
  · rw [Finset.prod_congr rfl (g := fun _ => y.1) fun m hm => by
      simp only [Finset.mem_filter] at hm; simp [coord, hm.2], Finset.prod_const]
  · rw [Finset.prod_congr rfl (g := fun _ => y.2) fun m hm => by
      simp only [Finset.mem_filter] at hm; simp [coord, hm.2], Finset.prod_const]

theorem card_filter_zero_add_one {j : ℕ} (r : Fin j → Fin 2) :
    (univ.filter fun m => r m = 0).card + (univ.filter fun m => r m = 1).card = j := by
  rw [← Finset.card_union_of_disjoint]
  · convert Finset.card_fin j
    ext m; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    generalize r m = i
    fin_cases i <;> simp
  · rw [Finset.disjoint_filter]; intro m _ h; rw [h]; decide

/-- `L(y, …, y) = ∑_r (∏ₘ y_{r m}) L(e_{r 1}, …, e_{r j})`. -/
theorem multilinear_diag_eq {j : ℕ} (L : ContinuousMultilinearMap ℝ (fun _ : Fin j => ℝ × ℝ) ℝ)
    (y : ℝ × ℝ) :
    L (fun _ => y) = ∑ r : Fin j → Fin 2,
      (y.1 ^ (univ.filter fun m => r m = 0).card * y.2 ^ (univ.filter fun m => r m = 1).card) *
        L (fun m => coordVec (r m)) := by
  conv_lhs => rw [show (fun _ : Fin j => y) = fun _ => ∑ i : Fin 2, coord i y • coordVec i from
    funext fun _ => (sum_coord_smul y).symm]
  rw [L.map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [L.map_smul_univ (fun m => coord (r m) y) (fun m => coordVec (r m)), prod_coord, smul_eq_mul]

/-! ### Exactness on monomials of degree `< k` gives `R = O(hᵏ)` -/

theorem abs_cubSum_le {r : List (ℝ × ℝ × ℝ)} {h B : ℝ} {g : ℝ × ℝ → ℝ}
    (hg : ∀ q ∈ r, |g (q.2.1 * h, q.2.2 * h)| ≤ B) :
    |cubSum r h g| ≤ (r.map fun q => |q.1|).sum * B := by
  induction r with
  | nil => simp [cubSum]
  | cons q r ih =>
    simp only [cubSum, List.map_cons, List.sum_cons] at ih ⊢
    have h1 := hg q (List.mem_cons_self ..)
    have h2 := ih fun q' hq' => hg q' (List.mem_cons_of_mem _ hq')
    calc |q.1 * g (q.2.1 * h, q.2.2 * h) + (r.map fun q => q.1 * g (q.2.1 * h, q.2.2 * h)).sum|
        ≤ |q.1| * |g (q.2.1 * h, q.2.2 * h)| +
          (r.map fun q => |q.1|).sum * B := by
          rw [← abs_mul]; exact (abs_add_le _ _).trans (by linarith)
      _ ≤ |q.1| * B + (r.map fun q => |q.1|).sum * B := by gcongr
      _ = _ := by ring

theorem norm_node_le {q : ℝ × ℝ × ℝ} (hq : |q.2.1| ≤ 1 ∧ |q.2.2| ≤ 1) {h : ℝ} (hh : 0 ≤ h) :
    ‖((q.2.1 * h, q.2.2 * h) : ℝ × ℝ)‖ ≤ h := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hh]
  exact max_le (by nlinarith [abs_nonneg q.2.1]) (by nlinarith [abs_nonneg q.2.2])

/-- If a rule is exact for all monomials `xᵃ yᵇ`, `a + b < k`, on regions `S_h ⊆ {‖p‖ ≤ h}` with
`c_h · area(S_h) ≤ 1`, and its nodes are `(ξh, ηh)` with `|ξ|, |η| ≤ 1`, then `R = O(hᵏ)` for
`f ∈ Cᵏ` (Taylor's formula with integral remainder at the origin). -/
theorem cubRem_le_of_exact {S : ℝ → Set (ℝ × ℝ)} {c : ℝ → ℝ} {r : List (ℝ × ℝ × ℝ)} {n : ℕ}
    (hsub : ∀ h, 0 < h → S h ⊆ Metric.closedBall 0 h)
    (hc : ∀ h, 0 < h → 0 ≤ c h ∧ c h * volume.real (S h) ≤ 1)
    (hr : ∀ q ∈ r, |q.2.1| ≤ 1 ∧ |q.2.2| ≤ 1)
    (hex : ∀ h, 0 < h → ∀ a b : ℕ, a + b ≤ n →
      cubRem (S h) (c h) r h (fun p => p.1 ^ a * p.2 ^ b) = 0)
    {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ (n + 1) f) :
    ∃ C, ∀ h, 0 < h → h ≤ 1 → |cubRem (S h) (c h) r h f| ≤ C * h ^ (n + 1) := by
  -- the Taylor polynomial and the remainder bound
  set P : ℝ × ℝ → ℝ := fun y => ∑ j ∈ Finset.range (n + 1),
    (j.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ j f 0 (fun _ => y)
  obtain ⟨M0, hM0⟩ := (isCompact_closedBall (0 : ℝ × ℝ) 1).exists_bound_of_continuousOn
    (hf.continuous_iteratedFDeriv (m := n + 1) le_rfl).continuousOn
  set M := max M0 0
  have hE : ∀ y : ℝ × ℝ, ‖y‖ ≤ 1 → |f y - P y| ≤ M * ‖y‖ ^ (n + 1) := fun y hy => by
    have ht := map_add_eq_sum_add_integral_iteratedFDeriv (x := (0 : ℝ × ℝ)) (y := y) (n := n)
      (fun t _ => hf.contDiffAt)
    simp only [zero_add, smul_eq_mul] at ht
    rw [ht]
    simp only [P, add_sub_cancel_left]
    have hb : ‖∫ t in (0 : ℝ)..1, (1 - t) ^ n *
        iteratedFDeriv ℝ (n + 1) f (t • y) (fun _ => y)‖ ≤ M * ‖y‖ ^ (n + 1) * |1 - 0| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht' => ?_
      rw [uIoc_of_le zero_le_one] at ht'
      have hty : t • y ∈ Metric.closedBall (0 : ℝ × ℝ) 1 := by
        rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos ht'.1]
        nlinarith [norm_nonneg y, ht'.2]
      have h1 : |(1 - t) ^ n| ≤ 1 := by
        rw [abs_of_nonneg (pow_nonneg (by linarith [ht'.2]) _)]
        exact pow_le_one₀ (by linarith [ht'.2]) (by linarith [ht'.1])
      have h2 := (iteratedFDeriv ℝ (n + 1) f (t • y)).le_opNorm (fun _ => y)
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h2
      have h3 : ‖iteratedFDeriv ℝ (n + 1) f (t • y)‖ ≤ M := (hM0 _ hty).trans (le_max_left _ _)
      rw [Real.norm_eq_abs, abs_mul]
      calc |(1 - t) ^ n| * |iteratedFDeriv ℝ (n + 1) f (t • y) (fun _ => y)|
          ≤ 1 * (M * ‖y‖ ^ (n + 1)) := by
            gcongr
            exact h2.trans (by gcongr)
        _ = M * ‖y‖ ^ (n + 1) := one_mul _
    rw [sub_zero, abs_one, mul_one] at hb
    rw [abs_mul, abs_of_pos (by positivity)]
    calc (n.factorial : ℝ)⁻¹ * |∫ t in (0 : ℝ)..1, (1 - t) ^ n *
          iteratedFDeriv ℝ (n + 1) f (t • y) (fun _ => y)|
        ≤ 1 * |∫ t in (0 : ℝ)..1, (1 - t) ^ n *
          iteratedFDeriv ℝ (n + 1) f (t • y) (fun _ => y)| :=
          mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀
            (by exact_mod_cast Nat.factorial_pos n)) (abs_nonneg _)
      _ ≤ _ := by rw [one_mul, ← Real.norm_eq_abs]; exact hb
  set W := (r.map fun q => |q.1|).sum
  have hW : 0 ≤ W := by
    simp only [W]
    exact List.sum_nonneg fun x hx => by
      obtain ⟨q, _, rfl⟩ := List.mem_map.mp hx; exact abs_nonneg _
  have hM : 0 ≤ M := le_max_right _ _
  refine ⟨M + W * M, fun h hh h1 => ?_⟩
  have hint : ∀ g : ℝ × ℝ → ℝ, Continuous g → IntegrableOn g (S h) := fun g hg =>
    (hg.continuousOn.integrableOn_compact (isCompact_closedBall 0 h)).mono_set (hsub h hh)
  have hcL : ∀ j, Continuous fun y : ℝ × ℝ => iteratedFDeriv ℝ j f 0 (fun _ => y) := fun j =>
    (iteratedFDeriv ℝ j f 0).cont.comp (continuous_pi fun _ => continuous_id)
  -- exactness on the Taylor polynomial
  have hL : ∀ j ≤ n, cubRem (S h) (c h) r h
      (fun y => iteratedFDeriv ℝ j f 0 (fun _ => y)) = 0 := fun j hj => by
    rw [show (fun y : ℝ × ℝ => iteratedFDeriv ℝ j f 0 (fun _ => y)) = fun y => ∑ ρ : Fin j → Fin 2,
        iteratedFDeriv ℝ j f 0 (fun m => coordVec (ρ m)) *
          (y.1 ^ (univ.filter fun m => ρ m = 0).card * y.2 ^ (univ.filter fun m => ρ m = 1).card)
        from funext fun y => by
          rw [multilinear_diag_eq]; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _]
    rw [cubRem_sum _ fun ρ _ => hint _ (by fun_prop)]
    refine Finset.sum_eq_zero fun ρ _ => ?_
    rw [cubRem_smul, hex h hh _ _ (by rw [card_filter_zero_add_one]; exact hj), mul_zero]
  have hP : cubRem (S h) (c h) r h P = 0 := by
    simp only [P]
    rw [cubRem_sum (f := fun j (y : ℝ × ℝ) => (j.factorial : ℝ)⁻¹ *
      iteratedFDeriv ℝ j f 0 (fun _ => y)) _ fun j _ => hint _ (continuous_const.mul (hcL j))]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [cubRem_smul, hL j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)), mul_zero]
  have hPc : Continuous P := continuous_finsetSum _ fun j _ => continuous_const.mul (hcL j)
  have hsplit : f = P + fun y => f y - P y := by ext y; simp
  rw [hsplit, cubRem_add (hint _ hPc) (hint (fun y => f y - P y) (hf.continuous.sub hPc)), hP,
    zero_add]
  -- the remainder bound
  have hEh : ∀ y : ℝ × ℝ, ‖y‖ ≤ h → |f y - P y| ≤ M * h ^ (n + 1) := fun y hy =>
    (hE y (hy.trans h1)).trans (by gcongr)
  have hfin : volume (S h) < ⊤ :=
    (measure_mono (hsub h hh)).trans_lt measure_closedBall_lt_top
  have hI := norm_setIntegral_le_of_norm_le_const hfin
    (f := fun y => f y - P y) (C := M * h ^ (n + 1)) fun y hy => by
      rw [Real.norm_eq_abs]; exact hEh y (mem_closedBall_zero_iff.mp (hsub h hh hy))
  have hQ := abs_cubSum_le (r := r) (h := h) (g := fun y => f y - P y) (B := M * h ^ (n + 1))
    fun q hq => hEh _ (norm_node_le (hr q hq) hh.le)
  obtain ⟨hc0, hc1⟩ := hc h hh
  unfold cubRem
  rw [Real.norm_eq_abs] at hI
  have hvol : 0 ≤ volume.real (S h) := measureReal_nonneg
  calc |c h * (∫ p in S h, f p - P p) - cubSum r h fun y => f y - P y|
      ≤ c h * |∫ p in S h, f p - P p| + |cubSum r h fun y => f y - P y| := by
        rw [← abs_of_nonneg hc0, ← abs_mul, abs_of_nonneg hc0]; exact abs_sub _ _
    _ ≤ c h * (M * h ^ (n + 1) * volume.real (S h)) + W * (M * h ^ (n + 1)) := by gcongr
    _ = (c h * volume.real (S h)) * (M * h ^ (n + 1)) + W * (M * h ^ (n + 1)) := by ring
    _ ≤ 1 * (M * h ^ (n + 1)) + W * (M * h ^ (n + 1)) := by gcongr
    _ = (M + W * M) * h ^ (n + 1) := by ring

/-! ### Trigonometric moments `Θ(a, b) = ∫_{−π}^{π} cosᵃθ sinᵇθ dθ` -/

/-- `Θ(a, b) = ∫_{−π}^{π} cosᵃθ sinᵇθ dθ`. -/
noncomputable def trigMom (a b : ℕ) : ℝ :=
  ∫ θ in (-Real.pi)..Real.pi, Real.cos θ ^ a * Real.sin θ ^ b

theorem trigMom_odd_right (a : ℕ) {b : ℕ} (hb : Odd b) : trigMom a b = 0 := by
  have h := intervalIntegral.integral_comp_neg (a := -Real.pi) (b := Real.pi)
    (fun θ => Real.cos θ ^ a * Real.sin θ ^ b)
  rw [neg_neg] at h
  simp only [Real.cos_neg, Real.sin_neg, hb.neg_pow, mul_neg, intervalIntegral.integral_neg] at h
  unfold trigMom
  linarith

theorem trigMom_swap (a b : ℕ) : trigMom a b = (-1) ^ a * trigMom b a := by
  have hp : Function.Periodic (fun θ => Real.cos θ ^ a * Real.sin θ ^ b) (2 * Real.pi) :=
    fun θ => by simp [Real.cos_add_two_pi, Real.sin_add_two_pi]
  have h1 := hp.intervalIntegral_add_eq (-Real.pi + Real.pi / 2) (-Real.pi)
  have h2 := intervalIntegral.integral_comp_add_right
    (fun θ => Real.cos θ ^ a * Real.sin θ ^ b) (a := -Real.pi) (b := Real.pi) (Real.pi / 2)
  rw [show -Real.pi + Real.pi / 2 + 2 * Real.pi = Real.pi + Real.pi / 2 by ring,
    show -Real.pi + 2 * Real.pi = Real.pi by ring] at h1
  rw [h1] at h2
  simp only [Real.cos_add_pi_div_two, Real.sin_add_pi_div_two] at h2
  unfold trigMom
  rw [← h2, ← intervalIntegral.integral_const_mul]
  congr 1; ext θ; rw [neg_pow]; ring

theorem trigMom_odd_left {a : ℕ} (ha : Odd a) (b : ℕ) : trigMom a b = 0 := by
  rw [trigMom_swap, trigMom_odd_right b ha, mul_zero]

theorem trigMom_zero_zero : trigMom 0 0 = 2 * Real.pi := by
  simp [trigMom]; ring

theorem trigMom_zero_two : trigMom 0 2 = Real.pi := by
  simp [trigMom, integral_sin_sq]

theorem trigMom_zero_four : trigMom 0 4 = 3 * Real.pi / 4 := by
  have := integral_sin_pow (a := -Real.pi) (b := Real.pi) (n := 2)
  simp only [trigMom, pow_zero, one_mul]
  rw [this, integral_sin_sq]
  simp; ring

theorem trigMom_two_zero : trigMom 2 0 = Real.pi := by
  rw [trigMom_swap, trigMom_zero_two]; norm_num

theorem trigMom_four_zero : trigMom 4 0 = 3 * Real.pi / 4 := by
  rw [trigMom_swap, trigMom_zero_four]; norm_num

theorem trigMom_two_two : trigMom 2 2 = Real.pi / 4 := by
  have e : ∀ θ : ℝ, Real.cos θ ^ 2 * Real.sin θ ^ 2 = Real.sin θ ^ 2 - Real.sin θ ^ 4 := fun θ => by
    have := Real.cos_sq_add_sin_sq θ; nlinarith
  have hi : ∀ m : ℕ, IntervalIntegrable (fun θ => Real.sin θ ^ m) volume (-Real.pi) Real.pi :=
    fun m => (Real.continuous_sin.pow m).intervalIntegrable _ _
  have h2 := trigMom_zero_two
  have h4 := trigMom_zero_four
  simp only [trigMom, pow_zero, one_mul] at h2 h4 ⊢
  simp only [e]
  rw [intervalIntegral.integral_sub (hi 2) (hi 4), h2, h4]; ring

/-! ### The disk `x² + y² ≤ h²` and the square `|x|, |y| ≤ h` -/

/-- The disk `D`: `x² + y² ≤ h²`. -/
def diskSet (h : ℝ) : Set (ℝ × ℝ) := {p | p.1 ^ 2 + p.2 ^ 2 ≤ h ^ 2}

/-- The square `S`: `|x| ≤ h`, `|y| ≤ h`. -/
def squareSet (h : ℝ) : Set (ℝ × ℝ) := Icc (-h) h ×ˢ Icc (-h) h

theorem measurableSet_diskSet (h : ℝ) : MeasurableSet (diskSet h) :=
  measurableSet_le (by fun_prop) (by fun_prop)

theorem diskSet_subset {h : ℝ} (hh : 0 < h) : diskSet h ⊆ Metric.closedBall 0 h := fun p hp => by
  simp only [diskSet] at hp; change p.1 ^ 2 + p.2 ^ 2 ≤ h ^ 2 at hp
  rw [mem_closedBall_zero_iff, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  exact max_le (abs_le.mpr ⟨by nlinarith [sq_nonneg p.2], by nlinarith [sq_nonneg p.2]⟩)
    (abs_le.mpr ⟨by nlinarith [sq_nonneg p.1], by nlinarith [sq_nonneg p.1]⟩)

theorem squareSet_subset (h : ℝ) : squareSet h ⊆ Metric.closedBall 0 h := fun p hp => by
  simp only [squareSet, Set.mem_prod, Set.mem_Icc] at hp
  rw [mem_closedBall_zero_iff, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  exact max_le (abs_le.mpr hp.1) (abs_le.mpr hp.2)

/-- `∬_D xᵃ yᵇ = h^{a+b+2}/(a + b + 2) · Θ(a, b)` (polar coordinates). -/
theorem integral_diskSet_mono {h : ℝ} (hh : 0 < h) (a b : ℕ) :
    ∫ p in diskSet h, p.1 ^ a * p.2 ^ b =
      h ^ (a + b + 2) / (a + b + 2) * trigMom a b := by
  rw [← integral_indicator (measurableSet_diskSet h), ← integral_comp_polarCoord_symm]
  have e : ∀ q ∈ polarCoord.target, q.1 • (diskSet h).indicator (fun p => p.1 ^ a * p.2 ^ b)
      (polarCoord.symm q) = (Ioc 0 h ×ˢ Set.univ).indicator
        (fun q : ℝ × ℝ => q.1 ^ (a + b + 1) * (Real.cos q.2 ^ a * Real.sin q.2 ^ b)) q := by
    rintro ⟨ρ, θ⟩ ⟨hρ, -⟩
    simp only [Set.mem_Ioi] at hρ
    have hsymm : polarCoord.symm (ρ, θ) = (ρ * Real.cos θ, ρ * Real.sin θ) := rfl
    rw [hsymm]
    have hmem : (ρ * Real.cos θ, ρ * Real.sin θ) ∈ diskSet h ↔ (ρ, θ) ∈ Ioc 0 h ×ˢ Set.univ := by
      simp only [diskSet, Set.mem_prod, Set.mem_Ioc, Set.mem_univ, and_true]
      change (ρ * Real.cos θ) ^ 2 + (ρ * Real.sin θ) ^ 2 ≤ h ^ 2 ↔ _
      rw [show (ρ * Real.cos θ) ^ 2 + (ρ * Real.sin θ) ^ 2 = ρ ^ 2 by
        have := Real.cos_sq_add_sin_sq θ; nlinarith]
      rw [pow_le_pow_iff_left₀ hρ.le hh.le two_ne_zero]
      exact ⟨fun h1 => ⟨hρ, h1⟩, fun h1 => h1.2⟩
    by_cases hm : (ρ * Real.cos θ, ρ * Real.sin θ) ∈ diskSet h
    · rw [indicator_of_mem hm, indicator_of_mem (hmem.mp hm), smul_eq_mul]; ring
    · rw [indicator_of_notMem hm, indicator_of_notMem (fun h' => hm (hmem.mpr h')), smul_zero]
  rw [setIntegral_congr_fun polarCoord.open_target.measurableSet e,
    setIntegral_indicator (measurableSet_Ioc.prod MeasurableSet.univ)]
  have hset : polarCoord.target ∩ (Ioc 0 h ×ˢ Set.univ) = Ioc 0 h ×ˢ Ioo (-Real.pi) Real.pi := by
    ext ⟨ρ, θ⟩
    simp only [polarCoord_target, Set.mem_inter_iff, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo,
      Set.mem_Ioc, Set.mem_univ,
      and_true]
    tauto
  rw [hset, Measure.volume_eq_prod, setIntegral_prod_mul (fun ρ : ℝ => ρ ^ (a + b + 1))
    (fun θ : ℝ => Real.cos θ ^ a * Real.sin θ ^ b), ← intervalIntegral.integral_of_le hh.le,
    integral_pow, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  unfold trigMom
  push_cast
  rw [zero_pow (by omega), sub_zero]
  congr 1
  ring_nf

theorem integral_squareSet_mono (h : ℝ) (hh : 0 < h) (a b : ℕ) :
    ∫ p in squareSet h, p.1 ^ a * p.2 ^ b =
      (h ^ (a + 1) - (-h) ^ (a + 1)) / (a + 1) * ((h ^ (b + 1) - (-h) ^ (b + 1)) / (b + 1)) := by
  rw [squareSet, Measure.volume_eq_prod,
    setIntegral_prod_mul (fun x : ℝ => x ^ a) (fun y : ℝ => y ^ b), integral_Icc_eq_integral_Ioc,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
    ← intervalIntegral.integral_of_le (by linarith), integral_pow, integral_pow]

theorem volume_diskSet {h : ℝ} (hh : 0 < h) : volume.real (diskSet h) = Real.pi * h ^ 2 := by
  have := integral_diskSet_mono hh 0 0
  simp only [pow_zero, mul_one, setIntegral_const, smul_eq_mul, trigMom_zero_zero] at this
  rw [this]; push_cast; ring

theorem volume_squareSet {h : ℝ} (hh : 0 < h) : volume.real (squareSet h) = 4 * h ^ 2 := by
  have := integral_squareSet_mono h hh 0 0
  simp only [pow_zero, mul_one, setIntegral_const, smul_eq_mul] at this
  rw [this]; push_cast; ring

/-! ### 3.5.47 and 3.5.48 -/

/-- The remainder `R` of **DLMF 3.5.47**:
`(πh²)^{−1} ∬_D f(x, y) dx dy = ∑ⱼ wⱼ f(xⱼ, yⱼ) + R`, `D: x² + y² ≤ h²`. -/
noncomputable def diskRem (r : List (ℝ × ℝ × ℝ)) (h : ℝ) (f : ℝ × ℝ → ℝ) : ℝ :=
  cubRem (diskSet h) (1 / (Real.pi * h ^ 2)) r h f

/-- The remainder `R` of **DLMF 3.5.48**:
`(4h²)^{−1} ∬_S f(x, y) dx dy = ∑ⱼ wⱼ f(xⱼ, yⱼ) + R`, `S: |x| ≤ h, |y| ≤ h`. -/
noncomputable def squareRem (r : List (ℝ × ℝ × ℝ)) (h : ℝ) (f : ℝ × ℝ → ℝ) : ℝ :=
  cubRem (squareSet h) (1 / (4 * h ^ 2)) r h f

theorem dlmf_3_5_47 (r : List (ℝ × ℝ × ℝ)) (h : ℝ) (f : ℝ × ℝ → ℝ) :
    1 / (Real.pi * h ^ 2) * ∫ p in diskSet h, f p = cubSum r h f + diskRem r h f := by
  unfold diskRem cubRem; ring

theorem dlmf_3_5_48 (r : List (ℝ × ℝ × ℝ)) (h : ℝ) (f : ℝ × ℝ → ℝ) :
    1 / (4 * h ^ 2) * ∫ p in squareSet h, f p = cubSum r h f + squareRem r h f := by
  unfold squareRem cubRem; ring

theorem cubSum_mono (r : List (ℝ × ℝ × ℝ)) (h : ℝ) (a b : ℕ) :
    cubSum r h (fun p => p.1 ^ a * p.2 ^ b) =
      h ^ (a + b) * cubSum r 1 (fun p => p.1 ^ a * p.2 ^ b) := by
  induction r with
  | nil => simp [cubSum]
  | cons q r ih =>
    simp only [cubSum, List.map_cons, List.sum_cons, mul_one] at ih ⊢
    rw [ih]; ring

/-- `Θ(a, b)/π` for `a + b ≤ 5`. -/
def thetaQ : ℕ → ℕ → ℚ
  | 0, 0 => 2
  | 2, 0 => 1
  | 0, 2 => 1
  | 4, 0 => 3 / 4
  | 0, 4 => 3 / 4
  | 2, 2 => 1 / 4
  | _, _ => 0

theorem trigMom_eq_thetaQ {a b : ℕ} (hab : a + b ≤ 5) : trigMom a b = thetaQ a b * Real.pi := by
  have ha : a ≤ 5 := by omega
  have hb : b ≤ 5 := by omega
  interval_cases a <;> interval_cases b <;>
    first
    | (exfalso; omega)
    | (rw [trigMom_odd_right _ (by decide)]; simp [thetaQ])
    | (rw [trigMom_odd_left (by decide)]; simp [thetaQ])
    | (simp only [thetaQ, trigMom_zero_zero, trigMom_zero_two, trigMom_zero_four,
        trigMom_two_zero, trigMom_four_zero, trigMom_two_two]; push_cast; ring)

/-- A disk rule exact on all monomials of degree `≤ n` has `R = O(h^{n+1})` for `f ∈ C^{n+1}`. -/
theorem diskRem_isBigO {r : List (ℝ × ℝ × ℝ)} {n : ℕ} (hn : n ≤ 5)
    (hr : ∀ q ∈ r, |q.2.1| ≤ 1 ∧ |q.2.2| ≤ 1)
    (hex : ∀ a b : ℕ, a + b ≤ n →
      cubSum r 1 (fun p => p.1 ^ a * p.2 ^ b) = (thetaQ a b : ℝ) / (a + b + 2))
    {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ (n + 1) f) :
    (fun h => diskRem r h f) =O[𝓝[>] 0] fun h => h ^ (n + 1) := by
  obtain ⟨C, hC⟩ := cubRem_le_of_exact (S := diskSet) (c := fun h => 1 / (Real.pi * h ^ 2))
    (fun h hh => diskSet_subset hh)
    (fun h hh => ⟨by positivity, by rw [volume_diskSet hh]; field_simp; rfl⟩) hr
    (fun h hh a b hab => by
      unfold cubRem
      rw [integral_diskSet_mono hh, cubSum_mono, hex a b hab, trigMom_eq_thetaQ (by omega)]
      have := Real.pi_pos
      field_simp
      ring) hf
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [Ioc_mem_nhdsGT one_pos] with h hh
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (pow_pos hh.1 _)]
  exact hC h hh.1 hh.2

/-- A square rule exact on all monomials of degree `≤ n` has `R = O(h^{n+1})` for
`f ∈ C^{n+1}`. -/
theorem squareRem_isBigO {r : List (ℝ × ℝ × ℝ)} {n : ℕ}
    (hr : ∀ q ∈ r, |q.2.1| ≤ 1 ∧ |q.2.2| ≤ 1)
    (hex : ∀ a b : ℕ, a + b ≤ n →
      cubSum r 1 (fun p => p.1 ^ a * p.2 ^ b) =
        (1 - (-1) ^ (a + 1)) / (2 * (a + 1)) * ((1 - (-1) ^ (b + 1)) / (2 * (b + 1))))
    {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ (n + 1) f) :
    (fun h => squareRem r h f) =O[𝓝[>] 0] fun h => h ^ (n + 1) := by
  obtain ⟨C, hC⟩ := cubRem_le_of_exact (S := squareSet) (c := fun h => 1 / (4 * h ^ 2))
    (fun h _ => squareSet_subset h)
    (fun h hh => ⟨by positivity, by rw [volume_squareSet hh]; field_simp; rfl⟩) hr
    (fun h hh a b hab => by
      unfold cubRem
      rw [integral_squareSet_mono h hh, cubSum_mono, hex a b hab, neg_pow h, neg_pow h]
      field_simp
      ring) hf
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [Ioc_mem_nhdsGT one_pos] with h hh
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (pow_pos hh.1 _)]
  exact hC h hh.1 hh.2

end Azurite.DLMF
