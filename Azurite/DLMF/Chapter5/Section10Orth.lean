/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section9Markov
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.PSeries
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Orthogonal polynomials of a symmetric weight on `ℝ`

Groundwork for DLMF §5.10. A `SymWeight` is an even weight `w ≥ 0` on `ℝ`, positive off `0`,
with all moments finite. Its moment functional `L(p) = ∫ p(x) w(x) dx` and the monic orthogonal
polynomials, defined by the three-term recurrence
`P₀ = 1`, `P₁ = x`, `P_{n+1} = x Pₙ − λₙ P_{n−1}`, `λₙ = hₙ/h_{n−1}`, `hₙ = L(Pₙ xⁿ)`:

* `P` is monic of degree `n` with the parity of `n` (`natDegree_P`, `monic_P`, `P_comp_neg`);
* `L(Pₙ q) = 0` for `deg q < n` (`L_P_mul_eq_zero`), `hₙ = L(Pₙ²) > 0` (`h_pos`), and
  `hₙ ≤ L(x^{2n})` (`h_le_mom`).
-/

open Polynomial MeasureTheory Filter Topology Finset

namespace Azurite.DLMF

/-- An even weight on `ℝ`, positive off `0`, with all moments finite. -/
structure SymWeight where
  /-- The weight. -/
  w : ℝ → ℝ
  nonneg : ∀ x, 0 ≤ w x
  pos : ∀ x, x ≠ 0 → 0 < w x
  even : ∀ x, w (-x) = w x
  integrable : ∀ k : ℕ, Integrable fun x => x ^ k * w x

namespace SymWeight

variable (W : SymWeight)

/-- The moments `mₖ = ∫ xᵏ w(x) dx`. -/
noncomputable def mom (k : ℕ) : ℝ := ∫ x, x ^ k * W.w x

/-- The moment functional `L(p) = ∫ p(x) w(x) dx`. -/
noncomputable def L (p : ℝ[X]) : ℝ := ∫ x, p.eval x * W.w x

theorem integrable_eval (p : ℝ[X]) : Integrable fun x => p.eval x * W.w x := by
  have e : (fun x => p.eval x * W.w x) =
      fun x => ∑ i ∈ range (p.natDegree + 1), p.coeff i * (x ^ i * W.w x) := by
    funext x
    rw [eval_eq_sum_range, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  exact integrable_finsetSum _ fun i _ => (W.integrable i).const_mul _

theorem L_add (p q : ℝ[X]) : W.L (p + q) = W.L p + W.L q := by
  simp only [L, eval_add, add_mul]
  exact integral_add (W.integrable_eval p) (W.integrable_eval q)

theorem L_sub (p q : ℝ[X]) : W.L (p - q) = W.L p - W.L q := by
  simp only [L, eval_sub, sub_mul]
  exact integral_sub (W.integrable_eval p) (W.integrable_eval q)

theorem L_C_mul (c : ℝ) (p : ℝ[X]) : W.L (C c * p) = c * W.L p := by
  simp only [L, eval_mul, eval_C, mul_assoc]
  exact integral_const_mul c _

theorem L_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ[X]) :
    W.L (∑ i ∈ s, f i) = ∑ i ∈ s, W.L (f i) := by
  simp only [L, eval_finsetSum, Finset.sum_mul]
  exact integral_finsetSum _ fun i _ => W.integrable_eval (f i)

theorem L_X_pow (k : ℕ) : W.L (X ^ k) = W.mom k := by simp [L, mom]

/-- `L` vanishes on odd polynomials. -/
theorem L_odd {q : ℝ[X]} (hq : q.comp (-X) = -q) : W.L q = 0 := by
  have h := integral_neg_eq_self (fun x => q.eval x * W.w x) volume
  have e : ∀ x, q.eval (-x) * W.w (-x) = -(q.eval x * W.w x) := fun x => by
    have := congrArg (eval x) hq
    simp only [eval_comp, eval_neg, eval_X] at this
    rw [this, W.even]
    ring
  simp_rw [e, integral_neg] at h
  unfold L
  linarith

theorem L_mul_self_nonneg (p : ℝ[X]) : 0 ≤ W.L (p * p) :=
  integral_nonneg fun x => by
    simp only [eval_mul]
    exact mul_nonneg (mul_self_nonneg _) (W.nonneg x)

theorem L_mul_self_pos {p : ℝ[X]} (hp : p ≠ 0) : 0 < W.L (p * p) := by
  unfold L
  have hnn : 0 ≤ᵐ[volume] fun x => (p * p).eval x * W.w x := ae_of_all _ fun x => by
    simp only [eval_mul, Pi.zero_apply]
    exact mul_nonneg (mul_self_nonneg _) (W.nonneg x)
  rw [integral_pos_iff_support_of_nonneg_ae hnn (W.integrable_eval _)]
  set F : Set ℝ := insert 0 (p.roots.toFinset : Set ℝ) with hF
  have hFfin : F.Finite := (Finset.finite_toSet _).insert 0
  have hsub : (Function.support fun x => (p * p).eval x * W.w x)ᶜ ⊆ F := fun x hx => by
    simp only [Set.mem_compl_iff, Function.mem_support, not_not] at hx
    by_contra hxF
    simp only [hF, Set.mem_insert_iff, Finset.mem_coe, Multiset.mem_toFinset, not_or] at hxF
    have h1 : p.eval x ≠ 0 := fun h => hxF.2 ((mem_roots hp).mpr h)
    simp only [eval_mul] at hx
    have := mul_ne_zero (mul_ne_zero h1 h1) (W.pos x hxF.1).ne'
    exact this hx
  by_contra hcon
  have h0 : volume (Function.support fun x => (p * p).eval x * W.w x) = 0 :=
    le_antisymm (not_lt.mp hcon) bot_le
  have h1 : volume (Function.support fun x => (p * p).eval x * W.w x)ᶜ = 0 :=
    measure_mono_null hsub (hFfin.measure_zero _)
  have := measure_union_null h0 h1
  rw [Set.union_compl_self, Real.volume_univ] at this
  exact ENNReal.top_ne_zero this

/-! ### The monic orthogonal polynomials -/

/-- The pairs `(Pₙ, P_{n+1})`. -/
noncomputable def PP : ℕ → ℝ[X] × ℝ[X]
  | 0 => (1, X)
  | n + 1 => ((PP n).2, X * (PP n).2 -
      C (W.L ((PP n).2 * X ^ (n + 1)) / W.L ((PP n).1 * X ^ n)) * (PP n).1)

/-- The monic orthogonal polynomials `Pₙ`. -/
noncomputable def P (n : ℕ) : ℝ[X] := (W.PP n).1

/-- `hₙ = L(Pₙ xⁿ)` (`= L(Pₙ²)`, `h_eq`). -/
noncomputable def h (n : ℕ) : ℝ := W.L (W.P n * X ^ n)

/-- The recurrence coefficients `λₙ = hₙ/h_{n−1}`. -/
noncomputable def lam (n : ℕ) : ℝ := W.h n / W.h (n - 1)

theorem P_zero : W.P 0 = 1 := rfl

theorem P_one : W.P 1 = X := rfl

theorem P_succ_succ (n : ℕ) : W.P (n + 2) = X * W.P (n + 1) - C (W.lam (n + 1)) * W.P n := rfl

theorem natDegree_P_monic : ∀ n, (W.P n).natDegree = n ∧ (W.P n).Monic
  | 0 => by simp [P_zero]
  | 1 => by simp [P_one]
  | n + 2 => by
    obtain ⟨h1, m1⟩ := natDegree_P_monic (n + 1)
    obtain ⟨h0, -⟩ := natDegree_P_monic n
    have hm : (X * W.P (n + 1)).Monic := monic_X.mul m1
    have hd : (X * W.P (n + 1)).natDegree = n + 2 := by
      rw [natDegree_mul X_ne_zero m1.ne_zero, natDegree_X, h1]; ring
    have hlt : (C (W.lam (n + 1)) * W.P n).degree < (X * W.P (n + 1)).degree := by
      refine degree_lt_degree ?_
      rw [hd]
      calc (C (W.lam (n + 1)) * W.P n).natDegree ≤ (W.P n).natDegree := natDegree_C_mul_le _ _
        _ < n + 2 := by omega
    rw [P_succ_succ]
    refine ⟨?_, hm.sub_of_left hlt⟩
    rw [natDegree_sub_eq_left_of_natDegree_lt, hd]
    rw [hd]
    calc (C (W.lam (n + 1)) * W.P n).natDegree ≤ (W.P n).natDegree := natDegree_C_mul_le _ _
      _ < n + 2 := by omega

theorem natDegree_P (n : ℕ) : (W.P n).natDegree = n := (W.natDegree_P_monic n).1

theorem monic_P (n : ℕ) : (W.P n).Monic := (W.natDegree_P_monic n).2

theorem P_ne_zero (n : ℕ) : W.P n ≠ 0 := (W.monic_P n).ne_zero

/-- `Pₙ(−x) = (−1)ⁿ Pₙ(x)`. -/
theorem P_comp_neg : ∀ n, (W.P n).comp (-X) = C ((-1) ^ n) * W.P n
  | 0 => by simp [P_zero]
  | 1 => by simp [P_one]
  | n + 2 => by
    rw [P_succ_succ, sub_comp, mul_comp, mul_comp, X_comp, C_comp, P_comp_neg (n + 1),
      P_comp_neg n]
    simp only [pow_succ, C_mul, C_neg, C_1]
    ring

theorem L_P_mul_X_pow_of_odd {n k : ℕ} (hnk : Odd (n + k)) : W.L (W.P n * X ^ k) = 0 := by
  refine W.L_odd ?_
  rw [mul_comp, P_comp_neg, X_pow_comp]
  obtain ⟨j, hj⟩ := hnk
  have : (-X : ℝ[X]) ^ k = C ((-1) ^ k) * X ^ k := by
    rw [neg_pow, C_pow, C_neg, C_1]
  rw [this, show C ((-1 : ℝ) ^ n) * W.P n * (C ((-1) ^ k) * X ^ k) =
    C ((-1) ^ (n + k)) * (W.P n * X ^ k) by rw [pow_add, C_mul]; ring, hj, pow_succ, pow_mul]
  simp

theorem L_P_mul_eq_zero_of_X_pow {n : ℕ} (horth : ∀ k < n, W.L (W.P n * X ^ k) = 0)
    {q : ℝ[X]} (hq : q.natDegree < n) : W.L (W.P n * q) = 0 := by
  rw [q.as_sum_range' n hq]
  simp_rw [← C_mul_X_pow_eq_monomial]
  rw [Finset.mul_sum, W.L_sum]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [show W.P n * (C (q.coeff i) * X ^ i) = C (q.coeff i) * (W.P n * X ^ i) by ring, W.L_C_mul,
    horth i (Finset.mem_range.mp hi), mul_zero]

theorem natDegree_P_sub_X_pow_lt {n : ℕ} (hne : W.P n - X ^ n ≠ 0) :
    (W.P n - X ^ n).natDegree < n := by
  have hd : (W.P n).degree = (X ^ n : ℝ[X]).degree := by
    rw [degree_eq_natDegree (W.P_ne_zero n), W.natDegree_P, degree_X_pow]
  have hlt := degree_sub_lt_left hd (W.P_ne_zero n) (by rw [(W.monic_P n).leadingCoeff,
    leadingCoeff_X_pow])
  rw [degree_eq_natDegree (W.P_ne_zero n), W.natDegree_P] at hlt
  exact (natDegree_lt_iff_degree_lt hne).mpr hlt

theorem h_eq_of_orth {n : ℕ} (horth : ∀ k < n, W.L (W.P n * X ^ k) = 0) :
    W.h n = W.L (W.P n * W.P n) := by
  rw [show W.P n * W.P n = W.P n * X ^ n + W.P n * (W.P n - X ^ n) by ring, W.L_add, h]
  rcases eq_or_ne (W.P n - X ^ n) 0 with h0 | h0
  · rw [h0, mul_zero, show W.L 0 = 0 by simp [L], add_zero]
  · rw [W.L_P_mul_eq_zero_of_X_pow horth (W.natDegree_P_sub_X_pow_lt h0), add_zero]

/-- Orthogonality: `L(Pₙ xᵏ) = 0` for `k < n`. -/
theorem orth : ∀ n, (∀ k < n, W.L (W.P n * X ^ k) = 0) ∧
    (∀ k < n + 1, W.L (W.P (n + 1) * X ^ k) = 0)
  | 0 => by
    refine ⟨fun k hk => absurd hk (Nat.not_lt_zero _), fun k hk => ?_⟩
    obtain rfl : k = 0 := by omega
    exact W.L_P_mul_X_pow_of_odd (by decide)
  | n + 1 => by
    obtain ⟨h0, h1⟩ := orth n
    refine ⟨h1, fun k hk => ?_⟩
    rcases Nat.even_or_odd (n + 2 + k) with hev | hodd
    · -- `k = n` or `k < n`
      have hk' : k ≤ n := by
        by_contra hc
        obtain rfl : k = n + 1 := by omega
        exact (Nat.not_even_iff_odd.mpr (by
          exact ⟨n + 1, by ring⟩ : Odd (n + 2 + (n + 1)))) hev
      have hpos : 0 < W.h n := by
        rw [W.h_eq_of_orth h0]; exact W.L_mul_self_pos (W.P_ne_zero n)
      rw [P_succ_succ, sub_mul, W.L_sub,
        show X * W.P (n + 1) * X ^ k = W.P (n + 1) * X ^ (k + 1) by ring,
        show C (W.lam (n + 1)) * W.P n * X ^ k = C (W.lam (n + 1)) * (W.P n * X ^ k) by ring,
        W.L_C_mul]
      rcases hk'.lt_or_eq with hlt | heq
      · rw [h1 (k + 1) (by omega), h0 k hlt, mul_zero, sub_zero]
      · rw [heq]
        show W.h (n + 1) - W.lam (n + 1) * W.h n = 0
        rw [lam, show n + 1 - 1 = n from rfl, div_mul_cancel₀ _ hpos.ne', sub_self]
    · exact W.L_P_mul_X_pow_of_odd (by simpa [add_assoc] using hodd)

theorem L_P_mul_eq_zero {n : ℕ} {q : ℝ[X]} (hq : q.natDegree < n) : W.L (W.P n * q) = 0 :=
  W.L_P_mul_eq_zero_of_X_pow (W.orth n).1 hq

theorem h_eq (n : ℕ) : W.h n = W.L (W.P n * W.P n) := W.h_eq_of_orth (W.orth n).1

theorem h_pos (n : ℕ) : 0 < W.h n := by
  rw [W.h_eq]; exact W.L_mul_self_pos (W.P_ne_zero n)

theorem L_P_mul_P_of_ne {m n : ℕ} (hmn : m ≠ n) : W.L (W.P m * W.P n) = 0 := by
  rcases lt_or_gt_of_ne hmn with h | h
  · rw [mul_comm]; exact W.L_P_mul_eq_zero (by rw [W.natDegree_P]; exact h)
  · exact W.L_P_mul_eq_zero (by rw [W.natDegree_P]; exact h)

theorem lam_pos (n : ℕ) : 0 < W.lam n := div_pos (W.h_pos n) (W.h_pos _)

theorem h_succ (n : ℕ) : W.h (n + 1) = W.lam (n + 1) * W.h n := by
  rw [lam, show n + 1 - 1 = n from rfl]
  field_simp [(W.h_pos n).ne']

/-- `hₙ ≤ m_{2n}`. -/
theorem h_le_mom (n : ℕ) : W.h n ≤ W.mom (2 * n) := by
  have h0 := W.L_mul_self_nonneg (W.P n - X ^ n)
  rw [show (W.P n - X ^ n) * (W.P n - X ^ n) =
    W.P n * W.P n - (W.P n * X ^ n + W.P n * X ^ n) + X ^ (2 * n) by ring,
    W.L_add, W.L_sub, W.L_add, ← W.h_eq, W.L_X_pow] at h0
  unfold h at h0 ⊢
  linarith

/-! ### Evaluation off the real axis and Markov's formula -/

/-- `Pₙ(ζ)`. -/
noncomputable def pz (n : ℕ) (ζ : ℂ) : ℂ := aeval ζ (W.P n)

/-- The polynomials of the second kind: `Q₀ = 0`, `Q₁ = m₀`, `Q_{n+1} = x Qₙ − λₙ Q_{n−1}`. -/
noncomputable def Q : ℕ → ℝ[X]
  | 0 => 0
  | 1 => C (W.mom 0)
  | n + 2 => X * Q (n + 1) - C (W.lam (n + 1)) * Q n

/-- `Qₙ(ζ)`. -/
noncomputable def qz (n : ℕ) (ζ : ℂ) : ℂ := aeval ζ (W.Q n)

/-- The Cauchy transform `G(ζ) = ∫ w(x)/(ζ − x) dx`. -/
noncomputable def G (ζ : ℂ) : ℂ := ∫ x, (W.w x : ℂ) / (ζ - x)

/-- `Iₙ(ζ) = ∫ Pₙ(x) w(x)/(ζ − x) dx`. -/
noncomputable def I (n : ℕ) (ζ : ℂ) : ℂ := ∫ x, (((W.P n).eval x * W.w x : ℝ) : ℂ) / (ζ - x)

theorem pz_zero (ζ : ℂ) : W.pz 0 ζ = 1 := by simp [pz, P_zero]

theorem pz_one (ζ : ℂ) : W.pz 1 ζ = ζ := by simp [pz, P_one]

theorem pz_succ_succ (n : ℕ) (ζ : ℂ) :
    W.pz (n + 2) ζ = ζ * W.pz (n + 1) ζ - W.lam (n + 1) * W.pz n ζ := by
  simp [pz, P_succ_succ]

theorem qz_zero (ζ : ℂ) : W.qz 0 ζ = 0 := by simp [qz, Q]

theorem qz_one (ζ : ℂ) : W.qz 1 ζ = W.mom 0 := by simp [qz, Q]

theorem qz_succ_succ (n : ℕ) (ζ : ℂ) :
    W.qz (n + 2) ζ = ζ * W.qz (n + 1) ζ - W.lam (n + 1) * W.qz n ζ := by
  simp [qz, Q]

theorem pz_conj (n : ℕ) (ζ : ℂ) : W.pz n ((starRingEnd ℂ) ζ) = (starRingEnd ℂ) (W.pz n ζ) :=
  aeval_conj _ _

theorem pz_ofReal (n : ℕ) (x : ℝ) : W.pz n x = (((W.P n).eval x : ℝ) : ℂ) := by
  exact aeval_algebraMap_apply_eq_algebraMap_eval x (W.P n)

theorem abs_im_le_norm_sub (ζ : ℂ) (x : ℝ) : |ζ.im| ≤ ‖ζ - x‖ := by
  have := Complex.abs_im_le_norm (ζ - x)
  simpa using this

theorem sub_ofReal_ne_zero {ζ : ℂ} (hζ : ζ.im ≠ 0) (x : ℝ) : ζ - x ≠ 0 := fun h => by
  have := abs_im_le_norm_sub ζ x
  rw [h, norm_zero] at this
  exact hζ (abs_nonpos_iff.mp this)

theorem aestronglyMeasurable_w : AEStronglyMeasurable W.w volume := by
  have := (W.integrable 0).aestronglyMeasurable
  simpa using this

theorem integrable_ofReal_div_sub {f : ℝ → ℝ} (hf : Integrable f) {ζ : ℂ} (hζ : ζ.im ≠ 0) :
    Integrable fun x : ℝ => (f x : ℂ) / (ζ - x) := by
  refine (hf.norm.div_const |ζ.im|).mono' ?_ (ae_of_all _ fun x => ?_)
  · have hm : AEStronglyMeasurable (fun x : ℝ => (f x : ℂ)) volume :=
      (Complex.continuous_ofReal.measurable.comp_aemeasurable hf.aemeasurable).aestronglyMeasurable
    exact (hm.mul (by fun_prop : Measurable fun x : ℝ => (ζ - x)⁻¹).aestronglyMeasurable).congr
      (ae_of_all _ fun x => (div_eq_mul_inv _ _).symm)
  · rw [norm_div, Complex.norm_real]
    exact div_le_div_of_nonneg_left (norm_nonneg _) (abs_pos.mpr hζ) (abs_im_le_norm_sub ζ x)

theorem I_zero (ζ : ℂ) : W.I 0 ζ = W.G ζ := by simp [I, G, P_zero]

theorem L_P_eq_zero (n : ℕ) : W.L (W.P (n + 1)) = 0 := by
  have := (W.orth (n + 1)).1 0 (by omega)
  simpa using this

theorem I_succ {n : ℕ} {ζ : ℂ} (hζ : ζ.im ≠ 0) :
    ∫ x, ((((W.P n).eval x * x) * W.w x : ℝ) : ℂ) / (ζ - x) =
      ζ * W.I n ζ - W.L (W.P n) := by
  have e : ∀ x : ℝ, ((((W.P n).eval x * x) * W.w x : ℝ) : ℂ) / (ζ - x) =
      ζ * ((((W.P n).eval x * W.w x : ℝ) : ℂ) / (ζ - x)) - (((W.P n).eval x * W.w x : ℝ) : ℂ) :=
    fun x => by
      have := sub_ofReal_ne_zero hζ x
      push_cast
      field_simp
      ring
  simp_rw [e]
  have hi2 : Integrable fun x : ℝ => (((W.P n).eval x * W.w x : ℝ) : ℂ) :=
    (W.integrable_eval _).ofReal
  rw [integral_sub ((integrable_ofReal_div_sub (W.integrable_eval _) hζ).const_mul ζ) hi2,
    integral_const_mul, integral_complex_ofReal]
  rfl

theorem I_one {ζ : ℂ} (hζ : ζ.im ≠ 0) : W.I 1 ζ = ζ * W.G ζ - W.mom 0 := by
  have h := W.I_succ (n := 0) hζ
  simp only [P_zero, eval_one, one_mul] at h
  rw [I, P_one]
  simp only [eval_X]
  rw [h, W.I_zero]
  simp [L, mom]

theorem I_succ_succ (n : ℕ) {ζ : ℂ} (hζ : ζ.im ≠ 0) :
    W.I (n + 2) ζ = ζ * W.I (n + 1) ζ - W.lam (n + 1) * W.I n ζ := by
  have e : ∀ x : ℝ, (((W.P (n + 2)).eval x * W.w x : ℝ) : ℂ) / (ζ - x) =
      ((((W.P (n + 1)).eval x * x) * W.w x : ℝ) : ℂ) / (ζ - x) -
        W.lam (n + 1) * ((((W.P n).eval x * W.w x : ℝ) : ℂ) / (ζ - x)) := fun x => by
    rw [P_succ_succ]
    simp only [eval_sub, eval_mul, eval_X, eval_C]
    push_cast
    ring
  rw [I]
  simp_rw [e]
  have hi1 : Integrable fun x : ℝ => ((((W.P (n + 1)).eval x * x) * W.w x : ℝ) : ℂ) / (ζ - x) := by
    have := integrable_ofReal_div_sub (W.integrable_eval (W.P (n + 1) * X)) hζ
    simpa [eval_mul] using this
  rw [integral_sub hi1 ((integrable_ofReal_div_sub (W.integrable_eval _) hζ).const_mul _),
    integral_const_mul, W.I_succ hζ, W.L_P_eq_zero, Complex.ofReal_zero, sub_zero]
  rfl

/-- **Markov's formula**: `G(ζ) Pₙ(ζ) − Qₙ(ζ) = ∫ Pₙ(x) w(x)/(ζ − x) dx`. -/
theorem G_mul_pz_sub_qz {ζ : ℂ} (hζ : ζ.im ≠ 0) :
    ∀ n, W.G ζ * W.pz n ζ - W.qz n ζ = W.I n ζ
  | 0 => by rw [pz_zero, qz_zero, I_zero]; ring
  | 1 => by rw [pz_one, qz_one, W.I_one hζ]; ring
  | n + 2 => by
    rw [pz_succ_succ, qz_succ_succ, W.I_succ_succ n hζ, ← G_mul_pz_sub_qz hζ (n + 1),
      ← G_mul_pz_sub_qz hζ n]
    ring

theorem integrable_P_mul_X_pow (n m : ℕ) :
    Integrable fun x : ℝ => (((W.P n).eval x * x ^ m * W.w x : ℝ) : ℂ) := by
  have := (W.integrable_eval (W.P n * X ^ m)).ofReal (𝕜 := ℂ)
  simpa [eval_mul] using this

theorem integral_P_mul_X_pow_eq_zero {n m : ℕ} (hm : m < n) :
    ∫ x : ℝ, (((W.P n).eval x * x ^ m * W.w x : ℝ) : ℂ) = 0 := by
  rw [integral_complex_ofReal]
  have := (W.orth n).1 m hm
  simp only [L, eval_mul, eval_pow, eval_X] at this
  rw [this, Complex.ofReal_zero]

/-- The reproducing identity: `∫ Pₙ(x) q(x) w(x)/(ζ − x) dx = q(ζ) Iₙ(ζ)` for `deg q ≤ n`. -/
theorem integral_P_mul_div {ζ : ℂ} (hζ : ζ.im ≠ 0) {n : ℕ} {q : ℝ[X]} (hq : q.natDegree ≤ n) :
    ∫ x, (((W.P n).eval x * q.eval x * W.w x : ℝ) : ℂ) / (ζ - x) = aeval ζ q * W.I n ζ := by
  set N := q.natDegree + 1 with hN
  have hpt : ∀ x : ℝ, (((W.P n).eval x * q.eval x * W.w x : ℝ) : ℂ) / (ζ - x) =
      aeval ζ q * ((((W.P n).eval x * W.w x : ℝ) : ℂ) / (ζ - x)) -
        ∑ j ∈ range N, ∑ i ∈ range j, (q.coeff j : ℂ) * ζ ^ i *
          (((W.P n).eval x * x ^ (j - 1 - i) * W.w x : ℝ) : ℂ) := fun x => by
    have hne := sub_ofReal_ne_zero hζ x
    have hD : ((q.eval x : ℝ) : ℂ) = aeval ζ q - (ζ - x) * ∑ j ∈ range N, (q.coeff j : ℂ) *
        ∑ i ∈ range j, ζ ^ i * (x : ℂ) ^ (j - 1 - i) := by
      rw [aeval_eq_sum_range, eval_eq_sum_range, Finset.mul_sum]
      push_cast
      rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.real_smul, mul_left_comm, ← mul_add, mul_comm (ζ - x), geom_sum₂_mul]
      ring
    have e1 : (((W.P n).eval x * q.eval x * W.w x : ℝ) : ℂ) / (ζ - x) =
        (((W.P n).eval x * W.w x : ℝ) : ℂ) * ((q.eval x : ℝ) : ℂ) / (ζ - x) := by
      push_cast; ring
    rw [e1, hD]
    have e2 : ∑ j ∈ range N, ∑ i ∈ range j, (q.coeff j : ℂ) * ζ ^ i *
        (((W.P n).eval x * x ^ (j - 1 - i) * W.w x : ℝ) : ℂ) =
        (((W.P n).eval x * W.w x : ℝ) : ℂ) * ∑ j ∈ range N, (q.coeff j : ℂ) *
          ∑ i ∈ range j, ζ ^ i * (x : ℂ) ^ (j - 1 - i) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast
      ring
    rw [e2]
    field_simp
  have hterm : ∀ j ∈ range N, ∀ i ∈ range j, Integrable fun x : ℝ => (q.coeff j : ℂ) * ζ ^ i *
      (((W.P n).eval x * x ^ (j - 1 - i) * W.w x : ℝ) : ℂ) := fun j _ i _ =>
    (W.integrable_P_mul_X_pow n _).const_mul _
  have hsum : Integrable fun x : ℝ => ∑ j ∈ range N, ∑ i ∈ range j, (q.coeff j : ℂ) * ζ ^ i *
      (((W.P n).eval x * x ^ (j - 1 - i) * W.w x : ℝ) : ℂ) :=
    integrable_finsetSum _ fun j hj => integrable_finsetSum _ fun i hi => hterm j hj i hi
  simp_rw [hpt]
  rw [integral_sub ((integrable_ofReal_div_sub (W.integrable_eval _) hζ).const_mul _) hsum,
    integral_const_mul, integral_finsetSum _ fun j hj => integrable_finsetSum _ fun i hi =>
      hterm j hj i hi]
  have hz : ∀ j ∈ range N, ∫ x : ℝ, ∑ i ∈ range j, (q.coeff j : ℂ) * ζ ^ i *
      (((W.P n).eval x * x ^ (j - 1 - i) * W.w x : ℝ) : ℂ) = 0 := fun j hj => by
    rw [integral_finsetSum _ fun i hi => hterm j hj i hi]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [integral_const_mul, W.integral_P_mul_X_pow_eq_zero, mul_zero]
    have := Finset.mem_range.mp hj
    have := Finset.mem_range.mp hi
    omega
  rw [Finset.sum_eq_zero hz, sub_zero]
  rfl

/-- A nonnegative integrable function that is positive off a finite set has positive integral. -/
theorem integral_pos_of_pos_off_finite {f : ℝ → ℝ} (hf : Integrable f) (hnn : ∀ x, 0 ≤ f x)
    {F : Set ℝ} (hF : F.Finite) (hpos : ∀ x ∉ F, 0 < f x) : 0 < ∫ x, f x := by
  rw [integral_pos_iff_support_of_nonneg_ae (ae_of_all _ hnn) hf]
  have hsub : (Function.support f)ᶜ ⊆ F := fun x hx => by
    simp only [Set.mem_compl_iff, Function.mem_support, not_not] at hx
    by_contra hxF
    exact (hpos x hxF).ne' hx
  by_contra hcon
  have h0 : volume (Function.support f) = 0 := le_antisymm (not_lt.mp hcon) bot_le
  have h1 : volume (Function.support f)ᶜ = 0 := measure_mono_null hsub (hF.measure_zero _)
  have := measure_union_null h0 h1
  rw [Set.union_compl_self, Real.volume_univ] at this
  exact ENNReal.top_ne_zero this

theorem im_ofReal_div_sub (a : ℝ) (ζ : ℂ) (x : ℝ) :
    ((a : ℂ) / (ζ - x)).im = -(a * ζ.im / ‖ζ - x‖ ^ 2) := by
  rw [Complex.div_im, ← Complex.normSq_eq_norm_sq]
  simp

/-- `Im ∫ Pₙ² w/(ζ − x) = −Im ζ ∫ Pₙ² w/|ζ − x|²`. -/
theorem im_integral_P_sq {ζ : ℂ} (hζ : ζ.im ≠ 0) (n : ℕ) :
    Integrable (fun x : ℝ => (W.P n).eval x ^ 2 * W.w x / ‖ζ - x‖ ^ 2) ∧
      (W.pz n ζ * W.I n ζ).im =
        -(ζ.im * ∫ x : ℝ, (W.P n).eval x ^ 2 * W.w x / ‖ζ - x‖ ^ 2) := by
  have hrep := W.integral_P_mul_div hζ (q := W.P n) (W.natDegree_P n).le
  have hi := integrable_ofReal_div_sub (W.integrable_eval (W.P n * W.P n)) hζ
  simp only [eval_mul] at hi
  have hint : Integrable (fun x : ℝ => (W.P n).eval x ^ 2 * W.w x / ‖ζ - x‖ ^ 2) := by
    refine ((W.integrable_eval (W.P n * W.P n)).div_const (ζ.im ^ 2)).mono' ?_
      (ae_of_all _ fun x => ?_)
    · have hm : AEStronglyMeasurable (fun x : ℝ => (W.P n).eval x ^ 2 * W.w x) volume := by
        refine (W.integrable_eval (W.P n * W.P n)).aestronglyMeasurable.congr
          (ae_of_all _ fun x => ?_)
        simp [eval_mul, sq]
      exact (hm.mul (by fun_prop : Measurable fun x : ℝ => (‖ζ - x‖ ^ 2)⁻¹).aestronglyMeasurable
        ).congr (ae_of_all _ fun x => (div_eq_mul_inv _ _).symm)
    · have hw := W.nonneg x
      have h1 : ζ.im ^ 2 ≤ ‖ζ - x‖ ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (abs_im_le_norm_sub ζ x) 2
      have h2 : 0 < ζ.im ^ 2 := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), eval_mul, ← sq]
      exact div_le_div_of_nonneg_left (by positivity) h2 h1
  refine ⟨hint, ?_⟩
  rw [pz, ← hrep]
  show RCLike.im (K := ℂ) _ = _
  rw [← integral_im hi]
  simp only [RCLike.im_to_complex, im_ofReal_div_sub]
  rw [integral_neg, ← integral_const_mul]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only
  ring

/-- `Pₙ(ζ) ≠ 0` off the real axis. -/
theorem pz_ne_zero {ζ : ℂ} (hζ : ζ.im ≠ 0) (n : ℕ) : W.pz n ζ ≠ 0 := by
  intro h0
  obtain ⟨hint, him⟩ := W.im_integral_P_sq hζ n
  rw [h0, zero_mul, Complex.zero_im] at him
  have hpos : 0 < ∫ x : ℝ, (W.P n).eval x ^ 2 * W.w x / ‖ζ - x‖ ^ 2 := by
    refine integral_pos_of_pos_off_finite hint (fun x => by
      have := W.nonneg x; positivity) (F := insert 0 ((W.P n).roots.toFinset : Set ℝ))
      ((Finset.finite_toSet _).insert 0) fun x hx => ?_
    simp only [Set.mem_insert_iff, Finset.mem_coe, Multiset.mem_toFinset, not_or] at hx
    have h1 : (W.P n).eval x ≠ 0 := fun h => hx.2 ((mem_roots (W.P_ne_zero n)).mpr h)
    have h2 := W.pos x hx.1
    have h3 : 0 < ‖ζ - x‖ := norm_pos_iff.mpr (sub_ofReal_ne_zero hζ x)
    positivity
  have := mul_ne_zero hζ hpos.ne'
  exact this (neg_eq_zero.mp him.symm)

/-! ### The error bound -/

/-- `Sₙ(ζ) = ∑_{k<n} |Pₖ(ζ)|²/hₖ`. -/
noncomputable def S (n : ℕ) (ζ : ℂ) : ℝ := ∑ k ∈ range n, ‖W.pz k ζ‖ ^ 2 / W.h k

theorem S_nonneg (n : ℕ) (ζ : ℂ) : 0 ≤ W.S n ζ :=
  Finset.sum_nonneg fun k _ => div_nonneg (sq_nonneg _) (W.h_pos k).le

theorem S_succ (n : ℕ) (ζ : ℂ) : W.S (n + 1) ζ = W.S n ζ + ‖W.pz n ζ‖ ^ 2 / W.h n := by
  rw [S, Finset.sum_range_succ]; rfl

theorem S_pos {ζ : ℂ} {n : ℕ} (hn : 1 ≤ n) : 0 < W.S n ζ := by
  have h0 : 0 < ‖W.pz 0 ζ‖ ^ 2 / W.h 0 := by
    rw [pz_zero, norm_one]; exact div_pos (by norm_num) (W.h_pos 0)
  exact h0.trans_le (Finset.single_le_sum (f := fun k => ‖W.pz k ζ‖ ^ 2 / W.h k)
    (fun k _ => div_nonneg (sq_nonneg _) (W.h_pos k).le) (Finset.mem_range.mpr hn))

/-- `L((∑ aₖ Pₖ)²) = ∑ aₖ² hₖ`. -/
theorem L_sum_C_mul_P_sq (n : ℕ) (a : ℕ → ℝ) :
    W.L ((∑ k ∈ range n, C (a k) * W.P k) * (∑ k ∈ range n, C (a k) * W.P k)) =
      ∑ k ∈ range n, a k ^ 2 * W.h k := by
  rw [Finset.sum_mul, W.L_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mul_sum, W.L_sum, Finset.sum_eq_single k]
  · rw [show C (a k) * W.P k * (C (a k) * W.P k) = C (a k ^ 2) * (W.P k * W.P k) by
      rw [C_pow]; ring, W.L_C_mul, ← W.h_eq]
  · intro l _ hlk
    rw [show C (a k) * W.P k * (C (a l) * W.P l) = C (a k * a l) * (W.P k * W.P l) by
      rw [C_mul]; ring, W.L_C_mul, W.L_P_mul_P_of_ne (Ne.symm hlk), mul_zero]
  · intro h; exact absurd hk h

/-- Cauchy–Schwarz for the weight: `(∫ f g w)² ≤ ∫ f² w ∫ g² w`. -/
theorem sq_integral_mul_w_le {f g : ℝ → ℝ} (h1 : Integrable fun x => f x ^ 2 * W.w x)
    (h2 : Integrable fun x => g x ^ 2 * W.w x) (h3 : Integrable fun x => f x * g x * W.w x) :
    (∫ x, f x * g x * W.w x) ^ 2 ≤ (∫ x, f x ^ 2 * W.w x) * ∫ x, g x ^ 2 * W.w x := by
  have hq : ∀ t : ℝ, 0 ≤ (∫ x, f x ^ 2 * W.w x) * (t * t) + (-2 * ∫ x, f x * g x * W.w x) * t +
      ∫ x, g x ^ 2 * W.w x := fun t => by
    have h0 : 0 ≤ ∫ x, (t * f x - g x) ^ 2 * W.w x :=
      integral_nonneg fun x => mul_nonneg (sq_nonneg _) (W.nonneg x)
    have e : ∀ x, (t * f x - g x) ^ 2 * W.w x =
        (t * t) * (f x ^ 2 * W.w x) - (2 * t) * (f x * g x * W.w x) + g x ^ 2 * W.w x :=
      fun x => by ring
    simp_rw [e] at h0
    have i1 : Integrable fun x => t * t * (f x ^ 2 * W.w x) := h1.const_mul _
    have i2 : Integrable fun x => 2 * t * (f x * g x * W.w x) := h3.const_mul _
    have i12 : Integrable fun x => t * t * (f x ^ 2 * W.w x) - 2 * t * (f x * g x * W.w x) :=
      i1.sub i2
    rw [integral_add i12 h2, integral_sub i1 i2, integral_const_mul,
      integral_const_mul] at h0
    linarith
  have := discrim_le_zero hq
  unfold discrim at this
  nlinarith

/-- **The error bound**: `|G(ζ) − Qₙ(ζ)/Pₙ(ζ)| ≤ 1/(|ℑζ| Sₙ(ζ))` for `n ≥ 1`, `ℑζ ≠ 0`. -/
theorem norm_G_sub_le {ζ : ℂ} (hζ : ζ.im ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    ‖W.G ζ - W.qz n ζ / W.pz n ζ‖ ≤ 1 / (|ζ.im| * W.S n ζ) := by
  have hp := W.pz_ne_zero hζ n
  have hSpos := W.S_pos (ζ := ζ) hn
  have him := abs_pos.mpr hζ
  have hE : W.G ζ - W.qz n ζ / W.pz n ζ = W.I n ζ / W.pz n ζ := by
    rw [← W.G_mul_pz_sub_qz hζ n]; field_simp
  rw [hE, norm_div]
  -- the coefficients `cₖ = conj(Pₖ(ζ))/hₖ` and `r(x) = ∑ cₖ Pₖ(x)`
  set c : ℕ → ℂ := fun k => (starRingEnd ℂ) (W.pz k ζ) / W.h k with hc
  set R1 : ℝ[X] := ∑ k ∈ range n, C (c k).re * W.P k with hR1
  set R2 : ℝ[X] := ∑ k ∈ range n, C (c k).im * W.P k with hR2
  set r : ℝ → ℂ := fun x => ∑ k ∈ range n, c k * (((W.P k).eval x : ℝ) : ℂ) with hr
  have hr_re : ∀ x, (r x).re = R1.eval x := fun x => by
    simp [hr, hR1, eval_finsetSum]
  have hr_im : ∀ x, (r x).im = R2.eval x := fun x => by
    simp [hr, hR2, eval_finsetSum]
  have hr_norm : ∀ x, ‖r x‖ ^ 2 = R1.eval x ^ 2 + R2.eval x ^ 2 := fun x => by
    rw [← hr_re, ← hr_im, Complex.sq_norm, Complex.normSq_apply]; ring
  have hcS : ∑ k ∈ range n, c k * W.pz k ζ = (W.S n ζ : ℂ) := by
    rw [S]; push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hc]
    rw [div_mul_eq_mul_div, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast; ring
  -- `S Iₙ = ∫ Pₙ(x) r(x) w(x)/(ζ − x) dx`
  have hint_k : ∀ k ∈ range n, Integrable fun x : ℝ => c k *
      ((((W.P n).eval x * (W.P k).eval x * W.w x : ℝ) : ℂ) / (ζ - x)) := fun k _ => by
    have := integrable_ofReal_div_sub (W.integrable_eval (W.P n * W.P k)) hζ
    simpa [eval_mul] using this.const_mul (c k)
  have hSI : (W.S n ζ : ℂ) * W.I n ζ = ∫ x : ℝ, ∑ k ∈ range n, c k *
      ((((W.P n).eval x * (W.P k).eval x * W.w x : ℝ) : ℂ) / (ζ - x)) := by
    rw [integral_finsetSum _ hint_k, ← hcS, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [integral_const_mul, W.integral_P_mul_div hζ (q := W.P k)
      (by rw [W.natDegree_P]; exact (Finset.mem_range.mp hk).le), pz]
    ring
  -- the pointwise norm of the integrand
  have hpt : ∀ x : ℝ, ‖∑ k ∈ range n, c k *
      ((((W.P n).eval x * (W.P k).eval x * W.w x : ℝ) : ℂ) / (ζ - x))‖ =
      (|(W.P n).eval x| / ‖ζ - x‖) * ‖r x‖ * W.w x := fun x => by
    have e : ∑ k ∈ range n, c k * ((((W.P n).eval x * (W.P k).eval x * W.w x : ℝ) : ℂ) /
        (ζ - x)) = (((W.P n).eval x * W.w x : ℝ) : ℂ) / (ζ - x) * r x := by
      rw [hr, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      push_cast; ring
    rw [e, norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (W.nonneg x)]
    ring
  -- integrability of the three Cauchy–Schwarz integrands
  obtain ⟨hA, hAim⟩ := W.im_integral_P_sq hζ n
  have hB : Integrable fun x : ℝ => ‖r x‖ ^ 2 * W.w x := by
    have := W.integrable_eval (R1 * R1 + R2 * R2)
    refine this.congr (ae_of_all _ fun x => ?_)
    simp only [eval_add, eval_mul, hr_norm]
    ring
  have hcont_r : Continuous r := continuous_finsetSum _ fun k _ =>
    continuous_const.mul (Complex.continuous_ofReal.comp (W.P k).continuous)
  have hC : Integrable fun x : ℝ => (|(W.P n).eval x| / ‖ζ - x‖) * ‖r x‖ * W.w x := by
    refine ((hA.add hB).div_const 2).mono' ?_ (ae_of_all _ fun x => ?_)
    · have hm : Measurable fun x : ℝ => (|(W.P n).eval x| / ‖ζ - x‖) * ‖r x‖ := by fun_prop
      exact hm.aestronglyMeasurable.mul W.aestronglyMeasurable_w
    · have hw := W.nonneg x
      have hne : 0 < ‖ζ - x‖ := norm_pos_iff.mpr (sub_ofReal_ne_zero hζ x)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Pi.add_apply]
      have : (|(W.P n).eval x| / ‖ζ - x‖) * ‖r x‖ ≤
          ((W.P n).eval x ^ 2 / ‖ζ - x‖ ^ 2 + ‖r x‖ ^ 2) / 2 := by
        have := two_mul_le_add_sq (|(W.P n).eval x| / ‖ζ - x‖) ‖r x‖
        rw [div_pow, sq_abs] at this
        linarith
      calc (|(W.P n).eval x| / ‖ζ - x‖) * ‖r x‖ * W.w x
          ≤ ((W.P n).eval x ^ 2 / ‖ζ - x‖ ^ 2 + ‖r x‖ ^ 2) / 2 * W.w x := by gcongr
        _ = _ := by ring
  have hCS := W.sq_integral_mul_w_le (f := fun x => |(W.P n).eval x| / ‖ζ - x‖)
    (g := fun x => ‖r x‖)
    (hA.congr (ae_of_all _ fun x => by simp only [div_pow, sq_abs]; ring))
    hB hC
  have hAeq : ∫ x : ℝ, (|(W.P n).eval x| / ‖ζ - x‖) ^ 2 * W.w x =
      ∫ x : ℝ, (W.P n).eval x ^ 2 * W.w x / ‖ζ - x‖ ^ 2 :=
    integral_congr_ae (ae_of_all _ fun x => by simp only [div_pow, sq_abs]; ring)
  have hBeq : ∫ x : ℝ, ‖r x‖ ^ 2 * W.w x = W.S n ζ := by
    have e : ∫ x : ℝ, ‖r x‖ ^ 2 * W.w x = W.L (R1 * R1) + W.L (R2 * R2) := by
      rw [← W.L_add, L]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      simp only [eval_add, eval_mul, hr_norm]
      ring
    rw [e, hR1, hR2, W.L_sum_C_mul_P_sq, W.L_sum_C_mul_P_sq, ← Finset.sum_add_distrib, S]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hh := (W.h_pos k).ne'
    have : (c k).re ^ 2 + (c k).im ^ 2 = ‖W.pz k ζ‖ ^ 2 / W.h k ^ 2 := by
      rw [show (c k).re ^ 2 + (c k).im ^ 2 = ‖c k‖ ^ 2 by
        rw [Complex.sq_norm, Complex.normSq_apply]; ring, hc]
      simp only
      rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg (W.h_pos k).le,
        div_pow]
    rw [← add_mul, this]
    field_simp
  rw [hAeq, hBeq] at hCS
  -- assemble
  have hnormSI : W.S n ζ * ‖W.I n ζ‖ ≤ ∫ x : ℝ, (|(W.P n).eval x| / ‖ζ - x‖) * ‖r x‖ * W.w x := by
    have := norm_integral_le_integral_norm (μ := volume) (fun x : ℝ => ∑ k ∈ range n, c k *
      ((((W.P n).eval x * (W.P k).eval x * W.w x : ℝ) : ℂ) / (ζ - x)))
    rw [← hSI, norm_mul, Complex.norm_real, Real.norm_of_nonneg (W.S_nonneg n ζ)] at this
    simp_rw [hpt] at this
    exact this
  set A := ∫ x : ℝ, (W.P n).eval x ^ 2 * W.w x / ‖ζ - x‖ ^ 2 with hAdef
  have hA_le : |ζ.im| * A ≤ ‖W.pz n ζ‖ * ‖W.I n ζ‖ := by
    have := Complex.abs_im_le_norm (W.pz n ζ * W.I n ζ)
    rw [hAim, norm_mul, abs_neg, abs_mul, abs_of_nonneg (integral_nonneg fun x => by
      have := W.nonneg x; positivity)] at this
    exact this
  have hC0 : 0 ≤ ∫ x : ℝ, (|(W.P n).eval x| / ‖ζ - x‖) * ‖r x‖ * W.w x :=
    integral_nonneg fun x => by have := W.nonneg x; positivity
  have h1 : (W.S n ζ * ‖W.I n ζ‖) ^ 2 ≤ A * W.S n ζ :=
    (pow_le_pow_left₀ (by positivity) hnormSI 2).trans hCS
  rcases eq_or_lt_of_le (norm_nonneg (W.I n ζ)) with h0 | hIpos
  · rw [← h0, zero_div]; positivity
  have h2 : |ζ.im| * W.S n ζ * ‖W.I n ζ‖ ≤ ‖W.pz n ζ‖ := by
    have h3 : W.S n ζ * (|ζ.im| * W.S n ζ * ‖W.I n ζ‖ ^ 2) ≤
        W.S n ζ * (‖W.pz n ζ‖ * ‖W.I n ζ‖) := by nlinarith
    have h4 := le_of_mul_le_mul_left h3 hSpos
    nlinarith
  rw [div_le_div_iff₀ (norm_pos_iff.mpr hp) (by positivity)]
  linarith

/-! ### Christoffel–Darboux and the growth of `Sₙ` -/

/-- **Christoffel–Darboux** at `(ζ, ζ̄)`:
`(ζ − ζ̄) ∑_{k≤n} Pₖ(ζ) conj Pₖ(ζ)/hₖ = (P_{n+1}(ζ) conj Pₙ(ζ) − Pₙ(ζ) conj P_{n+1}(ζ))/hₙ`. -/
theorem christoffel_darboux (ζ : ℂ) : ∀ n : ℕ,
    (ζ - (starRingEnd ℂ) ζ) * ∑ k ∈ range (n + 1),
      W.pz k ζ * (starRingEnd ℂ) (W.pz k ζ) / W.h k =
      (W.pz (n + 1) ζ * (starRingEnd ℂ) (W.pz n ζ) -
        W.pz n ζ * (starRingEnd ℂ) (W.pz (n + 1) ζ)) / W.h n
  | 0 => by simp [pz_zero, pz_one]; ring
  | n + 1 => by
    have ih := christoffel_darboux ζ n
    have hh0 : (W.h n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (W.h_pos n).ne'
    have hh1 : (W.h (n + 1) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (W.h_pos (n + 1)).ne'
    have hl : (W.lam (n + 1) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (W.lam_pos _).ne'
    have hlm : (W.h (n + 1) : ℂ) = W.lam (n + 1) * W.h n := by
      rw [W.h_succ]; push_cast; ring
    rw [Finset.sum_range_succ, mul_add, ih, W.pz_succ_succ n ζ, map_sub, map_mul, map_mul,
      Complex.conj_ofReal, hlm]
    field_simp
    ring

theorem two_abs_im_mul_S_le (ζ : ℂ) (n : ℕ) :
    2 * |ζ.im| * W.S (n + 1) ζ ≤ √(W.lam (n + 1)) * (W.S (n + 2) ζ - W.S n ζ) := by
  have hcd := W.christoffel_darboux ζ n
  have hS : ∑ k ∈ range (n + 1), W.pz k ζ * (starRingEnd ℂ) (W.pz k ζ) / W.h k =
      (W.S (n + 1) ζ : ℂ) := by
    rw [S]; push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  rw [hS, show ζ - (starRingEnd ℂ) ζ = 2 * ζ.im * Complex.I by
    rw [Complex.sub_conj]; push_cast; ring] at hcd
  have hn := congrArg norm hcd
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Complex.norm_real, norm_div, Complex.norm_real, Real.norm_of_nonneg (W.h_pos n).le,
    Real.norm_of_nonneg (W.S_nonneg _ _), Real.norm_eq_abs, show ‖(2 : ℂ)‖ = 2 by simp] at hn
  have hD : ‖W.pz (n + 1) ζ * (starRingEnd ℂ) (W.pz n ζ) -
      W.pz n ζ * (starRingEnd ℂ) (W.pz (n + 1) ζ)‖ ≤ 2 * (‖W.pz (n + 1) ζ‖ * ‖W.pz n ζ‖) := by
    refine (norm_sub_le _ _).trans (le_of_eq ?_)
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]; ring
  set a := ‖W.pz (n + 1) ζ‖
  set b := ‖W.pz n ζ‖
  set lam := W.lam (n + 1)
  have hlam := W.lam_pos (n + 1)
  have hh := W.h_pos n
  set sl := √lam with hsl
  have hsl0 : 0 < sl := Real.sqrt_pos.mpr hlam
  have hsl2 : sl ^ 2 = lam := Real.sq_sqrt hlam.le
  have hdiff : W.S (n + 2) ζ - W.S n ζ = a ^ 2 / W.h (n + 1) + b ^ 2 / W.h n := by
    rw [S_succ, S_succ]; ring
  rw [hdiff, W.h_succ, show W.lam (n + 1) = sl ^ 2 from hsl2.symm]
  have key : 2 * (a * b) / W.h n ≤ sl * (a ^ 2 / (sl ^ 2 * W.h n) + b ^ 2 / W.h n) := by
    rw [div_le_iff₀ hh]
    have : sl * (a ^ 2 / (sl ^ 2 * W.h n) + b ^ 2 / W.h n) * W.h n = a ^ 2 / sl + sl * b ^ 2 := by
      field_simp
    rw [this, div_add' _ _ _ hsl0.ne', le_div_iff₀ hsl0]
    nlinarith [sq_nonneg (a - sl * b)]
  calc 2 * |ζ.im| * W.S (n + 1) ζ = 2 * |ζ.im| * W.S (n + 1) ζ := rfl
    _ = ‖W.pz (n + 1) ζ * (starRingEnd ℂ) (W.pz n ζ) -
        W.pz n ζ * (starRingEnd ℂ) (W.pz (n + 1) ζ)‖ / W.h n := by rw [← hn]
    _ ≤ 2 * (a * b) / W.h n := by gcongr
    _ ≤ _ := key

/-- A growth lemma: if `2c S_{n+1} ≤ μ_{n+1}(S_{n+2} − S_n)`, `S` is monotone with `S₁ > 0`,
and `∑ 1/μₙ = ∞`, then `Sₙ → ∞`. -/
theorem tendsto_atTop_of_growth {S μ : ℕ → ℝ} {c : ℝ} (hc : 0 < c) (hμ : ∀ n, 0 < μ n)
    (hmono : Monotone S) (hS1 : 0 < S 1)
    (hgrow : ∀ n, 2 * c * S (n + 1) ≤ μ (n + 1) * (S (n + 2) - S n))
    (hdiv : ¬Summable fun n => 1 / μ (n + 1)) : Tendsto S atTop atTop := by
  set T : ℕ → ℝ := fun n => S (n + 1) + S (n + 2) with hT
  have hT0 : 0 < T 0 := by
    have := hmono (show 1 ≤ 2 by omega); simp only [hT]; linarith
  have hstep : ∀ n, T n * (1 + c / μ (n + 2)) ≤ T (n + 1) := fun n => by
    have h1 := hgrow (n + 1)
    have h2 := hmono (show n + 1 ≤ n + 2 by omega)
    have hm := hμ (n + 2)
    have this : c * (S (n + 1) + S (n + 2)) ≤ μ (n + 2) * (S (n + 3) - S (n + 1)) := by
      have : 2 * c * S (n + 2) ≤ μ (n + 2) * (S (n + 3) - S (n + 1)) := h1
      nlinarith
    have key : (S (n + 1) + S (n + 2)) * c / μ (n + 2) ≤ S (n + 3) - S (n + 1) := by
      rw [div_le_iff₀ hm]; linarith
    have e : T n * (1 + c / μ (n + 2)) =
        (S (n + 1) + S (n + 2)) + (S (n + 1) + S (n + 2)) * c / μ (n + 2) := by
      simp only [hT]; ring
    rw [e]
    show _ ≤ S (n + 2) + S (n + 3)
    linarith
  have hTmono : ∀ n, T 0 ≤ T n := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      refine ih.trans (le_trans ?_ (hstep n))
      have : 0 ≤ c / μ (n + 2) := div_nonneg hc.le (hμ _).le
      nlinarith [hT0]
  have hlin : ∀ n, T 0 * (1 + c * ∑ k ∈ range n, 1 / μ (k + 2)) ≤ T n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h := hstep n
      have h0 := hTmono n
      have hpos : 0 ≤ c / μ (n + 2) := div_nonneg hc.le (hμ _).le
      rw [Finset.sum_range_succ]
      calc T 0 * (1 + c * (∑ k ∈ range n, 1 / μ (k + 2) + 1 / μ (n + 2)))
          = T 0 * (1 + c * ∑ k ∈ range n, 1 / μ (k + 2)) + T 0 * (c / μ (n + 2)) := by ring
        _ ≤ T n + T n * (c / μ (n + 2)) := add_le_add ih (mul_le_mul_of_nonneg_right h0 hpos)
        _ = T n * (1 + c / μ (n + 2)) := by ring
        _ ≤ T (n + 1) := h
  have hdiv2 : Tendsto (fun n => ∑ k ∈ range n, 1 / μ (k + 2)) atTop atTop := by
    have hnn : ∀ k, 0 ≤ 1 / μ (k + 2) := fun k => div_nonneg zero_le_one (hμ _).le
    refine (not_summable_iff_tendsto_nat_atTop_of_nonneg hnn).mp fun hs => hdiv ?_
    exact (summable_nat_add_iff 1).mp (by simpa [add_assoc] using hs)
  have hTt : Tendsto T atTop atTop := by
    refine tendsto_atTop_mono hlin ?_
    exact Tendsto.const_mul_atTop hT0 (tendsto_atTop_add_const_left _ 1
      (hdiv2.const_mul_atTop hc))
  have hS2 : Tendsto (fun n => S (n + 2)) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) (hTt.atTop_div_const two_pos)
    have := hmono (show n + 1 ≤ n + 2 by omega)
    simp only [hT]; linarith
  exact (tendsto_add_atTop_iff_nat 2).mp hS2

theorem S_monotone (ζ : ℂ) : Monotone fun n => W.S n ζ :=
  monotone_nat_of_le_succ fun n => by
    rw [S_succ]; exact le_add_of_nonneg_right (div_nonneg (sq_nonneg _) (W.h_pos n).le)

/-- If `∑ 1/√λₙ = ∞`, the convergents `Qₙ(ζ)/Pₙ(ζ)` tend to `G(ζ)` off the real axis. -/
theorem tendsto_qz_div_pz_of_not_summable
    (hdiv : ¬Summable fun n => 1 / √(W.lam (n + 1))) {ζ : ℂ} (hζ : ζ.im ≠ 0) :
    Tendsto (fun n => W.qz n ζ / W.pz n ζ) atTop (𝓝 (W.G ζ)) := by
  have him := abs_pos.mpr hζ
  have hS : Tendsto (fun n => W.S n ζ) atTop atTop :=
    tendsto_atTop_of_growth (c := |ζ.im|) (μ := fun n => √(W.lam n)) him
      (fun n => Real.sqrt_pos.mpr (W.lam_pos n)) (W.S_monotone ζ) (W.S_pos le_rfl)
      (fun n => by have := W.two_abs_im_mul_S_le ζ n; linarith) hdiv
  have hb : Tendsto (fun n => 1 / (|ζ.im| * W.S n ζ)) atTop (𝓝 0) := by
    refine (hS.const_mul_atTop him).inv_tendsto_atTop.congr fun n => ?_
    simp [one_div]
  refine tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero_norm' ?_ hb)
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [norm_norm, norm_sub_rev]
  exact W.norm_G_sub_le hζ hn

/-! ### Carleman's inequality and the moment criterion -/

/-- Carleman's weights `cⱼ = (j + 2)^{j+1}/(j + 1)^j`, with `∏_{j<n} cⱼ = (n + 1)ⁿ`. -/
noncomputable def carlemanW (j : ℕ) : ℝ := ((j : ℝ) + 2) ^ (j + 1) / ((j : ℝ) + 1) ^ j

theorem carlemanW_pos (j : ℕ) : 0 < carlemanW j := by unfold carlemanW; positivity

theorem prod_carlemanW (n : ℕ) : ∏ j ∈ range n, carlemanW j = ((n : ℝ) + 1) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, carlemanW]
    have : ((n : ℝ) + 1) ^ n ≠ 0 := by positivity
    push_cast
    field_simp
    ring

theorem carlemanW_div_le (j : ℕ) : carlemanW j / ((j : ℝ) + 1) ≤ Real.exp 1 := by
  have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have e : carlemanW j / ((j : ℝ) + 1) = (1 + 1 / ((j : ℝ) + 1)) ^ (j + 1) := by
    rw [carlemanW, show (1 : ℝ) + 1 / ((j : ℝ) + 1) = ((j : ℝ) + 2) / ((j : ℝ) + 1) by
      field_simp; ring, div_pow]
    field_simp
    ring
  rw [e]
  calc (1 + 1 / ((j : ℝ) + 1)) ^ (j + 1) ≤ Real.exp (1 / ((j : ℝ) + 1)) ^ (j + 1) := by
        gcongr
        linarith [Real.add_one_le_exp (1 / ((j : ℝ) + 1))]
    _ = Real.exp 1 := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; field_simp

/-- **Carleman's inequality**, in the form used here: if `∏_{j<n} bⱼ ≥ (c/n)ⁿ` for all `n ≥ 1`,
then `∑ bⱼ = ∞`. -/
theorem not_summable_of_prod_ge {b : ℕ → ℝ} (hb : ∀ j, 0 < b j) {c : ℝ} (hc : 0 < c)
    (hprod : ∀ n, 1 ≤ n → (c / n) ^ n ≤ ∏ j ∈ range n, b j) : ¬Summable b := by
  intro hsum
  set F : ℕ → ℝ := fun n => ∑ j ∈ range n, b j * carlemanW j with hF
  -- `c (n + 1) ≤ Fₙ` by the AM–GM inequality
  have hlin : ∀ n : ℕ, 1 ≤ n → c * ((n : ℝ) + 1) ≤ F n := fun n hn => by
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hnpos : (0 : ℝ) < n := by positivity
    have hz : ∀ j ∈ range n, 0 ≤ b j * carlemanW j := fun j _ =>
      (mul_pos (hb j) (carlemanW_pos j)).le
    have amgm := Real.geom_mean_le_arith_mean_weighted (range n) (fun _ => (n : ℝ)⁻¹)
      (fun j => b j * carlemanW j) (fun _ _ => by positivity)
      (by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp) hz
    rw [Real.finsetProd_rpow _ _ hz, ← Finset.mul_sum] at amgm
    have hP : 0 ≤ ∏ j ∈ range n, b j * carlemanW j := Finset.prod_nonneg hz
    have h1 := pow_le_pow_left₀ (Real.rpow_nonneg hP _) amgm n
    rw [Real.rpow_inv_natCast_pow hP (by omega), Finset.prod_mul_distrib, prod_carlemanW] at h1
    have h2 : (c * ((n : ℝ) + 1) / n) ^ n ≤ ((n : ℝ)⁻¹ * F n) ^ n := by
      calc (c * ((n : ℝ) + 1) / n) ^ n = (c / n) ^ n * ((n : ℝ) + 1) ^ n := by
            rw [← mul_pow]; ring
        _ ≤ (∏ j ∈ range n, b j) * ((n : ℝ) + 1) ^ n := by gcongr; exact hprod n hn
        _ ≤ _ := h1
    have h3 := (pow_le_pow_iff_left₀ (by positivity) (by
      have : 0 ≤ F n := Finset.sum_nonneg hz; positivity) (by omega)).mp h2
    rw [div_eq_mul_inv, mul_comm _ (n : ℝ)⁻¹, mul_le_mul_iff_of_pos_left (by positivity)] at h3
    exact h3
  -- the telescoping identity
  have htel : ∀ N, ∑ n ∈ range N, F (n + 1) / (((n : ℝ) + 1) * ((n : ℝ) + 2)) =
      ∑ j ∈ range N, b j * carlemanW j / ((j : ℝ) + 1) - F N / ((N : ℝ) + 1) := by
    intro N
    induction N with
    | zero => simp [hF]
    | succ N ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      have : F (N + 1) = F N + b N * carlemanW N := by simp [hF, Finset.sum_range_succ]
      rw [this]
      push_cast
      field_simp
      ring
  have hFnn : ∀ N, 0 ≤ F N := fun N => Finset.sum_nonneg fun j _ =>
    (mul_pos (hb j) (carlemanW_pos j)).le
  have hbound : ∀ N, c * ∑ n ∈ range N, (1 / ((n : ℝ) + 1)) ≤ Real.exp 1 * ∑' j, b j := by
    intro N
    calc c * ∑ n ∈ range N, (1 / ((n : ℝ) + 1))
        ≤ ∑ n ∈ range N, F (n + 1) / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun n _ => ?_
          have := hlin (n + 1) (by omega)
          push_cast at this
          rw [le_div_iff₀ (by positivity)]
          calc c * (1 / ((n : ℝ) + 1)) * (((n : ℝ) + 1) * ((n : ℝ) + 2)) = c * ((n : ℝ) + 2) := by
                field_simp
            _ = c * ((n : ℝ) + 1 + 1) := by ring
            _ ≤ F (n + 1) := this
      _ ≤ ∑ j ∈ range N, b j * carlemanW j / ((j : ℝ) + 1) := by
          rw [htel]
          have := hFnn N
          have : 0 ≤ F N / ((N : ℝ) + 1) := by positivity
          linarith
      _ ≤ ∑ j ∈ range N, Real.exp 1 * b j := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [mul_div_assoc, mul_comm]
          exact mul_le_mul_of_nonneg_right (carlemanW_div_le j) (hb j).le
      _ = Real.exp 1 * ∑ j ∈ range N, b j := by rw [Finset.mul_sum]
      _ ≤ Real.exp 1 * ∑' j, b j := by
          gcongr
          exact hsum.sum_le_tsum _ fun j _ => (hb j).le
  have ht := Real.tendsto_sum_range_one_div_nat_succ_atTop.const_mul_atTop hc
  obtain ⟨N, hN⟩ := (ht.eventually_gt_atTop (Real.exp 1 * ∑' j, b j)).exists
  exact absurd (hbound N) (not_le.mpr hN)

theorem prod_lam (n : ℕ) : ∏ j ∈ range n, W.lam (j + 1) = W.h n / W.h 0 := by
  induction n with
  | zero => simp [(W.h_pos 0).ne']
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, W.h_succ]
    field_simp [(W.h_pos 0).ne']

/-- The moment criterion: if `m_{2n} ≤ K (Cn)^{2n}`, then `∑ 1/√λₙ = ∞` (via Carleman). -/
theorem not_summable_inv_sqrt_lam {K C : ℝ} (hK : 0 < K) (hC : 0 < C)
    (hmom : ∀ n, 1 ≤ n → W.mom (2 * n) ≤ K * (C * n) ^ (2 * n)) :
    ¬Summable fun n => 1 / √(W.lam (n + 1)) := by
  set δ := min 1 (W.h 0 / K) with hδ
  have hδ0 : 0 < δ := lt_min one_pos (div_pos (W.h_pos 0) hK)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  refine not_summable_of_prod_ge (fun j => by
    have := W.lam_pos (j + 1); positivity) (c := δ / C) (div_pos hδ0 hC) fun n hn => ?_
  have hb : ∀ j ∈ range n, 0 ≤ 1 / √(W.lam (j + 1)) := fun j _ => by positivity
  have hsq : (∏ j ∈ range n, 1 / √(W.lam (j + 1))) ^ 2 = W.h 0 / W.h n := by
    rw [← Finset.prod_pow]
    have : ∀ j ∈ range n, (1 / √(W.lam (j + 1))) ^ 2 = 1 / W.lam (j + 1) := fun j _ => by
      rw [div_pow, Real.sq_sqrt (W.lam_pos _).le, one_pow]
    rw [Finset.prod_congr rfl this, Finset.prod_div_distrib, Finset.prod_const_one, prod_lam]
    field_simp [(W.h_pos 0).ne', (W.h_pos n).ne']
  have hhn : W.h n ≤ K * (C * n) ^ (2 * n) := (W.h_le_mom n).trans (hmom n hn)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hle : ((δ / C / n) ^ n) ^ 2 ≤ (∏ j ∈ range n, 1 / √(W.lam (j + 1))) ^ 2 := by
    rw [hsq, ← pow_mul, show δ / C / n = δ / (C * n) by ring, div_pow,
      show n * 2 = 2 * n by ring]
    have hd : δ ^ (2 * n) ≤ W.h 0 / K := by
      calc δ ^ (2 * n) ≤ δ ^ 1 := pow_le_pow_of_le_one hδ0.le hδ1 (by omega)
        _ = δ := pow_one δ
        _ ≤ W.h 0 / K := min_le_right _ _
    have hpos : 0 < (C * n) ^ (2 * n) := by positivity
    rw [div_le_div_iff₀ hpos (W.h_pos n)]
    calc δ ^ (2 * n) * W.h n ≤ W.h 0 / K * (K * (C * n) ^ (2 * n)) :=
          mul_le_mul hd hhn (W.h_pos n).le (div_nonneg (W.h_pos 0).le hK.le)
      _ = W.h 0 * (C * n) ^ (2 * n) := by field_simp
  exact (pow_le_pow_iff_left₀ (by positivity) (Finset.prod_nonneg hb) (by omega)).mp hle

/-- **Convergence of the continued fraction** of a symmetric weight with
`m_{2n} ≤ K (Cn)^{2n}`: `Qₙ(ζ)/Pₙ(ζ) → G(ζ) = ∫ w(x)/(ζ − x) dx` for `ℑζ ≠ 0`. -/
theorem tendsto_qz_div_pz {K C : ℝ} (hK : 0 < K) (hC : 0 < C)
    (hmom : ∀ n, 1 ≤ n → W.mom (2 * n) ≤ K * (C * n) ^ (2 * n)) {ζ : ℂ} (hζ : ζ.im ≠ 0) :
    Tendsto (fun n => W.qz n ζ / W.pz n ζ) atTop (𝓝 (W.G ζ)) :=
  W.tendsto_qz_div_pz_of_not_summable (W.not_summable_inv_sqrt_lam hK hC hmom) hζ

end SymWeight

end Azurite.DLMF
