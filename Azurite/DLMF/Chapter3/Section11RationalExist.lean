/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section11Rational
import Azurite.DLMF.Chapter3.Section11Remez

/-!
# DLMF §3.11(iii): existence of minimax rational approximations

"There exists a … solution of this minimax problem", in the corrected class of `P/Q` with
`Q > 0` on `[a, b]` (`dlmf_3_11_iii_exists`; with the normalization `q₀ = 1` of 3.11.16 existence
fails, `dlmf_3_11_iii_not_exists`). When `0 ∈ [a, b]` the two classes agree up to scaling
(`dlmf_3_11_iii_exists_normalized`).

Proof: a minimizing sequence, normalized by the coefficient norm of `Q`, has bounded
numerator coefficients (`coeff_norm_le_of_eval_le`, interpolation at `k + 1` nodes); a
convergent subsequence gives `P*, Q*` with `|P* − fQ*| ≤ E* |w| Q*` and `Q* ≥ 0`, `Q* ≠ 0`. The
zeros of `Q*` in `[a, b]` are zeros of `P*` and are cancelled one at a time (`cancel_zeros`), after
which `Q*` has constant sign.
-/

open Polynomial Set Filter Topology Metric

namespace Azurite.DLMF

variable {a b : ℝ}

/-! ### A continuous inequality off one point holds at the point -/

theorem nonneg_of_nonneg_off {g : ℝ → ℝ} (hab : a < b) (hg : ContinuousOn g (Icc a b))
    {z : ℝ} (hz : z ∈ Icc a b) (h : ∀ x ∈ Icc a b, x ≠ z → 0 ≤ g x) : 0 ≤ g z := by
  by_contra hneg
  push Not at hneg
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.mp (hg z hz) (-g z) (by linarith)
  -- a point of `[a, b]` within `δ` of `z`, different from `z`
  obtain ⟨x, hx, hxz, hdist⟩ : ∃ x ∈ Icc a b, x ≠ z ∧ dist x z < δ := by
    rcases lt_or_eq_of_le hz.2 with hzb | hzb
    · refine ⟨z + min (δ / 2) (b - z), ⟨by linarith [hz.1, lt_min (half_pos hδ) (sub_pos.mpr hzb)],
        by linarith [min_le_right (δ / 2) (b - z)]⟩, by
          have := lt_min (half_pos hδ) (sub_pos.mpr hzb); linarith, ?_⟩
      rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (lt_min (half_pos hδ) (sub_pos.mpr hzb))]
      linarith [min_le_left (δ / 2) (b - z)]
    · have hza : a < z := hzb ▸ hab
      refine ⟨z - min (δ / 2) (z - a), ⟨by linarith [min_le_right (δ / 2) (z - a)],
        by linarith [hz.2, lt_min (half_pos hδ) (sub_pos.mpr hza)]⟩, by
          have := lt_min (half_pos hδ) (sub_pos.mpr hza); linarith, ?_⟩
      rw [Real.dist_eq, sub_sub_cancel_left, abs_neg,
        abs_of_pos (lt_min (half_pos hδ) (sub_pos.mpr hza))]
      linarith [min_le_left (δ / 2) (z - a)]
  have := hball hx hdist
  rw [Real.dist_eq] at this
  have := h x hx hxz
  have := abs_lt.mp ‹|g x - g z| < -g z›
  linarith

/-! ### Cancelling the zeros of the denominator -/

/-- If `|P − fQ| ≤ E |w| |Q|` on `[a, b]` and `Q ≠ 0`, the common zeros in `[a, b]` can be
cancelled: there are `P′, Q′` of no larger degrees, `Q′` without zeros in `[a, b]`, with the same
inequality. -/
theorem cancel_zeros (hab : a < b) {f w : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    (hw : ContinuousOn w (Icc a b)) {E : ℝ} (n : ℕ) :
    ∀ P Q : ℝ[X], Q ≠ 0 → Q.natDegree ≤ n →
      (∀ x ∈ Icc a b, |P.eval x - f x * Q.eval x| ≤ E * |w x| * |Q.eval x|) →
      ∃ P' Q' : ℝ[X], P'.natDegree ≤ P.natDegree ∧ Q'.natDegree ≤ Q.natDegree ∧
        (∀ x ∈ Icc a b, Q'.eval x ≠ 0) ∧
        ∀ x ∈ Icc a b, |P'.eval x - f x * Q'.eval x| ≤ E * |w x| * |Q'.eval x| := by
  induction n with
  | zero =>
    intro P Q hQ0 hQn h
    refine ⟨P, Q, le_rfl, le_rfl, fun x _ => ?_, h⟩
    rw [eq_C_of_natDegree_eq_zero (Nat.le_zero.mp hQn)]
    simp only [eval_C]
    intro h0
    exact hQ0 (by rw [eq_C_of_natDegree_eq_zero (Nat.le_zero.mp hQn), h0, C_0])
  | succ n ih =>
    intro P Q hQ0 hQn h
    by_cases hroot : ∃ z ∈ Icc a b, Q.eval z = 0
    · obtain ⟨z, hz, hQz⟩ := hroot
      have hPz : P.eval z = 0 := by
        have := h z hz
        rw [hQz, mul_zero, abs_zero, mul_zero, sub_zero] at this
        exact abs_nonpos_iff.mp this
      have hdQ := mul_divByMonic_eq_iff_isRoot.mpr (show Q.IsRoot z from hQz)
      have hdP := mul_divByMonic_eq_iff_isRoot.mpr (show P.IsRoot z from hPz)
      set Q1 := Q /ₘ (X - C z)
      set P1 := P /ₘ (X - C z)
      have hQ10 : Q1 ≠ 0 := by
        intro h0; rw [h0, mul_zero] at hdQ; exact hQ0 hdQ.symm
      have hdegQ : Q1.natDegree + 1 = Q.natDegree := by
        conv_rhs => rw [← hdQ]
        rw [natDegree_mul (X_sub_C_ne_zero z) hQ10, natDegree_X_sub_C]; ring
      have hdegP : P1.natDegree ≤ P.natDegree := by
        rcases eq_or_ne P1 0 with h0 | h0
        · rw [h0, natDegree_zero]; exact Nat.zero_le _
        · conv_rhs => rw [← hdP]
          rw [natDegree_mul (X_sub_C_ne_zero z) h0, natDegree_X_sub_C]; omega
      -- the inequality for `P₁, Q₁`, first off `z`, then at `z` by continuity
      have h1 : ∀ x ∈ Icc a b, |P1.eval x - f x * Q1.eval x| ≤ E * |w x| * |Q1.eval x| := by
        intro x hx
        have hg : ContinuousOn (fun x => E * |w x| * |Q1.eval x| - |P1.eval x - f x * Q1.eval x|)
            (Icc a b) :=
          ((continuousOn_const.mul hw.abs).mul Q1.continuous.continuousOn.abs).sub
            ((P1.continuous.continuousOn.sub (hf.mul Q1.continuous.continuousOn)).abs)
        have hoff : ∀ y ∈ Icc a b, y ≠ z →
            0 ≤ E * |w y| * |Q1.eval y| - |P1.eval y - f y * Q1.eval y| := fun y hy hyz => by
          have hy' := h y hy
          rw [← hdQ, ← hdP] at hy'
          simp only [eval_mul, eval_sub, eval_X, eval_C] at hy'
          have hyz' : 0 < |y - z| := abs_pos.mpr (sub_ne_zero.mpr hyz)
          have e1 : (y - z) * P1.eval y - f y * ((y - z) * Q1.eval y) =
              (y - z) * (P1.eval y - f y * Q1.eval y) := by ring
          rw [e1, abs_mul, abs_mul, show E * |w y| * (|y - z| * |Q1.eval y|) =
            |y - z| * (E * |w y| * |Q1.eval y|) by ring] at hy'
          have := le_of_mul_le_mul_left hy' hyz'
          linarith
        by_cases hxz : x = z
        · subst hxz
          have := nonneg_of_nonneg_off hab hg hz hoff
          linarith
        · have := hoff x hx hxz
          linarith
      obtain ⟨P', Q', hP', hQ', hne, hin⟩ := ih P1 Q1 hQ10 (by omega) h1
      exact ⟨P', Q', hP'.trans hdegP, by omega, hne, hin⟩
    · push Not at hroot
      exact ⟨P, Q, le_rfl, le_rfl, hroot, h⟩

/-! ### Bounding coefficients by values at nodes -/

/-- The evaluation map at `k + 1` distinct nodes. -/
noncomputable def evalNodes {k : ℕ} (t : Fin (k + 1) → ℝ) :
    (Fin (k + 1) → ℝ) →ₗ[ℝ] (Fin (k + 1) → ℝ) where
  toFun c i := (remezPoly c).eval (t i)
  map_add' c d := by funext i; simp [remezPoly_eval, mul_add, Finset.sum_add_distrib]
  map_smul' r c := by
    funext i; simp [remezPoly_eval, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring

theorem evalNodes_injective {k : ℕ} {t : Fin (k + 1) → ℝ} (ht : Function.Injective t) :
    Function.Injective (evalNodes t) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc
  have hroots : ∀ i, (remezPoly c).eval (t i) = 0 := fun i => congrFun hc i
  have h0 : remezPoly c = 0 := by
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero (remezPoly c) ht hroots ?_
    simpa using Nat.lt_succ_of_le (remezPoly_natDegree c)
  funext i
  rw [← remezPoly_coeff c i, h0, coeff_zero]
  rfl

/-- Coefficients are bounded by the values at `k + 1` distinct nodes. -/
theorem coeff_norm_le_of_eval_le {k : ℕ} {t : Fin (k + 1) → ℝ} (ht : Function.Injective t) :
    ∃ K, 0 ≤ K ∧ ∀ c : Fin (k + 1) → ℝ, ‖c‖ ≤ K * ‖evalNodes t c‖ := by
  set e := LinearEquiv.ofInjectiveEndo (evalNodes t) (evalNodes_injective ht)
  set L := LinearMap.toContinuousLinearMap (e.symm : (Fin (k + 1) → ℝ) →ₗ[ℝ] (Fin (k + 1) → ℝ))
  refine ⟨‖L‖, norm_nonneg _, fun c => ?_⟩
  have : c = L (evalNodes t c) := by
    simp [L, e, LinearEquiv.ofInjectiveEndo]
    exact ((LinearEquiv.ofInjectiveEndo (evalNodes t) (evalNodes_injective ht)).symm_apply_apply
      c).symm
  conv_lhs => rw [this]
  exact L.le_opNorm _

/-! ### Existence -/

/-- `ε` from the inequality `|P − fQ| ≤ E |w| Q`. -/
theorem abs_ratErr_le_of {f w : ℝ → ℝ} {P Q : ℝ[X]} {E x : ℝ} (hQ : 0 < Q.eval x)
    (hw : w x ≠ 0) (h : |P.eval x - f x * Q.eval x| ≤ E * |w x| * Q.eval x) :
    |ratErr f w P Q x| ≤ E := by
  rw [ratErr, abs_div, div_le_iff₀ (abs_pos.mpr hw)]
  have e : P.eval x / Q.eval x - f x = (P.eval x - f x * Q.eval x) / Q.eval x := by
    field_simp
  rw [e, abs_div, abs_of_pos hQ, div_le_iff₀ hQ]
  linarith

/-- **DLMF §3.11(iii)** (existence, corrected class): a minimax rational approximation of type
`[k, ℓ]` with positive denominator exists. -/
theorem dlmf_3_11_iii_exists (hab : a < b) {f w : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    (hw : ContinuousOn w (Icc a b)) (hw0 : ∀ x ∈ Icc a b, w x ≠ 0) (k ℓ : ℕ) :
    ∃ P Q, IsRatMinimax a b f w k ℓ P Q := by
  set S : Set ℝ := {e | ∃ P Q, RatAdmissible a b k ℓ P Q ∧ ratMaxErr a b f w P Q = e}
  have hadm1 : RatAdmissible a b k ℓ 0 1 := ⟨by simp, by simp, fun _ _ => by simp⟩
  have hSne : S.Nonempty := ⟨_, 0, 1, hadm1, rfl⟩
  have hSbdd : BddBelow S := ⟨0, by
    rintro _ ⟨P, Q, hPQ, rfl⟩
    exact ratMaxErr_nonneg hab.le hf hw hw0 fun x hx => (hPQ.2.2 x hx).ne'⟩
  set Es := sInf S
  have hEs : ∀ P Q, RatAdmissible a b k ℓ P Q → Es ≤ ratMaxErr a b f w P Q :=
    fun P Q h => csInf_le hSbdd ⟨P, Q, h, rfl⟩
  have hEs0 : 0 ≤ Es := le_csInf hSne fun _ ⟨P, Q, hPQ, he⟩ => he ▸
    ratMaxErr_nonneg hab.le hf hw hw0 fun x hx => (hPQ.2.2 x hx).ne'
  -- a minimizing sequence, normalized by the coefficient norm of the denominator
  have hseq : ∀ n : ℕ, ∃ cp : Fin (k + 1) → ℝ, ∃ cq : Fin (ℓ + 1) → ℝ, ‖cq‖ = 1 ∧
      (∀ x ∈ Icc a b, 0 < (remezPoly cq).eval x) ∧
      ratMaxErr a b f w (remezPoly cp) (remezPoly cq) < Es + 1 / (n + 1) := by
    intro n
    obtain ⟨_, ⟨P, Q, hPQ, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hSne
      (show Es < Es + 1 / (n + 1) by
        have : (0 : ℝ) < 1 / (n + 1) := (by positivity)
        linarith)
    set cq0 : Fin (ℓ + 1) → ℝ := fun i => Q.coeff i
    set cp0 : Fin (k + 1) → ℝ := fun i => P.coeff i
    have hQeq : remezPoly cq0 = Q := by
      ext i
      by_cases hi : i ≤ ℓ
      · exact remezPoly_coeff cq0 ⟨i, Nat.lt_succ_of_le hi⟩
      · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (remezPoly_natDegree cq0)
          (not_le.mp hi)), coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hPQ.2.1 (not_le.mp hi))]
    have hPeq : remezPoly cp0 = P := by
      ext i
      by_cases hi : i ≤ k
      · exact remezPoly_coeff cp0 ⟨i, Nat.lt_succ_of_le hi⟩
      · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (remezPoly_natDegree cp0)
          (not_le.mp hi)), coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hPQ.1 (not_le.mp hi))]
    have hs : 0 < ‖cq0‖ := by
      refine norm_pos_iff.mpr fun h0 => ?_
      have : Q = 0 := by rw [← hQeq, h0]; simp [remezPoly]
      have := hPQ.2.2 a (left_mem_Icc.mpr hab.le)
      simp_all
    refine ⟨‖cq0‖⁻¹ • cp0, ‖cq0‖⁻¹ • cq0, ?_, fun x hx => ?_, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hs.ne']
    · have : (remezPoly (‖cq0‖⁻¹ • cq0)).eval x = ‖cq0‖⁻¹ * Q.eval x := by
        rw [← hQeq, remezPoly_eval, remezPoly_eval, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by simp; ring
      rw [this]
      exact mul_pos (inv_pos.mpr hs) (hPQ.2.2 x hx)
    · have hR : ratErr f w (remezPoly (‖cq0‖⁻¹ • cp0)) (remezPoly (‖cq0‖⁻¹ • cq0)) =
          ratErr f w P Q := by
        funext x
        have e1 : (remezPoly (‖cq0‖⁻¹ • cp0)).eval x = ‖cq0‖⁻¹ * P.eval x := by
          rw [← hPeq, remezPoly_eval, remezPoly_eval, Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ => by simp; ring
        have e2 : (remezPoly (‖cq0‖⁻¹ • cq0)).eval x = ‖cq0‖⁻¹ * Q.eval x := by
          rw [← hQeq, remezPoly_eval, remezPoly_eval, Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ => by simp; ring
        simp only [ratErr, e1, e2]
        rw [mul_div_mul_left _ _ (inv_ne_zero hs.ne')]
      simp only [ratMaxErr, hR]
      exact hlt
  choose cp cq hcq1 hcqpos hlt using hseq
  -- uniform bounds
  obtain ⟨Mf, hMf⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  obtain ⟨Mw, hMw⟩ := isCompact_Icc.exists_bound_of_continuousOn hw
  set R : ℝ := 1 + |a| + |b|
  have hR1 : 1 ≤ R := by have := abs_nonneg a; have := abs_nonneg b; linarith
  have hxR : ∀ x ∈ Icc a b, |x| ≤ R := fun x hx =>
    abs_le.mpr ⟨by linarith [hx.1, neg_abs_le a, abs_nonneg b],
      by linarith [hx.2, le_abs_self b, abs_nonneg a]⟩
  set BQ : ℝ := R ^ ℓ * (ℓ + 1)
  have hcn : ∀ n, cn ℓ (remezPoly (cq n)) ≤ ℓ + 1 := fun n => by
    rw [cn, ← Fin.sum_univ_eq_sum_range (fun i => |(remezPoly (cq n)).coeff i|)]
    calc ∑ i : Fin (ℓ + 1), |(remezPoly (cq n)).coeff i| ≤ ∑ _i : Fin (ℓ + 1), (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => by
            rw [remezPoly_coeff, ← Real.norm_eq_abs, ← hcq1 n]; exact norm_le_pi_norm (cq n) i
      _ = ℓ + 1 := by simp
  have hQb : ∀ n, ∀ x ∈ Icc a b, |(remezPoly (cq n)).eval x| ≤ BQ := fun n x hx =>
    (eval_bound (remezPoly_natDegree _) hR1 (hxR x hx)).trans
      (mul_le_mul_of_nonneg_left (hcn n) (by positivity))
  have hlt1 : ∀ n, ratMaxErr a b f w (remezPoly (cp n)) (remezPoly (cq n)) < Es + 1 := fun n =>
    (hlt n).trans_le (by
      have : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      linarith)
  -- the key inequality `|P − fQ| ≤ e |w| Q`
  have hineq : ∀ n, ∀ x ∈ Icc a b, |(remezPoly (cp n)).eval x - f x * (remezPoly (cq n)).eval x| ≤
      ratMaxErr a b f w (remezPoly (cp n)) (remezPoly (cq n)) * |w x| *
        (remezPoly (cq n)).eval x := fun n x hx => by
    have hq := hcqpos n x hx
    have h := abs_ratErr_le hf hw hw0 (fun y hy => (hcqpos n y hy).ne') (P := remezPoly (cp n)) hx
    rw [ratErr, abs_div, div_le_iff₀ (abs_pos.mpr (hw0 x hx))] at h
    have e : (remezPoly (cp n)).eval x / (remezPoly (cq n)).eval x - f x =
        ((remezPoly (cp n)).eval x - f x * (remezPoly (cq n)).eval x) /
          (remezPoly (cq n)).eval x := by field_simp
    rw [e, abs_div, abs_of_pos hq, div_le_iff₀ hq] at h
    nlinarith [abs_nonneg (w x)]
  -- numerator values bounded, hence coefficients bounded
  set t : Fin (k + 1) → ℝ := fun i => a + (b - a) * i / (k + 1)
  have ht : Function.Injective t := fun i j h => by
    simp only [t] at h
    have hba : b - a ≠ 0 := (sub_pos.mpr hab).ne'
    have h2 := add_left_cancel h
    rw [div_left_inj' (by positivity), mul_right_inj' hba] at h2
    have : ((i : ℕ) : ℝ) = j := h2
    exact Fin.ext (by exact_mod_cast this)
  have htI : ∀ i, t i ∈ Icc a b := fun i => by
    have hi : ((i : ℕ) : ℝ) / (k + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; exact_mod_cast (Nat.lt_succ_iff.mp i.isLt).trans
        (Nat.le_succ k)
    have hba : 0 ≤ b - a := (sub_pos.mpr hab).le
    simp only [t]
    constructor
    · have : 0 ≤ (b - a) * i / (k + 1) := by positivity
      linarith
    · have : (b - a) * i / (k + 1) ≤ b - a := by
        rw [mul_div_assoc]; nlinarith [div_nonneg (Nat.cast_nonneg (i : ℕ))
          (by positivity : (0 : ℝ) ≤ k + 1)]
      linarith
  obtain ⟨K, hK0, hK⟩ := coeff_norm_le_of_eval_le ht
  set BP : ℝ := ((Es + 1) * Mw + Mf) * BQ
  have hPb : ∀ n, ∀ x ∈ Icc a b, |(remezPoly (cp n)).eval x| ≤ BP := fun n x hx => by
    have h1 := hineq n x hx
    have h2 := hQb n x hx
    have hq := hcqpos n x hx
    have he := hlt1 n
    have he0 : 0 ≤ ratMaxErr a b f w (remezPoly (cp n)) (remezPoly (cq n)) :=
      ratMaxErr_nonneg hab.le hf hw hw0 fun y hy => (hcqpos n y hy).ne'
    have hfx := hMf x hx
    have hwx := hMw x hx
    rw [Real.norm_eq_abs] at hfx hwx
    rw [abs_of_pos hq] at h2
    have : |(remezPoly (cp n)).eval x| ≤
        |(remezPoly (cp n)).eval x - f x * (remezPoly (cq n)).eval x| +
          |f x| * (remezPoly (cq n)).eval x := by
      have := abs_add_le ((remezPoly (cp n)).eval x - f x * (remezPoly (cq n)).eval x)
        (f x * (remezPoly (cq n)).eval x)
      rw [sub_add_cancel, abs_mul, abs_of_pos hq] at this
      exact this
    have hMw0 : 0 ≤ Mw := (abs_nonneg _).trans (hMw a (left_mem_Icc.mpr hab.le))
    have hMf0 : 0 ≤ Mf := (abs_nonneg _).trans (hMf a (left_mem_Icc.mpr hab.le))
    simp only [BP]
    calc |(remezPoly (cp n)).eval x| ≤ _ := this
      _ ≤ (Es + 1) * Mw * BQ + Mf * BQ := by
          gcongr
          · calc _ ≤ ratMaxErr a b f w (remezPoly (cp n)) (remezPoly (cq n)) * |w x| *
                (remezPoly (cq n)).eval x := h1
              _ ≤ (Es + 1) * Mw * BQ := by gcongr
      _ = _ := by ring
  have hBP0 : 0 ≤ BP := (abs_nonneg _).trans (hPb 0 a (left_mem_Icc.mpr hab.le))
  have hcpb : ∀ n, ‖cp n‖ ≤ K * BP := fun n =>
    (hK (cp n)).trans (mul_le_mul_of_nonneg_left
      ((pi_norm_le_iff_of_nonneg hBP0).mpr fun i => by
        rw [Real.norm_eq_abs]; exact hPb n _ (htI i)) hK0)
  -- a convergent subsequence
  set r : ℝ := max (K * BP) 1
  have hmem : ∀ n, (cp n, cq n) ∈ closedBall (0 : (Fin (k + 1) → ℝ) × (Fin (ℓ + 1) → ℝ)) r :=
    fun n => by
      rw [mem_closedBall_zero_iff, Prod.norm_def]
      exact max_le ((hcpb n).trans (le_max_left _ _)) ((hcq1 n).le.trans (le_max_right _ _))
  obtain ⟨⟨cps, cqs⟩, -, φ, hφ, hlim⟩ := (isCompact_closedBall _ r).tendsto_subseq hmem
  have hlimp : Tendsto (fun n => cp (φ n)) atTop (𝓝 cps) := (continuous_fst.tendsto _).comp hlim
  have hlimq : Tendsto (fun n => cq (φ n)) atTop (𝓝 cqs) := (continuous_snd.tendsto _).comp hlim
  have hev : ∀ {m : ℕ} {c : ℕ → Fin (m + 1) → ℝ} {c0 : Fin (m + 1) → ℝ},
      Tendsto c atTop (𝓝 c0) → ∀ x : ℝ,
        Tendsto (fun n => (remezPoly (c n)).eval x) atTop (𝓝 ((remezPoly c0).eval x)) := by
    intro m c c0 hc x
    simp only [remezPoly_eval]
    exact tendsto_finsetSum _ fun i _ =>
      ((continuous_apply i).tendsto _ |>.comp hc).const_mul _
  have hEn : Tendsto (fun n => ratMaxErr a b f w (remezPoly (cp (φ n))) (remezPoly (cq (φ n))))
      atTop (𝓝 Es) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun n => hEs _ _ ⟨remezPoly_natDegree _, remezPoly_natDegree _, hcqpos (φ n)⟩)
      (fun n => (hlt (φ n)).le)
    have h0 : Tendsto (fun n : ℕ => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
    simpa using h0.const_add Es
  set Ps := remezPoly cps
  set Qs := remezPoly cqs
  have hQs1 : ‖cqs‖ = 1 := by
    have := (continuous_norm.tendsto _).comp hlimq
    simp only [Function.comp_def, hcq1] at this
    exact tendsto_nhds_unique this tendsto_const_nhds
  have hQs0 : Qs ≠ 0 := fun h0 => by
    have : cqs = 0 := funext fun i => by rw [← remezPoly_coeff cqs i]; simp [Qs] at h0; simp [h0]
    rw [this, norm_zero] at hQs1
    exact zero_ne_one hQs1
  have hQsnn : ∀ x ∈ Icc a b, 0 ≤ Qs.eval x := fun x hx =>
    ge_of_tendsto (hev hlimq x) (Eventually.of_forall fun n => (hcqpos (φ n) x hx).le)
  have hineqs : ∀ x ∈ Icc a b, |Ps.eval x - f x * Qs.eval x| ≤ Es * |w x| * |Qs.eval x| :=
    fun x hx => by
      rw [abs_of_nonneg (hQsnn x hx)]
      have hL : Tendsto (fun n => |(remezPoly (cp (φ n))).eval x - f x *
          (remezPoly (cq (φ n))).eval x|) atTop (𝓝 |Ps.eval x - f x * Qs.eval x|) :=
        ((hev hlimp x).sub ((hev hlimq x).const_mul (f x))).abs
      have hRr : Tendsto (fun n => ratMaxErr a b f w (remezPoly (cp (φ n)))
          (remezPoly (cq (φ n))) * |w x| * (remezPoly (cq (φ n))).eval x) atTop
          (𝓝 (Es * |w x| * Qs.eval x)) := (hEn.mul_const _).mul (hev hlimq x)
      exact le_of_tendsto_of_tendsto hL hRr (Eventually.of_forall fun n => hineq (φ n) x hx)
  -- cancel the common zeros
  obtain ⟨P', Q', hP', hQ', hne, hin⟩ := cancel_zeros hab hf hw Qs.natDegree Ps Qs hQs0 le_rfl
    hineqs
  -- `Q′` has constant sign
  have hsign : ∀ x ∈ Icc a b, 0 < Q'.eval x * Q'.eval a := fun x hx =>
    weight_mul_pos Q'.continuous.continuousOn hne hx (left_mem_Icc.mpr hab.le)
  set σ : ℝ := if 0 < Q'.eval a then 1 else -1
  have hσ : ∀ x ∈ Icc a b, 0 < σ * Q'.eval x := fun x hx => by
    have h1 := hsign x hx
    have ha := hne a (left_mem_Icc.mpr hab.le)
    simp only [σ]
    split_ifs with h
    · rw [one_mul]; exact pos_of_mul_pos_left h1 h.le
    · push Not at h
      have : Q'.eval a < 0 := lt_of_le_of_ne h ha
      nlinarith
  have hσ2 : σ = 1 ∨ σ = -1 := by simp only [σ]; split_ifs <;> simp
  refine ⟨C σ * P', C σ * Q', ⟨?_, ?_, fun x hx => by simpa using hσ x hx⟩, fun P2 Q2 h2 => ?_⟩
  · exact (natDegree_C_mul_le _ _).trans (hP'.trans (remezPoly_natDegree _))
  · exact (natDegree_C_mul_le _ _).trans (hQ'.trans (remezPoly_natDegree _))
  · refine le_trans (ratMaxErr_le hab.le fun x hx => ?_) (hEs P2 Q2 h2)
    refine abs_ratErr_le_of (by simpa using hσ x hx) (hw0 x hx) ?_
    have h := hin x hx
    simp only [eval_mul, eval_C]
    have habs : |σ * Q'.eval x| = |Q'.eval x| := by
      rcases hσ2 with h | h <;> simp [h]
    have e : σ * P'.eval x - f x * (σ * Q'.eval x) = σ * (P'.eval x - f x * Q'.eval x) := by ring
    rw [e, abs_mul, show |σ| = 1 by rcases hσ2 with h | h <;> simp [h], one_mul,
      ← abs_of_pos (hσ x hx), habs]
    exact h

/-- When `0 ∈ [a, b]` the minimax approximation can be normalized as in 3.11.16 (`Q(0) = 1`). -/
theorem dlmf_3_11_iii_exists_normalized (hab : a < b) (h0 : (0 : ℝ) ∈ Icc a b) {f w : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (hw0 : ∀ x ∈ Icc a b, w x ≠ 0) (k ℓ : ℕ) :
    ∃ P Q, IsRatMinimax a b f w k ℓ P Q ∧ Q.eval 0 = 1 := by
  obtain ⟨P, Q, hPQ⟩ := dlmf_3_11_iii_exists hab hf hw hw0 k ℓ
  have hq := hPQ.1.2.2 0 h0
  set c := (Q.eval 0)⁻¹
  have hc : 0 < c := inv_pos.mpr hq
  have hR : ratErr f w (C c * P) (C c * Q) = ratErr f w P Q := by
    funext x; simp only [ratErr, eval_mul, eval_C]; rw [mul_div_mul_left _ _ hc.ne']
  refine ⟨C c * P, C c * Q, ⟨⟨(natDegree_C_mul_le _ _).trans hPQ.1.1,
    (natDegree_C_mul_le _ _).trans hPQ.1.2.1, fun x hx => by
      simp only [eval_mul, eval_C]; exact mul_pos hc (hPQ.1.2.2 x hx)⟩, fun P' Q' h => ?_⟩, ?_⟩
  · simp only [ratMaxErr, hR]; exact hPQ.2 P' Q' h
  · simp only [eval_mul, eval_C, c]; exact inv_mul_cancel₀ hq.ne'

end Azurite.DLMF
