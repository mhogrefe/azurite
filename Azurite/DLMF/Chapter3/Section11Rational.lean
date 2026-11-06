/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section11Minimax
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact

/-!
# DLMF §3.11(iii): Minimax rational approximations

Formalizations of <https://dlmf.nist.gov/3.11.iii>.

* 3.11.16 `ratDLMF` (`R_{k,ℓ} = (p₀ + ⋯ + p_k x^k)/(1 + q₁x + ⋯ + q_ℓ x^ℓ)`); in general a rational
  function is a pair `(P, Q)` with `deg P ≤ k`, `deg Q ≤ ℓ`, `Q > 0` on `[a, b]`
  (`RatAdmissible`).
* 3.11.17 `ratErr` (`ε = (R − f)/w`), `ratMaxErr` (`max |ε|` on `[a, b]`), `IsRatMinimax`.
* 3.11.18, sufficiency of alternation: `dlmf_3_11_iii_sufficient` (if `ε(x_j) = (−1)^j m`,
  `|m| = max |ε|`, at `k + ℓ + 2` points, then `R` is minimax), from the de la Vallée-Poussin
  bound `dlmf_3_11_iii_vallee_poussin` (alternation of size `≥ μ` forces `max |ε′| ≥ μ` for every
  competitor), via `not_alternates` of §3.11(i).
* Errata:
  - `dlmf_3_11_iii_not_exists` (normalization): with the normalization `q₀ = 1` of 3.11.16 a
    minimax approximation need not exist (`f = 1/x` on `[1, 2]`, type `[0, 1]`: every
    approximation is beaten, the error tends to `0`, but `1/x = 1/(0 + x)` is not of the form
    3.11.16). It exists among all `P/Q` with `Q > 0` (`Section11RationalExist.lean`).
  - `dlmf_3_11_iii_degenerate` (alternation count): "at least `k + ℓ + 2` values" fails for
    degenerate approximations (`f = x²` on `[−1, 1]`, type `[1, 1]`: the unique minimax
    approximation is `½`, and `|ε| = max |ε|` at only three points). The correct count is
    `k + ℓ + 2 − d`, `d` the defect (`Section11RationalAchieser.lean`).
-/

open Polynomial Set

namespace Azurite.DLMF

variable {a b : ℝ}

/-! ### Definitions -/

/-- **DLMF 3.11.17**: the weighted error `ε = (P/Q − f)/w`. -/
noncomputable def ratErr (f w : ℝ → ℝ) (P Q : ℝ[X]) (x : ℝ) : ℝ :=
  (P.eval x / Q.eval x - f x) / w x

/-- `max_{a ≤ x ≤ b} |ε(x)|`. -/
noncomputable def ratMaxErr (a b : ℝ) (f w : ℝ → ℝ) (P Q : ℝ[X]) : ℝ :=
  sSup ((fun x => |ratErr f w P Q x|) '' Icc a b)

/-- `P/Q` is of type `[k, ℓ]` with `Q > 0` on `[a, b]`. -/
def RatAdmissible (a b : ℝ) (k ℓ : ℕ) (P Q : ℝ[X]) : Prop :=
  P.natDegree ≤ k ∧ Q.natDegree ≤ ℓ ∧ ∀ x ∈ Icc a b, 0 < Q.eval x

/-- `P/Q` is a minimax (best uniform) rational approximation of type `[k, ℓ]` to `f`, weight `w`,
on `[a, b]`. -/
def IsRatMinimax (a b : ℝ) (f w : ℝ → ℝ) (k ℓ : ℕ) (P Q : ℝ[X]) : Prop :=
  RatAdmissible a b k ℓ P Q ∧
    ∀ P' Q', RatAdmissible a b k ℓ P' Q' → ratMaxErr a b f w P Q ≤ ratMaxErr a b f w P' Q'

/-- **DLMF 3.11.16**: `R_{k,ℓ}(x) = (p₀ + p₁x + ⋯ + p_k x^k)/(1 + q₁x + ⋯ + q_ℓ x^ℓ)`, as the pair
`(P, Q)` with `Q(0) = 1`. -/
noncomputable def ratDLMF {k ℓ : ℕ} (p : Fin (k + 1) → ℝ) (q : Fin ℓ → ℝ) : ℝ[X] × ℝ[X] :=
  (∑ i : Fin (k + 1), C (p i) * X ^ (i : ℕ), 1 + ∑ i : Fin ℓ, C (q i) * X ^ ((i : ℕ) + 1))

theorem dlmf_3_11_16 {k ℓ : ℕ} (p : Fin (k + 1) → ℝ) (q : Fin ℓ → ℝ) (x : ℝ) :
    (ratDLMF p q).1.eval x / (ratDLMF p q).2.eval x =
      (∑ i : Fin (k + 1), p i * x ^ (i : ℕ)) / (1 + ∑ i : Fin ℓ, q i * x ^ ((i : ℕ) + 1)) := by
  simp [ratDLMF, eval_finsetSum]

/-! ### Basic properties -/

section Basic

variable {f w : ℝ → ℝ} {P Q : ℝ[X]}

theorem continuousOn_ratErr (hf : ContinuousOn f (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (hw0 : ∀ x ∈ Icc a b, w x ≠ 0) (hQ : ∀ x ∈ Icc a b, Q.eval x ≠ 0) :
    ContinuousOn (ratErr f w P Q) (Icc a b) :=
  (((P.continuous.continuousOn).div Q.continuous.continuousOn hQ).sub hf).div hw hw0

theorem bddAbove_ratErr (hf : ContinuousOn f (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (hw0 : ∀ x ∈ Icc a b, w x ≠ 0) (hQ : ∀ x ∈ Icc a b, Q.eval x ≠ 0) :
    BddAbove ((fun x => |ratErr f w P Q x|) '' Icc a b) :=
  (isCompact_Icc.image_of_continuousOn
    (continuousOn_ratErr hf hw hw0 hQ).abs).bddAbove

theorem abs_ratErr_le (hf : ContinuousOn f (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (hw0 : ∀ x ∈ Icc a b, w x ≠ 0) (hQ : ∀ x ∈ Icc a b, Q.eval x ≠ 0) {x : ℝ}
    (hx : x ∈ Icc a b) : |ratErr f w P Q x| ≤ ratMaxErr a b f w P Q :=
  le_csSup (bddAbove_ratErr hf hw hw0 hQ) (mem_image_of_mem _ hx)

theorem ratMaxErr_le (hab : a ≤ b) {B : ℝ} (h : ∀ x ∈ Icc a b, |ratErr f w P Q x| ≤ B) :
    ratMaxErr a b f w P Q ≤ B :=
  csSup_le ((nonempty_Icc.mpr hab).image _) (by rintro _ ⟨x, hx, rfl⟩; exact h x hx)

theorem exists_ratMaxErr (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hw : ContinuousOn w (Icc a b)) (hw0 : ∀ x ∈ Icc a b, w x ≠ 0)
    (hQ : ∀ x ∈ Icc a b, Q.eval x ≠ 0) :
    ∃ x ∈ Icc a b, |ratErr f w P Q x| = ratMaxErr a b f w P Q := by
  have hK := (isCompact_Icc (a := a) (b := b)).image_of_continuousOn
    (continuousOn_ratErr (P := P) hf hw hw0 hQ).abs
  obtain ⟨x, hx, hxeq⟩ := hK.sSup_mem ((nonempty_Icc.mpr hab).image _)
  exact ⟨x, hx, hxeq⟩

theorem ratMaxErr_nonneg (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hw : ContinuousOn w (Icc a b)) (hw0 : ∀ x ∈ Icc a b, w x ≠ 0)
    (hQ : ∀ x ∈ Icc a b, Q.eval x ≠ 0) : 0 ≤ ratMaxErr a b f w P Q :=
  (abs_nonneg _).trans (abs_ratErr_le hf hw hw0 hQ (left_mem_Icc.mpr hab))

end Basic

/-- A continuous nonvanishing weight has constant sign on `[a, b]`. -/
theorem weight_mul_pos {w : ℝ → ℝ} (hw : ContinuousOn w (Icc a b))
    (hw0 : ∀ x ∈ Icc a b, w x ≠ 0) {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    0 < w x * w y := by
  rcases lt_or_gt_of_ne (mul_ne_zero (hw0 x hx) (hw0 y hy)) with h | h
  · exfalso
    have hsub : uIcc x y ⊆ Icc a b := uIcc_subset_Icc hx hy
    have h0 : (0 : ℝ) ∈ uIcc (w x) (w y) := by
      rcases lt_or_gt_of_ne (hw0 x hx) with h1 | h1
      · have : 0 < w y := by nlinarith
        exact mem_uIcc.mpr (Or.inl ⟨h1.le, this.le⟩)
      · have : w y < 0 := by nlinarith
        exact mem_uIcc.mpr (Or.inr ⟨this.le, h1.le⟩)
    obtain ⟨z, hz, hz0⟩ := intermediate_value_uIcc (hw.mono hsub) h0
    exact hw0 z (hsub hz) hz0
  · exact h

/-! ### Alternation: de la Vallée-Poussin and sufficiency -/

theorem natDegree_cross_le {k ℓ : ℕ} {P Q P' Q' : ℝ[X]} (hP : P.natDegree ≤ k)
    (hQ : Q.natDegree ≤ ℓ) (hP' : P'.natDegree ≤ k) (hQ' : Q'.natDegree ≤ ℓ) :
    (P' * Q - P * Q').natDegree ≤ k + ℓ := by
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · exact natDegree_mul_le.trans (add_le_add hP' hQ)
  · exact natDegree_mul_le.trans (add_le_add hP hQ')

/-- `(P′/Q′ − P/Q) Q′Q = P′Q − PQ′`, written through the errors. -/
theorem cross_eval_eq {f w : ℝ → ℝ} {P Q P' Q' : ℝ[X]} {x : ℝ} (hQ : Q.eval x ≠ 0)
    (hQ' : Q'.eval x ≠ 0) (hw : w x ≠ 0) :
    (P' * Q - P * Q').eval x =
      (ratErr f w P' Q' x - ratErr f w P Q x) * w x * Q'.eval x * Q.eval x := by
  simp only [ratErr, eval_sub, eval_mul]
  field_simp
  ring

/-- **de la Vallée-Poussin** for rational approximation: if the error of an admissible `P/Q`
alternates in sign at `k + ℓ + 2` points with magnitude `≥ μ > 0`, then every admissible `P′/Q′`
has `max |ε′| ≥ μ`. -/
theorem dlmf_3_11_iii_vallee_poussin {f w : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    (hw : ContinuousOn w (Icc a b)) (hw0 : ∀ x ∈ Icc a b, w x ≠ 0) {k ℓ : ℕ} {P Q : ℝ[X]}
    (hPQ : RatAdmissible a b k ℓ P Q) {x : Fin (k + ℓ + 2) → ℝ} (hx : StrictMono x)
    (hxI : ∀ j, x j ∈ Icc a b) {s μ : ℝ} (hs : s = 1 ∨ s = -1)
    (hμ : ∀ j : Fin (k + ℓ + 2), μ ≤ s * (-1) ^ (j : ℕ) * ratErr f w P Q (x j))
    {P' Q' : ℝ[X]}
    (hPQ' : RatAdmissible a b k ℓ P' Q') : μ ≤ ratMaxErr a b f w P' Q' := by
  by_contra hlt
  push Not at hlt
  have hQ' : ∀ y ∈ Icc a b, Q'.eval y ≠ 0 := fun y hy => (hPQ'.2.2 y hy).ne'
  have hlt' : ∀ j, |ratErr f w P' Q' (x j)| < μ := fun j =>
    lt_of_le_of_lt (abs_ratErr_le hf hw hw0 hQ' (hxI j)) hlt
  refine not_alternates (natDegree_cross_le hPQ.1 hPQ.2.1 hPQ'.1 hPQ'.2.1) hx fun j => ?_
  have hj1 := hxI j.castSucc
  have hj2 := hxI j.succ
  rw [cross_eval_eq (f := f) (w := w) (hPQ.2.2 _ hj1).ne' (hQ' _ hj1) (hw0 _ hj1),
    cross_eval_eq (f := f) (w := w) (hPQ.2.2 _ hj2).ne' (hQ' _ hj2) (hw0 _ hj2)]
  -- the sign of the error difference alternates
  set t : ℝ := s * (-1) ^ (j : ℕ) with ht
  have ht2 : t * t = 1 := by
    rcases hs with rfl | rfl <;> simp [ht, ← pow_add, ← two_mul, pow_mul]
  set e1 := ratErr f w P' Q' (x j.castSucc)
  set e2 := ratErr f w P' Q' (x j.succ)
  set c1 := ratErr f w P Q (x j.castSucc)
  set c2 := ratErr f w P Q (x j.succ)
  have h1 : μ ≤ t * c1 := by have := hμ j.castSucc; simpa [Fin.val_castSucc, ← ht] using this
  have h2' : μ ≤ -(t * c2) := by
    have := hμ j.succ
    have e : s * (-1) ^ ((j.succ : Fin (k + ℓ + 2)) : ℕ) * c2 = -(t * c2) := by
      rw [Fin.val_succ, pow_succ, ht]; ring
    linarith
  have key : (e1 - c1) * (e2 - c2) < 0 := by
    -- `t(e₁ − c₁) < 0 < t(e₂ − c₂)`
    have hte1 : |t * e1| < μ := by
      rw [abs_mul, show |t| = 1 by
        rcases hs with rfl | rfl <;> simp [ht, abs_pow]]; simpa using hlt' j.castSucc
    have hte2 : |t * e2| < μ := by
      rw [abs_mul, show |t| = 1 by
        rcases hs with rfl | rfl <;> simp [ht, abs_pow]]; simpa using hlt' j.succ
    have k1 : t * (e1 - c1) < 0 := by have := (abs_lt.mp hte1).2; nlinarith
    have k2 : 0 < t * (e2 - c2) := by have := (abs_lt.mp hte2).1; nlinarith
    have : (t * (e1 - c1)) * (t * (e2 - c2)) < 0 := mul_neg_of_neg_of_pos k1 k2
    have e : (t * (e1 - c1)) * (t * (e2 - c2)) = (t * t) * ((e1 - c1) * (e2 - c2)) := by ring
    rw [e, ht2, one_mul] at this
    exact this
  have hww := weight_mul_pos hw hw0 hj1 hj2
  have hq1 := hPQ'.2.2 _ hj1
  have hq2 := hPQ'.2.2 _ hj2
  have hq3 := hPQ.2.2 _ hj1
  have hq4 := hPQ.2.2 _ hj2
  have hpos : 0 < (w (x j.castSucc) * w (x j.succ)) *
      (Q'.eval (x j.castSucc) * Q.eval (x j.castSucc)) *
        (Q'.eval (x j.succ) * Q.eval (x j.succ)) := by positivity
  have e : (e1 - c1) * w (x j.castSucc) * Q'.eval (x j.castSucc) * Q.eval (x j.castSucc) *
      ((e2 - c2) * w (x j.succ) * Q'.eval (x j.succ) * Q.eval (x j.succ)) =
      ((e1 - c1) * (e2 - c2)) * ((w (x j.castSucc) * w (x j.succ)) *
        (Q'.eval (x j.castSucc) * Q.eval (x j.castSucc)) *
          (Q'.eval (x j.succ) * Q.eval (x j.succ))) := by ring
  rw [e]
  exact mul_neg_of_neg_of_pos key hpos

/-- **DLMF §3.11(iii)**, sufficiency (the rational analogue of §3.11(i)): if
`m_j = (−1)^j ε(x_j)` (3.11.18) is constant `= m` at `k + ℓ + 2` points with `|m| = max |ε|`,
then `P/Q` is a minimax approximation. -/
theorem dlmf_3_11_iii_sufficient {f w : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    (hw : ContinuousOn w (Icc a b)) (hw0 : ∀ x ∈ Icc a b, w x ≠ 0) {k ℓ : ℕ} {P Q : ℝ[X]}
    (hPQ : RatAdmissible a b k ℓ P Q) {x : Fin (k + ℓ + 2) → ℝ} (hx : StrictMono x)
    (hxI : ∀ j, x j ∈ Icc a b) {m : ℝ} (hm : |m| = ratMaxErr a b f w P Q)
    (h18 : ∀ j : Fin (k + ℓ + 2), (-1) ^ (j : ℕ) * ratErr f w P Q (x j) = m) :
    IsRatMinimax a b f w k ℓ P Q := by
  refine ⟨hPQ, fun P' Q' hPQ' => ?_⟩
  rw [← hm]
  have hs : (if 0 ≤ m then (1 : ℝ) else -1) = 1 ∨ (if 0 ≤ m then (1 : ℝ) else -1) = -1 := by
    split_ifs <;> simp
  refine dlmf_3_11_iii_vallee_poussin hf hw hw0 hPQ hx hxI hs (fun j => ?_) hPQ'
  rw [mul_assoc, h18 j]
  split_ifs with h
  · rw [abs_of_nonneg h, one_mul]
  · rw [abs_of_neg (not_le.mp h)]; ring_nf; rfl

/-! ### Erratum: existence fails with the normalization `q₀ = 1` -/

/-- DLMF's class 3.11.16 of type `[0, 1]`: `p₀/(1 + q₁x)`, `1 + q₁x > 0` on `[a, b]`. -/
def DLMFAdm01 (a b q1 : ℝ) : Prop := ∀ x ∈ Icc a b, 0 < 1 + q1 * x

theorem ratErr_inv (p0 q1 x : ℝ) :
    ratErr (fun x => 1 / x) (fun _ => 1) (C p0) (1 + C q1 * X) x = p0 / (1 + q1 * x) - 1 / x := by
  simp [ratErr]

/-- **Erratum** (DLMF §3.11(iii), "There exists a unique solution"): with the normalization of
3.11.16, `f(x) = 1/x` on `[1, 2]` (`w = 1`) has no minimax approximation of type `[0, 1]`:
every `p₀/(1 + q₁x)` is strictly beaten by another one. -/
theorem dlmf_3_11_iii_not_exists (p0 q1 : ℝ) (h : DLMFAdm01 1 2 q1) :
    ∃ p0' q1', DLMFAdm01 1 2 q1' ∧
      ratMaxErr 1 2 (fun x => 1 / x) (fun _ => 1) (C p0') (1 + C q1' * X) <
        ratMaxErr 1 2 (fun x => 1 / x) (fun _ => 1) (C p0) (1 + C q1 * X) := by
  have hf : ContinuousOn (fun x : ℝ => 1 / x) (Icc 1 2) :=
    continuousOn_const.div continuousOn_id fun x hx => by linarith [hx.1]
  have hw : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Icc 1 2) := continuousOn_const
  have hw0 : ∀ x ∈ Icc (1 : ℝ) 2, (fun _ : ℝ => (1 : ℝ)) x ≠ 0 := fun _ _ => one_ne_zero
  have hQ : ∀ x ∈ Icc (1 : ℝ) 2, (1 + C q1 * X).eval x ≠ 0 := fun x hx => by
    simpa using (h x hx).ne'
  -- the error of `p₀/(1 + q₁x)` is positive
  set E := ratMaxErr 1 2 (fun x => 1 / x) (fun _ => 1) (C p0) (1 + C q1 * X)
  have h1 := abs_ratErr_le (P := C p0) hf hw hw0 hQ (show (1 : ℝ) ∈ Icc 1 2 by norm_num)
  have h2 := abs_ratErr_le (P := C p0) hf hw hw0 hQ (show (2 : ℝ) ∈ Icc 1 2 by norm_num)
  rw [ratErr_inv] at h1 h2
  have hE : 0 < E := by
    by_contra hE
    push Not at hE
    have e1 : p0 / (1 + q1 * 1) - 1 / 1 = 0 := abs_nonpos_iff.mp (h1.trans hE)
    have e2 : p0 / (1 + q1 * 2) - 1 / 2 = 0 := abs_nonpos_iff.mp (h2.trans hE)
    have d1 := h 1 (by norm_num)
    have d2 := h 2 (by norm_num)
    rw [sub_eq_zero, div_eq_iff d1.ne'] at e1
    rw [sub_eq_zero, div_eq_iff d2.ne'] at e2
    linarith
  -- `t/(1 + tx)` has error `1/(x(1 + tx)) ≤ 1/(1 + t)`
  set t : ℝ := 1 / E
  have ht : 0 < t := by positivity
  refine ⟨t, t, fun x hx => by nlinarith [hx.1], ?_⟩
  have hQt : ∀ x ∈ Icc (1 : ℝ) 2, (1 + C t * X).eval x ≠ 0 := fun x hx => by
    simp; nlinarith [hx.1]
  refine lt_of_le_of_lt (ratMaxErr_le (by norm_num) (B := 1 / (1 + t)) fun x hx => ?_) ?_
  · rw [ratErr_inv]
    have hx1 : 1 ≤ x := hx.1
    have hd : 0 < 1 + t * x := by nlinarith
    have e : t / (1 + t * x) - 1 / x = -(1 / (x * (1 + t * x))) := by
      field_simp; ring
    rw [e, abs_neg, abs_of_pos (by positivity)]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  · rw [div_lt_iff₀ (by positivity)]
    have : E * t = 1 := by simp only [t]; field_simp
    nlinarith

/-- In the class `Q > 0` the minimax approximation of type `[0, 1]` to `1/x` on `[1, 2]` exists:
`1/x` itself (`Q = x`, `Q(0) = 0`), with error `0`. -/
theorem dlmf_3_11_iii_not_exists_corrected :
    IsRatMinimax 1 2 (fun x => 1 / x) (fun _ => 1) 0 1 1 X ∧
      ratMaxErr 1 2 (fun x => 1 / x) (fun _ => 1) 1 X = 0 := by
  have h0 : ratMaxErr 1 2 (fun x => 1 / x) (fun _ => 1) 1 X = 0 := by
    apply le_antisymm (ratMaxErr_le (by norm_num) fun x _ => by simp [ratErr])
    exact (abs_nonneg _).trans (le_csSup ⟨0, by rintro _ ⟨y, -, rfl⟩; simp [ratErr]⟩
      (mem_image_of_mem _ (show (1 : ℝ) ∈ Icc 1 2 by norm_num)))
  refine ⟨⟨⟨by simp, by simp, fun x hx => by simp; linarith [hx.1]⟩, fun P' Q' hPQ' => ?_⟩, h0⟩
  rw [h0]
  exact ratMaxErr_nonneg (by norm_num)
    (continuousOn_const.div continuousOn_id fun x hx => by linarith [hx.1]) continuousOn_const
    (fun _ _ => one_ne_zero) fun x hx => (hPQ'.2.2 x hx).ne'

/-! ### Erratum: fewer than `k + ℓ + 2` alternation points -/

/-- A rational function of type `[1, 1]`: `R(x) − R(y) = c(x − y)/(Q(x)Q(y))`. -/
theorem rat11_sub {P Q : ℝ[X]} (hP : P.natDegree ≤ 1) (hQ : Q.natDegree ≤ 1) (x y : ℝ)
    (hx : Q.eval x ≠ 0) (hy : Q.eval y ≠ 0) :
    P.eval x / Q.eval x - P.eval y / Q.eval y =
      (P.coeff 1 * Q.coeff 0 - P.coeff 0 * Q.coeff 1) * (x - y) / (Q.eval x * Q.eval y) := by
  have eP : ∀ z, P.eval z = P.coeff 1 * z + P.coeff 0 := fun z => by
    conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hP]
    simp
  have eQ : ∀ z, Q.eval z = Q.coeff 1 * z + Q.coeff 0 := fun z => by
    conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hQ]
    simp
  rw [div_sub_div _ _ hx hy]
  congr 1
  rw [eP, eP, eQ, eQ]
  ring

theorem ratErr_sq (P Q : ℝ[X]) (x : ℝ) :
    ratErr (fun x => x ^ 2) (fun _ => 1) P Q x = P.eval x / Q.eval x - x ^ 2 := by
  simp [ratErr]

/-- An admissible `R` of type `[1, 1]` with `max |R − x²| ≤ ½` on `[−1, 1]` is `½`. -/
theorem rat11_eq_half {P Q : ℝ[X]} (hPQ : RatAdmissible (-1) 1 1 1 P Q)
    (h : ∀ x ∈ Icc (-1 : ℝ) 1, |P.eval x / Q.eval x - x ^ 2| ≤ 1 / 2) :
    ∀ x ∈ Icc (-1 : ℝ) 1, P.eval x / Q.eval x = 1 / 2 := by
  have m1 : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 := by norm_num
  have z0 : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := by norm_num
  have p1 : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := by norm_num
  have hm := abs_le.mp (h _ m1)
  have h0 := abs_le.mp (h _ z0)
  have hp := abs_le.mp (h _ p1)
  set c := P.coeff 1 * Q.coeff 0 - P.coeff 0 * Q.coeff 1
  have hQ : ∀ y ∈ Icc (-1 : ℝ) 1, 0 < Q.eval y := hPQ.2.2
  have d1 := rat11_sub hPQ.1 hPQ.2.1 0 (-1) (hQ 0 z0).ne' (hQ _ m1).ne'
  have d2 := rat11_sub hPQ.1 hPQ.2.1 1 0 (hQ 1 p1).ne' (hQ 0 z0).ne'
  have q1 := hQ 0 z0
  have q2 := hQ _ m1
  have q3 := hQ 1 p1
  -- `c = 0`: otherwise `R` is strictly monotone, but `R(0) ≤ ½ ≤ R(±1)`
  have hc : c = 0 := by
    by_contra hc
    rcases lt_or_gt_of_ne hc with hc | hc
    · have : P.eval 1 / Q.eval 1 - P.eval 0 / Q.eval 0 < 0 := by
        rw [d2]; apply div_neg_of_neg_of_pos (by nlinarith) (by positivity)
      norm_num at hp h0; linarith
    · have : 0 < P.eval 0 / Q.eval 0 - P.eval (-1) / Q.eval (-1) := by
        rw [d1]; apply div_pos (by nlinarith) (by positivity)
      norm_num at hm h0; linarith
  intro x hx
  have d := rat11_sub hPQ.1 hPQ.2.1 x 0 (hQ x hx).ne' q1.ne'
  have d' := rat11_sub hPQ.1 hPQ.2.1 1 0 q3.ne' q1.ne'
  rw [show P.coeff 1 * Q.coeff 0 - P.coeff 0 * Q.coeff 1 = c from rfl, hc] at d d'
  simp only [zero_mul, zero_div, sub_eq_zero] at d d'
  norm_num at hp h0
  rw [d]
  linarith

/-- **Erratum** (DLMF §3.11(iii), "there are at least `k + ℓ + 2` values `x_j`"): for `f(x) = x²`
on `[−1, 1]`, `w = 1`, type `[1, 1]`, the constant `½` is the minimax approximation, every minimax
approximation equals `½` on `[−1, 1]`, and no four points of `[−1, 1]` have
`|ε(x_j)| = max |ε|` — fewer than `k + ℓ + 2 = 4`. -/
theorem dlmf_3_11_iii_degenerate :
    IsRatMinimax (-1) 1 (fun x => x ^ 2) (fun _ => 1) 1 1 (C (1 / 2)) 1 ∧
      ∀ P Q, IsRatMinimax (-1) 1 (fun x => x ^ 2) (fun _ => 1) 1 1 P Q →
        ratMaxErr (-1) 1 (fun x => x ^ 2) (fun _ => 1) P Q = 1 / 2 ∧
        (∀ x ∈ Icc (-1 : ℝ) 1, P.eval x / Q.eval x = 1 / 2) ∧
        ¬ ∃ x : Fin 4 → ℝ, StrictMono x ∧ ∀ j, x j ∈ Icc (-1 : ℝ) 1 ∧
          |ratErr (fun x => x ^ 2) (fun _ => 1) P Q (x j)| =
            ratMaxErr (-1) 1 (fun x => x ^ 2) (fun _ => 1) P Q := by
  have hf : ContinuousOn (fun x : ℝ => x ^ 2) (Icc (-1) 1) := by fun_prop
  have hw : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Icc (-1) 1) := continuousOn_const
  have hw0 : ∀ x ∈ Icc (-1 : ℝ) 1, (fun _ : ℝ => (1 : ℝ)) x ≠ 0 := fun _ _ => one_ne_zero
  have hhalf_adm : RatAdmissible (-1) 1 1 1 (C (1 / 2)) 1 :=
    ⟨by simp, by simp, fun _ _ => by simp⟩
  -- the error of `½` is `½`
  have hE : ratMaxErr (-1) 1 (fun x => x ^ 2) (fun _ => 1) (C (1 / 2)) 1 = 1 / 2 := by
    apply le_antisymm
    · refine ratMaxErr_le (by norm_num) fun x hx => ?_
      rw [ratErr_sq]; simp only [eval_C, eval_one, div_one]
      have : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2]
      rw [abs_le]; constructor <;> nlinarith
    · have := abs_ratErr_le (P := C (1 / 2)) (Q := 1) hf hw hw0 (fun _ _ => by simp)
        (show (0 : ℝ) ∈ Icc (-1 : ℝ) 1 by norm_num)
      rw [ratErr_sq] at this; norm_num at this; linarith
  -- any admissible `R` has error `≥ ½`, with equality only for `R = ½`
  have hlow : ∀ P Q, RatAdmissible (-1) 1 1 1 P Q →
      ratMaxErr (-1) 1 (fun x => x ^ 2) (fun _ => 1) P Q ≤ 1 / 2 →
      ∀ x ∈ Icc (-1 : ℝ) 1, P.eval x / Q.eval x = 1 / 2 := fun P Q hPQ hle =>
    rat11_eq_half hPQ fun x hx => by
      have := abs_ratErr_le (P := P) hf hw hw0 (fun y hy => (hPQ.2.2 y hy).ne') hx
      rw [ratErr_sq] at this; linarith
  have hge : ∀ P Q, RatAdmissible (-1) 1 1 1 P Q →
      1 / 2 ≤ ratMaxErr (-1) 1 (fun x => x ^ 2) (fun _ => 1) P Q := fun P Q hPQ => by
    by_contra hlt
    push Not at hlt
    have h0 := hlow P Q hPQ hlt.le 0 (by norm_num)
    have := abs_ratErr_le (P := P) hf hw hw0 (fun y hy => (hPQ.2.2 y hy).ne')
      (show (0 : ℝ) ∈ Icc (-1 : ℝ) 1 by norm_num)
    rw [ratErr_sq, h0] at this
    norm_num at this
    linarith
  refine ⟨⟨hhalf_adm, fun P' Q' hPQ' => by rw [hE]; exact hge P' Q' hPQ'⟩,
    fun P Q hmin => ?_⟩
  have hle : ratMaxErr (-1) 1 (fun x => x ^ 2) (fun _ => 1) P Q ≤ 1 / 2 := by
    rw [← hE]; exact hmin.2 _ _ hhalf_adm
  have heq : ratMaxErr (-1) 1 (fun x => x ^ 2) (fun _ => 1) P Q = 1 / 2 :=
    le_antisymm hle (hge P Q hmin.1)
  have hR := hlow P Q hmin.1 hle
  refine ⟨heq, hR, ?_⟩
  rintro ⟨x, hx, hxj⟩
  -- `|½ − x²| = ½` forces `x ∈ {−1, 0, 1}`
  have hval : ∀ j, x j = -1 ∨ x j = 0 ∨ x j = 1 := fun j => by
    obtain ⟨hI, he⟩ := hxj j
    rw [ratErr_sq, hR _ hI, heq] at he
    have h1 : x j ^ 2 ≤ 1 := by nlinarith [hI.1, hI.2]
    rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1 / 2) |>.mp he with h | h
    · have : x j ^ 2 = 0 := by linarith
      right; left; exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    · have : (x j - 1) * (x j + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h' | h'
      · right; right; linarith
      · left; linarith
  have h01 := hx (show (0 : Fin 4) < 1 by decide)
  have h12 := hx (show (1 : Fin 4) < 2 by decide)
  have h23 := hx (show (2 : Fin 4) < 3 by decide)
  rcases hval 0 with h0 | h0 | h0 <;> rcases hval 1 with h1 | h1 | h1 <;>
    rcases hval 2 with h2 | h2 | h2 <;> rcases hval 3 with h3 | h3 | h3 <;>
    · rw [h0, h1] at h01; rw [h1, h2] at h12; rw [h2, h3] at h23; linarith

end Azurite.DLMF
