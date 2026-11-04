/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section5ComplexGaussExample
import Azurite.DLMF.Chapter3.Section5ComplexGaussTable

/-!
# DLMF §3.5(viii), Example: Table 3.5.19

All entries of Table 3.5.19 are certified by exact rational arithmetic in the kernel.

* `J₀(t)` (`dlmf_table_3_5_19_J0`): 40 terms of the series (`j0Rec`, `j0Rec_spec`) and the
  geometric tail bound `abs_tsum_sub_sum_le`; all six printed values are correctly rounded.
* `g(t)` = the 5-point formula 3.5.41 with the exact nodes and weights of Table 3.5.18
  (`dlmf_table_3_5_19_g`): per node, the certified node disk and weight (`cgTable_nodes`), a
  certified square root (`norm_cpow_half_sub_le`, `re_cpow_half_nonneg`) and the quotient bound
  give `lapFt_sound`; summed in `lapApprox_near`. `g₅(0) = 1` exactly.
* **Errata** (`dlmf_table_3_5_19_erratum`): the printed `g(t)` at `t = 1, 2, 5, 10` are not the
  correctly rounded values of 3.5.41 (they are off by 2–6 units in the tenth decimal; inputs
  rounded to the 10 digits of Table 3.5.18 do not determine `g₅(t)` to 10D).
* "Agreement is very good for small values of `t`, but not for larger values"
  (`dlmf_table_3_5_19_agreement`).
-/

open Polynomial Finset Filter Topology

namespace Azurite.DLMF

/-! ### Square roots -/

theorem re_cpow_half_nonneg (b : ℂ) : 0 ≤ (b ^ (1 / 2 : ℂ)).re := by
  by_cases hb : b = 0
  · rw [hb, Complex.zero_cpow (by norm_num)]; simp
  rw [Complex.cpow_def_of_ne_zero hb, Complex.exp_re]
  refine mul_nonneg (Real.exp_pos _).le (Real.cos_nonneg_of_mem_Icc ⟨?_, ?_⟩)
  · have := Complex.neg_pi_lt_arg b
    simp only [Complex.mul_im, Complex.log_re, Complex.log_im]
    norm_num; linarith
  · have := Complex.arg_le_pi b
    simp only [Complex.mul_im, Complex.log_re, Complex.log_im]
    norm_num; linarith

/-- `|√b − s| ≤ |b − s²|/ℜs` for `ℜs > 0` (principal square root). -/
theorem norm_cpow_half_sub_le (b : ℂ) {s : ℂ} (hs : 0 < s.re) :
    ‖b ^ (1 / 2 : ℂ) - s‖ ≤ ‖b - s ^ 2‖ / s.re := by
  set S := b ^ (1 / 2 : ℂ)
  have hS2 : S ^ 2 = b := by
    have := Complex.cpow_nat_inv_pow b (n := 2) two_ne_zero
    simp only [S, one_div]; norm_num at this ⊢; exact this
  have hsum : s.re ≤ ‖S + s‖ := by
    have h1 := Complex.re_le_norm (S + s)
    have h2 := re_cpow_half_nonneg b
    simp only [Complex.add_re] at h1
    linarith
  have hfac : b - s ^ 2 = (S - s) * (S + s) := by rw [← hS2]; ring
  rw [le_div_iff₀ hs, hfac, norm_mul]
  exact mul_le_mul_of_nonneg_left hsum (norm_nonneg _)

/-! ### The terms `wₖ ζₖ/√(ζₖ² + t²)` -/

/-- The certified approximation `F̃` of `w ζ/√(ζ² + t²)` at a row and its error bound. -/
def lapFt (ρ t : ℚ) (r : CGRow) (s : ℚ × ℚ) : (ℚ × ℚ) × ℚ :=
  let z : ℚ × ℚ := (r.x, r.y)
  let R := |r.x| + |r.y| + ρ
  let W := gDiv (gEval lAz z) (gEval lBz z)
  let bt := ((gMul z z).1 + t ^ 2, (gMul z z).2)
  let N1 := |bt.1 - (gMul s s).1| + |bt.2 - (gMul s s).2|
  let es := (ρ * (2 * R) + N1) / s.1
  let At := gMul W z
  let eN := cgDelta ρ z * R + (|W.1| + |W.2|) * ρ
  let a := |At.1| + |At.2|
  let bb := max |s.1| |s.2|
  (gDiv At s, eN / (bb - es) + a * es / ((bb - es) * bb))

/-- The side conditions of `lapFt`. -/
def lapFtOK (ρ t : ℚ) (r : CGRow) (s : ℚ × ℚ) : Prop :=
  0 < s.1 ∧ 0 < max |s.1| |s.2| - (ρ * (2 * (|r.x| + |r.y| + ρ)) +
    (|(gMul (r.x, r.y) (r.x, r.y)).1 + t ^ 2 - (gMul s s).1| +
      |(gMul (r.x, r.y) (r.x, r.y)).2 - (gMul s s).2|)) / s.1

instance (ρ t : ℚ) (r : CGRow) (s : ℚ × ℚ) : Decidable (lapFtOK ρ t r s) := by
  unfold lapFtOK; infer_instance

theorem lapFt_sound {ρ t : ℚ} (hρ : 0 ≤ ρ) {r : CGRow} {s : ℚ × ℚ} (h : lapFtOK ρ t r s)
    {ζ w : ℂ} (hζ : ‖ζ - gToC (r.x, r.y)‖ ≤ ρ)
    (hw : ‖w - gToC (gDiv (gEval lAz (r.x, r.y)) (gEval lBz (r.x, r.y)))‖ ≤
      (cgDelta ρ (r.x, r.y) : ℝ)) :
    ‖w * (ζ / (ζ ^ 2 + (t : ℂ) ^ 2) ^ (1 / 2 : ℂ)) - gToC (lapFt ρ t r s).1‖ ≤
      ((lapFt ρ t r s).2 : ℝ) := by
  obtain ⟨hs1, hbp⟩ := h
  set z : ℚ × ℚ := (r.x, r.y)
  set R : ℚ := |r.x| + |r.y| + ρ
  set W := gDiv (gEval lAz z) (gEval lBz z)
  set At := gMul W z
  set N1 : ℚ := |(gMul z z).1 + t ^ 2 - (gMul s s).1| + |(gMul z z).2 - (gMul s s).2|
  set es : ℚ := (ρ * (2 * R) + N1) / s.1
  set eN : ℚ := cgDelta ρ z * R + (|W.1| + |W.2|) * ρ
  have hz0 : ‖gToC z‖ ≤ (R : ℝ) := by
    have := norm_toC_le z
    simp only [R, z] at this ⊢; push_cast at this ⊢; linarith [(Rat.cast_nonneg.mpr hρ :
      (0 : ℝ) ≤ ρ)]
  have hζR : ‖ζ‖ ≤ (R : ℝ) := by
    have := norm_toC_le z
    have h3 : ‖ζ‖ ≤ ‖gToC z‖ + ‖ζ - gToC z‖ := by
      have := norm_add_le (gToC z) (ζ - gToC z); simpa using this
    simp only [R, z] at this ⊢; push_cast at this ⊢; linarith
  -- the numerator
  have hN : ‖w * ζ - gToC At‖ ≤ (eN : ℝ) := by
    rw [show gToC At = gToC W * gToC z from gToC_mul W z]
    calc ‖w * ζ - gToC W * gToC z‖ = ‖(w - gToC W) * ζ + gToC W * (ζ - gToC z)‖ := by
          congr 1; ring
      _ ≤ ‖w - gToC W‖ * ‖ζ‖ + ‖gToC W‖ * ‖ζ - gToC z‖ := by
          rw [← norm_mul, ← norm_mul]; exact norm_add_le _ _
      _ ≤ (cgDelta ρ z : ℝ) * R + ((|W.1| + |W.2| : ℚ) : ℝ) * ρ := by
          gcongr
          · exact (norm_nonneg _).trans hw
          · exact norm_toC_le W
      _ = (eN : ℝ) := by simp only [eN]; push_cast; ring
  -- the square root
  have hsq : ‖(ζ ^ 2 + (t : ℂ) ^ 2) ^ (1 / 2 : ℂ) - gToC s‖ ≤ (es : ℝ) := by
    have hre : (gToC s).re = (s.1 : ℝ) := rfl
    have hs1' : (0 : ℝ) < s.1 := by exact_mod_cast hs1
    refine (norm_cpow_half_sub_le _ (by rw [hre]; exact hs1')).trans ?_
    rw [hre, div_le_iff₀ hs1']
    have hb : ‖(ζ ^ 2 + (t : ℂ) ^ 2) - (gToC z ^ 2 + (t : ℂ) ^ 2)‖ ≤ (ρ : ℝ) * (2 * R) := by
      rw [show (ζ ^ 2 + (t : ℂ) ^ 2) - (gToC z ^ 2 + (t : ℂ) ^ 2) = (ζ - gToC z) * (ζ + gToC z)
        by ring, norm_mul]
      gcongr
      exact (norm_add_le _ _).trans (by linarith)
    have hN1 : ‖(gToC z ^ 2 + (t : ℂ) ^ 2) - gToC s ^ 2‖ ≤ (N1 : ℝ) := by
      have e : (gToC z ^ 2 + (t : ℂ) ^ 2) - gToC s ^ 2 =
          gToC ((gMul z z).1 + t ^ 2 - (gMul s s).1, (gMul z z).2 - (gMul s s).2) := by
        rw [sq (gToC z), sq (gToC s), ← gToC_mul, ← gToC_mul]
        apply Complex.ext <;> simp [gToC, sq]
      rw [e]; exact norm_toC_le _
    calc ‖ζ ^ 2 + (t : ℂ) ^ 2 - gToC s ^ 2‖
        ≤ ‖(ζ ^ 2 + (t : ℂ) ^ 2) - (gToC z ^ 2 + (t : ℂ) ^ 2)‖ +
          ‖(gToC z ^ 2 + (t : ℂ) ^ 2) - gToC s ^ 2‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ (ρ : ℝ) * (2 * R) + N1 := add_le_add hb hN1
      _ = (es : ℝ) * (s.1 : ℝ) := by
          simp only [es]; push_cast; field_simp
  -- the quotient
  have hbp' : (0 : ℝ) < ((max |s.1| |s.2| : ℚ) : ℝ) - (es : ℝ) * 1 := by
    rw [mul_one]; exact_mod_cast hbp
  have h := norm_div_sub_div_le (A₁ := w * ζ) (A₀ := gToC At)
    (B₁ := (ζ ^ 2 + (t : ℂ) ^ 2) ^ (1 / 2 : ℂ)) (B₀ := gToC s) (LA := eN) (LB := es) (ρ := 1)
    (a := ((|At.1| + |At.2| : ℚ) : ℝ)) (b := ((max |s.1| |s.2| : ℚ) : ℝ))
    (by rw [mul_one]; exact hN) (by rw [mul_one]; exact hsq) (norm_toC_le _)
    (max_le_norm_toC _) hbp'
  rw [mul_div_assoc', show (lapFt ρ t r s).1 = gDiv At s from rfl, gToC_div]
  refine h.trans_eq ?_
  simp only [lapFt, z, R, W, At, N1, es, eN]
  push_cast
  ring

/-! ### The 5-point values `g₅(t)` -/

/-- The radius of the node disks of Table 3.5.18. -/
def lapRho : ℚ := 1 / 10 ^ 30

/-- `∑ₖ F̃ₖ` (real and imaginary parts) and `∑ₖ` errors over the rows of Table 3.5.18. -/
def lapTot (t : ℚ) (sq : List (ℚ × ℚ)) : (ℚ × ℚ) × ℚ :=
  ((∑ i : Fin cgRows_3_5_18.length, (lapFt lapRho t cgRows_3_5_18[i] (sq.getD i (0, 0))).1.1,
    ∑ i : Fin cgRows_3_5_18.length, (lapFt lapRho t cgRows_3_5_18[i] (sq.getD i (0, 0))).1.2),
  ∑ i : Fin cgRows_3_5_18.length, (lapFt lapRho t cgRows_3_5_18[i] (sq.getD i (0, 0))).2)

/-- The side conditions over all rows. -/
def lapOK (t : ℚ) (sq : List (ℚ × ℚ)) : Bool :=
  decide (∀ i : Fin cgRows_3_5_18.length, lapFtOK lapRho t cgRows_3_5_18[i] (sq.getD i (0, 0)))

theorem lapApprox_near {t : ℚ} {sq : List (ℚ × ℚ)} (h : lapOK t sq = true) :
    ‖lapApprox 5 t - gToC (lapTot t sq).1‖ ≤ ((lapTot t sq).2 : ℝ) := by
  classical
  simp only [lapOK, decide_eq_true_eq] at h
  obtain ⟨ζs, hinj, himg, hb⟩ := cgTable_nodes cgTableOK_3_5_18
  have hρ : (0 : ℚ) ≤ lapRho := by norm_num [lapRho]
  rw [lapApprox, ← himg, sum_image fun x _ y _ hxy => hinj hxy]
  have e : gToC (lapTot t sq).1 = ∑ i : Fin cgRows_3_5_18.length,
      gToC (lapFt lapRho t cgRows_3_5_18[i] (sq.getD i (0, 0))).1 := by
    apply Complex.ext <;> simp [gToC, lapTot, Complex.re_sum, Complex.im_sum]
  rw [e, ← sum_sub_distrib, lapTot]
  push_cast
  refine (norm_sum_le _ _).trans (sum_le_sum fun i _ => ?_)
  have hρc : ((lapRho : ℚ) : ℝ) = ((1 / 10 ^ 30 : ℚ) : ℝ) := rfl
  obtain ⟨h1, h2⟩ := hb i
  have := lapFt_sound hρ (h i) (ζ := ζs i) (w := cgWeight 1 5 (ζs i)) (t := t)
    (by simpa [lapRho] using h1) (by simpa [lapRho] using h2)
  simpa [Complex.ofReal_ratCast] using this

/-- The value check for a printed (or corrected) 10D value `X` of `g₅(t)`. -/
def lapRoundsOK (t : ℚ) (sq : List (ℚ × ℚ)) (X : ℤ) : Bool :=
  lapOK t sq && decide (|(lapTot t sq).1.1 - X / 10 ^ 10| + (lapTot t sq).2 ≤ 5 / 10 ^ 11) &&
    decide (|(lapTot t sq).1.2| + (lapTot t sq).2 ≤ 1 / 10 ^ 20)

/-- The erratum check: the printed value `P/10^{10}` is not a correct rounding. -/
def lapWrongOK (t : ℚ) (sq : List (ℚ × ℚ)) (P : ℤ) : Bool :=
  lapOK t sq && decide (5 / 10 ^ 11 < |(lapTot t sq).1.1 - P / 10 ^ 10| - (lapTot t sq).2)

theorem lapRoundsOK_sound {t : ℚ} {sq : List (ℚ × ℚ)} {X : ℤ} (h : lapRoundsOK t sq X = true) :
    RoundsTo (lapApprox 5 t).re (X, 10) ∧ |(lapApprox 5 t).im| ≤ 1 / 10 ^ 20 := by
  simp only [lapRoundsOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hok, hre⟩, him⟩ := h
  have hn := lapApprox_near hok
  have hre' : |(lapApprox 5 t).re - (lapTot t sq).1.1| ≤ (lapTot t sq).2 := by
    have := Complex.abs_re_le_norm (lapApprox 5 t - gToC (lapTot t sq).1)
    rw [Complex.sub_re, show (gToC (lapTot t sq).1).re = ((lapTot t sq).1.1 : ℝ) from rfl]
      at this
    linarith
  have him' : |(lapApprox 5 t).im - (lapTot t sq).1.2| ≤ (lapTot t sq).2 := by
    have := Complex.abs_im_le_norm (lapApprox 5 t - gToC (lapTot t sq).1)
    rw [Complex.sub_im, show (gToC (lapTot t sq).1).im = ((lapTot t sq).1.2 : ℝ) from rfl]
      at this
    linarith
  refine ⟨roundsTo_of_le hre' (by exact_mod_cast hre), ?_⟩
  have h3 := (Rat.cast_le (K := ℝ)).mpr him
  push_cast at h3
  have := abs_sub_abs_le_abs_sub (lapApprox 5 t).im ((lapTot t sq).1.2 : ℝ)
  linarith

theorem lapWrongOK_sound {t : ℚ} {sq : List (ℚ × ℚ)} {P : ℤ} (h : lapWrongOK t sq P = true) :
    ¬ RoundsTo (lapApprox 5 t).re (P, 10) := by
  simp only [lapWrongOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hok, hw⟩ := h
  have hn := lapApprox_near hok
  have hre' : |(lapApprox 5 t).re - (lapTot t sq).1.1| ≤ (lapTot t sq).2 := by
    have := Complex.abs_re_le_norm (lapApprox 5 t - gToC (lapTot t sq).1)
    rw [Complex.sub_re, show (gToC (lapTot t sq).1).re = ((lapTot t sq).1.1 : ℝ) from rfl]
      at this
    linarith
  intro hr
  unfold RoundsTo at hr
  have h3 := (Rat.cast_lt (K := ℝ)).mpr hw
  push_cast at h3 hr
  have := abs_sub_le ((lapTot t sq).1.1 : ℝ) (lapApprox 5 t).re ((P : ℝ) / 10 ^ 10)
  rw [abs_sub_comm ((lapTot t sq).1.1 : ℝ) (lapApprox 5 t).re] at this
  linarith

/-! ### `J₀(t)` by its series with a geometric tail bound -/

/-- `(Sⱼ, aⱼ)`: partial sums and terms of `∑ (−u)ʲ/(j!)²`, `u = (t/2)²`. -/
def j0Rec (u : ℚ) : ℕ → ℚ × ℚ
  | 0 => (0, 1)
  | j + 1 => ((j0Rec u j).1 + (j0Rec u j).2, (j0Rec u j).2 * -u / ((j : ℚ) + 1) ^ 2)

theorem besselCoeff_succ_term (t : ℝ) (j : ℕ) :
    BZ.besselCoeff 0 (j + 1) * (t / 2) ^ (2 * (j + 1) + 0) =
      BZ.besselCoeff 0 j * (t / 2) ^ (2 * j + 0) * -((t / 2) ^ 2) / ((j : ℝ) + 1) ^ 2 := by
  simp only [BZ.besselCoeff, zero_add, add_zero, Nat.factorial_succ]
  push_cast
  have : (j.factorial : ℝ) ≠ 0 := by positivity
  rw [show 2 * (j + 1) = 2 * j + 2 by ring, pow_add, pow_succ (-1 : ℝ)]
  field_simp
  ring

theorem j0Rec_spec (t : ℚ) (j : ℕ) :
    (((j0Rec ((t / 2) ^ 2) j).1 : ℚ) : ℝ) =
        ∑ i ∈ range j, BZ.besselCoeff 0 i * ((t : ℝ) / 2) ^ (2 * i + 0) ∧
      (((j0Rec ((t / 2) ^ 2) j).2 : ℚ) : ℝ) = BZ.besselCoeff 0 j * ((t : ℝ) / 2) ^ (2 * j + 0) := by
  induction j with
  | zero => simp [j0Rec, BZ.besselCoeff]
  | succ j ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨?_, ?_⟩
    · simp only [j0Rec]; push_cast; rw [sum_range_succ, ← h1, ← h2]
    · simp only [j0Rec]; push_cast; rw [besselCoeff_succ_term, ← h2]

/-- The geometric tail bound: if `|aⱼ₊₁| ≤ |aⱼ|/2` for `j ≥ N`, the tail is at most `2|a_N|`. -/
theorem abs_tsum_sub_sum_le {a : ℕ → ℝ} (ha : Summable a) {N : ℕ}
    (hr : ∀ j, N ≤ j → |a (j + 1)| ≤ |a j| / 2) :
    |∑' j, a j - ∑ j ∈ range N, a j| ≤ 2 * |a N| := by
  rw [← ha.sum_add_tsum_nat_add N, add_sub_cancel_left]
  have hg : ∀ i, |a (i + N)| ≤ |a N| * (1 / 2) ^ i := fun i => by
    induction i with
    | zero => simp
    | succ i ih =>
      rw [show i + 1 + N = (i + N) + 1 by ring]
      calc |a (i + N + 1)| ≤ |a (i + N)| / 2 := hr _ (by omega)
        _ ≤ |a N| * (1 / 2) ^ i / 2 := by gcongr
        _ = _ := by rw [pow_succ]; ring
  have hs : Summable fun i => |a N| * (1 / 2 : ℝ) ^ i :=
    (summable_geometric_two).mul_left _
  calc |∑' i, a (i + N)| ≤ ∑' i, |a (i + N)| := by
        rw [← Real.norm_eq_abs]
        refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq (by simp [Real.norm_eq_abs]))
        exact (ha.comp_injective (add_left_injective N)).norm
    _ ≤ ∑' i, |a N| * (1 / 2) ^ i :=
        Summable.tsum_le_tsum hg ((ha.comp_injective (add_left_injective N)).abs) hs
    _ = 2 * |a N| := by rw [tsum_mul_left, tsum_geometric_two]; ring

/-- The exact check of a printed 10D value `X` of `J₀(t)` using `N` terms. -/
def j0OK (t : ℚ) (N : ℕ) (X : ℤ) : Bool :=
  decide (2 * (t / 2) ^ 2 ≤ ((N : ℚ) + 1) ^ 2) &&
    decide (|(j0Rec ((t / 2) ^ 2) N).1 - X / 10 ^ 10| + 2 * |(j0Rec ((t / 2) ^ 2) N).2| ≤
      5 / 10 ^ 11)

theorem j0OK_sound {t : ℚ} {N : ℕ} {X : ℤ} (h : j0OK t N X = true) :
    RoundsTo (besselJ0 t) (X, 10) := by
  simp only [j0OK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hN, hX⟩ := h
  set a : ℕ → ℝ := fun j => BZ.besselCoeff 0 j * ((t : ℝ) / 2) ^ (2 * j + 0)
  have ha : Summable a := BZ.summable_besselJNat_term 0 t
  have hr : ∀ j, N ≤ j → |a (j + 1)| ≤ |a j| / 2 := fun j hj => by
    simp only [a]
    rw [besselCoeff_succ_term]
    set A := BZ.besselCoeff 0 j * ((t : ℝ) / 2) ^ (2 * j + 0)
    rw [abs_div, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg ((t : ℝ) / 2)),
      abs_of_pos (by positivity : (0 : ℝ) < ((j : ℝ) + 1) ^ 2)]
    have hN' : 2 * (((t : ℝ) / 2) ^ 2) ≤ ((j : ℝ) + 1) ^ 2 := by
      have := (Rat.cast_le (K := ℝ)).mpr hN
      push_cast at this
      have : ((N : ℝ) + 1) ^ 2 ≤ ((j : ℝ) + 1) ^ 2 := by
        gcongr
      linarith
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have := mul_le_mul_of_nonneg_left hN' (abs_nonneg A)
    linarith
  have htail := abs_tsum_sub_sum_le ha hr
  obtain ⟨hS, haN⟩ := j0Rec_spec t N
  have hJ : besselJ0 t = ∑' j, a j := rfl
  refine roundsTo_of_le (q := (j0Rec ((t / 2) ^ 2) N).1) (ρ := 2 * |(j0Rec ((t / 2) ^ 2) N).2|)
    ?_ hX
  rw [hJ, hS]
  push_cast
  rw [haN]
  exact htail

/-- Square-root certificates `√(z̃ₖ² + t²)` for `t = 1/2`. -/
def lapSq_half : List (ℚ × ℚ) := [
  (3663846105032138609128199043919453391870569118 / 10 ^ 45,
    6529177581302200164568832181016527833444294462 / 10 ^ 45),
  (3663846105032138609128199043919453391870569118 / 10 ^ 45,
    -6529177581302200164568832181016527833444294462 / 10 ^ 45),
  (5717599716212803309250402234508207408077223315 / 10 ^ 45,
    3200919122021733636384275875617869814350580159 / 10 ^ 45),
  (5717599716212803309250402234508207408077223315 / 10 ^ 45,
    -3200919122021733636384275875617869814350580159 / 10 ^ 45),
  (6306556638563984696050911320760206321103541727 / 10 ^ 45,
    0)]

/-- Square-root certificates `√(z̃ₖ² + t²)` for `t = 1`. -/
def lapSq_one : List (ℚ × ℚ) := [
  (3688525228239839518601943933730723979645203858 / 10 ^ 45,
    6485492268608593137023877229465916138288078370 / 10 ^ 45),
  (3688525228239839518601943933730723979645203858 / 10 ^ 45,
    -6485492268608593137023877229465916138288078370 / 10 ^ 45),
  (5767524151793261548510027039020072779331014145 / 10 ^ 45,
    3173211551788855796280750830552048864728977999 / 10 ^ 45),
  (5767524151793261548510027039020072779331014145 / 10 ^ 45,
    -3173211551788855796280750830552048864728977999 / 10 ^ 45),
  (6365740855188456845099071905802093478885073565 / 10 ^ 45,
    0)]

/-- Square-root certificates `√(z̃ₖ² + t²)` for `t = 2`. -/
def lapSq_two : List (ℚ × ℚ) := [
  (3790661804323532806556897319672665622677977094 / 10 ^ 45,
    6310745480652615980583571320227878321012994535 / 10 ^ 45),
  (3790661804323532806556897319672665622677977094 / 10 ^ 45,
    -6310745480652615980583571320227878321012994535 / 10 ^ 45),
  (5966819086642057234576956363597710039532412535 / 10 ^ 45,
    3067224596211306351137063286012058343767977259 / 10 ^ 45),
  (5966819086642057234576956363597710039532412535 / 10 ^ 45,
    -3067224596211306351137063286012058343767977259 / 10 ^ 45),
  (6597170350643938457730138524603584185858147550 / 10 ^ 45,
    0)]

/-- Square-root certificates `√(z̃ₖ² + t²)` for `t = 5`. -/
def lapSq_five : List (ℚ × ℚ) := [
  (4668752952724569352270812275248534138950333725 / 10 ^ 45,
    5123831158458918295634496043076926909717932753 / 10 ^ 45),
  (4668752952724569352270812275248534138950333725 / 10 ^ 45,
    -5123831158458918295634496043076926909717932753 / 10 ^ 45),
  (7311662162614585123761781912730419438999161394 / 10 ^ 45,
    2503066177930070031356628958718776095555809317 / 10 ^ 45),
  (7311662162614585123761781912730419438999161394 / 10 ^ 45,
    -2503066177930070031356628958718776095555809317 / 10 ^ 45),
  (8032599618766982083193779295201180423427629070 / 10 ^ 45,
    0)]

/-- Square-root certificates `√(z̃ₖ² + t²)` for `t = 10`. -/
def lapSq_ten : List (ℚ × ℚ) := [
  (8825562348608818573042860609501632855255472587 / 10 ^ 45,
    2710524372884641934683256504627602758823040146 / 10 ^ 45),
  (8825562348608818573042860609501632855255472587 / 10 ^ 45,
    -2710524372884641934683256504627602758823040146 / 10 ^ 45),
  (11174850226989934543888446982455631310843630640 / 10 ^ 45,
    1637746716236869385177632974840201247831826899 / 10 ^ 45),
  (11174850226989934543888446982455631310843630640 / 10 ^ 45,
    -1637746716236869385177632974840201247831826899 / 10 ^ 45),
  (11811970903935357472225554443880207411980339681 / 10 ^ 45,
    0)]

/-! ### Table 3.5.19 -/

set_option maxRecDepth 100000 in
/-- **Table 3.5.19**, column `J₀(t)`: the values `1.0000000000, 0.9384698072, 0.7651976866,
0.2238907791, −0.1775967713, −0.2459357645` at `t = 0, 0.5, 1, 2, 5, 10` are correctly
rounded. -/
theorem dlmf_table_3_5_19_J0 :
    RoundsTo (besselJ0 0) (10000000000, 10) ∧ RoundsTo (besselJ0 (1 / 2)) (9384698072, 10) ∧
    RoundsTo (besselJ0 1) (7651976866, 10) ∧ RoundsTo (besselJ0 2) (2238907791, 10) ∧
    RoundsTo (besselJ0 5) (-1775967713, 10) ∧ RoundsTo (besselJ0 10) (-2459357645, 10) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using j0OK_sound (t := 0) (N := 40) (X := 10000000000) (by decide +kernel)
  · simpa using j0OK_sound (t := 1 / 2) (N := 40) (X := 9384698072) (by decide +kernel)
  · simpa using j0OK_sound (t := 1) (N := 40) (X := 7651976866) (by decide +kernel)
  · simpa using j0OK_sound (t := 2) (N := 40) (X := 2238907791) (by decide +kernel)
  · simpa using j0OK_sound (t := 5) (N := 40) (X := -1775967713) (by decide +kernel)
  · simpa using j0OK_sound (t := 10) (N := 40) (X := -2459357645) (by decide +kernel)

set_option maxRecDepth 100000 in
/-- **Table 3.5.19**, column `g(t)` (the 5-point formula 3.5.41 with the exact nodes and weights
of Table 3.5.18): `g₅(0) = 1`, and the correctly rounded 10D values at `t = 0.5, 1, 2, 5, 10`
are `0.9384698072, 0.7651976863, 0.2238910323, −0.1790254103, −0.0754053537` (imaginary parts
`≤ 10⁻²⁰`). -/
theorem dlmf_table_3_5_19_g :
    lapApprox 5 0 = 1 ∧
    (RoundsTo (lapApprox 5 (1 / 2)).re (9384698072, 10) ∧
      |(lapApprox 5 (1 / 2)).im| ≤ 1 / 10 ^ 20) ∧
    (RoundsTo (lapApprox 5 1).re (7651976863, 10) ∧ |(lapApprox 5 1).im| ≤ 1 / 10 ^ 20) ∧
    (RoundsTo (lapApprox 5 2).re (2238910323, 10) ∧ |(lapApprox 5 2).im| ≤ 1 / 10 ^ 20) ∧
    (RoundsTo (lapApprox 5 5).re (-1790254103, 10) ∧ |(lapApprox 5 5).im| ≤ 1 / 10 ^ 20) ∧
    (RoundsTo (lapApprox 5 10).re (-754053537, 10) ∧ |(lapApprox 5 10).im| ≤ 1 / 10 ^ 20) := by
  refine ⟨lapApprox_zero (by norm_num) fun ζ hζ => cgNodes_one_five_re_pos hζ, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using lapRoundsOK_sound (t := 1 / 2) (sq := lapSq_half) (X := 9384698072)
      (by decide +kernel)
  · simpa using lapRoundsOK_sound (t := 1) (sq := lapSq_one) (X := 7651976863) (by decide +kernel)
  · simpa using lapRoundsOK_sound (t := 2) (sq := lapSq_two) (X := 2238910323) (by decide +kernel)
  · simpa using lapRoundsOK_sound (t := 5) (sq := lapSq_five) (X := -1790254103)
      (by decide +kernel)
  · simpa using lapRoundsOK_sound (t := 10) (sq := lapSq_ten) (X := -754053537)
      (by decide +kernel)

set_option maxRecDepth 100000 in
/-- **Erratum to Table 3.5.19**: the printed `g(t)` values `0.7651976865, 0.2238910326,
−0.1790254097, −0.0754053543` at `t = 1, 2, 5, 10` are not the correctly rounded values of the
5-point formula 3.5.41. -/
theorem dlmf_table_3_5_19_erratum :
    ¬ RoundsTo (lapApprox 5 1).re (7651976865, 10) ∧
    ¬ RoundsTo (lapApprox 5 2).re (2238910326, 10) ∧
    ¬ RoundsTo (lapApprox 5 5).re (-1790254097, 10) ∧
    ¬ RoundsTo (lapApprox 5 10).re (-754053543, 10) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using lapWrongOK_sound (t := 1) (sq := lapSq_one) (P := 7651976865) (by decide +kernel)
  · simpa using lapWrongOK_sound (t := 2) (sq := lapSq_two) (P := 2238910326) (by decide +kernel)
  · simpa using lapWrongOK_sound (t := 5) (sq := lapSq_five) (P := -1790254097)
      (by decide +kernel)
  · simpa using lapWrongOK_sound (t := 10) (sq := lapSq_ten) (P := -754053543)
      (by decide +kernel)

/-- "Agreement is very good for small values of `t`, but not for larger values": at `t = 1/2`,
`|g₅ − J₀| < 2·10⁻¹⁰`; at `t = 10`, `|g₅ − J₀| > 0.17`. -/
theorem dlmf_table_3_5_19_agreement :
    ‖lapApprox 5 (1 / 2) - besselJ0 (1 / 2)‖ < 2 / 10 ^ 10 ∧
      0.17 < ‖lapApprox 5 10 - besselJ0 10‖ := by
  obtain ⟨-, ⟨h1, h1i⟩, -, -, -, ⟨h5, -⟩⟩ := dlmf_table_3_5_19_g
  obtain ⟨-, j1, -, -, -, j5⟩ := dlmf_table_3_5_19_J0
  unfold RoundsTo at h1 h5 j1 j5
  rw [abs_le] at h1 h5 j1 j5 h1i
  norm_num at h1 h5 j1 j5 h1i
  constructor
  · have hle := Complex.norm_le_abs_re_add_abs_im (lapApprox 5 (1 / 2) - (besselJ0 (1 / 2) : ℂ))
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im,
      sub_zero] at hle
    have hre : |(lapApprox 5 (1 / 2)).re - besselJ0 (1 / 2)| ≤ 1 / 10 ^ 10 := by
      rw [abs_le]; constructor <;> linarith
    have him : |(lapApprox 5 (1 / 2)).im| ≤ 1 / 10 ^ 20 := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  · have := Complex.abs_re_le_norm (lapApprox 5 10 - (besselJ0 10 : ℂ))
    simp only [Complex.sub_re, Complex.ofReal_re] at this
    refine lt_of_lt_of_le ?_ this
    rw [lt_abs]; left; linarith

end Azurite.DLMF
