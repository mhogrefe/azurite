/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter3.Section1

/-!
# DLMF §3.1(ii): interval arithmetic

* **3.1.6** (`intervalOp`): `I * J = {x * y | x ∈ I, y ∈ J}`. For closed intervals the result is
  the closed interval between the extreme endpoint combinations.
  * `[a, b] + [c, d] = [a + c, b + d]` (`intervalOp_add`).
  * `[a, b] − [c, d] = [a − d, b − c]` (`intervalOp_sub`).
  * `[a, b]·[c, d] = [min(ac, ad, bc, bd), max(…)]` (`intervalOp_mul`).
  * `[a, b]/[c, d] = [a, b]·[1/d, 1/c]` for `0 ∉ [c, d]` (`intervalOp_div`, `image_inv_Icc`).
  * "Division is possible only if the divisor interval does not contain zero": otherwise the
    quotient set is unbounded (`intervalOp_div_unbounded`).
* "With appropriate roundings of the end points": Azurite's directed-rounding interval floats
  (`AzFloat.Encl`) enclose every element of `I + J` and `I − J` (`encl_intervalOp_add_sub`).

§3.1(iii), exact rational arithmetic (rationals in lowest terms over multi-length integers,
convertible to decimal strings of any length), is what Azurite's `AzRat` implements (`AzNat`
numerators and denominators, `AzRat.toSci`); there is nothing further to formalize.
-/

open Set

namespace Azurite.DLMF

/-- **DLMF 3.1.6**: `I * J = {x * y | x ∈ I, y ∈ J}` for an operation `*`. -/
def intervalOp (f : ℝ → ℝ → ℝ) (I J : Set ℝ) : Set ℝ := image2 f I J

/-- The image of a rectangle under a continuous operation is an interval: if every value lies in
`[m, M]` and both `m` and `M` are values, the image is exactly `[m, M]`. -/
theorem intervalOp_eq_Icc {f : ℝ → ℝ → ℝ} (hf : Continuous fun q : ℝ × ℝ => f q.1 q.2)
    {a b c d m M : ℝ}
    (hbd : ∀ x ∈ Icc a b, ∀ y ∈ Icc c d, m ≤ f x y ∧ f x y ≤ M)
    (hm : m ∈ intervalOp f (Icc a b) (Icc c d)) (hM : M ∈ intervalOp f (Icc a b) (Icc c d)) :
    intervalOp f (Icc a b) (Icc c d) = Icc m M := by
  apply Subset.antisymm
  · rintro _ ⟨x, hx, y, hy, rfl⟩
    exact hbd x hx y hy
  · have hconn : IsPreconnected (intervalOp f (Icc a b) (Icc c d)) := by
      unfold intervalOp
      rw [← image_uncurry_prod]
      exact (isPreconnected_Icc.prod isPreconnected_Icc).image _ hf.continuousOn
    exact hconn.Icc_subset hm hM

theorem corner_mem {f : ℝ → ℝ → ℝ} {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    f a c ∈ intervalOp f (Icc a b) (Icc c d) ∧ f a d ∈ intervalOp f (Icc a b) (Icc c d) ∧
      f b c ∈ intervalOp f (Icc a b) (Icc c d) ∧ f b d ∈ intervalOp f (Icc a b) (Icc c d) :=
  ⟨⟨a, left_mem_Icc.mpr hab, c, left_mem_Icc.mpr hcd, rfl⟩,
    ⟨a, left_mem_Icc.mpr hab, d, right_mem_Icc.mpr hcd, rfl⟩,
    ⟨b, right_mem_Icc.mpr hab, c, left_mem_Icc.mpr hcd, rfl⟩,
    ⟨b, right_mem_Icc.mpr hab, d, right_mem_Icc.mpr hcd, rfl⟩⟩

/-- **3.1.6, addition**: `[a, b] + [c, d] = [a + c, b + d]`. -/
theorem intervalOp_add {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    intervalOp (· + ·) (Icc a b) (Icc c d) = Icc (a + c) (b + d) := by
  obtain ⟨h1, -, -, h4⟩ := corner_mem (f := (· + ·)) hab hcd
  exact intervalOp_eq_Icc (by fun_prop)
    (fun x hx y hy => ⟨add_le_add hx.1 hy.1, add_le_add hx.2 hy.2⟩) h1 h4

/-- **3.1.6, subtraction**: `[a, b] − [c, d] = [a − d, b − c]`. -/
theorem intervalOp_sub {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    intervalOp (· - ·) (Icc a b) (Icc c d) = Icc (a - d) (b - c) := by
  obtain ⟨-, h2, h3, -⟩ := corner_mem (f := (· - ·)) hab hcd
  exact intervalOp_eq_Icc (by fun_prop)
    (fun x hx y hy => ⟨sub_le_sub hx.1 hy.2, sub_le_sub hx.2 hy.1⟩) h2 h3

theorem mul_mem_min_max {a b y x : ℝ} (hx : x ∈ Icc a b) :
    min (a * y) (b * y) ≤ x * y ∧ x * y ≤ max (a * y) (b * y) := by
  rcases le_total 0 y with hy | hy
  · have h1 := mul_le_mul_of_nonneg_right hx.1 hy
    have h2 := mul_le_mul_of_nonneg_right hx.2 hy
    exact ⟨min_le_left _ _ |>.trans h1, h2.trans (le_max_right _ _)⟩
  · have h1 := mul_le_mul_of_nonpos_right hx.1 hy
    have h2 := mul_le_mul_of_nonpos_right hx.2 hy
    exact ⟨min_le_right _ _ |>.trans h2, h1.trans (le_max_left _ _)⟩

/-- The least of the four endpoint products. -/
noncomputable def min4 (a b c d : ℝ) : ℝ := min (min (a * c) (a * d)) (min (b * c) (b * d))

/-- The greatest of the four endpoint products. -/
noncomputable def max4 (a b c d : ℝ) : ℝ := max (max (a * c) (a * d)) (max (b * c) (b * d))

/-- **3.1.6, multiplication**: `[a, b]·[c, d] = [min(ac, ad, bc, bd), max(ac, ad, bc, bd)]`. -/
theorem intervalOp_mul {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    intervalOp (· * ·) (Icc a b) (Icc c d) = Icc (min4 a b c d) (max4 a b c d) := by
  obtain ⟨h1, h2, h3, h4⟩ := corner_mem (f := (· * ·)) hab hcd
  refine intervalOp_eq_Icc (by fun_prop) (fun x hx y hy => ?_) ?_ ?_
  · obtain ⟨l, u⟩ := mul_mem_min_max (y := y) hx
    obtain ⟨la, ua⟩ := mul_mem_min_max (y := a) hy
    obtain ⟨lb, ub⟩ := mul_mem_min_max (y := b) hy
    simp only [min4, max4]
    rw [mul_comm c a, mul_comm d a, mul_comm y a] at la ua
    rw [mul_comm c b, mul_comm d b, mul_comm y b] at lb ub
    constructor
    · refine le_trans ?_ l
      rcases le_total (a * y) (b * y) with h | h
      · rw [min_eq_left h]; exact (min_le_left _ _).trans la
      · rw [min_eq_right h]; exact (min_le_right _ _).trans lb
    · refine u.trans ?_
      rcases le_total (a * y) (b * y) with h | h
      · rw [max_eq_right h]; exact ub.trans (le_max_right _ _)
      · rw [max_eq_left h]; exact ua.trans (le_max_left _ _)
  · simp only [min4]
    rcases le_total (min (a * c) (a * d)) (min (b * c) (b * d)) with h | h
    · rw [min_eq_left h]; rcases le_total (a * c) (a * d) with h' | h'
      · rw [min_eq_left h']; exact h1
      · rw [min_eq_right h']; exact h2
    · rw [min_eq_right h]; rcases le_total (b * c) (b * d) with h' | h'
      · rw [min_eq_left h']; exact h3
      · rw [min_eq_right h']; exact h4
  · simp only [max4]
    rcases le_total (max (a * c) (a * d)) (max (b * c) (b * d)) with h | h
    · rw [max_eq_right h]; rcases le_total (b * c) (b * d) with h' | h'
      · rw [max_eq_right h']; exact h4
      · rw [max_eq_left h']; exact h3
    · rw [max_eq_left h]; rcases le_total (a * c) (a * d) with h' | h'
      · rw [max_eq_right h']; exact h2
      · rw [max_eq_left h']; exact h1

/-- The reciprocal of an interval not containing zero: `{1/y | y ∈ [c, d]} = [1/d, 1/c]`. -/
theorem image_inv_Icc {c d : ℝ} (hcd : c ≤ d) (h0 : 0 ∉ Icc c d) :
    (fun y => y⁻¹) '' Icc c d = Icc d⁻¹ c⁻¹ := by
  have hsign : 0 < c ∨ d < 0 := by
    by_contra h; push Not at h; exact h0 ⟨h.1, h.2⟩
  have hne : ∀ y ∈ Icc c d, y ≠ 0 := fun y hy h => h0 (h ▸ hy)
  have hbd : ∀ y ∈ Icc c d, d⁻¹ ≤ y⁻¹ ∧ y⁻¹ ≤ c⁻¹ := by
    intro y hy
    rcases hsign with h | h
    · exact ⟨inv_anti₀ (h.trans_le hy.1) hy.2, inv_anti₀ h hy.1⟩
    · have hy0 : y < 0 := hy.2.trans_lt h
      have hc0 : c < 0 := hy.1.trans_lt hy0
      exact ⟨(inv_le_inv_of_neg h hy0).mpr hy.2, (inv_le_inv_of_neg hy0 hc0).mpr hy.1⟩
  apply Subset.antisymm
  · rintro _ ⟨y, hy, rfl⟩; exact hbd y hy
  · have hconn : IsPreconnected ((fun y : ℝ => y⁻¹) '' Icc c d) :=
      isPreconnected_Icc.image _ fun y hy => (continuousAt_inv₀ (hne y hy)).continuousWithinAt
    exact hconn.Icc_subset ⟨d, right_mem_Icc.mpr hcd, rfl⟩ ⟨c, left_mem_Icc.mpr hcd, rfl⟩

/-- **3.1.6, division** (`0 ∉ [c, d]`): `[a, b]/[c, d] = [a, b]·[1/d, 1/c]`. -/
theorem intervalOp_div {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (h0 : 0 ∉ Icc c d) :
    intervalOp (· / ·) (Icc a b) (Icc c d) = Icc (min4 a b d⁻¹ c⁻¹) (max4 a b d⁻¹ c⁻¹) := by
  have hinv := image_inv_Icc hcd h0
  have hle : d⁻¹ ≤ c⁻¹ := by
    have := (image_inv_Icc hcd h0).symm ▸ (mem_image_of_mem (fun y : ℝ => y⁻¹)
      (left_mem_Icc.mpr hcd))
    exact this.1.trans this.2
  rw [← intervalOp_mul hab hle, ← hinv]
  unfold intervalOp
  rw [image2_image_right]
  rfl

/-- **"Division is possible only if the divisor interval does not contain zero"**: if `0 ∈ [c, d]`
with `c < d` and `I` contains a nonzero number, then `I/J` is unbounded. -/
theorem intervalOp_div_unbounded {I : Set ℝ} {c d : ℝ} (hcd : c < d) (h0 : 0 ∈ Icc c d)
    {x : ℝ} (hx : x ∈ I) (hx0 : x ≠ 0) (M : ℝ) :
    ∃ z ∈ intervalOp (· / ·) I (Icc c d), M < |z| := by
  have hX : 0 < |x| := abs_pos.mpr hx0
  set δ := |x| / (|M| + 1)
  have hδ : 0 < δ := by positivity
  have key : ∀ y : ℝ, y ≠ 0 → |y| ≤ δ → M < |x / y| := by
    intro y hy hyδ
    rw [abs_div, lt_div_iff₀ (abs_pos.mpr hy)]
    have : |y| * (|M| + 1) ≤ |x| := by
      rw [← le_div_iff₀ (by positivity)]; exact hyδ
    nlinarith [abs_nonneg y, le_abs_self M, abs_pos.mpr hy]
  rcases lt_or_eq_of_le h0.2 with hd | hd
  · set y := min d δ
    have hy0 : 0 < y := lt_min hd hδ
    refine ⟨x / y, ⟨x, hx, y, ⟨by linarith [h0.1], min_le_left _ _⟩, rfl⟩,
      key y hy0.ne' ?_⟩
    rw [abs_of_pos hy0]; exact min_le_right _ _
  · have hc : c < 0 := hd ▸ hcd
    set y := max c (-δ)
    have hy0 : y < 0 := max_lt hc (by linarith)
    refine ⟨x / y, ⟨x, hx, y, ⟨le_max_left _ _, by rw [← hd]; exact hy0.le⟩, rfl⟩,
      key y hy0.ne ?_⟩
    rw [abs_of_neg hy0]; have := le_max_right c (-δ); linarith

/-! ### Rounded end points (`AzFloat.Encl`) -/

open Azurite.AzFloat Encl

/-- **"with appropriate roundings of the end points of `I * J` when machine numbers are being
used"**: Azurite's interval floats (`Encl`, directed rounding) enclose all of `I + J` and `I − J`
when their arguments enclose `I` and `J`. -/
theorem encl_intervalOp_add_sub {w : ℕ} [NeZero w] {A B : Encl} {I J : Set ℝ}
    (hA : ∀ x ∈ I, IsEncl A x) (hB : ∀ y ∈ J, IsEncl B y) :
    (∀ z ∈ intervalOp (· + ·) I J, IsEncl (Encl.add w A B) z) ∧
      ∀ z ∈ intervalOp (· - ·) I J, IsEncl (Encl.sub w A B) z := by
  constructor
  · rintro _ ⟨x, hx, y, hy, rfl⟩; exact (hA x hx).add (hB y hy)
  · rintro _ ⟨x, hx, y, hy, rfl⟩; exact (hA x hx).sub (hB y hy)

end Azurite.DLMF
