/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LambertWBracket
import Azurite.Transcendental.LambertW
import Azurite.AzFloat.Equiv.RatPowBracket
import Azurite.AzFloat.Equiv.Interval
import Azurite.AzFloat.Equiv.Ln
import Azurite.AzFloat.Equiv.Sqrt
import Azurite.AzFloat.Equiv.Pow

/-!
# Equivalence: the brackets of the real Lambert `W` function

* `findSome_spec`: the certified search returns a value of `f`.
* `mulExpBracket_spec`; `sideAt_eq_some_true/false`, `exists_sideAt_isSome` (the side of a
  test point `m` with `m eᵐ ≠ x` is decided at some precision), `sideOf_true/false`.
* `qBounds_spec`, `qAt_eq_some_none` (`x < −e⁻¹`), `qAt_eq_some_some` (`0 < lo ≤ q ≤ hi`),
  `exists_qAt_isSome` (decided at some precision when `q ≠ 0`), `qTight_spec`.
* `aprioriW0Pos_spec`, `aprioriW0Neg_spec`, `aprioriWm1_spec`: the a priori enclosures.
* `mvtRound_spec`, `mvtRounds_spec`: the mean-value rounds keep the root and the candidate.
* `gridBisectStep_spec`, `bisectGrid_spec`: the grid bisection keeps the root and shrinks the width
  by `3/4` per step.
* `lambertBracket_spec`: the bracket encloses the root with an explicit width bound,
  `lambertApprox_isSome_exists`: the Ziv certificate.
-/

open Real Set Azurite.DLMF Azurite.LambertW

namespace Azurite.AzFloat

/-! ### Comparisons -/

theorem toVal_zero' : zero.toVal = some ((0 : ℝ) : EReal) := by rw [toVal_zero, EReal.coe_zero]

/-! ### The target -/

/-- `xAt` encloses `x` at every precision `P ≥ 64`, within `4|x| 2^(−P)`. -/
def XEncl (xAt : ℕ → AzFloat × AzFloat) (xv : ℝ) : Prop :=
  ∀ P : ℕ, 64 ≤ P → ∃ lo hi : ℝ, (xAt P).1.toVal = some (lo : EReal) ∧
    (xAt P).2.toVal = some (hi : EReal) ∧ lo ≤ xv ∧ xv ≤ hi ∧ hi - lo ≤ 4 * |xv| * (1 / 2 : ℝ) ^ P

theorem floatAt_encl {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) :
    XEncl (floatAt x) xv := fun P _ =>
  ⟨xv, xv, hx, hx, le_rfl, le_rfl, by simp only [sub_self]; positivity⟩

theorem ratAt_encl (q : AzRat) : XEncl (ratAt q) ((AzRat.toRat q : ℚ) : ℝ) := fun P hP => by
  have : NeZero P := ⟨by omega⟩
  obtain ⟨r₁, h₁, h₁1, h₁2⟩ := ofAzRatRound_floor_abs q P
  obtain ⟨r₂, h₂, h₂1, h₂2⟩ := ofAzRatRound_ceiling_abs q P
  exact ⟨r₁, r₂, h₁, h₂, h₁1, h₂1, by linarith⟩

/-! ### The certified search -/

theorem findSome_go_spec {α : Type} (f : ℕ → Option α) (h : ∃ k, (f k).isSome = true) :
    ∀ (n k : ℕ) (hk : ∀ j < k, (f j).isSome = false), Nat.find h ≤ k + n →
      ∃ j, f j = some (findSome.go f h k hk) := by
  intro n
  induction n with
  | zero =>
    intro k hk hn
    rw [findSome.go.eq_def]
    split
    · rename_i a hf; exact ⟨k, hf⟩
    · rename_i hf
      exfalso
      have hspec := Nat.find_spec h
      rcases Nat.lt_or_ge (Nat.find h) k with hlt | hge
      · rw [hk _ hlt] at hspec; exact Bool.false_ne_true hspec
      · have : Nat.find h = k := by omega
        rw [this, hf] at hspec; exact Bool.false_ne_true hspec
  | succ n ih =>
    intro k hk hn
    rw [findSome.go.eq_def]
    split
    · rename_i a hf; exact ⟨k, hf⟩
    · rename_i hf
      exact ih (k + 1) _ (by omega)

/-- The certified search returns a value of `f`. -/
theorem findSome_spec {α : Type} (f : ℕ → Option α) (h : ∃ k, (f k).isSome = true) :
    ∃ j, f j = some (findSome f h) :=
  findSome_go_spec f h (Nat.find h) 0 _ (by omega)

/-! ### `t eᵗ` -/

/-- The width bound of `mulExpBracket t P`. -/
noncomputable def mulExpEps (tv : ℝ) (P : ℕ) : ℝ :=
  |tv| * expEps tv P + 2 * |tv| * (2 * Real.exp tv + 2 * expEps tv P) * (1 / 2 : ℝ) ^ P

theorem tendsto_mulExpEps (tv : ℝ) : Filter.Tendsto (mulExpEps tv) Filter.atTop (nhds 0) := by
  unfold mulExpEps
  have h1 := (tendsto_expEps tv).const_mul |tv|
  have hu := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have h2 := ((((tendsto_expEps tv).const_mul 2).const_add (2 * Real.exp tv)).const_mul
    (2 * |tv|)).mul hu
  simp only [mul_zero, add_zero] at h1 h2
  have := h1.add h2
  rwa [add_zero] at this

/-- `mulExpBracket t P` encloses `t eᵗ` with width at most `mulExpEps t P`. -/
theorem mulExpBracket_spec {t : AzFloat} {tv : ℝ} (ht : t.toVal = some (tv : EReal)) {P : ℕ}
    (hP : 64 ≤ P) :
    ∃ lo hi : ℝ, (mulExpBracket t P).1.toVal = some (lo : EReal) ∧
      (mulExpBracket t P).2.toVal = some (hi : EReal) ∧ lo ≤ tv * Real.exp tv ∧
      tv * Real.exp tv ≤ hi ∧ hi - lo ≤ mulExpEps tv P := by
  have : NeZero P := ⟨by omega⟩
  obtain ⟨c, d, hc, hd, hc1, hd1, hcd⟩ := expBracketAt_spec ht hP
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hw⟩ := mulBracketAny_spec ht hc hd hc1 hd1 P
  refine ⟨lo, hi, hlo, hhi, h1, h2, hw.trans ?_⟩
  have he := Real.exp_pos tv
  have hε0 : 0 ≤ expEps tv P := by unfold expEps; positivity
  have hcabs : |c| ≤ Real.exp tv + expEps tv P := by
    rw [abs_le]; constructor <;> linarith
  have hdabs : |d| ≤ Real.exp tv + expEps tv P := by
    rw [abs_of_nonneg (by linarith)]; linarith
  have ht0 : 0 ≤ |tv| := abs_nonneg _
  have hu0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ P := by positivity
  have h3 : |tv| * (d - c) ≤ |tv| * expEps tv P := mul_le_mul_of_nonneg_left hcd ht0
  have h4 : 2 * |tv| * (|c| + |d|) * (1 / 2 : ℝ) ^ P
      ≤ 2 * |tv| * (2 * Real.exp tv + 2 * expEps tv P) * (1 / 2 : ℝ) ^ P := by
    apply mul_le_mul_of_nonneg_right _ hu0
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  unfold mulExpEps
  linarith

/-! ### The side of a test point -/

theorem sideAt_eq_some_true {xAt : ℕ → AzFloat × AzFloat} {xv : ℝ} (hX : XEncl xAt xv)
    {m : AzFloat} {mv : ℝ} (hm : m.toVal = some (mv : EReal)) {P : ℕ} (hP : 64 ≤ P)
    (h : sideAt xAt m P = some true) : mv * Real.exp mv < xv := by
  obtain ⟨xlo, xhi, hxlo, hxhi, hx1, hx2, -⟩ := hX P hP
  obtain ⟨lo, hi, hlo, hhi, h1, h2, -⟩ := mulExpBracket_spec hm hP
  unfold sideAt at h
  simp only at h
  split_ifs at h with hc1 hc2
  · rw [lt_eq_true_iff hhi hxlo] at hc1; linarith
  · cases h

theorem sideAt_eq_some_false {xAt : ℕ → AzFloat × AzFloat} {xv : ℝ} (hX : XEncl xAt xv)
    {m : AzFloat} {mv : ℝ} (hm : m.toVal = some (mv : EReal)) {P : ℕ} (hP : 64 ≤ P)
    (h : sideAt xAt m P = some false) : xv < mv * Real.exp mv := by
  obtain ⟨xlo, xhi, hxlo, hxhi, hx1, hx2, -⟩ := hX P hP
  obtain ⟨lo, hi, hlo, hhi, h1, h2, -⟩ := mulExpBracket_spec hm hP
  unfold sideAt at h
  simp only at h
  split_ifs at h with hc1 hc2
  · cases h
  · rw [lt_eq_true_iff hxhi hlo] at hc2; linarith

theorem le_mul_two_pow_self (n : ℕ) : n ≤ 64 * 2 ^ n := by
  have := Nat.lt_two_pow_self (n := n)
  omega

/-- The side of a test point `m` with `m eᵐ ≠ x` is decided at some precision `64 · 2^k`. -/
theorem exists_sideAt_isSome {xAt : ℕ → AzFloat × AzFloat} {xv : ℝ} (hX : XEncl xAt xv)
    {m : AzFloat} {mv : ℝ} (hm : m.toVal = some (mv : EReal)) (hne : mv * Real.exp mv ≠ xv) :
    ∃ k, (sideAt xAt m (64 * 2 ^ k)).isSome = true := by
  have hδ : 0 < |mv * Real.exp mv - xv| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hu := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have htend : Filter.Tendsto (fun P : ℕ => mulExpEps mv P + 4 * |xv| * (1 / 2 : ℝ) ^ P)
      Filter.atTop (nhds 0) := by
    have := (tendsto_mulExpEps mv).add (hu.const_mul (4 * |xv|))
    simpa using this
  obtain ⟨P₀, hP₀⟩ := Filter.eventually_atTop.mp (htend.eventually (gt_mem_nhds hδ))
  refine ⟨P₀, ?_⟩
  have hP : 64 ≤ 64 * 2 ^ P₀ := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
  obtain ⟨xlo, xhi, hxlo, hxhi, hx1, hx2, hxw⟩ := hX _ hP
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hw⟩ := mulExpBracket_spec hm hP
  have hε := hP₀ _ (le_mul_two_pow_self P₀)
  unfold sideAt
  simp only
  split_ifs with hc1 hc2
  · rfl
  · rfl
  · exfalso
    rw [lt_eq_true_iff hhi hxlo] at hc1
    rw [lt_eq_true_iff hxhi hlo] at hc2
    have : |mv * Real.exp mv - xv| ≤ (hi - lo) + (xhi - xlo) := by
      rw [abs_le]; constructor <;> linarith
    linarith

theorem sideOf_true {xAt : ℕ → AzFloat × AzFloat} {xv : ℝ} (hX : XEncl xAt xv) {m : AzFloat}
    {mv : ℝ} (hm : m.toVal = some (mv : EReal))
    (hs : ∃ k, (sideAt xAt m (64 * 2 ^ k)).isSome = true) (h : sideOf xAt m hs = true) :
    mv * Real.exp mv < xv := by
  obtain ⟨j, hj⟩ := findSome_spec (fun k => sideAt xAt m (64 * 2 ^ k)) hs
  unfold sideOf at h
  rw [h] at hj
  exact sideAt_eq_some_true hX hm (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)) hj

theorem sideOf_false {xAt : ℕ → AzFloat × AzFloat} {xv : ℝ} (hX : XEncl xAt xv) {m : AzFloat}
    {mv : ℝ} (hm : m.toVal = some (mv : EReal))
    (hs : ∃ k, (sideAt xAt m (64 * 2 ^ k)).isSome = true) (h : sideOf xAt m hs = false) :
    xv < mv * Real.exp mv := by
  obtain ⟨j, hj⟩ := findSome_spec (fun k => sideAt xAt m (64 * 2 ^ k)) hs
  unfold sideOf at h
  rw [h] at hj
  exact sideAt_eq_some_false hX hm (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)) hj

/-! ### `q = 1 + e x` -/

/-- `(P + 9) 2^(−P)` is decreasing: at most `73 · 2^(−64)` from `P = 64`. -/
theorem add_nine_mul_half_pow_le {P : ℕ} (hP : 64 ≤ P) :
    ((P : ℝ) + 9) * (1 / 2 : ℝ) ^ P ≤ 73 * (1 / 2 : ℝ) ^ 64 := by
  induction P, hP using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h : ((n + 1 : ℕ) : ℝ) + 9 ≤ 2 * ((n : ℝ) + 9) := by push_cast; linarith
    calc (((n + 1 : ℕ) : ℝ) + 9) * (1 / 2 : ℝ) ^ (n + 1)
        = (((n + 1 : ℕ) : ℝ) + 9) * (1 / 2 : ℝ) ^ n * (1 / 2) := by ring
      _ ≤ 2 * ((n : ℝ) + 9) * (1 / 2 : ℝ) ^ n * (1 / 2) := by gcongr
      _ = ((n : ℝ) + 9) * (1 / 2 : ℝ) ^ n := by ring
      _ ≤ _ := ih

/-- `expEps 1 P ≤ 1` for `P ≥ 64`. -/
theorem expEps_one_le_one {P : ℕ} (hP : 64 ≤ P) : expEps 1 P ≤ 1 := by
  unfold expEps
  have h := add_nine_mul_half_pow_le hP
  have he : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
  have h0 : 0 ≤ ((P : ℝ) + 9) * (1 / 2 : ℝ) ^ P := by positivity
  calc Real.exp 1 * (80 * ((P : ℝ) + 9)) * (1 / 2 : ℝ) ^ P
      = Real.exp 1 * 80 * (((P : ℝ) + 9) * (1 / 2 : ℝ) ^ P) := by ring
    _ ≤ 3 * 80 * (73 * (1 / 2 : ℝ) ^ 64) := by gcongr
    _ ≤ 1 := by norm_num

/-- The bracket of `e` with a nonnegative lower end has the width of `expBracketAt`. -/
theorem exp_one_encl {P : ℕ} (hP : 64 ≤ P) :
    ∃ c d : ℝ, (Encl.exp P one).1.toVal = some (c : EReal) ∧
      (Encl.exp P one).2.toVal = some (d : EReal) ∧ 0 ≤ c ∧ c ≤ Real.exp 1 ∧ Real.exp 1 ≤ d ∧
      d - c ≤ expEps 1 P := by
  obtain ⟨c₀, d, hc₀, hd, hc1, hd1, hcd⟩ := expBracketAt_spec toVal_one' hP
  obtain ⟨c, hc, hc0, hcle, hceq⟩ := clampNonneg_spec hc₀
  have hc₀0 : 0 ≤ c₀ := by
    by_contra hneg
    push Not at hneg
    have := expEps_one_le_one hP
    have := Real.add_one_lt_exp (one_ne_zero (α := ℝ))
    linarith
  rw [hceq hc₀0] at hc
  exact ⟨c₀, d, hc, hd, hc₀0, hc1, hd1, hcd⟩

/-- `qBounds xAt P` encloses `1 + e x` for `x < 0`, within `(177|x| + 2)(expEps 1 P + 2^(−P))`
on each side. -/
theorem qBounds_spec {xAt : ℕ → AzFloat × AzFloat} {xv : ℝ} (hX : XEncl xAt xv) (hx0 : xv < 0)
    {P : ℕ} (hP : 64 ≤ P) :
    ∃ lo hi : ℝ, (qBounds xAt P).1.toVal = some (lo : EReal) ∧
      (qBounds xAt P).2.toVal = some (hi : EReal) ∧ lo ≤ 1 + Real.exp 1 * xv ∧
      1 + Real.exp 1 * xv ≤ hi ∧
      1 + Real.exp 1 * xv - (177 * |xv| + 2) * (expEps 1 P + (1 / 2 : ℝ) ^ P) ≤ lo ∧
      hi ≤ 1 + Real.exp 1 * xv + (177 * |xv| + 2) * (expEps 1 P + (1 / 2 : ℝ) ^ P) := by
  have : NeZero P := ⟨by omega⟩
  obtain ⟨c, d, hc, hd, hc0, hc1, hd1, hcd⟩ := exp_one_encl hP
  obtain ⟨x₁, x₂, hx₁, hx₂, hx₁1, hx₂1, hxw⟩ := hX P hP
  set u := (1 / 2 : ℝ) ^ P with hu
  set ε := expEps 1 P with hε
  have hu0 : 0 ≤ u := by positivity
  have hu1 : u ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hε0 : 0 ≤ ε := by rw [hε]; unfold expEps; positivity
  have hε1 : ε ≤ 1 := expEps_one_le_one hP
  have he0 := Real.exp_pos 1
  have he3 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
  set A := |xv| with hA
  have hA0 : 0 ≤ A := abs_nonneg _
  have hxA : xv = -A := by rw [hA, abs_of_neg hx0]; ring
  have hd4 : d ≤ 4 := by linarith
  have hc4 : c ≤ 4 := by linarith
  -- `x₁, x₂` are within `4Au` of `x`
  have hx₁A : |x₁| ≤ 5 * A := by rw [abs_le]; constructor <;> nlinarith
  have hx₂A : |x₂| ≤ 5 * A := by rw [abs_le]; constructor <;> nlinarith
  unfold qBounds
  simp only
  obtain ⟨r, hr, hr1, hr2⟩ := mulFloor_abs hd hx₁ P
  obtain ⟨lo, hlo, hlo1, hlo2⟩ := addFloor_abs toVal_one' hr P
  obtain ⟨r', hr', hr'1, hr'2⟩ := mulCeiling_abs hc hx₂ P
  obtain ⟨hi, hhi, hhi1, hhi2⟩ := addCeiling_abs toVal_one' hr' P
  rw [← hu] at hr2 hlo2 hr'2 hhi2
  have hdx : d * x₁ ≤ Real.exp 1 * xv := by
    calc d * x₁ ≤ d * xv := mul_le_mul_of_nonneg_left hx₁1 (by linarith)
      _ ≤ Real.exp 1 * xv := mul_le_mul_of_nonpos_right hd1 hx0.le
  have hcx : Real.exp 1 * xv ≤ c * x₂ := by
    calc Real.exp 1 * xv ≤ c * xv := mul_le_mul_of_nonpos_right hc1 hx0.le
      _ ≤ c * x₂ := mul_le_mul_of_nonneg_left hx₂1 hc0
  have hdxa : |d * x₁| ≤ 20 * A := by
    rw [abs_mul, abs_of_nonneg (by linarith)]; nlinarith
  have hcxa : |c * x₂| ≤ 20 * A := by
    rw [abs_mul, abs_of_nonneg hc0]; nlinarith
  have hdxu : |d * x₁| * u ≤ 20 * A * u := mul_le_mul_of_nonneg_right hdxa hu0
  have hcxu : |c * x₂| * u ≤ 20 * A * u := mul_le_mul_of_nonneg_right hcxa hu0
  have hr_abs : |1 + r| ≤ 1 + 60 * A := by
    have h1 := le_abs_self (d * x₁)
    have h2 := neg_abs_le (d * x₁)
    have hdxu1 : |d * x₁| * u ≤ |d * x₁| := mul_le_of_le_one_right (abs_nonneg _) hu1
    have : |r| ≤ 60 * A := by rw [abs_le]; constructor <;> nlinarith
    calc |1 + r| ≤ |(1 : ℝ)| + |r| := abs_add_le 1 r
      _ ≤ 1 + 60 * A := by rw [abs_one]; linarith
  have hr'_abs : |1 + r'| ≤ 1 + 60 * A := by
    have h1 := le_abs_self (c * x₂)
    have h2 := neg_abs_le (c * x₂)
    have hcxu1 : |c * x₂| * u ≤ |c * x₂| := mul_le_of_le_one_right (abs_nonneg _) hu1
    have : |r'| ≤ 60 * A := by rw [abs_le]; constructor <;> nlinarith
    calc |1 + r'| ≤ |(1 : ℝ)| + |r'| := abs_add_le 1 r'
      _ ≤ 1 + 60 * A := by rw [abs_one]; linarith
  have hru : |1 + r| * u ≤ (1 + 60 * A) * u := mul_le_mul_of_nonneg_right hr_abs hu0
  have hr'u : |1 + r'| * u ≤ (1 + 60 * A) * u := mul_le_mul_of_nonneg_right hr'_abs hu0
  -- the errors from the bracket of `e` and from the enclosure of `x`
  have hde : (d - Real.exp 1) * A ≤ ε * A := mul_le_mul_of_nonneg_right (by linarith) hA0
  have hce : (Real.exp 1 - c) * A ≤ ε * A := mul_le_mul_of_nonneg_right (by linarith) hA0
  have hdw : d * (xv - x₁) ≤ 16 * A * u := by
    calc d * (xv - x₁) ≤ 4 * (4 * A * u) :=
          mul_le_mul hd4 (by linarith) (by linarith) (by norm_num)
      _ = 16 * A * u := by ring
  have hcw : c * (x₂ - xv) ≤ 16 * A * u := by
    calc c * (x₂ - xv) ≤ 4 * (4 * A * u) :=
          mul_le_mul hc4 (by linarith) (by linarith) (by norm_num)
      _ = 16 * A * u := by ring
  have e1 : d * xv = Real.exp 1 * xv - (d - Real.exp 1) * A := by rw [hxA]; ring
  have e2 : c * xv = Real.exp 1 * xv + (Real.exp 1 - c) * A := by rw [hxA]; ring
  have hAu : 0 ≤ A * u := mul_nonneg hA0 hu0
  have hAε : 0 ≤ A * ε := mul_nonneg hA0 hε0
  have hprod : (177 * A + 2) * (ε + u) = 177 * (A * ε) + 2 * ε + 177 * (A * u) + 2 * u := by ring
  have hdx₁ : d * x₁ ≥ Real.exp 1 * xv - ε * A - 16 * A * u := by
    have : d * x₁ = d * xv - d * (xv - x₁) := by ring
    linarith
  have hcx₂ : c * x₂ ≤ Real.exp 1 * xv + ε * A + 16 * A * u := by
    have : c * x₂ = c * xv + c * (x₂ - xv) := by ring
    linarith
  refine ⟨lo, hi, hlo, hhi, by linarith, by linarith, ?_, ?_⟩
  · have hr_lo : r ≥ d * x₁ - 2 * (|d * x₁| * u) := by linarith
    have hlo_lo : lo ≥ 1 + r - 2 * (|1 + r| * u) := by linarith
    linarith
  · have hr_hi : r' ≤ c * x₂ + 2 * (|c * x₂| * u) := by linarith
    have hhi_hi : hi ≤ 1 + r' + 2 * (|1 + r'| * u) := by linarith
    linarith

/-- The error bound of `qBounds` tends to `0`. -/
theorem tendsto_qErr (A : ℝ) :
    Filter.Tendsto (fun P : ℕ => (177 * A + 2) * (expEps 1 P + (1 / 2 : ℝ) ^ P)) Filter.atTop
      (nhds 0) := by
  have hu := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have := ((tendsto_expEps 1).add hu).const_mul (177 * A + 2)
  simp only [add_zero, mul_zero] at this
  exact this

theorem exp_neg_one_eq : Real.exp (-1) = (Real.exp 1)⁻¹ := Real.exp_neg 1

theorem lt_neg_exp_neg_one_iff (xv : ℝ) : xv < -Real.exp (-1) ↔ 1 + Real.exp 1 * xv < 0 := by
  rw [exp_neg_one_eq]
  have he := Real.exp_pos 1
  constructor
  · intro h
    have : xv * Real.exp 1 < -(Real.exp 1)⁻¹ * Real.exp 1 := mul_lt_mul_of_pos_right h he
    rw [neg_mul, inv_mul_cancel₀ he.ne'] at this
    linarith
  · intro h
    have h2 : xv * Real.exp 1 < -1 := by linarith
    have : xv < -1 / Real.exp 1 := (lt_div_iff₀ he).mpr h2
    rwa [neg_div, one_div] at this

theorem qAt_eq_some_none {xAt : ℕ → AzFloat × AzFloat} {xv : ℝ} (hX : XEncl xAt xv)
    (hx0 : xv < 0) {P : ℕ} (hP : 64 ≤ P) (h : qAt xAt P = some none) : xv < -Real.exp (-1) := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, -, -⟩ := qBounds_spec hX hx0 hP
  unfold qAt at h
  simp only at h
  split_ifs at h with hc1 hc2
  · rw [lt_eq_true_iff hhi (by rw [toVal_zero, EReal.coe_zero])] at hc1
    rw [lt_neg_exp_neg_one_iff]
    linarith
  · cases h

theorem qAt_eq_some_some {xAt : ℕ → AzFloat × AzFloat} {xv : ℝ} (hX : XEncl xAt xv)
    (hx0 : xv < 0) {P : ℕ} (hP : 64 ≤ P) {lo hi : AzFloat} (h : qAt xAt P = some (some (lo, hi))) :
    ∃ lov hiv : ℝ, lo.toVal = some (lov : EReal) ∧ hi.toVal = some (hiv : EReal) ∧ 0 < lov ∧
      lov ≤ 1 + Real.exp 1 * xv ∧ 1 + Real.exp 1 * xv ≤ hiv := by
  obtain ⟨lov, hiv, hlo, hhi, h1, h2, -, -⟩ := qBounds_spec hX hx0 hP
  unfold qAt at h
  simp only at h
  split_ifs at h with hc1 hc2
  · cases h
  · rw [lt_eq_true_iff (by rw [toVal_zero, EReal.coe_zero]) hlo] at hc2
    simp only [Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨lov, hiv, hlo, hhi, hc2, h1, h2⟩

/-- The sign of `q = 1 + e x ≠ 0` is decided at some precision `64 · 2^k`. -/
theorem exists_qAt_isSome {xAt : ℕ → AzFloat × AzFloat} {xv : ℝ} (hX : XEncl xAt xv) (hx0 : xv < 0)
    (hne : 1 + Real.exp 1 * xv ≠ 0) : ∃ k, (qAt xAt (64 * 2 ^ k)).isSome = true := by
  have hδ : 0 < |1 + Real.exp 1 * xv| := abs_pos.mpr hne
  obtain ⟨P₀, hP₀⟩ := Filter.eventually_atTop.mp
    ((tendsto_qErr |xv|).eventually (gt_mem_nhds hδ))
  refine ⟨P₀, ?_⟩
  have hP : 64 ≤ 64 * 2 ^ P₀ := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
  obtain ⟨lo, hi, hlo, hhi, h1, h2, h3, h4⟩ := qBounds_spec hX hx0 hP
  have hε := hP₀ _ (le_mul_two_pow_self P₀)
  unfold qAt
  simp only
  split_ifs with hc1 hc2
  · rfl
  · rfl
  · exfalso
    rw [lt_eq_true_iff hhi (by rw [toVal_zero, EReal.coe_zero])] at hc1
    rw [lt_eq_true_iff (by rw [toVal_zero, EReal.coe_zero]) hlo] at hc2
    rcases lt_or_gt_of_ne hne with hq | hq
    · rw [abs_of_neg hq] at hε; linarith
    · rw [abs_of_pos hq] at hε; linarith

theorem qEncl_eq_none {xAt : ℕ → AzFloat × AzFloat} {xv : ℝ} (hX : XEncl xAt xv) (hx0 : xv < 0)
    (h : ∃ k, (qAt xAt (64 * 2 ^ k)).isSome = true) (hn : qEncl xAt h = none) :
    xv < -Real.exp (-1) := by
  obtain ⟨j, hj⟩ := findSome_spec (fun k => qAt xAt (64 * 2 ^ k)) h
  unfold qEncl at hn
  rw [hn] at hj
  exact qAt_eq_some_none hX hx0 (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)) hj

theorem qEncl_eq_some {xAt : ℕ → AzFloat × AzFloat} {xv : ℝ} (hX : XEncl xAt xv) (hx0 : xv < 0)
    (h : ∃ k, (qAt xAt (64 * 2 ^ k)).isSome = true) {lo hi : AzFloat}
    (hs : qEncl xAt h = some (lo, hi)) :
    ∃ lov hiv : ℝ, lo.toVal = some (lov : EReal) ∧ hi.toVal = some (hiv : EReal) ∧ 0 < lov ∧
      lov ≤ 1 + Real.exp 1 * xv ∧ 1 + Real.exp 1 * xv ≤ hiv := by
  obtain ⟨j, hj⟩ := findSome_spec (fun k => qAt xAt (64 * 2 ^ k)) h
  unfold qEncl at hs
  rw [hs] at hj
  exact qAt_eq_some_some hX hx0 (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)) hj

/-- `qTight` keeps a sound enclosure. -/
theorem qTight_spec {xAt : ℕ → AzFloat × AzFloat} {xv : ℝ} (hX : XEncl xAt xv) (hx0 : xv < 0)
    {q : AzFloat × AzFloat} {l h : ℝ} (hl : q.1.toVal = some (l : EReal))
    (hh : q.2.toVal = some (h : EReal)) (hl0 : 0 < l) (hlq : l ≤ 1 + Real.exp 1 * xv)
    (hqh : 1 + Real.exp 1 * xv ≤ h) :
    ∃ lov hiv : ℝ, (qTight xAt q).1.toVal = some (lov : EReal) ∧
      (qTight xAt q).2.toVal = some (hiv : EReal) ∧ 0 < lov ∧ lov ≤ 1 + Real.exp 1 * xv ∧
      1 + Real.exp 1 * xv ≤ hiv := by
  unfold qTight
  simp only
  have hP : 64 ≤ 128 + 2 * compBits (some q) := by omega
  obtain ⟨lov, hiv, hlo, hhi, h1, h2, -, -⟩ := qBounds_spec hX hx0 hP
  split_ifs with h0 hc
  · exact ⟨l, h, hl, hh, hl0, hlq, hqh⟩
  · rw [lt_eq_true_iff toVal_zero' hlo] at hc
    exact ⟨lov, hiv, hlo, hhi, hc, h1, h2⟩
  · exact ⟨l, h, hl, hh, hl0, hlq, hqh⟩

/-- `−e⁻¹ < x` iff `0 < 1 + e x`. -/
theorem neg_exp_neg_one_lt_iff (xv : ℝ) : -Real.exp (-1) < xv ↔ 0 < 1 + Real.exp 1 * xv := by
  rw [exp_neg_one_eq]
  have he := Real.exp_pos 1
  constructor
  · intro h
    have : -(Real.exp 1)⁻¹ * Real.exp 1 < xv * Real.exp 1 := mul_lt_mul_of_pos_right h he
    rw [neg_mul, inv_mul_cancel₀ he.ne'] at this
    linarith
  · intro h
    have h2 : -1 < xv * Real.exp 1 := by linarith
    have : -1 / Real.exp 1 < xv := (div_lt_iff₀ he).mpr h2
    rwa [neg_div, one_div] at this

/-! ### A priori enclosures -/

theorem lnFloor_le {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (hpos : 0 < xv)
    (P : ℕ) [NeZero P] :
    ∃ l : ℝ, (lnPrecRound x P .Floor).1.toVal = some (l : EReal) ∧ l ≤ Real.log xv := by
  rw [lnPrecRound_eq_liftVal, liftVal, hx, Option.bind_some, Spec.log_coe xv hpos]
  obtain ⟨v, hv, hv1, -⟩ := roundVal_floor_spec P (Real.log xv)
  exact ⟨v, hv, hv1⟩

theorem lnCeiling_ge {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (hpos : 0 < xv)
    (P : ℕ) [NeZero P] :
    ∃ l : ℝ, (lnPrecRound x P .Ceiling).1.toVal = some (l : EReal) ∧ Real.log xv ≤ l := by
  rw [lnPrecRound_eq_liftVal, liftVal, hx, Option.bind_some, Spec.log_coe xv hpos]
  obtain ⟨v, hv, hv1⟩ := roundVal_ceiling_spec P (Real.log xv)
  exact ⟨v, hv, hv1⟩

theorem toVal_three : (ofAzNat (AzNat.ofNat 3)).toVal = some ((3 : ℝ) : EReal) := by
  rw [toVal_ofAzNat, AzNat.toNat_ofNat]; push_cast; rfl

theorem toVal_shiftLeft_one {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) :
    (x <<< AzInt.ofInt 1).toVal = some ((2 * xv : ℝ) : EReal) := by
  rw [toVal_shiftLeft_of_toVal hx, AzInt.toInt_ofInt]
  norm_num [mul_comm]

/-- `aprioriW0Pos` encloses `W₀ x` for `x > 0`. -/
theorem aprioriW0Pos_spec {xAt : ℕ → AzFloat × AzFloat} {xv : ℝ} (hX : XEncl xAt xv)
    (hx0 : 0 < xv) {P : ℕ} (hP : 64 ≤ P) :
    ∃ a b : ℝ, (aprioriW0Pos xAt P).1.toVal = some (a : EReal) ∧
      (aprioriW0Pos xAt P).2.toVal = some (b : EReal) ∧ a ≤ lambertW0 xv ∧ lambertW0 xv ≤ b := by
  have : NeZero P := ⟨by omega⟩
  obtain ⟨x₁, x₂, hx₁, hx₂, hx₁1, hx₂1, hxw⟩ := hX P hP
  have hu : (1 / 2 : ℝ) ^ P ≤ 1 / 8 := by
    calc (1 / 2 : ℝ) ^ P ≤ (1 / 2 : ℝ) ^ 3 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 8 := by norm_num
  have hx₁pos : 0 < x₁ := by
    rw [abs_of_pos hx0] at hxw
    nlinarith [mul_le_mul_of_nonneg_left hu hx0.le]
  unfold aprioriW0Pos
  simp only
  split_ifs with hlt
  · obtain ⟨c, hc, hc1, -⟩ := addCeiling_abs toVal_one' hx₁ P
    have hc0 : c ≠ 0 := by linarith
    obtain ⟨r, hr, hr1, -⟩ := divFloor_abs hx₁ hc hc0 P
    refine ⟨r, x₂, hr, hx₂, ?_, (lambertW0_le_self hx0.le).trans hx₂1⟩
    calc r ≤ x₁ / c := hr1
      _ ≤ x₁ / (1 + x₁) := div_le_div_of_nonneg_left hx₁pos.le (by linarith) hc1
      _ ≤ xv / (1 + xv) := by
          rw [div_le_div_iff₀ (by linarith) (by linarith)]
          nlinarith
      _ ≤ lambertW0 xv := div_one_add_le_lambertW0 hx0.le
  · rw [lt_eq_true_iff hx₁ toVal_three] at hlt
    push Not at hlt
    have hxe : Real.exp 1 ≤ xv := by linarith [Real.exp_one_lt_d9]
    have hl1 : 1 ≤ Real.log xv := by
      rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hxe
    obtain ⟨l₁, hl₁, hl₁1⟩ := lnFloor_le hx₁ hx₁pos P
    obtain ⟨l₂, hl₂, hl₂1⟩ := lnCeiling_ge hx₂ (by linarith) P
    have hl₁' : l₁ ≤ Real.log xv := hl₁1.trans (Real.log_le_log hx₁pos hx₁1)
    have hl₂' : Real.log xv ≤ l₂ := (Real.log_le_log hx0 hx₂1).trans hl₂1
    have hl₂pos : 0 < l₂ := by linarith
    obtain ⟨c, hc, hc1⟩ := lnCeiling_ge hl₂ hl₂pos P
    obtain ⟨a, ha, ha1, -⟩ := subFloor_le hl₁ hc P
    refine ⟨a, l₂, ha, hl₂, ?_, (lambertW0_le_log hxe).trans hl₂'⟩
    have hlog : Real.log (Real.log xv) ≤ c :=
      (Real.log_le_log (by linarith) hl₂').trans hc1
    linarith [log_sub_log_log_le_lambertW0 hxe]

/-- `aprioriW0Neg` encloses `W₀ x` for `−e⁻¹ < x < 0`, from an enclosure `0 < l ≤ q ≤ h`. -/
theorem aprioriW0Neg_spec {xv : ℝ} (hx1 : -Real.exp (-1) < xv) (hx0 : xv < 0)
    {qlo qhi : AzFloat} {l h : ℝ} (hlo : qlo.toVal = some (l : EReal))
    (hhi : qhi.toVal = some (h : EReal)) (hl0 : 0 < l) (hl : l ≤ 1 + Real.exp 1 * xv)
    (hh : 1 + Real.exp 1 * xv ≤ h) {P : ℕ} (hP : 64 ≤ P) :
    ∃ a b : ℝ, (aprioriW0Neg qlo qhi P).1.toVal = some (a : EReal) ∧
      (aprioriW0Neg qlo qhi P).2.toVal = some (b : EReal) ∧ a ≤ lambertW0 xv ∧
      lambertW0 xv ≤ b := by
  have : NeZero P := ⟨by omega⟩
  obtain ⟨c, d, hc, hd, hc1, hd1, -⟩ := expBracketAt_spec toVal_one' hP
  have he0 := Real.exp_pos 1
  have hd0 : 0 < d := lt_of_lt_of_le he0 hd1
  set q := 1 + Real.exp 1 * xv with hq
  have hq0 : 0 < q := lt_of_lt_of_le hl0 hl
  obtain ⟨hW1, hW2⟩ := lambertW0_branch_bounds hx1 hx0
  obtain ⟨hWm1, -⟩ := lambertW0_spec hx1.le
  have hWneg := lambertW0_neg hx1.le hx0
  unfold aprioriW0Neg
  simp only
  -- lower end
  obtain ⟨r₁, hr₁, hr₁f⟩ := divFloor_err (toVal_shiftLeft_one hlo) hd hd0 (by linarith) P
  obtain ⟨r, hr, hrf⟩ := sqrtFloor_err hr₁ hr₁f.nonneg P
  obtain ⟨a', ha', ha'1, -⟩ := addFloor_abs toVal_neg_one hr P
  -- upper end
  obtain ⟨s, hs, hsc⟩ := sqrtCeiling_err (toVal_shiftLeft_one hhi) (by linarith) P
  obtain ⟨b', hb', hb'1, -⟩ := addCeiling_abs toVal_neg_one hs P
  refine ⟨max (-1) a', min 0 b', toVal_maxOf toVal_neg_one ha', toVal_minOf toVal_zero' hb',
    ?_, ?_⟩
  · apply max_le hWm1
    have h1 : 2 * l / d ≤ 2 * q / Real.exp 1 := by
      calc 2 * l / d ≤ 2 * l / Real.exp 1 :=
            div_le_div_of_nonneg_left (by linarith) he0 hd1
        _ ≤ 2 * q / Real.exp 1 := div_le_div_of_nonneg_right (by linarith) he0.le
    have h2 : r ≤ √(2 * q / Real.exp 1) :=
      hrf.le.trans ((Real.sqrt_le_sqrt hr₁f.le).trans (Real.sqrt_le_sqrt h1))
    linarith
  · apply le_min hWneg.le
    have h1 : √(2 * q) ≤ s := (Real.sqrt_le_sqrt (by linarith)).trans hsc.ge
    linarith

/-- `aprioriWm1` encloses `W₋₁ x` for `−e⁻¹ < x < 0`, from an enclosure `0 < l ≤ q ≤ h`. -/
theorem aprioriWm1_spec {xAt : ℕ → AzFloat × AzFloat} {xv : ℝ} (hX : XEncl xAt xv)
    (hx1 : -Real.exp (-1) < xv) (hx0 : xv < 0)
    {qlo qhi : AzFloat} {l h : ℝ} (hlo : qlo.toVal = some (l : EReal))
    (hhi : qhi.toVal = some (h : EReal)) (hl0 : 0 < l) (hl : l ≤ 1 + Real.exp 1 * xv)
    (hh : 1 + Real.exp 1 * xv ≤ h) {P : ℕ} (hP : 64 ≤ P) :
    ∃ a b : ℝ, (aprioriWm1 xAt qlo qhi P).1.toVal = some (a : EReal) ∧
      (aprioriWm1 xAt qlo qhi P).2.toVal = some (b : EReal) ∧ a ≤ lambertWm1 xv ∧
      lambertWm1 xv ≤ b := by
  have : NeZero P := ⟨by omega⟩
  obtain ⟨x₁, x₂, hx₁, hx₂, hx₁1, hx₂1, hxw⟩ := hX P hP
  have hu : (1 / 2 : ℝ) ^ P ≤ 1 / 8 := by
    calc (1 / 2 : ℝ) ^ P ≤ (1 / 2 : ℝ) ^ 3 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 8 := by norm_num
  have hx₂neg : x₂ < 0 := by
    rw [abs_of_neg hx0] at hxw
    nlinarith [mul_le_mul_of_nonneg_left hu (by linarith : (0:ℝ) ≤ -xv)]
  obtain ⟨c, d, hc, hd, hc1, hd1, -⟩ := expBracketAt_spec toVal_one' hP
  have he0 := Real.exp_pos 1
  have hd0 : 0 < d := lt_of_lt_of_le he0 hd1
  set q := 1 + Real.exp 1 * xv with hq
  have hq0 : 0 < q := lt_of_lt_of_le hl0 hl
  obtain ⟨hWm1, -⟩ := lambertWm1_spec hx1.le hx0
  unfold aprioriWm1
  simp only
  -- upper end
  obtain ⟨s, hs, hsf⟩ := sqrtFloor_err (toVal_shiftLeft_one hlo) (by linarith) P
  obtain ⟨b', hb', hb'1, -⟩ := subCeiling_abs toVal_neg_one hs P
  have hb : lambertWm1 xv ≤ min (-1) b' := by
    apply le_min hWm1
    have h1 : s ≤ √(2 * q) := hsf.le.trans (Real.sqrt_le_sqrt (by linarith))
    linarith [lambertWm1_le_branch hx1 hx0]
  split_ifs with hle
  · -- the branch-point bound
    rw [le_eq_true_iff hhi (toVal_powerOf2 _), AzInt.toInt_ofInt] at hle
    norm_num at hle
    have hq4 : q ≤ 1 / 4 := by linarith
    have h2dh : 0 ≤ 2 * d * h := mul_nonneg (by linarith) (by linarith)
    obtain ⟨m, hm, hmc⟩ := mulCeiling_err (toVal_shiftLeft_one hd) hhi P h2dh
    obtain ⟨t, ht, htc⟩ := sqrtCeiling_err hm (h2dh.trans hmc.ge) P
    obtain ⟨a, ha, ha1, -⟩ := subFloor_le toVal_neg_one ht P
    refine ⟨a, min (-1) b', ha, toVal_minOf toVal_neg_one hb', ?_, hb⟩
    have h1 : 2 * Real.exp 1 * q ≤ 2 * d * h := by
      have := mul_le_mul hd1 hh hq0.le hd0.le
      nlinarith
    have h2 : √(2 * Real.exp 1 * q) ≤ t :=
      (Real.sqrt_le_sqrt h1).trans ((Real.sqrt_le_sqrt hmc.ge).trans htc.ge)
    linarith [branch_le_lambertWm1 hx1 hx0 hq4]
  · -- the logarithmic bound, from `ln(−x₂) ≤ ln(−x)`
    have hnx : (-(xAt P).2).toVal = some ((-x₂ : ℝ) : EReal) := by
      rw [toVal_neg, hx₂, Option.map_some, EReal.coe_neg]
    have hypos : 0 < -x₂ := by linarith
    have hylt : Real.log (-xv) < -1 := by
      have := Real.log_lt_log (by linarith) (by linarith : -xv < Real.exp (-1))
      rwa [Real.log_exp] at this
    unfold lnBounds
    obtain ⟨l₁, hl₁, hl₁1⟩ := lnFloor_le hnx hypos P
    have hl₁1' : l₁ ≤ Real.log (-xv) := hl₁1.trans (Real.log_le_log hypos (by linarith))
    obtain ⟨l₂, hl₂, -⟩ := lnCeiling_ge hnx hypos P
    have hv : (-(lnPrecRound (-(xAt P).2) P .Floor).1).toVal = some ((-l₁ : ℝ) : EReal) := by
      rw [toVal_neg, hl₁, Option.map_some, EReal.coe_neg]
    have hvpos : 0 < -l₁ := by linarith
    obtain ⟨c', hc', hc'1⟩ := lnCeiling_ge hv hvpos P
    obtain ⟨a₁, ha₁, ha₁1, -⟩ := subFloor_le hl₁ hc' P
    obtain ⟨a, ha, ha1, -⟩ := subFloor_le ha₁ toVal_one' P
    refine ⟨a, min (-1) b', ha, toVal_minOf toVal_neg_one hb', ?_, hb⟩
    have hlog : Real.log (-Real.log (-xv)) ≤ c' :=
      (Real.log_le_log (by linarith) (by linarith)).trans hc'1
    linarith [log_sub_log_sub_one_le_lambertWm1 hx1 hx0]

/-! ### The mean-value rounds -/

/-- `mvtDelta X F P ≥ |x − g|` for any `x` enclosed by `X` and `g` enclosed by `F`. -/
theorem mvtDelta_spec {X : AzFloat × AzFloat} {xlo xhi xv : ℝ}
    (hxlo : X.1.toVal = some (xlo : EReal)) (hxhi : X.2.toVal = some (xhi : EReal))
    (hx1 : xlo ≤ xv) (hx2 : xv ≤ xhi)
    {F : AzFloat × AzFloat} {lo hi g : ℝ} (hlo : F.1.toVal = some (lo : EReal))
    (hhi : F.2.toVal = some (hi : EReal)) (h1 : lo ≤ g) (h2 : g ≤ hi) (P : ℕ) [NeZero P] :
    ∃ δ : ℝ, (mvtDelta X F P).toVal = some (δ : EReal) ∧ |xv - g| ≤ δ := by
  obtain ⟨d₁, hd₁, hd₁1, -⟩ := subCeiling_abs hhi hxlo P
  obtain ⟨d₂, hd₂, hd₂1, -⟩ := subCeiling_abs hxhi hlo P
  refine ⟨max d₁ d₂, toVal_maxOf hd₁ hd₂, ?_⟩
  rw [abs_le]
  constructor
  · linarith [le_max_left d₁ d₂]
  · linarith [le_max_right d₁ d₂]

/-- `derivLowerExp a n elo0` is a nonnegative lower bound of `eᵃ` when `0 ≤ elo0 ≤ eⁿ`. -/
theorem derivLowerExp_spec {a n elo0 : AzFloat} {av nv el : ℝ} (ha : a.toVal = some (av : EReal))
    (hn : n.toVal = some (nv : EReal)) (hel : elo0.toVal = some (el : EReal)) (hel0 : 0 ≤ el)
    (hel1 : el ≤ Real.exp nv) :
    ∃ v : ℝ, (derivLowerExp a n elo0).toVal = some (v : EReal) ∧ 0 ≤ v ∧ v ≤ Real.exp av := by
  unfold derivLowerExp
  simp only
  obtain ⟨c, hc, hc1, -⟩ := subFloor_le ha hn 64
  obtain ⟨c1, hc1', hc1'1, -⟩ := addFloor_abs hc toVal_one' 64
  split_ifs with hpos
  · rw [lt_eq_true_iff toVal_zero' hc1'] at hpos
    obtain ⟨v, hv, hvf⟩ := mulFloor_err hel hc1' 64 (mul_nonneg hel0 hpos.le)
    refine ⟨v, hv, hvf.nonneg, hvf.le.trans ?_⟩
    have h1 : c1 ≤ Real.exp (av - nv) := by
      have := Real.add_one_le_exp (av - nv); linarith
    calc el * c1 ≤ Real.exp nv * Real.exp (av - nv) :=
          mul_le_mul hel1 h1 hpos.le (Real.exp_pos _).le
      _ = Real.exp av := by rw [← Real.exp_add]; ring_nf
  · obtain ⟨el', eh, hel', -, hel'0, hel'1, -⟩ := encloses0_exp ha (le_refl 64)
    exact ⟨el', hel', hel'0, hel'1⟩

/-- One mean-value round for `W₀` keeps the root and the candidate, inside the old interval. -/
theorem mvtRound_spec_W0 {n elo0 δ : AzFloat} {xv nv el δv : ℝ}
    (hn : n.toVal = some (nv : EReal)) (hel : elo0.toVal = some (el : EReal)) (hel0 : 0 ≤ el)
    (hel1 : el ≤ Real.exp nv) (hδ : δ.toVal = some (δv : EReal))
    (hδv : |xv - nv * Real.exp nv| ≤ δv)
    {I : AzFloat × AzFloat} {a b : ℝ} (ha : I.1.toVal = some (a : EReal))
    (hb : I.2.toVal = some (b : EReal)) {W : ℝ} (hWx : W * Real.exp W = xv) (haW : a ≤ W)
    (hWb : W ≤ b) (han : a ≤ nv) (hnb : nv ≤ b) (P : ℕ) [NeZero P] :
    ∃ a' b' : ℝ, (mvtRound true n elo0 δ I P).1.toVal = some (a' : EReal) ∧
      (mvtRound true n elo0 δ I P).2.toVal = some (b' : EReal) ∧ a ≤ a' ∧ a' ≤ W ∧ W ≤ b' ∧
      b' ≤ b ∧ a' ≤ nv ∧ nv ≤ b' := by
  have hδ0 : 0 ≤ δv := (abs_nonneg _).trans hδv
  unfold mvtRound
  simp only [↓reduceIte]
  obtain ⟨dist, hdist, hdist1, -⟩ := addFloor_abs ha toVal_one' 64
  obtain ⟨el', hel', hel'0, hel'1⟩ := derivLowerExp_spec ha hn hel hel0 hel1
  split_ifs with h1 h2
  · rw [lt_eq_true_iff toVal_zero' hdist] at h1
    have ha1 : -1 < a := by linarith
    obtain ⟨D, hD, hDf⟩ := mulFloor_err hdist hel' 64 (mul_nonneg h1.le hel'0)
    rw [lt_eq_true_iff toVal_zero' hD] at h2
    have hDle : D ≤ (1 + a) * Real.exp a :=
      hDf.le.trans (mul_le_mul (by linarith) hel'1 hel'0 (by linarith))
    obtain ⟨r, hr, hrc⟩ := divCeiling_err hδ hD h2 hδ0 P
    have hmvt := mul_abs_sub_le_abs_sub_mul_exp_W0 ha1 han haW hWx h2.le hDle
    have hWn : |W - nv| ≤ r := by
      have : |W - nv| ≤ δv / D := by
        rw [le_div_iff₀ h2]; linarith
      exact this.trans hrc.ge
    have hr0 : 0 ≤ r := (div_nonneg hδ0 h2.le).trans hrc.ge
    obtain ⟨a'', ha'', ha''1, -⟩ := subFloor_le hn hr P
    obtain ⟨b'', hb'', hb''1, -⟩ := addCeiling_abs hn hr P
    refine ⟨max a a'', min b b'', toVal_maxOf ha ha'', toVal_minOf hb hb'', le_max_left _ _,
      ?_, ?_, min_le_left _ _, ?_, ?_⟩
    · apply max_le haW
      have := abs_le.mp hWn
      linarith
    · apply le_min hWb
      have := abs_le.mp hWn
      linarith
    · exact max_le han (by linarith)
    · exact le_min hnb (by linarith)
  · exact ⟨a, b, ha, hb, le_rfl, haW, hWb, le_rfl, han, hnb⟩
  · exact ⟨a, b, ha, hb, le_rfl, haW, hWb, le_rfl, han, hnb⟩

/-- One mean-value round for `W₋₁`. -/
theorem mvtRound_spec_Wm1 {n elo0 δ : AzFloat} {xv nv el δv : ℝ}
    (hn : n.toVal = some (nv : EReal)) (hel : elo0.toVal = some (el : EReal)) (hel0 : 0 ≤ el)
    (hel1 : el ≤ Real.exp nv) (hδ : δ.toVal = some (δv : EReal))
    (hδv : |xv - nv * Real.exp nv| ≤ δv)
    {I : AzFloat × AzFloat} {a b : ℝ} (ha : I.1.toVal = some (a : EReal))
    (hb : I.2.toVal = some (b : EReal)) {W : ℝ} (hWx : W * Real.exp W = xv) (haW : a ≤ W)
    (hWb : W ≤ b) (han : a ≤ nv) (hnb : nv ≤ b) (P : ℕ) [NeZero P] :
    ∃ a' b' : ℝ, (mvtRound false n elo0 δ I P).1.toVal = some (a' : EReal) ∧
      (mvtRound false n elo0 δ I P).2.toVal = some (b' : EReal) ∧ a ≤ a' ∧ a' ≤ W ∧ W ≤ b' ∧
      b' ≤ b ∧ a' ≤ nv ∧ nv ≤ b' := by
  have hδ0 : 0 ≤ δv := (abs_nonneg _).trans hδv
  unfold mvtRound
  simp only [Bool.false_eq_true, ↓reduceIte]
  obtain ⟨dist, hdist, hdist1, -⟩ := subFloor_le toVal_neg_one hb 64
  obtain ⟨el', hel', hel'0, hel'1⟩ := derivLowerExp_spec ha hn hel hel0 hel1
  split_ifs with h1 h2
  · rw [lt_eq_true_iff toVal_zero' hdist] at h1
    have hb1 : b < -1 := by linarith
    obtain ⟨D, hD, hDf⟩ := mulFloor_err hdist hel' 64 (mul_nonneg h1.le hel'0)
    rw [lt_eq_true_iff toVal_zero' hD] at h2
    have hDle : D ≤ (-1 - b) * Real.exp a :=
      hDf.le.trans (mul_le_mul (by linarith) hel'1 hel'0 (by linarith))
    obtain ⟨r, hr, hrc⟩ := divCeiling_err hδ hD h2 hδ0 P
    have hmvt := mul_abs_sub_le_abs_sub_mul_exp_Wm1 hb1 han hnb haW hWb hWx h2.le hDle
    have hWn : |W - nv| ≤ r := by
      have : |W - nv| ≤ δv / D := by
        rw [le_div_iff₀ h2]; linarith
      exact this.trans hrc.ge
    have hr0 : 0 ≤ r := (div_nonneg hδ0 h2.le).trans hrc.ge
    obtain ⟨a'', ha'', ha''1, -⟩ := subFloor_le hn hr P
    obtain ⟨b'', hb'', hb''1, -⟩ := addCeiling_abs hn hr P
    refine ⟨max a a'', min b b'', toVal_maxOf ha ha'', toVal_minOf hb hb'', le_max_left _ _,
      ?_, ?_, min_le_left _ _, ?_, ?_⟩
    · apply max_le haW
      have := abs_le.mp hWn
      linarith
    · apply le_min hWb
      have := abs_le.mp hWn
      linarith
    · exact max_le han (by linarith)
    · exact le_min hnb (by linarith)
  · exact ⟨a, b, ha, hb, le_rfl, haW, hWb, le_rfl, han, hnb⟩
  · exact ⟨a, b, ha, hb, le_rfl, haW, hWb, le_rfl, han, hnb⟩

/-- One mean-value round, either branch. -/
theorem mvtRound_spec (branch0 : Bool) {n elo0 δ : AzFloat} {xv nv el δv : ℝ}
    (hn : n.toVal = some (nv : EReal)) (hel : elo0.toVal = some (el : EReal)) (hel0 : 0 ≤ el)
    (hel1 : el ≤ Real.exp nv) (hδ : δ.toVal = some (δv : EReal))
    (hδv : |xv - nv * Real.exp nv| ≤ δv) {I : AzFloat × AzFloat} {a b : ℝ}
    (ha : I.1.toVal = some (a : EReal)) (hb : I.2.toVal = some (b : EReal)) {W : ℝ}
    (hWx : W * Real.exp W = xv) (haW : a ≤ W) (hWb : W ≤ b) (han : a ≤ nv) (hnb : nv ≤ b)
    (P : ℕ) [NeZero P] :
    ∃ a' b' : ℝ, (mvtRound branch0 n elo0 δ I P).1.toVal = some (a' : EReal) ∧
      (mvtRound branch0 n elo0 δ I P).2.toVal = some (b' : EReal) ∧ a ≤ a' ∧ a' ≤ W ∧ W ≤ b' ∧
      b' ≤ b ∧ a' ≤ nv ∧ nv ≤ b' := by
  cases branch0
  · exact mvtRound_spec_Wm1 hn hel hel0 hel1 hδ hδv ha hb hWx haW hWb han hnb P
  · exact mvtRound_spec_W0 hn hel hel0 hel1 hδ hδv ha hb hWx haW hWb han hnb P

/-- The three rounds keep the root inside the old interval. -/
theorem mvtRounds_spec (branch0 : Bool) {xAt : ℕ → AzFloat × AzFloat} {n : AzFloat} {xv nv : ℝ}
    (hX : XEncl xAt xv) (hn : n.toVal = some (nv : EReal))
    {I₀ : AzFloat × AzFloat} {a₀ b₀ : ℝ} (ha₀ : I₀.1.toVal = some (a₀ : EReal))
    (hb₀ : I₀.2.toVal = some (b₀ : EReal)) {W : ℝ} (hWx : W * Real.exp W = xv) (haW : a₀ ≤ W)
    (hWb : W ≤ b₀) (han : a₀ ≤ nv) (hnb : nv ≤ b₀) {P : ℕ} (hP : 64 ≤ P) :
    ∃ a b : ℝ, (mvtRounds branch0 xAt n I₀ P).1.toVal = some (a : EReal) ∧
      (mvtRounds branch0 xAt n I₀ P).2.toVal = some (b : EReal) ∧ a₀ ≤ a ∧ a ≤ W ∧ W ≤ b ∧
      b ≤ b₀ := by
  have : NeZero P := ⟨by omega⟩
  obtain ⟨xlo, xhi, hxlo, hxhi, hx1, hx2, -⟩ := hX P hP
  obtain ⟨c, d, hc, hd, hc1, hd1, -⟩ := expBracketAt_spec hn hP
  obtain ⟨el, hel, hel0, helle, -⟩ := clampNonneg_spec hc
  have hel1 : el ≤ Real.exp nv := helle.trans (max_le hc1 (Real.exp_pos nv).le)
  obtain ⟨lo, hi, hlo, hhi, h1, h2, -⟩ := mulBracketAny_spec hn hc hd hc1 hd1 P
  obtain ⟨δ, hδ, hδv⟩ := mvtDelta_spec hxlo hxhi hx1 hx2 hlo hhi h1 h2 P
  unfold mvtRounds
  simp only
  obtain ⟨a₁, b₁, ha₁, hb₁, h01, haW1, hWb1, hb01, han1, hnb1⟩ :=
    mvtRound_spec branch0 hn hel hel0 hel1 hδ hδv ha₀ hb₀ hWx haW hWb han hnb P
  obtain ⟨a₂, b₂, ha₂, hb₂, h12, haW2, hWb2, hb12, han2, hnb2⟩ :=
    mvtRound_spec branch0 hn hel hel0 hel1 hδ hδv ha₁ hb₁ hWx haW1 hWb1 han1 hnb1 P
  obtain ⟨a₃, b₃, ha₃, hb₃, h23, haW3, hWb3, hb23, -, -⟩ :=
    mvtRound_spec branch0 hn hel hel0 hel1 hδ hδv ha₂ hb₂ hWx haW2 hWb2 han2 hnb2 P
  exact ⟨a₃, b₃, ha₃, hb₃, by linarith, haW3, hWb3, by linarith⟩

/-! ### The grid bisection -/

/-- The real value of a grid point `M · 2^e`. -/
noncomputable def gridVal (M e : AzInt) : ℝ := (M.toInt : ℝ) * (2 : ℝ) ^ e.toInt

theorem toVal_gridPoint (M e : AzInt) :
    (ofAzInt M <<< e).toVal = some ((gridVal M e : ℝ) : EReal) :=
  toVal_shiftLeft_of_toVal (toVal_ofAzInt M) e

/-- The invariant of the grid bisection: the root lies in `[A, B] · 2^e`, and the whole
interval lies in the monotone region of the branch. -/
def GridInv (branch0 : Bool) (W : ℝ) (s : AzInt × AzInt × AzInt) : Prop :=
  gridVal s.1 s.2.2 ≤ W ∧ W ≤ gridVal s.2.1 s.2.2 ∧
    (branch0 = true → -1 ≤ gridVal s.1 s.2.2) ∧ (branch0 = false → gridVal s.2.1 s.2.2 ≤ -1)

/-- The width of a grid interval. -/
noncomputable def gridWidth (s : AzInt × AzInt × AzInt) : ℝ :=
  gridVal s.2.1 s.2.2 - gridVal s.1 s.2.2

theorem toInt_shl1 (z : AzInt) : (z <<< 1).toInt = 2 * z.toInt := by
  show (AzInt.shiftLeft z 1).toInt = 2 * z.toInt
  rw [AzInt.toInt_shiftLeft]
  norm_num [mul_comm]

theorem gridVal_shiftLeft_sub_one (M e : AzInt) :
    gridVal (M <<< 1) (e - AzInt.ofInt 1) = gridVal M e := by
  unfold gridVal
  rw [toInt_shl1, AzInt.toInt_sub, AzInt.toInt_ofInt, zpow_sub_one₀ (by norm_num)]
  push_cast
  ring

theorem gridVal_strictMono {M N e : AzInt} (h : M.toInt < N.toInt) :
    gridVal M e < gridVal N e := by
  unfold gridVal
  exact mul_lt_mul_of_pos_right (by exact_mod_cast h) (by positivity)

theorem gridVal_mono {M N e : AzInt} (h : M.toInt ≤ N.toInt) : gridVal M e ≤ gridVal N e := by
  unfold gridVal
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast h) (by positivity)

/-- One bisection step keeps the invariant and shrinks the width by `3/4`. -/
theorem gridBisectStep_spec (branch0 : Bool) {xAt : ℕ → AzFloat × AzFloat} {xv : ℝ}
    (hX : XEncl xAt xv)
    (hs : ∀ M e : AzInt, ∃ k, (sideAt xAt (ofAzInt M <<< e) (64 * 2 ^ k)).isSome = true)
    {W : ℝ} (hWx : W * Real.exp W = xv) {A B e : AzInt} (hinv : GridInv branch0 W (A, B, e)) :
    GridInv branch0 W (gridBisectStep branch0 xAt hs A B e) ∧
      gridWidth (gridBisectStep branch0 xAt hs A B e) ≤ 3 / 4 * gridWidth (A, B, e) := by
  obtain ⟨hAW, hWB, hreg0, hreg1⟩ := hinv
  simp only at hAW hWB hreg0 hreg1
  -- the regrid
  obtain ⟨A', B', e', hA', hB', he', hval, hD⟩ : ∃ A' B' e' : AzInt,
      gridVal A' e' = gridVal A e ∧ gridVal B' e' = gridVal B e ∧ True ∧
      (if B - A ≤ AzInt.ofInt 1 then (A <<< 1, B <<< 1, e - AzInt.ofInt 1) else (A, B, e))
        = (A', B', e') ∧ (B'.toInt - A'.toInt = 0 ∨ 2 ≤ B'.toInt - A'.toInt) := by
    have hAB : A.toInt ≤ B.toInt := by
      by_contra hlt
      push Not at hlt
      have := gridVal_strictMono (e := e) hlt
      linarith
    split_ifs with hle
    · refine ⟨A <<< 1, B <<< 1, e - AzInt.ofInt 1, gridVal_shiftLeft_sub_one A e,
        gridVal_shiftLeft_sub_one B e, trivial, rfl, ?_⟩
      rw [AzInt.le_iff_toInt_le, AzInt.toInt_sub, AzInt.toInt_ofInt] at hle
      rw [toInt_shl1, toInt_shl1]
      omega
    · refine ⟨A, B, e, rfl, rfl, trivial, rfl, ?_⟩
      rw [AzInt.le_iff_toInt_le, AzInt.toInt_sub, AzInt.toInt_ofInt] at hle
      omega
  unfold gridBisectStep
  simp only
  rw [hval]
  simp only
  set M := (A' + B').ediv (AzInt.ofInt 2) with hM
  have hMv : M.toInt = (A'.toInt + B'.toInt) / 2 := by
    rw [hM, AzInt.toInt_ediv, AzInt.toInt_add, AzInt.toInt_ofInt]
  have hA'B' : A'.toInt ≤ B'.toInt := by omega
  have hAM : A'.toInt ≤ M.toInt := by rw [hMv]; omega
  have hMB : M.toInt ≤ B'.toInt := by rw [hMv]; omega
  have hgA : gridVal A' e' ≤ gridVal M e' := gridVal_mono hAM
  have hgB : gridVal M e' ≤ gridVal B' e' := gridVal_mono hMB
  have hm : (ofAzInt M <<< e').toVal = some ((gridVal M e' : ℝ) : EReal) := toVal_gridPoint M e'
  -- the width of either half
  have hwidth : gridVal B' e' - gridVal M e' ≤ 3 / 4 * (gridVal B' e' - gridVal A' e') ∧
      gridVal M e' - gridVal A' e' ≤ 3 / 4 * (gridVal B' e' - gridVal A' e') := by
    unfold gridVal
    have h2 : (0 : ℝ) < (2 : ℝ) ^ e'.toInt := by positivity
    have hM1 : 2 * M.toInt ≤ A'.toInt + B'.toInt := by rw [hMv]; omega
    have hM2 : A'.toInt + B'.toInt - 1 ≤ 2 * M.toInt := by rw [hMv]; omega
    have hM1' : 2 * (M.toInt : ℝ) ≤ A'.toInt + B'.toInt := by exact_mod_cast hM1
    have hM2' : (A'.toInt : ℝ) + B'.toInt - 1 ≤ 2 * M.toInt := by exact_mod_cast hM2
    rcases hD with hD | hD
    · have : (B'.toInt : ℝ) = A'.toInt := by exact_mod_cast (by omega : B'.toInt = A'.toInt)
      have hM' : (M.toInt : ℝ) = A'.toInt := by exact_mod_cast (by omega : M.toInt = A'.toInt)
      rw [this, hM']
      constructor <;> nlinarith
    · have hD' : (2 : ℝ) ≤ B'.toInt - A'.toInt := by exact_mod_cast hD
      constructor
      · nlinarith
      · nlinarith
  have hWm1 : branch0 = true → -1 ≤ gridVal M e' := fun hb => by
    have := hreg0 hb; rw [← hA'] at this; exact this.trans hgA
  have hWm1' : branch0 = false → gridVal M e' ≤ -1 := fun hb => by
    have := hreg1 hb; rw [← hB'] at this; exact hgB.trans this
  rw [← hA'] at hAW hreg0
  rw [← hB'] at hWB hreg1
  -- the side of `M 2^e'`
  cases hside : sideOf xAt (ofAzInt M <<< e') (hs M e') with
  | true =>
    have hlt := sideOf_true hX hm (hs M e') hside
    cases branch0 with
    | true =>
      -- increasing branch: `g(m) < g(W)` gives `m < W`
      simp only [beq_iff_eq, ↓reduceIte]
      have hmW : gridVal M e' < W := by
        by_contra hge
        push Not at hge
        have := strictMonoOn_mul_exp.monotoneOn (by simp; linarith [hreg0 rfl])
          (by simp; exact hWm1 rfl) hge
        rw [hWx] at this
        linarith
      refine ⟨⟨hmW.le, hWB, fun _ => hWm1 rfl, fun h => (Bool.false_ne_true h.symm).elim⟩, ?_⟩
      unfold gridWidth
      try simp only
      linarith [hwidth.1]
    | false =>
      -- decreasing branch: `g(m) < g(W)` gives `W < m`
      simp only [beq_iff_eq, Bool.true_eq_false, ↓reduceIte]
      have hWm : W < gridVal M e' := by
        by_contra hge
        push Not at hge
        have := strictAntiOn_mul_exp.antitoneOn (by simp; exact hWm1' rfl)
          (by simp; linarith [hreg1 rfl]) hge
        rw [hWx] at this
        linarith
      refine ⟨⟨hAW, hWm.le, fun h => (Bool.false_ne_true h).elim, fun _ => hWm1' rfl⟩, ?_⟩
      unfold gridWidth
      try simp only
      linarith [hwidth.2]
  | false =>
    have hgt := sideOf_false hX hm (hs M e') hside
    cases branch0 with
    | true =>
      simp only [beq_iff_eq, Bool.false_eq_true, ↓reduceIte]
      have hWm : W < gridVal M e' := by
        by_contra hge
        push Not at hge
        have := strictMonoOn_mul_exp.monotoneOn (by simp; exact hWm1 rfl)
          (by simp; linarith [hreg0 rfl]) hge
        rw [hWx] at this
        linarith
      refine ⟨⟨hAW, hWm.le, fun _ => hreg0 rfl, fun h => (Bool.false_ne_true h.symm).elim⟩, ?_⟩
      unfold gridWidth
      try simp only
      linarith [hwidth.2]
    | false =>
      simp only [beq_iff_eq, ↓reduceIte]
      have hmW : gridVal M e' < W := by
        by_contra hge
        push Not at hge
        have := strictAntiOn_mul_exp.antitoneOn (by simp; linarith [hreg1 rfl])
          (by simp; exact hWm1' rfl) hge
        rw [hWx] at this
        linarith
      refine ⟨⟨hmW.le, hWB, fun h => (Bool.false_ne_true h).elim, fun _ => hreg1 rfl⟩, ?_⟩
      unfold gridWidth
      try simp only
      linarith [hwidth.1]

/-- `k` bisection steps keep the invariant and shrink the width by `(3/4)^k`. -/
theorem bisectGrid_spec (branch0 : Bool) {xAt : ℕ → AzFloat × AzFloat} {xv : ℝ}
    (hX : XEncl xAt xv)
    (hs : ∀ M e : AzInt, ∃ k, (sideAt xAt (ofAzInt M <<< e) (64 * 2 ^ k)).isSome = true)
    {W : ℝ} (hWx : W * Real.exp W = xv) :
    ∀ (k : ℕ) (s : AzInt × AzInt × AzInt), GridInv branch0 W s →
      GridInv branch0 W (bisectGrid branch0 xAt hs k s) ∧
        gridWidth (bisectGrid branch0 xAt hs k s) ≤ (3 / 4 : ℝ) ^ k * gridWidth s := by
  intro k
  induction k with
  | zero => intro s hs'; exact ⟨hs', by simp only [bisectGrid, pow_zero, one_mul]; exact le_rfl⟩
  | succ k ih =>
    rintro ⟨A, B, e⟩ hinv
    obtain ⟨hinv', hw⟩ := gridBisectStep_spec branch0 hX hs hWx hinv
    obtain ⟨hinv'', hw'⟩ := ih _ hinv'
    refine ⟨hinv'', ?_⟩
    calc gridWidth (bisectGrid branch0 xAt hs k (gridBisectStep branch0 xAt hs A B e))
        ≤ (3 / 4 : ℝ) ^ k * gridWidth (gridBisectStep branch0 xAt hs A B e) := hw'
      _ ≤ (3 / 4 : ℝ) ^ k * (3 / 4 * gridWidth (A, B, e)) :=
          mul_le_mul_of_nonneg_left hw (by positivity)
      _ = (3 / 4 : ℝ) ^ (k + 1) * gridWidth (A, B, e) := by ring

/-! ### The grid of the a priori interval -/

theorem toInt_neg_ofInt_one : (-AzInt.ofInt 1).toInt = -1 := by
  rw [AzInt.toInt_neg, AzInt.toInt_ofInt]

theorem gridVal_zero_exp (M : AzInt) : gridVal M 0 = M.toInt := by
  unfold gridVal
  rw [AzInt.toInt_zero, zpow_zero, mul_one]

/-- `gridOf` encloses the root in the monotone region, with width at most `b − a + 4`. -/
theorem gridOf_spec (branch0 : Bool) {I : AzFloat × AzFloat} {a b : ℝ}
    (ha : I.1.toVal = some (a : EReal)) (hb : I.2.toVal = some (b : EReal)) {W : ℝ}
    (haW : a ≤ W) (hWb : W ≤ b) (hbr : (branch0 = true → -1 ≤ W) ∧ (branch0 = false → W ≤ -1)) :
    GridInv branch0 W (gridOf branch0 I) ∧ gridWidth (gridOf branch0 I) ≤ b - a + 4 := by
  obtain ⟨hta, -⟩ := truncToAzInt_spec ha
  obtain ⟨htb, -⟩ := truncToAzInt_spec hb
  obtain ⟨hta1, hta2⟩ := abs_lt.mp hta
  obtain ⟨htb1, htb2⟩ := abs_lt.mp htb
  unfold gridOf
  simp only
  set A := truncToAzInt I.1 - AzInt.ofInt 1 with hA
  set B := truncToAzInt I.2 + AzInt.ofInt 1 with hB
  have hAv : (A.toInt : ℝ) = (truncToAzInt I.1).toInt - 1 := by
    rw [hA, AzInt.toInt_sub, AzInt.toInt_ofInt]; push_cast; ring
  have hBv : (B.toInt : ℝ) = (truncToAzInt I.2).toInt + 1 := by
    rw [hB, AzInt.toInt_add, AzInt.toInt_ofInt]; push_cast; ring
  have hAa : (A.toInt : ℝ) ≤ a := by rw [hAv]; linarith
  have hBb : b ≤ B.toInt := by rw [hBv]; linarith
  have hAa' : a - 2 ≤ A.toInt := by rw [hAv]; linarith
  have hBb' : (B.toInt : ℝ) ≤ b + 2 := by rw [hBv]; linarith
  cases branch0 with
  | true =>
    simp only [↓reduceIte]
    split_ifs with hc
    · rw [AzInt.le_iff_toInt_le, toInt_neg_ofInt_one] at hc
      have hc' : (A.toInt : ℝ) ≤ -1 := by exact_mod_cast hc
      refine ⟨⟨?_, ?_, fun _ => ?_, fun h => (Bool.false_ne_true h.symm).elim⟩, ?_⟩
      · simp only [gridVal_zero_exp, toInt_neg_ofInt_one]; push_cast; exact hbr.1 rfl
      · simp only [gridVal_zero_exp]; linarith
      · simp only [gridVal_zero_exp, toInt_neg_ofInt_one]; push_cast; exact le_rfl
      · unfold gridWidth; simp only [gridVal_zero_exp, toInt_neg_ofInt_one]; push_cast; linarith
    · rw [AzInt.le_iff_toInt_le, toInt_neg_ofInt_one] at hc
      push Not at hc
      have hc' : (-1 : ℝ) < A.toInt := by exact_mod_cast hc
      refine ⟨⟨?_, ?_, fun _ => ?_, fun h => (Bool.false_ne_true h.symm).elim⟩, ?_⟩
      · simp only [gridVal_zero_exp]; linarith
      · simp only [gridVal_zero_exp]; linarith
      · simp only [gridVal_zero_exp]; linarith
      · unfold gridWidth; simp only [gridVal_zero_exp]; linarith
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    split_ifs with hc
    · rw [AzInt.le_iff_toInt_le, toInt_neg_ofInt_one] at hc
      have hc' : (-1 : ℝ) ≤ B.toInt := by exact_mod_cast hc
      refine ⟨⟨?_, ?_, fun h => (Bool.false_ne_true h).elim, fun _ => ?_⟩, ?_⟩
      · simp only [gridVal_zero_exp]; linarith
      · simp only [gridVal_zero_exp, toInt_neg_ofInt_one]; push_cast; exact hbr.2 rfl
      · simp only [gridVal_zero_exp, toInt_neg_ofInt_one]; push_cast; exact le_rfl
      · unfold gridWidth; simp only [gridVal_zero_exp, toInt_neg_ofInt_one]; push_cast; linarith
    · rw [AzInt.le_iff_toInt_le, toInt_neg_ofInt_one] at hc
      push Not at hc
      have hc' : (B.toInt : ℝ) < -1 := by exact_mod_cast hc
      refine ⟨⟨?_, ?_, fun h => (Bool.false_ne_true h).elim, fun _ => ?_⟩, ?_⟩
      · simp only [gridVal_zero_exp]; linarith
      · simp only [gridVal_zero_exp]; linarith
      · simp only [gridVal_zero_exp]; linarith
      · unfold gridWidth; simp only [gridVal_zero_exp]; linarith

theorem gridFloats_spec (s : AzInt × AzInt × AzInt) :
    (gridFloats s).1.toVal = some ((gridVal s.1 s.2.2 : ℝ) : EReal) ∧
      (gridFloats s).2.toVal = some ((gridVal s.2.1 s.2.2 : ℝ) : EReal) :=
  ⟨toVal_gridPoint _ _, toVal_gridPoint _ _⟩

/-! ### The candidate and the target -/

/-- The clamped candidate lies in `[a, b]`. -/
theorem clampInto_spec {I : AzFloat × AzFloat} {a b : ℝ} (ha : I.1.toVal = some (a : EReal))
    (hb : I.2.toVal = some (b : EReal)) (hab : a ≤ b) (n : AzFloat) :
    ∃ nv : ℝ, (clampInto I n).toVal = some (nv : EReal) ∧ a ≤ nv ∧ nv ≤ b := by
  unfold clampInto
  cases n with
  | finite s e q m hv =>
    refine ⟨max a (min b (finiteVal s e m)),
      toVal_maxOf ha (toVal_minOf hb (toVal_finite s e q m hv)), le_max_left _ _,
      max_le hab (min_le_left _ _)⟩
  | zero =>
    refine ⟨max a (min b 0), toVal_maxOf ha (toVal_minOf hb toVal_zero'), le_max_left _ _,
      max_le hab (min_le_left _ _)⟩
  | nan => exact ⟨a, ha, le_rfl, hab⟩
  | infinity s => exact ⟨a, ha, le_rfl, hab⟩

theorem halleyCandidate_spec (branch0 : Bool) (xAt : ℕ → AzFloat × AzFloat)
    (qE : Option (AzFloat × AzFloat))
    {I₀ : AzFloat × AzFloat} {a₀ b₀ : ℝ} (ha₀ : I₀.1.toVal = some (a₀ : EReal))
    (hb₀ : I₀.2.toVal = some (b₀ : EReal)) (hab : a₀ ≤ b₀) (W : ℕ) :
    ∃ nv : ℝ, (halleyCandidate branch0 xAt qE I₀ W).toVal = some (nv : EReal) ∧ a₀ ≤ nv ∧
      nv ≤ b₀ := by
  unfold halleyCandidate
  simp only
  exact clampInto_spec ha₀ hb₀ hab _

theorem toVal_lambertTarget {I₀ : AzFloat × AzFloat} {a₀ b₀ : ℝ}
    (ha₀ : I₀.1.toVal = some (a₀ : EReal)) (hb₀ : I₀.2.toVal = some (b₀ : EReal)) (w : ℕ) :
    (lambertTarget I₀ w).toVal
      = some ((max |a₀| |b₀| * (1 / 2 : ℝ) ^ (w + 1) : ℝ) : EReal) := by
  unfold lambertTarget
  have hna : (-I₀.1).toVal = some ((-a₀ : ℝ) : EReal) := by
    rw [toVal_neg, ha₀, Option.map_some, EReal.coe_neg]
  have hnb : (-I₀.2).toVal = some ((-b₀ : ℝ) : EReal) := by
    rw [toVal_neg, hb₀, Option.map_some, EReal.coe_neg]
  rw [toVal_shiftLeft_of_toVal (toVal_maxOf (toVal_maxOf ha₀ hna) (toVal_maxOf hb₀ hnb)),
    AzInt.toInt_neg, AzNat.toInt_toAzInt, AzNat.toNat_ofNat, zpow_neg, zpow_natCast, one_div_pow,
    one_div, abs_eq_max_neg, abs_eq_max_neg]

/-! ### The bracket at a Ziv level -/

/-- The width bound of `lambertBracket` at level `w`. -/
noncomputable def lambertEps (a₀ b₀ : ℝ) (qE : Option (AzFloat × AzFloat)) (w : ℕ) : ℝ :=
  max (max |a₀| |b₀| * (1 / 2 : ℝ) ^ (w + 1))
    ((3 / 4 : ℝ) ^ (3 * lambertWork qE w + 8) * (b₀ - a₀ + 4))

theorem tendsto_lambertEps (a₀ b₀ : ℝ) (qE : Option (AzFloat × AzFloat)) (hab : a₀ ≤ b₀) :
    Filter.Tendsto (lambertEps a₀ b₀ qE) Filter.atTop (nhds 0) := by
  have hM : 0 ≤ max |a₀| |b₀| := le_max_of_le_left (abs_nonneg _)
  have hC : 0 ≤ b₀ - a₀ + 4 := by linarith
  have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (max |a₀| |b₀|)
  have h2 := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 3 / 4)
    (by norm_num : (3 / 4 : ℝ) < 1)).const_mul (b₀ - a₀ + 4)
  simp only [mul_zero] at h1 h2
  have h3 := h1.add h2
  rw [add_zero] at h3
  refine squeeze_zero (fun w => ?_) (fun w => ?_) h3
  · unfold lambertEps; positivity
  · unfold lambertEps
    apply max_le
    · have : (1 / 2 : ℝ) ^ (w + 1) ≤ (1 / 2 : ℝ) ^ w :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      nlinarith [mul_nonneg hC (pow_nonneg (by norm_num : (0:ℝ) ≤ 3 / 4) w)]
    · have : (3 / 4 : ℝ) ^ (3 * lambertWork qE w + 8) ≤ (3 / 4 : ℝ) ^ w :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by unfold lambertWork; omega)
      nlinarith [mul_nonneg hM (pow_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2) w)]

/-- `lambertBracket` encloses the root, with width at most `lambertEps a₀ b₀ qE w`. -/
theorem lambertBracket_spec (branch0 : Bool) {xAt : ℕ → AzFloat × AzFloat} {xv : ℝ}
    (hX : XEncl xAt xv)
    (qE : Option (AzFloat × AzFloat)) {I₀ : AzFloat × AzFloat} {a₀ b₀ : ℝ}
    (ha₀ : I₀.1.toVal = some (a₀ : EReal)) (hb₀ : I₀.2.toVal = some (b₀ : EReal)) {W : ℝ}
    (hWx : W * Real.exp W = xv) (haW : a₀ ≤ W) (hWb : W ≤ b₀)
    (hbr : (branch0 = true → -1 ≤ W) ∧ (branch0 = false → W ≤ -1))
    (hs : ∀ M e : AzInt, ∃ k, (sideAt xAt (ofAzInt M <<< e) (64 * 2 ^ k)).isSome = true) (w : ℕ) :
    ∃ lo hi : ℝ, (lambertBracket branch0 xAt qE I₀ hs w).1.toVal = some (lo : EReal) ∧
      (lambertBracket branch0 xAt qE I₀ hs w).2.toVal = some (hi : EReal) ∧ lo ≤ W ∧ W ≤ hi ∧
      hi - lo ≤ lambertEps a₀ b₀ qE w := by
  have hab : a₀ ≤ b₀ := haW.trans hWb
  have hP : 64 ≤ lambertWork qE w := by unfold lambertWork; omega
  unfold lambertBracket
  simp only
  set P := lambertWork qE w with hPdef
  obtain ⟨nv, hn, han, hnb⟩ := halleyCandidate_spec branch0 xAt qE ha₀ hb₀ hab P
  obtain ⟨a, b, ha, hb, h0a, haW', hWb', hbb0⟩ :=
    mvtRounds_spec branch0 hX hn ha₀ hb₀ hWx haW hWb han hnb hP
  obtain ⟨d, hd, hd1, -⟩ := subCeiling_abs hb ha 64
  split_ifs with hle
  · rw [le_eq_true_iff hd (toVal_lambertTarget ha₀ hb₀ w)] at hle
    refine ⟨a, b, ha, hb, haW', hWb', ?_⟩
    unfold lambertEps
    exact le_max_of_le_left (by linarith)
  · obtain ⟨hinv₀, hw₀⟩ := gridOf_spec branch0 ha₀ hb₀ haW hWb hbr
    obtain ⟨hinv, hw⟩ := bisectGrid_spec branch0 hX hs hWx (3 * P + 8) _ hinv₀
    obtain ⟨hlo, hhi⟩ := gridFloats_spec (bisectGrid branch0 xAt hs (3 * P + 8) (gridOf branch0 I₀))
    obtain ⟨hAW, hWB, -, -⟩ := hinv
    refine ⟨_, _, hlo, hhi, hAW, hWB, ?_⟩
    have hwid : gridWidth (bisectGrid branch0 xAt hs (3 * P + 8) (gridOf branch0 I₀))
        ≤ (3 / 4 : ℝ) ^ (3 * P + 8) * (b₀ - a₀ + 4) := by
      calc gridWidth (bisectGrid branch0 xAt hs (3 * P + 8) (gridOf branch0 I₀))
          ≤ (3 / 4 : ℝ) ^ (3 * P + 8) * gridWidth (gridOf branch0 I₀) := hw
        _ ≤ (3 / 4 : ℝ) ^ (3 * P + 8) * (b₀ - a₀ + 4) :=
            mul_le_mul_of_nonneg_left hw₀ (by positivity)
    unfold gridWidth at hwid
    unfold lambertEps
    rw [← hPdef]
    exact le_max_of_le_right hwid

/-- `lambertApprox` brackets the root by `Roundable`s. -/
theorem lambertApprox_spec (branch0 : Bool) {xAt : ℕ → AzFloat × AzFloat} {xv : ℝ}
    (hX : XEncl xAt xv)
    (qE : Option (AzFloat × AzFloat)) {I₀ : AzFloat × AzFloat} {a₀ b₀ : ℝ}
    (ha₀ : I₀.1.toVal = some (a₀ : EReal)) (hb₀ : I₀.2.toVal = some (b₀ : EReal)) {W : ℝ}
    (hWx : W * Real.exp W = xv) (haW : a₀ ≤ W) (hWb : W ≤ b₀)
    (hbr : (branch0 = true → -1 ≤ W) ∧ (branch0 = false → W ≤ -1))
    (hs : ∀ M e : AzInt, ∃ k, (sideAt xAt (ofAzInt M <<< e) (64 * 2 ^ k)).isSome = true) (w : ℕ) :
    ∃ lv hv : ℝ, Rounds (lambertApprox branch0 xAt qE I₀ hs w).1 lv ∧
      Rounds (lambertApprox branch0 xAt qE I₀ hs w).2 hv ∧ lv ≤ W ∧ W ≤ hv ∧
      hv - lv ≤ lambertEps a₀ b₀ qE w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hw⟩ :=
    lambertBracket_spec branch0 hX qE ha₀ hb₀ hWx haW hWb hbr hs w
  have hR1 := rounds_setPrecRound (isFinite_of_toVal_coe hlo)
  rw [fval_of_toVal_coe hlo] at hR1
  have hR2 := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
  rw [fval_of_toVal_coe hhi] at hR2
  exact ⟨lo, hi, hR1, hR2, h1, h2, hw⟩

/-- The Ziv certificate for an irrational root. -/
theorem lambertApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (branch0 : Bool)
    {xAt : ℕ → AzFloat × AzFloat} {xv : ℝ} (hX : XEncl xAt xv) (qE : Option (AzFloat × AzFloat))
    {I₀ : AzFloat × AzFloat} {a₀ b₀ : ℝ} (ha₀ : I₀.1.toVal = some (a₀ : EReal))
    (hb₀ : I₀.2.toVal = some (b₀ : EReal)) {W : ℝ} (hWx : W * Real.exp W = xv) (haW : a₀ ≤ W)
    (hWb : W ≤ b₀) (hbr : (branch0 = true → -1 ≤ W) ∧ (branch0 = false → W ≤ -1))
    (hs : ∀ M e : AzInt, ∃ k, (sideAt xAt (ofAzInt M <<< e) (64 * 2 ^ k)).isSome = true)
    (hirr : Irrational W) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (lambertApprox branch0 xAt qE I₀ hs (w₀ * 2 ^ f)).1
      (lambertApprox branch0 xAt qE I₀ hs (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (lambertApprox branch0 xAt qE I₀ hs) hirr
    (lambertEps a₀ b₀ qE) (tendsto_lambertEps a₀ b₀ qE (haW.trans hWb)) 0
    (fun w _ => lambertApprox_spec branch0 hX qE ha₀ hb₀ hWx haW hWb hbr hs w) w₀ hw₀

/-! ### The side certificate from irrationality -/

/-- A grid point is rational. -/
theorem gridVal_rat (M e : AzInt) : ∃ r : ℚ, gridVal M e = r :=
  ⟨(M.toInt : ℚ) * (2 : ℚ) ^ e.toInt, by unfold gridVal; push_cast; rfl⟩

/-- For a rational `x ≠ 0` in the domain, no grid point `m` has `m eᵐ = x`: the roots are
irrational. -/
theorem exists_sideAt_isSome_grid {xAt : ℕ → AzFloat × AzFloat} {xv : ℝ} (hX : XEncl xAt xv)
    {r : ℚ} (hxr : xv = r) (hx0 : xv ≠ 0) (hx1 : -Real.exp (-1) < xv) (M e : AzInt) :
    ∃ k, (sideAt xAt (ofAzInt M <<< e) (64 * 2 ^ k)).isSome = true := by
  apply exists_sideAt_isSome hX (toVal_gridPoint M e)
  intro heq
  obtain ⟨q, hq⟩ := gridVal_rat M e
  have hr0 : r ≠ 0 := by rintro rfl; exact hx0 (by rw [hxr, Rat.cast_zero])
  rcases lt_or_gt_of_ne hx0 with hneg | hpos
  · have hroots := (dlmf_4_13_1_two hx1 hneg).1
    have hmem : gridVal M e ∈ {t : ℝ | t * Real.exp t = xv} := heq
    rw [hroots] at hmem
    rcases hmem with h | h
    · exact irrational_lambertW0 hr0 (by rw [← hxr]; exact hx1.le) ⟨q, by rw [← hxr, ← h, hq]⟩
    · rw [Set.mem_singleton_iff] at h
      exact irrational_lambertWm1 (by rw [← hxr]; exact hx1.le) (by rw [← hxr]; exact hneg)
        ⟨q, by rw [← hxr, ← h, hq]⟩
  · have hroots := (dlmf_4_13_1_nonneg hpos.le).1
    have hmem : gridVal M e ∈ {t : ℝ | t * Real.exp t = xv} := heq
    rw [hroots, Set.mem_singleton_iff] at hmem
    exact irrational_lambertW0 hr0 (by rw [← hxr]; exact hx1.le) ⟨q, by rw [← hxr, ← hmem, hq]⟩

/-! ### The certificates of the drivers -/

theorem finiteVal_rat (s : Bool) (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m) :
    ∃ r : ℚ, finiteVal s e m = r :=
  exists_rat_of_toVal (toVal_finite s e q m hv)

/-- `1 + e r ≠ 0` for a rational `r`. -/
theorem one_add_exp_mul_rat_ne_zero (r : ℚ) : 1 + Real.exp 1 * (r : ℝ) ≠ 0 := by
  intro h
  apply irrational_neg_exp_neg_one
  refine ⟨r, ?_⟩
  rw [Real.exp_neg]
  have he := Real.exp_pos 1
  field_simp
  linarith

/-- The side certificate for a rational target `x > 0`. -/
theorem sideCert_pos {xAt : ℕ → AzFloat × AzFloat} {xv : ℝ} (hX : XEncl xAt xv)
    (hrat : ∃ r : ℚ, xv = r) (hpos : 0 < xv) (M e' : AzInt) :
    ∃ k, (sideAt xAt (ofAzInt M <<< e') (64 * 2 ^ k)).isSome = true := by
  obtain ⟨r, hr⟩ := hrat
  exact exists_sideAt_isSome_grid hX hr hpos.ne' (by linarith [Real.exp_pos (-1)]) M e'

/-- The `q` certificate for a rational target `x < 0`. -/
theorem qCert {xAt : ℕ → AzFloat × AzFloat} {xv : ℝ} (hX : XEncl xAt xv) (hrat : ∃ r : ℚ, xv = r)
    (hneg : xv < 0) : ∃ k, (qAt xAt (64 * 2 ^ k)).isSome = true := by
  obtain ⟨r, hr⟩ := hrat
  exact exists_qAt_isSome hX hneg (by rw [hr]; exact one_add_exp_mul_rat_ne_zero r)

/-- The side certificate for a rational target `x < 0` in the domain. -/
theorem sideCert_neg {xAt : ℕ → AzFloat × AzFloat} {xv : ℝ} (hX : XEncl xAt xv)
    (hrat : ∃ r : ℚ, xv = r) (hneg : xv < 0) {h : ∃ k, (qAt xAt (64 * 2 ^ k)).isSome = true}
    {lo hi : AzFloat} (hq : qEncl xAt h = some (lo, hi)) (M e' : AzInt) :
    ∃ k, (sideAt xAt (ofAzInt M <<< e') (64 * 2 ^ k)).isSome = true := by
  obtain ⟨r, hr⟩ := hrat
  obtain ⟨lov, hiv, -, -, hl0, hl, -⟩ := qEncl_eq_some hX hneg _ hq
  have hx1 : -Real.exp (-1) < xv := by rw [neg_exp_neg_one_lt_iff]; linarith
  exact exists_sideAt_isSome_grid hX hr hneg.ne hx1 M e'

/-- The Ziv certificate of `W₀` for a rational target `x > 0`. -/
theorem zivCert_W0_pos (p : ℕ) [NeZero p] (mode : RoundingMode) {xAt : ℕ → AzFloat × AzFloat}
    {xv : ℝ} (hX : XEncl xAt xv) (hrat : ∃ r : ℚ, xv = r) (hpos : 0 < xv)
    (hs : ∀ M e : AzInt, ∃ k, (sideAt xAt (ofAzInt M <<< e) (64 * 2 ^ k)).isSome = true) :
    ∃ f : ℕ, (roundingPossible
      (lambertApprox true xAt none (aprioriW0Pos xAt 64) hs ((p + zivGuardBits) * 2 ^ f)).1
      (lambertApprox true xAt none (aprioriW0Pos xAt 64) hs ((p + zivGuardBits) * 2 ^ f)).2
      p mode).isSome = true := by
  obtain ⟨r, hr⟩ := hrat
  have hr0 : r ≠ 0 := by rintro rfl; rw [Rat.cast_zero] at hr; linarith
  obtain ⟨a₀, b₀, ha₀, hb₀, haW, hWb⟩ := aprioriW0Pos_spec hX hpos (le_refl 64)
  have hW := lambertW0_spec (neg_exp_neg_one_le_of_nonneg hpos.le)
  refine lambertApprox_isSome_exists p mode true hX none ha₀ hb₀ hW.2 haW hWb
    ⟨fun _ => hW.1, fun h => (Bool.false_ne_true h.symm).elim⟩ hs ?_ _
    (by unfold zivGuardBits; omega)
  rw [hr]
  exact irrational_lambertW0 hr0 (by rw [← hr]; exact neg_exp_neg_one_le_of_nonneg hpos.le)

/-- The Ziv certificate of `W₀` for a rational target `x < 0` in the domain. -/
theorem zivCert_W0_neg (p : ℕ) [NeZero p] (mode : RoundingMode) {xAt : ℕ → AzFloat × AzFloat}
    {xv : ℝ} (hX : XEncl xAt xv) (hrat : ∃ r : ℚ, xv = r) (hneg : xv < 0)
    {h : ∃ k, (qAt xAt (64 * 2 ^ k)).isSome = true} {lo hi : AzFloat}
    (hq : qEncl xAt h = some (lo, hi))
    (hs : ∀ M e : AzInt, ∃ k, (sideAt xAt (ofAzInt M <<< e) (64 * 2 ^ k)).isSome = true) :
    ∃ f : ℕ, (roundingPossible
      (lambertApprox true xAt (some (qTight xAt (lo, hi)))
        (aprioriW0Neg (qTight xAt (lo, hi)).1 (qTight xAt (lo, hi)).2
          (64 + 2 * compBits (some (qTight xAt (lo, hi))))) hs ((p + zivGuardBits) * 2 ^ f)).1
      (lambertApprox true xAt (some (qTight xAt (lo, hi)))
        (aprioriW0Neg (qTight xAt (lo, hi)).1 (qTight xAt (lo, hi)).2
          (64 + 2 * compBits (some (qTight xAt (lo, hi))))) hs ((p + zivGuardBits) * 2 ^ f)).2
      p mode).isSome = true := by
  obtain ⟨r, hr⟩ := hrat
  have hr0 : r ≠ 0 := by rintro rfl; rw [Rat.cast_zero] at hr; linarith
  obtain ⟨lov, hiv, hlo, hhi, hl0, hl, hh⟩ := qEncl_eq_some hX hneg _ hq
  have hx1 : -Real.exp (-1) < xv := by rw [neg_exp_neg_one_lt_iff]; linarith
  obtain ⟨l', h', hl', hh', hl0', hlq', hqh'⟩ :=
    qTight_spec (q := (lo, hi)) hX hneg hlo hhi hl0 hl hh
  obtain ⟨a₀, b₀, ha₀, hb₀, haW, hWb⟩ := aprioriW0Neg_spec hx1 hneg hl' hh' hl0' hlq' hqh'
    (by omega : 64 ≤ 64 + 2 * compBits (some (qTight xAt (lo, hi))))
  have hW := lambertW0_spec hx1.le
  refine lambertApprox_isSome_exists p mode true hX _ ha₀ hb₀ hW.2 haW hWb
    ⟨fun _ => hW.1, fun h => (Bool.false_ne_true h.symm).elim⟩ hs ?_ _
    (by unfold zivGuardBits; omega)
  rw [hr]
  exact irrational_lambertW0 hr0 (by rw [← hr]; exact hx1.le)

/-- The Ziv certificate of `W₋₁` for a rational target `x < 0` in the domain. -/
theorem zivCert_Wm1 (p : ℕ) [NeZero p] (mode : RoundingMode) {xAt : ℕ → AzFloat × AzFloat}
    {xv : ℝ} (hX : XEncl xAt xv) (hrat : ∃ r : ℚ, xv = r) (hneg : xv < 0)
    {h : ∃ k, (qAt xAt (64 * 2 ^ k)).isSome = true} {lo hi : AzFloat}
    (hq : qEncl xAt h = some (lo, hi))
    (hs : ∀ M e : AzInt, ∃ k, (sideAt xAt (ofAzInt M <<< e) (64 * 2 ^ k)).isSome = true) :
    ∃ f : ℕ, (roundingPossible
      (lambertApprox false xAt (some (qTight xAt (lo, hi)))
        (aprioriWm1 xAt (qTight xAt (lo, hi)).1 (qTight xAt (lo, hi)).2
          (64 + 2 * compBits (some (qTight xAt (lo, hi))))) hs ((p + zivGuardBits) * 2 ^ f)).1
      (lambertApprox false xAt (some (qTight xAt (lo, hi)))
        (aprioriWm1 xAt (qTight xAt (lo, hi)).1 (qTight xAt (lo, hi)).2
          (64 + 2 * compBits (some (qTight xAt (lo, hi))))) hs ((p + zivGuardBits) * 2 ^ f)).2
      p mode).isSome = true := by
  obtain ⟨r, hr⟩ := hrat
  obtain ⟨lov, hiv, hlo, hhi, hl0, hl, hh⟩ := qEncl_eq_some hX hneg _ hq
  have hx1 : -Real.exp (-1) < xv := by rw [neg_exp_neg_one_lt_iff]; linarith
  obtain ⟨l', h', hl', hh', hl0', hlq', hqh'⟩ :=
    qTight_spec (q := (lo, hi)) hX hneg hlo hhi hl0 hl hh
  obtain ⟨a₀, b₀, ha₀, hb₀, haW, hWb⟩ := aprioriWm1_spec hX hx1 hneg hl' hh' hl0' hlq' hqh'
    (by omega : 64 ≤ 64 + 2 * compBits (some (qTight xAt (lo, hi))))
  have hW := lambertWm1_spec hx1.le hneg
  refine lambertApprox_isSome_exists p mode false hX _ ha₀ hb₀ hW.2 haW hWb
    ⟨fun h => (Bool.false_ne_true h).elim, fun _ => hW.1⟩ hs ?_ _
    (by unfold zivGuardBits; omega)
  rw [hr]
  exact irrational_lambertWm1 (by rw [← hr]; exact hx1.le) (by rw [← hr]; exact hneg)

/-! ### The float and rational instances -/

theorem finite_true_pos_rat (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m) :
    0 < finiteVal true e m := finiteVal_true_pos e hv

theorem finite_false_neg_rat (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m) :
    finiteVal false e m < 0 := finiteVal_false_neg e hv

/-- A rational with positive sign and nonzero numerator is positive. -/
theorem toRat_pos_real (q : AzRat) (hs : q.sign = true) (h0 : q.num ≠ 0) :
    (0 : ℝ) < ((AzRat.toRat q : ℚ) : ℝ) := by exact_mod_cast toRat_pos_of_sign q hs h0

/-- A rational with negative sign and nonzero numerator is negative. -/
theorem toRat_neg_real (q : AzRat) (hs : q.sign = false) (h0 : q.num ≠ 0) :
    ((AzRat.toRat q : ℚ) : ℝ) < 0 := by exact_mod_cast toRat_neg_of_sign q hs h0

/-! ### Bundled targets (the drivers carry one proposition, not a real) -/

/-- A positive rational target with its enclosure function. -/
def PosTarget (xAt : ℕ → AzFloat × AzFloat) : Prop :=
  ∃ xv : ℝ, XEncl xAt xv ∧ (∃ r : ℚ, xv = r) ∧ 0 < xv

/-- A negative rational target with its enclosure function. -/
def NegTarget (xAt : ℕ → AzFloat × AzFloat) : Prop :=
  ∃ xv : ℝ, XEncl xAt xv ∧ (∃ r : ℚ, xv = r) ∧ xv < 0

theorem sideCert_pos' {xAt : ℕ → AzFloat × AzFloat} (h : PosTarget xAt) (M e' : AzInt) :
    ∃ k, (sideAt xAt (ofAzInt M <<< e') (64 * 2 ^ k)).isSome = true := by
  obtain ⟨xv, hX, hrat, hpos⟩ := h
  exact sideCert_pos hX hrat hpos M e'

theorem qCert' {xAt : ℕ → AzFloat × AzFloat} (h : NegTarget xAt) :
    ∃ k, (qAt xAt (64 * 2 ^ k)).isSome = true := by
  obtain ⟨xv, hX, hrat, hneg⟩ := h
  exact qCert hX hrat hneg

theorem sideCert_neg' {xAt : ℕ → AzFloat × AzFloat} (h : NegTarget xAt)
    {h0 : ∃ k, (qAt xAt (64 * 2 ^ k)).isSome = true} {lo hi : AzFloat}
    (hq : qEncl xAt h0 = some (lo, hi)) (M e' : AzInt) :
    ∃ k, (sideAt xAt (ofAzInt M <<< e') (64 * 2 ^ k)).isSome = true := by
  obtain ⟨xv, hX, hrat, hneg⟩ := h
  exact sideCert_neg hX hrat hneg hq M e'

theorem zivCert_W0_pos' (p : ℕ) [NeZero p] (mode : RoundingMode) {xAt : ℕ → AzFloat × AzFloat}
    (h : PosTarget xAt)
    (hs : ∀ M e : AzInt, ∃ k, (sideAt xAt (ofAzInt M <<< e) (64 * 2 ^ k)).isSome = true) :
    ∃ f : ℕ, (roundingPossible
      (lambertApprox true xAt none (aprioriW0Pos xAt 64) hs ((p + zivGuardBits) * 2 ^ f)).1
      (lambertApprox true xAt none (aprioriW0Pos xAt 64) hs ((p + zivGuardBits) * 2 ^ f)).2
      p mode).isSome = true := by
  obtain ⟨xv, hX, hrat, hpos⟩ := h
  exact zivCert_W0_pos p mode hX hrat hpos hs

theorem zivCert_W0_neg' (p : ℕ) [NeZero p] (mode : RoundingMode) {xAt : ℕ → AzFloat × AzFloat}
    (h : NegTarget xAt) {h0 : ∃ k, (qAt xAt (64 * 2 ^ k)).isSome = true} {lo hi : AzFloat}
    (hq : qEncl xAt h0 = some (lo, hi))
    (hs : ∀ M e : AzInt, ∃ k, (sideAt xAt (ofAzInt M <<< e) (64 * 2 ^ k)).isSome = true) :
    ∃ f : ℕ, (roundingPossible
      (lambertApprox true xAt (some (qTight xAt (lo, hi)))
        (aprioriW0Neg (qTight xAt (lo, hi)).1 (qTight xAt (lo, hi)).2
          (64 + 2 * compBits (some (qTight xAt (lo, hi))))) hs ((p + zivGuardBits) * 2 ^ f)).1
      (lambertApprox true xAt (some (qTight xAt (lo, hi)))
        (aprioriW0Neg (qTight xAt (lo, hi)).1 (qTight xAt (lo, hi)).2
          (64 + 2 * compBits (some (qTight xAt (lo, hi))))) hs ((p + zivGuardBits) * 2 ^ f)).2
      p mode).isSome = true := by
  obtain ⟨xv, hX, hrat, hneg⟩ := h
  exact zivCert_W0_neg p mode hX hrat hneg hq hs

theorem zivCert_Wm1' (p : ℕ) [NeZero p] (mode : RoundingMode) {xAt : ℕ → AzFloat × AzFloat}
    (h : NegTarget xAt) {h0 : ∃ k, (qAt xAt (64 * 2 ^ k)).isSome = true} {lo hi : AzFloat}
    (hq : qEncl xAt h0 = some (lo, hi))
    (hs : ∀ M e : AzInt, ∃ k, (sideAt xAt (ofAzInt M <<< e) (64 * 2 ^ k)).isSome = true) :
    ∃ f : ℕ, (roundingPossible
      (lambertApprox false xAt (some (qTight xAt (lo, hi)))
        (aprioriWm1 xAt (qTight xAt (lo, hi)).1 (qTight xAt (lo, hi)).2
          (64 + 2 * compBits (some (qTight xAt (lo, hi))))) hs ((p + zivGuardBits) * 2 ^ f)).1
      (lambertApprox false xAt (some (qTight xAt (lo, hi)))
        (aprioriWm1 xAt (qTight xAt (lo, hi)).1 (qTight xAt (lo, hi)).2
          (64 + 2 * compBits (some (qTight xAt (lo, hi))))) hs ((p + zivGuardBits) * 2 ^ f)).2
      p mode).isSome = true := by
  obtain ⟨xv, hX, hrat, hneg⟩ := h
  exact zivCert_Wm1 p mode hX hrat hneg hq hs

end Azurite.AzFloat
