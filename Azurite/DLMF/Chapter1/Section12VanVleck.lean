/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section12Convergence
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# DLMF §1.12(v): Van Vleck's Theorem

A complete proof of **Van Vleck's theorem** (`dlmf_1_12_28`, DLMF 1.12.26–1.12.28). If the
elements of `1/(b₁ + 1/(b₂ + ⋯))` satisfy `−π/2 + δ < ph bₙ < π/2 − δ`, then the even and odd parts
converge to finite values, and the continued fraction converges iff `∑ |bₙ| = ∞`. The sector bound
on the convergents (1.12.27) is in `Section12Convergence`.

Proof (no normal families):

1. **Positive elements.** When `bₙ > 0`, the even convergents increase and the odd ones decrease,
   and both stay bounded (`posC_even_tendsto`, `posC_odd_tendsto`). The identity
   `BₙB_{n+1} = ∑ b_k B_{k−1}²` gives Seidel–Stern: `∑ bₙ = ∞` forces convergence
   (`posC_tendsto`).
2. **Stern–Stolz** (`stern_stolz`). If `∑ |bₙ| < ∞`, then `Aₙ` and `Bₙ` converge along the even
   and along the odd indices, and the limits satisfy `A_o B_e − B_o A_e = 1`. So the convergents
   diverge.
3. **Vitali, power-series form** (`coeff_tendsto_of_bounded`, `tendsto_of_bounded_power_series`).
   Suppose the coefficients are bounded uniformly, `|a_{n,k}| ≤ M/Rᵏ`, and the power series
   converge on a set accumulating at `0`. Then every coefficient converges (a Cauchy argument,
   proved by induction on `k`), and Tannery's theorem gives convergence on `|z| < R`.
4. **The holomorphic family** `bₖ(z) = |bₖ| e^{iz ph bₖ}` (`vvFamily`).
   * On a disk of radius `R > 1` the elements stay in a smaller sector (`vvFamily_sector`). So the
     convergents are holomorphic (`cfConv_differentiableOn`) and bounded by `1/Re b₁(z)`
     (`norm_cfConv_le`).
   * On the imaginary axis the elements are positive (`vvFamily_imag`), and at `z = 1` they are the
     `bₖ` (`vvFamily_one`). Their Taylor coefficients at `0` satisfy Cauchy's bounds.
   * Convergence on the imaginary axis therefore transfers to `z = 1`.
-/

open Filter Topology Finset Complex Metric
open scoped Real Nat

namespace Azurite.DLMF

/-! ### Generic lemmas -/

theorem cfw_map {K L : Type*} [Field K] [Field L] (ρ : K →+* L) (a b : ℕ → K) (n : ℕ) :
    ∀ w, cfw (fun k => ρ (a k)) (fun k => ρ (b k)) n (ρ w) = ρ (cfw a b n w) := by
  induction n with
  | zero => intro w; simp [cfw]
  | succ n ih => intro w; rw [cfw, cfw, ← ih, map_div₀, map_add]

theorem cfP_map {K L : Type*} [Field K] [Field L] (ρ : K →+* L) (a b : ℕ → K) (k : ℕ) :
    cfP (fun k => ρ (a k)) (fun k => ρ (b k)) k = ρ (cfP a b k) ∧
      cfQ (fun k => ρ (a k)) (fun k => ρ (b k)) k = ρ (cfQ a b k) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simp [cfP, cfQ]
    | 1 => simp [cfP, cfQ]
    | k + 2 =>
      obtain ⟨p1, q1⟩ := ih (k + 1) (by omega)
      obtain ⟨p0, q0⟩ := ih k (by omega)
      simp only [cfP, cfQ] at p1 q1 p0 q0 ⊢
      rw [p1, q1, p0, q0]
      simp

/-- Peeling off the outermost level: `C_{n+1}(w) = b₀ + a₁/(b₁ + a₂/(⋯ (bₙ₊₁ + w)))`. -/
theorem cfw_succ_shift {K : Type*} [Field K] (a b : ℕ → K) (n : ℕ) :
    ∀ w, cfw a b (n + 1) w = b 0 + a 1 / cfw (fun k => a (k + 1)) (fun k => b (k + 1)) n w := by
  induction n with
  | zero => intro w; simp [cfw]
  | succ n ih => intro w; rw [cfw, ih, cfw]

/-- In a sector of half-angle `< π/2`, the tails of `1/(b₁ + 1/(b₂ + ⋯))` stay in the sector. -/
theorem sector_tails {b : ℕ → ℂ} {δ : ℝ} (hs : 0 ≤ Real.sin δ)
    (hb : ∀ n ≥ 1, b n ∈ VVSector δ) :
    ∀ n w, w ∈ VVSector δ →
      CfNonzero (fun _ => 1) b n w ∧ cfw (fun _ => 1) b n w - b 0 ∈ VVSector δ := by
  intro n
  induction n with
  | zero => intro w hw; exact ⟨trivial, by simpa [cfw] using hw⟩
  | succ n ih =>
    intro w hw
    have hsum := VVSector.add (hb (n + 1) (by omega)) hw hs
    obtain ⟨h1, h2⟩ := ih (1 / (b (n + 1) + w)) (by rw [one_div]; exact VVSector.inv hsum)
    exact ⟨⟨VVSector.ne_zero hsum, h1⟩, h2⟩

theorem sector_conv {b : ℕ → ℂ} {δ : ℝ} (hs : 0 ≤ Real.sin δ) (hb : ∀ n ≥ 1, b n ∈ VVSector δ)
    (n : ℕ) : CfNonzero (fun _ => 1) b (n + 1) 0 ∧
      cfConv (fun _ => 1) b (n + 1) - b 0 ∈ VVSector δ := by
  have hb1 : b (n + 1) + 0 ∈ VVSector δ := by simpa using hb (n + 1) (by omega)
  obtain ⟨h1, h2⟩ := sector_tails hs hb n (1 / (b (n + 1) + 0))
    (by rw [one_div]; exact VVSector.inv hb1)
  exact ⟨⟨VVSector.ne_zero hb1, h1⟩, h2⟩

theorem sector_nonzero {b : ℕ → ℂ} {δ : ℝ} (hs : 0 ≤ Real.sin δ)
    (hb : ∀ n ≥ 1, b n ∈ VVSector δ) : ∀ n, CfNonzero (fun _ => 1) b n 0 := by
  intro n
  rcases n with _ | n
  · trivial
  · exact (sector_conv hs hb n).1

/-- In the sector case the canonical denominators never vanish: `Bₙ/B_{n−1}` stays in the
sector. -/
theorem sector_denom {b : ℕ → ℂ} {δ : ℝ} (hs : 0 ≤ Real.sin δ)
    (hb : ∀ n ≥ 1, b n ∈ VVSector δ) :
    ∀ n, cfB (fun _ => 1) b n ≠ 0 ∧
      cfB (fun _ => 1) b (n + 1) / cfB (fun _ => 1) b n ∈ VVSector δ := by
  intro n
  induction n with
  | zero =>
    refine ⟨by simp [cfB, cfQ], ?_⟩
    simpa [cfB, cfQ] using hb 1 le_rfl
  | succ n ih =>
    obtain ⟨h0, hr⟩ := ih
    have hne : cfB (fun _ => 1) b (n + 1) ≠ 0 := by
      intro h
      rw [h, zero_div] at hr
      exact VVSector.ne_zero hr rfl
    refine ⟨hne, ?_⟩
    have heq : cfB (fun _ => 1) b (n + 2) / cfB (fun _ => 1) b (n + 1) =
        b (n + 2) + (cfB (fun _ => 1) b (n + 1) / cfB (fun _ => 1) b n)⁻¹ := by
      rw [inv_div]
      simp only [cfB]
      rw [show cfQ (fun _ => 1) b (n + 2 + 1) = b (n + 2) * cfQ (fun _ => 1) b (n + 2) +
        1 * cfQ (fun _ => 1) b (n + 1) from rfl]
      simp only [cfB] at hne
      field_simp
    rw [heq]
    exact VVSector.add (hb (n + 2) (by omega)) (VVSector.inv hr) hs

/-! ### Positive real elements -/

section Positive

variable {β : ℕ → ℝ}

theorem pos_cfNonzero (hβ : ∀ k ≥ 1, 0 < β k) :
    ∀ n w, 0 ≤ w → CfNonzero (fun _ => (1 : ℝ)) β n w := by
  intro n
  induction n with
  | zero => intro w _; trivial
  | succ n ih =>
    intro w hw
    have hpos : 0 < β (n + 1) + w := by linarith [hβ (n + 1) (by omega)]
    exact ⟨hpos.ne', ih _ (by positivity)⟩

theorem pos_cfQ (hβ : ∀ k ≥ 1, 0 < β k) : ∀ k ≥ 1, 0 < cfQ (fun _ => (1 : ℝ)) β k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    match k with
    | 1 => simp [cfQ]
    | 2 => simp [cfQ, hβ 1 le_rfl]
    | k + 3 =>
      have h1 := ih (k + 2) (by omega) (by omega)
      have h0 := ih (k + 1) (by omega) (by omega)
      rw [show cfQ (fun _ => (1 : ℝ)) β (k + 3) = β (k + 2) * cfQ (fun _ => 1) β (k + 2) +
        1 * cfQ (fun _ => 1) β (k + 1) from rfl]
      have := hβ (k + 2) (by omega)
      positivity

theorem pos_cfB (hβ : ∀ k ≥ 1, 0 < β k) (n : ℕ) : 0 < cfB (fun _ => (1 : ℝ)) β n :=
  pos_cfQ hβ (n + 1) (by omega)

theorem cfB_add_two (β : ℕ → ℝ) (n : ℕ) :
    cfB (fun _ => (1 : ℝ)) β (n + 2) =
      β (n + 2) * cfB (fun _ => 1) β (n + 1) + cfB (fun _ => 1) β n := by
  simp only [cfB]
  rw [show cfQ (fun _ => (1 : ℝ)) β (n + 2 + 1) = β (n + 2) * cfQ (fun _ => 1) β (n + 2) +
    1 * cfQ (fun _ => 1) β (n + 1) from rfl]
  ring

theorem cfB_lt_add_two (hβ : ∀ k ≥ 1, 0 < β k) (n : ℕ) :
    cfB (fun _ => (1 : ℝ)) β n < cfB (fun _ => 1) β (n + 2) := by
  rw [cfB_add_two]
  have := hβ (n + 2) (by omega)
  have := pos_cfB hβ (n + 1)
  nlinarith

/-- `C_{n+1} − Cₙ = (−1)ⁿ/(BₙB_{n+1})`. -/
theorem pos_diff (hβ : ∀ k ≥ 1, 0 < β k) (n : ℕ) :
    cfA (fun _ => (1 : ℝ)) β (n + 1) / cfB (fun _ => 1) β (n + 1) -
      cfA (fun _ => 1) β n / cfB (fun _ => 1) β n =
        (-1) ^ n / (cfB (fun _ => 1) β n * cfB (fun _ => 1) β (n + 1)) := by
  rw [dlmf_1_12_8 _ β n (pos_cfB hβ n).ne' (pos_cfB hβ (n + 1)).ne']
  simp

/-- The convergents `Aₙ/Bₙ` (positive case). -/
noncomputable def posC (β : ℕ → ℝ) (n : ℕ) : ℝ :=
  cfA (fun _ => (1 : ℝ)) β n / cfB (fun _ => 1) β n

theorem posC_even_lt (hβ : ∀ k ≥ 1, 0 < β k) (n : ℕ) : posC β (2 * n) < posC β (2 * n + 2) := by
  have h1 := pos_diff hβ (2 * n + 1)
  have h0 := pos_diff hβ (2 * n)
  have hB := cfB_lt_add_two hβ (2 * n)
  have p0 := pos_cfB hβ (2 * n)
  have p1 := pos_cfB hβ (2 * n + 1)
  have p2 := pos_cfB hβ (2 * n + 2)
  simp only [posC]
  rw [show 2 * n + 1 + 1 = 2 * n + 2 by ring] at h1
  have e : posC β (2 * n + 2) - posC β (2 * n) =
      -1 / (cfB (fun _ => 1) β (2 * n + 1) * cfB (fun _ => 1) β (2 * n + 2)) +
        1 / (cfB (fun _ => 1) β (2 * n) * cfB (fun _ => 1) β (2 * n + 1)) := by
    simp only [posC]
    rw [show cfA (fun _ => 1) β (2 * n + 2) / cfB (fun _ => 1) β (2 * n + 2) -
      cfA (fun _ => 1) β (2 * n) / cfB (fun _ => 1) β (2 * n) =
      (cfA (fun _ => 1) β (2 * n + 2) / cfB (fun _ => 1) β (2 * n + 2) -
        cfA (fun _ => 1) β (2 * n + 1) / cfB (fun _ => 1) β (2 * n + 1)) +
      (cfA (fun _ => 1) β (2 * n + 1) / cfB (fun _ => 1) β (2 * n + 1) -
        cfA (fun _ => 1) β (2 * n) / cfB (fun _ => 1) β (2 * n)) by ring, h1, h0,
      pow_succ, pow_mul, neg_one_sq, one_pow, one_mul]
  simp only [posC] at e
  have : 0 < -1 / (cfB (fun _ => 1) β (2 * n + 1) * cfB (fun _ => 1) β (2 * n + 2)) +
      1 / (cfB (fun _ => 1) β (2 * n) * cfB (fun _ => 1) β (2 * n + 1)) := by
    rw [div_add_div _ _ (by positivity) (by positivity)]
    apply div_pos _ (by positivity)
    nlinarith [mul_pos p1 p1]
  linarith

theorem posC_odd_lt (hβ : ∀ k ≥ 1, 0 < β k) (n : ℕ) :
    posC β (2 * n + 3) < posC β (2 * n + 1) := by
  have h1 := pos_diff hβ (2 * n + 2)
  have h0 := pos_diff hβ (2 * n + 1)
  have hB := cfB_lt_add_two hβ (2 * n + 1)
  have p1 := pos_cfB hβ (2 * n + 1)
  have p2 := pos_cfB hβ (2 * n + 2)
  have p3 := pos_cfB hβ (2 * n + 3)
  rw [show 2 * n + 2 + 1 = 2 * n + 3 by ring] at h1
  rw [show 2 * n + 1 + 1 = 2 * n + 2 by ring] at h0
  have e : posC β (2 * n + 3) - posC β (2 * n + 1) =
      1 / (cfB (fun _ => 1) β (2 * n + 2) * cfB (fun _ => 1) β (2 * n + 3)) +
        -1 / (cfB (fun _ => 1) β (2 * n + 1) * cfB (fun _ => 1) β (2 * n + 2)) := by
    simp only [posC]
    rw [show cfA (fun _ => 1) β (2 * n + 3) / cfB (fun _ => 1) β (2 * n + 3) -
      cfA (fun _ => 1) β (2 * n + 1) / cfB (fun _ => 1) β (2 * n + 1) =
      (cfA (fun _ => 1) β (2 * n + 3) / cfB (fun _ => 1) β (2 * n + 3) -
        cfA (fun _ => 1) β (2 * n + 2) / cfB (fun _ => 1) β (2 * n + 2)) +
      (cfA (fun _ => 1) β (2 * n + 2) / cfB (fun _ => 1) β (2 * n + 2) -
        cfA (fun _ => 1) β (2 * n + 1) / cfB (fun _ => 1) β (2 * n + 1)) by ring, h1, h0,
      show 2 * n + 2 = 2 * (n + 1) by ring, pow_mul, neg_one_sq, one_pow, pow_succ, pow_mul,
      neg_one_sq, one_pow, one_mul]
  have : 1 / (cfB (fun _ => 1) β (2 * n + 2) * cfB (fun _ => 1) β (2 * n + 3)) +
      -1 / (cfB (fun _ => 1) β (2 * n + 1) * cfB (fun _ => 1) β (2 * n + 2)) < 0 := by
    rw [div_add_div _ _ (by positivity) (by positivity)]
    apply div_neg_of_neg_of_pos _ (by positivity)
    nlinarith [mul_pos p2 p2]
  linarith

theorem posC_even_lt_odd (hβ : ∀ k ≥ 1, 0 < β k) (n : ℕ) :
    posC β (2 * n) < posC β (2 * n + 1) := by
  have h := pos_diff hβ (2 * n)
  simp only [posC] at h ⊢
  have p0 := pos_cfB hβ (2 * n)
  have p1 := pos_cfB hβ (2 * n + 1)
  rw [pow_mul, neg_one_sq, one_pow] at h
  have : 0 < 1 / (cfB (fun _ => 1) β (2 * n) * cfB (fun _ => 1) β (2 * n + 1)) := by positivity
  linarith

theorem posC_odd_le_one (hβ : ∀ k ≥ 1, 0 < β k) (n : ℕ) : posC β (2 * n + 1) ≤ posC β 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have := posC_odd_lt hβ n
    rw [show 2 * (n + 1) + 1 = 2 * n + 3 by ring]
    linarith

theorem posC_zero_le_even (hβ : ∀ k ≥ 1, 0 < β k) (n : ℕ) : posC β 0 ≤ posC β (2 * n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have := posC_even_lt hβ n
    rw [show 2 * (n + 1) = 2 * n + 2 by ring]
    linarith

/-- The even part converges (positive case). -/
theorem posC_even_tendsto (hβ : ∀ k ≥ 1, 0 < β k) :
    ∃ L, Tendsto (fun n => posC β (2 * n)) atTop (𝓝 L) := by
  have hmono : Monotone fun n => posC β (2 * n) := monotone_nat_of_le_succ fun n => by
    rw [show 2 * (n + 1) = 2 * n + 2 by ring]
    exact (posC_even_lt hβ n).le
  have hbdd : BddAbove (Set.range fun n => posC β (2 * n)) := ⟨posC β 1, by
    rintro _ ⟨n, rfl⟩
    exact (posC_even_lt_odd hβ n).le.trans (posC_odd_le_one hβ n)⟩
  exact ⟨_, tendsto_atTop_ciSup hmono hbdd⟩

/-- The odd part converges (positive case). -/
theorem posC_odd_tendsto (hβ : ∀ k ≥ 1, 0 < β k) :
    ∃ L, Tendsto (fun n => posC β (2 * n + 1)) atTop (𝓝 L) := by
  have hanti : Antitone fun n => posC β (2 * n + 1) := antitone_nat_of_succ_le fun n => by
    rw [show 2 * (n + 1) + 1 = 2 * n + 3 by ring]
    exact (posC_odd_lt hβ n).le
  have hbdd : BddBelow (Set.range fun n => posC β (2 * n + 1)) := ⟨posC β 0, by
    rintro _ ⟨n, rfl⟩
    exact (posC_zero_le_even hβ n).trans (posC_even_lt_odd hβ n).le⟩
  exact ⟨_, tendsto_atTop_ciInf hanti hbdd⟩

theorem tendsto_of_even_odd {X : Type*} [TopologicalSpace X] {f : ℕ → X} {L : X}
    (he : Tendsto (fun n => f (2 * n)) atTop (𝓝 L))
    (ho : Tendsto (fun n => f (2 * n + 1)) atTop (𝓝 L)) : Tendsto f atTop (𝓝 L) := by
  rw [tendsto_atTop_nhds] at he ho ⊢
  intro U hU hUo
  obtain ⟨N₁, h₁⟩ := he U hU hUo
  obtain ⟨N₂, h₂⟩ := ho U hU hUo
  refine ⟨2 * (N₁ + N₂) + 1, fun n hn => ?_⟩
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rw [← two_mul]
    exact h₁ m (by omega)
  · exact h₂ m (by omega)

/-- `B_n B_{n+1} = ∑_{k=1}^{n+1} β_k B_{k−1}²`. -/
theorem pos_BB (β : ℕ → ℝ) (n : ℕ) :
    cfQ (fun _ => (1 : ℝ)) β (n + 1) * cfQ (fun _ => 1) β (n + 2) =
      ∑ k ∈ Icc 1 (n + 1), β k * cfQ (fun _ => 1) β k ^ 2 := by
  induction n with
  | zero => simp [cfQ]
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega), ← ih]
    rw [show cfQ (fun _ => (1 : ℝ)) β (n + 1 + 2) = β (n + 2) * cfQ (fun _ => 1) β (n + 2) +
      1 * cfQ (fun _ => 1) β (n + 1) from rfl]
    ring

theorem pos_cfQ_ge (hβ : ∀ k ≥ 1, 0 < β k) :
    ∀ k ≥ 1, min 1 (β 1) ≤ cfQ (fun _ => (1 : ℝ)) β k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    match k with
    | 1 => simp [cfQ]
    | 2 => simp [cfQ]
    | k + 3 =>
      have h0 := ih (k + 1) (by omega) (by omega)
      have h1 := pos_cfQ hβ (k + 2) (by omega)
      rw [show cfQ (fun _ => (1 : ℝ)) β (k + 3) = β (k + 2) * cfQ (fun _ => 1) β (k + 2) +
        1 * cfQ (fun _ => 1) β (k + 1) from rfl]
      have := hβ (k + 2) (by omega)
      nlinarith

/-- **Seidel–Stern**: if `bₙ > 0` and `∑ bₙ = ∞`, then `1/(b₁ + 1/(b₂ + ⋯))` converges. -/
theorem posC_tendsto (hβ0 : β 0 = 0) (hβ : ∀ k ≥ 1, 0 < β k) (hns : ¬ Summable β) :
    ∃ L, Tendsto (posC β) atTop (𝓝 L) := by
  obtain ⟨E, hE⟩ := posC_even_tendsto hβ
  obtain ⟨O, hO⟩ := posC_odd_tendsto hβ
  set m := min 1 (β 1)
  have hm : 0 < m := lt_min one_pos (hβ 1 le_rfl)
  have hsum : Tendsto (fun n => ∑ i ∈ range n, β i) atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg fun n => by
      rcases n with _ | n
      · rw [hβ0]
      · exact (hβ (n + 1) (by omega)).le).mp hns
  have hIcc : ∀ n, ∑ k ∈ Icc 1 (n + 1), β k = ∑ i ∈ range (n + 2), β i := by
    intro n
    induction n with
    | zero => simp [sum_range_succ, hβ0]
    | succ n ih =>
      rw [sum_Icc_succ_top (show 1 ≤ n + 1 + 1 by omega), ih,
        show n + 1 + 2 = (n + 2) + 1 from rfl, sum_range_succ _ (n + 2)]
  -- `BₙB_{n+1} → ∞`
  have hBB : Tendsto (fun n => cfB (fun _ => (1 : ℝ)) β n * cfB (fun _ => 1) β (n + 1)) atTop
      atTop := by
    have hlow : ∀ n, m ^ 2 * ∑ i ∈ range (n + 2), β i ≤
        cfB (fun _ => (1 : ℝ)) β n * cfB (fun _ => 1) β (n + 1) := by
      intro n
      simp only [cfB]
      rw [pos_BB, ← hIcc, mul_sum]
      refine sum_le_sum fun k hk => ?_
      have hk1 := (mem_Icc.mp hk).1
      have hq := pos_cfQ_ge hβ k hk1
      have := hβ k hk1
      have hm2 : m ^ 2 ≤ cfQ (fun _ => 1) β k ^ 2 := pow_le_pow_left₀ hm.le hq 2
      nlinarith
    exact tendsto_atTop_mono hlow (Tendsto.const_mul_atTop (by positivity)
      (hsum.comp (tendsto_add_atTop_nat 2)))
  have hdiff : Tendsto (fun n => posC β (2 * n + 1) - posC β (2 * n)) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero.comp hBB).comp
      (tendsto_id.const_mul_atTop' (by norm_num : (0 : ℕ) < 2))
    refine h.congr fun n => ?_
    have := pos_diff hβ (2 * n)
    simp only [posC, Function.comp_apply, id]
    rw [this, pow_mul]
    norm_num
  have hEO : O = E := sub_eq_zero.mp (tendsto_nhds_unique (hO.sub hE) hdiff)
  exact ⟨E, tendsto_of_even_odd hE (hEO ▸ hO)⟩

end Positive

/-! ### Stern–Stolz: `∑ |bₙ| < ∞` forces divergence -/

/-- A sequence with summable increments converges. -/
theorem exists_tendsto_of_summable_sub {v : ℕ → ℂ} (hv : Summable fun n => ‖v (n + 1) - v n‖) :
    ∃ L, Tendsto v atTop (𝓝 L) := by
  have hs : Summable fun n => v (n + 1) - v n := Summable.of_norm hv
  refine ⟨v 0 + ∑' n, (v (n + 1) - v n), ?_⟩
  have := (hs.hasSum.tendsto_sum_nat).const_add (v 0)
  refine this.congr fun n => ?_
  rw [sum_range_sub]
  ring

/-- Solutions of `u_{n+2} = b_{n+1}u_{n+1} + uₙ` with `|u₀|, |u₁| ≤ 1` are bounded by
`exp ∑ |bₙ|`. -/
theorem recurrence_bound {b : ℕ → ℂ} (hs : Summable fun n => ‖b n‖) {u : ℕ → ℂ}
    (hu : ∀ n, u (n + 2) = b (n + 1) * u (n + 1) + u n) (h0 : ‖u 0‖ ≤ 1) (h1 : ‖u 1‖ ≤ 1) :
    ∀ n, ‖u n‖ ≤ Real.exp (∑' n, ‖b n‖) := by
  set PP : ℕ → ℝ := fun n => ∏ k ∈ range (n + 1), (1 + ‖b k‖) with hPP
  have hPP1 : ∀ n, 1 ≤ PP n := fun n => one_le_prod₀ fun k _ => by linarith [norm_nonneg (b k)]
  have hPPexp : ∀ n, PP n ≤ Real.exp (∑' n, ‖b n‖) := by
    intro n
    calc PP n ≤ ∏ k ∈ range (n + 1), Real.exp ‖b k‖ := by
          simp only [hPP]
          gcongr with k
          linarith [Real.add_one_le_exp ‖b k‖]
      _ = Real.exp (∑ k ∈ range (n + 1), ‖b k‖) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp (∑' n, ‖b n‖) :=
          Real.exp_le_exp.mpr (hs.sum_le_tsum _ fun k _ => norm_nonneg _)
  have key : ∀ n, ‖u n‖ ≤ PP n ∧ ‖u (n + 1)‖ ≤ PP n := by
    intro n
    induction n with
    | zero => exact ⟨h0.trans (hPP1 0), h1.trans (hPP1 0)⟩
    | succ n ih =>
      have hstep : PP (n + 1) = PP n * (1 + ‖b (n + 1)‖) := by
        simp only [hPP]
        rw [prod_range_succ]
      refine ⟨ih.2.trans (by rw [hstep]; nlinarith [hPP1 n, norm_nonneg (b (n + 1))]), ?_⟩
      rw [hu, hstep]
      calc ‖b (n + 1) * u (n + 1) + u n‖ ≤ ‖b (n + 1)‖ * ‖u (n + 1)‖ + ‖u n‖ := by
            rw [← norm_mul]
            exact norm_add_le _ _
        _ ≤ ‖b (n + 1)‖ * PP n + PP n := by
            gcongr
            exacts [ih.2, ih.1]
        _ = PP n * (1 + ‖b (n + 1)‖) := by ring
  exact fun n => (key n).1.trans (hPPexp n)

/-- Under `∑ |bₙ| < ∞`, a solution of the recurrence converges along even and odd indices. -/
theorem recurrence_even_odd {b : ℕ → ℂ} (hs : Summable fun n => ‖b n‖) {u : ℕ → ℂ}
    (hu : ∀ n, u (n + 2) = b (n + 1) * u (n + 1) + u n) (h0 : ‖u 0‖ ≤ 1) (h1 : ‖u 1‖ ≤ 1)
    (j : ℕ) : ∃ L, Tendsto (fun n => u (2 * n + j)) atTop (𝓝 L) := by
  have hK := recurrence_bound hs hu h0 h1
  apply exists_tendsto_of_summable_sub
  have hsub : Summable fun n => ‖b (2 * n + j + 1)‖ :=
    hs.comp_injective fun m n h => by omega
  refine (hsub.mul_left (Real.exp (∑' n, ‖b n‖))).of_nonneg_of_le (fun _ => norm_nonneg _)
    fun n => ?_
  rw [show 2 * (n + 1) + j = (2 * n + j) + 2 by ring, hu, add_sub_cancel_right, norm_mul,
    mul_comm]
  exact mul_le_mul_of_nonneg_right (hK _) (norm_nonneg _)

/-- **Stern–Stolz**: if `b₀ = 0`, `∑ |bₙ| < ∞` and `Bₙ ≠ 0`, then `1/(b₁ + 1/(b₂ + ⋯))` diverges:
the even and odd convergents tend to different limits. -/
theorem stern_stolz {b : ℕ → ℂ} (hb0 : b 0 = 0) (hs : Summable fun n => ‖b n‖)
    (hB : ∀ n, cfB (fun _ => 1) b n ≠ 0) :
    ¬ ∃ C, Tendsto (fun n => cfA (fun _ => 1) b n / cfB (fun _ => 1) b n) atTop (𝓝 C) := by
  rintro ⟨C, hC⟩
  have hPrec : ∀ n, cfP (fun _ => (1 : ℂ)) b (n + 2) =
      b (n + 1) * cfP (fun _ => 1) b (n + 1) + cfP (fun _ => 1) b n := fun n => by
    rw [show cfP (fun _ => (1 : ℂ)) b (n + 2) = b (n + 1) * cfP (fun _ => 1) b (n + 1) +
      1 * cfP (fun _ => 1) b n from rfl, one_mul]
  have hQrec : ∀ n, cfQ (fun _ => (1 : ℂ)) b (n + 2) =
      b (n + 1) * cfQ (fun _ => 1) b (n + 1) + cfQ (fun _ => 1) b n := fun n => by
    rw [show cfQ (fun _ => (1 : ℂ)) b (n + 2) = b (n + 1) * cfQ (fun _ => 1) b (n + 1) +
      1 * cfQ (fun _ => 1) b n from rfl, one_mul]
  have hP0 : ‖cfP (fun _ => (1 : ℂ)) b 0‖ ≤ 1 := by simp [cfP]
  have hP1 : ‖cfP (fun _ => (1 : ℂ)) b 1‖ ≤ 1 := by simp [cfP, hb0]
  have hQ0 : ‖cfQ (fun _ => (1 : ℂ)) b 0‖ ≤ 1 := by simp [cfQ]
  have hQ1 : ‖cfQ (fun _ => (1 : ℂ)) b 1‖ ≤ 1 := by simp [cfQ]
  obtain ⟨Ae, hAe⟩ := recurrence_even_odd hs hPrec hP0 hP1 1
  obtain ⟨Ao, hAo⟩ := recurrence_even_odd hs hPrec hP0 hP1 2
  obtain ⟨Be, hBe⟩ := recurrence_even_odd hs hQrec hQ0 hQ1 1
  obtain ⟨Bo, hBo⟩ := recurrence_even_odd hs hQrec hQ0 hQ1 2
  -- the determinant formula in the limit
  have hdet : ∀ n, cfP (fun _ => (1 : ℂ)) b (2 * n + 2) * cfQ (fun _ => 1) b (2 * n + 1) -
      cfQ (fun _ => 1) b (2 * n + 2) * cfP (fun _ => 1) b (2 * n + 1) = 1 := fun n => by
    have := dlmf_1_12_7 (fun _ => (1 : ℂ)) b (2 * n + 1)
    simp only [cfA, cfB, prod_const_one, mul_one] at this
    rw [this, show 2 * n + 1 + 1 = 2 * (n + 1) by ring, pow_mul]
    simp
  have hlim1 : Ao * Be - Bo * Ae = 1 :=
    tendsto_nhds_unique ((hAo.mul hBe).sub (hBo.mul hAe)) (tendsto_const_nhds.congr fun n =>
      (hdet n).symm)
  -- `Aₙ = Cₙ Bₙ` along even and odd indices
  have hAe' : Ae = C * Be := by
    refine tendsto_nhds_unique hAe ?_
    have := (hC.comp (tendsto_id.const_mul_atTop' (by norm_num : (0 : ℕ) < 2))).mul hBe
    refine this.congr fun n => ?_
    show cfA (fun _ => 1) b (2 * n) / cfB (fun _ => 1) b (2 * n) * cfB (fun _ => 1) b (2 * n) =
      cfA (fun _ => 1) b (2 * n)
    rw [div_mul_cancel₀ _ (hB (2 * n))]
  have hAo' : Ao = C * Bo := by
    refine tendsto_nhds_unique hAo ?_
    have := (hC.comp ((tendsto_add_atTop_nat 1).comp
      (tendsto_id.const_mul_atTop' (by norm_num : (0 : ℕ) < 2)))).mul hBo
    refine this.congr fun n => ?_
    show cfA (fun _ => 1) b (2 * n + 1) / cfB (fun _ => 1) b (2 * n + 1) *
      cfB (fun _ => 1) b (2 * n + 1) = cfA (fun _ => 1) b (2 * n + 1)
    rw [div_mul_cancel₀ _ (hB (2 * n + 1))]
  rw [hAe', hAo'] at hlim1
  have : (1 : ℂ) = 0 := by rw [← hlim1]; ring
  exact one_ne_zero this

/-! ### A power-series form of Vitali's theorem -/

/-- If `|a_{n,k}| ≤ M/Rᵏ` and `∑ₖ a_{n,k} tᵏ` converges as `n → ∞` for all `t` in a set
accumulating at `0`, then each coefficient `a_{n,k}` converges. -/
theorem coeff_tendsto_of_bounded {a : ℕ → ℕ → ℂ} {M R : ℝ} (hM : 0 < M) (hR : 0 < R)
    (ha : ∀ n k, ‖a n k‖ ≤ M / R ^ k) {E : Set ℂ} (hE : ∀ ε > 0, ∃ t ∈ E, t ≠ 0 ∧ ‖t‖ < ε)
    (hconv : ∀ t ∈ E, ∃ L, Tendsto (fun n => ∑' k, a n k * t ^ k) atTop (𝓝 L)) :
    ∀ k, ∃ α, Tendsto (fun n => a n k) atTop (𝓝 α) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    choose α hα using ih
    apply cauchySeq_tendsto_of_complete
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨t, htE, ht0, htsmall⟩ := hE (min (R / 2) (ε * R ^ (k + 1) / (6 * M)))
      (by positivity)
    have ht1 : ‖t‖ ≤ R / 2 := htsmall.le.trans (min_le_left _ _)
    have ht2 : ‖t‖ ≤ ε * R ^ (k + 1) / (6 * M) := htsmall.le.trans (min_le_right _ _)
    set q := ‖t‖ / R with hq
    have hq0 : 0 ≤ q := by positivity
    have hq1 : q ≤ 1 / 2 := by rw [hq, div_le_iff₀ hR]; linarith
    -- summability and the tail bound
    have hsumm : ∀ n, Summable fun j => a n j * t ^ j := fun n =>
      Summable.of_norm_bounded ((summable_geometric_of_lt_one hq0 (by linarith)).mul_left M)
        fun j => by
          rw [norm_mul, norm_pow, hq, div_pow, ← mul_div_assoc]
          calc ‖a n j‖ * ‖t‖ ^ j ≤ M / R ^ j * ‖t‖ ^ j :=
                mul_le_mul_of_nonneg_right (ha n j) (by positivity)
            _ = M * ‖t‖ ^ j / R ^ j := by ring
    set T : ℕ → ℂ := fun n => ∑' j, a n (j + (k + 1)) * t ^ (j + 1) with hT
    have hTbound : ∀ n, ‖T n‖ ≤ ε / 3 := by
      intro n
      have hgeo : Summable fun j : ℕ => M / R ^ k * q ^ (j + 1) :=
        ((summable_geometric_of_lt_one hq0 (by linarith)).mul_left (M / R ^ k * q)).congr
          fun j => by ring
      have hbd : ∀ j, ‖a n (j + (k + 1)) * t ^ (j + 1)‖ ≤ M / R ^ k * q ^ (j + 1) := by
        intro j
        rw [norm_mul, norm_pow, hq, div_pow]
        calc ‖a n (j + (k + 1))‖ * ‖t‖ ^ (j + 1) ≤ M / R ^ (j + (k + 1)) * ‖t‖ ^ (j + 1) :=
              mul_le_mul_of_nonneg_right (ha _ _) (by positivity)
          _ = M / R ^ k * (‖t‖ ^ (j + 1) / R ^ (j + 1)) := by
              rw [show j + (k + 1) = k + (j + 1) by ring, pow_add]
              field_simp
      calc ‖T n‖ ≤ ∑' j, M / R ^ k * q ^ (j + 1) :=
            tsum_of_norm_bounded hgeo.hasSum hbd
        _ = M / R ^ k * (q / (1 - q)) := by
            rw [tsum_mul_left]
            congr 1
            rw [show (fun j : ℕ => q ^ (j + 1)) = fun j => q * q ^ j from funext fun j => by ring,
              tsum_mul_left, tsum_geometric_of_lt_one hq0 (by linarith), div_eq_mul_inv]
        _ ≤ M / R ^ k * (2 * q) := by
            gcongr
            rw [div_le_iff₀ (by linarith)]
            nlinarith
        _ ≤ ε / 3 := by
            rw [hq]
            have : M / R ^ k * (2 * (‖t‖ / R)) = 2 * M * ‖t‖ / R ^ (k + 1) := by
              rw [pow_succ]; field_simp
            rw [this, div_le_iff₀ (by positivity)]
            calc 2 * M * ‖t‖ ≤ 2 * M * (ε * R ^ (k + 1) / (6 * M)) := by gcongr
              _ = ε / 3 * R ^ (k + 1) := by field_simp; ring
    -- the decomposition `a_{n,k} = Q_n − T_n`
    set F : ℕ → ℂ := fun n => ∑ j ∈ range k, a n j * t ^ j with hF
    have hdecomp : ∀ n, a n k = ((∑' j, a n j * t ^ j) - F n) / t ^ k - T n := by
      intro n
      have h1 := (Summable.sum_add_tsum_nat_add (k + 1) (hsumm n)).symm
      rw [sum_range_succ] at h1
      have h2 : ∑' j, a n (j + (k + 1)) * t ^ (j + (k + 1)) = t ^ k * T n := by
        rw [hT, ← tsum_mul_left]
        congr 1
        funext j
        ring
      rw [h1, h2]
      have : t ^ k ≠ 0 := pow_ne_zero _ ht0
      field_simp
      ring
    obtain ⟨L, hL⟩ := hconv t htE
    set g : ℕ → ℂ := fun j => if h : j < k then α j h else 0 with hg
    have hFlim : Tendsto F atTop (𝓝 (∑ j ∈ range k, g j * t ^ j)) := by
      refine tendsto_finsetSum _ fun j hj => ?_
      have hj' := mem_range.mp hj
      have : g j = α j hj' := by simp [hg, hj']
      rw [this]
      exact (hα j hj').mul_const _
    have hQ : Tendsto (fun n => ((∑' j, a n j * t ^ j) - F n) / t ^ k) atTop
        (𝓝 ((L - ∑ j ∈ range k, g j * t ^ j) / t ^ k)) := (hL.sub hFlim).div_const _
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hQ.cauchySeq (ε / 3) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [dist_eq_norm, hdecomp m, hdecomp n]
    have h := hN m hm n hn
    rw [dist_eq_norm] at h
    set Qm := ((∑' j, a m j * t ^ j) - F m) / t ^ k
    set Qn := ((∑' j, a n j * t ^ j) - F n) / t ^ k
    have e : Qm - T m - (Qn - T n) = (Qm - Qn) - T m + T n := by ring
    rw [e]
    calc ‖(Qm - Qn) - T m + T n‖ ≤ ‖(Qm - Qn) - T m‖ + ‖T n‖ := norm_add_le _ _
      _ ≤ ‖Qm - Qn‖ + ‖T m‖ + ‖T n‖ := by gcongr; exact norm_sub_le _ _
      _ < ε := by linarith [hTbound m, hTbound n]

/-- **Vitali, power-series form**: under the hypotheses of `coeff_tendsto_of_bounded`,
`∑ₖ a_{n,k} zᵏ` converges as `n → ∞` for every `|z| < R`. -/
theorem tendsto_of_bounded_power_series {a : ℕ → ℕ → ℂ} {M R : ℝ} (hM : 0 < M) (hR : 0 < R)
    (ha : ∀ n k, ‖a n k‖ ≤ M / R ^ k) {E : Set ℂ} (hE : ∀ ε > 0, ∃ t ∈ E, t ≠ 0 ∧ ‖t‖ < ε)
    (hconv : ∀ t ∈ E, ∃ L, Tendsto (fun n => ∑' k, a n k * t ^ k) atTop (𝓝 L)) {z : ℂ}
    (hz : ‖z‖ < R) : ∃ L, Tendsto (fun n => ∑' k, a n k * z ^ k) atTop (𝓝 L) := by
  choose α hα using coeff_tendsto_of_bounded hM hR ha hE hconv
  have hq : ‖z‖ / R < 1 := (div_lt_one hR).mpr hz
  refine ⟨∑' k, α k * z ^ k, tendsto_tsum_of_dominated_convergence
    (bound := fun k => M * (‖z‖ / R) ^ k)
    ((summable_geometric_of_lt_one (by positivity) hq).mul_left M)
    (fun k => (hα k).mul_const _) (Eventually.of_forall fun n k => ?_)⟩
  rw [norm_mul, norm_pow, div_pow]
  calc ‖a n k‖ * ‖z‖ ^ k ≤ M / R ^ k * ‖z‖ ^ k :=
        mul_le_mul_of_nonneg_right (ha n k) (by positivity)
    _ = M * (‖z‖ ^ k / R ^ k) := by ring

/-! ### Holomorphic families of continued fractions -/

theorem VVSector.re_pos {δ : ℝ} (hs : 0 ≤ Real.sin δ) (hc : 0 < Real.cos δ) {z : ℂ}
    (hz : z ∈ VVSector δ) : 0 < z.re := by
  have : 0 ≤ |z.im| * Real.sin δ := by positivity
  exact (mul_pos_iff_of_pos_right hc).mp (lt_of_le_of_lt this hz)

/-- If the elements `c(z)ₖ` (`k ≥ 1`) depend holomorphically on `z ∈ U` and stay in a sector,
then so do the tails `C_n(W(z))` of `1/(c₁(z) + 1/(c₂(z) + ⋯))`. -/
theorem cfw_differentiableOn {c : ℂ → ℕ → ℂ} {U : Set ℂ} {δ : ℝ} (hs : 0 ≤ Real.sin δ)
    (hcd : ∀ k, DifferentiableOn ℂ (fun z => c z k) U)
    (hcS : ∀ z ∈ U, ∀ k ≥ 1, c z k ∈ VVSector δ) :
    ∀ n (W : ℂ → ℂ), DifferentiableOn ℂ W U → (∀ z ∈ U, W z ∈ VVSector δ) →
      DifferentiableOn ℂ (fun z => cfw (fun _ => 1) (c z) n (W z)) U := by
  intro n
  induction n with
  | zero =>
    intro W hW _
    have h : DifferentiableOn ℂ (fun z => c z 0 + W z) U := (hcd 0).add hW
    simpa only [cfw] using h
  | succ n ih =>
    intro W hW hWS
    have hsum : ∀ z ∈ U, c z (n + 1) + W z ∈ VVSector δ := fun z hz =>
      VVSector.add (hcS z hz (n + 1) (by omega)) (hWS z hz) hs
    refine ih (fun z => 1 / (c z (n + 1) + W z)) ?_ fun z hz => by
      rw [one_div]; exact VVSector.inv (hsum z hz)
    exact (differentiableOn_const 1).div ((hcd (n + 1)).add hW) fun z hz =>
      VVSector.ne_zero (hsum z hz)

theorem cfConv_differentiableOn {c : ℂ → ℕ → ℂ} {U : Set ℂ} {δ : ℝ} (hs : 0 ≤ Real.sin δ)
    (hcd : ∀ k, DifferentiableOn ℂ (fun z => c z k) U) (hcS : ∀ z ∈ U, ∀ k ≥ 1, c z k ∈ VVSector δ)
    (n : ℕ) : DifferentiableOn ℂ (fun z => cfConv (fun _ => 1) (c z) n) U := by
  rcases n with _ | m
  · simpa [cfConv, cfw] using hcd 0
  · have hS : ∀ z ∈ U, c z (m + 1) + 0 ∈ VVSector δ := fun z hz => by
      simpa using hcS z hz (m + 1) (by omega)
    have := cfw_differentiableOn hs hcd hcS m (fun z => 1 / (c z (m + 1) + 0))
      ((differentiableOn_const 1).div ((hcd (m + 1)).add (differentiableOn_const 0))
        fun z hz => VVSector.ne_zero (hS z hz))
      fun z hz => by rw [one_div]; exact VVSector.inv (hS z hz)
    exact this

/-- `|Cₙ| ≤ 1/Re b₁` for `1/(b₁ + 1/(b₂ + ⋯))` (`b₀ = 0`) with elements in a sector. -/
theorem norm_cfConv_le {b : ℕ → ℂ} {δ : ℝ} (hs : 0 ≤ Real.sin δ) (hc : 0 < Real.cos δ)
    (hb0 : b 0 = 0) (hb : ∀ n ≥ 1, b n ∈ VVSector δ) (n : ℕ) :
    ‖cfConv (fun _ => 1) b n‖ ≤ 1 / (b 1).re := by
  have hre1 : 0 < (b 1).re := VVSector.re_pos hs hc (hb 1 le_rfl)
  rcases n with _ | m
  · simp [cfConv, cfw, hb0]
    positivity
  · rw [cfConv, cfw_succ_shift, hb0, zero_add, norm_div, norm_one]
    set D := cfw (fun k => (fun _ => (1 : ℂ)) (k + 1)) (fun k => b (k + 1)) m 0
    have hD : (b 1).re ≤ D.re := by
      rcases m with _ | m'
      · simp [D, cfw]
      · have hb' : ∀ n ≥ 1, b (n + 1) ∈ VVSector δ := fun n _ => hb (n + 1) (by omega)
        have hW : b (m' + 1 + 1) + 0 ∈ VVSector δ := by simpa using hb (m' + 2) (by omega)
        obtain ⟨-, h2⟩ := sector_tails (b := fun k => b (k + 1)) hs hb' m'
          (1 / (b (m' + 1 + 1) + 0)) (by rw [one_div]; exact VVSector.inv hW)
        have := VVSector.re_pos hs hc h2
        simp only [D, cfw]
        rw [sub_re] at this
        linarith
    have hDpos : 0 < D.re := lt_of_lt_of_le hre1 hD
    calc 1 / ‖D‖ ≤ 1 / D.re := one_div_le_one_div_of_le hDpos (re_le_norm D)
      _ ≤ 1 / (b 1).re := one_div_le_one_div_of_le hre1 hD

/-! ### The family `bₖ(z) = |bₖ| e^{iz ph bₖ}` -/

/-- `bₖ(z) = |bₖ| e^{iz ph bₖ}` (`b₀(z) = 0`): `bₖ(1) = bₖ`, and `bₖ(iy) > 0` for real `y`. -/
noncomputable def vvFamily (b : ℕ → ℂ) (z : ℂ) (k : ℕ) : ℂ :=
  if k = 0 then 0 else (‖b k‖ : ℂ) * exp (z * (arg (b k) : ℂ) * I)

theorem vvFamily_one {b : ℕ → ℂ} (hb0 : b 0 = 0) : vvFamily b 1 = b := by
  funext k
  by_cases hk : k = 0
  · simp [vvFamily, hk, hb0]
  · simp only [vvFamily, hk, ↓reduceIte, one_mul]
    exact norm_mul_exp_arg_mul_I (b k)

/-- The positive elements `|bₖ| e^{−y ph bₖ}` on the imaginary axis. -/
noncomputable def vvReal (b : ℕ → ℂ) (y : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 0 else ‖b k‖ * Real.exp (-(y * arg (b k)))

theorem vvFamily_imag (b : ℕ → ℂ) (y : ℝ) :
    vvFamily b (y * I) = fun k => ((vvReal b y k : ℝ) : ℂ) := by
  funext k
  by_cases hk : k = 0
  · simp [vvFamily, vvReal, hk]
  · simp only [vvFamily, vvReal, hk, ↓reduceIte]
    rw [show (y : ℂ) * I * (arg (b k) : ℂ) * I = ((-(y * arg (b k)) : ℝ) : ℂ) by
      push_cast; ring_nf; rw [I_sq]; ring]
    push_cast
    rfl

theorem vvFamily_differentiable (b : ℕ → ℂ) (k : ℕ) :
    Differentiable ℂ fun z => vvFamily b z k := by
  unfold vvFamily
  split_ifs
  · exact differentiable_const _
  · fun_prop

/-- For `|z| < ρ` with `ρ(π/2 − δ) < π/2`, the elements `bₖ(z)` lie in the sector of half-angle
`ρ(π/2 − δ)`. -/
theorem vvFamily_sector {b : ℕ → ℂ} {δ ρ : ℝ} (hδ : δ < π / 2)
    (hb : ∀ k ≥ 1, |arg (b k)| < π / 2 - δ) (hbne : ∀ k ≥ 1, b k ≠ 0)
    (hρ : ρ * (π / 2 - δ) < π / 2) {z : ℂ} (hz : ‖z‖ < ρ) {k : ℕ} (hk : 1 ≤ k) :
    vvFamily b z k ∈ VVSector (π / 2 - ρ * (π / 2 - δ)) := by
  set δ' := π / 2 - ρ * (π / 2 - δ) with hδ'
  set θ := arg (b k)
  have hθ := hb k hk
  have hpos : 0 < ‖b k‖ := norm_pos_iff.mpr (hbne k hk)
  set ψ := z.re * θ with hψ
  have hψb : |ψ| < π / 2 - δ' := by
    rw [hδ', hψ, abs_mul]
    have h1 : |z.re| < ρ := (abs_re_le_norm z).trans_lt hz
    calc |z.re| * |θ| ≤ |z.re| * (π / 2 - δ) := by gcongr
      _ < ρ * (π / 2 - δ) := by gcongr
      _ = π / 2 - (π / 2 - ρ * (π / 2 - δ)) := by ring
  have hδ'0 : 0 < δ' := by rw [hδ']; linarith
  -- `cos(|ψ| + δ') > 0`
  have hcos : |Real.sin ψ| * Real.sin δ' < Real.cos ψ * Real.cos δ' := by
    have hc : 0 < Real.cos (|ψ| + δ') :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [abs_nonneg ψ], by linarith⟩
    rw [Real.cos_add] at hc
    rcases abs_cases ψ with ⟨h, hge⟩ | ⟨h, hlt⟩
    · rw [h] at hc
      rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hge (by linarith [abs_nonneg ψ]))]
      linarith
    · rw [h, Real.cos_neg, Real.sin_neg] at hc
      rw [abs_of_nonpos (Real.sin_nonpos_of_nonpos_of_neg_pi_le hlt.le (by linarith))]
      linarith
  simp only [VVSector, Set.mem_ofPred_eq, vvFamily, show k ≠ 0 by omega, ↓reduceIte]
  rw [re_ofReal_mul, im_ofReal_mul, exp_re, exp_im]
  have hre : (z * (θ : ℂ) * I).re = -(z.im * θ) := by simp
  have him : (z * (θ : ℂ) * I).im = ψ := by simp [hψ]
  rw [hre, him]
  set e := Real.exp (-(z.im * θ))
  have he : 0 < ‖b k‖ * e := by positivity
  rw [show ‖b k‖ * (e * Real.sin ψ) = (‖b k‖ * e) * Real.sin ψ by ring,
    show ‖b k‖ * (e * Real.cos ψ) = (‖b k‖ * e) * Real.cos ψ by ring, abs_mul, abs_of_pos he]
  nlinarith

/-! ### Van Vleck's theorem -/

/-- **Van Vleck's theorem** (DLMF 1.12.26–1.12.28): if the elements of `1/(b₁ + 1/(b₂ + ⋯))`
satisfy `−π/2 + δ < ph bₙ < π/2 − δ` (`bₙ ≠ 0`), then the even and odd parts converge to finite
values, and the continued fraction converges iff `∑ |bₙ| = ∞`. -/
theorem dlmf_1_12_28 {b : ℕ → ℂ} {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < π / 2) (hb0 : b 0 = 0)
    (hbne : ∀ n ≥ 1, b n ≠ 0)
    (hb : ∀ n ≥ 1, -(π / 2) + δ < arg (b n) ∧ arg (b n) < π / 2 - δ) :
    (∃ L, Tendsto (fun n => cfConv (fun _ => 1) b (2 * n)) atTop (𝓝 L)) ∧
    (∃ L, Tendsto (fun n => cfConv (fun _ => 1) b (2 * n + 1)) atTop (𝓝 L)) ∧
    (CfConvergent (fun _ => 1) b ↔ ¬ Summable fun n => ‖b n‖) := by
  have hbabs : ∀ k ≥ 1, |arg (b k)| < π / 2 - δ := fun k hk =>
    abs_lt.mpr ⟨by linarith [(hb k hk).1], (hb k hk).2⟩
  have hpd : 0 < π / 2 - δ := by linarith
  -- radii `1 < R < ρ < (π/2)/(π/2 − δ)`
  set X := (π / 2) / (π / 2 - δ) with hX
  have hX1 : 1 < X := by rw [hX, one_lt_div hpd]; linarith
  set ρ := (1 + X) / 2 with hρdef
  set R := (1 + ρ) / 2 with hRdef
  have hR1 : 1 < R := by rw [hRdef, hρdef]; linarith
  have hRρ : R < ρ := by rw [hRdef, hρdef]; linarith
  have hρX : ρ * (π / 2 - δ) < π / 2 := by
    have : ρ < X := by rw [hρdef]; linarith
    calc ρ * (π / 2 - δ) < X * (π / 2 - δ) := by gcongr
      _ = π / 2 := by rw [hX, div_mul_cancel₀ _ hpd.ne']
  have hR0 : 0 < R := by linarith
  set δ' := π / 2 - ρ * (π / 2 - δ) with hδ'
  have hδ'0 : 0 < δ' := by rw [hδ']; linarith
  have hδ'1 : δ' < π / 2 := by rw [hδ']; nlinarith
  have hs' : 0 ≤ Real.sin δ' := (Real.sin_pos_of_pos_of_lt_pi hδ'0 (by linarith)).le
  have hc' : 0 < Real.cos δ' := Real.cos_pos_of_mem_Ioo ⟨by linarith, hδ'1⟩
  set U := ball (0 : ℂ) ρ
  set c : ℂ → ℕ → ℂ := vvFamily b
  have hcS : ∀ z ∈ U, ∀ k ≥ 1, c z k ∈ VVSector δ' := fun z hz k hk =>
    vvFamily_sector hδ hbabs hbne hρX (mem_ball_zero_iff.mp hz) hk
  have hcd : ∀ k, DifferentiableOn ℂ (fun z => c z k) U := fun k =>
    (vvFamily_differentiable b k).differentiableOn
  set F : ℕ → ℂ → ℂ := fun n z => cfConv (fun _ => 1) (c z) n with hF
  have hFd : ∀ n, DifferentiableOn ℂ (F n) U := fun n => cfConv_differentiableOn hs' hcd hcS n
  -- a uniform bound on `|z| ≤ R`
  have hcb : closedBall (0 : ℂ) R ⊆ U := closedBall_subset_ball hRρ
  obtain ⟨z₀, hz₀, hmin⟩ := (isCompact_closedBall (0 : ℂ) R).exists_isMinOn
    ⟨0, mem_closedBall_self hR0.le⟩
    ((continuous_re.comp (vvFamily_differentiable b 1).continuous).continuousOn)
  set m₀ := (c z₀ 1).re
  have hm₀ : 0 < m₀ := VVSector.re_pos hs' hc' (hcS z₀ (hcb hz₀) 1 le_rfl)
  set M := 1 / m₀
  have hM : 0 < M := by positivity
  have hbound : ∀ n, ∀ z ∈ closedBall (0 : ℂ) R, ‖F n z‖ ≤ M := by
    intro n z hz
    have h0 : c z 0 = 0 := by simp [c, vvFamily]
    have h1 := norm_cfConv_le hs' hc' h0 (hcS z (hcb hz)) n
    have h2 : m₀ ≤ (c z 1).re := hmin hz
    exact h1.trans (one_div_le_one_div_of_le hm₀ h2)
  -- Taylor coefficients with Cauchy bounds
  set a : ℕ → ℕ → ℂ := fun n k => ((k ! : ℂ))⁻¹ * iteratedDeriv k (F n) 0 with ha
  have hab : ∀ n k, ‖a n k‖ ≤ M / R ^ k := by
    intro n k
    have h := norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hR0
      ((hFd n).diffContOnCl_ball hcb) fun z hz => hbound n z (sphere_subset_closedBall hz)
    have hk : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
    rw [ha, norm_mul, norm_inv, Complex.norm_natCast]
    rw [mul_div_assoc] at h
    calc (k ! : ℝ)⁻¹ * ‖iteratedDeriv k (F n) 0‖ ≤ (k ! : ℝ)⁻¹ * (k ! * (M / R ^ k)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = M / R ^ k := by field_simp
  have hrep : ∀ n z, z ∈ U → F n z = ∑' k, a n k * z ^ k := by
    intro n z hz
    rw [← (Complex.hasSum_taylorSeries_on_ball (hFd n) hz).tsum_eq]
    congr 1
    funext k
    simp only [ha, sub_zero, smul_eq_mul]
    ring
  -- the imaginary axis: positive elements
  set E : Set ℂ := {t | ∃ y : ℝ, 0 < y ∧ y < R ∧ t = y * I} with hEdef
  have hE : ∀ ε > 0, ∃ t ∈ E, t ≠ 0 ∧ ‖t‖ < ε := by
    intro ε hε
    set y := min (ε / 2) (R / 2)
    have hy : 0 < y := by positivity
    refine ⟨y * I, ⟨y, hy, by linarith [min_le_right (ε / 2) (R / 2)], rfl⟩, by simp [hy.ne'],
      ?_⟩
    rw [norm_mul, norm_I, mul_one, norm_real, Real.norm_of_nonneg hy.le]
    linarith [min_le_left (ε / 2) (R / 2)]
  have hβpos : ∀ y : ℝ, ∀ k ≥ 1, 0 < vvReal b y k := fun y k hk => by
    simp only [vvReal, show k ≠ 0 by omega, ↓reduceIte]
    exact mul_pos (norm_pos_iff.mpr (hbne k hk)) (Real.exp_pos _)
  have hFimag : ∀ y : ℝ, ∀ n, F n (y * I) = ((posC (vvReal b y) n : ℝ) : ℂ) := by
    intro y n
    have hc : c (y * I) = fun k => ((vvReal b y k : ℝ) : ℂ) := vvFamily_imag b y
    simp only [hF, hc]
    have hmap := cfw_map Complex.ofRealHom (fun _ => (1 : ℝ)) (vvReal b y) n 0
    simp only [map_one, map_zero, Complex.ofRealHom_eq_coe] at hmap
    rw [cfConv, hmap, ← cfConv,
      dlmf_1_12_4 _ _ (pos_cfNonzero (hβpos y) n 0 le_rfl)]
    rfl
  have hEmem : ∀ t ∈ E, t ∈ U := by
    rintro t ⟨y, hy, hyR, rfl⟩
    rw [mem_ball_zero_iff, norm_mul, norm_I, mul_one, norm_real, Real.norm_of_nonneg hy.le]
    linarith
  -- transfer convergence along the imaginary axis to `z = 1`
  have htransfer : ∀ σ : ℕ → ℕ, (∀ y : ℝ, 0 < y → ∃ L : ℝ,
      Tendsto (fun n => posC (vvReal b y) (σ n)) atTop (𝓝 L)) →
      ∃ L, Tendsto (fun n => cfConv (fun _ => 1) b (σ n)) atTop (𝓝 L) := by
    intro σ hσ
    have hconv : ∀ t ∈ E, ∃ L, Tendsto (fun n => ∑' k, a (σ n) k * t ^ k) atTop (𝓝 L) := by
      rintro t ⟨y, hy, hyR, rfl⟩
      obtain ⟨L, hL⟩ := hσ y hy
      refine ⟨(L : ℂ), ((continuous_ofReal.tendsto L).comp hL).congr fun n => ?_⟩
      simp only [Function.comp_apply]
      rw [← hFimag y, hrep _ _ (hEmem _ ⟨y, hy, hyR, rfl⟩)]
    obtain ⟨L, hL⟩ := tendsto_of_bounded_power_series hM hR0 (fun n k => hab (σ n) k) hE hconv
      (z := 1) (by simpa using hR1)
    refine ⟨L, hL.congr fun n => ?_⟩
    rw [← hrep _ _ (by simpa [U] using hR1.trans hRρ)]
    simp only [hF, c, vvFamily_one hb0]
  refine ⟨htransfer (fun n => 2 * n) fun y _ => posC_even_tendsto (hβpos y),
    htransfer (fun n => 2 * n + 1) fun y _ => posC_odd_tendsto (hβpos y), ⟨?_, ?_⟩⟩
  · -- convergence forces `∑ |bₙ| = ∞` (Stern–Stolz)
    rintro ⟨C, hC⟩ hsum
    have hs : 0 ≤ Real.sin δ := (Real.sin_pos_of_pos_of_lt_pi hδ0 (by linarith)).le
    have hbS : ∀ k ≥ 1, b k ∈ VVSector δ := fun k hk =>
      (arg_sector_iff hδ0 hδ (hbne k hk)).mp (hb k hk)
    refine stern_stolz hb0 hsum (fun n => (sector_denom hs hbS n).1) ⟨C, hC.congr fun n => ?_⟩
    exact dlmf_1_12_4 _ _ (sector_nonzero hs hbS n)
  · -- `∑ |bₙ| = ∞` gives convergence on the imaginary axis (Seidel–Stern)
    intro hns
    have hβ0 : ∀ y, vvReal b y 0 = 0 := fun y => by simp [vvReal]
    have hall : ∀ y : ℝ, 0 < y → ∃ L : ℝ, Tendsto (fun n => posC (vvReal b y) n) atTop (𝓝 L) := by
      intro y hy
      refine posC_tendsto (hβ0 y) (hβpos y) fun hsumm => hns ?_
      refine (hsumm.mul_left (Real.exp (y * (π / 2)))).of_nonneg_of_le (fun _ => norm_nonneg _)
        fun k => ?_
      by_cases hk : k = 0
      · simp [hk, hb0, vvReal]
      · simp only [vvReal, hk, ↓reduceIte]
        have hθ : y * arg (b k) ≤ y * (π / 2) := by
          have := hbabs k (by omega)
          have : arg (b k) ≤ π / 2 := by linarith [le_abs_self (arg (b k))]
          exact mul_le_mul_of_nonneg_left this hy.le
        rw [← mul_assoc, mul_comm (Real.exp _), mul_assoc, ← Real.exp_add]
        calc ‖b k‖ = ‖b k‖ * 1 := (mul_one _).symm
          _ ≤ ‖b k‖ * Real.exp (y * (π / 2) + -(y * arg (b k))) := by
              gcongr
              exact Real.one_le_exp (by linarith)
    obtain ⟨L, hL⟩ := htransfer id fun y hy => hall y hy
    exact ⟨L, hL⟩

end Azurite.DLMF
