/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.Agm
import Azurite.AzFloat.Equiv.EnclWidth
import Azurite.AzFloat.Equiv.LnGammaEventually
import Azurite.AzFloat.Equiv.ZivSpec

/-!
# The width of the interval AGM

The interval iteration of `AzFloat/Agm.lean` converges: at working precision `w`, from
enclosures of `a` and `b` of relative width `λ₀` and with `fuel` steps allowed, the final
bracket `[bLo, aHi]` of `AGM(a, b)` has width at most `agmEps (max a b) Λ fuel w` with
`Λ = λ₀ + 9 (fuel + 1) 2^(−w)` (`agm_bracket_width`), which tends to `0` when `fuel` grows
like `w` (`tendsto_agmEps`).

* `LEncl.add'`, `lencl_sqrt`, `lencl_half`: relative widths through a sum, a square root and a
  halving.
* `RelEnc`: the four bounds enclose the exact pair `(a_n, b_n)` with relative width `λ`;
  `relEnc_agmStep` (a step adds `9 · 2^(−w)`), `relEnc_agmIter`.
* `agmConverged_spec`: the stopping test bounds the width directly.
* **`agmApproxFrom_bracketConv`**, and `agmApprox_bracketConv`, `agmRatApprox_bracketConv`,
  `agmFloatRatApprox_bracketConv`: the brackets of the three AGM functions converge
  (`BracketConv`).
-/

namespace Azurite.AzFloat

open Azurite.BZ Filter Topology

variable {a b : ℝ}

/-! ### Relative widths through the operations of a step -/

/-- A sum of two enclosures of the same relative width. -/
theorem LEncl.add' {A B : Encl} {x y lam : ℝ} {w : ℕ} [NeZero w]
    (hu : (1 / 2 : ℝ) ^ w ≤ 1 / 8) (ha : LEncl A x lam) (hb : LEncl B y lam) :
    LEncl (Encl.add w A B) (x + y) (lam + 6 * (1 / 2 : ℝ) ^ w) := by
  obtain ⟨l₁, h₁, hl₁, hh₁, p₁, a₁, b₁, c₁⟩ := ha
  obtain ⟨l₂, h₂, hl₂, hh₂, p₂, a₂, b₂, c₂⟩ := hb
  obtain ⟨r, hr, hfr⟩ := addFloor_err hl₁ hl₂ w (by linarith)
  obtain ⟨s, hs, hcs⟩ := addCeiling_err hh₁ hh₂ w (by linarith)
  obtain ⟨hr0, hrs⟩ := round_pos_combine (lam := lam) (by linarith : 0 < l₁ + l₂)
    (by rw [add_mul]; linarith : h₁ + h₂ ≤ (l₁ + l₂) * Real.exp lam) (by positivity) hu
    hfr.ge hcs.le
  exact ⟨r, s, hr, hs, hr0, by linarith [hfr.le], by linarith [hcs.ge], hrs⟩

theorem sqrt_exp (t : ℝ) : Real.sqrt (Real.exp t) = Real.exp (t / 2) := by
  have h : Real.exp t = Real.exp (t / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [h, Real.sqrt_sq (Real.exp_pos _).le]

/-- The square root halves the relative width. -/
theorem lencl_sqrt {lo hi : AzFloat} {x lam : ℝ} {w : ℕ} [NeZero w]
    (hu : (1 / 2 : ℝ) ^ w ≤ 1 / 8) (h : LEncl (lo, hi) x lam) :
    LEncl ((sqrtPrecRound lo w .Floor).1, (sqrtPrecRound hi w .Ceiling).1) (Real.sqrt x)
      (lam / 2 + 6 * (1 / 2 : ℝ) ^ w) := by
  obtain ⟨l, h', hl, hh, p, a₁, b₁, c₁⟩ := h
  obtain ⟨r, hr, hfr⟩ := sqrtFloor_err hl p.le w
  obtain ⟨s, hs, hcs⟩ := sqrtCeiling_err hh (by linarith) w
  have hsq : Real.sqrt h' ≤ Real.sqrt l * Real.exp (lam / 2) := by
    calc Real.sqrt h' ≤ Real.sqrt (l * Real.exp lam) := Real.sqrt_le_sqrt c₁
      _ = Real.sqrt l * Real.exp (lam / 2) := by rw [Real.sqrt_mul p.le, sqrt_exp]
  obtain ⟨hr0, hrs⟩ := round_pos_combine (lam := lam / 2) (Real.sqrt_pos.mpr p) hsq
    (by positivity) hu hfr.ge hcs.le
  exact ⟨r, s, hr, hs, hr0, hfr.le.trans (Real.sqrt_le_sqrt a₁),
    (Real.sqrt_le_sqrt b₁).trans hcs.ge, hrs⟩

/-- Halving keeps the relative width. -/
theorem lencl_half {lo hi : AzFloat} {x lam : ℝ} (h : LEncl (lo, hi) x lam) :
    LEncl (lo >>> (1 : ℕ), hi >>> (1 : ℕ)) (x / 2) lam := by
  obtain ⟨l, h', hl, hh, p, a₁, b₁, c₁⟩ := h
  exact ⟨l / 2, h' / 2, toVal_half hl, toVal_half hh, by linarith, by linarith, by linarith,
    by linarith⟩

/-! ### The relative enclosure of the iterates -/

/-- The bounds enclose the exact pair `(a_n, b_n)` with relative width `lam`. -/
def RelEnc (a b : ℝ) (n : ℕ) (lam : ℝ) (s : AgmBounds) : Prop :=
  LEncl (s.aLo, s.aHi) (agmA a b n) lam ∧ LEncl (s.bLo, s.bHi) (agmB a b n) lam

theorem RelEnc.mono {n : ℕ} {lam lam' : ℝ} {s : AgmBounds} (h : RelEnc a b n lam s)
    (hl : lam ≤ lam') : RelEnc a b n lam' s :=
  ⟨h.1.mono hl, h.2.mono hl⟩

/-- **One interval step adds `9 · 2^(−w)` to the relative width.** -/
theorem relEnc_agmStep {n : ℕ} {lam : ℝ} {s : AgmBounds} (w : ℕ) [NeZero w]
    (hu : (1 / 2 : ℝ) ^ w ≤ 1 / 8) (h : RelEnc a b n lam s) :
    RelEnc a b (n + 1) (lam + 9 * (1 / 2 : ℝ) ^ w) (agmStep w s) := by
  have hu0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
  refine ⟨?_, ?_⟩
  · rw [agmA_succ]
    exact (lencl_half (LEncl.add' hu h.1 h.2)).mono (by linarith)
  · rw [agmB_succ]
    have hm := h.1.mul hu h.2
    have hs := lencl_sqrt hu hm
    exact hs.mono (by linarith)

/-- The stopping test bounds the width of the bracket. -/
theorem agmConverged_spec {w : ℕ} [NeZero w] {s : AgmBounds} {ah bl : ℝ}
    (hah : s.aHi.toVal = some (ah : EReal)) (hbl : s.bLo.toVal = some (bl : EReal))
    (h : agmConverged w s = true) : ah - bl ≤ ah * (1 / 2 : ℝ) ^ (w - 8) := by
  unfold agmConverged at h
  have hnb : (-s.bLo).toVal = some ((-bl : ℝ) : EReal) := by
    rw [toVal_neg, hbl, Option.map_some, EReal.coe_neg]
  obtain ⟨r, hr, hrge⟩ := addCeiling_spec hah hnb w
  have hsh : (s.aHi >>> (w - 8)).toVal = some ((ah * (1 / 2 : ℝ) ^ (w - 8) : ℝ) : EReal) := by
    show (shiftRight s.aHi (AzNat.ofNat (w - 8)).toAzInt).toVal = _
    rw [toVal_shiftRight, hah, Option.map_some, AzNat.toInt_toAzInt, AzNat.toNat_ofNat,
      ← EReal.coe_mul, zpow_neg, zpow_natCast, one_div_pow, one_div]
  have := (le_eq_true_iff hr hsh).mp h
  linarith

/-- **The iteration**: after at most `fuel` more steps the relative width has grown by at
most `9 fuel 2^(−w)`, and either the stopping test holds or all the steps were made. -/
theorem relEnc_agmIter (w : ℕ) [NeZero w] (hu : (1 / 2 : ℝ) ^ w ≤ 1 / 8) :
    ∀ (fuel : ℕ) (s : AgmBounds) (n : ℕ) (lam : ℝ), RelEnc a b n lam s →
      ∃ m, n ≤ m ∧ RelEnc a b m (lam + 9 * (1 / 2 : ℝ) ^ w * fuel) (agmIter w fuel s) ∧
        (agmConverged w (agmIter w fuel s) = true ∨ m = n + fuel)
  | 0, s, n, lam, h => ⟨n, le_rfl, by simpa [agmIter] using h, Or.inr rfl⟩
  | fuel + 1, s, n, lam, h => by
    have hu0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
    rw [agmIter]
    split_ifs with hc
    · exact ⟨n, le_rfl, h.mono (by
        have : (0 : ℝ) ≤ ((fuel + 1 : ℕ) : ℝ) := by positivity
        nlinarith), Or.inl hc⟩
    · obtain ⟨m, hm, hm', hm''⟩ := relEnc_agmIter w hu fuel (agmStep w s) (n + 1) _
        (relEnc_agmStep w hu h)
      refine ⟨m, by omega, hm'.mono (le_of_eq ?_), hm''.imp_right fun h => by omega⟩
      push_cast
      ring

/-! ### The width of the bracket -/

/-- The bound for the width of the AGM bracket: `M` bounds the arguments, `Λ` the relative
width of the bounds, `fuel` the number of steps. -/
noncomputable def agmEps (M Λ : ℝ) (fuel w : ℕ) : ℝ :=
  2 * M * (Real.exp Λ - 1) + M / 2 ^ fuel + M * Real.exp Λ * (1 / 2 : ℝ) ^ (w - 8)

theorem agmA_le_max (ha : 0 < a) (hb : 0 < b) {n : ℕ} (hn : 1 ≤ n) : agmA a b n ≤ max a b := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h1 : agmA a b (k + 1) ≤ agmA a b (0 + 1) := agmA_antitone ha hb (Nat.zero_le k)
  have h2 : agmA a b (0 + 1) ≤ max a b := by
    rw [agmA_succ, agmA_zero, agmB_zero]
    have := le_max_left a b
    have := le_max_right a b
    linarith
  exact h1.trans h2

/-- **The bracket of the interval AGM and its width.** -/
theorem agm_bracket_width (ha : 0 < a) (hb : 0 < b) {w : ℕ} [NeZero w]
    (hu : (1 / 2 : ℝ) ^ w ≤ 1 / 8) {s₀ : AgmBounds} {lam₀ : ℝ} (hlam : 0 ≤ lam₀)
    (h₀ : RelEnc a b 0 lam₀ s₀) (fuel : ℕ) :
    ∃ bl ah : ℝ, (agmIter w fuel (agmStep w s₀)).bLo.toVal = some (bl : EReal) ∧
      (agmIter w fuel (agmStep w s₀)).aHi.toVal = some (ah : EReal) ∧ 0 < bl ∧
      bl ≤ AGM a b ∧ AGM a b ≤ ah ∧
      ah - bl ≤ agmEps (max a b) (lam₀ + 9 * (1 / 2 : ℝ) ^ w * ((fuel + 1 : ℕ) : ℝ)) fuel w := by
  have hu0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
  obtain ⟨m, hm, hrel, hstop⟩ := relEnc_agmIter w hu fuel _ 1 _ (relEnc_agmStep w hu h₀)
  set Λ : ℝ := lam₀ + 9 * (1 / 2 : ℝ) ^ w * ((fuel + 1 : ℕ) : ℝ) with hΛ
  have hΛeq : lam₀ + 9 * (1 / 2 : ℝ) ^ w + 9 * (1 / 2 : ℝ) ^ w * fuel = Λ := by
    rw [hΛ]
    push_cast
    ring
  rw [hΛeq] at hrel
  have hΛ0 : 0 ≤ Λ := by
    rw [hΛ]
    positivity
  obtain ⟨⟨al, ah, hal, hah, pa, a₁, a₂, a₃⟩, ⟨bl, bh, hbl, hbh, pb, b₁, b₂, b₃⟩⟩ := hrel
  have hE1 : 1 ≤ Real.exp Λ := Real.one_le_exp hΛ0
  have hE0 : 0 < Real.exp Λ := Real.exp_pos _
  set M := max a b with hM
  have hAM : agmA a b m ≤ M := agmA_le_max ha hb hm
  obtain ⟨hA0, hB0⟩ := agm_pos ha hb m
  have hBA : agmB a b m ≤ agmA a b m := agmB_le_agmA ha hb hm
  have hM0 : 0 < M := lt_of_lt_of_le hA0 hAM
  have hah_le : ah ≤ M * Real.exp Λ :=
    a₃.trans (mul_le_mul_of_nonneg_right (a₁.trans hAM) hE0.le)
  refine ⟨bl, ah, hbl, hah, pb, b₁.trans (agmB_le_AGM ha hb hm),
    (AGM_le_agmA ha hb hm).trans a₂, ?_⟩
  unfold agmEps
  have hpow8 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (w - 8) := by positivity
  have hfuel0 : (0 : ℝ) < 2 ^ fuel := by positivity
  rcases hstop with hc | hmf
  · have h1 := agmConverged_spec hah hbl hc
    have h2 : ah * (1 / 2 : ℝ) ^ (w - 8) ≤ M * Real.exp Λ * (1 / 2 : ℝ) ^ (w - 8) :=
      mul_le_mul_of_nonneg_right hah_le hpow8
    have h3 : 0 ≤ 2 * M * (Real.exp Λ - 1) := by nlinarith
    have h4 : 0 ≤ M / 2 ^ fuel := by positivity
    linarith
  · -- all the steps were made: the exact gap is small
    have hgap : agmA a b m - agmB a b m ≤ M / 2 ^ fuel := by
      rw [hmf, show 1 + fuel = fuel + 1 by ring]
      refine (agm_gap_le_half_pow ha hb fuel).trans ?_
      have h1 : agmA a b 1 - agmB a b 1 ≤ M := by
        have := (agm_pos ha hb 1).2
        have := agmA_le_max ha hb (le_refl 1)
        linarith
      exact div_le_div_of_nonneg_right h1 hfuel0.le
    -- `bl ≥ b_m e^{−Λ} ≥ b_m (2 − e^Λ)`
    have hbl_ge : agmB a b m * (2 - Real.exp Λ) ≤ bl := by
      have h1 : agmB a b m ≤ bl * Real.exp Λ := b₂.trans b₃
      have h2 : (2 - Real.exp Λ) * Real.exp Λ ≤ 1 := by nlinarith [sq_nonneg (Real.exp Λ - 1)]
      by_contra hlt
      push Not at hlt
      have h3 : bl * Real.exp Λ < agmB a b m * (2 - Real.exp Λ) * Real.exp Λ :=
        mul_lt_mul_of_pos_right hlt hE0
      have h4 : agmB a b m * (2 - Real.exp Λ) * Real.exp Λ ≤ agmB a b m := by
        calc agmB a b m * (2 - Real.exp Λ) * Real.exp Λ
            = agmB a b m * ((2 - Real.exp Λ) * Real.exp Λ) := by ring
          _ ≤ agmB a b m * 1 := mul_le_mul_of_nonneg_left h2 hB0.le
          _ = agmB a b m := mul_one _
      linarith
    have hah2 : ah ≤ agmA a b m * Real.exp Λ :=
      a₃.trans (mul_le_mul_of_nonneg_right a₁ hE0.le)
    have h5 : 0 ≤ M * Real.exp Λ * (1 / 2 : ℝ) ^ (w - 8) := by positivity
    have hE : 0 ≤ Real.exp Λ - 1 := by linarith
    have h6 : agmA a b m * (Real.exp Λ - 1) ≤ M * (Real.exp Λ - 1) :=
      mul_le_mul_of_nonneg_right hAM hE
    have h7 : agmB a b m * (Real.exp Λ - 1) ≤ M * (Real.exp Λ - 1) :=
      mul_le_mul_of_nonneg_right (hBA.trans hAM) hE
    nlinarith

/-- The bound of the width tends to `0` when the number of steps is `w + c`. -/
theorem tendsto_agmEps (M : ℝ) (c : ℕ) {lam₀ : ℕ → ℝ} (hlam : Tendsto lam₀ atTop (𝓝 0)) :
    Tendsto (fun w : ℕ => agmEps M
      (lam₀ w + 9 * (1 / 2 : ℝ) ^ w * ((w + c + 1 : ℕ) : ℝ)) (w + c) w) atTop (𝓝 0) := by
  have hhalf := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hPB : PB fun w : ℕ => 9 * ((w + c + 1 : ℕ) : ℝ) := by
    have : PB fun w : ℕ => 9 * ((w : ℝ) + c + 1) :=
      ((PB.natCast.add (PB.const c)).add (PB.const 1)).const_mul 9
    refine this.of_abs_le fun w => le_of_eq ?_
    push_cast
    rfl
  have h1 : Tendsto (fun w : ℕ => 9 * (1 / 2 : ℝ) ^ w * ((w + c + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    refine hPB.tendsto.congr fun w => ?_
    ring
  have hΛ : Tendsto (fun w : ℕ => lam₀ w + 9 * (1 / 2 : ℝ) ^ w * ((w + c + 1 : ℕ) : ℝ)) atTop
      (𝓝 0) := by
    simpa using hlam.add h1
  have hexp : Tendsto (fun w : ℕ =>
      Real.exp (lam₀ w + 9 * (1 / 2 : ℝ) ^ w * ((w + c + 1 : ℕ) : ℝ))) atTop (𝓝 1) := by
    have := (Real.continuous_exp.tendsto 0).comp hΛ
    rw [Real.exp_zero] at this
    exact this
  have h2 : Tendsto (fun w : ℕ => M / 2 ^ (w + c)) atTop (𝓝 0) := by
    have h := (hhalf.comp (tendsto_add_atTop_nat c)).const_mul M
    simp only [mul_zero] at h
    refine h.congr fun w => ?_
    simp only [Function.comp_apply, one_div, inv_pow]
    rw [div_eq_mul_inv]
  have h3 : Tendsto (fun w : ℕ => (1 / 2 : ℝ) ^ (w - 8)) atTop (𝓝 0) :=
    hhalf.comp (tendsto_sub_atTop_nat 8)
  unfold agmEps
  have := (((hexp.sub_const 1).const_mul (2 * M)).add h2).add ((hexp.const_mul M).mul h3)
  simpa using this

/-- **The brackets of the interval AGM converge**, from enclosures of the arguments whose
relative widths tend to `0`, with `w + c` steps allowed at working precision `w`. -/
theorem agmApproxFrom_bracketConv (ha : 0 < a) (hb : 0 < b) {s₀ : ℕ → AgmBounds}
    {lam₀ : ℕ → ℝ} (hlam : Tendsto lam₀ atTop (𝓝 0)) (hlam0 : ∀ w, 0 ≤ lam₀ w)
    (h₀ : ∀ w, 3 ≤ w → RelEnc a b 0 (lam₀ w) (s₀ w)) (c : ℕ) :
    BracketConv (fun w => agmApproxFrom (s₀ w) (w + c) w) (AGM a b) := by
  refine ⟨_, tendsto_agmEps (max a b) c hlam, 3, fun w hw => ?_⟩
  have : NeZero w := ⟨by omega⟩
  have hu : (1 / 2 : ℝ) ^ w ≤ 1 / 8 :=
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) hw).trans (by norm_num)
  obtain ⟨bl, ah, hbl, hah, -, h1, h2, h3⟩ :=
    agm_bracket_width ha hb hu (hlam0 w) (h₀ w hw) (w + c)
  refine ⟨bl, ah, ?_, ?_, h1, h2, h3⟩
  · have := rounds_setPrecRound (isFinite_of_toVal_coe hbl)
    rwa [fval_of_toVal_coe hbl] at this
  · have := rounds_setPrecRound (isFinite_of_toVal_coe hah)
    rwa [fval_of_toVal_coe hah] at this

/-- The floor and ceiling of a positive rational at `w ≥ 3` bits. -/
theorem ratBounds_L (q : AzRat) (hq : 0 < ((AzRat.toRat q : ℚ) : ℝ)) {w : ℕ} (hw : 3 ≤ w) :
    LEncl (ratBounds q w) ((AzRat.toRat q : ℚ) : ℝ) (6 * (1 / 2 : ℝ) ^ w) := by
  have : NeZero w := ⟨by omega⟩
  obtain ⟨r, hr, hr1, hr2⟩ := ofAzRatRound_floor_abs q w
  obtain ⟨s, hs, hs1, hs2⟩ := ofAzRatRound_ceiling_abs q w
  rw [abs_of_pos hq] at hr2 hs2
  have hu : (1 / 2 : ℝ) ^ w ≤ 1 / 8 :=
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) hw).trans (by norm_num)
  obtain ⟨p1, p2⟩ := round_pos_combine (lam := 0) hq (by simp) (by positivity) hu hr2 hs2
  exact ⟨r, s, hr, hs, p1, hr1, hs1, by simpa using p2⟩

theorem tendsto_six_half_pow : Tendsto (fun w : ℕ => 6 * (1 / 2 : ℝ) ^ w) atTop (𝓝 0) := by
  have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).const_mul 6
  simpa using this

/-- **The bracket of `AGM(x, y)` converges** for positive floats. -/
theorem agmApprox_bracketConv {x y : AzFloat} (hx : x.toVal = some (a : EReal))
    (hy : y.toVal = some (b : EReal)) (ha : 0 < a) (hb : 0 < b) :
    BracketConv (agmApprox x y) (AGM a b) := by
  have h := agmApproxFrom_bracketConv ha hb (s₀ := fun _ => ⟨x, x, y, y⟩)
    (lam₀ := fun _ => 0) tendsto_const_nhds (fun _ => le_rfl)
    (fun w _ => ⟨LEncl.exact hx ha, LEncl.exact hy hb⟩) (expBits x + expBits y + 2)
  refine h.congr ⟨0, fun w _ => ?_⟩
  unfold agmApprox agmIterFuel
  rw [show w + expBits x + expBits y + 2 = w + (expBits x + expBits y + 2) by ring]

/-- **The bracket of `AGM(q₁, q₂)` converges** for positive rationals. -/
theorem agmRatApprox_bracketConv {q₁ q₂ : AzRat} (ha : 0 < ((AzRat.toRat q₁ : ℚ) : ℝ))
    (hb : 0 < ((AzRat.toRat q₂ : ℚ) : ℝ)) :
    BracketConv (agmRatApprox q₁ q₂) (AGM (AzRat.toRat q₁) (AzRat.toRat q₂)) := by
  have h := agmApproxFrom_bracketConv ha hb
    (s₀ := fun w => ⟨(ratBounds q₁ w).1, (ratBounds q₁ w).2, (ratBounds q₂ w).1,
      (ratBounds q₂ w).2⟩)
    (lam₀ := fun w => 6 * (1 / 2 : ℝ) ^ w) tendsto_six_half_pow (fun _ => by positivity)
    (fun w hw => ⟨ratBounds_L q₁ ha hw, ratBounds_L q₂ hb hw⟩)
    (ratExpBits q₁ + ratExpBits q₂ + 2)
  refine h.congr ⟨0, fun w _ => ?_⟩
  unfold agmRatApprox
  dsimp only
  rw [show w + ratExpBits q₁ + ratExpBits q₂ + 2 = w + (ratExpBits q₁ + ratExpBits q₂ + 2)
    by ring]

/-- **The bracket of `AGM(x, q)` converges** for a positive float and a positive rational. -/
theorem agmFloatRatApprox_bracketConv {x : AzFloat} {q : AzRat}
    (hx : x.toVal = some (a : EReal)) (ha : 0 < a) (hb : 0 < ((AzRat.toRat q : ℚ) : ℝ)) :
    BracketConv (agmFloatRatApprox x q) (AGM a (AzRat.toRat q)) := by
  have h := agmApproxFrom_bracketConv ha hb
    (s₀ := fun w => ⟨x, x, (ratBounds q w).1, (ratBounds q w).2⟩)
    (lam₀ := fun w => 6 * (1 / 2 : ℝ) ^ w) tendsto_six_half_pow (fun _ => by positivity)
    (fun w hw => ⟨(LEncl.exact hx ha).mono (by positivity), ratBounds_L q hb hw⟩)
    (expBits x + ratExpBits q + 2)
  refine h.congr ⟨0, fun w _ => ?_⟩
  unfold agmFloatRatApprox
  dsimp only
  rw [show w + expBits x + ratExpBits q + 2 = w + (expBits x + ratExpBits q + 2) by ring]

end Azurite.AzFloat
