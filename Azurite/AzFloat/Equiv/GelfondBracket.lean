/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.GelfondBracket
import Azurite.AzFloat.Equiv.AgmWidth
import Azurite.AzFloat.Equiv.GammaWidth
import Azurite.AzFloat.Equiv.Ln2Bracket
import Azurite.AzFloat.Equiv.PiBracket
import Azurite.AzFloat.Equiv.Constants
import Azurite.Transcendental.GelfondSchneider

/-!
# The brackets of `e^π`, `2^√2` and `e^(π √163)` converge, and their Ziv certificates

* `expOfBracket_bracketConv`: the exponential of a convergent bracket converges
  (`BracketConv`).
* `piBracket_A`, `sqrt2Ln2Bracket_A`, `piSqrt163Bracket_A`: the widths of the brackets of `π`,
  `√2 ln 2` and `π √163`.
* `gelfondApprox_cert`, `gelfondSchneiderApprox_cert`, `ramanujanApprox_cert`: the three values
  are irrational (`irrational_exp_pi`, `irrational_two_rpow_sqrt_two`,
  `irrational_exp_pi_sqrt`, by the Gelfond–Schneider theorem of
  `Transcendental/GelfondSchneider.lean`), so some level of each Ziv loop is accepted.
-/

namespace Azurite.AzFloat

open Filter Topology

theorem tendsto_const_mul_half_pow (c : ℝ) :
    Tendsto (fun w : ℕ => c * (1 / 2 : ℝ) ^ w) atTop (𝓝 0) := by
  have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).const_mul c
  simpa using this

/-- **The exponential of a convergent bracket converges.** -/
theorem expOfBracket_bracketConv {X : ℕ → AzFloat × AzFloat} {v : ℝ} {δ : ℕ → ℝ}
    (hδ : Tendsto δ atTop (𝓝 0)) (hX : ∀ w, 64 ≤ w → AEncl (X w) v (δ w)) :
    BracketConv (fun w => (fun p mode => setPrecRound (expOfBracket (X w) w).1 p mode,
      fun p mode => setPrecRound (expOfBracket (X w) w).2 p mode)) (Real.exp v) := by
  have hpow : Tendsto (fun w : ℕ => (1 / 2 : ℝ) ^ w) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have ht : Tendsto (fun w => expOfBracketEps v (δ w) w) atTop (𝓝 0) := by
    unfold expOfBracketEps
    have := (tendsto_expEps v).add (((hδ.const_mul 24).add (hpow.div_const 4)).const_mul
      (Real.exp v))
    simpa using this
  obtain ⟨W₁, hW₁⟩ := eventually_atTop.mp
    (hδ.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  refine ⟨_, ht, max 64 W₁, fun w hw => ?_⟩
  have hw64 : 64 ≤ w := le_trans (le_max_left _ _) hw
  obtain ⟨lo, hi, hlo, hhi, h1, h2, h3⟩ := hX w hw64
  have hδ1 := hW₁ w (le_trans (le_max_right _ _) hw)
  obtain ⟨a, b, ha, hb, ha1, hb1, hab⟩ :=
    expOfBracket_spec_width hlo hhi h1 h2 (h3.trans hδ1) hw64
  refine ⟨a, b, ?_, ?_, ha1, hb1, hab.trans (expOfBracketEps_mono v h3 w)⟩
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe ha)
    rw [fval_of_toVal_coe ha] at hR
    exact hR
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hb)
    rw [fval_of_toVal_coe hb] at hR
    exact hR

/-! ### The three inner brackets -/

theorem piBracket_A {w : ℕ} (hw : 64 ≤ w) :
    AEncl (piBracket w) Real.pi (8 * (1 / 2 : ℝ) ^ w) := by
  obtain ⟨lv, hv, hlv, hhv, -, hlo, hhi, hwid⟩ := piBracket_spec_width hw
  exact ⟨lv, hv, hlv, hhv, hlo.le, hhi, hwid⟩

theorem sqrt2Ln2Bracket_A {w : ℕ} (hw : 64 ≤ w) :
    AEncl (sqrt2Ln2Bracket w) (Real.sqrt 2 * Real.log 2)
      (2 * (Real.sqrt 2 * Real.log 2) * (40 * (1 / 2 : ℝ) ^ w)) := by
  have : NeZero w := ⟨by omega⟩
  have hu : (1 / 2 : ℝ) ^ w ≤ 1 / 8 := half_pow_le_eighth (by omega)
  have hu0 : (0 : ℝ) < (1 / 2 : ℝ) ^ w := by positivity
  have hus := half_pow_small hw
  have hS : LEncl ((sqrtPrecRound two w .Floor).1, (sqrtPrecRound two w .Ceiling).1)
      (Real.sqrt 2) (0 / 2 + 6 * (1 / 2 : ℝ) ^ w) :=
    lencl_sqrt hu (LEncl.exact toVal_two (by norm_num))
  obtain ⟨lv, hv, hlv, hhv, hl, hh, hwid, -⟩ := ln2Bracket_spec w
  have hlog := Real.log_two_gt_d9
  have hA : AEncl (ln2Bracket w) (Real.log 2) (8 * (1 / 2 : ℝ) ^ w) :=
    ⟨lv, hv, hlv, hhv, hl, hh, hwid⟩
  have hL := LEncl.ofA hA (by linarith) (by linarith)
  have hM := hS.mul hu hL
  have hlam : 0 / 2 + 6 * (1 / 2 : ℝ) ^ w + 2 * (8 * (1 / 2 : ℝ) ^ w) / Real.log 2
      + 6 * (1 / 2 : ℝ) ^ w ≤ 40 * (1 / 2 : ℝ) ^ w := by
    have : 2 * (8 * (1 / 2 : ℝ) ^ w) / Real.log 2 ≤ 28 * (1 / 2 : ℝ) ^ w := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  obtain ⟨l, h, e1, e2, -, e3, e4, e5⟩ := (hM.mono hlam).toA (by positivity) (by linarith)
  exact ⟨l, h, e1, e2, e3, e4, e5⟩

theorem piSqrt163Bracket_A {w : ℕ} (hw : 64 ≤ w) :
    AEncl (piSqrt163Bracket w) (Real.pi * Real.sqrt 163)
      (2 * (Real.pi * Real.sqrt 163) * (15 * (1 / 2 : ℝ) ^ w)) := by
  have : NeZero w := ⟨by omega⟩
  have hu : (1 / 2 : ℝ) ^ w ≤ 1 / 8 := half_pow_le_eighth (by omega)
  have hu0 : (0 : ℝ) < (1 / 2 : ℝ) ^ w := by positivity
  have hus := half_pow_small hw
  have h163 : (ofAzNat (AzNat.ofNat 163)).toVal = some ((163 : ℝ) : EReal) := by
    rw [toVal_ofAzNat, AzNat.toNat_ofNat, Nat.cast_ofNat]
  have hS : LEncl (sqrtBracket (ofAzNat (AzNat.ofNat 163), ofAzNat (AzNat.ofNat 163)) w)
      (Real.sqrt 163) (0 / 2 + 6 * (1 / 2 : ℝ) ^ w) :=
    lencl_sqrt hu (LEncl.exact h163 (by norm_num))
  have hM := (LEncl.pi hw).mul hu hS
  have hlam : 3 * (1 / 2 : ℝ) ^ w + (0 / 2 + 6 * (1 / 2 : ℝ) ^ w) + 6 * (1 / 2 : ℝ) ^ w
      ≤ 15 * (1 / 2 : ℝ) ^ w := by linarith
  obtain ⟨l, h, e1, e2, -, e3, e4, e5⟩ := (hM.mono hlam).toA (by positivity) (by linarith)
  exact ⟨l, h, e1, e2, e3, e4, e5⟩

/-! ### Convergence of the brackets -/

/-- **The bracket of `e^π` converges.** -/
theorem gelfondApprox_bracketConv : BracketConv gelfondApprox (Real.exp Real.pi) :=
  expOfBracket_bracketConv (tendsto_const_mul_half_pow 8) fun _ hw => piBracket_A hw

/-- **The bracket of `2^√2` converges.** -/
theorem gelfondSchneiderApprox_bracketConv :
    BracketConv gelfondSchneiderApprox (Real.exp (Real.sqrt 2 * Real.log 2)) :=
  expOfBracket_bracketConv
    ((tendsto_const_mul_half_pow (2 * (Real.sqrt 2 * Real.log 2) * 40)).congr fun w => by ring)
    fun _ hw => sqrt2Ln2Bracket_A hw

/-- **The bracket of `e^(π √163)` converges.** -/
theorem ramanujanApprox_bracketConv :
    BracketConv ramanujanApprox (Real.exp (Real.pi * Real.sqrt 163)) :=
  expOfBracket_bracketConv
    ((tendsto_const_mul_half_pow (2 * (Real.pi * Real.sqrt 163) * 15)).congr fun w => by ring)
    fun _ hw => piSqrt163Bracket_A hw

/-! ### The certificates -/

theorem irrational_exp_sqrt_two_mul_log_two :
    Irrational (Real.exp (Real.sqrt 2 * Real.log 2)) := by
  have h := irrational_two_rpow_sqrt_two
  rwa [Real.rpow_def_of_pos (by norm_num), mul_comm] at h

theorem irrational_ramanujan : Irrational (Real.exp (Real.pi * Real.sqrt 163)) := by
  have h := irrational_exp_pi_sqrt (n := 163) (by norm_num)
  simpa using h

/-- **The Ziv certificate of `e^π`**: the value is irrational (Gelfond), the brackets
converge. -/
theorem gelfondApprox_cert (p : ℕ) [NeZero p] (mode : RoundingMode) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (gelfondApprox (w₀ * 2 ^ f)).1 (gelfondApprox (w₀ * 2 ^ f)).2 p
      mode).isSome = true :=
  gelfondApprox_bracketConv.exists_isSome (Real.exp_pos _).ne' p
    (not_mem_floatSet_of_irrational p irrational_exp_pi) mode w₀ hw₀

/-- **The Ziv certificate of `2^√2`** (Gelfond–Schneider). -/
theorem gelfondSchneiderApprox_cert (p : ℕ) [NeZero p] (mode : RoundingMode) (w₀ : ℕ)
    (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (gelfondSchneiderApprox (w₀ * 2 ^ f)).1
      (gelfondSchneiderApprox (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  gelfondSchneiderApprox_bracketConv.exists_isSome (Real.exp_pos _).ne' p
    (not_mem_floatSet_of_irrational p irrational_exp_sqrt_two_mul_log_two) mode w₀ hw₀

/-- **The Ziv certificate of `e^(π √163)`** (Gelfond–Schneider). -/
theorem ramanujanApprox_cert (p : ℕ) [NeZero p] (mode : RoundingMode) (w₀ : ℕ)
    (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (ramanujanApprox (w₀ * 2 ^ f)).1
      (ramanujanApprox (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  ramanujanApprox_bracketConv.exists_isSome (Real.exp_pos _).ne' p
    (not_mem_floatSet_of_irrational p irrational_ramanujan) mode w₀ hw₀

end Azurite.AzFloat
