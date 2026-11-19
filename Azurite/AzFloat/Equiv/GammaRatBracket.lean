/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.GammaRatBracket
import Azurite.AzFloat.Equiv.GammaWidth
import Azurite.AzRat.Equiv.Conversion
import Azurite.AzRat.Equiv.Unary
import Azurite.AzRat.Equiv.Sub
import Azurite.AzRat.Equiv.Round
import Azurite.Rounding.Int

/-!
# Equivalence: the brackets of `Γ` and `1/Γ` of a rational

* `gammaRatSinEncl_spec`, `gammaRatCore_spec`: the pieces on enclosures of rationals.
* `gammaRatCore_conv`: the core converges (`CoreConv`, `Equiv/GammaWidth.lean`), and
  `gammaRatApprox_isSome_exists`: the Ziv certificate at an irrational value.
-/

namespace Azurite.AzFloat

open Real Filter Topology

/-- A nonzero rational with the negative sign is negative. -/
theorem toRat_neg_of_sign_false (q : AzRat) (h0 : q.num ≠ 0) (hs : q.sign = false) :
    ((AzRat.toRat q : ℚ) : ℝ) < 0 := by
  have hne : ((AzRat.toRat q : ℚ) : ℝ) ≠ 0 := fun h =>
    h0 ((AzRat.toRat_eq_zero_iff q).mp (by exact_mod_cast h))
  refine lt_of_le_of_ne (not_lt.mp fun hpos => ?_) hne
  rw [(toRat_sign_iff q h0).mpr hpos] at hs
  exact Bool.noConfusion hs

/-- `gammaRatSinEncl` answers with the sign and a positive enclosure of `|sin (π q)|`. -/
theorem gammaRatSinEncl_spec (q : AzRat) {W : ℕ} (hW : 64 ≤ W) {w : ℕ} (hw : 64 ≤ w)
    {neg : Bool} {S : Encl} (h : gammaRatSinEncl q W w = some (neg, S)) :
    IsEnclPos S ((if neg then -1 else 1) * Real.sin (π * ((AzRat.toRat q : ℚ) : ℝ))) := by
  unfold gammaRatSinEncl at h
  dsimp only at h
  generalize (q.round .Nearest).1 = k at h
  have hdv : ((AzRat.toRat (q - k.toAzRat) : ℚ) : ℝ) = ((AzRat.toRat q : ℚ) : ℝ) - k.toInt := by
    rw [AzRat.toRat_sub, AzRat.toRat_toAzRat_int]
    push_cast
    rfl
  split_ifs at h with h0 hs
  · refine gammaSinOfFrac_spec ?_ hW hw h
    have := lnGammaRatEncl_spec _ ((toRat_sign_iff _ h0).mp hs) W
    rw [hdv] at this
    simpa [hs] using this
  · have hs' : (q - k.toAzRat).sign = false := by simpa using hs
    refine gammaSinOfFrac_spec ?_ hW hw h
    have hneg := toRat_neg_of_sign_false _ h0 hs'
    have hv : ((AzRat.toRat (-(q - k.toAzRat)) : ℚ) : ℝ)
        = -(((AzRat.toRat q : ℚ) : ℝ) - k.toInt) := by
      rw [AzRat.toRat_neg, Rat.cast_neg, hdv]
    have := lnGammaRatEncl_spec (-(q - k.toAzRat)) (by rw [hv]; rw [hdv] at hneg; linarith) W
    rw [hv] at this
    simpa [hs'] using this

/-- **`gammaRatCore` answers with the sign and a positive enclosure of `|Γ(q)|` or
`|1/Γ(q)|`.** -/
theorem gammaRatCore_spec {recip : Bool} (q : AzRat) {e : AzInt} {pos : Bool}
    (hpos : pos = true → 0 < ((AzRat.toRat q : ℚ) : ℝ))
    (hneg : pos = false → ((AzRat.toRat q : ℚ) : ℝ) < 0) {w : ℕ} (hw : 64 ≤ w) {neg : Bool}
    {b : Encl} (h : gammaRatCore recip q e pos w = some (neg, b)) :
    IsEnclPos b ((if neg then -1 else 1) * gammaVal recip ((AzRat.toRat q : ℚ) : ℝ)) := by
  unfold gammaRatCore at h
  cases pos with
  | true =>
    have hx0 := hpos rfl
    rw [ite_eq_left rfl] at h
    dsimp only at h
    obtain ⟨b', hb', hbeq⟩ := Option.map_eq_some_iff.mp h
    rw [Prod.mk.injEq] at hbeq
    obtain ⟨rfl, rfl⟩ := hbeq
    have hL := lnGammaBracketEncl_spec (lnGammaRatEncl_spec q hx0 (w + gammaLnBits e)) e
      (w := w + gammaLnBits e) (by omega)
    simpa using gammaExpEncl_lnGamma hx0 hL hw hb'
  | false =>
    have hx0 := hneg rfl
    rw [ite_eq_right (by simp)] at h
    dsimp only at h
    set e' : AzInt := (if e.sign then e else 0) + 1
    have hv : ((AzRat.toRat (1 - q) : ℚ) : ℝ) = -((AzRat.toRat q : ℚ) : ℝ) + 1 := by
      rw [AzRat.toRat_sub, AzRat.toRat_one]
      push_cast
      ring
    have hX₁ := lnGammaRatEncl_spec (1 - q) (by rw [hv]; linarith) (w + gammaLnBits e')
    rw [hv] at hX₁
    have hL := lnGammaBracketEncl_spec hX₁ e' (w := w + gammaLnBits e') (by omega)
    refine gammaReflect_spec (by linarith) hw (fun G' hG => ?_)
      (fun neg' S' hS => gammaRatSinEncl_spec q (by omega) hw hS) h
    have := gammaExpEncl_lnGamma (recip := false)
      (by linarith : (0 : ℝ) < -((AzRat.toRat q : ℚ) : ℝ) + 1) hL hw hG
    simpa [gammaVal] using this

/-! ### Convergence -/

/-- The roundings of a positive rational, as a relative width. -/
theorem lnGammaRatEncl_L (q : AzRat) (hq : 0 < ((AzRat.toRat q : ℚ) : ℝ)) (w : ℕ) :
    LEncl (lnGammaRatEncl q w) ((AzRat.toRat q : ℚ) : ℝ) (6 * (1 / 2 : ℝ) ^ (w + 32)) := by
  have : NeZero (w + 32) := ⟨by omega⟩
  obtain ⟨r, hr, hr1, hr2⟩ := ofAzRatRound_floor_abs q (w + 32)
  obtain ⟨s, hs, hs1, hs2⟩ := ofAzRatRound_ceiling_abs q (w + 32)
  rw [abs_of_pos hq] at hr2 hs2
  obtain ⟨p1, p2⟩ := round_pos_combine (lam := 0) hq (by simp) (by positivity)
    (half_pow_le_eighth (by omega : 3 ≤ w + 32)) hr2 hs2
  exact ⟨r, s, hr, hs, p1, hr1, hs1, by simpa using p2⟩

/-- The nearest integer is within `1`. -/
theorem abs_sub_round_lt_one (q : AzRat) :
    |((AzRat.toRat q : ℚ) : ℝ) - (((q.round .Nearest).1.toInt : ℤ) : ℝ)| < 1 := by
  have h := AzRat.toInt_round q .Nearest
  rcases round_nearest_eq_or RoundingTarget.intSet ((AzRat.toRat q : ℚ) : ℝ) with h' | h'
  · rw [h', RoundingTarget.val_roundFloor_intSet, EReal.coe_eq_coe_iff] at h
    rw [h, abs_lt]
    constructor <;> linarith [Int.floor_le ((AzRat.toRat q : ℚ) : ℝ),
      Int.lt_floor_add_one ((AzRat.toRat q : ℚ) : ℝ)]
  · rw [h', RoundingTarget.val_roundCeiling_intSet, EReal.coe_eq_coe_iff] at h
    rw [h, abs_lt]
    constructor <;> linarith [Int.le_ceil ((AzRat.toRat q : ℚ) : ℝ),
      Int.ceil_lt_add_one ((AzRat.toRat q : ℚ) : ℝ)]

/-- **The sine of the reflection formula converges** at a non-integer rational. -/
theorem gammaRatSinEncl_conv (q : AzRat) (hint : ∀ k : ℤ, ((AzRat.toRat q : ℚ) : ℝ) ≠ k) :
    SinConv (fun w => gammaRatSinEncl q (w + 16) w) ((AzRat.toRat q : ℚ) : ℝ) := by
  have hk1 := abs_sub_round_lt_one q
  have hdv : ((AzRat.toRat (q - (q.round .Nearest).1.toAzRat) : ℚ) : ℝ)
      = ((AzRat.toRat q : ℚ) : ℝ) - (q.round .Nearest).1.toInt := by
    rw [AzRat.toRat_sub, AzRat.toRat_toAzRat_int]
    push_cast
    rfl
  have hd : ((AzRat.toRat q : ℚ) : ℝ) - (((q.round .Nearest).1.toInt : ℤ) : ℝ) ≠ 0 :=
    fun h => hint _ (sub_eq_zero.mp h)
  have h0 : (q - (q.round .Nearest).1.toAzRat).num ≠ 0 := by
    intro h
    apply hd
    rw [← hdv, (AzRat.toRat_eq_zero_iff _).mpr h]
  have hval := abs_sin_pi_mul ((AzRat.toRat q : ℚ) : ℝ) (q.round .Nearest).1.toInt hk1
  have hspos : 0 < |Real.sin (π * ((AzRat.toRat q : ℚ) : ℝ))| := by
    rw [hval]
    exact Real.sin_pos_of_pos_of_lt_pi (mul_pos (abs_pos.mpr hd) Real.pi_pos)
      (by nlinarith [Real.pi_pos])
  have hpow : Tendsto (fun w : ℕ => 496 * (1 / 2 : ℝ) ^ (w + 16)) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).comp (tendsto_add_atTop_nat 16)).const_mul 496
    simpa using this
  have hE : Tendsto (fun w => sinEnv w + 496 * (1 / 2 : ℝ) ^ (w + 16)) atTop (𝓝 0) := by
    simpa using tendsto_sinEnv.add hpow
  refine ⟨_, hE, ?_⟩
  filter_upwards [hE.eventually (gt_mem_nhds hspos),
    tendsto_sinEnv.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_ge_atTop 64] with w h1 h2 h3
  have hW : 64 ≤ w + 16 := by omega
  rw [hval] at h1
  have hmono : 6 * (1 / 2 : ℝ) ^ (w + 16 + 32) ≤ 6 * (1 / 2 : ℝ) ^ (w + 16) := by
    have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      (by omega : w + 16 ≤ w + 16 + 32)
    linarith
  have key : ∃ neg S, gammaRatSinEncl q (w + 16) w = some (neg, S) ∧
      AEncl S (Real.sin (|((AzRat.toRat q : ℚ) : ℝ) - (((q.round .Nearest).1.toInt : ℤ) : ℝ)|
        * π)) (sinEnv w + 496 * (1 / 2 : ℝ) ^ (w + 16)) := by
    cases hs : (q - (q.round .Nearest).1.toAzRat).sign with
    | true =>
      have hpos := (toRat_sign_iff _ h0).mp hs
      have hA := (lnGammaRatEncl_L _ hpos (w + 16)).mono hmono
      rw [hdv] at hpos hA
      rw [← abs_of_pos hpos] at hA
      obtain ⟨S, hS, hSw⟩ := gammaSinOfFrac_some (σ := false) (k := (q.round .Nearest).1)
        hW hA hk1 h3 h2 h1
      refine ⟨false != (q.round .Nearest).1.isOdd, S, ?_, hSw⟩
      unfold gammaRatSinEncl
      simp only [h0, hs, ↓reduceIte, Bool.not_true]
      exact hS
    | false =>
      have hneg := toRat_neg_of_sign_false _ h0 hs
      have hv : ((AzRat.toRat (-(q - (q.round .Nearest).1.toAzRat)) : ℚ) : ℝ)
          = -(((AzRat.toRat q : ℚ) : ℝ) - (q.round .Nearest).1.toInt) := by
        rw [AzRat.toRat_neg, Rat.cast_neg, hdv]
      rw [hdv] at hneg
      have hA := (lnGammaRatEncl_L (-(q - (q.round .Nearest).1.toAzRat))
        (by rw [hv]; linarith) (w + 16)).mono hmono
      rw [hv, ← abs_of_neg hneg] at hA
      obtain ⟨S, hS, hSw⟩ := gammaSinOfFrac_some (σ := true) (k := (q.round .Nearest).1)
        hW hA hk1 h3 h2 h1
      refine ⟨true != (q.round .Nearest).1.isOdd, S, ?_, hSw⟩
      unfold gammaRatSinEncl
      simp only [h0, hs, ↓reduceIte, Bool.not_false, Bool.false_eq_true]
      exact hS
  obtain ⟨neg, S, hsome, hSw⟩ := key
  rw [← hval] at hSw
  exact ⟨neg, S, hsome, gammaRatSinEncl_spec q hW h3 hsome, hSw⟩

/-- **The core of `Γ(q)` and `1/Γ(q)` converges** at every rational `q` that is not `0` or a
negative integer (`pos` the sign of `q`). -/
theorem gammaRatCore_conv (recip : Bool) (q : AzRat) (e : AzInt) {pos : Bool}
    (hpos : pos = true → 0 < ((AzRat.toRat q : ℚ) : ℝ))
    (hneg : pos = false → ((AzRat.toRat q : ℚ) : ℝ) < 0 ∧
      ∀ k : ℤ, ((AzRat.toRat q : ℚ) : ℝ) ≠ k) :
    CoreConv (gammaRatCore recip q e pos) (gammaVal recip ((AzRat.toRat q : ℚ) : ℝ)) := by
  cases pos with
  | true =>
    have h0 := hpos rfl
    refine (coreConv_pos recip h0 e (gammaLnBits e) (X := fun w => lnGammaRatEncl q w)
      fun w => lnGammaRatEncl_L q h0 w).congr fun w => ?_
    simp [gammaRatCore]
  | false =>
    obtain ⟨h0, hint⟩ := hneg rfl
    have hv : ((AzRat.toRat (1 - q) : ℚ) : ℝ) = -((AzRat.toRat q : ℚ) : ℝ) + 1 := by
      rw [AzRat.toRat_sub, AzRat.toRat_one]
      push_cast
      ring
    refine (coreConv_reflect recip h0 ((if e.sign then e else 0) + 1)
      (gammaLnBits ((if e.sign then e else 0) + 1))
      (X := fun w => lnGammaRatEncl (1 - q) w) (fun w => ?_)
      (gammaRatSinEncl_conv q hint)).congr fun w => ?_
    · rw [← hv]
      exact lnGammaRatEncl_L (1 - q) (by rw [hv]; linarith) w
    · simp [gammaRatCore]

/-- **The Ziv certificate of `Γ(q)` and `1/Γ(q)` at an irrational value.** -/
theorem gammaRatApprox_isSome_exists (recip : Bool) (q : AzRat) (e : AzInt) {pos : Bool}
    (hpos : pos = true → 0 < ((AzRat.toRat q : ℚ) : ℝ))
    (hneg : pos = false → ((AzRat.toRat q : ℚ) : ℝ) < 0 ∧
      ∀ k : ℤ, ((AzRat.toRat q : ℚ) : ℝ) ≠ k)
    (hirr : Irrational (gammaVal recip ((AzRat.toRat q : ℚ) : ℝ)))
    (p : ℕ) [NeZero p] (mode : RoundingMode) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (gammaRatApprox recip q e pos (w₀ * 2 ^ f)).1
      (gammaRatApprox recip q e pos (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  gammaApproxOf_isSome_exists (gammaRatCore_conv recip q e hpos hneg) hirr p mode w₀ hw₀

/-- **The bracket of `Γ(q)` and `1/Γ(q)` converges** at every rational `q` that is not `0` or
a negative integer. -/
theorem gammaRatApprox_bracketConv (recip : Bool) (q : AzRat) (e : AzInt) {pos : Bool}
    (hpos : pos = true → 0 < ((AzRat.toRat q : ℚ) : ℝ))
    (hneg : pos = false → ((AzRat.toRat q : ℚ) : ℝ) < 0 ∧
      ∀ k : ℤ, ((AzRat.toRat q : ℚ) : ℝ) ≠ k) :
    BracketConv (gammaRatApprox recip q e pos) (gammaVal recip ((AzRat.toRat q : ℚ) : ℝ)) :=
  gammaApproxOf_bracketConv (gammaRatCore_conv recip q e hpos hneg)

end Azurite.AzFloat
