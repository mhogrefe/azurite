/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.GammaBracket
import Azurite.AzFloat.Equiv.LnGammaBracket
import Azurite.AzFloat.Equiv.ExpApprox
import Azurite.AzFloat.Equiv.TanBracket
import Azurite.AzFloat.Equiv.LnP1
import Azurite.AzInt.Equiv.Parity
import Azurite.Transcendental.GammaNearZero

/-!
# Equivalence: the brackets of `Γ` and `1/Γ`

* `gammaExpEncl_spec`, `gammaFracEncl_spec`, `sinOfEncl_spec`, `gammaSinEncl_spec`: the pieces,
  each a positive enclosure whenever it answers.
* `gammaCore_spec`: `gammaCore recip x e pos w = some (neg, b)` gives a positive enclosure `b`
  of `± Γ(x)` or `± 1/Γ(x)`, by `exp ∘ ln Γ` for `x > 0` and the reflection formula
  `Real.Gamma_mul_Gamma_one_sub` for `x < 0`.
* `gammaApprox_valid_or_none`: at every level `w ≥ 64` the bracket handed to the Ziv loop
  encloses the value strictly, or is rejected by `roundingPossible`.
* `zivLoop_eq_of_ne_nan_or_none`: the loop with fuel is correct, when it does not give up, for
  brackets that are valid or rejected.
* `gammaTiny?_eq`, `reciprocalGammaTiny?_eq`: the tiny-argument paths.
-/

namespace Azurite.AzFloat

open Real

/-! ### Ziv's loop with fuel on brackets that are valid or rejected -/

/-- `zivLoop_eq_of_ne_nan_threshold` when, from `w₀` on, every bracket either encloses the value
or is rejected by `roundingPossible`. -/
theorem zivLoop_eq_of_ne_nan_or_none (p : ℕ) [NeZero p] (mode : RoundingMode)
    (approx : Nat → Roundable × Roundable) (v : ℝ) (w₀ : ℕ)
    (happrox : ∀ w, w₀ ≤ w → (∃ lv hv : ℝ, Rounds (approx w).1 lv ∧ Rounds (approx w).2 hv ∧
      lv ≤ v ∧ v ≤ hv ∧ (lv = v → hv = v)) ∨
      roundingPossible (approx w).1 (approx w).2 p mode = none) :
    ∀ (fuel w : Nat), w₀ ≤ w → zivLoop approx p mode fuel w ≠ (nan, .eq) →
      zivLoop approx p mode fuel w = roundVal p mode (some (v : EReal))
  | fuel, w, hw, hne => by
    rw [zivLoop.eq_def] at hne ⊢
    split at hne
    · rename_i r hr
      rcases happrox w hw with ⟨lv, hv, hl, hh, h₁, h₂, h₃⟩ | hnone
      · exact roundingPossible_eq p mode hl hh h₁ h₂ h₃ hr
      · rw [hnone] at hr
        exact absurd hr (by simp)
    · rename_i hr
      cases fuel with
      | zero => exact absurd rfl hne
      | succ fuel =>
        exact zivLoop_eq_of_ne_nan_or_none p mode approx v w₀ happrox fuel (2 * w) (by omega) hne

/-! ### The pieces -/

/-- A float is below `2` to its exponent (`0` for zero). -/
theorem abs_lt_two_zpow_expOf {t : AzFloat} {tv : ℝ} (ht : t.toVal = some (tv : EReal)) :
    |tv| < (2 : ℝ) ^ (expOf t).toInt := by
  cases t with
  | nan => simp at ht
  | infinity s => cases s <;> simp at ht
  | zero =>
    rw [toVal_zero, Option.some.injEq] at ht
    have : tv = 0 := by exact_mod_cast ht.symm
    rw [this, abs_zero]
    positivity
  | finite s e q m hv =>
    rw [toVal_finite, Option.some.injEq, EReal.coe_eq_coe_iff] at ht
    rw [← ht]
    exact (abs_finiteVal_bounds s e hv).2

/-- A positive lower end makes an enclosure positive. -/
theorem IsEncl.pos_of_lt {a : Encl} {x : ℝ} (h : IsEncl a x) (hlt : lt zero a.1 = true) :
    IsEnclPos a x := by
  obtain ⟨l, u, hl, hu, h1, h2⟩ := h
  exact ⟨l, u, hl, hu, (lt_eq_true_iff toVal_zero' hl).mp hlt, h1, h2⟩

/-- `expEnclPos?` answers with a positive enclosure of the exponential. -/
theorem expEnclPos?_spec {M b : Encl} {v : ℝ} (hM : IsEncl M v) {w : ℕ} (hw : 64 ≤ w)
    (h : expEnclPos? M w = some b) : IsEnclPos b (Real.exp v) := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2⟩ := hM
  unfold expEnclPos? at h
  split_ifs at h with hc hp
  rw [Option.some.injEq] at h
  subst h
  obtain ⟨r, hr, hrge⟩ := subCeiling_ge hhi hlo 64
  have hr1 : r ≤ 1 := (le_eq_true_iff hr toVal_one').mp hc
  obtain ⟨a, c, ha, hc', ha1, hc1, -⟩ :=
    expOfBracket_spec_width hlo hhi h1 h2 (by linarith) hw
  exact IsEncl.pos_of_lt ⟨a, c, ha, hc', ha1, hc1⟩ hp

/-- `gammaExpEncl` answers with a positive enclosure of `exp (± v)`. -/
theorem gammaExpEncl_spec {neg : Bool} {L b : Encl} {v : ℝ} (hL : IsEncl L v) {w : ℕ}
    (hw : 64 ≤ w) (h : gammaExpEncl neg L w = some b) :
    IsEnclPos b (Real.exp (if neg then -v else v)) := by
  unfold gammaExpEncl at h
  cases neg with
  | false => exact expEnclPos?_spec hL hw h
  | true => exact expEnclPos?_spec hL.neg hw h

/-- `gammaFracEncl` answers with the sign of `x − k` and a positive enclosure of `|x − k|`. -/
theorem gammaFracEncl_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (k : AzInt)
    {W : ℕ} [NeZero W] {σ : Bool} {A : Encl} (h : gammaFracEncl x k W = some (σ, A)) :
    IsEnclPos A ((if σ then -1 else 1) * (xv - k.toInt)) := by
  have hX : IsEncl (Encl.exact x) xv := ⟨xv, xv, hx, hx, le_rfl, le_rfl⟩
  have hK : IsEncl (Encl.exact (ofAzInt k)) (k.toInt : ℝ) :=
    ⟨_, _, toVal_ofAzInt k, toVal_ofAzInt k, le_rfl, le_rfl⟩
  have hD := hX.sub (w := W) hK
  unfold gammaFracEncl at h
  dsimp only at h
  split_ifs at h with h1 h2
  · rw [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simpa using hD.pos_of_lt h1
  · rw [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨l, u, hl, hu, hl1, hu1⟩ := hD
    have hu0 : u < 0 := (lt_eq_true_iff hu toVal_zero').mp h2
    refine ⟨-u, -l, ?_, ?_, by linarith, by simp only [↓reduceIte]; linarith,
      by simp only [↓reduceIte]; linarith⟩
    · show (-(Encl.sub W (Encl.exact x) (Encl.exact (ofAzInt k))).2).toVal = _
      rw [toVal_neg, hu]; rfl
    · show (-(Encl.sub W (Encl.exact x) (Encl.exact (ofAzInt k))).1).toVal = _
      rw [toVal_neg, hl]; rfl

/-- `sinOfEncl` encloses the sine of a positive number given by an enclosure. -/
theorem sinOfEncl_spec {Y : Encl} {y : ℝ} (hY : IsEnclPos Y y) {W : ℕ} [NeZero W] {w : ℕ}
    (hw : 64 ≤ w) : IsEncl (sinOfEncl Y W w) (Real.sin y) := by
  obtain ⟨tl, th, hl, hh, h0, h1, h2⟩ := hY
  obtain ⟨lo, hi, hlo, hhi, hs1, hs2, -⟩ := sinBracket_spec hl (abs_lt_two_zpow_expOf hl) hw
  rw [abs_of_pos h0] at hs1 hs2
  obtain ⟨r, hr, hrge⟩ := subCeiling_ge hh hl W
  have hE : IsEncl0 (Encl.exact (subPrecRound Y.2 Y.1 W .Ceiling).1) r :=
    ⟨r, r, hr, hr, by linarith, le_rfl, le_rfl⟩
  refine IsEncl.widen (x := Real.sin tl) ⟨lo, hi, hlo, hhi, hs1, hs2⟩ hE ?_
  refine (abs_sin_sub_sin_le _ _).trans ?_
  rw [abs_of_nonneg (by linarith)]
  linarith

/-- `sin (π x) = (−1)^k sin (π (x − k))`. -/
theorem sin_pi_mul_eq (xv : ℝ) (k : ℤ) :
    Real.sin (π * xv) = (-1) ^ k * Real.sin (π * (xv - k)) := by
  rw [← Real.sin_add_int_mul_pi]
  congr 1
  ring

/-- `gammaSinOfFrac` answers with the sign and a positive enclosure of `|sin (π x)|`. -/
theorem gammaSinOfFrac_spec {σ : Bool} {k : AzInt} {A : Encl} {xv : ℝ}
    (hA : IsEnclPos A ((if σ then -1 else 1) * (xv - k.toInt))) {W : ℕ}
    (hW : 64 ≤ W) {w : ℕ} (hw : 64 ≤ w) {neg : Bool} {S : Encl}
    (h : gammaSinOfFrac σ k A W w = some (neg, S)) :
    IsEnclPos S ((if neg then -1 else 1) * Real.sin (π * xv)) := by
  have : NeZero W := ⟨by omega⟩
  unfold gammaSinOfFrac at h
  dsimp only at h
  split_ifs at h with hp
  rw [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hY := hA.mul (by omega : 2 ≤ W) (enclosesPos_pi hW)
  have hS := (sinOfEncl_spec hY (W := W) (Nat.le_add_right_of_le hw)).pos_of_lt hp
  convert hS using 1
  rw [sin_pi_mul_eq xv k.toInt]
  have hpar : ((-1 : ℝ)) ^ k.toInt = if k.isOdd then -1 else 1 := by
    by_cases ho : k.isOdd = true
    · rw [ho, ite_eq_left rfl, ((AzInt.isOdd_iff k).mp ho).neg_one_zpow]
    · have he : Even k.toInt := Int.not_odd_iff_even.mp fun h' => ho ((AzInt.isOdd_iff k).mpr h')
      rw [Bool.not_eq_true] at ho
      rw [ho, ite_eq_right (by simp), he.neg_one_zpow]
  rw [hpar]
  cases σ <;> cases hk : k.isOdd <;> simp [mul_comm π]
  all_goals
    rw [← Real.sin_neg]
    congr 1
    ring

/-- `gammaSinEncl` answers with the sign and a positive enclosure of `|sin (π x)|`. -/
theorem gammaSinEncl_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) {W : ℕ}
    (hW : 64 ≤ W) {w : ℕ} (hw : 64 ≤ w) {neg : Bool} {S : Encl}
    (h : gammaSinEncl x W w = some (neg, S)) :
    IsEnclPos S ((if neg then -1 else 1) * Real.sin (π * xv)) := by
  have : NeZero W := ⟨by omega⟩
  unfold gammaSinEncl at h
  dsimp only at h
  generalize gammaNearInt x = k at h
  split at h
  · exact absurd h (by simp)
  · rename_i σ A hF
    exact gammaSinOfFrac_spec (gammaFracEncl_spec hx k hF) hW hw h

/-! ### The core -/

private theorem sign_mul_div {c s g a : ℝ} (hc : c = 1 ∨ c = -1) (hs : s ≠ 0) (hg : g ≠ 0) :
    c * (a / (s * g)) = a / (c * s * g) := by
  rcases hc with rfl | rfl
  · rw [one_mul, one_mul]
  · field_simp

private theorem sign_mul_inv_div (c s g a : ℝ) :
    c * (a / (s * g))⁻¹ = c * s * g / a := by
  rw [inv_div]
  ring

/-- The value `gammaCore` encloses, up to sign. -/
noncomputable def gammaVal (recip : Bool) (xv : ℝ) : ℝ :=
  if recip then (Real.Gamma xv)⁻¹ else Real.Gamma xv

/-- **The reflection formula on enclosures** (`x < 1` not an integer). -/
theorem gammaReflect_spec {recip : Bool} {G : Option Encl} {S : Option (Bool × Encl)} {xv : ℝ}
    (hx1 : xv < 1) {w : ℕ} (hw : 64 ≤ w)
    (hG : ∀ G', G = some G' → IsEnclPos G' (Real.Gamma (-xv + 1)))
    (hS : ∀ neg S', S = some (neg, S') →
      IsEnclPos S' ((if neg then -1 else 1) * Real.sin (π * xv)))
    {neg : Bool} {b : Encl} (h : gammaReflect recip G S w = some (neg, b)) :
    IsEnclPos b ((if neg then -1 else 1) * gammaVal recip xv) := by
  unfold gammaReflect at h
  split at h
  · rename_i G' neg' S'
    rw [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hV : 64 ≤ w + 16 := by omega
    have : NeZero (w + 16) := ⟨by omega⟩
    have hGe := hG G' rfl
    have hSe := hS neg' S' rfl
    have hg0 : 0 < Real.Gamma (-xv + 1) := Real.Gamma_pos_of_pos (by linarith)
    have hT := hSe.mul (by omega : 2 ≤ w + 16) hGe
    have hπ := enclosesPos_pi hV
    have hrefl := Real.Gamma_mul_Gamma_one_sub xv
    rw [show (1 : ℝ) - xv = -xv + 1 by ring] at hrefl
    have hsin0 : Real.sin (π * xv) ≠ 0 := by
      obtain ⟨l, u, -, -, hl0, hl1, -⟩ := hSe
      intro h0
      rw [h0, mul_zero] at hl1
      linarith
    have hGx : Real.Gamma xv = π / (Real.sin (π * xv) * Real.Gamma (-xv + 1)) := by
      rw [eq_div_iff (mul_ne_zero hsin0 hg0.ne'), mul_comm (Real.sin _), ← mul_assoc, hrefl]
      field_simp
    unfold gammaVal
    cases recip
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have := hπ.div (by omega : 2 ≤ w + 16) hT
      convert this using 1
      rw [hGx]
      exact sign_mul_div (by cases neg' <;> simp) hsin0 hg0.ne'
    · simp only [↓reduceIte]
      have := hT.div (by omega : 2 ≤ w + 16) hπ
      convert this using 1
      rw [hGx]
      exact sign_mul_inv_div _ _ _ _
  · exact absurd h (by simp)

/-- The exponential of an enclosure of `ln Γ(y)`, `y > 0`, encloses `Γ(y)` or `1/Γ(y)`. -/
theorem gammaExpEncl_lnGamma {recip : Bool} {L b : Encl} {yv : ℝ} (hy : 0 < yv)
    (hL : IsEncl L (Real.log (Real.Gamma yv))) {w : ℕ} (hw : 64 ≤ w)
    (h : gammaExpEncl recip L w = some b) : IsEnclPos b (gammaVal recip yv) := by
  have hb := gammaExpEncl_spec hL hw h
  have hG := Real.Gamma_pos_of_pos hy
  convert hb using 1
  unfold gammaVal
  cases recip
  · simp [Real.exp_log hG]
  · simp [Real.exp_neg, Real.exp_log hG]

/-- **`gammaCore` answers with the sign and a positive enclosure of `|Γ(x)|` or `|1/Γ(x)|`.** -/
theorem gammaCore_spec {recip : Bool} {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    {e : AzInt} {pos : Bool} (hpos : pos = true → 0 < xv) (hneg : pos = false → xv < 0) {w : ℕ}
    (hw : 64 ≤ w) {neg : Bool} {b : Encl} (h : gammaCore recip x e pos w = some (neg, b)) :
    IsEnclPos b ((if neg then -1 else 1) * gammaVal recip xv) := by
  unfold gammaCore at h
  cases pos with
  | true =>
    have hx0 := hpos rfl
    rw [ite_eq_left rfl] at h
    obtain ⟨b', hb', hbeq⟩ := Option.map_eq_some_iff.mp h
    rw [Prod.mk.injEq] at hbeq
    obtain ⟨rfl, rfl⟩ := hbeq
    have hL := lnGammaBracket_spec hx hx0 e (w := w + gammaLnBits e) (by omega)
    simpa using gammaExpEncl_lnGamma hx0 hL hw hb'
  | false =>
    have hx0 := hneg rfl
    rw [ite_eq_right (by simp)] at h
    dsimp only at h
    set e' : AzInt := (if e.sign then e else 0) + 1
    have : NeZero (w + gammaLnBits e' + 32) := ⟨by omega⟩
    have hnx : (-x).toVal = some ((-xv : ℝ) : EReal) := by
      rw [toVal_neg, hx, Option.map_some, EReal.coe_neg]
    have hX₁ : IsEnclPos (Encl.add (w + gammaLnBits e' + 32) (Encl.exact (-x))
        (Encl.exact one)) (-xv + 1) :=
      (isEnclPos_exact hnx (by linarith)).add (by omega) enclosesPos_one.encloses0
    have hL := lnGammaBracketEncl_spec hX₁ e' (w := w + gammaLnBits e') (by omega)
    refine gammaReflect_spec (by linarith) hw (fun G' hG => ?_)
      (fun neg' S' hS => gammaSinEncl_spec hx (by omega) hw hS) h
    have := gammaExpEncl_lnGamma (recip := false) (by linarith : (0 : ℝ) < -xv + 1) hL hw hG
    simpa [gammaVal] using this

/-- `gammaStrict` encloses a positive value strictly on both sides. -/
theorem gammaStrict_spec {b : Encl} {v : ℝ} (hb : IsEnclPos b v) (w : ℕ) :
    ∃ l u : ℝ, (gammaStrict b w).1.toVal = some (l : EReal) ∧
      (gammaStrict b w).2.toVal = some (u : EReal) ∧ l < v ∧ v < u := by
  obtain ⟨lo, hi, hlo, hhi, h0, h1, h2⟩ := hb
  have : NeZero (2 * w + 64) := ⟨by omega⟩
  set k : AzInt := -(AzNat.ofNat (2 * w)).toAzInt
  have hk : (0 : ℝ) < (2 : ℝ) ^ k.toInt := by positivity
  obtain ⟨r, hr, hr1, -⟩ := subFloor_le hlo (toVal_shiftLeft_of_toVal hlo k) (2 * w + 64)
  obtain ⟨s, hs, hs1⟩ := addCeiling_ge hhi (toVal_shiftLeft_of_toVal hhi k) (2 * w + 64)
  have h3 : 0 < lo * (2 : ℝ) ^ k.toInt := mul_pos h0 hk
  have h4 : 0 < hi * (2 : ℝ) ^ k.toInt := mul_pos (by linarith) hk
  exact ⟨r, s, hr, hs, by linarith, by linarith⟩

/-- **The bracket of `gammaApproxOf` encloses the value strictly or is rejected**, when every
answer of the core is a positive enclosure of the signed value. -/
theorem gammaApproxOf_valid_or_none {c : Option (Bool × Encl)} {v : ℝ}
    (hc : ∀ neg b, c = some (neg, b) → IsEnclPos b ((if neg then -1 else 1) * v)) (w p : ℕ)
    [NeZero p] (mode : RoundingMode) :
    (∃ lv hv : ℝ, Rounds (gammaApproxOf c w).1 lv ∧ Rounds (gammaApproxOf c w).2 hv ∧
        lv ≤ v ∧ v ≤ hv ∧ (lv = v → hv = v)) ∨
      roundingPossible (gammaApproxOf c w).1 (gammaApproxOf c w).2 p mode = none := by
  unfold gammaApproxOf
  cases hc' : c with
  | none => right; exact roundingPossible_negSwapApprox_dummy false p mode
  | some pr =>
    obtain ⟨neg, b⟩ := pr
    left
    obtain ⟨l, u, hl, hu, hl1, hu1⟩ := gammaStrict_spec (hc neg b hc') w
    simp only [negSwapApprox]
    cases neg with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at hl1 hu1 ⊢
      have hR1 := rounds_setPrecRound (isFinite_of_toVal_coe hl)
      rw [fval_of_toVal_coe hl] at hR1
      have hR2 := rounds_setPrecRound (isFinite_of_toVal_coe hu)
      rw [fval_of_toVal_coe hu] at hR2
      exact ⟨l, u, hR1, hR2, hl1.le, hu1.le, fun h => absurd h hl1.ne⟩
    | true =>
      simp only [↓reduceIte, neg_one_mul] at hl1 hu1 ⊢
      have hnl : (-(gammaStrict b w).1).toVal = some ((-l : ℝ) : EReal) := by
        rw [toVal_neg, hl, Option.map_some, EReal.coe_neg]
      have hnu : (-(gammaStrict b w).2).toVal = some ((-u : ℝ) : EReal) := by
        rw [toVal_neg, hu, Option.map_some, EReal.coe_neg]
      have hR1 := rounds_setPrecRound (isFinite_of_toVal_coe hnu)
      rw [fval_of_toVal_coe hnu] at hR1
      have hR2 := rounds_setPrecRound (isFinite_of_toVal_coe hnl)
      rw [fval_of_toVal_coe hnl] at hR2
      exact ⟨-u, -l, hR1, hR2, by linarith, by linarith, fun h => absurd h (by linarith)⟩

/-- **At every level `w ≥ 64` the bracket of `gammaApprox` encloses the value strictly or is
rejected.** -/
theorem gammaApprox_valid_or_none (recip : Bool) {x : AzFloat} {xv : ℝ}
    (hx : x.toVal = some (xv : EReal)) (e : AzInt) {pos : Bool} (hpos : pos = true → 0 < xv)
    (hneg : pos = false → xv < 0) {w : ℕ} (hw : 64 ≤ w) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    (∃ lv hv : ℝ, Rounds (gammaApprox recip x e pos w).1 lv ∧
        Rounds (gammaApprox recip x e pos w).2 hv ∧
        lv ≤ gammaVal recip xv ∧ gammaVal recip xv ≤ hv ∧
        (lv = gammaVal recip xv → hv = gammaVal recip xv)) ∨
      roundingPossible (gammaApprox recip x e pos w).1 (gammaApprox recip x e pos w).2 p mode
        = none :=
  gammaApproxOf_valid_or_none (fun _ _ hc => gammaCore_spec hx hpos hneg hw hc) w p mode

/-! ### Tiny arguments -/

/-- The tiny-argument path of `Γ` answers with the rounding of `Γ(x)`. -/
theorem gammaTiny?_eq {s : Bool} {e : AzInt} {q : ℕ} {m : AzNat} (hv : FiniteValid q m) (p : ℕ)
    [NeZero p] (mode : RoundingMode) {r : AzFloat × Ordering}
    (h : gammaTiny? (finite s e q m hv) e q p mode = some r) :
    r = roundVal p mode (some ((Real.Gamma (finiteVal s e m) : ℝ) : EReal)) := by
  unfold gammaTiny? at h
  dsimp only at h
  split_ifs at h with hc
  obtain ⟨hs, he⟩ := hc
  obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp h
  set W := p + q + zivGuardBits + 8 with hW
  have : NeZero W := ⟨by omega⟩
  set xv := finiteVal s e m with hxv
  have hx : (finite s e q m hv).toVal = some (xv : EReal) := toVal_finite s e q m hv
  obtain ⟨hlt, h2e⟩ := abs_finiteVal_lt_of_tiny s hv hs he
  rw [← hxv] at hlt
  have hhalf : |xv| ≤ 1 / 2 := by
    have : (1 / 2 : ℝ) ^ (p + zivGuardBits + 8) ≤ 1 / 2 := by
      calc (1 / 2 : ℝ) ^ (p + zivGuardBits + 8) ≤ (1 / 2 : ℝ) ^ 1 :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        _ = 1 / 2 := by norm_num
    linarith
  have hx0 : xv ≠ 0 := finiteVal_ne_zero s e hv
  obtain ⟨hG1, hG2⟩ := gamma_near_zero hx0 hhalf
  obtain ⟨lo, hlo, hlo1, -⟩ := divFloor_abs toVal_neg_one_float hx hx0 W
  obtain ⟨c, hc, hc1, -⟩ := divCeiling_abs toVal_neg_one_float hx hx0 W
  obtain ⟨hi, hhi, hhi1⟩ := addCeiling_ge hc (toVal_ofAzNat_ofNat 2) W
  have hdiv : (-1 : ℝ) / xv = -(1 / xv) := by ring
  rw [hdiv] at hlo1 hc1
  push_cast at hhi1
  have hR1 := rounds_setPrecRound (isFinite_of_toVal_coe hlo)
  rw [fval_of_toVal_coe hlo] at hR1
  have hR2 := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
  rw [fval_of_toVal_coe hhi] at hR2
  have hr := roundingPossible_eq p (-mode) (v := -Real.Gamma xv) hR1 hR2 (by linarith)
    (by linarith) (fun h => absurd h (by linarith)) hr'
  rw [hr]
  have hneg := roundVal_neg p mode (-Real.Gamma xv)
  rw [neg_neg] at hneg
  exact hneg.symm

/-- The tiny-argument path of `1/Γ` answers with the rounding of `1/Γ(x)`. -/
theorem reciprocalGammaTiny?_eq {s : Bool} {e : AzInt} {q : ℕ} {m : AzNat}
    (hv : FiniteValid q m) (p : ℕ) [NeZero p] (mode : RoundingMode) {r : AzFloat × Ordering}
    (h : reciprocalGammaTiny? (finite s e q m hv) e q p mode = some r) :
    r = roundVal p mode (some (((Real.Gamma (finiteVal s e m))⁻¹ : ℝ) : EReal)) := by
  unfold reciprocalGammaTiny? at h
  dsimp only at h
  split_ifs at h with hc
  obtain ⟨hs, he⟩ := hc
  set w := max p q + zivGuardBits with hw
  have : NeZero (w + 8) := ⟨by omega⟩
  set xv := finiteVal s e m with hxv
  have hx : (finite s e q m hv).toVal = some (xv : EReal) := toVal_finite s e q m hv
  obtain ⟨hlt, h2e⟩ := abs_finiteVal_lt_of_tiny s hv hs he
  rw [← hxv] at hlt
  have hhalf : |xv| ≤ 1 / 2 := by
    have : (1 / 2 : ℝ) ^ (w + 8) ≤ 1 / 2 := by
      calc (1 / 2 : ℝ) ^ (w + 8) ≤ (1 / 2 : ℝ) ^ 1 :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        _ = 1 / 2 := by norm_num
    linarith
  have hx0 : xv ≠ 0 := finiteVal_ne_zero s e hv
  obtain ⟨hG1, hG2⟩ := inv_gamma_near_zero hx0 hhalf
  have habs : (finite s e q m hv).abs.toVal = some ((|xv| : ℝ) : EReal) := by
    rw [toVal_abs, hx, Option.map_some, ← EReal.coe_neg]
    congr 1
  obtain ⟨hi, hhi, hhi1⟩ := addCeiling_ge hx (toVal_shiftLeft_of_toVal habs e) (w + 8)
  have hsq : xv ^ 2 ≤ |xv| * (2 : ℝ) ^ e.toInt := by
    rw [← sq_abs, sq]; exact mul_le_mul_of_nonneg_left hlt.le (abs_nonneg xv)
  have hR1 := rounds_setPrecRound (isFinite_of_toVal_coe hx)
  rw [fval_of_toVal_coe hx] at hR1
  have hR2 := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
  rw [fval_of_toVal_coe hhi] at hR2
  exact roundingPossible_eq p mode (v := (Real.Gamma xv)⁻¹) hR1 hR2 hG1.le (by linarith)
    (fun h' => absurd h' hG1.ne) h

end Azurite.AzFloat
