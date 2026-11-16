/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.SinhCoshBracket
import Azurite.AzFloat.Equiv.SinhRatBracket
import Azurite.AzFloat.Equiv.CoshBracket
import Azurite.AzFloat.Equiv.ZivPair

/-!
# Equivalence: the joint brackets of `sinh x` and `cosh x`

`expOfExpM1_spec` (the enclosure of `1 + U`, width at most `jointExpWidth`),
`coshOfExpM1_width` (the `cosh` part of `sinhCoshOfExpM1`), the component specifications
`sinhCoshApprox_fst` (the `sinh` part **is** `sinhApprox`), `sinhCoshApprox_spec_cosh`,
`sinhCoshApprox_isSome_exists` (the joint Ziv certificate), and the rational versions
`sinhCoshRatApprox_fst`, `sinhCoshRatApprox_spec_cosh`, `sinhCoshRatApprox_isSome_exists`.
-/

open Real

namespace Azurite.AzFloat

/-- The width of `expOfExpM1` at precision `w` on an enclosure of `U` of width `E`. -/
noncomputable def jointExpWidth (U E : ℝ) (w : ℕ) : ℝ := E + 4 * (1 + U + E) * (1 / 2 : ℝ) ^ w

/-- The width of the `cosh` part of `sinhCoshOfExpM1` at level `w`. -/
noncomputable def jointCoshWidth (U E : ℝ) (w : ℕ) : ℝ :=
  coshWidth (1 + U) (jointExpWidth U E w) w

theorem tendsto_jointCoshWidth (U : ℝ) {E : ℕ → ℝ}
    (hE : Filter.Tendsto E Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun w => jointCoshWidth U (E w) w) Filter.atTop (nhds 0) := by
  have hp : Filter.Tendsto (fun w : ℕ => (1 / 2 : ℝ) ^ w) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h := hE.add (((hE.const_add (1 + U)).const_mul 4).mul hp)
  have h0 : (0 + 4 * (1 + U + 0) * 0 : ℝ) = 0 := by ring
  rw [h0] at h
  exact tendsto_coshWidth (1 + U) (E := fun w => jointExpWidth U (E w) w) h

/-- **`expOfExpM1` encloses `1 + U`** for an enclosure `[lo, hi]` of `U ≥ 0` of width at most
`E`. -/
theorem expOfExpM1_spec {u : Encl} {U lo hi E : ℝ} (hlo : u.1.toVal = some (lo : EReal))
    (hhi : u.2.toVal = some (hi : EReal)) (hU0 : 0 ≤ U) (h1 : lo ≤ U) (h2 : U ≤ hi)
    (h3 : hi - lo ≤ E) {W : ℕ} (hW : 1 ≤ W) :
    IsEnclW (expOfExpM1 u W) (1 + U) (jointExpWidth U E W) := by
  have : NeZero W := ⟨by omega⟩
  obtain ⟨cv, hcv, hcv0, hcvle, hcveq⟩ := clampNonneg_spec hlo
  have hcU : cv ≤ U := hcvle.trans (max_le h1 hU0)
  have hrc : lo ≤ cv := by
    rcases le_or_gt 0 lo with h | h
    · rw [hcveq h]
    · linarith
  have hη0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ W := by positivity
  obtain ⟨r1, hr1, hr1a, hr1b⟩ := addFloor_abs toVal_one' hcv W
  obtain ⟨r2, hr2, hr2a, hr2b⟩ := addCeiling_abs toVal_one' hhi W
  have hhi0 : 0 ≤ hi := hU0.trans h2
  rw [abs_of_nonneg (by linarith)] at hr1b hr2b
  have e1 : (1 + cv) * (1 / 2 : ℝ) ^ W ≤ (1 + U + E) * (1 / 2 : ℝ) ^ W :=
    mul_le_mul_of_nonneg_right (by linarith) hη0
  have e2 : (1 + hi) * (1 / 2 : ℝ) ^ W ≤ (1 + U + E) * (1 / 2 : ℝ) ^ W :=
    mul_le_mul_of_nonneg_right (by linarith) hη0
  unfold jointExpWidth
  exact ⟨r1, r2, hr1, hr2, by linarith, by linarith, by linarith⟩

/-- **The `cosh` part of `sinhCoshOfExpM1` encloses `cosh a`**, `a ≥ 0`, from an enclosure of
`e^a − 1` of width at most `E`. -/
theorem coshOfExpM1_width {u : Encl} {av lo hi E : ℝ} (hlo : u.1.toVal = some (lo : EReal))
    (hhi : u.2.toVal = some (hi : EReal)) (ha0 : 0 ≤ av) (h1 : lo ≤ Real.exp av - 1)
    (h2 : Real.exp av - 1 ≤ hi) (h3 : hi - lo ≤ E) (w : ℕ) :
    IsEnclW (sinhCoshOfExpM1 u w).2 (Real.cosh av) (jointCoshWidth (Real.exp av - 1) E w) := by
  have hU0 : 0 ≤ Real.exp av - 1 := by linarith [add_one_le_exp av]
  have hE0 : 0 ≤ E := by linarith
  obtain ⟨l, h, hl, hh, b1, b2, b3⟩ :=
    expOfExpM1_spec hlo hhi hU0 h1 h2 h3 (W := w + 16) (by omega)
  have he : 1 + (Real.exp av - 1) = Real.exp av := by ring
  rw [he] at b1 b2
  have hpw : (1 / 2 : ℝ) ^ (w + 16) ≤ (1 / 2 : ℝ) ^ w :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hmono : jointExpWidth (Real.exp av - 1) E (w + 16)
      ≤ jointExpWidth (Real.exp av - 1) E w := by
    unfold jointExpWidth
    have hc : 0 ≤ 4 * (1 + (Real.exp av - 1) + E) := by positivity
    have := mul_le_mul_of_nonneg_left hpw hc
    linarith
  have hc := coshOfExp_width hl hh ha0 b1 b2 (b3.trans hmono) w
  unfold jointCoshWidth
  rw [he]
  exact hc

/-! ### Floats -/

/-- The `sinh` part of the joint bracket is `sinhApprox`. -/
theorem sinhCoshApprox_fst (neg : Bool) (x : AzFloat) (e : AzInt) (w : ℕ) :
    (sinhCoshApprox neg x e w).1 = sinhApprox neg x e w := rfl

/-- The width bound of the `cosh` part of `sinhCoshApprox`. -/
noncomputable def jointCoshEps (xv : ℝ) (c w : ℕ) : ℝ :=
  jointCoshWidth (Real.exp |xv| - 1) (expM1Eps |xv| c w) w

theorem tendsto_jointCoshEps (xv : ℝ) (c : ℕ) :
    Filter.Tendsto (jointCoshEps xv c) Filter.atTop (nhds 0) :=
  tendsto_jointCoshWidth _ (tendsto_expM1Eps _ _)

/-- The `cosh` part of `sinhCoshApprox` as a pair of `Roundable`s bracketing `cosh x`. -/
theorem sinhCoshApprox_spec_cosh (neg : Bool) {x : AzFloat} {xv : ℝ}
    (hx : x.toVal = some (xv : EReal)) {e : AzInt} (hxe : |xv| < (2 : ℝ) ^ e.toInt) {w : ℕ}
    (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, Rounds (sinhCoshApprox neg x e w).2.1 lv ∧
      Rounds (sinhCoshApprox neg x e w).2.2 hv ∧ lv ≤ Real.cosh xv ∧ Real.cosh xv ≤ hv ∧
      hv - lv ≤ jointCoshEps xv (expM1Comp e) w := by
  have habs : x.abs.toVal = some ((|xv| : ℝ) : EReal) := by
    rw [toVal_abs, hx, Option.map_some, ← EReal.coe_neg]
    congr 1
  obtain ⟨lo, hi, hlo, hhi, h1, h2, h3⟩ := expM1Bracket_spec habs e (by rwa [abs_abs]) hw
  obtain ⟨cl, ch, hcl, hch, c1, c2, c3⟩ :=
    coshOfExpM1_width hlo hhi (abs_nonneg xv) h1 h2 h3 w
  rw [cosh_abs] at c1 c2
  obtain ⟨lv, hv, hR1, hR2, hl, hh, he⟩ := enclApprox_spec false hcl hch c1 c2
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at hl hh
  exact ⟨lv, hv, hR1, hR2, hl, hh, by rw [he]; exact c3⟩

/-- The joint Ziv certificate for `sinh x` and `cosh x`, `x` a finite nonzero float. -/
theorem sinhCoshApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) {neg : Bool}
    {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (hx0 : xv ≠ 0) {e : AzInt}
    (hxe : |xv| < (2 : ℝ) ^ e.toInt) (hneg : neg = true ↔ xv < 0) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible₂ (sinhCoshApprox neg x e (w₀ * 2 ^ f)) p mode).isSome = true :=
  exists_isSome₂_of_irrational_threshold p mode (sinhCoshApprox neg x e)
    (irrational_sinh_of_toVal hx hx0) (irrational_cosh_of_toVal hx hx0)
    (sinhEps |xv| (expM1Comp e)) (jointCoshEps xv (expM1Comp e)) (tendsto_sinhEps _ _)
    (tendsto_jointCoshEps _ _) 64
    (fun w hw => by rw [sinhCoshApprox_fst]; exact sinhApprox_spec hx hx0 hxe hneg hw)
    (fun _ hw => sinhCoshApprox_spec_cosh neg hx hxe hw) w₀ hw₀

/-! ### Rationals -/

/-- The `sinh` part of the joint rational bracket is `sinhRatApprox`. -/
theorem sinhCoshRatApprox_fst (q : AzRat) (w : ℕ) :
    (sinhCoshRatApprox q w).1 = sinhRatApprox q w := rfl

/-- The width bound of the `cosh` part of `sinhCoshRatApprox`. -/
noncomputable def jointCoshRatEps (q : AzRat) (w : ℕ) : ℝ :=
  jointCoshWidth (Real.exp (AzRat.toRat q.abs : ℝ) - 1)
    (expM1RatEps (AzRat.toRat q.abs : ℝ)
      (expM1Comp (AzInt.ofInt (AzRat.floorLogBaseAbs 2 q.abs + 2))) w) w

theorem tendsto_jointCoshRatEps (q : AzRat) :
    Filter.Tendsto (jointCoshRatEps q) Filter.atTop (nhds 0) :=
  tendsto_jointCoshWidth _ (tendsto_expM1RatEps _ _)

/-- The `cosh` part of `sinhCoshRatApprox` as a pair of `Roundable`s bracketing `cosh q`. -/
theorem sinhCoshRatApprox_spec_cosh {w : ℕ} (hw : 64 ≤ w) (q : AzRat) (h0 : q.num ≠ 0) :
    ∃ lv hv : ℝ, Rounds (sinhCoshRatApprox q w).2.1 lv ∧
      Rounds (sinhCoshRatApprox q w).2.2 hv ∧ lv ≤ Real.cosh (AzRat.toRat q : ℝ) ∧
      Real.cosh (AzRat.toRat q : ℝ) ≤ hv ∧ hv - lv ≤ jointCoshRatEps q w := by
  have habs : ((AzRat.toRat q.abs : ℚ) : ℝ) = |((AzRat.toRat q : ℚ) : ℝ)| := by
    rw [AzRat.toRat_abs]
    push_cast
    rfl
  obtain ⟨lo, hi, hlo, hhi, h1, h2, h3⟩ := expM1RatBracket_spec hw q.abs h0
  obtain ⟨cl, ch, hcl, hch, c1, c2, c3⟩ :=
    coshOfExpM1_width hlo hhi (by rw [habs]; exact abs_nonneg _) h1 h2 h3 w
  rw [habs, cosh_abs] at c1 c2
  obtain ⟨lv, hv, hR1, hR2, hl, hh, he⟩ := enclApprox_spec false hcl hch c1 c2
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at hl hh
  exact ⟨lv, hv, hR1, hR2, hl, hh, by rw [he]; exact c3⟩

/-- The joint Ziv certificate for `sinh q` and `cosh q`. -/
theorem sinhCoshRatApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (q : AzRat)
    (h0 : q.num ≠ 0) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible₂ (sinhCoshRatApprox q (w₀ * 2 ^ f)) p mode).isSome = true :=
  exists_isSome₂_of_irrational_threshold p mode (sinhCoshRatApprox q)
    (irrational_sinh_toRat q h0) (irrational_cosh_toRat q h0) (sinhRatEps q)
    (jointCoshRatEps q) (tendsto_sinhRatEps q) (tendsto_jointCoshRatEps q) 64
    (fun w hw => by rw [sinhCoshRatApprox_fst]; exact sinhRatApprox_spec hw q h0)
    (fun _ hw => sinhCoshRatApprox_spec_cosh hw q h0) w₀ hw₀

end Azurite.AzFloat
