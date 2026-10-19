/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Agm
import Azurite.AzFloat.Equiv.AddSubRat
import Azurite.AzFloat.Equiv.Compare
import Azurite.AzFloat.Equiv.Conversion
import Azurite.AzFloat.Equiv.Mul
import Azurite.AzFloat.Equiv.Sqrt
import Azurite.AzFloat.Equiv.Sum
import Azurite.AzRat.Equiv.Compare
import Azurite.BrentZimmermann.Chapter4.AGM

/-!
# Equivalence: the arithmetic–geometric mean

`Spec.agm` is the extended-real specification (`NaN` for negatives and for `AGM(∞, 0)`; `0`
for a zero argument; `∞` for an infinite one; `AGM a b` of `AGM.lean` for positive reals).  The
interval iteration keeps the exact pair enclosed (`Encloses`, preserved by `agmStep` because
every operation rounds in the safe direction and the step is monotone), so after `m ≥ 1` steps
`bLo ≤ b_m < AGM ≤ a_m ≤ aHi` (`agmApprox_spec`, strictness from `agmB_lt_AGM`), and Ziv's
loop answers correctly whenever it answers (`zivLoop_eq_of_ne_nan`).  The main theorem
`agmPrecRound_eq_or`: `agmPrecRound x y p mode` is `liftVal₂ Spec.agm x y p mode` or the `NaN`
fallback of an exhausted fuel.
-/

namespace Azurite.AzFloat

open Azurite.BZ
open RoundingTarget

/-! ### The specification -/

namespace Spec

open Classical in
/-- Extended-real AGM: `NaN` for a negative argument and for `AGM(±∞, 0)`, `0` for a zero
argument, `∞` for an infinite one, `AGM a b` for positive reals. -/
noncomputable def agm (a b : EReal) : Option EReal :=
  if a < 0 ∨ b < 0 then none
  else if a = 0 ∨ b = 0 then (if a = ⊤ ∨ b = ⊤ then none else some 0)
  else if a = ⊤ ∨ b = ⊤ then some ⊤
  else some ((AGM a.toReal b.toReal : ℝ) : EReal)

theorem agm_coe_coe {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    agm (a : EReal) (b : EReal) = some ((AGM a b : ℝ) : EReal) := by
  have h1 : ¬ ((a : EReal) < 0 ∨ (b : EReal) < 0) := by
    push Not
    exact ⟨EReal.coe_nonneg.mpr ha.le, EReal.coe_nonneg.mpr hb.le⟩
  have h2 : ¬ ((a : EReal) = 0 ∨ (b : EReal) = 0) := by
    push Not
    exact ⟨EReal.coe_ne_zero.mpr ha.ne', EReal.coe_ne_zero.mpr hb.ne'⟩
  have h3 : ¬ ((a : EReal) = ⊤ ∨ (b : EReal) = ⊤) := by
    push Not
    exact ⟨EReal.coe_ne_top a, EReal.coe_ne_top b⟩
  rw [agm]
  simp only [h1, h2, h3, ite_false, EReal.toReal_coe]

theorem agm_of_neg_left {a : EReal} (ha : a < 0) (b : EReal) : agm a b = none := by
  rw [agm]; simp only [ha, true_or, ite_true]

theorem agm_of_neg_right (a : EReal) {b : EReal} (hb : b < 0) : agm a b = none := by
  rw [agm]; simp only [hb, or_true, ite_true]

theorem agm_zero_of_nonneg_ne_top {b : EReal} (hb : 0 ≤ b) (hbt : b ≠ ⊤) : agm 0 b = some 0 := by
  have h1 : ¬ ((0 : EReal) < 0 ∨ b < 0) := by push Not; exact ⟨le_rfl, hb⟩
  have h3 : ¬ ((0 : EReal) = ⊤ ∨ b = ⊤) := by push Not; exact ⟨EReal.zero_ne_top, hbt⟩
  rw [agm]; simp only [h1, h3, ite_false, true_or, ite_true]

theorem agm_of_nonneg_ne_top_zero {a : EReal} (ha : 0 ≤ a) (hat : a ≠ ⊤) : agm a 0 = some 0 := by
  have h1 : ¬ (a < 0 ∨ (0 : EReal) < 0) := by push Not; exact ⟨ha, le_rfl⟩
  have h3 : ¬ (a = ⊤ ∨ (0 : EReal) = ⊤) := by push Not; exact ⟨hat, EReal.zero_ne_top⟩
  rw [agm]; simp only [h1, h3, ite_false, or_true, ite_true]

theorem agm_zero_top : agm 0 ⊤ = none := by
  have h1 : ¬ ((0 : EReal) < 0 ∨ (⊤ : EReal) < 0) := by push Not; exact ⟨le_rfl, le_top⟩
  rw [agm]; simp only [h1, ite_false, true_or, or_true, ite_true]

theorem agm_top_zero : agm ⊤ 0 = none := by
  have h1 : ¬ ((⊤ : EReal) < 0 ∨ (0 : EReal) < 0) := by push Not; exact ⟨le_top, le_rfl⟩
  rw [agm]; simp only [h1, ite_false, true_or, or_true, ite_true]

theorem agm_top_of_pos {b : EReal} (hb : 0 < b) : agm ⊤ b = some ⊤ := by
  have h1 : ¬ ((⊤ : EReal) < 0 ∨ b < 0) := by push Not; exact ⟨le_top, hb.le⟩
  have h2 : ¬ ((⊤ : EReal) = 0 ∨ b = 0) := by push Not; exact ⟨EReal.top_ne_zero, hb.ne'⟩
  rw [agm]; simp only [h1, h2, ite_false, true_or, ite_true]

theorem agm_of_pos_top {a : EReal} (ha : 0 < a) : agm a ⊤ = some ⊤ := by
  have h1 : ¬ (a < 0 ∨ (⊤ : EReal) < 0) := by push Not; exact ⟨ha.le, le_top⟩
  have h2 : ¬ (a = 0 ∨ (⊤ : EReal) = 0) := by push Not; exact ⟨ha.ne', EReal.top_ne_zero⟩
  rw [agm]; simp only [h1, h2, ite_false, or_true, ite_true]

end Spec

/-! ### Directed roundings -/

/-- Rounding a real down gives a real below it, nonnegative when the real is. -/
theorem roundVal_floor_spec (w : ℕ) [NeZero w] (r : ℝ) :
    ∃ v : ℝ, (roundVal w .Floor (some (r : EReal))).1.toVal = some (v : EReal) ∧ v ≤ r ∧
      (0 ≤ r → 0 ≤ v) := by
  obtain ⟨v, hv⟩ : ∃ v : ℝ, ((v : ℝ) : EReal) = (roundFloor (floatSet w) r).val := by
    rw [val_roundFloor_floatSet]; exact precisionSet_exists_real _
  refine ⟨v, ?_, ?_, ?_⟩
  · rw [(roundVal_coe w .Floor r).1]; exact congrArg some hv.symm
  · have := (isGreatest_roundFloor (floatSet w) r).1.2
    rw [← hv] at this
    exact EReal.coe_le_coe_iff.mp this
  · intro hr
    have h0 : ((0 : ℝ) : EReal) ∈ floatSet w := ⟨zero, Or.inr rfl, by rw [toVal_zero]; rfl⟩
    have := (isGreatest_roundFloor (floatSet w) r).2 ⟨h0, EReal.coe_le_coe_iff.mpr hr⟩
    rw [← hv] at this
    exact EReal.coe_le_coe_iff.mp this

/-- Rounding a real up gives a real above it. -/
theorem roundVal_ceiling_spec (w : ℕ) [NeZero w] (r : ℝ) :
    ∃ v : ℝ, (roundVal w .Ceiling (some (r : EReal))).1.toVal = some (v : EReal) ∧ r ≤ v := by
  obtain ⟨v, hv⟩ : ∃ v : ℝ, ((v : ℝ) : EReal) = (roundCeiling (floatSet w) r).val := by
    rw [val_roundCeiling_floatSet]; exact precisionSet_exists_real _
  refine ⟨v, ?_, ?_⟩
  · rw [(roundVal_coe w .Ceiling r).1]; exact congrArg some hv.symm
  · have := (isLeast_roundCeiling (floatSet w) r).1.2
    rw [← hv] at this
    exact EReal.coe_le_coe_iff.mp this

variable {u v : AzFloat} {uv vv : ℝ}

theorem addFloor_spec (hu : u.toVal = some (uv : EReal)) (hv : v.toVal = some (vv : EReal))
    (w : ℕ) [NeZero w] :
    ∃ r : ℝ, (addPrecRound u v w .Floor).1.toVal = some (r : EReal) ∧ r ≤ uv + vv ∧
      (0 ≤ uv + vv → 0 ≤ r) := by
  rw [addPrecRound_eq_liftVal₂, liftVal₂, hu, hv, Option.bind_some, Option.bind_some,
    Spec.add_coe_coe]
  exact roundVal_floor_spec w _

theorem addCeiling_spec (hu : u.toVal = some (uv : EReal)) (hv : v.toVal = some (vv : EReal))
    (w : ℕ) [NeZero w] :
    ∃ r : ℝ, (addPrecRound u v w .Ceiling).1.toVal = some (r : EReal) ∧ uv + vv ≤ r := by
  rw [addPrecRound_eq_liftVal₂, liftVal₂, hu, hv, Option.bind_some, Option.bind_some,
    Spec.add_coe_coe]
  exact roundVal_ceiling_spec w _

theorem mulFloor_spec (hu : u.toVal = some (uv : EReal)) (hv : v.toVal = some (vv : EReal))
    (w : ℕ) [NeZero w] :
    ∃ r : ℝ, (mulPrecRound u v w .Floor).1.toVal = some (r : EReal) ∧ r ≤ uv * vv ∧
      (0 ≤ uv * vv → 0 ≤ r) := by
  rw [mulPrecRound_eq_liftVal₂, liftVal₂, hu, hv, Option.bind_some, Option.bind_some,
    Spec.mul_coe_coe]
  exact roundVal_floor_spec w _

theorem mulCeiling_spec (hu : u.toVal = some (uv : EReal)) (hv : v.toVal = some (vv : EReal))
    (w : ℕ) [NeZero w] :
    ∃ r : ℝ, (mulPrecRound u v w .Ceiling).1.toVal = some (r : EReal) ∧ uv * vv ≤ r := by
  rw [mulPrecRound_eq_liftVal₂, liftVal₂, hu, hv, Option.bind_some, Option.bind_some,
    Spec.mul_coe_coe]
  exact roundVal_ceiling_spec w _

theorem sqrtFloor_spec (hu : u.toVal = some (uv : EReal)) (h0 : 0 ≤ uv) (w : ℕ) [NeZero w] :
    ∃ r : ℝ, (sqrtPrecRound u w .Floor).1.toVal = some (r : EReal) ∧ r ≤ Real.sqrt uv ∧
      0 ≤ r := by
  rw [sqrtPrecRound_eq_liftVal, liftVal, hu, Option.bind_some, Spec.sqrt_coe uv h0]
  obtain ⟨r, hr, hle, hnn⟩ := roundVal_floor_spec w (Real.sqrt uv)
  exact ⟨r, hr, hle, hnn (Real.sqrt_nonneg _)⟩

theorem sqrtCeiling_spec (hu : u.toVal = some (uv : EReal)) (h0 : 0 ≤ uv) (w : ℕ) [NeZero w] :
    ∃ r : ℝ, (sqrtPrecRound u w .Ceiling).1.toVal = some (r : EReal) ∧ Real.sqrt uv ≤ r := by
  rw [sqrtPrecRound_eq_liftVal, liftVal, hu, Option.bind_some, Spec.sqrt_coe uv h0]
  exact roundVal_ceiling_spec w _

/-- Halving a finite value. -/
theorem toVal_half (hu : u.toVal = some (uv : EReal)) :
    (u >>> (1 : Nat)).toVal = some ((uv / 2 : ℝ) : EReal) := by
  rw [toVal_shiftRight_one (isFinite_of_toVal_coe hu), fval_of_toVal_coe hu]

/-! ### The enclosure invariant -/

/-- The bounds enclose the exact pair `(a_n, b_n)`, the lower bounds nonnegative. -/
def Encloses (a b : ℝ) (n : ℕ) (s : AgmBounds) : Prop :=
  (∃ v : ℝ, s.aLo.toVal = some (v : EReal) ∧ 0 ≤ v ∧ v ≤ agmA a b n) ∧
  (∃ v : ℝ, s.aHi.toVal = some (v : EReal) ∧ agmA a b n ≤ v) ∧
  (∃ v : ℝ, s.bLo.toVal = some (v : EReal) ∧ 0 ≤ v ∧ v ≤ agmB a b n) ∧
  (∃ v : ℝ, s.bHi.toVal = some (v : EReal) ∧ agmB a b n ≤ v)

variable {a b : ℝ}

theorem encloses_init {x y : AzFloat} (hx : x.toVal = some (a : EReal))
    (hy : y.toVal = some (b : EReal)) (ha : 0 < a) (hb : 0 < b) :
    Encloses a b 0 ⟨x, x, y, y⟩ :=
  ⟨⟨a, hx, ha.le, le_rfl⟩, ⟨a, hx, le_rfl⟩, ⟨b, hy, hb.le, le_rfl⟩, ⟨b, hy, le_rfl⟩⟩

/-- One interval step preserves the enclosure: the step is monotone in both arguments and
every rounding is in the safe direction. -/
theorem encloses_agmStep (ha : 0 < a) (hb : 0 < b) {n : ℕ} {s : AgmBounds} (w : ℕ) [NeZero w]
    (h : Encloses a b n s) : Encloses a b (n + 1) (agmStep w s) := by
  obtain ⟨⟨al, hal, hal0, halle⟩, ⟨ah, hah, hahge⟩, ⟨bl, hbl, hbl0, hblle⟩, ⟨bh, hbh, hbhge⟩⟩ := h
  obtain ⟨hA, hB⟩ := agm_pos ha hb n
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨r, hr, hrle, hr0⟩ := addFloor_spec hal hbl w
    refine ⟨r / 2, toVal_half hr, by linarith [hr0 (by linarith)], ?_⟩
    rw [agmA_succ]; linarith
  · obtain ⟨r, hr, hrge⟩ := addCeiling_spec hah hbh w
    refine ⟨r / 2, toVal_half hr, ?_⟩
    rw [agmA_succ]; linarith
  · obtain ⟨m, hm, hmle, hm0⟩ := mulFloor_spec hal hbl w
    have hm0' : 0 ≤ m := hm0 (mul_nonneg hal0 hbl0)
    obtain ⟨r, hr, hrle, hr0⟩ := sqrtFloor_spec hm hm0' w
    refine ⟨r, hr, hr0, ?_⟩
    rw [agmB_succ]
    exact hrle.trans (Real.sqrt_le_sqrt (hmle.trans (mul_le_mul halle hblle hbl0 hA.le)))
  · obtain ⟨m, hm, hmge⟩ := mulCeiling_spec hah hbh w
    have hm0 : 0 ≤ m := le_trans (mul_nonneg (hA.le.trans hahge) (hB.le.trans hbhge)) hmge
    obtain ⟨r, hr, hrge⟩ := sqrtCeiling_spec hm hm0 w
    refine ⟨r, hr, ?_⟩
    rw [agmB_succ]
    exact (Real.sqrt_le_sqrt ((mul_le_mul hahge hbhge hB.le (by linarith)).trans hmge)).trans hrge

theorem encloses_agmIter (ha : 0 < a) (hb : 0 < b) (w : ℕ) [NeZero w] :
    ∀ (fuel : ℕ) (s : AgmBounds) (n : ℕ), Encloses a b n s →
      ∃ m, n ≤ m ∧ Encloses a b m (agmIter w fuel s)
  | 0, s, n, h => ⟨n, le_rfl, h⟩
  | fuel + 1, s, n, h => by
    rw [agmIter]
    split_ifs
    · exact ⟨n, le_rfl, h⟩
    · obtain ⟨m, hm, hm'⟩ :=
        encloses_agmIter ha hb w fuel (agmStep w s) (n + 1) (encloses_agmStep ha hb w h)
      exact ⟨m, by omega, hm'⟩

/-- The bracket from any initial enclosure: `bLo ≤ AGM ≤ aHi` with `bLo < AGM` strictly, for
distinct positive values. -/
theorem agmApproxFrom_spec {s₀ : AgmBounds} (h₀ : Encloses a b 0 s₀) (ha : 0 < a) (hb : 0 < b)
    (hab : a ≠ b) (fuel w : ℕ) [NeZero w] :
    ∃ lv hv : ℝ, Rounds (agmApproxFrom s₀ fuel w).1 lv ∧ Rounds (agmApproxFrom s₀ fuel w).2 hv ∧
      lv ≤ AGM a b ∧ AGM a b ≤ hv ∧ (lv = AGM a b → hv = AGM a b) := by
  have h1 := encloses_agmStep ha hb w h₀
  obtain ⟨m, hm, ⟨-, ⟨ah, hah, hahge⟩, ⟨bl, hbl, -, hblle⟩, -⟩⟩ :=
    encloses_agmIter ha hb w fuel _ 1 h1
  refine ⟨bl, ah, ?_, ?_, hblle.trans (agmB_le_AGM ha hb hm), (AGM_le_agmA ha hb hm).trans hahge,
    fun h => absurd (h ▸ hblle) (not_le.mpr (agmB_lt_AGM ha hb hab hm))⟩
  · have := rounds_setPrecRound (isFinite_of_toVal_coe hbl)
    rwa [fval_of_toVal_coe hbl] at this
  · have := rounds_setPrecRound (isFinite_of_toVal_coe hah)
    rwa [fval_of_toVal_coe hah] at this

theorem agmApprox_spec {x y : AzFloat} (hx : x.toVal = some (a : EReal))
    (hy : y.toVal = some (b : EReal)) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) (w : ℕ)
    [NeZero w] :
    ∃ lv hv : ℝ, Rounds (agmApprox x y w).1 lv ∧ Rounds (agmApprox x y w).2 hv ∧
      lv ≤ AGM a b ∧ AGM a b ≤ hv ∧ (lv = AGM a b → hv = AGM a b) :=
  agmApproxFrom_spec (encloses_init hx hy ha hb) ha hb hab _ w

theorem finiteVal_true_pos_ereal (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m) :
    (0 : EReal) < ((finiteVal true e m : ℝ) : EReal) :=
  EReal.coe_pos.mpr (finiteVal_true_pos e hv)

theorem finiteVal_false_neg_ereal (e : AzInt) {q : ℕ} {m : AzNat} (hv : FiniteValid q m) :
    ((finiteVal false e m : ℝ) : EReal) < 0 := by
  rw [finiteVal_false]
  exact EReal.coe_neg'.mpr (neg_neg_of_pos (finiteVal_true_pos e hv))

/-! ### The rational variants -/

/-- The floor and ceiling of a rational enclose it (the floor nonnegative when it is). -/
theorem ratBounds_spec (q : AzRat) (w : ℕ) [NeZero w] :
    ∃ lo hi : ℝ, (ratBounds q w).1.toVal = some (lo : EReal) ∧
      (ratBounds q w).2.toVal = some (hi : EReal) ∧ lo ≤ (AzRat.toRat q : ℝ) ∧
      (0 ≤ (AzRat.toRat q : ℝ) → 0 ≤ lo) ∧ (AzRat.toRat q : ℝ) ≤ hi := by
  obtain ⟨lo, hlo, hle, hnn⟩ := roundVal_floor_spec w (AzRat.toRat q : ℝ)
  obtain ⟨hi, hhi, hge⟩ := roundVal_ceiling_spec w (AzRat.toRat q : ℝ)
  refine ⟨lo, hi, ?_, ?_, hle, hnn, hge⟩
  · show (ofAzRatRound q w .Floor).1.toVal = _
    rw [ofAzRatRound_eq_roundVal]; exact hlo
  · show (ofAzRatRound q w .Ceiling).1.toVal = _
    rw [ofAzRatRound_eq_roundVal]; exact hhi

theorem encloses_init_bounds {aLo aHi bLo bHi : AzFloat} {al ah bl bh : ℝ}
    (hal : aLo.toVal = some (al : EReal)) (hah : aHi.toVal = some (ah : EReal))
    (hbl : bLo.toVal = some (bl : EReal)) (hbh : bHi.toVal = some (bh : EReal))
    (hal0 : 0 ≤ al) (hale : al ≤ a) (hage : a ≤ ah) (hbl0 : 0 ≤ bl) (hble : bl ≤ b)
    (hbge : b ≤ bh) : Encloses a b 0 ⟨aLo, aHi, bLo, bHi⟩ :=
  ⟨⟨al, hal, hal0, hale⟩, ⟨ah, hah, hage⟩, ⟨bl, hbl, hbl0, hble⟩, ⟨bh, hbh, hbge⟩⟩

theorem agmRatApprox_spec {q₁ q₂ : AzRat} (ha : 0 < (AzRat.toRat q₁ : ℝ))
    (hb : 0 < (AzRat.toRat q₂ : ℝ)) (hab : (AzRat.toRat q₁ : ℝ) ≠ AzRat.toRat q₂) (w : ℕ)
    [NeZero w] :
    ∃ lv hv : ℝ, Rounds (agmRatApprox q₁ q₂ w).1 lv ∧ Rounds (agmRatApprox q₁ q₂ w).2 hv ∧
      lv ≤ AGM (AzRat.toRat q₁) (AzRat.toRat q₂) ∧ AGM (AzRat.toRat q₁) (AzRat.toRat q₂) ≤ hv ∧
      (lv = AGM (AzRat.toRat q₁) (AzRat.toRat q₂) →
        hv = AGM (AzRat.toRat q₁) (AzRat.toRat q₂)) := by
  obtain ⟨lo₁, hi₁, h1, h2, h3, h4, h5⟩ := ratBounds_spec q₁ w
  obtain ⟨lo₂, hi₂, h1', h2', h3', h4', h5'⟩ := ratBounds_spec q₂ w
  exact agmApproxFrom_spec (encloses_init_bounds h1 h2 h1' h2' (h4 ha.le) h3 h5 (h4' hb.le) h3' h5')
    ha hb hab _ w

theorem agmFloatRatApprox_spec {x : AzFloat} {q : AzRat} (hx : x.toVal = some (a : EReal))
    (ha : 0 < a) (hb : 0 < (AzRat.toRat q : ℝ)) (hab : a ≠ AzRat.toRat q) (w : ℕ) [NeZero w] :
    ∃ lv hv : ℝ, Rounds (agmFloatRatApprox x q w).1 lv ∧ Rounds (agmFloatRatApprox x q w).2 hv ∧
      lv ≤ AGM a (AzRat.toRat q) ∧ AGM a (AzRat.toRat q) ≤ hv ∧
      (lv = AGM a (AzRat.toRat q) → hv = AGM a (AzRat.toRat q)) := by
  obtain ⟨lo, hi, h1, h2, h3, h4, h5⟩ := ratBounds_spec q w
  exact agmApproxFrom_spec (encloses_init_bounds hx hx h1 h2 ha.le le_rfl le_rfl (h4 hb.le) h3 h5)
    ha hb hab _ w

/-- Order on `AzRat` against `0`, as reals. -/
theorem azRat_lt_zero_iff (q : AzRat) : q < 0 ↔ (AzRat.toRat q : ℝ) < 0 := by
  show AzRat.cmp q 0 = .lt ↔ _
  rw [AzRat.cmp_eq_compare, AzRat.toRat_zero, compare_lt_iff_lt]
  exact (Rat.cast_lt_zero (K := ℝ)).symm

theorem azRat_eq_zero_iff (q : AzRat) : q = 0 ↔ (AzRat.toRat q : ℝ) = 0 := by
  constructor
  · rintro rfl; simp
  · intro h
    apply AzRat.toRat_injective
    rw [AzRat.toRat_zero]; exact_mod_cast h

theorem azRat_toRat_eq_iff (q₁ q₂ : AzRat) :
    q₁ = q₂ ↔ (AzRat.toRat q₁ : ℝ) = AzRat.toRat q₂ :=
  ⟨fun h => by rw [h], fun h => AzRat.toRat_injective (by exact_mod_cast h)⟩

/-- A float is zero iff its value is `0`. -/
theorem isZero_iff_toVal (x : AzFloat) : x.isZero = true ↔ x.toVal = some 0 := by
  cases x with
  | nan => simp [isZero, toVal]
  | infinity s => cases s <;> simp [isZero, toVal, EReal.top_ne_zero, EReal.bot_ne_zero]
  | zero => simp [isZero, toVal]
  | finite s e q m hv =>
    constructor
    · intro h; exact absurd h (by simp [isZero])
    · intro h
      simp only [toVal, Option.some.injEq] at h
      exact absurd (EReal.coe_eq_zero.mp h) (finiteVal_ne_zero s e hv)

/-- The correctly rounded `x − q` at one bit is zero iff `x = q`. -/
theorem subRat_isZero_iff {x : AzFloat} (hx : x.toVal = some (a : EReal)) (q : AzRat) :
    (subRatPrecRound x q 1 .Floor).1.isZero = true ↔ a = AzRat.toRat q := by
  rw [isZero_iff_toVal, subRatPrecRound_eq_liftVal, liftVal, hx, Option.bind_some, Spec.sub,
    ← EReal.coe_neg, Spec.add_coe_coe]
  constructor
  · intro h
    rw [(roundVal_coe 1 .Floor _).1, Option.some.injEq] at h
    have h' : (roundFloor (floatSet 1) (a + -(AzRat.toRat q : ℝ))).val = 0 := h
    rw [val_roundFloor_floatSet] at h'
    have := eq_zero_of_roundFloor_eq_zero 1 _ h'
    linarith
  · intro h
    rw [h, add_neg_cancel, EReal.coe_zero, roundVal_zero]
    rfl

/-- **`agmRatPrecRound` is the correctly rounded AGM of two rationals, unless the fuel runs
out.** -/
theorem agmRatPrecRound_eq_or (q₁ q₂ : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    agmRatPrecRound q₁ q₂ p mode
        = liftVal₀ (Spec.agm (AzRat.toRat q₁ : ℝ) (AzRat.toRat q₂ : ℝ)) p mode ∨
      agmRatPrecRound q₁ q₂ p mode = (nan, .eq) := by
  unfold agmRatPrecRound liftVal₀
  split_ifs with h1 h2 h3
  · left
    rcases h1 with h | h
    · rw [Spec.agm_of_neg_left (EReal.coe_neg'.mpr ((azRat_lt_zero_iff q₁).mp h))]; rfl
    · rw [Spec.agm_of_neg_right _ (EReal.coe_neg'.mpr ((azRat_lt_zero_iff q₂).mp h))]; rfl
  · left
    push Not at h1
    obtain ⟨hq₁, hq₂⟩ := h1
    rw [azRat_lt_zero_iff, not_lt] at hq₁ hq₂
    rcases h2 with h | h
    · rw [(azRat_eq_zero_iff q₁).mp h, EReal.coe_zero,
        Spec.agm_zero_of_nonneg_ne_top (EReal.coe_nonneg.mpr hq₂) (EReal.coe_ne_top _),
        roundVal_zero]
    · rw [(azRat_eq_zero_iff q₂).mp h, EReal.coe_zero,
        Spec.agm_of_nonneg_ne_top_zero (EReal.coe_nonneg.mpr hq₁) (EReal.coe_ne_top _),
        roundVal_zero]
  · left
    push Not at h1 h2
    obtain ⟨hq₁, -⟩ := h1
    obtain ⟨hz₁, -⟩ := h2
    rw [azRat_lt_zero_iff, not_lt] at hq₁
    have hz₁' : (AzRat.toRat q₁ : ℝ) ≠ 0 := fun h => hz₁ ((azRat_eq_zero_iff q₁).mpr h)
    have ha : 0 < (AzRat.toRat q₁ : ℝ) := lt_of_le_of_ne hq₁ (Ne.symm hz₁')
    rw [← h3, Spec.agm_coe_coe ha ha, AGM_self ha.le, ofAzRatRound_eq_roundVal]
  · push Not at h1 h2
    obtain ⟨hq₁, hq₂⟩ := h1
    obtain ⟨hz₁, hz₂⟩ := h2
    rw [azRat_lt_zero_iff, not_lt] at hq₁ hq₂
    have hz₁' : (AzRat.toRat q₁ : ℝ) ≠ 0 := fun h => hz₁ ((azRat_eq_zero_iff q₁).mpr h)
    have hz₂' : (AzRat.toRat q₂ : ℝ) ≠ 0 := fun h => hz₂ ((azRat_eq_zero_iff q₂).mpr h)
    have ha : 0 < (AzRat.toRat q₁ : ℝ) := lt_of_le_of_ne hq₁ (Ne.symm hz₁')
    have hb : 0 < (AzRat.toRat q₂ : ℝ) := lt_of_le_of_ne hq₂ (Ne.symm hz₂')
    have hab : (AzRat.toRat q₁ : ℝ) ≠ AzRat.toRat q₂ := fun h =>
      h3 ((azRat_toRat_eq_iff q₁ q₂).mpr h)
    rcases eq_or_ne (zivLoop (agmRatApprox q₁ q₂) p mode (agmFuel p) (p + zivGuardBits))
      (nan, .eq) with hz | hz
    · right; exact hz
    · left
      rw [Spec.agm_coe_coe ha hb]
      exact zivLoop_eq_of_ne_nan p mode _ (AGM _ _) (fun w hw => by
        have : NeZero w := ⟨hw.ne'⟩
        exact agmRatApprox_spec ha hb hab w) _ _ (by unfold zivGuardBits; omega) hz

/-- **`agmFloatRatPrecRound` is the correctly rounded `AGM(x, q)`, unless the fuel runs out.** -/
theorem agmFloatRatPrecRound_eq_or (x : AzFloat) (q : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    agmFloatRatPrecRound x q p mode
        = roundVal p mode (x.toVal.bind fun a => Spec.agm a (AzRat.toRat q : ℝ)) ∨
      agmFloatRatPrecRound x q p mode = (nan, .eq) := by
  have hq0 : ((AzRat.toRat q : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
  cases x with
  | nan => left; simp [agmFloatRatPrecRound, isNaN]
  | infinity s =>
    left
    cases s with
    | false =>
      simp [agmFloatRatPrecRound, isNaN, isNegative, Spec.agm_of_neg_left EReal.bot_lt_zero]
    | true =>
      by_cases hneg : q < 0
      · have h := EReal.coe_neg'.mpr ((azRat_lt_zero_iff q).mp hneg)
        simp [agmFloatRatPrecRound, isNaN, isNegative, hneg, Spec.agm_of_neg_right _ h]
      · by_cases hz : q = 0
        · subst hz
          simp [agmFloatRatPrecRound, isNaN, isNegative, isInfinite, hneg, Spec.agm_top_zero]
        · have hpos : (0 : EReal) < ((AzRat.toRat q : ℝ) : EReal) := by
            rw [azRat_lt_zero_iff, not_lt] at hneg
            rw [azRat_eq_zero_iff] at hz
            exact EReal.coe_pos.mpr (lt_of_le_of_ne hneg (Ne.symm hz))
          simp [agmFloatRatPrecRound, isNaN, isNegative, isZero, isInfinite, hneg, hz,
            Spec.agm_top_of_pos hpos]
  | zero =>
    left
    by_cases hneg : q < 0
    · have h := EReal.coe_neg'.mpr ((azRat_lt_zero_iff q).mp hneg)
      simp [agmFloatRatPrecRound, isNaN, isNegative, hneg, Spec.agm_of_neg_right _ h]
    · have hq : (0 : EReal) ≤ ((AzRat.toRat q : ℝ) : EReal) := by
        rw [azRat_lt_zero_iff, not_lt] at hneg
        exact EReal.coe_nonneg.mpr hneg
      by_cases hz : q = 0
      · subst hz
        simp [agmFloatRatPrecRound, isNaN, isNegative, isInfinite, hneg,
          Spec.agm_zero_of_nonneg_ne_top le_rfl EReal.zero_ne_top]
      · simp [agmFloatRatPrecRound, isNaN, isNegative, isZero, hneg, hz,
          Spec.agm_zero_of_nonneg_ne_top hq hq0]
  | finite s e q' m hv =>
    cases s with
    | false =>
      left
      simp [agmFloatRatPrecRound, isNaN, isNegative,
        Spec.agm_of_neg_left (finiteVal_false_neg_ereal e hv)]
    | true =>
      set X := finite true e q' m hv with hX
      have hx : X.toVal = some ((finiteVal true e m : ℝ) : EReal) := rfl
      have ha := finiteVal_true_pos e hv
      by_cases hneg : q < 0
      · left
        have h := EReal.coe_neg'.mpr ((azRat_lt_zero_iff q).mp hneg)
        simp [agmFloatRatPrecRound, hX, isNaN, isNegative, hneg, Spec.agm_of_neg_right _ h]
      · have hq : 0 ≤ (AzRat.toRat q : ℝ) := by rwa [azRat_lt_zero_iff, not_lt] at hneg
        by_cases hz : q = 0
        · left
          subst hz
          simp [agmFloatRatPrecRound, hX, isNaN, isNegative, isInfinite, hneg,
            Spec.agm_of_nonneg_ne_top_zero (finiteVal_true_pos_ereal e hv).le (EReal.coe_ne_top _)]
        · have hb : 0 < (AzRat.toRat q : ℝ) := by
            rw [azRat_eq_zero_iff] at hz
            exact lt_of_le_of_ne hq (Ne.symm hz)
          have hred : agmFloatRatPrecRound X q p mode
              = if (subRatPrecRound X q 1 .Floor).1.isZero then setPrecRound X p mode
                else zivLoop (agmFloatRatApprox X q) p mode (agmFuel p) (p + zivGuardBits) := by
            simp [agmFloatRatPrecRound, hX, isNaN, isNegative, isZero, isInfinite, hneg, hz]
          rw [hred, hx, Option.bind_some, Spec.agm_coe_coe ha hb]
          by_cases heq : (subRatPrecRound X q 1 .Floor).1.isZero = true
          · left
            simp only [heq, ↓reduceIte]
            have hab := (subRat_isZero_iff hx q).mp heq
            rw [← hab, AGM_self ha.le]
            exact setPrecRound_eq_roundVal hx p mode
          · simp only [heq]
            have hab : finiteVal true e m ≠ AzRat.toRat q := fun h =>
              heq ((subRat_isZero_iff hx q).mpr h)
            rcases eq_or_ne (zivLoop (agmFloatRatApprox X q) p mode (agmFuel p) (p + zivGuardBits))
              (nan, .eq) with hzv | hzv
            · right; exact hzv
            · left
              exact zivLoop_eq_of_ne_nan p mode _ (AGM _ _) (fun w hw => by
                have : NeZero w := ⟨hw.ne'⟩
                exact agmFloatRatApprox_spec hx ha hb hab w) _ _ (by unfold zivGuardBits; omega) hzv

/-! ### The main theorem -/

/-- **`agmPrecRound` is the correctly rounded AGM, unless the fuel runs out** (which the
transcendence of the AGM of distinct positive algebraic numbers rules out in principle). -/
theorem agmPrecRound_eq_or (x y : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    agmPrecRound x y p mode = liftVal₂ Spec.agm x y p mode ∨
      agmPrecRound x y p mode = (nan, .eq) := by
  cases x with
  | nan => left; simp [agmPrecRound, isNaN, liftVal₂]
  | infinity s =>
    cases y with
    | nan => left; simp [agmPrecRound, isNaN, liftVal₂]
    | infinity t =>
      left
      cases s <;> cases t <;>
        simp [agmPrecRound, isNaN, isNegative, isZero, isInfinite, liftVal₂, Spec.agm_top_of_pos,
          Spec.agm_of_neg_left, Spec.agm_of_neg_right, EReal.bot_lt_zero, EReal.zero_lt_top]
    | zero =>
      left
      cases s <;> simp [agmPrecRound, isNaN, isNegative, isZero, isInfinite, liftVal₂,
        Spec.agm_top_zero, Spec.agm_of_neg_left, EReal.bot_lt_zero]
    | finite t e q m hv =>
      left
      cases s <;> cases t <;>
        simp [agmPrecRound, isNaN, isNegative, isZero, isInfinite, liftVal₂,
          Spec.agm_top_of_pos (finiteVal_true_pos_ereal e hv), Spec.agm_of_neg_left,
          Spec.agm_of_neg_right, EReal.bot_lt_zero, finiteVal_false_neg_ereal e hv]
  | zero =>
    cases y with
    | nan => left; simp [agmPrecRound, isNaN, liftVal₂]
    | infinity t =>
      left
      cases t <;> simp [agmPrecRound, isNaN, isNegative, isZero, isInfinite, liftVal₂,
        Spec.agm_zero_top, Spec.agm_of_neg_right, EReal.bot_lt_zero]
    | zero =>
      left
      simp [agmPrecRound, isNaN, isNegative, isZero, isInfinite, liftVal₂,
        Spec.agm_zero_of_nonneg_ne_top le_rfl EReal.zero_ne_top]
    | finite t e q m hv =>
      left
      cases t <;> simp [agmPrecRound, isNaN, isNegative, isZero, isInfinite, liftVal₂,
        Spec.agm_of_neg_right, finiteVal_false_neg_ereal e hv,
        Spec.agm_zero_of_nonneg_ne_top (finiteVal_true_pos_ereal e hv).le (EReal.coe_ne_top _)]
  | finite s e q m hv =>
    cases y with
    | nan => left; simp [agmPrecRound, isNaN, liftVal₂]
    | infinity t =>
      left
      cases s <;> cases t <;>
        simp [agmPrecRound, isNaN, isNegative, isZero, isInfinite, liftVal₂,
          Spec.agm_of_pos_top (finiteVal_true_pos_ereal e hv), Spec.agm_of_neg_left,
          Spec.agm_of_neg_right, EReal.bot_lt_zero, finiteVal_false_neg_ereal e hv]
    | zero =>
      left
      cases s <;> simp [agmPrecRound, isNaN, isNegative, isZero, isInfinite, liftVal₂,
        Spec.agm_of_neg_left, finiteVal_false_neg_ereal e hv,
        Spec.agm_of_nonneg_ne_top_zero (finiteVal_true_pos_ereal e hv).le (EReal.coe_ne_top _)]
    | finite t e' q' m' hv' =>
      cases s with
      | false =>
        left
        simp [agmPrecRound, isNaN, isNegative, liftVal₂, Spec.agm_of_neg_left,
          finiteVal_false_neg_ereal e hv]
      | true =>
        cases t with
        | false =>
          left
          simp [agmPrecRound, isNaN, isNegative, liftVal₂, Spec.agm_of_neg_right,
            finiteVal_false_neg_ereal e' hv']
        | true =>
          set X := finite true e q m hv with hX
          set Y := finite true e' q' m' hv' with hY
          have hx : X.toVal = some ((finiteVal true e m : ℝ) : EReal) := rfl
          have hy : Y.toVal = some ((finiteVal true e' m' : ℝ) : EReal) := rfl
          have ha := finiteVal_true_pos e hv
          have hb := finiteVal_true_pos e' hv'
          have hred : agmPrecRound X Y p mode
              = if eqIEEE X Y then setPrecRound X p mode
                else zivLoop (agmApprox X Y) p mode (agmFuel p) (p + zivGuardBits) := by
            simp [agmPrecRound, hX, hY, isNaN, isNegative, isZero, isInfinite]
          rw [hred, liftVal₂, hx, hy, Option.bind_some, Option.bind_some, Spec.agm_coe_coe ha hb]
          by_cases heq : eqIEEE X Y = true
          · left
            simp only [heq, ↓reduceIte]
            obtain ⟨v, hXv, hYv⟩ := (eqIEEE_iff X Y).mp heq
            rw [hx] at hXv
            rw [hy] at hYv
            have hab : finiteVal true e' m' = finiteVal true e m :=
              EReal.coe_eq_coe_iff.mp (Option.some_injective _ (hYv.trans hXv.symm))
            rw [hab, AGM_self ha.le]
            exact setPrecRound_eq_roundVal hx p mode
          · simp only [heq]
            have hab : finiteVal true e m ≠ finiteVal true e' m' := fun h =>
              heq ((eqIEEE_iff X Y).mpr ⟨_, hx, by rw [hy, h]⟩)
            rcases eq_or_ne (zivLoop (agmApprox X Y) p mode (agmFuel p) (p + zivGuardBits))
              (nan, .eq) with hz | hz
            · right; exact hz
            · left
              exact zivLoop_eq_of_ne_nan p mode _ (AGM _ _) (fun w hw => by
                have : NeZero w := ⟨hw.ne'⟩
                exact agmApprox_spec hx hy ha hb hab w) _ _ (by unfold zivGuardBits; omega) hz

end Azurite.AzFloat
