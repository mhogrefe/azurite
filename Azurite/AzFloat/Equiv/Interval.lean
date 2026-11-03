/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Interval
import Azurite.AzFloat.Equiv.ExpApprox
import Azurite.AzFloat.Equiv.PiBracket
import Azurite.AzFloat.Equiv.Sum
import Azurite.AzRat.Equiv.LogBase2

/-!
# Soundness of interval evaluation

`IsEncl a x` says that the ends of `a` have real values `l ≤ x ≤ h`; `IsEncl0` adds `0 ≤ l`
and `IsEnclPos` adds `0 < l`. Every `Encl` operation preserves enclosures (with the sign
conditions that `×` and `/` need), from the directed-rounding lemmas of
`Equiv/DirectedRounding.lean`; `π` and `exp` come from `piBracket_spec` and
`expBracketAt_spec`. `IsEncl.bounds` reads real bounds off the kernel-computed `valData` of
the two ends.
-/

namespace Azurite.AzFloat

open RoundingTarget

/-- `a` encloses `x`: its ends have real values `l ≤ x ≤ h`. -/
def IsEncl (a : Encl) (x : ℝ) : Prop :=
  ∃ l h : ℝ, a.1.toVal = some (l : EReal) ∧ a.2.toVal = some (h : EReal) ∧ l ≤ x ∧ x ≤ h

/-- `a` encloses `x` with a nonnegative lower end. -/
def IsEncl0 (a : Encl) (x : ℝ) : Prop :=
  ∃ l h : ℝ, a.1.toVal = some (l : EReal) ∧ a.2.toVal = some (h : EReal) ∧ 0 ≤ l ∧ l ≤ x ∧ x ≤ h

/-- `a` encloses `x` with a positive lower end. -/
def IsEnclPos (a : Encl) (x : ℝ) : Prop :=
  ∃ l h : ℝ, a.1.toVal = some (l : EReal) ∧ a.2.toVal = some (h : EReal) ∧ 0 < l ∧ l ≤ x ∧ x ≤ h

theorem IsEnclPos.encloses0 {a : Encl} {x : ℝ} (h : IsEnclPos a x) : IsEncl0 a x := by
  obtain ⟨l, u, hl, hu, h0, h1, h2⟩ := h
  exact ⟨l, u, hl, hu, h0.le, h1, h2⟩

theorem IsEncl0.encloses {a : Encl} {x : ℝ} (h : IsEncl0 a x) : IsEncl a x := by
  obtain ⟨l, u, hl, hu, -, h1, h2⟩ := h
  exact ⟨l, u, hl, hu, h1, h2⟩

/-- A directed rounding down of a positive number at precision `w ≥ 2` is positive. -/
theorem FloorOf.pos {w : ℕ} {x r : ℝ} (h : FloorOf w x r) (hw : 2 ≤ w) (hx : 0 < x) : 0 < r := by
  have hp : (1 / 2 : ℝ) ^ w ≤ (1 / 2) ^ 2 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hw
  have := h.ge
  nlinarith

/-! ### Generic directed rounding of sums and differences -/

variable {u v : AzFloat} {uv vv : ℝ}

theorem addFloor_le (hu : u.toVal = some (uv : EReal)) (hv : v.toVal = some (vv : EReal))
    (w : ℕ) [NeZero w] :
    ∃ r : ℝ, (addPrecRound u v w .Floor).1.toVal = some (r : EReal) ∧ r ≤ uv + vv := by
  rw [addPrecRound_eq_liftVal₂, liftVal₂, hu, hv, Option.bind_some, Option.bind_some,
    Spec.add_coe_coe]
  obtain ⟨r, hr, hle, -⟩ := roundVal_floor_spec w (uv + vv)
  exact ⟨r, hr, hle⟩

theorem addCeiling_ge (hu : u.toVal = some (uv : EReal)) (hv : v.toVal = some (vv : EReal))
    (w : ℕ) [NeZero w] :
    ∃ r : ℝ, (addPrecRound u v w .Ceiling).1.toVal = some (r : EReal) ∧ uv + vv ≤ r := by
  rw [addPrecRound_eq_liftVal₂, liftVal₂, hu, hv, Option.bind_some, Option.bind_some,
    Spec.add_coe_coe]
  exact roundVal_ceiling_spec w (uv + vv)

theorem subCeiling_ge (hu : u.toVal = some (uv : EReal)) (hv : v.toVal = some (vv : EReal))
    (w : ℕ) [NeZero w] :
    ∃ r : ℝ, (subPrecRound u v w .Ceiling).1.toVal = some (r : EReal) ∧ uv - vv ≤ r := by
  rw [subPrecRound_eq_liftVal₂, liftVal₂, hu, hv, Option.bind_some, Option.bind_some,
    Spec.sub_coe_coe]
  exact roundVal_ceiling_spec w (uv - vv)

/-! ### The operations -/

variable {a b e : Encl} {x y : ℝ} {w : ℕ}

open Encl

theorem enclosesPos_nat {n : ℕ} (hn : 0 < n) : IsEnclPos (nat n) n := by
  have h := toVal_ofAzNat (AzNat.ofNat n)
  rw [AzNat.toNat_ofNat] at h
  exact ⟨n, n, h, h, by exact_mod_cast hn, le_rfl, le_rfl⟩

theorem enclosesPos_one : IsEnclPos (exact one) 1 :=
  ⟨1, 1, toVal_one', toVal_one', one_pos, le_rfl, le_rfl⟩

theorem IsEncl.add [NeZero w] (ha : IsEncl a x) (hb : IsEncl b y) :
    IsEncl (add w a b) (x + y) := by
  obtain ⟨la, ha', hla, hha, h1, h2⟩ := ha
  obtain ⟨lb, hb', hlb, hhb, h3, h4⟩ := hb
  obtain ⟨r, hr, hr1⟩ := addFloor_le hla hlb w
  obtain ⟨s, hs, hs1⟩ := addCeiling_ge hha hhb w
  exact ⟨r, s, hr, hs, by linarith, by linarith⟩

theorem IsEncl.sub [NeZero w] (ha : IsEncl a x) (hb : IsEncl b y) :
    IsEncl (sub w a b) (x - y) := by
  obtain ⟨la, ha', hla, hha, h1, h2⟩ := ha
  obtain ⟨lb, hb', hlb, hhb, h3, h4⟩ := hb
  obtain ⟨r, hr, hr1, -⟩ := subFloor_le hla hhb w
  obtain ⟨s, hs, hs1⟩ := subCeiling_ge hha hlb w
  exact ⟨r, s, hr, hs, by linarith, by linarith⟩

theorem IsEncl.subNonneg [NeZero w] (ha : IsEncl a x) (hb : IsEncl b y) (hxy : y ≤ x) :
    IsEncl0 (subNonneg w a b) (x - y) := by
  obtain ⟨la, ha', hla, hha, h1, h2⟩ := ha
  obtain ⟨lb, hb', hlb, hhb, h3, h4⟩ := hb
  obtain ⟨r, hr, hr1, -⟩ := subFloor_le hla hhb w
  obtain ⟨c, hc, hc0, hcle, -⟩ := clampNonneg_spec hr
  obtain ⟨s, hs, hs1⟩ := subCeiling_ge hha hlb w
  refine ⟨c, s, hc, hs, hc0, hcle.trans (max_le (by linarith) (by linarith)), by linarith⟩

theorem IsEncl.widen [NeZero w] (ha : IsEncl a x) (he : IsEncl0 e y) {z : ℝ}
    (hz : |z - x| ≤ y) : IsEncl (widen w a e) z := by
  obtain ⟨la, ha', hla, hha, h1, h2⟩ := ha
  obtain ⟨le, he', hle, hhe, -, h3, h4⟩ := he
  obtain ⟨r, hr, hr1, -⟩ := subFloor_le hla hhe w
  obtain ⟨s, hs, hs1⟩ := addCeiling_ge hha hhe w
  rw [abs_le] at hz
  exact ⟨r, s, hr, hs, by linarith, by linarith⟩

theorem IsEncl.neg (ha : IsEncl a x) : IsEncl (Encl.neg a) (-x) := by
  obtain ⟨la, ha', hla, hha, h1, h2⟩ := ha
  refine ⟨-ha', -la, ?_, ?_, by linarith, by linarith⟩
  · show (-a.2).toVal = _
    rw [toVal_neg, hha]; rfl
  · show (-a.1).toVal = _
    rw [toVal_neg, hla]; rfl

theorem IsEncl0.add [NeZero w] (ha : IsEncl0 a x) (hb : IsEncl0 b y) :
    IsEncl0 (add w a b) (x + y) := by
  obtain ⟨la, ha', hla, hha, h0, h1, h2⟩ := ha
  obtain ⟨lb, hb', hlb, hhb, h0', h3, h4⟩ := hb
  obtain ⟨r, hr, hr1⟩ := addFloor_err hla hlb w (by linarith)
  obtain ⟨s, hs, hs1⟩ := addCeiling_err hha hhb w (by linarith)
  exact ⟨r, s, hr, hs, hr1.nonneg, hr1.le.trans (by linarith), by linarith [hs1.ge]⟩

theorem IsEnclPos.add [NeZero w] (hw : 2 ≤ w) (ha : IsEnclPos a x) (hb : IsEncl0 b y) :
    IsEnclPos (add w a b) (x + y) := by
  obtain ⟨la, ha', hla, hha, h0, h1, h2⟩ := ha
  obtain ⟨lb, hb', hlb, hhb, h0', h3, h4⟩ := hb
  obtain ⟨r, hr, hr1⟩ := addFloor_err hla hlb w (by linarith)
  obtain ⟨s, hs, hs1⟩ := addCeiling_err hha hhb w (by linarith)
  exact ⟨r, s, hr, hs, hr1.pos hw (by linarith), hr1.le.trans (by linarith), by linarith [hs1.ge]⟩

theorem IsEncl0.mul [NeZero w] (ha : IsEncl0 a x) (hb : IsEncl0 b y) :
    IsEncl0 (mul w a b) (x * y) := by
  obtain ⟨la, ha', hla, hha, h0, h1, h2⟩ := ha
  obtain ⟨lb, hb', hlb, hhb, h0', h3, h4⟩ := hb
  obtain ⟨r, hr, hr1⟩ := mulFloor_err hla hlb w (mul_nonneg h0 h0')
  obtain ⟨s, hs, hs1⟩ := mulCeiling_err hha hhb w (mul_nonneg (h0.trans (h1.trans h2))
    (h0'.trans (h3.trans h4)))
  exact ⟨r, s, hr, hs, hr1.nonneg, hr1.le.trans (mul_le_mul h1 h3 h0' (h0.trans h1)),
    (mul_le_mul h2 h4 (h0'.trans h3) (h0.trans (h1.trans h2))).trans hs1.ge⟩

theorem IsEnclPos.mul [NeZero w] (hw : 2 ≤ w) (ha : IsEnclPos a x) (hb : IsEnclPos b y) :
    IsEnclPos (mul w a b) (x * y) := by
  obtain ⟨la, ha', hla, hha, h0, h1, h2⟩ := ha
  obtain ⟨lb, hb', hlb, hhb, h0', h3, h4⟩ := hb
  obtain ⟨r, hr, hr1⟩ := mulFloor_err hla hlb w (mul_nonneg h0.le h0'.le)
  obtain ⟨s, hs, hs1⟩ := mulCeiling_err hha hhb w (mul_nonneg (h0.le.trans (h1.trans h2))
    (h0'.le.trans (h3.trans h4)))
  exact ⟨r, s, hr, hs, hr1.pos hw (mul_pos h0 h0'),
    hr1.le.trans (mul_le_mul h1 h3 h0'.le (h0.le.trans h1)),
    (mul_le_mul h2 h4 (h0'.le.trans h3) (h0.le.trans (h1.trans h2))).trans hs1.ge⟩

theorem IsEncl0.div [NeZero w] (ha : IsEncl0 a x) (hb : IsEnclPos b y) :
    IsEncl0 (div w a b) (x / y) := by
  obtain ⟨la, ha', hla, hha, h0, h1, h2⟩ := ha
  obtain ⟨lb, hb', hlb, hhb, h0', h3, h4⟩ := hb
  have hy : 0 < y := h0'.trans_le h3
  obtain ⟨r, hr, hr1⟩ := divFloor_err hla hhb (hy.trans_le h4) h0 w
  obtain ⟨s, hs, hs1⟩ := divCeiling_err hha hlb h0' (h0.trans (h1.trans h2)) w
  refine ⟨r, s, hr, hs, hr1.nonneg, hr1.le.trans ?_, le_trans ?_ hs1.ge⟩
  · exact div_le_div₀ (h0.trans h1) h1 hy h4
  · exact div_le_div₀ (h0.trans (h1.trans h2)) h2 h0' h3

theorem IsEnclPos.div [NeZero w] (hw : 2 ≤ w) (ha : IsEnclPos a x) (hb : IsEnclPos b y) :
    IsEnclPos (div w a b) (x / y) := by
  obtain ⟨r, s, hr, hs, -, h1, h2⟩ := IsEncl0.div (w := w) ha.encloses0 hb
  obtain ⟨la, ha', hla, hha, h0, -, -⟩ := ha
  obtain ⟨lb, hb', hlb, hhb, h0', h3, h4⟩ := hb
  have hy : 0 < hb' := h0'.trans_le (h3.trans h4)
  obtain ⟨r', hr', hr1⟩ := divFloor_err hla hhb hy h0.le w
  have : r = r' := by
    change (divPrecRound a.1 b.2 w .Floor).1.toVal = _ at hr
    rw [hr'] at hr
    exact EReal.coe_injective (Option.some_injective _ hr).symm
  exact ⟨r, s, hr, hs, this ▸ hr1.pos hw (div_pos h0 hy), h1, h2⟩

theorem IsEnclPos.pow [NeZero w] (hw : 2 ≤ w) (ha : IsEnclPos a x) :
    ∀ n : ℕ, IsEnclPos (pow w a n) (x ^ n)
  | 0 => by rw [pow_zero]; exact enclosesPos_one
  | n + 1 => by rw [pow_succ]; exact (IsEnclPos.pow hw ha n).mul hw ha

theorem enclosesPos_pi (hw : 64 ≤ w) : IsEnclPos (Encl.pi w) Real.pi := by
  obtain ⟨lv, hv, hl, hh, -, hlt, hle, hwid⟩ := piBracket_spec hw
  have := piEps_le hw
  exact ⟨lv, hv, hl, hh, by linarith [Real.pi_gt_three], hlt.le, hle⟩

theorem encloses0_exp {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (hw : 64 ≤ w) :
    IsEncl0 (Encl.exp w x) (Real.exp xv) := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, -⟩ := expBracketAt_spec hx hw
  obtain ⟨c, hc, hc0, hcle, -⟩ := clampNonneg_spec hlo
  exact ⟨c, hi, hc, hhi, hc0, hcle.trans (max_le h1 (Real.exp_pos _).le), h2⟩

/-! ### Reading off the bounds -/

/-- The real number with sign `s` (`true` = nonnegative), numerator `n` and denominator `d`. -/
noncomputable def signedVal (s : Bool) (n d : ℕ) : ℝ := (if s then (n : ℝ) else -n) / d

theorem toVal_of_valData {x : AzFloat} {s : Bool} {n d : ℕ} (h : valData x = some (s, n, d)) :
    x.toVal = some ((signedVal s n d : ℝ) : EReal) := by
  unfold valData at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨q, hq, hqd⟩ := h
  simp only [Prod.mk.injEq] at hqd
  obtain ⟨hs, hn, hd⟩ := hqd
  rw [toVal_of_toAzRat? _ _ hq, AzRat.toRat_cast_eq, hs, hn, hd, signedVal]
  cases s <;> simp

/-- Real bounds from the kernel-computed data of the two ends. -/
theorem IsEncl.bounds {a : Encl} {x : ℝ} (h : IsEncl a x) {s₁ s₂ : Bool} {n₁ d₁ n₂ d₂ : ℕ}
    (h₁ : valData a.1 = some (s₁, n₁, d₁)) (h₂ : valData a.2 = some (s₂, n₂, d₂)) :
    signedVal s₁ n₁ d₁ ≤ x ∧ x ≤ signedVal s₂ n₂ d₂ := by
  obtain ⟨l, u, hl, hu, h1, h2⟩ := h
  rw [toVal_of_valData h₁] at hl
  rw [toVal_of_valData h₂] at hu
  have e1 := EReal.coe_injective (Option.some_injective _ hl)
  have e2 := EReal.coe_injective (Option.some_injective _ hu)
  exact ⟨e1 ▸ h1, e2 ▸ h2⟩

end Azurite.AzFloat
