/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.AgmWidth
import Azurite.AzFloat.Equiv.GammaConstantsEncl
import Azurite.AzFloat.Equiv.GammaWidth
import Azurite.AzFloat.Equiv.LnGammaCertificate

/-!
# Convergent enclosures

`LConv b x`: the enclosures `b w` of `x > 0` have relative widths that tend to `0` as the Ziv
level `w` grows.  The predicate is closed under the operations on enclosures at the working
precision `w + c` — each operation adds a multiple of `2^(−w−c)` to the relative width:

* `LConv.const`, `LConv.nat`, `LConv.pi`;
* `LConv.mul`, `LConv.div`, `LConv.add`, `LConv.half`, `LConv.sqrt`, `LConv.cbrt`;
* `LConv.agm` (the interval AGM, by `agm_bracket_width`), `LConv.agmRaw` (its two ends
  `bLo`, `aHi` without the guard of `Encl.agm`).

A convergent enclosure gives a convergent bracket of a Ziv loop (`BracketConv`), in the two
shapes in use: `LConv.lnGammaApproxOf_bracketConv` (the lower end lowered) and
`LConv.bracketConv` (the two ends rounded).  `LConv.ofA`, `LConv.toA` pass to absolute widths
and back.
-/

namespace Azurite.AzFloat

open Azurite.BZ Filter Topology

/-- The enclosures `b w` of `x` converge: their relative widths tend to `0`. -/
def LConv (b : ℕ → Encl) (x : ℝ) : Prop :=
  ∃ lam : ℕ → ℝ, Tendsto lam atTop (𝓝 0) ∧ ∀ᶠ w in atTop, 0 ≤ lam w ∧ LEncl (b w) x (lam w)

variable {a b : ℕ → Encl} {x y : ℝ}

theorem LConv.pos (h : LConv a x) : 0 < x := by
  obtain ⟨lam, -, hev⟩ := h
  obtain ⟨w, -, hw⟩ := hev.exists
  exact hw.pos

theorem tendsto_half_pow_add (c : ℕ) :
    Tendsto (fun w : ℕ => (1 / 2 : ℝ) ^ (w + c)) atTop (𝓝 0) :=
  (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
    (tendsto_add_atTop_nat c)

theorem tendsto_const_mul_half_pow_add (k : ℝ) (c : ℕ) :
    Tendsto (fun w : ℕ => k * (1 / 2 : ℝ) ^ (w + c)) atTop (𝓝 0) := by
  simpa using (tendsto_half_pow_add c).const_mul k

theorem LConv.const {t : AzFloat} {tv : ℝ} (ht : t.toVal = some (tv : EReal)) (h0 : 0 < tv) :
    LConv (fun _ => Encl.exact t) tv :=
  ⟨fun _ => 0, tendsto_const_nhds, Eventually.of_forall fun _ => ⟨le_rfl, LEncl.exact ht h0⟩⟩

theorem LConv.nat {n : ℕ} (hn : 0 < n) : LConv (fun _ => Encl.nat n) n :=
  LConv.const (toVal_ofAzNat_ofNat n) (by exact_mod_cast hn)

theorem LConv.pi (c : ℕ) : LConv (fun w => Encl.pi (w + c)) Real.pi := by
  refine ⟨fun w => 3 * (1 / 2 : ℝ) ^ (w + c), tendsto_const_mul_half_pow_add 3 c, ?_⟩
  filter_upwards [eventually_ge_atTop 64] with w hw
  exact ⟨by positivity, LEncl.pi (by omega)⟩

theorem LConv.mul (c : ℕ) (ha : LConv a x) (hb : LConv b y) :
    LConv (fun w => Encl.mul (w + c) (a w) (b w)) (x * y) := by
  obtain ⟨l₁, t₁, e₁⟩ := ha
  obtain ⟨l₂, t₂, e₂⟩ := hb
  refine ⟨fun w => l₁ w + l₂ w + 6 * (1 / 2 : ℝ) ^ (w + c), ?_, ?_⟩
  · simpa using (t₁.add t₂).add (tendsto_const_mul_half_pow_add 6 c)
  · filter_upwards [e₁, e₂, eventually_ge_atTop 3] with w h1 h2 hw
    have : NeZero (w + c) := ⟨by omega⟩
    exact ⟨add_nonneg (add_nonneg h1.1 h2.1) (by positivity),
      h1.2.mul (half_pow_le_eighth (by omega)) h2.2⟩

theorem LConv.div (c : ℕ) (ha : LConv a x) (hb : LConv b y) :
    LConv (fun w => Encl.div (w + c) (a w) (b w)) (x / y) := by
  obtain ⟨l₁, t₁, e₁⟩ := ha
  obtain ⟨l₂, t₂, e₂⟩ := hb
  refine ⟨fun w => l₁ w + l₂ w + 6 * (1 / 2 : ℝ) ^ (w + c), ?_, ?_⟩
  · simpa using (t₁.add t₂).add (tendsto_const_mul_half_pow_add 6 c)
  · filter_upwards [e₁, e₂, eventually_ge_atTop 3] with w h1 h2 hw
    have : NeZero (w + c) := ⟨by omega⟩
    exact ⟨add_nonneg (add_nonneg h1.1 h2.1) (by positivity),
      h1.2.div (half_pow_le_eighth (by omega)) h2.2⟩

theorem LConv.add (c : ℕ) (ha : LConv a x) (hb : LConv b y) :
    LConv (fun w => Encl.add (w + c) (a w) (b w)) (x + y) := by
  obtain ⟨l₁, t₁, e₁⟩ := ha
  obtain ⟨l₂, t₂, e₂⟩ := hb
  refine ⟨fun w => max (l₁ w) (l₂ w) + 6 * (1 / 2 : ℝ) ^ (w + c), ?_, ?_⟩
  · simpa using (t₁.max t₂).add (tendsto_const_mul_half_pow_add 6 c)
  · filter_upwards [e₁, e₂, eventually_ge_atTop 3] with w h1 h2 hw
    have : NeZero (w + c) := ⟨by omega⟩
    exact ⟨add_nonneg (le_max_of_le_left h1.1) (by positivity),
      LEncl.add' (half_pow_le_eighth (by omega)) (h1.2.mono (le_max_left _ _))
        (h2.2.mono (le_max_right _ _))⟩

theorem LEncl.half {A : Encl} {lam : ℝ} (h : LEncl A x lam) : LEncl (Encl.half A) (x / 2) lam := by
  obtain ⟨l, u, hl, hu, p, a₁, b₁, c₁⟩ := h
  have e1 := toVal_shiftLeft_of_toVal hl (AzInt.ofInt (-1))
  have e2 := toVal_shiftLeft_of_toVal hu (AzInt.ofInt (-1))
  rw [AzInt.toInt_ofInt, zpow_neg_one, ← div_eq_mul_inv] at e1 e2
  exact ⟨l / 2, u / 2, e1, e2, by linarith, by linarith, by linarith, by linarith⟩

theorem LConv.half (ha : LConv a x) : LConv (fun w => Encl.half (a w)) (x / 2) := by
  obtain ⟨l₁, t₁, e₁⟩ := ha
  exact ⟨l₁, t₁, e₁.mono fun w h => ⟨h.1, h.2.half⟩⟩

theorem LConv.sqrt (c : ℕ) (ha : LConv a x) :
    LConv (fun w => Encl.sqrt (w + c) (a w)) (Real.sqrt x) := by
  obtain ⟨l₁, t₁, e₁⟩ := ha
  refine ⟨fun w => l₁ w / 2 + 6 * (1 / 2 : ℝ) ^ (w + c), ?_, ?_⟩
  · simpa using (t₁.div_const 2).add (tendsto_const_mul_half_pow_add 6 c)
  · filter_upwards [e₁, eventually_ge_atTop 3] with w h1 hw
    have : NeZero (w + c) := ⟨by omega⟩
    exact ⟨add_nonneg (by linarith [h1.1]) (by positivity),
      lencl_sqrt (half_pow_le_eighth (by omega)) h1.2⟩

/-- The cube root divides the relative width by three. -/
theorem lencl_cbrt {lo hi : AzFloat} {lam : ℝ} {w : ℕ} [NeZero w]
    (hu : (1 / 2 : ℝ) ^ w ≤ 1 / 8) (h : LEncl (lo, hi) x lam) :
    LEncl ((cbrtPrecRound lo w .Floor).1, (cbrtPrecRound hi w .Ceiling).1) (realCbrt x)
      (lam / 3 + 6 * (1 / 2 : ℝ) ^ w) := by
  obtain ⟨l, h', hl, hh, p, a₁, b₁, c₁⟩ := h
  have hl' : lo.toVal = some (l : EReal) := hl
  have hh' : hi.toVal = some (h' : EReal) := hh
  have hh0 : 0 ≤ h' := by linarith
  obtain ⟨r, hr, hfr⟩ : ∃ r : ℝ, (cbrtPrecRound lo w .Floor).1.toVal = some (r : EReal) ∧
      FloorOf w (realCbrt l) r := by
    rw [cbrtPrecRound_eq_liftVal, liftVal, hl', Option.bind_some, Spec.cbrt_coe]
    exact roundVal_floor_err w (realCbrt_nonneg p.le)
  obtain ⟨s, hs, hcs⟩ : ∃ s : ℝ, (cbrtPrecRound hi w .Ceiling).1.toVal = some (s : EReal) ∧
      CeilOf w (realCbrt h') s := by
    rw [cbrtPrecRound_eq_liftVal, liftVal, hh', Option.bind_some, Spec.cbrt_coe]
    exact roundVal_ceiling_err w (realCbrt_nonneg hh0)
  have hcb : realCbrt h' ≤ realCbrt l * Real.exp (lam / 3) := by
    calc realCbrt h' ≤ realCbrt (l * Real.exp lam) := realCbrt_le_realCbrt hh0 c₁
      _ = realCbrt l * Real.exp (lam / 3) := by
          refine realCbrt_eq_of_pow_three
            (mul_nonneg (realCbrt_nonneg p.le) (Real.exp_pos _).le) ?_
          rw [mul_pow, realCbrt_pow_three, ← Real.exp_nat_mul]
          congr 2
          push_cast
          ring
  obtain ⟨hr0, hrs⟩ := round_pos_combine (lam := lam / 3) (realCbrt_pos p) hcb
    (by positivity) hu hfr.ge hcs.le
  exact ⟨r, s, hr, hs, hr0, hfr.le.trans (realCbrt_le_realCbrt p.le a₁),
    (realCbrt_le_realCbrt (p.le.trans a₁) b₁).trans hcs.ge, hrs⟩

theorem LConv.cbrt (c : ℕ) (ha : LConv a x) :
    LConv (fun w => Encl.cbrt (w + c) (a w)) (realCbrt x) := by
  obtain ⟨l₁, t₁, e₁⟩ := ha
  refine ⟨fun w => l₁ w / 3 + 6 * (1 / 2 : ℝ) ^ (w + c), ?_, ?_⟩
  · simpa using (t₁.div_const 3).add (tendsto_const_mul_half_pow_add 6 c)
  · filter_upwards [e₁, eventually_ge_atTop 3] with w h1 hw
    have : NeZero (w + c) := ⟨by omega⟩
    exact ⟨add_nonneg (by linarith [h1.1]) (by positivity),
      lencl_cbrt (half_pow_le_eighth (by omega)) h1.2⟩

/-! ### Absolute widths -/

theorem LConv.toA (h : LConv a x) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ w in atTop, AEncl (a w) x (ε w) := by
  obtain ⟨lam, t, e⟩ := h
  refine ⟨fun w => 2 * x * lam w, by simpa using t.const_mul (2 * x), ?_⟩
  filter_upwards [e, t.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with w h1 h2
  obtain ⟨l, u, e1, e2, -, e3, e4, e5⟩ := h1.2.toA h1.1 h2
  exact ⟨l, u, e1, e2, e3, e4, e5⟩

theorem LConv.ofA (hx : 0 < x) {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (h : ∀ᶠ w in atTop, AEncl (a w) x (ε w)) : LConv a x := by
  refine ⟨fun w => 2 * ε w / x, by simpa using (hε.const_mul 2).div_const x, ?_⟩
  filter_upwards [h, hε.eventually (ge_mem_nhds (by positivity : 0 < x / 2))] with w h1 h2
  have hε0 : 0 ≤ ε w := by
    obtain ⟨l, u, -, -, a1, a2, a3⟩ := h1
    linarith
  exact ⟨by positivity, LEncl.ofA h1 (by linarith) hx⟩

/-! ### The interval AGM -/

/-- **The two ends `bLo`, `aHi` of the interval AGM converge.** -/
theorem LConv.agmRaw (c : ℕ) (ha : LConv a x) (hb : LConv b y) :
    LConv (fun w =>
      ((agmIter (w + c) (w + c + 4)
          (agmStep (w + c) ⟨(a w).1, (a w).2, (b w).1, (b w).2⟩)).bLo,
        (agmIter (w + c) (w + c + 4)
          (agmStep (w + c) ⟨(a w).1, (a w).2, (b w).1, (b w).2⟩)).aHi)) (AGM x y) := by
  have hx := ha.pos
  have hy := hb.pos
  have hAGM : 0 < AGM x y := lt_of_lt_of_le (lt_min hx hy) (min_le_AGM hx hy)
  obtain ⟨l₁, t₁, e₁⟩ := ha
  obtain ⟨l₂, t₂, e₂⟩ := hb
  have hl0 : Tendsto (fun w => max (l₁ w) (l₂ w)) atTop (𝓝 0) := by simpa using t₁.max t₂
  have hl0' : Tendsto (fun W => max (l₁ (W - c)) (l₂ (W - c))) atTop (𝓝 0) :=
    hl0.comp (tendsto_sub_atTop_nat c)
  have hε : Tendsto (fun w : ℕ => agmEps (max x y)
      (max (l₁ w) (l₂ w) + 9 * (1 / 2 : ℝ) ^ (w + c) * ((w + c + 4 + 1 : ℕ) : ℝ))
      (w + c + 4) (w + c)) atTop (𝓝 0) := by
    have h := (tendsto_agmEps (max x y) 4 hl0').comp (tendsto_add_atTop_nat c)
    refine h.congr fun w => ?_
    simp only [Function.comp_apply, Nat.add_sub_cancel]
  refine LConv.ofA hAGM hε ?_
  filter_upwards [e₁, e₂, eventually_ge_atTop 3] with w h1 h2 hw
  have : NeZero (w + c) := ⟨by omega⟩
  have hrel : RelEnc x y 0 (max (l₁ w) (l₂ w)) ⟨(a w).1, (a w).2, (b w).1, (b w).2⟩ :=
    ⟨h1.2.mono (le_max_left _ _), h2.2.mono (le_max_right _ _)⟩
  obtain ⟨bl, ah, hbl, hah, -, hle, hge, hwid⟩ := agm_bracket_width hx hy
    (half_pow_le_eighth (by omega : 3 ≤ w + c)) (le_max_of_le_left h1.1) hrel (w + c + 4)
  exact ⟨bl, ah, hbl, hah, hle, hge, hwid⟩

/-- **The interval AGM of two convergent enclosures converges.** -/
theorem LConv.agm (c : ℕ) (ha : LConv a x) (hb : LConv b y) :
    LConv (fun w => Encl.agm (w + c) (a w) (b w)) (AGM x y) := by
  obtain ⟨lam, t, e⟩ := LConv.agmRaw c ha hb
  refine ⟨lam, t, e.mono fun w h => ⟨h.1, ?_⟩⟩
  obtain ⟨l, u, hl, hu, hl0, -⟩ := h.2
  have hpos : lt zero (agmIter (w + c) (w + c + 4)
      (agmStep (w + c) ⟨(a w).1, (a w).2, (b w).1, (b w).2⟩)).bLo = true :=
    (lt_eq_true_iff toVal_zero' hl).mpr hl0
  have hEq : Encl.agm (w + c) (a w) (b w)
      = ((agmIter (w + c) (w + c + 4)
          (agmStep (w + c) ⟨(a w).1, (a w).2, (b w).1, (b w).2⟩)).bLo,
        (agmIter (w + c) (w + c + 4)
          (agmStep (w + c) ⟨(a w).1, (a w).2, (b w).1, (b w).2⟩)).aHi) := by
    unfold Encl.agm
    dsimp only
    rw [ite_eq_left hpos]
  show LEncl (Encl.agm (w + c) (a w) (b w)) (AGM x y) (lam w)
  rw [hEq]
  exact h.2

/-! ### Brackets of Ziv loops -/

/-- A convergent enclosure, as a bracket with the lower end lowered (`lnGammaApproxOf`). -/
theorem LConv.lnGammaApproxOf_bracketConv (h : LConv a x) :
    BracketConv (fun w => lnGammaApproxOf (a w) w) x := by
  obtain ⟨ε, hε, hev⟩ := h.toA
  exact Azurite.AzFloat.lnGammaApproxOf_bracketConv hε hev

/-- Enclosures whose widths tend to `0`, as brackets with the two ends rounded. -/
theorem bracketConv_of_AEncl {v : ℝ} {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (h : ∀ᶠ w in atTop, AEncl (a w) v (ε w)) :
    BracketConv (fun w => (fun p mode => setPrecRound (a w).1 p mode,
      fun p mode => setPrecRound (a w).2 p mode)) v := by
  obtain ⟨W₀, hW₀⟩ := eventually_atTop.mp h
  refine ⟨ε, hε, W₀, fun w hw => ?_⟩
  obtain ⟨l, u, hl, hu, h1, h2, h3⟩ := hW₀ w hw
  refine ⟨l, u, ?_, ?_, h1, h2, h3⟩
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hl)
    rw [fval_of_toVal_coe hl] at hR
    exact hR
  · have hR := rounds_setPrecRound (isFinite_of_toVal_coe hu)
    rw [fval_of_toVal_coe hu] at hR
    exact hR

/-- A convergent enclosure, as a bracket with the two ends rounded. -/
theorem LConv.bracketConv (h : LConv a x) :
    BracketConv (fun w => (fun p mode => setPrecRound (a w).1 p mode,
      fun p mode => setPrecRound (a w).2 p mode)) x := by
  obtain ⟨ε, hε, hev⟩ := h.toA
  exact bracketConv_of_AEncl hε hev

end Azurite.AzFloat
