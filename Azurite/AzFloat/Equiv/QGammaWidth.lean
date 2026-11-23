/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.QGammaBracket
import Azurite.AzFloat.Equiv.BarnesGWidth

/-!
# Equivalence: the bracket of the `q`-gamma function converges

**`qGammaCoreOf_coreConv`**: off the poles the core of `AzFloat/QGammaBracket.lean` answers at
every large level, with a width that tends to `0`.  In the calculus of `Equiv/EnclGeom.lean`
(geometrically small widths at a level-dependent working precision):

* additions to the calculus: `PB.of_eventually_le`, `AW.neg`, `AW.toLW_of_pos`, `LW.congr'`,
  `AW.of_level`;
* `exists_pos_le_abs_one_sub_rpow`: off the poles the factors `|1 − p^(x+i)|` are bounded
  below, uniformly in `i`;
* `qProdLoop_lencl`: the relative widths of the loop — each step adds the width of `p`, of
  the rounding and of one factor, whose cancellation is controlled by that lower bound;
* the number of factors `qgK` is polynomially bounded and at least `0.7 (w + 64)/ln(1/p)`
  (`qgK_bounds`), so that `p^K` is geometrically small;
* `qgL_aw`: the enclosure of `ln |Γ_q(x)|` has a geometrically small width.
-/

namespace Azurite.AzFloat

open Filter Topology Finset DLMF

/-! ### Additions to the calculus -/

theorem PB.of_eventually_le {f g : ℕ → ℝ} (hf : PB f) (h : ∀ᶠ w in atTop, |g w| ≤ |f w|) :
    PB g := by
  obtain ⟨C, k, hC⟩ := hf
  obtain ⟨W, hW⟩ := eventually_atTop.mp h
  refine ⟨|C| + ∑ i ∈ range W, |g i|, k, fun w => ?_⟩
  have hw0 : (0 : ℝ) ≤ (w : ℝ) := Nat.cast_nonneg w
  have hpow : (1 : ℝ) ≤ ((w : ℝ) + 1) ^ k := one_le_pow₀ (by linarith)
  have hS : 0 ≤ ∑ i ∈ range W, |g i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h1 := mul_le_mul_of_nonneg_left hpow hS
  have h2 := mul_nonneg (abs_nonneg C) (by positivity : (0 : ℝ) ≤ ((w : ℝ) + 1) ^ k)
  rw [add_mul]
  rcases lt_or_ge w W with hlt | hge
  · have : |g w| ≤ ∑ i ∈ range W, |g i| :=
      Finset.single_le_sum (f := fun i => |g i|) (fun i _ => abs_nonneg (g i))
        (Finset.mem_range.mpr hlt)
    linarith
  · have h3 := (hW w hge).trans (hC w)
    have h4 : C * ((w : ℝ) + 1) ^ k ≤ |C| * ((w : ℝ) + 1) ^ k :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    linarith

theorem AW.neg {a : ℕ → Encl} {x : ℕ → ℝ} (h : AW a x) :
    AW (fun w => Encl.neg (a w)) fun w => -x w := by
  obtain ⟨hx, ε, g, e⟩ := h
  exact ⟨hx.neg, ε, g, e.mono fun w hw => hw.neg⟩

/-- Enclosures of values bounded below by a positive constant: absolute to relative widths. -/
theorem AW.toLW_of_pos {a : ℕ → Encl} {x : ℕ → ℝ} (h : AW a x) {c : ℝ} (hc : 0 < c)
    (h1 : ∀ᶠ w in atTop, c ≤ x w) : LW a x := by
  obtain ⟨-, ε, g, e⟩ := h
  refine ⟨fun w => 2 * ε w / x w, ?_, ?_⟩
  · refine (g.const_mul (2 / c)).of_le ?_
    filter_upwards [h1] with w hw
    have hx0 : 0 < x w := lt_of_lt_of_le hc hw
    rw [abs_div, abs_mul, abs_mul, abs_of_pos hx0, abs_of_pos (by positivity : (0 : ℝ) < 2 / c),
      abs_two, div_le_iff₀ hx0]
    have e2 : 2 * |ε w| = 2 / c * |ε w| * c := by field_simp
    rw [e2]
    exact mul_le_mul_of_nonneg_left hw (by positivity)
  · filter_upwards [e, h1, g.eventually_le (by positivity : (0 : ℝ) < c / 2)] with w he hw hs
    have hε0 := he.width_nonneg
    have hε : ε w ≤ c / 2 := (le_abs_self _).trans hs
    have hx0 : 0 < x w := lt_of_lt_of_le hc hw
    exact ⟨by positivity, LEncl.ofA he (by linarith) hx0⟩

theorem LW.congr' {a : ℕ → Encl} {x y : ℕ → ℝ} (h : LW a x)
    (hxy : ∀ᶠ w in atTop, x w = y w) : LW a y := by
  obtain ⟨lam, g, e⟩ := h
  refine ⟨lam, g, ?_⟩
  filter_upwards [e, hxy] with w h1 h2
  rw [← h2]
  exact h1

/-- Enclosures of a constant of width `C · 2^(−V)` at the working precision. -/
theorem AW.of_level {V : ℕ → ℕ} (hV : ∀ w, w + 64 ≤ V w) {a : ℕ → Encl} {v C : ℝ}
    (h : ∀ V, 64 ≤ V → AEncl (a V) v (C * (1 / 2 : ℝ) ^ V)) :
    AW (fun w => a (V w)) fun _ => v :=
  ⟨PB.const v, fun w => C * (1 / 2 : ℝ) ^ V w, (GS.half_pow hV).const_mul C,
    Eventually.of_forall fun w => h _ (by have := hV w; omega)⟩

/-! ### The factors -/

/-- Off the poles the factors `1 − p^(x+i)` stay away from `0`. -/
theorem exists_pos_le_abs_one_sub_rpow {pv xv : ℝ} (hp0 : 0 < pv) (hp1 : pv < 1)
    (hnz : ∀ m : ℕ, xv ≠ -m) :
    ∃ m : ℝ, 0 < m ∧ m ≤ 1 - pv ∧ ∀ i : ℕ, m ≤ |1 - pv ^ (xv + i)| := by
  obtain ⟨d, hd0, -, hd⟩ := exists_pos_le_abs_add hnz
  have h1 : pv ^ d < 1 := Real.rpow_lt_one hp0.le hp1 hd0
  have h2 : 1 < pv ^ (-d) := Real.one_lt_rpow_of_pos_of_lt_one_of_neg hp0 hp1 (by linarith)
  refine ⟨min (1 - pv) (min (1 - pv ^ d) (pv ^ (-d) - 1)),
    lt_min (by linarith) (lt_min (by linarith) (by linarith)), min_le_left _ _, fun i => ?_⟩
  have hi := hd i
  rcases le_or_gt 0 (xv + i) with hy | hy
  · rw [abs_of_nonneg hy] at hi
    have h3 : pv ^ (xv + i) ≤ pv ^ d := Real.rpow_le_rpow_of_exponent_ge hp0 hp1.le hi
    rw [abs_of_nonneg (by linarith)]
    exact (min_le_right _ _).trans ((min_le_left _ _).trans (by linarith))
  · rw [abs_of_neg hy] at hi
    have h3 : pv ^ (-d) ≤ pv ^ (xv + i) :=
      Real.rpow_le_rpow_of_exponent_ge hp0 hp1.le (by linarith)
    rw [abs_of_nonpos (by linarith), neg_sub]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (by linarith))

/-- One factor `|1 − ρ|` of the loop: from a relative width `l ≤ Λ` of `ρ ≤ B` to the relative
width `Φ = 2 (2 B Λ + 4 (2 B + 1) u)/m` when `|1 − ρ| ≥ m`. -/
theorem qFactor_lencl {V : ℕ} [NeZero V] {r : Encl} {ρ l Λ B m : ℝ} (hr : LEncl r ρ l)
    (hl0 : 0 ≤ l) (hlΛ : l ≤ Λ) (hΛ : Λ ≤ 1 / 2) (hρB : ρ ≤ B) (hB : 1 ≤ B) (hm : 0 < m)
    (hmρ : m ≤ |1 - ρ|)
    (hS : 2 * (2 * B * Λ + 4 * (2 * B + 1) * (1 / 2 : ℝ) ^ V) ≤ m) :
    ∃ (σ : Bool) (f : Encl), fracOfEncl (Encl.sub V (Encl.exact one) r) = some (σ, f) ∧
      LEncl f |1 - ρ| (2 * (2 * B * Λ + 4 * (2 * B + 1) * (1 / 2 : ℝ) ^ V) / m) := by
  have hρ0 : 0 < ρ := hr.pos
  have hu0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ V := by positivity
  have hrA : AEncl r ρ (2 * B * Λ) := ((hr.toA hl0 (hlΛ.trans hΛ)).toA).mono (by
    have h1 : ρ * l ≤ B * Λ := mul_le_mul hρB hlΛ hl0 (by linarith)
    linarith)
  have hBΛ : 2 * B * Λ ≤ B := by nlinarith
  have habs : |1 - ρ| ≤ 1 + B := by
    rw [abs_le]
    constructor <;> linarith
  have hD := (AEncl.exact toVal_one').sub (w := V) hrA (B := 2 * B + 1) (by linarith)
  have hD' : AEncl (Encl.sub V (Encl.exact one) r) (1 - ρ)
      (2 * B * Λ + 4 * (2 * B + 1) * (1 / 2 : ℝ) ^ V) := hD.mono (by linarith)
  have hne : 1 - ρ ≠ 0 := fun h0 => by rw [h0, abs_zero] at hmρ; linarith
  obtain ⟨σ, f, hf, hfL⟩ := fracOfEncl_some hD' (hS.trans hmρ) hne
  refine ⟨σ, f, hf, hfL.mono ?_⟩
  have hnum : 0 ≤ 2 * (2 * B * Λ + 4 * (2 * B + 1) * (1 / 2 : ℝ) ^ V) := by
    have : 0 ≤ Λ := hl0.trans hlΛ
    positivity
  exact div_le_div_of_nonneg_left hnum hm hmρ

/-- **The relative widths of the loop.**  With `u = 2^(−V)`, `p` of relative width `lp`, the
powers of relative width at most `Λ` throughout, the factors `|1 − p^(x+i)| ≥ m` and
`p^(x+i) ≤ B`: `k` steps add `k (lp + 6u)` to the widths of the powers and `k (Φ + 6u)` to
those of the products, `Φ = 2 (2 B Λ + 4 (2 B + 1) u)/m`. -/
theorem qProdLoop_lencl {V : ℕ} [NeZero V] (hu : (1 / 2 : ℝ) ^ V ≤ 1 / 8) {P : Encl}
    {pv xv lp Λ B m : ℝ} (hp0 : 0 < pv) (hp1 : pv < 1) (hP : LEncl P pv lp) (hlp : 0 ≤ lp)
    (hΛ : Λ ≤ 1 / 2) (hB : 1 ≤ B) (hBx : ∀ i : ℕ, pv ^ (xv + i) ≤ B) (hm : 0 < m)
    (hm1 : m ≤ 1 - pv) (hmx : ∀ i : ℕ, m ≤ |1 - pv ^ (xv + i)|)
    (hS : 2 * (2 * B * Λ + 4 * (2 * B + 1) * (1 / 2 : ℝ) ^ V) ≤ m) :
    ∀ (k j : ℕ) (t r n d : Encl) (neg : Bool) (lt lr ln ld : ℝ),
      LEncl t (pv ^ (j + 1)) lt → LEncl r (pv ^ (xv + j)) lr →
      LEncl n (∏ i ∈ range j, (1 - pv ^ (i + 1))) ln →
      LEncl d (∏ i ∈ range j, |1 - pv ^ (xv + i)|) ld →
      0 ≤ lt → 0 ≤ lr →
      lt + k * (lp + 6 * (1 / 2 : ℝ) ^ V) ≤ Λ → lr + k * (lp + 6 * (1 / 2 : ℝ) ^ V) ≤ Λ →
      ∃ o, qProdLoop V P k t r n d neg = some o ∧
        LEncl o.2.1 (pv ^ (j + k + 1)) (lt + k * (lp + 6 * (1 / 2 : ℝ) ^ V)) ∧
        LEncl o.2.2.1 (pv ^ (xv + (j + k : ℕ))) (lr + k * (lp + 6 * (1 / 2 : ℝ) ^ V)) ∧
        LEncl o.2.2.2.1 (∏ i ∈ range (j + k), (1 - pv ^ (i + 1)))
          (ln + k * (2 * (2 * B * Λ + 4 * (2 * B + 1) * (1 / 2 : ℝ) ^ V) / m
            + 6 * (1 / 2 : ℝ) ^ V)) ∧
        LEncl o.2.2.2.2 (∏ i ∈ range (j + k), |1 - pv ^ (xv + i)|)
          (ld + k * (2 * (2 * B * Λ + 4 * (2 * B + 1) * (1 / 2 : ℝ) ^ V) / m
            + 6 * (1 / 2 : ℝ) ^ V))
  | 0, j, t, r, n, d, neg, lt, lr, ln, ld, ht, hr, hn, hd, _, _, _, _ => by
    refine ⟨(neg, t, r, n, d), rfl, ?_, ?_, ?_, ?_⟩
    · simpa using ht
    · simpa using hr
    · simpa using hn
    · simpa using hd
  | k + 1, j, t, r, n, d, neg, lt, lr, ln, ld, ht, hr, hn, hd, hlt0, hlr0, hltΛ, hlrΛ => by
    have hu0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ V := by positivity
    have hstep : 0 ≤ lp + 6 * (1 / 2 : ℝ) ^ V := by positivity
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hcast] at hltΛ hlrΛ
    have hkstep := mul_nonneg hk0 hstep
    have hpj : pv ^ (j + 1) < 1 := pow_lt_one₀ hp0.le hp1 (by omega)
    have hpj0 : 0 < pv ^ (j + 1) := by positivity
    have hpj' : pv ^ (j + 1) ≤ pv := by
      calc pv ^ (j + 1) ≤ pv ^ 1 := pow_le_pow_of_le_one hp0.le hp1.le (by omega)
        _ = pv := pow_one pv
    obtain ⟨σ', f, hf, hfL⟩ := qFactor_lencl (V := V) ht hlt0 (by nlinarith) hΛ
      (by linarith : pv ^ (j + 1) ≤ B) hB hm
      (by rw [abs_of_pos (by linarith)]; linarith) hS
    obtain ⟨σ, g, hg, hgL⟩ := qFactor_lencl (V := V) hr hlr0 (by nlinarith) hΛ (hBx j) hB hm
      (hmx j) hS
    rw [abs_of_pos (by linarith)] at hfL
    have e1 : pv ^ (j + 1) * pv = pv ^ (j + 1 + 1) := by ring
    have e2 : pv ^ (xv + j) * pv = pv ^ (xv + ((j + 1 : ℕ) : ℝ)) := by
      rw [Nat.cast_succ, ← add_assoc, Real.rpow_add_one hp0.ne']
    have e3 : (∏ i ∈ range j, (1 - pv ^ (i + 1))) * (1 - pv ^ (j + 1))
        = ∏ i ∈ range (j + 1), (1 - pv ^ (i + 1)) := by rw [prod_range_succ]
    have e4 : (∏ i ∈ range j, |1 - pv ^ (xv + i)|) * |1 - pv ^ (xv + j)|
        = ∏ i ∈ range (j + 1), |1 - pv ^ (xv + i)| := by rw [prod_range_succ]
    obtain ⟨o, ho, h1, h2, h3, h4⟩ := qProdLoop_lencl hu hp0 hp1 hP hlp hΛ hB hBx hm hm1 hmx hS
      k (j + 1) _ _ _ _ (neg != σ) _ _ _ _ (e1 ▸ ht.mul hu hP) (e2 ▸ hr.mul hu hP)
      (e3 ▸ hn.mul hu hfL) (e4 ▸ hd.mul hu hgL) (by positivity) (by positivity)
      (by linarith) (by linarith)
    refine ⟨o, ?_, ?_, ?_, ?_, ?_⟩
    · rw [qProdLoop, hf, hg]
      exact ho
    · rw [show j + (k + 1) = j + 1 + k by omega, hcast]
      exact h1.mono (by linarith)
    · rw [show j + (k + 1) = j + 1 + k by omega, hcast]
      exact h2.mono (by linarith)
    · rw [show j + (k + 1) = j + 1 + k by omega, hcast]
      exact h3.mono (by linarith)
    · rw [show j + (k + 1) = j + 1 + k by omega, hcast]
      exact h4.mono (by linarith)

theorem GS.congr {f g : ℕ → ℝ} (hf : GS f) (h : ∀ w, g w = f w) : GS g :=
  hf.of_le (Eventually.of_forall fun w => by rw [h w])

/-! ### The level functions -/

/-- The working precision of level `w`. -/
def qgV (A : QGammaIn) (w : ℕ) : ℕ := w + A.eb + 2 * w.log2 + 64

/-- `1 − p`. -/
def qgQ1 (A : QGammaIn) (w : ℕ) : Encl :=
  Encl.sub (qgV A w) (Encl.exact one) (A.P (qgV A w))

/-- `ln(1/p)`. -/
def qgLam (A : QGammaIn) (w : ℕ) : Encl := Encl.neg (lnOfEncl (A.P (qgV A w)) (qgV A w))

/-- `−ln(1 − p)`. -/
def qgMu (A : QGammaIn) (w : ℕ) : Encl := Encl.neg (lnOfEncl (qgQ1 A w) (qgV A w))

def qgLamc (A : QGammaIn) (w : ℕ) : Encl := (clampNonneg (qgLam A w).1, (qgLam A w).2)

def qgMuc (A : QGammaIn) (w : ℕ) : Encl := (clampNonneg (qgMu A w).1, (qgMu A w).2)

/-- The number of factors. -/
def qgK (A : QGammaIn) (w : ℕ) : ℕ := qGammaTerms (qgV A w) w (qgLam A w) (qgMu A w) A.shift

/-- `x ln p`. -/
def qgM (A : QGammaIn) (w : ℕ) : Encl :=
  Encl.mulPos (qgV A w) (Encl.neg (A.X (qgV A w))) (qgLamc A w)

/-- `p^x`. -/
def qgR0 (A : QGammaIn) (w : ℕ) : Encl :=
  (gammaExpEncl false (qgM A w) (qgV A w)).getD (one, one)

/-- The output of the loop. -/
def qgLoop (A : QGammaIn) (w : ℕ) : Bool × Encl × Encl × Encl × Encl :=
  (qProdLoop (qgV A w) (A.P (qgV A w)) (qgK A w) (A.P (qgV A w)) (qgR0 A w) (Encl.exact one)
    (Encl.exact one) false).getD
    (false, Encl.exact one, Encl.exact one, Encl.exact one, Encl.exact one)

/-- The quotient of the two products with their tails. -/
def qgR (A : QGammaIn) (w : ℕ) : Encl :=
  Encl.div (qgV A w)
    (Encl.mul (qgV A w) (qgLoop A w).2.2.2.1
      (qGammaTailLo (qgV A w) (qgQ1 A w) (qgLoop A w).2.1, one))
    (Encl.mul (qgV A w) (qgLoop A w).2.2.2.2
      (qGammaTailLo (qgV A w) (qgQ1 A w) (qgLoop A w).2.2.1, one))

/-- `ln |Γ_p(x)|`. -/
def qgL0 (A : QGammaIn) (w : ℕ) : Encl :=
  Encl.add (qgV A w)
    (Encl.mulPos (qgV A w) (Encl.sub (qgV A w) (A.X (qgV A w)) (Encl.exact one)) (qgMuc A w))
    (lnOfEncl (qgR A w) (qgV A w))

/-- `(x − 1)(x − 2)/2`. -/
def qgC2 (A : QGammaIn) (w : ℕ) : Encl :=
  Encl.half (Encl.add (qgV A w) (Encl.sub (qgV A w)
    (Encl.mul (qgV A w) (A.absX (qgV A w)) (A.absX (qgV A w)))
    (Encl.add (qgV A w) (A.X (qgV A w)) (Encl.add (qgV A w) (A.X (qgV A w)) (A.X (qgV A w)))))
    (Encl.nat 2))

/-- `ln |Γ_q(x)|` for the base `q = 1/p`. -/
def qgL1 (A : QGammaIn) (w : ℕ) : Encl :=
  Encl.add (qgV A w) (qgL0 A w) (Encl.mulPos (qgV A w) (qgC2 A w) (qgLamc A w))

/-- The enclosure of the bracket. -/
def qgL (A : QGammaIn) (w : ℕ) : Encl := if A.inv then qgL1 A w else qgL0 A w

theorem qgV_ge (A : QGammaIn) (w : ℕ) : w + 64 ≤ qgV A w := by
  unfold qgV
  omega

theorem pb_qgV (A : QGammaIn) : PB fun w : ℕ => ((qgV A w : ℕ) : ℝ) := by
  refine ((PB.natCast.const_mul 3).add (PB.const ((A.eb : ℝ) + 64))).of_abs_le fun w => ?_
  have h1 := log2_le_self w
  have h : qgV A w ≤ 3 * w + (A.eb + 64) := by
    unfold qgV
    omega
  have h' : ((qgV A w : ℕ) : ℝ) ≤ 3 * (w : ℝ) + ((A.eb : ℝ) + 64) := by exact_mod_cast h
  rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (by positivity)]
  exact h'

/-- **The bracket in terms of the level functions.** -/
theorem qGammaLnEnclOf_eq {A : QGammaIn} {w : ℕ} (hQ : lt zero (qgQ1 A w).1 = true)
    (hexp : gammaExpEncl false (qgM A w) (qgV A w) = some (qgR0 A w))
    (hloop : qProdLoop (qgV A w) (A.P (qgV A w)) (qgK A w) (A.P (qgV A w)) (qgR0 A w)
      (Encl.exact one) (Encl.exact one) false = some (qgLoop A w))
    (hEn : lt zero (qGammaTailLo (qgV A w) (qgQ1 A w) (qgLoop A w).2.1) = true)
    (hEd : lt zero (qGammaTailLo (qgV A w) (qgQ1 A w) (qgLoop A w).2.2.1) = true) :
    qGammaLnEnclOf A w = some ((qgLoop A w).1, qgL A w) := by
  show (if lt zero (qgQ1 A w).1 = true then
    (gammaExpEncl false (qgM A w) (qgV A w)).bind fun r0 =>
      (qProdLoop (qgV A w) (A.P (qgV A w)) (qgK A w) (A.P (qgV A w)) r0 (Encl.exact one)
        (Encl.exact one) false).bind fun o =>
        if (lt zero (qGammaTailLo (qgV A w) (qgQ1 A w) o.2.1) &&
            lt zero (qGammaTailLo (qgV A w) (qgQ1 A w) o.2.2.1)) = true then
          some (o.1, qGammaFinL (qgV A w) A.inv (A.X (qgV A w)) (A.absX (qgV A w)) (qgQ1 A w)
            (qgLamc A w) (qgMuc A w) o)
        else none
    else none) = _
  rw [ite_eq_left hQ, hexp, Option.bind_some, hloop, Option.bind_some, hEn, hEd]
  simp only [Bool.and_self, ↓reduceIte]
  rfl

section Conv

variable {A : QGammaIn} {pv xv : ℝ}

theorem qgP_lw (hA : QGammaArg A pv xv) : LW (fun w => A.P (qgV A w)) fun _ => pv :=
  ⟨fun w => 6 * (1 / 2 : ℝ) ^ qgV A w, (GS.half_pow (qgV_ge A)).const_mul 6,
    Eventually.of_forall fun w =>
      ⟨by positivity, hA.P _ (by have := qgV_ge A w; omega)⟩⟩

theorem qgX_aw (hA : QGammaArg A pv xv) : AW (fun w => A.X (qgV A w)) fun _ => xv := by
  obtain ⟨C, hC⟩ := hA.X
  exact AW.of_level (qgV_ge A) hC

theorem qgQ1_aw (hA : QGammaArg A pv xv) : AW (qgQ1 A) fun _ => 1 - pv :=
  AW.sub (qgV_ge A) (AW.exact toVal_one') ((qgP_lw hA).toAW (PB.const pv))

theorem qgQ1_lw (hA : QGammaArg A pv xv) : LW (qgQ1 A) fun _ => 1 - pv :=
  (qgQ1_aw hA).toLW_of_pos (c := 1 - pv) (by linarith [hA.p_lt])
    (Eventually.of_forall fun _ => le_rfl)

theorem qgLam_aw (hA : QGammaArg A pv xv) : AW (qgLam A) fun _ => -Real.log pv :=
  (LW.ln (qgV_ge A) (pb_qgV A) (qgP_lw hA) (G := fun _ => |Real.log pv|) (PB.const _)
    (fun _ => le_rfl)).neg

theorem qgMu_aw (hA : QGammaArg A pv xv) : AW (qgMu A) fun _ => -Real.log (1 - pv) :=
  (LW.ln (qgV_ge A) (pb_qgV A) (qgQ1_lw hA) (G := fun _ => |Real.log (1 - pv)|) (PB.const _)
    (fun _ => le_rfl)).neg

/-- The first term of the numerator of `K`. -/
def qgm (w : ℕ) : ℕ := (w + 64) * 7 / 10 + 1

theorem pb_qgm : PB fun w : ℕ => ((qgm w : ℕ) : ℝ) := by
  refine (PB.natCast.add (PB.const 65)).of_abs_le fun w => ?_
  have h : qgm w ≤ w + 65 := by
    unfold qgm
    omega
  have h' : ((qgm w : ℕ) : ℝ) ≤ (w : ℝ) + 65 := by exact_mod_cast h
  rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (by positivity)]
  exact h'

/-- **The number of factors**: `K ln(1/p) ≥ 0.7 (w + 64)`, and `K` grows linearly. -/
theorem qgK_bounds (hA : QGammaArg A pv xv) : ∀ᶠ w in atTop,
    ((qgm w : ℕ) : ℝ) ≤ (qgK A w : ℝ) * -Real.log pv ∧
      (qgK A w : ℝ) ≤ A.shift
        + 2 * ((((qgm w : ℕ) : ℝ) + -Real.log (1 - pv)) / -Real.log pv) + 3 := by
  have hp0 := hA.p_pos
  have hp1 := hA.p_lt
  have hlam : 0 < -Real.log pv := by linarith [Real.log_neg hp0 hp1]
  have hmu : 0 ≤ -Real.log (1 - pv) := by
    linarith [Real.log_nonpos (by linarith : (0 : ℝ) ≤ 1 - pv) (by linarith : 1 - pv ≤ 1)]
  have hV := qgV_ge A
  have hm1 : ∀ w, (1 : ℝ) ≤ ((qgm w : ℕ) : ℝ) := fun w => by
    have : 1 ≤ qgm w := by unfold qgm; omega
    exact_mod_cast this
  have numL := (AW.add hV (AW.nat pb_qgm) (qgMu_aw hA)).toLW
    (Eventually.of_forall fun w => by linarith [hm1 w])
  have lamL := (qgLam_aw hA).toLW_of_pos hlam (Eventually.of_forall fun _ => le_rfl)
  obtain ⟨lam, g, e⟩ := LW.div hV numL lamL
  filter_upwards [e, g.eventually_le (by norm_num : (0 : ℝ) < 1 / 2)] with w he hs
  obtain ⟨h0, hL⟩ := he
  have hκ0 : 0 < (((qgm w : ℕ) : ℝ) + -Real.log (1 - pv)) / -Real.log pv :=
    div_pos (by linarith [hm1 w]) hlam
  obtain ⟨l, u, hl, hu, hl0, h1, h2, h3⟩ := (hL.toA h0 ((le_abs_self _).trans hs))
  have hlam2 : 2 * ((((qgm w : ℕ) : ℝ) + -Real.log (1 - pv)) / -Real.log pv) * lam w
      ≤ (((qgm w : ℕ) : ℝ) + -Real.log (1 - pv)) / -Real.log pv := by
    have := (le_abs_self _).trans hs
    nlinarith
  obtain ⟨ht, -⟩ := truncToAzInt_spec hu
  have ht' := abs_lt.mp ht
  have hz : ((azIntPos (truncToAzInt (Encl.div (qgV A w) (Encl.add (qgV A w)
      (Encl.nat (qgm w)) (qgMu A w)) (qgLam A w)).2) : ℕ) : ℝ)
      = max (((truncToAzInt (Encl.div (qgV A w) (Encl.add (qgV A w)
        (Encl.nat (qgm w)) (qgMu A w)) (qgLam A w)).2).toInt : ℝ)) 0 := by
    have := azIntPos_cast (truncToAzInt (Encl.div (qgV A w) (Encl.add (qgV A w)
      (Encl.nat (qgm w)) (qgMu A w)) (qgLam A w)).2)
    have h' : (((azIntPos (truncToAzInt (Encl.div (qgV A w) (Encl.add (qgV A w)
        (Encl.nat (qgm w)) (qgMu A w)) (qgLam A w)).2) : ℕ) : ℤ) : ℝ)
        = ((max (truncToAzInt (Encl.div (qgV A w) (Encl.add (qgV A w)
          (Encl.nat (qgm w)) (qgMu A w)) (qgLam A w)).2).toInt 0 : ℤ) : ℝ) := by rw [this]
    push_cast at h'
    exact h'
  have hK : (qgK A w : ℝ) = A.shift + ((azIntPos (truncToAzInt (Encl.div (qgV A w)
      (Encl.add (qgV A w) (Encl.nat (qgm w)) (qgMu A w)) (qgLam A w)).2) : ℕ) : ℝ) + 2 := by
    have : qgK A w = A.shift + azIntPos (truncToAzInt (Encl.div (qgV A w)
      (Encl.add (qgV A w) (Encl.nat (qgm w)) (qgMu A w)) (qgLam A w)).2) + 2 := rfl
    rw [this]
    push_cast
    ring
  have hsh : (0 : ℝ) ≤ (A.shift : ℝ) := Nat.cast_nonneg _
  rw [hK, hz]
  constructor
  · have h4 : (((qgm w : ℕ) : ℝ) + -Real.log (1 - pv)) / -Real.log pv
        ≤ (A.shift : ℝ) + max (((truncToAzInt (Encl.div (qgV A w) (Encl.add (qgV A w)
          (Encl.nat (qgm w)) (qgMu A w)) (qgLam A w)).2).toInt : ℝ)) 0 + 2 := by
      have := le_max_left (((truncToAzInt (Encl.div (qgV A w) (Encl.add (qgV A w)
        (Encl.nat (qgm w)) (qgMu A w)) (qgLam A w)).2).toInt : ℝ)) 0
      linarith [ht'.1]
    have h5 := mul_le_mul_of_nonneg_right h4 hlam.le
    rw [div_mul_cancel₀ _ hlam.ne'] at h5
    linarith
  · have : max (((truncToAzInt (Encl.div (qgV A w) (Encl.add (qgV A w)
        (Encl.nat (qgm w)) (qgMu A w)) (qgLam A w)).2).toInt : ℝ)) 0 ≤ u + 1 :=
      max_le (by linarith [ht'.2]) (by linarith)
    linarith

theorem pb_qgK (hA : QGammaArg A pv xv) : PB fun w : ℕ => ((qgK A w : ℕ) : ℝ) := by
  refine ((((PB.const (A.shift : ℝ)).add (((pb_qgm.add (PB.const (-Real.log (1 - pv)))).div_const
    (-Real.log pv)).const_mul 2)).add (PB.const 3))).of_eventually_le ?_
  filter_upwards [qgK_bounds hA] with w hw
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  exact hw.2.trans (le_abs_self _)

theorem gs_pow_qgK (hA : QGammaArg A pv xv) : GS fun w => pv ^ qgK A w := by
  have hp0 := hA.p_pos
  refine ⟨fun _ => 1, Real.exp (-(7 / 10)), PB.const 1, (Real.exp_pos _).le,
    by simp, ?_⟩
  filter_upwards [qgK_bounds hA] with w hw
  have hm : (7 / 10 : ℝ) * w ≤ ((qgm w : ℕ) : ℝ) := by
    have : 7 * w ≤ 10 * qgm w := by unfold qgm; omega
    have h' : (7 : ℝ) * w ≤ 10 * ((qgm w : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  rw [one_mul, abs_of_pos (pow_pos hp0 _), ← Real.exp_nat_mul]
  conv_lhs => rw [← Real.exp_log hp0, ← Real.exp_nat_mul]
  exact Real.exp_le_exp.mpr (by linarith [hw.1])

theorem qgM_aw (hA : QGammaArg A pv xv) : AW (qgM A) fun _ => -xv * -Real.log pv :=
  AW.mulPosClamp (qgV_ge A) (qgX_aw hA).neg (qgLam_aw hA)
    (Eventually.of_forall fun _ => by
      linarith [Real.log_nonpos hA.p_pos.le hA.p_lt.le])

/-- `p^x`: the exponential answers, with a geometrically small relative width. -/
theorem qgR0_spec (hA : QGammaArg A pv xv) : ∃ lam : ℕ → ℝ, GS lam ∧ ∀ᶠ w in atTop,
    0 ≤ lam w ∧ gammaExpEncl false (qgM A w) (qgV A w) = some (qgR0 A w) ∧
      LEncl (qgR0 A w) (pv ^ xv) (lam w) := by
  have hp0 := hA.p_pos
  obtain ⟨-, ε, g, e⟩ := qgM_aw hA
  have gu := GS.half_pow (qgV_ge A)
  obtain ⟨v, hv⟩ : ∃ v : ℝ, v = -xv * -Real.log pv := ⟨_, rfl⟩
  rw [← hv] at e
  have hpx : pv ^ xv = Real.exp v := by
    rw [Real.rpow_def_of_pos hp0, hv]
    congr 1
    ring
  have gη : GS fun w => expOfBracketEps v (ε w) (qgV A w) := by
    refine ((GS.pb_mul (((pb_qgV A).add (PB.const 9)).const_mul (Real.exp v * 80)) gu).add
      (((g.const_mul 24).add (gu.const_mul (1 / 4))).const_mul (Real.exp v))).congr fun w => ?_
    unfold expOfBracketEps expEps
    ring
  refine ⟨fun w => 2 / Real.exp v * expOfBracketEps v (ε w) (qgV A w), gη.const_mul _, ?_⟩
  filter_upwards [e, g.eventually_le (by norm_num : (0 : ℝ) < 1 / 2),
    gη.eventually_le (by positivity : (0 : ℝ) < Real.exp v / 2)] with w he h1 h2
  have hη := (le_abs_self _).trans h2
  have h64 : 64 ≤ qgV A w := by have := qgV_ge A w; omega
  obtain ⟨b, hb, -, hbA⟩ := gammaExpEncl_width (neg := false) he ((le_abs_self _).trans h1) h64
    (by
      simp only [Bool.false_eq_true, ↓reduceIte]
      linarith [Real.exp_pos v])
  simp only [Bool.false_eq_true, ↓reduceIte] at hbA
  have hr : qgR0 A w = b := by
    unfold qgR0
    rw [hb]
    rfl
  have hη0 := hbA.width_nonneg
  rw [hr, hpx]
  refine ⟨by positivity, hb, ?_⟩
  have := LEncl.ofA hbA (by linarith) (Real.exp_pos v)
  rwa [show 2 * expOfBracketEps v (ε w) (qgV A w) / Real.exp v
    = 2 / Real.exp v * expOfBracketEps v (ε w) (qgV A w) by ring] at this

/-- **The loop answers**, with geometrically small relative widths. -/
theorem qgLoop_spec (hA : QGammaArg A pv xv) (hnz : ∀ m : ℕ, xv ≠ -m) :
    ∃ lam : ℕ → ℝ, GS lam ∧ ∀ᶠ w in atTop, 0 ≤ lam w ∧
      qProdLoop (qgV A w) (A.P (qgV A w)) (qgK A w) (A.P (qgV A w)) (qgR0 A w)
        (Encl.exact one) (Encl.exact one) false = some (qgLoop A w) ∧
      LEncl (qgLoop A w).2.1 (pv ^ (qgK A w + 1)) (lam w) ∧
      LEncl (qgLoop A w).2.2.1 (pv ^ (xv + (qgK A w : ℕ))) (lam w) ∧
      LEncl (qgLoop A w).2.2.2.1 (∏ i ∈ range (qgK A w), (1 - pv ^ (i + 1))) (lam w) ∧
      LEncl (qgLoop A w).2.2.2.2 (∏ i ∈ range (qgK A w), |1 - pv ^ (xv + i)|) (lam w) := by
  have hp0 := hA.p_pos
  have hp1 := hA.p_lt
  obtain ⟨m, hm0, hm1, hmx⟩ := exists_pos_le_abs_one_sub_rpow hp0 hp1 hnz
  obtain ⟨B, hBd⟩ : ∃ B : ℝ, B = pv ^ xv + 1 := ⟨_, rfl⟩
  have hpx0 : 0 < pv ^ xv := Real.rpow_pos_of_pos hp0 _
  have hB1 : 1 ≤ B := by rw [hBd]; linarith
  have hBx : ∀ i : ℕ, pv ^ (xv + i) ≤ B := fun i => by
    rw [Real.rpow_add hp0, Real.rpow_natCast, hBd]
    have : pv ^ i ≤ 1 := pow_le_one₀ hp0.le hp1.le
    nlinarith
  obtain ⟨l0, g0, e0⟩ := qgR0_spec hA
  have gu := GS.half_pow (qgV_ge A)
  have pbK := pb_qgK hA
  have gΛ : GS fun w => 6 * (1 / 2 : ℝ) ^ qgV A w + l0 w
      + (qgK A w : ℝ) * (12 * (1 / 2 : ℝ) ^ qgV A w) :=
    ((gu.const_mul 6).add g0).add (GS.pb_mul pbK (gu.const_mul 12))
  have gS : GS fun w => 2 * (2 * B * (6 * (1 / 2 : ℝ) ^ qgV A w + l0 w
      + (qgK A w : ℝ) * (12 * (1 / 2 : ℝ) ^ qgV A w))
      + 4 * (2 * B + 1) * (1 / 2 : ℝ) ^ qgV A w) :=
    (((gΛ.const_mul (2 * B)).add (gu.const_mul (4 * (2 * B + 1)))).const_mul 2)
  have gΦ : GS fun w => 2 * (2 * B * (6 * (1 / 2 : ℝ) ^ qgV A w + l0 w
      + (qgK A w : ℝ) * (12 * (1 / 2 : ℝ) ^ qgV A w))
      + 4 * (2 * B + 1) * (1 / 2 : ℝ) ^ qgV A w) / m :=
    (gS.const_mul (1 / m)).congr fun w => by ring
  refine ⟨fun w => (6 * (1 / 2 : ℝ) ^ qgV A w + l0 w
      + (qgK A w : ℝ) * (12 * (1 / 2 : ℝ) ^ qgV A w))
      + (qgK A w : ℝ) * (2 * (2 * B * (6 * (1 / 2 : ℝ) ^ qgV A w + l0 w
      + (qgK A w : ℝ) * (12 * (1 / 2 : ℝ) ^ qgV A w))
      + 4 * (2 * B + 1) * (1 / 2 : ℝ) ^ qgV A w) / m + 6 * (1 / 2 : ℝ) ^ qgV A w),
    gΛ.add (GS.pb_mul pbK (gΦ.add (gu.const_mul 6))), ?_⟩
  filter_upwards [e0, gΛ.eventually_le (by norm_num : (0 : ℝ) < 1 / 2),
    gS.eventually_le hm0] with w he hΛ hS
  obtain ⟨hl0, -, hr0⟩ := he
  have h64 : 64 ≤ qgV A w := by have := qgV_ge A w; omega
  have : NeZero (qgV A w) := ⟨by omega⟩
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (1 / 2 : ℝ) ^ qgV A w := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hK0 : (0 : ℝ) ≤ (qgK A w : ℝ) := Nat.cast_nonneg _
  rw [← hu] at hΛ hS ⊢
  obtain ⟨Λ, hΛd⟩ : ∃ Λ : ℝ, Λ = 6 * u + l0 w + (qgK A w : ℝ) * (12 * u) := ⟨_, rfl⟩
  rw [← hΛd] at hΛ hS ⊢
  have hΛ0 : 0 ≤ Λ := by rw [hΛd]; positivity
  have hΛ' := (le_abs_self _).trans hΛ
  have hS' := (le_abs_self _).trans hS
  have hP := hA.P _ h64
  rw [← hu] at hP
  obtain ⟨o, ho, h1, h2, h3, h4⟩ := qProdLoop_lencl (half_pow_le_eighth (by omega))
    hp0 hp1 (lp := 6 * u) hP (by positivity) hΛ' hB1 hBx hm0 hm1 hmx (hu ▸ hS')
    (qgK A w) 0 (A.P (qgV A w)) (qgR0 A w) (Encl.exact one) (Encl.exact one) false
    (6 * u) (l0 w) 0 0 (by simpa using hP) (by simpa using hr0)
    (by simpa using LEncl.exact toVal_one' one_pos)
    (by simpa using LEncl.exact toVal_one' one_pos) (by positivity) hl0
    (by rw [← hu, hΛd]; nlinarith) (by rw [← hu, hΛd]; nlinarith)
  have hlo : qgLoop A w = o := by
    unfold qgLoop
    rw [ho]
    rfl
  rw [← hu] at h1 h2 h3 h4
  simp only [zero_add] at h1 h2 h3 h4
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℝ, Φ = 2 * (2 * B * Λ + 4 * (2 * B + 1) * u) / m := ⟨_, rfl⟩
  rw [← hΦ] at h3 h4 ⊢
  have hΦ0 : 0 ≤ Φ := by rw [hΦ]; positivity
  have hstep : 0 ≤ (qgK A w : ℝ) * (Φ + 6 * u) := by positivity
  rw [hlo]
  refine ⟨by positivity, ho, h1.mono ?_, h2.mono ?_, h3.mono ?_, h4.mono ?_⟩
  · rw [hΛd]; nlinarith
  · rw [hΛd]; nlinarith
  · linarith
  · linarith

/-- The tail `(a; p)_∞` enclosed by `[1 − a/(1 − p), 1]`. -/
theorem qTail_lw {En : ℕ → Encl} {a T : ℕ → ℝ} (hEn : AW En fun w => 1 - a w) (ha : GS a)
    (hb : ∀ᶠ w in atTop, 0 ≤ a w ∧ 1 - a w ≤ T w ∧ T w ≤ 1) :
    (∀ᶠ w in atTop, lt zero (En w).1 = true) ∧ LW (fun w => ((En w).1, one)) T := by
  obtain ⟨-, ε, g, e⟩ := hEn
  have key : ∀ᶠ w in atTop, lt zero (En w).1 = true ∧ 0 ≤ 2 * (a w + ε w) ∧
      LEncl ((En w).1, one) (T w) (2 * (a w + ε w)) := by
    filter_upwards [e, hb, (ha.add g).eventually_le (by norm_num : (0 : ℝ) < 1 / 2)] with
      w he hbw hs
    obtain ⟨ha0, hT1, hT2⟩ := hbw
    have hε0 := he.width_nonneg
    have hs' := (le_abs_self _).trans hs
    obtain ⟨l, u, hl, hu, h1, h2, h3⟩ := he
    have hl0 : 0 < l := by linarith
    refine ⟨(lt_eq_true_iff toVal_zero' hl).mpr hl0, by positivity,
      l, 1, hl, toVal_one', hl0, by linarith, hT2, ?_⟩
    have hexp := Real.add_one_le_exp (2 * (a w + ε w))
    have hl1 : 1 - (a w + ε w) ≤ l := by linarith
    nlinarith
  exact ⟨key.mono fun w h => h.1,
    fun w => 2 * (a w + ε w), (ha.add g).const_mul 2, key.mono fun w h => h.2⟩

/-- The square of `|x|`. -/
theorem qgAbsSq_aw (hA : QGammaArg A pv xv) :
    AW (fun w => Encl.mul (qgV A w) (A.absX (qgV A w)) (A.absX (qgV A w)))
      fun _ => |xv| * |xv| := by
  obtain ⟨C, hC⟩ := hA.absX
  refine ⟨PB.const _, fun w => (2 * (|C| * (|xv| + |C|)) + 4 * (|xv| + |C|) * (|xv| + |C|))
    * (1 / 2 : ℝ) ^ qgV A w, (GS.half_pow (qgV_ge A)).const_mul _,
    Eventually.of_forall fun w => ?_⟩
  have h64 : 64 ≤ qgV A w := by have := qgV_ge A w; omega
  have : NeZero (qgV A w) := ⟨by omega⟩
  have hu0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ qgV A w := by positivity
  have hu1 : (1 / 2 : ℝ) ^ qgV A w ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hCu : C * (1 / 2 : ℝ) ^ qgV A w ≤ |C| * (1 / 2 : ℝ) ^ qgV A w :=
    mul_le_mul_of_nonneg_right (le_abs_self C) hu0
  have hCu' : |C| * (1 / 2 : ℝ) ^ qgV A w ≤ |C| := by
    have := mul_le_mul_of_nonneg_left hu1 (abs_nonneg C)
    linarith
  have h := (hC _ h64).mono hCu
  have hm := h.mul (w := qgV A w) h (B₁ := |xv| + |C|) (B₂ := |xv| + |C|) (by linarith)
    (by linarith)
  exact hm.toA.mono (le_of_eq (by ring))

/-- **The enclosure of `ln |Γ_q(x)|` converges**: at every large level the bracket answers,
with a width that tends to `0`. -/
theorem qGammaLnEnclOf_conv (hA : QGammaArg A pv xv) (hnz : ∀ m : ℕ, xv ≠ -m) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ w in atTop, ∃ (neg : Bool) (L : Encl),
      qGammaLnEnclOf A w = some (neg, L) ∧
        AEncl L (Real.log |qGammaVal A.inv pv xv|) (ε w) := by
  have hp0 := hA.p_pos
  have hp1 := hA.p_lt
  have h1p : 0 < 1 - pv := by linarith
  have hV := qgV_ge A
  have pbV := pb_qgV A
  have hlam0 : 0 ≤ -Real.log pv := by linarith [Real.log_nonpos hp0.le hp1.le]
  have hmu0 : 0 ≤ -Real.log (1 - pv) := by
    linarith [Real.log_nonpos h1p.le (by linarith : 1 - pv ≤ 1)]
  have Xa := qgX_aw hA
  have Q1L := qgQ1_lw hA
  have gK := gs_pow_qgK hA
  obtain ⟨lam, gl, el⟩ := qgLoop_spec hA hnz
  obtain ⟨l0, g0, e0⟩ := qgR0_spec hA
  have tL : LW (fun w => (qgLoop A w).2.1) fun w => pv ^ (qgK A w + 1) :=
    ⟨lam, gl, el.mono fun w h => ⟨h.1, h.2.2.1⟩⟩
  have rL : LW (fun w => (qgLoop A w).2.2.1) fun w => pv ^ (xv + (qgK A w : ℕ)) :=
    ⟨lam, gl, el.mono fun w h => ⟨h.1, h.2.2.2.1⟩⟩
  have nL : LW (fun w => (qgLoop A w).2.2.2.1)
      fun w => ∏ i ∈ range (qgK A w), (1 - pv ^ (i + 1)) :=
    ⟨lam, gl, el.mono fun w h => ⟨h.1, h.2.2.2.2.1⟩⟩
  have dL : LW (fun w => (qgLoop A w).2.2.2.2)
      fun w => ∏ i ∈ range (qgK A w), |1 - pv ^ (xv + i)| :=
    ⟨lam, gl, el.mono fun w h => ⟨h.1, h.2.2.2.2.2⟩⟩
  -- the tails
  have ga : GS fun w => pv ^ (qgK A w + 1) / (1 - pv) :=
    (gK.const_mul (pv / (1 - pv))).congr fun w => by rw [pow_succ]; ring
  have gb : GS fun w => pv ^ (xv + (qgK A w : ℕ)) / (1 - pv) :=
    (gK.const_mul (pv ^ xv / (1 - pv))).congr fun w => by
      rw [Real.rpow_add hp0, Real.rpow_natCast]
      ring
  have EnA : AW (fun w => Encl.sub (qgV A w) (Encl.exact one)
      (Encl.div (qgV A w) (qgLoop A w).2.1 (qgQ1 A w)))
      fun w => 1 - pv ^ (qgK A w + 1) / (1 - pv) :=
    AW.sub hV (AW.exact toVal_one') ((LW.div hV tL Q1L).toAW
      ((PB.const (1 / (1 - pv))).of_abs_le fun w => by
        rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
        exact div_le_div_of_nonneg_right (pow_le_one₀ hp0.le hp1.le) h1p.le))
  have EdA : AW (fun w => Encl.sub (qgV A w) (Encl.exact one)
      (Encl.div (qgV A w) (qgLoop A w).2.2.1 (qgQ1 A w)))
      fun w => 1 - pv ^ (xv + (qgK A w : ℕ)) / (1 - pv) :=
    AW.sub hV (AW.exact toVal_one') ((LW.div hV rL Q1L).toAW
      ((PB.const (pv ^ xv / (1 - pv))).of_abs_le fun w => by
        have hpx : 0 < pv ^ xv := Real.rpow_pos_of_pos hp0 _
        rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
        refine div_le_div_of_nonneg_right ?_ h1p.le
        rw [Real.rpow_add hp0, Real.rpow_natCast]
        have : pv ^ qgK A w ≤ 1 := pow_le_one₀ hp0.le hp1.le
        nlinarith))
  obtain ⟨hEn, TnL⟩ := qTail_lw (T := fun w => qPochR (pv ^ (qgK A w + 1)) pv) EnA ga
    (Eventually.of_forall fun w => by
      have hb := qPochR_bounds hp0 hp1 (a := pv ^ (qgK A w + 1)) (by positivity)
        (pow_le_one₀ hp0.le hp1.le)
      exact ⟨by positivity, hb.1, hb.2⟩)
  have hbd : ∀ᶠ w in atTop, 0 ≤ pv ^ (xv + (qgK A w : ℕ)) / (1 - pv) ∧
      1 - pv ^ (xv + (qgK A w : ℕ)) / (1 - pv) ≤ qPochR (pv ^ (xv + (qgK A w : ℕ))) pv ∧
      qPochR (pv ^ (xv + (qgK A w : ℕ))) pv ≤ 1 := by
    filter_upwards [gb.eventually_le (by norm_num : (0 : ℝ) < 1 / 2)] with w hs
    have ha0 : 0 ≤ pv ^ (xv + (qgK A w : ℕ)) := Real.rpow_nonneg hp0.le _
    have h2 := (le_abs_self _).trans hs
    have ha1 : pv ^ (xv + (qgK A w : ℕ)) ≤ 1 := by
      rw [div_le_iff₀ h1p] at h2
      linarith
    have hb := qPochR_bounds hp0 hp1 ha0 ha1
    exact ⟨by positivity, hb.1, hb.2⟩
  obtain ⟨hEd, TdL⟩ := qTail_lw (T := fun w => qPochR (pv ^ (xv + (qgK A w : ℕ))) pv) EdA gb hbd
  -- the quotient
  have NL := (LW.mul hV nL TnL).congr' (y := fun _ => qPochR pv pv)
    (Eventually.of_forall fun w => (qPochR_self_split hp0 hp1 (qgK A w)).symm)
  have DL := (LW.mul hV dL TdL).congr' (y := fun _ => |qPochR (pv ^ xv) pv|) (by
    filter_upwards [hbd, gb.eventually_le (by norm_num : (0 : ℝ) < 1 / 2)] with w hw hs
    have h2 := (le_abs_self _).trans hs
    have hAd : 0 ≤ qPochR (pv ^ (xv + (qgK A w : ℕ))) pv := by linarith [hw.2.1]
    rw [qPochR_rpow_split hp0 hp1 xv (qgK A w), abs_mul, Finset.abs_prod, abs_of_nonneg hAd])
  have RL : LW (qgR A) fun _ => qPochR pv pv / |qPochR (pv ^ xv) pv| := LW.div hV NL DL
  have lnR := LW.ln hV pbV RL (G := fun _ => |Real.log (qPochR pv pv / |qPochR (pv ^ xv) pv|)|)
    (PB.const _) (fun _ => le_rfl)
  have L0A : AW (qgL0 A) _ := AW.add hV
    (AW.mulPosClamp hV (AW.sub hV Xa (AW.exact toVal_one')) (qgMu_aw hA)
      (Eventually.of_forall fun _ => hmu0)) lnR
  have c2A : AW (qgC2 A) _ := (AW.add hV (AW.sub hV (qgAbsSq_aw hA)
    (AW.add hV Xa (AW.add hV Xa Xa))) (AW.nat (n := fun _ => 2) (PB.const _))).half
  have L1A : AW (qgL1 A) _ := AW.add hV L0A
    (AW.mulPosClamp hV c2A (qgLam_aw hA) (Eventually.of_forall fun _ => hlam0))
  have LA : ∃ v : ℕ → ℝ, AW (qgL A) v := by
    cases hinv : A.inv with
    | false =>
      have : qgL A = qgL0 A := funext fun w => by unfold qgL; rw [hinv]; rfl
      rw [this]
      exact ⟨_, L0A⟩
    | true =>
      have : qgL A = qgL1 A := funext fun w => by unfold qgL; rw [hinv]; rfl
      rw [this]
      exact ⟨_, L1A⟩
  obtain ⟨v, -, ε, g, e⟩ := LA
  refine ⟨ε, g.tendsto, ?_⟩
  filter_upwards [e, e0, el, hEn, hEd, (qgQ1_lw hA).choose_spec.2] with w he h0 hl hn hd hq
  have hQ : lt zero (qgQ1 A w).1 = true := by
    obtain ⟨l, u, hl', -, hl0, -⟩ := hq.2
    exact (lt_eq_true_iff toVal_zero' hl').mpr hl0
  have hc := qGammaLnEnclOf_eq hQ h0.2.1 hl.2.1 hn hd
  obtain ⟨hpos, hL⟩ := qGammaLnEnclOf_spec hA hc
  rw [sign_mul_eq_abs hpos] at hL
  exact ⟨_, _, hc, he.of_isEncl hL⟩

/-- **The core of `Γ_q(x)` converges** off the poles. -/
theorem qGammaCoreOf_coreConv (hA : QGammaArg A pv xv) (hnz : ∀ m : ℕ, xv ≠ -m) :
    CoreConv (qGammaCoreOf A) (qGammaVal A.inv pv xv) := by
  obtain ⟨E, hE, hev⟩ := qGammaLnEnclOf_conv hA hnz
  obtain ⟨ht, hevE⟩ := gammaExpEncl_eventually false (Real.log |qGammaVal A.inv pv xv|) hE
  simp only [Bool.false_eq_true, ↓reduceIte] at ht hevE
  refine ⟨_, ht, ?_⟩
  filter_upwards [hev, hevE, eventually_ge_atTop 64] with w h1 h2 h3
  obtain ⟨neg, L, hc, hLA⟩ := h1
  obtain ⟨hpos, -⟩ := qGammaLnEnclOf_spec hA hc
  have habs := sign_mul_eq_abs hpos
  have hB0 : 0 < |qGammaVal A.inv pv xv| := habs ▸ hpos
  obtain ⟨b, hb, hb1, hb2⟩ := h2 L hLA
  rw [Real.exp_log hB0] at hb1 hb2
  refine ⟨neg, b, ?_, ?_, ?_⟩
  · unfold qGammaCoreOf
    rw [hc]
    simp [hb]
  · rw [habs]; exact hb1
  · rw [habs]; exact hb2

end Conv

end Azurite.AzFloat
