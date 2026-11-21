/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.GlaisherKinkelin
import Azurite.AzFloat.Equiv.PochhammerWidth
import Azurite.AzFloat.Equiv.PolygammaWidth
import Azurite.Transcendental.GlaisherKinkelin

/-!
# Equivalence: the Glaisher–Kinkelin constant

`glaisherKinkelinPrecRound p mode` is the correct rounding of `DLMF.glaisherA = e^C`, the
Glaisher–Kinkelin constant (`ln A = C = 1/12 − ζ′(−1)`, `DLMF.deriv_zeta_neg_one`), or
`(nan, .eq)` when the fuel runs out (`glaisherKinkelinPrecRound_eq_or`);
`glaisherKinkelinPrecRoundFuel_zivSpec` adds completeness in the limit of the fuel.

One theorem carries both: `glaisherKinkelinLnEncl_aencl` — at every level `w ≥ 64` the
enclosure of `ln A` contains `C` and is at most `glaisherDelta w` wide, an explicit function
that tends to `0` (`tendsto_glaisherDelta`): twice the last term of the expansion, and a
polynomial in `w` times `2^(−w)` for the rounding.  The pieces: `glaisherProd_lencl` (the
factorial and the product of factorials, from products rounded down: `LLow`,
`glaisherProdLo_llow`, `LLow.toEncl`), `glaisherTermEncl_lencl` (a term from the tangent
numbers), `glaisher_alt` (the terms envelop the remainder, from DLMF 2.10.4–2.10.5), and
`altSumLoop_width` (`Equiv/AltSeriesWidth.lean`), the width of the loop of Stirling's
series.
-/

namespace Azurite.AzFloat

open Filter Topology Finset
open scoped Nat

/-! ### The products -/

/-- `f` is a positive lower bound of `F` within the factor `e^lam`. -/
def LLow (f : AzFloat) (F lam : ℝ) : Prop :=
  ∃ fv : ℝ, f.toVal = some (fv : EReal) ∧ 0 < fv ∧ fv ≤ F ∧ F ≤ fv * Real.exp lam

theorem LLow.mono {f : AzFloat} {F lam lam' : ℝ} (h : LLow f F lam) (hl : lam ≤ lam') :
    LLow f F lam' := by
  obtain ⟨fv, hf, h0, h1, h2⟩ := h
  exact ⟨fv, hf, h0, h1,
    h2.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hl) h0.le)⟩

theorem LLow.exact {f : AzFloat} {fv : ℝ} (hf : f.toVal = some (fv : EReal)) (h0 : 0 < fv) :
    LLow f fv 0 := ⟨fv, hf, h0, le_rfl, by simp⟩

/-- A product rounded down: three more units of `u`. -/
theorem LLow.mulFloor {V : ℕ} [NeZero V] (hu : (1 / 2 : ℝ) ^ V ≤ 1 / 8) {f g : AzFloat}
    {F G a b : ℝ} (hf : LLow f F a) (hg : LLow g G b) :
    LLow (mulPrecRound f g V .Floor).1 (F * G) (a + b + 3 * (1 / 2 : ℝ) ^ V) := by
  obtain ⟨fv, hfv, f0, f1, f2⟩ := hf
  obtain ⟨gv, hgv, g0, g1, g2⟩ := hg
  obtain ⟨r, hr, -, hr1, hr2⟩ := mulFloor_err hfv hgv V (mul_pos f0 g0).le
  obtain ⟨u, hud⟩ : ∃ u : ℝ, u = (1 / 2 : ℝ) ^ V := ⟨_, rfl⟩
  rw [← hud] at hu hr2 ⊢
  have hu0 : 0 < u := by rw [hud]; positivity
  have hx0 : 0 < fv * gv := mul_pos f0 g0
  have hrx : fv * gv * (1 - 2 * u) ≤ r := by linarith only [hr2]
  have hr0 : 0 < r := lt_of_lt_of_le (mul_pos hx0 (by linarith only [hu])) hrx
  have hF0 : 0 < F := lt_of_lt_of_le f0 f1
  refine ⟨r, hr, hr0, hr1.trans (mul_le_mul f1 g1 g0.le hF0.le), ?_⟩
  have h3 : 1 + 3 * u ≤ Real.exp (3 * u) := by linarith only [Real.add_one_le_exp (3 * u)]
  have hx : fv * gv ≤ r * Real.exp (3 * u) := by
    have h4 : fv * gv * 1 ≤ fv * gv * ((1 - 2 * u) * (1 + 3 * u)) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hx0.le
    have h5 : fv * gv * (1 - 2 * u) * (1 + 3 * u) ≤ r * Real.exp (3 * u) :=
      mul_le_mul hrx h3 (by linarith only [hu0]) hr0.le
    linarith only [h4, h5, show fv * gv * ((1 - 2 * u) * (1 + 3 * u))
      = fv * gv * (1 - 2 * u) * (1 + 3 * u) by ring]
  calc F * G ≤ fv * Real.exp a * (gv * Real.exp b) :=
        mul_le_mul f2 g2 (lt_of_lt_of_le g0 g1).le (mul_pos f0 (Real.exp_pos a)).le
    _ = fv * gv * (Real.exp a * Real.exp b) := by ring
    _ ≤ r * Real.exp (3 * u) * (Real.exp a * Real.exp b) :=
        mul_le_mul_of_nonneg_right hx (by positivity)
    _ = r * Real.exp (a + b + 3 * u) := by
        rw [Real.exp_add, Real.exp_add]
        ring

/-- **The loop of the factorials**: from lower bounds of `i!` and `∏_{l<i} l!`, lower bounds
of `(i + k)!` and `∏_{l<i+k} l!`. -/
theorem glaisherProdLo_llow {V : ℕ} [NeZero V] (hu : (1 / 2 : ℝ) ^ V ≤ 1 / 8) :
    ∀ (k i : ℕ) (f w : AzFloat) (a b : ℝ), 0 ≤ a →
      LLow f (i ! : ℝ) a → LLow w (∏ l ∈ range i, (l ! : ℝ)) b →
      LLow (glaisherProdLo V k i f w).1 ((i + k) ! : ℝ) (a + 3 * k * (1 / 2 : ℝ) ^ V) ∧
        LLow (glaisherProdLo V k i f w).2 (∏ l ∈ range (i + k), (l ! : ℝ))
          (b + k * a + 3 * (k : ℝ) ^ 2 * (1 / 2 : ℝ) ^ V)
  | 0, i, f, w, a, b, _, hf, hw => by
    rw [glaisherProdLo]
    exact ⟨hf.mono (by simp), hw.mono (by simp)⟩
  | k + 1, i, f, w, a, b, h0, hf, hw => by
    rw [glaisherProdLo]
    have hu0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ V := by positivity
    have hf' : LLow (mulPrecRound f (ofAzNat (AzNat.ofNat (i + 1))) V .Floor).1
        ((i + 1) ! : ℝ) (a + 3 * (1 / 2 : ℝ) ^ V) := by
      have := (hf.mulFloor hu (LLow.exact (toVal_ofAzNat_ofNat (i + 1))
        (by exact_mod_cast Nat.succ_pos i))).mono
        (le_of_eq (by ring : a + 0 + 3 * (1 / 2 : ℝ) ^ V = a + 3 * (1 / 2 : ℝ) ^ V))
      rw [Nat.factorial_succ, Nat.cast_mul, mul_comm]
      exact this
    have hw' : LLow (mulPrecRound w f V .Floor).1 (∏ l ∈ range (i + 1), (l ! : ℝ))
        (b + a + 3 * (1 / 2 : ℝ) ^ V) := by
      rw [prod_range_succ]
      exact hw.mulFloor hu hf
    obtain ⟨g1, g2⟩ := glaisherProdLo_llow hu k (i + 1) _ _ _ _ (by positivity) hf' hw'
    rw [show i + 1 + k = i + (k + 1) by ring] at g1 g2
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    refine ⟨g1.mono ?_, g2.mono ?_⟩
    · push_cast
      linarith
    · push_cast
      nlinarith

/-- **The upper bound from the count of the roundings**: a lower bound within `e^lam`,
`lam ≤ K u ≤ 1/2`, and `glaisherUpper` enclose the number within `e^((2K + 4)u)`. -/
theorem LLow.toEncl {V : ℕ} [NeZero V] {f : AzFloat}
    {F lam : ℝ} (hf : LLow f F lam) {K : ℕ} (hK : lam ≤ K * (1 / 2 : ℝ) ^ V)
    (hK2 : (K : ℝ) * (1 / 2 : ℝ) ^ V ≤ 1 / 2) :
    LEncl (f, glaisherUpper V f K) F (2 * K * (1 / 2 : ℝ) ^ V + 4 * (1 / 2 : ℝ) ^ V) := by
  obtain ⟨fv, hfv, f0, f1, f2⟩ := hf
  obtain ⟨u, hud⟩ : ∃ u : ℝ, u = (1 / 2 : ℝ) ^ V := ⟨_, rfl⟩
  have hshift : (ofAzNat (AzNat.ofNat (2 * K)) <<< AzInt.ofInt (-(V : ℤ))).toVal
      = some ((2 * K * u : ℝ) : EReal) := by
    rw [toVal_shiftLeft_of_toVal (toVal_ofAzNat_ofNat (2 * K)), AzInt.toInt_ofInt, zpow_neg,
      zpow_natCast, hud, one_div, inv_pow]
    push_cast
    rfl
  rw [← hud] at hK hK2 ⊢
  have hu0 : 0 < u := by rw [hud]; positivity
  have hKu0 : 0 ≤ (K : ℝ) * u := by positivity
  obtain ⟨cv, hcv, hc1, hc2⟩ := addCeiling_abs toVal_one' hshift V
  rw [← hud, abs_of_pos (by linarith only [hKu0])] at hc2
  obtain ⟨hi, hhi, hh1, hh2⟩ := mulCeiling_abs hfv hcv V
  have hcv0 : 0 < cv := by linarith only [hc1, hKu0]
  rw [← hud, abs_of_pos (mul_pos f0 hcv0)] at hh2
  have hexp : Real.exp ((K : ℝ) * u) ≤ 1 + 2 * (K * u) := by
    rcases hKu0.eq_or_lt with h | h
    · rw [← h]; simp
    · have h2 := (Real.exp_bound_div_one_sub_of_interval' h (by linarith only [hK2])).le
      have h3 : 1 / (1 - (K : ℝ) * u) ≤ 1 + 2 * (K * u) := by
        rw [div_le_iff₀ (by linarith only [hK2])]
        nlinarith
      linarith only [h2, h3]
  refine ⟨fv, hi, hfv, hhi, f0, f1, ?_, ?_⟩
  · -- `F ≤ fv e^lam ≤ fv (1 + 2Ku) ≤ fv cv ≤ hi`
    have h1 : Real.exp lam ≤ cv :=
      (Real.exp_le_exp.mpr hK).trans (hexp.trans (by linarith only [hc1]))
    exact (f2.trans (mul_le_mul_of_nonneg_left h1 f0.le)).trans hh1
  · -- `hi ≤ fv (1 + 2Ku)(1 + 2u)²`
    have e1 : 1 + 2 * (K * u) ≤ Real.exp (2 * K * u) := by
      linarith only [Real.add_one_le_exp (2 * (K : ℝ) * u)]
    have e2 : 1 + 2 * u ≤ Real.exp (2 * u) := by linarith only [Real.add_one_le_exp (2 * u)]
    have hc3 : cv ≤ (1 + 2 * (K * u)) * (1 + 2 * u) := by linarith only [hc2]
    have hh3 : hi ≤ fv * cv * (1 + 2 * u) := by linarith only [hh2]
    have p1 : (0 : ℝ) < 1 + 2 * u := by linarith only [hu0]
    have p2 : (0 : ℝ) < 1 + 2 * (K * u) := by linarith only [hKu0]
    calc hi ≤ fv * cv * (1 + 2 * u) := hh3
      _ ≤ fv * ((1 + 2 * (K * u)) * (1 + 2 * u)) * (1 + 2 * u) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc3 f0.le) p1.le
      _ = fv * ((1 + 2 * (K * u)) * ((1 + 2 * u) * (1 + 2 * u))) := by ring
      _ ≤ fv * (Real.exp (2 * K * u) * (Real.exp (2 * u) * Real.exp (2 * u))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul e1 (mul_le_mul e2 e2 p1.le (Real.exp_pos _).le)
            (mul_pos p1 p1).le (Real.exp_pos _).le) f0.le
      _ = fv * Real.exp (2 * K * u + 4 * u) := by
          rw [← Real.exp_add, ← Real.exp_add]
          ring_nf

/-- **The enclosures of `n!` and of `∏_{k<n} k!`.** -/
theorem glaisherProd_lencl {V : ℕ} [NeZero V] (hu : (1 / 2 : ℝ) ^ V ≤ 1 / 8) (n : ℕ)
    (hn : 3 * (n : ℝ) ^ 2 * (1 / 2 : ℝ) ^ V ≤ 1 / 2) (hn1 : 1 ≤ n) :
    LEncl (glaisherProd V n).1 (n ! : ℝ) (6 * n * (1 / 2 : ℝ) ^ V + 4 * (1 / 2 : ℝ) ^ V) ∧
      LEncl (glaisherProd V n).2 (∏ l ∈ range n, (l ! : ℝ))
        (6 * (n : ℝ) ^ 2 * (1 / 2 : ℝ) ^ V + 4 * (1 / 2 : ℝ) ^ V) := by
  have hu0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ V := by positivity
  have hN1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  obtain ⟨hf, hw⟩ := glaisherProdLo_llow hu n 0 one one 0 0 le_rfl
    (by simpa using LLow.exact toVal_one' one_pos) (by simpa using LLow.exact toVal_one' one_pos)
  rw [zero_add] at hf hw
  have hNN : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    have h1 : (n : ℝ) * 1 ≤ n * n := mul_le_mul_of_nonneg_left hN1 (Nat.cast_nonneg n)
    rw [mul_one, ← sq] at h1
    exact h1
  have hF := hf.toEncl (K := 3 * n) (le_of_eq (by push_cast; ring)) (by
    push_cast
    have := mul_le_mul_of_nonneg_right hNN hu0
    linarith only [this, hn])
  have hW := hw.toEncl (K := 3 * n * n) (le_of_eq (by push_cast; ring)) (by
    push_cast
    linarith only [hn, show 3 * (n : ℝ) * n * (1 / 2 : ℝ) ^ V = 3 * (n : ℝ) ^ 2 * (1 / 2 : ℝ) ^ V
      by ring])
  unfold glaisherProd
  refine ⟨hF.mono (le_of_eq ?_), hW.mono (le_of_eq ?_)⟩
  · push_cast
    ring
  · push_cast
    ring

/-! ### The terms -/

/-- **A term on enclosures**: from an enclosure of `n^(−2k−2)`, the term `τ_k`, with `24 u`
more of relative width. -/
theorem glaisherTermEncl_lencl {V : ℕ} [NeZero V] (hu : (1 / 2 : ℝ) ^ V ≤ 1 / 8) {n M k : ℕ}
    (hn : 1 ≤ n) (hk : 1 ≤ k) (hkM : k ≤ M) {p : Encl} {lam : ℝ}
    (hp : LEncl p (1 / (n : ℝ) ^ (2 * (k + 1))) lam) :
    LEncl (glaisherTermEncl V (AzNat.tangentNumbers (M + 1)) (Encl.nat (n * n)) k p)
      (DLMF.glaisherTau n k) (lam + 24 * (1 / 2 : ℝ) ^ V) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 := psiTermEncl_width hu (M := M + 1) (k := k + 1) (by omega) (by omega) hp
  have h2 := (h1.mul hu (LEncl.nat (n := n * n) (Nat.mul_pos hn hn))).div hu
    (LEncl.nat (n := 2 * k * (2 * k + 1)) (by positivity))
  unfold glaisherTermEncl
  have hval : psiCoeffT (k + 1) / (n : ℝ) ^ (2 * (k + 1)) * ((n * n : ℕ) : ℝ)
      / ((2 * k * (2 * k + 1) : ℕ) : ℝ) = DLMF.glaisherTau n k := by
    unfold DLMF.glaisherTau
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add]
    push_cast
    field_simp
  rw [hval] at h2
  exact h2.mono (le_of_eq (by ring))

/-- **The terms envelop the remainder**: `glaisherSeq n − C` is the alternating partial sum
before the index `k` plus a remainder of the sign of the term `k`, bounded by it. -/
theorem glaisher_alt {n : ℕ} (hn : 1 ≤ n) {k : ℕ} (hk : 1 ≤ k) :
    ∃ r : ℝ, DLMF.glaisherSeq n - DLMF.glaisherC = altPartial (DLMF.glaisherTau n) k + r ∧
      0 ≤ (-1) ^ (k + 1) * r ∧ |r| ≤ DLMF.glaisherTau n k := by
  have hsum : ∀ k, 1 ≤ k →
      altPartial (DLMF.glaisherTau n) k = ∑ s ∈ Icc 2 k, DLMF.exTerm s n := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => simp [altPartial]
    | succ k hk ih =>
      rw [altPartial_succ hk, ih, sum_Icc_succ_top (by omega), DLMF.exTerm_succ_eq_tau hn hk]
  obtain ⟨hs, -, -, habs⟩ := DLMF.dlmf_2_10_5_bound (m := k + 1) (by omega) hn
  refine ⟨DLMF.jlogR (k + 1) n, ?_, hs, ?_⟩
  · rw [hsum k hk]
    exact DLMF.glaisherSeq_sub_eq hn hk
  · rw [DLMF.exTerm_succ_eq_tau hn hk, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_pos (DLMF.glaisherTau_pos hn hk)] at habs
    exact habs

/-! ### The width -/

noncomputable def gkA1 (N V : ℝ) : ℝ := 2 ^ 42 * (V + 2 * N ^ 3 + 10) ^ 5 + 180 * N ^ 2
noncomputable def gkA2 (N V : ℝ) : ℝ := 2 ^ 42 * (V + 2 * N + 10) ^ 5
noncomputable def gkBa (N V : ℝ) : ℝ := N + gkA2 N V
noncomputable def gkA4 (N V : ℝ) : ℝ :=
  gkA2 N V * (26 * N ^ 2) + gkBa N V * (24 * N ^ 2) + 4 * gkBa N V * (26 * N ^ 2)
noncomputable def gkB1 (N V : ℝ) : ℝ := 3 * N ^ 3 + gkA1 N V + gkA4 N V
noncomputable def gkA5 (N V : ℝ) : ℝ := gkA1 N V + gkA4 N V + 4 * gkB1 N V
noncomputable def gkB3 (N V : ℝ) : ℝ := 4 * N ^ 3 + gkA5 N V
noncomputable def gkA7 (N V : ℝ) : ℝ := gkA5 N V + 4 * gkB3 N V
noncomputable def gkAN (N : ℝ) : ℝ :=
  N * (32 * (12 * N + 18) + 4 * (33 * N + 33)) + 2 * (33 * N + 33) + 1
noncomputable def gkB4 (N V β Cc : ℝ) : ℝ := Cc + gkA7 N V + gkAN N + 2 * β
noncomputable def gkA6 (N V β Cc : ℝ) : ℝ := gkA7 N V + gkAN N + 4 * gkB4 N V β Cc

/-- The last term of the expansion at level `w`. -/
noncomputable def glaisherBeta (w : ℕ) : ℝ :=
  |DLMF.glaisherTerm (glaisherArg w) (glaisherTerms w)|

/-- The working precision at level `w`. -/
def glaisherPrec (w : ℕ) : ℕ := w + 2 * (glaisherArg w).log2 + 64

/-- **The width of the enclosure of `ln A` at level `w`.** -/
noncomputable def glaisherDelta (w : ℕ) : ℝ :=
  2 * glaisherBeta w
    + gkA6 (glaisherArg w) (glaisherPrec w) (glaisherBeta w) |DLMF.glaisherC| * (1 / 2 : ℝ) ^ w

theorem glaisherArg_ge (w : ℕ) : 24 ≤ glaisherArg w := by
  unfold glaisherArg glaisherTerms
  omega

/-- **The enclosure of `ln A`**: it contains `C` and is at most `glaisherDelta w` wide. -/
theorem glaisherKinkelinLnEncl_aencl {w : ℕ} (hw : 64 ≤ w) :
    AEncl (glaisherKinkelinLnEncl w) DLMF.glaisherC (glaisherDelta w) := by
  obtain ⟨j, hj⟩ : ∃ j : ℕ, j = glaisherTerms w := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = glaisherArg w := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V : ℕ, V = w + 2 * n.log2 + 64 := ⟨_, rfl⟩
  have hj1 : 1 ≤ j := by rw [hj]; unfold glaisherTerms; omega
  have hn24 : 24 ≤ n := by rw [hn]; exact glaisherArg_ge w
  have hn1 : 1 ≤ n := by omega
  have hV64 : 64 ≤ V := by omega
  have hVw : w ≤ V := by omega
  have : NeZero V := ⟨by omega⟩
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (1 / 2 : ℝ) ^ V := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : ℝ, U = (1 / 2 : ℝ) ^ w := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = (n : ℝ) := ⟨_, rfl⟩
  obtain ⟨Vr, hVr⟩ : ∃ Vr : ℝ, Vr = (V : ℝ) := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hu]; positivity
  have hU0 : 0 < U := by rw [hU]; positivity
  have huU : u ≤ U := by
    rw [hu, hU]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hVw
  have hU1 : U ≤ 1 := by rw [hU]; exact pow_le_one₀ (by norm_num) (by norm_num)
  have hu8 : (1 / 2 : ℝ) ^ V ≤ 1 / 8 := half_pow_le_eighth (by omega)
  have hN1 : 1 ≤ N := by rw [hN]; exact_mod_cast hn1
  have hVr0 : 0 ≤ Vr := by rw [hVr]; exact Nat.cast_nonneg V
  -- `N² u` is tiny
  have hN2u : N ^ 2 * u ≤ 1 / 288 := by
    have h1 : (n : ℝ) < 2 ^ (n.log2 + 1) := by exact_mod_cast Nat.lt_log2_self
    have h2 : N ^ 2 ≤ 4 * (2 : ℝ) ^ (2 * n.log2) := by
      have h3 : N ^ 2 ≤ ((2 : ℝ) ^ (n.log2 + 1)) ^ 2 :=
        pow_le_pow_left₀ (by linarith) (by rw [hN]; exact h1.le) 2
      have h4 : ((2 : ℝ) ^ (n.log2 + 1)) ^ 2 = 4 * (2 : ℝ) ^ (2 * n.log2) := by
        rw [← pow_mul, show (n.log2 + 1) * 2 = 2 * n.log2 + 2 by ring, pow_add]
        ring
      rw [h4] at h3
      exact h3
    have h5 : u = (1 / 2 : ℝ) ^ w * (1 / 2 : ℝ) ^ (2 * n.log2) * (1 / 2 : ℝ) ^ 64 := by
      rw [hu, hV, pow_add, pow_add]
    have h6 : (2 : ℝ) ^ (2 * n.log2) * (1 / 2 : ℝ) ^ (2 * n.log2) = 1 := by
      rw [← mul_pow]
      norm_num
    have h7 : N ^ 2 * u ≤ 4 * (2 : ℝ) ^ (2 * n.log2) * u :=
      mul_le_mul_of_nonneg_right h2 hu0.le
    have h8 : 4 * (2 : ℝ) ^ (2 * n.log2) * u
        = 4 * ((2 : ℝ) ^ (2 * n.log2) * (1 / 2 : ℝ) ^ (2 * n.log2)) * (1 / 2 : ℝ) ^ w
          * (1 / 2 : ℝ) ^ 64 := by
      rw [h5]
      ring
    rw [h8, h6, ← hU] at h7
    have h9 : (1 / 2 : ℝ) ^ 64 ≤ 1 / 1152 := by norm_num
    have h10 : 4 * 1 * U * (1 / 2 : ℝ) ^ 64 ≤ 4 * 1 * 1 * (1 / 1152) := by
      apply mul_le_mul _ h9 (by positivity) (by positivity)
      linarith
    linarith
  -- the products
  obtain ⟨hF, hW⟩ := glaisherProd_lencl hu8 n (by
    rw [← hu, ← hN]
    linarith only [hN2u]) hn1
  rw [← hu, ← hN] at hF hW
  obtain ⟨FW, hFW⟩ : ∃ FW : Encl × Encl, FW = glaisherProd V n := ⟨_, rfl⟩
  rw [← hFW] at hF hW
  have hHq := ((LEncl.powBin hu8 hF hn1).div hu8 hW).mono
    (lam' := 36 * (N ^ 2 * u)) (by
      rw [← hu, ← hN]
      have a0 : N ≤ N ^ 2 := by nlinarith
      have a1 : N * u ≤ N ^ 2 * u := mul_le_mul_of_nonneg_right a0 hu0.le
      have a2 : u ≤ N * u := le_mul_of_one_le_left hu0.le hN1
      have hN24 : (24 : ℝ) ≤ N := by rw [hN]; exact_mod_cast hn24
      have a3 : 24 * (N * u) ≤ N * (N * u) :=
        mul_le_mul_of_nonneg_right hN24 (mul_nonneg (by linarith only [hN1]) hu0.le)
      have a4 : 24 * u ≤ N * u := mul_le_mul_of_nonneg_right hN24 hu0.le
      linarith only [a1, a2, a3, a4, show N * (N * u) = N ^ 2 * u by ring])
  -- the sum of `k ln k`
  obtain ⟨Sk, hSk⟩ : ∃ Sk : ℝ, Sk = ∑ k ∈ Icc 1 n, (k : ℝ) * Real.log k := ⟨_, rfl⟩
  obtain ⟨hSk0, hSkN⟩ := DLMF.sum_mul_log_bounds n
  rw [← hSk] at hSk0
  rw [← hSk, ← hN] at hSkN
  have hlogH : Real.log ((n ! : ℝ) ^ n / ∏ k ∈ range n, (k ! : ℝ)) = Sk := by
    rw [hSk, DLMF.sum_mul_log_eq_log_hyper]
  have hN30 : (0 : ℝ) ≤ N ^ 3 := by positivity
  have hlnH := hHq.lnOfEncl (by positivity) (by linarith) (G := N ^ 3)
    (by rw [hlogH, abs_of_nonneg hSk0]; exact hSkN) hV64
  rw [hlogH] at hlnH
  have hlnW1 : lnW (N ^ 3) V ≤ 2 ^ 42 * (Vr + 2 * N ^ 3 + 10) ^ 5 * U := by
    unfold lnW
    rw [← hu, ← hVr]
    exact mul_le_mul_of_nonneg_left huU (by positivity)
  have hN2U : N ^ 2 * u ≤ N ^ 2 * U := mul_le_mul_of_nonneg_left huU (by positivity)
  have hlnH' := hlnH.mono (ε' := gkA1 N Vr * U) (by
    unfold gkA1
    linarith only [hlnW1, hN2U])
  -- `ln n`
  have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
  have hlognN : Real.log n ≤ N := by
    rw [hN]
    have := Real.log_le_sub_one_of_pos (by exact_mod_cast hn1 : (0 : ℝ) < n)
    linarith
  have hL := (LEncl.nat (n := n) hn1).lnOfEncl le_rfl (by norm_num) (G := N)
    (by rw [abs_of_nonneg hlogn0]; exact hlognN) hV64
  have hlnW2 : lnW N V ≤ 2 ^ 42 * (Vr + 2 * N + 10) ^ 5 * U := by
    unfold lnW
    rw [← hu, ← hVr]
    exact mul_le_mul_of_nonneg_left huU (by positivity)
  have hL' := hL.mono (ε' := gkA2 N Vr * U) (by
    unfold gkA2
    linarith only [hlnW2])
  -- the coefficient `(6n² + 6n + 1)/12`
  obtain ⟨cv, hcv⟩ : ∃ cv : ℝ, cv = ((6 * n * n + 6 * n + 1 : ℕ) : ℝ) / ((12 : ℕ) : ℝ) :=
    ⟨_, rfl⟩
  have hcvN : cv = (6 * N ^ 2 + 6 * N + 1) / 12 := by
    rw [hcv, hN]
    push_cast
    ring
  have hcv0 : 0 ≤ cv := by rw [hcvN]; positivity
  have hcv2 : cv ≤ 2 * N ^ 2 := by
    rw [hcvN]
    nlinarith
  have hc := ((LEncl.nat (n := 6 * n * n + 6 * n + 1) (Nat.succ_pos _)).div (w := V) hu8
    (LEncl.nat (n := 12) (by norm_num)))
  rw [← hcv, ← hu] at hc
  obtain ⟨cl, ch, hcl, hch, hcl0, hcl1, hch1, hcw⟩ :=
    hc.toA (by positivity) (by
      have h64 := half_pow_le_of_64 hV64
      have : (1 : ℝ) / 2 ^ 64 ≤ 1 / 12 := by norm_num
      linarith only [h64, hu, this])
  have hc' : AEncl0 (Encl.div V (Encl.nat (6 * n * n + 6 * n + 1)) (Encl.nat 12)) cv
      (24 * N ^ 2 * U) := by
    refine ⟨cl, ch, hcl, hch, hcl0, hcl1, hch1, hcw.trans ?_⟩
    have h1 : cv * u ≤ 2 * N ^ 2 * U :=
      mul_le_mul hcv2 huU hu0.le (by positivity)
    linarith only [h1]
  have hA20 : 0 ≤ gkA2 N Vr := by unfold gkA2; positivity
  have hBa0 : 0 ≤ gkBa N Vr := by unfold gkBa; linarith
  have hA2U : gkA2 N Vr * U ≤ gkA2 N Vr := mul_le_of_le_one_right hA20 hU1
  have hN2U1 : 24 * N ^ 2 * U ≤ 24 * N ^ 2 := mul_le_of_le_one_right (by positivity) hU1
  have hcL := AEncl.mulPos (W := V) hL' hc' (Ba := gkBa N Vr) (Bb := 26 * N ^ 2)
    (by rw [abs_of_nonneg hlogn0]; unfold gkBa; linarith only [hlognN, hA2U])
    (by linarith only [hcv2, hN2U1])
  rw [← hu] at hcL
  have hcL' := hcL.mono (ε' := gkA4 N Vr * U) (by
    have h1 : 4 * gkBa N Vr * (26 * N ^ 2) * u ≤ 4 * gkBa N Vr * (26 * N ^ 2) * U :=
      mul_le_mul_of_nonneg_left huU (by positivity)
    have e : gkA4 N Vr * U = gkA2 N Vr * U * (26 * N ^ 2) + gkBa N Vr * (24 * N ^ 2 * U)
        + 4 * gkBa N Vr * (26 * N ^ 2) * U := by
      unfold gkA4
      ring
    rw [e]
    linarith only [h1])
  -- the main part
  have hprod0 : 0 ≤ Real.log n * cv := mul_nonneg hlogn0 hcv0
  have hprodN : Real.log n * cv ≤ 2 * N ^ 3 := by
    have := mul_le_mul hlognN hcv2 hcv0 (by linarith)
    linarith only [this, show N * (2 * N ^ 2) = 2 * N ^ 3 by ring]
  have hA10 : 0 ≤ gkA1 N Vr := by unfold gkA1; positivity
  have hA40 : 0 ≤ gkA4 N Vr := by unfold gkA4; positivity
  have hA1U : gkA1 N Vr * U ≤ gkA1 N Vr := mul_le_of_le_one_right hA10 hU1
  have hA4U : gkA4 N Vr * U ≤ gkA4 N Vr := mul_le_of_le_one_right hA40 hU1
  have habs1 : |Sk - Real.log n * cv| ≤ 3 * N ^ 3 := by
    rw [abs_le]
    constructor
    · linarith only [hSk0, hprodN, hN30]
    · linarith only [hSkN, hprod0, hN30]
  have hmain := hlnH'.sub (w := V) hcL' (B := gkB1 N Vr) (by
    unfold gkB1
    linarith only [habs1, hA1U, hA4U])
  rw [← hu] at hmain
  have hB10 : 0 ≤ gkB1 N Vr := by unfold gkB1; linarith
  have hmain' := hmain.mono (ε' := gkA5 N Vr * U) (by
    have h1 : 4 * gkB1 N Vr * u ≤ 4 * gkB1 N Vr * U :=
      mul_le_mul_of_nonneg_left huU (by linarith)
    have e : gkA5 N Vr * U = gkA1 N Vr * U + gkA4 N Vr * U + 4 * gkB1 N Vr * U := by
      unfold gkA5
      ring
    rw [e]
    linarith only [h1])
  -- the sequence `glaisherSeq n`: adding `n²/4`
  have hn8 : n = 8 * j := by rw [hn, hj]; rfl
  have hquarter : ((n * n / 4 : ℕ) : ℝ) = N ^ 2 / 4 := by
    have h1 : n * n = 4 * (16 * j * j) := by rw [hn8]; ring
    rw [h1, Nat.mul_div_cancel_left _ (by norm_num : 0 < 4), hN, hn8]
    push_cast
    ring
  have hA50 : 0 ≤ gkA5 N Vr := by unfold gkA5; linarith
  have hA5U : gkA5 N Vr * U ≤ gkA5 N Vr := mul_le_of_le_one_right hA50 hU1
  have hN23 : N ^ 2 / 4 ≤ N ^ 3 := by
    have h1 : N ^ 2 * 1 ≤ N ^ 2 * N := mul_le_mul_of_nonneg_left hN1 (sq_nonneg N)
    have h2 : N ^ 2 * N = N ^ 3 := by ring
    have h3 := sq_nonneg N
    linarith only [h1, h2, h3]
  have hX := hmain'.add (w := V) (AEncl.natEncl (n * n / 4)) (B := gkB3 N Vr) (by
    rw [hquarter]
    have : |Sk - Real.log n * cv + N ^ 2 / 4| ≤ 4 * N ^ 3 := by
      have h1 := abs_add_le (Sk - Real.log n * cv) (N ^ 2 / 4)
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ N ^ 2 / 4)] at h1
      linarith only [h1, habs1, hN23]
    unfold gkB3
    linarith only [this, hA5U])
  have hseq : Sk - Real.log n * cv + ((n * n / 4 : ℕ) : ℝ) = DLMF.glaisherSeq n := by
    rw [hquarter, DLMF.glaisherSeq, ← hSk, hcvN, hN]
    ring
  rw [hseq, ← hu] at hX
  have hB30 : 0 ≤ gkB3 N Vr := by unfold gkB3; linarith
  have hX' := hX.mono (ε' := gkA7 N Vr * U) (by
    have h1 : 4 * gkB3 N Vr * u ≤ 4 * gkB3 N Vr * U :=
      mul_le_mul_of_nonneg_left huU (by linarith)
    have e : gkA7 N Vr * U = gkA5 N Vr * U + 4 * gkB3 N Vr * U := by
      unfold gkA7
      ring
    rw [e]
    linarith only [h1])
  -- the terms of the expansion
  have hjn : j ≤ n := by omega
  have hjN : (j : ℝ) ≤ N := by rw [hN]; exact_mod_cast hjn
  have hj0 : (1 : ℝ) ≤ j := by exact_mod_cast hj1
  have hNN : N ≤ N ^ 2 := by
    have h1 : N * 1 ≤ N * N := mul_le_mul_of_nonneg_left hN1 (by linarith only [hN1])
    rw [mul_one, ← sq] at h1
    exact h1
  have hNu : N * u ≤ 1 / 288 := (mul_le_mul_of_nonneg_right hNN hu0.le).trans hN2u
  have hu288 : u ≤ 1 / 288 := (le_mul_of_one_le_left hu0.le (one_le_pow₀ hN1)).trans hN2u
  obtain ⟨Lam, hLam⟩ : ∃ Lam : ℝ, Lam = (12 * (j : ℝ) + 18) * u := ⟨_, rfl⟩
  have hLamN : Lam ≤ (12 * N + 18) * u := by
    rw [hLam]
    exact mul_le_mul_of_nonneg_right (by linarith) hu0.le
  have hLam2 : Lam ≤ 1 / 2 := by linarith only [hLamN, hNu, hu288]
  have hLam0 : 0 ≤ Lam := by rw [hLam]; positivity
  have hinv2 : LEncl (Encl.div V (Encl.exact one) (Encl.nat (n * n))) (1 / N ^ 2)
      (0 + 0 + 6 * u) := by
    have := (LEncl.exact toVal_one' one_pos).div (w := V) hu8
      (LEncl.nat (n := n * n) (Nat.mul_pos hn1 hn1))
    rw [hu, hN]
    convert this using 2
    push_cast
    ring
  have hp1 : LEncl (Encl.div V (Encl.exact one) (Encl.nat (n * n * (n * n))))
      (1 / (n : ℝ) ^ (2 * (1 + 1))) (0 + 0 + 6 * u) := by
    have := (LEncl.exact toVal_one' one_pos).div (w := V) hu8
      (LEncl.nat (n := n * n * (n * n)) (Nat.mul_pos (Nat.mul_pos hn1 hn1) (Nat.mul_pos hn1 hn1)))
    rw [hu]
    convert this using 2
    push_cast
    ring
  have hn0' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hS := altSumLoop_width (V := V) (M := j) (t := DLMF.glaisherTau n)
    (q := fun k => 1 / (n : ℝ) ^ (2 * (k + 1)))
    (term := glaisherTermEncl V (AzNat.tangentNumbers (j + 1)) (Encl.nat (n * n)))
    (T := 16) (B := 33 * N + 33) (Lam := Lam) (c := 24)
    (μ := DLMF.glaisherSeq n - DLMF.glaisherC) (i2 := 1 / N ^ 2) hu8 hinv2
    (fun k => by
      rw [show 2 * (k + 1 + 1) = 2 * (k + 1) + 2 by ring, pow_add, hN]
      field_simp)
    (toVal_lnGammaTol w) hLam2 (by norm_num) (by norm_num)
    (fun k hk _ => DLMF.glaisherTau_pos hn1 hk)
    (fun k hk hkj => DLMF.glaisherTau_le_sixteen hk (by omega))
    (fun k p lam hk hkj hp => glaisherTermEncl_lencl hu8 hn1 hk hkj hp)
    (fun k hk _ => glaisher_alt hn1 hk)
    (by rw [← hu]; linarith only [hNu, hu288])
    (by
      have h1 : (j : ℝ) * (16 + 2 * 16 * Lam + 1) ≤ j * 33 :=
        mul_le_mul_of_nonneg_left (by linarith only [hLam2]) (by linarith only [hj0])
      linarith only [h1, hjN])
    (j - 1) 1 _ (Encl.exact zero) (0 + 0 + 6 * u) 0 le_rfl (by omega) hp1 (by positivity)
    (by
      rw [← hu, hLam, Nat.cast_sub hj1]
      push_cast
      linarith)
    (by simpa [altPartial] using AEncl.exact toVal_zero') (by simp)
  rw [← hu] at hS
  obtain ⟨βv, hβv⟩ : ∃ βv : ℝ, βv = glaisherBeta w := ⟨_, rfl⟩
  have hτβ : DLMF.glaisherTau n j = βv := by
    rw [hβv, glaisherBeta, ← hn, ← hj, DLMF.glaisherTau_eq_abs hn1 hj1]
  have hβ0 : 0 ≤ βv := by rw [← hτβ]; exact (DLMF.glaisherTau_pos hn1 hj1).le
  rw [hτβ] at hS
  have hS' := hS.mono (ε' := gkAN N * U + 2 * βv) (by
    have hj1' : (((j - 1 : ℕ) : ℕ) : ℝ) ≤ N := by
      have : j - 1 ≤ n := by omega
      rw [hN]
      exact_mod_cast this
    have hstep : 2 * 16 * Lam + 4 * (33 * N + 33) * u
        ≤ (32 * (12 * N + 18) + 4 * (33 * N + 33)) * U := by
      have h1 : (12 * N + 18) * u ≤ (12 * N + 18) * U :=
        mul_le_mul_of_nonneg_left huU (by linarith)
      have h2 : (33 * N + 33) * u ≤ (33 * N + 33) * U :=
        mul_le_mul_of_nonneg_left huU (by linarith)
      linarith only [hLamN, h1, h2]
    have hstep0 : 0 ≤ 2 * 16 * Lam + 4 * (33 * N + 33) * u := by positivity
    have h3 : ((j - 1 : ℕ) : ℝ) * (2 * 16 * Lam + 4 * (33 * N + 33) * u)
        ≤ N * ((32 * (12 * N + 18) + 4 * (33 * N + 33)) * U) :=
      mul_le_mul hj1' hstep hstep0 (by linarith)
    have h4 : max ((1 / 2 : ℝ) ^ (w + 16)) (2 * βv) ≤ U + 2 * βv := by
      have : (1 / 2 : ℝ) ^ (w + 16) ≤ U := by
        rw [hU]
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      exact max_le (by linarith) (by linarith)
    have h5 : 2 * (33 * N + 33) * u ≤ 2 * (33 * N + 33) * U :=
      mul_le_mul_of_nonneg_left huU (by linarith)
    have e : gkAN N * U = N * ((32 * (12 * N + 18) + 4 * (33 * N + 33)) * U)
        + 2 * (33 * N + 33) * U + U := by
      unfold gkAN
      ring
    rw [e]
    linarith only [h3, h4, h5])
  -- the difference
  obtain ⟨Cc, hCc⟩ : ∃ Cc : ℝ, Cc = |DLMF.glaisherC| := ⟨_, rfl⟩
  have hA70 : 0 ≤ gkA7 N Vr := by unfold gkA7; linarith
  have hAN0 : 0 ≤ gkAN N := by unfold gkAN; positivity
  have hA7U : gkA7 N Vr * U ≤ gkA7 N Vr := mul_le_of_le_one_right hA70 hU1
  have hANU : gkAN N * U ≤ gkAN N := mul_le_of_le_one_right hAN0 hU1
  have hval : DLMF.glaisherSeq n - (DLMF.glaisherSeq n - DLMF.glaisherC) = DLMF.glaisherC := by
    ring
  have hfin := hX'.sub (w := V) hS' (B := gkB4 N Vr βv Cc) (by
    rw [hval, ← hCc]
    unfold gkB4
    linarith only [hA7U, hANU])
  rw [hval, ← hu] at hfin
  have hCc0 : 0 ≤ Cc := by rw [hCc]; exact abs_nonneg _
  have hB40 : 0 ≤ gkB4 N Vr βv Cc := by unfold gkB4; linarith
  have hfin' := hfin.mono (ε' := 2 * βv + gkA6 N Vr βv Cc * U) (by
    have h1 : 4 * gkB4 N Vr βv Cc * u ≤ 4 * gkB4 N Vr βv Cc * U :=
      mul_le_mul_of_nonneg_left huU (by linarith)
    have e : gkA6 N Vr βv Cc * U = gkA7 N Vr * U + gkAN N * U + 4 * gkB4 N Vr βv Cc * U := by
      unfold gkA6
      ring
    rw [e]
    linarith only [h1])
  have hδ : glaisherDelta w = 2 * βv + gkA6 N Vr βv Cc * U := by
    unfold glaisherDelta glaisherPrec
    rw [← hβv, ← hn, ← hV, ← hCc, ← hU, hN, hVr]
  rw [hδ]
  unfold glaisherKinkelinLnEncl glaisherKinkelinLnEnclWith
  dsimp only
  rw [← hj, ← hn, ← hV, ← hFW]
  exact hfin'

/-! ### The width tends to `0` -/

theorem tendsto_glaisherTerms : Tendsto glaisherTerms atTop atTop :=
  tendsto_atTop.mpr fun b => (eventually_ge_atTop (12 * b)).mono fun w hw => by
    unfold glaisherTerms
    omega

theorem glaisherBeta_le (w : ℕ) :
    glaisherBeta w ≤ 16 * ((glaisherTerms w : ℝ) + 1) ^ 2 * (1 / 4 : ℝ) ^ glaisherTerms w := by
  unfold glaisherBeta
  refine DLMF.abs_glaisherTerm_le ?_ ?_
  · unfold glaisherTerms
    omega
  · unfold glaisherArg glaisherTerms
    omega

theorem tendsto_glaisherBeta : Tendsto glaisherBeta atTop (𝓝 0) := by
  have hg : Tendsto (fun j : ℕ => 16 * ((j : ℝ) + 1) ^ 2 * (1 / 2 : ℝ) ^ j) atTop (𝓝 0) :=
    (((PB.natCast.add (PB.const 1)).pow 2).const_mul 16).tendsto
  refine squeeze_zero (fun w => abs_nonneg _) (fun w => ?_) (hg.comp tendsto_glaisherTerms)
  refine (glaisherBeta_le w).trans ?_
  have : (1 / 4 : ℝ) ^ glaisherTerms w ≤ (1 / 2 : ℝ) ^ glaisherTerms w :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  exact mul_le_mul_of_nonneg_left this (by positivity)

theorem pb_glaisherArg : PB fun w : ℕ => ((glaisherArg w : ℕ) : ℝ) := by
  refine ((PB.natCast.const_mul 8).add (PB.const 24)).of_abs_le fun w => ?_
  have h : glaisherArg w ≤ 8 * w + 24 := by
    unfold glaisherArg glaisherTerms
    omega
  have h' : ((glaisherArg w : ℕ) : ℝ) ≤ 8 * (w : ℝ) + 24 := by exact_mod_cast h
  rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (by positivity)]
  exact h'

theorem pb_glaisherPrec : PB fun w : ℕ => ((glaisherPrec w : ℕ) : ℝ) := by
  refine ((PB.natCast.const_mul 17).add (PB.const 112)).of_abs_le fun w => ?_
  have h : glaisherPrec w ≤ 17 * w + 112 := by
    have h1 := log2_le_self (glaisherArg w)
    have h2 : glaisherArg w ≤ 8 * w + 24 := by
      unfold glaisherArg glaisherTerms
      omega
    unfold glaisherPrec
    omega
  have h' : ((glaisherPrec w : ℕ) : ℝ) ≤ 17 * (w : ℝ) + 112 := by exact_mod_cast h
  rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (by positivity)]
  exact h'

theorem pb_glaisherBeta : PB glaisherBeta := by
  refine (((PB.natCast.add (PB.const 4)).pow 2).const_mul 16).of_abs_le fun w => ?_
  have h1 := glaisherBeta_le w
  have h2 : (1 / 4 : ℝ) ^ glaisherTerms w ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h3 : ((glaisherTerms w : ℕ) : ℝ) + 1 ≤ (w : ℝ) + 4 := by
    have : glaisherTerms w + 1 ≤ w + 4 := by
      unfold glaisherTerms
      omega
    exact_mod_cast this
  have h4 : ((glaisherTerms w : ℝ) + 1) ^ 2 ≤ ((w : ℝ) + 4) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h3 2
  have h5 : 16 * ((glaisherTerms w : ℝ) + 1) ^ 2 * (1 / 4 : ℝ) ^ glaisherTerms w
      ≤ 16 * ((w : ℝ) + 4) ^ 2 * 1 :=
    mul_le_mul (by linarith) h2 (by positivity) (by positivity)
  rw [abs_of_nonneg (by unfold glaisherBeta; exact abs_nonneg _), abs_of_nonneg (by positivity)]
  linarith

/-- **The width of the enclosure of `ln A` tends to `0`.** -/
theorem tendsto_glaisherDelta : Tendsto glaisherDelta atTop (𝓝 0) := by
  have hN := pb_glaisherArg
  have hV := pb_glaisherPrec
  have hβ := pb_glaisherBeta
  have hN2 := hN.pow 2
  have hN3 := hN.pow 3
  have hA1 : PB fun w : ℕ => gkA1 (glaisherArg w) (glaisherPrec w) := by
    unfold gkA1
    exact ((((hV.add (hN3.const_mul 2)).add (PB.const 10)).pow 5).const_mul _).add
      (hN2.const_mul 180)
  have hA2 : PB fun w : ℕ => gkA2 (glaisherArg w) (glaisherPrec w) := by
    unfold gkA2
    exact (((hV.add (hN.const_mul 2)).add (PB.const 10)).pow 5).const_mul _
  have hBa : PB fun w : ℕ => gkBa (glaisherArg w) (glaisherPrec w) := by
    unfold gkBa
    exact hN.add hA2
  have hA4 : PB fun w : ℕ => gkA4 (glaisherArg w) (glaisherPrec w) := by
    unfold gkA4
    exact ((hA2.mul (hN2.const_mul 26)).add (hBa.mul (hN2.const_mul 24))).add
      ((hBa.const_mul 4).mul (hN2.const_mul 26))
  have hB1 : PB fun w : ℕ => gkB1 (glaisherArg w) (glaisherPrec w) := by
    unfold gkB1
    exact ((hN3.const_mul 3).add hA1).add hA4
  have hA5 : PB fun w : ℕ => gkA5 (glaisherArg w) (glaisherPrec w) := by
    unfold gkA5
    exact (hA1.add hA4).add (hB1.const_mul 4)
  have hB3 : PB fun w : ℕ => gkB3 (glaisherArg w) (glaisherPrec w) := by
    unfold gkB3
    exact (hN3.const_mul 4).add hA5
  have hA7 : PB fun w : ℕ => gkA7 (glaisherArg w) (glaisherPrec w) := by
    unfold gkA7
    exact hA5.add (hB3.const_mul 4)
  have hAN : PB fun w : ℕ => gkAN (glaisherArg w) := by
    unfold gkAN
    exact ((hN.mul ((((hN.const_mul 12).add (PB.const 18)).const_mul 32).add
      (((hN.const_mul 33).add (PB.const 33)).const_mul 4))).add
      (((hN.const_mul 33).add (PB.const 33)).const_mul 2)).add (PB.const 1)
  have hB4 : PB fun w : ℕ =>
      gkB4 (glaisherArg w) (glaisherPrec w) (glaisherBeta w) |DLMF.glaisherC| := by
    unfold gkB4
    exact (((PB.const _).add hA7).add hAN).add (hβ.const_mul 2)
  have hA6 : PB fun w : ℕ =>
      gkA6 (glaisherArg w) (glaisherPrec w) (glaisherBeta w) |DLMF.glaisherC| := by
    unfold gkA6
    exact (hA7.add hAN).add (hB4.const_mul 4)
  have := (tendsto_glaisherBeta.const_mul 2).add hA6.tendsto
  rw [mul_zero, add_zero] at this
  exact this

/-! ### The constant -/

/-- **`glaisherKinkelinCore` answers with a positive enclosure of `A`.** -/
theorem glaisherKinkelinCore_spec {w : ℕ} (hw : 64 ≤ w) {neg : Bool} {b : Encl}
    (h : glaisherKinkelinCore w = some (neg, b)) :
    IsEnclPos b ((if neg then -1 else 1) * DLMF.glaisherA) := by
  unfold glaisherKinkelinCore at h
  obtain ⟨g, hg, hgeq⟩ := Option.map_eq_some_iff.mp h
  rw [Prod.mk.injEq] at hgeq
  obtain ⟨rfl, rfl⟩ := hgeq
  have := gammaExpEncl_spec (glaisherKinkelinLnEncl_aencl hw).isEncl hw hg
  simpa [DLMF.glaisherA] using this

/-- **The core of `A` converges.** -/
theorem glaisherKinkelinCore_coreConv : CoreConv glaisherKinkelinCore DLMF.glaisherA := by
  obtain ⟨ht, hev⟩ := gammaExpEncl_eventually false DLMF.glaisherC tendsto_glaisherDelta
  simp only [Bool.false_eq_true, ↓reduceIte] at ht hev
  refine ⟨_, ht, ?_⟩
  filter_upwards [hev, eventually_ge_atTop 64] with w h1 hw
  obtain ⟨b, hb, hb1, hb2⟩ := h1 _ (glaisherKinkelinLnEncl_aencl hw)
  refine ⟨false, b, ?_, ?_, ?_⟩
  · unfold glaisherKinkelinCore
    rw [hb, Option.map_some]
  · simpa [DLMF.glaisherA] using hb1
  · simpa [DLMF.glaisherA] using hb2

/-- **`glaisherKinkelinPrecRoundFuel` is a convergent loop.** -/
theorem glaisherKinkelinPrecRoundFuel_zivCases (p : ℕ) [NeZero p] (mode : RoundingMode) :
    ZivCases (fun fuel => glaisherKinkelinPrecRoundFuel fuel p mode)
      (some ((DLMF.glaisherA : ℝ) : EReal)) p mode := by
  refine (ZivCases.of_core glaisherKinkelinCore_coreConv
    (fun w hw neg b hc => glaisherKinkelinCore_spec hw hc) p mode).congr fun fuel => ?_
  show glaisherKinkelinPrecRoundFuel fuel p mode = _
  unfold glaisherKinkelinPrecRoundFuel
  rw [ite_eq_right (NeZero.ne p)]
  rfl

/-- **The specification of the Glaisher–Kinkelin constant** (`ZivSpec`): sound at every fuel,
and complete in the limit of the fuel at every precision at which `A` is no rounding
boundary.  The sets of arguments with a known value are empty: whether `A` is rational is not
known. -/
theorem glaisherKinkelinPrecRoundFuel_zivSpec :
    ZivSpec (fun _ : Unit => some ((DLMF.glaisherA : ℝ) : EReal))
      (fun fuel _ p mode => glaisherKinkelinPrecRoundFuel fuel p mode) ∅ ∅ where
  sound := fun fuel _ p _ mode => (glaisherKinkelinPrecRoundFuel_zivCases p mode).sound fuel
  complete := fun _ p _ mode hB => (glaisherKinkelinPrecRoundFuel_zivCases p mode).complete hB
  dyadic := fun _ h => absurd h (Set.notMem_empty _)
  nondyadic := fun _ h => absurd h (Set.notMem_empty _)
  correct := fun _ h => by
    rcases h with h | h <;> exact absurd h (Set.notMem_empty _)

/-- **The Glaisher–Kinkelin constant is correctly rounded, or the fuel ran out**, at every
fuel. -/
theorem glaisherKinkelinPrecRoundFuel_eq_or (fuel p : ℕ) [NeZero p] (mode : RoundingMode) :
    glaisherKinkelinPrecRoundFuel fuel p mode
        = roundVal p mode (some ((DLMF.glaisherA : ℝ) : EReal)) ∨
      glaisherKinkelinPrecRoundFuel fuel p mode = (nan, .eq) :=
  (glaisherKinkelinPrecRoundFuel_zivCases p mode).sound fuel

/-- **The Glaisher–Kinkelin constant is correctly rounded, or the fuel ran out.** -/
theorem glaisherKinkelinPrecRound_eq_or (p : ℕ) [NeZero p] (mode : RoundingMode) :
    glaisherKinkelinPrecRound p mode
        = roundVal p mode (some ((DLMF.glaisherA : ℝ) : EReal)) ∨
      glaisherKinkelinPrecRound p mode = (nan, .eq) :=
  glaisherKinkelinPrecRoundFuel_eq_or (gammaFuel p) p mode

end Azurite.AzFloat
