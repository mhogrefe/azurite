/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.BarnesGBracket
import Azurite.AzFloat.Equiv.GlaisherKinkelin
import Azurite.AzFloat.Equiv.BetaBracket
import Azurite.Transcendental.BarnesG

/-!
# The bracket of the Barnes `G`-function encloses

`barnesGLnEncl_spec`: at every level `w ≥ 64`, an answer `(neg, L)` of `barnesGLnEncl x w` at a
float `x` that is no zero of `G` has `neg` the sign of `G(x)` and `L` an enclosure of
`ln |G(x)|`; `barnesGCore_spec`: the same for the enclosure of `|G(x)|`.  The pieces:
`barnesShift_spec` (`x + N > n + 1`), `barnesProd_spec` (the suffix products and the parity),
`altSumLoop_isEncl` (the alternating loop, generically), `barnesMu_alt` (the terms envelop
the remainder at a real argument: `Transcendental/BarnesG.lean`).
-/

namespace Azurite.AzFloat

open Finset DLMF
open scoped Nat

/-! ### The alternating loop encloses -/

/-- **The alternating loop encloses** a number enveloped by its terms, wherever it stops. -/
theorem altSumLoop_isEncl {V : ℕ} [NeZero V] (hV : 2 ≤ V) {t q : ℕ → ℝ}
    {term : ℕ → Encl → Encl} {μ i2 : ℝ} {inv2 : Encl} (hinv2 : IsEnclPos inv2 i2)
    (hq : ∀ k, q (k + 1) = q k * i2) (tol : AzFloat)
    {M : ℕ} (hτ : ∀ k p, 1 ≤ k → k ≤ M → IsEnclPos p (q k) → IsEncl0 (term k p) (t k))
    (hμ : ∀ k, 1 ≤ k → ∃ r : ℝ, μ = altPartial t k + r ∧ 0 ≤ (-1) ^ (k + 1) * r ∧ |r| ≤ t k) :
    ∀ (fuel k : ℕ) (p acc : Encl), 1 ≤ k → k + fuel ≤ M → IsEnclPos p (q k) →
      IsEncl acc (altPartial t k) → IsEncl (altSumLoop V term inv2 tol fuel k p acc) μ
  | 0, k, p, acc, hk, hkM, hp, hacc => by
    obtain ⟨r, h1, h2, h3⟩ := hμ k hk
    rw [altSumLoop]
    exact stirlingClose_spec hacc (hτ k p hk (by omega) hp) h1 h2 h3
  | fuel + 1, k, p, acc, hk, hkM, hp, hacc => by
    obtain ⟨r, h1, h2, h3⟩ := hμ k hk
    have hτk := hτ k p hk (by omega) hp
    have hclose := stirlingClose_spec (V := V) hacc hτk h1 h2 h3
    rw [altSumLoop]
    split_ifs with hstop hodd hodd
    · rwa [ite_eq_left hodd] at hclose
    · rwa [ite_eq_right hodd] at hclose
    all_goals
      have hp' : IsEnclPos (Encl.mul V p inv2) (q (k + 1)) := by
        rw [hq]; exact hp.mul hV hinv2
      refine altSumLoop_isEncl hV hinv2 hq tol hτ hμ fuel (k + 1) _ _ (by omega) (by omega) hp' ?_
      rw [altPartial_succ hk]
    · rw [(Nat.even_iff.mpr (by omega : (k + 1) % 2 = 0)).neg_one_pow, one_mul]
      exact hacc.add hτk.encloses
    · rw [(Nat.odd_iff.mpr (by omega : (k + 1) % 2 = 1)).neg_one_pow, neg_one_mul,
        ← sub_eq_add_neg]
      exact hacc.sub hτk.encloses

/-! ### The remainder at a real argument, in the alternating form -/

theorem altPartial_barnesTau {y : ℝ} (hy : 0 < y) :
    ∀ k, 1 ≤ k → altPartial (barnesTau y) k = -∑ i ∈ Icc 1 (k - 1), barnesTerm y i := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => simp [altPartial]
  | succ k hk ih =>
    rw [altPartial_succ hk, ih, Nat.add_sub_cancel]
    obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
    rw [Nat.add_sub_cancel, sum_Icc_succ_top (by omega), barnesTerm_eq_tau hy (by omega),
      pow_succ]
    ring

/-- **The terms envelop the remainder**: `−R(y) − C` is the alternating partial sum before the
index `k` plus a remainder of the sign of the term `k`, bounded by it. -/
theorem barnesMu_alt {y : ℝ} (hy : 0 < y) {k : ℕ} (hk : 1 ≤ k) :
    ∃ r : ℝ, -(glaisherR y).re - glaisherC = altPartial (barnesTau y) k + r ∧
      0 ≤ (-1) ^ (k + 1) * r ∧ |r| ≤ barnesTau y k := by
  obtain ⟨h1, h2⟩ := barnesRho_enveloping hy hk
  refine ⟨-barnesRho y (k - 1), ?_, ?_, by rwa [abs_neg]⟩
  · rw [altPartial_barnesTau hy k hk, barnesRho]
    ring
  · rw [pow_succ]
    linarith

/-! ### The term -/

/-- A term on enclosures. -/
theorem glaisherTermEncl_spec {V : ℕ} [NeZero V] {M k : ℕ} (hk : 1 ≤ k) (hkM : k ≤ M)
    {y : ℝ} (hy : 0 < y) {y2 p : Encl} (hy2 : IsEnclPos y2 (y ^ 2))
    (hp : IsEnclPos p (1 / y ^ (2 * (k + 1)))) :
    IsEncl0 (glaisherTermEncl V (AzNat.tangentNumbers (M + 1)) y2 k p) (barnesTau y k) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 := psiTermEncl_spec (V := V) (M := M + 1) (k := k + 1) (by omega) (by omega) hp
  have h2 := (h1.mul (w := V) hy2.encloses0).div (w := V)
    (enclosesPos_nat (n := 2 * k * (2 * k + 1)) (by positivity))
  unfold glaisherTermEncl
  convert h2 using 1
  unfold barnesTau
  rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add]
  push_cast
  field_simp

/-! ### The shift -/

theorem azIntPos_cast (e : AzInt) : ((azIntPos e : ℕ) : ℤ) = max e.toInt 0 := expPos_eq_max e

/-- `x + N > n + 1`. -/
theorem barnesShift_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (n : ℕ) :
    (n : ℝ) + 1 < xv + barnesShift x n := by
  obtain ⟨ht, -⟩ := truncToAzInt_spec hx
  have hN : (((n : ℤ) + 2 - (truncToAzInt x).toInt : ℤ) : ℝ) ≤ (barnesShift x n : ℝ) := by
    have h := azIntPos_cast ((AzNat.ofNat (n + 2)).toAzInt - truncToAzInt x)
    rw [AzInt.toInt_sub, AzNat.toInt_toAzInt, AzNat.toNat_ofNat] at h
    have h2 : ((n + 2 : ℕ) : ℤ) - (truncToAzInt x).toInt ≤ (barnesShift x n : ℤ) := by
      unfold barnesShift
      rw [h]
      exact le_max_left _ _
    have h3 : (((n : ℤ) + 2 - (truncToAzInt x).toInt : ℤ) : ℝ)
        ≤ ((barnesShift x n : ℤ) : ℝ) := by
      exact_mod_cast (by push_cast at h2 ⊢; linarith : (n : ℤ) + 2 - (truncToAzInt x).toInt
        ≤ (barnesShift x n : ℤ))
    exact_mod_cast h3
  push_cast at hN
  have := abs_lt.mp ht
  linarith

/-! ### The products -/

/-- **One factor**: the sign of `x + k` and a lower bound of `|x + k|` within `e^(8u)`. -/
theorem barnesFrac_spec {V : ℕ} [NeZero V] (hu : (1 / 2 : ℝ) ^ V ≤ 1 / 8) {x : AzFloat}
    {xv : ℝ} (hx : x.toVal = some (xv : EReal)) {k : ℕ} (hk : xv + k ≠ 0) :
    ∃ (σ : Bool) (f : AzFloat), barnesFrac V x k = some (σ, f) ∧
      LLow f |xv + k| (8 * (1 / 2 : ℝ) ^ V) ∧
      (if σ then (-1 : ℝ) else 1) * (xv + k) = |xv + k| := by
  have hu0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ V := by positivity
  have hd0 : 0 < |xv + k| := abs_pos.mpr hk
  have hK := toVal_ofAzNat_ofNat k
  unfold barnesFrac
  dsimp only
  by_cases hex : exactSumPrec x (ofAzNat (AzNat.ofNat k)) ≤ 2 * V
  · -- the exact sum
    simp only [hex, ↓reduceIte]
    have hd : (exactAdd x (ofAzNat (AzNat.ofNat k))).toVal = some ((xv + k : ℝ) : EReal) := by
      rw [toVal_exactAdd (isFinite_of_toVal_coe hx) (isFinite_of_toVal_coe hK),
        fval_of_toVal_coe hx, fval_of_toVal_coe hK]
    rcases lt_or_gt_of_ne hk with hneg | hpos
    · have c1 : lt zero (exactAdd x (ofAzNat (AzNat.ofNat k))) = false := by
        rw [← Bool.not_eq_true, lt_eq_true_iff toVal_zero' hd]
        linarith
      have c2 : lt (exactAdd x (ofAzNat (AzNat.ofNat k))) zero = true :=
        (lt_eq_true_iff hd toVal_zero').mpr hneg
      refine ⟨true, -exactAdd x (ofAzNat (AzNat.ofNat k)),
        by simp only [c1, c2, Bool.false_eq_true, ↓reduceIte], ?_, ?_⟩
      · refine ⟨-(xv + k), ?_, by linarith, by rw [abs_of_neg hneg], ?_⟩
        · rw [toVal_neg, hd, Option.map_some, EReal.coe_neg]
        · rw [abs_of_neg hneg]
          exact le_mul_of_one_le_right (by linarith) (Real.one_le_exp (by positivity))
      · simp only [↓reduceIte, neg_one_mul]
        rw [abs_of_neg hneg]
    · have c1 : lt zero (exactAdd x (ofAzNat (AzNat.ofNat k))) = true :=
        (lt_eq_true_iff toVal_zero' hd).mpr hpos
      refine ⟨false, exactAdd x (ofAzNat (AzNat.ofNat k)), by simp only [c1, ↓reduceIte], ?_,
        ?_⟩
      · refine ⟨xv + k, hd, hpos, by rw [abs_of_pos hpos], ?_⟩
        rw [abs_of_pos hpos]
        exact le_mul_of_one_le_right hpos.le (Real.one_le_exp (by positivity))
      · simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
        rw [abs_of_pos hpos]
  · -- the enclosure
    simp only [hex, ↓reduceIte]
    have hD := (AEncl.exact hx).add (w := V) (AEncl.natEncl k) (B := |xv + k|) (by linarith)
    obtain ⟨σ, F, hF, hFL⟩ := fracOfEncl_some hD (by
      have := mul_le_mul_of_nonneg_left hu hd0.le
      linarith) hk
    have hFs := fracOfEncl_spec hD.isEncl hF
    refine ⟨σ, F.1, by rw [hF]; rfl, ?_, ?_⟩
    · obtain ⟨l, h, hl, hh, h0, h1, h2, h3⟩ := hFL
      refine ⟨l, hl, h0, h1, h2.trans (h3.trans (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (le_of_eq ?_)) h0.le))⟩
      field_simp
      ring
    · obtain ⟨l, h, hl, hh, h0, h1, h2⟩ := hFs
      obtain ⟨l', h', hl', hh', -, h1', -⟩ := hFL
      rw [hl, Option.some.injEq, EReal.coe_eq_coe_iff] at hl'
      have hpos : 0 < (if σ then (-1 : ℝ) else 1) * (xv + k) := lt_of_lt_of_le h0 h1
      cases σ
      · simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at hpos ⊢
        exact (abs_of_pos hpos).symm
      · simp only [↓reduceIte, neg_one_mul] at hpos ⊢
        exact (abs_of_neg (by linarith)).symm

/-- **The suffix products rounded down**: an answer, a lower bound of the product within
`e^(lamW + k lamS + 16 k² u)`, and the sign, from factors within `e^(10u)`. -/
theorem barnesProdLo_llow {V : ℕ} [NeZero V] (hu : (1 / 2 : ℝ) ^ V ≤ 1 / 8)
    {F : ℕ → Option (Bool × AzFloat)} {xv : ℝ}
    (hF : ∀ k : ℕ, xv + k ≠ 0 → ∃ (σ : Bool) (f : AzFloat), F k = some (σ, f) ∧
      LLow f |xv + k| (10 * (1 / 2 : ℝ) ^ V) ∧
      (if σ then (-1 : ℝ) else 1) * (xv + k) = |xv + k|) (hnz : ∀ m : ℕ, xv ≠ -m) :
    ∀ (k : ℕ) (s w : AzFloat) (neg : Bool) (sv wv lamS lamW : ℝ), 0 ≤ lamS →
      LLow s sv lamS → LLow w wv lamW →
      ∃ (neg' : Bool) (w' : AzFloat), barnesProdLo V F k s w neg = some (neg', w') ∧
        LLow w' (wv * sv ^ k * ∏ j ∈ range k, |xv + j| ^ (j + 1))
          (lamW + k * lamS + 16 * (k : ℝ) ^ 2 * (1 / 2 : ℝ) ^ V) ∧
        (if neg' then (-1 : ℝ) else 1) * ∏ j ∈ range k, (xv + j) ^ (j + 1)
          = (if neg then (-1 : ℝ) else 1) * ∏ j ∈ range k, |xv + j| ^ (j + 1)
  | 0, s, w, neg, sv, wv, lamS, lamW, _, _, hw => by
    refine ⟨neg, w, by rw [barnesProdLo], ?_, by simp⟩
    simpa using hw
  | k + 1, s, w, neg, sv, wv, lamS, lamW, hS0, hs, hw => by
    have hu0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ V := by positivity
    have hd : xv + k ≠ 0 := fun h => hnz k (by linarith)
    obtain ⟨σ, f, hFk, hfL, habs⟩ := hF k hd
    have hs' := hs.mulFloor hu hfL
    have hw' := hw.mulFloor hu hs'
    obtain ⟨neg', w', h1, h2, h3⟩ := barnesProdLo_llow hu hF hnz k _ _
      (neg != (σ && k % 2 == 0)) _ _ _ _ (by positivity) hs' hw'
    refine ⟨neg', w', ?_, ?_, ?_⟩
    · rw [barnesProdLo, hFk]
      exact h1
    · have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      refine (congrArg (fun v => LLow w' v _) ?_).mp (h2.mono ?_)
      · rw [prod_range_succ]
        ring
      · push_cast
        nlinarith [mul_nonneg hk0 hu0, mul_nonneg hk0 hS0]
    · have hx' : xv + k = (if σ then (-1 : ℝ) else 1) * |xv + k| := by
        rw [← habs, ← mul_assoc]
        cases σ <;> simp
      rw [prod_range_succ, prod_range_succ, ← mul_assoc, h3]
      have hsgn : (if (neg != (σ && k % 2 == 0)) then (-1 : ℝ) else 1) * (xv + k) ^ (k + 1)
          = (if neg then (-1 : ℝ) else 1) * |xv + k| ^ (k + 1) := by
        conv_lhs => rw [hx', mul_pow]
        rcases Nat.even_or_odd k with he | ho
        · have hk2 : k % 2 = 0 := Nat.even_iff.mp he
          have hp : ((if σ then (-1 : ℝ) else 1)) ^ (k + 1) = if σ then (-1 : ℝ) else 1 := by
            cases σ
            · simp
            · simp [Even.neg_one_pow he, pow_succ]
          rw [hp]
          cases neg <;> cases σ <;> simp [hk2]
        · have hk2 : k % 2 = 1 := Nat.odd_iff.mp ho
          have hp : ((if σ then (-1 : ℝ) else 1)) ^ (k + 1) = 1 := by
            cases σ
            · simp
            · simp [Odd.neg_one_pow ho, pow_succ]
          rw [hp]
          cases neg <;> cases σ <;> simp [hk2]
      linear_combination (∏ j ∈ range k, |xv + j| ^ (j + 1)) * hsgn

/-- `16 N² 2^(−V)` is tiny when `N < 2^L` and `V ≥ 3L + 64`. -/
theorem sq_mul_half_pow_le {N L V : ℕ} (hN : N < 2 ^ L) (hV : 3 * L + 64 ≤ V) :
    16 * (N : ℝ) ^ 2 * (1 / 2 : ℝ) ^ V ≤ 1 / 2 := by
  have h1 : (N : ℝ) ^ 2 ≤ ((2 : ℝ) ^ L) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg N) (by exact_mod_cast hN.le) 2
  have h2 : (1 / 2 : ℝ) ^ V ≤ (1 / 2 : ℝ) ^ (2 * L) * (1 / 2 : ℝ) ^ 64 := by
    rw [← pow_add]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have h3 : ((2 : ℝ) ^ L) ^ 2 * (1 / 2 : ℝ) ^ (2 * L) = 1 := by
    rw [← pow_mul, mul_comm L 2, ← mul_pow]
    norm_num
  have h4 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ V := by positivity
  calc 16 * (N : ℝ) ^ 2 * (1 / 2 : ℝ) ^ V
      ≤ 16 * ((2 : ℝ) ^ L) ^ 2 * ((1 / 2 : ℝ) ^ (2 * L) * (1 / 2 : ℝ) ^ 64) :=
        mul_le_mul (by linarith) h2 h4 (by positivity)
    _ = 16 * (((2 : ℝ) ^ L) ^ 2 * (1 / 2 : ℝ) ^ (2 * L)) * (1 / 2 : ℝ) ^ 64 := by ring
    _ ≤ 1 / 2 := by rw [h3]; norm_num

/-- **The enclosure of the product**: rounded down, the upper end from the count of the
roundings. -/
theorem barnesProdLo_lencl {V : ℕ} [NeZero V] (hu : (1 / 2 : ℝ) ^ V ≤ 1 / 8)
    {F : ℕ → Option (Bool × AzFloat)} {xv : ℝ}
    (hF : ∀ k : ℕ, xv + k ≠ 0 → ∃ (σ : Bool) (f : AzFloat), F k = some (σ, f) ∧
      LLow f |xv + k| (10 * (1 / 2 : ℝ) ^ V) ∧
      (if σ then (-1 : ℝ) else 1) * (xv + k) = |xv + k|) (hnz : ∀ m : ℕ, xv ≠ -m) (N : ℕ)
    (hN : 16 * (N : ℝ) ^ 2 * (1 / 2 : ℝ) ^ V ≤ 1 / 2) :
    ∃ (neg : Bool) (wlo : AzFloat), barnesProdLo V F N one one false = some (neg, wlo) ∧
      LEncl (wlo, glaisherUpper V wlo (16 * N * N)) (∏ j ∈ range N, |xv + j| ^ (j + 1))
        ((32 * (N : ℝ) ^ 2 + 4) * (1 / 2 : ℝ) ^ V) ∧
      (if neg then (-1 : ℝ) else 1) * ∏ j ∈ range N, (xv + j) ^ (j + 1)
        = ∏ j ∈ range N, |xv + j| ^ (j + 1) := by
  obtain ⟨neg, wlo, h1, h2, h3⟩ := barnesProdLo_llow hu hF hnz N one one false 1 1 0 0 le_rfl
    (LLow.exact toVal_one' one_pos) (LLow.exact toVal_one' one_pos)
  refine ⟨neg, wlo, h1, ?_, by simpa using h3⟩
  simp only [one_pow, one_mul, mul_zero, zero_add] at h2
  have := h2.toEncl (K := 16 * N * N) (le_of_eq (by push_cast; ring))
    (by push_cast; linarith [show 16 * (N : ℝ) * N * (1 / 2 : ℝ) ^ V
      = 16 * (N : ℝ) ^ 2 * (1 / 2 : ℝ) ^ V by ring])
  refine this.mono (le_of_eq ?_)
  push_cast
  ring

/-! ### The argument -/

/-- **What the bracket asks of its argument** `x = xv`: enclosures of width at most `2^(−V)`,
a shift beyond `n + 1` that grows no faster than `n`, and the factors `|x + k|` within
`e^(10u)` with their signs. -/
structure BarnesArg (A : BarnesIn) (xv : ℝ) : Prop where
  encl : ∀ V, 64 ≤ V → AEncl (A.X V) xv ((1 / 2 : ℝ) ^ V)
  shift_gt : ∀ n : ℕ, (n : ℝ) + 1 < xv + A.shift n
  shift_le : ∃ C : ℝ, ∀ n : ℕ, (A.shift n : ℝ) ≤ n + C
  frac : ∀ (V : ℕ) [NeZero V], (1 / 2 : ℝ) ^ V ≤ 1 / 8 → ∀ k : ℕ, xv + k ≠ 0 →
    ∃ (σ : Bool) (f : AzFloat), A.frac V k = some (σ, f) ∧
      LLow f |xv + k| (10 * (1 / 2 : ℝ) ^ V) ∧
      (if σ then (-1 : ℝ) else 1) * (xv + k) = |xv + k|

theorem barnesShift_le (x : AzFloat) (n : ℕ) :
    (barnesShift x n : ℝ) ≤ n + (2 + |((truncToAzInt x).toInt : ℝ)|) := by
  have h := azIntPos_cast ((AzNat.ofNat (n + 2)).toAzInt - truncToAzInt x)
  rw [AzInt.toInt_sub, AzNat.toInt_toAzInt, AzNat.toNat_ofNat] at h
  have h2 : (barnesShift x n : ℤ) ≤ (n : ℤ) + 2 + |(truncToAzInt x).toInt| := by
    unfold barnesShift
    rw [h]
    have := neg_abs_le (truncToAzInt x).toInt
    have h0 := abs_nonneg (truncToAzInt x).toInt
    push_cast
    omega
  have h3 : ((barnesShift x n : ℤ) : ℝ) ≤ (((n : ℤ) + 2 + |(truncToAzInt x).toInt| : ℤ) : ℝ) :=
    by exact_mod_cast h2
  push_cast at h3
  linarith

/-- **A float is an argument of the bracket.** -/
theorem barnesArg_float {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) :
    BarnesArg (barnesIn x) xv where
  encl := fun V _ => ⟨xv, xv, hx, hx, le_rfl, le_rfl, by simp⟩
  shift_gt := barnesShift_spec hx
  shift_le := ⟨_, barnesShift_le x⟩
  frac := fun V _ hu k hk => by
    obtain ⟨σ, f, h1, h2, h3⟩ := barnesFrac_spec hu hx hk
    exact ⟨σ, f, h1, h2.mono (by have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ V := by positivity
                                 linarith), h3⟩

/-! ### The enclosure of `ln |G(x)|` -/

/-- An enclosure narrower than the number is positive. -/
theorem AEncl.toPos {a : Encl} {v ε : ℝ} (h : AEncl a v ε) (hε : ε < v) : IsEnclPos a v := by
  obtain ⟨l, u, hl, hu, h1, h2, h3⟩ := h
  exact ⟨l, u, hl, hu, by linarith, h1, h2⟩

theorem one_le_gamma_of_two_le {Y : ℝ} (hY : 2 ≤ Y) : 1 ≤ Real.Gamma Y := by
  rcases hY.eq_or_lt with rfl | h
  · rw [Real.Gamma_two]
  · have := Real.Gamma_strictMonoOn_Ici (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hY) h
    rw [Real.Gamma_two] at this
    exact this.le

/-- **The enclosure of `ln |G(x)|` and the sign of `G(x)`**, at every level, off the zeros of
`G`. -/
theorem barnesGLnEnclOf_spec {A : BarnesIn} {xv : ℝ} (hA : BarnesArg A xv)
    (hnz : ∀ m : ℕ, xv ≠ -m) {w : ℕ} (hw : 64 ≤ w) {neg : Bool} {L : Encl}
    (h : barnesGLnEnclOf A w = some (neg, L)) :
    0 < (if neg then (-1 : ℝ) else 1) * barnesGR xv ∧
      IsEncl L (Real.log ((if neg then (-1 : ℝ) else 1) * barnesGR xv)) := by
  unfold barnesGLnEnclOf at h
  dsimp only at h
  obtain ⟨j, hj⟩ : ∃ j : ℕ, j = glaisherTerms w := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = glaisherArg w := ⟨_, rfl⟩
  rw [← hj, ← hn] at h
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = A.shift n := ⟨_, rfl⟩
  rw [← hN] at h
  obtain ⟨V, hVd⟩ : ∃ V : ℕ,
      V = w + 3 * max A.eb ((N + n + 3).log2 + 1) + 64 := ⟨_, rfl⟩
  rw [← hVd] at h
  split at h
  · exact absurd h (by simp)
  next neg0 wlo hprod =>
  rw [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hV64 : 64 ≤ V := by omega
  have hV2 : 2 ≤ V := by omega
  have : NeZero V := ⟨by omega⟩
  have hj1 : 1 ≤ j := by rw [hj]; unfold glaisherTerms; omega
  have hn24 : 24 ≤ n := by rw [hn]; exact glaisherArg_ge w
  have hshift := hA.shift_gt n
  rw [← hN] at hshift
  have hn24r : (24 : ℝ) ≤ n := by exact_mod_cast hn24
  obtain ⟨Yv, hYv⟩ : ∃ Yv : ℝ, Yv = xv + N := ⟨_, rfl⟩
  obtain ⟨yv, hyv⟩ : ∃ yv : ℝ, yv = Yv - 1 := ⟨_, rfl⟩
  rw [← hYv] at hshift
  have hY25 : 25 < Yv := by linarith
  have hy24 : 24 < yv := by rw [hyv]; linarith
  have hy0 : 0 < yv := by linarith
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (1 / 2 : ℝ) ^ V := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hu]; positivity
  have hu64 : u ≤ 1 / 64 := by
    rw [hu]
    calc (1 / 2 : ℝ) ^ V ≤ (1 / 2 : ℝ) ^ 6 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 64 := by norm_num
  -- the arguments
  have hXA := hA.encl V hV64
  rw [← hu] at hXA
  have hX : IsEncl (A.X V) xv := hXA.isEncl
  have hYA := hXA.add (w := V) (AEncl.natEncl N) (B := Yv + 1)
    (by rw [← hYv, abs_of_pos (by linarith)]; linarith)
  rw [← hYv, ← hu] at hYA
  have hYu : Yv * u ≤ Yv / 64 := by
    have := mul_le_mul_of_nonneg_left hu64 (by linarith : (0 : ℝ) ≤ Yv)
    linarith
  have hYpos : IsEnclPos (Encl.add V (A.X V) (Encl.nat N)) Yv :=
    hYA.toPos (by linarith)
  have hyA := hYA.sub (w := V) (AEncl.exact toVal_one') (B := 2 * Yv)
    (by rw [abs_of_pos (by linarith)]; linarith)
  rw [← hyv, ← hu] at hyA
  have hypos : IsEnclPos (Encl.sub V (Encl.add V (A.X V) (Encl.nat N))
      (Encl.exact one)) yv := hyA.toPos (by rw [hyv]; linarith)
  -- the product
  have hNs : 16 * (N : ℝ) ^ 2 * (1 / 2 : ℝ) ^ V ≤ 1 / 2 :=
    sq_mul_half_pow_le (L := (N + n + 3).log2 + 1)
      ((Nat.lt_log2_self (n := N + n + 3)).trans_le' (by omega)) (by
        rw [hVd]
        have := le_max_right A.eb ((N + n + 3).log2 + 1)
        omega)
  obtain ⟨neg1, wlo1, hprod1, hWL, hsgn⟩ :=
    barnesProdLo_lencl (half_pow_le_eighth (by omega))
      (hA.frac V (half_pow_le_eighth (by omega))) hnz N hNs
  rw [hprod] at hprod1
  rw [Option.some.injEq, Prod.mk.injEq] at hprod1
  obtain ⟨rfl, rfl⟩ := hprod1
  have hW := hWL.isEnclPos
  obtain ⟨Pa, hPa⟩ : ∃ Pa : ℝ, Pa = ∏ j ∈ range N, |xv + j| ^ (j + 1) := ⟨_, rfl⟩
  obtain ⟨Pv, hPv⟩ : ∃ Pv : ℝ, Pv = ∏ j ∈ range N, (xv + j) ^ (j + 1) := ⟨_, rfl⟩
  rw [← hPa] at hW hsgn
  rw [← hPv] at hsgn
  have hPa0 : 0 < Pa := by
    obtain ⟨l, -, -, -, h0, h1, -⟩ := hW
    linarith
  have hlnP := lnOfEncl_pos hW hV64
  -- the logarithms
  have hlny := (lnOfEncl_pos hypos hV64).clamp0 (Real.log_nonneg (by linarith))
  have hSt := lnGammaStirlingEncl_spec hV64 (M := j + 1) (by omega) hYpos (by linarith)
    (powerOf2 (-(AzNat.ofNat (w + 16)).toAzInt))
  have h2pi := (lnOfEncl_pos ((enclosesPos_nat (n := 2) (by norm_num)).mul hV2
    (enclosesPos_pi hV64)) hV64).half
  have hGam := hSt.add (w := V) h2pi
  have eGam : Real.log (Real.Gamma Yv) - 1 / 2 * Real.log (2 * Real.pi)
      + Real.log (((2 : ℕ) : ℝ) * Real.pi) / 2 = Real.log (Real.Gamma Yv) := by
    push_cast
    ring
  rw [eGam] at hGam
  have hGam0 := hGam.clamp0 (Real.log_nonneg (one_le_gamma_of_two_le (by linarith)))
  -- the series
  have hy2 := hypos.mul hV2 hypos
  have hinv2 := enclosesPos_one.div hV2 hy2
  have hp1 := hinv2.mul hV2 hinv2
  have hy2' : IsEnclPos (Encl.mul V
      (Encl.sub V (Encl.add V (A.X V) (Encl.nat N)) (Encl.exact one))
      (Encl.sub V (Encl.add V (A.X V) (Encl.nat N)) (Encl.exact one))) (yv ^ 2) := by
    rw [sq]; exact hy2
  have hinv2' : IsEnclPos (Encl.div V (Encl.exact one) (Encl.mul V
      (Encl.sub V (Encl.add V (A.X V) (Encl.nat N)) (Encl.exact one))
      (Encl.sub V (Encl.add V (A.X V) (Encl.nat N)) (Encl.exact one))))
      (1 / yv ^ 2) := by
    rw [sq]; exact hinv2
  have hS := altSumLoop_isEncl hV2 (t := barnesTau yv) (q := fun k => 1 / yv ^ (2 * (k + 1)))
    (μ := -(glaisherR yv).re - glaisherC) hinv2'
    (fun k => by
      show 1 / yv ^ (2 * (k + 1 + 1)) = 1 / yv ^ (2 * (k + 1)) * (1 / yv ^ 2)
      rw [show 2 * (k + 1 + 1) = 2 * (k + 1) + 2 by ring, pow_add]
      field_simp)
    (powerOf2 (-(AzNat.ofNat (w + 16)).toAzInt)) (M := j)
    (fun k p hk hkM hp => glaisherTermEncl_spec (V := V) hk hkM hy0 hy2' hp)
    (fun k hk => barnesMu_alt hy0 hk) (j - 1) 1 _ (Encl.exact zero) le_rfl (by omega)
    (by
      show IsEnclPos _ (1 / yv ^ (2 * (1 + 1)))
      convert hp1 using 1
      field_simp)
    (by
      have : altPartial (barnesTau yv) 1 = 0 := by simp [altPartial]
      rw [this]
      exact ⟨0, 0, toVal_zero', toVal_zero', le_rfl, le_rfl⟩)
  have hlnA : IsEncl (glaisherKinkelinLnEnclWith w (AzNat.tangentNumbers (j + 1)))
      glaisherC := by
    rw [hj]
    exact (glaisherKinkelinLnEncl_aencl hw).isEncl
  -- the coefficients
  have hc := ((hypos.mul hV2 hYpos).encloses0.encloses.half).add (w := V)
    (enclosesPos_one.div hV2 (enclosesPos_nat (n := 12) (by norm_num))).encloses0.encloses
  have ht2 := (hX.sub (w := V) enclosesPos_one.encloses0.encloses).mulPos (W := V) hGam0
  have ht3 := hc.mulPos (W := V) hlny
  have hfin := ((((hy2.encloses0.encloses.half.half.add (w := V) ht2).sub (w := V) ht3).sub
    (w := V) hlnA).sub (w := V) hS).add (w := V) hlnP
  -- the value
  have hG := barnesGR_eq_shift hnz N
  rw [← hYv, ← hPv] at hG
  have hGY : 0 < barnesGR Yv := barnesGR_pos (by linarith)
  have hΓ : 0 < Real.Gamma Yv := Real.Gamma_pos_of_pos (by linarith)
  have hval : (if neg0 = true then (-1 : ℝ) else 1) * barnesGR xv
      = barnesGR Yv * Pa / Real.Gamma Yv ^ N := by
    rw [hG, ← hsgn]
    ring
  have hlog1 := log_barnesGR_add_one hy0
  rw [show yv + 1 = Yv by rw [hyv]; ring] at hlog1
  refine ⟨by rw [hval]; positivity, ?_⟩
  rw [hval, Real.log_div (by positivity) (by positivity), Real.log_mul hGY.ne' hPa0.ne',
    Real.log_pow, hlog1]
  refine (congrArg (IsEncl _) ?_).mpr hfin
  rw [hyv, hYv]
  push_cast
  ring

/-- **The enclosure of `|G(x)|` and the sign of `G(x)`.** -/
theorem barnesGCoreOf_spec {A : BarnesIn} {xv : ℝ} (hA : BarnesArg A xv)
    (hnz : ∀ m : ℕ, xv ≠ -m) {w : ℕ} (hw : 64 ≤ w) {neg : Bool} {b : Encl}
    (h : barnesGCoreOf A w = some (neg, b)) :
    IsEnclPos b ((if neg then (-1 : ℝ) else 1) * barnesGR xv) := by
  unfold barnesGCoreOf at h
  obtain ⟨c, hc, hr⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨neg', Lg⟩ := c
  obtain ⟨g, hg, hgeq⟩ := Option.map_eq_some_iff.mp hr
  rw [Prod.mk.injEq] at hgeq
  obtain ⟨rfl, rfl⟩ := hgeq
  obtain ⟨hpos, hL⟩ := barnesGLnEnclOf_spec hA hnz hw hc
  have := gammaExpEncl_spec hL hw hg
  simp only [Bool.false_eq_true, ↓reduceIte] at this
  rwa [Real.exp_log hpos] at this

/-- The enclosure of `|G(x)|` and the sign of `G(x)` for a float. -/
theorem barnesGCore_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hnz : ∀ m : ℕ, xv ≠ -m) {w : ℕ} (hw : 64 ≤ w) {neg : Bool} {b : Encl}
    (h : barnesGCore x w = some (neg, b)) :
    IsEnclPos b ((if neg then (-1 : ℝ) else 1) * barnesGR xv) :=
  barnesGCoreOf_spec (barnesArg_float hx) hnz hw h

end Azurite.AzFloat
