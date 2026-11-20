/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Pochhammer
import Azurite.AzFloat.Equiv.Beta
import Azurite.BrentZimmermann.Chapter4.ArgumentReduction
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Equivalence: Pochhammer's symbol

`Spec.pochhammer n : EReal → Option EReal` is `(a)ₙ` on the extended reals — Mathlib's
`(ascPochhammer ℝ n).eval a`, as in `DLMF/Chapter5/Section2.lean` — and
`pochhammerPrecRound_eq_or` says that `pochhammerPrecRound x n p mode` is its correct rounding,
or `(nan, .eq)` when the fuel of the Ziv loop runs out.

The steps: `ascPochhammer_eval_eq_prod`, `prod_add_eq_split` (the splitting at `k` negative
factors, an identity for every `k ≤ n`), `lnGammaDiff_spec`, `risingPiece_spec`,
`pochCore_spec`; `pochHasZero_spec`, `pochExact?_eq`.
-/

namespace Azurite.AzFloat

open Finset

/-! ### The symbol as a product -/

theorem ascPochhammer_eval_eq_prod (x : ℝ) (n : ℕ) :
    (ascPochhammer ℝ n).eval x = ∏ j ∈ range n, (x + j) := by
  induction n with
  | zero => simp
  | succ n ih => rw [ascPochhammer_succ_eval, ih, prod_range_succ]

/-- `∏_{j<k} (x + j) = (−1)^k ∏_{i<k} (1 − x − k + i)`. -/
theorem prod_add_eq_neg_one_pow (x : ℝ) (k : ℕ) :
    ∏ j ∈ range k, (x + j) = (-1) ^ k * ∏ i ∈ range k, (1 - x - k + i) := by
  rw [← prod_range_reflect (fun j => x + (j : ℝ)) k]
  have h : ∀ i ∈ range k, x + ((k - 1 - i : ℕ) : ℝ) = -(1 - x - k + i) := fun i hi => by
    have hik : i + 1 ≤ k := mem_range.mp hi
    rw [Nat.sub_sub, Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [prod_congr rfl h, prod_neg, card_range]

/-- **The splitting at `k`**: `(x)ₙ = (−1)^k (1 − x − k)_k (x + k)_{n−k}` for every `k ≤ n`. -/
theorem prod_add_eq_split (x : ℝ) {k n : ℕ} (hk : k ≤ n) :
    ∏ j ∈ range n, (x + j)
      = (-1) ^ k * (∏ i ∈ range k, (1 - x - k + i)) * ∏ i ∈ range (n - k), (x + k + i) := by
  conv_lhs => rw [show n = k + (n - k) by omega, prod_range_add]
  rw [prod_add_eq_neg_one_pow x k]
  congr 1
  refine prod_congr rfl fun i _ => ?_
  push_cast
  ring

/-! ### The bracket -/

/-- **`lnGammaDiff`**: `Γ(u)/Γ(v) = eᵗ q` for `u, v > 0`. -/
theorem lnGammaDiff_spec {U Vv : Encl} {u v : ℝ} (hU : IsEncl U u) (hVv : IsEncl Vv v) {L V : ℕ}
    (hV : 64 ≤ V) {M : ℕ} (hM : 1 ≤ M) {tol : AzFloat} {t q : Encl}
    (h : lnGammaDiff U Vv L V M (AzNat.tangentNumbers M) tol = some (t, q)) :
    0 < v ∧ ∃ tv qv : ℝ, IsEncl t tv ∧ IsEnclPos q qv ∧
      Real.Gamma u / Real.Gamma v = Real.exp tv * qv := by
  have : NeZero V := ⟨by omega⟩
  unfold lnGammaDiff at h
  split_ifs at h with hc
  rw [Bool.and_eq_true] at hc
  rw [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hUp := hU.pos_of_lt hc.1
  have hVp := hVv.pos_of_lt hc.2
  have hu0 : 0 < u := by obtain ⟨l, h', -, -, h0, h1, -⟩ := hUp; linarith
  have hv0 : 0 < v := by obtain ⟨l, h', -, -, h0, h1, -⟩ := hVp; linarith
  obtain ⟨gu, Pu, hSu, hPu, hlu⟩ := stirlingShifted_spec hUp (expOf U.2) L hV hM tol
  obtain ⟨gv, Pv, hSv, hPv, hlv⟩ := stirlingShifted_spec hVp (expOf Vv.2) L hV hM tol
  have hPu0 : 0 < Pu := by obtain ⟨l, h', -, -, h0, h1, -⟩ := hPu; linarith
  have hPv0 : 0 < Pv := by obtain ⟨l, h', -, -, h0, h1, -⟩ := hPv; linarith
  refine ⟨hv0, _, _, hSu.sub hSv, hPv.div (by omega) hPu, ?_⟩
  have hGu := Real.Gamma_pos_of_pos hu0
  have hGv := Real.Gamma_pos_of_pos hv0
  have eu : Real.Gamma u = Real.exp gu / Pu := by
    rw [← Real.exp_log hGu, hlu, Real.exp_sub, Real.exp_log hPu0]
  have ev : Real.Gamma v = Real.exp gv / Pv := by
    rw [← Real.exp_log hGv, hlv, Real.exp_sub, Real.exp_log hPv0]
  rw [eu, ev, show gu - 1 / 2 * Real.log (2 * Real.pi) - (gv - 1 / 2 * Real.log (2 * Real.pi))
    = gu - gv by ring, Real.exp_sub]
  field_simp

/-- A rising factorial `(y)ₘ` with a positive first factor, as `eᵗ q`: trivially for `m = 0`,
from `lnGammaDiff` otherwise. -/
theorem risingPiece_spec {U Vv : Encl} {y : ℝ} {m : ℕ} (hU : IsEncl U (y + m))
    (hVv : IsEncl Vv y) {L V : ℕ} (hV : 64 ≤ V) {M : ℕ} (hM : 1 ≤ M) {tol : AzFloat}
    {t q : Encl}
    (h : (if m = 0 then some (Encl.exact zero, Encl.exact one)
      else lnGammaDiff U Vv L V M (AzNat.tangentNumbers M) tol) = some (t, q)) :
    ∃ tv qv : ℝ, IsEncl t tv ∧ IsEnclPos q qv ∧ ∏ i ∈ range m, (y + i) = Real.exp tv * qv := by
  split_ifs at h with hm
  · rw [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    subst hm
    exact ⟨0, 1, isEncl0_exact_zero, enclosesPos_one, by simp⟩
  · obtain ⟨hy, tv, qv, ht, hq, hval⟩ := lnGammaDiff_spec hU hVv hV hM h
    refine ⟨tv, qv, ht, hq, ?_⟩
    rw [← hval, BZ.Gamma_add_nat hy m]
    field_simp [(Real.Gamma_pos_of_pos hy).ne']

theorem pochSplit_le (x : AzFloat) (n : ℕ) : pochSplit x n ≤ n := by
  unfold pochSplit
  split_ifs <;> first | exact Nat.zero_le n | exact le_rfl | exact min_le_left _ _

/-- **`pochCoreOf` answers with the sign and a positive enclosure of `|(x)ₙ|`**, for any
`k ≤ n`. -/
theorem pochCoreOf_spec {X : ℕ → Encl} {xv : ℝ} (hX : ∀ V, 64 ≤ V → IsEncl (X V) xv)
    {k n : ℕ} (hk : k ≤ n) {bits w : ℕ} (hw : 64 ≤ w) {neg : Bool} {r : Encl}
    (h : pochCoreOf X k n bits w = some (neg, r)) :
    IsEnclPos r ((if neg then -1 else 1) * ∏ j ∈ range n, (xv + j)) := by
  unfold pochCoreOf at h
  dsimp only at h
  set wL := w + bits
  set L := lnGammaShiftExp wL
  set V := wL + 2 * L + 8 + 2 * wL.log2 with hVdef
  have hV : 64 ≤ V := by omega
  have : NeZero V := ⟨by omega⟩
  have hV2 : 2 ≤ V := by omega
  have hM : 1 ≤ lnGammaTerms wL (L + 1) := by
    unfold lnGammaTerms; exact le_trans (by norm_num) (Nat.le_add_left 3 _)
  have hXV := hX V hV
  have hY : IsEncl (Encl.sub V (Encl.exact one) (X V)) (1 - xv) :=
    enclosesPos_one.encloses0.encloses.sub hXV
  split at h
  · rename_i t₁ q₁ t₂ q₂ h1 h2
    obtain ⟨g, hg, hgeq⟩ := Option.map_eq_some_iff.mp h
    rw [Prod.mk.injEq] at hgeq
    obtain ⟨rfl, rfl⟩ := hgeq
    obtain ⟨tv₁, qv₁, ht₁, hq₁, hv₁⟩ := risingPiece_spec (y := 1 - xv - k) (m := k)
      (by rw [show (1 : ℝ) - xv - k + k = 1 - xv by ring]; exact hY)
      (hY.sub (isEncl0_nat k).encloses) hV hM h1
    obtain ⟨tv₂, qv₂, ht₂, hq₂, hv₂⟩ := risingPiece_spec (y := xv + k) (m := n - k)
      (by
        rw [show xv + (k : ℝ) + ((n - k : ℕ) : ℝ) = xv + (n : ℕ) by
          rw [Nat.cast_sub hk]; ring]
        exact hXV.add (isEncl0_nat n).encloses)
      (hXV.add (isEncl0_nat k).encloses) hV hM h2
    have hE := gammaExpEncl_spec (ht₁.add (w := V) ht₂) hw hg
    simp only [Bool.false_eq_true, ↓reduceIte] at hE
    have := (hE.mul hV2 hq₁).mul hV2 hq₂
    convert this using 1
    rw [prod_add_eq_split xv hk, hv₁, hv₂, Real.exp_add]
    have hsq : ((-1 : ℝ) ^ k) * ((-1 : ℝ) ^ k) = 1 := by rw [← mul_pow]; norm_num
    by_cases hodd : k % 2 = 1
    · have : (k % 2 == 1) = true := by simpa using hodd
      rw [this, ite_eq_left rfl, (Nat.odd_iff.mpr hodd).neg_one_pow]
      ring
    · have : (k % 2 == 1) = false := by simpa using hodd
      rw [this, ite_eq_right (by simp), (Nat.even_iff.mpr (by omega)).neg_one_pow]
      ring
  · exact absurd h (by simp)

/-- **`pochCore` answers with the sign and a positive enclosure of `|(x)ₙ|`.** -/
theorem pochCore_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) {n w : ℕ}
    (hw : 64 ≤ w) {neg : Bool} {r : Encl} (h : pochCore x n w = some (neg, r)) :
    IsEnclPos r ((if neg then -1 else 1) * ∏ j ∈ range n, (xv + j)) :=
  pochCoreOf_spec (fun _ _ => ⟨xv, xv, hx, hx, le_rfl, le_rfl⟩) (pochSplit_le x n) hw h

/-! ### The exact cases -/

/-- A vanishing factor. -/
theorem pochHasZero_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) {n : ℕ}
    (h : pochHasZero x n = true) : ∏ j ∈ range n, (xv + j) = 0 := by
  unfold pochHasZero at h
  rw [Bool.and_eq_true, Bool.and_eq_true, isInteger_iff_of_toVal hx,
    le_eq_true_iff hx toVal_zero'] at h
  obtain ⟨⟨⟨k, hk⟩, hle⟩, hlt⟩ := h
  have hn : (-(ofAzNat (AzNat.ofNat n))).toVal = some ((-(n : ℝ) : ℝ) : EReal) := by
    rw [toVal_neg, toVal_ofAzNat_ofNat, Option.map_some, EReal.coe_neg]
  rw [lt_eq_true_iff hn hx] at hlt
  have hk0 : k ≤ 0 := by exact_mod_cast (hk ▸ hle : (k : ℝ) ≤ 0)
  have hkn : -(n : ℤ) < k := by exact_mod_cast (hk ▸ hlt : -(n : ℝ) < (k : ℝ))
  refine prod_eq_zero (i := (-k).toNat) (mem_range.mpr (by omega)) ?_
  have : (((-k).toNat : ℕ) : ℝ) = -(k : ℝ) := by
    rw [show (((-k).toNat : ℕ) : ℝ) = (((-k).toNat : ℤ) : ℝ) by push_cast; rfl,
      Int.toNat_of_nonneg (by omega)]
    push_cast
    rfl
  rw [this, hk]
  ring

/-- `∏ (N + j D) / Dⁿ = ∏ (N/D + j)`. -/
theorem prod_div_pow_eq {N D : ℝ} (hD : D ≠ 0) (n : ℕ) :
    (∏ j ∈ range n, (N + j * D)) / D ^ n = ∏ j ∈ range n, (N / D + j) := by
  have hterm : ∀ j ∈ range n, N / D + (j : ℝ) = (N + j * D) / D := fun j _ => by field_simp
  rw [prod_congr rfl hterm, prod_div_distrib, prod_const, card_range]

/-- **`pochIntQuot N D n` is the rounding of `(N/D)ₙ`.** -/
theorem pochIntQuot_eq {N D : AzInt} {xv : ℝ} (hD : (0 : ℝ) < (D.toInt : ℝ))
    (hN : (N.toInt : ℝ) / (D.toInt : ℝ) = xv) (n p : ℕ) [NeZero p] (mode : RoundingMode) :
    pochIntQuot N D n p mode
      = roundVal p mode (some ((∏ j ∈ range n, (xv + j) : ℝ) : EReal)) := by
  have hDn : (((D.pow n).toInt : ℤ) : ℝ) ≠ 0 := by
    rw [AzInt.toInt_pow]
    push_cast
    exact pow_ne_zero _ hD.ne'
  unfold pochIntQuot
  rw [divPrecRound_eq_liftVal₂, liftVal₂, toVal_ofAzInt, toVal_ofAzInt, Option.bind_some,
    Option.bind_some, Spec.div_coe_coe _ _ hDn]
  congr 3
  rw [AzInt.toInt_pow, toInt_risingInt, ← hN]
  push_cast
  exact prod_div_pow_eq hD.ne' n

/-- The signed numerator over the denominator of an `AzRat` is its value. -/
theorem mkNorm_div_den_eq (q : AzRat) :
    ((AzInt.mkNorm q.sign q.num).toInt : ℝ) / ((q.den.toAzInt).toInt : ℝ)
      = ((AzRat.toRat q : ℚ) : ℝ) := by
  rw [coe_toRat_eq_sign_mul, AzNat.toInt_mkNorm, AzRat.toInt_toAzInt']
  cases q.sign <;> simp [neg_div]

/-- **The exact path answers with the rounding of `(x)ₙ`.** -/
theorem pochExact?_eq {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) {n : ℕ} (p : ℕ)
    [NeZero p] (mode : RoundingMode) {r : AzFloat × Ordering}
    (h : pochExact? x n p mode = some r) :
    r = roundVal p mode (some ((∏ j ∈ range n, (xv + j) : ℝ) : EReal)) := by
  unfold pochExact? at h
  split_ifs at h
  obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h
  have hav := toVal_of_toAzRat? x q hq
  rw [hx, Option.some.injEq, EReal.coe_eq_coe_iff] at hav
  exact pochIntQuot_eq (by rw [AzRat.toInt_toAzInt']; exact_mod_cast den_pos_real q)
    (by rw [hav]; exact mkNorm_div_den_eq q) n p mode

/-! ### The driver -/

namespace Spec

/-- `(a)ₙ` on the extended reals: `1` for `n = 0`; `(+∞)ₙ = +∞`, `(−∞)ₙ = (−1)ⁿ ∞` for
`n ≥ 1`. -/
noncomputable def pochhammer (n : ℕ) (a : EReal) : Option EReal :=
  if n = 0 then some 1
  else if a = ⊤ then some ⊤
  else if a = ⊥ then (if n % 2 = 0 then some ⊤ else some ⊥)
  else some (((ascPochhammer ℝ n).eval a.toReal : ℝ) : EReal)

theorem pochhammer_zero (a : EReal) : pochhammer 0 a = some 1 := by simp [pochhammer]

theorem pochhammer_coe {n : ℕ} (hn : n ≠ 0) (xv : ℝ) :
    pochhammer n (xv : EReal) = some ((∏ j ∈ range n, (xv + j) : ℝ) : EReal) := by
  unfold pochhammer
  rw [ite_eq_right hn, ite_eq_right (EReal.coe_ne_top _), ite_eq_right (EReal.coe_ne_bot _),
    EReal.toReal_coe, ascPochhammer_eval_eq_prod]

end Spec

/-- `pochRealFuel` is the correct rounding of `(x)ₙ`, or it is the loop with fuel. -/
theorem pochRealFuel_eq_or_loop (fuel : ℕ) {x : AzFloat} {xv : ℝ}
    (hx : x.toVal = some (xv : EReal)) (n p : ℕ) [NeZero p] (mode : RoundingMode) :
    pochRealFuel fuel x n p mode
        = roundVal p mode (some ((∏ j ∈ range n, (xv + j) : ℝ) : EReal)) ∨
      (pochHasZero x n = false ∧ pochRealFuel fuel x n p mode
        = zivLoop (pochApprox x n) p mode fuel (max 64 (p + 32))) := by
  unfold pochRealFuel
  by_cases hz : pochHasZero x n = true
  · left
    rw [ite_eq_left hz, pochHasZero_spec hx hz, EReal.coe_zero, roundVal_zero]
  rw [ite_eq_right hz, ite_eq_right (NeZero.ne p)]
  split
  · next r hr => left; exact pochExact?_eq hx p mode hr
  · exact Or.inr ⟨by simpa using hz, rfl⟩

/-- The loop of `(x)ₙ` is correct when it does not give up. -/
theorem pochLoop_eq_of_ne_nan {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (n p : ℕ) [NeZero p] (mode : RoundingMode) (fuel : ℕ)
    (h : zivLoop (pochApprox x n) p mode fuel (max 64 (p + 32)) ≠ (nan, .eq)) :
    zivLoop (pochApprox x n) p mode fuel (max 64 (p + 32))
      = roundVal p mode (some ((∏ j ∈ range n, (xv + j) : ℝ) : EReal)) :=
  zivLoop_eq_of_ne_nan_or_none p mode _ _ 64
    (fun w hw => gammaApproxOf_valid_or_none (fun _ _ hc => pochCore_spec hx hw hc) w p mode)
    _ _ (le_max_left _ _) h

/-- `pochRealFuel` is the correct rounding of `(x)ₙ`, or the fuel ran out. -/
theorem pochRealFuel_eq_or (fuel : ℕ) {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (n p : ℕ) [NeZero p] (mode : RoundingMode) :
    pochRealFuel fuel x n p mode
        = roundVal p mode (some ((∏ j ∈ range n, (xv + j) : ℝ) : EReal)) ∨
      pochRealFuel fuel x n p mode = (nan, .eq) := by
  rcases pochRealFuel_eq_or_loop fuel hx n p mode with h | ⟨-, h⟩
  · exact Or.inl h
  · rw [h]
    rcases eq_or_ne (zivLoop (pochApprox x n) p mode fuel (max 64 (p + 32)))
      (nan, .eq) with hzv | hzv
    · exact Or.inr hzv
    · exact Or.inl (pochLoop_eq_of_ne_nan hx n p mode fuel hzv)

/-- **Pochhammer's symbol is correctly rounded, or it is the loop with fuel** at a finite
argument without a vanishing factor, `n ≥ 1`. -/
theorem pochhammerPrecRoundFuel_eq_or_loop (fuel : ℕ) (x : AzFloat) (n p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    pochhammerPrecRoundFuel fuel x n p mode = liftVal (Spec.pochhammer n) x p mode ∨
      (∃ xv : ℝ, x.toVal = some (xv : EReal) ∧ n ≠ 0 ∧ pochHasZero x n = false ∧
        pochhammerPrecRoundFuel fuel x n p mode
          = zivLoop (pochApprox x n) p mode fuel (max 64 (p + 32))) := by
  have hp := NeZero.ne p
  have hone : setPrecRound one p mode = roundVal p mode (some (1 : EReal)) := by
    rw [setPrecRound_eq_roundVal toVal_one', EReal.coe_one]
  unfold liftVal
  cases x with
  | nan => left; rfl
  | infinity s =>
    left
    by_cases hn : n = 0
    · subst hn
      simp only [pochhammerPrecRoundFuel, ↓reduceIte, toVal_infinity, Option.bind_some,
        Spec.pochhammer_zero, ite_eq_right hp, hone]
    · simp only [pochhammerPrecRoundFuel, ite_eq_right hn, toVal_infinity, Option.bind_some]
      cases s
      · by_cases he : n % 2 = 0
        · simp [Spec.pochhammer, hn, he]
        · simp [Spec.pochhammer, hn, he]
      · simp [Spec.pochhammer, hn]
  | zero =>
    by_cases hn : n = 0
    · left
      subst hn
      simp only [pochhammerPrecRoundFuel, ↓reduceIte, toVal_zero, Option.bind_some,
        Spec.pochhammer_zero, ite_eq_right hp, hone]
    · simp only [pochhammerPrecRoundFuel, ite_eq_right hn, toVal_zero, Option.bind_some]
      rw [← EReal.coe_zero, Spec.pochhammer_coe hn]
      rcases pochRealFuel_eq_or_loop fuel toVal_zero' n p mode with h | ⟨hz, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨0, rfl, hn, hz, h⟩
  | finite s e q m hv =>
    by_cases hn : n = 0
    · left
      subst hn
      simp only [pochhammerPrecRoundFuel, ↓reduceIte, toVal_finite, Option.bind_some,
        Spec.pochhammer_zero, ite_eq_right hp, hone]
    · simp only [pochhammerPrecRoundFuel, ite_eq_right hn, toVal_finite, Option.bind_some]
      rw [Spec.pochhammer_coe hn]
      rcases pochRealFuel_eq_or_loop fuel (toVal_finite s e q m hv) n p mode with h | ⟨hz, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨_, rfl, hn, hz, h⟩

/-- **Pochhammer's symbol is correctly rounded, or the fuel ran out**, at every fuel. -/
theorem pochhammerPrecRoundFuel_eq_or (fuel : ℕ) (x : AzFloat) (n p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    pochhammerPrecRoundFuel fuel x n p mode = liftVal (Spec.pochhammer n) x p mode ∨
      pochhammerPrecRoundFuel fuel x n p mode = (nan, .eq) := by
  rcases pochhammerPrecRoundFuel_eq_or_loop fuel x n p mode with h | ⟨xv, hx, hn, -, h⟩
  · exact Or.inl h
  · rw [h]
    rcases eq_or_ne (zivLoop (pochApprox x n) p mode fuel (max 64 (p + 32)))
      (nan, .eq) with hzv | hzv
    · exact Or.inr hzv
    · left
      unfold liftVal
      rw [hx, Option.bind_some, Spec.pochhammer_coe hn]
      exact pochLoop_eq_of_ne_nan hx n p mode fuel hzv

/-- **Pochhammer's symbol is correctly rounded, or the fuel ran out.** -/
theorem pochhammerPrecRound_eq_or (x : AzFloat) (n p : ℕ) [NeZero p] (mode : RoundingMode) :
    pochhammerPrecRound x n p mode = liftVal (Spec.pochhammer n) x p mode ∨
      pochhammerPrecRound x n p mode = (nan, .eq) :=
  pochhammerPrecRoundFuel_eq_or (gammaFuel p) x n p mode

end Azurite.AzFloat
