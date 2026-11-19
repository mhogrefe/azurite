/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.GenPochhammer
import Azurite.AzFloat.Equiv.Pochhammer

/-!
# Equivalence: the generalized Pochhammer symbol

`Spec.genPochhammer : EReal → EReal → Option EReal` is `Γ(x + y)/Γ(x)` continued to the poles
of `Γ(x)` where the quotient has a limit, and `genPochhammerPrecRound_eq_or` says that
`genPochhammerPrecRound x y p mode` is its correct rounding, or `(nan, .eq)` when the fuel of
the Ziv loop runs out.  `Spec.genPochhammerReal_eq_of_not_pole` identifies the value with
`Γ(x + y)/Γ(x)` off the poles of both.
-/

namespace Azurite.AzFloat

open Finset

namespace Spec

open Classical in
/-- `Γ(x + y)/Γ(x)` for real `x`, `y`:

* an integer `y ≥ 0`: the polynomial `x (x + 1) ⋯ (x + y − 1)`;
* an integer `y < 0`: `1 / ((x + y) (x + y + 1) ⋯ (x − 1))`, undefined where the product
  vanishes (`x = 1, …, −y`);
* otherwise `Γ(x + y)/Γ(x)` — `0` at the poles of `Γ(x)`, as `Real.Gamma` vanishes there —,
  undefined at the poles `x + y = 0, −1, …` of `Γ(x + y)`. -/
noncomputable def genPochhammerReal (x y : ℝ) : Option EReal :=
  if ∃ k : ℤ, y = k then
    if 0 ≤ y then some ((∏ j ∈ range ⌊y⌋₊, (x + j) : ℝ) : EReal)
    else if ∏ j ∈ range ⌊-y⌋₊, (x + y + j) = 0 then none
    else some (((∏ j ∈ range ⌊-y⌋₊, (x + y + j))⁻¹ : ℝ) : EReal)
  else if x + y ≤ 0 ∧ ∃ k : ℤ, x + y = k then none
  else some ((Real.Gamma (x + y) / Real.Gamma x : ℝ) : EReal)

/-- The generalized Pochhammer symbol on the extended reals: undefined at the infinities. -/
noncomputable def genPochhammer (a b : EReal) : Option EReal :=
  if a = ⊤ ∨ a = ⊥ ∨ b = ⊤ ∨ b = ⊥ then none else genPochhammerReal a.toReal b.toReal

theorem genPochhammer_coe (xv yv : ℝ) :
    genPochhammer (xv : EReal) (yv : EReal) = genPochhammerReal xv yv := by
  simp [genPochhammer]

theorem genPochhammerReal_nat (x : ℝ) (n : ℕ) :
    genPochhammerReal x n = some ((∏ j ∈ range n, (x + j) : ℝ) : EReal) := by
  unfold genPochhammerReal
  rw [ite_eq_left ⟨(n : ℤ), by push_cast; rfl⟩, ite_eq_left (Nat.cast_nonneg n), Nat.floor_natCast]

theorem genPochhammerReal_neg_nat (x : ℝ) {n : ℕ} (hn : n ≠ 0) :
    genPochhammerReal x (-(n : ℝ)) =
      if ∏ j ∈ range n, (x - n + j) = 0 then none
      else some (((∏ j ∈ range n, (x - n + j))⁻¹ : ℝ) : EReal) := by
  unfold genPochhammerReal
  have hpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [ite_eq_left ⟨-(n : ℤ), by push_cast; rfl⟩, ite_eq_right (by linarith), neg_neg,
    Nat.floor_natCast]
  simp only [← sub_eq_add_neg]

/-- Off the poles of `Γ(x)` and `Γ(x + y)` the value is `Γ(x + y)/Γ(x)`. -/
theorem genPochhammerReal_eq_of_not_pole {x y : ℝ} (hx : ∀ m : ℕ, x ≠ -m)
    (hs : ∀ m : ℕ, x + y ≠ -m) :
    genPochhammerReal x y = some ((Real.Gamma (x + y) / Real.Gamma x : ℝ) : EReal) := by
  have hGx : Real.Gamma x ≠ 0 := Real.Gamma_ne_zero hx
  by_cases hy : ∃ k : ℤ, y = k
  · obtain ⟨k, rfl⟩ := hy
    rcases le_or_gt 0 k with hk | hk
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
      rw [Int.cast_natCast, genPochhammerReal_nat, gamma_add_nat_of_ne hx,
        mul_div_cancel_left₀ _ hGx]
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, k = -(n : ℤ) := ⟨(-k).toNat, by omega⟩
      have hn0 : n ≠ 0 := by omega
      subst hn
      rw [show (((-(n : ℤ) : ℤ)) : ℝ) = -(n : ℝ) by push_cast; rfl] at hs ⊢
      have hs' : ∀ m : ℕ, x - n ≠ -m := fun m => by rw [sub_eq_add_neg]; exact hs m
      have hG := gamma_add_nat_of_ne hs' n
      rw [sub_add_cancel] at hG
      have hP : ∏ j ∈ range n, (x - n + j) ≠ 0 := fun h0 => hGx (by rw [hG, h0, mul_zero])
      rw [genPochhammerReal_neg_nat x hn0, ite_eq_right hP, ← sub_eq_add_neg, hG]
      congr 2
      field_simp [Real.Gamma_ne_zero hs']
  · unfold genPochhammerReal
    rw [ite_eq_right hy, ite_eq_right]
    rintro ⟨hle, k, hk⟩
    refine hs (-k).toNat ?_
    have hk0 : k ≤ 0 := by exact_mod_cast (hk ▸ hle : (k : ℝ) ≤ 0)
    rw [hk, show (((-k).toNat : ℕ) : ℝ) = (((-k).toNat : ℤ) : ℝ) by push_cast; rfl,
      Int.toNat_of_nonneg (by omega)]
    push_cast
    ring

end Spec

/-! ### Integer `y` -/

/-- The truncation of an integer float, as a natural number, is its absolute value. -/
theorem truncToAzInt_abs_of_int {y : AzFloat} {yv : ℝ} (hy : y.toVal = some (yv : EReal))
    (hi : isInteger y = true) : (((truncToAzInt y).abs.toNat : ℕ) : ℝ) = |yv| := by
  obtain ⟨k, rfl⟩ := (isInteger_iff_of_toVal hy).mp hi
  obtain ⟨h1, -⟩ := truncToAzInt_spec hy
  set z := truncToAzInt y
  have hzk : z.toInt = k := by
    have : |((z.toInt - k : ℤ) : ℝ)| < 1 := by push_cast; exact h1
    have : |z.toInt - k| < 1 := by exact_mod_cast this
    have := Int.abs_lt_one_iff.mp this
    omega
  have htoInt : z.toInt = if z.sign then (z.abs.toNat : ℤ) else -(z.abs.toNat : ℤ) := rfl
  have : (z.abs.toNat : ℤ) = |k| := by
    rw [← hzk, htoInt]
    split_ifs
    · exact (abs_of_nonneg (Int.natCast_nonneg _)).symm
    · rw [abs_neg]; exact (abs_of_nonneg (Int.natCast_nonneg _)).symm
  rw [show ((z.abs.toNat : ℕ) : ℝ) = ((z.abs.toNat : ℤ) : ℝ) by push_cast; rfl, this]
  push_cast
  rfl

/-- **`genPochPole` decides whether `(x − n) ⋯ (x − 1)` vanishes.** -/
theorem genPochPole_iff {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (n : ℕ) :
    genPochPole x n = true ↔ ∏ j ∈ range n, (xv - n + j) = 0 := by
  unfold genPochPole
  rw [Bool.and_eq_true, Bool.and_eq_true, isInteger_iff_of_toVal hx,
    lt_eq_true_iff toVal_zero' hx, le_eq_true_iff hx (toVal_ofAzNat_ofNat n), prod_eq_zero_iff]
  constructor
  · rintro ⟨⟨⟨k, hk⟩, hpos⟩, hle⟩
    have hk0 : 0 < k := by exact_mod_cast (hk ▸ hpos : (0 : ℝ) < (k : ℝ))
    have hkn : k ≤ n := by exact_mod_cast (hk ▸ hle : (k : ℝ) ≤ (n : ℝ))
    refine ⟨n - k.toNat, mem_range.mpr (by omega), ?_⟩
    have hkc : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by
      rw [show ((k.toNat : ℕ) : ℝ) = ((k.toNat : ℤ) : ℝ) by push_cast; rfl,
        Int.toNat_of_nonneg hk0.le]
    rw [Nat.cast_sub (by omega), hkc, hk]
    ring
  · rintro ⟨j, hj, h0⟩
    have hjn : j < n := mem_range.mp hj
    have hxv : xv = ((n - j : ℕ) : ℝ) := by rw [Nat.cast_sub hjn.le]; linarith
    refine ⟨⟨⟨((n - j : ℕ) : ℤ), by rw [hxv]; push_cast; rfl⟩, ?_⟩, ?_⟩
    · rw [hxv]; exact_mod_cast Nat.sub_pos_of_lt hjn
    · rw [hxv]; exact_mod_cast Nat.sub_le n j

/-- **`recipPochIntQuot N D n` is the rounding of `1 / ((N/D − n)ₙ)`** off its poles. -/
theorem recipPochIntQuot_eq {N D : AzInt} {xv : ℝ} (hD : (0 : ℝ) < (D.toInt : ℝ))
    (hN : (N.toInt : ℝ) / (D.toInt : ℝ) = xv) {n : ℕ}
    (hne : ∏ j ∈ range n, (xv - n + j) ≠ 0) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    recipPochIntQuot N D n p mode
      = roundVal p mode (some (((∏ j ∈ range n, (xv - n + j))⁻¹ : ℝ) : EReal)) := by
  have hprod : (((risingInt (N - (n : AzInt) * D) D n).toInt : ℤ) : ℝ)
      = (D.toInt : ℝ) ^ n * ∏ j ∈ range n, (xv - n + j) := by
    rw [toInt_risingInt, AzInt.toInt_sub, AzInt.toInt_mul, AzInt.toInt_natCast]
    push_cast
    have := prod_div_pow_eq (N := (N.toInt : ℝ) - n * D.toInt) hD.ne' n
    rw [show ((N.toInt : ℝ) - n * D.toInt) / D.toInt = xv - n by rw [← hN]; field_simp] at this
    rw [← this]
    field_simp
  have hden : (((risingInt (N - (n : AzInt) * D) D n).toInt : ℤ) : ℝ) ≠ 0 := by
    rw [hprod]; exact mul_ne_zero (pow_ne_zero _ hD.ne') hne
  unfold recipPochIntQuot
  rw [divPrecRound_eq_liftVal₂, liftVal₂, toVal_ofAzInt, toVal_ofAzInt, Option.bind_some,
    Option.bind_some, Spec.div_coe_coe _ _ hden]
  congr 3
  rw [hprod, AzInt.toInt_pow]
  push_cast
  field_simp

/-- **The exact path answers with the rounding of `1 / ((x − n)ₙ)`.** -/
theorem recipPochExact?_eq {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) {n : ℕ}
    (hne : ∏ j ∈ range n, (xv - n + j) ≠ 0) (p : ℕ) [NeZero p] (mode : RoundingMode)
    {r : AzFloat × Ordering} (h : recipPochExact? x n p mode = some r) :
    r = roundVal p mode (some (((∏ j ∈ range n, (xv - n + j))⁻¹ : ℝ) : EReal)) := by
  unfold recipPochExact? at h
  split_ifs at h
  obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h
  have hav := toVal_of_toAzRat? x q hq
  rw [hx, Option.some.injEq, EReal.coe_eq_coe_iff] at hav
  exact recipPochIntQuot_eq (by rw [AzRat.toInt_toAzInt']; exact_mod_cast den_pos_real q)
    (by rw [hav]; exact mkNorm_div_den_eq q) hne p mode

theorem recipPochSplit_le (x : AzFloat) (n : ℕ) : recipPochSplit x n ≤ n := by
  unfold recipPochSplit
  split_ifs <;> first | exact Nat.zero_le n | exact le_rfl | exact Nat.sub_le _ _

/-- **`recipPochCoreOf` answers with the sign and a positive enclosure of `|1 / (s)ₙ|`.** -/
theorem recipPochCoreOf_spec {S : ℕ → Encl} {sv : ℝ} (hS : ∀ V, 64 ≤ V → IsEncl (S V) sv)
    {k n : ℕ} (hk : k ≤ n) {bits w : ℕ} (hw : 64 ≤ w) {neg : Bool} {r : Encl}
    (h : recipPochCoreOf S k n bits w = some (neg, r)) :
    IsEnclPos r ((if neg then -1 else 1) * (∏ j ∈ range n, (sv + j))⁻¹) := by
  unfold recipPochCoreOf at h
  obtain ⟨c, hc, heq⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨neg', E⟩ := c
  rw [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  have hE := pochCoreOf_spec hS hk hw hc
  have : NeZero (w + 32) := ⟨by omega⟩
  have := enclosesPos_one.div (w := w + 32) (by omega) hE
  convert this using 1
  cases neg'
  · simp only [Bool.false_eq_true, ↓reduceIte, one_mul, one_div]
  · simp only [↓reduceIte]
    rw [neg_one_mul, neg_one_mul, one_div, inv_neg]

/-- **`recipPochCore` answers with the sign and a positive enclosure of
`|1 / ((x − n)ₙ)|`.** -/
theorem recipPochCore_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) {n w : ℕ}
    (hw : 64 ≤ w) {neg : Bool} {r : Encl} (h : recipPochCore x n w = some (neg, r)) :
    IsEnclPos r ((if neg then -1 else 1) * (∏ j ∈ range n, (xv - n + j))⁻¹) := by
  have hX : IsEncl (Encl.exact x) xv := ⟨xv, xv, hx, hx, le_rfl, le_rfl⟩
  exact recipPochCoreOf_spec (sv := xv - n)
    (fun V hV => by
      have : NeZero V := ⟨by omega⟩
      exact hX.sub (isEncl0_nat n).encloses) (recipPochSplit_le x n) hw h

/-- `genPochNegInt` is the correct rounding of `Γ(x − n)/Γ(x)`, or the fuel ran out. -/
theorem genPochNegInt_eq_or {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) {n : ℕ}
    (hn : n ≠ 0) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    genPochNegInt x n p mode = roundVal p mode (Spec.genPochhammerReal xv (-(n : ℝ))) ∨
      genPochNegInt x n p mode = (nan, .eq) := by
  unfold genPochNegInt
  rw [Spec.genPochhammerReal_neg_nat xv hn]
  by_cases hpole : genPochPole x n = true
  · left
    rw [ite_eq_left hpole, ite_eq_left ((genPochPole_iff hx n).mp hpole), roundVal_none]
  have hne : ∏ j ∈ range n, (xv - n + j) ≠ 0 := fun h0 => hpole ((genPochPole_iff hx n).mpr h0)
  rw [ite_eq_right hpole, ite_eq_right (NeZero.ne p), ite_eq_right hne]
  split
  · next r hr => left; exact recipPochExact?_eq hx hne p mode hr
  · rcases eq_or_ne (zivLoop (fun w => gammaApproxOf (recipPochCore x n w) w) p mode gammaFuel
      (max 64 (p + 32))) (nan, .eq) with hzv | hzv
    · right; exact hzv
    · left
      exact zivLoop_eq_of_ne_nan_or_none p mode _ _ 64
        (fun w hw => gammaApproxOf_valid_or_none
          (fun _ _ hc => recipPochCore_spec hx hw hc) w p mode)
        _ _ (le_max_left _ _) hzv

/-! ### A `y` that is not an integer -/

/-- **`lnAbsGammaQuotEncl` answers with the sign of `Γ(s)/Γ(x)` and an enclosure of the
logarithm of its absolute value**, for arguments given by enclosures. -/
theorem lnAbsGammaQuotEncl_spec {X S : ℕ → Encl} {xv sv : ℝ}
    (hX : ∀ V, 64 ≤ V → IsEncl (X V) xv) (hS : ∀ V, 64 ≤ V → IsEncl (S V) sv) {ex es : AzInt}
    {Fx Fs : ℕ → Option (Bool × AzInt × Encl)}
    (hFx : ∀ W σ k E, 64 ≤ W → Fx W = some (σ, k, E) →
      IsEnclPos E ((if σ then -1 else 1) * (xv - k.toInt)))
    (hFs : ∀ W σ k E, 64 ≤ W → Fs W = some (σ, k, E) →
      IsEnclPos E ((if σ then -1 else 1) * (sv - k.toInt)))
    {w : ℕ} (hw : 64 ≤ w) {ws : ℕ} (hws : 64 ≤ ws) {neg : Bool} {r : Encl}
    (h : lnAbsGammaQuotEncl X S ex es Fx Fs w ws = some (neg, r)) :
    0 < (if neg then -1 else 1) * (Real.Gamma sv / Real.Gamma xv) ∧
      IsEncl r (Real.log ((if neg then -1 else 1) * (Real.Gamma sv / Real.Gamma xv))) := by
  unfold lnAbsGammaQuotEncl at h
  dsimp only at h
  set L := lnGammaShiftExp w
  set V := w + 2 * L + 8 + 2 * w.log2 with hVdef
  have hV : 64 ≤ V := by omega
  have : NeZero V := ⟨by omega⟩
  have hV2 : 2 ≤ V := by omega
  have hPi := enclosesPos_pi hV
  have hM : ∀ a b : ℕ, 1 ≤ max (lnGammaTerms w a) (lnGammaTerms w b) := fun a b =>
    le_trans (le_trans (by norm_num) (Nat.le_add_left 3 _)) (le_max_right _ _)
  split at h
  · rename_i ns ts qs nx tx qx h1 h2
    rw [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨tsv, qsv, g1, g2, g3, g4⟩ := lnGammaPiece_spec (hS V hV)
      (fun σ k E hF => hFs _ σ k E (by omega) hF) hPi hV (hM _ _) hws h1
    obtain ⟨txv, qxv, e1, e2, e3, e4⟩ := lnGammaPiece_spec (hX V hV)
      (fun σ k E hF => hFx _ σ k E (by omega) hF) hPi hV (hM _ _) hws h2
    have hqs : 0 < qsv := by obtain ⟨l, u, -, -, h0, h1', -⟩ := g2; linarith
    have hqx : 0 < qxv := by obtain ⟨l, u, -, -, h0, h1', -⟩ := e2; linarith
    have hval : (if (ns != nx) = true then (-1 : ℝ) else 1) * (Real.Gamma sv / Real.Gamma xv)
        = ((if ns = true then (-1 : ℝ) else 1) * Real.Gamma sv)
          / ((if nx = true then (-1 : ℝ) else 1) * Real.Gamma xv) := by
      cases ns <;> cases nx <;> simp [neg_div, div_neg]
    rw [hval]
    refine ⟨div_pos g3 e3, ?_⟩
    have hQ := lnOfEncl_pos (g2.div hV2 e2) hV
    have := ((g1.sub (w := V) e1)).add (w := V) hQ.half
    convert this using 1
    rw [Real.log_div g3.ne' e3.ne', g4, e4, Real.log_div hqs.ne' hqx.ne']
    ring
  · exact absurd h (by simp)

/-- **`gammaQuotEnclOf` answers with the sign and a positive enclosure of `|Γ(s)/Γ(x)|`.** -/
theorem gammaQuotEnclOf_spec {X S : ℕ → Encl} {xv sv : ℝ}
    (hX : ∀ V, 64 ≤ V → IsEncl (X V) xv) (hS : ∀ V, 64 ≤ V → IsEncl (S V) sv) {ex es : AzInt}
    {Fx Fs : ℕ → Option (Bool × AzInt × Encl)}
    (hFx : ∀ W σ k E, 64 ≤ W → Fx W = some (σ, k, E) →
      IsEnclPos E ((if σ then -1 else 1) * (xv - k.toInt)))
    (hFs : ∀ W σ k E, 64 ≤ W → Fs W = some (σ, k, E) →
      IsEnclPos E ((if σ then -1 else 1) * (sv - k.toInt)))
    {w : ℕ} (hw : 64 ≤ w) {neg : Bool} {r : Encl}
    (h : gammaQuotEnclOf X S ex es Fx Fs w = some (neg, r)) :
    IsEnclPos r ((if neg then -1 else 1) * (Real.Gamma sv / Real.Gamma xv)) := by
  unfold gammaQuotEnclOf at h
  obtain ⟨c, hc, hr⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨neg', Lg⟩ := c
  obtain ⟨g, hg, hgeq⟩ := Option.map_eq_some_iff.mp hr
  rw [Prod.mk.injEq] at hgeq
  obtain ⟨rfl, rfl⟩ := hgeq
  obtain ⟨hpos, hL⟩ := lnAbsGammaQuotEncl_spec hX hS hFx hFs (by omega) hw hc
  have := gammaExpEncl_spec hL hw hg
  simp only [Bool.false_eq_true, ↓reduceIte] at this
  rwa [Real.exp_log hpos] at this

/-- **`genPochCore` answers with the sign and a positive enclosure of
`|Γ(x + y)/Γ(x)|`.** -/
theorem genPochCore_spec {x y : AzFloat} {xv yv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hy : y.toVal = some (yv : EReal)) {w : ℕ} (hw : 64 ≤ w) {neg : Bool} {r : Encl}
    (h : genPochCore x y w = some (neg, r)) :
    IsEnclPos r ((if neg then -1 else 1) * (Real.Gamma (xv + yv) / Real.Gamma xv)) := by
  have hX : IsEncl (Encl.exact x) xv := ⟨xv, xv, hx, hx, le_rfl, le_rfl⟩
  have hY : IsEncl (Encl.exact y) yv := ⟨yv, yv, hy, hy, le_rfl, le_rfl⟩
  unfold genPochCore at h
  refine gammaQuotEnclOf_spec ?_ ?_ ?_ ?_ hw h
  · exact fun _ _ => hX
  · intro V hV
    have : NeZero V := ⟨by omega⟩
    exact hX.add hY
  · intro W σ k E hW hF
    have : NeZero W := ⟨by omega⟩
    exact gammaFloatFrac_spec hx hF
  · intro W σ k E hW hF
    have : NeZero W := ⟨by omega⟩
    exact betaSumFrac_spec hx hy hF

/-! ### The driver -/

open Classical in
/-- `genPochReal` is the correct rounding of `Γ(x + y)/Γ(x)`, or the fuel ran out. -/
theorem genPochReal_eq_or {x y : AzFloat} {xv yv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hy : y.toVal = some (yv : EReal)) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    genPochReal x y p mode = roundVal p mode (Spec.genPochhammerReal xv yv) ∨
      genPochReal x y p mode = (nan, .eq) := by
  unfold genPochReal
  by_cases hi : isInteger y = true
  · rw [ite_eq_left hi]
    have habs := truncToAzInt_abs_of_int hy hi
    set n := (truncToAzInt y).abs.toNat
    by_cases h0 : le zero y = true
    · rw [ite_eq_left h0]
      have hy0 : 0 ≤ yv := (le_eq_true_iff toVal_zero' hy).mp h0
      rw [abs_of_nonneg hy0] at habs
      rw [← habs, Spec.genPochhammerReal_nat]
      exact pochReal_eq_or hx n p mode
    · rw [ite_eq_right h0]
      have hy0 : yv < 0 := not_le.mp fun h => h0 ((le_eq_true_iff toVal_zero' hy).mpr h)
      rw [abs_of_neg hy0] at habs
      have hn : n ≠ 0 := fun hn => by rw [hn] at habs; simp at habs; linarith
      rw [show yv = -(n : ℝ) by linarith]
      exact genPochNegInt_eq_or hx hn p mode
  rw [ite_eq_right hi]
  have hni : ¬ ∃ k : ℤ, yv = k := fun h => hi ((isInteger_iff_of_toVal hy).mpr h)
  have hspec : Spec.genPochhammerReal xv yv =
      if xv + yv ≤ 0 ∧ ∃ k : ℤ, xv + yv = k then none
      else some ((Real.Gamma (xv + yv) / Real.Gamma xv : ℝ) : EReal) := by
    unfold Spec.genPochhammerReal
    rw [ite_eq_right hni]
  rw [hspec]
  by_cases hxp : (isInteger x && le x zero) = true
  · left
    rw [ite_eq_left hxp]
    rw [Bool.and_eq_true, isInteger_iff_of_toVal hx, le_eq_true_iff hx toVal_zero'] at hxp
    obtain ⟨⟨k, hk⟩, hle⟩ := hxp
    have hns : ¬ (xv + yv ≤ 0 ∧ ∃ k : ℤ, xv + yv = k) := by
      rintro ⟨-, j, hj⟩
      exact hni ⟨j - k, by push_cast; linarith⟩
    rw [ite_eq_right hns, gamma_eq_zero_of_nonpos_int hle hk, div_zero, EReal.coe_zero,
      roundVal_zero]
  rw [ite_eq_right hxp]
  by_cases hs : sumIsNonposInt x y = true
  · left
    rw [ite_eq_left hs, ite_eq_left ((sumIsNonposInt_iff hx hy).mp hs), roundVal_none]
  rw [ite_eq_right hs, ite_eq_right (NeZero.ne p),
    ite_eq_right (fun h => hs ((sumIsNonposInt_iff hx hy).mpr h))]
  rcases eq_or_ne (zivLoop (fun w => gammaApproxOf (genPochCore x y w) w) p mode gammaFuel
    (max 64 (p + 32))) (nan, .eq) with hz | hz
  · right; exact hz
  · left
    exact zivLoop_eq_of_ne_nan_or_none p mode _ _ 64
      (fun w hw => gammaApproxOf_valid_or_none
        (fun _ _ hc => genPochCore_spec hx hy hw hc) w p mode)
      _ _ (le_max_left _ _) hz

/-- **The generalized Pochhammer symbol is correctly rounded, or the fuel ran out.** -/
theorem genPochhammerPrecRound_eq_or (x y : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    genPochhammerPrecRound x y p mode = liftVal₂ Spec.genPochhammer x y p mode ∨
      genPochhammerPrecRound x y p mode = (nan, .eq) := by
  unfold liftVal₂
  cases x with
  | nan => left; simp [genPochhammerPrecRound, toVal_nan]
  | infinity s =>
    left
    cases y <;> cases s <;> simp [genPochhammerPrecRound, Spec.genPochhammer]
  | zero =>
    cases y with
    | nan => left; simp [genPochhammerPrecRound, toVal_nan]
    | infinity s => left; cases s <;> simp [genPochhammerPrecRound, Spec.genPochhammer]
    | zero =>
      simp only [genPochhammerPrecRound, toVal_zero, Option.bind_some]
      rw [← EReal.coe_zero, Spec.genPochhammer_coe]
      exact genPochReal_eq_or toVal_zero' toVal_zero' p mode
    | finite s e q m hv =>
      simp only [genPochhammerPrecRound, toVal_zero, toVal_finite, Option.bind_some]
      rw [← EReal.coe_zero, Spec.genPochhammer_coe]
      exact genPochReal_eq_or toVal_zero' (toVal_finite s e q m hv) p mode
  | finite s e q m hv =>
    cases y with
    | nan => left; simp [genPochhammerPrecRound, toVal_nan]
    | infinity s' => left; cases s' <;> simp [genPochhammerPrecRound, Spec.genPochhammer]
    | zero =>
      simp only [genPochhammerPrecRound, toVal_zero, toVal_finite, Option.bind_some]
      rw [← EReal.coe_zero, Spec.genPochhammer_coe]
      exact genPochReal_eq_or (toVal_finite s e q m hv) toVal_zero' p mode
    | finite s' e' q' m' hv' =>
      simp only [genPochhammerPrecRound, toVal_finite, Option.bind_some]
      rw [Spec.genPochhammer_coe]
      exact genPochReal_eq_or (toVal_finite s e q m hv) (toVal_finite s' e' q' m' hv') p mode

end Azurite.AzFloat
