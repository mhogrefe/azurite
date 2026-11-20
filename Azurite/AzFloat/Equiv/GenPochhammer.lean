/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.GenPochhammer
import Azurite.AzFloat.Equiv.PochhammerWidth

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

/-- **The split of `(x − n)ₙ` is right**: off the poles, both rising factorials have a
positive first factor. -/
theorem recipPochSplit_facts {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) {n : ℕ}
    (hpole : ¬ genPochPole x n = true) :
    (recipPochSplit x n ≠ 0 → 0 < 1 - (xv - n) - (recipPochSplit x n : ℕ)) ∧
      (n - recipPochSplit x n ≠ 0 → 0 < xv - n + (recipPochSplit x n : ℕ)) := by
  have hp' : ¬ ((∃ k : ℤ, xv = k) ∧ 0 < xv ∧ xv ≤ n) := by
    rintro ⟨h1, h2, h3⟩
    refine hpole ?_
    unfold genPochPole
    rw [Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨⟨(isInteger_iff_of_toVal hx).mpr h1, (lt_eq_true_iff toVal_zero' hx).mpr h2⟩,
      (le_eq_true_iff hx (toVal_ofAzNat_ofNat n)).mpr h3⟩
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  unfold recipPochSplit
  by_cases c1 : le (ofAzNat (AzNat.ofNat n)) x = true
  · rw [ite_eq_left c1]
    have h1 : (n : ℝ) ≤ xv := (le_eq_true_iff (toVal_ofAzNat_ofNat n) hx).mp c1
    refine ⟨fun h => absurd rfl h, fun h => ?_⟩
    have hn : 0 < n := by omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    rw [Nat.cast_zero, add_zero]
    rcases h1.eq_or_lt with h' | h'
    · exact absurd ⟨⟨(n : ℤ), by rw [← h']; push_cast; rfl⟩, by linarith, h'.symm.le⟩ hp'
    · linarith
  rw [ite_eq_right c1]
  have hlt : xv < n := by
    by_contra h
    exact c1 ((le_eq_true_iff (toVal_ofAzNat_ofNat n) hx).mpr (not_lt.mp h))
  by_cases c2 : le x zero = true
  · rw [ite_eq_left c2]
    have h2 : xv ≤ 0 := (le_eq_true_iff hx toVal_zero').mp c2
    exact ⟨fun _ => by linarith, fun h => absurd (Nat.sub_self n) h⟩
  rw [ite_eq_right c2]
  have hpos : 0 < xv := by
    by_contra h
    exact c2 ((le_eq_true_iff hx toVal_zero').mpr (not_lt.mp h))
  have hni : ¬ ∃ k : ℤ, xv = k := fun h => hp' ⟨h, hpos, hlt.le⟩
  rw [toNat_abs_eq_natAbs]
  obtain ⟨t, ht⟩ : ∃ t : ℤ, t = (truncToAzInt x).toInt := ⟨_, rfl⟩
  obtain ⟨ht1, ht2⟩ := truncToAzInt_spec hx
  rw [← ht] at ht1 ht2 ⊢
  have ht1' := abs_lt.mp ht1
  have ht0 : 0 ≤ t := by
    have : (-1 : ℝ) < t := by linarith
    have : (-1 : ℤ) < t := by exact_mod_cast this
    omega
  have ht0' : (0 : ℝ) ≤ t := by exact_mod_cast ht0
  rw [abs_of_nonneg ht0', abs_of_pos hpos] at ht2
  have hxt : (t : ℝ) < xv := lt_of_le_of_ne ht2 fun h => hni ⟨t, h.symm⟩
  have htn : t.natAbs ≤ n := by
    have : (t : ℝ) < n := by linarith
    have : t < (n : ℤ) := by exact_mod_cast this
    omega
  have hm : ((t.natAbs : ℕ) : ℝ) = (t : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg ht0']
  rw [Nat.cast_sub htn, hm]
  exact ⟨fun _ => by linarith, fun _ => by linarith⟩

/-- **The core of `1 / ((x − n)ₙ)` converges** off the poles. -/
theorem recipPochCore_coreConv {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    {n : ℕ} (hpole : ¬ genPochPole x n = true) :
    CoreConv (recipPochCore x n) (∏ j ∈ range n, (xv - n + j))⁻¹ := by
  obtain ⟨h1, h2⟩ := recipPochSplit_facts hx hpole
  exact (pochCoreOf_coreConv (X := fun V => Encl.sub V (Encl.exact x) (Encl.nat n))
    (xv := xv - n) (fun V hV => by
      have : NeZero V := ⟨by omega⟩
      exact (AEncl.exact_level hx V).sub_level (AEncl.exact_level (toVal_ofAzNat_ofNat n) V))
    (recipPochSplit_le x n) h1 h2 _).recip

/-- **`genPochNegIntFuel` is exact or a convergent loop.** -/
theorem genPochNegIntFuel_zivCases {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    {n : ℕ} (hn : n ≠ 0) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    ZivCases (fun fuel => genPochNegIntFuel fuel x n p mode)
      (Spec.genPochhammerReal xv (-(n : ℝ))) p mode := by
  rw [Spec.genPochhammerReal_neg_nat xv hn]
  by_cases hpole : genPochPole x n = true
  · refine Or.inl fun fuel => ?_
    show genPochNegIntFuel fuel x n p mode = _
    unfold genPochNegIntFuel
    rw [ite_eq_left hpole, ite_eq_left ((genPochPole_iff hx n).mp hpole), roundVal_none]
  have hne : ∏ j ∈ range n, (xv - n + j) ≠ 0 := fun h0 => hpole ((genPochPole_iff hx n).mpr h0)
  rw [ite_eq_right hne]
  cases hr : recipPochExact? x n p mode with
  | some r =>
    refine Or.inl fun fuel => ?_
    show genPochNegIntFuel fuel x n p mode = _
    unfold genPochNegIntFuel
    rw [ite_eq_right hpole, ite_eq_right (NeZero.ne p), hr]
    exact recipPochExact?_eq hx hne p mode hr
  | none =>
    refine (ZivCases.of_core (recipPochCore_coreConv hx hpole)
      (fun w hw neg b hc => recipPochCore_spec hx hw hc) p mode).congr fun fuel => ?_
    show genPochNegIntFuel fuel x n p mode = _
    unfold genPochNegIntFuel
    rw [ite_eq_right hpole, ite_eq_right (NeZero.ne p), hr]

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

/-! ### The convergence of the quotient -/

open Filter Topology in
/-- **The subtraction and the logarithm of `q_s / q_x`.** -/
theorem quotCombine_width {V : ℕ} (hV : 64 ≤ V) {ts tx qs qx : Encl}
    {tsv txv qsv qxv εs εx ls lx Gs Gx : ℝ}
    (hts : AEncl ts tsv εs) (htx : AEncl tx txv εx)
    (hqs : LEncl qs qsv ls) (hqx : LEncl qx qxv lx) (hls : 0 ≤ ls) (hlx : 0 ≤ lx)
    (hlam : ls + lx + 6 * (1 / 2 : ℝ) ^ V ≤ 1 / 2) (hεs : εs ≤ 1) (hεx : εx ≤ 1)
    (hGs : |tsv| ≤ Gs) (hGx : |txv| ≤ Gx)
    (hGs' : |Real.log qsv| ≤ Gs) (hGx' : |Real.log qxv| ≤ Gx)
    (hlnW : lnW (Gs + Gx) V ≤ 1) :
    AEncl (Encl.add V (Encl.sub V ts tx) (Encl.half (lnOfEncl (Encl.div V qs qx) V)))
      (tsv - txv + Real.log (qsv / qxv) / 2)
      (εs + εx + (lnW (Gs + Gx) V + 5 * (ls + lx + 6 * (1 / 2 : ℝ) ^ V)) / 2
        + 8 * (2 * (Gs + Gx) + 6) * (1 / 2 : ℝ) ^ V) := by
  have : NeZero V := ⟨by omega⟩
  have hu8 : (1 / 2 : ℝ) ^ V ≤ 1 / 8 := half_pow_le_eighth (by omega)
  have hu64 : (1 / 2 : ℝ) ^ V ≤ 1 / 64 := by
    calc (1 / 2 : ℝ) ^ V ≤ (1 / 2 : ℝ) ^ 6 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 64 := by norm_num
  have hu0 : (0 : ℝ) < (1 / 2 : ℝ) ^ V := by positivity
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = Gs + Gx := ⟨_, rfl⟩
  rw [← hG] at hlnW ⊢
  have a1 := abs_le.mp hGs
  have a2 := abs_le.mp hGx
  have b1 := abs_le.mp hGs'
  have b2 := abs_le.mp hGx'
  have hG0 : 0 ≤ G := by linarith
  have hεs0 : 0 ≤ εs := by obtain ⟨l, u, -, -, c1, c2, c3⟩ := hts; linarith
  have hεx0 : 0 ≤ εx := by obtain ⟨l, u, -, -, c1, c2, c3⟩ := htx; linarith
  have hGu : (2 * G + 6) * (1 / 2 : ℝ) ^ V ≤ (2 * G + 6) / 64 := by
    have := mul_le_mul_of_nonneg_left hu64 (by linarith : (0 : ℝ) ≤ 2 * G + 6)
    linarith
  have hGu0 : 0 ≤ (2 * G + 6) * (1 / 2 : ℝ) ^ V := by positivity
  have h2 := hts.sub (w := V) htx (B := 2 * G + 6) (by
    have : |tsv - txv| ≤ G := by rw [abs_le]; constructor <;> linarith
    linarith)
  have hqs0 := hqs.pos
  have hqx0 := hqx.pos
  have hlogQ : Real.log (qsv / qxv) = Real.log qsv - Real.log qxv :=
    Real.log_div hqs0.ne' hqx0.ne'
  have hQG : |Real.log (qsv / qxv)| ≤ G := by
    rw [hlogQ, abs_le]; constructor <;> linarith
  have hQ := hqs.div hu8 hqx
  have hL := (hQ.lnOfEncl (by positivity) hlam hQG hV).half
  have hlnW0 := lnW_nonneg hG0 V
  have h3 := h2.add (w := V) hL (B := 2 * G + 6) (by
    have hQa := abs_le.mp hQG
    have : |tsv - txv + Real.log (qsv / qxv) / 2| ≤ G + G / 2 := by
      rw [abs_le]; constructor <;> linarith
    linarith)
  refine h3.mono (le_of_eq ?_)
  ring

/-- The number of terms shared by the two pieces. -/
def quotTerms (ex es : AzInt) (W : ℕ) : ℕ := max (lgTerms ex W) (lgTerms es W)

theorem lnAbsGammaQuotEncl_eq (X S : ℕ → Encl) (ex es : AzInt)
    (Fx Fs : ℕ → Option (Bool × AzInt × Encl)) (W ws : ℕ) :
    lnAbsGammaQuotEncl X S ex es Fx Fs W ws
      = match pieceAt S Fs es (quotTerms ex es W) W ws,
          pieceAt X Fx ex (quotTerms ex es W) W ws with
        | some (ns, ts, qs), some (nx, tx, qx) =>
          some (ns != nx,
            Encl.add (W + 2 * lnGammaShiftExp W + 8 + 2 * W.log2)
              (Encl.sub (W + 2 * lnGammaShiftExp W + 8 + 2 * W.log2) ts tx)
              (Encl.half (lnOfEncl (Encl.div (W + 2 * lnGammaShiftExp W + 8 + 2 * W.log2)
                qs qx) (W + 2 * lnGammaShiftExp W + 8 + 2 * W.log2))))
        | _, _ => none := rfl

open Filter Topology in
/-- **The enclosure of `ln |Γ(s) / Γ(x)|` converges** at convergent arguments: at every large
level it answers, with a width that tends to `0`. -/
theorem lnAbsGammaQuotEncl_conv {X S : ℕ → Encl} {Fx Fs : ℕ → Option (Bool × AzInt × Encl)}
    {xv sv : ℝ} (hX : ArgConv X Fx xv) (hS : ArgConv S Fs sv) (ex es : AzInt) (c : ℕ) :
    ∃ E : ℕ → ℝ, Tendsto E atTop (𝓝 0) ∧ ∀ᶠ w in atTop, ∃ (neg : Bool) (r : Encl) (x : ℝ),
      lnAbsGammaQuotEncl X S ex es Fx Fs (w + c) w = some (neg, r) ∧ AEncl r x (E w) := by
  have hm4 : ∀ w, 4 ≤ quotTerms ex es w := fun w =>
    le_trans (lgTerms_le ex w).1 (le_max_left _ _)
  have hm : ∀ w, quotTerms ex es w ≤ w / 2 + 4 := fun w =>
    max_le (lgTerms_le ex w).2 (lgTerms_le es w).2
  have hmt : Tendsto (fun w => 2 * quotTerms ex es w - 1) atTop atTop :=
    tendsto_atTop_mono (fun w => by
      have : lgTerms ex w ≤ quotTerms ex es w := le_max_left _ _
      omega) (tendsto_lgTerms ex)
  obtain ⟨Es, ls, Gs, hEs, hls, hGs, hevs⟩ := pieceAt_conv hS es c hm4 hm hmt
  obtain ⟨Ex, lx, Gx, hEx, hlx, hGx, hevx⟩ := pieceAt_conv hX ex c hm4 hm hmt
  have hG : PB fun w => Gs w + Gx w := hGs.add hGx
  have hcast : (fun w : ℕ => ((w + c : ℕ) : ℝ)) = fun w : ℕ => (w : ℝ) + c := by
    funext w
    push_cast
    rfl
  have hPBw : PB fun w : ℕ => ((w + c : ℕ) : ℝ) := by
    rw [hcast]
    exact PB.natCast.add (PB.const _)
  have hT1 : Tendsto (fun w : ℕ => 2 ^ 42
      * (6 * ((w + c : ℕ) : ℝ) + 2 * (Gs w + Gx w) + 10) ^ 5 * (1 / 2 : ℝ) ^ w) atTop
      (𝓝 0) :=
    (((((hPBw.const_mul 6).add (hG.const_mul 2)).add (PB.const 10)).pow 5).const_mul _).tendsto
  have hT2 : Tendsto (fun w : ℕ => 8 * (2 * (Gs w + Gx w) + 6) * (1 / 2 : ℝ) ^ w)
      atTop (𝓝 0) := (((hG.const_mul 2).add (PB.const 6)).const_mul 8).tendsto
  have hpow : Tendsto (fun w : ℕ => (1 / 2 : ℝ) ^ w) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hlam : Tendsto (fun w => ls w + lx w + 6 * (1 / 2 : ℝ) ^ w) atTop (𝓝 0) := by
    simpa using (hls.add hlx).add (hpow.const_mul 6)
  have hE : Tendsto (fun w => Es w + Ex w
      + (2 ^ 42 * (6 * ((w + c : ℕ) : ℝ) + 2 * (Gs w + Gx w) + 10) ^ 5 * (1 / 2 : ℝ) ^ w
        + 5 * (ls w + lx w + 6 * (1 / 2 : ℝ) ^ w)) / 2
      + 8 * (2 * (Gs w + Gx w) + 6) * (1 / 2 : ℝ) ^ w) atTop (𝓝 0) := by
    simpa using ((hEs.add hEx).add ((hT1.add (hlam.const_mul 5)).div_const 2)).add hT2
  refine ⟨_, hE, ?_⟩
  filter_upwards [hevs, hevx, hEs.eventually (ge_mem_nhds one_pos),
    hEx.eventually (ge_mem_nhds one_pos), hT1.eventually (ge_mem_nhds one_pos),
    hlam.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)), eventually_ge_atTop 64]
    with w hs hx h1 h2 h4 h5 h6
  obtain ⟨ns, ts, qs, tsv, qsv, hps, hts, hqs, hls0, hGs1, hGs2⟩ := hs
  obtain ⟨nx, tx, qx, txv, qxv, hpx, htx, hqx, hlx0, hGx1, hGx2⟩ := hx
  rw [lnAbsGammaQuotEncl_eq, hps, hpx]
  obtain ⟨V, hV⟩ : ∃ V : ℕ, V = w + c + 2 * lnGammaShiftExp (w + c) + 8 + 2 * (w + c).log2 :=
    ⟨_, rfl⟩
  rw [← hV]
  have hLlog := shiftExp_le_log2 (by omega : 4 ≤ w + c)
  have hlogw := log2_le_self (w + c)
  have hV64 : 64 ≤ V := by omega
  have hu0 : (0 : ℝ) < (1 / 2 : ℝ) ^ V := by positivity
  have hu : (1 / 2 : ℝ) ^ V ≤ (1 / 2 : ℝ) ^ w :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hG0 : 0 ≤ Gs w + Gx w := by
    have := (abs_nonneg tsv).trans hGs1
    have := (abs_nonneg txv).trans hGx1
    linarith
  have hlnW : lnW (Gs w + Gx w) V
      ≤ 2 ^ 42 * (6 * ((w + c : ℕ) : ℝ) + 2 * (Gs w + Gx w) + 10) ^ 5 * (1 / 2 : ℝ) ^ w := by
    refine (lnW_le hG0 (w := w + c) (by omega) (by omega)).trans ?_
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_right w c)) (by positivity)
  have key := quotCombine_width hV64 hts htx hqs hqx hls0 hlx0 (by linarith)
    h1 h2 hGs1 hGx1 hGs2 hGx2 (hlnW.trans h4)
  refine ⟨_, _, _, rfl, key.mono ?_⟩
  have h7 : 8 * (2 * (Gs w + Gx w) + 6) * (1 / 2 : ℝ) ^ V
      ≤ 8 * (2 * (Gs w + Gx w) + 6) * (1 / 2 : ℝ) ^ w :=
    mul_le_mul_of_nonneg_left hu (by positivity)
  linarith

/-- **The core of `Γ(s) / Γ(x)` converges** at convergent arguments. -/
theorem gammaQuotEnclOf_coreConv {X S : ℕ → Encl} {Fx Fs : ℕ → Option (Bool × AzInt × Encl)}
    {xv sv : ℝ} (hX : ArgConv X Fx xv) (hS : ArgConv S Fs sv) {ex es : AzInt}
    (hFx : ∀ W σ k E, 64 ≤ W → Fx W = some (σ, k, E) →
      IsEnclPos E ((if σ then -1 else 1) * (xv - k.toInt)))
    (hFs : ∀ W σ k E, 64 ≤ W → Fs W = some (σ, k, E) →
      IsEnclPos E ((if σ then -1 else 1) * (sv - k.toInt))) :
    CoreConv (gammaQuotEnclOf X S ex es Fx Fs) (Real.Gamma sv / Real.Gamma xv) := by
  obtain ⟨E, hE, hev⟩ := lnAbsGammaQuotEncl_conv hX hS ex es
    (max (gammaLnBits ex) (gammaLnBits es))
  obtain ⟨Kx, hKx⟩ := hX.1
  obtain ⟨Ks, hKs⟩ := hS.1
  obtain ⟨Qv, hQv⟩ : ∃ Qv : ℝ, Qv = Real.Gamma sv / Real.Gamma xv := ⟨_, rfl⟩
  rw [← hQv]
  obtain ⟨ht, hevE⟩ := gammaExpEncl_eventually false (Real.log |Qv|) hE
  simp only [Bool.false_eq_true, ↓reduceIte] at ht hevE
  refine ⟨_, ht, ?_⟩
  filter_upwards [hev, hevE, Filter.eventually_ge_atTop 64] with w h1 h2 h3
  obtain ⟨neg, r, x, hc, hr⟩ := h1
  obtain ⟨hpos, hL⟩ := lnAbsGammaQuotEncl_spec (fun V hV => (hKx V hV).isEncl)
    (fun V hV => (hKs V hV).isEncl) hFx hFs
    (by omega : 64 ≤ w + max (gammaLnBits ex) (gammaLnBits es)) h3 hc
  rw [← hQv] at hpos hL
  have habs := sign_mul_eq_abs hpos
  rw [habs] at hL
  have hB0 : 0 < |Qv| := habs ▸ hpos
  obtain ⟨b, hb, hb1, hb2⟩ := h2 r (hr.of_isEncl hL)
  rw [Real.exp_log hB0] at hb1 hb2
  refine ⟨neg, b, ?_, ?_, ?_⟩
  · unfold gammaQuotEnclOf
    rw [hc, Option.bind_some, hb, Option.map_some]
  · rw [habs]; exact hb1
  · rw [habs]; exact hb2

/-- **The core of `Γ(x + y)/Γ(x)` converges** for floats where neither `x` nor `x + y` is `0`
or a negative integer. -/
theorem genPochCore_coreConv {x y : AzFloat} {xv yv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hy : y.toVal = some (yv : EReal)) (hX : 0 < xv ∨ (xv < 0 ∧ ∀ k : ℤ, xv ≠ k))
    (hS : 0 < xv + yv ∨ (xv + yv < 0 ∧ ∀ k : ℤ, xv + yv ≠ k)) :
    CoreConv (genPochCore x y) (Real.Gamma (xv + yv) / Real.Gamma xv) :=
  (gammaQuotEnclOf_coreConv (argConv_float hx hX) (argConv_sum hx hy hS)
    (ex := expOf x) (es := (if expOf x ≤ expOf y then expOf y else expOf x) + 1)
    (fun W σ k E hW hF => by
      have : NeZero W := ⟨by omega⟩
      exact gammaFloatFrac_spec hx hF)
    (fun W σ k E hW hF => by
      have : NeZero W := ⟨by omega⟩
      exact betaSumFrac_spec hx hy hF)).congr fun _ => rfl

/-! ### The driver -/

open Classical in
/-- **`genPochRealFuel` is exact or a convergent loop.** -/
theorem genPochRealFuel_zivCases {x y : AzFloat} {xv yv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hy : y.toVal = some (yv : EReal)) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    ZivCases (fun fuel => genPochRealFuel fuel x y p mode) (Spec.genPochhammerReal xv yv)
      p mode := by
  by_cases hi : isInteger y = true
  · have habs := truncToAzInt_abs_of_int hy hi
    obtain ⟨n, hn⟩ : ∃ n : ℕ, n = (truncToAzInt y).abs.toNat := ⟨_, rfl⟩
    rw [← hn] at habs
    by_cases h0 : le zero y = true
    · have hy0 : 0 ≤ yv := (le_eq_true_iff toVal_zero' hy).mp h0
      rw [abs_of_nonneg hy0] at habs
      rw [← habs, Spec.genPochhammerReal_nat]
      refine (pochRealFuel_zivCases hx n p mode).congr fun fuel => ?_
      show genPochRealFuel fuel x y p mode = _
      unfold genPochRealFuel
      rw [ite_eq_left hi, ite_eq_left h0, ← hn]
    · have hy0 : yv < 0 := not_le.mp fun h => h0 ((le_eq_true_iff toVal_zero' hy).mpr h)
      rw [abs_of_neg hy0] at habs
      have hn0 : n ≠ 0 := fun h => by rw [h] at habs; simp at habs; linarith
      rw [show yv = -(n : ℝ) by linarith]
      refine (genPochNegIntFuel_zivCases hx hn0 p mode).congr fun fuel => ?_
      show genPochRealFuel fuel x y p mode = _
      unfold genPochRealFuel
      rw [ite_eq_left hi, ite_eq_right h0, ← hn]
  have hni : ¬ ∃ k : ℤ, yv = k := fun h => hi ((isInteger_iff_of_toVal hy).mpr h)
  have hspec : Spec.genPochhammerReal xv yv =
      if xv + yv ≤ 0 ∧ ∃ k : ℤ, xv + yv = k then none
      else some ((Real.Gamma (xv + yv) / Real.Gamma xv : ℝ) : EReal) := by
    unfold Spec.genPochhammerReal
    rw [ite_eq_right hni]
  rw [hspec]
  by_cases hxp : (isInteger x && le x zero) = true
  · refine Or.inl fun fuel => ?_
    show genPochRealFuel fuel x y p mode = _
    unfold genPochRealFuel
    rw [ite_eq_right hi, ite_eq_left hxp]
    rw [Bool.and_eq_true, isInteger_iff_of_toVal hx, le_eq_true_iff hx toVal_zero'] at hxp
    obtain ⟨⟨k, hk⟩, hle⟩ := hxp
    have hns : ¬ (xv + yv ≤ 0 ∧ ∃ k : ℤ, xv + yv = k) := by
      rintro ⟨-, j, hj⟩
      exact hni ⟨j - k, by push_cast; linarith⟩
    rw [ite_eq_right hns, gamma_eq_zero_of_nonpos_int hle hk, div_zero, EReal.coe_zero,
      roundVal_zero]
  by_cases hs : sumIsNonposInt x y = true
  · refine Or.inl fun fuel => ?_
    show genPochRealFuel fuel x y p mode = _
    unfold genPochRealFuel
    rw [ite_eq_right hi, ite_eq_right hxp, ite_eq_left hs,
      ite_eq_left ((sumIsNonposInt_iff hx hy).mp hs), roundVal_none]
  have hns : ¬ (xv + yv ≤ 0 ∧ ∃ k : ℤ, xv + yv = k) :=
    fun h => hs ((sumIsNonposInt_iff hx hy).mpr h)
  rw [ite_eq_right hns]
  have hxa : ¬ (xv ≤ 0 ∧ ∃ k : ℤ, xv = k) := by
    rintro ⟨hle, hk⟩
    refine hxp ?_
    rw [Bool.and_eq_true, isInteger_iff_of_toVal hx, le_eq_true_iff hx toVal_zero']
    exact ⟨hk, hle⟩
  refine (ZivCases.of_core (genPochCore_coreConv hx hy
      (beta_arg_cases (fun h => hxa ⟨h.le, 0, by rw [h]; simp⟩) (fun h => hxa ⟨h.1.le, h.2⟩))
      (beta_sum_cases hns))
    (fun w hw neg b hc => genPochCore_spec hx hy hw hc) p mode).congr fun fuel => ?_
  show genPochRealFuel fuel x y p mode = _
  unfold genPochRealFuel
  rw [ite_eq_right hi, ite_eq_right hxp, ite_eq_right hs, ite_eq_right (NeZero.ne p)]

/-- **The generalized Pochhammer symbol is exact or a convergent loop.** -/
theorem genPochhammerPrecRoundFuel_zivCases (x y : AzFloat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    ZivCases (fun fuel => genPochhammerPrecRoundFuel fuel x y p mode)
      (x.toVal.bind fun a => y.toVal.bind fun b => Spec.genPochhammer a b) p mode := by
  cases x with
  | nan => exact Or.inl fun fuel => by simp [genPochhammerPrecRoundFuel, toVal_nan]
  | infinity s =>
    exact Or.inl fun fuel => by
      cases y <;> cases s <;> simp [genPochhammerPrecRoundFuel, Spec.genPochhammer]
  | zero =>
    cases y with
    | nan => exact Or.inl fun fuel => by simp [genPochhammerPrecRoundFuel, toVal_nan]
    | infinity s =>
      exact Or.inl fun fuel => by
        cases s <;> simp [genPochhammerPrecRoundFuel, Spec.genPochhammer]
    | zero =>
      simp only [genPochhammerPrecRoundFuel, toVal_zero, Option.bind_some]
      rw [← EReal.coe_zero, Spec.genPochhammer_coe]
      exact genPochRealFuel_zivCases toVal_zero' toVal_zero' p mode
    | finite s e q m hv =>
      simp only [genPochhammerPrecRoundFuel, toVal_zero, toVal_finite, Option.bind_some]
      rw [← EReal.coe_zero, Spec.genPochhammer_coe]
      exact genPochRealFuel_zivCases toVal_zero' (toVal_finite s e q m hv) p mode
  | finite s e q m hv =>
    cases y with
    | nan => exact Or.inl fun fuel => by simp [genPochhammerPrecRoundFuel, toVal_nan]
    | infinity s' =>
      exact Or.inl fun fuel => by
        cases s' <;> simp [genPochhammerPrecRoundFuel, Spec.genPochhammer]
    | zero =>
      simp only [genPochhammerPrecRoundFuel, toVal_zero, toVal_finite, Option.bind_some]
      rw [← EReal.coe_zero, Spec.genPochhammer_coe]
      exact genPochRealFuel_zivCases (toVal_finite s e q m hv) toVal_zero' p mode
    | finite s' e' q' m' hv' =>
      simp only [genPochhammerPrecRoundFuel, toVal_finite, Option.bind_some]
      rw [Spec.genPochhammer_coe]
      exact genPochRealFuel_zivCases (toVal_finite s e q m hv) (toVal_finite s' e' q' m' hv')
        p mode

/-- **The specification of the generalized Pochhammer symbol** (`ZivSpec`): sound at every
fuel; complete in the limit of the fuel wherever the value is no rounding boundary; correct
at every fuel where the value is undefined (a pole, an argument that is not finite) or
`0`. -/
theorem genPochhammerPrecRoundFuel_zivSpec :
    ZivSpec (fun xy : AzFloat × AzFloat =>
        xy.1.toVal.bind fun a => xy.2.toVal.bind fun b => Spec.genPochhammer a b)
      (fun fuel xy p mode => genPochhammerPrecRoundFuel fuel xy.1 xy.2 p mode)
      {xy | ∀ v : ℝ, (xy.1.toVal.bind fun a => xy.2.toVal.bind fun b =>
        Spec.genPochhammer a b) = some (v : EReal) → v = 0} ∅ :=
  ZivSpec.of_zivCases fun xy p _ mode => genPochhammerPrecRoundFuel_zivCases xy.1 xy.2 p mode

/-- **The generalized Pochhammer symbol is correctly rounded, or the fuel ran out**, at
every fuel. -/
theorem genPochhammerPrecRoundFuel_eq_or (fuel : ℕ) (x y : AzFloat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    genPochhammerPrecRoundFuel fuel x y p mode = liftVal₂ Spec.genPochhammer x y p mode ∨
      genPochhammerPrecRoundFuel fuel x y p mode = (nan, .eq) :=
  (genPochhammerPrecRoundFuel_zivCases x y p mode).sound fuel

/-- **The generalized Pochhammer symbol is correctly rounded, or the fuel ran out.** -/
theorem genPochhammerPrecRound_eq_or (x y : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    genPochhammerPrecRound x y p mode = liftVal₂ Spec.genPochhammer x y p mode ∨
      genPochhammerPrecRound x y p mode = (nan, .eq) :=
  genPochhammerPrecRoundFuel_eq_or (gammaFuel p) x y p mode

end Azurite.AzFloat
