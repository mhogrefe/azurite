/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.QGammaBracket
import Azurite.AzFloat.Equiv.BarnesGBracket
import Azurite.Transcendental.QGamma

/-!
# Equivalence: the bracket of the `q`-gamma function

The bracket of `AzFloat/QGammaBracket.lean` encloses, at every level:

* `qGammaVal inv p x`, the value the bracket is after for a base `p ∈ (0, 1)`: `Γ_p(x)`, times
  `(1/p)^((x−1)(x−2)/2)` when `inv` (the base is `q = 1/p > 1`);
* `QGammaArg A p x`, what the bracket asks of its base and its argument;
* `qProdLoop_spec`: the loop encloses the powers, the numerator and the denominator with its
  sign;
* **`qGammaLnEnclOf_spec`**: the sign and an enclosure of `ln |Γ_q(x)|`;
  **`qGammaCoreOf_spec`**: a positive enclosure of `|Γ_q(x)|`.  Neither needs `x` to be off
  the poles: at a pole the bracket gives nothing.
-/

namespace Azurite.AzFloat

open Finset DLMF

/-- The value of the bracket for a base `p ∈ (0, 1)`: `Γ_p(x)`, or with `inv` the function at
the base `1/p`, `Γ_p(x) (1/p)^((x−1)(x−2)/2)`. -/
noncomputable def qGammaVal (inv : Bool) (p x : ℝ) : ℝ :=
  qGammaR p x * if inv then Real.exp ((x - 1) * (x - 2) / 2 * (-Real.log p)) else 1

/-- **What the bracket asks of its base `p` and its argument `x`**: `0 < p < 1`, enclosures of
`p` of relative width `6 · 2^(−V)`, and enclosures of `x` and `|x|` of width `O(2^(−V))`. -/
structure QGammaArg (A : QGammaIn) (pv xv : ℝ) : Prop where
  p_pos : 0 < pv
  p_lt : pv < 1
  P : ∀ V, 64 ≤ V → LEncl (A.P V) pv (6 * (1 / 2 : ℝ) ^ V)
  X : ∃ C : ℝ, ∀ V, 64 ≤ V → AEncl (A.X V) xv (C * (1 / 2 : ℝ) ^ V)
  absX : ∃ C : ℝ, ∀ V, 64 ≤ V → AEncl0 (A.absX V) |xv| (C * (1 / 2 : ℝ) ^ V)

theorem AEncl0.isEncl0 {a : Encl} {x ε : ℝ} (h : AEncl0 a x ε) : IsEncl0 a x := by
  obtain ⟨l, u, hl, hu, h0, h1, h2, -⟩ := h
  exact ⟨l, u, hl, hu, h0, h1, h2⟩

theorem sign_xor (a b : Bool) :
    (if (a != b) = true then (-1 : ℝ) else 1)
      = (if a = true then (-1 : ℝ) else 1) * (if b = true then (-1 : ℝ) else 1) := by
  cases a <;> cases b <;> simp

/-- **The loop encloses** the powers `p^(j+1)`, `p^(x+j)`, the numerator `∏ (1 − p^(i+1))`
and the denominator `∏ (1 − p^(x+i))` up to its sign. -/
theorem qProdLoop_spec {V : ℕ} [NeZero V] (hV2 : 2 ≤ V) {P : Encl} {pv xv : ℝ}
    (hp0 : 0 < pv) (hp1 : pv < 1) (hP : IsEnclPos P pv) :
    ∀ (k j : ℕ) (t r n d : Encl) (neg : Bool) (o : Bool × Encl × Encl × Encl × Encl),
      IsEnclPos t (pv ^ (j + 1)) → IsEnclPos r (pv ^ (xv + j)) →
      IsEnclPos n (∏ i ∈ range j, (1 - pv ^ (i + 1))) →
      IsEnclPos d ((if neg then (-1 : ℝ) else 1) * ∏ i ∈ range j, (1 - pv ^ (xv + i))) →
      qProdLoop V P k t r n d neg = some o →
      IsEnclPos o.2.1 (pv ^ (j + k + 1)) ∧ IsEnclPos o.2.2.1 (pv ^ (xv + (j + k : ℕ))) ∧
        IsEnclPos o.2.2.2.1 (∏ i ∈ range (j + k), (1 - pv ^ (i + 1))) ∧
        IsEnclPos o.2.2.2.2 ((if o.1 then (-1 : ℝ) else 1) *
          ∏ i ∈ range (j + k), (1 - pv ^ (xv + i)))
  | 0, j, t, r, n, d, neg, o, ht, hr, hn, hd, h => by
    rw [qProdLoop, Option.some.injEq] at h
    subst h
    exact ⟨ht, hr, hn, hd⟩
  | k + 1, j, t, r, n, d, neg, o, ht, hr, hn, hd, h => by
    have hI : IsEncl (Encl.exact one) 1 := enclosesPos_one.encloses0.encloses
    rw [qProdLoop] at h
    split at h
    next σ' f σ g hf hg =>
      have hf' := fracOfEncl_spec (hI.sub (w := V) ht.encloses0.encloses) hf
      have hg' := fracOfEncl_spec (hI.sub (w := V) hr.encloses0.encloses) hg
      have hσ' : σ' = false := by
        cases σ' with
        | false => rfl
        | true =>
          exfalso
          obtain ⟨l, u, -, -, h0, h1, -⟩ := hf'
          simp only [↓reduceIte] at h1
          have : pv ^ (j + 1) < 1 := pow_lt_one₀ hp0.le hp1 (by omega)
          linarith
      subst hσ'
      simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at hf'
      have e1 : pv ^ (j + 1) * pv = pv ^ (j + 1 + 1) := by ring
      have e2 : pv ^ (xv + j) * pv = pv ^ (xv + ((j + 1 : ℕ) : ℝ)) := by
        rw [Nat.cast_succ, ← add_assoc, Real.rpow_add_one hp0.ne']
      have e3 : (∏ i ∈ range j, (1 - pv ^ (i + 1))) * (1 - pv ^ (j + 1))
          = ∏ i ∈ range (j + 1), (1 - pv ^ (i + 1)) := by rw [prod_range_succ]
      have e4 : ((if neg then (-1 : ℝ) else 1) * ∏ i ∈ range j, (1 - pv ^ (xv + i))) *
          ((if σ then (-1 : ℝ) else 1) * (1 - pv ^ (xv + j)))
          = (if (neg != σ) then (-1 : ℝ) else 1) * ∏ i ∈ range (j + 1), (1 - pv ^ (xv + i)) := by
        rw [prod_range_succ, sign_xor]
        ring
      have := qProdLoop_spec hV2 hp0 hp1 hP k (j + 1) _ _ _ _ _ o
        (e1 ▸ ht.mul hV2 hP) (e2 ▸ hr.mul hV2 hP) (e3 ▸ hn.mul hV2 hf') (e4 ▸ hd.mul hV2 hg') h
      rwa [show j + 1 + k = j + (k + 1) by omega] at this
    next => exact absurd h (by simp)

/-- **The sign of `Γ_q(x)` and the enclosure of `ln |Γ_q(x)|`.** -/
theorem qGammaLnEnclOf_spec {A : QGammaIn} {pv xv : ℝ} (hA : QGammaArg A pv xv) {w : ℕ}
    {neg : Bool} {L : Encl} (h : qGammaLnEnclOf A w = some (neg, L)) :
    0 < (if neg then (-1 : ℝ) else 1) * qGammaVal A.inv pv xv ∧
      IsEncl L (Real.log ((if neg then (-1 : ℝ) else 1) * qGammaVal A.inv pv xv)) := by
  have hp0 := hA.p_pos
  have hp1 := hA.p_lt
  have h1p : 0 < 1 - pv := by linarith
  unfold qGammaLnEnclOf at h
  dsimp only at h
  obtain ⟨V, hVd⟩ : ∃ V : ℕ, V = w + A.eb + 2 * w.log2 + 64 := ⟨_, rfl⟩
  rw [← hVd] at h
  have hV64 : 64 ≤ V := by omega
  have hV2 : 2 ≤ V := by omega
  have : NeZero V := ⟨by omega⟩
  have hP : IsEnclPos (A.P V) pv := (hA.P V hV64).isEnclPos
  obtain ⟨C, hC⟩ := hA.X
  have hX : IsEncl (A.X V) xv := (hC V hV64).isEncl
  obtain ⟨C', hC'⟩ := hA.absX
  have haX : IsEncl0 (A.absX V) |xv| := (hC' V hV64).isEncl0
  have hI : IsEncl (Encl.exact one) 1 := enclosesPos_one.encloses0.encloses
  split at h
  swap
  · exact absurd h (by simp)
  next hQ =>
  have hQ1 : IsEnclPos (Encl.sub V (Encl.exact one) (A.P V)) (1 - pv) :=
    (hI.sub (w := V) hP.encloses0.encloses).pos_of_lt hQ
  have hlamc := ((lnOfEncl_pos hP hV64).neg).clamp0
    (by linarith [Real.log_nonpos hp0.le hp1.le] : (0 : ℝ) ≤ -Real.log pv)
  have hmuc := ((lnOfEncl_pos hQ1 hV64).neg).clamp0
    (by linarith [Real.log_nonpos h1p.le (by linarith : 1 - pv ≤ 1)] :
      (0 : ℝ) ≤ -Real.log (1 - pv))
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = qGammaTerms V w (Encl.neg (lnOfEncl (A.P V) V))
      (Encl.neg (lnOfEncl (Encl.sub V (Encl.exact one) (A.P V)) V)) A.shift := ⟨_, rfl⟩
  rw [← hK] at h
  obtain ⟨r0, hexp, h⟩ := Option.bind_eq_some_iff.mp h
  have hr0 := gammaExpEncl_spec (hX.neg.mulPos (W := V) hlamc) hV64 hexp
  simp only [Bool.false_eq_true, ↓reduceIte] at hr0
  have er0 : Real.exp (-xv * -Real.log pv) = pv ^ (xv + ((0 : ℕ) : ℝ)) := by
    rw [Real.rpow_def_of_pos hp0]
    congr 1
    push_cast
    ring
  rw [er0] at hr0
  obtain ⟨o, hloop, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨neg0, t, r, n, d⟩ := o
  dsimp only at h
  obtain ⟨ht, hr, hn, hd⟩ := qProdLoop_spec hV2 hp0 hp1 hP K 0 _ _ _ _ _ _
    (by simpa using hP) hr0 (by simpa using enclosesPos_one)
    (by simpa using enclosesPos_one) hloop
  simp only [zero_add] at ht hr hn hd
  split at h
  swap
  · exact absurd h (by simp)
  next hE =>
  rw [Bool.and_eq_true] at hE
  obtain ⟨hEn, hEd⟩ := hE
  -- the tails
  obtain ⟨Pn, hPn⟩ : ∃ Pn : ℝ, Pn = ∏ i ∈ range K, (1 - pv ^ (i + 1)) := ⟨_, rfl⟩
  obtain ⟨Pd, hPd⟩ : ∃ Pd : ℝ, Pd = ∏ i ∈ range K, (1 - pv ^ (xv + i)) := ⟨_, rfl⟩
  obtain ⟨An, hAn⟩ : ∃ An : ℝ, An = qPochR (pv ^ (K + 1)) pv := ⟨_, rfl⟩
  obtain ⟨Ad, hAd⟩ : ∃ Ad : ℝ, Ad = qPochR (pv ^ (xv + K)) pv := ⟨_, rfl⟩
  rw [← hPn] at hn
  rw [← hPd] at hd
  unfold qGammaTailLo at hEn hEd
  have hTn : IsEnclPos ((Encl.sub V (Encl.exact one) (Encl.div V t
      (Encl.sub V (Encl.exact one) (A.P V)))).1, one) An := by
    obtain ⟨l, u, hl, -, h1, -⟩ := hI.sub (w := V) (ht.div hV2 hQ1).encloses0.encloses
    have hl0 : 0 < l := (lt_eq_true_iff toVal_zero' hl).mp hEn
    have hb := qPochR_bounds hp0 hp1 (a := pv ^ (K + 1)) (by positivity)
      (pow_le_one₀ hp0.le hp1.le)
    rw [← hAn] at hb
    exact ⟨l, 1, hl, toVal_one', hl0, by linarith [hb.1], hb.2⟩
  have hTd : IsEnclPos ((Encl.sub V (Encl.exact one) (Encl.div V r
      (Encl.sub V (Encl.exact one) (A.P V)))).1, one) Ad := by
    obtain ⟨l, u, hl, -, h1, -⟩ := hI.sub (w := V) (hr.div hV2 hQ1).encloses0.encloses
    have hl0 : 0 < l := (lt_eq_true_iff toVal_zero' hl).mp hEd
    have ha0 : 0 ≤ pv ^ (xv + K) := Real.rpow_nonneg hp0.le _
    have ha1 : pv ^ (xv + K) ≤ 1 := by
      have h2 : pv ^ (xv + K) / (1 - pv) < 1 := by linarith
      rw [div_lt_one h1p] at h2
      linarith
    have hb := qPochR_bounds hp0 hp1 ha0 ha1
    rw [← hAd] at hb
    exact ⟨l, 1, hl, toVal_one', hl0, by linarith [hb.1], hb.2⟩
  have hR := (hn.mul hV2 hTn).div hV2 (hd.mul hV2 hTd)
  have hlnR := lnOfEncl_pos hR hV64
  have hL0 := ((hX.sub (w := V) hI).mulPos (W := V) hmuc).add (w := V) hlnR
  -- the value
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = if neg0 then (-1 : ℝ) else 1 := ⟨_, rfl⟩
  rw [← hs] at hd hR hlnR hL0
  have hss : s * s = 1 := by rw [hs]; cases neg0 <;> simp
  obtain ⟨Rv, hRv⟩ : ∃ Rv : ℝ, Rv = Pn * An / (s * Pd * Ad) := ⟨_, rfl⟩
  rw [← hRv] at hR hlnR hL0
  have hRv0 : 0 < Rv := by
    obtain ⟨l, -, -, -, h0, h1, -⟩ := hR
    linarith
  have hG := qGammaR_eq_trunc hp0 hp1 xv K
  rw [← hPn, ← hPd, ← hAn, ← hAd] at hG
  have hsG : s * qGammaR pv xv = (1 - pv) ^ (1 - xv) * Rv := by
    rw [hG, hRv]
    have hs' : s⁻¹ = s := by
      have hs0 : s ≠ 0 := fun h0 => by rw [h0] at hss; simp at hss
      field_simp
      linarith
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv, mul_inv, mul_inv, hs']
    ring
  have hpw : 0 < (1 - pv) ^ (1 - xv) := Real.rpow_pos_of_pos h1p _
  have hlogG : Real.log (s * qGammaR pv xv)
      = (xv - 1) * -Real.log (1 - pv) + Real.log Rv := by
    rw [hsG, Real.log_mul hpw.ne' hRv0.ne', Real.log_rpow h1p]
    ring
  rw [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, hL⟩ := h
  unfold qGammaFinL qGammaTailLo at hL
  dsimp only at hL
  unfold qGammaVal
  cases hinv : A.inv with
  | false =>
    rw [hinv] at hL
    simp only [Bool.false_eq_true, ↓reduceIte] at hL
    subst hL
    simp only [Bool.false_eq_true, ↓reduceIte, mul_one]
    rw [← hs, hlogG]
    exact ⟨by rw [hsG]; positivity, hL0⟩
  | true =>
    rw [hinv] at hL
    simp only [↓reduceIte] at hL
    subst hL
    simp only [↓reduceIte]
    rw [← hs]
    have hc2 := (((haX.mul (w := V) haX).encloses.sub (w := V)
      (hX.add (w := V) (hX.add (w := V) hX))).add (w := V)
      (enclosesPos_nat (n := 2) (by norm_num)).encloses0.encloses).half
    have hfin := hL0.add (w := V) (hc2.mulPos (W := V) hlamc)
    have hE0 : 0 < Real.exp ((xv - 1) * (xv - 2) / 2 * -Real.log pv) := Real.exp_pos _
    have hval : s * (qGammaR pv xv * Real.exp ((xv - 1) * (xv - 2) / 2 * -Real.log pv))
        = (1 - pv) ^ (1 - xv) * Rv * Real.exp ((xv - 1) * (xv - 2) / 2 * -Real.log pv) := by
      rw [← mul_assoc, hsG]
    refine ⟨by rw [hval]; positivity, ?_⟩
    rw [← mul_assoc, Real.log_mul (by rw [hsG]; positivity) hE0.ne', Real.log_exp, hlogG]
    refine (congrArg (IsEncl _) ?_).mpr hfin
    have : |xv| * |xv| = xv * xv := abs_mul_abs_self xv
    rw [this]
    push_cast
    ring

/-- **The enclosure of `|Γ_q(x)|` and the sign of `Γ_q(x)`.** -/
theorem qGammaCoreOf_spec {A : QGammaIn} {pv xv : ℝ} (hA : QGammaArg A pv xv) {w : ℕ}
    (hw : 64 ≤ w) {neg : Bool} {b : Encl} (h : qGammaCoreOf A w = some (neg, b)) :
    IsEnclPos b ((if neg then (-1 : ℝ) else 1) * qGammaVal A.inv pv xv) := by
  unfold qGammaCoreOf at h
  obtain ⟨c, hc, hr⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨neg', Lg⟩ := c
  obtain ⟨g, hg, hgeq⟩ := Option.map_eq_some_iff.mp hr
  rw [Prod.mk.injEq] at hgeq
  obtain ⟨rfl, rfl⟩ := hgeq
  obtain ⟨hpos, hL⟩ := qGammaLnEnclOf_spec hA hc
  have := gammaExpEncl_spec hL hw hg
  simp only [Bool.false_eq_true, ↓reduceIte] at this
  rwa [Real.exp_log hpos] at this

end Azurite.AzFloat
