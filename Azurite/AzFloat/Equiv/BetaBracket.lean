/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.BetaBracket
import Azurite.AzFloat.Equiv.GammaBracket
import Azurite.BrentZimmermann.Chapter4.StirlingLogGamma

/-!
# Equivalence: the bracket of the Beta function

`betaCore_spec`: every answer `(neg, b)` of `betaCore a b w` (`w ≥ 64`) is the sign and a
positive enclosure of `|Γ(a) Γ(b) / Γ(a + b)|` — whatever `a` and `b` are: the pieces answer
only where they are valid.  The steps: `fracOfEncl_spec`, `gammaFloatFrac_spec`,
`betaSumFrac_spec` (the distances to an integer), `stirlingShifted_spec` (Stirling's series at
the shifted argument, on a shared table), `lnGammaPiece_spec` (`ln |Γ(v)| = t + ½ ln q`, with
the sign of `Γ(v)`), `lnAbsBetaCore_spec` (the enclosure of `ln |B(a, b)|` and the sign).
-/

namespace Azurite.AzFloat

open Finset
open scoped Real

/-- `fracOfEncl` answers with the sign and a positive enclosure of the absolute value. -/
theorem fracOfEncl_spec {D : Encl} {d : ℝ} (hD : IsEncl D d) {σ : Bool} {A : Encl}
    (h : fracOfEncl D = some (σ, A)) : IsEnclPos A ((if σ then -1 else 1) * d) := by
  unfold fracOfEncl at h
  split_ifs at h with h1 h2
  · rw [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simpa using hD.pos_of_lt h1
  · rw [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨l, u, hl, hu, hl1, hu1⟩ := hD
    have hu0 : u < 0 := (lt_eq_true_iff hu toVal_zero').mp h2
    refine ⟨-u, -l, ?_, ?_, by linarith, by simp only [↓reduceIte]; linarith,
      by simp only [↓reduceIte]; linarith⟩
    · show (-D.2).toVal = _
      rw [toVal_neg, hu]; rfl
    · show (-D.1).toVal = _
      rw [toVal_neg, hl]; rfl

/-- The fractional part of a float. -/
theorem gammaFloatFrac_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) {W : ℕ}
    [NeZero W] {σ : Bool} {k : AzInt} {A : Encl} (h : gammaFloatFrac x W = some (σ, k, A)) :
    IsEnclPos A ((if σ then -1 else 1) * (xv - k.toInt)) := by
  unfold gammaFloatFrac at h
  obtain ⟨t, ht, heq⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨σ', A'⟩ := t
  rw [Prod.mk.injEq, Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl, rfl⟩ := heq
  exact gammaFracEncl_spec hx _ ht

/-- The fractional part of a sum of two floats. -/
theorem betaSumFrac_spec {a b : AzFloat} {av bv : ℝ} (ha : a.toVal = some (av : EReal))
    (hb : b.toVal = some (bv : EReal)) {W : ℕ} [NeZero W] {σ : Bool} {k : AzInt} {A : Encl}
    (h : betaSumFrac a b W = some (σ, k, A)) :
    IsEnclPos A ((if σ then -1 else 1) * (av + bv - k.toInt)) := by
  unfold betaSumFrac at h
  obtain ⟨t, ht, heq⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨σ', A'⟩ := t
  rw [Prod.mk.injEq, Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl, rfl⟩ := heq
  have hA : IsEncl (Encl.exact a) av := ⟨av, av, ha, ha, le_rfl, le_rfl⟩
  have hB : IsEncl (Encl.exact b) bv := ⟨bv, bv, hb, hb, le_rfl, le_rfl⟩
  have hK : IsEncl (Encl.exact (ofAzInt (gammaNearInt (addPrecRound a b 64 .Nearest).1)))
      (((gammaNearInt (addPrecRound a b 64 .Nearest).1).toInt : ℤ) : ℝ) :=
    ⟨_, _, toVal_ofAzInt _, toVal_ofAzInt _, le_rfl, le_rfl⟩
  have hD := (hA.sub (w := W) hK).add (w := W) hB
  have := fracOfEncl_spec hD ht
  convert this using 2
  ring

/-- `stirlingEnclWith` on the table of `M` tangent numbers is `lnGammaStirlingEncl`. -/
theorem stirlingEnclWith_eq (V M : ℕ) (Y : Encl) (tol : AzFloat) :
    stirlingEnclWith V M (AzNat.tangentNumbers M) Y tol = lnGammaStirlingEncl V M Y tol := rfl

/-- **Stirling's series at the shifted argument**: for `x > 0` with shift `δ`, the first
component encloses `g − ½ ln (2π)` and the second `P`, where `ln Γ(x) = g − ln P`
(`g = ln Γ(x + δ)`, `P = x (x + 1) ⋯ (x + δ − 1)`). -/
theorem stirlingShifted_spec {X : Encl} {xv : ℝ} (hX : IsEnclPos X xv) (e : AzInt) (L : ℕ)
    {V : ℕ} (hV : 64 ≤ V) {M : ℕ} (hM : 1 ≤ M) (tol : AzFloat) :
    ∃ g P : ℝ, IsEncl (stirlingShifted X e L V M (AzNat.tangentNumbers M) tol).1
        (g - 1 / 2 * Real.log (2 * π)) ∧
      IsEnclPos (stirlingShifted X e L V M (AzNat.tangentNumbers M) tol).2 P ∧
      Real.log (Real.Gamma xv) = g - Real.log P := by
  have : NeZero V := ⟨by omega⟩
  have hV2 : 2 ≤ V := by omega
  obtain ⟨xl, xh, hxl, -, hxl0, hxl1, -⟩ := id hX
  have hpos : 0 < xv := by linarith
  unfold stirlingShifted
  dsimp only
  set δ := lnGammaShift X.1 e L with hδ
  have hY : IsEnclPos (Encl.add V X (Encl.nat δ)) (xv + (δ : ℕ)) := hX.add hV2 (isEncl0_nat _)
  have hy1 : 1 ≤ xv + (δ : ℕ) := by
    by_cases h0 : δ = 0
    · have := (one_le_of_lnGammaShift_eq_zero hxl h0).trans hxl1
      rw [h0, Nat.cast_zero, add_zero]
      exact this
    · have : (1 : ℝ) ≤ (δ : ℕ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
      linarith
  have hS := lnGammaStirlingEncl_spec hV hM hY hy1 tol
  have hP := risingEncl_spec hV2 hX δ
  have hPpos : 0 < ∏ j ∈ range δ, (xv + j) :=
    prod_pos fun i _ => by
      have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      linarith
  refine ⟨Real.log (Real.Gamma (xv + (δ : ℕ))), ∏ j ∈ range δ, (xv + j), ?_, hP, ?_⟩
  · rw [stirlingEnclWith_eq]; exact hS
  · rw [BZ.log_Gamma_eq_log_Gamma_add_sub hpos δ, Real.log_prod]
    intro i _
    have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    exact (by linarith : (0 : ℝ) < xv + i).ne'

/-- **A piece of `ln |Γ(v)|`**: the sign of `Γ(v)` and `ln |Γ(v)| = t + ½ ln q`. -/
theorem lnGammaPiece_spec {X : Encl} {v : ℝ} (hX : IsEncl X v) {e : AzInt}
    {F : Unit → Option (Bool × AzInt × Encl)}
    (hF : ∀ σ k A, F () = some (σ, k, A) →
      IsEnclPos A ((if σ then -1 else 1) * (v - k.toInt))) {Pi : Encl}
    (hPi : IsEnclPos Pi π) {L V : ℕ} (hV : 64 ≤ V) {M : ℕ} (hM : 1 ≤ M) {tol : AzFloat} {w : ℕ}
    (hw : 64 ≤ w) {neg : Bool} {t q : Encl}
    (h : lnGammaPiece X e F Pi L V M (AzNat.tangentNumbers M) tol w = some (neg, t, q)) :
    ∃ tv qv : ℝ, IsEncl t tv ∧ IsEnclPos q qv ∧
      0 < (if neg then -1 else 1) * Real.Gamma v ∧
      Real.log ((if neg then -1 else 1) * Real.Gamma v) = tv + 1 / 2 * Real.log qv := by
  have : NeZero V := ⟨by omega⟩
  have hV2 : 2 ≤ V := by omega
  have hπ : 0 < π := Real.pi_pos
  have h2π : IsEnclPos (Encl.mul V (Encl.nat 2) Pi) (2 * π) := by
    have := (enclosesPos_nat (n := 2) (by norm_num)).mul hV2 hPi
    simpa using this
  unfold lnGammaPiece at h
  dsimp only at h
  generalize (if e.sign then e else 0) + 1 = e' at h
  split_ifs at h with hp hn hp₁
  · -- `v > 0`
    rw [Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have hXp := hX.pos_of_lt hp
    have hv0 : 0 < v := by obtain ⟨l, u, -, -, h0, h1, -⟩ := hXp; linarith
    obtain ⟨g, P, hS, hP, hlog⟩ := stirlingShifted_spec hXp e L hV hM tol
    have hP0 : 0 < P := by obtain ⟨l, u, -, -, h0, h1, -⟩ := hP; linarith
    refine ⟨g - 1 / 2 * Real.log (2 * π), 2 * π / (P * P), hS, h2π.div hV2 (hP.mul hV2 hP), ?_,
      ?_⟩
    · simpa using Real.Gamma_pos_of_pos hv0
    · simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
      rw [hlog, Real.log_div (by positivity) (mul_pos hP0 hP0).ne', Real.log_mul hP0.ne' hP0.ne']
      ring
  · -- `v < 0`: the reflection formula
    have hv0 : v < 0 := by
      obtain ⟨l, u, -, hu, -, hu1⟩ := hX
      have := (lt_eq_true_iff hu toVal_zero').mp hn
      linarith
    have hX₁ : IsEnclPos (Encl.sub V (Encl.exact one) X) (1 - v) :=
      (enclosesPos_one.encloses0.encloses.sub hX).pos_of_lt hp₁
    split at h
    · rename_i neg' Sn hS
      rw [Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨tt, htt, hS'⟩ := Option.bind_eq_some_iff.mp hS
      obtain ⟨σ, k, A⟩ := tt
      have hSn := gammaSinOfFrac_spec (hF σ k A htt) (by omega : 64 ≤ w + 16) hw hS'
      obtain ⟨g, P, hSt, hP, hlog⟩ := stirlingShifted_spec hX₁ e' L hV hM tol
      have hP0 : 0 < P := by obtain ⟨l, u, -, -, h0, h1, -⟩ := hP; linarith
      obtain ⟨sv, hsv⟩ : ∃ sv : ℝ,
          sv = (if neg' = true then (-1 : ℝ) else 1) * Real.sin (π * v) := ⟨_, rfl⟩
      rw [← hsv] at hSn
      have hs0 : 0 < sv := by obtain ⟨l, u, -, -, h0, h1, -⟩ := hSn; linarith
      have hg0 : 0 < Real.Gamma (1 - v) := Real.Gamma_pos_of_pos (by linarith)
      have hrefl := Real.Gamma_mul_Gamma_one_sub v
      have hsin0 : Real.sin (π * v) ≠ 0 := by
        intro h0
        rw [hsv, h0, mul_zero] at hs0
        exact lt_irrefl _ hs0
      have hsg : (if neg' = true then (-1 : ℝ) else 1) * Real.Gamma v
          = π / (sv * Real.Gamma (1 - v)) := by
        have hGx : Real.Gamma v = π / (Real.sin (π * v) * Real.Gamma (1 - v)) := by
          rw [eq_div_iff (mul_ne_zero hsin0 hg0.ne'), mul_comm (Real.sin _), ← mul_assoc, hrefl]
          field_simp
        rw [hGx, hsv]
        cases neg'
        · simp
        · simp only [↓reduceIte]
          rw [neg_one_mul, neg_one_mul, neg_mul, div_neg]
      have hq : IsEnclPos (Encl.div V (Encl.mul V Pi (Encl.mul V
          (stirlingShifted (Encl.sub V (Encl.exact one) X) e' L V M (AzNat.tangentNumbers M)
            tol).2
          (stirlingShifted (Encl.sub V (Encl.exact one) X) e' L V M (AzNat.tangentNumbers M)
            tol).2))
          (Encl.mul V (Encl.nat 2) (Encl.mul V Sn Sn))) (π * (P * P) / (2 * (sv * sv))) := by
        have := (hPi.mul hV2 (hP.mul hV2 hP)).div hV2
          ((enclosesPos_nat (n := 2) (by norm_num)).mul hV2 (hSn.mul hV2 hSn))
        simpa using this
      refine ⟨-(g - 1 / 2 * Real.log (2 * π)), π * (P * P) / (2 * (sv * sv)), hSt.neg, hq, ?_,
        ?_⟩
      · rw [hsg]; positivity
      · have e1 : Real.log (π * (P * P) / (2 * (sv * sv)))
            = Real.log π + 2 * Real.log P - Real.log 2 - 2 * Real.log sv := by
          rw [Real.log_div (mul_pos hπ (mul_pos hP0 hP0)).ne'
            (mul_pos two_pos (mul_pos hs0 hs0)).ne', Real.log_mul hπ.ne' (mul_pos hP0 hP0).ne',
            Real.log_mul hP0.ne' hP0.ne', Real.log_mul two_ne_zero (mul_pos hs0 hs0).ne',
            Real.log_mul hs0.ne' hs0.ne']
          ring
        have e2 : Real.log (2 * π) = Real.log 2 + Real.log π := Real.log_mul two_ne_zero hπ.ne'
        rw [hsg, Real.log_div hπ.ne' (mul_pos hs0 hg0).ne', Real.log_mul hs0.ne' hg0.ne', hlog,
          e1, e2]
        ring
    · exact absurd h (by simp)

/-- **`lnAbsBetaCore` answers with the sign of `B(a, b)` and an enclosure of
`ln |B(a, b)|`.** -/
theorem lnAbsBetaCore_spec {a b : AzFloat} {av bv : ℝ} (ha : a.toVal = some (av : EReal))
    (hb : b.toVal = some (bv : EReal)) {w : ℕ} (hw : 64 ≤ w) {ws : ℕ} (hws : 64 ≤ ws)
    {neg : Bool} {r : Encl} (h : lnAbsBetaCore a b w ws = some (neg, r)) :
    0 < (if neg then -1 else 1) * (Real.Gamma av * Real.Gamma bv / Real.Gamma (av + bv)) ∧
      IsEncl r (Real.log ((if neg then -1 else 1)
        * (Real.Gamma av * Real.Gamma bv / Real.Gamma (av + bv)))) := by
  unfold lnAbsBetaCore at h
  dsimp only at h
  set L := lnGammaShiftExp w
  set V := w + 2 * L + 8 + 2 * w.log2 with hVdef
  have hV : 64 ≤ V := by omega
  have : NeZero V := ⟨by omega⟩
  have hV2 : 2 ≤ V := by omega
  have : NeZero (ws + 16) := ⟨by omega⟩
  have hA : IsEncl (Encl.exact a) av := ⟨av, av, ha, ha, le_rfl, le_rfl⟩
  have hB : IsEncl (Encl.exact b) bv := ⟨bv, bv, hb, hb, le_rfl, le_rfl⟩
  have hS := hA.add (w := V) hB
  have hPi := enclosesPos_pi hV
  have hM : ∀ x y z : ℕ, 1 ≤ max (max (lnGammaTerms w x) (lnGammaTerms w y))
      (lnGammaTerms w z) := fun x y z =>
    le_trans (le_trans (by norm_num) (Nat.le_add_left 3 _)) (le_max_right _ _)
  split at h
  · rename_i na ta qa nb tb qb ns ts qs h1 h2 h3
    rw [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨tav, qav, e1, e2, e3, e4⟩ := lnGammaPiece_spec hA
      (fun σ k A hF => gammaFloatFrac_spec ha hF) hPi hV (hM _ _ _) hws h1
    obtain ⟨tbv, qbv, f1, f2, f3, f4⟩ := lnGammaPiece_spec hB
      (fun σ k A hF => gammaFloatFrac_spec hb hF) hPi hV (hM _ _ _) hws h2
    obtain ⟨tsv, qsv, g1, g2, g3, g4⟩ := lnGammaPiece_spec hS
      (fun σ k A hF => betaSumFrac_spec ha hb hF) hPi hV (hM _ _ _) hws h3
    have hqa : 0 < qav := by obtain ⟨l, u, -, -, h0, h1', -⟩ := e2; linarith
    have hqb : 0 < qbv := by obtain ⟨l, u, -, -, h0, h1', -⟩ := f2; linarith
    have hqs : 0 < qsv := by obtain ⟨l, u, -, -, h0, h1', -⟩ := g2; linarith
    have hval : (if ((na != nb) != ns) = true then (-1 : ℝ) else 1)
        * (Real.Gamma av * Real.Gamma bv / Real.Gamma (av + bv))
        = ((if na = true then (-1 : ℝ) else 1) * Real.Gamma av)
          * ((if nb = true then (-1 : ℝ) else 1) * Real.Gamma bv)
          / ((if ns = true then (-1 : ℝ) else 1) * Real.Gamma (av + bv)) := by
      cases na <;> cases nb <;> cases ns <;> simp [neg_div, div_neg]
    rw [hval]
    refine ⟨div_pos (mul_pos e3 f3) g3, ?_⟩
    have hQ := lnOfEncl_pos ((e2.mul hV2 f2).div hV2 g2) hV
    have := ((e1.add (w := V) f1).sub (w := V) g1).add (w := V) hQ.half
    convert this using 1
    rw [Real.log_div (mul_pos e3 f3).ne' g3.ne', Real.log_mul e3.ne' f3.ne', e4, f4, g4,
      Real.log_div (mul_pos hqa hqb).ne' hqs.ne', Real.log_mul hqa.ne' hqb.ne']
    ring
  · exact absurd h (by simp)

/-- **`betaCore` answers with the sign and a positive enclosure of
`|Γ(a) Γ(b) / Γ(a + b)|`.** -/
theorem betaCore_spec {a b : AzFloat} {av bv : ℝ} (ha : a.toVal = some (av : EReal))
    (hb : b.toVal = some (bv : EReal)) {w : ℕ} (hw : 64 ≤ w) {neg : Bool} {r : Encl}
    (h : betaCore a b w = some (neg, r)) :
    IsEnclPos r ((if neg then -1 else 1)
      * (Real.Gamma av * Real.Gamma bv / Real.Gamma (av + bv))) := by
  unfold betaCore at h
  dsimp only at h
  obtain ⟨c, hc, hr⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨neg', Lg⟩ := c
  obtain ⟨g, hg, hgeq⟩ := Option.map_eq_some_iff.mp hr
  rw [Prod.mk.injEq] at hgeq
  obtain ⟨rfl, rfl⟩ := hgeq
  obtain ⟨hpos, hL⟩ := lnAbsBetaCore_spec ha hb (by omega) hw hc
  have := gammaExpEncl_spec hL hw hg
  simp only [Bool.false_eq_true, ↓reduceIte] at this
  rwa [Real.exp_log hpos] at this

end Azurite.AzFloat
