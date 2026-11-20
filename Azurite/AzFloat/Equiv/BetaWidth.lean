/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.BetaBracket
import Azurite.AzFloat.Equiv.LnGammaEventually
import Azurite.AzFloat.Equiv.GammaWidth
import Azurite.AzFloat.Equiv.PowBaseBracket

/-!
# The bracket of the Beta function converges

The width of `lnAbsBetaEncl` — the enclosure of `ln |Γ(a) Γ(b) / Γ(s)|` from three pieces with
a shared table, a shared `π` and one logarithm — tends to `0` with the Ziv level, for
arguments given by convergent enclosures (`ArgConv`).

* `stirlingShifted_width`: Stirling's series and the rising product of one positive argument,
  on a number `M` of terms that need not be the one of `ln Γ` (the three pieces share the
  largest of theirs).
* `lnGammaPiece_pos_width`, `lnGammaPiece_neg_width`: a piece `(t, q)` with an absolute width
  for `t` and a relative width for `q`.
* `betaCombine_width`: the two additions and the logarithm of `q_a q_b / q_s`.
* `lnAbsBetaEncl_conv`, `betaEnclOf_coreConv`: the convergence.
-/

namespace Azurite.AzFloat

open Finset Filter Topology

/-! ### Stirling's series at a shifted argument, on `M` terms -/

/-- The width of a piece at level `w` on `M` terms: `lgEps` with the number of terms as a
parameter and without the last addition. -/
noncomputable def pcEps (xv : ℝ) (M w : ℕ) : ℝ :=
  lgPoly (2 ^ 42 * (6 * (w : ℝ) + 2 * (xv + 4 * w) + 10) ^ 5)
      (2 ^ 42 * (6 * (w : ℝ) + 2 * (3 + 2 * w * (|Real.log xv| + (xv + w))) + 10) ^ 5)
      w M (xv + 4 * w) 0 * (1 / 2 : ℝ) ^ w
    + max ((1 / 2 : ℝ) ^ (w + 16)) (2 * (9 / 10 : ℝ) ^ (2 * M - 1))

theorem tendsto_pcEps (xv : ℝ) {m : ℕ → ℕ} (hm : ∀ w, m w ≤ w / 2 + 4)
    (hmt : Tendsto (fun w => 2 * m w - 1) atTop atTop) :
    Tendsto (fun w => pcEps xv (m w) w) atTop (𝓝 0) := by
  have hw : PB fun w : ℕ => (w : ℝ) := PB.natCast
  have hM : PB fun w : ℕ => ((m w : ℕ) : ℝ) := by
    refine (hw.add (PB.const 4)).of_abs_le fun w => ?_
    have h1 := hm w
    have h2 : ((m w : ℕ) : ℝ) ≤ (w : ℝ) + 4 := by
      have : m w ≤ w + 4 := by omega
      exact_mod_cast this
    have h3 : (0 : ℝ) ≤ (w : ℝ) := Nat.cast_nonneg w
    rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (by linarith)]
    exact h2
  have hB : PB fun w : ℕ => xv + 4 * (w : ℝ) := (PB.const xv).add (hw.const_mul 4)
  have hpB : PB fun w : ℕ => (2 : ℝ) ^ 42 * (6 * (w : ℝ) + 2 * (xv + 4 * w) + 10) ^ 5 :=
    ((((hw.const_mul 6).add (hB.const_mul 2)).add (PB.const 10)).pow 5).const_mul _
  have hGQ : PB fun w : ℕ => 3 + 2 * (w : ℝ) * (|Real.log xv| + (xv + w)) :=
    (PB.const 3).add ((hw.const_mul 2).mul ((PB.const _).add ((PB.const xv).add hw)))
  have hpQ : PB fun w : ℕ => (2 : ℝ) ^ 42
      * (6 * (w : ℝ) + 2 * (3 + 2 * w * (|Real.log xv| + (xv + w))) + 10) ^ 5 :=
    ((((hw.const_mul 6).add (hGQ.const_mul 2)).add (PB.const 10)).pow 5).const_mul _
  have hpoly : PB fun w : ℕ => lgPoly (2 ^ 42 * (6 * (w : ℝ) + 2 * (xv + 4 * w) + 10) ^ 5)
      (2 ^ 42 * (6 * (w : ℝ) + 2 * (3 + 2 * w * (|Real.log xv| + (xv + w))) + 10) ^ 5)
      w (m w) (xv + 4 * w) 0 := by
    unfold lgPoly
    exact ((((((((hB.pow 2).const_mul 42).add (hB.mul (hpB.add (PB.const 70)))).add
      (hM.mul ((hM.const_mul 104).add (hB.const_mul 4)))).add (hB.const_mul 2)).add
      ((hB.pow 2).const_mul 42)).add
      ((hpQ.add ((((hw.const_mul 40).add (PB.const 21)).const_mul 5))).div_const 2)).add
      ((PB.const _).const_mul 4))
  have h1 := hpoly.tendsto
  have h2 : Tendsto (fun w : ℕ => (1 / 2 : ℝ) ^ (w + 16)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
      (tendsto_add_atTop_nat 16)
  have h3 : Tendsto (fun w : ℕ => 2 * (9 / 10 : ℝ) ^ (2 * m w - 1)) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 9 / 10)
      (by norm_num)).comp hmt).const_mul 2
    simpa using this
  have h4 := h1.add (h2.max h3)
  rw [max_self, add_zero] at h4
  exact h4

/-- **Stirling's series and the rising product of a positive argument** at level `w` on `M`
terms: `g = ln Γ(x + δ)` and `P = x (x + 1) ⋯ (x + δ − 1)`, with their sizes. -/
theorem stirlingShifted_width {xv : ℝ} (hxv : 0 < xv) (e : AzInt) {w : ℕ}
    (hw : 64 ≤ w) (hwa : 64 * (2 ^ e.abs.toNat + 1) ≤ w) {M : ℕ} (hM4 : 4 ≤ M)
    (hMle : M ≤ w / 2 + 4) (hsmall : pcEps xv M w ≤ 3 / 8)
    {X : Encl} {lam₀ : ℝ} (hX : LEncl X xv lam₀) (h0 : 0 ≤ lam₀)
    (hlam : lam₀ ≤ 8 * (1 / 2 : ℝ) ^ w) :
    ∃ g P : ℝ,
      AEncl (stirlingShifted X e (lnGammaShiftExp w)
        (w + 2 * lnGammaShiftExp w + 8 + 2 * w.log2) M (AzNat.tangentNumbers M)
        (powerOf2 (-(AzNat.ofNat (w + 16)).toAzInt))).1
        (g - 1 / 2 * Real.log (2 * Real.pi)) (pcEps xv M w) ∧
      LEncl (stirlingShifted X e (lnGammaShiftExp w)
        (w + 2 * lnGammaShiftExp w + 8 + 2 * w.log2) M (AzNat.tangentNumbers M)
        (powerOf2 (-(AzNat.ofNat (w + 16)).toAzInt))).2 P (20 * w * (1 / 2 : ℝ) ^ w) ∧
      |g| ≤ |Real.log (Real.Gamma xv)| + w * (|Real.log xv| + (xv + w)) ∧
      |Real.log P| ≤ w * (|Real.log xv| + (xv + w)) := by
  set a := e.abs.toNat with ha
  set L := lnGammaShiftExp w with hL
  set V := w + 2 * L + 8 + 2 * w.log2 with hV
  unfold stirlingShifted
  dsimp only
  set δ := lnGammaShift X.1 e L with hδ
  have hLs := two_pow_shiftExp (by omega : 4 ≤ w)
  have hLlog := shiftExp_le_log2 (by omega : 4 ≤ w)
  rw [← hL] at hLs hLlog
  obtain ⟨hL1, hL2⟩ := hLs
  have hlogw := log2_le_self w
  have hV1 : w ≤ V := by omega
  have hV2 : V ≤ 6 * w := by omega
  have hV64 : 64 ≤ V := by omega
  have : NeZero V := ⟨by omega⟩
  have haL : a ≤ L := by
    have h1 : 2 ^ a < 2 ^ L := by omega
    exact ((Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h1).le
  have hδle : δ ≤ 2 ^ L := lnGammaShift_le _ _ _
  have hδge : 2 ^ L - 2 ^ a ≤ δ := lnGammaShift_ge _ _ haL
  have hsub : 2 ^ L - 2 ^ a + 2 ^ a = 2 ^ L :=
    Nat.sub_add_cancel (Nat.pow_le_pow_right (by norm_num) haL)
  have hδpos : 0 < δ := by omega
  -- real versions
  have hwR : (64 : ℝ) ≤ w := by exact_mod_cast hw
  have hδw : (δ : ℝ) ≤ w := by exact_mod_cast (by omega : δ ≤ w)
  have hδ0 : (0 : ℝ) ≤ δ := Nat.cast_nonneg δ
  have hδ1 : (1 : ℝ) ≤ δ := by exact_mod_cast hδpos
  have hMR : (M : ℝ) ≤ w / 2 + 4 := by
    have : 2 * M ≤ w + 8 := by omega
    have : (2 : ℝ) * M ≤ w + 8 := by exact_mod_cast this
    linarith
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (by omega : 1 ≤ M)
  have hδlow : (w : ℝ) / 4 - w / 64 ≤ δ := by
    have h1 : w + 4 * 2 ^ a ≤ 4 * δ + 4 * 2 ^ a + 4 * 2 ^ a := by omega
    have h2 : 64 * 2 ^ a ≤ w := by omega
    have h1' : (w : ℝ) + 4 * 2 ^ a ≤ 4 * δ + 4 * 2 ^ a + 4 * 2 ^ a := by exact_mod_cast h1
    have h2' : (64 : ℝ) * 2 ^ a ≤ w := by exact_mod_cast h2
    linarith
  set U := (1 / 2 : ℝ) ^ w with hU
  have hU0 : 0 < U := by positivity
  have hu0 : (0 : ℝ) < (1 / 2 : ℝ) ^ V := by positivity
  have hu : (1 / 2 : ℝ) ^ V ≤ U := pow_le_pow_of_le_one (by norm_num) (by norm_num) hV1
  have hu8 : (1 / 2 : ℝ) ^ V ≤ 1 / 8 := half_pow_le_eighth (by omega)
  set B := xv + 4 * (w : ℝ) with hB
  have hB3 : 3 ≤ B := by linarith
  have hB0 : 0 ≤ B := by linarith
  set GQ := 3 + 2 * (w : ℝ) * (|Real.log xv| + (xv + w)) with hGQ
  have hGQ0 : 0 ≤ GQ := by positivity
  have hmx : (0 : ℝ) ≤ max ((1 / 2 : ℝ) ^ (w + 16)) (2 * (9 / 10 : ℝ) ^ (2 * M - 1)) :=
    le_trans (by positivity) (le_max_left _ _)
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := lgBound_facts (l := lam₀) (u := (1 / 2 : ℝ) ^ V)
    (U := U) (a := lnW B V) (q := lnW GQ V) (δ := δ) (wr := w) (M := M) (B := B) (Bf := 0)
    h0 hlam hu0.le hu hB3 le_rfl (lnW_nonneg hB0 V) (lnW_le hB0 hV1 hV2)
    (lnW_nonneg hGQ0 V) (lnW_le hGQ0 hV1 hV2) hM1 hδ0 hδw hmx hsmall
  have hY : LEncl (Encl.add V X (Encl.nat δ)) (xv + δ) (lam₀ + 6 * (1 / 2 : ℝ) ^ V) :=
    hX.add_exact (w := V) (b := Encl.nat δ) hu8 h0 (toVal_ofAzNat_ofNat δ)
      (toVal_ofAzNat_ofNat δ) hδ0
  have hS := lnGammaStirlingEncl_width' hV64 (by omega : 1 ≤ M) hY (by positivity)
    (by linarith) (by linarith) (toVal_lnGammaTol w) (B := B) (by linarith) (by linarith)
    f1 f2 f3 f4 f5
  have hP := risingEncl_width (V := V) hu8 hX h0 δ
  have hPpos : 0 < ∏ j ∈ range δ, (xv + j) :=
    prod_pos fun i _ => by
      have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      linarith
  have hlogP : |Real.log (∏ j ∈ range δ, (xv + j))| ≤ w * (|Real.log xv| + (xv + w)) := by
    rw [Real.log_prod (fun i _ => by
      have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      exact (by linarith : (0 : ℝ) < xv + i).ne')]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i ∈ range δ, |Real.log (xv + i)| ≤ ∑ _i ∈ range δ, (|Real.log xv| + (xv + δ)) :=
          sum_le_sum fun i hi => abs_log_add_nat_le hxv (mem_range.mp hi)
      _ = δ * (|Real.log xv| + (xv + δ)) := by rw [sum_const, card_range, nsmul_eq_mul]
      _ ≤ w * (|Real.log xv| + (xv + w)) :=
          mul_le_mul hδw (by linarith) (by positivity) (by positivity)
  have hid : Real.log (Real.Gamma xv)
      = Real.log (Real.Gamma (xv + δ)) - Real.log (∏ j ∈ range δ, (xv + j)) := by
    rw [BZ.log_Gamma_eq_log_Gamma_add_sub hxv δ, Real.log_prod]
    intro i _
    have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    exact (by linarith : (0 : ℝ) < xv + i).ne'
  refine ⟨Real.log (Real.Gamma (xv + δ)), ∏ j ∈ range δ, (xv + j), ?_, ?_, ?_, hlogP⟩
  · rw [stirlingEnclWith_eq]
    refine hS.mono (le_trans ?_ f7)
    have hq := lnW_nonneg hGQ0 V
    have hq2 : 0 ≤ 5 * (2 * (δ : ℝ) * (lam₀ + 12 * (1 / 2 : ℝ) ^ V) + 21 * (1 / 2 : ℝ) ^ V) := by
      positivity
    unfold lgBound
    linarith
  · refine hP.mono ?_
    have h1 : lam₀ + 12 * (1 / 2 : ℝ) ^ V ≤ 20 * U := by linarith
    calc (δ : ℝ) * (lam₀ + 12 * (1 / 2 : ℝ) ^ V) ≤ w * (20 * U) :=
          mul_le_mul hδw h1 (by positivity) (by positivity)
      _ = 20 * w * U := by ring
  · have h1 := abs_le.mp hlogP
    have h2 := abs_le.mp (le_refl |Real.log (Real.Gamma xv)|)
    rw [abs_le]
    constructor <;> linarith

/-! ### The pieces -/

/-- The size of the two values of a piece (`c`: the contribution of the sine). -/
noncomputable def pcG (xv c : ℝ) (w : ℕ) : ℝ :=
  |Real.log (Real.Gamma xv)| + c + 6 + 2 * (w * (|Real.log xv| + (xv + w)))

/-- **The piece of a positive argument.** -/
theorem lnGammaPiece_pos_width {xv : ℝ} (hxv : 0 < xv) (e : AzInt) {w : ℕ}
    (hw : 64 ≤ w) (hwa : 64 * (2 ^ e.abs.toNat + 1) ≤ w) {M : ℕ} (hM4 : 4 ≤ M)
    (hMle : M ≤ w / 2 + 4) (hsmall : pcEps xv M w ≤ 3 / 8)
    {X : Encl} {lam₀ : ℝ} (hX : LEncl X xv lam₀) (h0 : 0 ≤ lam₀)
    (hlam : lam₀ ≤ 8 * (1 / 2 : ℝ) ^ w) (F : Unit → Option (Bool × AzInt × Encl)) (ws : ℕ) :
    ∃ (t q : Encl) (tv qv : ℝ),
      lnGammaPiece X e F (Encl.pi (w + 2 * lnGammaShiftExp w + 8 + 2 * w.log2))
        (lnGammaShiftExp w) (w + 2 * lnGammaShiftExp w + 8 + 2 * w.log2) M
        (AzNat.tangentNumbers M) (powerOf2 (-(AzNat.ofNat (w + 16)).toAzInt)) ws
        = some (false, t, q) ∧
      AEncl t tv (pcEps xv M w) ∧ LEncl q qv (41 * w * (1 / 2 : ℝ) ^ w + 2 * 0) ∧
      |tv| ≤ pcG xv 0 w ∧ |Real.log qv| ≤ pcG xv 0 w := by
  obtain ⟨g, P, hS, hP, hg, hlP⟩ :=
    stirlingShifted_width hxv e hw hwa hM4 hMle hsmall hX h0 hlam
  set L := lnGammaShiftExp w with hL
  set V := w + 2 * L + 8 + 2 * w.log2 with hV
  have hV64 : 64 ≤ V := by omega
  have : NeZero V := ⟨by omega⟩
  have hu8 : (1 / 2 : ℝ) ^ V ≤ 1 / 8 := half_pow_le_eighth (by omega)
  have hu0 : (0 : ℝ) < (1 / 2 : ℝ) ^ V := by positivity
  have hu : (1 / 2 : ℝ) ^ V ≤ (1 / 2 : ℝ) ^ w :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hU0 : (0 : ℝ) < (1 / 2 : ℝ) ^ w := by positivity
  have hwR : (64 : ℝ) ≤ w := by exact_mod_cast hw
  obtain ⟨l, h, hl, -, hl0, -⟩ := id hX
  have c1 : lt zero X.1 = true := (lt_eq_true_iff toVal_zero' hl).mpr hl0
  have hP0 := hP.pos
  have h2π : LEncl (Encl.mul V (Encl.nat 2) (Encl.pi V)) (2 * Real.pi)
      (9 * (1 / 2 : ℝ) ^ V) := by
    have := ((LEncl.nat (n := 2) (by norm_num)).mul (w := V) hu8 (LEncl.pi hV64)).mono
      (le_of_eq (by ring : (0 : ℝ) + 3 * (1 / 2 : ℝ) ^ V + 6 * (1 / 2 : ℝ) ^ V
        = 9 * (1 / 2 : ℝ) ^ V))
    simpa using this
  have hQ := h2π.div hu8 (hP.mul hu8 hP)
  have hwU : 21 * (1 / 2 : ℝ) ^ w ≤ w * (1 / 2 : ℝ) ^ w :=
    mul_le_mul_of_nonneg_right (by linarith) hU0.le
  have hW0 : 0 ≤ (w : ℝ) * (|Real.log xv| + (xv + w)) := by positivity
  have h2πa := abs_le.mp abs_log_two_pi_le
  have hgA := abs_le.mp hg
  have hPA := abs_le.mp hlP
  have hΓA := abs_nonneg (Real.log (Real.Gamma xv))
  unfold lnGammaPiece
  simp only [c1, ↓reduceIte]
  refine ⟨_, _, g - 1 / 2 * Real.log (2 * Real.pi), 2 * Real.pi / (P * P), rfl, hS,
    hQ.mono (by linarith), ?_, ?_⟩
  · unfold pcG
    rw [abs_le]
    constructor <;> linarith
  · unfold pcG
    rw [Real.log_div (by positivity) (mul_pos hP0 hP0).ne', Real.log_mul hP0.ne' hP0.ne',
      abs_le]
    constructor <;> linarith

theorem abs_log_pi_le : |Real.log Real.pi| ≤ 3 := by
  have hπ := Real.pi_gt_three
  have h1 : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith)
  have h2 := Real.log_le_sub_one_of_pos Real.pi_pos
  rw [abs_of_nonneg h1]
  linarith [Real.pi_le_four]

theorem abs_log_two_le : |Real.log 2| ≤ 1 := by
  have h1 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  rw [abs_of_nonneg h1]
  linarith

/-- **The piece of a negative argument**, by the reflection formula: `X₁ = 1 − X` encloses
`1 − v` and `Sn` encloses `s = |sin (π v)|`. -/
theorem lnGammaPiece_neg_width {x₁ : ℝ} (hx₁ : 0 < x₁) (e : AzInt) {w : ℕ} (hw : 64 ≤ w)
    (hwa : 64 * (2 ^ ((if e.sign then e else 0) + 1).abs.toNat + 1) ≤ w) {M : ℕ}
    (hM4 : 4 ≤ M) (hMle : M ≤ w / 2 + 4) (hsmall : pcEps x₁ M w ≤ 3 / 8)
    {X : Encl} (hX1 : lt zero X.1 = false) (hX2 : lt X.2 zero = true) {lam₀ : ℝ}
    (hX₁ : LEncl (Encl.sub (w + 2 * lnGammaShiftExp w + 8 + 2 * w.log2) (Encl.exact one) X)
      x₁ lam₀) (h0 : 0 ≤ lam₀) (hlam : lam₀ ≤ 8 * (1 / 2 : ℝ) ^ w)
    {F : Unit → Option (Bool × AzInt × Encl)} {ws : ℕ} {neg : Bool} {Sn : Encl}
    {s lamS : ℝ}
    (hF : ((F ()).bind fun t => gammaSinOfFrac t.1 t.2.1 t.2.2 (ws + 16) ws) = some (neg, Sn))
    (hSn : LEncl Sn s lamS) :
    ∃ (t q : Encl) (tv qv : ℝ),
      lnGammaPiece X e F (Encl.pi (w + 2 * lnGammaShiftExp w + 8 + 2 * w.log2))
        (lnGammaShiftExp w) (w + 2 * lnGammaShiftExp w + 8 + 2 * w.log2) M
        (AzNat.tangentNumbers M) (powerOf2 (-(AzNat.ofNat (w + 16)).toAzInt)) ws
        = some (neg, t, q) ∧
      AEncl t tv (pcEps x₁ M w) ∧ LEncl q qv (41 * w * (1 / 2 : ℝ) ^ w + 2 * lamS) ∧
      |tv| ≤ pcG x₁ (2 * |Real.log s|) w ∧ |Real.log qv| ≤ pcG x₁ (2 * |Real.log s|) w := by
  obtain ⟨g, P, hS, hP, hg, hlP⟩ :=
    stirlingShifted_width hx₁ ((if e.sign then e else 0) + 1) hw hwa hM4 hMle hsmall hX₁ h0 hlam
  set L := lnGammaShiftExp w with hL
  set V := w + 2 * L + 8 + 2 * w.log2 with hV
  have hV64 : 64 ≤ V := by omega
  have : NeZero V := ⟨by omega⟩
  have hu8 : (1 / 2 : ℝ) ^ V ≤ 1 / 8 := half_pow_le_eighth (by omega)
  have hu0 : (0 : ℝ) < (1 / 2 : ℝ) ^ V := by positivity
  have hu : (1 / 2 : ℝ) ^ V ≤ (1 / 2 : ℝ) ^ w :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hU0 : (0 : ℝ) < (1 / 2 : ℝ) ^ w := by positivity
  have hwR : (64 : ℝ) ≤ w := by exact_mod_cast hw
  obtain ⟨l, h, hl, -, hl0, -⟩ := id hX₁
  have c1 : lt zero (Encl.sub V (Encl.exact one) X).1 = true :=
    (lt_eq_true_iff toVal_zero' hl).mpr hl0
  have hP0 := hP.pos
  have hs0 := hSn.pos
  have hnum := (LEncl.pi hV64).mul hu8 (hP.mul hu8 hP)
  have hden : LEncl (Encl.mul V (Encl.nat 2) (Encl.mul V Sn Sn)) (2 * (s * s))
      (lamS + lamS + 6 * (1 / 2 : ℝ) ^ V + 6 * (1 / 2 : ℝ) ^ V) := by
    have := (LEncl.nat (n := 2) (by norm_num)).mul (w := V) hu8 (hSn.mul hu8 hSn)
    simpa using this
  have hQ := hnum.div hu8 hden
  have hwU : 33 * (1 / 2 : ℝ) ^ w ≤ w * (1 / 2 : ℝ) ^ w :=
    mul_le_mul_of_nonneg_right (by linarith) hU0.le
  have hW0 : 0 ≤ (w : ℝ) * (|Real.log x₁| + (x₁ + w)) := by positivity
  have h2πa := abs_le.mp abs_log_two_pi_le
  have hπa := abs_le.mp abs_log_pi_le
  have h2a := abs_le.mp abs_log_two_le
  have hgA := abs_le.mp hg
  have hPA := abs_le.mp hlP
  have hΓA := abs_nonneg (Real.log (Real.Gamma x₁))
  have hsA := abs_le.mp (le_refl |Real.log s|)
  have hsA0 := abs_nonneg (Real.log s)
  unfold lnGammaPiece
  simp only [c1, hX1, hX2, Bool.false_eq_true, ↓reduceIte, hF]
  refine ⟨_, _, -(g - 1 / 2 * Real.log (2 * Real.pi)),
    Real.pi * (P * P) / (2 * (s * s)), rfl, hS.neg, hQ.mono (by linarith), ?_, ?_⟩
  · unfold pcG
    rw [abs_le]
    constructor <;> linarith
  · unfold pcG
    rw [Real.log_div (mul_pos Real.pi_pos (mul_pos hP0 hP0)).ne'
        (mul_pos two_pos (mul_pos hs0 hs0)).ne',
      Real.log_mul Real.pi_pos.ne' (mul_pos hP0 hP0).ne', Real.log_mul hP0.ne' hP0.ne',
      Real.log_mul two_ne_zero (mul_pos hs0 hs0).ne', Real.log_mul hs0.ne' hs0.ne', abs_le]
    constructor <;> linarith

/-! ### The three pieces together -/

/-- **The two additions and the logarithm of `q_a q_b / q_s`.** -/
theorem betaCombine_width {V : ℕ} (hV : 64 ≤ V) {ta tb ts qa qb qs : Encl}
    {tav tbv tsv qav qbv qsv εa εb εs la lb ls Ga Gb Gs : ℝ}
    (hta : AEncl ta tav εa) (htb : AEncl tb tbv εb) (hts : AEncl ts tsv εs)
    (hqa : LEncl qa qav la) (hqb : LEncl qb qbv lb) (hqs : LEncl qs qsv ls)
    (hla : 0 ≤ la) (hlb : 0 ≤ lb) (hls : 0 ≤ ls)
    (hlam : la + lb + ls + 12 * (1 / 2 : ℝ) ^ V ≤ 1 / 2)
    (hεa : εa ≤ 1) (hεb : εb ≤ 1) (hεs : εs ≤ 1)
    (hGa : |tav| ≤ Ga) (hGb : |tbv| ≤ Gb) (hGs : |tsv| ≤ Gs)
    (hGa' : |Real.log qav| ≤ Ga) (hGb' : |Real.log qbv| ≤ Gb) (hGs' : |Real.log qsv| ≤ Gs)
    (hlnW : lnW (Ga + Gb + Gs) V ≤ 1) :
    AEncl (Encl.add V (Encl.sub V (Encl.add V ta tb) ts)
        (Encl.half (lnOfEncl (Encl.div V (Encl.mul V qa qb) qs) V)))
      (tav + tbv - tsv + Real.log (qav * qbv / qsv) / 2)
      (εa + εb + εs + (lnW (Ga + Gb + Gs) V + 5 * (la + lb + ls + 12 * (1 / 2 : ℝ) ^ V)) / 2
        + 12 * (2 * (Ga + Gb + Gs) + 6) * (1 / 2 : ℝ) ^ V) := by
  have : NeZero V := ⟨by omega⟩
  have hu8 : (1 / 2 : ℝ) ^ V ≤ 1 / 8 := half_pow_le_eighth (by omega)
  have hu64 : (1 / 2 : ℝ) ^ V ≤ 1 / 64 := by
    calc (1 / 2 : ℝ) ^ V ≤ (1 / 2 : ℝ) ^ 6 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 64 := by norm_num
  have hu0 : (0 : ℝ) < (1 / 2 : ℝ) ^ V := by positivity
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = Ga + Gb + Gs := ⟨_, rfl⟩
  rw [← hG] at hlnW ⊢
  have a1 := abs_le.mp hGa
  have a2 := abs_le.mp hGb
  have a3 := abs_le.mp hGs
  have b1 := abs_le.mp hGa'
  have b2 := abs_le.mp hGb'
  have b3 := abs_le.mp hGs'
  have hG0 : 0 ≤ G := by linarith
  have hεa0 : 0 ≤ εa := by obtain ⟨l, u, -, -, c1, c2, c3⟩ := hta; linarith
  have hεb0 : 0 ≤ εb := by obtain ⟨l, u, -, -, c1, c2, c3⟩ := htb; linarith
  have hεs0 : 0 ≤ εs := by obtain ⟨l, u, -, -, c1, c2, c3⟩ := hts; linarith
  have hGu : (2 * G + 6) * (1 / 2 : ℝ) ^ V ≤ (2 * G + 6) / 64 := by
    have := mul_le_mul_of_nonneg_left hu64 (by linarith : (0 : ℝ) ≤ 2 * G + 6)
    linarith
  have hGu0 : 0 ≤ (2 * G + 6) * (1 / 2 : ℝ) ^ V := by positivity
  have h1 := hta.add (w := V) htb (B := 2 * G + 6) (by
    have : |tav + tbv| ≤ G := by rw [abs_le]; constructor <;> linarith
    linarith)
  have h2 := h1.sub (w := V) hts (B := 2 * G + 6) (by
    have : |tav + tbv - tsv| ≤ G := by rw [abs_le]; constructor <;> linarith
    linarith)
  have hqa0 := hqa.pos
  have hqb0 := hqb.pos
  have hqs0 := hqs.pos
  have hlogQ : Real.log (qav * qbv / qsv) = Real.log qav + Real.log qbv - Real.log qsv := by
    rw [Real.log_div (mul_pos hqa0 hqb0).ne' hqs0.ne', Real.log_mul hqa0.ne' hqb0.ne']
  have hQG : |Real.log (qav * qbv / qsv)| ≤ G := by
    rw [hlogQ, abs_le]; constructor <;> linarith
  have hQ := ((hqa.mul hu8 hqb).div hu8 hqs).mono (le_of_eq (by ring :
    la + lb + 6 * (1 / 2 : ℝ) ^ V + ls + 6 * (1 / 2 : ℝ) ^ V
      = la + lb + ls + 12 * (1 / 2 : ℝ) ^ V))
  have hL := (hQ.lnOfEncl (by positivity) hlam hQG hV).half
  have hlnW0 := lnW_nonneg hG0 V
  have h3 := h2.add (w := V) hL (B := 2 * G + 6) (by
    have hQa := abs_le.mp hQG
    have : |tav + tbv - tsv + Real.log (qav * qbv / qsv) / 2| ≤ G + G / 2 := by
      rw [abs_le]; constructor <;> linarith
    linarith)
  refine h3.mono (le_of_eq ?_)
  ring

/-! ### The integer next to a sum, and the sine at it -/

theorem roundVal_nearest_abs (w : ℕ) [NeZero w] (x : ℝ) :
    ∃ v : ℝ, (roundVal w .Nearest (some (x : EReal))).1.toVal = some (v : EReal) ∧
      |v - x| ≤ 2 * |x| * (1 / 2 : ℝ) ^ w := by
  obtain ⟨vf, hf, hf1, hf2⟩ := roundVal_floor_abs w x
  obtain ⟨vc, hc, hc1, hc2⟩ := roundVal_ceiling_abs w x
  rw [(roundVal_coe w .Floor x).1] at hf
  rw [(roundVal_coe w .Ceiling x).1] at hc
  rw [(roundVal_coe w .Nearest x).1]
  have hnn : 0 ≤ 2 * |x| * (1 / 2 : ℝ) ^ w := by positivity
  rcases round_nearest_eq_or (floatSet w) x with h | h
  · exact ⟨vf, by rw [h]; exact hf, by rw [abs_le]; constructor <;> linarith⟩
  · exact ⟨vc, by rw [h]; exact hc, by rw [abs_le]; constructor <;> linarith⟩

theorem subNearest_abs {u v : AzFloat} {uv vv : ℝ} (hu : u.toVal = some (uv : EReal))
    (hv : v.toVal = some (vv : EReal)) (w : ℕ) [NeZero w] :
    ∃ r : ℝ, (subPrecRound u v w .Nearest).1.toVal = some (r : EReal) ∧
      |r - (uv - vv)| ≤ 2 * |uv - vv| * (1 / 2 : ℝ) ^ w := by
  rw [subPrecRound_eq_liftVal₂, liftVal₂, hu, hv, Option.bind_some, Option.bind_some,
    Spec.sub_coe_coe]
  exact roundVal_nearest_abs w _

theorem addNearest_abs {u v : AzFloat} {uv vv : ℝ} (hu : u.toVal = some (uv : EReal))
    (hv : v.toVal = some (vv : EReal)) (w : ℕ) [NeZero w] :
    ∃ r : ℝ, (addPrecRound u v w .Nearest).1.toVal = some (r : EReal) ∧
      |r - (uv + vv)| ≤ 2 * |uv + vv| * (1 / 2 : ℝ) ^ w := by
  rw [addPrecRound_eq_liftVal₂, liftVal₂, hu, hv, Option.bind_some, Option.bind_some,
    Spec.add_coe_coe]
  exact roundVal_nearest_abs w _

/-- The integer next to a float `x ≤ 0` is within `3/4` of it. -/
theorem gammaNearInt_spec_nonpos {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (h0 : xv ≤ 0) : |xv - ((gammaNearInt x).toInt : ℝ)| ≤ 3 / 4 := by
  obtain ⟨ht, ht2⟩ := truncToAzInt_spec hx
  have : NeZero 64 := ⟨by norm_num⟩
  obtain ⟨d, hd, hdabs⟩ := subNearest_abs hx (toVal_ofAzInt (truncToAzInt x)) 64
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = ((truncToAzInt x).toInt : ℝ) := ⟨_, rfl⟩
  rw [← htdef] at ht ht2 hdabs
  have habs := abs_lt.mp ht
  have ht0 : t ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have h1 : (1 : ℝ) ≤ t := by
      rw [htdef] at hpos ⊢
      have : (0 : ℤ) < (truncToAzInt x).toInt := by exact_mod_cast hpos
      exact_mod_cast (by omega : (1 : ℤ) ≤ (truncToAzInt x).toInt)
    linarith
  have hxt : xv ≤ t := by
    rw [abs_of_nonpos ht0, abs_of_nonpos h0] at ht2
    linarith
  have hy : |xv - t| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hdb : |d - (xv - t)| ≤ 1 / 32 := by
    refine hdabs.trans ?_
    have h64 : (1 / 2 : ℝ) ^ 64 ≤ 1 / 64 := by norm_num
    have := mul_le_mul hy h64 (by positivity) zero_le_one
    linarith
  have hdb' := abs_le.mp hdb
  have hh : (-(one <<< AzInt.ofInt (-1))).toVal = some (((-(1 / 2) : ℝ)) : EReal) := by
    rw [toVal_neg, toVal_shiftLeft_of_toVal toVal_one', Option.map_some, AzInt.toInt_ofInt]
    norm_num
  unfold gammaNearInt
  dsimp only
  split_ifs with hc
  · have hlt := (lt_eq_true_iff hd hh).mp hc
    rw [AzInt.toInt_sub]
    have h1 : ((1 : AzInt).toInt : ℝ) = 1 := by norm_num [show (1 : AzInt).toInt = 1 from rfl]
    push_cast
    rw [h1, ← htdef, abs_le]
    constructor <;> linarith
  · have hge : ¬ d < -(1 / 2) := fun h => hc ((lt_eq_true_iff hd hh).mpr h)
    push Not at hge
    rw [← htdef, abs_le]
    constructor <;> linarith

/-- **The integer next to a negative sum is less than `1` away from it**, whatever the sizes
of the terms. -/
theorem betaSumNear_spec {a b : AzFloat} {av bv : ℝ} (ha : a.toVal = some (av : EReal))
    (hb : b.toVal = some (bv : EReal)) (hneg : av + bv < 0) :
    |av + bv - ((gammaNearInt (addPrecRound a b (betaSumPrec a b) .Nearest).1).toInt : ℝ)|
      < 1 := by
  have hP0 : 66 ≤ betaSumPrec a b := Nat.le_add_right _ _
  have : NeZero (betaSumPrec a b) := ⟨by omega⟩
  obtain ⟨r, hr, hrabs⟩ := addNearest_abs ha hb (betaSumPrec a b)
  -- the size of the sum
  obtain ⟨E, hE⟩ : ∃ E : ℤ, E = ((if expOf a ≤ expOf b then expOf b else expOf a) + 1).toInt :=
    ⟨_, rfl⟩
  have hEa : (expOf a).toInt ≤ E - 1 ∧ (expOf b).toInt ≤ E - 1 := by
    rw [hE, AzInt.toInt_add, show (1 : AzInt).toInt = 1 from rfl]
    split_ifs with hc
    · have := (AzInt.le_iff_toInt_le _ _).mp hc
      omega
    · have := (AzInt.le_iff_toInt_le _ _).not.mp hc
      omega
  have hPE : ((betaSumPrec a b : ℕ) : ℤ) = 66 + max E 0 := by
    have hmax := expPos_eq_max ((if expOf a ≤ expOf b then expOf b else expOf a) + 1)
    rw [← hE] at hmax
    unfold betaSumPrec
    dsimp only
    rw [Nat.cast_add, hmax]
    norm_num
  have h1 := abs_lt_two_zpow_expOf ha
  have h2 := abs_lt_two_zpow_expOf hb
  have h3 : (2 : ℝ) ^ (expOf a).toInt ≤ 2 ^ (E - 1) :=
    zpow_le_zpow_right₀ (by norm_num) hEa.1
  have h4 : (2 : ℝ) ^ (expOf b).toInt ≤ 2 ^ (E - 1) :=
    zpow_le_zpow_right₀ (by norm_num) hEa.2
  have h5 : (2 : ℝ) ^ (1 + (E - 1)) = 2 * 2 ^ (E - 1) := zpow_one_add₀ (by norm_num) _
  rw [show 1 + (E - 1) = E by ring] at h5
  have hs : |av + bv| < 2 ^ E := by
    have := abs_add_le av bv
    linarith
  have hu : (1 / 2 : ℝ) ^ betaSumPrec a b = 2 ^ (-((betaSumPrec a b : ℕ) : ℤ)) := by
    rw [zpow_neg, zpow_natCast, one_div, inv_pow]
  have hu0 : (0 : ℝ) < (1 / 2 : ℝ) ^ betaSumPrec a b := by positivity
  have hsu : |av + bv| * (1 / 2 : ℝ) ^ betaSumPrec a b ≤ 1 / 64 := by
    have h6 : |av + bv| * (1 / 2 : ℝ) ^ betaSumPrec a b
        ≤ 2 ^ E * (1 / 2 : ℝ) ^ betaSumPrec a b :=
      mul_le_mul_of_nonneg_right hs.le hu0.le
    have h7 : (2 : ℝ) ^ E * (1 / 2 : ℝ) ^ betaSumPrec a b
        = 2 ^ (E + -((betaSumPrec a b : ℕ) : ℤ)) := by
      rw [hu, zpow_add₀ (by norm_num)]
    have h8 : (2 : ℝ) ^ (E + -((betaSumPrec a b : ℕ) : ℤ)) ≤ 2 ^ (-6 : ℤ) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h9 : (2 : ℝ) ^ (-6 : ℤ) = 1 / 64 := by norm_num
    exact h6.trans (h7.le.trans (h8.trans h9.le))
  have hrabs' := abs_le.mp (hrabs.trans (le_of_eq (by ring :
    2 * |av + bv| * (1 / 2 : ℝ) ^ betaSumPrec a b
      = 2 * (|av + bv| * (1 / 2 : ℝ) ^ betaSumPrec a b))))
  have hr0 : r ≤ 0 := by
    have h10 : |av + bv| = -(av + bv) := abs_of_neg hneg
    rw [h10] at hrabs'
    have h11 := mul_le_mul_of_nonneg_left (half_pow_le_eighth (by omega : 3 ≤ betaSumPrec a b))
      (by linarith : (0 : ℝ) ≤ -(av + bv))
    linarith
  have hk := abs_le.mp (gammaNearInt_spec_nonpos hr hr0)
  rw [abs_lt]
  constructor <;> linarith

/-- `fracOfEncl` answers once the enclosure is narrow against the number. -/
theorem fracOfEncl_some {D : Encl} {d ε : ℝ} (hD : AEncl D d ε) (hε : 2 * ε ≤ |d|)
    (hd : d ≠ 0) :
    ∃ (σ : Bool) (A : Encl), fracOfEncl D = some (σ, A) ∧ LEncl A |d| (2 * ε / |d|) := by
  have hd0 : 0 < |d| := abs_pos.mpr hd
  obtain ⟨l, h, hl, hh, h1, h2, h3⟩ := id hD
  unfold fracOfEncl
  rcases lt_or_gt_of_ne hd with hneg | hpos
  · rw [abs_of_neg hneg] at hε hd0 ⊢
    have c1 : lt zero D.1 = false := by
      rw [← Bool.not_eq_true, lt_eq_true_iff toVal_zero' hl]
      linarith
    have c2 : lt D.2 zero = true := (lt_eq_true_iff hh toVal_zero').mpr (by linarith)
    refine ⟨true, Encl.neg D, by simp only [c1, c2, Bool.false_eq_true, ↓reduceIte], ?_⟩
    exact LEncl.ofA hD.neg hε hd0
  · rw [abs_of_pos hpos] at hε hd0 ⊢
    have c1 : lt zero D.1 = true := (lt_eq_true_iff toVal_zero' hl).mpr (by linarith)
    exact ⟨false, D, by simp only [c1, ↓reduceIte], LEncl.ofA hD hε hd0⟩

/-- `gammaSinOfFrac` on an enclosure of any small relative width. -/
theorem gammaSinOfFrac_some' {σ : Bool} {k : AzInt} {A : Encl} {a lamA : ℝ} {W : ℕ}
    (hW : 64 ≤ W) (hA : LEncl A a lamA) (hlam0 : 0 ≤ lamA) (hlam : lamA ≤ 1 / 64) (ha : a < 1)
    {w : ℕ} (hw : 64 ≤ w) (henv : sinEnv w ≤ 1)
    (hsmall : sinEnv w + 32 * lamA + 304 * (1 / 2 : ℝ) ^ W < Real.sin (a * Real.pi)) :
    ∃ S, gammaSinOfFrac σ k A W w = some (σ != k.isOdd, S) ∧
      AEncl S (Real.sin (a * Real.pi)) (sinEnv w + 32 * lamA + 304 * (1 / 2 : ℝ) ^ W) := by
  have : NeZero W := ⟨by omega⟩
  have hu := half_pow_le_of_64 hW
  have hu0 : (0 : ℝ) < (1 / 2 : ℝ) ^ W := by positivity
  have hu8 : (1 / 2 : ℝ) ^ W ≤ 1 / 8 := hu.trans (by norm_num)
  have hu' : (1 / 2 : ℝ) ^ W ≤ 1 / 576 := hu.trans (by norm_num)
  have ha0 := hA.pos
  have hY : LEncl (Encl.mul W A (Encl.pi W)) (a * Real.pi) (lamA + 9 * (1 / 2 : ℝ) ^ W) :=
    (hA.mul hu8 (LEncl.pi hW)).mono (by linarith)
  have hy4 : a * Real.pi ≤ 4 := by nlinarith [Real.pi_le_four, Real.pi_pos]
  have hS := (sinOfEncl_width hY (by positivity) (by linarith) hy4 hW hw
    (Nat.le_add_right w (sinLostBits (Encl.mul W A (Encl.pi W)).1)) henv).mono
    (by linarith : sinEnv w + 32 * (lamA + 9 * (1 / 2 : ℝ) ^ W) + 16 * (1 / 2 : ℝ) ^ W
      ≤ sinEnv w + 32 * lamA + 304 * (1 / 2 : ℝ) ^ W)
  refine ⟨_, ?_, hS⟩
  obtain ⟨c, d, hc, hd, hc1, hd1, hcd⟩ := hS
  have hc0 : 0 < c := by linarith
  unfold gammaSinOfFrac
  dsimp only
  rw [(lt_eq_true_iff toVal_zero' hc).mpr hc0]
  rfl

theorem AEncl.of_isEncl {a : Encl} {x y ε : ℝ} (h : AEncl a x ε) (h' : IsEncl a y) :
    AEncl a y ε := by
  obtain ⟨l, u, hl, hu, h1, h2, h3⟩ := h
  obtain ⟨l', u', hl', hu', h1', h2'⟩ := h'
  rw [hl, Option.some.injEq, EReal.coe_eq_coe_iff] at hl'
  rw [hu, Option.some.injEq, EReal.coe_eq_coe_iff] at hu'
  subst hl' hu'
  exact ⟨l, u, hl, hu, h1', h2', h3⟩

/-- The working precision `V ≥ W + log₂ W` of level `W` gains a factor `W / 2` on the
level. -/
theorem natCast_mul_half_pow_le {W V : ℕ} (hV : W + W.log2 ≤ V) :
    (W : ℝ) * (1 / 2 : ℝ) ^ V ≤ 2 * (1 / 2 : ℝ) ^ W := by
  have h1 : (1 / 2 : ℝ) ^ V ≤ (1 / 2 : ℝ) ^ (W + W.log2) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hV
  have h2 : (W : ℝ) ≤ 2 ^ (W.log2 + 1) := by exact_mod_cast (Nat.lt_log2_self (n := W)).le
  have h3 : (W : ℝ) * (1 / 2 : ℝ) ^ W.log2 ≤ 2 := by
    have h4 : (2 : ℝ) ^ (W.log2 + 1) * (1 / 2 : ℝ) ^ W.log2 = 2 := by
      rw [pow_succ, one_div, inv_pow]
      field_simp
    have := mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ W.log2)
    linarith
  calc (W : ℝ) * (1 / 2 : ℝ) ^ V ≤ W * (1 / 2 : ℝ) ^ (W + W.log2) :=
        mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg W)
    _ = (W * (1 / 2 : ℝ) ^ W.log2) * (1 / 2 : ℝ) ^ W := by rw [pow_add]; ring
    _ ≤ 2 * (1 / 2 : ℝ) ^ W := mul_le_mul_of_nonneg_right h3 (by positivity)

/-! ### Convergent arguments -/

/-- **An argument of the Beta bracket converges**: its enclosures at the working precision
`V` have widths `O(2^(−V))`, and for a negative argument the sine of the reflection formula
converges. -/
def ArgConv (X : ℕ → Encl) (F : ℕ → Option (Bool × AzInt × Encl)) (v : ℝ) : Prop :=
  (∃ K : ℝ, ∀ V, 64 ≤ V → AEncl (X V) v (K * (1 / 2 : ℝ) ^ V)) ∧
    (0 < v ∨ (v < 0 ∧ SinConv
      (fun ws => (F (ws + 16)).bind fun t => gammaSinOfFrac t.1 t.2.1 t.2.2 (ws + 16) ws) v))

/-- The piece of an argument inside `lnAbsBetaEncl` at level `W` (sines at level `ws`) on `M`
terms. -/
def pieceAt (X : ℕ → Encl) (F : ℕ → Option (Bool × AzInt × Encl)) (e : AzInt) (M W ws : ℕ) :
    Option (Bool × Encl × Encl) :=
  lnGammaPiece (X (W + 2 * lnGammaShiftExp W + 8 + 2 * W.log2)) e (fun _ => F (ws + 16))
    (Encl.pi (W + 2 * lnGammaShiftExp W + 8 + 2 * W.log2)) (lnGammaShiftExp W)
    (W + 2 * lnGammaShiftExp W + 8 + 2 * W.log2) M (AzNat.tangentNumbers M)
    (powerOf2 (-(AzNat.ofNat (W + 16)).toAzInt)) ws

/-- An enclosure of width `O(2^(−V))` has relative width at most `8 · 2^(−W)` at a large
level `W`. -/
theorem lencl_of_level {X : Encl} {x K : ℝ} {W V : ℕ} (hW : 64 ≤ W) (hV : W + W.log2 ≤ V)
    (hx : 0 < x) (hK : K ≤ W * x)
    (h : AEncl X x (K * (1 / 2 : ℝ) ^ V + 8 * x * (1 / 2 : ℝ) ^ V)) :
    ∃ lam₀ : ℝ, LEncl X x lam₀ ∧ 0 ≤ lam₀ ∧ lam₀ ≤ 8 * (1 / 2 : ℝ) ^ W := by
  have hWu := natCast_mul_half_pow_le hV
  have hu0 : (0 : ℝ) < (1 / 2 : ℝ) ^ V := by positivity
  have hU8 : (1 / 2 : ℝ) ^ W ≤ 1 / 8 := half_pow_le_eighth (by omega)
  have hU0 : (0 : ℝ) < (1 / 2 : ℝ) ^ W := by positivity
  have hWR : (64 : ℝ) ≤ W := by exact_mod_cast hW
  have h64 : 64 * (1 / 2 : ℝ) ^ V ≤ W * (1 / 2 : ℝ) ^ V :=
    mul_le_mul_of_nonneg_right hWR hu0.le
  have hKu : K * (1 / 2 : ℝ) ^ V ≤ W * x * (1 / 2 : ℝ) ^ V :=
    mul_le_mul_of_nonneg_right hK hu0.le
  have hxWu : x * (W * (1 / 2 : ℝ) ^ V) ≤ x * (2 * (1 / 2 : ℝ) ^ W) :=
    mul_le_mul_of_nonneg_left hWu hx.le
  have hxu : x * (1 / 2 : ℝ) ^ V ≤ x * ((1 / 2 : ℝ) ^ W / 32) :=
    mul_le_mul_of_nonneg_left (by linarith) hx.le
  have hxU : x * (1 / 2 : ℝ) ^ W ≤ x * (1 / 8) := mul_le_mul_of_nonneg_left hU8 hx.le
  have hε0 : 0 ≤ K * (1 / 2 : ℝ) ^ V + 8 * x * (1 / 2 : ℝ) ^ V := by
    obtain ⟨l, u, -, -, c1, c2, c3⟩ := h
    linarith
  have hε : K * (1 / 2 : ℝ) ^ V + 8 * x * (1 / 2 : ℝ) ^ V ≤ 3 * (x * (1 / 2 : ℝ) ^ W) := by
    linarith
  refine ⟨_, LEncl.ofA h (by linarith) hx, by positivity, ?_⟩
  rw [div_le_iff₀ hx]
  linarith

/-- **A piece converges** at a convergent argument, on any number of terms `m` that tends to
infinity within the bounds of `ln Γ`. -/
theorem pieceAt_conv {X : ℕ → Encl} {F : ℕ → Option (Bool × AzInt × Encl)} {v : ℝ}
    (h : ArgConv X F v) (e : AzInt) (c : ℕ) {m : ℕ → ℕ} (hm4 : ∀ w, 4 ≤ m w)
    (hm : ∀ w, m w ≤ w / 2 + 4) (hmt : Tendsto (fun w => 2 * m w - 1) atTop atTop) :
    ∃ E lam G : ℕ → ℝ, Tendsto E atTop (𝓝 0) ∧ Tendsto lam atTop (𝓝 0) ∧ PB G ∧
      ∀ᶠ w in atTop, ∃ (neg : Bool) (t q : Encl) (tv qv : ℝ),
        pieceAt X F e (m (w + c)) (w + c) w = some (neg, t, q) ∧
        AEncl t tv (E w) ∧ LEncl q qv (lam w) ∧ 0 ≤ lam w ∧ |tv| ≤ G w ∧
        |Real.log qv| ≤ G w := by
  obtain ⟨⟨K, hK⟩, hsign⟩ := h
  have hshift := tendsto_add_atTop_nat c
  have hU : Tendsto (fun w : ℕ => (1 / 2 : ℝ) ^ (w + c)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp hshift
  have hwU : Tendsto (fun w : ℕ => 41 * ((w + c : ℕ) : ℝ) * (1 / 2 : ℝ) ^ (w + c)) atTop
      (𝓝 0) := ((PB.natCast.const_mul 41).tendsto).comp hshift
  have hcast : (fun w : ℕ => ((w + c : ℕ) : ℝ)) = fun w : ℕ => (w : ℝ) + c := by
    funext w
    push_cast
    rfl
  have hPBw : PB fun w : ℕ => ((w + c : ℕ) : ℝ) := by
    rw [hcast]
    exact PB.natCast.add (PB.const _)
  have hPBG : ∀ x cc : ℝ, PB fun w : ℕ => pcG x cc (w + c) := by
    intro x cc
    unfold pcG
    exact (PB.const _).add ((hPBw.mul ((PB.const _).add ((PB.const x).add hPBw))).const_mul 2)
  rcases hsign with hv | ⟨hv, hSin⟩
  · -- a positive argument
    have hE := (tendsto_pcEps v hm hmt).comp hshift
    refine ⟨fun w => pcEps v (m (w + c)) (w + c),
      fun w => 41 * ((w + c : ℕ) : ℝ) * (1 / 2 : ℝ) ^ (w + c) + 2 * 0,
      fun w => pcG v 0 (w + c), hE, by simpa using hwU, hPBG v 0, ?_⟩
    filter_upwards [hE.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 3 / 8)),
      eventually_ge_atTop (64 * (2 ^ e.abs.toNat + 1)), eventually_ge_atTop ⌈K / v⌉₊]
      with w h1 h2 h3
    have hW64 : 64 ≤ w + c := by
      have : 1 ≤ 2 ^ e.abs.toNat := Nat.one_le_two_pow
      omega
    have hK' : K ≤ ((w + c : ℕ) : ℝ) * v := by
      have h4 := (div_le_iff₀ hv).mp (Nat.le_of_ceil_le h3)
      have h5 : (w : ℝ) * v ≤ ((w + c : ℕ) : ℝ) * v :=
        mul_le_mul_of_nonneg_right (by push_cast; linarith [(Nat.cast_nonneg c : (0 : ℝ) ≤ c)])
          hv.le
      linarith
    obtain ⟨V, hV⟩ : ∃ V : ℕ, V = w + c + 2 * lnGammaShiftExp (w + c) + 8 + 2 * (w + c).log2 :=
      ⟨_, rfl⟩
    have hXA := hK V (by omega)
    obtain ⟨lam₀, hXL, hl0, hl8⟩ := lencl_of_level (V := V) hW64 (by omega) hv hK'
      (hXA.mono (by
        have : (0 : ℝ) ≤ 8 * v * (1 / 2 : ℝ) ^ V := by positivity
        linarith))
    subst hV
    obtain ⟨t, q, tv, qv, hp, ht, hq, hG1, hG2⟩ := lnGammaPiece_pos_width hv e hW64 (by omega)
      (hm4 _) (hm _) h1 hXL hl0 hl8 (fun _ => F (w + 16)) w
    exact ⟨false, t, q, tv, qv, hp, ht, hq, by positivity, hG1, hG2⟩
  · -- a negative argument
    obtain ⟨ES, htS, hevS⟩ := hSin
    obtain ⟨s, hs⟩ : ∃ s : ℝ, s = |Real.sin (Real.pi * v)| := ⟨_, rfl⟩
    rw [← hs] at hevS
    have hs0 : 0 < s := by
      obtain ⟨w, neg, S', -, hSp, -⟩ := hevS.exists
      rw [hs]
      exact abs_pos.mpr fun h0 => by
        obtain ⟨l, u, -, -, hl0, hl1, -⟩ := hSp
        rw [h0, mul_zero] at hl1
        linarith
    have hx₁ : 0 < 1 - v := by linarith
    have hlamS : Tendsto (fun w => 2 * (2 * ES w / s)) atTop (𝓝 0) := by
      simpa using ((htS.const_mul 2).div_const s).const_mul 2
    have hKU : Tendsto (fun w : ℕ => K * (1 / 2 : ℝ) ^ (w + c)) atTop (𝓝 0) := by
      simpa using hU.const_mul K
    have hE := (tendsto_pcEps (1 - v) hm hmt).comp hshift
    refine ⟨fun w => pcEps (1 - v) (m (w + c)) (w + c),
      fun w => 41 * ((w + c : ℕ) : ℝ) * (1 / 2 : ℝ) ^ (w + c) + 2 * (2 * ES w / s),
      fun w => pcG (1 - v) (2 * |Real.log s|) (w + c), hE, by simpa using hwU.add hlamS,
      hPBG _ _, ?_⟩
    filter_upwards [hE.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 3 / 8)),
      eventually_ge_atTop (64 * (2 ^ ((if e.sign then e else 0) + 1).abs.toNat + 1)),
      eventually_ge_atTop ⌈K / (1 - v)⌉₊, hevS, htS.eventually (ge_mem_nhds (half_pos hs0)),
      hKU.eventually (gt_mem_nhds (neg_pos.mpr hv))] with w h1 h2 h3 h4 h5 h6
    have hW64 : 64 ≤ w + c := by
      have : 1 ≤ 2 ^ ((if e.sign then e else 0) + 1).abs.toNat := Nat.one_le_two_pow
      omega
    have hK' : K ≤ ((w + c : ℕ) : ℝ) * (1 - v) := by
      have h7 := (div_le_iff₀ hx₁).mp (Nat.le_of_ceil_le h3)
      have h8 : (w : ℝ) * (1 - v) ≤ ((w + c : ℕ) : ℝ) * (1 - v) :=
        mul_le_mul_of_nonneg_right (by push_cast; linarith [(Nat.cast_nonneg c : (0 : ℝ) ≤ c)])
          hx₁.le
      linarith
    obtain ⟨V, hV⟩ : ∃ V : ℕ, V = w + c + 2 * lnGammaShiftExp (w + c) + 8 + 2 * (w + c).log2 :=
      ⟨_, rfl⟩
    have hV64 : 64 ≤ V := by omega
    have : NeZero V := ⟨by omega⟩
    have hu0 : (0 : ℝ) < (1 / 2 : ℝ) ^ V := by positivity
    have hu : (1 / 2 : ℝ) ^ V ≤ (1 / 2 : ℝ) ^ (w + c) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have hXA := hK V hV64
    obtain ⟨l, u, hl, hh, a1, a2, a3⟩ := id hXA
    have hK0 : 0 ≤ K := by
      by_contra hneg
      push Not at hneg
      have := mul_neg_of_neg_of_pos hneg hu0
      linarith
    have hKu : K * (1 / 2 : ℝ) ^ V ≤ K * (1 / 2 : ℝ) ^ (w + c) :=
      mul_le_mul_of_nonneg_left hu hK0
    have c1 : lt zero (X V).1 = false := by
      rw [← Bool.not_eq_true, lt_eq_true_iff toVal_zero' hl]
      linarith
    have c2 : lt (X V).2 zero = true := (lt_eq_true_iff hh toVal_zero').mpr (by linarith)
    have hone : AEncl (Encl.exact one) 1 0 :=
      ⟨1, 1, toVal_one', toVal_one', le_rfl, le_rfl, by simp⟩
    have hX₁A := (hone.sub (w := V) hXA (B := 2 * (1 - v)) (by
      rw [abs_of_pos hx₁]
      linarith)).mono (le_of_eq (by ring :
        0 + K * (1 / 2 : ℝ) ^ V + 4 * (2 * (1 - v)) * (1 / 2 : ℝ) ^ V
          = K * (1 / 2 : ℝ) ^ V + 8 * (1 - v) * (1 / 2 : ℝ) ^ V))
    obtain ⟨lam₀, hXL, hl0, hl8⟩ := lencl_of_level (V := V) hW64 (by omega) hx₁ hK' hX₁A
    obtain ⟨neg, S', hF, hSp, hSw⟩ := h4
    have hES0 : 0 ≤ ES w := by
      obtain ⟨l', u', -, -, b1, b2, b3⟩ := hSw
      linarith
    have hSL : LEncl S' s (2 * ES w / s) := LEncl.ofA hSw (by linarith) hs0
    subst hV
    obtain ⟨t, q, tv, qv, hp, ht, hq, hG1, hG2⟩ := lnGammaPiece_neg_width hx₁ e hW64 (by omega)
      (hm4 _) (hm _) h1 c1 c2 hXL hl0 hl8 (F := fun _ => F (w + 16)) (ws := w) hF hSL
    refine ⟨neg, t, q, tv, qv, hp, ht, hq, ?_, hG1, hG2⟩
    have := div_nonneg (mul_nonneg zero_le_two hES0) hs0.le
    positivity

/-! ### The convergence of `lnAbsBetaEncl` -/

/-- The number of terms shared by the three pieces. -/
def betaTerms (ea eb es : AzInt) (W : ℕ) : ℕ :=
  max (max (lgTerms ea W) (lgTerms eb W)) (lgTerms es W)

theorem lnAbsBetaEncl_eq (A B S : ℕ → Encl) (ea eb es : AzInt)
    (Fa Fb Fs : ℕ → Option (Bool × AzInt × Encl)) (W ws : ℕ) :
    lnAbsBetaEncl A B S ea eb es Fa Fb Fs W ws
      = match pieceAt A Fa ea (betaTerms ea eb es W) W ws,
          pieceAt B Fb eb (betaTerms ea eb es W) W ws,
          pieceAt S Fs es (betaTerms ea eb es W) W ws with
        | some (na, ta, qa), some (nb, tb, qb), some (ns, ts, qs) =>
          some ((na != nb) != ns,
            Encl.add (W + 2 * lnGammaShiftExp W + 8 + 2 * W.log2)
              (Encl.sub (W + 2 * lnGammaShiftExp W + 8 + 2 * W.log2)
                (Encl.add (W + 2 * lnGammaShiftExp W + 8 + 2 * W.log2) ta tb) ts)
              (Encl.half (lnOfEncl (Encl.div (W + 2 * lnGammaShiftExp W + 8 + 2 * W.log2)
                (Encl.mul (W + 2 * lnGammaShiftExp W + 8 + 2 * W.log2) qa qb) qs)
                (W + 2 * lnGammaShiftExp W + 8 + 2 * W.log2))))
        | _, _, _ => none := rfl

/-- **The enclosure of `ln |Γ(a) Γ(b) / Γ(s)|` converges** at convergent arguments: at every
large level it answers, with a width that tends to `0`. -/
theorem lnAbsBetaEncl_conv {A B S : ℕ → Encl} {Fa Fb Fs : ℕ → Option (Bool × AzInt × Encl)}
    {av bv sv : ℝ} (hA : ArgConv A Fa av) (hB : ArgConv B Fb bv) (hS : ArgConv S Fs sv)
    (ea eb es : AzInt) (c : ℕ) :
    ∃ E : ℕ → ℝ, Tendsto E atTop (𝓝 0) ∧ ∀ᶠ w in atTop, ∃ (neg : Bool) (r : Encl) (x : ℝ),
      lnAbsBetaEncl A B S ea eb es Fa Fb Fs (w + c) w = some (neg, r) ∧ AEncl r x (E w) := by
  have hm4 : ∀ w, 4 ≤ betaTerms ea eb es w := fun w =>
    le_trans (lgTerms_le ea w).1 (le_trans (le_max_left _ _) (le_max_left _ _))
  have hm : ∀ w, betaTerms ea eb es w ≤ w / 2 + 4 := fun w =>
    max_le (max_le (lgTerms_le ea w).2 (lgTerms_le eb w).2) (lgTerms_le es w).2
  have hmt : Tendsto (fun w => 2 * betaTerms ea eb es w - 1) atTop atTop :=
    tendsto_atTop_mono (fun w => by
      have : lgTerms ea w ≤ betaTerms ea eb es w :=
        le_trans (le_max_left _ _) (le_max_left _ _)
      omega) (tendsto_lgTerms ea)
  obtain ⟨Ea, la, Ga, hEa, hla, hGa, heva⟩ := pieceAt_conv hA ea c hm4 hm hmt
  obtain ⟨Eb, lb, Gb, hEb, hlb, hGb, hevb⟩ := pieceAt_conv hB eb c hm4 hm hmt
  obtain ⟨Es, ls, Gs, hEs, hls, hGs, hevs⟩ := pieceAt_conv hS es c hm4 hm hmt
  have hG : PB fun w => Ga w + Gb w + Gs w := (hGa.add hGb).add hGs
  have hcast : (fun w : ℕ => ((w + c : ℕ) : ℝ)) = fun w : ℕ => (w : ℝ) + c := by
    funext w
    push_cast
    rfl
  have hPBw : PB fun w : ℕ => ((w + c : ℕ) : ℝ) := by
    rw [hcast]
    exact PB.natCast.add (PB.const _)
  have hT1 : Tendsto (fun w : ℕ => 2 ^ 42
      * (6 * ((w + c : ℕ) : ℝ) + 2 * (Ga w + Gb w + Gs w) + 10) ^ 5 * (1 / 2 : ℝ) ^ w) atTop
      (𝓝 0) :=
    (((((hPBw.const_mul 6).add (hG.const_mul 2)).add (PB.const 10)).pow 5).const_mul _).tendsto
  have hT2 : Tendsto (fun w : ℕ => 12 * (2 * (Ga w + Gb w + Gs w) + 6) * (1 / 2 : ℝ) ^ w)
      atTop (𝓝 0) := (((hG.const_mul 2).add (PB.const 6)).const_mul 12).tendsto
  have hpow : Tendsto (fun w : ℕ => (1 / 2 : ℝ) ^ w) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hlam : Tendsto (fun w => la w + lb w + ls w + 12 * (1 / 2 : ℝ) ^ w) atTop (𝓝 0) := by
    simpa using ((hla.add hlb).add hls).add (hpow.const_mul 12)
  have hE : Tendsto (fun w => Ea w + Eb w + Es w
      + (2 ^ 42 * (6 * ((w + c : ℕ) : ℝ) + 2 * (Ga w + Gb w + Gs w) + 10) ^ 5 * (1 / 2 : ℝ) ^ w
        + 5 * (la w + lb w + ls w + 12 * (1 / 2 : ℝ) ^ w)) / 2
      + 12 * (2 * (Ga w + Gb w + Gs w) + 6) * (1 / 2 : ℝ) ^ w) atTop (𝓝 0) := by
    simpa using (((hEa.add hEb).add hEs).add ((hT1.add (hlam.const_mul 5)).div_const 2)).add hT2
  refine ⟨_, hE, ?_⟩
  filter_upwards [heva, hevb, hevs, hEa.eventually (ge_mem_nhds one_pos),
    hEb.eventually (ge_mem_nhds one_pos), hEs.eventually (ge_mem_nhds one_pos),
    hT1.eventually (ge_mem_nhds one_pos),
    hlam.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)), eventually_ge_atTop 64]
    with w ha hb hs h1 h2 h3 h4 h5 h6
  obtain ⟨na, ta, qa, tav, qav, hpa, hta, hqa, hla0, hGa1, hGa2⟩ := ha
  obtain ⟨nb, tb, qb, tbv, qbv, hpb, htb, hqb, hlb0, hGb1, hGb2⟩ := hb
  obtain ⟨ns, ts, qs, tsv, qsv, hps, hts, hqs, hls0, hGs1, hGs2⟩ := hs
  rw [lnAbsBetaEncl_eq, hpa, hpb, hps]
  obtain ⟨V, hV⟩ : ∃ V : ℕ, V = w + c + 2 * lnGammaShiftExp (w + c) + 8 + 2 * (w + c).log2 :=
    ⟨_, rfl⟩
  rw [← hV]
  have hLlog := shiftExp_le_log2 (by omega : 4 ≤ w + c)
  have hlogw := log2_le_self (w + c)
  have hV64 : 64 ≤ V := by omega
  have hu0 : (0 : ℝ) < (1 / 2 : ℝ) ^ V := by positivity
  have hu : (1 / 2 : ℝ) ^ V ≤ (1 / 2 : ℝ) ^ w :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hG0 : 0 ≤ Ga w + Gb w + Gs w := by
    have := (abs_nonneg tav).trans hGa1
    have := (abs_nonneg tbv).trans hGb1
    have := (abs_nonneg tsv).trans hGs1
    linarith
  have hlnW : lnW (Ga w + Gb w + Gs w) V
      ≤ 2 ^ 42 * (6 * ((w + c : ℕ) : ℝ) + 2 * (Ga w + Gb w + Gs w) + 10) ^ 5
        * (1 / 2 : ℝ) ^ w := by
    refine (lnW_le hG0 (w := w + c) (by omega) (by omega)).trans ?_
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_right w c)) (by positivity)
  have key := betaCombine_width hV64 hta htb hts hqa hqb hqs hla0 hlb0 hls0 (by linarith)
    h1 h2 h3 hGa1 hGb1 hGs1 hGa2 hGb2 hGs2 (hlnW.trans h4)
  refine ⟨_, _, _, rfl, key.mono ?_⟩
  have h7 : 12 * (2 * (Ga w + Gb w + Gs w) + 6) * (1 / 2 : ℝ) ^ V
      ≤ 12 * (2 * (Ga w + Gb w + Gs w) + 6) * (1 / 2 : ℝ) ^ w :=
    mul_le_mul_of_nonneg_left hu (by positivity)
  linarith

/-- **The enclosure of `ln |Γ(a) Γ(b) / Γ(s)|` converges to it.** -/
theorem lnAbsBetaEncl_conv_log {A B S : ℕ → Encl}
    {Fa Fb Fs : ℕ → Option (Bool × AzInt × Encl)} {av bv sv : ℝ} (hA : ArgConv A Fa av)
    (hB : ArgConv B Fb bv) (hS : ArgConv S Fs sv)
    (hFa : ∀ W σ k E, 64 ≤ W → Fa W = some (σ, k, E) →
      IsEnclPos E ((if σ then -1 else 1) * (av - k.toInt)))
    (hFb : ∀ W σ k E, 64 ≤ W → Fb W = some (σ, k, E) →
      IsEnclPos E ((if σ then -1 else 1) * (bv - k.toInt)))
    (hFs : ∀ W σ k E, 64 ≤ W → Fs W = some (σ, k, E) →
      IsEnclPos E ((if σ then -1 else 1) * (sv - k.toInt))) (ea eb es : AzInt) (c : ℕ) :
    ∃ E : ℕ → ℝ, Tendsto E atTop (𝓝 0) ∧ ∀ᶠ w in atTop, ∃ (neg : Bool) (r : Encl),
      lnAbsBetaEncl A B S ea eb es Fa Fb Fs (w + c) w = some (neg, r) ∧
      AEncl r (Real.log |Real.Gamma av * Real.Gamma bv / Real.Gamma sv|) (E w) := by
  obtain ⟨E, hE, hev⟩ := lnAbsBetaEncl_conv hA hB hS ea eb es c
  obtain ⟨Ka, hKa⟩ := hA.1
  obtain ⟨Kb, hKb⟩ := hB.1
  obtain ⟨Ks, hKs⟩ := hS.1
  refine ⟨E, hE, ?_⟩
  filter_upwards [hev, eventually_ge_atTop 64] with w h1 h3
  obtain ⟨neg, r, x, hc, hr⟩ := h1
  obtain ⟨hpos, hL⟩ := lnAbsBetaEncl_spec (fun V hV => (hKa V hV).isEncl)
    (fun V hV => (hKb V hV).isEncl) (fun V hV => (hKs V hV).isEncl) hFa hFb hFs
    (by omega : 64 ≤ w + c) h3 hc
  rw [sign_mul_eq_abs hpos] at hL
  exact ⟨neg, r, hc, hr.of_isEncl hL⟩

/-- **The core of `Γ(a) Γ(b) / Γ(s)` converges** at convergent arguments. -/
theorem betaEnclOf_coreConv {A B S : ℕ → Encl} {Fa Fb Fs : ℕ → Option (Bool × AzInt × Encl)}
    {av bv sv : ℝ} (hA : ArgConv A Fa av) (hB : ArgConv B Fb bv) (hS : ArgConv S Fs sv)
    {ea eb es : AzInt}
    (hFa : ∀ W σ k E, 64 ≤ W → Fa W = some (σ, k, E) →
      IsEnclPos E ((if σ then -1 else 1) * (av - k.toInt)))
    (hFb : ∀ W σ k E, 64 ≤ W → Fb W = some (σ, k, E) →
      IsEnclPos E ((if σ then -1 else 1) * (bv - k.toInt)))
    (hFs : ∀ W σ k E, 64 ≤ W → Fs W = some (σ, k, E) →
      IsEnclPos E ((if σ then -1 else 1) * (sv - k.toInt))) :
    CoreConv (betaEnclOf A B S ea eb es Fa Fb Fs)
      (Real.Gamma av * Real.Gamma bv / Real.Gamma sv) := by
  obtain ⟨E, hE, hev⟩ := lnAbsBetaEncl_conv hA hB hS ea eb es (betaBits ea eb es)
  obtain ⟨Ka, hKa⟩ := hA.1
  obtain ⟨Kb, hKb⟩ := hB.1
  obtain ⟨Ks, hKs⟩ := hS.1
  obtain ⟨Bv, hBv⟩ : ∃ Bv : ℝ, Bv = Real.Gamma av * Real.Gamma bv / Real.Gamma sv := ⟨_, rfl⟩
  rw [← hBv]
  obtain ⟨ht, hevE⟩ := gammaExpEncl_eventually false (Real.log |Bv|) hE
  simp only [Bool.false_eq_true, ↓reduceIte] at ht hevE
  refine ⟨_, ht, ?_⟩
  filter_upwards [hev, hevE, eventually_ge_atTop 64] with w h1 h2 h3
  obtain ⟨neg, r, x, hc, hr⟩ := h1
  obtain ⟨hpos, hL⟩ := lnAbsBetaEncl_spec (fun V hV => (hKa V hV).isEncl)
    (fun V hV => (hKb V hV).isEncl) (fun V hV => (hKs V hV).isEncl) hFa hFb hFs
    (by omega : 64 ≤ w + betaBits ea eb es) h3 hc
  rw [← hBv] at hpos hL
  have habs := sign_mul_eq_abs hpos
  rw [habs] at hL
  have hB0 : 0 < |Bv| := habs ▸ hpos
  obtain ⟨b, hb, hb1, hb2⟩ := h2 r (hr.of_isEncl hL)
  rw [Real.exp_log hB0] at hb1 hb2
  refine ⟨neg, b, ?_, ?_, ?_⟩
  · unfold betaEnclOf
    rw [hc]
    simp [hb]
  · rw [habs]; exact hb1
  · rw [habs]; exact hb2

/-! ### Float arguments -/

theorem AEncl.exact {t : AzFloat} {tv : ℝ} (ht : t.toVal = some (tv : EReal)) :
    AEncl (Encl.exact t) tv 0 :=
  ⟨tv, tv, ht, ht, le_rfl, le_rfl, by simp⟩

/-- **The sine at a negative sum of two floats converges.** -/
theorem betaSumSin_conv {a b : AzFloat} {av bv : ℝ} (ha : a.toVal = some (av : EReal))
    (hb : b.toVal = some (bv : EReal)) (hneg : av + bv < 0) (hint : ∀ k : ℤ, av + bv ≠ k) :
    SinConv (fun w => (betaSumFrac a b (w + 16)).bind
      fun t => gammaSinOfFrac t.1 t.2.1 t.2.2 (w + 16) w) (av + bv) := by
  obtain ⟨k, hk⟩ : ∃ k : AzInt,
      k = gammaNearInt (addPrecRound a b (betaSumPrec a b) .Nearest).1 := ⟨_, rfl⟩
  have hk1 := betaSumNear_spec ha hb hneg
  rw [← hk] at hk1
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = av + bv - (k.toInt : ℝ) := ⟨_, rfl⟩
  rw [← hd] at hk1
  have hd0 : d ≠ 0 := by
    rw [hd]
    exact fun h => hint _ (sub_eq_zero.mp h)
  have hdpos : 0 < |d| := abs_pos.mpr hd0
  have hval := abs_sin_pi_mul (av + bv) k.toInt (by rw [← hd]; exact hk1)
  rw [← hd] at hval
  have hspos : 0 < Real.sin (|d| * Real.pi) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos hdpos Real.pi_pos) (by nlinarith [Real.pi_pos])
  obtain ⟨C, hC⟩ : ∃ C : ℝ,
      C = 4 * |av - (k.toInt : ℝ)| + 4 * (|d| + |av - (k.toInt : ℝ)|) := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  have hpow : Tendsto (fun w : ℕ => (1 / 2 : ℝ) ^ (w + 16)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
      (tendsto_add_atTop_nat 16)
  have hCu : Tendsto (fun w : ℕ => C * (1 / 2 : ℝ) ^ (w + 16)) atTop (𝓝 0) := by
    simpa using hpow.const_mul C
  have hlam : Tendsto (fun w : ℕ => 2 * (C * (1 / 2 : ℝ) ^ (w + 16)) / |d|) atTop (𝓝 0) := by
    simpa using (hCu.const_mul 2).div_const |d|
  have hE : Tendsto (fun w => sinEnv w + 32 * (2 * (C * (1 / 2 : ℝ) ^ (w + 16)) / |d|)
      + 304 * (1 / 2 : ℝ) ^ (w + 16)) atTop (𝓝 0) := by
    simpa using (tendsto_sinEnv.add (hlam.const_mul 32)).add (hpow.const_mul 304)
  refine ⟨_, hE, ?_⟩
  filter_upwards [hE.eventually (gt_mem_nhds hspos),
    tendsto_sinEnv.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_ge_atTop 64, hlam.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 64)),
    hCu.eventually (ge_mem_nhds (by positivity : 0 < |d| / 4))] with w h1 h2 h3 h4 h5
  have hW : 64 ≤ w + 16 := by omega
  have : NeZero (w + 16) := ⟨by omega⟩
  have hu8 : (1 / 2 : ℝ) ^ (w + 16) ≤ 1 / 8 := half_pow_le_eighth (by omega)
  have hu0 : (0 : ℝ) < (1 / 2 : ℝ) ^ (w + 16) := by positivity
  have hK0 : AEncl (Encl.exact (ofAzInt k)) (k.toInt : ℝ) 0 :=
    ⟨_, _, toVal_ofAzInt k, toVal_ofAzInt k, le_rfl, le_rfl, by simp⟩
  have hD1 := (AEncl.exact ha).sub (w := w + 16) hK0 (B := |av - (k.toInt : ℝ)|)
    (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hu8 (abs_nonneg (av - (k.toInt : ℝ)))
  have e : av - (k.toInt : ℝ) + bv = d := by rw [hd]; ring
  have hD2 := hD1.add (w := w + 16) (AEncl.exact hb) (B := |d| + |av - (k.toInt : ℝ)|) (by
    rw [e]
    linarith [abs_nonneg (av - (k.toInt : ℝ))])
  rw [e] at hD2
  have hD := hD2.mono (le_of_eq (by rw [hC]; ring :
    0 + 0 + 4 * |av - (k.toInt : ℝ)| * (1 / 2 : ℝ) ^ (w + 16) + 0
        + 4 * (|d| + |av - (k.toInt : ℝ)|) * (1 / 2 : ℝ) ^ (w + 16)
      = C * (1 / 2 : ℝ) ^ (w + 16)))
  obtain ⟨σ, A, hfrac, hAL⟩ := fracOfEncl_some hD (by linarith) hd0
  have hF : betaSumFrac a b (w + 16) = some (σ, k, A) := by
    unfold betaSumFrac
    dsimp only
    rw [← hk, hfrac]
    rfl
  have hAspec := betaSumFrac_spec ha hb hF
  obtain ⟨S', hS', hSw⟩ := gammaSinOfFrac_some' (σ := σ) (k := k) hW hAL
    (div_nonneg (by positivity) hdpos.le) h4 (abs_lt.mpr (abs_lt.mp hk1)) h3 h2 h1
  have hspec := gammaSinOfFrac_spec hAspec hW h3 hS'
  refine ⟨σ != k.isOdd, S', ?_, hspec, ?_⟩
  · show (betaSumFrac a b (w + 16)).bind _ = _
    rw [hF]
    exact hS'
  · rw [hval]
    exact hSw

/-- A float argument converges where `Γ` is finite and nonzero. -/
theorem argConv_float {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (h : 0 < xv ∨ (xv < 0 ∧ ∀ k : ℤ, xv ≠ k)) :
    ArgConv (fun _ => Encl.exact x) (gammaFloatFrac x) xv := by
  refine ⟨⟨0, fun V _ => (AEncl.exact hx).mono (by simp)⟩, ?_⟩
  rcases h with h | ⟨h, hint⟩
  · exact Or.inl h
  · refine Or.inr ⟨h, ?_⟩
    have e : (fun ws => (gammaFloatFrac x (ws + 16)).bind
        fun t => gammaSinOfFrac t.1 t.2.1 t.2.2 (ws + 16) ws)
        = fun w => gammaSinEncl x (w + 16) w := by
      funext w
      unfold gammaFloatFrac gammaSinEncl
      dsimp only
      cases gammaFracEncl x (gammaNearInt x) (w + 16) <;> rfl
    rw [e]
    exact gammaSinEncl_conv hx hint

/-- The sum of two floats converges as an argument. -/
theorem argConv_sum {a b : AzFloat} {av bv : ℝ} (ha : a.toVal = some (av : EReal))
    (hb : b.toVal = some (bv : EReal))
    (h : 0 < av + bv ∨ (av + bv < 0 ∧ ∀ k : ℤ, av + bv ≠ k)) :
    ArgConv (fun V => Encl.add V (Encl.exact a) (Encl.exact b)) (betaSumFrac a b)
      (av + bv) := by
  refine ⟨⟨4 * |av + bv|, fun V hV => ?_⟩, ?_⟩
  · have : NeZero V := ⟨by omega⟩
    exact ((AEncl.exact ha).add (w := V) (AEncl.exact hb) (B := |av + bv|) (by linarith)).mono
      (le_of_eq (by ring))
  · rcases h with h | ⟨h, hint⟩
    · exact Or.inl h
    · exact Or.inr ⟨h, betaSumSin_conv ha hb h hint⟩

/-- **The core of `B(a, b)` converges** for floats `a`, `b` where none of `a`, `b`, `a + b` is
`0` or a negative integer. -/
theorem betaCore_coreConv {a b : AzFloat} {av bv : ℝ} (ha : a.toVal = some (av : EReal))
    (hb : b.toVal = some (bv : EReal)) (hA : 0 < av ∨ (av < 0 ∧ ∀ k : ℤ, av ≠ k))
    (hB : 0 < bv ∨ (bv < 0 ∧ ∀ k : ℤ, bv ≠ k))
    (hS : 0 < av + bv ∨ (av + bv < 0 ∧ ∀ k : ℤ, av + bv ≠ k)) :
    CoreConv (betaCore a b) (Real.Gamma av * Real.Gamma bv / Real.Gamma (av + bv)) :=
  (betaEnclOf_coreConv (argConv_float ha hA) (argConv_float hb hB) (argConv_sum ha hb hS)
    (ea := expOf a) (eb := expOf b)
    (es := (if expOf a ≤ expOf b then expOf b else expOf a) + 1)
    (fun W σ k E hW hF => by
      have : NeZero W := ⟨by omega⟩
      exact gammaFloatFrac_spec ha hF)
    (fun W σ k E hW hF => by
      have : NeZero W := ⟨by omega⟩
      exact gammaFloatFrac_spec hb hF)
    (fun W σ k E hW hF => by
      have : NeZero W := ⟨by omega⟩
      exact betaSumFrac_spec ha hb hF)).congr fun _ => rfl

/-- **The bracket of `B(a, b)` converges.** -/
theorem betaApprox_bracketConv {a b : AzFloat} {av bv : ℝ} (ha : a.toVal = some (av : EReal))
    (hb : b.toVal = some (bv : EReal)) (hA : 0 < av ∨ (av < 0 ∧ ∀ k : ℤ, av ≠ k))
    (hB : 0 < bv ∨ (bv < 0 ∧ ∀ k : ℤ, bv ≠ k))
    (hS : 0 < av + bv ∨ (av + bv < 0 ∧ ∀ k : ℤ, av + bv ≠ k)) :
    BracketConv (fun w => gammaApproxOf (betaCore a b w) w)
      (Real.Gamma av * Real.Gamma bv / Real.Gamma (av + bv)) :=
  gammaApproxOf_bracketConv (betaCore_coreConv ha hb hA hB hS)

end Azurite.AzFloat
