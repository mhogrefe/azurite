/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.Pochhammer

/-!
# The bracket of Pochhammer's symbol converges

`pochCoreOf_coreConv`: at an argument whose enclosures have widths `O(2^(−V))`, and with the
right number `k` of negative factors, `pochCoreOf` answers at every large level, with a width
that tends to `0`.

The pieces are ratios `Γ(u)/Γ(v) = eᵗ q` (`lnGammaDiff`), where neither `t` (a difference of
Stirling values at shifted arguments) nor `q` (a quotient of rising products of the shifts)
is a fixed number: both move with the level.  So the widths are carried in relative form —
`lnGammaDiff_conv` gives `t` within an absolute width and `q` within a relative one, the
exponential turns the first into a relative width (`expOfBracketEps` is `exp v` times a small
number), the products add them up — and the value is put in at the very end, from the
specification `pochCoreOf_spec` (`LEncl.toA_of_isEnclPos`).

The exponent handed to `stirlingShifted` is the one of the upper end of the enclosure, which
may move with the level; it stays bounded (`expOf_abs_le_of_lencl`).
-/

namespace Azurite.AzFloat

open Filter Topology Finset

/-- The exponent of the upper end of a narrow enclosure of `u > 0` is bounded. -/
theorem expOf_abs_le_of_lencl {u : ℝ} (hu : 0 < u) :
    ∃ B : ℕ, ∀ (U : Encl) (lam : ℝ), LEncl U u lam → lam ≤ 1 / 2 →
      (expOf U.2).abs.toNat ≤ B := by
  obtain ⟨B₁, hB₁⟩ := pow_unbounded_of_one_lt (2 * u) (by norm_num : (1 : ℝ) < 2)
  obtain ⟨B₂, hB₂⟩ := exists_pow_lt_of_lt_one hu (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨max B₁ B₂, fun U lam hU hlam => ?_⟩
  obtain ⟨l, h, hl, hh, hl0, hlu, huh, hhl⟩ := hU
  have hexp : Real.exp lam ≤ 2 := by
    have h1 : Real.exp lam ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr hlam
    have h2 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    have h3 := Real.exp_one_lt_d9
    have h4 := Real.exp_pos (1 / 2)
    nlinarith
  have hh2 : h ≤ 2 * u := by nlinarith
  have hh0 : 0 < h := by linarith
  have hfin := isFinite_of_toVal_coe hh
  have hne : U.2 ≠ zero := by
    intro hz
    rw [hz, toVal_zero', Option.some.injEq, EReal.coe_eq_coe_iff] at hh
    linarith
  obtain ⟨b1, b2⟩ := abs_fval_bounds (isNormal_of_isFinite_ne_zero hfin hne)
  have hf : fval U.2 = h := by
    have := toVal_of_isFinite hfin
    rw [hh, Option.some.injEq, EReal.coe_eq_coe_iff] at this
    exact this.symm
  rw [hf, abs_of_pos hh0] at b1 b2
  have c1 : (expOf U.2).toInt - 1 < (B₁ : ℤ) := by
    have : (2 : ℝ) ^ ((expOf U.2).toInt - 1) < (2 : ℝ) ^ (B₁ : ℤ) := by
      rw [zpow_natCast]
      linarith
    exact (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp this
  have c2 : -(B₂ : ℤ) < (expOf U.2).toInt := by
    have : (2 : ℝ) ^ (-(B₂ : ℤ)) < (2 : ℝ) ^ (expOf U.2).toInt := by
      rw [zpow_neg, zpow_natCast, ← inv_pow, ← one_div]
      linarith
    exact (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp this
  rw [toNat_abs_eq_natAbs]
  omega

/-- A relative width around one value is an absolute width around any enclosed value. -/
theorem LEncl.toA_of_isEnclPos {a : Encl} {y p lam : ℝ} (h : LEncl a y lam)
    (hp : IsEnclPos a p) (h0 : 0 ≤ lam) (h1 : lam ≤ 1 / 2) : AEncl a p (2 * p * lam) := by
  obtain ⟨l, u, hl, hu, -, -, -, hw⟩ := (h.toA h0 h1)
  obtain ⟨l', u', hl', hu', q, a₁, b₁, c₁⟩ := h
  obtain ⟨l'', u'', hl'', hu'', q'', a₂, b₂⟩ := hp
  rw [hl', Option.some.injEq, EReal.coe_eq_coe_iff] at hl hl''
  rw [hu', Option.some.injEq, EReal.coe_eq_coe_iff] at hu hu''
  subst hl hu hl'' hu''
  have hexp : Real.exp lam ≤ 1 + 2 * lam := by
    rcases h0.eq_or_lt with h | h
    · rw [← h]; simp
    · have h2 := (Real.exp_bound_div_one_sub_of_interval' h (by linarith)).le
      have h3 : 1 / (1 - lam) ≤ 1 + 2 * lam := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith
      linarith
  have h4 : u' ≤ l' * (1 + 2 * lam) := c₁.trans (mul_le_mul_of_nonneg_left hexp q.le)
  have h5 : l' * lam ≤ p * lam := mul_le_mul_of_nonneg_right a₂ h0
  exact ⟨l', u', hl', hu', a₂, b₂, by linarith⟩

/-- The sum of two enclosures of widths `O(2^(−V))`. -/
theorem AEncl.add_level {a b : Encl} {x y Ka Kb : ℝ} {V : ℕ} [NeZero V]
    (ha : AEncl a x (Ka * (1 / 2 : ℝ) ^ V)) (hb : AEncl b y (Kb * (1 / 2 : ℝ) ^ V)) :
    AEncl (Encl.add V a b) (x + y)
      ((Ka + Kb + 4 * (|x + y| + |Ka| + |Kb|)) * (1 / 2 : ℝ) ^ V) := by
  have hu0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ V := by positivity
  have hu1 : (1 / 2 : ℝ) ^ V ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h1 : Ka * (1 / 2 : ℝ) ^ V ≤ |Ka| :=
    (mul_le_mul_of_nonneg_right (le_abs_self Ka) hu0).trans
      (mul_le_of_le_one_right (abs_nonneg Ka) hu1)
  have h2 : Kb * (1 / 2 : ℝ) ^ V ≤ |Kb| :=
    (mul_le_mul_of_nonneg_right (le_abs_self Kb) hu0).trans
      (mul_le_of_le_one_right (abs_nonneg Kb) hu1)
  exact (ha.add (w := V) hb (B := |x + y| + |Ka| + |Kb|) (by linarith)).mono
    (le_of_eq (by ring))

/-- The difference of two enclosures of widths `O(2^(−V))`. -/
theorem AEncl.sub_level {a b : Encl} {x y Ka Kb : ℝ} {V : ℕ} [NeZero V]
    (ha : AEncl a x (Ka * (1 / 2 : ℝ) ^ V)) (hb : AEncl b y (Kb * (1 / 2 : ℝ) ^ V)) :
    AEncl (Encl.sub V a b) (x - y)
      ((Ka + Kb + 4 * (|x - y| + |Ka| + |Kb|)) * (1 / 2 : ℝ) ^ V) := by
  have hu0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ V := by positivity
  have hu1 : (1 / 2 : ℝ) ^ V ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h1 : Ka * (1 / 2 : ℝ) ^ V ≤ |Ka| :=
    (mul_le_mul_of_nonneg_right (le_abs_self Ka) hu0).trans
      (mul_le_of_le_one_right (abs_nonneg Ka) hu1)
  have h2 : Kb * (1 / 2 : ℝ) ^ V ≤ |Kb| :=
    (mul_le_mul_of_nonneg_right (le_abs_self Kb) hu0).trans
      (mul_le_of_le_one_right (abs_nonneg Kb) hu1)
  exact (ha.sub (w := V) hb (B := |x - y| + |Ka| + |Kb|) (by linarith)).mono
    (le_of_eq (by ring))

theorem AEncl.exact_level {t : AzFloat} {tv : ℝ} (ht : t.toVal = some (tv : EReal)) (V : ℕ) :
    AEncl (Encl.exact t) tv (0 * (1 / 2 : ℝ) ^ V) := by
  rw [zero_mul]
  exact AEncl.exact ht

/-- The size of the Stirling value of an argument at level `W`. -/
noncomputable def pochG (x : ℝ) (W : ℕ) : ℝ :=
  |Real.log (Real.Gamma x)| + W * (|Real.log x| + (x + W))

theorem pb_pochG (x : ℝ) : PB (pochG x) :=
  (PB.const _).add (PB.natCast.mul ((PB.const _).add ((PB.const x).add PB.natCast)))

/-- **`lnGammaDiff` converges**: at arguments `u, v > 0` whose enclosures have widths
`O(2^(−V))`, it answers at every large level `W` with `t` in an absolute and `q` in a
relative width, both tending to `0`, and a polynomially bounded `|t|`. -/
theorem lnGammaDiff_conv {U Vv : ℕ → Encl} {u v : ℝ} (hu : 0 < u) (hv : 0 < v) {Ku Kv : ℝ}
    (hU : ∀ V, 64 ≤ V → AEncl (U V) u (Ku * (1 / 2 : ℝ) ^ V))
    (hVv : ∀ V, 64 ≤ V → AEncl (Vv V) v (Kv * (1 / 2 : ℝ) ^ V)) :
    ∃ E lam G : ℕ → ℝ, Tendsto E atTop (𝓝 0) ∧ Tendsto lam atTop (𝓝 0) ∧ PB G ∧
      ∀ᶠ W in atTop, ∃ (t q : Encl) (tv qv : ℝ),
        lnGammaDiff (U (W + 2 * lnGammaShiftExp W + 8 + 2 * W.log2))
          (Vv (W + 2 * lnGammaShiftExp W + 8 + 2 * W.log2)) (lnGammaShiftExp W)
          (W + 2 * lnGammaShiftExp W + 8 + 2 * W.log2)
          (lnGammaTerms W (lnGammaShiftExp W + 1))
          (AzNat.tangentNumbers (lnGammaTerms W (lnGammaShiftExp W + 1)))
          (powerOf2 (-(AzNat.ofNat (W + 16)).toAzInt)) = some (t, q) ∧
        AEncl t tv (E W) ∧ LEncl q qv (lam W) ∧ 0 ≤ lam W ∧ |tv| ≤ G W := by
  obtain ⟨Bu, hBu⟩ := expOf_abs_le_of_lencl hu
  obtain ⟨Bv, hBv⟩ := expOf_abs_le_of_lencl hv
  have hm : ∀ W, lnGammaTerms W (lnGammaShiftExp W + 1) ≤ W / 2 + 4 := fun W =>
    (lnGammaTerms_bounds W _).2.1
  have hmt : Tendsto (fun W => 2 * lnGammaTerms W (lnGammaShiftExp W + 1) - 1) atTop atTop := by
    rw [tendsto_atTop]
    intro K
    obtain ⟨W₀, hW₀⟩ := lnGammaTerms_tendsto 0 (K + 1)
    filter_upwards [eventually_ge_atTop (max W₀ 4)] with W hW
    have h4 : 4 ≤ W := le_trans (le_max_right _ _) hW
    have := hW₀ W (le_trans (le_max_left _ _) hW) (lnGammaShiftExp W + 1)
      (by have := shiftExp_le_log2 h4; omega)
    omega
  have hEu := tendsto_pcEps u hm hmt
  have hEv := tendsto_pcEps v hm hmt
  have hG : PB fun W => pochG u W + pochG v W := (pb_pochG u).add (pb_pochG v)
  have hpow : Tendsto (fun w : ℕ => (1 / 2 : ℝ) ^ w) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hE : Tendsto (fun W : ℕ => pcEps u (lnGammaTerms W (lnGammaShiftExp W + 1)) W
      + pcEps v (lnGammaTerms W (lnGammaShiftExp W + 1)) W
      + 4 * (pochG u W + pochG v W + 1) * (1 / 2 : ℝ) ^ W) atTop (𝓝 0) := by
    have := (hEu.add hEv).add ((hG.add (PB.const 1)).const_mul 4).tendsto
    rwa [add_zero, add_zero] at this
  have hlam : Tendsto (fun W : ℕ => 40 * (W : ℝ) * (1 / 2 : ℝ) ^ W + 6 * (1 / 2 : ℝ) ^ W) atTop
      (𝓝 0) := by
    have := (PB.natCast.const_mul 40).tendsto.add (hpow.const_mul 6)
    rwa [mul_zero, add_zero] at this
  refine ⟨_, _, _, hE, hlam, hG, ?_⟩
  filter_upwards [eventually_ge_atTop 64, eventually_ge_atTop (64 * (2 ^ Bu + 1)),
    eventually_ge_atTop (64 * (2 ^ Bv + 1)),
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (Ku / u),
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (Kv / v),
    hEu.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 3 / 8)),
    hEv.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 3 / 8))]
    with W hW hWu hWv hKu hKv hsu hsv
  obtain ⟨L, hL⟩ : ∃ L : ℕ, L = lnGammaShiftExp W := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = lnGammaTerms W (lnGammaShiftExp W + 1) := ⟨_, rfl⟩
  rw [← hM] at hsu hsv ⊢
  have hM4 : 4 ≤ M := by rw [hM]; exact (lnGammaTerms_bounds W _).1
  have hMle : M ≤ W / 2 + 4 := by rw [hM]; exact hm W
  have hVW : W + W.log2 ≤ W + 2 * lnGammaShiftExp W + 8 + 2 * W.log2 := by omega
  have hV64 : 64 ≤ W + 2 * lnGammaShiftExp W + 8 + 2 * W.log2 := by omega
  obtain ⟨V, hV⟩ : ∃ V : ℕ, V = W + 2 * lnGammaShiftExp W + 8 + 2 * W.log2 := ⟨_, rfl⟩
  rw [← hV] at hVW hV64 ⊢
  have : NeZero V := ⟨by omega⟩
  have hu8 : (1 / 2 : ℝ) ^ V ≤ 1 / 8 := half_pow_le_eighth (by omega)
  have hVu0 : (0 : ℝ) < (1 / 2 : ℝ) ^ V := by positivity
  have hWu0 : (0 : ℝ) < (1 / 2 : ℝ) ^ W := by positivity
  have hVleW : (1 / 2 : ℝ) ^ V ≤ (1 / 2 : ℝ) ^ W :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hW64 : (1 / 2 : ℝ) ^ W ≤ 1 / 2 ^ 64 := half_pow_le_of_64 hW
  have hhalf : 8 * (1 / 2 : ℝ) ^ W ≤ 1 / 2 := by
    have : (1 : ℝ) / 2 ^ 64 ≤ 1 / 16 := by norm_num
    linarith
  have hKu' : Ku ≤ W * u := (div_le_iff₀ hu).mp hKu
  have hKv' : Kv ≤ W * v := (div_le_iff₀ hv).mp hKv
  obtain ⟨lu, hLu, hlu0, hlu8⟩ := lencl_of_level hW hVW hu hKu'
    ((hU V hV64).mono (by nlinarith))
  obtain ⟨lv, hLv, hlv0, hlv8⟩ := lencl_of_level hW hVW hv hKv'
    ((hVv V hV64).mono (by nlinarith))
  have heu := hBu _ _ hLu (hlu8.trans hhalf)
  have hev := hBv _ _ hLv (hlv8.trans hhalf)
  have hwau : 64 * (2 ^ (expOf (U V).2).abs.toNat + 1) ≤ W := by
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) heu
    omega
  have hwav : 64 * (2 ^ (expOf (Vv V).2).abs.toNat + 1) ≤ W := by
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hev
    omega
  obtain ⟨gu, Pu, hSu, hPu, hgu, -⟩ :=
    stirlingShifted_width hu (expOf (U V).2) hW hwau hM4 hMle hsu hLu hlu0 hlu8
  obtain ⟨gv, Pv, hSv, hPv, hgv, -⟩ :=
    stirlingShifted_width hv (expOf (Vv V).2) hW hwav hM4 hMle hsv hLv hlv0 hlv8
  rw [← hV] at hSu hPu hSv hPv
  have hc1 : lt zero (U V).1 = true := by
    obtain ⟨l, h, hl, -, hl0, -⟩ := hLu
    exact (lt_eq_true_iff toVal_zero' hl).mpr hl0
  have hc2 : lt zero (Vv V).1 = true := by
    obtain ⟨l, h, hl, -, hl0, -⟩ := hLv
    exact (lt_eq_true_iff toVal_zero' hl).mpr hl0
  have hgu' : |gu| ≤ pochG u W := hgu
  have hgv' : |gv| ≤ pochG v W := hgv
  have hG0 : 0 ≤ pochG u W + pochG v W + 1 := by
    linarith [abs_nonneg gu, abs_nonneg gv]
  have habs : |gu - gv| ≤ pochG u W + pochG v W := (abs_sub gu gv).trans (by linarith)
  have hval : gu - 1 / 2 * Real.log (2 * Real.pi) - (gv - 1 / 2 * Real.log (2 * Real.pi))
      = gu - gv := by ring
  have hmul := mul_le_mul_of_nonneg_left hVleW (by linarith : 0 ≤ 4 * (pochG u W + pochG v W + 1))
  have heq : lnGammaDiff (U V) (Vv V) (lnGammaShiftExp W) V M (AzNat.tangentNumbers M)
      (powerOf2 (-(AzNat.ofNat (W + 16)).toAzInt))
      = some (Encl.sub V (stirlingShifted (U V) (expOf (U V).2) (lnGammaShiftExp W) V M
          (AzNat.tangentNumbers M) (powerOf2 (-(AzNat.ofNat (W + 16)).toAzInt))).1
          (stirlingShifted (Vv V) (expOf (Vv V).2) (lnGammaShiftExp W) V M
          (AzNat.tangentNumbers M) (powerOf2 (-(AzNat.ofNat (W + 16)).toAzInt))).1,
        Encl.div V (stirlingShifted (Vv V) (expOf (Vv V).2) (lnGammaShiftExp W) V M
          (AzNat.tangentNumbers M) (powerOf2 (-(AzNat.ofNat (W + 16)).toAzInt))).2
          (stirlingShifted (U V) (expOf (U V).2) (lnGammaShiftExp W) V M
          (AzNat.tangentNumbers M) (powerOf2 (-(AzNat.ofNat (W + 16)).toAzInt))).2) := by
    unfold lnGammaDiff
    rw [hc1, hc2]
    rfl
  refine ⟨_, _, gu - gv, Pv / Pu, heq, ?_, ?_, by positivity, habs⟩
  · have hsub := hSu.sub (w := V) hSv (B := pochG u W + pochG v W + 1) (by
      rw [hval]
      linarith)
    rw [hval] at hsub
    exact hsub.mono (by linarith)
  · exact (hPv.div (w := V) hu8 hPu).mono (by linarith)

/-- **A rising factorial piece converges**: the trivial one for `m = 0`, `lnGammaDiff`
otherwise. -/
theorem risingPiece_conv (m : ℕ) {U Vv : ℕ → Encl} {u v : ℝ} (hm : m ≠ 0 → 0 < u ∧ 0 < v)
    {Ku Kv : ℝ} (hU : ∀ V, 64 ≤ V → AEncl (U V) u (Ku * (1 / 2 : ℝ) ^ V))
    (hVv : ∀ V, 64 ≤ V → AEncl (Vv V) v (Kv * (1 / 2 : ℝ) ^ V)) :
    ∃ E lam G : ℕ → ℝ, Tendsto E atTop (𝓝 0) ∧ Tendsto lam atTop (𝓝 0) ∧ PB G ∧
      ∀ᶠ W in atTop, ∃ (t q : Encl) (tv qv : ℝ),
        (if m = 0 then some (Encl.exact zero, Encl.exact one)
          else lnGammaDiff (U (W + 2 * lnGammaShiftExp W + 8 + 2 * W.log2))
            (Vv (W + 2 * lnGammaShiftExp W + 8 + 2 * W.log2)) (lnGammaShiftExp W)
            (W + 2 * lnGammaShiftExp W + 8 + 2 * W.log2)
            (lnGammaTerms W (lnGammaShiftExp W + 1))
            (AzNat.tangentNumbers (lnGammaTerms W (lnGammaShiftExp W + 1)))
            (powerOf2 (-(AzNat.ofNat (W + 16)).toAzInt))) = some (t, q) ∧
        AEncl t tv (E W) ∧ LEncl q qv (lam W) ∧ 0 ≤ lam W ∧ |tv| ≤ G W := by
  by_cases h0 : m = 0
  · refine ⟨fun _ => 0, fun _ => 0, fun _ => 0, tendsto_const_nhds, tendsto_const_nhds,
      PB.const 0, Eventually.of_forall fun W => ?_⟩
    exact ⟨_, _, 0, 1, by rw [ite_eq_left h0], AEncl.exact toVal_zero',
      LEncl.exact toVal_one' one_pos, le_rfl, by simp⟩
  · obtain ⟨E, lam, G, hE, hlam, hG, hev⟩ := lnGammaDiff_conv (hm h0).1 (hm h0).2 hU hVv
    refine ⟨E, lam, G, hE, hlam, hG, hev.mono fun W hW => ?_⟩
    rw [ite_eq_right h0]
    exact hW

/-- **The core of Pochhammer's symbol converges**: at an argument whose enclosures have
widths `O(2^(−V))`, split at a `k ≤ n` that leaves both rising factorials a positive first
factor. -/
theorem pochCoreOf_coreConv {X : ℕ → Encl} {xv K : ℝ}
    (hX : ∀ V, 64 ≤ V → AEncl (X V) xv (K * (1 / 2 : ℝ) ^ V)) {k n : ℕ} (hk : k ≤ n)
    (hk1 : k ≠ 0 → 0 < 1 - xv - k) (hk2 : n - k ≠ 0 → 0 < xv + k) (bits : ℕ) :
    CoreConv (pochCoreOf X k n bits) (∏ j ∈ range n, (xv + j)) := by
  have hY : ∀ V, 64 ≤ V → AEncl (Encl.sub V (Encl.exact one) (X V)) (1 - xv)
      ((0 + K + 4 * (|1 - xv| + |(0 : ℝ)| + |K|)) * (1 / 2 : ℝ) ^ V) := fun V hV => by
    have : NeZero V := ⟨by omega⟩
    exact (AEncl.exact_level toVal_one' V).sub_level (hX V hV)
  have hYk : ∀ V, 64 ≤ V → AEncl (Encl.sub V (Encl.sub V (Encl.exact one) (X V)) (Encl.nat k))
      (1 - xv - k) _ := fun V hV => by
    have : NeZero V := ⟨by omega⟩
    exact (hY V hV).sub_level (AEncl.exact_level (toVal_ofAzNat_ofNat k) V)
  have hXn : ∀ V, 64 ≤ V → AEncl (Encl.add V (X V) (Encl.nat n)) (xv + n) _ := fun V hV => by
    have : NeZero V := ⟨by omega⟩
    exact (hX V hV).add_level (AEncl.exact_level (toVal_ofAzNat_ofNat n) V)
  have hXk : ∀ V, 64 ≤ V → AEncl (Encl.add V (X V) (Encl.nat k)) (xv + k) _ := fun V hV => by
    have : NeZero V := ⟨by omega⟩
    exact (hX V hV).add_level (AEncl.exact_level (toVal_ofAzNat_ofNat k) V)
  have hkR : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hnk : (k : ℝ) ≤ n := by exact_mod_cast hk
  obtain ⟨E₁, l₁, G₁, hE₁, hl₁, hG₁, hev₁⟩ := risingPiece_conv k
    (fun h => ⟨by linarith [hk1 h], hk1 h⟩) hY hYk
  obtain ⟨E₂, l₂, G₂, hE₂, hl₂, hG₂, hev₂⟩ := risingPiece_conv (n - k)
    (fun h => ⟨by linarith [hk2 h], hk2 h⟩) hXn hXk
  have hs := tendsto_add_atTop_nat bits
  have hpow : Tendsto (fun w : ℕ => (1 / 2 : ℝ) ^ w) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨εW, hεWdef⟩ : ∃ εW : ℕ → ℝ, εW = fun W =>
      E₁ W + E₂ W + 4 * (G₁ W + G₂ W + 1) * (1 / 2 : ℝ) ^ W := ⟨_, rfl⟩
  have hεW : Tendsto εW atTop (𝓝 0) := by
    have := (hE₁.add hE₂).add (((hG₁.add hG₂).add (PB.const 1)).const_mul 4).tendsto
    rw [add_zero, add_zero] at this
    rw [hεWdef]
    exact this
  have hε : Tendsto (fun w : ℕ => εW (w + bits)) atTop (𝓝 0) := hεW.comp hs
  obtain ⟨η, hηdef⟩ : ∃ η : ℕ → ℝ, η = fun w : ℕ =>
      80 * ((w : ℝ) + 9) * (1 / 2 : ℝ) ^ w + 24 * εW (w + bits) + (1 / 2 : ℝ) ^ w / 4 :=
    ⟨_, rfl⟩
  have hη : Tendsto η atTop (𝓝 0) := by
    have := (((PB.natCast.add (PB.const 9)).const_mul 80).tendsto.add (hε.const_mul 24)).add
      (hpow.div_const 4)
    rw [mul_zero, add_zero, zero_div, add_zero] at this
    rw [hηdef]
    exact this
  obtain ⟨lamT, hlamTdef⟩ : ∃ lamT : ℕ → ℝ, lamT = fun w : ℕ =>
      2 * η w + l₁ (w + bits) + l₂ (w + bits) + 12 * (1 / 2 : ℝ) ^ w := ⟨_, rfl⟩
  have hlamT : Tendsto lamT atTop (𝓝 0) := by
    have := (((hη.const_mul 2).add (hl₁.comp hs)).add (hl₂.comp hs)).add (hpow.const_mul 12)
    rw [mul_zero, add_zero, add_zero, mul_zero, add_zero] at this
    rw [hlamTdef]
    exact this
  have hfin : Tendsto (fun w => 2 * |∏ j ∈ range n, (xv + j)| * lamT w) atTop (𝓝 0) := by
    have := hlamT.const_mul (2 * |∏ j ∈ range n, (xv + j)|)
    rwa [mul_zero] at this
  refine ⟨_, hfin, ?_⟩
  filter_upwards [hs.eventually hev₁, hs.eventually hev₂, eventually_ge_atTop 64,
    hε.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    hη.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
    hlamT.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    (hE₁.comp hs).eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    (hE₂.comp hs).eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
    with w h1 h2 hw e1 e2 e3 e4 e5
  obtain ⟨t₁, q₁, tv₁, qv₁, hp₁, hA₁, hL₁, hl₁0, hg₁⟩ := h1
  obtain ⟨t₂, q₂, tv₂, qv₂, hp₂, hA₂, hL₂, hl₂0, hg₂⟩ := h2
  obtain ⟨V, hV⟩ : ∃ V : ℕ,
      V = w + bits + 2 * lnGammaShiftExp (w + bits) + 8 + 2 * (w + bits).log2 := ⟨_, rfl⟩
  have hVw : w + bits ≤ V := by omega
  have : NeZero V := ⟨by omega⟩
  have hu8 : (1 / 2 : ℝ) ^ V ≤ 1 / 8 := half_pow_le_eighth (by omega)
  have hVleW : (1 / 2 : ℝ) ^ V ≤ (1 / 2 : ℝ) ^ (w + bits) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hVw
  have hVlew : (1 / 2 : ℝ) ^ V ≤ (1 / 2 : ℝ) ^ w :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hVu0 : (0 : ℝ) < (1 / 2 : ℝ) ^ V := by positivity
  have e4' : E₁ (w + bits) ≤ 1 / 2 := e4
  have e5' : E₂ (w + bits) ≤ 1 / 2 := e5
  have hG0 : 0 ≤ G₁ (w + bits) + G₂ (w + bits) + 1 := by
    linarith [abs_nonneg tv₁, abs_nonneg tv₂]
  have hmul := mul_le_mul_of_nonneg_left hVleW
    (by linarith : 0 ≤ 4 * (G₁ (w + bits) + G₂ (w + bits) + 1))
  have hsum : AEncl (Encl.add V t₁ t₂) (tv₁ + tv₂) (εW (w + bits)) := by
    refine (hA₁.add (w := V) hA₂ (B := G₁ (w + bits) + G₂ (w + bits) + 1) ?_).mono ?_
    · linarith [abs_add_le tv₁ tv₂]
    · rw [hεWdef]
      linarith
  have hηw : expOfBracketEps (tv₁ + tv₂) (εW (w + bits)) w = Real.exp (tv₁ + tv₂) * η w := by
    rw [hηdef]
    unfold expOfBracketEps expEps
    ring
  have hexp0 := Real.exp_pos (tv₁ + tv₂)
  obtain ⟨g, hg, -, hAg⟩ := gammaExpEncl_width (neg := false) hsum e1 hw (by
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hηw]
    nlinarith)
  simp only [Bool.false_eq_true, ↓reduceIte] at hAg
  rw [hηw] at hAg
  have hLg : LEncl g (Real.exp (tv₁ + tv₂)) (2 * η w) := by
    refine (LEncl.ofA hAg (by nlinarith) hexp0).mono (le_of_eq ?_)
    field_simp
  have hLr := (hLg.mul (w := V) hu8 hL₁).mul hu8 hL₂
  have heq : pochCoreOf X k n bits w
      = some (k % 2 == 1, Encl.mul V (Encl.mul V g q₁) q₂) := by
    unfold pochCoreOf
    dsimp only
    rw [← hV]
    rw [← hV] at hp₁ hp₂
    rw [hp₁, hp₂]
    dsimp only
    rw [hg, Option.map_some]
  have hpos := pochCoreOf_spec (fun V hV => (hX V hV).isEncl) hk hw heq
  have hη0 : 0 ≤ η w := by
    rw [hηdef]
    have : 0 ≤ εW (w + bits) := by
      obtain ⟨l, u, -, -, c1, c2, c3⟩ := hsum
      linarith
    positivity
  have hlam_le : 2 * η w + l₁ (w + bits) + 6 * (1 / 2 : ℝ) ^ V + l₂ (w + bits)
      + 6 * (1 / 2 : ℝ) ^ V ≤ lamT w := by
    rw [hlamTdef]
    linarith
  have hA := (hLr.mono hlam_le).toA_of_isEnclPos hpos (by
    rw [hlamTdef]
    positivity) e3
  refine ⟨_, _, heq, hpos, hA.mono ?_⟩
  have hp0 : 0 < (if (k % 2 == 1) = true then (-1 : ℝ) else 1) * ∏ j ∈ range n, (xv + j) := by
    obtain ⟨l, u, -, -, c1, c2, -⟩ := hpos
    linarith
  have hple : (if (k % 2 == 1) = true then (-1 : ℝ) else 1) * ∏ j ∈ range n, (xv + j)
      ≤ |∏ j ∈ range n, (xv + j)| := by
    split_ifs
    · rw [neg_one_mul]
      exact neg_le_abs _
    · rw [one_mul]
      exact le_abs_self _
  have hlamT0 : 0 ≤ lamT w := by
    rw [hlamTdef]
    positivity
  nlinarith [mul_le_mul_of_nonneg_right hple hlamT0]

/-! ### The specification for floats -/

/-- **The split of `(x)ₙ` is right**: off the zeros, both rising factorials have a positive
first factor. -/
theorem pochSplit_facts {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) {n : ℕ}
    (hz : pochHasZero x n = false) :
    (pochSplit x n ≠ 0 → 0 < 1 - xv - (pochSplit x n : ℕ)) ∧
      (n - pochSplit x n ≠ 0 → 0 < xv + (pochSplit x n : ℕ)) := by
  have hnv : (-(ofAzNat (AzNat.ofNat n))).toVal = some ((-(n : ℝ) : ℝ) : EReal) := by
    rw [toVal_neg, toVal_ofAzNat_ofNat, Option.map_some, EReal.coe_neg]
  have hz' : ¬ ((∃ k : ℤ, xv = k) ∧ xv ≤ 0 ∧ -(n : ℝ) < xv) := by
    rintro ⟨h1, h2, h3⟩
    have : pochHasZero x n = true := by
      unfold pochHasZero
      rw [Bool.and_eq_true, Bool.and_eq_true]
      exact ⟨⟨(isInteger_iff_of_toVal hx).mpr h1, (le_eq_true_iff hx toVal_zero').mpr h2⟩,
        (lt_eq_true_iff hnv hx).mpr h3⟩
    rw [hz] at this
    cases this
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  unfold pochSplit
  by_cases c1 : le zero x = true
  · rw [ite_eq_left c1]
    have h0 : 0 ≤ xv := (le_eq_true_iff toVal_zero' hx).mp c1
    refine ⟨fun h => absurd rfl h, fun h => ?_⟩
    have hn : n ≠ 0 := fun h' => h (by omega)
    have hn1 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    rcases h0.eq_or_lt with h' | h'
    · exact absurd ⟨⟨0, by rw [← h']; simp⟩, h'.symm.le, by linarith⟩ hz'
    · rw [Nat.cast_zero, add_zero]
      exact h'
  rw [ite_eq_right c1]
  have hneg : xv < 0 := by
    by_contra h
    exact c1 ((le_eq_true_iff toVal_zero' hx).mpr (not_lt.mp h))
  by_cases c2 : le x (-(ofAzNat (AzNat.ofNat n))) = true
  · rw [ite_eq_left c2]
    have h2 : xv ≤ -(n : ℝ) := (le_eq_true_iff hx hnv).mp c2
    exact ⟨fun _ => by linarith, fun h => absurd (Nat.sub_self n) h⟩
  rw [ite_eq_right c2]
  have hgt : -(n : ℝ) < xv := by
    by_contra h
    exact c2 ((le_eq_true_iff hx hnv).mpr (not_lt.mp h))
  have hni : ¬ ∃ k : ℤ, xv = k := fun h => hz' ⟨h, hneg.le, hgt⟩
  have hint : isInteger x = false := by
    rcases Bool.eq_false_or_eq_true (isInteger x) with h | h
    · exact absurd ((isInteger_iff_of_toVal hx).mp h) hni
    · exact h
  rw [hint, toNat_abs_eq_natAbs]
  obtain ⟨t, ht⟩ : ∃ t : ℤ, t = (truncToAzInt x).toInt := ⟨_, rfl⟩
  obtain ⟨ht1, ht2⟩ := truncToAzInt_spec hx
  rw [← ht] at ht1 ht2 ⊢
  have ht1' := abs_lt.mp ht1
  have htle : (t : ℝ) < 1 := by linarith
  have ht0 : t ≤ 0 := by
    have : t < 1 := by exact_mod_cast htle
    omega
  have ht0' : (t : ℝ) ≤ 0 := by exact_mod_cast ht0
  rw [abs_of_nonpos ht0', abs_of_neg hneg] at ht2
  have hxt : xv < t := lt_of_le_of_ne (by linarith) fun h => hni ⟨t, h⟩
  have hm : ((t.natAbs : ℕ) : ℝ) = -(t : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonpos ht0']
  simp only [Bool.false_eq_true, ↓reduceIte]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = min n (t.natAbs + 1) := ⟨_, rfl⟩
  rw [← hk]
  have hk1 : (k : ℝ) ≤ (t.natAbs : ℝ) + 1 := by
    have : k ≤ t.natAbs + 1 := by omega
    exact_mod_cast this
  constructor
  · intro _
    linarith
  · intro h
    have hk2 : k = t.natAbs + 1 := by omega
    rw [hk2]
    push_cast
    linarith

/-- **The core of `(x)ₙ` converges** off the zeros. -/
theorem pochCore_coreConv {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    {n : ℕ} (hz : pochHasZero x n = false) :
    CoreConv (pochCore x n) (∏ j ∈ range n, (xv + j)) := by
  obtain ⟨h1, h2⟩ := pochSplit_facts hx hz
  exact pochCoreOf_coreConv (X := fun _ => Encl.exact x) (fun V _ => AEncl.exact_level hx V)
    (pochSplit_le x n) h1 h2 _

/-- **The bracket of `(x)ₙ` converges** off the zeros. -/
theorem pochApprox_bracketConv {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    {n : ℕ} (hz : pochHasZero x n = false) :
    BracketConv (pochApprox x n) (∏ j ∈ range n, (xv + j)) :=
  gammaApproxOf_bracketConv (pochCore_coreConv hx hz)

theorem isDyadic_one : IsDyadic 1 := by simpa using isDyadic_natCast 1

/-- **The specification of Pochhammer's symbol** (`ZivSpec`): sound at every fuel; complete
in the limit of the fuel wherever the value is no rounding boundary; correct at every fuel
for `n = 0`, at the arguments that are not finite, and where a factor vanishes.  (The value
at a float is always dyadic, so there are no arguments known to be free of boundaries.) -/
theorem pochhammerPrecRoundFuel_zivSpec :
    ZivSpec (fun xn : AzFloat × ℕ => xn.1.toVal.bind (Spec.pochhammer xn.2))
      (fun fuel xn p mode => pochhammerPrecRoundFuel fuel xn.1 xn.2 p mode)
      {xn | xn.2 = 0 ∨ xn.1.isFinite = false ∨ pochHasZero xn.1 xn.2 = true} ∅ where
  sound := fun fuel xn p _ mode => pochhammerPrecRoundFuel_eq_or fuel xn.1 xn.2 p mode
  complete := fun xn p _ mode hB => by
    by_cases hgen : ∃ xv : ℝ, xn.1.toVal = some (xv : EReal) ∧ xn.2 ≠ 0 ∧
        pochHasZero xn.1 xn.2 = false
    · obtain ⟨xv, hx, hn, hz⟩ := hgen
      have hval : xn.1.toVal.bind (Spec.pochhammer xn.2)
          = some ((∏ j ∈ range xn.2, (xv + j) : ℝ) : EReal) := by
        rw [hx, Option.bind_some, Spec.pochhammer_coe hn]
      have hB' := hB _ hval
      obtain ⟨F, hF⟩ := zivLoop_eventually_eq p mode (pochApprox xn.1 xn.2)
        (pochApprox_bracketConv hx hz) (ne_zero_of_not_mem_floatSet hB') hB'
        (max 64 (p + 32)) (Nat.lt_of_lt_of_le (by norm_num) (le_max_left 64 _))
        (fun w hw => (gammaApproxOf_valid_or_none
          (fun _ _ hc => pochCore_spec hx (le_trans (le_max_left _ _) hw) hc) w p mode).imp_left
            fun ⟨lv, hv', h1, h2, h3, h4, _⟩ => ⟨lv, hv', h1, h2, h3, h4⟩)
      refine ⟨F, fun fuel hfuel => ?_⟩
      rcases pochhammerPrecRoundFuel_eq_or_loop fuel xn.1 xn.2 p mode with h | ⟨-, -, -, -, h⟩
      · exact h
      · show pochhammerPrecRoundFuel fuel xn.1 xn.2 p mode = _
        rw [h, hval]
        exact hF fuel hfuel
    · refine ⟨0, fun fuel _ => ?_⟩
      rcases pochhammerPrecRoundFuel_eq_or_loop fuel xn.1 xn.2 p mode with
        h | ⟨xv, hx, hn, hz, -⟩
      · exact h
      · exact absurd ⟨xv, hx, hn, hz⟩ hgen
  dyadic := fun xn hxn v hv => by
    by_cases hn : xn.2 = 0
    · cases hx : xn.1.toVal with
      | none => rw [hx] at hv; exact absurd hv (by simp)
      | some a =>
        rw [hx, Option.bind_some, hn, Spec.pochhammer_zero, Option.some.injEq] at hv
        have : v = 1 := by exact_mod_cast hv.symm
        rw [this]
        exact isDyadic_one
    · by_cases hfin : xn.1.isFinite = true
      · have hxv := toVal_of_isFinite hfin
        rw [hxv, Option.bind_some, Spec.pochhammer_coe hn, Option.some.injEq,
          EReal.coe_eq_coe_iff] at hv
        rcases hxn with h | h | h
        · exact absurd h hn
        · rw [hfin] at h
          cases h
        · rw [pochHasZero_spec hxv h] at hv
          rw [← hv]
          exact isDyadic_zero
      · exfalso
        cases hxx : xn.1 with
        | nan => rw [hxx] at hv; simp at hv
        | infinity s =>
          rw [hxx, toVal_infinity, Option.bind_some] at hv
          cases s <;> by_cases he : xn.2 % 2 = 0 <;> simp [Spec.pochhammer, hn, he] at hv
        | zero => exact hfin (by rw [hxx]; rfl)
        | finite s e q m hv' => exact hfin (by rw [hxx]; rfl)
  nondyadic := fun xn h => absurd h (Set.notMem_empty _)
  correct := fun xn hxn fuel p _ mode => by
    rcases pochhammerPrecRoundFuel_eq_or_loop fuel xn.1 xn.2 p mode with h | ⟨xv, hx, hn, hz, -⟩
    · exact h
    · exfalso
      rcases hxn with (h | h | h) | h
      · exact hn h
      · rw [isFinite_of_toVal_coe hx] at h
        cases h
      · rw [hz] at h
        cases h
      · exact absurd h (Set.notMem_empty _)

/-! ### Exact, or a convergent loop

The functions of the generalized Pochhammer family branch into several loops.  `ZivCases`
is what every branch delivers — the exact value at every fuel, or one Ziv loop on a
convergent valid bracket of a nonzero value — and what a `ZivSpec` follows from
(`ZivSpec.of_zivCases`). -/

/-- `g fuel` is the correct rounding of `o` at every fuel, or it is a Ziv loop with that fuel
on a convergent, valid bracket of the nonzero real `o`. -/
def ZivCases (g : ℕ → AzFloat × Ordering) (o : Option EReal) (p : ℕ) [NeZero p]
    (mode : RoundingMode) : Prop :=
  (∀ fuel, g fuel = roundVal p mode o) ∨
    ∃ (approx : ℕ → Roundable × Roundable) (v : ℝ) (w₀ : ℕ), 0 < w₀ ∧ o = some (v : EReal) ∧
      v ≠ 0 ∧ BracketConv approx v ∧
      (∀ w, w₀ ≤ w → (∃ lv hv : ℝ, Rounds (approx w).1 lv ∧ Rounds (approx w).2 hv ∧
        lv ≤ v ∧ v ≤ hv ∧ (lv = v → hv = v)) ∨
        roundingPossible (approx w).1 (approx w).2 p mode = none) ∧
      ∀ fuel, g fuel = zivLoop approx p mode fuel w₀

theorem ZivCases.congr {g g' : ℕ → AzFloat × Ordering} {o : Option EReal} {p : ℕ} [NeZero p]
    {mode : RoundingMode} (h : ZivCases g o p mode) (hg : ∀ fuel, g' fuel = g fuel) :
    ZivCases g' o p mode := by
  rcases h with h | ⟨approx, v, w₀, h1, h2, h3, h4, h5, h6⟩
  · exact Or.inl fun fuel => (hg fuel).trans (h fuel)
  · exact Or.inr ⟨approx, v, w₀, h1, h2, h3, h4, h5, fun fuel => (hg fuel).trans (h6 fuel)⟩

theorem ZivCases.sound {g : ℕ → AzFloat × Ordering} {o : Option EReal} {p : ℕ} [NeZero p]
    {mode : RoundingMode} (h : ZivCases g o p mode) (fuel : ℕ) :
    g fuel = roundVal p mode o ∨ g fuel = (nan, .eq) := by
  rcases h with h | ⟨approx, v, w₀, -, h2, -, -, h5, h6⟩
  · exact Or.inl (h fuel)
  · rw [h6 fuel, h2]
    rcases eq_or_ne (zivLoop approx p mode fuel w₀) (nan, .eq) with hz | hz
    · exact Or.inr hz
    · exact Or.inl (zivLoop_eq_of_ne_nan_or_none p mode approx v w₀ h5 fuel w₀ le_rfl hz)

theorem ZivCases.complete {g : ℕ → AzFloat × Ordering} {o : Option EReal} {p : ℕ} [NeZero p]
    {mode : RoundingMode} (h : ZivCases g o p mode)
    (hB : ∀ v : ℝ, o = some (v : EReal) → ((v : ℝ) : EReal) ∉ floatSet (p + 1)) :
    ∃ F : ℕ, ∀ fuel, F ≤ fuel → g fuel = roundVal p mode o := by
  rcases h with h | ⟨approx, v, w₀, h1, h2, h3, h4, h5, h6⟩
  · exact ⟨0, fun fuel _ => h fuel⟩
  · obtain ⟨F, hF⟩ := zivLoop_eventually_eq p mode approx h4 h3 (hB v h2) w₀ h1
      (fun w hw => (h5 w hw).imp_left
        fun ⟨lv, hv', a1, a2, a3, a4, _⟩ => ⟨lv, hv', a1, a2, a3, a4⟩)
    exact ⟨F, fun fuel hfuel => by rw [h6 fuel, h2]; exact hF fuel hfuel⟩

/-- **A function that is exact or a convergent loop at every argument has a specification**:
sound, complete, and correct at every fuel where the value is undefined or `0`. -/
theorem ZivSpec.of_zivCases {α : Type*} {val : α → Option EReal}
    {f : ℕ → α → ℕ → RoundingMode → AzFloat × Ordering}
    (h : ∀ (x : α) (p : ℕ) [NeZero p] (mode : RoundingMode),
      ZivCases (fun fuel => f fuel x p mode) (val x) p mode) :
    ZivSpec val f {x | ∀ v : ℝ, val x = some (v : EReal) → v = 0} ∅ where
  sound := fun fuel x p _ mode => (h x p mode).sound fuel
  complete := fun x p _ mode hB => (h x p mode).complete hB
  dyadic := fun x hx v hv => by
    rw [hx v hv]
    exact isDyadic_zero
  nondyadic := fun x hx => absurd hx (Set.notMem_empty _)
  correct := fun x hx fuel p _ mode => by
    rcases h x p mode with h' | ⟨approx, v, w₀, -, h2, h3, -, -, -⟩
    · exact h' fuel
    · rcases hx with hx | hx
      · exact absurd (hx v h2) h3
      · exact absurd hx (Set.notMem_empty _)

/-- The value of a convergent core is not `0`. -/
theorem CoreConv.ne_zero {c : ℕ → Option (Bool × Encl)} {v : ℝ} (h : CoreConv c v) : v ≠ 0 := by
  obtain ⟨E, -, hev⟩ := h
  obtain ⟨w, neg, b, -, ⟨l, u, -, -, h0, h1, -⟩, -⟩ := hev.exists
  rintro rfl
  rw [mul_zero] at h1
  linarith

/-- **A loop on a convergent core** is a case of `ZivCases`. -/
theorem ZivCases.of_core {c : ℕ → Option (Bool × Encl)} {v : ℝ} (hc : CoreConv c v)
    (hspec : ∀ w, 64 ≤ w → ∀ neg b, c w = some (neg, b) →
      IsEnclPos b ((if neg then -1 else 1) * v)) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    ZivCases (fun fuel => zivLoop (fun w => gammaApproxOf (c w) w) p mode fuel
      (max 64 (p + 32))) (some (v : EReal)) p mode :=
  Or.inr ⟨_, v, _, Nat.lt_of_lt_of_le (by norm_num) (le_max_left 64 _), rfl, hc.ne_zero,
    gammaApproxOf_bracketConv hc,
    fun w hw => gammaApproxOf_valid_or_none (hspec w (le_trans (le_max_left _ _) hw)) w p mode,
    fun _ => rfl⟩

/-- **The reciprocal of a convergent core converges.** -/
theorem CoreConv.recip {c : ℕ → Option (Bool × Encl)} {v : ℝ} (h : CoreConv c v) :
    CoreConv (fun w => (c w).map fun r => (r.1, Encl.div (w + 32) (Encl.exact one) r.2))
      v⁻¹ := by
  have hv0 := h.ne_zero
  obtain ⟨E, hE, hev⟩ := h
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = |v| := ⟨_, rfl⟩
  have hA0 : 0 < A := by rw [hA]; exact abs_pos.mpr hv0
  have hpow : Tendsto (fun w : ℕ => (1 / 2 : ℝ) ^ (w + 32)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
      (tendsto_add_atTop_nat 32)
  have hlam : Tendsto (fun w : ℕ => 2 * E w / A + 6 * (1 / 2 : ℝ) ^ (w + 32)) atTop (𝓝 0) := by
    have := ((hE.const_mul 2).div_const A).add (hpow.const_mul 6)
    rwa [mul_zero, zero_div, mul_zero, add_zero] at this
  have hE' : Tendsto (fun w : ℕ => 2 * (1 / A) * (2 * E w / A + 6 * (1 / 2 : ℝ) ^ (w + 32)))
      atTop (𝓝 0) := by
    have := hlam.const_mul (2 * (1 / A))
    rwa [mul_zero] at this
  refine ⟨_, hE', ?_⟩
  filter_upwards [hev, hE.eventually (ge_mem_nhds (half_pos hA0)),
    hlam.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with w h1 h2 h3
  obtain ⟨neg, b, hc, hb, hAb⟩ := h1
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = (if neg then (-1 : ℝ) else 1) * v := ⟨_, rfl⟩
  rw [← hq] at hb hAb
  have hq0 : 0 < q := by
    obtain ⟨l, u, -, -, a1, a2, -⟩ := hb
    linarith
  have hqA : q = A := by
    rw [hA, hq]
    cases neg
    · simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at hq ⊢
      rw [abs_of_pos (hq ▸ hq0)]
    · simp only [↓reduceIte, neg_one_mul] at hq ⊢
      rw [abs_of_neg (by linarith [hq ▸ hq0])]
  have hval : (if neg then (-1 : ℝ) else 1) * v⁻¹ = 1 / q := by
    rw [hq]
    cases neg
    · simp
    · simp only [↓reduceIte, neg_one_mul, one_div, inv_neg]
  have hE0 : 0 ≤ E w := by
    obtain ⟨l, u, -, -, a1, a2, a3⟩ := hAb
    linarith
  have : NeZero (w + 32) := ⟨by omega⟩
  have hu8 : (1 / 2 : ℝ) ^ (w + 32) ≤ 1 / 8 := half_pow_le_eighth (by omega)
  have hL := LEncl.ofA hAb (by rw [hqA]; linarith) hq0
  have hd := ((LEncl.exact toVal_one' one_pos).div (w := w + 32) hu8 hL).mono
    (le_of_eq (by rw [zero_add, hqA] :
      0 + 2 * E w / q + 6 * (1 / 2 : ℝ) ^ (w + 32) = 2 * E w / A + 6 * (1 / 2 : ℝ) ^ (w + 32)))
  have hA' := (hd.toA (by positivity) h3).toA
  refine ⟨neg, _, by rw [hc]; rfl, ?_, ?_⟩
  · rw [hval]
    exact hd.isEnclPos
  · rw [hval]
    rw [hqA] at hA' ⊢
    exact hA'

/-- **`pochRealFuel` is exact or a convergent loop.** -/
theorem pochRealFuel_zivCases {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (n p : ℕ) [NeZero p] (mode : RoundingMode) :
    ZivCases (fun fuel => pochRealFuel fuel x n p mode)
      (some ((∏ j ∈ range n, (xv + j) : ℝ) : EReal)) p mode := by
  by_cases hz : pochHasZero x n = true
  · refine Or.inl fun fuel => ?_
    show pochRealFuel fuel x n p mode = _
    unfold pochRealFuel
    rw [ite_eq_left hz, pochHasZero_spec hx hz, EReal.coe_zero, roundVal_zero]
  cases hr : pochExact? x n p mode with
  | some r =>
    refine Or.inl fun fuel => ?_
    show pochRealFuel fuel x n p mode = _
    unfold pochRealFuel
    rw [ite_eq_right hz, ite_eq_right (NeZero.ne p), hr]
    exact pochExact?_eq hx p mode hr
  | none =>
    refine (ZivCases.of_core (pochCore_coreConv hx (by simpa using hz))
      (fun w hw neg b hc => pochCore_spec hx hw hc) p mode).congr fun fuel => ?_
    show pochRealFuel fuel x n p mode = _
    unfold pochRealFuel
    rw [ite_eq_right hz, ite_eq_right (NeZero.ne p), hr]
    rfl

end Azurite.AzFloat
