/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.SinCosBracket
import Azurite.AzFloat.Equiv.SinBracket
import Azurite.AzFloat.Equiv.ZivPair
import Azurite.AzInt.Equiv.SinCosSplit
import Azurite.AzNat.Equiv.ModPow2
import Azurite.AzNat.Equiv.ShiftRight

/-!
# Equivalence: the joint bracket of `sin x` and `cos x`

* `cos_partial_bounds`, `sin_partial_bounds`: consecutive partial sums of the two alternating
  Taylor series bracket the values; `abs_sub_partial_le`, `alternating_partial_nonneg`.
* `cosTerm_sinCosTerms_le`: the term count of `sinCosTerms` certifies a term below `2^(−V)`.
* `enclFraction_spec`: the one-division enclosure of a value near an integer fraction;
  `sinCosBlock_spec`: the binary-splitting enclosures of `sin y`, `cos y` for `y = d/2^c ≤ 1`.
* `sinCosY`, `sum_Ico_sinCosY`: the blocks of the fixed-point number telescope to `M / 2^T`.
* `sinCosRotate_spec`, `sinCosFixLoop_spec`, `sinCosFix_spec`: the rotation recurrence.
* `enclMulNonnegSigned_spec`, `sinCosTail_spec`: the double-angle steps and the widening.
* `sinCosBracket_spec`: `sinCosBracket x ex w` encloses `sin |x|` and `cos x` with widths at most
  `sinCosEps ex w`; `tendsto_sinCosEps`; `sinCosApprox_spec_sin`/`_cos`;
  `sinCosApprox_isSome_exists` (the joint Ziv certificate).
* `sinBracket_spec`, `cosBracket_spec` (the two components alone, widths `sinEps`, `cosEps`),
  `sinApprox_spec`, `cosApprox_spec`, `sinApprox_isSome_exists`, `cosApprox_isSome_exists`.
-/

open Finset

namespace Azurite.AzFloat

/-! ### Consecutive partial sums bracket the alternating series -/

/-- The terms `m^{2k+1}/(2k+1)!` of the sine series. -/
noncomputable def sinTerm (m : ℝ) (k : ℕ) : ℝ := m ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)

theorem sinTerm_nonneg {m : ℝ} (hm : 0 ≤ m) (k : ℕ) : 0 ≤ sinTerm m k := by
  unfold sinTerm; positivity

theorem sinTerm_le_cosTerm {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (k : ℕ) :
    sinTerm m k ≤ cosTerm m k := by
  unfold sinTerm cosTerm
  have h1 : m ^ (2 * k + 1) ≤ m ^ (2 * k) := by
    rw [pow_succ]; exact mul_le_of_le_one_right (by positivity) hm1
  have h2 : ((2 * k).factorial : ℝ) ≤ ((2 * k + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (Nat.le_succ _)
  exact div_le_div₀ (by positivity) h1 (by positivity) h2

theorem sinTerm_antitone {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 1) : Antitone (sinTerm m) := by
  refine antitone_nat_of_succ_le fun k => ?_
  unfold sinTerm
  have h1 : m ^ (2 * (k + 1) + 1) ≤ m ^ (2 * k + 1) :=
    pow_le_pow_of_le_one hm0 hm1 (by omega)
  have h2 : ((2 * k + 1).factorial : ℝ) ≤ ((2 * (k + 1) + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega)
  exact div_le_div₀ (by positivity) h1 (by positivity) h2

/-- `∑_{i<2k} ≤ cos m ≤ ∑_{i<2k+1}` for the cosine series, `|m| ≤ 1`. -/
theorem cos_partial_bounds {m : ℝ} (hm : |m| ≤ 1) (k : ℕ) :
    ∑ i ∈ range (2 * k), (-1) ^ i * cosTerm m i ≤ Real.cos m ∧
      Real.cos m ≤ ∑ i ∈ range (2 * k + 1), (-1) ^ i * cosTerm m i := by
  have hsum := (Real.hasSum_cos m).tendsto_sum_nat
  have hsum' : Filter.Tendsto (fun n => ∑ i ∈ range n, (-1) ^ i * cosTerm m i) Filter.atTop
      (nhds (Real.cos m)) := by
    refine hsum.congr fun n => sum_congr rfl fun i _ => ?_
    unfold cosTerm; ring
  have hanti := cosTerm_antitone hm
  exact ⟨hanti.alternating_series_le_tendsto hsum' k,
    hanti.tendsto_le_alternating_series hsum' k⟩

/-- `∑_{i<2k} ≤ sin m ≤ ∑_{i<2k+1}` for the sine series, `0 ≤ m ≤ 1`. -/
theorem sin_partial_bounds {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (k : ℕ) :
    ∑ i ∈ range (2 * k), (-1) ^ i * sinTerm m i ≤ Real.sin m ∧
      Real.sin m ≤ ∑ i ∈ range (2 * k + 1), (-1) ^ i * sinTerm m i := by
  have hsum := (Real.hasSum_sin m).tendsto_sum_nat
  have hsum' : Filter.Tendsto (fun n => ∑ i ∈ range n, (-1) ^ i * sinTerm m i) Filter.atTop
      (nhds (Real.sin m)) := by
    refine hsum.congr fun n => sum_congr rfl fun i _ => ?_
    unfold sinTerm; ring
  have hanti := sinTerm_antitone hm0 hm1
  exact ⟨hanti.alternating_series_le_tendsto hsum' k,
    hanti.tendsto_le_alternating_series hsum' k⟩

/-- For an alternating series whose even and odd partial sums bracket `v`, the partial sums
with `N` and `N + 1` terms bracket `v` in the order given by the parity of `N`. -/
theorem partial_bracket_of_parity {f : ℕ → ℝ} {v : ℝ}
    (h : ∀ k, ∑ i ∈ range (2 * k), (-1) ^ i * f i ≤ v ∧
      v ≤ ∑ i ∈ range (2 * k + 1), (-1) ^ i * f i) (N : ℕ) :
    (N % 2 = 0 → ∑ i ∈ range N, (-1) ^ i * f i ≤ v ∧ v ≤ ∑ i ∈ range (N + 1), (-1) ^ i * f i) ∧
    (¬ N % 2 = 0 →
      ∑ i ∈ range (N + 1), (-1) ^ i * f i ≤ v ∧ v ≤ ∑ i ∈ range N, (-1) ^ i * f i) := by
  constructor
  · intro hN
    obtain ⟨k, rfl⟩ : ∃ k, N = 2 * k := ⟨N / 2, by omega⟩
    exact h k
  · intro hN
    obtain ⟨k, rfl⟩ : ∃ k, N = 2 * k + 1 := ⟨N / 2, by omega⟩
    exact ⟨(h (k + 1)).1, (h k).2⟩

/-! ### The number of terms -/

/-- The invariant of `sinCosTermsLoop`. -/
theorem cosTerm_sinCosTermsLoop_le {y : ℝ} {c V : ℕ} (hy0 : 0 ≤ y) (hy : y ≤ (1 / 2 : ℝ) ^ c) :
    ∀ (fuel n acc : ℕ), cosTerm y n ≤ (1 / 2 : ℝ) ^ acc → V ≤ acc + fuel →
      cosTerm y (sinCosTermsLoop c V fuel n acc) ≤ (1 / 2 : ℝ) ^ V := by
  intro fuel
  induction fuel with
  | zero =>
    intro n acc h hV
    rw [sinCosTermsLoop]
    exact h.trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega))
  | succ fuel ih =>
    intro n acc h hV
    rw [sinCosTermsLoop]
    split_ifs with hc
    · exact h.trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) hc)
    · set q := (2 * n + 1) * (2 * n + 2) with hq
      have hq2 : 2 ≤ q := by rw [hq]; nlinarith
      have hsz : 2 ≤ q.size := by
        have : 1 < q.size := Nat.lt_size.mpr (by simpa using hq2)
        omega
      have hpow : (2 : ℝ) ^ (q.size - 1) ≤ (q : ℝ) := by
        exact_mod_cast (Nat.lt_size.mp (by omega) : 2 ^ (q.size - 1) ≤ q)
      refine ih (n + 1) _ ?_ (by rw [AzNat.size_ofNat]; omega)
      rw [cosTerm_succ, AzNat.size_ofNat, pow_add, pow_add]
      have hyy : y * y ≤ (1 / 2 : ℝ) ^ (2 * c) := by
        rw [two_mul, pow_add]
        exact mul_le_mul hy hy hy0 (by positivity)
      have hq0 : (0 : ℝ) < ((2 * n + 1) * (2 * n + 2) : ℕ) := by
        rw [← hq]; exact_mod_cast (by omega : 0 < q)
      rw [div_le_iff₀ hq0]
      have hct := cosTerm_nonneg y n
      have h1 : cosTerm y n * (y * y) ≤ (1 / 2 : ℝ) ^ acc * (1 / 2 : ℝ) ^ (2 * c) :=
        mul_le_mul h hyy (mul_self_nonneg y) (by positivity)
      have h2 : (1 : ℝ) ≤ (1 / 2 : ℝ) ^ (q.size - 1) * ((2 * n + 1) * (2 * n + 2) : ℕ) := by
        rw [← hq, one_div_pow, one_div, inv_mul_eq_div, le_div_iff₀ (by positivity), one_mul]
        exact hpow
      calc cosTerm y n * (y * y) ≤ (1 / 2 : ℝ) ^ acc * (1 / 2 : ℝ) ^ (2 * c) * 1 := by
            rw [mul_one]; exact h1
        _ ≤ (1 / 2 : ℝ) ^ acc * (1 / 2 : ℝ) ^ (2 * c)
            * ((1 / 2 : ℝ) ^ (q.size - 1) * ((2 * n + 1) * (2 * n + 2) : ℕ)) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = _ := by ring

/-- **The term count certifies the tail**: `y^(2N)/(2N)! ≤ 2^(−V)` for `N = sinCosTerms c V`
and `0 ≤ y ≤ 2^(−c)`. -/
theorem cosTerm_sinCosTerms_le {y : ℝ} {c : ℕ} (hy0 : 0 ≤ y) (hy : y ≤ (1 / 2 : ℝ) ^ c)
    (V : ℕ) : cosTerm y (sinCosTerms c V) ≤ (1 / 2 : ℝ) ^ V :=
  cosTerm_sinCosTermsLoop_le hy0 hy V 0 0 (by rw [cosTerm_zero, pow_zero]) (by omega)

/-! ### The block enclosures -/

/-- The partial sums of an alternating series with antitone nonnegative terms are nonnegative. -/
theorem alternating_partial_nonneg {f : ℕ → ℝ} (hf : Antitone f) (h0 : ∀ i, 0 ≤ f i) (n : ℕ) :
    0 ≤ ∑ i ∈ range n, (-1) ^ i * f i := by
  have heven : ∀ k, 0 ≤ ∑ i ∈ range (2 * k), (-1) ^ i * f i := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, sum_range_succ, sum_range_succ,
        (even_two_mul k).neg_one_pow, (even_two_mul k).add_one.neg_one_pow]
      have := hf (Nat.le_succ (2 * k))
      linarith
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · exact heven k
  · rw [sum_range_succ, (even_two_mul k).neg_one_pow]
    linarith [heven k, h0 (2 * k)]

/-- The partial sum with `N + 1` terms is within the term of index `N` of the value. -/
theorem abs_sub_partial_le {f : ℕ → ℝ} {v : ℝ}
    (h : ∀ k, ∑ i ∈ range (2 * k), (-1) ^ i * f i ≤ v ∧
      v ≤ ∑ i ∈ range (2 * k + 1), (-1) ^ i * f i) (N : ℕ) :
    |v - ∑ i ∈ range (N + 1), (-1) ^ i * f i| ≤ f N := by
  obtain ⟨hev, hodd⟩ := partial_bracket_of_parity h N
  by_cases hN : N % 2 = 0
  · obtain ⟨h1, h2⟩ := hev hN
    rw [sum_range_succ, (Nat.even_iff.mpr hN).neg_one_pow] at h2 ⊢
    rw [abs_le]; constructor <;> linarith
  · obtain ⟨h1, h2⟩ := hodd hN
    rw [sum_range_succ, (Nat.odd_iff.mpr (by omega)).neg_one_pow] at h1 ⊢
    rw [abs_le]; constructor <;> linarith

set_option maxHeartbeats 800000 in
/-- **`enclFraction` encloses** every `v ∈ [0, 1]` within `τ = |P| / D` of `a / D`, with width
at most `6 τ + 19 · 2^(−V)`. -/
theorem enclFraction_spec {a P D : AzInt} {v τ : ℝ} (hD : (0 : ℝ) < D.toInt)
    (ha : (0 : ℝ) ≤ a.toInt) (hτ : |(P.toInt : ℝ)| / D.toInt = τ)
    (hv : |v - (a.toInt : ℝ) / D.toInt| ≤ τ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hτ1 : τ ≤ 1) {V : ℕ}
    (hV : 64 ≤ V) :
    IsEncl0W (enclFraction V a P D) v (6 * τ + 19 * (1 / 2 : ℝ) ^ V) := by
  have : NeZero V := ⟨by omega⟩
  have : NeZero (V + 8) := ⟨by omega⟩
  have : NeZero (64 : ℕ) := ⟨by norm_num⟩
  set u := (1 / 2 : ℝ) ^ V with hu
  set u' := (1 / 2 : ℝ) ^ (V + 8) with hu'
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = (1 / 2 : ℝ) ^ 64 := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by positivity
  have hu'0 : 0 ≤ u' := by positivity
  have hε0 : 0 ≤ ε := by rw [hε]; positivity
  have hus : u ≤ 1 / 10 ^ 18 := half_pow_small hV
  have hεs : ε ≤ 1 / 10 ^ 18 := by rw [hε]; exact half_pow_small le_rfl
  have hu'u : u' = u / 256 := by
    rw [hu', hu, pow_add]; norm_num; ring
  have hu's : u' ≤ 1 / 10 ^ 18 := by rw [hu'u]; linarith
  have hav := toVal_ofAzInt a
  have hDval := toVal_ofAzInt D
  have hPabs : (ofAzInt P).abs.toVal = some ((|(P.toInt : ℝ)| : ℝ) : EReal) := by
    rw [toVal_abs, toVal_ofAzInt, Option.map_some, ← EReal.coe_neg]
    congr 1
  have hPa0 := abs_nonneg (P.toInt : ℝ)
  generalize |(P.toInt : ℝ)| = Pa at *
  generalize (a.toInt : ℝ) = A at *
  generalize (D.toInt : ℝ) = Dv at *
  set base := A / Dv with hbase
  have hτ0 : 0 ≤ τ := by rw [← hτ]; positivity
  obtain ⟨hv1', hv2'⟩ := abs_le.mp hv
  have hbase0 : 0 ≤ base := div_nonneg ha hD.le
  have hbase2 : base ≤ 2 := by linarith
  have hAb : A = base * Dv := by rw [hbase, div_mul_cancel₀ _ hD.ne']
  -- the truncations and the division
  obtain ⟨x, hx, hxf⟩ := setPrecFloor_err hav ha (V + 8)
  obtain ⟨y, hy, hyc⟩ := setPrecCeiling_err hDval hD.le (V + 8)
  have hy0 : 0 < y := lt_of_lt_of_le hD hyc.ge
  obtain ⟨q, hq, hqf⟩ := divFloor_err hx hy hy0 hxf.nonneg (V + 8)
  have hx1 := hxf.le
  have hx2 := hxf.ge
  have hy1 := hyc.ge
  have hy2 := hyc.le
  have hq0 := hqf.nonneg
  have hq1 := hqf.le
  have hq2 := hqf.ge
  rw [← hu'] at hx2 hy2 hq2
  have hqb : q ≤ base := hq1.trans (div_le_div₀ ha hx1 hD hy1)
  set r := x / y with hr
  have hr0 : 0 ≤ r := div_nonneg hxf.nonneg hy0.le
  have hxr : x = r * y := by rw [hr, div_mul_cancel₀ _ hy0.ne']
  have h1 : base * (1 - 2 * u') ≤ r * (1 + 2 * u') := by
    have h : base * (1 - 2 * u') * Dv ≤ r * (1 + 2 * u') * Dv :=
      calc base * (1 - 2 * u') * Dv = A - 2 * A * u' := by rw [hAb]; ring
        _ ≤ x := by linarith
        _ = r * y := hxr
        _ ≤ r * (Dv + 2 * Dv * u') := mul_le_mul_of_nonneg_left hy2 hr0
        _ = r * (1 + 2 * u') * Dv := by ring
    exact le_of_mul_le_mul_right h hD
  have h2 : r * (1 - 2 * u') ≤ q := by linarith
  have hkey : base ≤ q + 8 * u' * q := by
    have hpos : 0 < (1 - 2 * u') ^ 2 := pow_pos (by linarith) 2
    have ha' : base * (1 - 2 * u') ^ 2 ≤ q * (1 + 2 * u') :=
      calc base * (1 - 2 * u') ^ 2 = base * (1 - 2 * u') * (1 - 2 * u') := by ring
        _ ≤ r * (1 + 2 * u') * (1 - 2 * u') := mul_le_mul_of_nonneg_right h1 (by linarith)
        _ = r * (1 - 2 * u') * (1 + 2 * u') := by ring
        _ ≤ q * (1 + 2 * u') := mul_le_mul_of_nonneg_right h2 (by linarith)
    have hb : 1 + 2 * u' ≤ (1 + 8 * u') * (1 - 2 * u') ^ 2 := by
      nlinarith [mul_nonneg hu'0 (by linarith : 0 ≤ 2 - 28 * u'), pow_nonneg hu'0 3]
    have h : base * (1 - 2 * u') ^ 2 ≤ (q + 8 * u' * q) * (1 - 2 * u') ^ 2 :=
      calc base * (1 - 2 * u') ^ 2 ≤ q * (1 + 2 * u') := ha'
        _ ≤ q * ((1 + 8 * u') * (1 - 2 * u') ^ 2) := mul_le_mul_of_nonneg_left hb hq0
        _ = (q + 8 * u' * q) * (1 - 2 * u') ^ 2 := by ring
    exact le_of_mul_le_mul_right h hpos
  have hq2' : q ≤ 2 := hqb.trans hbase2
  -- the bound of the term
  obtain ⟨pu, hpu, hpuc⟩ := setPrecCeiling_err hPabs hPa0 64
  obtain ⟨dl, hdl, hdlf⟩ := setPrecFloor_err hDval hD.le 64
  have hdl0 : 0 < dl := hdlf.pos (by norm_num) hD
  have hpu0 : 0 ≤ pu := le_trans hPa0 hpuc.ge
  obtain ⟨t, ht, htc⟩ := divCeiling_err hpu hdl hdl0 hpu0 64
  have hpu2 := hpuc.le
  have hdl2 := hdlf.ge
  have ht' := htc.le
  rw [← hε] at hpu2 hdl2 ht'
  have htτ : τ ≤ t :=
    calc τ = Pa / Dv := hτ.symm
      _ ≤ pu / dl := div_le_div₀ hpu0 hpuc.ge hdl0 hdlf.le
      _ ≤ t := htc.ge
  have ht2 : t ≤ 2 * τ := by
    set ρ := pu / dl with hρ
    have hρ0 : 0 ≤ ρ := div_nonneg hpu0 hdl0.le
    have hP : Pa = τ * Dv := by rw [← hτ, div_mul_cancel₀ _ hD.ne']
    have hρ1 : ρ * (1 - 2 * ε) ≤ τ * (1 + 2 * ε) := by
      have h : ρ * (1 - 2 * ε) * Dv ≤ τ * (1 + 2 * ε) * Dv :=
        calc ρ * (1 - 2 * ε) * Dv = ρ * (Dv - 2 * Dv * ε) := by ring
          _ ≤ ρ * dl := mul_le_mul_of_nonneg_left (by linarith) hρ0
          _ = pu := div_mul_cancel₀ _ hdl0.ne'
          _ ≤ Pa + 2 * Pa * ε := hpu2
          _ = τ * (1 + 2 * ε) * Dv := by rw [hP]; ring
      exact le_of_mul_le_mul_right h hD
    have hsq : (1 + 2 * ε) * (1 + 2 * ε) ≤ 2 * (1 - 2 * ε) := by
      nlinarith [mul_le_mul_of_nonneg_left hεs hε0]
    have h : t * (1 - 2 * ε) ≤ 2 * τ * (1 - 2 * ε) :=
      calc t * (1 - 2 * ε) ≤ ρ * (1 + 2 * ε) * (1 - 2 * ε) :=
            mul_le_mul_of_nonneg_right (by linarith) (by linarith)
        _ = ρ * (1 - 2 * ε) * (1 + 2 * ε) := by ring
        _ ≤ τ * (1 + 2 * ε) * (1 + 2 * ε) := mul_le_mul_of_nonneg_right hρ1 (by linarith)
        _ = τ * ((1 + 2 * ε) * (1 + 2 * ε)) := by ring
        _ ≤ τ * (2 * (1 - 2 * ε)) := mul_le_mul_of_nonneg_left hsq hτ0
        _ = 2 * τ * (1 - 2 * ε) := by ring
    exact le_of_mul_le_mul_right h (by linarith)
  -- the slack of the upper end
  have h8 : q * (2 : ℝ) ^ ((3 : ℤ) - ((V + 8 : ℕ) : ℤ)) = 8 * u' * q := by
    have h23 : (2 : ℝ) ^ (3 : ℤ) = 8 := by norm_num
    rw [zpow_sub₀ two_ne_zero, zpow_natCast, hu', one_div_pow, h23]
    ring
  have hsh := toVal_shiftLeft_of_toVal hq (AzInt.ofInt (3 - ((V + 8 : ℕ) : Int)))
  rw [AzInt.toInt_ofInt, h8] at hsh
  obtain ⟨e, he, hec⟩ := addCeiling_err hsh ht 64
    (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hu'0) hq0) (hτ0.trans htτ))
  have he1 := hec.ge
  have he2 := hec.le
  rw [← hε] at he2
  have hqu : 8 * u' * q ≤ 16 * u' := by nlinarith
  have he3 : e ≤ 4 * τ + u / 8 := by
    have hb0 : 0 ≤ 8 * u' * q + t :=
      add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hu'0) hq0) (hτ0.trans htτ)
    have := mul_le_mul_of_nonneg_left (by linarith : ε ≤ 1 / 2) hb0
    linarith
  -- the two ends
  obtain ⟨l, hl, hl1, hl2⟩ := subFloor_abs hq ht V
  obtain ⟨h, hh, hh1, hh2⟩ := addCeiling_abs hq he V
  rw [← hu] at hl2 hh2
  have habs1 : |q - t| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have habs2 : |q + e| ≤ 7 := abs_le.mpr ⟨by linarith, by linarith⟩
  have m1 := mul_le_mul_of_nonneg_right habs1 hu0
  have m2 := mul_le_mul_of_nonneg_right habs2 hu0
  have hW : IsEnclW ((subPrecRound _ _ V .Floor).1, (addPrecRound _ _ V .Ceiling).1) v
      (6 * τ + 19 * u) :=
    ⟨l, h, hl, hh, by linarith, by linarith, by linarith⟩
  exact enclClamp0_spec hW hv0

/-- `enclFraction` at the partial sum with `N + 1` terms of an alternating series. -/
theorem enclFraction_partial_spec {a P D : AzInt} {f : ℕ → ℝ} {v τ : ℝ} (N : ℕ)
    (hD : (0 : ℝ) < D.toInt)
    (ha : (a.toInt : ℝ) / D.toInt = ∑ i ∈ range (N + 1), (-1) ^ i * f i)
    (hP : |(P.toInt : ℝ)| / D.toInt = f N)
    (hbr : ∀ k, ∑ i ∈ range (2 * k), (-1) ^ i * f i ≤ v ∧
      v ≤ ∑ i ∈ range (2 * k + 1), (-1) ^ i * f i)
    (hanti : Antitone f) (hf0 : ∀ i, 0 ≤ f i) (hf : f N ≤ τ) (hτ1 : τ ≤ 1) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) {V : ℕ} (hV : 64 ≤ V) :
    IsEncl0W (enclFraction V a P D) v (6 * τ + 19 * (1 / 2 : ℝ) ^ V) := by
  have ha0 : (0 : ℝ) ≤ a.toInt := by
    have h := alternating_partial_nonneg hanti hf0 (N + 1)
    rw [← ha] at h
    exact (div_nonneg_iff.mp h).elim (fun h => h.1) fun h => absurd h.2 (not_le.mpr hD)
  have hv := abs_sub_partial_le hbr N
  rw [← ha] at hv
  exact (enclFraction_spec hD ha0 hP hv hv0 hv1 (hf.trans hτ1) hV).mono (by linarith)

/-- **The block enclosures**: `sinCosBlock d c N V` encloses `sin y` and `cos y` for
`y = d / 2^c ≤ 1`, with widths at most six times the term of index `N` plus the rounding. -/
theorem sinCosBlock_spec (d : AzNat) (c N : ℕ) {V : ℕ} (hV : 64 ≤ V)
    (hy : (d.toNat : ℝ) / 2 ^ c ≤ 1) :
    IsEncl0W (sinCosBlock d c N V).1 (Real.sin ((d.toNat : ℝ) / 2 ^ c))
        (6 * cosTerm ((d.toNat : ℝ) / 2 ^ c) N + 19 * (1 / 2 : ℝ) ^ V) ∧
      IsEncl0W (sinCosBlock d c N V).2 (Real.cos ((d.toNat : ℝ) / 2 ^ c))
        (6 * cosTerm ((d.toNat : ℝ) / 2 ^ c) N + 19 * (1 / 2 : ℝ) ^ V) := by
  set y := (d.toNat : ℝ) / 2 ^ c with hydef
  have hy0 : 0 ≤ y := by positivity
  have habs : |y| ≤ 1 := by rw [abs_of_nonneg hy0]; exact hy
  have hx : (((d * d).toNat : ℝ)) / 2 ^ (2 * c) = y * y := by
    rw [AzNat.toNat_mul, hydef, pow_mul']
    push_cast
    field_simp
  have hpi : (1 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hcos0 : 0 ≤ Real.cos y := Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have hsin0 : 0 ≤ Real.sin y := Real.sin_nonneg_of_nonneg_of_le_pi hy0 (by linarith)
  have hct1 := cosTerm_le_one habs N
  have hpowy : ∀ k : ℕ, (y * y) ^ k = y ^ (2 * k) := fun k => by rw [pow_mul, sq]
  obtain ⟨hcP, hcB, hcT⟩ := AzInt.altSpec_split (d * d) (2 * c) 0 0 N
  rw [hx] at hcT
  rw [AzInt.prod_altDen_zero] at hcB
  obtain ⟨hsP, hsB, hsT⟩ := AzInt.altSpec_split (d * d) (2 * c) 1 0 N
  rw [hx] at hsT
  rw [AzInt.prod_altDen_one] at hsB
  set sc := AzInt.altSplit (d * d) (2 * c) 0 0 N with hsc
  set ss := AzInt.altSplit (d * d) (2 * c) 1 0 N with hss
  have hFc : (0 : ℝ) < ((2 * N).factorial : ℝ) := by positivity
  have hFs : (0 : ℝ) < ((2 * N + 1).factorial : ℝ) := by positivity
  have h2p : (0 : ℝ) < (2 : ℝ) ^ (2 * c * N) := by positivity
  have h2c : (0 : ℝ) < (2 : ℝ) ^ c := by positivity
  have hd0 : (0 : ℝ) ≤ (d.toNat : ℝ) := by positivity
  have hdd0 : (0 : ℝ) ≤ ((d * d).toNat : ℝ) ^ N := by positivity
  have hPc : |(sc.1.toInt : ℝ)| = ((d * d).toNat : ℝ) ^ N := by
    rw [hcP]; push_cast
    rw [abs_pow, abs_neg, Nat.abs_cast]
  have hPs : |((d.toAzInt * ss.1).toInt : ℝ)| = (d.toNat : ℝ) * ((d * d).toNat : ℝ) ^ N := by
    rw [AzInt.toInt_mul, AzInt.toInt_natToAzInt, hsP]; push_cast
    rw [abs_mul, abs_pow, abs_neg, Nat.abs_cast, Nat.abs_cast]
  have hxN : ((d * d).toNat : ℝ) ^ N = (y * y) ^ N * 2 ^ (2 * c * N) := by
    rw [← hx, div_pow, ← pow_mul, div_mul_cancel₀ _ h2p.ne']
  simp only [sinCosBlock]
  rw [← hsc, ← hss]
  constructor
  · refine enclFraction_partial_spec (f := sinTerm y) N ?_ ?_ ?_ (sin_partial_bounds hy0 hy)
      (sinTerm_antitone hy0 hy) (sinTerm_nonneg hy0) (sinTerm_le_cosTerm hy0 hy N) hct1 hsin0
      (Real.sin_le_one y) hV
    · simp only [AzInt.toInt_hShiftLeft, AzInt.toInt_natToAzInt, hsB]
      push_cast
      positivity
    · simp only [AzInt.toInt_hShiftLeft, AzInt.toInt_natToAzInt, AzInt.toInt_mul,
        AzInt.toInt_add, hsB]
      push_cast
      have h := AzInt.one_add_altPartial_one (y * y) N
      rw [← hsT, hsB] at h
      have e : ∑ i ∈ range (N + 1), (-1) ^ i * sinTerm y i
          = y * ∑ k ∈ range (N + 1), (-1) ^ k * ((y * y) ^ k / ((2 * k + 1).factorial : ℝ)) := by
        rw [mul_sum]
        refine sum_congr rfl fun k _ => ?_
        unfold sinTerm
        rw [hpowy]
        ring
      rw [e, ← h, hydef]
      field_simp
    · rw [hPs, hxN]
      simp only [AzInt.toInt_hShiftLeft, AzInt.toInt_natToAzInt, hsB]
      push_cast
      unfold sinTerm
      rw [pow_succ, ← hpowy, hydef]
      field_simp
  · refine enclFraction_partial_spec (f := cosTerm y) N ?_ ?_ ?_ (cos_partial_bounds habs)
      (cosTerm_antitone habs) (cosTerm_nonneg y) le_rfl hct1 hcos0 (Real.cos_le_one y) hV
    · simp only [AzInt.toInt_hShiftLeft, AzInt.toInt_natToAzInt, hcB]
      push_cast
      positivity
    · simp only [AzInt.toInt_hShiftLeft, AzInt.toInt_natToAzInt, AzInt.toInt_add, hcB]
      push_cast
      have h := AzInt.one_add_altPartial_zero (y * y) N
      rw [← hcT, hcB] at h
      have e : ∑ i ∈ range (N + 1), (-1) ^ i * cosTerm y i
          = ∑ k ∈ range (N + 1), (-1) ^ k * ((y * y) ^ k / ((2 * k).factorial : ℝ)) := by
        refine sum_congr rfl fun k _ => ?_
        unfold cosTerm
        rw [hpowy]
      rw [e, ← h]
      field_simp
    · rw [hPc, hxN]
      simp only [AzInt.toInt_hShiftLeft, AzInt.toInt_natToAzInt, hcB]
      push_cast
      unfold cosTerm
      rw [← hpowy]
      field_simp

/-! ### The blocks of the fixed-point number -/

theorem sinCosCut_le (T i : ℕ) : sinCosCut T i ≤ T := min_le_right _ _

theorem sinCosCut_mono (T i : ℕ) : sinCosCut T i ≤ sinCosCut T (i + 1) := by
  unfold sinCosCut
  have h : 2 ^ i - 1 ≤ 2 ^ (i + 1) - 1 := by
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (Nat.le_succ i)
    omega
  exact min_le_min (Nat.mul_le_mul_left _ h) le_rfl

theorem sinCosCut_zero (T : ℕ) : sinCosCut T 0 = 0 := by simp [sinCosCut]

theorem sinCosCut_size (T : ℕ) : sinCosCut T (AzNat.ofNat T).size = T := by
  unfold sinCosCut sinCosBlockBase
  rw [AzNat.size_ofNat]
  have := Nat.lt_size_self T
  exact min_eq_right (by omega)

/-- The prefix of `M / 2^T` at the cut position `i`: `⌊M / 2^(T − c_i)⌋ / 2^(c_i)`. -/
noncomputable def sinCosPrefix (M : AzNat) (T i : ℕ) : ℝ :=
  ((M.toNat / 2 ^ (T - sinCosCut T i) : ℕ) : ℝ) / 2 ^ sinCosCut T i

/-- The value of block `i` of `M / 2^T`. -/
noncomputable def sinCosY (M : AzNat) (T i : ℕ) : ℝ :=
  ((sinCosDigit M T i).toNat : ℝ) / 2 ^ sinCosCut T (i + 1)

theorem toNat_sinCosDigit (M : AzNat) (T i : ℕ) :
    (sinCosDigit M T i).toNat
      = M.toNat / 2 ^ (T - sinCosCut T (i + 1)) % 2 ^ (sinCosCut T (i + 1) - sinCosCut T i) := by
  unfold sinCosDigit
  rw [AzNat.toNat_modPow2, AzNat.toNat_hShiftRight, Nat.shiftRight_eq_div_pow]

theorem sinCosPrefix_nonneg (M : AzNat) (T i : ℕ) : 0 ≤ sinCosPrefix M T i := by
  unfold sinCosPrefix; positivity

theorem sinCosPrefix_le (M : AzNat) (T i : ℕ) :
    sinCosPrefix M T i ≤ (M.toNat : ℝ) / 2 ^ T := by
  unfold sinCosPrefix
  have hc := sinCosCut_le T i
  have h : ((M.toNat / 2 ^ (T - sinCosCut T i) : ℕ) : ℝ)
      ≤ (M.toNat : ℝ) / 2 ^ (T - sinCosCut T i) := by
    have := Nat.cast_div_le (α := ℝ) (m := M.toNat) (n := 2 ^ (T - sinCosCut T i))
    simpa using this
  have hT : (2 : ℝ) ^ T = 2 ^ (T - sinCosCut T i) * 2 ^ sinCosCut T i := by
    rw [← pow_add, Nat.sub_add_cancel hc]
  rw [hT, ← div_div]
  exact div_le_div_of_nonneg_right h (by positivity)

/-- A block is the difference of two consecutive prefixes. -/
theorem sinCosY_eq (M : AzNat) (T i : ℕ) :
    sinCosY M T i = sinCosPrefix M T (i + 1) - sinCosPrefix M T i := by
  unfold sinCosY sinCosPrefix
  rw [toNat_sinCosDigit]
  have h1 := sinCosCut_mono T i
  have h2 := sinCosCut_le T (i + 1)
  set c := sinCosCut T i with hc
  set c' := sinCosCut T (i + 1) with hc'
  set a := M.toNat / 2 ^ (T - c') with ha
  have hdiv : M.toNat / 2 ^ (T - c) = a / 2 ^ (c' - c) := by
    rw [ha, Nat.div_div_eq_div_mul, ← pow_add]
    congr 2
    omega
  have hdm := Nat.div_add_mod a (2 ^ (c' - c))
  have hreal : (a : ℝ)
      = 2 ^ (c' - c) * ((a / 2 ^ (c' - c) : ℕ) : ℝ) + ((a % 2 ^ (c' - c) : ℕ) : ℝ) := by
    exact_mod_cast hdm.symm
  have hpow : (2 : ℝ) ^ c' = 2 ^ (c' - c) * 2 ^ c := by
    rw [← pow_add, Nat.sub_add_cancel h1]
  rw [hdiv, eq_sub_iff_add_eq, hreal, hpow]
  field_simp
  ring

theorem sinCosY_nonneg (M : AzNat) (T i : ℕ) : 0 ≤ sinCosY M T i := by
  unfold sinCosY; positivity

/-- A block is below `2^(−c_i)`. -/
theorem sinCosY_le (M : AzNat) (T i : ℕ) :
    sinCosY M T i ≤ (1 / 2 : ℝ) ^ sinCosCut T i := by
  unfold sinCosY
  rw [toNat_sinCosDigit]
  have h1 := sinCosCut_mono T i
  set c := sinCosCut T i with hc
  set c' := sinCosCut T (i + 1) with hc'
  have hlt : M.toNat / 2 ^ (T - c') % 2 ^ (c' - c) < 2 ^ (c' - c) :=
    Nat.mod_lt _ (by positivity)
  have hlt' : ((M.toNat / 2 ^ (T - c') % 2 ^ (c' - c) : ℕ) : ℝ) ≤ 2 ^ (c' - c) := by
    exact_mod_cast hlt.le
  have hpow : (2 : ℝ) ^ c' = 2 ^ (c' - c) * 2 ^ c := by
    rw [← pow_add, Nat.sub_add_cancel h1]
  rw [div_le_iff₀ (by positivity), hpow, one_div_pow, one_div, mul_comm ((2 : ℝ) ^ c)⁻¹,
    mul_assoc, mul_inv_cancel₀ (by positivity), mul_one]
  exact hlt'

/-- The blocks telescope. -/
theorem sum_Ico_sinCosY (M : AzNat) (T : ℕ) {a b : ℕ} (hab : a ≤ b) :
    ∑ i ∈ Ico a b, sinCosY M T i = sinCosPrefix M T b - sinCosPrefix M T a := by
  rw [← Finset.sum_Ico_sub (sinCosPrefix M T) hab]
  exact sum_congr rfl fun i _ => sinCosY_eq M T i

theorem sum_Ico_sinCosY_nonneg (M : AzNat) (T a b : ℕ) : 0 ≤ ∑ i ∈ Ico a b, sinCosY M T i :=
  sum_nonneg fun i _ => sinCosY_nonneg M T i

theorem sum_Ico_sinCosY_le (M : AzNat) (T : ℕ) {a b : ℕ} (hab : a ≤ b) :
    ∑ i ∈ Ico a b, sinCosY M T i ≤ (M.toNat : ℝ) / 2 ^ T := by
  rw [sum_Ico_sinCosY M T hab]
  linarith [sinCosPrefix_nonneg M T a, sinCosPrefix_le M T b]

/-- All the blocks together are the number itself. -/
theorem sum_range_sinCosY (M : AzNat) {T : ℕ} (hM : M.toNat < 2 ^ T) :
    ∑ i ∈ Ico 0 (AzNat.ofNat T).size, sinCosY M T i = (M.toNat : ℝ) / 2 ^ T := by
  rw [sum_Ico_sinCosY M T (Nat.zero_le _)]
  unfold sinCosPrefix
  rw [sinCosCut_size, sinCosCut_zero, Nat.sub_self, Nat.sub_zero, pow_zero, Nat.div_one,
    Nat.div_eq_of_lt hM]
  simp

/-! ### The rotation recurrence -/

theorem IsEncl0W.width_nonneg {a : Encl} {x δ : ℝ} (h : IsEncl0W a x δ) : 0 ≤ δ := by
  obtain ⟨lo, hi, -, -, -, h1, h2, h3⟩ := h
  linarith

theorem IsEncl0W.nonneg {a : Encl} {x δ : ℝ} (h : IsEncl0W a x δ) : 0 ≤ x := by
  obtain ⟨lo, hi, -, -, h0, h1, -, -⟩ := h
  linarith

/-- **The rotation by a block**, for angles `y, x ≥ 0` with `y + x ≤ 1`. -/
theorem sinCosRotate_spec {b r : Encl × Encl} {y x η δ : ℝ}
    (hb1 : IsEncl0W b.1 (Real.sin y) η) (hb2 : IsEncl0W b.2 (Real.cos y) η)
    (hr1 : IsEncl0W r.1 (Real.sin x) δ) (hr2 : IsEncl0W r.2 (Real.cos x) δ)
    (hy0 : 0 ≤ y) (hx0 : 0 ≤ x) (hyx : y + x ≤ 1) (hη : η ≤ 1 / 16) (hδ : δ ≤ 1 / 4)
    {V : ℕ} (hV : 64 ≤ V) :
    IsEncl0W (sinCosRotate V b r).1 (Real.sin (y + x))
        (2 * δ + 4 * η + 48 * (1 / 2 : ℝ) ^ V) ∧
      IsEncl0W (sinCosRotate V b r).2 (Real.cos (y + x))
        (2 * δ + 4 * η + 48 * (1 / 2 : ℝ) ^ V) := by
  set u := (1 / 2 : ℝ) ^ V with hu
  have hu0 : 0 ≤ u := by positivity
  have hus : u ≤ 1 / 10 ^ 18 := half_pow_small hV
  have hη0 := hb1.width_nonneg
  have hδ0 := hr1.width_nonneg
  have hpi : (1 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hsy0 := hb1.nonneg
  have hcy0 := hb2.nonneg
  have hsx0 := hr1.nonneg
  have hcx0 := hr2.nonneg
  have hsy1 := Real.sin_le_one y
  have hcy1 := Real.cos_le_one y
  have hsx1 := Real.sin_le_one x
  have hcx1 := Real.cos_le_one x
  have hηδ : η * δ ≤ η := by nlinarith
  have m1 := hb1.mul hr2 hsy1 hcx1 (by linarith) (by linarith) hV
  have m2 := hb2.mul hr1 hcy1 hsx1 (by linarith) (by linarith) hV
  have m3 := hb2.mul hr2 hcy1 hcx1 (by linarith) (by linarith) hV
  have m4 := hb1.mul hr1 hsy1 hsx1 (by linarith) (by linarith) hV
  rw [← hu] at m1 m2 m3 m4
  have hw1 : η + δ + η * δ + 16 * u ≤ 1 := by linarith
  have hsum0 : 0 ≤ Real.sin (y + x) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hcos0 : 0 ≤ Real.cos (y + x) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  constructor
  · have h := m1.toW.add0 m2 (M := 1)
      (by rw [abs_of_nonneg (mul_nonneg hsy0 hcx0)]; nlinarith)
      (by nlinarith) hw1 hw1 hV
    rw [← hu, ← Real.sin_add] at h
    exact (enclClamp0_spec h hsum0).mono (by linarith)
  · have h := m3.toW.sub0 m4 (M := 1)
      (by rw [abs_of_nonneg (mul_nonneg hcy0 hcx0)]; nlinarith)
      (by nlinarith) hw1 hw1 hV
    rw [← hu, ← Real.cos_add] at h
    exact (enclClamp0_spec h hcos0).mono (by linarith)

/-- **The rotation recurrence**: `sinCosFixLoop M T V n j` encloses the sine and the cosine of
the sum of the blocks `j, …, j + n − 1`, the widths at most doubling per block. -/
theorem sinCosFixLoop_spec (M : AzNat) {T V : ℕ} (hV : 64 ≤ V) (hM : (M.toNat : ℝ) / 2 ^ T ≤ 1) :
    ∀ n j : ℕ, (2 : ℝ) ^ n * (148 * (1 / 2 : ℝ) ^ V) ≤ 1 / 4 →
      IsEncl0W (sinCosFixLoop M T V n j).1 (Real.sin (∑ i ∈ Ico j (j + n), sinCosY M T i))
          (((2 : ℝ) ^ n - 1) * (148 * (1 / 2 : ℝ) ^ V)) ∧
        IsEncl0W (sinCosFixLoop M T V n j).2 (Real.cos (∑ i ∈ Ico j (j + n), sinCosY M T i))
          (((2 : ℝ) ^ n - 1) * (148 * (1 / 2 : ℝ) ^ V)) := by
  set u := (1 / 2 : ℝ) ^ V with hu
  have hu0 : 0 ≤ u := by positivity
  have hus : u ≤ 1 / 10 ^ 18 := half_pow_small hV
  intro n
  induction n with
  | zero =>
    intro j _
    simp only [sinCosFixLoop, Nat.add_zero, Ico_self, sum_empty, Real.sin_zero, Real.cos_zero,
      pow_zero, sub_self, zero_mul]
    exact ⟨isEncl0W_exact toVal_zero' le_rfl, isEncl0W_exact toVal_one' zero_le_one⟩
  | succ n ih =>
    intro j hn
    have hpow : (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
    have h2n : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    have hn' : (2 : ℝ) ^ n * (148 * u) ≤ 1 / 4 := by
      rw [hpow] at hn; nlinarith
    obtain ⟨ih1, ih2⟩ := ih (j + 1) hn'
    have hsum : ∑ i ∈ Ico j (j + (n + 1)), sinCosY M T i
        = sinCosY M T j + ∑ i ∈ Ico (j + 1) (j + 1 + n), sinCosY M T i := by
      rw [Finset.sum_eq_sum_Ico_succ_bot (by omega), show j + (n + 1) = j + 1 + n by ring]
    have hmono : ((2 : ℝ) ^ n - 1) * (148 * u) ≤ ((2 : ℝ) ^ (n + 1) - 1) * (148 * u) := by
      rw [hpow]; nlinarith
    rw [hsum]
    simp only [sinCosFixLoop]
    split_ifs with hd
    · have hy : sinCosY M T j = 0 := by
        unfold sinCosY
        rw [hd, AzNat.toNat_ofNat]
        simp
      rw [hy, zero_add]
      exact ⟨ih1.mono hmono, ih2.mono hmono⟩
    · have hy0 := sinCosY_nonneg M T j
      have hyc := sinCosY_le M T j
      have hy1 : sinCosY M T j ≤ 1 := hyc.trans (pow_le_one₀ (by norm_num) (by norm_num))
      obtain ⟨hb1, hb2⟩ := sinCosBlock_spec (sinCosDigit M T j) (sinCosCut T (j + 1))
        (sinCosTerms (sinCosCut T j) V) hV hy1
      have hterm := cosTerm_sinCosTerms_le hy0 hyc V
      rw [← hu] at hterm hb1 hb2
      have hη : 6 * cosTerm (sinCosY M T j) (sinCosTerms (sinCosCut T j) V) + 19 * u
          ≤ 25 * u := by
        linarith
      have htot : sinCosY M T j + ∑ i ∈ Ico (j + 1) (j + 1 + n), sinCosY M T i ≤ 1 := by
        rw [← hsum]
        exact (sum_Ico_sinCosY_le M T (by omega)).trans hM
      obtain ⟨h1, h2⟩ := sinCosRotate_spec (hb1.mono hη) (hb2.mono hη) ih1 ih2 hy0
        (sum_Ico_sinCosY_nonneg M T _ _) htot (by linarith) (by nlinarith) hV
      rw [← hu] at h1 h2
      have hw : 2 * (((2 : ℝ) ^ n - 1) * (148 * u)) + 4 * (25 * u) + 48 * u
          ≤ ((2 : ℝ) ^ (n + 1) - 1) * (148 * u) := by
        rw [hpow]; nlinarith
      exact ⟨h1.mono hw, h2.mono hw⟩

/-- **`sinCosFix` encloses `sin θ` and `cos θ`** for `θ = M / 2^T ≤ 1`, with widths at most
`296 T 2^(−V)`. -/
theorem sinCosFix_spec (M : AzNat) {T V : ℕ} (hV : 64 ≤ V) (hT0 : 0 < T)
    (hM : M.toNat < 2 ^ T) (hT : 296 * (T : ℝ) * (1 / 2 : ℝ) ^ V ≤ 1 / 4) :
    IsEncl0W (sinCosFix M T V).1 (Real.sin ((M.toNat : ℝ) / 2 ^ T))
        (296 * (T : ℝ) * (1 / 2 : ℝ) ^ V) ∧
      IsEncl0W (sinCosFix M T V).2 (Real.cos ((M.toNat : ℝ) / 2 ^ T))
        (296 * (T : ℝ) * (1 / 2 : ℝ) ^ V) := by
  set u := (1 / 2 : ℝ) ^ V with hu
  have hu0 : 0 ≤ u := by positivity
  have hM1 : (M.toNat : ℝ) / 2 ^ T ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact_mod_cast hM.le
  have hK : (2 : ℝ) ^ (AzNat.ofNat T).size ≤ 2 * T := by
    rw [AzNat.size_ofNat]
    have h1 : 2 ^ (T.size - 1) ≤ T := Nat.lt_size.mp (by have := Nat.size_pos.mpr hT0; omega)
    have h2 : 2 ^ T.size = 2 * 2 ^ (T.size - 1) := by
      rw [← pow_succ']; congr 1; have := Nat.size_pos.mpr hT0; omega
    exact_mod_cast (by omega : 2 ^ T.size ≤ 2 * T)
  have hK' : (2 : ℝ) ^ (AzNat.ofNat T).size * (148 * u) ≤ 296 * (T : ℝ) * u := by
    nlinarith [mul_le_mul_of_nonneg_right hK hu0]
  obtain ⟨h1, h2⟩ := sinCosFixLoop_spec M hV hM1 (AzNat.ofNat T).size 0 (by rw [← hu]; linarith)
  rw [Nat.zero_add, sum_range_sinCosY M hM, ← hu] at h1 h2
  unfold sinCosFix
  have hw : ((2 : ℝ) ^ (AzNat.ofNat T).size - 1) * (148 * u) ≤ 296 * (T : ℝ) * u := by
    nlinarith
  exact ⟨h1.mono hw, h2.mono hw⟩

/-! ### The double-angle steps -/

theorem enclDouble_spec {a : Encl} {x δ : ℝ} (ha : IsEnclW a x δ) :
    IsEnclW (enclDouble a) (2 * x) (2 * δ) := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, h3⟩ := ha
  exact ⟨2 * lo, 2 * hi, toVal_shiftLeft_one hlo, toVal_shiftLeft_one hhi, by linarith,
    by linarith, by linarith⟩

/-- The corner estimate of the signed product. -/
theorem corner_sub_le {a a' la ha lb hb : ℝ} (h1 : la ≤ a) (h2 : a ≤ ha) (h3 : la ≤ a')
    (h4 : a' ≤ ha) (hb' : lb ≤ hb) :
    a * hb - a' * lb ≤ ha * (hb - lb) + (ha - la) * |lb| := by
  have e : a * hb - a' * lb = a * (hb - lb) + (a - a') * lb := by ring
  have t1 : a * (hb - lb) ≤ ha * (hb - lb) := mul_le_mul_of_nonneg_right h2 (by linarith)
  have t2 : (a - a') * lb ≤ (ha - la) * |lb| :=
    calc (a - a') * lb ≤ |(a - a') * lb| := le_abs_self _
      _ = |a - a'| * |lb| := abs_mul _ _
      _ ≤ (ha - la) * |lb| :=
        mul_le_mul_of_nonneg_right (abs_le.mpr ⟨by linarith, by linarith⟩) (abs_nonneg _)
  linarith

/-- The product of a nonnegative enclosure (`x ≤ 1`) and an enclosure of any sign
(`|y| ≤ 1`). -/
theorem enclMulNonnegSigned_spec {a b : Encl} {x y δ ε : ℝ} (ha : IsEncl0W a x δ)
    (hb : IsEnclW b y ε) (hx : x ≤ 1) (hy : |y| ≤ 1) (hδ : δ ≤ 1) (hε : ε ≤ 1) {W : ℕ}
    (hW : 64 ≤ W) :
    IsEnclW (enclMulNonnegSigned W a b) (x * y) (2 * (δ + ε) + 16 * (1 / 2 : ℝ) ^ W) := by
  have : NeZero W := ⟨by omega⟩
  obtain ⟨la, ha', hla, hha, ha0, ha1, ha2, ha3⟩ := ha
  obtain ⟨lb, hb', hlb, hhb, hb1, hb2, hb3⟩ := hb
  set u := (1 / 2 : ℝ) ^ W with hu
  have hu0 : 0 ≤ u := by positivity
  obtain ⟨hy1, hy2⟩ := abs_le.mp hy
  have hδ0 : 0 ≤ δ := by linarith
  have hε0 : 0 ≤ ε := by linarith
  obtain ⟨r1, hr1, hr1a, hr1b⟩ := mulFloor_abs hla hlb W
  obtain ⟨r2, hr2, hr2a, hr2b⟩ := mulFloor_abs hha hlb W
  obtain ⟨r3, hr3, hr3a, hr3b⟩ := mulCeiling_abs hla hhb W
  obtain ⟨r4, hr4, hr4a, hr4b⟩ := mulCeiling_abs hha hhb W
  rw [← hu] at hr1b hr2b hr3b hr4b
  have hlbabs : |lb| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hhbabs : |hb'| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hha2 : ha' ≤ 2 := by linarith
  have hla2 : la ≤ 2 := by linarith
  have habs : ∀ {p q : ℝ}, 0 ≤ p → p ≤ 2 → |q| ≤ 2 → |p * q| ≤ 4 := fun {p q} hp hp2 hq => by
    rw [abs_mul, abs_of_nonneg hp]
    nlinarith [abs_nonneg q]
  have e1 := mul_le_mul_of_nonneg_right (habs ha0 hla2 hlbabs) hu0
  have e2 := mul_le_mul_of_nonneg_right (habs (by linarith) hha2 hlbabs) hu0
  have e3 := mul_le_mul_of_nonneg_right (habs ha0 hla2 hhbabs) hu0
  have e4 := mul_le_mul_of_nonneg_right (habs (by linarith) hha2 hhbabs) hu0
  have hcorner : ha' * (hb' - lb) + (ha' - la) * |lb| ≤ 2 * (δ + ε) := by
    have t1 : ha' * (hb' - lb) ≤ (1 + δ) * ε :=
      mul_le_mul (by linarith) hb3 (by linarith) (by linarith)
    have hlb1 : |lb| ≤ 1 + ε := abs_le.mpr ⟨by linarith, by linarith⟩
    have t2 : (ha' - la) * |lb| ≤ δ * (1 + ε) :=
      mul_le_mul ha3 hlb1 (abs_nonneg _) hδ0
    nlinarith [mul_nonneg hδ0 hε0, mul_le_mul hδ hε hε0 (by norm_num : (0 : ℝ) ≤ 1)]
  have hlh : lb ≤ hb' := by linarith
  have hlh' : la ≤ ha' := by linarith
  have c31 := corner_sub_le (a := la) (a' := la) (la := la) (ha := ha') le_rfl hlh' le_rfl hlh'
    hlh
  have c32 := corner_sub_le (a := la) (a' := ha') (la := la) (ha := ha') le_rfl hlh' hlh' le_rfl
    hlh
  have c41 := corner_sub_le (a := ha') (a' := la) (la := la) (ha := ha') hlh' le_rfl le_rfl hlh'
    hlh
  have c42 := corner_sub_le (a := ha') (a' := ha') (la := la) (ha := ha') hlh' le_rfl hlh' le_rfl
    hlh
  refine ⟨min r1 r2, max r3 r4, toVal_minOf hr1 hr2, toVal_maxOf hr3 hr4, ?_, ?_, ?_⟩
  · rcases le_or_gt 0 lb with h | h
    · calc min r1 r2 ≤ r1 := min_le_left _ _
        _ ≤ la * lb := hr1a
        _ ≤ x * lb := mul_le_mul_of_nonneg_right ha1 h
        _ ≤ x * y := mul_le_mul_of_nonneg_left hb1 (by linarith)
    · calc min r1 r2 ≤ r2 := min_le_right _ _
        _ ≤ ha' * lb := hr2a
        _ ≤ x * lb := mul_le_mul_of_nonpos_right ha2 h.le
        _ ≤ x * y := mul_le_mul_of_nonneg_left hb1 (by linarith)
  · rcases le_or_gt 0 hb' with h | h
    · calc x * y ≤ x * hb' := mul_le_mul_of_nonneg_left hb2 (by linarith)
        _ ≤ ha' * hb' := mul_le_mul_of_nonneg_right ha2 h
        _ ≤ r4 := hr4a
        _ ≤ max r3 r4 := le_max_right _ _
    · calc x * y ≤ x * hb' := mul_le_mul_of_nonneg_left hb2 (by linarith)
        _ ≤ la * hb' := mul_le_mul_of_nonpos_right ha1 h.le
        _ ≤ r3 := hr3a
        _ ≤ max r3 r4 := le_max_left _ _
  · rw [sub_le_iff_le_add]
    refine max_le ?_ ?_
    · rcases min_choice r1 r2 with h | h <;> rw [h] <;> linarith
    · rcases min_choice r1 r2 with h | h <;> rw [h] <;> linarith

/-- The width of the tail of the joint bracket. -/
theorem sinCosTail_spec {sc : Encl × Encl} {E : AzFloat} {θ δ Ev t : ℝ}
    (hs : IsEncl0W sc.1 (Real.sin θ) δ) (hc : IsEncl0W sc.2 (Real.cos θ) δ) (hθ0 : 0 ≤ θ)
    (hθ : 4 * θ ≤ Real.pi) (hδ : δ ≤ 1 / 10 ^ 6) (hE : E.toVal = some (Ev : EReal))
    (hEv0 : 0 ≤ Ev) (hEvs : Ev ≤ 1 / 128) (ht : |t - 8 * θ| ≤ Ev) {V : ℕ} (hV : 64 ≤ V) :
    IsEnclW (sinCosTail sc E V).1 (Real.sin t)
        (288 * δ + 4528 * (1 / 2 : ℝ) ^ V + 2 * Ev) ∧
      IsEnclW (sinCosTail sc E V).2 (Real.cos t)
        (288 * δ + 4528 * (1 / 2 : ℝ) ^ V + 2 * Ev) := by
  have : NeZero V := ⟨by omega⟩
  set u := (1 / 2 : ℝ) ^ V with hu
  have hu0 : 0 ≤ u := by positivity
  have hus : u ≤ 1 / 10 ^ 18 := half_pow_small hV
  have hδ0 := hs.width_nonneg
  have hpi := Real.pi_gt_three
  have hδδ : δ * δ ≤ δ := by nlinarith
  -- 2θ
  have hs1 := Real.sin_le_one θ
  have hc1 := Real.cos_le_one θ
  have hm2 := (hs.mul hc hs1 hc1 (by linarith) (by linarith) hV).toW
  rw [← hu] at hm2
  have hS2' := enclDouble_spec hm2
  rw [← mul_assoc, ← Real.sin_two_mul] at hS2'
  have hsin2 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hcos2 : 0 ≤ Real.cos (2 * θ) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  set δ₁ := 6 * δ + 80 * u with hδ₁
  have hS2 : IsEncl0W (enclClamp0 (enclDouble (Encl.mul V sc.1 sc.2))) (Real.sin (2 * θ)) δ₁ :=
    (enclClamp0_spec hS2' hsin2).mono (by rw [hδ₁]; linarith)
  have hC2' := cosDouble_spec hc hc1 (by linarith) hV
  rw [← hu, ← Real.cos_two_mul] at hC2'
  have hC2 : IsEncl0W (enclClamp0 (cosDouble V sc.2)) (Real.cos (2 * θ)) δ₁ :=
    enclClamp0_spec hC2' hcos2
  have hδ₁s : δ₁ ≤ 1 / 10 ^ 5 := by rw [hδ₁]; linarith
  have hδ₁0 : 0 ≤ δ₁ := by rw [hδ₁]; linarith
  have hδδ₁ : δ₁ * δ₁ ≤ δ₁ := by nlinarith
  -- 4θ
  have hm4 := (hS2.mul hC2 (Real.sin_le_one _) (Real.cos_le_one _) (by linarith) (by linarith)
    hV).toW
  rw [← hu] at hm4
  have hS4' := enclDouble_spec hm4
  rw [← mul_assoc, ← Real.sin_two_mul, show 2 * (2 * θ) = 4 * θ by ring] at hS4'
  have hsin4 : 0 ≤ Real.sin (4 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) hθ
  set δ₂ := 6 * δ₁ + 80 * u with hδ₂
  have hS4 : IsEncl0W (enclClamp0 (enclDouble (Encl.mul V
      (enclClamp0 (enclDouble (Encl.mul V sc.1 sc.2))) (enclClamp0 (cosDouble V sc.2)))))
      (Real.sin (4 * θ)) δ₂ :=
    (enclClamp0_spec hS4' hsin4).mono (by rw [hδ₂]; linarith)
  have hC4 := cosDouble_spec hC2 (Real.cos_le_one _) (by linarith) hV
  rw [← hu, ← Real.cos_two_mul, show 2 * (2 * θ) = 4 * θ by ring, ← hδ₂] at hC4
  have hδ₂s : δ₂ ≤ 1 / 10 ^ 4 := by rw [hδ₂]; linarith
  have hδ₂0 : 0 ≤ δ₂ := by rw [hδ₂]; linarith
  -- 8θ
  have hm8 := enclMulNonnegSigned_spec hS4 hC4 (Real.sin_le_one _) (Real.abs_cos_le_one _)
    (by linarith) (by linarith) hV
  rw [← hu] at hm8
  have hS8 := enclDouble_spec hm8
  rw [← mul_assoc, ← Real.sin_two_mul, show 2 * (4 * θ) = 8 * θ by ring] at hS8
  have hC8 := cosDouble_spec (enclAbs_spec hC4) (Real.abs_cos_le_one _) (by linarith) hV
  rw [← hu, sq_abs, ← Real.cos_two_mul, show 2 * (4 * θ) = 8 * θ by ring] at hC8
  -- the widening
  have hEe : IsEncl0W (Encl.exact E) Ev 0 := isEncl0W_exact hE hEv0
  have hzs : |Real.sin t - Real.sin (8 * θ)| ≤ Ev := (Real.abs_sin_sub_sin_le _ _).trans ht
  have hzc : |Real.cos t - Real.cos (8 * θ)| ≤ Ev := (Real.abs_cos_sub_cos_le _ _).trans ht
  have hfs := hS8.widen0 (M := 1) hEe hzs (Real.abs_sin_le_one _) (by linarith) (by linarith)
    (by norm_num) hV
  have hfc := hC8.widen0 (M := 1) hEe hzc (Real.abs_cos_le_one _) (by linarith) (by linarith)
    (by norm_num) hV
  rw [← hu] at hfs hfc
  simp only [sinCosTail]
  exact ⟨hfs.mono (by rw [hδ₂, hδ₁]; linarith), hfc.mono (by rw [hδ₂, hδ₁]; linarith)⟩

/-! ### The joint bracket -/

/-- The width of `sinCosBracket` at the series precision `V`. -/
noncomputable def sinCosEpsW (V : ℕ) : ℝ :=
  85248 * (((V : ℝ) + 4) * (1 / 2 : ℝ) ^ V) + 4658 * (1 / 2 : ℝ) ^ V

/-- The width of `sinCosBracket x ex w` (it does not depend on the exponent: the reduction
precision absorbs it). -/
noncomputable def sinCosEps (_ex : AzInt) (w : ℕ) : ℝ := sinCosEpsW (w + 12)

set_option maxHeartbeats 1600000 in
/-- **`sinCosBracket` encloses `sin |x|` and `cos x`** for a float `x` with `|x| < 2^ex`, at Ziv
level `w ≥ 64`, with widths at most `sinCosEps ex w`. -/
theorem sinCosBracket_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) {ex : AzInt}
    (hex : |xv| < (2 : ℝ) ^ ex.toInt) {w : ℕ} (hw : 64 ≤ w) :
    IsEnclW (sinCosBracket x ex w).1 (Real.sin |xv|) (sinCosEps ex w) ∧
      IsEnclW (sinCosBracket x ex w).2 (Real.cos xv) (sinCosEps ex w) := by
  have hW64 : 64 ≤ cosWork ex w := by unfold cosWork; omega
  have hV64 : 64 ≤ w + 12 := by omega
  have hexu := two_zpow_mul_half_pow_cosWork ex w
  simp only [sinCosBracket, sinCosReduce]
  set W := cosWork ex w with hWdef
  have : NeZero W := ⟨by omega⟩
  have : NeZero (64 : ℕ) := ⟨by norm_num⟩
  have : NeZero (w + 12) := ⟨by omega⟩
  set P := piBracket W with hP
  set y := P.1 <<< AzInt.ofInt 1 with hy
  set r := remExact x.abs y with hr
  set u := (1 / 2 : ℝ) ^ W with hu
  set uV := (1 / 2 : ℝ) ^ (w + 12) with huV
  have hu0 : 0 ≤ u := by positivity
  have huV0 : 0 ≤ uV := by positivity
  have hus : u ≤ 1 / 10 ^ 18 := half_pow_small hW64
  have huVs : uV ≤ 1 / 10 ^ 18 := half_pow_small hV64
  have huuV : u ≤ uV :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by rw [hWdef]; unfold cosWork; omega)
  have hex' : |xv| ≤ 2 ^ ex.toInt := hex.le
  have hx0 := abs_nonneg xv
  have hpi3 := Real.pi_gt_three
  have hpi4 := Real.pi_le_four
  -- π
  obtain ⟨lv, hv, hlv, hhv, hlv0, hlvπ, hπhv, hwid⟩ := piBracket_spec_width hW64
  rw [← hu] at hwid
  have hlv1 : 1 ≤ lv := by linarith
  have hlv' : P.1.toVal = some (lv : EReal) := hlv
  have hhv' : P.2.toVal = some (hv : EReal) := hhv
  have hyv : y.toVal = some ((2 * lv : ℝ) : EReal) := toVal_shiftLeft_one hlv'
  have h2lv : (0 : ℝ) < 2 * lv := by linarith
  -- the remainder
  have habs : x.abs.toVal = some ((|xv| : ℝ) : EReal) := by
    rw [toVal_abs, hx, Option.map_some, ← EReal.coe_neg]
    congr 1
  have hq0 : (0 : ℝ) ≤ |xv| / (2 * lv) := by positivity
  set k : ℤ := ⌊|xv| / (2 * lv)⌋ with hk
  have hrv : r.toVal = some ((|xv| - 2 * lv * k : ℝ) : EReal) := by
    rw [hr, toVal_remExact, habs, hyv, Option.bind_some, Option.bind_some,
      Spec.rem_coe_coe _ _ h2lv.ne', toInt_round_down, ite_eq_left hq0]
  have hk0 : (0 : ℝ) ≤ k := by exact_mod_cast Int.floor_nonneg.mpr hq0
  have hkle : (k : ℝ) ≤ |xv| / (2 * lv) := Int.floor_le _
  have hkgt : |xv| / (2 * lv) < k + 1 := Int.lt_floor_add_one _
  set rv := |xv| - 2 * lv * k with hrvdef
  have hrv0 : 0 ≤ rv := by
    have := (le_div_iff₀ h2lv).mp hkle; linarith
  have hrvlt : rv < 2 * lv := by
    have := (div_lt_iff₀ h2lv).mp hkgt; linarith
  -- the error of the reduction
  obtain ⟨d, hd, hdc⟩ := subCeiling_err hhv' hlv' 64 (by linarith)
  have hd0 : 0 ≤ d := by linarith [hdc.ge]
  obtain ⟨Ev, hEv, hEvc⟩ := mulCeiling_err habs hd 64 (mul_nonneg hx0 hd0)
  have h64 : (1 / 2 : ℝ) ^ 64 ≤ 1 / 2 := by norm_num
  have hd1 : d ≤ 2 * (hv - lv) := by
    have := hdc.le
    nlinarith [mul_le_mul_of_nonneg_left h64 (by linarith : 0 ≤ hv - lv)]
  have hd16 : d ≤ 16 * u := by linarith
  have hEv1 : Ev ≤ 2 * (|xv| * d) := by
    have := hEvc.le
    nlinarith [mul_le_mul_of_nonneg_left h64 (mul_nonneg hx0 hd0)]
  have hEv0 : 0 ≤ Ev := le_trans (mul_nonneg hx0 hd0) hEvc.ge
  have hEvle : Ev ≤ 32 * uV := by
    have h1 : |xv| * d ≤ |xv| * (16 * u) := mul_le_mul_of_nonneg_left hd16 hx0
    have h2 : |xv| * u ≤ (2 : ℝ) ^ ex.toInt * u := mul_le_mul_of_nonneg_right hex' hu0
    nlinarith
  have hk2 : 2 * (k : ℝ) ≤ |xv| := by
    have := (le_div_iff₀ h2lv).mp hkle
    nlinarith [mul_le_mul_of_nonneg_left hlv1 hk0]
  have hkπ0 : 0 ≤ 2 * k * (Real.pi - lv) := mul_nonneg (by linarith) (by linarith)
  have hkπ : 2 * k * (Real.pi - lv) ≤ Ev :=
    calc 2 * k * (Real.pi - lv) ≤ |xv| * (Real.pi - lv) :=
          mul_le_mul_of_nonneg_right hk2 (by linarith)
      _ ≤ |xv| * (hv - lv) := mul_le_mul_of_nonneg_left (by linarith) hx0
      _ ≤ |xv| * d := mul_le_mul_of_nonneg_left hdc.ge hx0
      _ ≤ Ev := hEvc.ge
  -- the true reduction
  set rt := rv - 2 * k * (Real.pi - lv) with hrt
  have hcos : Real.cos xv = Real.cos rt := by
    rw [← Real.cos_abs (x := xv), show |xv| = rt + k * (2 * Real.pi) by rw [hrt, hrvdef]; ring,
      Real.cos_add_int_mul_two_pi]
  have hsin : Real.sin |xv| = Real.sin rt := by
    rw [show |xv| = rt + k * (2 * Real.pi) by rw [hrt, hrvdef]; ring,
      Real.sin_add_int_mul_two_pi]
  -- the fixed-point number
  have hT3 : w + 12 + 4 - 3 = w + 13 := by omega
  rw [hT3]
  obtain ⟨hM1, hM2⟩ := floorScaled_spec hrv (w + 13)
  rw [abs_of_nonneg hrv0] at hM1 hM2
  set M := floorScaled r (w + 13) with hMdef
  have hpowT : (2 : ℝ) ^ (w + 12 + 4) = 8 * 2 ^ (w + 13) := by
    rw [show w + 12 + 4 = (w + 13) + 3 by omega, pow_add]
    ring
  have hq : (0 : ℝ) < 2 ^ (w + 13) := by positivity
  have huV2 : uV * 2 ^ (w + 12) = 1 := by
    rw [huV, ← mul_pow]
    norm_num
  have hquV : (1 : ℝ) / 2 ^ (w + 13) = uV / 2 := by
    rw [div_eq_div_iff hq.ne' two_ne_zero, pow_succ]
    linarith
  set θ := (M.toNat : ℝ) / 2 ^ (w + 12 + 4) with hθ
  have h8θ : 8 * θ = (M.toNat : ℝ) / 2 ^ (w + 13) := by
    rw [hθ, hpowT]; field_simp
  have hθ0 : 0 ≤ θ := by positivity
  have h8le : 8 * θ ≤ rv := by
    rw [h8θ, div_le_iff₀ hq]; exact hM1
  have h8gt : rv < 8 * θ + uV / 2 := by
    rw [h8θ, ← hquV, ← add_div, lt_div_iff₀ hq]; exact hM2
  have hMlt : M.toNat < 2 ^ (w + 12 + 4) := by
    have : (M.toNat : ℝ) < 2 ^ (w + 12 + 4) := by
      rw [hpowT]
      calc (M.toNat : ℝ) ≤ rv * 2 ^ (w + 13) := hM1
        _ < 8 * 2 ^ (w + 13) := mul_lt_mul_of_pos_right (by linarith) hq
    exact_mod_cast this
  -- the slack `E₂`
  have h8 : (1 : ℝ) * (2 : ℝ) ^ ((3 : ℤ) - ((w + 12 + 4 : ℕ) : ℤ)) = uV / 2 := by
    rw [one_mul, zpow_sub₀ two_ne_zero, zpow_natCast, pow_add,
      div_eq_div_iff (by positivity) two_ne_zero]
    norm_num
    linarith
  have ht8 : (one <<< AzInt.ofInt (3 - ((w + 12 + 4 : ℕ) : Int))).toVal
      = some ((uV / 2 : ℝ) : EReal) := by
    rw [toVal_shiftLeft_of_toVal toVal_one', AzInt.toInt_ofInt, h8]
  obtain ⟨E2v, hE2, hE2c⟩ := addCeiling_err hEv ht8 64 (by linarith)
  have hE2le : E2v ≤ 2 * (Ev + uV / 2) := by
    have h1 := hE2c.le
    have h2 := mul_le_mul_of_nonneg_left h64 (by linarith : 0 ≤ Ev + uV / 2)
    linarith
  have hE2ge : Ev + uV / 2 ≤ E2v := hE2c.ge
  have hE20 : 0 ≤ E2v := by linarith
  have hE2b : E2v ≤ 65 * uV := by linarith
  have hE2s : E2v ≤ 1 / 128 := by linarith
  have hts : |rt - 8 * θ| ≤ E2v := by
    rw [abs_le]; constructor <;> linarith
  -- the rotation recurrence
  have hTu : (((w + 12 + 4 : ℕ) : ℝ)) * uV ≤ 1 / 10 ^ 16 := by
    have h := add_nine_mul_half_pow_le hV64
    rw [← huV] at h
    push_cast at h ⊢
    have : (73 : ℝ) * (1 / 2 : ℝ) ^ 64 ≤ 1 / 10 ^ 16 := by norm_num
    linarith
  obtain ⟨hfs, hfc⟩ := sinCosFix_spec M hV64 (by omega : 0 < w + 12 + 4) hMlt
    (by rw [← huV]; linarith)
  rw [← huV, ← hθ] at hfs hfc
  obtain ⟨hs, hc⟩ := sinCosTail_spec hfs hfc hθ0 (by linarith) (by linarith) hE2 hE20 hE2s hts
    hV64
  rw [← huV, ← hsin] at hs
  rw [← huV, ← hcos] at hc
  have hwfin : 288 * (296 * ((w + 12 + 4 : ℕ) : ℝ) * uV) + 4528 * uV + 2 * E2v
      ≤ sinCosEps ex w := by
    unfold sinCosEps sinCosEpsW
    rw [← huV]
    push_cast
    linarith
  exact ⟨hs.mono hwfin, hc.mono hwfin⟩

/-- `sinCosEpsW V → 0` as `V → ∞`. -/
theorem tendsto_sinCosEpsW : Filter.Tendsto sinCosEpsW Filter.atTop (nhds 0) := by
  have h1 := tendsto_self_mul_const_pow_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have h := (h1.const_mul 85248).add (h2.const_mul (85248 * 4 + 4658))
  simp only [mul_zero, add_zero] at h
  refine h.congr fun V => ?_
  simp only [sinCosEpsW]
  ring

/-- `sinCosEps ex w → 0` as `w → ∞`. -/
theorem tendsto_sinCosEps (ex : AzInt) : Filter.Tendsto (sinCosEps ex) Filter.atTop (nhds 0) :=
  tendsto_sinCosEpsW.comp (Filter.tendsto_add_atTop_nat 12)

/-- The sine half of `sinCosApprox neg`: `Roundable`s bracketing `± sin |x|`. -/
theorem sinCosApprox_spec_sin (neg : Bool) {x : AzFloat} {xv : ℝ}
    (hx : x.toVal = some (xv : EReal)) {ex : AzInt} (hex : |xv| < (2 : ℝ) ^ ex.toInt) {w : ℕ}
    (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, Rounds (sinCosApprox neg x ex w).1.1 lv ∧
      Rounds (sinCosApprox neg x ex w).1.2 hv ∧
      lv ≤ (if neg then -1 else 1) * Real.sin |xv| ∧
      (if neg then -1 else 1) * Real.sin |xv| ≤ hv ∧ hv - lv ≤ sinCosEps ex w := by
  obtain ⟨⟨lo, hi, hlo, hhi, h1, h2, hwid⟩, -⟩ := sinCosBracket_spec hx hex hw
  simp only [sinCosApprox]
  cases neg with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    have hR1 := rounds_setPrecRound (isFinite_of_toVal_coe hlo)
    rw [fval_of_toVal_coe hlo] at hR1
    have hR2 := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
    rw [fval_of_toVal_coe hhi] at hR2
    exact ⟨lo, hi, hR1, hR2, h1, h2, hwid⟩
  | true =>
    simp only [↓reduceIte, neg_one_mul]
    have hnlo : (-(sinCosBracket x ex w).1.2).toVal = some ((-hi : ℝ) : EReal) := by
      rw [toVal_neg, hhi, Option.map_some, EReal.coe_neg]
    have hnhi : (-(sinCosBracket x ex w).1.1).toVal = some ((-lo : ℝ) : EReal) := by
      rw [toVal_neg, hlo, Option.map_some, EReal.coe_neg]
    have hR3 := rounds_setPrecRound (isFinite_of_toVal_coe hnlo)
    rw [fval_of_toVal_coe hnlo] at hR3
    have hR4 := rounds_setPrecRound (isFinite_of_toVal_coe hnhi)
    rw [fval_of_toVal_coe hnhi] at hR4
    exact ⟨-hi, -lo, hR3, hR4, by linarith, by linarith, by linarith⟩

/-- The cosine half of `sinCosApprox neg`: `Roundable`s bracketing `cos x`. -/
theorem sinCosApprox_spec_cos (neg : Bool) {x : AzFloat} {xv : ℝ}
    (hx : x.toVal = some (xv : EReal)) {ex : AzInt} (hex : |xv| < (2 : ℝ) ^ ex.toInt) {w : ℕ}
    (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, Rounds (sinCosApprox neg x ex w).2.1 lv ∧
      Rounds (sinCosApprox neg x ex w).2.2 hv ∧
      lv ≤ Real.cos xv ∧ Real.cos xv ≤ hv ∧ hv - lv ≤ sinCosEps ex w := by
  obtain ⟨-, lo, hi, hlo, hhi, h1, h2, hwid⟩ := sinCosBracket_spec hx hex hw
  have hR1 := rounds_setPrecRound (isFinite_of_toVal_coe hlo)
  rw [fval_of_toVal_coe hlo] at hR1
  have hR2 := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
  rw [fval_of_toVal_coe hhi] at hR2
  simp only [sinCosApprox]
  exact ⟨lo, hi, hR1, hR2, h1, h2, hwid⟩

/-- The joint Ziv certificate for `sin x` and `cos x`, `x` a nonzero finite float of sign
`¬ neg`. -/
theorem sinCosApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (neg : Bool)
    {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (hx0 : xv ≠ 0)
    (hneg : neg = true ↔ xv < 0) {ex : AzInt} (hex : |xv| < (2 : ℝ) ^ ex.toInt) (w₀ : ℕ)
    (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible₂ (sinCosApprox neg x ex (w₀ * 2 ^ f)) p mode).isSome = true := by
  have hval := sin_eq_of_neg_iff hneg
  refine exists_isSome₂_of_irrational_threshold p mode (sinCosApprox neg x ex)
    (v₁ := (if neg then -1 else 1) * Real.sin |xv|) (v₂ := Real.cos xv) ?_
    (irrational_cos_of_toVal hx hx0) (sinCosEps ex) (sinCosEps ex) (tendsto_sinCosEps ex)
    (tendsto_sinCosEps ex) 64 (fun _ hw => sinCosApprox_spec_sin neg hx hex hw)
    (fun _ hw => sinCosApprox_spec_cos neg hx hex hw) w₀ hw₀
  rw [← hval]
  exact irrational_sin_of_toVal hx hx0

/-! ### The brackets of `sin` and `cos` alone -/

/-- The width of `sinBracket x ex w`. -/
noncomputable def sinEps (ex : AzInt) (w : ℕ) : ℝ := sinCosEps ex w

/-- The width of `cosBracket x ex w`. -/
noncomputable def cosEps (ex : AzInt) (w : ℕ) : ℝ := sinCosEps ex w

theorem tendsto_sinEps (ex : AzInt) : Filter.Tendsto (sinEps ex) Filter.atTop (nhds 0) :=
  tendsto_sinCosEps ex

theorem tendsto_cosEps (ex : AzInt) : Filter.Tendsto (cosEps ex) Filter.atTop (nhds 0) :=
  tendsto_sinCosEps ex

/-- `sinCosEps ex w ≤ 1` from `w = 64` on. -/
theorem sinCosEps_le_one (ex : AzInt) {w : ℕ} (hw : 64 ≤ w) : sinCosEps ex w ≤ 1 := by
  have hV : 64 ≤ w + 12 := by omega
  have h := add_nine_mul_half_pow_le hV
  have h3 := half_pow_small hV
  have h0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (w + 12) := by positivity
  have : (73 : ℝ) * (1 / 2 : ℝ) ^ 64 ≤ 1 / 10 ^ 16 := by norm_num
  unfold sinCosEps sinCosEpsW
  linarith

theorem sinEps_le_one (ex : AzInt) {w : ℕ} (hw : 64 ≤ w) : sinEps ex w ≤ 1 :=
  sinCosEps_le_one ex hw

theorem cosEps_le_one (ex : AzInt) {w : ℕ} (hw : 64 ≤ w) : cosEps ex w ≤ 1 :=
  sinCosEps_le_one ex hw

/-- **`sinBracket` encloses `sin |x|`** for a float `x` with `|x| < 2^ex`, at Ziv level
`w ≥ 64`, with width at most `sinEps ex w`. -/
theorem sinBracket_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) {ex : AzInt}
    (hex : |xv| < (2 : ℝ) ^ ex.toInt) {w : ℕ} (hw : 64 ≤ w) :
    ∃ lo hi : ℝ, (sinBracket x ex w).1.toVal = some (lo : EReal) ∧
      (sinBracket x ex w).2.toVal = some (hi : EReal) ∧
      lo ≤ Real.sin |xv| ∧ Real.sin |xv| ≤ hi ∧ hi - lo ≤ sinEps ex w := by
  rw [sinBracket_eq]
  exact (sinCosBracket_spec hx hex hw).1

/-- **`cosBracket` encloses `cos x`** for a float `x` with `|x| < 2^ex`, at Ziv level
`w ≥ 64`, with width at most `cosEps ex w`. -/
theorem cosBracket_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) {ex : AzInt}
    (hex : |xv| < (2 : ℝ) ^ ex.toInt) {w : ℕ} (hw : 64 ≤ w) :
    ∃ lo hi : ℝ, (cosBracket x ex w).1.toVal = some (lo : EReal) ∧
      (cosBracket x ex w).2.toVal = some (hi : EReal) ∧
      lo ≤ Real.cos xv ∧ Real.cos xv ≤ hi ∧ hi - lo ≤ cosEps ex w := by
  rw [cosBracket_eq]
  exact (sinCosBracket_spec hx hex hw).2

/-- `sinApprox neg` as a pair of `Roundable`s bracketing `± sin |x|`. -/
theorem sinApprox_spec (neg : Bool) {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    {ex : AzInt} (hex : |xv| < (2 : ℝ) ^ ex.toInt) {w : ℕ} (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, Rounds (sinApprox neg x ex w).1 lv ∧ Rounds (sinApprox neg x ex w).2 hv ∧
      lv ≤ (if neg then -1 else 1) * Real.sin |xv| ∧
      (if neg then -1 else 1) * Real.sin |xv| ≤ hv ∧ hv - lv ≤ sinEps ex w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := sinBracket_spec hx hex hw
  simp only [sinApprox]
  cases neg with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    have hR1 := rounds_setPrecRound (isFinite_of_toVal_coe hlo)
    rw [fval_of_toVal_coe hlo] at hR1
    have hR2 := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
    rw [fval_of_toVal_coe hhi] at hR2
    exact ⟨lo, hi, hR1, hR2, h1, h2, hwid⟩
  | true =>
    simp only [↓reduceIte, neg_one_mul]
    have hnlo : (-(sinBracket x ex w).2).toVal = some ((-hi : ℝ) : EReal) := by
      rw [toVal_neg, hhi, Option.map_some, EReal.coe_neg]
    have hnhi : (-(sinBracket x ex w).1).toVal = some ((-lo : ℝ) : EReal) := by
      rw [toVal_neg, hlo, Option.map_some, EReal.coe_neg]
    have hR3 := rounds_setPrecRound (isFinite_of_toVal_coe hnlo)
    rw [fval_of_toVal_coe hnlo] at hR3
    have hR4 := rounds_setPrecRound (isFinite_of_toVal_coe hnhi)
    rw [fval_of_toVal_coe hnhi] at hR4
    exact ⟨-hi, -lo, hR3, hR4, by linarith, by linarith, by linarith⟩

/-- The Ziv certificate for `sin x`, `x` a nonzero finite float of sign `¬ neg`. -/
theorem sinApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (neg : Bool)
    {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (hx0 : xv ≠ 0)
    (hneg : neg = true ↔ xv < 0) {ex : AzInt} (hex : |xv| < (2 : ℝ) ^ ex.toInt) (w₀ : ℕ)
    (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (sinApprox neg x ex (w₀ * 2 ^ f)).1
      (sinApprox neg x ex (w₀ * 2 ^ f)).2 p mode).isSome = true := by
  have hval := sin_eq_of_neg_iff hneg
  refine exists_isSome_of_irrational_threshold p mode (sinApprox neg x ex)
    (v := (if neg then -1 else 1) * Real.sin |xv|) ?_ (sinEps ex) (tendsto_sinEps ex) 64
    (fun _ hw => sinApprox_spec neg hx hex hw) w₀ hw₀
  rw [← hval]
  exact irrational_sin_of_toVal hx hx0

/-- `cosApprox` as a pair of `Roundable`s bracketing `cos x`. -/
theorem cosApprox_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) {ex : AzInt}
    (hex : |xv| < (2 : ℝ) ^ ex.toInt) {w : ℕ} (hw : 64 ≤ w) :
    ∃ lv hv : ℝ, Rounds (cosApprox x ex w).1 lv ∧ Rounds (cosApprox x ex w).2 hv ∧
      lv ≤ Real.cos xv ∧ Real.cos xv ≤ hv ∧ hv - lv ≤ cosEps ex w := by
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := cosBracket_spec hx hex hw
  have hR1 := rounds_setPrecRound (isFinite_of_toVal_coe hlo)
  rw [fval_of_toVal_coe hlo] at hR1
  have hR2 := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
  rw [fval_of_toVal_coe hhi] at hR2
  simp only [cosApprox]
  exact ⟨lo, hi, hR1, hR2, h1, h2, hwid⟩

/-- The Ziv certificate for `cos x`, `x` a nonzero finite float. -/
theorem cosApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) {x : AzFloat} {xv : ℝ}
    (hx : x.toVal = some (xv : EReal)) (hx0 : xv ≠ 0) {ex : AzInt}
    (hex : |xv| < (2 : ℝ) ^ ex.toInt) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (cosApprox x ex (w₀ * 2 ^ f)).1 (cosApprox x ex (w₀ * 2 ^ f)).2 p
      mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (cosApprox x ex) (irrational_cos_of_toVal hx hx0)
    (cosEps ex) (tendsto_cosEps ex) 64 (fun _ hw => cosApprox_spec hx hex hw) w₀ hw₀

end Azurite.AzFloat
