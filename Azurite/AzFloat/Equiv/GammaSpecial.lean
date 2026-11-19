/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.GammaSpecial
import Azurite.AzFloat.Equiv.GammaConstants
import Azurite.AzFloat.Equiv.GammaBracket
import Azurite.AzNat.Equiv.SumProduct
import Azurite.AzNat.Equiv.Pow
import Azurite.AzNat.Equiv.Div.DivMod
import Azurite.AzNat.Equiv.Compare

/-!
# Equivalence: `Γ` at the denominators `2, 3, 4, 6` through the constants

* The closed forms: `gamma_three_quarters`, `gamma_two_thirds`, `gamma_one_sixth`,
  `gamma_five_sixths` (reflection and duplication), and the shifts `gamma_shift_pos`,
  `gamma_shift_neg` (recurrence).
* `gammaBaseEncl_spec`, `gammaSpecialEncl_spec`: the enclosures.
* `gammaSpecialFast?_eq_or`: the result of `gammaSpecialFast?` is the correctly rounded
  `Γ(± n/d)` (or its reciprocal), or `(nan, .eq)`.
-/

namespace Azurite.AzFloat

open Real Finset

/-! ### Closed forms -/

theorem gamma_three_quarters : Real.Gamma (3 / 4) = π * √2 / Real.Gamma (1 / 4) := by
  have hR := Real.Gamma_mul_Gamma_one_sub (1 / 4)
  rw [show π * (1 / 4 : ℝ) = π / 4 by ring, Real.sin_pi_div_four,
    show (1 - 1 / 4 : ℝ) = 3 / 4 by norm_num] at hR
  have hx : 0 < Real.Gamma (1 / 4) := Real.Gamma_pos_of_pos (by norm_num)
  have hs2 : (0 : ℝ) < √2 := by positivity
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [eq_div_iff hx.ne', mul_comm, hR]
  field_simp
  linarith

theorem gamma_two_thirds : Real.Gamma (2 / 3) = 2 * π / (√3 * Real.Gamma (1 / 3)) := by
  have hR := Real.Gamma_mul_Gamma_one_sub (1 / 3)
  rw [show π * (1 / 3 : ℝ) = π / 3 by ring, Real.sin_pi_div_three,
    show (1 - 1 / 3 : ℝ) = 2 / 3 by norm_num] at hR
  have hx : 0 < Real.Gamma (1 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  have hs3 : (0 : ℝ) < √3 := by positivity
  rw [eq_div_iff (mul_pos hs3 hx).ne']
  field_simp at hR
  linarith

theorem gamma_five_sixths : Real.Gamma (5 / 6) = 2 * π / Real.Gamma (1 / 6) := by
  have hR := Real.Gamma_mul_Gamma_one_sub (1 / 6)
  rw [show π * (1 / 6 : ℝ) = π / 6 by ring, Real.sin_pi_div_six,
    show (1 - 1 / 6 : ℝ) = 5 / 6 by norm_num] at hR
  have hx : 0 < Real.Gamma (1 / 6) := Real.Gamma_pos_of_pos (by norm_num)
  rw [eq_div_iff hx.ne', mul_comm, hR]
  ring

theorem gamma_one_sixth :
    Real.Gamma (1 / 6) = √3 * (Real.Gamma (1 / 3) * Real.Gamma (1 / 3)) / (realCbrt 2 * √π) := by
  have hD := Real.Gamma_mul_Gamma_add_half (1 / 6)
  rw [show (1 / 6 + 1 / 2 : ℝ) = 2 / 3 by norm_num,
    show (2 * (1 / 6) : ℝ) = 1 / 3 by norm_num,
    show (1 - 1 / 3 : ℝ) = 2 / 3 by norm_num] at hD
  set t : ℝ := (2 : ℝ) ^ (2 / 3 : ℝ) with ht
  have ht0 : 0 < t := by positivity
  have ht3 : t ^ 3 = 4 := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  set c := realCbrt 2 with hc
  have hc0 : 0 < c := realCbrt_pos (by norm_num)
  have hc3 : c ^ 3 = 2 := realCbrt_pow_three 2
  have htc : t * c = 2 := by
    have h8 : (t * c) ^ 3 = 2 ^ 3 := by rw [mul_pow, ht3, hc3]; norm_num
    exact (pow_left_inj₀ (by positivity) (by norm_num) (by norm_num)).mp h8
  have hB : 0 < Real.Gamma (1 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  have hz : 0 < Real.Gamma (2 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  have hsπ : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  have hππ : √π * √π = π := Real.mul_self_sqrt Real.pi_pos.le
  have hs3 : (0 : ℝ) < √3 := by positivity
  have h33 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h23 := gamma_two_thirds
  rw [eq_div_iff (mul_pos hs3 hB).ne'] at h23
  rw [eq_div_iff (mul_pos hc0 hsπ).ne']
  -- `Γ(1/6) Γ(2/3) = B t √π`, `Γ(2/3) √3 B = 2π`
  have e1 : Real.Gamma (1 / 6) * (c * √π) * (Real.Gamma (2 / 3) * (√3 * Real.Gamma (1 / 3)))
      = √3 * (Real.Gamma (1 / 3) * Real.Gamma (1 / 3))
        * (Real.Gamma (2 / 3) * (√3 * Real.Gamma (1 / 3))) := by
    calc Real.Gamma (1 / 6) * (c * √π) * (Real.Gamma (2 / 3) * (√3 * Real.Gamma (1 / 3)))
        = (Real.Gamma (1 / 6) * Real.Gamma (2 / 3)) * (c * √π * √3 * Real.Gamma (1 / 3)) := by
          ring
      _ = (Real.Gamma (1 / 3) * t * √π) * (c * √π * √3 * Real.Gamma (1 / 3)) := by rw [hD]
      _ = (t * c) * (√π * √π) * √3 * (Real.Gamma (1 / 3) * Real.Gamma (1 / 3)) := by ring
      _ = √3 * (Real.Gamma (1 / 3) * Real.Gamma (1 / 3)) * (2 * π) := by rw [htc, hππ]; ring
      _ = _ := by rw [h23]
  exact mul_right_cancel₀ (mul_pos hz (mul_pos hs3 hB)).ne' e1

/-! ### Integer shifts -/

theorem gamma_add_nat_prod {y : ℝ} (m : ℕ) (hy : ∀ i : ℕ, i < m → y + i ≠ 0) :
    Real.Gamma (y + m) = Real.Gamma y * ∏ i ∈ range m, (y + i) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [prod_range_succ, ← mul_assoc, ← ih fun i hi => hy i (by omega)]
    push_cast
    rw [← add_assoc, Real.Gamma_add_one (hy m (by omega)), mul_comm]

theorem gamma_shift_pos {r d : ℕ} (hr : 0 < r) (hd : 0 < d) (n : ℕ) :
    Real.Gamma ((n : ℝ) + (r : ℝ) / d)
      = Real.Gamma ((r : ℝ) / d) * (∏ j ∈ range n, ((r + j * d : ℕ) : ℝ)) / (d : ℝ) ^ n := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have h := gamma_add_nat_prod (y := (r : ℝ) / d) n fun i _ => by positivity
  have hi : ∀ i ∈ range n, (r : ℝ) / d + i = ((r + i * d : ℕ) : ℝ) / d := fun i _ => by
    push_cast
    field_simp
  rw [add_comm, h, mul_div_assoc, prod_congr rfl hi, prod_div_distrib, prod_const, card_range]

theorem gamma_shift_neg {r d : ℕ} (hr : 0 < r) (hrd : r < d) (n : ℕ) :
    Real.Gamma (-((n : ℝ) + (r : ℝ) / d))
      = (-1) ^ (n + 1) * (Real.Gamma (((d - r : ℕ) : ℝ) / d) * (d : ℝ) ^ (n + 1)
        / ∏ j ∈ range (n + 1), ((r + j * d : ℕ) : ℝ)) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hy : ∀ i : ℕ, i < n + 1 → -((n : ℝ) + (r : ℝ) / d) + i ≠ 0 := fun i hi => by
    have h1 : (i : ℝ) ≤ n := by exact_mod_cast (by omega : i ≤ n)
    have h2 : 0 < (r : ℝ) / d := by positivity
    linarith
  have h := gamma_add_nat_prod (n + 1) hy
  have hym : -((n : ℝ) + (r : ℝ) / d) + ((n + 1 : ℕ) : ℝ) = ((d - r : ℕ) : ℝ) / d := by
    rw [Nat.cast_sub hrd.le]
    push_cast
    field_simp
    ring
  have hi : ∀ i ∈ range (n + 1), -((n : ℝ) + (r : ℝ) / d) + i
      = -1 * (((r + (n + 1 - 1 - i) * d : ℕ) : ℝ) / d) := fun i hi => by
    have hin : i ≤ n := by have := mem_range.mp hi; omega
    rw [show n + 1 - 1 - i = n - i by omega]
    push_cast [Nat.cast_sub hin]
    field_simp
    ring
  rw [hym, prod_congr rfl hi, prod_mul_distrib, prod_const, card_range, prod_div_distrib,
    prod_const, card_range,
    prod_range_reflect (fun j => ((r + j * d : ℕ) : ℝ)) (n + 1)] at h
  have hP : (0 : ℝ) < ∏ j ∈ range (n + 1), ((r + j * d : ℕ) : ℝ) :=
    prod_pos fun j _ => by exact_mod_cast (by positivity : 0 < r + j * d)
  have hs : ((-1 : ℝ) ^ (n + 1)) * ((-1) ^ (n + 1)) = 1 := by rw [← mul_pow]; norm_num
  have hD : (0 : ℝ) < (d : ℝ) ^ (n + 1) := by positivity
  rw [h]
  generalize Real.Gamma (-((n : ℝ) + (r : ℝ) / d)) = G
  generalize (∏ j ∈ range (n + 1), ((r + j * d : ℕ) : ℝ)) = P at hP ⊢
  generalize ((d : ℝ) ^ (n + 1)) = D at hD ⊢
  generalize ((-1 : ℝ) ^ (n + 1)) = s at hs ⊢
  have e : P / D * D / P = 1 := by field_simp
  calc G = (s * s) * G * (P / D * D / P) := by rw [hs, e]; ring
    _ = _ := by ring

/-! ### The enclosures -/

theorem toNat_gammaAP (r d m : ℕ) : (gammaAP r d m).toNat = ∏ j ∈ range m, (r + j * d) := by
  unfold gammaAP
  rw [AzNat.toNat_product, List.map_map]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ih, prod_range_succ]
    simp [AzNat.toNat_ofNat]

theorem gammaOneQuarterEncl_pos {w : ℕ} (hw : 64 ≤ w) :
    IsEnclPos (gammaOneQuarterEncl w) (Real.Gamma (1 / 4)) := by
  obtain ⟨l, u, hl, hu, h1, h2⟩ := gammaOneQuarterEncl_spec hw
  unfold gammaOneQuarterEncl at hl hu ⊢
  dsimp only at hl hu ⊢
  have : NeZero (w + 32) := ⟨by omega⟩
  have hW : 2 ≤ w + 32 := by omega
  have hM := (enclosesPos_one.agm (w := w + 32) ((isEnclPos_nat (by norm_num : 0 < 2)).sqrt hW))
  have hT := (isEnclPos_nat (by norm_num : 0 < 2)).mul hW (enclosesPos_pi (w := w + 32) (by omega))
  obtain ⟨l', u', hl', hu', h0, -, -⟩ := ((hT.mul hW (hT.sqrt hW)).div hW hM).sqrt hW
  rw [hl, Option.some.injEq, EReal.coe_eq_coe_iff] at hl'
  exact ⟨l, u, hl, hu, hl' ▸ h0, h1, h2⟩

theorem gammaOneThirdEncl_pos {w : ℕ} (hw : 64 ≤ w) :
    IsEnclPos (gammaOneThirdEncl w) (Real.Gamma (1 / 3)) := by
  obtain ⟨l, u, hl, hu, h1, h2⟩ := gammaOneThirdEncl_spec hw
  unfold gammaOneThirdEncl at hl hu ⊢
  dsimp only at hl hu ⊢
  have : NeZero (w + 32) := ⟨by omega⟩
  have hW : 2 ≤ w + 32 := by omega
  have h3 := (isEnclPos_nat (by norm_num : 0 < 3))
  have hr := h3.sqrt hW
  have hA := ((hr.add hW h3.half.encloses0).half).sqrt hW
  have hM := hA.agm (w := w + 32) (hr.sqrt hW)
  have hP := enclosesPos_pi (w := w + 32) (by omega)
  have h2' := (isEnclPos_nat (by norm_num : 0 < 2))
  obtain ⟨l', u', hl', hu', h0, -, -⟩ :=
    (((h2'.mul hW (h2'.cbrt hW)).mul hW (hP.mul hW hP)).div hW hM).cbrt hW
  rw [hl, Option.some.injEq, EReal.coe_eq_coe_iff] at hl'
  exact ⟨l, u, hl, hu, hl' ▸ h0, h1, h2⟩

/-- **`gammaBaseEncl` encloses `Γ(r/d)`.** -/
theorem gammaBaseEncl_spec {r d : ℕ} (hd : d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 6) (hr : 0 < r)
    (hrd : r < d) (hc : Nat.Coprime r d ∨ 2 * r = d) {w : ℕ} (hw : 64 ≤ w) :
    IsEnclPos (gammaBaseEncl r d w) (Real.Gamma ((r : ℝ) / d)) := by
  have : NeZero (w + 32) := ⟨by omega⟩
  have hW : 2 ≤ w + 32 := by omega
  have hP := enclosesPos_pi (w := w + 32) (by omega)
  have h2 := isEnclPos_nat (by norm_num : 0 < 2)
  have h3 := isEnclPos_nat (by norm_num : 0 < 3)
  have hA := gammaOneQuarterEncl_pos hw
  have hB := gammaOneThirdEncl_pos hw
  have khalf : IsEnclPos (Encl.sqrt (w + 32) (Encl.pi (w + 32))) (Real.Gamma (1 / 2)) := by
    rw [Real.Gamma_one_half_eq]
    exact hP.sqrt hW
  have k34 : IsEnclPos (gammaBaseEncl 3 4 w) (Real.Gamma (3 / 4)) := by
    rw [gamma_three_quarters]
    exact (hP.mul hW (h2.sqrt hW)).div hW hA
  have k23 : IsEnclPos (gammaBaseEncl 2 3 w) (Real.Gamma (2 / 3)) := by
    rw [gamma_two_thirds]
    exact (h2.mul hW hP).div hW ((h3.sqrt hW).mul hW hB)
  have k16 : IsEnclPos (gammaBaseEncl 1 6 w) (Real.Gamma (1 / 6)) := by
    rw [gamma_one_sixth]
    exact ((h3.sqrt hW).mul hW (hB.mul hW hB)).div hW ((h2.cbrt hW).mul hW (hP.sqrt hW))
  have k56 : IsEnclPos (gammaBaseEncl 5 6 w) (Real.Gamma (5 / 6)) := by
    rw [gamma_five_sixths]
    exact (h2.mul hW hP).div hW k16
  rcases hd with rfl | rfl | rfl | rfl
  · obtain rfl : r = 1 := by omega
    convert khalf using 2 <;> first | rfl | norm_num
  · interval_cases r
    · convert hB using 2 <;> first | rfl | norm_num
    · convert k23 using 2
  · interval_cases r
    · convert hA using 2 <;> first | rfl | norm_num
    · convert khalf using 2 <;> first | rfl | norm_num
    · convert k34 using 2
  · interval_cases r
    · convert k16 using 2
      norm_num
    · exact absurd hc (by norm_num)
    · convert khalf using 2 <;> first | rfl | norm_num
    · exact absurd hc (by norm_num)
    · convert k56 using 2

/-- **`gammaSpecialEncl` encloses `g · num / den` or its reciprocal.** -/
theorem gammaSpecialEncl_spec (recip : Bool) {r d : ℕ} {num den : AzFloat} {nv dv g : ℝ}
    {w : ℕ} (hg : IsEnclPos (gammaBaseEncl r d w) g)
    (hn : num.toVal = some (nv : EReal)) (hn0 : 0 < nv) (hd : den.toVal = some (dv : EReal))
    (hd0 : 0 < dv) :
    IsEnclPos (gammaSpecialEncl recip r d num den w)
      (if recip then dv / (g * nv) else g * nv / dv) := by
  have : NeZero (w + 32) := ⟨by omega⟩
  have hW : 2 ≤ w + 32 := by omega
  have hN := hg.mul hW (isEnclPos_exact hn hn0)
  have hD := isEnclPos_exact hd hd0
  unfold gammaSpecialEncl
  cases recip
  · exact hN.div hW hD
  · exact hD.div hW hN

/-! ### The loop -/

/-- The fuel loop on `gammaSpecialApprox` is correct when it does not give up. -/
theorem gammaSpecial_zivLoop (recip neg : Bool) {r d : ℕ} {num den : AzFloat}
    {nv dv g V : ℝ} (hg : ∀ w, 64 ≤ w → IsEnclPos (gammaBaseEncl r d w) g)
    (hn : num.toVal = some (nv : EReal)) (hn0 : 0 < nv) (hd : den.toVal = some (dv : EReal))
    (hd0 : 0 < dv)
    (hV : (if neg then -1 else 1) * V = if recip then dv / (g * nv) else g * nv / dv)
    (p : ℕ) [NeZero p] (mode : RoundingMode) :
    zivLoop (gammaSpecialApprox recip neg r d num den) p mode (gammaFuel p) (max 64 (p + 32))
        = roundVal p mode (some (V : EReal)) ∨
      zivLoop (gammaSpecialApprox recip neg r d num den) p mode (gammaFuel p) (max 64 (p + 32))
        = (nan, .eq) := by
  rcases eq_or_ne (zivLoop (gammaSpecialApprox recip neg r d num den) p mode (gammaFuel p)
    (max 64 (p + 32))) (nan, .eq) with hz | hz
  · right; exact hz
  · left
    refine zivLoop_eq_of_ne_nan_or_none p mode _ _ 64 (fun w hw => ?_) _ _ (le_max_left _ _) hz
    refine gammaApproxOf_valid_or_none (fun neg' b hc => ?_) w p mode
    rw [Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    rw [hV]
    exact gammaSpecialEncl_spec recip (hg w hw) hn hn0 hd hd0

theorem neg_one_pow_eq_ite (m : ℕ) : ((-1 : ℝ)) ^ m = if (m % 2 == 1) = true then -1 else 1 := by
  rcases Nat.even_or_odd m with h | h
  · have : m % 2 = 0 := Nat.even_iff.mp h
    simp [h.neg_one_pow, this]
  · have : m % 2 = 1 := Nat.odd_iff.mp h
    simp [h.neg_one_pow, this]

/-- **`gammaSpecialFast?` answers with the correctly rounded `Γ(± n/d)` (or its reciprocal),
or with `(nan, .eq)`.** -/
theorem gammaSpecialFast?_eq_or (recip pos : Bool) {n : AzNat} {d : ℕ}
    (hd : d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 6) (hr0 : n.toNat % d ≠ 0)
    (hc : Nat.Coprime (n.toNat % d) d ∨ 2 * (n.toNat % d) = d) (p : ℕ) [NeZero p]
    (mode : RoundingMode) {res : AzFloat × Ordering}
    (h : gammaSpecialFast? recip pos n d p mode = some res) :
    res = roundVal p mode (some ((gammaVal recip
        ((if pos then 1 else -1) * ((n.toNat : ℝ) / d)) : ℝ) : EReal)) ∨
      res = (nan, .eq) := by
  have hd0 : 0 < d := by rcases hd with rfl | rfl | rfl | rfl <;> norm_num
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  have hQ : (n / AzNat.ofNat d).toNat = n.toNat / d := by
    rw [AzNat.toNat_div, AzNat.toNat_ofNat]
  have hR : (n % AzNat.ofNat d).toNat = n.toNat % d := by
    rw [AzNat.toNat_mod, AzNat.toNat_ofNat]
  set qu := n.toNat / d with hqu
  set r := n.toNat % d with hr
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
  have hrd : r < d := Nat.mod_lt _ hd0
  have hsplit : (n.toNat : ℝ) / d = (qu : ℝ) + (r : ℝ) / d := by
    have h1 : n.toNat = d * qu + r := (Nat.div_add_mod _ _).symm
    rw [h1]
    push_cast
    field_simp
  have hAP : ∀ m : ℕ, (ofAzNat (gammaAP r d m)).toVal
      = some (((∏ j ∈ range m, ((r + j * d : ℕ) : ℝ) : ℝ)) : EReal) := fun m => by
    rw [toVal_ofAzNat, toNat_gammaAP]
    push_cast
    rfl
  have hAP0 : ∀ m : ℕ, (0 : ℝ) < ∏ j ∈ range m, ((r + j * d : ℕ) : ℝ) := fun m =>
    prod_pos fun j _ => by exact_mod_cast (by positivity : 0 < r + j * d)
  have hPow : ∀ m : ℕ, (ofAzNat ((AzNat.ofNat d).pow m)).toVal
      = some ((((d : ℝ) ^ m : ℝ)) : EReal) := fun m => by
    rw [toVal_ofAzNat, AzNat.toNat_pow, AzNat.toNat_ofNat]
    push_cast
    rfl
  unfold gammaSpecialFast? at h
  dsimp only at h
  split_ifs at h with hb hp <;> rw [Option.some.injEq] at h <;> rw [hQ, hR] at h <;> subst h
  · -- positive
    refine gammaSpecial_zivLoop recip false
      (fun w hw => gammaBaseEncl_spec hd hrpos hrd hc hw) (hAP qu) (hAP0 qu) (hPow qu)
      (by positivity) ?_ p mode
    simp only [↓reduceIte, Bool.false_eq_true, one_mul]
    rw [hsplit]
    simp only [hp, ↓reduceIte, one_mul]
    unfold gammaVal
    rw [gamma_shift_pos hrpos hd0 qu]
    cases recip
    · simp
    · simp only [↓reduceIte]
      rw [inv_div]
  · -- negative
    have hc' : Nat.Coprime (d - r) d ∨ 2 * (d - r) = d := by
      rcases hc with h | h
      · exact Or.inl ((Nat.coprime_self_sub_left hrd.le).mpr h)
      · exact Or.inr (by omega)
    refine gammaSpecial_zivLoop recip ((qu + 1) % 2 == 1)
      (fun w hw => gammaBaseEncl_spec hd (by omega) (by omega) hc' hw) (hPow (qu + 1))
      (by positivity) (hAP (qu + 1)) (hAP0 (qu + 1)) ?_ p mode
    have hx : (if pos then (1 : ℝ) else -1) * ((n.toNat : ℝ) / d)
        = -((qu : ℝ) + (r : ℝ) / d) := by
      rw [hsplit]
      simp [hp]
    rw [hx]
    unfold gammaVal
    rw [gamma_shift_neg hrpos hrd qu, ← neg_one_pow_eq_ite]
    have hs : ((-1 : ℝ) ^ (qu + 1)) * ((-1) ^ (qu + 1)) = 1 := by rw [← mul_pow]; norm_num
    have hinv : ((-1 : ℝ) ^ (qu + 1))⁻¹ = (-1) ^ (qu + 1) := inv_eq_of_mul_eq_one_right hs
    cases recip
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [← mul_assoc, hs, one_mul]
    · simp only [↓reduceIte]
      rw [mul_inv, hinv, ← mul_assoc, hs, one_mul, inv_div]

end Azurite.AzFloat
