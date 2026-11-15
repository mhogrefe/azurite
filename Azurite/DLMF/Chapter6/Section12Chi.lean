/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter6.Section12

/-!
# Computable bounds for Olver's `χ` (DLMF 9.7.3) and the remainder of 6.12.2

`χ(a) = π^{1/2} Γ(a/2 + 1)/Γ(a/2 + 1/2)` (`olverChi`) enters the remainder bound of 6.12.2
(`dlmf_6_12_2_remainder`).  For computation we bound it by elementary expressions.

## Main results

* `olverChi_le_sqrt`, `sqrt_le_olverChi`: `√(πa/2) ≤ χ(a) ≤ √(π(a + 1)/2)` for `a > 0`
  (log-convexity of `Γ`, `Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma`).
* `olverChi_le_add_one`: `χ(a) ≤ a + 1` for `a ≥ 1`.
* `dlmf_6_12_2_remainder_sqrt`, `dlmf_6_12_2_remainder_nat`: the 6.12.2 remainder after `n` terms
  is at most `(1 + √(π(n + 2)/2))` resp. `(n + 3)` times the next term `n! eˣ/x^{n+1}`.
-/

open Real Set
open scoped Nat

namespace Azurite.DLMF

/-- Log-convexity at the midpoint: `Γ((s + t)/2)² ≤ Γ(s) Γ(t)`. -/
theorem Gamma_midpoint_sq_le {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Gamma ((s + t) / 2) ^ 2 ≤ Gamma s * Gamma t := by
  have h := Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma hs ht (a := 1 / 2) (b := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num)
  rw [show 1 / 2 * s + 1 / 2 * t = (s + t) / 2 by ring] at h
  have hg := (Gamma_pos_of_pos ((by positivity : 0 < (s + t) / 2))).le
  have h0 : 0 ≤ Gamma s ^ (1 / 2 : ℝ) * Gamma t ^ (1 / 2 : ℝ) := by
    have := (Gamma_pos_of_pos hs).le; have := (Gamma_pos_of_pos ht).le; positivity
  have hsq := pow_le_pow_left₀ hg h 2
  rw [mul_pow, ← rpow_natCast (Gamma s ^ (1 / 2 : ℝ)), ← rpow_natCast (Gamma t ^ (1 / 2 : ℝ)),
    ← rpow_mul (Gamma_pos_of_pos hs).le, ← rpow_mul (Gamma_pos_of_pos ht).le] at hsq
  norm_num at hsq
  exact hsq

/-- `χ(a) ≤ √(π(a + 1)/2)` for `a > 0`. -/
theorem olverChi_le_sqrt {a : ℝ} (ha : 0 < a) : olverChi a ≤ √(π * (a + 1) / 2) := by
  set y := a / 2 + 1 / 2 with hy
  have hy0 : 0 < y := by positivity
  -- `Γ(y + ½)² ≤ Γ(y) Γ(y + 1) = y Γ(y)²`
  have h := Gamma_midpoint_sq_le hy0 (by positivity : 0 < y + 1)
  rw [show (y + (y + 1)) / 2 = a / 2 + 1 by rw [hy]; ring, Gamma_add_one hy0.ne'] at h
  have hG := Gamma_pos_of_pos hy0
  have hG1 := Gamma_pos_of_pos (by positivity : 0 < a / 2 + 1)
  have hratio : Gamma (a / 2 + 1) / Gamma y ≤ √y := by
    rw [div_le_iff₀ hG, ← abs_of_pos hG1, ← sqrt_sq_eq_abs]
    calc √(Gamma (a / 2 + 1) ^ 2) ≤ √(y * Gamma y * Gamma y) := sqrt_le_sqrt (by linarith)
      _ = √y * Gamma y := by
          rw [show y * Gamma y * Gamma y = y * Gamma y ^ 2 by ring, sqrt_mul hy0.le,
            sqrt_sq hG.le]
  rw [olverChi, ← hy, mul_div_assoc]
  calc √π * (Gamma (a / 2 + 1) / Gamma y) ≤ √π * √y := by gcongr
    _ = √(π * (a + 1) / 2) := by
        rw [← sqrt_mul pi_pos.le, hy]; congr 1; ring

/-- `χ(a) ≥ √(πa/2)` for `a > 0`. -/
theorem sqrt_le_olverChi {a : ℝ} (ha : 0 < a) : √(π * a / 2) ≤ olverChi a := by
  have hy0 : 0 < a / 2 := by positivity
  -- `Γ(a/2 + ½)² ≤ Γ(a/2) Γ(a/2 + 1) = Γ(a/2 + 1)²/(a/2)`
  have h := Gamma_midpoint_sq_le hy0 (by positivity : 0 < a / 2 + 1)
  rw [show (a / 2 + (a / 2 + 1)) / 2 = a / 2 + 1 / 2 by ring] at h
  have hG1 := Gamma_pos_of_pos (by positivity : 0 < a / 2 + 1)
  have hGh := Gamma_pos_of_pos (by positivity : 0 < a / 2 + 1 / 2)
  have hrec : Gamma (a / 2) = Gamma (a / 2 + 1) / (a / 2) := by
    rw [Gamma_add_one hy0.ne']; field_simp
  rw [hrec] at h
  have hratio : √(a / 2) ≤ Gamma (a / 2 + 1) / Gamma (a / 2 + 1 / 2) := by
    rw [le_div_iff₀ hGh, ← abs_of_pos hGh, ← sqrt_sq_eq_abs, ← sqrt_mul hy0.le,
      ← sqrt_sq hG1.le]
    refine sqrt_le_sqrt ?_
    rw [div_mul_eq_mul_div, le_div_iff₀ hy0] at h
    nlinarith
  rw [olverChi]
  calc √(π * a / 2) = √π * √(a / 2) := by rw [← sqrt_mul pi_pos.le]; congr 1; ring
    _ ≤ √π * (Gamma (a / 2 + 1) / Gamma (a / 2 + 1 / 2)) := by gcongr
    _ = √π * Gamma (a / 2 + 1) / Gamma (a / 2 + 1 / 2) := by ring

/-- `χ(a) ≤ a + 1` for `a ≥ 1`. -/
theorem olverChi_le_add_one {a : ℝ} (ha : 1 ≤ a) : olverChi a ≤ a + 1 := by
  refine (olverChi_le_sqrt (by linarith)).trans ?_
  rw [sqrt_le_left (by linarith)]
  have := pi_lt_four
  nlinarith

/-- **6.12.2, computable remainder bound**: `|Ei(x) − eˣ/x ∑_{s<n} s!/x^s| ≤
(1 + √(π(n + 2)/2)) n! eˣ/x^{n+1}`, `x > 0`. -/
theorem dlmf_6_12_2_remainder_sqrt (n : ℕ) {x : ℝ} (hx : 0 < x) :
    |Ei x - eiAsymp n x| ≤ (1 + √(π * (n + 2) / 2)) * (n ! * exp x / x ^ (n + 1)) := by
  refine (dlmf_6_12_2_remainder n hx).trans ?_
  have hT : 0 ≤ (n ! : ℝ) * exp x / x ^ (n + 1) := by positivity
  gcongr
  have := olverChi_le_sqrt (a := (n : ℝ) + 1) (by positivity)
  rwa [show (n : ℝ) + 1 + 1 = n + 2 by ring] at this

/-- **6.12.2, integer remainder bound**: `|Ei(x) − eˣ/x ∑_{s<n} s!/x^s| ≤ (n + 3) n! eˣ/x^{n+1}`,
`x > 0`. -/
theorem dlmf_6_12_2_remainder_nat (n : ℕ) {x : ℝ} (hx : 0 < x) :
    |Ei x - eiAsymp n x| ≤ (n + 3) * (n ! * exp x / x ^ (n + 1)) := by
  refine (dlmf_6_12_2_remainder n hx).trans ?_
  have hT : 0 ≤ (n ! : ℝ) * exp x / x ^ (n + 1) := by positivity
  have := olverChi_le_add_one (a := (n : ℝ) + 1) (by linarith [n.cast_nonneg (α := ℝ)])
  exact mul_le_mul_of_nonneg_right (by linarith) hT

end Azurite.DLMF
