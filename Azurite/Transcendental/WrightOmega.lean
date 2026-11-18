/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Transcendental.LambertW

/-!
# The real Wright `ω` function: enclosures and irrationality

The analytic facts behind `AzFloat.wrightOmegaPrecRound` (`AzFloat/WrightOmega.lean`), for
`ω(x) = W₀(eˣ)`, the positive root of `y + ln y = x` (`wrightOmegaReal`,
`DLMF/Chapter4/Section13Real.lean`).

* **The enclosure from a candidate.**  For any `n > 0` with residual `d = n + ln n − x`,
  `n − ω = d c` with `c` between `t/(1 + t)` at `t = min(n, ω)` and at `t = max(n, ω)`
  (`exists_factor`: the mean value theorem for `y + ln y`, whose derivative is `1 + 1/y`, here
  from `1 − 1/t ≤ ln t ≤ t − 1` alone).  Since `c ≤ min(1, max(n, ω))`, the residual also gives
  the crude bounds on `ω` that enclose `c` (`sub_mul_min_le`, `le_add`, `le_add_mul`); with them
  `ω ∈ n − [d]·[c]` has a width of the order `d²`: a candidate with half the bits wanted is
  enough.
* **Large arguments** (`bounds_of_one_lt`): `x − ln x < ω(x) < x` for `x > 1`.
* **Irrationality** of `ω(r)` for a rational `r ≠ 1` (`ln ω` would be rational), and no
  rational `m` has `m eᵐ = eʳ` then.  `ω(1) = 1`.
-/

open Real Azurite.DLMF

namespace Azurite.WrightOmega

/-! ### The mean value form -/

/-- For `0 < a < b`: `(b − a)/D` with `D = (b + ln b) − (a + ln a)` lies between `a/(1 + a)` and
`b/(1 + b)`. -/
theorem factor_bounds {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    0 < (b + log b) - (a + log a) ∧
      a / (1 + a) ≤ (b - a) / ((b + log b) - (a + log a)) ∧
      (b - a) / ((b + log b) - (a + log a)) ≤ b / (1 + b) := by
  have hb : 0 < b := ha.trans hab
  have hL : log b - log a = log (b / a) := (Real.log_div hb.ne' ha.ne').symm
  have h1 : 1 - (b / a)⁻¹ ≤ log (b / a) := Real.one_sub_inv_le_log_of_pos (div_pos hb ha)
  have h2 : log (b / a) ≤ b / a - 1 := Real.log_le_sub_one_of_pos (div_pos hb ha)
  rw [inv_div] at h1
  -- `(b − a)/b ≤ L ≤ (b − a)/a`
  have k1 : b - a ≤ b * (log b - log a) := by
    rw [hL]
    have : b * (1 - a / b) = b - a := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left h1 hb.le]
  have k2 : a * (log b - log a) ≤ b - a := by
    rw [hL]
    have : a * (b / a - 1) = b - a := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left h2 ha.le]
  have hLpos : 0 ≤ log b - log a := by
    by_contra h
    push Not at h
    nlinarith
  have hD : 0 < (b + log b) - (a + log a) := by linarith
  refine ⟨hD, ?_, ?_⟩
  · rw [div_le_div_iff₀ (by linarith) hD]
    nlinarith
  · rw [div_le_div_iff₀ hD (by linarith)]
    nlinarith

/-- **The mean value form of `y + ln y`**: for `n, ω > 0` and `d = (n + ln n) − (ω + ln ω)`,
`n − ω = d c` with `c` between `t/(1 + t)` at `t = min(n, ω)` and at `t = max(n, ω)`. -/
theorem exists_factor {n ω : ℝ} (hn : 0 < n) (hω : 0 < ω) :
    ∃ c : ℝ, n - ω = ((n + log n) - (ω + log ω)) * c ∧
      min n ω / (1 + min n ω) ≤ c ∧ c ≤ max n ω / (1 + max n ω) := by
  rcases lt_trichotomy ω n with h | h | h
  · obtain ⟨hD, h1, h2⟩ := factor_bounds hω h
    refine ⟨(n - ω) / ((n + log n) - (ω + log ω)), by field_simp, ?_, ?_⟩
    · rw [min_eq_right h.le]; exact h1
    · rw [max_eq_left h.le]; exact h2
  · subst h
    exact ⟨ω / (1 + ω), by ring, by rw [min_self], by rw [max_self]⟩
  · obtain ⟨hD, h1, h2⟩ := factor_bounds hn h
    refine ⟨(ω - n) / ((ω + log ω) - (n + log n)), ?_, ?_, ?_⟩
    · have : (n + log n) - (ω + log ω) = -((ω + log ω) - (n + log n)) := by ring
      rw [this]
      field_simp
      ring
    · rw [min_eq_left h.le]; exact h1
    · rw [max_eq_right h.le]; exact h2

/-- `t/(1 + t)` is increasing on `t ≥ 0`. -/
theorem div_one_add_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : s / (1 + s) ≤ t / (1 + t) := by
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- `t/(1 + t) ≤ min(1, t)` for `t ≥ 0`. -/
theorem div_one_add_le_min {t : ℝ} (ht : 0 ≤ t) : t / (1 + t) ≤ min 1 t := by
  apply le_min
  · rw [div_le_one (by linarith)]; linarith
  · rw [div_le_iff₀ (by linarith)]; nlinarith

section Candidate

variable {n ω x d : ℝ}

/-- The lower bound of `ω` from the residual: `n − max(d, 0)·min(1, n) ≤ ω`. -/
theorem sub_mul_min_le (hn : 0 < n) (hω : 0 < ω) (hx : ω + log ω = x)
    (hd : d = n + log n - x) : n - max d 0 * min 1 n ≤ ω := by
  obtain ⟨c, hc, -, hc2⟩ := exists_factor hn hω
  rw [hx, ← hd] at hc
  rcases le_total d 0 with h | h
  · rw [max_eq_right h, zero_mul, sub_zero]
    obtain ⟨c', hc', hc1', -⟩ := exists_factor hn hω
    rw [hx, ← hd] at hc'
    have hc0 : 0 ≤ c' := le_trans (div_nonneg (le_min hn.le hω.le)
      (by linarith [le_min hn.le hω.le])) hc1'
    nlinarith
  · rw [max_eq_left h]
    have hωn : ω ≤ n := by
      obtain ⟨c', hc', hc1', -⟩ := exists_factor hn hω
      rw [hx, ← hd] at hc'
      have hc0 : 0 ≤ c' := le_trans (div_nonneg (le_min hn.le hω.le)
        (by linarith [le_min hn.le hω.le])) hc1'
      nlinarith
    rw [max_eq_left hωn] at hc2
    have := (hc2.trans (div_one_add_le_min hn.le))
    nlinarith [mul_le_mul_of_nonneg_left this h]

/-- The upper bound of `ω` from the residual: `ω ≤ n + max(−d, 0)`. -/
theorem le_add (hn : 0 < n) (hω : 0 < ω) (hx : ω + log ω = x) (hd : d = n + log n - x) :
    ω ≤ n + max (-d) 0 := by
  obtain ⟨c, hc, hc1, hc2⟩ := exists_factor hn hω
  rw [hx, ← hd] at hc
  have hM : 0 ≤ max n ω := le_max_of_le_left hn.le
  have hc0 : 0 ≤ c := le_trans (div_nonneg (le_min hn.le hω.le)
    (by linarith [le_min hn.le hω.le])) hc1
  have hc1' : c ≤ 1 := hc2.trans ((div_one_add_le_min hM).trans (min_le_left _ _))
  rcases le_total d 0 with h | h
  · rw [max_eq_left (by linarith)]
    nlinarith
  · rw [max_eq_right (by linarith)]
    nlinarith

/-- The relative upper bound of `ω` for a small residual: `ω ≤ n + max(−d, 0)·2n` when
`max(−d, 0) ≤ 1/2`. -/
theorem le_add_mul (hn : 0 < n) (hω : 0 < ω) (hx : ω + log ω = x) (hd : d = n + log n - x)
    (hsmall : max (-d) 0 ≤ 1 / 2) : ω ≤ n + max (-d) 0 * (2 * n) := by
  obtain ⟨c, hc, hc1, hc2⟩ := exists_factor hn hω
  rw [hx, ← hd] at hc
  have hM : 0 ≤ max n ω := le_max_of_le_left hn.le
  have hc0 : 0 ≤ c := le_trans (div_nonneg (le_min hn.le hω.le)
    (by linarith [le_min hn.le hω.le])) hc1
  rcases le_total d 0 with h | h
  · rw [max_eq_left (by linarith)] at hsmall ⊢
    rcases le_total ω n with hωn | hnω
    · nlinarith
    · rw [max_eq_right hnω] at hc2
      have hcω : c ≤ ω := hc2.trans ((div_one_add_le_min hω.le).trans (min_le_right _ _))
      -- `ω − n = (−d) c ≤ (−d) ω`, so `ω (1 + d) ≤ n`
      have h1 : ω * (1 + d) ≤ n := by nlinarith
      nlinarith
  · rw [max_eq_right (by linarith), zero_mul, add_zero]
    nlinarith

/-- **The enclosure of `ω` from a candidate**: with `m ≤ min(n, ω)`, `M ≥ max(n, ω)`,
`c₁ ≤ m/(1 + m)`, `M/(1 + M) ≤ c₂` and `D₁ ≤ d ≤ D₂`, `ω ∈ n − [D₁, D₂]·[c₁, c₂]`. -/
theorem candidate_encl (hn : 0 < n) (hω : 0 < ω) (hx : ω + log ω = x) (hd : d = n + log n - x)
    {m M c₁ c₂ D₁ D₂ : ℝ} (hm0 : 0 ≤ m) (hm : m ≤ min n ω) (hM : max n ω ≤ M)
    (hc0 : 0 ≤ c₁) (hc₁ : c₁ ≤ m / (1 + m)) (hc₂ : M / (1 + M) ≤ c₂) (hD₁ : D₁ ≤ d)
    (hD₂ : d ≤ D₂) :
    n - (if 0 < D₂ then D₂ * c₂ else D₂ * c₁) ≤ ω ∧
      ω ≤ n - (if D₁ < 0 then D₁ * c₂ else D₁ * c₁) := by
  obtain ⟨c, hc, hc1, hc2⟩ := exists_factor hn hω
  rw [hx, ← hd] at hc
  have hmin : 0 ≤ min n ω := le_min hn.le hω.le
  have h1 : c₁ ≤ c := hc₁.trans ((div_one_add_mono hm0 hm).trans hc1)
  have h2 : c ≤ c₂ := hc2.trans ((div_one_add_mono (le_max_of_le_left hn.le) hM).trans hc₂)
  have hcpos : 0 ≤ c := hc0.trans h1
  constructor
  · split_ifs with h
    · nlinarith [mul_le_mul_of_nonneg_right hD₂ hcpos, mul_le_mul_of_nonneg_left h2 h.le]
    · push Not at h
      nlinarith [mul_le_mul_of_nonneg_right hD₂ hcpos, mul_le_mul_of_nonpos_left h1 h]
  · split_ifs with h
    · nlinarith [mul_le_mul_of_nonneg_right hD₁ hcpos, mul_le_mul_of_nonpos_left h2 h.le]
    · push Not at h
      nlinarith [mul_le_mul_of_nonneg_right hD₁ hcpos, mul_le_mul_of_nonneg_left h1 h]

end Candidate

/-! ### `ω` itself -/

theorem wrightOmegaReal_one : wrightOmegaReal 1 = 1 := lambertW0_exp_one

/-- `ω(x) e^{ω(x)} = eˣ`. -/
theorem wrightOmegaReal_mul_exp (x : ℝ) :
    wrightOmegaReal x * exp (wrightOmegaReal x) = exp x :=
  (lambertW0_spec (y := exp x) (by linarith [exp_pos x, exp_pos (-1)])).2

/-- `x − ln x < ω(x) < x` for `x > 1`. -/
theorem bounds_of_one_lt {x : ℝ} (hx : 1 < x) :
    x - log x < wrightOmegaReal x ∧ wrightOmegaReal x < x := by
  have hω := wrightOmegaReal_pos x
  have he := dlmf_4_13_1_2_real x
  have h1 : 1 < wrightOmegaReal x := by
    by_contra h
    push Not at h
    have : log (wrightOmegaReal x) ≤ 0 := Real.log_nonpos hω.le h
    linarith
  have hl : 0 < log (wrightOmegaReal x) := Real.log_pos h1
  have hlt : wrightOmegaReal x < x := by linarith
  exact ⟨by linarith [Real.log_lt_log hω hlt], hlt⟩

/-- A positive rational `m` with `m + ln m` rational is `1`. -/
theorem eq_one_of_add_log_rat {m r : ℚ} (hm : 0 < m) (h : (m : ℝ) + log m = r) : m = 1 := by
  by_contra hne
  exact irrational_log_rat hm hne ⟨r - m, by push_cast; linarith⟩

/-- **`ω(r)` is irrational for a rational `r ≠ 1`.** -/
theorem irrational_wrightOmegaReal {r : ℚ} (hr : r ≠ 1) : Irrational (wrightOmegaReal r) := by
  rintro ⟨q, hq⟩
  have hpos := wrightOmegaReal_pos (r : ℝ)
  have he := dlmf_4_13_1_2_real (r : ℝ)
  rw [← hq] at hpos he
  have hq1 : q = 1 := eq_one_of_add_log_rat (by exact_mod_cast hpos) he
  rw [hq1, Rat.cast_one, Real.log_one, add_zero] at he
  exact hr (by exact_mod_cast he.symm)

/-- No rational `m` has `m eᵐ = eʳ` for a rational `r ≠ 1`. -/
theorem mul_exp_ne_exp_rat {m r : ℚ} (hr : r ≠ 1) : (m : ℝ) * exp m ≠ exp r := by
  intro h
  rcases le_or_gt m 0 with hm | hm
  · have : (m : ℝ) * exp m ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hm) (exp_pos _).le
    linarith [exp_pos (r : ℝ)]
  · have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have := congrArg Real.log h
    rw [Real.log_mul hm'.ne' (exp_pos _).ne', Real.log_exp, Real.log_exp] at this
    have hm1 : m = 1 := eq_one_of_add_log_rat hm (by linarith)
    rw [hm1, Rat.cast_one, Real.log_one, zero_add] at this
    exact hr (by exact_mod_cast this.symm)

end Azurite.WrightOmega
