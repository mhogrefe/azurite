/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.AsinBracket
import Azurite.AzFloat.Equiv.Atan2Bracket
import Azurite.AzFloat.Equiv.TanBracket
import Azurite.Transcendental.Cos

/-!
# Equivalence: the bracket of `arcsin x`

* Real analysis: `arcsin_eq_two_arctan` (the half-angle identity), `arcsin_bounds_of_small`
  (`a < arcsin a ≤ a + a³` for `0 < a ≤ 1/2`), `irrational_arcsin_rat`.
* `asinSqrt_spec` (`√(1 − a²)` with relative accuracy), `asinArgOf_spec`, `asinArg_spec`
  (width at most `40·2^(−P)`), `asinDouble_spec`, `asinBracket_spec` (width at most `2^(−w)`),
  `asinApprox_spec`, `asinApprox_isSome_exists` (the Ziv certificate), `asinTiny?_eq`.
-/

open Real

namespace Azurite.AzFloat

/-! ### Real analysis -/

/-- The half-angle identity `arcsin a = 2 arctan (a / (1 + √(1 − a²)))` for `0 ≤ a ≤ 1`. -/
theorem arcsin_eq_two_arctan {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) :
    arcsin a = 2 * arctan (a / (1 + √(1 - a ^ 2))) := by
  set φ := arcsin a with hφ
  have hφ0 : 0 ≤ φ := arcsin_nonneg.mpr h0
  have hφ1 : φ ≤ π / 2 := arcsin_le_pi_div_two a
  have hπ := pi_pos
  have hsin : sin φ = a := sin_arcsin (by linarith) h1
  have hcos : cos φ = √(1 - a ^ 2) := cos_arcsin a
  have hc2 : 0 < cos (φ / 2) := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have htan : a / (1 + √(1 - a ^ 2)) = tan (φ / 2) := by
    rw [← hcos, tan_eq_sin_div_cos]
    nth_rewrite 1 [← hsin]
    have e1 : sin φ = 2 * sin (φ / 2) * cos (φ / 2) := by
      rw [← sin_two_mul]
      congr 1
      ring
    have e2 : 1 + cos φ = 2 * cos (φ / 2) ^ 2 := by
      have := cos_sq (φ / 2)
      rw [show 2 * (φ / 2) = φ by ring] at this
      linarith
    rw [e1, e2]
    field_simp
  rw [htan, arctan_tan (by linarith) (by linarith)]
  ring

/-- `a < arcsin a ≤ a + a³` for `0 < a ≤ 1/2`. -/
theorem arcsin_bounds_of_small {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1 / 2) :
    a < arcsin a ∧ arcsin a ≤ a + a ^ 3 := by
  have hφ0 : 0 < arcsin a := arcsin_pos.mpr ha0
  have hsin : sin (arcsin a) = a := sin_arcsin (by linarith) (by linarith)
  refine ⟨by have := sin_lt hφ0; rwa [hsin] at this, ?_⟩
  -- `arcsin a = arctan (a/√(1 − a²)) ≤ a/√(1 − a²) ≤ a (1 + a²)`
  have hsq : 0 < 1 - a ^ 2 := by nlinarith
  have hs0 : 0 < √(1 - a ^ 2) := sqrt_pos.mpr hsq
  have harc : arcsin a = arctan (a / √(1 - a ^ 2)) := arcsin_eq_arctan
    ⟨by linarith, by linarith⟩
  have hle : arctan (a / √(1 - a ^ 2)) ≤ a / √(1 - a ^ 2) :=
    arctan_le_self (div_nonneg ha0.le hs0.le)
  have hinv : a / √(1 - a ^ 2) ≤ a * (1 + a ^ 2) := by
    rw [div_le_iff₀ hs0]
    have h1 : 1 ≤ (1 + a ^ 2) * √(1 - a ^ 2) := by
      have h2 : (1 : ℝ) ≤ ((1 + a ^ 2) * √(1 - a ^ 2)) ^ 2 := by
        rw [mul_pow, sq_sqrt hsq.le]
        have ha2 : a ^ 2 ≤ 1 / 4 := by nlinarith
        have ha20 : 0 ≤ a ^ 2 := by positivity
        have ha4 : a ^ 4 ≤ 1 / 16 := by nlinarith
        have e : (1 + a ^ 2) ^ 2 * (1 - a ^ 2) = 1 + a ^ 2 * (1 - a ^ 2 - a ^ 4) := by ring
        rw [e]
        have := mul_nonneg ha20 (by linarith : 0 ≤ 1 - a ^ 2 - a ^ 4)
        linarith
      have h3 : 0 ≤ (1 + a ^ 2) * √(1 - a ^ 2) := by positivity
      nlinarith
    nlinarith
  rw [harc]
  linarith

/-- `arcsin q` is irrational for a nonzero rational `q` in `[−1, 1]`. -/
theorem irrational_arcsin_rat {q : ℚ} (hq : q ≠ 0) (h1 : -1 ≤ (q : ℝ)) (h2 : (q : ℝ) ≤ 1) :
    Irrational (arcsin q) := by
  rintro ⟨r, hr⟩
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [Rat.cast_zero] at hr
    exact hq (by exact_mod_cast arcsin_eq_zero_iff.mp hr.symm)
  apply irrational_sin_rat hr0
  rw [hr, sin_arcsin h1 h2]
  exact ⟨q, rfl⟩

/-! ### The argument -/

/-- **The enclosure of `s = √(1 − a²)`** for a float `0 < a < 1`, with relative accuracy:
`s − 6·2^(−P) ≤ lo ≤ s ≤ hi ≤ s + 7·2^(−P)` (the errors are in fact relative to `s ≤ 1`). -/
theorem asinSqrt_spec {a : AzFloat} {av : ℝ} (ha : a.toVal = some (av : EReal)) (h0 : 0 < av)
    (h1 : av < 1) {P : ℕ} (hP : 8 ≤ P) :
    ∃ sl sh : ℝ, (asinSqrt a P).1.toVal = some (sl : EReal) ∧
      (asinSqrt a P).2.toVal = some (sh : EReal) ∧ 0 ≤ sl ∧
      √(1 - av ^ 2) - 6 * (1 / 2 : ℝ) ^ P ≤ sl ∧ sl ≤ √(1 - av ^ 2) ∧ √(1 - av ^ 2) ≤ sh ∧
      sh ≤ √(1 - av ^ 2) + 7 * (1 / 2 : ℝ) ^ P := by
  unfold asinSqrt
  dsimp only
  have : NeZero P := ⟨by omega⟩
  set ε := (1 / 2 : ℝ) ^ P with hε
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 / 256 := by
    have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) hP
    rw [← hε] at this
    norm_num at this
    linarith
  set α := 1 - 2 * ε with hα
  set β := 1 + 2 * ε with hβ
  have hα0 : 0 < α := by rw [hα]; linarith
  have hα1 : α ≤ 1 := by rw [hα]; linarith
  have hβ1 : 1 ≤ β := by rw [hβ]; linarith
  have hεε : ε * ε ≤ ε / 256 := by nlinarith
  have hα3 : 1 - 6 * ε ≤ α ^ 3 := by rw [hα]; nlinarith
  have hβ3 : β ^ 3 ≤ 1 + 7 * ε := by rw [hβ]; nlinarith
  set D := 1 - av with hD
  set E := 1 + av with hE
  have hD0 : 0 < D := by rw [hD]; linarith
  have hE0 : 0 < E := by rw [hE]; linarith
  set p := 1 - av ^ 2 with hp
  have hpDE : p = D * E := by rw [hp, hD, hE]; ring
  have hp0 : 0 < p := by rw [hpDE]; positivity
  have hp1 : p ≤ 1 := by rw [hp]; nlinarith
  set s := √p with hs
  have hs0 : 0 ≤ s := sqrt_nonneg p
  have hs1 : s ≤ 1 := by
    rw [hs]
    exact sqrt_le_one.mpr hp1
  -- `1 − a`, `1 + a`
  obtain ⟨dl, hdl, hdl1, hdl2⟩ := subFloor_abs toVal_one' ha P
  obtain ⟨dh, hdh, hdh1, hdh2⟩ := subCeiling_abs toVal_one' ha P
  obtain ⟨el, hel, hel1, hel2⟩ := addFloor_abs toVal_one' ha P
  obtain ⟨eh, heh, heh1, heh2⟩ := addCeiling_abs toVal_one' ha P
  rw [← hD, abs_of_pos hD0, ← hε] at hdl2 hdh2
  rw [← hD] at hdl1 hdh1
  rw [← hE, abs_of_pos hE0, ← hε] at hel2 heh2
  rw [← hE] at hel1 heh1
  have hdlα : α * D ≤ dl := by rw [hα]; linarith
  have hdhβ : dh ≤ β * D := by rw [hβ]; linarith
  have helα : α * E ≤ el := by rw [hα]; linarith
  have hehβ : eh ≤ β * E := by rw [hβ]; linarith
  have hdl0 : 0 ≤ dl := le_trans (by positivity) hdlα
  have hel0 : 0 ≤ el := le_trans (by positivity) helα
  have hdh0 : 0 ≤ dh := by linarith
  have heh0 : 0 ≤ eh := by linarith
  -- the product
  obtain ⟨pl, hpl, hpl1, hpl2⟩ := mulFloor_abs hdl hel P
  obtain ⟨ph, hph, hph1, hph2⟩ := mulCeiling_abs hdh heh P
  rw [abs_of_nonneg (mul_nonneg hdl0 hel0), ← hε] at hpl2
  rw [abs_of_nonneg (mul_nonneg hdh0 heh0), ← hε] at hph2
  have hdlel : α * D * (α * E) ≤ dl * el :=
    mul_le_mul hdlα helα (by positivity) hdl0
  have hdheh : dh * eh ≤ β * D * (β * E) :=
    mul_le_mul hdhβ hehβ heh0 (by positivity)
  have hdlel' : dl * el ≤ p := by
    rw [hpDE]
    exact mul_le_mul hdl1 hel1 hel0 hD0.le
  have hdheh' : p ≤ dh * eh := by
    rw [hpDE]
    exact mul_le_mul hdh1 heh1 hE0.le hdh0
  have hplα : α ^ 3 * p ≤ pl := by
    have h1 : α * (dl * el) ≤ pl := by rw [hα]; linarith
    have h2 : α * (α * D * (α * E)) ≤ α * (dl * el) := mul_le_mul_of_nonneg_left hdlel hα0.le
    rw [hpDE]
    calc α ^ 3 * (D * E) = α * (α * D * (α * E)) := by ring
      _ ≤ α * (dl * el) := h2
      _ ≤ pl := h1
  have hphβ : ph ≤ β ^ 3 * p := by
    have h1 : ph ≤ β * (dh * eh) := by rw [hβ]; linarith
    have h2 : β * (dh * eh) ≤ β * (β * D * (β * E)) :=
      mul_le_mul_of_nonneg_left hdheh (by linarith)
    rw [hpDE]
    calc ph ≤ β * (dh * eh) := h1
      _ ≤ β * (β * D * (β * E)) := h2
      _ = β ^ 3 * (D * E) := by ring
  have hpl0 : 0 ≤ pl := le_trans (by positivity) hplα
  have hplp : pl ≤ p := hpl1.trans hdlel'
  have hpph : p ≤ ph := hdheh'.trans hph1
  have hph0 : 0 ≤ ph := hp0.le.trans hpph
  -- the square root
  obtain ⟨sl, hsl, hsl0, hsl1, hsl2⟩ := sqrtFloor_err hpl hpl0 P
  obtain ⟨sh, hsh, hsh1, hsh2⟩ := sqrtCeiling_err hph hph0 P
  rw [← hε] at hsl2 hsh2
  have hsqα : α ^ 2 * s ≤ √pl := by
    have h1 : (α ^ 2) ^ 2 * p ≤ pl := by
      have : (α ^ 2) ^ 2 * p ≤ α ^ 3 * p := by
        apply mul_le_mul_of_nonneg_right _ hp0.le
        have : α ^ 4 ≤ α ^ 3 := pow_le_pow_of_le_one hα0.le hα1 (by norm_num)
        calc (α ^ 2) ^ 2 = α ^ 4 := by ring
          _ ≤ α ^ 3 := this
      linarith
    have h2 := sqrt_le_sqrt h1
    rwa [sqrt_mul (by positivity), sqrt_sq (by positivity)] at h2
  have hsqβ : √ph ≤ β ^ 2 * s := by
    have h1 : ph ≤ (β ^ 2) ^ 2 * p := by
      have : β ^ 3 * p ≤ (β ^ 2) ^ 2 * p := by
        apply mul_le_mul_of_nonneg_right _ hp0.le
        have : β ^ 3 ≤ β ^ 4 := pow_le_pow_right₀ hβ1 (by norm_num)
        calc β ^ 3 ≤ β ^ 4 := this
          _ = (β ^ 2) ^ 2 := by ring
      linarith
    have h2 := sqrt_le_sqrt h1
    rwa [sqrt_mul (by positivity), sqrt_sq (by positivity)] at h2
  have hsls : sl ≤ s := hsl1.trans (sqrt_le_sqrt hplp)
  have hssh : s ≤ sh := (sqrt_le_sqrt hpph).trans hsh1
  have hslα : α ^ 3 * s ≤ sl := by
    have h1 : α * √pl ≤ sl := by rw [hα]; linarith
    have h2 : α * (α ^ 2 * s) ≤ α * √pl := mul_le_mul_of_nonneg_left hsqα hα0.le
    calc α ^ 3 * s = α * (α ^ 2 * s) := by ring
      _ ≤ α * √pl := h2
      _ ≤ sl := h1
  have hshβ : sh ≤ β ^ 3 * s := by
    have h1 : sh ≤ β * √ph := by rw [hβ]; linarith
    have h2 : β * √ph ≤ β * (β ^ 2 * s) := mul_le_mul_of_nonneg_left hsqβ (by linarith)
    calc sh ≤ β * √ph := h1
      _ ≤ β * (β ^ 2 * s) := h2
      _ = β ^ 3 * s := by ring
  have hεs : ε * s ≤ ε * 1 := mul_le_mul_of_nonneg_left hs1 hε0.le
  have hsl6 : s - 6 * ε ≤ sl := by
    have := mul_le_mul_of_nonneg_right hα3 hs0
    linarith
  have hsh7 : sh ≤ s + 7 * ε := by
    have := mul_le_mul_of_nonneg_right hβ3 hs0
    linarith
  exact ⟨sl, sh, hsl, hsh, hsl0, hsl6, hsls, hssh, hsh7⟩

/-- **The quotient step**: for floats `a − 2ε ≤ al ≤ a ≤ ah ≤ a + 2ε` (`0 ≤ al`, `0 < a ≤ 1`,
`ε = 2^(−P)`) and an enclosure `s − 6ε ≤ sl ≤ s ≤ sh ≤ s + 7ε` of `s ∈ [0, 1]` (`0 ≤ sl`),
`asinArgOf` encloses `a / (1 + s)` with a nonnegative lower end and width at most `40 ε`. -/
theorem asinArgOf_spec {al ah : AzFloat} {S : Encl} {av alv ahv s sl sh : ℝ} {P : ℕ}
    (hP : 8 ≤ P) (hal : al.toVal = some (alv : EReal)) (hah : ah.toVal = some (ahv : EReal))
    (hsl : S.1.toVal = some (sl : EReal)) (hsh : S.2.toVal = some (sh : EReal))
    (h0 : 0 < av) (h1 : av ≤ 1) (hal0 : 0 ≤ alv) (hal1 : av - 2 * (1 / 2 : ℝ) ^ P ≤ alv)
    (hal2 : alv ≤ av) (hah1 : av ≤ ahv) (hah2 : ahv ≤ av + 2 * (1 / 2 : ℝ) ^ P)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hsl0 : 0 ≤ sl) (hsl6 : s - 6 * (1 / 2 : ℝ) ^ P ≤ sl)
    (hsls : sl ≤ s) (hssh : s ≤ sh) (hsh7 : sh ≤ s + 7 * (1 / 2 : ℝ) ^ P) :
    ∃ tl th : ℝ, (asinArgOf al ah S P).1.toVal = some (tl : EReal) ∧
      (asinArgOf al ah S P).2.toVal = some (th : EReal) ∧ 0 ≤ tl ∧
      tl ≤ av / (1 + s) ∧ av / (1 + s) ≤ th ∧ th - tl ≤ 40 * (1 / 2 : ℝ) ^ P := by
  unfold asinArgOf
  dsimp only
  have : NeZero P := ⟨by omega⟩
  set ε := (1 / 2 : ℝ) ^ P with hε
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 / 256 := by
    have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) hP
    rw [← hε] at this
    norm_num at this
    linarith
  have hεε : ε * ε ≤ ε / 256 := by nlinarith
  set O := 1 + s with hO
  have hO1 : 1 ≤ O := by rw [hO]; linarith
  have hO2 : O ≤ 2 := by rw [hO]; linarith
  obtain ⟨ol, hol, hol1, hol2⟩ := addFloor_abs toVal_one' hsl P
  obtain ⟨oh, hoh, hoh1, hoh2⟩ := addCeiling_abs toVal_one' hsh P
  rw [abs_of_nonneg (by linarith), ← hε] at hol2
  rw [abs_of_nonneg (by linarith), ← hε] at hoh2
  have holO : ol ≤ O := by rw [hO]; linarith
  have hOoh : O ≤ oh := by rw [hO]; linarith
  have hm1 : (1 + sl) * ε ≤ 2 * ε := mul_le_mul_of_nonneg_right (by linarith) hε0.le
  have hm2 : (1 + sh) * ε ≤ 5 / 2 * ε := mul_le_mul_of_nonneg_right (by linarith) hε0.le
  have hol10 : O - 10 * ε ≤ ol := by
    rw [hO]
    linarith
  have hoh12 : oh ≤ O + 12 * ε := by
    rw [hO]
    linarith
  have hol0 : 0 < ol := by linarith
  have hoh0 : 0 < oh := by linarith
  set T := av / O with hT
  have hTO : T * O = av := by rw [hT, div_mul_cancel₀]; linarith
  have hT0 : 0 ≤ T := by rw [hT]; positivity
  have hT1 : T ≤ 1 := by
    rw [hT, div_le_one (by linarith)]
    linarith
  have hah0 : 0 ≤ ahv := by linarith
  obtain ⟨tl, htl, htl0, htl1, htl2⟩ := divFloor_err hal hoh hoh0 hal0 P
  obtain ⟨th, hth, hth1, hth2⟩ := divCeiling_err hah hol hol0 hah0 P
  rw [← hε] at htl2 hth2
  have hq1 : alv / oh ≤ T := by
    rw [hT]
    exact (div_le_div_of_nonneg_left hal0 (by linarith) hOoh).trans
      (div_le_div_of_nonneg_right hal2 (by linarith))
  have hq2 : T ≤ ahv / ol := by
    rw [hT]
    exact (div_le_div_of_nonneg_right hah1 (by linarith)).trans
      (div_le_div_of_nonneg_left hah0 hol0 holO)
  have m3 : T * ε ≤ 1 * ε := mul_le_mul_of_nonneg_right hT1 hε0.le
  have hq3 : T - 14 * ε ≤ alv / oh := by
    rw [le_div_iff₀ hoh0]
    have m1 : T * oh ≤ T * (O + 12 * ε) := mul_le_mul_of_nonneg_left hoh12 hT0
    have m2 : ε * 1 ≤ ε * oh := mul_le_mul_of_nonneg_left (by linarith) hε0.le
    have e1 : T * (O + 12 * ε) = T * O + 12 * (T * ε) := by ring
    have e2 : (T - 14 * ε) * oh = T * oh - 14 * (ε * oh) := by ring
    rw [e2]
    linarith
  have hq4 : ahv / ol ≤ T + 14 * ε := by
    rw [div_le_iff₀ hol0]
    have m1 : (T + 14 * ε) * (O - 10 * ε) ≤ (T + 14 * ε) * ol :=
      mul_le_mul_of_nonneg_left hol10 (by linarith)
    have m2 : ε * 1 ≤ ε * O := mul_le_mul_of_nonneg_left hO1 hε0.le
    have e1 : (T + 14 * ε) * (O - 10 * ε)
        = T * O - 10 * (T * ε) + 14 * (ε * O) - 140 * (ε * ε) := by ring
    linarith
  have hq5 : alv / oh ≤ 1 := hq1.trans hT1
  have hq6 : ahv / ol ≤ 2 := by linarith
  have m4 := mul_le_mul_of_nonneg_right hq5 hε0.le
  have m5 := mul_le_mul_of_nonneg_right hq6 hε0.le
  exact ⟨tl, th, htl, hth, htl0, htl1.trans hq1, hq2.trans hth1, by linarith⟩

/-- **The enclosure of `t = a / (1 + √(1 − a²))`** for a float `0 < a < 1`: nonnegative lower
end, width at most `40·2^(−P)`. -/
theorem asinArg_spec {a : AzFloat} {av : ℝ} (ha : a.toVal = some (av : EReal)) (h0 : 0 < av)
    (h1 : av < 1) {P : ℕ} (hP : 8 ≤ P) :
    ∃ tl th : ℝ, (asinArg a P).1.toVal = some (tl : EReal) ∧
      (asinArg a P).2.toVal = some (th : EReal) ∧ 0 ≤ tl ∧
      tl ≤ av / (1 + √(1 - av ^ 2)) ∧ av / (1 + √(1 - av ^ 2)) ≤ th ∧
      th - tl ≤ 40 * (1 / 2 : ℝ) ^ P := by
  obtain ⟨sl, sh, hsl, hsh, hsl0, hsl6, hsls, hssh, hsh7⟩ := asinSqrt_spec ha h0 h1 hP
  have hε0 : (0 : ℝ) < (1 / 2 : ℝ) ^ P := by positivity
  exact asinArgOf_spec hP ha ha hsl hsh h0 h1.le h0.le (by linarith) le_rfl le_rfl
    (by linarith) (sqrt_nonneg _) (sqrt_le_one.mpr (by nlinarith)) hsl0 hsl6 hsls hssh hsh7

/-! ### The bracket -/

/-- **The doubled arctangent**: from an enclosure `[tl, th]` of `t = a/(1 + √(1 − a²))` of
width at most `40·2^(−K−72)` with `0 ≤ tl`, the doubled `atanWiden` at level `K ≥ w + 8`
encloses `arcsin a` with width at most `2^(−w)`. -/
theorem asinDouble_spec {t : Encl} {a tl th : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) {K w : ℕ}
    (hKw : w + 8 ≤ K) (htl : t.1.toVal = some (tl : EReal)) (hth : t.2.toVal = some (th : EReal))
    (htl0 : 0 ≤ tl) (htl1 : tl ≤ a / (1 + √(1 - a ^ 2))) (hth1 : a / (1 + √(1 - a ^ 2)) ≤ th)
    (htw : th - tl ≤ 40 * (1 / 2 : ℝ) ^ (K + 64 + 8)) :
    ∃ lo hi : ℝ, ((atanWiden t.1 t.2 K (K + 64)).1 <<< AzInt.ofInt 1).toVal
        = some (lo : EReal) ∧
      ((atanWiden t.1 t.2 K (K + 64)).2 <<< AzInt.ofInt 1).toVal = some (hi : EReal) ∧
      0 ≤ lo ∧ lo ≤ arcsin a ∧ arcsin a ≤ hi ∧ hi - lo ≤ (1 / 2 : ℝ) ^ w := by
  set T := a / (1 + √(1 - a ^ 2)) with hT
  have hs0 : 0 ≤ √(1 - a ^ 2) := sqrt_nonneg _
  have hT1 : T ≤ 1 := by
    rw [hT, div_le_one (by linarith)]
    linarith
  have hd : th - tl ≤ 4 * (1 / 2 : ℝ) ^ (K + 64) := by
    have e : (1 / 2 : ℝ) ^ (K + 64 + 8) = (1 / 2 : ℝ) ^ (K + 64) / 256 := by
      rw [pow_add (1 / 2 : ℝ) (K + 64) 8]
      norm_num
      ring
    have h0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (K + 64) := by positivity
    rw [e] at htw
    linarith
  obtain ⟨lo, hi, hlo, hhi, hlo0, h1, h2, -, h3⟩ :=
    atanWiden_spec htl hth htl0 htl1 hth1 hT1 K hd
  have hlo2 : ((atanWiden t.1 t.2 K (K + 64)).1 <<< AzInt.ofInt 1).toVal
      = some ((lo * 2 : ℝ) : EReal) := by
    have h := toVal_shiftLeft_of_toVal hlo (AzInt.ofInt 1)
    rw [h, AzInt.toInt_ofInt, zpow_one]
  have hhi2 : ((atanWiden t.1 t.2 K (K + 64)).2 <<< AzInt.ofInt 1).toVal
      = some ((hi * 2 : ℝ) : EReal) := by
    have h := toVal_shiftLeft_of_toVal hhi (AzInt.ofInt 1)
    rw [h, AzInt.toInt_ofInt, zpow_one]
  have hid := arcsin_eq_two_arctan ha0.le ha1
  rw [← hT] at hid
  refine ⟨lo * 2, hi * 2, hlo2, hhi2, by linarith, by linarith, by linarith, ?_⟩
  have hKle : (1 / 2 : ℝ) ^ K ≤ (1 / 2 : ℝ) ^ (w + 8) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hKw
  have h8 : (1 / 2 : ℝ) ^ (w + 8) = (1 / 2 : ℝ) ^ w / 256 := by
    rw [pow_add]
    norm_num
    ring
  have hK0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ K := by positivity
  have h64 : (1 / 2 : ℝ) ^ 64 ≤ 1 / 2 ^ 64 := by norm_num
  have hw0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ w := by positivity
  rw [h8] at hKle
  rw [pow_add] at h3
  nlinarith

/-- **The bracket of `arcsin |x|`** for `0 < |x| < 1`: width at most `2^(−w)`. -/
theorem asinBracket_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx0 : xv ≠ 0) (hx1 : |xv| < 1) (ex : AzInt) (w : ℕ) :
    ∃ lo hi : ℝ, (asinBracket x ex w).1.toVal = some (lo : EReal) ∧
      (asinBracket x ex w).2.toVal = some (hi : EReal) ∧ 0 ≤ lo ∧ lo ≤ arcsin |xv| ∧
      arcsin |xv| ≤ hi ∧ hi - lo ≤ (1 / 2 : ℝ) ^ w := by
  set a := |xv| with ha
  have ha0 : 0 < a := abs_pos.mpr hx0
  have habs : x.abs.toVal = some ((a : ℝ) : EReal) := by
    rw [toVal_abs, hx, Option.map_some, ← EReal.coe_neg]
    congr 1
  unfold asinBracket
  dsimp only
  have hKw : w + 8 ≤ atanWork ex w := by
    unfold atanWork
    omega
  obtain ⟨tl, th, htl, hth, htl0, htl1, hth1, htw⟩ :=
    asinArg_spec habs ha0 hx1 (P := atanWork ex w + 64 + 8) (by omega)
  exact asinDouble_spec ha0 hx1.le hKw htl hth htl0 htl1 hth1 htw

/-- `arcsin x = ± arcsin |x|` with the sign bit of `x`. -/
theorem arcsin_eq_of_neg_iff {neg : Bool} {xv : ℝ} (hneg : neg = true ↔ xv < 0) :
    arcsin xv = (if neg then -1 else 1) * arcsin |xv| := by
  cases neg with
  | true =>
    have h := hneg.mp rfl
    simp only [↓reduceIte]
    rw [abs_of_neg h, arcsin_neg]
    ring
  | false =>
    have h : 0 ≤ xv := not_lt.mp fun h => by simpa using hneg.mpr h
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    rw [abs_of_nonneg h]

/-- `asinApprox neg` as a pair of `Roundable`s bracketing `± arcsin |x|`. -/
theorem asinApprox_spec (neg : Bool) {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx0 : xv ≠ 0) (hx1 : |xv| < 1) (ex : AzInt) (w : ℕ) :
    ∃ lv hv : ℝ, Rounds (asinApprox neg x ex w).1 lv ∧ Rounds (asinApprox neg x ex w).2 hv ∧
      lv ≤ (if neg then -1 else 1) * arcsin |xv| ∧
      (if neg then -1 else 1) * arcsin |xv| ≤ hv ∧ hv - lv ≤ (1 / 2 : ℝ) ^ w := by
  obtain ⟨lo, hi, hlo, hhi, -, h1, h2, hwid⟩ := asinBracket_spec hx hx0 hx1 ex w
  obtain ⟨lv, hv, hR1, hR2, hl, hh, he⟩ := enclApprox_spec neg hlo hhi h1 h2
  exact ⟨lv, hv, hR1, hR2, hl, hh, by rw [he]; exact hwid⟩

/-- `arcsin x` is irrational for a nonzero finite float `x` with `|x| ≤ 1`. -/
theorem irrational_arcsin_of_toVal {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hx0 : xv ≠ 0) (hx1 : |xv| ≤ 1) : Irrational (arcsin xv) := by
  obtain ⟨q, hq⟩ := exists_rat_of_toVal hx
  have hq0 : q ≠ 0 := by
    rintro rfl
    apply hx0
    rw [hq, Rat.cast_zero]
  obtain ⟨h1, h2⟩ := abs_le.mp hx1
  rw [hq] at h1 h2 ⊢
  exact irrational_arcsin_rat hq0 h1 h2

/-- An exponent that is not positive bounds the float by `1`. -/
theorem abs_lt_one_of_exponent {xv : ℝ} {e : AzInt} (hex : |xv| < (2 : ℝ) ^ e.toInt)
    (he : ¬ (e.sign = true ∧ e.abs.toNat ≠ 0)) : |xv| < 1 := by
  have htoInt : e.toInt = if e.sign then (e.abs.toNat : ℤ) else -(e.abs.toNat : ℤ) := rfl
  have h0 : e.toInt ≤ 0 := by
    rw [htoInt]
    cases hs : e.sign with
    | false => simp
    | true =>
      simp only [↓reduceIte]
      have : e.abs.toNat = 0 := by
        by_contra h
        exact he ⟨hs, h⟩
      omega
  exact hex.trans_le (zpow_le_one_of_nonpos₀ (by norm_num) h0)

/-- The Ziv certificate for `arcsin x`, `x` a finite float with `0 < |x| < 1`. -/
theorem asinApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (neg : Bool)
    {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) (hx0 : xv ≠ 0)
    (hx1 : |xv| < 1) (hneg : neg = true ↔ xv < 0) (ex : AzInt) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (asinApprox neg x ex (w₀ * 2 ^ f)).1
      (asinApprox neg x ex (w₀ * 2 ^ f)).2 p mode).isSome = true := by
  refine exists_isSome_of_irrational_threshold p mode (asinApprox neg x ex)
    (v := (if neg then -1 else 1) * arcsin |xv|) ?_ (fun w => (1 / 2 : ℝ) ^ w)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)) 0
    (fun w _ => asinApprox_spec neg hx hx0 hx1 ex w) w₀ hw₀
  rw [← arcsin_eq_of_neg_iff hneg]
  exact irrational_arcsin_of_toVal hx hx0 hx1.le

/-- `arcsin` near `0`, patched by the tangent above `1/2`: an odd function with
`a < f a ≤ a + a³` on all of `(0, 1]`, as the generic tiny-argument lemmas require (the bounds
of `arcsin` hold for `a ≤ 1/2` only, and the tests only pass far below). -/
noncomputable def asinPatch (a : ℝ) : ℝ := if |a| ≤ 1 / 2 then arcsin a else Real.tan a

theorem asinPatch_neg (a : ℝ) : asinPatch (-a) = -asinPatch a := by
  unfold asinPatch
  rw [abs_neg]
  by_cases ha : |a| ≤ 1 / 2
  · rw [ite_eq_left ha, ite_eq_left ha, arcsin_neg]
  · rw [ite_eq_right ha, ite_eq_right ha, Real.tan_neg]

theorem asinPatch_bounds (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1) :
    a < asinPatch a ∧ asinPatch a ≤ a + a ^ 3 := by
  unfold asinPatch
  rw [abs_of_pos ha0]
  by_cases ha : a ≤ 1 / 2
  · rw [ite_eq_left ha]
    exact arcsin_bounds_of_small ha0 ha
  · rw [ite_eq_right ha]
    exact tan_bounds_of_small ha0 ha1

theorem asinPatch_eq {a : ℝ} (ha : |a| ≤ 1 / 2) : asinPatch a = arcsin a := by
  unfold asinPatch
  rw [ite_eq_left ha]

/-- A negative exponent (`e ≤ −1`) bounds `2^e` by `1/2`. -/
theorem two_zpow_le_half {e : AzInt} (hs : e.sign = false) (h1 : 1 ≤ e.abs.toNat) :
    (2 : ℝ) ^ e.toInt ≤ 1 / 2 := by
  have htoInt : e.toInt = if e.sign then (e.abs.toNat : ℤ) else -(e.abs.toNat : ℤ) := rfl
  rw [hs] at htoInt
  simp only [Bool.false_eq_true, ↓reduceIte] at htoInt
  rw [htoInt, zpow_neg, zpow_natCast, ← one_div]
  have h2 : (2 : ℝ) ^ 1 ≤ 2 ^ e.abs.toNat := pow_le_pow_right₀ (by norm_num) h1
  rw [pow_one] at h2
  exact one_div_le_one_div_of_le (by norm_num) h2

/-- The tiny-argument path answers with the rounding of `arcsin x`. -/
theorem asinTiny?_eq {s : Bool} {e : AzInt} {q : ℕ} {m : AzNat} (hv : FiniteValid q m) (p : ℕ)
    [NeZero p] (mode : RoundingMode) {r : AzFloat × Ordering}
    (h : asinTiny? s (finite s e q m hv) e q p mode = some r) :
    r = roundVal p mode (some ((arcsin (finiteVal s e m) : ℝ) : EReal)) := by
  unfold asinTiny? at h
  have hc : e.sign = false ∧ max p q + zivGuardBits + 8 ≤ e.abs.toNat := by
    unfold tanTiny? at h
    dsimp only at h
    by_contra hc
    rw [ite_eq_right hc] at h
    exact absurd h (by simp)
  have hlt := (abs_finiteVal_bounds s e hv).2
  have hhalf := two_zpow_le_half hc.1 (by
    have := hc.2
    unfold zivGuardBits at this
    omega)
  rw [← asinPatch_eq (by linarith : |finiteVal s e m| ≤ 1 / 2)]
  exact tanTiny?_eq_of asinPatch_neg asinPatch_bounds hv p mode h

/-- A number of sign `s` with `|x| = c > 0` is `± c`. -/
theorem eq_signed_of_abs_eq {s : Bool} {xv c : ℝ} (hsgn : s = true ↔ 0 < xv) (hx0 : xv ≠ 0)
    (habs : |xv| = c) : xv = if s then c else -c := by
  cases s with
  | true =>
    simp only [↓reduceIte]
    rw [← habs, abs_of_pos (hsgn.mp rfl)]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hlt : xv < 0 := by
      rcases lt_or_gt_of_ne hx0 with h | h
      · exact h
      · exact absurd (hsgn.mpr h) (by simp)
    rw [← habs, abs_of_neg hlt, neg_neg]

end Azurite.AzFloat
