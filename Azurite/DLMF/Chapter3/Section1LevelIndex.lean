/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# DLMF §3.1(iv)–(v): level-index arithmetic and error measures

* **3.1.7** (`genLog`): `ln₀ x = x`, `ln_ℓ x = ln(ln_{ℓ−1} x)`.
  * For `x ≥ 0` there is a unique `ℓ` with `ln_k x ≥ 1` for `k < ℓ` and `ln_ℓ x ∈ [0, 1)`
    (`existsUnique_level`).
  * The level-index representation `ℓ + a` (`levelIndex`) is decoded by
    `t ↦ exp^{[⌊t⌋]}(t − ⌊t⌋)` (`levelIndexInv_levelIndex`).
  * The uniqueness needs the side condition `ln_k x ≥ 1` for `k < ℓ`, since Mathlib's `log 0 = 0`
    and `log` of a negative number is the logarithm of its absolute value.
* **3.1.8–3.1.11**: the absolute error, relative error, relative precision (principal logarithm)
  and mollified error (`absErr`, `relErr`, `relPrec`, `mollErr`).
  * 3.1.9 (`dlmf_3_1_9`).
  * The mollified error is the absolute error for `|x| ≤ 1` and the relative error for `|x| ≥ 1`
    (`mollErr_eq`).
  * For real `x x* > 0`: the real logarithm (`relPrec_ofReal`), symmetry (`relPrec_symm`), and
    `ε_r ≤ e^{ε_rp} − 1`, `ε_rp ≤ −ln(1 − ε_r)` (`relErr_relPrec`).
* Generalized precision is mentioned without a definition and is not formalized.
-/

namespace Azurite.DLMF

/-! ### §3.1(iv) Level-index arithmetic -/

/-- **DLMF 3.1.7**: the generalized logarithms `ln₀ x = x`, `ln_ℓ x = ln(ln_{ℓ−1} x)`. -/
noncomputable def genLog : ℕ → ℝ → ℝ
  | 0, x => x
  | ℓ + 1, x => Real.log (genLog ℓ x)

theorem genLog_succ' (ℓ : ℕ) (x : ℝ) : genLog (ℓ + 1) x = genLog ℓ (Real.log x) := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih => rw [genLog, ih, genLog]

/-- `ℓ` is a level of `x`: the iterates `ln_k x` stay `≥ 1` for `k < ℓ` (so each logarithm is
taken of a number `≥ 1`) and `ln_ℓ x ∈ [0, 1)`. -/
def IsLevel (x : ℝ) (ℓ : ℕ) : Prop := (∀ k < ℓ, 1 ≤ genLog k x) ∧ genLog ℓ x ∈ Set.Ico 0 1

/-- **The level exists and is unique** for every `x ≥ 0` ("`ℓ` the unique nonnegative integer such
that `a ≡ ln_ℓ(x) ∈ [0, 1)`"). -/
theorem existsUnique_level {x : ℝ} (hx : 0 ≤ x) : ∃! ℓ, IsLevel x ℓ := by
  have hex : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → x < n → ∃ ℓ, IsLevel x ℓ := by
    intro n
    induction n with
    | zero => intro x hx h; exact absurd h (by push_cast; linarith)
    | succ n ih =>
      intro x hx h
      rcases lt_or_ge x 1 with h1 | h1
      · exact ⟨0, fun k hk => absurd hk (Nat.not_lt_zero _), hx, h1⟩
      · have hl0 : 0 ≤ Real.log x := Real.log_nonneg h1
        have hl : Real.log x < n := by
          have := Real.log_le_sub_one_of_pos (by linarith : 0 < x); push_cast at h; linarith
        obtain ⟨ℓ, hk, ha⟩ := ih _ hl0 hl
        refine ⟨ℓ + 1, fun k hk' => ?_, by rw [genLog_succ']; exact ha⟩
        rcases k with _ | k
        · exact h1
        · rw [genLog_succ']; exact hk k (by omega)
  obtain ⟨n, hn⟩ := exists_nat_gt x
  obtain ⟨ℓ, hℓ⟩ := hex n x hx hn
  refine ⟨ℓ, hℓ, fun m hm => ?_⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact absurd (hℓ.1 m h) (not_le.mpr hm.2.2)
  · exact absurd (hm.1 ℓ h) (not_le.mpr hℓ.2.2)

/-- The inverse map: `x = exp^{[ℓ]}(a)` (the `ℓ`-fold exponential of the index). -/
theorem exp_iterate_genLog {x : ℝ} {ℓ : ℕ} (h : ∀ k < ℓ, 0 < genLog k x) :
    Real.exp^[ℓ] (genLog ℓ x) = x := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih =>
    rw [genLog, Function.iterate_succ_apply, Real.exp_log (h ℓ (by omega))]
    exact ih fun k hk => h k (by omega)

/-- **Level-index representation**: `x ≥ 0` is represented by `ℓ + a`, `a = ln_ℓ x ∈ [0, 1)`. -/
noncomputable def levelIndex (x : ℝ) : ℝ :=
  if hx : 0 ≤ x then ((Classical.choose (existsUnique_level hx).exists : ℕ) : ℝ) +
    genLog (Classical.choose (existsUnique_level hx).exists) x else 0

/-- The decoding map `t ↦ exp^{[⌊t⌋]}(t − ⌊t⌋)`. -/
noncomputable def levelIndexInv (t : ℝ) : ℝ := Real.exp^[⌊t⌋₊] (t - ⌊t⌋₊)

/-- **Round trip**: the level-index representation determines `x`. -/
theorem levelIndexInv_levelIndex {x : ℝ} (hx : 0 ≤ x) : levelIndexInv (levelIndex x) = x := by
  set ℓ := Classical.choose (existsUnique_level hx).exists
  have hℓ : IsLevel x ℓ := Classical.choose_spec (existsUnique_level hx).exists
  have hl : levelIndex x = ℓ + genLog ℓ x := by simp only [levelIndex, hx, ↓reduceDIte]; rfl
  have hfl : ⌊levelIndex x⌋₊ = ℓ := by
    rw [hl, Nat.floor_eq_iff (by linarith [hℓ.2.1])]
    exact ⟨by linarith [hℓ.2.1], by linarith [hℓ.2.2]⟩
  rw [levelIndexInv, hfl, hl, add_sub_cancel_left]
  exact exp_iterate_genLog fun k hk => lt_of_lt_of_le one_pos (hℓ.1 k hk)

/-! ### §3.1(v) Error measures -/

/-- **DLMF 3.1.8**: the absolute error `ε_a = |x* − x|`. -/
noncomputable def absErr (xs x : ℂ) : ℝ := ‖xs - x‖

/-- **DLMF 3.1.9**: the relative error `ε_r = |(x* − x)/x|`. -/
noncomputable def relErr (xs x : ℂ) : ℝ := ‖(xs - x) / x‖

/-- **DLMF 3.1.10**: the relative precision `ε_rp = |ln(x*/x)|` (principal logarithm; for real
`x x* > 0` it is the real logarithm, `relPrec_ofReal`). -/
noncomputable def relPrec (xs x : ℂ) : ℝ := ‖Complex.log (xs / x)‖

/-- **DLMF 3.1.11**: the mollified error `ε_m = |x* − x|/max(|x|, 1)`. -/
noncomputable def mollErr (xs x : ℂ) : ℝ := ‖xs - x‖ / max ‖x‖ 1

/-- **DLMF 3.1.9**: `ε_r = ε_a/|x|`. -/
theorem dlmf_3_1_9 (xs x : ℂ) : relErr xs x = absErr xs x / ‖x‖ := by
  rw [relErr, absErr, norm_div]

/-- The mollified error is the absolute error for `|x| ≤ 1` and the relative error for
`|x| ≥ 1`. -/
theorem mollErr_eq (xs x : ℂ) :
    (‖x‖ ≤ 1 → mollErr xs x = absErr xs x) ∧ (1 ≤ ‖x‖ → mollErr xs x = relErr xs x) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [mollErr, max_eq_right h, div_one, absErr]
  · rw [mollErr, max_eq_left h, dlmf_3_1_9, absErr]

/-- For real `x x* > 0` the relative precision is `|ln(x*/x)|` with the real logarithm. -/
theorem relPrec_ofReal {xs x : ℝ} (h : 0 < xs * x) :
    relPrec xs x = |Real.log (xs / x)| := by
  have hq : 0 < xs / x := by
    rcases mul_pos_iff.mp h with h' | h'
    · exact div_pos h'.1 h'.2
    · exact div_pos_of_neg_of_neg h'.1 h'.2
  rw [relPrec, ← Complex.ofReal_div, ← Complex.ofReal_log hq.le, Complex.norm_real,
    Real.norm_eq_abs]

/-- The relative precision is symmetric in `x` and `x*` (real case). -/
theorem relPrec_symm {xs x : ℝ} (h : 0 < xs * x) : relPrec xs x = relPrec x xs := by
  rw [relPrec_ofReal h, relPrec_ofReal (by linarith [mul_comm xs x]), ← abs_neg,
    ← Real.log_inv, inv_div]

/-- Relative error and relative precision (real case): `ε_r ≤ e^{ε_rp} − 1`, and
`ε_rp ≤ −ln(1 − ε_r)` when `ε_r < 1`; so `ε_rp ∼ ε_r` as either tends to `0`. -/
theorem relErr_relPrec {xs x : ℝ} (h : 0 < xs * x) :
    relErr xs x ≤ Real.exp (relPrec xs x) - 1 ∧
      (relErr xs x < 1 → relPrec xs x ≤ -Real.log (1 - relErr xs x)) := by
  have hx : x ≠ 0 := by rintro rfl; simp at h
  have hq : 0 < xs / x := by
    rcases mul_pos_iff.mp h with h' | h'
    · exact div_pos h'.1 h'.2
    · exact div_pos_of_neg_of_neg h'.1 h'.2
  set t := xs / x - 1
  have hrel : relErr xs x = |t| := by
    rw [relErr, ← Complex.ofReal_sub, ← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs,
      sub_div, div_self hx]
  rw [hrel, relPrec_ofReal h, show xs / x = 1 + t by simp only [t]; ring]
  have h1t : 0 < 1 + t := by simp only [t]; linarith
  constructor
  · rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht, abs_of_nonneg (Real.log_nonneg (by linarith)), Real.exp_log h1t]
      linarith
    · rw [abs_of_nonpos ht, abs_of_nonpos (Real.log_nonpos (by linarith) (by linarith)),
        Real.exp_neg, Real.exp_log h1t,
        show (1 + t)⁻¹ - 1 = -t / (1 + t) by field_simp; ring, le_div_iff₀ h1t]
      nlinarith
  · intro ht1
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht] at ht1 ⊢
      rw [abs_of_nonneg (Real.log_nonneg (by linarith)), ← Real.log_inv]
      apply Real.log_le_log h1t
      rw [le_inv_comm₀ h1t (by linarith), inv_eq_one_div, le_div_iff₀ h1t]
      nlinarith
    · rw [abs_of_nonpos ht, abs_of_nonpos (Real.log_nonpos (by linarith) (by linarith)),
        show 1 - -t = 1 + t by ring]

end Azurite.DLMF
