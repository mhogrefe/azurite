/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Chudnovsky.Independence

/-!
# The core of Chudnovsky's theorem: a pair measure is contradictory

`CMData.core_false`: for a CM lattice, a pair measure for `(ϖ, e)` (which exists when `ϖ` and
`e` are algebraically dependent, `exists_pairMeasure`) leads to a contradiction, given a
system of parameters `Params` (whose existence is pure arithmetic, proved separately).

Stages `s ≥ s₀`, with `N(s) = 2^(16s)`, `H(s) = 2^(10s)`: the auxiliary function `Φ`
(`exists_start`) vanishes to order `N(s)` at the points `1/2 + m + nτ`, `0 ≤ m, n < H(s)`.
The start is Dirichlet's box principle with the dichotomy `Rep.dichotomy`; the step from `s`
to `s + 1` is `cauchy_PhiC` on the parallelogram of size `K(s) = 2^s · 16 H(s+1)` (gain
`2^(−s N H²)`) with the dichotomy.  Hence all derivatives of `Φ` vanish at `1/2`, `Φ ≡ 0`,
all coefficients vanish (`coef_eq_zero`), and `ϖ` would be algebraic.
-/

namespace Azurite.Chudnovsky

open MvPolynomial UpperHalfPlane Filter Topology

/-- The order of vanishing at stage `s`. -/
def Nst (s : ℕ) : ℕ := 2 ^ (16 * s)

/-- The size of the box of points at stage `s`. -/
def Hst (s : ℕ) : ℕ := 2 ^ (10 * s)

/-- The size of the parallelogram in the step from `s` to `s + 1`. -/
def Kst (s : ℕ) : ℕ := 2 ^ s * (16 * Hst (s + 1))

/-- The growth bound in the step from `s` to `s + 1`. -/
def Ghat (γ Lc J ζ s : ℕ) : ℕ :=
  (16 * Kst s + 4) ^ ((2 * Kst s + 1) ^ 2 * (3 * Lc))
    * (Lc ^ 3 * (J * (2 ^ ζ * (2 ^ γ) ^ J)
      * ((4 * Kst s + 2) * 2 ^ γ * (2 ^ γ * (Kst s + 1))) ^ Lc))

/-- A system of parameters for the proof. -/
structure Params (cst γ : ℕ) where
  /-- the first stage -/
  s₀ : ℕ
  /-- the degree in each of `z`, `℘`, `ζ` -/
  Lc : ℕ
  /-- the degree in `ϖ` -/
  J : ℕ
  /-- the unknowns are `≤ 2^ζ` -/
  ζ : ℕ
  /-- the exponent of the box principle -/
  ν : ℕ
  /-- the size of the values at stage `s` -/
  T : ℕ → ℕ
  hcount : ν * (Nst s₀ * (Hst s₀ * Hst s₀) * 2) < ζ * (Lc ^ 3 * J)
  hstart : 4 * (Lc ^ 3 * J * 2 ^ ζ * ((8 * (3 * Lc + J + Nst s₀)) ^ Nst s₀
      * (7 * Hst s₀ * 2 ^ γ) ^ (3 * Lc + J + Nst s₀)))
        * 2 ^ (cst * T s₀ ^ 2 * Nat.size (T s₀) ^ 3) < 2 ^ ν
  hTd : ∀ s, s₀ ≤ s → 3 * Lc + J + Nst s ≤ T s
  hTB : ∀ s, s₀ ≤ s → (8 * (3 * Lc + J + Nst s)) ^ Nst s * (Lc ^ 3 * J * 2 ^ ζ)
      * (3 * (1 + 4 * Hst s)) ^ (3 * Lc + J + Nst s) ≤ 2 ^ T s
  hstep : ∀ s, s₀ ≤ s → Nst (s + 1) ^ Nst (s + 1) * 8 ^ Nst (s + 1) * Ghat γ Lc J ζ s
      * 2 ^ (cst * T (s + 1) ^ 2 * Nat.size (T (s + 1)) ^ 3) < 2 ^ (s * (Nst s * Hst s ^ 2))

theorem one_le_Nst (s : ℕ) : 1 ≤ Nst s := Nat.one_le_two_pow

theorem one_le_Hst (s : ℕ) : 1 ≤ Hst s := Nat.one_le_two_pow

theorem Hst_le_succ (s : ℕ) : Hst s ≤ Hst (s + 1) :=
  Nat.pow_le_pow_right (by norm_num) (by omega)

theorem lt_Nst (n : ℕ) : n < Nst n :=
  lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem Nst_mono {s t : ℕ} (h : s ≤ t) : Nst s ≤ Nst t :=
  Nat.pow_le_pow_right (by norm_num) (by omega)

theorem Nst_def (s : ℕ) : Nst s = 2 ^ (16 * s) := rfl

theorem Hst_def (s : ℕ) : Hst s = 2 ^ (10 * s) := rfl

theorem Kst_def (s : ℕ) : Kst s = 2 ^ s * (16 * Hst (s + 1)) := rfl

theorem Ghat_def (γ Lc J ζ s : ℕ) : Ghat γ Lc J ζ s
    = (16 * Kst s + 4) ^ ((2 * Kst s + 1) ^ 2 * (3 * Lc))
      * (Lc ^ 3 * (J * (2 ^ ζ * (2 ^ γ) ^ J)
        * ((4 * Kst s + 2) * 2 ^ γ * (2 ^ γ * (Kst s + 1))) ^ Lc)) := rfl

attribute [irreducible] Nst Hst Kst Ghat

namespace CMData

variable (D : CMData)

theorem coB_wpt (m n : ℤ) : coB D.τ (D.wpt m n) = n := by
  have h := coB_add_mul D.τ (1 / 2 + m : ℝ) (n : ℝ)
  have e1 : D.wpt m n = ((1 / 2 + m : ℝ) : ℂ) + ((n : ℝ) : ℂ) * D.τ := by
    rw [wpt]
    push_cast
    ring
  rw [e1, h]

theorem coA_wpt (m n : ℤ) : coA D.τ (D.wpt m n) = 1 / 2 + m := by
  have h := coA_add_mul D.τ (1 / 2 + m : ℝ) (n : ℝ)
  have e1 : D.wpt m n = ((1 / 2 + m : ℝ) : ℂ) + ((n : ℝ) : ℂ) * D.τ := by
    rw [wpt]
    push_cast
    ring
  rw [e1, h]

theorem wpt_injective :
    Function.Injective fun x : ℕ × ℕ => D.wpt (x.1 : ℤ) (x.2 : ℤ) := by
  intro x y hxy
  simp only at hxy
  have hB := congrArg (coB D.τ) hxy
  have hA := congrArg (coA D.τ) hxy
  rw [coB_wpt, coB_wpt] at hB
  rw [coA_wpt, coA_wpt] at hA
  have h1 : (x.1 : ℝ) = y.1 := by
    push_cast at hA
    linarith
  have h2 : (x.2 : ℝ) = y.2 := by exact_mod_cast hB
  exact Prod.ext (by exact_mod_cast h1) (by exact_mod_cast h2)

/-- The points of stage `s`. -/
noncomputable def Zst (s : ℕ) : Finset ℂ :=
  (Finset.range (Hst s) ×ˢ Finset.range (Hst s)).image fun x => D.wpt (x.1 : ℤ) (x.2 : ℤ)

theorem card_Zst (s : ℕ) : (D.Zst s).card = Hst s ^ 2 := by
  rw [Zst, Finset.card_image_of_injective _ D.wpt_injective, Finset.card_product,
    Finset.card_range]
  ring

theorem norm_wpt_nat_le {m n H : ℕ} (hm : m < H) (hn : n < H) :
    ‖D.wpt (m : ℤ) (n : ℤ)‖ ≤ 2 * H - 3 / 2 := by
  have h1 : |(((m : ℤ) : ℝ))| ≤ (H : ℝ) - 1 := by
    rw [Int.cast_natCast, Nat.abs_cast]
    have : (m : ℝ) + 1 ≤ H := by exact_mod_cast hm
    linarith
  have h2 : |(((n : ℤ) : ℝ))| ≤ (H : ℝ) - 1 := by
    rw [Int.cast_natCast, Nat.abs_cast]
    have : (n : ℝ) + 1 ≤ H := by exact_mod_cast hn
    linarith
  have := D.norm_wpt_le h1 h2
  linarith

/-- The auxiliary function for the integers `a`. -/
noncomputable def PhiA {cst γ : ℕ} (P : Params cst γ) (a : ℕ × ℕ × ℕ × ℕ → ℤ) : ℂ → ℂ :=
  PhiC (pairOf D.τ) P.Lc (coefC D.ϖ P.J a)

theorem PhiA_deriv {cst γ : ℕ} (P : Params cst γ) (a : ℕ × ℕ × ℕ × ℕ → ℤ) (n m n' : ℕ) :
    iteratedDeriv n (D.PhiA P a) (D.wpt (m : ℤ) (n' : ℤ))
      = aeval (D.ptH (m : ℤ) (n' : ℤ)) ((dD D.c)^[n] (polyQ P.Lc P.J a)) :=
  D.iteratedDeriv_PhiC_wpt P.Lc P.J a n m n'

/-- The dichotomy at stage `s`. -/
theorem dich {cst γ : ℕ} (hmeas : PairMeasure D.ϖ D.e D.τ cst) (P : Params cst γ)
    {a : ℕ × ℕ × ℕ × ℕ → ℤ} (habs : ∀ x, |(a x : ℝ)| ≤ 2 ^ P.ζ) (s : ℕ) (hs : P.s₀ ≤ s)
    (n : ℕ) (hn : n < Nst s) (m : ℕ) (hm : m < Hst s) (n' : ℕ) (hn' : n' < Hst s) :
    iteratedDeriv n (D.PhiA P a) (D.wpt (m : ℤ) (n' : ℤ)) = 0 ∨
      1 ≤ ‖iteratedDeriv n (D.PhiA P a) (D.wpt (m : ℤ) (n' : ℤ))‖
        * (2 : ℝ) ^ (cst * P.T s ^ 2 * Nat.size (P.T s) ^ 3) := by
  rw [PhiA_deriv]
  have hrep := D.rep_value P.Lc P.J habs n (m : ℤ) (n' : ℤ)
  have hTd := P.hTd s hs
  have hN1 := one_le_Nst s
  refine hrep.dichotomy hmeas (by omega) (by omega) ?_
  rw [mul_div_cancel_left₀ _ (by norm_num : (3 : ℝ) ≠ 0)]
  have hTB : ((8 * (3 * P.Lc + P.J + Nst s : ℕ) : ℝ)) ^ Nst s * (P.Lc ^ 3 * P.J * 2 ^ P.ζ)
      * (3 * (1 + 4 * (Hst s : ℝ))) ^ (3 * P.Lc + P.J + Nst s) ≤ 2 ^ P.T s := by
    exact_mod_cast P.hTB s hs
  refine le_trans ?_ hTB
  have hd1 : (1 : ℝ) ≤ 8 * ((3 * P.Lc + P.J + Nst s : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ ((3 * P.Lc + P.J + Nst s : ℕ) : ℝ) := by exact_mod_cast (by omega)
    linarith
  have f1 : (8 * ((3 * P.Lc + P.J + n : ℕ) : ℝ)) ^ n
      ≤ (8 * ((3 * P.Lc + P.J + Nst s : ℕ) : ℝ)) ^ Nst s :=
    (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left
      (Nat.cast_le.mpr (by omega)) (by norm_num)) n).trans (pow_le_pow_right₀ hd1 hn.le)
  have hm' : |(((m : ℤ) : ℝ))| ≤ Hst s := by
    rw [Int.cast_natCast, Nat.abs_cast]
    exact_mod_cast hm.le
  have hn'' : |(((n' : ℤ) : ℝ))| ≤ Hst s := by
    rw [Int.cast_natCast, Nat.abs_cast]
    exact_mod_cast hn'.le
  have hb1 : (1 : ℝ) ≤ 3 * (1 + 4 * (Hst s : ℝ)) := by
    have : (0 : ℝ) ≤ Hst s := by positivity
    linarith
  have f3 : (3 * (1 + 2 * |(((m : ℤ) : ℝ))| + 2 * |(((n' : ℤ) : ℝ))|)) ^ (3 * P.Lc + P.J + n)
      ≤ (3 * (1 + 4 * (Hst s : ℝ))) ^ (3 * P.Lc + P.J + Nst s) :=
    (pow_le_pow_left₀ (by positivity) (by linarith) _).trans
      (pow_le_pow_right₀ hb1 (by omega))
  exact mul_le_mul (mul_le_mul_of_nonneg_right f1 (by positivity)) f3 (by positivity)
    (by positivity)

/-- The step from stage `s` to stage `s + 1`. -/
theorem step_false {cst γ : ℕ} {C₁ C₂ : ℝ}
    (hC₁ : ∀ z, Far D.τ z → ‖(pairOf D.τ).weierstrassP z‖ ≤ C₁) (hC₂0 : 0 ≤ C₂)
    (hC₂ : ∀ z, Far D.τ z → ‖weierstrassZeta (pairOf D.τ) z‖ ≤ C₂ * (1 + ‖z‖))
    (hγϖ : ‖D.ϖ‖ ≤ 2 ^ γ) (hγ1 : max 1 C₁ ≤ 2 ^ γ) (hγ2 : max 1 (4 * C₂) ≤ 2 ^ γ)
    (P : Params cst γ) {a : ℕ × ℕ × ℕ × ℕ → ℤ} (habs : ∀ x, |(a x : ℝ)| ≤ 2 ^ P.ζ) (s : ℕ)
    (hs : P.s₀ ≤ s)
    (ih : ∀ n < Nst s, ∀ m < Hst s, ∀ n' < Hst s,
      iteratedDeriv n (D.PhiA P a) (D.wpt (m : ℤ) (n' : ℤ)) = 0)
    (n : ℕ) (hn : n < Nst (s + 1)) (m : ℕ) (hm : m < Hst (s + 1)) (n' : ℕ)
    (hn' : n' < Hst (s + 1))
    (h1 : 1 ≤ ‖iteratedDeriv n (D.PhiA P a) (D.wpt (m : ℤ) (n' : ℤ))‖
      * (2 : ℝ) ^ (cst * P.T (s + 1) ^ 2 * Nat.size (P.T (s + 1)) ^ 3)) : False := by
  have h2γ : (1 : ℝ) ≤ 2 ^ γ := one_le_pow₀ one_le_two
  set V := iteratedDeriv n (D.PhiA P a) (D.wpt (m : ℤ) (n' : ℤ)) with hVdef
  have hH1 : (1 : ℝ) ≤ Hst s := by exact_mod_cast one_le_Hst s
  have hH1' : (1 : ℝ) ≤ Hst (s + 1) := by exact_mod_cast one_le_Hst (s + 1)
  have hHH : (Hst s : ℝ) ≤ Hst (s + 1) := by exact_mod_cast Hst_le_succ s
  have h2s : (1 : ℝ) ≤ 2 ^ s := one_le_pow₀ one_le_two
  have hK : (Kst s : ℝ) = 2 ^ s * (16 * (Hst (s + 1) : ℝ)) := by
    rw [Kst_def]
    push_cast
    ring
  have hK16 : 16 * (Hst (s + 1) : ℝ) ≤ Kst s := by
    rw [hK]
    exact le_mul_of_one_le_left (by positivity) h2s
  have hA : ∀ i j k, ‖coefC D.ϖ P.J a i j k‖ ≤ P.J * (2 ^ P.ζ * (2 ^ γ) ^ P.J) :=
    fun i j k => norm_coefC_le h2γ hγϖ P.J habs i j k
  have hZ : ∀ b ∈ D.Zst s, b ∉ (pairOf D.τ).lattice ∧ ‖b‖ ≤ 2 * (Hst s : ℝ) ∧
      ∀ ν < Nst s, iteratedDeriv ν (PhiC (pairOf D.τ) P.Lc (coefC D.ϖ P.J a)) b = 0 := by
    intro b hb
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
    simp only [Finset.mem_product, Finset.mem_range] at hx
    refine ⟨D.wpt_notMem _ _, ?_, fun ν hν => ih ν hν x.1 hx.1 x.2 hx.2⟩
    have := D.norm_wpt_nat_le hx.1 hx.2
    linarith
  have hc := cauchy_PhiC D.hn D.hr hC₁ hC₂0 hC₂ P.Lc (coefC D.ϖ P.J a) hA (D.Zst s)
    (Nst s) (r₀ := 2 * (Hst s : ℝ)) (r₁ := 2 * (Hst (s + 1) : ℝ)) (by positivity) hZ
    (Kst s) (by linarith) (by linarith) (D.wpt_far (m : ℤ) (n' : ℤ))
    (by
      have := D.norm_wpt_nat_le hm hn'
      linarith) n
  rw [card_Zst] at hc
  change ‖V‖ * _ ≤ _ at hc
  set M := Nst s * Hst s ^ 2 with hM
  set r : ℝ := 2 * (Hst s : ℝ) + 2 * (Hst (s + 1) : ℝ) with hr
  have hr0 : 0 < r := by positivity
  -- the gain
  have hgain : (2 : ℝ) ^ s * r ≤ (Kst s : ℝ) / 4 := by
    rw [hK, hr]
    have h4 : 2 * (Hst s : ℝ) + 2 * (Hst (s + 1) : ℝ) ≤ 4 * (Hst (s + 1) : ℝ) := by linarith
    calc (2 : ℝ) ^ s * (2 * (Hst s : ℝ) + 2 * (Hst (s + 1) : ℝ))
        ≤ 2 ^ s * (4 * (Hst (s + 1) : ℝ)) := mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = 2 ^ s * (16 * (Hst (s + 1) : ℝ)) / 4 := by ring
  have hgainM : ((2 : ℝ) ^ s) ^ M * r ^ M ≤ ((Kst s : ℝ) / 4) ^ M := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hgain M
  -- the growth
  set e := (2 * Kst s + 1) ^ 2 * (3 * P.Lc) with he
  have hB : (4 * (Kst s : ℝ) + 2) * max 1 C₁ * max 1 (4 * C₂ * ((Kst s : ℝ) + 1))
      ≤ (4 * (Kst s : ℝ) + 2) * 2 ^ γ * (2 ^ γ * ((Kst s : ℝ) + 1)) := by
    have hK0 : (0 : ℝ) ≤ Kst s := by positivity
    have h2 : max 1 (4 * C₂ * ((Kst s : ℝ) + 1)) ≤ 2 ^ γ * ((Kst s : ℝ) + 1) := by
      refine max_le (one_le_mul_of_one_le_of_one_le h2γ (by linarith)) ?_
      have := (le_max_right 1 (4 * C₂)).trans hγ2
      exact mul_le_mul_of_nonneg_right this (by linarith)
    have h1 : (0 : ℝ) ≤ max 1 C₁ := le_trans zero_le_one (le_max_left _ _)
    have h3 : (0 : ℝ) ≤ max 1 (4 * C₂ * ((Kst s : ℝ) + 1)) :=
      le_trans zero_le_one (le_max_left _ _)
    gcongr
  have hG : (16 * (Kst s : ℝ) + 4) ^ e * (P.Lc ^ 3 * (P.J * (2 ^ P.ζ * (2 ^ γ) ^ P.J)
      * ((4 * (Kst s : ℝ) + 2) * max 1 C₁ * max 1 (4 * C₂ * ((Kst s : ℝ) + 1))) ^ P.Lc))
      ≤ (Ghat γ P.Lc P.J P.ζ s : ℝ) := by
    rw [Ghat_def]
    push_cast
    have h1 : (0 : ℝ) ≤ max 1 C₁ := le_trans zero_le_one (le_max_left _ _)
    have h3 : (0 : ℝ) ≤ max 1 (4 * C₂ * ((Kst s : ℝ) + 1)) :=
      le_trans zero_le_one (le_max_left _ _)
    gcongr
  have hfac : (n.factorial : ℝ) * 8 ^ n
      ≤ ((Nst (s + 1) : ℕ) : ℝ) ^ Nst (s + 1) * 8 ^ Nst (s + 1) := by
    have h1 : (n.factorial : ℝ) ≤ ((Nst (s + 1) : ℕ) : ℝ) ^ Nst (s + 1) := by
      have hN1 : 1 ≤ Nst (s + 1) := one_le_Nst _
      have : n.factorial ≤ Nst (s + 1) ^ Nst (s + 1) :=
        (Nat.factorial_le_pow n).trans ((Nat.pow_le_pow_left hn.le n).trans
          (Nat.pow_le_pow_right hN1 hn.le))
      exact_mod_cast this
    have h2 : (8 : ℝ) ^ n ≤ 8 ^ Nst (s + 1) := pow_le_pow_right₀ (by norm_num) hn.le
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  -- `|V| 2^(sM) ≤ n! 8ⁿ Ĝ`
  have hV1 : ‖V‖ * ((2 : ℝ) ^ s) ^ M
      ≤ ((Nst (s + 1) : ℕ) : ℝ) ^ Nst (s + 1) * 8 ^ Nst (s + 1)
        * (Ghat γ P.Lc P.J P.ζ s : ℝ) := by
    have hrM : (0 : ℝ) < r ^ M := by positivity
    have h1 : ‖V‖ * ((2 : ℝ) ^ s) ^ M * r ^ M
        ≤ ((Nst (s + 1) : ℕ) : ℝ) ^ Nst (s + 1) * 8 ^ Nst (s + 1)
          * (Ghat γ P.Lc P.J P.ζ s : ℝ) * r ^ M := by
      calc ‖V‖ * ((2 : ℝ) ^ s) ^ M * r ^ M = ‖V‖ * (((2 : ℝ) ^ s) ^ M * r ^ M) := by ring
        _ ≤ ‖V‖ * ((Kst s : ℝ) / 4) ^ M :=
            mul_le_mul_of_nonneg_left hgainM (norm_nonneg _)
        _ ≤ _ := hc
        _ ≤ ((Nst (s + 1) : ℕ) : ℝ) ^ Nst (s + 1) * 8 ^ Nst (s + 1)
              * (r ^ M * (Ghat γ P.Lc P.J P.ζ s : ℝ)) := by
            refine mul_le_mul hfac (mul_le_mul_of_nonneg_left hG hrM.le)
              (by positivity) (by positivity)
        _ = _ := by ring
    exact le_of_mul_le_mul_right h1 hrM
  have hstep : (((Nst (s + 1) : ℕ) : ℝ) ^ Nst (s + 1) * 8 ^ Nst (s + 1)
      * (Ghat γ P.Lc P.J P.ζ s : ℝ)
      * 2 ^ (cst * P.T (s + 1) ^ 2 * Nat.size (P.T (s + 1)) ^ 3) : ℝ)
      < 2 ^ (s * M) := by
    exact_mod_cast P.hstep s hs
  rw [← pow_mul] at hV1
  have hpos : (0 : ℝ) < 2 ^ (cst * P.T (s + 1) ^ 2 * Nat.size (P.T (s + 1)) ^ 3) := by
    positivity
  have h2M : (0 : ℝ) < 2 ^ (s * M) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hV1 hpos.le, mul_le_mul_of_nonneg_right h1 h2M.le]

/-- **A pair measure is contradictory.** -/
theorem core_false {cst γ : ℕ} (hmeas : PairMeasure D.ϖ D.e D.τ cst) {C₁ C₂ : ℝ}
    (hC₁ : ∀ z, Far D.τ z → ‖(pairOf D.τ).weierstrassP z‖ ≤ C₁) (hC₂0 : 0 ≤ C₂)
    (hC₂ : ∀ z, Far D.τ z → ‖weierstrassZeta (pairOf D.τ) z‖ ≤ C₂ * (1 + ‖z‖))
    (hγϖ : ‖D.ϖ‖ ≤ 2 ^ γ) (hγe : ‖D.e‖ ≤ 2 ^ γ) (hγ1 : max 1 C₁ ≤ 2 ^ γ)
    (hγ2 : max 1 (4 * C₂) ≤ 2 ^ γ)
    (htr : ∀ P : Polynomial ℤ, P ≠ 0 → Polynomial.aeval D.ϖ P ≠ 0) (P : Params cst γ) :
    False := by
  obtain ⟨a, ⟨x₀, hx₀, hax₀⟩, habs, hsmall⟩ := D.exists_start P.Lc P.J (Nst P.s₀) (Hst P.s₀)
    P.ζ P.ν γ P.hcount (one_le_Hst _) hγϖ hγe
  set Φ := D.PhiA P a with hΦ
  -- the stages
  have hstage : ∀ s, P.s₀ ≤ s → ∀ n < Nst s, ∀ m < Hst s, ∀ n' < Hst s,
      iteratedDeriv n Φ (D.wpt (m : ℤ) (n' : ℤ)) = 0 := by
    intro s hs
    induction s, hs using Nat.le_induction with
    | base =>
      intro n hn m hm n' hn'
      rcases D.dich hmeas P habs P.s₀ le_rfl n hn m hm n' hn' with h0 | h1
      · exact h0
      · exfalso
        have hsm := hsmall n hn m hm n' hn'
        rw [← D.PhiA_deriv P a] at hsm
        have hst : (4 * (P.Lc ^ 3 * P.J * 2 ^ P.ζ * ((8 * ((3 * P.Lc + P.J + Nst P.s₀ : ℕ) : ℝ))
            ^ Nst P.s₀ * (7 * (Hst P.s₀ : ℝ) * 2 ^ γ) ^ (3 * P.Lc + P.J + Nst P.s₀)))
              * 2 ^ (cst * P.T P.s₀ ^ 2 * Nat.size (P.T P.s₀) ^ 3) : ℝ) < 2 ^ P.ν := by
          exact_mod_cast P.hstart
        have hpos : (0 : ℝ) < 2 ^ (cst * P.T P.s₀ ^ 2 * Nat.size (P.T P.s₀) ^ 3) := by positivity
        have hν : (0 : ℝ) < 2 ^ P.ν := by positivity
        have := mul_le_mul_of_nonneg_right hsm hpos.le
        nlinarith [mul_le_mul_of_nonneg_right h1 hν.le]
    | succ s hs ih =>
      intro n hn m hm n' hn'
      rcases D.dich hmeas P habs (s + 1) (by omega) n hn m hm n' hn' with h0 | h1
      · exact h0
      · exact (D.step_false hC₁ hC₂0 hC₂ hγϖ hγ1 hγ2 P habs s hs ih n hn m hm n' hn' h1).elim
  -- all derivatives vanish at `1/2`
  have hall : ∀ n, iteratedDeriv n Φ (D.wpt 0 0) = 0 := by
    intro n
    have hn : n < Nst (max P.s₀ n) :=
      lt_of_le_of_lt (le_max_right _ _) (lt_Nst _)
    have := hstage (max P.s₀ n) (le_max_left _ _) n hn 0 (one_le_Hst _) 0 (one_le_Hst _)
    simpa using this
  have hw : D.wpt 0 0 ∈ ((pairOf D.τ).lattice : Set ℂ)ᶜ := D.wpt_notMem 0 0
  have hU : IsOpen ((pairOf D.τ).lattice : Set ℂ)ᶜ := (pairOf D.τ).isClosed_lattice.isOpen_compl
  have hΦa : AnalyticOnNhd ℂ Φ ((pairOf D.τ).lattice : Set ℂ)ᶜ :=
    (differentiableOn_PhiC (pairOf D.τ) P.Lc (coefC D.ϖ P.J a)).analyticOnNhd hU
  have htop : analyticOrderAt Φ (D.wpt 0 0) = ⊤ := by
    by_contra hne
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hne
    have h1 : ((k + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt Φ (D.wpt 0 0) :=
      (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hΦa _ hw)).mpr fun i _ => hall i
    rw [← hk] at h1
    exact absurd (Nat.cast_le.mp h1) (by omega)
  have hzero : ∀ z, z ∉ D.L.lattice → Φ z = 0 := fun z hz =>
    hΦa.eqOn_zero_of_preconnected_of_eventuallyEq_zero (isPreconnected_compl_lattice _) hw
      (analyticOrderAt_eq_top.mp htop) hz
  -- the coefficients vanish
  have hx₀' := mem_idx.mp hx₀
  have hc0 := D.coef_eq_zero (fun h0 => htr 1 one_ne_zero (by
    have : D.ϖ ≠ 0 := fun h => htr Polynomial.X Polynomial.X_ne_zero (by simpa using h)
    exact absurd h0 this)) hzero x₀.1 hx₀'.1 x₀.2.1 hx₀'.2.1 x₀.2.2.1 hx₀'.2.2.1
  set Pz : Polynomial ℤ := ∑ l ∈ Finset.range P.J,
    Polynomial.C (a (x₀.1, x₀.2.1, x₀.2.2.1, l)) * Polynomial.X ^ l with hPz
  have hPz0 : Pz ≠ 0 := by
    intro h0
    have hcf : Pz.coeff x₀.2.2.2 = a x₀ := by
      rw [hPz, Polynomial.finsetSum_coeff]
      simp only [Polynomial.coeff_C_mul_X_pow]
      rw [Finset.sum_ite_eq (Finset.range P.J) x₀.2.2.2]
      simp [hx₀'.2.2.2]
    rw [h0, Polynomial.coeff_zero] at hcf
    exact hax₀ hcf.symm
  refine htr Pz hPz0 ?_
  rw [hPz, map_sum, ← hc0]
  unfold coefC
  refine Finset.sum_congr rfl fun l _ => ?_
  simp

end CMData

end Azurite.Chudnovsky
