/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Chudnovsky.Transfer
import Azurite.Feldman.Theorem4
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Localization.Integral

/-!
# Transcendence measures for a pair of numbers

`HasMeasure ϖ c`: every nonzero `P ∈ ℤ[X]` of degree `≤ t` and height `≤ 2^t` has
`|P(ϖ)| ≥ 2^(−c t² (size t)³)` — the shape of Fel'dman's measure of `π` (`hasMeasure_pi`).

`transfer_measure`: if `ϖ` has such a measure and `e` is algebraic over `ℚ(ϖ)` (a relation
`R(ϖ, e) = 0` of minimal `Y`-degree), then the same holds for polynomials in `(ϖ, e)`, with
another constant.
-/

namespace Azurite.Chudnovsky

open Polynomial Azurite.Feldman

/-- A transcendence measure of the type `exp(−c t² log³ t)`. -/
def HasMeasure (ϖ : ℂ) (c : ℕ) : Prop :=
  ∀ t : ℕ, 1 ≤ t → ∀ P : ℤ[X], P ≠ 0 → P.natDegree ≤ t → (∀ i, |(P.coeff i : ℝ)| ≤ 2 ^ t) →
    1 ≤ ‖aeval ϖ P‖ * (2 : ℝ) ^ (c * t ^ 2 * Nat.size t ^ 3)

theorem one_le_mul_two_pow_mono {x : ℝ} (hx : 0 ≤ x) {m n : ℕ} (h : 1 ≤ x * (2 : ℝ) ^ m)
    (hmn : m ≤ n) : 1 ≤ x * (2 : ℝ) ^ n :=
  h.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ one_le_two hmn) hx)

/-- **Fel'dman's measure of `π`** in the form `HasMeasure`. -/
theorem hasMeasure_pi : HasMeasure (Real.pi : ℂ) (2 ^ 49) := by
  intro t ht P hP hdeg hH
  refine one_le_mul_two_pow_mono (norm_nonneg _) (pi_measure hP ht hdeg hH) ?_
  set s := Nat.size t with hs
  have hs1 : 1 ≤ s := Nat.size_pos.mpr ht
  set b := 2 * s + 30 with hb
  set u := s ^ 3 with hu
  have hsu : s ≤ u := Nat.le_self_pow (by norm_num) s
  have htu : u ≤ t * u := Nat.le_mul_of_pos_left _ ht
  have hb32 : b ≤ 32 * s := by omega
  have hb3 : b ^ 3 ≤ 32768 * u := by
    calc b ^ 3 ≤ (32 * s) ^ 3 := Nat.pow_le_pow_left hb32 3
      _ = 32768 * u := by rw [hu]; ring
  have h1 : t * b ≤ 32 * (t * u) := by
    calc t * b ≤ t * (32 * u) := Nat.mul_le_mul_left t (by omega)
      _ = 32 * (t * u) := by ring
  have h2 : t * b ^ 3 ≤ 32768 * (t * u) := by
    calc t * b ^ 3 ≤ t * (32768 * u) := Nat.mul_le_mul_left t hb3
      _ = 32768 * (t * u) := by ring
  have hk : kappa t b ≤ 2 ^ 49 * (t * u) := by
    have : kappa t b = 1 + b + 2 * (t * b) + 9934848000 * (t * b ^ 3) := by
      unfold kappa; ring
    rw [this]
    norm_num
    omega
  calc kappa t b * t ≤ 2 ^ 49 * (t * u) * t := Nat.mul_le_mul_right t hk
    _ = 2 ^ 49 * t ^ 2 * s ^ 3 := by rw [hu]; ring

theorem size_mul_le (m n : ℕ) : Nat.size (m * n) ≤ Nat.size m + Nat.size n := by
  rw [Nat.size_le, pow_add]
  exact Nat.mul_lt_mul'' (Nat.lt_size_self m) (Nat.lt_size_self n)

theorem natCast_le_two_pow (n : ℕ) : (n : ℝ) ≤ 2 ^ n := by
  exact_mod_cast Nat.lt_two_pow_self.le

/-- A number with a measure is transcendental. -/
theorem HasMeasure.aeval_ne_zero {ϖ : ℂ} {c : ℕ} (h : HasMeasure ϖ c) {P : ℤ[X]} (hP : P ≠ 0) :
    aeval ϖ P ≠ 0 := by
  intro h0
  set t := P.natDegree + 1 + ⌈l1 (toC P)⌉₊ with ht
  have hH : ∀ i, |(P.coeff i : ℝ)| ≤ 2 ^ t := by
    intro i
    rw [← norm_coeff_toC]
    refine (norm_coeff_le_l1 _ i).trans ((Nat.le_ceil _).trans ?_)
    refine le_trans ?_ (natCast_le_two_pow t)
    exact_mod_cast (by omega : ⌈l1 (toC P)⌉₊ ≤ t)
  have := h t (by omega) P hP (by omega) hH
  rw [h0, norm_zero, zero_mul] at this
  linarith

theorem exists_nat_bounds (xs : List ℝ) : ∃ a : ℕ, 1 ≤ a ∧ ∀ x ∈ xs, x ≤ a ∧ x ≤ 2 ^ a := by
  induction xs with
  | nil => exact ⟨1, le_rfl, by simp⟩
  | cons x xs ih =>
    obtain ⟨a, ha, h⟩ := ih
    refine ⟨a + ⌈x⌉₊, by omega, ?_⟩
    have hmono : (2 : ℝ) ^ a ≤ 2 ^ (a + ⌈x⌉₊) := pow_le_pow_right₀ one_le_two (by omega)
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · have h1 : y ≤ ((a + ⌈y⌉₊ : ℕ) : ℝ) := (Nat.le_ceil y).trans (by exact_mod_cast (by omega))
      exact ⟨h1, h1.trans (natCast_le_two_pow _)⟩
    · exact ⟨(h y hy).1.trans (by exact_mod_cast (by omega)), (h y hy).2.trans hmono⟩

/-- **Transfer of the measure to a pair.** -/
theorem transfer_measure {ϖ e : ℂ} {c₀ : ℕ} (hϖ : HasMeasure ϖ c₀) {R : ℤ[X][X]} {d : ℕ}
    (hd : R.natDegree = d) (hd1 : 0 < d) (hR : ev2 ϖ e R = 0)
    (hmin : ∀ c : ℤ[X][X], c ≠ 0 → c.natDegree < d → ev2 ϖ e c ≠ 0) :
    ∃ c₁ : ℕ, ∀ T : ℕ, 1 ≤ T → ∀ M : ℤ[X][X], M.natDegree ≤ T →
      (∀ k, Sz T (2 ^ T) (M.coeff k)) → ev2 ϖ e M ≠ 0 →
        1 ≤ ‖ev2 ϖ e M‖ * (2 : ℝ) ^ (c₁ * T ^ 2 * Nat.size T ^ 3) := by
  have hR0 : R ≠ 0 := by
    rintro rfl
    rw [natDegree_zero] at hd
    omega
  have hlc : R.coeff d ≠ 0 := by
    rw [← hd]
    exact leadingCoeff_ne_zero.mpr hR0
  have hδ : evX ϖ (R.coeff d) ≠ 0 := hϖ.aeval_ne_zero hlc
  -- the sizes of `R`
  set ρ : ℕ := R.support.sup fun j => (R.coeff j).natDegree with hρdef
  set lam : ℝ := 1 + ∑ j ∈ R.support, l1 (toC (R.coeff j)) with hlamdef
  have hρ : ∀ j, (R.coeff j).natDegree ≤ ρ := by
    intro j
    by_cases hj : j ∈ R.support
    · exact Finset.le_sup (f := fun j => (R.coeff j).natDegree) hj
    · rw [notMem_support_iff.mp hj]
      simp
  have hsum0 : 0 ≤ ∑ j ∈ R.support, l1 (toC (R.coeff j)) :=
    Finset.sum_nonneg fun _ _ => l1_nonneg _
  have hlam1 : 1 ≤ lam := by linarith
  have hlam : ∀ j, l1 (toC (R.coeff j)) ≤ lam := by
    intro j
    by_cases hj : j ∈ R.support
    · have := Finset.single_le_sum (f := fun j => l1 (toC (R.coeff j)))
        (fun _ _ => l1_nonneg _) hj
      linarith
    · rw [notMem_support_iff.mp hj, toC, Polynomial.map_zero, l1_zero]
      linarith
  obtain ⟨a, ha1, hall⟩ := exists_nat_bounds
    [(ρ : ℝ), (d : ℝ), d * lam, max 1 ‖ϖ‖, max 1 ‖e‖, ‖evX ϖ (R.coeff d)‖, (d.factorial : ℝ)]
  have hρa : ρ ≤ a := by exact_mod_cast (hall ρ (by simp)).1
  have hda : d ≤ a := by exact_mod_cast (hall d (by simp)).1
  have hd2 : (d : ℝ) ≤ 2 ^ a := (hall d (by simp)).2
  have hdl : d * lam ≤ 2 ^ a := (hall _ (by simp)).2
  have hW : max 1 ‖ϖ‖ ≤ 2 ^ a := (hall _ (by simp)).2
  have hE : max 1 ‖e‖ ≤ 2 ^ a := (hall _ (by simp)).2
  have hδa : ‖evX ϖ (R.coeff d)‖ ≤ 2 ^ a := (hall _ (by simp)).2
  have hfa : (d.factorial : ℝ) ≤ 2 ^ a := (hall _ (by simp)).2
  set σ := Nat.size (4 * a ^ 2) + 1 with hσ
  refine ⟨9 * a ^ 3 + c₀ * (16 * a ^ 4 * σ ^ 3), fun T hT M hD hM hMne => ?_⟩
  have hgM : ∀ k, (M.coeff k).natDegree ≤ T := fun k => (hM k).1
  have hLM : ∀ k, l1 (toC (M.coeff k)) ≤ (2 : ℝ) ^ T := fun k => (hM k).2
  obtain ⟨𝒟, h0, hdeg, hl1, hval⟩ := transfer hd hd1 hR hδ hmin hρ hlam hlam1 hD hMne hgM hLM
  -- basic monomial facts
  have haa : a ≤ a ^ 2 := Nat.le_self_pow (by norm_num) a
  have haa3 : a ^ 2 ≤ a ^ 3 := Nat.pow_le_pow_right ha1 (by norm_num)
  have m1 : T ≤ a * T := Nat.le_mul_of_pos_left _ ha1
  have m2 : a * T ≤ a ^ 2 * T := Nat.mul_le_mul_right T haa
  have m3 : a ^ 2 * T ≤ a ^ 3 * T := Nat.mul_le_mul_right T haa3
  have m4 : a ≤ a * T := Nat.le_mul_of_pos_right _ hT
  have m5 : a ^ 2 ≤ a ^ 2 * T := Nat.le_mul_of_pos_right _ hT
  have hT1 : ((T + 1 : ℕ) : ℝ) ≤ 2 ^ T := by exact_mod_cast Nat.lt_two_pow_self
  have h2a : (1 : ℝ) ≤ 2 ^ a := one_le_pow₀ one_le_two
  have hdl0 : (0 : ℝ) ≤ d * lam := by positivity
  set t := 4 * a ^ 2 * T with ht
  have ht1 : 1 ≤ t := by
    have : 1 ≤ a ^ 2 * T := Nat.mul_pos (by positivity) hT
    rw [ht]
    linarith
  -- the inner quantity
  have hinner : ((T + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ T * (d * lam) ^ T) ≤ 2 ^ (2 * T + a * T) := by
    calc ((T + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ T * (d * lam) ^ T)
        ≤ 2 ^ T * (2 ^ T * (2 ^ a) ^ T) := by gcongr
      _ = 2 ^ (2 * T + a * T) := by
          rw [← pow_mul, ← pow_add, ← pow_add]
          congr 1
          ring
  have hinner1 : (1 : ℝ) ≤ 2 ^ (2 * T + a * T) := one_le_pow₀ one_le_two
  -- degree and height of `𝒟`
  have hdeg' : 𝒟.natDegree ≤ t := by
    refine hdeg.trans ?_
    calc d * (T + T * ρ) ≤ a * (T + T * a) :=
          Nat.mul_le_mul hda (Nat.add_le_add_left (Nat.mul_le_mul_left T hρa) T)
      _ = a * T + a ^ 2 * T := by ring
      _ ≤ t := by rw [ht]; linarith
  have hl1' : l1 (toC 𝒟) ≤ (2 : ℝ) ^ t := by
    refine hl1.trans ?_
    calc (d.factorial : ℝ) * (((T + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ T * (d * lam) ^ T)) ^ d
        ≤ 2 ^ a * (2 ^ (2 * T + a * T)) ^ d := by gcongr
      _ ≤ 2 ^ a * (2 ^ (2 * T + a * T)) ^ a := by
          gcongr
      _ = 2 ^ (a + (2 * T + a * T) * a) := by rw [← pow_mul, ← pow_add]
      _ ≤ 2 ^ t := by
          refine pow_le_pow_right₀ one_le_two ?_
          have : (2 * T + a * T) * a = 2 * (a * T) + a ^ 2 * T := by ring
          rw [this, ht]
          linarith
  have hH : ∀ i, |(𝒟.coeff i : ℝ)| ≤ 2 ^ t := fun i => by
    rw [← norm_coeff_toC]
    exact (norm_coeff_le_l1 _ i).trans hl1'
  have hmeas := hϖ t ht1 𝒟 h0 hdeg' hH
  rw [← evX_apply] at hmeas
  -- the upper bound for `𝒟(ϖ)`
  have hB : max 1 (((T + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ T * (d * lam) ^ T)
      * max 1 ‖ϖ‖ ^ (T + T * ρ)) ≤ 2 ^ (5 * a ^ 2 * T) := by
    refine max_le (one_le_pow₀ one_le_two) ?_
    calc ((T + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ T * (d * lam) ^ T) * max 1 ‖ϖ‖ ^ (T + T * ρ)
        ≤ 2 ^ (2 * T + a * T) * (2 ^ a) ^ (T + T * ρ) := by gcongr
      _ ≤ 2 ^ (2 * T + a * T) * (2 ^ a) ^ (T + T * a) := by
          gcongr
      _ = 2 ^ (2 * T + a * T + a * (T + T * a)) := by rw [← pow_mul, ← pow_add]
      _ ≤ 2 ^ (5 * a ^ 2 * T) := by
          refine pow_le_pow_right₀ one_le_two ?_
          have : a * (T + T * a) = a * T + a ^ 2 * T := by ring
          rw [this]
          linarith
  have hfac : (d : ℝ) * (d.factorial
      * (max 1 (((T + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ T * (d * lam) ^ T)
        * max 1 ‖ϖ‖ ^ (T + T * ρ))) ^ d) * max 1 ‖e‖ ^ d
      ≤ 2 ^ (2 * a + 5 * a ^ 3 * T + a ^ 2) := by
    calc _ ≤ (2 : ℝ) ^ a * (2 ^ a * (2 ^ (5 * a ^ 2 * T)) ^ d) * (2 ^ a) ^ d := by gcongr
      _ ≤ (2 : ℝ) ^ a * (2 ^ a * (2 ^ (5 * a ^ 2 * T)) ^ a) * (2 ^ a) ^ a := by
          gcongr
          exact one_le_pow₀ one_le_two
      _ = 2 ^ (2 * a + 5 * a ^ 3 * T + a ^ 2) := by
          rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
          ring
  have hup : ‖evX ϖ 𝒟‖ ≤ ‖ev2 ϖ e M‖ * 2 ^ (9 * a ^ 3 * T) := by
    refine hval.trans ?_
    calc ‖evX ϖ (R.coeff d)‖ ^ T * ‖ev2 ϖ e M‖ * _
        ≤ (2 ^ a) ^ T * ‖ev2 ϖ e M‖ * 2 ^ (2 * a + 5 * a ^ 3 * T + a ^ 2) := by gcongr
      _ = ‖ev2 ϖ e M‖ * 2 ^ (a * T + (2 * a + 5 * a ^ 3 * T + a ^ 2)) := by
          rw [← pow_mul, pow_add]
          ring
      _ ≤ ‖ev2 ϖ e M‖ * 2 ^ (9 * a ^ 3 * T) := by
          refine mul_le_mul_of_nonneg_left (pow_le_pow_right₀ one_le_two ?_) (norm_nonneg _)
          linarith
  -- the exponent
  have hsize : Nat.size t ≤ σ * Nat.size T := by
    have h1 := size_mul_le (4 * a ^ 2) T
    have h2 : 1 ≤ Nat.size T := Nat.size_pos.mpr hT
    calc Nat.size t ≤ Nat.size (4 * a ^ 2) + Nat.size T := h1
      _ ≤ Nat.size (4 * a ^ 2) * Nat.size T + Nat.size T :=
          Nat.add_le_add_right (Nat.le_mul_of_pos_right _ h2) _
      _ = σ * Nat.size T := by rw [hσ]; ring
  have hexp : c₀ * t ^ 2 * Nat.size t ^ 3 ≤ c₀ * (16 * a ^ 4 * σ ^ 3) * T ^ 2 * Nat.size T ^ 3 := by
    calc c₀ * t ^ 2 * Nat.size t ^ 3 ≤ c₀ * t ^ 2 * (σ * Nat.size T) ^ 3 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsize 3)
      _ = c₀ * (16 * a ^ 4 * σ ^ 3) * T ^ 2 * Nat.size T ^ 3 := by rw [ht]; ring
  have hS1 : 1 ≤ Nat.size T ^ 3 := Nat.one_le_pow _ _ (Nat.size_pos.mpr hT)
  have hlin : 9 * a ^ 3 * T ≤ 9 * a ^ 3 * T ^ 2 * Nat.size T ^ 3 := by
    calc 9 * a ^ 3 * T ≤ 9 * a ^ 3 * (T ^ 2 * Nat.size T ^ 3) :=
          Nat.mul_le_mul_left _ ((Nat.le_self_pow (by norm_num) T).trans
            (Nat.le_mul_of_pos_right _ hS1))
      _ = 9 * a ^ 3 * T ^ 2 * Nat.size T ^ 3 := by ring
  have hfinal : 1 ≤ ‖ev2 ϖ e M‖ * (2 : ℝ) ^ (9 * a ^ 3 * T + c₀ * t ^ 2 * Nat.size t ^ 3) := by
    calc (1 : ℝ) ≤ ‖evX ϖ 𝒟‖ * 2 ^ (c₀ * t ^ 2 * Nat.size t ^ 3) := hmeas
      _ ≤ ‖ev2 ϖ e M‖ * 2 ^ (9 * a ^ 3 * T) * 2 ^ (c₀ * t ^ 2 * Nat.size t ^ 3) := by gcongr
      _ = _ := by rw [pow_add]; ring
  refine one_le_mul_two_pow_mono (norm_nonneg _) hfinal ?_
  calc 9 * a ^ 3 * T + c₀ * t ^ 2 * Nat.size t ^ 3
      ≤ 9 * a ^ 3 * T ^ 2 * Nat.size T ^ 3
        + c₀ * (16 * a ^ 4 * σ ^ 3) * T ^ 2 * Nat.size T ^ 3 := Nat.add_le_add hlin hexp
    _ = (9 * a ^ 3 + c₀ * (16 * a ^ 4 * σ ^ 3)) * T ^ 2 * Nat.size T ^ 3 := by ring

/-! ### The measure of `2π/√3` -/

theorem l1_toC_C (n : ℤ) : l1 (toC (C n)) = |(n : ℝ)| := by
  have h : toC (C n) = C (n : ℂ) * 1 := by simp [toC]
  rw [h, l1_C_mul, l1_one, mul_one, Complex.norm_intCast]

theorem Sz_C (n : ℤ) : Sz 0 |(n : ℝ)| (C n) := ⟨by simp, (l1_toC_C n).le⟩

theorem Sz.add {g : ℕ} {B₁ B₂ : ℝ} {p q : ℤ[X]} (hp : Sz g B₁ p) (hq : Sz g B₂ q) :
    Sz g (B₁ + B₂) (p + q) := by
  refine ⟨(natDegree_add_le _ _).trans (max_le hp.1 hq.1), ?_⟩
  rw [toC, Polynomial.map_add]
  exact (l1_add_le _ _).trans (add_le_add hp.2 hq.2)

theorem ev2_map_C (ϖ e : ℂ) (S : ℤ[X]) : ev2 ϖ e (S.map C) = aeval e S := by
  unfold ev2
  rw [coe_eval₂RingHom, eval₂_map, aeval_def]
  congr 1
  exact RingHom.ext_int _ _

/-- No rational `q` has `3 a² = 4 b²` with `b ≠ 0`. -/
theorem three_mul_sq_ne {a b : ℤ} (hb : b ≠ 0) : 3 * a ^ 2 ≠ 4 * b ^ 2 := by
  intro h
  have ha : a ≠ 0 := by
    rintro rfl
    have : b ^ 2 = 0 := by omega
    exact hb (pow_eq_zero_iff (by norm_num) |>.mp this)
  have hirr : Irrational (Real.sqrt 3) := by
    have := Nat.Prime.irrational_sqrt Nat.prime_three
    simpa using this
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hq : ((|2 * b / a| : ℚ) : ℝ) ^ 2 = 3 := by
    have hR : (3 : ℝ) * (a : ℝ) ^ 2 = 4 * (b : ℝ) ^ 2 := by exact_mod_cast h
    push_cast
    rw [sq_abs]
    field_simp
    linarith
  have hsq : Real.sqrt 3 = ((|2 * b / a| : ℚ) : ℝ) := by
    rw [← hq, Real.sqrt_sq (by exact_mod_cast abs_nonneg _)]
  exact hirr.ne_rat _ hsq

/-- A root of `3Y² = 4π²` is transcendental. -/
theorem aeval_ne_zero_of_sq {ϖ : ℂ} (hsq : 3 * ϖ ^ 2 = 4 * (Real.pi : ℂ) ^ 2) {P : ℤ[X]}
    (hP : P ≠ 0) : aeval ϖ P ≠ 0 := by
  intro h0
  have h1 : IsAlgebraic ℚ ϖ := (IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mp ⟨P, hP, h0⟩
  have h2 : IsAlgebraic ℚ ((Real.pi : ℂ) ^ 2) := by
    have : (Real.pi : ℂ) ^ 2 = algebraMap ℚ ℂ (3 / 4) * ϖ ^ 2 := by
      have : algebraMap ℚ ℂ (3 / 4) = 3 / 4 := by simp
      rw [this]
      linear_combination (-1 / 4 : ℂ) * hsq
    rw [this]
    exact (isAlgebraic_algebraMap _).mul (h1.pow 2)
  exact Azurite.Feldman.transcendental_pi
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mpr (h2.of_pow (by norm_num)))

/-- **A measure for the roots of `3Y² = 4π²`.** -/
theorem exists_hasMeasure_of_sq {ϖ : ℂ} (hsq : 3 * ϖ ^ 2 = 4 * (Real.pi : ℂ) ^ 2) :
    ∃ c : ℕ, HasMeasure ϖ c := by
  set R : ℤ[X][X] := C (C 3) * X ^ 2 - C (C 4 * X ^ 2) with hRdef
  have hdeg : R.natDegree = 2 := by
    rw [hRdef, natDegree_sub_C, natDegree_C_mul_X_pow]
    simp
  have hR : ev2 (Real.pi : ℂ) ϖ R = 0 := by
    simp only [hRdef, ev2, evX, coe_eval₂RingHom, eval₂_sub, eval₂_mul, eval₂_C, eval₂_pow,
      eval₂_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul, map_pow, aeval_C, aeval_X]
    simp only [eq_intCast, Int.cast_ofNat]
    linear_combination hsq
  have hmin : ∀ c : ℤ[X][X], c ≠ 0 → c.natDegree < 2 → ev2 (Real.pi : ℂ) ϖ c ≠ 0 := by
    intro c hc hcd hev
    obtain ⟨c₁, c₀, rfl⟩ : ∃ c₁ c₀ : ℤ[X], c = C c₁ * X + C c₀ :=
      ⟨_, _, eq_X_add_C_of_natDegree_le_one (by omega)⟩
    have hev' : aeval (Real.pi : ℂ) c₁ * ϖ + aeval (Real.pi : ℂ) c₀ = 0 := by
      simpa [ev2, evX] using hev
    have hP : aeval (Real.pi : ℂ) (3 * c₀ ^ 2 - 4 * X ^ 2 * c₁ ^ 2) = 0 := by
      simp only [map_sub, map_mul, map_pow, aeval_X, map_ofNat]
      linear_combination (3 * (aeval (Real.pi : ℂ) c₀ - aeval (Real.pi : ℂ) c₁ * ϖ)) * hev'
        + (aeval (Real.pi : ℂ) c₁) ^ 2 * hsq
    have hP0 : 3 * c₀ ^ 2 - 4 * X ^ 2 * c₁ ^ 2 = 0 := by
      by_contra hne
      exact hasMeasure_pi.aeval_ne_zero hne hP
    have heq : 3 * c₀ ^ 2 = 4 * X ^ 2 * c₁ ^ 2 := sub_eq_zero.mp hP0
    by_cases h1 : c₁ = 0
    · rw [h1] at heq
      have h0 : c₀ = 0 := by
        have : (3 : ℤ[X]) * c₀ ^ 2 = 0 := by rw [heq]; ring
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h (by norm_num)
        · exact pow_eq_zero_iff (by norm_num) |>.mp h
      apply hc
      rw [h1, h0]
      simp
    · have hl := congrArg leadingCoeff heq
      simp only [leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_X, one_pow, mul_one] at hl
      have e3 : leadingCoeff (3 : ℤ[X]) = 3 := leadingCoeff_C (3 : ℤ)
      have e4 : leadingCoeff (4 : ℤ[X]) = 4 := leadingCoeff_C (4 : ℤ)
      rw [e3, e4] at hl
      exact three_mul_sq_ne (leadingCoeff_ne_zero.mpr h1) hl
  obtain ⟨c₁, hc₁⟩ := transfer_measure hasMeasure_pi hdeg (by norm_num) hR hmin
  refine ⟨c₁, fun t ht P hP hdegP hH => ?_⟩
  have hne : ev2 (Real.pi : ℂ) ϖ (P.map C) ≠ 0 := by
    rw [ev2_map_C]
    exact aeval_ne_zero_of_sq hsq hP
  have := hc₁ t ht (P.map C) (natDegree_map_le.trans hdegP) (fun k => by
    rw [coeff_map]
    exact (Sz_C _).mono (Nat.zero_le _) (hH k)) hne
  rwa [ev2_map_C] at this

/-- **A measure for `2π/√3`.** -/
theorem exists_hasMeasure_two_pi_div_sqrt_three :
    ∃ c : ℕ, HasMeasure (2 * (Real.pi : ℂ) / (Real.sqrt 3 : ℝ)) c := by
  have h3 : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  refine exists_hasMeasure_of_sq ?_
  rw [div_pow, h3]
  ring

/-! ### The measure with coefficients in an imaginary quadratic order -/

/-- `M ∈ ℤ[X][Y]` has degrees `≤ T` and coefficients of `ℓ¹`-norm `≤ 2^T`. -/
def BSz (T : ℕ) (M : ℤ[X][X]) : Prop := M.natDegree ≤ T ∧ ∀ k, Sz T (2 ^ T) (M.coeff k)

/-- A measure for the values `A(ϖ, e) + τ B(ϖ, e)`. -/
def PairMeasure (ϖ e τ : ℂ) (c : ℕ) : Prop :=
  ∀ T : ℕ, 1 ≤ T → ∀ A B : ℤ[X][X], BSz T A → BSz T B → ev2 ϖ e A + τ * ev2 ϖ e B ≠ 0 →
    1 ≤ ‖ev2 ϖ e A + τ * ev2 ϖ e B‖ * (2 : ℝ) ^ (c * T ^ 2 * Nat.size T ^ 3)

theorem Sz_coeff_mul {T : ℕ} {A B : ℤ[X][X]} (hA : BSz T A) (hB : BSz T B) (k : ℕ) :
    Sz (2 * T) ((2 * T + 1 : ℕ) * ((2 : ℝ) ^ T * 2 ^ T)) ((A * B).coeff k) := by
  by_cases hk : k ≤ 2 * T
  · rw [coeff_mul]
    have h := Sz.sum (Finset.antidiagonal k) (f := fun x => A.coeff x.1 * B.coeff x.2)
      (fun x _ => (hA.2 x.1).mul (hB.2 x.2))
    rw [Finset.Nat.card_antidiagonal] at h
    refine h.mono (by omega) ?_
    gcongr
  · rw [coeff_eq_zero_of_natDegree_lt
      (natDegree_mul_le.trans_lt (by have := hA.1; have := hB.1; omega))]
    exact Sz.zero _ (by positivity)

theorem norm_ev2_le {T : ℕ} {M : ℤ[X][X]} (hM : BSz T M) (ϖ e : ℂ) :
    ‖ev2 ϖ e M‖ ≤ (T + 1 : ℕ) * ((2 : ℝ) ^ T * max 1 ‖ϖ‖ ^ T * max 1 ‖e‖ ^ T) := by
  rw [ev2_eq_sum ϖ e hM.1]
  refine (norm_sum_le _ _).trans ?_
  have hE : (1 : ℝ) ≤ max 1 ‖e‖ := le_max_left _ _
  have hterm : ∀ k ∈ Finset.range (T + 1), ‖evX ϖ (M.coeff k) * e ^ k‖
      ≤ (2 : ℝ) ^ T * max 1 ‖ϖ‖ ^ T * max 1 ‖e‖ ^ T := by
    intro k hk
    have hk' : k ≤ T := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [norm_mul, norm_pow]
    refine mul_le_mul ((hM.2 k).norm_evX_le ϖ) ?_ (by positivity) (by positivity)
    exact (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _).trans
      (pow_le_pow_right₀ hE hk')
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem ev2_C_C (ϖ e : ℂ) (n : ℤ) : ev2 ϖ e (C (C n)) = n := by
  simp [ev2, evX]

/-- **The measure for `A(ϖ, e) + τ B(ϖ, e)`** from the measure for `M(ϖ, e)`: `τ` is a root of
`x² − p x + q`, `τ′` the other root. -/
theorem pairMeasure_of {ϖ e τ τ' : ℂ} {p q : ℤ} (hp : τ + τ' = p) (hq : τ * τ' = q)
    (hp1 : |p| ≤ 1) (hq1 : |q| ≤ 1) (hτ : 1 ≤ ‖τ - τ'‖) (hτ' : ‖τ'‖ ≤ 1) {c₁ : ℕ}
    (h : ∀ T : ℕ, 1 ≤ T → ∀ M : ℤ[X][X], BSz T M → ev2 ϖ e M ≠ 0 →
      1 ≤ ‖ev2 ϖ e M‖ * (2 : ℝ) ^ (c₁ * T ^ 2 * Nat.size T ^ 3)) :
    ∃ c : ℕ, PairMeasure ϖ e τ c := by
  obtain ⟨a, ha1, hall⟩ := exists_nat_bounds [max 1 ‖ϖ‖, max 1 ‖e‖]
  have hW : max 1 ‖ϖ‖ ≤ 2 ^ a := (hall _ (by simp)).2
  have hE : max 1 ‖e‖ ≤ 2 ^ a := (hall _ (by simp)).2
  refine ⟨2304 * c₁ + 2 * a + 3, fun T hT A B hA hB hne => ?_⟩
  set vA := ev2 ϖ e A with hvA
  set vB := ev2 ϖ e B with hvB
  have hS1 : 1 ≤ Nat.size T := Nat.size_pos.mpr hT
  have hS3 : 1 ≤ Nat.size T ^ 3 := Nat.one_le_pow _ _ hS1
  have hTT : T ≤ T ^ 2 * Nat.size T ^ 3 :=
    (Nat.le_self_pow (by norm_num) T).trans (Nat.le_mul_of_pos_right _ hS3)
  set Nm : ℤ[X][X] := A * A + C (C p) * (A * B) + C (C q) * (B * B) with hNm
  have hNmval : ev2 ϖ e Nm = (vA + τ * vB) * (vA + τ' * vB) := by
    rw [hNm, map_add, map_add, map_mul, map_mul, map_mul, map_mul, map_mul, ev2_C_C, ev2_C_C,
      ← hp, ← hq]
    ring
  by_cases hN0 : ev2 ϖ e Nm = 0
  · -- the conjugate vanishes
    rw [hNmval] at hN0
    have hconj : vA + τ' * vB = 0 := (mul_eq_zero.mp hN0).resolve_left hne
    have heq : vA + τ * vB = (τ - τ') * vB := by linear_combination hconj
    have hB0 : vB ≠ 0 := by
      intro h0
      apply hne
      rw [heq, h0, mul_zero]
    have h1 := h T hT B hB hB0
    have hle : ‖vB‖ ≤ ‖vA + τ * vB‖ := by
      rw [heq, norm_mul]
      exact le_mul_of_one_le_left (norm_nonneg _) hτ
    refine one_le_mul_two_pow_mono (norm_nonneg _)
      (h1.trans (mul_le_mul_of_nonneg_right hle (by positivity))) ?_
    calc c₁ * T ^ 2 * Nat.size T ^ 3 ≤ (2304 * c₁ + 2 * a + 3) * (T ^ 2 * Nat.size T ^ 3) := by
          rw [mul_assoc]
          exact Nat.mul_le_mul_right _ (by omega)
      _ = (2304 * c₁ + 2 * a + 3) * T ^ 2 * Nat.size T ^ 3 := by ring
  · -- the size of the norm
    have hK : (3 : ℝ) * ((2 * T + 1 : ℕ) * ((2 : ℝ) ^ T * 2 ^ T)) ≤ 2 ^ (6 * T) := by
      have h3 : (3 : ℝ) ≤ 2 ^ (2 * T) := by
        calc (3 : ℝ) ≤ 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (2 * T) := pow_le_pow_right₀ one_le_two (by omega)
      have h4 : ((2 * T + 1 : ℕ) : ℝ) ≤ 2 ^ (2 * T) := by exact_mod_cast Nat.lt_two_pow_self
      calc (3 : ℝ) * ((2 * T + 1 : ℕ) * ((2 : ℝ) ^ T * 2 ^ T))
          ≤ 2 ^ (2 * T) * (2 ^ (2 * T) * (2 ^ T * 2 ^ T)) := by gcongr
        _ = 2 ^ (6 * T) := by
            rw [← pow_add, ← pow_add, ← pow_add]
            congr 1
            ring
    have hpR : |(p : ℝ)| ≤ 1 := by exact_mod_cast hp1
    have hqR : |(q : ℝ)| ≤ 1 := by exact_mod_cast hq1
    have hNsz : BSz (6 * T) Nm := by
      refine ⟨?_, fun k => ?_⟩
      · have h1 : (A * A).natDegree ≤ 2 * T := natDegree_mul_le.trans (by have := hA.1; omega)
        have h2 : (C (C p) * (A * B)).natDegree ≤ 2 * T :=
          (natDegree_C_mul_le _ _).trans
            (natDegree_mul_le.trans (by have := hA.1; have := hB.1; omega))
        have h3 : (C (C q) * (B * B)).natDegree ≤ 2 * T :=
          (natDegree_C_mul_le _ _).trans (natDegree_mul_le.trans (by have := hB.1; omega))
        have := (natDegree_add_le _ _).trans
          (max_le ((natDegree_add_le _ _).trans (max_le h1 h2)) h3)
        rw [hNm]
        omega
      · rw [hNm, coeff_add, coeff_add, coeff_C_mul, coeff_C_mul]
        have s1 := Sz_coeff_mul hA hA k
        have s2 := (Sz_C p).mul (Sz_coeff_mul hA hB k)
        have s3 := (Sz_C q).mul (Sz_coeff_mul hB hB k)
        refine ((s1.add (s2.mono (by omega) le_rfl)).add (s3.mono (by omega) le_rfl)).mono
          (by omega) (le_trans ?_ hK)
        have hK0 : (0 : ℝ) ≤ (2 * T + 1 : ℕ) * ((2 : ℝ) ^ T * 2 ^ T) := by positivity
        nlinarith [mul_le_mul_of_nonneg_right hpR hK0, mul_le_mul_of_nonneg_right hqR hK0]
    have h1 := h (6 * T) (by omega) Nm hNsz hN0
    rw [hNmval, norm_mul] at h1
    -- the conjugate is not large
    have hconj : ‖vA + τ' * vB‖ ≤ 2 ^ (1 + 2 * T + 2 * (a * T)) := by
      have hb : ∀ {M : ℤ[X][X]}, BSz T M → ‖ev2 ϖ e M‖ ≤ 2 ^ (2 * T + 2 * (a * T)) := by
        intro M hM
        refine (norm_ev2_le hM ϖ e).trans ?_
        have hT1 : ((T + 1 : ℕ) : ℝ) ≤ 2 ^ T := by exact_mod_cast Nat.lt_two_pow_self
        calc ((T + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ T * max 1 ‖ϖ‖ ^ T * max 1 ‖e‖ ^ T)
            ≤ 2 ^ T * (2 ^ T * (2 ^ a) ^ T * (2 ^ a) ^ T) := by gcongr
          _ = 2 ^ (2 * T + 2 * (a * T)) := by
              rw [← pow_mul, ← pow_add, ← pow_add, ← pow_add]
              congr 1
              ring
      calc ‖vA + τ' * vB‖ ≤ ‖vA‖ + ‖τ'‖ * ‖vB‖ := (norm_add_le _ _).trans (by rw [norm_mul])
        _ ≤ 2 ^ (2 * T + 2 * (a * T)) + 1 * 2 ^ (2 * T + 2 * (a * T)) :=
            add_le_add (hb hA) (mul_le_mul hτ' (hb hB) (norm_nonneg _) zero_le_one)
        _ = 2 ^ (1 + 2 * T + 2 * (a * T)) := by
            rw [add_assoc 1, pow_add 2 1]
            ring
    have hfinal : 1 ≤ ‖vA + τ * vB‖
        * (2 : ℝ) ^ (1 + 2 * T + 2 * (a * T) + c₁ * (6 * T) ^ 2 * Nat.size (6 * T) ^ 3) := by
      calc (1 : ℝ) ≤ ‖vA + τ * vB‖ * ‖vA + τ' * vB‖
            * 2 ^ (c₁ * (6 * T) ^ 2 * Nat.size (6 * T) ^ 3) := h1
        _ ≤ ‖vA + τ * vB‖ * 2 ^ (1 + 2 * T + 2 * (a * T))
            * 2 ^ (c₁ * (6 * T) ^ 2 * Nat.size (6 * T) ^ 3) := by gcongr
        _ = _ := by rw [pow_add _ (1 + 2 * T + 2 * (a * T))]; ring
    refine one_le_mul_two_pow_mono (norm_nonneg _) hfinal ?_
    have hsz : Nat.size (6 * T) ≤ 4 * Nat.size T := by
      have h6 : Nat.size 6 ≤ 3 := Nat.size_le.mpr (by norm_num)
      have := size_mul_le 6 T
      omega
    have hc : c₁ * (6 * T) ^ 2 * Nat.size (6 * T) ^ 3
        ≤ 2304 * c₁ * (T ^ 2 * Nat.size T ^ 3) := by
      calc c₁ * (6 * T) ^ 2 * Nat.size (6 * T) ^ 3 ≤ c₁ * (6 * T) ^ 2 * (4 * Nat.size T) ^ 3 :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsz 3)
        _ = 2304 * c₁ * (T ^ 2 * Nat.size T ^ 3) := by ring
    have haT : a * T ≤ a * (T ^ 2 * Nat.size T ^ 3) := Nat.mul_le_mul_left a hTT
    calc 1 + 2 * T + 2 * (a * T) + c₁ * (6 * T) ^ 2 * Nat.size (6 * T) ^ 3
        ≤ 3 * (T ^ 2 * Nat.size T ^ 3) + 2 * (a * (T ^ 2 * Nat.size T ^ 3))
          + 2304 * c₁ * (T ^ 2 * Nat.size T ^ 3) := by omega
      _ = (2304 * c₁ + 2 * a + 3) * T ^ 2 * Nat.size T ^ 3 := by ring

/-- **The pair measure in the algebraically dependent case.**  If `ϖ` has a measure and
`(ϖ, e)` satisfy a nonzero polynomial relation, then `(ϖ, e)` has a pair measure. -/
theorem exists_pairMeasure {ϖ e τ τ' : ℂ} {p q : ℤ} (hp : τ + τ' = p) (hq : τ * τ' = q)
    (hp1 : |p| ≤ 1) (hq1 : |q| ≤ 1) (hτ : 1 ≤ ‖τ - τ'‖) (hτ' : ‖τ'‖ ≤ 1) {c₀ : ℕ}
    (hϖ : HasMeasure ϖ c₀) {R : ℤ[X][X]} (hR0 : R ≠ 0) (hR : ev2 ϖ e R = 0) :
    ∃ c : ℕ, PairMeasure ϖ e τ c := by
  classical
  -- a relation of minimal degree
  have hex : ∃ d : ℕ, ∃ R : ℤ[X][X], R ≠ 0 ∧ ev2 ϖ e R = 0 ∧ R.natDegree = d :=
    ⟨_, R, hR0, hR, rfl⟩
  obtain ⟨R', hR'0, hR', hd⟩ := Nat.find_spec hex
  set d := Nat.find hex with hddef
  have hmin : ∀ c : ℤ[X][X], c ≠ 0 → c.natDegree < d → ev2 ϖ e c ≠ 0 := by
    intro c hc hcd h0
    exact Nat.find_min hex hcd ⟨c, hc, h0, rfl⟩
  have hd1 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · exfalso
      rw [h0] at hd
      rw [eq_C_of_natDegree_eq_zero hd] at hR' hR'0
      have hc0 : R'.coeff 0 ≠ 0 := fun h => hR'0 (by rw [h, C_0])
      have : ev2 ϖ e (C (R'.coeff 0)) = aeval ϖ (R'.coeff 0) := by simp [ev2, evX]
      rw [this] at hR'
      exact hϖ.aeval_ne_zero hc0 hR'
    · exact h0
  obtain ⟨c₁, hc₁⟩ := transfer_measure hϖ hd hd1 hR' hmin
  exact pairMeasure_of hp hq hp1 hq1 hτ hτ' fun T hT M hM hne => hc₁ T hT M hM.1 hM.2 hne

end Azurite.Chudnovsky
