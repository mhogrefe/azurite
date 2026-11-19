/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Feldman.Auxiliary
import Azurite.Feldman.Extrapolation
import Azurite.Feldman.Dirichlet
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Fel'dman's Theorem 3: `π` is not well approximated by algebraic numbers

N. I. Fel'dman, *Approximation of certain transcendental numbers. I*, Izv. Akad. Nauk SSSR
Ser. Mat. 15 (1951), 53–74, §2, Theorem 3, with the bookkeeping in powers of two (plan and
parameters: `docs/chudnovsky_plan.md`).

`Thm3Data` bundles an algebraic number `ξ` (a root of an irreducible `p ∈ ℤ[X]` of degree `n`
with `(n + 1) H ≤ 2^(N b)`), the parameters `q₀, q, s₀, x₀, c, g, b, Φ` with the inequalities
between them, and the assumption `|ξ − π| < 2^(−Φ)`; the theorem is that there is no such
data (`Thm3Data.false`).
-/

namespace Azurite.Feldman

open Polynomial Finset

/-- An integer polynomial of degree less than that of an irreducible `p` that vanishes at a
root of `p` is zero. -/
theorem eq_zero_of_aeval_eq_zero {p R : ℤ[X]} (hp : Irreducible p) (hn : p.natDegree ≠ 0)
    {ξ : ℂ} (hξ : aeval ξ p = 0) (hR : aeval ξ R = 0) (hdeg : R.natDegree < p.natDegree) :
    R = 0 := by
  by_contra hR0
  have hq : Irreducible (p.map (Int.castRingHom ℚ)) :=
    (IsPrimitive.Int.irreducible_iff_irreducible_map_cast (hp.isPrimitive hn)).mp hp
  have hev : ∀ (q : ℤ[X]) (z : ℂ), aeval z (q.map (Int.castRingHom ℚ)) = aeval z q := fun q z =>
    aeval_map_algebraMap ℚ z q
  have hRq : R.map (Int.castRingHom ℚ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff Int.cast_injective).mpr hR0
  by_cases hdvd : p.map (Int.castRingHom ℚ) ∣ R.map (Int.castRingHom ℚ)
  · have h1 := natDegree_le_of_dvd hdvd hRq
    rw [natDegree_map_eq_of_injective Int.cast_injective,
      natDegree_map_eq_of_injective Int.cast_injective] at h1
    omega
  · obtain ⟨u, v, huv⟩ := (hq.coprime_iff_not_dvd).mpr hdvd
    have := congrArg (aeval ξ) huv
    rw [map_add, map_mul, map_mul, hev p ξ, hev R ξ, hξ, hR, mul_zero, mul_zero, add_zero,
      map_one] at this
    exact zero_ne_one this

/-- The data of a counterexample to Theorem 3. -/
structure Thm3Data where
  p : ℤ[X]
  ξ : ℂ
  H : ℝ
  N : ℕ
  q₀ : ℕ
  q : ℕ
  s₀ : ℕ
  x₀ : ℕ
  c : ℕ
  g : ℕ
  b : ℕ
  Φ : ℕ
  hp : Irreducible p
  hn : p.natDegree ≠ 0
  hξ : aeval ξ p = 0
  hH : ∀ i, |(p.coeff i : ℝ)| ≤ H
  hHN : (p.natDegree + 1) * H ≤ (2 : ℝ) ^ (N * b)
  hsmall : ‖ξ - Real.pi‖ * (2 : ℝ) ^ Φ < 1
  hsize : 64 * (q₀ + q + s₀ + p.natDegree) ≤ 2 ^ b
  hq₀ : 1 ≤ q₀
  hq : 1 ≤ q
  hx₀ : 1 ≤ x₀
  hqs : q ≤ s₀
  hx₀q : x₀ ≤ 2 * q₀
  h2 : g * (2 * s₀ * (x₀ + 1)) ≤ c * (q₀ * (q * p.natDegree))
  h3 : c + (3 * p.natDegree + 3 * b + b * s₀ + b * q₀)
      + (2 * p.natDegree * (c + (3 * p.natDegree + 3 * b + b * s₀ + b * q₀))
        + 2 * b * p.natDegree + 3 * (q₀ + p.natDegree) * (N * b)) + 4 ≤ g
  h4a : 42 * q ≤ s₀
  h4 : b * s₀ + c + (3 * p.natDegree + 3 * b + b * s₀ + b * q₀)
      + (2 * p.natDegree * (c + (3 * p.natDegree + 3 * b + b * s₀ + b * q₀))
        + 2 * b * p.natDegree + 3 * (q₀ + p.natDegree) * (N * b)) + 2 ≤ (s₀ - 42 * q) * x₀
  h5 : 2 * b * s₀ * q₀ + 2 * b * s₀ + c + (3 * p.natDegree + 3 * b + b * s₀ + b * q₀)
      + (2 * p.natDegree * (c + (3 * p.natDegree + 3 * b + b * s₀ + b * q₀))
        + 2 * b * p.natDegree + 3 * (q₀ + p.natDegree) * (N * b)) + 4 * b + 6 ≤ Φ
  h6 : q + b * q + q₀ + c + (3 * p.natDegree + 3 * b + b * s₀ + b * q₀) + 3 * b
      + p.natDegree * (b + c + N * b) + 1 ≤ Φ

namespace Thm3Data

variable (D : Thm3Data)

/-- The degree `n` of `ξ`. -/
noncomputable abbrev n : ℕ := D.p.natDegree

/-- `W = 3n + 3b + b s₀ + b q₀`. -/
noncomputable abbrev W : ℕ := 3 * D.n + 3 * D.b + D.b * D.s₀ + D.b * D.q₀

/-- `Y = 2n(c + W) + 2bn + 3(q₀ + n) N b`. -/
noncomputable abbrev Y : ℕ :=
  2 * D.n * (D.c + D.W) + 2 * D.b * D.n + 3 * (D.q₀ + D.n) * (D.N * D.b)

theorem n_pos : 1 ≤ D.n := Nat.one_le_iff_ne_zero.mpr D.hn

/-- Everything of the size of the parameters is at most `2^b`. -/
theorem cast_le_two_pow {a : ℕ} (h : a ≤ 64 * (D.q₀ + D.q + D.s₀ + D.n)) :
    (a : ℝ) ≤ (2 : ℝ) ^ D.b := by
  exact_mod_cast h.trans D.hsize

theorem eps_lt : ‖D.ξ - Real.pi‖ < 1 := by
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ D.Φ := one_le_pow₀ (by norm_num)
  have h2 := D.hsmall
  nlinarith [norm_nonneg (D.ξ - Real.pi)]

theorem norm_ξ_le : ‖D.ξ‖ ≤ 5 := by
  have h1 : ‖D.ξ‖ ≤ ‖D.ξ - Real.pi‖ + ‖(Real.pi : ℂ)‖ := by
    have := norm_add_le (D.ξ - Real.pi) (Real.pi : ℂ)
    rwa [sub_add_cancel] at this
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos] at h1
  linarith [D.eps_lt, Real.pi_lt_four]

/-- `‖ξ − π‖ 2^e < 1` for every exponent `e ≤ Φ`. -/
theorem eps_mul_lt {e : ℕ} (he : e ≤ D.Φ) : ‖D.ξ - Real.pi‖ * (2 : ℝ) ^ e < 1 := by
  have h1 : (2 : ℝ) ^ e ≤ (2 : ℝ) ^ D.Φ := pow_le_pow_right₀ (by norm_num) he
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)) D.hsmall

/-! ### The bounds for `V` in powers of two -/

theorem five_pow_le (n : ℕ) : (5 : ℝ) ^ n ≤ (2 : ℝ) ^ (3 * n) := by
  rw [pow_mul]
  exact pow_le_pow_left₀ (by norm_num) (by norm_num) n

theorem q₀_le : (D.q₀ : ℝ) ≤ (2 : ℝ) ^ D.b := D.cast_le_two_pow (by omega)
theorem q_le : (D.q : ℝ) ≤ (2 : ℝ) ^ D.b := D.cast_le_two_pow (by omega)
theorem s₀_le : (D.s₀ : ℝ) ≤ (2 : ℝ) ^ D.b := D.cast_le_two_pow (by omega)
theorem n_le : (D.n : ℝ) ≤ (2 : ℝ) ^ D.b := D.cast_le_two_pow (by omega)

theorem add_pow_le {s : ℕ} (hs : s ≤ D.s₀) :
    ((D.q₀ : ℝ) + D.q) ^ s ≤ ((2 : ℝ) ^ D.b) ^ D.s₀ := by
  have h1 : (D.q₀ : ℝ) + D.q ≤ (2 : ℝ) ^ D.b := by
    have := D.cast_le_two_pow (a := D.q₀ + D.q) (by omega)
    push_cast at this
    exact this
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ D.b := one_le_pow₀ (by norm_num)
  exact (pow_le_pow_left₀ (by positivity) h1 s).trans (pow_le_pow_right₀ h2 hs)

/-- The common size `q (q₀ + q)^s q₀ n 2^c 5ⁿ (2^b)^{q₀} ≤ 2^(c + W)`. -/
theorem size_le {s : ℕ} (hs : s ≤ D.s₀) :
    (D.q : ℝ) * (((D.q₀ : ℝ) + D.q) ^ s * (D.q₀ * (D.n * ((2 : ℝ) ^ D.c * 5 ^ D.n)))
      * ((2 : ℝ) ^ D.b) ^ D.q₀) ≤ (2 : ℝ) ^ (D.c + D.W) := by
  have h1 := D.q_le
  have h2 := D.add_pow_le hs
  have h3 := D.q₀_le
  have h4 := D.n_le
  have h5 := five_pow_le D.n
  calc (D.q : ℝ) * (((D.q₀ : ℝ) + D.q) ^ s * (D.q₀ * (D.n * ((2 : ℝ) ^ D.c * 5 ^ D.n)))
        * ((2 : ℝ) ^ D.b) ^ D.q₀)
      ≤ (2 : ℝ) ^ D.b * (((2 : ℝ) ^ D.b) ^ D.s₀ * ((2 : ℝ) ^ D.b * ((2 : ℝ) ^ D.b
          * ((2 : ℝ) ^ D.c * (2 : ℝ) ^ (3 * D.n)))) * ((2 : ℝ) ^ D.b) ^ D.q₀) := by gcongr
    _ = (2 : ℝ) ^ (D.c + D.W) := by
        rw [← pow_mul, ← pow_mul]
        simp only [← pow_add]
        congr 1
        unfold W
        ring

variable {y : ℕ × ℕ × ℕ → ℤ}

/-- `|V(s, x, w)| ≤ 2^(c + W)` for `s ≤ s₀`, `x ≤ 4q₀`, `|w| ≤ 5`. -/
theorem norm_auxV_le_two_pow (hy : ∀ j, |(y j : ℝ)| ≤ (2 : ℝ) ^ D.c) {s x : ℕ} (hs : s ≤ D.s₀)
    (hx : x ≤ 4 * D.q₀) {w : ℂ} (hw : ‖w‖ ≤ 5) :
    ‖auxV D.q₀ D.q D.n y D.ξ s x w‖ ≤ (2 : ℝ) ^ (D.c + D.W) := by
  have hR : (1 : ℝ) ≤ (2 : ℝ) ^ D.b := one_le_pow₀ (by norm_num)
  have hxw : (x : ℝ) * ‖w‖ ≤ (2 : ℝ) ^ D.b := by
    have h1 : (x : ℝ) ≤ 4 * D.q₀ := by exact_mod_cast hx
    have h2 := D.cast_le_two_pow (a := 20 * D.q₀) (by omega)
    push_cast at h2
    nlinarith [norm_nonneg w, Nat.cast_nonneg (α := ℝ) x]
  exact (norm_auxV_le hy D.norm_ξ_le s x hR hxw).trans (D.size_le hs)

/-- The change from `π` to `ξ`: `|V(s, x, π) − V(s, x, ξ)| ≤ |ξ − π| 2^(c + W + 2b)`. -/
theorem norm_auxV_pi_sub_le (hy : ∀ j, |(y j : ℝ)| ≤ (2 : ℝ) ^ D.c) {s x : ℕ} (hs : s ≤ D.s₀)
    (hx : x ≤ 4 * D.q₀) :
    ‖auxV D.q₀ D.q D.n y D.ξ s x Real.pi - auxV D.q₀ D.q D.n y D.ξ s x D.ξ‖
      ≤ ‖D.ξ - Real.pi‖ * (2 : ℝ) ^ (D.c + D.W + 2 * D.b) := by
  have hR : (1 : ℝ) ≤ (2 : ℝ) ^ D.b := one_le_pow₀ (by norm_num)
  have h20 := D.cast_le_two_pow (a := 20 * D.q₀) (by omega)
  push_cast at h20
  have hx' : (x : ℝ) ≤ 4 * D.q₀ := by exact_mod_cast hx
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  have hxw : ∀ w : ℂ, ‖w‖ ≤ 5 → (x : ℝ) * ‖w‖ ≤ (2 : ℝ) ^ D.b := fun w hw => by
    nlinarith [norm_nonneg w]
  have hπ : ‖(Real.pi : ℂ)‖ ≤ 5 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    linarith [Real.pi_lt_four]
  refine (norm_auxV_sub_le hy D.norm_ξ_le s x hR (hxw _ hπ) (hxw _ D.norm_ξ_le)).trans ?_
  rw [norm_sub_rev]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hsize := D.size_le hs
  have hxb : (x : ℝ) ≤ (2 : ℝ) ^ D.b := by linarith
  have hq₀ := D.q₀_le
  have hnn : (0 : ℝ) ≤ ((D.q₀ : ℝ) + D.q) ^ s * (D.q₀ * (D.n * ((2 : ℝ) ^ D.c * 5 ^ D.n)))
      * ((2 : ℝ) ^ D.b) ^ D.q₀ := by positivity
  calc (x : ℝ) * (D.q * (D.q₀ * (((D.q₀ : ℝ) + D.q) ^ s
        * (D.q₀ * (D.n * ((2 : ℝ) ^ D.c * 5 ^ D.n))) * ((2 : ℝ) ^ D.b) ^ D.q₀)))
      = x * (D.q₀ * (D.q * (((D.q₀ : ℝ) + D.q) ^ s
        * (D.q₀ * (D.n * ((2 : ℝ) ^ D.c * 5 ^ D.n))) * ((2 : ℝ) ^ D.b) ^ D.q₀))) := by ring
    _ ≤ (2 : ℝ) ^ D.b * ((2 : ℝ) ^ D.b * (2 : ℝ) ^ (D.c + D.W)) := by
        gcongr
    _ = (2 : ℝ) ^ (D.c + D.W + 2 * D.b) := by
        simp only [← pow_add]
        congr 1
        ring

/-! ### Liouville's inequality for `V(s, x, ξ)` -/

theorem exponent_liouville (b cw n q₀ N : ℕ) (hn : 1 ≤ n) :
    b + cw + (n - 1) * (2 * b + 2 * cw) + N * b * (3 * (q₀ + n))
      ≤ 2 * n * cw + 2 * b * n + 3 * (q₀ + n) * (N * b) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  nlinarith [Nat.zero_le (m * b), Nat.zero_le (m * cw)]

/-- The heights of `Q₁`, `Q₂` are at most `2^(c + W)`. -/
theorem abs_coeff_auxQ_le_two_pow {part : ℕ → ℤ} (hpart : ∀ j, |part j| ≤ 1)
    (hy : ∀ j, |(y j : ℝ)| ≤ (2 : ℝ) ^ D.c) {s x : ℕ} (hs : s ≤ D.s₀) (hx : x ≤ 4 * D.q₀)
    (m : ℕ) :
    |((auxQ part D.q₀ D.q D.n y s x).coeff m : ℝ)| ≤ (2 : ℝ) ^ (D.c + D.W) := by
  refine (abs_coeff_auxQ_le hpart hy s x m).trans ?_
  have h1 := D.q₀_le
  have h2 := D.q_le
  have h3 := D.n_le
  have h4 := D.add_pow_le hs
  have hR : (1 : ℝ) ≤ (2 : ℝ) ^ D.b := one_le_pow₀ (by norm_num)
  have h5 : (max 1 (x : ℝ)) ^ D.q₀ ≤ ((2 : ℝ) ^ D.b) ^ D.q₀ := by
    refine pow_le_pow_left₀ (by positivity) (max_le hR ?_) _
    exact D.cast_le_two_pow (hx.trans (by omega))
  calc (D.q₀ : ℝ) * (D.q * D.n) * ((2 : ℝ) ^ D.c
        * (((D.q₀ : ℝ) + D.q) ^ s * (max 1 (x : ℝ)) ^ D.q₀))
      ≤ (2 : ℝ) ^ D.b * ((2 : ℝ) ^ D.b * (2 : ℝ) ^ D.b) * ((2 : ℝ) ^ D.c
        * (((2 : ℝ) ^ D.b) ^ D.s₀ * ((2 : ℝ) ^ D.b) ^ D.q₀)) := by gcongr
    _ = (2 : ℝ) ^ (3 * D.b + D.c + D.b * D.s₀ + D.b * D.q₀) := by
        rw [← pow_mul, ← pow_mul]
        simp only [← pow_add]
        congr 1
        ring
    _ ≤ (2 : ℝ) ^ (D.c + D.W) := pow_le_pow_right₀ (by norm_num) (by unfold W; omega)

/-- **Liouville's inequality for `V(s, x, ξ)`**: if `|V(s, x, ξ)| 2^Y < 1` then
`V(s, x, ξ) = 0` (`s ≤ s₀`, `x ≤ 4q₀`). -/
theorem auxV_ξ_eq_zero (hy : ∀ j, |(y j : ℝ)| ≤ (2 : ℝ) ^ D.c) {s x : ℕ} (hs : s ≤ D.s₀)
    (hx : x ≤ 4 * D.q₀) (hlt : ‖auxV D.q₀ D.q D.n y D.ξ s x D.ξ‖ * (2 : ℝ) ^ D.Y < 1) :
    auxV D.q₀ D.q D.n y D.ξ s x D.ξ = 0 := by
  by_contra hne
  rw [auxV_eq_aeval] at hne hlt
  have hA1 : (1 : ℝ) ≤ (2 : ℝ) ^ (D.c + D.W) := one_le_pow₀ (by norm_num)
  have hL := liouville_gaussian D.hp D.hn D.hξ hne (M := (D.n - 1) + (D.q₀ - 1))
    (natDegree_auxQ_le reI D.q₀ D.q D.n y s x) (natDegree_auxQ_le imI D.q₀ D.q D.n y s x)
    hA1 (D.abs_coeff_auxQ_le_two_pow abs_reI_le hy hs hx)
    (D.abs_coeff_auxQ_le_two_pow abs_imI_le hy hs hx) D.hH
  have hn1 := D.n_pos
  have hq₀1 := D.hq₀
  set Ml : ℕ := (D.n - 1) + (D.q₀ - 1) with hMl
  -- the factors
  have t1 : 2 * ((Ml : ℝ) + 1) ≤ (2 : ℝ) ^ D.b := by
    have := D.cast_le_two_pow (a := 2 * (Ml + 1)) (by omega)
    push_cast at this
    exact this
  have t2 : 2 * (Ml : ℝ) + 1 ≤ (2 : ℝ) ^ D.b := by
    have := D.cast_le_two_pow (a := 2 * Ml + 1) (by omega)
    push_cast at this
    exact this
  have hH0 : 0 ≤ D.H := (abs_nonneg _).trans (D.hH 0)
  have hbase0 : (0 : ℝ) ≤ (D.p.natDegree + 1) * D.H := by positivity
  have t3 : (((D.p.natDegree : ℝ) + 1) * D.H) ^ (3 * Ml)
      ≤ ((2 : ℝ) ^ (D.N * D.b)) ^ (3 * (D.q₀ + D.n)) := by
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (D.N * D.b) := one_le_pow₀ (by norm_num)
    exact (pow_le_pow_left₀ hbase0 D.hHN _).trans (pow_le_pow_right₀ h1 (by omega))
  have hbig : 2 * ((Ml : ℝ) + 1) * (2 : ℝ) ^ (D.c + D.W)
      * ((2 * (Ml : ℝ) + 1) * (2 * ((Ml : ℝ) + 1) * ((2 : ℝ) ^ (D.c + D.W)) ^ 2))
        ^ (D.p.natDegree - 1)
      * (((D.p.natDegree : ℝ) + 1) * D.H) ^ (3 * Ml) ≤ (2 : ℝ) ^ D.Y := by
    calc 2 * ((Ml : ℝ) + 1) * (2 : ℝ) ^ (D.c + D.W)
          * ((2 * (Ml : ℝ) + 1) * (2 * ((Ml : ℝ) + 1) * ((2 : ℝ) ^ (D.c + D.W)) ^ 2))
            ^ (D.p.natDegree - 1)
          * (((D.p.natDegree : ℝ) + 1) * D.H) ^ (3 * Ml)
        ≤ (2 : ℝ) ^ D.b * (2 : ℝ) ^ (D.c + D.W)
          * ((2 : ℝ) ^ D.b * ((2 : ℝ) ^ D.b * ((2 : ℝ) ^ (D.c + D.W)) ^ 2))
            ^ (D.p.natDegree - 1)
          * ((2 : ℝ) ^ (D.N * D.b)) ^ (3 * (D.q₀ + D.n)) := by gcongr
      _ = (2 : ℝ) ^ (D.b + (D.c + D.W) + (D.n - 1) * (2 * D.b + 2 * (D.c + D.W))
            + D.N * D.b * (3 * (D.q₀ + D.n))) := by
          simp only [← pow_mul, ← pow_add]
          congr 1
          ring
      _ ≤ (2 : ℝ) ^ D.Y := by
          refine pow_le_pow_right₀ (by norm_num) ?_
          have := exponent_liouville D.b (D.c + D.W) D.n D.q₀ D.N hn1
          unfold Y
          omega
  have hnn := norm_nonneg (aeval D.ξ (auxQ reI D.q₀ D.q D.n y s x)
    + Complex.I * aeval D.ξ (auxQ imI D.q₀ D.q D.n y s x))
  have := mul_le_mul_of_nonneg_left hbig hnn
  linarith

/-! ### The step `Z(X) ⟹ Z(2X)` -/

/-- `e^{9π k} ≤ 2^{42 k}`. -/
theorem exp_nine_pi_le (k : ℕ) : Real.exp (9 * Real.pi * k) ≤ (2 : ℝ) ^ (42 * k) := by
  have h1 : 9 * Real.pi ≤ 42 * Real.log 2 := by
    have := Real.log_two_gt_d9
    have := Real.pi_lt_d2
    linarith
  have h2 : Real.exp (9 * Real.pi * k) ≤ Real.exp (42 * Real.log 2 * k) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg k))
  refine h2.trans (le_of_eq ?_)
  rw [show 42 * Real.log 2 * (k : ℝ) = ((42 * k : ℕ) : ℝ) * Real.log 2 by push_cast; ring,
    Real.exp_nat_mul, Real.exp_log (by norm_num)]

/-- The invariant `Z(X)`: `V(s, x, ξ) = 0` for `s < s₀`, `x ≤ X`. -/
def Zero (y : ℕ × ℕ × ℕ → ℤ) (X : ℕ) : Prop :=
  ∀ s < D.s₀, ∀ x ≤ X, auxV D.q₀ D.q D.n y D.ξ s x D.ξ = 0

theorem Zero.mono {X X' : ℕ} (h : D.Zero y X) (hX : X' ≤ X) : D.Zero y X' :=
  fun s hs x hx => h s hs x (hx.trans hX)

/-- Under `Z(X)` the derivatives `f⁽ⁱ⁾(πix)`, `i < s₀`, `x ≤ X`, are at most
`|ξ − π| 2^(c + W + 2b)`. -/
theorem norm_iteratedDeriv_le_of_zero (hy : ∀ j, |(y j : ℝ)| ≤ (2 : ℝ) ^ D.c) {X : ℕ}
    (hX : X ≤ 4 * D.q₀) (hZ : D.Zero y X) {i x : ℕ} (hi : i < D.s₀) (hx : x ≤ X) :
    ‖iteratedDeriv i (auxF D.q₀ D.q D.n y D.ξ) (Complex.I * x * Real.pi)‖
      ≤ ‖D.ξ - Real.pi‖ * (2 : ℝ) ^ (D.c + D.W + 2 * D.b) := by
  rw [← auxV_pi]
  have := D.norm_auxV_pi_sub_le hy hi.le (hx.trans hX)
  rwa [hZ i hi x hx, sub_zero] at this

/-- The growth of `f` on the circle `|w| = 9πX`. -/
theorem norm_auxF_circle_le (hy : ∀ j, |(y j : ℝ)| ≤ (2 : ℝ) ^ D.c) {X : ℕ} (hX1 : 1 ≤ X)
    (hX : X ≤ 2 * D.q₀) {w : ℂ} (hw : ‖w‖ = 9 * Real.pi * X) :
    ‖auxF D.q₀ D.q D.n y D.ξ w‖ ≤ (2 : ℝ) ^ (42 * D.q * X + D.c + D.W) := by
  have hπ3 := Real.pi_gt_three
  have hπ4 := Real.pi_lt_d2
  have hXr : (1 : ℝ) ≤ X := by exact_mod_cast hX1
  have hR1 : (1 : ℝ) ≤ 9 * Real.pi * X := by nlinarith
  have hRb : 9 * Real.pi * X ≤ (2 : ℝ) ^ D.b := by
    have h1 : (X : ℝ) ≤ 2 * D.q₀ := by exact_mod_cast hX
    have h2 := D.cast_le_two_pow (a := 64 * D.q₀) (by omega)
    push_cast at h2
    nlinarith
  refine (norm_auxF_le hy D.norm_ξ_le hR1 hw.le).trans ?_
  have h1 := D.q_le
  have h3 := D.q₀_le
  have h4 := D.n_le
  have h5 := five_pow_le D.n
  have hexp : Real.exp (D.q * (9 * Real.pi * X)) ≤ (2 : ℝ) ^ (42 * (D.q * X)) := by
    have := exp_nine_pi_le (D.q * X)
    rw [show 9 * Real.pi * ((D.q * X : ℕ) : ℝ) = D.q * (9 * Real.pi * X) by push_cast; ring]
      at this
    exact this
  have hpow : (9 * Real.pi * X) ^ D.q₀ ≤ ((2 : ℝ) ^ D.b) ^ D.q₀ :=
    pow_le_pow_left₀ (by positivity) hRb _
  calc (D.q : ℝ) * (Real.exp (D.q * (9 * Real.pi * X))
        * (D.q₀ * (D.n * ((2 : ℝ) ^ D.c * 5 ^ D.n)) * (9 * Real.pi * X) ^ D.q₀))
      ≤ (2 : ℝ) ^ D.b * ((2 : ℝ) ^ (42 * (D.q * X))
        * ((2 : ℝ) ^ D.b * ((2 : ℝ) ^ D.b * ((2 : ℝ) ^ D.c * (2 : ℝ) ^ (3 * D.n)))
          * ((2 : ℝ) ^ D.b) ^ D.q₀)) := by gcongr
    _ = (2 : ℝ) ^ (D.b + 42 * (D.q * X) + 2 * D.b + D.c + 3 * D.n + D.b * D.q₀) := by
        simp only [← pow_mul, ← pow_add]
        congr 1
        ring
    _ ≤ (2 : ℝ) ^ (42 * D.q * X + D.c + D.W) := by
        refine pow_le_pow_right₀ (by norm_num) ?_
        have : 42 * (D.q * X) = 42 * D.q * X := by ring
        unfold W
        omega

/-- The bound for `extE X s₀ δ`. -/
theorem extE_le {X : ℕ} (hX1 : 1 ≤ X) (hX : X ≤ 2 * D.q₀) {δ : ℝ} (hδ : 0 ≤ δ) :
    extE X D.s₀ δ ≤ δ * (2 : ℝ) ^ (2 * D.b + 3 + D.b * D.s₀ * X + D.b * D.s₀) := by
  have hπ3 := Real.pi_gt_three
  have hπ4 := Real.pi_lt_d2
  have hXr : (1 : ℝ) ≤ X := by exact_mod_cast hX1
  have hX2 : (X : ℝ) ≤ 2 * D.q₀ := by exact_mod_cast hX
  have h64 := D.cast_le_two_pow (a := 64 * D.q₀) (by omega)
  push_cast at h64
  have h10 : 10 * Real.pi * X ≤ (2 : ℝ) ^ D.b := by nlinarith
  have h20 : 10 * Real.pi * X / (Real.pi / 2) ≤ (2 : ℝ) ^ D.b := by
    have : 10 * Real.pi * X / (Real.pi / 2) = 20 * X := by
      field_simp
      ring
    rw [this]
    nlinarith
  have hX1' : ((X + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ D.b := D.cast_le_two_pow (by omega)
  have hs := D.s₀_le
  have hexp : Real.exp (Real.pi / 2) ≤ 8 := by
    have h1 : Real.exp (Real.pi / 2) ≤ Real.exp 2 := Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    have h3 := Real.exp_one_lt_d9
    have h4 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    nlinarith
  have hp1 : (10 * Real.pi * X) ^ (D.s₀ * (X + 1 - 1)) ≤ ((2 : ℝ) ^ D.b) ^ (D.s₀ * X) := by
    rw [Nat.add_sub_cancel]
    exact pow_le_pow_left₀ (by positivity) h10 _
  have hp2 : (10 * Real.pi * X / (Real.pi / 2)) ^ D.s₀ ≤ ((2 : ℝ) ^ D.b) ^ D.s₀ :=
    pow_le_pow_left₀ (by positivity) h20 _
  unfold extE
  calc ((X + 1 : ℕ) : ℝ) * ((10 * Real.pi * X) ^ (D.s₀ * (X + 1 - 1))
        * (D.s₀ * (δ * Real.exp (Real.pi / 2) / 1) * (10 * Real.pi * X / (Real.pi / 2)) ^ D.s₀))
      ≤ (2 : ℝ) ^ D.b * (((2 : ℝ) ^ D.b) ^ (D.s₀ * X)
        * ((2 : ℝ) ^ D.b * (δ * 8 / 1) * ((2 : ℝ) ^ D.b) ^ D.s₀)) := by gcongr
    _ = δ * (2 : ℝ) ^ (2 * D.b + 3 + D.b * D.s₀ * X + D.b * D.s₀) := by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, div_one, ← pow_mul, ← pow_mul]
        simp only [pow_add]
        ring

theorem extE_nonneg (X T : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) : 0 ≤ extE X T δ := by
  unfold extE
  have := Real.pi_pos
  positivity

/-- **The step `Z(X) ⟹ Z(2X)`** for `x₀ ≤ X ≤ 2q₀` (Fel'dman's Lemma B). -/
theorem zero_step (hy : ∀ j, |(y j : ℝ)| ≤ (2 : ℝ) ^ D.c) {X : ℕ} (hX₀ : D.x₀ ≤ X)
    (hX : X ≤ 2 * D.q₀) (hZ : D.Zero y X) : D.Zero y (2 * X) := by
  intro σ hσ x' hx'
  have hX1 : 1 ≤ X := D.hx₀.trans hX₀
  refine D.auxV_ξ_eq_zero hy hσ.le (hx'.trans (by omega)) ?_
  set ε : ℝ := ‖D.ξ - Real.pi‖ with hε
  have hε0 : 0 ≤ ε := norm_nonneg _
  set δ : ℝ := ε * (2 : ℝ) ^ (D.c + D.W + 2 * D.b) with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have hderiv := extrapolate_deriv (differentiable_auxF D.q₀ D.q D.n y D.ξ) hX1 hδ0
    (fun x hx i hi => D.norm_iteratedDeriv_le_of_zero hy (hX.trans (by omega)) hZ hi hx)
    (fun w hw => D.norm_auxF_circle_le hy hX1 hX hw) hx' σ
  rw [← auxV_pi] at hderiv
  have hE := D.extE_le hX1 hX hδ0
  have hE0 := extE_nonneg X D.s₀ hδ0
  -- `σ! ≤ 2^(b s₀)`
  have hfac : (σ.factorial : ℝ) ≤ (2 : ℝ) ^ (D.b * D.s₀) := by
    have h1 : σ.factorial ≤ D.s₀ ^ D.s₀ :=
      (Nat.factorial_le hσ.le).trans (Nat.factorial_le_pow D.s₀)
    have h2 : ((D.s₀ ^ D.s₀ : ℕ) : ℝ) ≤ ((2 : ℝ) ^ D.b) ^ D.s₀ := by
      push_cast
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) D.s₀_le _
    rw [pow_mul]
    exact (by exact_mod_cast h1 : (σ.factorial : ℝ) ≤ ((D.s₀ ^ D.s₀ : ℕ) : ℝ)).trans h2
  have hsub := D.norm_auxV_pi_sub_le hy hσ.le (x := x') (hx'.trans (by omega))
  rw [← hε, ← hδ] at hsub
  set Vπ := auxV D.q₀ D.q D.n y D.ξ σ x' Real.pi with hVπ
  set Vξ := auxV D.q₀ D.q D.n y D.ξ σ x' D.ξ with hVξ
  have hVle : ‖Vξ‖ ≤ ‖Vπ‖ + δ := by
    have h1 : ‖Vξ‖ ≤ ‖Vπ‖ + ‖Vπ - Vξ‖ := by
      have := norm_sub_le Vπ (Vπ - Vξ)
      rwa [sub_sub_cancel] at this
    linarith
  -- abbreviations
  set P : ℝ := (2 : ℝ) ^ (D.b * D.s₀) with hP
  set Mb : ℝ := (2 : ℝ) ^ (42 * D.q * X + D.c + D.W) with hMb
  set EB : ℝ := δ * (2 : ℝ) ^ (2 * D.b + 3 + D.b * D.s₀ * X + D.b * D.s₀) with hEB
  set hh : ℝ := (1 / 2 : ℝ) ^ (D.s₀ * X) with hhh
  have hP0 : 0 < P := by positivity
  have hMb0 : 0 < Mb := by positivity
  have hEB0 : 0 ≤ EB := by positivity
  have hhh0 : 0 ≤ hh := by positivity
  have hhh1 : hh ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hhle : (1 / 2 : ℝ) ^ (D.s₀ * (X + 1)) ≤ hh :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.mul_le_mul_left _ (by omega))
  have hVπ' : ‖Vπ‖ ≤ P * (2 * EB + hh * Mb) := by
    have h1 : extE X D.s₀ δ + (1 / 2 : ℝ) ^ (D.s₀ * (X + 1)) * (Mb + extE X D.s₀ δ)
        ≤ 2 * EB + hh * Mb := by
      have h2 : (1 / 2 : ℝ) ^ (D.s₀ * (X + 1)) * (Mb + extE X D.s₀ δ)
          ≤ hh * (Mb + EB) := mul_le_mul hhle (by linarith) (by positivity) hhh0
      nlinarith
    have h3 : 0 ≤ extE X D.s₀ δ + (1 / 2 : ℝ) ^ (D.s₀ * (X + 1)) * (Mb + extE X D.s₀ δ) := by
      positivity
    exact hderiv.trans (mul_le_mul hfac h1 h3 hP0.le)
  -- the exponents
  have hbx : D.b * D.s₀ * X ≤ 2 * D.b * D.s₀ * D.q₀ := by
    calc D.b * D.s₀ * X ≤ D.b * D.s₀ * (2 * D.q₀) := Nat.mul_le_mul_left _ hX
      _ = 2 * D.b * D.s₀ * D.q₀ := by ring
  have hE1 : D.b * D.s₀ + (D.c + D.W + 2 * D.b)
      + (2 * D.b + 3 + D.b * D.s₀ * X + D.b * D.s₀) + D.Y + 3 ≤ D.Φ := by
    have := D.h5
    change _ + D.c + D.W + D.Y + _ + _ ≤ _ at this
    linarith
  have hE3 : D.c + D.W + 2 * D.b + D.Y + 2 ≤ D.Φ := by
    have := D.h5
    change _ + D.c + D.W + D.Y + _ + _ ≤ _ at this
    omega
  have hE2 : D.b * D.s₀ + (42 * D.q * X + D.c + D.W) + D.Y + 2 ≤ D.s₀ * X := by
    have h4 := D.h4
    change D.b * D.s₀ + D.c + D.W + D.Y + 2 ≤ _ at h4
    have h1 : (D.s₀ - 42 * D.q) * D.x₀ ≤ (D.s₀ - 42 * D.q) * X := Nat.mul_le_mul_left _ hX₀
    have h2 : D.s₀ * X = (D.s₀ - 42 * D.q) * X + 42 * D.q * X := by
      rw [← Nat.add_mul, Nat.sub_add_cancel D.h4a]
    linarith
  -- the three terms
  have f1 : P * EB * (2 : ℝ) ^ D.Y < 1 / 8 := by
    have h1 := D.eps_mul_lt hE1
    rw [← hε] at h1
    have h2 : P * EB * (2 : ℝ) ^ D.Y * 8 = ε * (2 : ℝ) ^ (D.b * D.s₀ + (D.c + D.W + 2 * D.b)
        + (2 * D.b + 3 + D.b * D.s₀ * X + D.b * D.s₀) + D.Y + 3) := by
      rw [hP, hEB, hδ]
      simp only [pow_add]
      ring
    linarith
  have f3 : δ * (2 : ℝ) ^ D.Y < 1 / 4 := by
    have h1 := D.eps_mul_lt hE3
    rw [← hε] at h1
    have h2 : δ * (2 : ℝ) ^ D.Y * 4 = ε * (2 : ℝ) ^ (D.c + D.W + 2 * D.b + D.Y + 2) := by
      rw [hδ]
      simp only [pow_add]
      ring
    linarith
  have f2 : P * Mb * (2 : ℝ) ^ D.Y * hh ≤ 1 / 4 := by
    have h1 : hh ≤ (1 / 2 : ℝ) ^ (D.b * D.s₀ + (42 * D.q * X + D.c + D.W) + D.Y + 2) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hE2
    have h2 : P * Mb * (2 : ℝ) ^ D.Y
        * (1 / 2 : ℝ) ^ (D.b * D.s₀ + (42 * D.q * X + D.c + D.W) + D.Y + 2) = 1 / 4 := by
      rw [hP, hMb, one_div, inv_pow]
      simp only [pow_add]
      field_simp
      ring
    calc P * Mb * (2 : ℝ) ^ D.Y * hh
        ≤ P * Mb * (2 : ℝ) ^ D.Y
          * (1 / 2 : ℝ) ^ (D.b * D.s₀ + (42 * D.q * X + D.c + D.W) + D.Y + 2) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 1 / 4 := h2
  have hY0 : (0 : ℝ) < (2 : ℝ) ^ D.Y := by positivity
  calc ‖Vξ‖ * (2 : ℝ) ^ D.Y ≤ (P * (2 * EB + hh * Mb) + δ) * (2 : ℝ) ^ D.Y :=
        mul_le_mul_of_nonneg_right (by linarith) hY0.le
    _ = 2 * (P * EB * (2 : ℝ) ^ D.Y) + P * Mb * (2 : ℝ) ^ D.Y * hh + δ * (2 : ℝ) ^ D.Y := by
        ring
    _ < 1 := by linarith

/-! ### The start: Dirichlet's principle -/

/-- The real forms `Re V(s, x, π)`, `Im V(s, x, π)` in the unknowns `y`. -/
theorem sum_part_auxBeta (y : ℕ × ℕ × ℕ → ℤ) (s x : ℕ) (part : Bool) :
    ∑ j ∈ idxJ D.q₀ D.q D.n,
        (if part then (auxBeta D.ξ s x Real.pi j).re else (auxBeta D.ξ s x Real.pi j).im)
          * (y j : ℝ)
      = if part then (auxV D.q₀ D.q D.n y D.ξ s x Real.pi).re
        else (auxV D.q₀ D.q D.n y D.ξ s x Real.pi).im := by
  rw [auxV_eq_sum]
  cases part
  · simp only [Bool.false_eq_true, ↓reduceIte, Complex.im_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Complex.mul_im, mul_comm]
  · simp only [↓reduceIte, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Complex.mul_re, mul_comm]

/-- **The auxiliary function**: integers `y`, not all zero, `|y| ≤ 2^c`, with `Z(x₀)`. -/
theorem exists_y : ∃ y : ℕ × ℕ × ℕ → ℤ, (∃ j ∈ idxJ D.q₀ D.q D.n, y j ≠ 0) ∧
    (∀ j, |(y j : ℝ)| ≤ (2 : ℝ) ^ D.c) ∧ D.Zero y D.x₀ := by
  have hn1 := D.n_pos
  set F : Finset ((ℕ × ℕ) × Bool) :=
    (range D.s₀ ×ˢ range (D.x₀ + 1)) ×ˢ (Finset.univ : Finset Bool) with hF
  have hFcard : F.card = D.s₀ * (D.x₀ + 1) * 2 := by simp [hF]
  have hJpos : 0 < (idxJ D.q₀ D.q D.n).card := by
    rw [card_idxJ]
    exact Nat.mul_pos D.hq₀ (Nat.mul_pos D.hq hn1)
  have hcard : (2 ^ D.g) ^ F.card < (2 ^ D.c + 1) ^ (idxJ D.q₀ D.q D.n).card := by
    have h1 : (2 ^ D.g) ^ F.card ≤ (2 ^ D.c) ^ (idxJ D.q₀ D.q D.n).card := by
      rw [← pow_mul, ← pow_mul, hFcard, card_idxJ]
      refine Nat.pow_le_pow_right (by norm_num) ?_
      have := D.h2
      calc D.g * (D.s₀ * (D.x₀ + 1) * 2) = D.g * (2 * D.s₀ * (D.x₀ + 1)) := by ring
        _ ≤ D.c * (D.q₀ * (D.q * D.n)) := this
    exact h1.trans_lt (Nat.pow_lt_pow_left (by omega) hJpos.ne')
  have hπ5 : ‖(Real.pi : ℂ)‖ ≤ 5 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    linarith [Real.pi_lt_four]
  have hpartle : ∀ (z : ℂ) (part : Bool), |if part then z.re else z.im| ≤ ‖z‖ := fun z part => by
    cases part
    · simpa using Complex.abs_im_le_norm z
    · simpa using Complex.abs_re_le_norm z
  obtain ⟨y, hy0, hyz, hy⟩ := dirichlet_box_finset F (idxJ D.q₀ D.q D.n)
    (fun i j => if i.2 then (auxBeta D.ξ i.1.1 i.1.2 Real.pi j).re
      else (auxBeta D.ξ i.1.1 i.1.2 Real.pi j).im)
    (2 ^ D.c) (2 ^ D.g) ((2 : ℝ) ^ (D.c + D.W)) (by positivity) hcard
    (fun x hx i hi => by
      have hi' := hi
      simp only [hF, mem_product, mem_range, mem_univ, and_true] at hi'
      have h1 := D.sum_part_auxBeta (fun j => (x j : ℤ)) i.1.1 i.1.2 i.2
      simp only [Int.cast_natCast] at h1
      rw [h1]
      refine (hpartle _ _).trans (D.norm_auxV_le_two_pow (fun j => ?_) hi'.1.le
        (by have := D.hx₀q; omega) hπ5)
      rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast hx j)
  have hyb : ∀ j, |(y j : ℝ)| ≤ (2 : ℝ) ^ D.c := fun j => by
    have := hyz j
    exact_mod_cast this
  refine ⟨y, hy0, hyb, fun s hs x hx => ?_⟩
  refine D.auxV_ξ_eq_zero hyb hs.le (by have := D.hx₀q; omega) ?_
  -- `|V(s, x, π)| ≤ 4 · 2^(c+W) / 2^g`
  have hre := hy ((s, x), true) (by simp [hF, hs]; omega)
  have him := hy ((s, x), false) (by simp [hF, hs]; omega)
  rw [D.sum_part_auxBeta y s x true] at hre
  rw [D.sum_part_auxBeta y s x false] at him
  simp only [↓reduceIte, Bool.false_eq_true, Nat.cast_pow, Nat.cast_ofNat] at hre him
  set Vπ := auxV D.q₀ D.q D.n y D.ξ s x Real.pi with hVπ
  set Vξ := auxV D.q₀ D.q D.n y D.ξ s x D.ξ with hVξ
  have hVπn : ‖Vπ‖ ≤ 4 * (2 : ℝ) ^ (D.c + D.W) / (2 : ℝ) ^ D.g := by
    have := Complex.norm_le_abs_re_add_abs_im Vπ
    have e : 4 * (2 : ℝ) ^ (D.c + D.W) / (2 : ℝ) ^ D.g
        = 2 * (2 : ℝ) ^ (D.c + D.W) / (2 : ℝ) ^ D.g
          + 2 * (2 : ℝ) ^ (D.c + D.W) / (2 : ℝ) ^ D.g := by ring
    linarith
  have hsub := D.norm_auxV_pi_sub_le hyb hs.le (x := x) (by have := D.hx₀q; omega)
  rw [← hVπ, ← hVξ] at hsub
  have hVle : ‖Vξ‖ ≤ ‖Vπ‖ + ‖Vπ - Vξ‖ := by
    have := norm_sub_le Vπ (Vπ - Vξ)
    rwa [sub_sub_cancel] at this
  have hE3 : D.c + D.W + 2 * D.b + D.Y + 2 ≤ D.Φ := by
    have := D.h5
    change _ + D.c + D.W + D.Y + _ + _ ≤ _ at this
    omega
  have f3 : ‖D.ξ - Real.pi‖ * (2 : ℝ) ^ (D.c + D.W + 2 * D.b) * (2 : ℝ) ^ D.Y < 1 / 4 := by
    have h1 := D.eps_mul_lt hE3
    have h2 : ‖D.ξ - Real.pi‖ * (2 : ℝ) ^ (D.c + D.W + 2 * D.b) * (2 : ℝ) ^ D.Y * 4
        = ‖D.ξ - Real.pi‖ * (2 : ℝ) ^ (D.c + D.W + 2 * D.b + D.Y + 2) := by
      simp only [pow_add]
      ring
    linarith
  have f1 : 4 * (2 : ℝ) ^ (D.c + D.W) / (2 : ℝ) ^ D.g * (2 : ℝ) ^ D.Y ≤ 1 / 4 := by
    have h3 := D.h3
    change D.c + D.W + D.Y + 4 ≤ D.g at h3
    have h1 : (2 : ℝ) ^ (D.c + D.W + D.Y + 4) ≤ (2 : ℝ) ^ D.g :=
      pow_le_pow_right₀ (by norm_num) h3
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have h2 : (2 : ℝ) ^ (D.c + D.W + D.Y + 4) = 16 * ((2 : ℝ) ^ (D.c + D.W) * (2 : ℝ) ^ D.Y) := by
      simp only [pow_add]
      ring
    nlinarith
  have hY0 : (0 : ℝ) < (2 : ℝ) ^ D.Y := by positivity
  calc ‖Vξ‖ * (2 : ℝ) ^ D.Y
      ≤ (4 * (2 : ℝ) ^ (D.c + D.W) / (2 : ℝ) ^ D.g
          + ‖D.ξ - Real.pi‖ * (2 : ℝ) ^ (D.c + D.W + 2 * D.b)) * (2 : ℝ) ^ D.Y :=
        mul_le_mul_of_nonneg_right (by linarith) hY0.le
    _ = 4 * (2 : ℝ) ^ (D.c + D.W) / (2 : ℝ) ^ D.g * (2 : ℝ) ^ D.Y
          + ‖D.ξ - Real.pi‖ * (2 : ℝ) ^ (D.c + D.W + 2 * D.b) * (2 : ℝ) ^ D.Y := by ring
    _ < 1 := by linarith

/-! ### The end: all the coefficients vanish -/

/-- `Z(2q₀)` is impossible for integers `y`, not all zero, with `|y| ≤ 2^c`. -/
theorem false_of_zero (hy : ∀ j, |(y j : ℝ)| ≤ (2 : ℝ) ^ D.c)
    (hne : ∃ j ∈ idxJ D.q₀ D.q D.n, y j ≠ 0) (hZ : D.Zero y (2 * D.q₀)) : False := by
  obtain ⟨⟨k, l, τ⟩, hj, hyj⟩ := hne
  simp only [idxJ, mem_product, mem_range] at hj
  obtain ⟨hk, hl, hτ⟩ := hj
  have hn1 := D.n_pos
  set ε : ℝ := ‖D.ξ - Real.pi‖ with hε
  set δ : ℝ := ε * (2 : ℝ) ^ (D.c + D.W + 2 * D.b) with hδ
  -- Lemma 6
  have hL6 := l1_le_of_iteratedDeriv_le (q₀ := D.q₀) (q := D.q) (auxP D.q₀ D.n y D.ξ)
    (fun l => lt_of_le_of_lt (natDegree_auxP_le D.q₀ D.n y D.ξ l) (by have := D.hq₀; omega))
    (ε := δ) (fun s hs x hx => by
      have h1 := D.norm_iteratedDeriv_le_of_zero hy (X := 2 * D.q₀) (by omega) hZ
        (i := s) (x := 2 * x) (lt_of_lt_of_le hs D.hqs) (by omega)
      have e : (2 * Real.pi * Complex.I * x : ℂ) = Complex.I * ((2 * x : ℕ) : ℂ) * Real.pi := by
        push_cast
        ring
      rw [e]
      exact h1) l hl
  -- the coefficient `C_{k,l}`
  have hcoeff : (auxP D.q₀ D.n y D.ξ l).coeff k = coefC D.n y D.ξ k l := by
    unfold auxP
    rw [finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq (range D.q₀) k, ite_eq_left (mem_range.mpr hk)]
  have hCn : ‖coefC D.n y D.ξ k l‖
      ≤ 2 ^ D.q * (1 + (D.q₀ : ℝ)) ^ D.q * (D.q₀ * 2 ^ D.q₀) * δ := by
    rw [← hcoeff]
    exact (norm_coeff_le_l1 _ k).trans hL6
  -- as the value at `ξ` of an integer polynomial of degree `< n`
  set Rp : ℤ[X] := ∑ τ ∈ range D.n, C (y (k, l, τ)) * X ^ τ with hRp
  have hRval : aeval D.ξ Rp = coefC D.n y D.ξ k l := by
    rw [hRp]
    unfold coefC
    simp only [map_sum, map_mul, map_pow, aeval_X, eq_intCast, map_intCast]
  have hRdeg : Rp.natDegree ≤ D.n - 1 := by
    refine natDegree_sum_le_of_forall_le _ _ fun τ hτ' => ?_
    have := mem_range.mp hτ'
    exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
  have hRcoeff : ∀ m, Rp.coeff m = if m < D.n then y (k, l, m) else 0 := by
    intro m
    rw [hRp, finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq (range D.n) m]
    simp only [mem_range]
  have hRh : ∀ m, |(Rp.coeff m : ℝ)| ≤ (2 : ℝ) ^ D.c := by
    intro m
    rw [hRcoeff]
    split_ifs
    · exact hy _
    · simp
  -- Liouville
  have hzero : aeval D.ξ Rp = 0 := by
    by_contra hR0
    have hL := liouville_int D.hp D.hn D.hξ hR0 hRdeg hRh D.hH
    rw [hRval] at hL
    have hcast : (((D.n - 1 : ℕ) : ℝ) + 1) = D.n := by
      rw [Nat.cast_sub hn1]
      simp
    rw [hcast] at hL
    have hH0 : 0 ≤ D.H := (abs_nonneg _).trans (D.hH 0)
    have hb1 : (1 : ℝ) ≤ (2 : ℝ) ^ D.b * (2 : ℝ) ^ D.c := by
      have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ D.b := one_le_pow₀ (by norm_num)
      have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ D.c := one_le_pow₀ (by norm_num)
      nlinarith
    have hNb1 : (1 : ℝ) ≤ (2 : ℝ) ^ (D.N * D.b) := one_le_pow₀ (by norm_num)
    have t1 : ((D.n : ℝ) * (2 : ℝ) ^ D.c) ^ (D.p.natDegree - 1)
        ≤ ((2 : ℝ) ^ D.b * (2 : ℝ) ^ D.c) ^ D.n :=
      (pow_le_pow_left₀ (by positivity)
        (mul_le_mul_of_nonneg_right D.n_le (by positivity)) _).trans
        (pow_le_pow_right₀ hb1 (Nat.sub_le _ _))
    have t2 : (((D.p.natDegree : ℝ) + 1) * D.H) ^ (D.p.natDegree - 1)
        ≤ ((2 : ℝ) ^ (D.N * D.b)) ^ D.n :=
      (pow_le_pow_left₀ (by positivity) D.hHN _).trans
        (pow_le_pow_right₀ hNb1 (Nat.sub_le _ _))
    have t3 : (2 : ℝ) ^ D.q * (1 + (D.q₀ : ℝ)) ^ D.q * (D.q₀ * 2 ^ D.q₀)
        ≤ (2 : ℝ) ^ D.q * ((2 : ℝ) ^ D.b) ^ D.q * ((2 : ℝ) ^ D.b * 2 ^ D.q₀) := by
      have h1 : 1 + (D.q₀ : ℝ) ≤ (2 : ℝ) ^ D.b := by
        have := D.cast_le_two_pow (a := 1 + D.q₀) (by have := D.hq₀; omega)
        push_cast at this
        exact this
      have h2 := D.q₀_le
      gcongr
    have hε0 : 0 ≤ ε := norm_nonneg _
    have hδ0 : 0 ≤ δ := by positivity
    have hexp : (D.c + D.W + 2 * D.b) + (D.q + D.b * D.q + D.b + D.q₀)
        + D.n * (D.b + D.c + D.N * D.b) ≤ D.Φ := by
      have := D.h6
      change D.q + D.b * D.q + D.q₀ + D.c + D.W + 3 * D.b + D.n * (D.b + D.c + D.N * D.b) + 1
        ≤ D.Φ at this
      omega
    have hlt := D.eps_mul_lt hexp
    rw [← hε] at hlt
    have hbound : ‖coefC D.n y D.ξ k l‖ * (((D.n : ℝ) * (2 : ℝ) ^ D.c) ^ (D.p.natDegree - 1)
        * (((D.p.natDegree : ℝ) + 1) * D.H) ^ (D.p.natDegree - 1))
        ≤ ε * (2 : ℝ) ^ ((D.c + D.W + 2 * D.b) + (D.q + D.b * D.q + D.b + D.q₀)
          + D.n * (D.b + D.c + D.N * D.b)) := by
      calc ‖coefC D.n y D.ξ k l‖ * (((D.n : ℝ) * (2 : ℝ) ^ D.c) ^ (D.p.natDegree - 1)
            * (((D.p.natDegree : ℝ) + 1) * D.H) ^ (D.p.natDegree - 1))
          ≤ ((2 : ℝ) ^ D.q * ((2 : ℝ) ^ D.b) ^ D.q * ((2 : ℝ) ^ D.b * 2 ^ D.q₀) * δ)
            * (((2 : ℝ) ^ D.b * (2 : ℝ) ^ D.c) ^ D.n * ((2 : ℝ) ^ (D.N * D.b)) ^ D.n) := by
            refine mul_le_mul (hCn.trans (mul_le_mul_of_nonneg_right t3 hδ0))
              (mul_le_mul t1 t2 (by positivity) (by positivity)) (by positivity) (by positivity)
        _ = ε * (2 : ℝ) ^ ((D.c + D.W + 2 * D.b) + (D.q + D.b * D.q + D.b + D.q₀)
              + D.n * (D.b + D.c + D.N * D.b)) := by
            rw [hδ]
            simp only [← pow_mul, ← pow_add]
            rw [show ε * (2 : ℝ) ^ (D.c + D.W + 2 * D.b + (D.q + D.b * D.q + D.b + D.q₀)
                + D.n * (D.b + D.c + D.N * D.b))
              = ε * ((2 : ℝ) ^ (D.c + D.W + 2 * D.b) * ((2 : ℝ) ^ (D.q + D.b * D.q + D.b + D.q₀)
                * (2 : ℝ) ^ (D.n * (D.b + D.c + D.N * D.b)))) by
                rw [← pow_add, ← pow_add]; ring_nf]
            have e1 : (2 : ℝ) ^ (D.q + D.b * D.q + D.b + D.q₀)
                = (2 : ℝ) ^ D.q * (2 : ℝ) ^ (D.b * D.q) * ((2 : ℝ) ^ D.b * (2 : ℝ) ^ D.q₀) := by
              simp only [pow_add]
              ring
            have e2 : (2 : ℝ) ^ (D.n * (D.b + D.c + D.N * D.b))
                = (2 : ℝ) ^ (D.b * D.n) * (2 : ℝ) ^ (D.c * D.n) * (2 : ℝ) ^ (D.N * D.b * D.n) := by
              rw [← pow_add, ← pow_add]
              congr 1
              ring
            rw [e1, e2]
            ring
    linarith
  -- so the polynomial is zero, and `y(k, l, τ) = 0`
  have hR0 := eq_zero_of_aeval_eq_zero D.hp D.hn D.hξ hzero
    (lt_of_le_of_lt hRdeg (Nat.sub_lt hn1 one_pos))
  have := hRcoeff τ
  rw [hR0, coeff_zero, ite_eq_left hτ] at this
  exact hyj this.symm

/-- **Fel'dman's Theorem 3**, in the form: there is no data `Thm3Data`. -/
theorem false (D : Thm3Data) : False := by
  obtain ⟨y, hne, hy, hZ₀⟩ := D.exists_y
  have key : ∀ X, X ≤ 4 * D.q₀ → D.Zero y X := by
    intro X
    induction X using Nat.strong_induction_on with
    | _ X ih =>
      intro hX
      by_cases hXx : X ≤ D.x₀
      · exact Thm3Data.Zero.mono D hZ₀ hXx
      · have hx₀q := D.hx₀q
        have hx₀1 := D.hx₀
        set X' := max D.x₀ ((X + 1) / 2) with hX'
        have h1 : D.x₀ ≤ X' := le_max_left _ _
        have h2 : X' < X := max_lt (by omega) (by omega)
        have h3 : X' ≤ 2 * D.q₀ := max_le hx₀q (by omega)
        have h4 : X ≤ 2 * X' := by
          have : (X + 1) / 2 ≤ X' := le_max_right _ _
          omega
        exact Thm3Data.Zero.mono D (D.zero_step hy h1 h3 (ih X' h2 (by omega))) h4
  exact D.false_of_zero hy hne (key (2 * D.q₀) (by omega))

end Thm3Data

/-- **Fel'dman's Theorem 3** (with explicit, non-optimized constants): let `ξ` be a root of an
irreducible `p ∈ ℤ[X]` of degree `n ≥ 1` and height `≤ H`.  For naturals `N ≥ n` and `b ≥ 1`
with `(n + 1) H ≤ 2^(N b)` and `2^23 N b ≤ 2^b`,

  `|ξ − π| ≥ 2^(−Φ)`,   `Φ = 4 b (84000 N b) (29568 n b)`.

With `b` of the order of `log N` this is `exp(−O(n N log³ N))`; Fel'dman has
`exp(−γ n N ln² N)`. -/
theorem feldman_theorem3 {p : ℤ[X]} (hp : Irreducible p) (hn : p.natDegree ≠ 0) {ξ : ℂ}
    (hξ : aeval ξ p = 0) {H : ℝ} (hH : ∀ i, |(p.coeff i : ℝ)| ≤ H) {N b : ℕ}
    (hnN : p.natDegree ≤ N) (hb1 : 1 ≤ b)
    (hHN : (p.natDegree + 1) * H ≤ (2 : ℝ) ^ (N * b)) (hb : 2 ^ 23 * (N * b) ≤ 2 ^ b) :
    1 ≤ ‖ξ - Real.pi‖
      * (2 : ℝ) ^ (4 * b * (84000 * N * b) * (29568 * p.natDegree * b)) := by
  by_contra hlt
  rw [not_le] at hlt
  set n := p.natDegree with hn_def
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  have hN1 : 1 ≤ N := hn1.trans hnN
  -- monomial facts, all in terms of `t = n N b²`
  have pNbb : 1 ≤ N * b * b := Nat.mul_pos (Nat.mul_pos hN1 hb1) hb1
  have pnNb : 1 ≤ n * N * b := Nat.mul_pos (Nat.mul_pos hn1 hN1) hb1
  have e1 := Nat.mul_le_mul_right (N * b * b) hn1
  have e2 := Nat.mul_le_mul_left n pNbb
  have e3 := Nat.mul_le_mul_right b pnNb
  have e4 := Nat.mul_le_mul_left (n * b * b) hN1
  have e5a := Nat.mul_le_mul_left n hnN
  have e5 := Nat.mul_le_mul_left (n * N) (Nat.mul_pos hb1 hb1 : 1 ≤ b * b)
  have e6 := Nat.mul_le_mul_left (n * b) (Nat.mul_pos hN1 hb1 : 1 ≤ N * b)
  have e7 := Nat.mul_le_mul_right (b * b) (Nat.mul_le_mul_left n hnN)
  have e8 := Nat.mul_le_mul_left (n * N * b) hb1
  have e9 : 1 ≤ n * N * b * b := Nat.mul_pos pnNb hb1
  have e10 := Nat.mul_le_mul_left (N * b) (Nat.mul_pos hn1 hb1 : 1 ≤ n * b)
  have e11 := Nat.mul_le_mul_left (n * N * b * b) hb1
  have e12 := Nat.mul_le_mul_right b hnN
  have e13 : n ≤ N * b := hnN.trans (Nat.le_mul_of_pos_right N hb1)
  have hsub : 84000 * N * b - 42 * (1000 * N * b) = 42000 * N * b :=
    Nat.sub_eq_of_eq_add (by ring)
  refine Thm3Data.false
    { p := p, ξ := ξ, H := H, N := N
      q₀ := 29568 * n * b, q := 1000 * N * b, s₀ := 84000 * N * b, x₀ := 43 * n * b
      c := 429435 * N * b * b, g := 4 * n * (429435 * N * b * b), b := b
      Φ := 4 * b * (84000 * N * b) * (29568 * n * b)
      hp := hp, hn := hn, hξ := hξ, hH := hH, hHN := hHN, hsmall := hlt
      hsize := ?_, hq₀ := ?_, hq := ?_, hx₀ := ?_, hqs := ?_, hx₀q := ?_, h2 := ?_, h3 := ?_
      h4a := ?_, h4 := ?_, h5 := ?_, h6 := ?_ }
  · -- sizes
    refine le_trans ?_ hb
    linarith
  · nlinarith [Nat.mul_pos hn1 hb1]
  · nlinarith [Nat.mul_pos hN1 hb1]
  · nlinarith [Nat.mul_pos hn1 hb1]
  · nlinarith [Nat.mul_pos hN1 hb1]
  · nlinarith [Nat.mul_pos hn1 hb1]
  · -- Dirichlet
    have key : 4 * n * (2 * (84000 * N * b) * (43 * n * b + 1))
        ≤ 29568 * n * b * (1000 * N * b * n) := by
      have h1 := Nat.mul_le_mul_left (n * N * b) (Nat.mul_pos hn1 hb1 : 1 ≤ n * b)
      linarith
    calc 4 * n * (429435 * N * b * b) * (2 * (84000 * N * b) * (43 * n * b + 1))
        = 429435 * N * b * b * (4 * n * (2 * (84000 * N * b) * (43 * n * b + 1))) := by ring
      _ ≤ 429435 * N * b * b * (29568 * n * b * (1000 * N * b * n)) :=
          Nat.mul_le_mul_left _ key
  · linarith
  · linarith
  · rw [hsub]
    linarith
  · have e14 := Nat.mul_le_mul_left (n * N * b * b) hb1
    linarith
  · have e14 := Nat.mul_le_mul_left (n * N * b * b) hb1
    linarith

end Azurite.Feldman
