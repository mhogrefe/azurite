/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section10Series

/-!
# DLMF §3.10(ii): correctness of the quotient-difference algorithm

"The coefficients `aₙ` can always be calculated from the power-series coefficients by means of the
quotient-difference algorithm": if `cₖ ≠ 0` and the `e_j^k` of Table 3.10.1 do not vanish, the
`S`-fraction (3.10.6) with the coefficients 3.10.10 corresponds (3.10.7) to
`f(z) = c₀ + c₁z + ⋯` (`dlmf_3_10_10_corresponds`).

* `tail_residual`, `tail_dvd`: if power series `u_k` satisfy `u_k (1 + u_{k+1}) = a′_{k+1}` (the
  partial numerators) with `u₀ = f`, then `f Bₙ − Aₙ = −uₙ (f B_{n−1} − A_{n−1})`; so if
  `z ∣ u_k` (`k ≥ 1`), then `zⁿ ∣ f Bₙ − Aₙ`.
* The tails of the `S`-fraction of `F_k = c_k + c_{k+1}z + ⋯` (`qdV`): `u_m = z v_m` with
  `v₁ = −F_{k+1}/F_k`, `v_{2j} = v_{2j−1}^{(k+1)} + q_j^k − e_{j−1}^{k+1}`, and `v_{2j+1}` from
  `v_{2j}(1 + z v_{2j+1}) = −e_j^k`. The tail equations `v_{2j−1}(1 + z v_{2j}) = −q_j^k` follow
  by induction on `j` from the rhombus rules 3.10.9 (`qdV_tails`).
-/

open Finset

namespace Azurite.DLMF

/-! ### Tails and correspondence -/

section Tails

variable {S : Type*} [CommRing S]

/-- `f Bₖ₊₁ − Aₖ₊₁ = −u_k (f B_k − A_k)` for tails `u` with `u₀ = f`. -/
theorem tail_residual (a b : ℕ → S) (hb0 : b 0 = 0) (hb : ∀ k, b (k + 1) = 1) (u : ℕ → S)
    (hu : ∀ k, u k * (1 + u (k + 1)) = a (k + 1)) (k : ℕ) :
    u 0 * pcfQ a b (k + 1) - pcfP a b (k + 1) =
      -u k * (u 0 * pcfQ a b k - pcfP a b k) := by
  induction k with
  | zero => simp [pcfP, pcfQ, hb0]
  | succ k ih =>
    have hP : pcfP a b (k + 2) = pcfP a b (k + 1) + a (k + 1) * pcfP a b k := by
      rw [pcfP, hb, one_mul]
    have hQ : pcfQ a b (k + 2) = pcfQ a b (k + 1) + a (k + 1) * pcfQ a b k := by
      rw [pcfQ, hb, one_mul]
    rw [show k + 1 + 1 = k + 2 from rfl, hP, hQ, ← hu k]
    linear_combination (1 + u (k + 1)) * ih

/-- If moreover `x ∣ u_k` for `k ≥ 1`, then `xⁿ ∣ f Bₙ − Aₙ`. -/
theorem tail_dvd (a b : ℕ → S) (hb0 : b 0 = 0) (hb : ∀ k, b (k + 1) = 1) (u : ℕ → S)
    (hu : ∀ k, u k * (1 + u (k + 1)) = a (k + 1)) (x : S) (hx : ∀ k, x ∣ u (k + 1)) (n : ℕ) :
    x ^ n ∣ u 0 * pcfQ a b (n + 1) - pcfP a b (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [tail_residual a b hb0 hb u hu (n + 1), pow_succ, neg_mul, dvd_neg, mul_comm (u _)]
    exact mul_dvd_mul ih (hx n)

end Tails

/-! ### Power series -/

section PS

variable {𝕜 : Type*} [Field 𝕜]

/-- `F_k(z) = c_k + c_{k+1}z + c_{k+2}z² + ⋯`. -/
noncomputable def shiftSeries (c : ℕ → 𝕜) (k : ℕ) : PowerSeries 𝕜 :=
  PowerSeries.mk fun n => c (k + n)

theorem shiftSeries_succ (c : ℕ → 𝕜) (k : ℕ) :
    shiftSeries c k = PowerSeries.C (c k) + PowerSeries.X * shiftSeries c (k + 1) := by
  ext n
  rcases n with _ | n
  · simp [shiftSeries]
  · rw [map_add, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C]
    simp [shiftSeries, show k + (n + 1) = k + 1 + n by ring]

theorem constantCoeff_shiftSeries (c : ℕ → 𝕜) (k : ℕ) :
    PowerSeries.constantCoeff (shiftSeries c k) = c k := by
  simp [shiftSeries]

/-- Division by `z` of a series with zero constant term. -/
noncomputable def divX (g : PowerSeries 𝕜) : PowerSeries 𝕜 :=
  PowerSeries.mk fun n => PowerSeries.coeff (n + 1) g

theorem X_mul_divX {g : PowerSeries 𝕜} (h : PowerSeries.constantCoeff g = 0) :
    PowerSeries.X * divX g = g := by
  ext n
  rcases n with _ | n
  · simpa using h.symm
  · rw [PowerSeries.coeff_succ_X_mul]
    simp [divX]

/-- The tails `v_m^{(k)}` of the `S`-fraction of `F_k` (with `u_m = z v_m`). -/
noncomputable def qdV (c : ℕ → 𝕜) : ℕ → ℕ → PowerSeries 𝕜
  | 0, k => shiftSeries c k
  | 1, k => -(shiftSeries c (k + 1) * (shiftSeries c k)⁻¹)
  | m + 2, k =>
    if m % 2 = 0 then
      qdV c (m + 1) (k + 1) + PowerSeries.C (qdQ c (m / 2 + 1) k - qdE c (m / 2) (k + 1))
    else
      divX (-(PowerSeries.C (qdE c (m / 2 + 1) k) * (qdV c (m + 1) k)⁻¹) - 1)

theorem qdV_two (c : ℕ → 𝕜) (j k : ℕ) :
    qdV c (2 * j + 2) k =
      qdV c (2 * j + 1) (k + 1) + PowerSeries.C (qdQ c (j + 1) k - qdE c j (k + 1)) := by
  rw [qdV, ite_eq_left (by omega), show 2 * j / 2 = j by omega]

theorem qdV_three (c : ℕ → 𝕜) (j k : ℕ) :
    qdV c (2 * j + 3) k =
      divX (-(PowerSeries.C (qdE c (j + 1) k) * (qdV c (2 * j + 2) k)⁻¹) - 1) := by
  rw [show 2 * j + 3 = (2 * j + 1) + 2 from rfl, qdV, ite_eq_right (by omega),
    show (2 * j + 1) / 2 = j by omega]

theorem constantCoeff_one_add_X_mul_qd (w : PowerSeries 𝕜) :
    PowerSeries.constantCoeff (1 + PowerSeries.X * w) = 1 := by
  simp

/-- The tail equations of the quotient-difference algorithm, by induction on `j`:
`v_{2j+1}^{(k)} (1 + z v_{2j+2}^{(k)}) = −q_{j+1}^k`, the constant term of `v_{2j+2}^{(k)}` is
`−e_{j+1}^k`, and `v_{2j+2}^{(k)} (1 + z v_{2j+3}^{(k)}) = −e_{j+1}^k`. -/
theorem qdV_tails {c : ℕ → 𝕜} (hc : ∀ k, c k ≠ 0) (he : ∀ j k, qdE c (j + 1) k ≠ 0) (j : ℕ) :
    ∀ k, qdV c (2 * j + 1) k * (1 + PowerSeries.X * qdV c (2 * j + 2) k) =
        PowerSeries.C (-qdQ c (j + 1) k) ∧
      PowerSeries.constantCoeff (qdV c (2 * j + 2) k) = -qdE c (j + 1) k ∧
      qdV c (2 * j + 2) k * (1 + PowerSeries.X * qdV c (2 * j + 3) k) =
        PowerSeries.C (-qdE c (j + 1) k) := by
  -- the even equation and the constant term follow from the odd equations
  have finish : ∀ j, (∀ k, qdV c (2 * j + 1) k * (1 + PowerSeries.X * qdV c (2 * j + 2) k) =
      PowerSeries.C (-qdQ c (j + 1) k)) →
      ∀ k, qdV c (2 * j + 1) k * (1 + PowerSeries.X * qdV c (2 * j + 2) k) =
          PowerSeries.C (-qdQ c (j + 1) k) ∧
        PowerSeries.constantCoeff (qdV c (2 * j + 2) k) = -qdE c (j + 1) k ∧
        qdV c (2 * j + 2) k * (1 + PowerSeries.X * qdV c (2 * j + 3) k) =
          PowerSeries.C (-qdE c (j + 1) k) := by
    intro j hodd k
    have hcc : PowerSeries.constantCoeff (qdV c (2 * j + 2) k) = -qdE c (j + 1) k := by
      have h1 := congrArg PowerSeries.constantCoeff (hodd (k + 1))
      rw [map_mul, constantCoeff_one_add_X_mul_qd, mul_one, PowerSeries.constantCoeff_C] at h1
      rw [qdV_two, map_add, h1, PowerSeries.constantCoeff_C, (dlmf_3_10_9 c j k).1]
      ring
    refine ⟨hodd k, hcc, ?_⟩
    have hne : PowerSeries.constantCoeff (qdV c (2 * j + 2) k) ≠ 0 := by
      rw [hcc]; exact neg_ne_zero.mpr (he j k)
    rw [qdV_three, X_mul_divX]
    · rw [mul_add, mul_one, mul_sub, mul_one, mul_neg, ← mul_assoc, mul_comm _ (PowerSeries.C _),
        mul_assoc, PowerSeries.mul_inv_cancel _ hne, mul_one, map_neg]
      ring
    · rw [map_sub, map_neg, map_mul, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_inv,
        hcc, map_one]
      field_simp [he j k]
      ring
  induction j with
  | zero =>
    apply finish 0
    intro k
    have hF := shiftSeries_succ c (k + 1)
    have hF0 := shiftSeries_succ c k
    have hk : PowerSeries.constantCoeff (shiftSeries c k) ≠ 0 := by
      rw [constantCoeff_shiftSeries]; exact hc k
    have hk1 : PowerSeries.constantCoeff (shiftSeries c (k + 1)) ≠ 0 := by
      rw [constantCoeff_shiftSeries]; exact hc (k + 1)
    have hq : qdQ c 1 k = c (k + 1) / c k := rfl
    have he0 : qdE c 0 (k + 1) = 0 := rfl
    simp only [show 2 * 0 + 1 = 1 from rfl, show 2 * 0 + 2 = 0 * 2 + 2 from rfl]
    rw [show 0 * 2 + 2 = 2 * 0 + 2 from rfl, qdV_two]
    simp only [show 2 * 0 + 1 = 1 from rfl, qdV, he0, sub_zero, hq]
    have hinv := PowerSeries.mul_inv_cancel _ hk
    have hinv1 := PowerSeries.mul_inv_cancel _ hk1
    -- `F_{k+1} − z F_{k+2} = c_{k+1}` and `c_{k+1} = q c_k`
    have hCq : PowerSeries.C (c (k + 1)) =
        PowerSeries.C (c (k + 1) / c k) * PowerSeries.C (c k) := by
      rw [← map_mul, div_mul_cancel₀ _ (hc k)]
    rw [map_neg]
    set F0 := shiftSeries c k
    set F1 := shiftSeries c (k + 1)
    set F2 := shiftSeries c (k + 1 + 1)
    set Q := PowerSeries.C (c (k + 1) / c k)
    linear_combination (PowerSeries.X * F2 * F0⁻¹) * hinv1 - F0⁻¹ * hF - F0⁻¹ * hCq +
      Q * F0⁻¹ * hF0 - Q * hinv
  | succ j ih =>
    apply finish (j + 1)
    intro k
    obtain ⟨E1, -, -⟩ := ih (k + 1)
    obtain ⟨-, hc0, E2⟩ := ih k
    obtain ⟨-, hc1, E3⟩ := ih (k + 1)
    -- rhombus rules
    have R1 : qdE c (j + 1) k + (qdQ c (j + 1) k - qdE c j (k + 1)) = qdQ c (j + 1) (k + 1) := by
      rw [(dlmf_3_10_9 c j k).1]; ring
    have R2 : qdQ c (j + 2) k * qdE c (j + 1) k =
        qdQ c (j + 1) (k + 1) * qdE c (j + 1) (k + 1) := by
      rw [(dlmf_3_10_9 c j k).2]; field_simp [he j k]
    set X := (PowerSeries.X : PowerSeries 𝕜)
    set Xv := qdV c (2 * j + 1) (k + 1)
    set Yv := qdV c (2 * j + 2) (k + 1)
    set P := qdV c (2 * j + 2) k
    set A := qdV c (2 * j + 3) k
    set B := qdV c (2 * j + 3) (k + 1)
    have hP : P = Xv + PowerSeries.C (qdQ c (j + 1) k - qdE c j (k + 1)) := qdV_two c j k
    have hgoal : qdV c (2 * (j + 1) + 2) k =
        B + PowerSeries.C (qdQ c (j + 2) k - qdE c (j + 1) (k + 1)) := by
      rw [qdV_two, show 2 * (j + 1) + 1 = 2 * j + 3 by ring]
    rw [show 2 * (j + 1) + 1 = 2 * j + 3 by ring, hgoal]
    -- cancel the nonzero factor `P Yv X (1 + X Yv)`
    have hPne : P ≠ 0 := fun h => by
      rw [h, map_zero] at hc0; exact he j k (neg_eq_zero.mp hc0.symm)
    have hYne : Yv ≠ 0 := fun h => by
      rw [h, map_zero] at hc1; exact he j (k + 1) (neg_eq_zero.mp hc1.symm)
    have hXne : X ≠ 0 := PowerSeries.X_ne_zero
    have hSne : (1 + X * Yv) ≠ 0 := fun h => by
      have := congrArg PowerSeries.constantCoeff h
      rw [constantCoeff_one_add_X_mul_qd, map_zero] at this; exact one_ne_zero this
    refine mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (mul_ne_zero hPne hYne) hXne) hSne) ?_
    set e := qdE c (j + 1) k
    set e' := qdE c (j + 1) (k + 1)
    set q := qdQ c (j + 2) k
    set q' := qdQ c (j + 1) (k + 1)
    set δ' := qdQ c (j + 1) k - qdE c j (k + 1)
    have R1' : PowerSeries.C e + PowerSeries.C δ' = PowerSeries.C q' := by rw [← map_add, R1]
    have R2' : PowerSeries.C q * PowerSeries.C e = PowerSeries.C q' * PowerSeries.C e' := by
      rw [← map_mul, ← map_mul, R2]
    rw [map_neg] at E1 E2 E3 ⊢
    rw [map_sub]
    have h1 : P * X * A = -PowerSeries.C e - P := by linear_combination E2
    have h2 : Yv * X * B = -PowerSeries.C e' - Yv := by linear_combination E3
    have h3 : (PowerSeries.C e + P) * (1 + X * Yv) = PowerSeries.C q' * X * Yv := by
      rw [hP]; linear_combination E1 + (1 + X * Yv) * R1'
    have h4 : P * (1 + X * Yv) = -PowerSeries.C q' + PowerSeries.C δ' * (1 + X * Yv) := by
      rw [hP]; linear_combination E1
    linear_combination ((1 + X * Yv) * Yv * (1 + X * B + X * (PowerSeries.C q - PowerSeries.C e')))
      * h1 + ((1 + X * Yv) * (-PowerSeries.C e - P)) * h2 -
      (-PowerSeries.C e' + X * Yv * (PowerSeries.C q - PowerSeries.C e')) * h3 +
      (PowerSeries.C q * X * Yv) * h4 - (X * Yv * (1 + X * Yv)) * R2' +
      (X * Yv * (1 + X * Yv) * PowerSeries.C q) * R1'

/-! ### The correspondence -/

theorem pcfP_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a b : ℕ → R) (k : ℕ) :
    pcfP (fun i => φ (a i)) (fun i => φ (b i)) k = φ (pcfP a b k) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | _ | k
    · simp [pcfP]
    · simp [pcfP]
    · rw [pcfP, pcfP, ih _ (by omega), ih _ (by omega)]
      simp

theorem pcfQ_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a b : ℕ → R) (k : ℕ) :
    pcfQ (fun i => φ (a i)) (fun i => φ (b i)) k = φ (pcfQ a b k) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | _ | k
    · simp [pcfQ]
    · simp [pcfQ]
    · rw [pcfQ, pcfQ, ih _ (by omega), ih _ (by omega)]
      simp

/-- **DLMF §3.10(ii)**: the quotient-difference algorithm. If the `cₖ` and the `e_j^k` (`j ≥ 1`)
of Table 3.10.1 do not vanish, the `S`-fraction (3.10.6) whose coefficients are given by 3.10.10
(`a₀ = c₀`, `a₁ = q_1^0`, `a₂ = e_1^0`, `a₃ = q_2^0`, …) corresponds (3.10.7) to
`f(z) = c₀ + c₁z + c₂z² + ⋯`. -/
theorem dlmf_3_10_10_corresponds {c : ℕ → 𝕜} (hc : ∀ k, c k ≠ 0)
    (he : ∀ j k, qdE c (j + 1) k ≠ 0) :
    SCorresponds (qdCoeff c) (PowerSeries.mk c) := by
  set φ := Polynomial.coeToPowerSeries.ringHom (R := 𝕜)
  have hF0 : shiftSeries c 0 = PowerSeries.mk c := by ext n; simp [shiftSeries]
  set u : ℕ → PowerSeries 𝕜 := fun m =>
    if m = 0 then shiftSeries c 0 else PowerSeries.X * qdV c m 0
  have hk0 : PowerSeries.constantCoeff (shiftSeries c 0) ≠ 0 := by
    rw [constantCoeff_shiftSeries]; exact hc 0
  have hu : ∀ m, u m * (1 + u (m + 1)) = φ (sfA (qdCoeff c) (m + 1)) := by
    intro m
    rcases m with _ | m
    · simp only [u, ite_eq_left, ite_eq_right (Nat.succ_ne_zero 0), sfA, qdCoeff, φ,
        Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C]
      show (shiftSeries c 0) * (1 + PowerSeries.X * qdV c 1 0) = PowerSeries.C (c 0)
      have h := shiftSeries_succ c 0
      have hinv := PowerSeries.mul_inv_cancel _ hk0
      simp only [qdV]
      linear_combination h - (PowerSeries.X * shiftSeries c (0 + 1)) * hinv
    · simp only [u, ite_eq_right (Nat.succ_ne_zero _), sfA, φ,
        Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_neg, Polynomial.coe_mul,
        Polynomial.coe_C, Polynomial.coe_X]
      obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' m
      · obtain ⟨h1, -, -⟩ := qdV_tails hc he j 0
        have hq : qdCoeff c (2 * j + 1) = qdQ c (j + 1) 0 := (dlmf_3_10_10 c j).2.1
        rw [hq, show 2 * j + 1 + 1 = 2 * j + 2 from rfl]
        rw [map_neg] at h1
        linear_combination PowerSeries.X * h1
      · obtain ⟨-, -, h3⟩ := qdV_tails hc he j 0
        have hq : qdCoeff c (2 * j + 2) = qdE c (j + 1) 0 := (dlmf_3_10_10 c j).2.2
        rw [show 2 * j + 1 + 1 = 2 * j + 2 from rfl, hq,
          show 2 * j + 2 + 1 = 2 * j + 3 from rfl]
        rw [map_neg] at h3
        linear_combination PowerSeries.X * h3
  have hb0 : φ (sfB (𝕜 := 𝕜) 0) = 0 := by simp [sfB, φ]
  have hb : ∀ k, φ (sfB (𝕜 := 𝕜) (k + 1)) = 1 := fun k => by simp [sfB, φ]
  have hx : ∀ k, PowerSeries.X ∣ u (k + 1) := fun k => by
    simp only [u, ite_eq_right (Nat.succ_ne_zero _)]; exact dvd_mul_right _ _
  intro n hn i hi
  have hdvd := tail_dvd (fun k => φ (sfA (qdCoeff c) k)) (fun k => φ (sfB k)) hb0 hb u hu
    PowerSeries.X hx n
  rw [pcfQ_map, pcfP_map] at hdvd
  simp only [u, ite_eq_left] at hdvd
  set N : PowerSeries 𝕜 := (sNum (qdCoeff c) n : PowerSeries 𝕜)
  set D : PowerSeries 𝕜 := (sDen (qdCoeff c) n : PowerSeries 𝕜)
  have hD : PowerSeries.constantCoeff D ≠ 0 := by
    have := sDen_coeff_zero (qdCoeff c) n
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, this]
    exact one_ne_zero
  have hdvd' : PowerSeries.X ^ n ∣ (shiftSeries c 0) - N * D⁻¹ := by
    have : (shiftSeries c 0) - N * D⁻¹ = ((shiftSeries c 0) * D - N) * D⁻¹ := by
      rw [sub_mul, mul_assoc, PowerSeries.mul_inv_cancel _ hD, mul_one]
    rw [this]
    exact dvd_mul_of_dvd_left hdvd _
  have := (PowerSeries.X_pow_dvd_iff.mp hdvd') i hi
  rw [map_sub, sub_eq_zero] at this
  rw [← hF0, ← this]

end PS

end Azurite.DLMF
