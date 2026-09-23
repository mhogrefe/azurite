/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  **Cohen–Lenstra §9: Jacobi sums for `p = 2` — Theorems (9.1),
  (9.3), (9.5).**

  For `p = 2` (so `n` odd) the group-ring element is simply `β = 1`,
  and the tested congruences reduce to Gauss-sum algebra:

  * **(9.1)** (`k = 1`): if `q^((n−1)/2) ≡ ζ (mod n)` with
    `ζ ∈ {±1}`, then (7.9) holds — from `τ(χ)² = χ(−1)q` (Mathlib's
    `gaussSum_sq`), with the root `χ(−1)^((n−1)/2)·ζ`;
  * **(9.3)** (`k = 2`, `n ≡ 1 mod 4`): if
    `j(χ,χ)^((n−1)/2)·q^((n−1)/4) ≡ ζ (mod 𝔪)` with `ζ ∈ U₄`, then
    (7.9) holds — from `j(χ,χ) = τ(χ)²/τ(χ²)` (our (8.2)) and
    `τ(χ²)² = q`, with `σ_n` acting trivially;
  * **(9.5)** (`k = 2`, `n ≡ 3 mod 4`): if
    `j(χ,χ)^((n+1)/2)·q^((n−3)/4) ≡ ζ (mod nℤ[ζ₄])`, then (7.9)
    holds with `ζ` replaced by `χ(−1)·ζ` — additionally using the
    same-`ψ` product formula `τ(χ)·τ(χ⁻¹) = χ(−1)q` (the paper's
    (7.2), our `tau_mul_tau_inv`) and one cancellation of the
    nonzero factor `q` in the domain (the paper's division by the
    unit `χ(−1)q`).

  In each case the conclusion is the unit-free (7.9)-form
  `τ(χ,ψ)^n − ζ₀·σ(τ(χ,ψ)) ∈ I`, consumed with the singleton family
  `β = 1` by Theorem (7.8); the `p = 2` condition (6.4) comes from
  (7.24)/(7.25)/(10.8) rather than (7.19).  The "otherwise `n` is
  composite" halves are the (7.5)-completeness statements, assembled
  with the algorithm.  The remark that for (9.5) the only admissible
  ideal is `nℤ[ζ₄]` awaits (10.5).
-/
import Azurite.CohenLenstra.Equation_8_2
import Azurite.CohenLenstra.Theorem_7_8

namespace Azurite

namespace CL

open Finset

section NineOne

variable {R : Type _} [CommRing R] [IsDomain R] {q n : ℕ}
variable [Fact q.Prime]
variable {χ : MulChar (ZMod q) R} {ψ : AddChar (ZMod q) R}
variable {σ : R →+* R} {I : Ideal R}

omit [IsDomain R] in
/-- `χ(−1)² = 1`. -/
theorem chi_neg_one_sq (χ : MulChar (ZMod q) R) :
    χ (-1) * χ (-1) = 1 := by
  rw [← map_mul, neg_mul_neg, one_mul, MulChar.map_one]

/-- A character of order `2` is quadratic. -/
theorem isQuadratic_of_orderOf (hord : orderOf χ = 2) :
    MulChar.IsQuadratic χ := by
  intro a
  by_cases ha : IsUnit a
  · have hsq : χ a * χ a = 1 := by
      have hχ2 : χ ^ 2 = 1 := hord ▸ pow_orderOf_eq_one χ
      have h2 : (χ ^ 2) a = χ a ^ 2 :=
        MulChar.pow_apply' χ (by norm_num) a
      rw [hχ2, MulChar.one_apply ha] at h2
      rw [← pow_two]
      exact h2.symm
    rcases mul_self_eq_one_iff.mp hsq with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · exact Or.inl (χ.map_nonunit ha)

/-- **The paper's (7.2), same-`ψ` form**:
`τ(χ,ψ)·τ(χ⁻¹,ψ) = χ(−1)·q`. -/
theorem tau_mul_tau_inv (hχ1 : χ ≠ 1) (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ * gaussSum χ⁻¹ ψ = χ (-1) * ((q : ℕ) : R) := by
  have h1 := gaussSum_mul_gaussSum_eq_card hχ1 hψ
  have h2 := mul_gaussSum_inv_eq_gaussSum χ⁻¹ ψ
  have hinv : χ⁻¹ (-1) * χ (-1) = 1 := by
    rw [← MulChar.mul_apply, inv_mul_cancel]
    exact MulChar.one_apply (IsUnit.neg isUnit_one)
  have hinv' : χ⁻¹ (-1) = χ (-1) := by
    calc χ⁻¹ (-1) = χ⁻¹ (-1) * (χ (-1) * χ (-1)) := by
          rw [chi_neg_one_sq, mul_one]
      _ = (χ⁻¹ (-1) * χ (-1)) * χ (-1) := by ring
      _ = χ (-1) := by rw [hinv, one_mul]
  calc gaussSum χ ψ * gaussSum χ⁻¹ ψ
      = gaussSum χ ψ * (χ⁻¹ (-1) * gaussSum χ⁻¹ ψ⁻¹) := by rw [h2]
    _ = χ⁻¹ (-1) * (gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹) := by ring
    _ = χ⁻¹ (-1) * ((Fintype.card (ZMod q) : R)) := by rw [h1]
    _ = χ (-1) * ((q : ℕ) : R) := by rw [hinv', ZMod.card]

/-- **Cohen–Lenstra Theorem (9.1)** (`p = 2`, `k = 1`): if
`q^((n−1)/2) ≡ ζ' (mod I)` — the test (9.2) — then the
(7.9)-congruence holds for the quadratic character, with the root
`χ(−1)^((n−1)/2)·ζ'`. -/
theorem theorem_9_1 (hψ : ψ.IsPrimitive) (hord : orderOf χ = 2)
    (hodd : n % 2 = 1)
    (hσχ : ∀ a : ZMod q, σ (χ a) = χ a ^ n)
    (hσψ : ∀ a : ZMod q, σ (ψ a) = ψ a)
    {ζ' : R} (h92 : ((q : ℕ) : R) ^ ((n - 1) / 2) - ζ' ∈ I) :
    gaussSum χ ψ ^ n
      - (χ (-1) ^ ((n - 1) / 2) * ζ') * σ (gaussSum χ ψ) ∈ I := by
  have hχ1 : χ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hord
    omega
  have hsq : gaussSum χ ψ ^ 2 = χ (-1) * ((q : ℕ) : R) := by
    rw [gaussSum_sq hχ1 (isQuadratic_of_orderOf hord) hψ, ZMod.card]
  have hχn : χ ^ n = χ := by
    have h := pow_eq_pow_iff_modEq.mpr
      (show n ≡ 1 [MOD orderOf χ] from by
        rw [hord]
        unfold Nat.ModEq
        omega)
    rwa [pow_one] at h
  have hστ : σ (gaussSum χ ψ) = gaussSum χ ψ := by
    have h := sigma_gaussSum (χ := χ) (ψ := ψ) hσχ hσψ
      (by omega : n ≠ 0) (y := 1) one_ne_zero
    rw [pow_one, one_mul] at h
    rw [h, hχn]
  have hkey : gaussSum χ ψ ^ n
      = gaussSum χ ψ * (χ (-1) * ((q : ℕ) : R)) ^ ((n - 1) / 2) := by
    conv_lhs => rw [show n = 1 + 2 * ((n - 1) / 2) from by omega]
    rw [pow_add, pow_one, pow_mul, hsq]
  rw [hστ, hkey]
  have hfactor : gaussSum χ ψ * (χ (-1) * ((q : ℕ) : R)) ^ ((n - 1) / 2)
      - χ (-1) ^ ((n - 1) / 2) * ζ' * gaussSum χ ψ
      = (gaussSum χ ψ * χ (-1) ^ ((n - 1) / 2))
        * (((q : ℕ) : R) ^ ((n - 1) / 2) - ζ') := by
    rw [mul_pow]
    ring
  rw [hfactor]
  exact Ideal.mul_mem_left _ _ h92

/-- **Cohen–Lenstra Theorem (9.3)** (`p = 2`, `k = 2`,
`n ≡ 1 mod 4`): if `j(χ,χ)^((n−1)/2)·q^((n−1)/4) ≡ ζ' (mod I)` —
the test (9.4) — then the (7.9)-congruence holds, with the same
`ζ'`. -/
theorem theorem_9_3 (hψ : ψ.IsPrimitive) (hord : orderOf χ = 4)
    (hn4 : n % 4 = 1)
    (hσχ : ∀ a : ZMod q, σ (χ a) = χ a ^ n)
    (hσψ : ∀ a : ZMod q, σ (ψ a) = ψ a)
    {ζ' : R}
    (h94 : jacobiSum χ χ ^ ((n - 1) / 2) * ((q : ℕ) : R) ^ ((n - 1) / 4)
      - ζ' ∈ I) :
    gaussSum χ ψ ^ n - ζ' * σ (gaussSum χ ψ) ∈ I := by
  have hord2 : orderOf (χ ^ 2) = 2 := by
    rw [orderOf_pow, hord]
    decide
  have hχ21 : χ ^ 2 ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hord2
    omega
  have hsq2 : gaussSum (χ ^ 2) ψ ^ 2 = ((q : ℕ) : R) := by
    rw [gaussSum_sq hχ21 (isQuadratic_of_orderOf hord2) hψ, ZMod.card]
    have hval : (χ ^ 2) (-1) = 1 := by
      rw [MulChar.pow_apply' χ (by norm_num) _, pow_two,
        chi_neg_one_sq]
    rw [hval, one_mul]
  have h82' : gaussSum (χ ^ 2) ψ * jacobiSum χ χ
      = gaussSum χ ψ * gaussSum χ ψ := by
    have h := eq_8_2 (p := 2) (k := 2) (χ := χ)
      (by rw [hord]; norm_num) ψ (a := 1) (b := 1) (by norm_num)
    simpa using h
  have hχn : χ ^ n = χ := by
    have h := pow_eq_pow_iff_modEq.mpr
      (show n ≡ 1 [MOD orderOf χ] from by
        rw [hord]
        unfold Nat.ModEq
        omega)
    rwa [pow_one] at h
  have hστ : σ (gaussSum χ ψ) = gaussSum χ ψ := by
    have h := sigma_gaussSum (χ := χ) (ψ := ψ) hσχ hσψ
      (by omega : n ≠ 0) (y := 1) one_ne_zero
    rw [pow_one, one_mul] at h
    rw [h, hχn]
  have hkey : gaussSum χ ψ ^ n
      = gaussSum χ ψ * (jacobiSum χ χ ^ ((n - 1) / 2)
          * ((q : ℕ) : R) ^ ((n - 1) / 4)) := by
    have h2 : gaussSum (χ ^ 2) ψ ^ ((n - 1) / 2)
        = ((q : ℕ) : R) ^ ((n - 1) / 4) := by
      rw [show (n - 1) / 2 = 2 * ((n - 1) / 4) from by omega,
        pow_mul, hsq2]
    conv_lhs => rw [show n = 1 + 2 * ((n - 1) / 2) from by omega]
    rw [pow_add, pow_one, pow_mul, pow_two, ← h82', mul_pow, h2]
    ring
  rw [hστ, hkey]
  have hfactor : gaussSum χ ψ * (jacobiSum χ χ ^ ((n - 1) / 2)
        * ((q : ℕ) : R) ^ ((n - 1) / 4))
      - ζ' * gaussSum χ ψ
      = gaussSum χ ψ * (jacobiSum χ χ ^ ((n - 1) / 2)
          * ((q : ℕ) : R) ^ ((n - 1) / 4) - ζ') := by
    ring
  rw [hfactor]
  exact Ideal.mul_mem_left _ _ h94

/-- **Cohen–Lenstra Theorem (9.5)** (`p = 2`, `k = 2`,
`n ≡ 3 mod 4`): if `j(χ,χ)^((n+1)/2)·q^((n−3)/4) ≡ ζ' (mod I)` —
the test (9.6) — then the (7.9)-congruence holds, with `ζ'` replaced
by `χ(−1)·ζ'`. -/
theorem theorem_9_5 (hψ : ψ.IsPrimitive) (hord : orderOf χ = 4)
    (hn4 : n % 4 = 3) (hq0 : ((q : ℕ) : R) ≠ 0)
    (hσχ : ∀ a : ZMod q, σ (χ a) = χ a ^ n)
    (hσψ : ∀ a : ZMod q, σ (ψ a) = ψ a)
    {ζ' : R}
    (h96 : jacobiSum χ χ ^ ((n + 1) / 2) * ((q : ℕ) : R) ^ ((n - 3) / 4)
      - ζ' ∈ I) :
    gaussSum χ ψ ^ n - (χ (-1) * ζ') * σ (gaussSum χ ψ) ∈ I := by
  have hχ1 : χ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hord
    omega
  have hord2 : orderOf (χ ^ 2) = 2 := by
    rw [orderOf_pow, hord]
    decide
  have hχ21 : χ ^ 2 ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hord2
    omega
  have hsq2 : gaussSum (χ ^ 2) ψ ^ 2 = ((q : ℕ) : R) := by
    rw [gaussSum_sq hχ21 (isQuadratic_of_orderOf hord2) hψ, ZMod.card]
    have hval : (χ ^ 2) (-1) = 1 := by
      rw [MulChar.pow_apply' χ (by norm_num) _, pow_two,
        chi_neg_one_sq]
    rw [hval, one_mul]
  have h82' : gaussSum (χ ^ 2) ψ * jacobiSum χ χ
      = gaussSum χ ψ * gaussSum χ ψ := by
    have h := eq_8_2 (p := 2) (k := 2) (χ := χ)
      (by rw [hord]; norm_num) ψ (a := 1) (b := 1) (by norm_num)
    simpa using h
  have hχn : χ ^ n = χ ^ 3 := pow_eq_pow_iff_modEq.mpr (by
    rw [hord]
    unfold Nat.ModEq
    omega)
  have hστ : σ (gaussSum χ ψ) = gaussSum (χ ^ 3) ψ := by
    have h := sigma_gaussSum (χ := χ) (ψ := ψ) hσχ hσψ
      (by omega : n ≠ 0) (y := 1) one_ne_zero
    rw [pow_one, one_mul] at h
    rw [h, hχn]
  have hinv3 : χ ^ 3 = χ⁻¹ := by
    have h4 : χ ^ 4 = 1 := hord ▸ pow_orderOf_eq_one χ
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ]
    exact h4
  have h72 : gaussSum χ ψ * gaussSum (χ ^ 3) ψ
      = χ (-1) * ((q : ℕ) : R) := by
    rw [hinv3]
    exact tau_mul_tau_inv hχ1 hψ
  -- the paper's division, done as an exact identity in the domain
  have hn1e : gaussSum χ ψ ^ (n + 1)
      = jacobiSum χ χ ^ ((n + 1) / 2)
        * ((q : ℕ) : R) ^ ((n + 1) / 4) := by
    have h2 : gaussSum (χ ^ 2) ψ ^ ((n + 1) / 2)
        = ((q : ℕ) : R) ^ ((n + 1) / 4) := by
      rw [show (n + 1) / 2 = 2 * ((n + 1) / 4) from by omega,
        pow_mul, hsq2]
    conv_lhs => rw [show n + 1 = 2 * ((n + 1) / 2) from by omega]
    rw [pow_mul, pow_two, ← h82', mul_pow, h2]
    ring
  have hmain : ((q : ℕ) : R) * gaussSum χ ψ ^ n
      = ((q : ℕ) : R) * (χ (-1) * (jacobiSum χ χ ^ ((n + 1) / 2)
          * ((q : ℕ) : R) ^ ((n - 3) / 4)) * gaussSum (χ ^ 3) ψ) := by
    calc ((q : ℕ) : R) * gaussSum χ ψ ^ n
        = χ (-1) * (χ (-1) * ((q : ℕ) : R)) * gaussSum χ ψ ^ n := by
          rw [← mul_assoc, chi_neg_one_sq, one_mul]
      _ = χ (-1) * (gaussSum χ ψ * gaussSum (χ ^ 3) ψ)
            * gaussSum χ ψ ^ n := by rw [h72]
      _ = χ (-1) * gaussSum χ ψ ^ (n + 1) * gaussSum (χ ^ 3) ψ := by
          rw [pow_succ]
          ring
      _ = χ (-1) * (jacobiSum χ χ ^ ((n + 1) / 2)
            * ((q : ℕ) : R) ^ ((n + 1) / 4)) * gaussSum (χ ^ 3) ψ := by
          rw [hn1e]
      _ = ((q : ℕ) : R) * (χ (-1) * (jacobiSum χ χ ^ ((n + 1) / 2)
            * ((q : ℕ) : R) ^ ((n - 3) / 4)) * gaussSum (χ ^ 3) ψ) := by
          rw [show (n + 1) / 4 = (n - 3) / 4 + 1 from by omega,
            pow_succ]
          ring
  have hexact : gaussSum χ ψ ^ n
      = χ (-1) * (jacobiSum χ χ ^ ((n + 1) / 2)
          * ((q : ℕ) : R) ^ ((n - 3) / 4)) * gaussSum (χ ^ 3) ψ :=
    mul_left_cancel₀ hq0 hmain
  rw [hστ, hexact]
  have hfactor : χ (-1) * (jacobiSum χ χ ^ ((n + 1) / 2)
        * ((q : ℕ) : R) ^ ((n - 3) / 4)) * gaussSum (χ ^ 3) ψ
      - χ (-1) * ζ' * gaussSum (χ ^ 3) ψ
      = (χ (-1) * gaussSum (χ ^ 3) ψ)
        * (jacobiSum χ χ ^ ((n + 1) / 2)
          * ((q : ℕ) : R) ^ ((n - 3) / 4) - ζ') := by
    ring
  rw [hfactor]
  exact Ideal.mul_mem_left _ _ h96

end NineOne

end CL

end Azurite
